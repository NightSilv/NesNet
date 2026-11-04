/*
 * NesNet v1 - emulador de NES con netplay para PS3
 *   PSL1GHT + nucleo libretro FCEUmm
 *
 * Netplay: lockstep con retraso fijo (delay) sobre TCP, 2 jugadores.
 *   - El host crea la sala y recibe un CODIGO NUMERICO (15 digitos) que codifica
 *     su IP publica y puerto. El cliente escribe ese codigo con el mando.
 *   - Sin servidor: conexion directa host <-> cliente.
 *
 * Se compila de 2 formas:
 *   -DNESNET_PS3   -> aplicacion real para PS3
 *   -DNESNET_HOST  -> version de pruebas para PC (sin video, mando simulado)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>

#include "libretro.h"

#ifdef NESNET_PS3
#include <ppu-types.h>
#include <malloc.h>
#include <sys/process.h>
#include <sys/systime.h>
#include <io/pad.h>
#include <rsx/rsx.h>
#include <sysutil/sysutil.h>
#include <sysutil/video.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <net/net.h>
#include <net/netdb.h>
#include <netinet/in.h>
SYS_PROCESS_PARAM(1001, 0x100000);
int closesocket(int s);      /* definida en libnet, pero sin prototipo en las cabeceras */
#else
#include <time.h>
#include <signal.h>
#include <poll.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#define closesocket close
#endif

#ifndef TCP_NODELAY
#define TCP_NODELAY 1
#endif

/* ------------------------------------------------------------------ */
/* Constantes                                                          */
/* ------------------------------------------------------------------ */
#define PROTO_VER      1
#define DEFAULT_PORT   7777
#define SCR_W          256
#define SCR_H          240
#define RING           64
#define MSG_SIZE       16
#define NO_FRAME       0xFFFFFFFFu

/* Modos de juego (el menu y config.txt devuelven siempre estos valores) */
#define MODE_SOLO      0
#define MODE_HOST      1
#define MODE_JOIN      2

/* Botones NES (mismo orden que el byte del mando) */
#define NB_A      0x01
#define NB_B      0x02
#define NB_SEL    0x04
#define NB_START  0x08
#define NB_UP     0x10
#define NB_DOWN   0x20
#define NB_LEFT   0x40
#define NB_RIGHT  0x80

/* Botones de la interfaz (menus) */
#define UI_UP     0x01
#define UI_DOWN   0x02
#define UI_LEFT   0x04
#define UI_RIGHT  0x08
#define UI_OK     0x10
#define UI_CANCEL 0x20
#define UI_START  0x40

/* ------------------------------------------------------------------ */
/* Estado global                                                       */
/* ------------------------------------------------------------------ */
typedef struct {
    char     rom[256];
    char     mode[16];        /* "", "host", "client", "local" */
    char     code[32];
    char     public_ip[32];
    int      delay;           /* 0 = automatico */
    int      port;
} Config;

static Config   g_cfg;
static char     g_dir[256] = "/dev_hdd0/game/NESN00001/USRDIR";
static FILE    *g_log;
static int      g_running = 1;
static const char *g_err = "";

static uint8_t *g_rom;
static size_t   g_romsz;
static uint32_t g_romcrc;

static uint32_t g_fb[SCR_W * SCR_H];      /* lienzo ARGB */
static uint16_t g_pad[2];                 /* entrada NES que ve el nucleo */
static unsigned g_pixfmt = RETRO_PIXEL_FORMAT_RGB565;
static uint32_t g_frame_crc;
static int      g_core_loaded;

static int      g_net = -1;               /* socket de la partida */
static uint8_t  g_rx[512];
static int      g_rxlen;

/* ------------------------------------------------------------------ */
/* Utilidades                                                          */
/* ------------------------------------------------------------------ */
static uint32_t now_ms(void)
{
#ifdef NESNET_PS3
    u64 s, n;
    sysGetCurrentTime(&s, &n);
    return (uint32_t)(s * 1000ULL + n / 1000000ULL);
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint32_t)(ts.tv_sec * 1000ULL + ts.tv_nsec / 1000000ULL);
#endif
}

static void sleep_ms(int ms) { usleep((useconds_t)ms * 1000); }

static void logf_(const char *fmt, ...)
{
    char buf[256];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    if (g_log) { fprintf(g_log, "[%u] %s\n", (unsigned)now_ms(), buf); fflush(g_log); }
#ifdef NESNET_HOST
    fprintf(stderr, "%s\n", buf);
#endif
}

static uint32_t crc32_buf(const uint8_t *d, size_t n)
{
    uint32_t c = 0xFFFFFFFFu;
    size_t i;
    int k;
    for (i = 0; i < n; i++) {
        c ^= d[i];
        for (k = 0; k < 8; k++) c = (c >> 1) ^ (0xEDB88320u & (0u - (c & 1u)));
    }
    return ~c;
}

static uint32_t fnv_u32(uint32_t h, uint32_t v)
{
    int i;
    for (i = 0; i < 4; i++) { h ^= (v >> (i * 8)) & 0xFF; h *= 16777619u; }
    return h;
}

static void pump(void);   /* atiende al sistema (boton PS, etc.) */

/* Latido: cada ~2 s escribe en nesnet.log en que fase esta el programa. Si la consola se
 * cuelga, la ultima linea del log dice cuando y en que fase paso. */
static const char *g_stage = "inicio";
static uint32_t    g_hb;
static void heartbeat(void)
{
    if (++g_hb % 120 == 0) logf_("latido %u fase=%s", (unsigned)g_hb, g_stage);
}

/* ------------------------------------------------------------------ */
/* Configuracion (config.txt: clave=valor)                             */
/* ------------------------------------------------------------------ */
static void cfg_defaults(void)
{
    memset(&g_cfg, 0, sizeof g_cfg);
    snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s/rom.nes", g_dir);
    g_cfg.port = DEFAULT_PORT;
}

static void cfg_load(void)
{
    char path[300], line[300];
    FILE *f;
    cfg_defaults();
    snprintf(path, sizeof path, "%s/config.txt", g_dir);
    f = fopen(path, "r");
    if (!f) { logf_("sin config.txt (%s), uso valores por defecto", path); return; }
    while (fgets(line, sizeof line, f)) {
        char *k = line, *v, *e;
        while (*k == ' ' || *k == '\t') k++;
        if (*k == '#' || *k == ';' || *k == '\n' || *k == '\r' || !*k) continue;
        v = strchr(k, '=');
        if (!v) continue;
        *v++ = 0;
        e = k + strlen(k);
        while (e > k && (e[-1] == ' ' || e[-1] == '\t')) *--e = 0;
        while (*v == ' ' || *v == '\t') v++;
        e = v + strlen(v);
        while (e > v && (e[-1] == '\n' || e[-1] == '\r' || e[-1] == ' ' || e[-1] == '\t')) *--e = 0;
        if (!strcmp(k, "rom")) {
            if (v[0] == '/') snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s", v);
            else snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s/%s", g_dir, v);
        }
        else if (!strcmp(k, "mode"))      snprintf(g_cfg.mode, sizeof g_cfg.mode, "%s", v);
        else if (!strcmp(k, "code"))      snprintf(g_cfg.code, sizeof g_cfg.code, "%s", v);
        else if (!strcmp(k, "public_ip")) snprintf(g_cfg.public_ip, sizeof g_cfg.public_ip, "%s", v);
        else if (!strcmp(k, "delay"))     g_cfg.delay = atoi(v);
        else if (!strcmp(k, "port"))      g_cfg.port = atoi(v);
    }
    fclose(f);
    if (g_cfg.port <= 0 || g_cfg.port > 65535) g_cfg.port = DEFAULT_PORT;
}

/* ------------------------------------------------------------------ */
/* Shims de libretro-common que el nucleo (modo estatico) espera       */
/* ------------------------------------------------------------------ */
struct RFILE { FILE *f; };

void filestream_vfs_init(const struct retro_vfs_interface_info *i) { (void)i; }
void path_vfs_init(const struct retro_vfs_interface_info *i) { (void)i; }

struct RFILE *filestream_open(const char *path, unsigned mode, unsigned hints)
{
    struct RFILE *r;
    FILE *f;
    (void)hints;
    f = fopen(path, (mode & RETRO_VFS_FILE_ACCESS_WRITE) ? "wb" : "rb");
    if (!f) return NULL;
    r = (struct RFILE *)malloc(sizeof *r);
    if (!r) { fclose(f); return NULL; }
    r->f = f;
    return r;
}
int filestream_close(struct RFILE *r)
{
    if (!r) return -1;
    fclose(r->f);
    free(r);
    return 0;
}
int64_t filestream_get_size(struct RFILE *r)
{
    long cur, end;
    if (!r) return -1;
    cur = ftell(r->f);
    fseek(r->f, 0, SEEK_END);
    end = ftell(r->f);
    fseek(r->f, cur, SEEK_SET);
    return end;
}
int64_t filestream_read(struct RFILE *r, void *d, int64_t n)
{
    if (!r) return -1;
    return (int64_t)fread(d, 1, (size_t)n, r->f);
}
int64_t filestream_seek(struct RFILE *r, int64_t off, int pos)
{
    int w = (pos == RETRO_VFS_SEEK_POSITION_CURRENT) ? SEEK_CUR :
            (pos == RETRO_VFS_SEEK_POSITION_END) ? SEEK_END : SEEK_SET;
    if (!r) return -1;
    return fseek(r->f, (long)off, w) == 0 ? 0 : -1;
}
int64_t filestream_tell(struct RFILE *r)
{
    return r ? (int64_t)ftell(r->f) : -1;
}
size_t fill_pathname_join(char *s, const char *dir, const char *path, size_t len)
{
    size_t n;
    snprintf(s, len, "%s", dir);
    n = strlen(s);
    if (n && s[n - 1] != '/' && n + 1 < len) { s[n++] = '/'; s[n] = 0; }
    if (n < len) snprintf(s + n, len - n, "%s", path);
    return strlen(s);
}
int path_is_valid(const char *path)
{
    struct stat st;
    return path && stat(path, &st) == 0;
}

/* ------------------------------------------------------------------ */
/* Fuente 5x7 (ASCII 32..90) y dibujo de texto en el lienzo            */
/* ------------------------------------------------------------------ */
static const uint8_t font5x7[59][5] = {
    {0x00,0x00,0x00,0x00,0x00},{0x00,0x00,0x5F,0x00,0x00},{0x00,0x07,0x00,0x07,0x00},
    {0x14,0x7F,0x14,0x7F,0x14},{0x24,0x2A,0x7F,0x2A,0x12},{0x23,0x13,0x08,0x64,0x62},
    {0x36,0x49,0x55,0x22,0x50},{0x00,0x05,0x03,0x00,0x00},{0x00,0x1C,0x22,0x41,0x00},
    {0x00,0x41,0x22,0x1C,0x00},{0x14,0x08,0x3E,0x08,0x14},{0x08,0x08,0x3E,0x08,0x08},
    {0x00,0x50,0x30,0x00,0x00},{0x08,0x08,0x08,0x08,0x08},{0x00,0x60,0x60,0x00,0x00},
    {0x20,0x10,0x08,0x04,0x02},
    {0x3E,0x51,0x49,0x45,0x3E},{0x00,0x42,0x7F,0x40,0x00},{0x42,0x61,0x51,0x49,0x46},
    {0x21,0x41,0x45,0x4B,0x31},{0x18,0x14,0x12,0x7F,0x10},{0x27,0x45,0x45,0x45,0x39},
    {0x3C,0x4A,0x49,0x49,0x30},{0x01,0x71,0x09,0x05,0x03},{0x36,0x49,0x49,0x49,0x36},
    {0x06,0x49,0x49,0x29,0x1E},
    {0x00,0x36,0x36,0x00,0x00},{0x00,0x56,0x36,0x00,0x00},{0x08,0x14,0x22,0x41,0x00},
    {0x14,0x14,0x14,0x14,0x14},{0x00,0x41,0x22,0x14,0x08},{0x02,0x01,0x51,0x09,0x06},
    {0x32,0x49,0x79,0x41,0x3E},
    {0x7E,0x11,0x11,0x11,0x7E},{0x7F,0x49,0x49,0x49,0x36},{0x3E,0x41,0x41,0x41,0x22},
    {0x7F,0x41,0x41,0x22,0x1C},{0x7F,0x49,0x49,0x49,0x41},{0x7F,0x09,0x09,0x09,0x01},
    {0x3E,0x41,0x49,0x49,0x7A},{0x7F,0x08,0x08,0x08,0x7F},{0x00,0x41,0x7F,0x41,0x00},
    {0x20,0x40,0x41,0x3F,0x01},{0x7F,0x08,0x14,0x22,0x41},{0x7F,0x40,0x40,0x40,0x40},
    {0x7F,0x02,0x0C,0x02,0x7F},{0x7F,0x04,0x08,0x10,0x7F},{0x3E,0x41,0x41,0x41,0x3E},
    {0x7F,0x09,0x09,0x09,0x06},{0x3E,0x41,0x51,0x21,0x5E},{0x7F,0x09,0x19,0x29,0x46},
    {0x46,0x49,0x49,0x49,0x31},{0x01,0x01,0x7F,0x01,0x01},{0x3F,0x40,0x40,0x40,0x3F},
    {0x1F,0x20,0x40,0x20,0x1F},{0x3F,0x40,0x38,0x40,0x3F},{0x63,0x14,0x08,0x14,0x63},
    {0x07,0x08,0x70,0x08,0x07},{0x61,0x51,0x49,0x45,0x43}
};

static void ui_text(int x, int y, const char *s, int sc, uint32_t col)
{
    for (; *s; s++, x += 6 * sc) {
        int c = (unsigned char)*s, cx, cy, i, j;
        if (c >= 'a' && c <= 'z') c -= 32;
        if (c < 32 || c > 90) c = '?';
        for (cx = 0; cx < 5; cx++) {
            uint8_t colbits = font5x7[c - 32][cx];
            for (cy = 0; cy < 7; cy++) {
                if (!(colbits & (1 << cy))) continue;
                for (j = 0; j < sc; j++)
                    for (i = 0; i < sc; i++) {
                        int px = x + cx * sc + i, py = y + cy * sc + j;
                        if (px >= 0 && px < SCR_W && py >= 0 && py < SCR_H)
                            g_fb[py * SCR_W + px] = col;
                    }
            }
        }
    }
}

static void ui_center(int y, const char *s, int sc, uint32_t col)
{
    int w = (int)strlen(s) * 6 * sc - sc;
    ui_text((SCR_W - w) / 2, y, s, sc, col);
}

static void ui_clear(void)
{
    int i;
    for (i = 0; i < SCR_W * SCR_H; i++) g_fb[i] = 0xFF101838;
}

/* ------------------------------------------------------------------ */
/* Plataforma: video, mando                                            */
/* ------------------------------------------------------------------ */
#ifdef NESNET_PS3

#define CB_SIZE   0x100000
#define HOST_SIZE (32 * 1024 * 1024)
#define GCM_LABEL_INDEX 255
#define LABEL_TEX0      253          /* 253 y 254: una por textura */

static gcmContextData *g_ctx;
static u32 g_dw, g_dh, g_pitch, g_off[2], g_dpitch, g_doff;
static u32 g_cur, g_first = 1, g_label = 1;
static u32 *g_cbuf[2], *g_dbuf;
static u32 *g_tex[2];
static u32  g_texoff[2];
static int  g_texsel;
static u32  g_texval[2];
static int  g_zoom = 3;
static padData g_pd[2];
static uint16_t g_ui_prev;

static void gpu_wait_finish(void)
{
    rsxSetWriteBackendLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    rsxFlushBuffer(g_ctx);
    while (*(vu32 *)gcmGetLabelAddress(GCM_LABEL_INDEX) != g_label) usleep(30);
    ++g_label;
}

static void gpu_wait_idle(void)
{
    rsxSetWriteBackendLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    rsxSetWaitLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    ++g_label;
    gpu_wait_finish();
}

static void gpu_set_target(u32 idx)
{
    gcmSurface sf;
    memset(&sf, 0, sizeof sf);
    sf.colorFormat      = GCM_SURFACE_X8R8G8B8;
    sf.colorTarget      = GCM_SURFACE_TARGET_0;
    sf.colorLocation[0] = GCM_LOCATION_RSX;
    sf.colorOffset[0]   = g_off[idx];
    sf.colorPitch[0]    = g_pitch;
    sf.colorLocation[1] = GCM_LOCATION_RSX;
    sf.colorLocation[2] = GCM_LOCATION_RSX;
    sf.colorLocation[3] = GCM_LOCATION_RSX;
    sf.colorOffset[1]   = 0;
    sf.colorOffset[2]   = 0;
    sf.colorOffset[3]   = 0;
    sf.colorPitch[1]    = 64;
    sf.colorPitch[2]    = 64;
    sf.colorPitch[3]    = 64;
    sf.depthFormat      = GCM_SURFACE_ZETA_Z16;
    sf.depthLocation    = GCM_LOCATION_RSX;
    sf.depthOffset      = g_doff;
    sf.depthPitch       = g_dpitch;
    sf.type             = GCM_SURFACE_TYPE_LINEAR;
    sf.antiAlias        = GCM_SURFACE_CENTER_1;
    sf.width            = g_dw;
    sf.height           = g_dh;
    sf.x                = 0;
    sf.y                = 0;
    rsxSetSurface(g_ctx, &sf);
}

static void gpu_init(void)
{
    videoState state;
    videoConfiguration vconfig;
    videoResolution res;
    void *host_addr = memalign(1024 * 1024, HOST_SIZE);
    int i;

    rsxInit(&g_ctx, CB_SIZE, HOST_SIZE, host_addr);

    videoGetState(0, 0, &state);
    videoGetResolution(state.displayMode.resolution, &res);

    memset(&vconfig, 0, sizeof vconfig);
    vconfig.resolution = state.displayMode.resolution;
    vconfig.format     = VIDEO_BUFFER_FORMAT_XRGB;
    vconfig.pitch      = res.width * sizeof(u32);

    gpu_wait_idle();
    videoConfigure(0, &vconfig, NULL, 0);
    videoGetState(0, 0, &state);

    gcmSetFlipMode(GCM_FLIP_VSYNC);

    g_dw = res.width;
    g_dh = res.height;
    g_pitch = g_dw * sizeof(u32);
    g_cbuf[0] = (u32 *)rsxMemalign(64, g_dh * g_pitch);
    g_cbuf[1] = (u32 *)rsxMemalign(64, g_dh * g_pitch);
    rsxAddressToOffset(g_cbuf[0], &g_off[0]);
    rsxAddressToOffset(g_cbuf[1], &g_off[1]);
    gcmSetDisplayBuffer(0, g_off[0], g_pitch, g_dw, g_dh);
    gcmSetDisplayBuffer(1, g_off[1], g_pitch, g_dw, g_dh);

    g_dpitch = g_dw * sizeof(u32);
    g_dbuf = (u32 *)rsxMemalign(64, (g_dh * g_dpitch) * 2);
    rsxAddressToOffset(g_dbuf, &g_doff);

    for (i = 0; i < 2; i++) {
        g_tex[i] = (u32 *)rsxMemalign(64, SCR_W * SCR_H * 4);
        rsxAddressToOffset(g_tex[i], &g_texoff[i]);
        memset(g_tex[i], 0, SCR_W * SCR_H * 4);
        g_texval[i] = 0;
        *(vu32 *)gcmGetLabelAddress(LABEL_TEX0 + i) = 0;
    }

    g_zoom = (int)(g_dh / SCR_H);
    if (g_zoom < 1) g_zoom = 1;
    if (g_zoom > 4) g_zoom = 4;

    gpu_set_target(g_cur);
}

static void gpu_flip(void)
{
    if (!g_first) {
        while (gcmGetFlipStatus() != 0) usleep(200);
        gcmResetFlipStatus();
    } else {
        gcmResetFlipStatus();
    }
    gcmSetFlip(g_ctx, g_cur);
    rsxFlushBuffer(g_ctx);
    gcmSetWaitFlip(g_ctx);
    g_cur ^= 1;
    gpu_set_target(g_cur);
    g_first = 0;
}

static void gpu_blit_canvas(void)
{
    gcmTransferScale scale;
    gcmTransferSurface surface;
    int sel = g_texsel;
    float zoom = (float)g_zoom;

    g_texsel ^= 1;

    /* Esperar a que la GPU termine de leer ESTA textura (la uso cada 2 cuadros) antes de
     * escribirla otra vez; con tope de ~0,5 s para no quedarse esperando para siempre. */
    g_stage = "gpu-espera-textura";
    {
        int guard = 0;
        while (*(vu32 *)gcmGetLabelAddress(LABEL_TEX0 + sel) != g_texval[sel] && guard++ < 16000)
            usleep(30);
        if (guard >= 16000) logf_("AVISO: la GPU no libero la textura %d a tiempo", sel);
    }
    g_stage = "gpu-copia-textura";
    memcpy(g_tex[sel], g_fb, SCR_W * SCR_H * 4);

    rsxSetClearColor(g_ctx, 0x00000000);
    rsxSetClearDepthStencil(g_ctx, 0xffff);
    rsxClearSurface(g_ctx, GCM_CLEAR_R | GCM_CLEAR_G | GCM_CLEAR_B | GCM_CLEAR_A |
                           GCM_CLEAR_S | GCM_CLEAR_Z);

    rsxSetBlendFunc(g_ctx, GCM_SRC_ALPHA, GCM_ONE_MINUS_SRC_ALPHA,
                    GCM_SRC_ALPHA, GCM_ONE_MINUS_SRC_ALPHA);
    rsxSetBlendEquation(g_ctx, GCM_FUNC_ADD, GCM_FUNC_ADD);
    rsxSetBlendEnable(g_ctx, GCM_TRUE);

    memset(&scale, 0, sizeof scale);
    scale.conversion = GCM_TRANSFER_CONVERSION_TRUNCATE;
    scale.format     = GCM_TRANSFER_SCALE_FORMAT_A8R8G8B8;
    scale.origin     = GCM_TRANSFER_ORIGIN_CORNER;
    scale.operation  = GCM_TRANSFER_OPERATION_SRCCOPY_AND;
    scale.interp     = GCM_TRANSFER_INTERPOLATOR_NEAREST;
    scale.clipX = 0;
    scale.clipY = 0;
    scale.clipW = g_dw;
    scale.clipH = g_dh;
    scale.outX  = (g_dw - SCR_W * g_zoom) / 2;
    scale.outY  = (g_dh - SCR_H * g_zoom) / 2;
    scale.outW  = SCR_W * g_zoom;
    scale.outH  = SCR_H * g_zoom;
    scale.ratioX = rsxGetFixedSint32(1.f / zoom);
    scale.ratioY = rsxGetFixedSint32(1.f / zoom);
    scale.inX = rsxGetFixedUint16(0);
    scale.inY = rsxGetFixedUint16(0);
    scale.inW = SCR_W;
    scale.inH = SCR_H;
    scale.offset = g_texoff[sel];
    scale.pitch  = sizeof(u32) * SCR_W;

    surface.format = GCM_TRANSFER_SURFACE_FORMAT_A8R8G8B8;
    surface.pitch  = g_pitch;
    surface.offset = g_off[g_cur];

    g_stage = "gpu-encolar-blit";
    rsxSetTransferScaleMode(g_ctx, GCM_TRANSFER_LOCAL_TO_LOCAL, GCM_TRANSFER_SURFACE);
    rsxSetTransferScaleSurface(g_ctx, &scale, &surface);

    /* la GPU escribe esta marca cuando termine el blit de esta textura */
    g_texval[sel]++;
    rsxSetWriteBackendLabel(g_ctx, LABEL_TEX0 + sel, g_texval[sel]);
}

static void present(void)
{
    gpu_blit_canvas();
    g_stage = "gpu-flip";
    gpu_flip();
    g_stage = "ok";
    heartbeat();
}

static void sysutil_cb(u64 status, u64 param, void *usrdata)
{
    (void)param; (void)usrdata;
    if (status == SYSUTIL_EXIT_GAME) g_running = 0;
}

static void pump(void) { sysUtilCheckCallback(); }

static void exit_cb(void)
{
    sysUtilUnregisterCallback(SYSUTIL_EVENT_SLOT0);
    if (g_ctx) { gcmSetWaitFlip(g_ctx); rsxFinish(g_ctx, 1); }
}

static void platform_init(void)
{
    gpu_init();
    ioPadInit(7);
    atexit(exit_cb);
    sysUtilRegisterCallback(0, sysutil_cb, NULL);
}

static void net_ensure(void)
{
    static int ready;
    if (!ready) { logf_("iniciando red"); netInitialize(); ready = 1; logf_("red lista"); }
}

/* Lee el mando 'port'; conserva el ultimo estado si no hay cambios */
static padData *pad_read(int port)
{
    padInfo pi;
    padData d;
    ioPadGetInfo(&pi);
    if (!pi.status[port]) { memset(&g_pd[port], 0, sizeof g_pd[port]); return &g_pd[port]; }
    memset(&d, 0, sizeof d);
    ioPadGetData(port, &d);
    if (d.len > 0) g_pd[port] = d;
    return &g_pd[port];
}

static uint16_t pad_nes_bits(int port)
{
    padData *d = pad_read(port);
    uint16_t b = 0;
    if (d->BTN_CIRCLE) b |= NB_A;
    if (d->BTN_CROSS)  b |= NB_B;
    if (d->BTN_SELECT) b |= NB_SEL;
    if (d->BTN_START)  b |= NB_START;
    if (d->BTN_UP)     b |= NB_UP;
    if (d->BTN_DOWN)   b |= NB_DOWN;
    if (d->BTN_LEFT)   b |= NB_LEFT;
    if (d->BTN_RIGHT)  b |= NB_RIGHT;
    if ((b & NB_UP) && (b & NB_DOWN))   b &= ~NB_DOWN;
    if ((b & NB_LEFT) && (b & NB_RIGHT)) b &= ~NB_RIGHT;
    return b;
}

static uint16_t ui_edges(void)
{
    padData *d = pad_read(0);
    uint16_t c = 0, e;
    if (d->BTN_UP)     c |= UI_UP;
    if (d->BTN_DOWN)   c |= UI_DOWN;
    if (d->BTN_LEFT)   c |= UI_LEFT;
    if (d->BTN_RIGHT)  c |= UI_RIGHT;
    if (d->BTN_CROSS)  c |= UI_OK;
    if (d->BTN_CIRCLE) c |= UI_CANCEL;
    if (d->BTN_START)  c |= UI_START;
    e = c & ~g_ui_prev;
    g_ui_prev = c;
    return e;
}

#else /* ------------------------- version de pruebas (PC) ------------- */

static void pump(void) {}
static void present(void) { heartbeat(); }
static void net_ensure(void) {}

/* Pulsaciones simuladas del menu: u d l r = direcciones, x = OK, o = cancelar, s = START */
static const char *g_ui_script = "";
static uint16_t ui_edges(void)
{
    char c = *g_ui_script;
    if (!c) return 0;
    g_ui_script++;
    switch (c) {
    case 'u': return UI_UP;
    case 'd': return UI_DOWN;
    case 'l': return UI_LEFT;
    case 'r': return UI_RIGHT;
    case 'x': return UI_OK;
    case 'o': return UI_CANCEL;
    case 's': return UI_START;
    default:  return 0;
    }
}
static uint16_t pad_nes_bits(int port) { (void)port; return 0; }

/* Mando simulado: determinista por (jugador, frame); cambia cada 6 frames */
static uint16_t script_input(int slot, uint32_t f)
{
    uint32_t x = (f / 6 + 1) * 2654435761u ^ ((uint32_t)(slot + 1) * 40503u * 2246822519u);
    uint16_t b;
    x ^= x >> 15; x *= 2246822519u; x ^= x >> 13; x *= 3266489917u; x ^= x >> 16;
    b = (uint16_t)(x & 0xFF);
    if ((b & NB_UP) && (b & NB_DOWN))   b &= ~NB_DOWN;
    if ((b & NB_LEFT) && (b & NB_RIGHT)) b &= ~NB_RIGHT;
    return b;
}
#endif

/* ------------------------------------------------------------------ */
/* Nucleo libretro (FCEUmm)                                            */
/* ------------------------------------------------------------------ */
static bool env_cb(unsigned cmd, void *data)
{
    switch (cmd) {
    case RETRO_ENVIRONMENT_SET_PIXEL_FORMAT: {
        enum retro_pixel_format f = *(enum retro_pixel_format *)data;
        if (f == RETRO_PIXEL_FORMAT_RGB565 || f == RETRO_PIXEL_FORMAT_XRGB8888) {
            g_pixfmt = (unsigned)f;
            return true;
        }
        return false;
    }
    case RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY:
    case RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY:
        *(const char **)data = g_dir;
        return true;
    case RETRO_ENVIRONMENT_GET_CAN_DUPE:
        *(bool *)data = true;
        return true;
    default:
        return false;
    }
}

static void video_cb(const void *data, unsigned w, unsigned h, size_t pitch)
{
    unsigned x, y, ox, oy;
    uint32_t hsh = 2166136261u;
    if (!data) return;                      /* frame repetido: no hay cambios */
    if (w > SCR_W) w = SCR_W;
    if (h > SCR_H) h = SCR_H;
    ox = (SCR_W - w) / 2;
    oy = (SCR_H - h) / 2;
    for (y = 0; y < SCR_W * SCR_H; y++) g_fb[y] = 0xFF000000;
    for (y = 0; y < h; y++) {
        const uint8_t *row = (const uint8_t *)data + y * pitch;
        uint32_t *dst = &g_fb[(oy + y) * SCR_W + ox];
        for (x = 0; x < w; x++) {
            uint32_t px;
            if (g_pixfmt == RETRO_PIXEL_FORMAT_RGB565) {
                uint32_t p = ((const uint16_t *)row)[x];
                uint32_t r = (p >> 11) & 31, g = (p >> 5) & 63, b = p & 31;
                px = 0xFF000000u | (((r << 3) | (r >> 2)) << 16) |
                     (((g << 2) | (g >> 4)) << 8) | ((b << 3) | (b >> 2));
            } else {
                px = 0xFF000000u | (((const uint32_t *)row)[x] & 0x00FFFFFFu);
            }
            dst[x] = px;
        }
    }
    for (y = 0; y < SCR_W * SCR_H; y++) hsh = fnv_u32(hsh, g_fb[y]);
    g_frame_crc = hsh;
}

static void audio_cb(int16_t l, int16_t r) { (void)l; (void)r; }
static size_t audio_batch_cb(const int16_t *d, size_t frames) { (void)d; return frames; }
static void input_poll_cb(void) {}
static int16_t input_state_cb(unsigned port, unsigned dev, unsigned idx, unsigned id)
{
    unsigned bit;
    (void)idx;
    if (port > 1 || dev != RETRO_DEVICE_JOYPAD) return 0;
    switch (id) {
    case RETRO_DEVICE_ID_JOYPAD_A:      bit = 0; break;
    case RETRO_DEVICE_ID_JOYPAD_B:      bit = 1; break;
    case RETRO_DEVICE_ID_JOYPAD_SELECT: bit = 2; break;
    case RETRO_DEVICE_ID_JOYPAD_START:  bit = 3; break;
    case RETRO_DEVICE_ID_JOYPAD_UP:     bit = 4; break;
    case RETRO_DEVICE_ID_JOYPAD_DOWN:   bit = 5; break;
    case RETRO_DEVICE_ID_JOYPAD_LEFT:   bit = 6; break;
    case RETRO_DEVICE_ID_JOYPAD_RIGHT:  bit = 7; break;
    default: return 0;
    }
    return (g_pad[port] >> bit) & 1;
}

static int read_whole_file(const char *path, uint8_t **buf, size_t *size)
{
    FILE *f = fopen(path, "rb");
    long n;
    if (!f) return 0;
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n <= 0) { fclose(f); return 0; }
    *buf = (uint8_t *)malloc((size_t)n);
    if (!*buf || fread(*buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(*buf); *buf = NULL; return 0; }
    fclose(f);
    *size = (size_t)n;
    return 1;
}

static void core_boot(void)
{
    retro_set_environment(env_cb);
    retro_set_video_refresh(video_cb);
    retro_set_audio_sample(audio_cb);
    retro_set_audio_sample_batch(audio_batch_cb);
    retro_set_input_poll(input_poll_cb);
    retro_set_input_state(input_state_cb);
    retro_init();
}

static int core_load(void)
{
    struct retro_game_info gi;
    if (g_core_loaded) return 1;
    memset(&gi, 0, sizeof gi);
    gi.path = g_cfg.rom;
    gi.data = g_rom;
    gi.size = g_romsz;
    if (!retro_load_game(&gi)) { g_err = "EL NUCLEO NO PUDO CARGAR LA ROM"; return 0; }
    retro_set_controller_port_device(0, RETRO_DEVICE_JOYPAD);
    retro_set_controller_port_device(1, RETRO_DEVICE_JOYPAD);
    g_core_loaded = 1;
    return 1;
}

static void core_unload(void)
{
    if (g_core_loaded) { retro_unload_game(); g_core_loaded = 0; }
}

static void step_frame(uint16_t p1, uint16_t p2)
{
    g_pad[0] = p1;
    g_pad[1] = p2;
    retro_run();
}

/* ------------------------------------------------------------------ */
/* Red: mensajes de 16 bytes, TCP, poll() con espera propia            */
/* ------------------------------------------------------------------ */
enum { M_HELLO = 1, M_PING, M_PONG, M_CFG, M_START, M_INPUT, M_QUIT, M_REJECT };

typedef struct {
    uint8_t  type, a;
    uint16_t input;
    uint32_t frame, v1, v2;
} Msg;

static void put32(uint8_t *p, uint32_t v) { p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v; }
static uint32_t get32(const uint8_t *p) { return ((uint32_t)p[0] << 24) | (p[1] << 16) | (p[2] << 8) | p[3]; }

static int net_send(const Msg *m)
{
    uint8_t b[MSG_SIZE];
    int off = 0;
    memset(b, 0, sizeof b);
    b[0] = m->type; b[1] = m->a; b[2] = m->input >> 8; b[3] = m->input & 0xFF;
    put32(b + 4, m->frame); put32(b + 8, m->v1); put32(b + 12, m->v2);
#ifdef NESNET_HOST
    { const char *j = getenv("NESNET_JITTER_MS"); if (j && atoi(j) > 0) sleep_ms(rand() % (atoi(j) + 1)); }
#endif
    while (off < MSG_SIZE) {
        int n = (int)send(g_net, (const char *)b + off, MSG_SIZE - off, 0);
        if (n <= 0) return 0;
        off += n;
    }
    return 1;
}

/* Espera a que 'fd' tenga evento; 1 = listo, 0 = agotado, -1 = error */
static int fd_wait(int fd, short ev, int timeout_ms)
{
    uint32_t t0 = now_ms();
    for (;;) {
        struct pollfd p;
        int r;
        p.fd = fd; p.events = ev; p.revents = 0;
        r = poll(&p, 1, 0);
        if (r < 0) return -1;
        if (r > 0) return 1;
        if ((int)(now_ms() - t0) >= timeout_ms) return 0;
        pump();
        if (!g_running) return -1;
        sleep_ms(2);
    }
}

/* 1 = mensaje, 0 = tiempo agotado, -1 = error / conexion cerrada */
static int net_recv(Msg *m, int timeout_ms)
{
    uint32_t t0 = now_ms();
    for (;;) {
        if (g_rxlen >= MSG_SIZE) {
            const uint8_t *b = g_rx;
            m->type = b[0]; m->a = b[1]; m->input = (uint16_t)((b[2] << 8) | b[3]);
            m->frame = get32(b + 4); m->v1 = get32(b + 8); m->v2 = get32(b + 12);
            memmove(g_rx, g_rx + MSG_SIZE, g_rxlen - MSG_SIZE);
            g_rxlen -= MSG_SIZE;
            return 1;
        }
        {
            int left = timeout_ms - (int)(now_ms() - t0);
            int r = fd_wait(g_net, POLLIN, left > 0 ? left : 0);
            int n;
            if (r < 0) return -1;
            if (r == 0) return 0;
            n = (int)recv(g_net, (char *)g_rx + g_rxlen, (int)sizeof g_rx - g_rxlen, 0);
            if (n <= 0) return -1;
            g_rxlen += n;
        }
    }
}

static void sock_nonblock(int fd, int on)
{
#ifdef NESNET_PS3
    int v = on;
    setsockopt(fd, SOL_SOCKET, SO_NBIO, &v, sizeof v);
#else
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, on ? (fl | O_NONBLOCK) : (fl & ~O_NONBLOCK));
#endif
}

static void sock_nodelay(int fd)
{
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);   /* si falla, no pasa nada */
}

static int tcp_connect(uint32_t ip, int port, int timeout_ms)
{
    struct sockaddr_in a;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    sock_nonblock(fd, 1);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(ip);
    if (connect(fd, (struct sockaddr *)&a, sizeof a) < 0) {
        int err = 0;
        socklen_t l = sizeof err;
        if (fd_wait(fd, POLLOUT, timeout_ms) <= 0) { closesocket(fd); return -1; }
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &l) == 0 && err != 0) { closesocket(fd); return -1; }
    }
    sock_nonblock(fd, 0);
    sock_nodelay(fd);
    return fd;
}

static int tcp_listen(int port)
{
    struct sockaddr_in a;
    int one = 1;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    if (bind(fd, (struct sockaddr *)&a, sizeof a) < 0 || listen(fd, 1) < 0) { closesocket(fd); return -1; }
    return fd;
}

static int parse_ip(const char *s, uint32_t *out)
{
    unsigned a, b, c, d;
    char tail;
    if (sscanf(s, "%u.%u.%u.%u%c", &a, &b, &c, &d, &tail) < 4) return 0;
    if (a > 255 || b > 255 || c > 255 || d > 255) return 0;
    *out = (a << 24) | (b << 16) | (c << 8) | d;
    return 1;
}

/* IP publica: GET http://api.ipify.org (devuelve solo la IP en texto) */
static int get_public_ip(uint32_t *ip)
{
    static const char req[] =
        "GET / HTTP/1.0\r\nHost: api.ipify.org\r\nConnection: close\r\n\r\n";
    struct hostent *he;
    uint8_t *b;
    char buf[512];
    int fd, n, len = 0;
    char *body;
    uint32_t sip;

    he = gethostbyname("api.ipify.org");
    if (!he || !he->h_addr_list || !he->h_addr_list[0]) return 0;
    b = (uint8_t *)he->h_addr_list[0];
    sip = ((uint32_t)b[0] << 24) | (b[1] << 16) | (b[2] << 8) | b[3];
    fd = tcp_connect(sip, 80, 6000);
    if (fd < 0) return 0;
    if (send(fd, req, (int)sizeof req - 1, 0) <= 0) { closesocket(fd); return 0; }
    while (len < (int)sizeof buf - 1 && fd_wait(fd, POLLIN, 6000) > 0) {
        n = (int)recv(fd, buf + len, (int)sizeof buf - 1 - len, 0);
        if (n <= 0) break;
        len += n;
    }
    closesocket(fd);
    buf[len] = 0;
    body = strstr(buf, "\r\n\r\n");
    if (!body) return 0;
    body += 4;
    while (*body == ' ' || *body == '\r' || *body == '\n') body++;
    return parse_ip(body, ip);
}

/* Codigo = (IP << 16 | puerto) en decimal de 15 digitos */
static void code_encode(uint32_t ip, int port, char *out)
{
    uint64_t v = ((uint64_t)ip << 16) | (uint64_t)(port & 0xFFFF);
    int i;
    for (i = 14; i >= 0; i--) { out[i] = (char)('0' + (int)(v % 10)); v /= 10; }
    out[15] = 0;
}

static int code_decode(const char *code, uint32_t *ip, int *port)
{
    uint64_t v = 0;
    int i, n = 0;
    for (i = 0; code[i]; i++) {
        if (code[i] < '0' || code[i] > '9') continue;     /* ignora espacios y guiones */
        v = v * 10 + (uint64_t)(code[i] - '0');
        n++;
    }
    if (n < 10 || n > 15 || v >= (1ULL << 48)) return 0;
    *ip = (uint32_t)(v >> 16);
    *port = (int)(v & 0xFFFF);
    return *port > 0 && *ip != 0;
}

/* ------------------------------------------------------------------ */
/* Handshake                                                           */
/* ------------------------------------------------------------------ */
static int cmp_u32(const void *a, const void *b)
{
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return x < y ? -1 : x > y;
}

static int clamp_i(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }

static int handshake_host(int *outD)
{
    Msg m;
    uint32_t rtt[5];
    int i, D, r;

    r = net_recv(&m, 10000);
    if (r <= 0 || m.type != M_HELLO) { g_err = "EL AMIGO NO RESPONDIO"; return 0; }
    if (m.frame != PROTO_VER) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 1; net_send(&m);
        g_err = "VERSIONES DISTINTAS DE NESNET"; return 0;
    }
    if (m.v1 != g_romcrc) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 2; net_send(&m);
        g_err = "ROM DISTINTA A LA DEL AMIGO"; return 0;
    }
    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = PROTO_VER; m.v1 = g_romcrc;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }

    for (i = 0; i < 5; i++) {
        uint32_t t0 = now_ms();
        memset(&m, 0, sizeof m); m.type = M_PING; m.v1 = (uint32_t)i;
        if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
        r = net_recv(&m, 5000);
        if (r <= 0 || m.type != M_PONG || m.v1 != (uint32_t)i) { g_err = "FALLO LA MEDICION DE LATENCIA"; return 0; }
        rtt[i] = now_ms() - t0;
    }
    qsort(rtt, 5, sizeof rtt[0], cmp_u32);
    D = g_cfg.delay > 0 ? g_cfg.delay : clamp_i((int)((rtt[2] / 2 + 16) / 17) + 2, 3, 12);
    logf_("RTT mediana %u ms -> delay %d frames", (unsigned)rtt[2], D);

    memset(&m, 0, sizeof m); m.type = M_CFG; m.v1 = (uint32_t)D; m.v2 = rtt[2];
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    memset(&m, 0, sizeof m); m.type = M_START;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    *outD = D;
    return 1;
}

static int handshake_client(int *outD)
{
    Msg m;
    int r, D = 0, haveD = 0;
    uint32_t t0;

    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = PROTO_VER; m.v1 = g_romcrc;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    r = net_recv(&m, 10000);
    if (r <= 0) { g_err = "EL HOST NO RESPONDIO"; return 0; }
    if (m.type == M_REJECT) { g_err = (m.v1 == 2) ? "ROM DISTINTA A LA DEL HOST" : "VERSIONES DISTINTAS DE NESNET"; return 0; }
    if (m.type != M_HELLO) { g_err = "RESPUESTA INVALIDA DEL HOST"; return 0; }

    t0 = now_ms();
    while (now_ms() - t0 < 20000) {
        r = net_recv(&m, 2000);
        if (r < 0) { g_err = "SE CORTO LA CONEXION"; return 0; }
        if (r == 0) continue;
        if (m.type == M_PING) {
            Msg p; memset(&p, 0, sizeof p); p.type = M_PONG; p.v1 = m.v1;
            if (!net_send(&p)) { g_err = "SE CORTO LA CONEXION"; return 0; }
        } else if (m.type == M_CFG) {
            D = (int)m.v1; haveD = 1;
        } else if (m.type == M_START && haveD) {
            *outD = clamp_i(D, 1, 20);
            return 1;
        }
    }
    g_err = "TIEMPO AGOTADO EN EL INICIO";
    return 0;
}

/* ------------------------------------------------------------------ */
/* Bucle de partida                                                    */
/* ------------------------------------------------------------------ */
static uint32_t g_run_hash, g_frames_done;
static uint32_t g_maxframes;              /* 0 = sin limite (solo la version de pruebas lo usa) */
static int      g_desyncs;
static uint32_t g_first_desync;

static uint16_t local_bits(int port, int slot, uint32_t frame)
{
#ifdef NESNET_HOST
    (void)port;
    return script_input(slot, frame);
#else
    (void)slot; (void)frame;
    return pad_nes_bits(port);
#endif
}

/* role: 0 = host (P1), 1 = cliente (P2), -1 = local directo (2 mandos),
 *       -2 = referencia de pruebas: local con el mismo retraso D     */
static int session_loop(int role, int D, uint32_t maxframes)
{
    uint16_t loc[RING], rem[RING];
    uint8_t  have[RING];
    uint32_t mine_f[RING], mine_c[RING], rem_f[RING], rem_c[RING];
    uint32_t frame = 0, last_rx = now_ms();
    int i, ended_ok = 1, peer_gone = 0, peer_quit = 0;
    char ov[64];

    memset(loc, 0, sizeof loc); memset(rem, 0, sizeof rem); memset(have, 0, sizeof have);
    for (i = 0; i < RING; i++) { mine_f[i] = NO_FRAME; rem_f[i] = NO_FRAME; mine_c[i] = rem_c[i] = 0; }
    if (role >= 0) for (i = 0; i < D; i++) have[i] = 1;

    g_run_hash = 2166136261u; g_frames_done = 0; g_desyncs = 0; g_first_desync = NO_FRAME;
    g_stage = role == 0 ? "juego-host" : role == 1 ? "juego-cliente" : "juego-local";

#define COMPARE(f) do { uint32_t _f = (f); \
        if (mine_f[_f % RING] == _f && rem_f[_f % RING] == _f && \
            mine_c[_f % RING] != rem_c[_f % RING]) { \
            if (!g_desyncs) { g_first_desync = _f; logf_("DESYNC en frame %u", (unsigned)_f); } \
            g_desyncs++; \
            mine_f[_f % RING] = NO_FRAME; } } while (0)

    while (g_running && (maxframes == 0 || frame < maxframes)) {
        uint16_t p1, p2;
        pump();

        if (role == -1) {
            p1 = local_bits(0, 0, frame);
            p2 = local_bits(1, 1, frame);
        } else if (role == -2) {
            p1 = frame >= (uint32_t)D ? local_bits(0, 0, frame - D) : 0;
            p2 = frame >= (uint32_t)D ? local_bits(0, 1, frame - D) : 0;
        } else {
            Msg m;
            uint32_t tgt = frame + (uint32_t)D;
            uint16_t bits = local_bits(0, role, frame);
            loc[tgt % RING] = bits;

            memset(&m, 0, sizeof m);
            m.type = M_INPUT; m.input = bits; m.frame = tgt;
            if (frame > 0) { m.v1 = frame - 1; m.v2 = mine_c[(frame - 1) % RING]; } else { m.v1 = NO_FRAME; }
            if (!peer_gone && !net_send(&m)) peer_gone = 1;   /* lo decide el bucle de espera */

            for (;;) {
                int r;
                if (peer_gone) {
                    /* el otro lado cerro: seguimos solo mientras queden entradas ya recibidas */
                    if (have[frame % RING]) break;
                    g_err = peer_quit ? "EL AMIGO SALIO DE LA PARTIDA" : "SE PERDIO LA CONEXION";
                    ended_ok = 0; goto out;
                }
                r = net_recv(&m, have[frame % RING] ? 0 : 100);
                if (r < 0) { if (!g_running) goto out; peer_gone = 1; continue; }
                if (r == 0) {
                    if (have[frame % RING]) break;
                    if (!g_running) goto out;
                    if (now_ms() - last_rx > 15000) { g_err = "EL AMIGO NO RESPONDE (15 S)"; ended_ok = 0; goto out; }
                    continue;
                }
                last_rx = now_ms();
                if (m.type == M_INPUT) {
                    rem[m.frame % RING] = m.input;
                    have[m.frame % RING] = 1;
                    if (m.v1 != NO_FRAME) { rem_f[m.v1 % RING] = m.v1; rem_c[m.v1 % RING] = m.v2; COMPARE(m.v1); }
                } else if (m.type == M_QUIT) {
                    peer_quit = 1; peer_gone = 1;
                }
            }
            have[frame % RING] = 0;
            {
                uint16_t mine = loc[frame % RING], theirs = rem[frame % RING];
                p1 = (role == 0) ? mine : theirs;
                p2 = (role == 0) ? theirs : mine;
            }
        }

#ifdef NESNET_HOST
        { const char *b = getenv("NESNET_BREAK");        /* prueba: corrompe a proposito un frame */
          if (b && role == 1 && frame >= (uint32_t)atoi(b) && frame < (uint32_t)atoi(b) + 30) p1 ^= 0xFF; }
#endif
        step_frame(p1, p2);

        mine_f[frame % RING] = frame;
        mine_c[frame % RING] = g_frame_crc;
        if (role >= 0) COMPARE(frame);
        g_run_hash = fnv_u32(g_run_hash, g_frame_crc);

        if (role >= 0 && (g_desyncs || frame < 300)) {
            if (g_desyncs) snprintf(ov, sizeof ov, "DESYNC EN FRAME %u", (unsigned)g_first_desync);
            else snprintf(ov, sizeof ov, "NESNET  P%d  DELAY %d", role + 1, D);
            ui_text(2, 2, ov, 1, g_desyncs ? 0xFFFF4040 : 0xFFFFFFFF);
        }
        present();
        frame++;
        g_frames_done = frame;
    }
out:
    if (role >= 0 && g_net >= 0) {
        Msg q; memset(&q, 0, sizeof q); q.type = M_QUIT; net_send(&q);
    }
#undef COMPARE
    return ended_ok;
}

/* ------------------------------------------------------------------ */
/* Interfaz                                                            */
/* ------------------------------------------------------------------ */
static void ui_show(const char *l1, const char *l2, const char *l3)
{
    ui_clear();
    ui_center(20, "NESNET V1", 2, 0xFFFFD040);
    if (l1) ui_center(90, l1, 1, 0xFFFFFFFF);
    if (l2) ui_center(110, l2, 1, 0xFFC0C0FF);
    if (l3) ui_center(130, l3, 1, 0xFFC0C0FF);
    present();
}

static void ui_message(const char *l1, const char *l2, int frames)
{
    int i;
    for (i = 0; i < frames && g_running; i++) {
        uint16_t e;
        pump();
        ui_show(l1, l2, NULL);
        e = ui_edges();
        if (i > 60 && (e & (UI_OK | UI_CANCEL | UI_START))) break;   /* ~1 s minimo en pantalla */
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

static int ui_menu(void)
{
    static const char *items[3] = { "CREAR SALA (HOST)", "UNIRSE A UNA SALA", "SOLO - 2 MANDOS" };
    static const int modes[3] = { MODE_HOST, MODE_JOIN, MODE_SOLO };   /* mismo orden que items */
    int sel = 0, i;
    g_stage = "menu";
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 2) % 3;
        if (e & UI_DOWN) sel = (sel + 1) % 3;
        if (e & (UI_OK | UI_START)) return modes[sel];
        ui_clear();
        ui_center(20, "NESNET V1", 2, 0xFFFFD040);
        ui_center(46, "NES CON NETPLAY PARA PS3", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", items[i]);
            ui_center(90 + i * 22, line, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(200, "ARRIBA/ABAJO + X", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

static int ui_enter_code(char *out)
{
    int d[15], pos = 0, i;
    memset(d, 0, sizeof d);
    while (g_running) {
        uint16_t e;
        char digits[16], line[40];
        pump();
        e = ui_edges();
        if (e & UI_UP)    d[pos] = (d[pos] + 1) % 10;
        if (e & UI_DOWN)  d[pos] = (d[pos] + 9) % 10;
        if (e & UI_LEFT)  { if (pos > 0) pos--; }
        if (e & (UI_RIGHT | UI_OK)) { if (pos < 14) pos++; }
        if (e & UI_CANCEL) return 0;
        if (e & UI_START) {
            for (i = 0; i < 15; i++) out[i] = (char)('0' + d[i]);
            out[15] = 0;
            return 1;
        }
        for (i = 0; i < 15; i++) digits[i] = (char)('0' + d[i]);
        digits[15] = 0;
        ui_clear();
        ui_center(20, "NESNET V1", 2, 0xFFFFD040);
        ui_center(60, "ESCRIBE EL CODIGO DEL HOST", 1, 0xFFFFFFFF);
        for (i = 0; i < 15; i++) {
            char c[2] = { digits[i], 0 };
            ui_text(28 + i * 14, 100, c, 2, i == pos ? 0xFFFFFF40 : 0xFFFFFFFF);
        }
        ui_text(28 + pos * 14, 118, "-", 2, 0xFFFFFF40);
        snprintf(line, sizeof line, "DIGITO %d DE 15", pos + 1);
        ui_center(140, line, 1, 0xFFC0C0FF);
        ui_center(170, "ARRIBA/ABAJO: CAMBIAR   IZQ/DER: MOVER", 1, 0xFF8080A0);
        ui_center(184, "START: CONECTAR    O: CANCELAR", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Modos                                                               */
/* ------------------------------------------------------------------ */
static void net_close(void)
{
    if (g_net >= 0) { closesocket(g_net); g_net = -1; }
    g_rxlen = 0;
}

static int run_online(int is_host, int D)
{
    int ok;
    if (!core_load()) return 0;
    ok = session_loop(is_host ? 0 : 1, D, g_maxframes);
    core_unload();
    net_close();
    return ok;
}

static int run_host(void)
{
    uint32_t ip = 0;
    char code[20], l2[48];
    int lfd, D = 0;

    net_ensure();
    g_stage = "buscando-ip";
    ui_show("CREANDO SALA...", "BUSCANDO TU IP PUBLICA", NULL);
    if (g_cfg.public_ip[0] && parse_ip(g_cfg.public_ip, &ip)) { /* IP fijada a mano */ }
    else if (!get_public_ip(&ip)) { g_err = "NO PUDE OBTENER TU IP PUBLICA"; return 0; }
    code_encode(ip, g_cfg.port, code);
    logf_("sala creada: ip=%u.%u.%u.%u puerto=%d codigo=%s",
          (unsigned)(ip >> 24), (unsigned)((ip >> 16) & 255), (unsigned)((ip >> 8) & 255), (unsigned)(ip & 255),
          g_cfg.port, code);

    lfd = tcp_listen(g_cfg.port);
    if (lfd < 0) { g_err = "NO PUDE ABRIR EL PUERTO"; return 0; }

    snprintf(l2, sizeof l2, "PUERTO %d", g_cfg.port);
    g_stage = "esperando-amigo";
    for (;;) {
        uint16_t e;
        pump();
        if (!g_running) { closesocket(lfd); return 1; }
        e = ui_edges();
        if (e & UI_CANCEL) { closesocket(lfd); g_err = ""; return 1; }
        ui_clear();
        ui_center(20, "NESNET V1", 2, 0xFFFFD040);
        ui_center(64, "TU CODIGO DE SALA:", 1, 0xFFFFFFFF);
        ui_center(84, code, 2, 0xFFFFFF40);
        ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
        ui_center(136, l2, 1, 0xFFC0C0FF);
        ui_center(170, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
        ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
        present();
        {
            int r = fd_wait(lfd, POLLIN, 0);
            if (r > 0) {
                int c = accept(lfd, NULL, NULL);
                if (c >= 0) { g_net = c; sock_nodelay(c); break; }
            }
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
        }
    }
    closesocket(lfd);
    ui_show("AMIGO CONECTADO", "MIDIENDO LATENCIA...", NULL);
    if (!handshake_host(&D)) { net_close(); return 0; }
    return run_online(1, D);
}

static int run_client(void)
{
    char code[20];
    uint32_t ip;
    int port, D = 0;

    if (g_cfg.code[0]) snprintf(code, sizeof code, "%s", g_cfg.code);
    else if (!ui_enter_code(code)) { g_err = ""; return 1; }

    if (!code_decode(code, &ip, &port)) { g_err = "CODIGO INVALIDO"; return 0; }
    net_ensure();
    g_stage = "conectando";
    {
        char l2[48];
        snprintf(l2, sizeof l2, "%u.%u.%u.%u:%d", (unsigned)(ip >> 24), (unsigned)((ip >> 16) & 255),
                 (unsigned)((ip >> 8) & 255), (unsigned)(ip & 255), port);
        ui_show("CONECTANDO...", l2, NULL);
    }
    g_net = tcp_connect(ip, port, 10000);
    if (g_net < 0) { g_err = "NO PUDE CONECTAR CON EL HOST"; return 0; }
    ui_show("CONECTADO", "SINCRONIZANDO...", NULL);
    if (!handshake_client(&D)) { net_close(); return 0; }
    return run_online(0, D);
}

static int run_solo(void)
{
    if (!core_load()) return 0;
    session_loop(-1, 0, g_maxframes);
    core_unload();
    return 1;
}

/* ------------------------------------------------------------------ */
/* Programa                                                            */
/* ------------------------------------------------------------------ */
static int app_main(const char *argv0)
{
    int choice = -1, from_cfg;

    if (argv0) {
        const char *s = strrchr(argv0, '/');
        if (s && s > argv0) {
            size_t n = (size_t)(s - argv0);
            if (n < sizeof g_dir) { memcpy(g_dir, argv0, n); g_dir[n] = 0; }
        }
    }
    {
        char p[300];
        snprintf(p, sizeof p, "%s/nesnet.log", g_dir);
        g_log = fopen(p, "w");
    }
    logf_("NesNet v1 - dir=%s", g_dir);
    cfg_load();

    if (!read_whole_file(g_cfg.rom, &g_rom, &g_romsz)) {
        char l2[80];
        logf_("no se pudo leer la ROM: %s", g_cfg.rom);
        snprintf(l2, sizeof l2, "PON LA ROM EN: %s", g_dir);
        ui_message("NO ENCUENTRO LA ROM (rom.nes)", l2, 600);
        return 1;
    }
    g_romcrc = crc32_buf(g_rom, g_romsz);
    logf_("ROM %s  %u bytes  crc32=%08X", g_cfg.rom, (unsigned)g_romsz, (unsigned)g_romcrc);

    core_boot();

    from_cfg = g_cfg.mode[0] != 0;
    while (g_running) {
        int ok = 1;
        if (from_cfg) {
            choice = !strcmp(g_cfg.mode, "host") ? MODE_HOST : !strcmp(g_cfg.mode, "client") ? MODE_JOIN :
                     !strcmp(g_cfg.mode, "local") ? MODE_SOLO : -1;
            from_cfg = 0;                 /* despues de la primera vez, usa el menu */
        }
        if (choice < 0) choice = ui_menu();
        if (choice < 0) break;
        logf_("modo elegido: %s", choice == MODE_SOLO ? "SOLO (2 mandos)" : choice == MODE_HOST ? "CREAR SALA (host)" : "UNIRSE (cliente)");
        g_err = "";
        if (choice == MODE_SOLO) ok = run_solo();
        else if (choice == MODE_HOST) ok = run_host();
        else ok = run_client();
        choice = -1;
#ifdef NESNET_HOST
        if (g_maxframes) g_running = 0;       /* pruebas: una sola sesion */
#endif
        if (!ok || g_err[0]) {
            logf_("fin con error: %s", g_err);
            if (g_err[0]) ui_message(g_err, "X: VOLVER AL MENU", 600);
        }
    }
    logf_("salida");
    retro_deinit();
    if (g_log) fclose(g_log);
    return 0;
}

#ifdef NESNET_PS3
int main(int argc, const char *argv[])
{
    platform_init();
    return app_main(argc > 0 ? argv[0] : NULL);
}
#endif

#ifdef NESNET_HOST
/* Pruebas en PC:
 *   nesnet_test ROM local   FRAMES            -> sin retraso, 2 jugadores simulados
 *   nesnet_test ROM ref     FRAMES D          -> referencia local con retraso D
 *   nesnet_test ROM host    FRAMES PUERTO [D] -> host de red
 *   nesnet_test ROM client  FRAMES PUERTO     -> cliente de red (127.0.0.1)
 *   nesnet_test --ui DIR                      -> vuelca pantallas de la interfaz en PPM
 */
static void dump_ppm(const char *path)
{
    FILE *f = fopen(path, "wb");
    int i;
    if (!f) return;
    fprintf(f, "P6\n%d %d\n255\n", SCR_W, SCR_H);
    for (i = 0; i < SCR_W * SCR_H; i++) {
        uint8_t px[3] = { (uint8_t)(g_fb[i] >> 16), (uint8_t)(g_fb[i] >> 8), (uint8_t)g_fb[i] };
        fwrite(px, 1, 3, f);
    }
    fclose(f);
}

int main(int argc, char **argv)
{
    const char *mode;
    uint32_t frames;
    int D = 6, port = 7777, ok = 1;

    if (argc >= 3 && !strcmp(argv[1], "--ui")) {
        char p[300];
        static const char *items[3] = { "CREAR SALA (HOST)", "UNIRSE A UNA SALA", "SOLO - 2 MANDOS" };
        int i;
        ui_clear();
        ui_center(20, "NESNET V1", 2, 0xFFFFD040);
        ui_center(46, "NES CON NETPLAY PARA PS3", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == 0 ? ">" : " ", items[i]);
            ui_center(90 + i * 22, line, 1, i == 0 ? 0xFFFFFFFF : 0xFF8080A0);
        }
        snprintf(p, sizeof p, "%s/menu.ppm", argv[2]); dump_ppm(p);
        {
            char code[20];
            code_encode(((uint32_t)181 << 24) | (45u << 16) | (200u << 8) | 17u, 7777, code);
            ui_clear();
            ui_center(20, "NESNET V1", 2, 0xFFFFD040);
            ui_center(64, "TU CODIGO DE SALA:", 1, 0xFFFFFFFF);
            ui_center(84, code, 2, 0xFFFFFF40);
            ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
            ui_center(136, "PUERTO 7777", 1, 0xFFC0C0FF);
            ui_center(170, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
            ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
            snprintf(p, sizeof p, "%s/host.ppm", argv[2]); dump_ppm(p);
        }
        return 0;
    }

    if (argc < 4) { fprintf(stderr, "uso: %s ROM modo FRAMES [...]\n", argv[0]); return 2; }
    mode = argv[2];
    frames = (uint32_t)atoi(argv[3]);
    if (argc > 4) port = atoi(argv[4]);
    g_maxframes = frames;
    signal(SIGPIPE, SIG_IGN);
    if (!strcmp(mode, "app")) {
        /* flujo real: lee DIR/config.txt y ejecuta app_main (argv[4] = carpeta) */
        char exe[300];
        int rc;
        snprintf(exe, sizeof exe, "%s/EBOOT.BIN", argv[4]);
        if (getenv("NESNET_UI")) g_ui_script = getenv("NESNET_UI");
        rc = app_main(exe);
        printf("RESULT mode=app frames=%u hash=%08X desyncs=%d rc=%d\n", (unsigned)g_frames_done,
               (unsigned)g_run_hash, g_desyncs, rc);
        return rc;
    }
    snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s", argv[1]);
    g_cfg.port = port;
    if (!read_whole_file(argv[1], &g_rom, &g_romsz)) { fprintf(stderr, "no puedo leer la ROM\n"); return 2; }
    g_romcrc = crc32_buf(g_rom, g_romsz);
    snprintf(g_dir, sizeof g_dir, "/tmp");
    core_boot();

    if (!strcmp(mode, "local")) {
        core_load(); session_loop(-1, 0, frames); core_unload();
    } else if (!strcmp(mode, "ref")) {
        D = argc > 4 ? atoi(argv[4]) : 6;
        core_load(); session_loop(-2, D, frames); core_unload();
    } else if (!strcmp(mode, "host")) {
        int lfd = tcp_listen(port);
        if (lfd < 0) { fprintf(stderr, "no puedo escuchar\n"); return 2; }
        if (argc > 5) g_cfg.delay = atoi(argv[5]);
        g_net = accept(lfd, NULL, NULL);
        closesocket(lfd);
        sock_nodelay(g_net);
        ok = handshake_host(&D);
        if (ok) ok = run_online(1, D) ;
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "client")) {
        int tries;
        for (tries = 0; tries < 50 && g_net < 0; tries++) {
            g_net = tcp_connect(0x7F000001u, port, 2000);
            if (g_net < 0) sleep_ms(100);
        }
        if (g_net < 0) { fprintf(stderr, "no pude conectar\n"); return 2; }
        ok = handshake_client(&D);
        if (ok) ok = run_online(0, D);
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "reload")) {
        /* sesion solo, descarga, y luego sesion de referencia: debe dar igual que un proceso nuevo */
        core_load(); session_loop(-1, 0, 300); core_unload();
        D = 6;
        core_load(); session_loop(-2, D, frames); core_unload();
    } else if (!strcmp(mode, "codetest")) {
        char c[20]; uint32_t ip; int p, n = 0, bad = 0;
        uint32_t t;
        for (t = 0; t < 200000; t++) {
            uint32_t a = t * 2654435761u; int pt = 1 + (int)(t * 40503u % 65535);
            code_encode(a ? a : 1, pt, c);
            if (!code_decode(c, &ip, &p) || ip != (a ? a : 1) || p != pt) bad++;
            n++;
        }
        printf("codetest n=%d bad=%d\n", n, bad);
        return bad != 0;
    }
    printf("RESULT mode=%s frames=%u hash=%08X desyncs=%d D=%d first_desync=%d\n", mode,
           (unsigned)g_frames_done, (unsigned)g_run_hash, g_desyncs, D,
           g_first_desync == NO_FRAME ? -1 : (int)g_first_desync);
    return ok ? 0 : 1;
}
#endif
