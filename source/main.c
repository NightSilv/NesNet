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
    int      res;             /* 0 = la de la TV, 720 = forzar 720p */
    int      render;          /* 0 = GPU (escalado), 1 = CPU directo (sin transferencia GPU) */
    int      zoom;            /* 0 = automatico */
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
        else if (!strcmp(k, "res"))       g_cfg.res = !strcmp(v, "720") ? 720 : 0;
        else if (!strcmp(k, "render"))    g_cfg.render = !strcmp(v, "cpu") ? 1 : 0;
        else if (!strcmp(k, "zoom"))      g_cfg.zoom = atoi(v);
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
    {
        int guard = 0;
        while (*(vu32 *)gcmGetLabelAddress(GCM_LABEL_INDEX) != g_label) {
            usleep(30);
            if ((++guard & 0x3FF) == 0) pump();
            if (guard > 100000) { logf_("AVISO: gpu_wait_finish agotó el tiempo (3 s)"); break; }
        }
    }
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
    logf_("video: modo de la TV resolucion id=%d", (int)state.displayMode.resolution);
    {
        int rid = (int)state.displayMode.resolution;
        if (g_cfg.res == 720 && rid != VIDEO_RESOLUTION_720) {
            if (videoGetResolutionAvailability(VIDEO_PRIMARY, VIDEO_RESOLUTION_720, VIDEO_ASPECT_AUTO, 0) == 1) {
                rid = VIDEO_RESOLUTION_720;
                logf_("video: forzando 720p (res=720)");
            } else logf_("AVISO: la TV no ofrece 720p, sigo con la resolucion actual");
        }
        videoGetResolution(rid, &res);
        state.displayMode.resolution = (u8)rid;
    }

    memset(&vconfig, 0, sizeof vconfig);
    vconfig.resolution = state.displayMode.resolution;
    vconfig.format     = VIDEO_BUFFER_FORMAT_XRGB;
    vconfig.pitch      = res.width * sizeof(u32);

    gpu_wait_idle();
    videoConfigure(0, &vconfig, NULL, 0);
    videoGetState(0, 0, &state);
    logf_("video: configurado %ux%u", (unsigned)res.width, (unsigned)res.height);

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
    if (g_cfg.render && g_zoom > 2) g_zoom = 2;      /* escribir a mano en la VRAM es lento: x2 maximo */
    if (g_cfg.zoom > 0 && g_cfg.zoom < g_zoom) g_zoom = g_cfg.zoom;
    if (g_zoom < 1) g_zoom = 1;
    if (g_zoom > 4) g_zoom = 4;
    memset(g_cbuf[0], 0, g_dh * g_pitch);
    memset(g_cbuf[1], 0, g_dh * g_pitch);
    logf_("video: zoom x%d  render=%s", g_zoom, g_cfg.render ? "cpu" : "gpu");

    gpu_set_target(g_cur);
}

static void gpu_flip(void)
{
    if (!g_first) {
        int guard = 0;
        while (gcmGetFlipStatus() != 0) {
            usleep(200);
            if ((++guard & 0xFF) == 0) pump();
            if (guard > 15000) { logf_("AVISO: el flip no termino en 3 s"); break; }
        }
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

    if (g_cfg.render) {
        /* Modo CPU: sin transferencia ni clear ni blend de la GPU; escribo directo en el buffer de pantalla */
        static u32 row[SCR_W * 4];
        int z = g_zoom, x, y, k;
        u32 *dst = g_cbuf[g_cur] + ((g_dh - SCR_H * z) / 2) * g_dw + (g_dw - SCR_W * z) / 2;
        if (!g_first) {
            int guard = 0;
            while (gcmGetFlipStatus() != 0 && guard++ < 15000) usleep(200);
        }
        g_stage = "cpu-copia";
        for (y = 0; y < SCR_H; y++) {
            const u32 *src = g_fb + y * SCR_W;
            for (x = 0; x < SCR_W; x++) for (k = 0; k < z; k++) row[x * z + k] = src[x];
            for (k = 0; k < z; k++) { memcpy(dst, row, SCR_W * z * 4); dst += g_dw; }
        }
        return;
    }

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

    memset(&scale,
