/*
 * NesNet v1 - emulador de NES con netplay para PS3
 *   PSL1GHT + nucleo libretro FCEUmm
 *
 * Netplay: lockstep con retraso fijo (delay) sobre TCP, 2 jugadores.
 *   - El host crea la sala y recibe un CODIGO NUMERICO (10 digitos) que codifica
 *     su IP publica (el puerto es el de config.txt, 7777 por defecto, igual en los dos).
 *     El cliente escribe ese codigo con el mando.
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
#include <dirent.h>
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
#include <audio/audio.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <net/net.h>
#include <net/netdb.h>
#include <net/netctl.h>
#include <sysmodule/sysmodule.h>
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
/* v1.9.1: el mensaje M_RESET (reinicio sincronizado desde el menu R2) cambia el protocolo: una v1.9.1 y una v1.9
 * se rechazan entre si con el aviso "VERSIONES DISTINTAS DE NESNET" en vez de desincronizarse. */
/* v1.9.2: el mensaje M_GAME (el host cambia de juego desde R2) vuelve a cambiar el protocolo: 1vs1 = 5, modo de 4 = 6. */
/* v1.9.4: el mensaje M_STATE (el host carga un estado guardado y se lo manda al amigo) cambia el protocolo otra vez: 1vs1 = 7, modo de 4 = 8.
 * Una v1.9.3 y una v1.9.4 se rechazan en el saludo en vez de desincronizarse. */
/* v1.9.6: captura de pantalla con L2 (local, no toca la red): el protocolo NO cambia, 1vs1 = 7 y modo de 4 = 8 como en la v1.9.5. */
#define PROTO_VER      7
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
#define MODE_ROM       3      /* v1.7: opcion "ELEGIR ROM" del menu (no es un modo de juego) */
#define MODE_FOUR      4      /* v1.8: opcion "MULTIJUGADOR DE 4" (submenu con host y unirse) */
#define MODE_OPT       5      /* v1.8.2: opcion "OPCIONES" del menu (pantalla y mandos; no es un modo de juego) */

/* v1.8: el modo de 4 jugadores es una COPIA aparte del 1vs1 y habla otro protocolo, asi un host de 1vs1
 * nunca acepta a alguien del modo de 4 (ni al reves). Desde la v1.9.2: 1vs1 = 5, modo de 4 = 6. */
#define PROTO_VER4     8

/* FCEUmm define su "GAMEPAD" como subclase 1 del mando (RETRO_DEVICE_GAMEPAD en su libretro.c) */
#define NES_DEV_GAMEPAD RETRO_DEVICE_SUBCLASS(RETRO_DEVICE_JOYPAD, 1)

/* v1.7: selector de ROMs. Las ROMs van en USRDIR/roms/ y se reconocen por su cabecera, no por el nombre */
#define ROM_MAX        256
#define ROM_NAMELEN    96

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
    char     rom[420];        /* v1.7: ruta de la ROM elegida en el selector (ya no sale de config.txt) */
    char     mode[16];        /* "", "host", "client", "local" */
    char     code[32];
    char     public_ip[32];
    int      delay;           /* 0 = automatico */
    int      port;
    int      res;             /* 0 = la de la TV, 720 = forzar 720p */
    int      render;          /* 0 = GPU (escalado), 1 = CPU directo (sin transferencia GPU) */
    int      zoom;            /* 0 = automatico */
    int      audio;           /* 1 = con sonido (por defecto), 0 = sin sonido */
    int      upnp;            /* v1.6: 1 = el host abre el puerto por UPnP (por defecto), 0 = no */
} Config;

static Config   g_cfg;
static char     g_dir[256] = "/dev_hdd0/game/NESN00001/USRDIR";
static FILE    *g_log;
static int      g_running = 1;
static const char *g_err = "";

static uint8_t *g_rom;                    /* NULL = ninguna ROM elegida (stand-by) */
static size_t   g_romsz;
static uint32_t g_romcrc;
static char     g_rom_name[ROM_NAMELEN];  /* v1.7: nombre del archivo de la ROM elegida */
static int      g_menu_sel;               /* v1.7: opcion marcada del menu principal */

static uint32_t g_fb[SCR_W * SCR_H];      /* lienzo ARGB */
static uint16_t g_pad[4];                 /* entrada NES que ve el nucleo (v1.8: 4 puertos; el 1vs1 solo usa 0 y 1) */
static int      g_four;                   /* v1.8: 1 = partida de 4 jugadores (Four Score), 0 = 1vs1 como siempre */
static unsigned g_pixfmt = RETRO_PIXEL_FORMAT_RGB565;
static uint32_t g_frame_crc;
static int      g_vid_fresh;              /* v1.9.6: 1 = el nucleo entrego imagen nueva en este cuadro (g_fb esta limpia, sin textos encima) */
static int      g_shot_req;               /* v1.9.6: 1 = hay una captura pedida (L2); se toma justo despues de emular el cuadro */
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
    g_cfg.port = DEFAULT_PORT;
    g_cfg.res = 720;                      /* v1.3: por defecto 720p (probado en la PS3) */
    g_cfg.audio = 1;                      /* v1.5: sonido activado por defecto (audio=off o R2 al abrir lo apaga) */
    g_cfg.render = 1;                     /* v1.3: por defecto dibujo por CPU, sin la GPU (la ruta GPU se colgo 3 veces) */
    g_cfg.upnp = 1;                       /* v1.6: abrir el puerto por UPnP (upnp=off en config.txt lo apaga) */
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
        if (!strcmp(k, "rom")) { /* v1.7: la ROM ya no se lee de aqui, se elige en el menu (carpeta roms) */ }
        else if (!strcmp(k, "mode"))      snprintf(g_cfg.mode, sizeof g_cfg.mode, "%s", v);
        else if (!strcmp(k, "code"))      snprintf(g_cfg.code, sizeof g_cfg.code, "%s", v);
        else if (!strcmp(k, "public_ip")) snprintf(g_cfg.public_ip, sizeof g_cfg.public_ip, "%s", v);
        else if (!strcmp(k, "delay"))     g_cfg.delay = atoi(v);
        else if (!strcmp(k, "port"))      g_cfg.port = atoi(v);
        else if (!strcmp(k, "res"))       { if (!strcmp(v, "auto")) g_cfg.res = 0; else if (!strcmp(v, "720")) g_cfg.res = 720; }
        else if (!strcmp(k, "render"))    { if (!strcmp(v, "gpu")) g_cfg.render = 0; else if (!strcmp(v, "cpu")) g_cfg.render = 1; }
        else if (!strcmp(k, "zoom"))      g_cfg.zoom = atoi(v);
        else if (!strcmp(k, "audio"))     { if (!strcmp(v, "off")) g_cfg.audio = 0; else if (!strcmp(v, "on")) g_cfg.audio = 1; }
        else if (!strcmp(k, "upnp"))      { if (!strcmp(v, "off")) g_cfg.upnp = 0; else if (!strcmp(v, "on")) g_cfg.upnp = 1; }
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


/* ------------------------------------------------------------------ */
/* v1.9.7: menus en 1280x720 con fuente DejaVu Sans Bold y fondo mosaico.
 * Solo es DIBUJO de menus: no toca la red ni el juego. Los menus siguen llamando a ui_text / ui_center / ui_clear con las
 * coordenadas del lienzo viejo (256x240); mientras g_hr_on = 1 esas llamadas se traducen a este lienzo de 1280x720
 * (x5, y3). El modo GPU (render = 0), el AJUSTE DE IMAGEN y lo que se dibuja en pleno juego siguen con el dibujo de siempre. */
/* ------------------------------------------------------------------ */
#define HR_W 1280
#define HR_H 720
#define HC_RED   0xFFDE263Au
#define HC_WHITE 0xFFF4F6FFu
#define HC_DIM   0xFF96A8DEu
#define HC_GRID  0xFF2C54BEu
#define HC_GREEN 0xFF6EDC96u
#define HC_AMBER 0xFFFFBE50u
#define HC_YEL   0xFFFFE246u
#define HC_MUTE  0xFF6E7CAAu
#define HC_SHAD  0xFF02040Eu
/* ---- v1.9.7: fuente DejaVu Sans Bold (licencia libre Bitstream Vera / DejaVu), 5 tamanos, alfa de 4 bits, generada fuera de la PS3 ---- */
typedef struct { uint16_t cp; uint8_t adv; int8_t bx, by; uint8_t w, h; uint32_t off; } FGlyph;
enum { FS_S, FS_M, FS_L, FS_H, FS_X, FS_N };        /* 22, 28, 34, 46 y 88 px (alto) */
static const int fg_asc[FS_N] = { 21, 26, 32, 43, 82 };
static const int fg_start[FS_N + 1] = { 0, 113, 226, 339, 399, 415 };
#define FG_NDATA 127163
static const FGlyph fg_tab[415] = {
 {32,8,0,0,0,0,0u},{33,10,0,-16,10,16,0u},{34,11,0,-16,11,16,80u},{35,18,0,-16,18,16,168u},{36,15,0,-16,15,19,312u},
 {37,22,0,-16,22,16,455u},{38,19,0,-16,19,16,631u},{39,7,0,-16,7,16,783u},{40,10,0,-17,10,20,839u},
 {41,10,0,-17,10,20,939u},{42,12,0,-16,12,16,1039u},{43,18,0,-13,18,13,1135u},{44,8,0,-4,8,7,1252u},
 {45,9,0,-8,9,8,1280u},{46,8,0,-4,8,4,1316u},{47,8,0,-16,9,18,1332u},{48,15,0,-16,15,16,1413u},
 {49,15,0,-16,15,16,1533u},{50,15,0,-16,15,16,1653u},{51,15,0,-16,15,16,1773u},{52,15,0,-16,15,16,1893u},
 {53,15,0,-16,15,16,2013u},{54,15,0,-16,15,16,2133u},{55,15,0,-16,15,16,2253u},{56,15,0,-16,15,16,2373u},
 {57,15,0,-16,15,16,2493u},{58,9,0,-12,9,12,2613u},{59,9,0,-12,9,15,2667u},{60,18,0,-13,18,13,2735u},
 {61,18,0,-11,18,11,2852u},{62,18,0,-13,18,13,2951u},{63,13,0,-16,13,16,3068u},{64,22,0,-16,22,19,3172u},
 {65,17,0,-16,17,16,3381u},{66,17,0,-16,17,16,3517u},{67,16,0,-16,16,16,3653u},{68,18,0,-16,18,16,3781u},
 {69,15,0,-16,15,16,3925u},{70,15,0,-16,15,16,4045u},{71,18,0,-16,18,16,4165u},{72,18,0,-16,18,16,4309u},
 {73,8,0,-16,8,16,4453u},{74,8,-2,-16,10,20,4517u},{75,17,0,-16,18,16,4617u},{76,14,0,-16,14,16,4761u},
 {77,22,0,-16,22,16,4873u},{78,18,0,-16,18,16,5049u},{79,19,0,-16,19,16,5193u},{80,16,0,-16,16,16,5345u},
 {81,19,0,-16,19,19,5473u},{82,17,0,-16,17,16,5654u},{83,16,0,-16,16,16,5790u},{84,15,0,-16,15,16,5918u},
 {85,18,0,-16,18,16,6038u},{86,17,0,-16,17,16,6182u},{87,24,0,-16,24,16,6318u},{88,17,0,-16,17,16,6510u},
 {89,16,-1,-16,18,16,6646u},{90,16,0,-16,16,16,6790u},{91,10,0,-17,10,20,6918u},{92,8,0,-16,9,18,7018u},
 {93,10,0,-17,10,20,7099u},{94,18,0,-16,18,16,7199u},{95,11,0,0,11,5,7343u},{96,11,0,-18,11,18,7371u},
 {97,15,0,-12,15,12,7470u},{98,16,0,-17,16,17,7560u},{99,13,0,-12,13,12,7696u},{100,16,0,-17,16,17,7774u},
 {101,15,0,-12,15,12,7910u},{102,10,0,-17,10,17,8000u},{103,16,0,-12,16,17,8085u},{104,16,0,-17,16,17,8221u},
 {105,8,0,-17,8,17,8357u},{106,8,-1,-17,9,22,8425u},{107,15,0,-17,16,17,8524u},{108,8,0,-17,8,17,8660u},
 {109,23,0,-12,23,12,8728u},{110,16,0,-12,16,12,8866u},{111,15,0,-12,15,12,8962u},{112,16,0,-12,16,17,9052u},
 {113,16,0,-12,16,17,9188u},{114,11,0,-12,11,12,9324u},{115,13,0,-12,13,12,9390u},{116,11,0,-15,11,15,9468u},
 {117,16,0,-12,16,12,9551u},{118,14,0,-12,15,12,9647u},{119,20,0,-12,20,12,9737u},{120,14,0,-12,14,12,9857u},
 {121,14,0,-12,14,17,9941u},{122,13,0,-12,13,12,10060u},{123,16,0,-17,16,20,10138u},{124,8,0,-17,8,22,10298u},
 {125,16,0,-17,16,20,10386u},{126,18,0,-10,18,10,10546u},{161,10,0,-12,10,16,10636u},{176,11,0,-16,11,16,10716u},
 {183,8,0,-10,8,10,10804u},{191,13,0,-12,13,17,10844u},{193,17,0,-21,17,21,10955u},{201,15,0,-21,15,21,11134u},
 {205,8,0,-21,8,21,11292u},{209,18,0,-21,18,21,11376u},{211,19,0,-21,19,21,11565u},{218,18,0,-21,18,21,11765u},
 {220,18,0,-21,18,21,11954u},{225,15,0,-18,15,18,12143u},{233,15,0,-18,15,18,12278u},{237,8,0,-18,9,18,12413u},
 {241,16,0,-18,16,18,12494u},{243,15,0,-18,15,18,12638u},{250,16,0,-18,16,18,12773u},{252,16,0,-17,16,17,12917u},
 {32,10,0,0,0,0,0u},{33,13,0,-20,13,20,13053u},{34,15,0,-20,15,20,13183u},{35,23,0,-20,23,20,13333u},
 {36,19,0,-21,19,25,13563u},{37,28,0,-20,28,20,13801u},{38,24,0,-20,24,20,14081u},{39,9,0,-20,9,20,14321u},
 {40,13,0,-21,13,25,14411u},{41,13,0,-21,13,25,14574u},{42,15,0,-20,15,20,14737u},{43,23,0,-17,23,17,14887u},
 {44,11,0,-5,11,9,15083u},{45,12,0,-10,12,10,15133u},{46,11,0,-5,11,5,15193u},{47,10,0,-20,11,23,15221u},
 {48,19,0,-20,19,20,15348u},{49,19,0,-20,19,20,15538u},{50,19,0,-20,19,20,15728u},{51,19,0,-20,19,20,15918u},
 {52,19,0,-20,19,20,16108u},{53,19,0,-20,19,20,16298u},{54,19,0,-20,19,20,16488u},{55,19,0,-20,19,20,16678u},
 {56,19,0,-20,19,20,16868u},{57,19,0,-20,19,20,17058u},{58,11,0,-15,11,15,17248u},{59,11,0,-15,11,19,17331u},
 {60,23,0,-17,23,17,17436u},{61,23,0,-13,23,13,17632u},{62,23,0,-17,23,17,17782u},{63,16,0,-20,16,20,17978u},
 {64,28,0,-20,28,25,18138u},{65,22,0,-20,22,20,18488u},{66,21,0,-20,21,20,18708u},{67,21,0,-20,21,20,18918u},
 {68,23,0,-20,23,20,19128u},{69,19,0,-20,19,20,19358u},{70,19,0,-20,19,20,19548u},{71,23,0,-20,23,20,19738u},
 {72,23,0,-20,23,20,19968u},{73,10,0,-20,10,20,20198u},{74,10,-2,-20,12,26,20298u},{75,22,0,-20,23,20,20454u},
 {76,18,0,-20,18,20,20684u},{77,28,0,-20,28,20,20864u},{78,23,0,-20,23,20,21144u},{79,24,0,-20,24,20,21374u},
 {80,21,0,-20,21,20,21614u},{81,24,0,-20,24,24,21824u},{82,22,0,-20,22,20,22112u},{83,20,0,-20,20,20,22332u},
 {84,19,0,-20,19,20,22532u},{85,23,0,-20,23,20,22722u},{86,22,0,-20,22,20,22952u},{87,31,0,-20,31,20,23172u},
 {88,22,0,-20,22,20,23482u},{89,20,-1,-20,22,20,23702u},{90,20,0,-20,20,20,23922u},{91,13,0,-21,13,25,24122u},
 {92,10,0,-20,11,23,24285u},{93,13,0,-21,13,25,24412u},{94,23,0,-20,23,20,24575u},{95,14,0,0,14,7,24805u},
 {96,14,0,-22,14,22,24854u},{97,19,0,-15,19,15,25008u},{98,20,0,-21,20,21,25151u},{99,17,0,-15,17,15,25361u},
 {100,20,0,-21,20,21,25489u},{101,19,0,-15,19,15,25699u},{102,12,0,-21,13,21,25842u},{103,20,0,-15,20,21,25979u},
 {104,20,0,-21,20,21,26189u},{105,10,0,-21,10,21,26399u},{106,10,-1,-21,11,27,26504u},{107,19,0,-21,20,21,26653u},
 {108,10,0,-21,10,21,26863u},{109,29,0,-15,29,15,26968u},{110,20,0,-15,20,15,27186u},{111,19,0,-15,19,15,27336u},
 {112,20,0,-15,20,21,27479u},{113,20,0,-15,20,21,27689u},{114,14,0,-15,14,15,27899u},{115,17,0,-15,17,15,28004u},
 {116,13,0,-20,13,20,28132u},{117,20,0,-15,20,15,28262u},{118,18,0,-15,18,15,28412u},{119,26,0,-15,26,15,28547u},
 {120,18,0,-15,18,15,28742u},{121,18,0,-15,18,21,28877u},{122,16,0,-15,16,15,29066u},{123,20,0,-21,20,26,29186u},
 {124,10,0,-21,10,28,29446u},{125,20,0,-21,20,26,29586u},{126,23,0,-12,23,12,29846u},{161,13,0,-15,13,20,29984u},
 {176,14,0,-21,14,21,30114u},{183,11,0,-12,11,12,30261u},{191,16,0,-15,16,21,30327u},{193,22,0,-26,22,26,30495u},
 {201,19,0,-26,19,26,30781u},{205,10,0,-26,10,26,31028u},{209,23,0,-26,23,26,31158u},{211,24,0,-26,24,26,31457u},
 {218,23,0,-26,23,26,31769u},{220,23,0,-26,23,26,32068u},{225,19,0,-22,19,22,32367u},{233,19,0,-22,19,22,32576u},
 {237,10,0,-22,11,22,32785u},{241,20,0,-22,20,22,32906u},{243,19,0,-22,19,22,33126u},{250,20,0,-22,20,22,33335u},
 {252,20,0,-22,20,22,33555u},{32,12,0,0,0,0,0u},{33,16,0,-25,16,25,33775u},{34,18,0,-25,18,25,33975u},
 {35,28,0,-25,28,25,34200u},{36,24,0,-26,24,31,34550u},{37,34,0,-25,34,25,34922u},{38,30,0,-25,30,25,35347u},
 {39,10,0,-25,10,25,35722u},{40,16,0,-26,16,30,35847u},{41,16,0,-26,16,30,36087u},{42,18,0,-25,18,25,36327u},
 {43,28,0,-22,28,22,36552u},{44,13,0,-6,13,11,36860u},{45,14,0,-13,14,13,36932u},{46,13,0,-6,13,6,37023u},
 {47,12,0,-25,13,28,37062u},{48,24,0,-25,24,25,37244u},{49,24,0,-25,24,25,37544u},{50,24,0,-25,24,25,37844u},
 {51,24,0,-25,24,25,38144u},{52,24,0,-25,24,25,38444u},{53,24,0,-25,24,25,38744u},{54,24,0,-25,24,25,39044u},
 {55,24,0,-25,24,25,39344u},{56,24,0,-25,24,25,39644u},{57,24,0,-25,24,25,39944u},{58,14,0,-19,14,19,40244u},
 {59,14,0,-19,14,24,40377u},{60,28,0,-20,28,20,40545u},{61,28,0,-17,28,17,40825u},{62,28,0,-20,28,20,41063u},
 {63,20,0,-25,20,25,41343u},{64,34,0,-25,34,30,41593u},{65,26,0,-25,27,25,42103u},{66,26,0,-25,26,25,42441u},
 {67,25,0,-25,25,25,42766u},{68,28,0,-25,28,25,43079u},{69,23,0,-25,23,25,43429u},{70,23,0,-25,23,25,43717u},
 {71,28,0,-25,28,25,44005u},{72,28,0,-25,28,25,44355u},{73,13,0,-25,13,25,44705u},{74,13,-2,-25,15,32,44868u},
 {75,26,0,-25,28,25,45108u},{76,22,0,-25,22,25,45458u},{77,34,0,-25,34,25,45733u},{78,28,0,-25,28,25,46158u},
 {79,29,0,-25,29,25,46508u},{80,25,0,-25,25,25,46871u},{81,29,0,-25,29,30,47184u},{82,26,0,-25,26,25,47619u},
 {83,24,0,-25,24,25,47944u},{84,23,0,-25,24,25,48244u},{85,28,0,-25,28,25,48544u},{86,26,0,-25,27,25,48894u},
 {87,38,0,-25,38,25,49232u},{88,26,0,-25,26,25,49707u},{89,25,-1,-25,26,25,50032u},{90,25,0,-25,25,25,50357u},
 {91,16,0,-26,16,30,50670u},{92,12,0,-25,13,28,50910u},{93,16,0,-26,16,30,51092u},{94,28,0,-25,28,25,51332u},
 {95,17,0,0,17,8,51682u},{96,17,0,-27,17,27,51750u},{97,23,0,-19,23,19,51980u},{98,24,0,-26,24,26,52199u},
 {99,20,0,-19,20,19,52511u},{100,24,0,-26,24,26,52701u},{101,23,0,-19,23,19,53013u},{102,15,0,-26,16,26,53232u},
 {103,24,0,-19,24,26,53440u},{104,24,0,-26,24,26,53752u},{105,12,0,-26,12,26,54064u},{106,12,-2,-26,14,33,54220u},
 {107,23,0,-26,24,26,54451u},{108,12,0,-26,12,26,54763u},{109,35,0,-19,35,19,54919u},{110,24,0,-19,24,19,55252u},
 {111,23,0,-19,23,19,55480u},{112,24,0,-19,24,26,55699u},{113,24,0,-19,24,26,56011u},{114,17,0,-19,17,19,56323u},
 {115,20,0,-19,20,19,56485u},{116,16,0,-24,16,24,56675u},{117,24,0,-19,24,19,56867u},{118,22,0,-19,22,19,57095u},
 {119,31,0,-19,31,19,57304u},{120,22,0,-19,22,19,57599u},{121,22,0,-19,22,26,57808u},{122,20,0,-19,20,19,58094u},
 {123,24,0,-26,24,31,58284u},{124,12,0,-26,12,34,58656u},{125,24,0,-26,24,31,58860u},{126,28,0,-15,28,15,59232u},
 {161,16,0,-19,16,25,59442u},{176,17,0,-25,17,25,59642u},{183,13,0,-15,13,15,59855u},{191,20,0,-19,20,26,59953u},
 {193,26,0,-31,27,31,60213u},{201,23,0,-31,23,31,60632u},{205,13,0,-31,13,31,60989u},{209,28,0,-32,28,32,61191u},
 {211,29,0,-31,29,31,61639u},{218,28,0,-31,28,31,62089u},{220,28,0,-31,28,31,62523u},{225,23,0,-27,23,27,62957u},
 {233,23,0,-27,23,27,63268u},{237,12,0,-27,14,27,63579u},{241,24,0,-27,24,27,63768u},{243,23,0,-27,23,27,64092u},
 {250,24,0,-27,24,27,64403u},{252,24,0,-26,24,26,64727u},{32,16,0,0,0,0,0u},{33,21,0,-34,21,34,65039u},
 {37,46,0,-35,46,35,65396u},{40,21,0,-35,21,41,66201u},{41,21,0,-35,21,41,66632u},{43,39,0,-29,39,29,67063u},
 {44,17,0,-9,17,15,67629u},{45,19,0,-17,19,17,67757u},{46,17,0,-9,17,9,67919u},{47,17,0,-34,17,38,67996u},
 {48,32,0,-35,32,35,68319u},{49,32,0,-34,32,34,68879u},{50,32,0,-35,32,35,69423u},{51,32,0,-35,32,35,69983u},
 {52,32,0,-34,32,34,70543u},{53,32,0,-34,32,34,71087u},{54,32,0,-35,32,35,71631u},{55,32,0,-34,32,34,72191u},
 {56,32,0,-35,32,35,72735u},{57,32,0,-35,32,35,73295u},{58,18,0,-25,18,25,73855u},{60,39,0,-27,39,27,74080u},
 {62,39,0,-27,39,27,74607u},{63,27,0,-34,27,34,75134u},{65,36,0,-34,36,34,75593u},{66,35,0,-34,35,34,76205u},
 {67,34,0,-35,34,35,76800u},{68,38,0,-34,38,34,77395u},{69,31,0,-34,31,34,78041u},{70,31,0,-34,31,34,78568u},
 {71,38,0,-35,38,35,79095u},{72,38,0,-34,39,34,79760u},{73,17,0,-34,17,34,80423u},{74,17,-3,-34,20,43,80712u},
 {75,36,0,-34,38,34,81142u},{76,29,0,-34,29,34,81788u},{77,46,0,-34,46,34,82281u},{78,38,0,-34,39,34,83063u},
 {79,39,0,-35,39,35,83726u},{80,34,0,-34,34,34,84409u},{81,39,0,-35,39,42,84987u},{82,35,0,-34,35,34,85806u},
 {83,33,0,-35,33,35,86401u},{84,31,0,-34,32,34,86979u},{85,37,0,-34,37,34,87523u},{86,36,0,-34,36,34,88152u},
 {87,51,0,-34,51,34,88764u},{88,35,0,-34,35,34,89631u},{89,33,-1,-34,35,34,90226u},{90,33,0,-34,33,34,90821u},
 {161,21,0,-25,21,34,91382u},{183,17,0,-20,17,20,91739u},{191,27,0,-25,27,35,91909u},{193,36,0,-42,36,42,92382u},
 {201,31,0,-42,31,42,93138u},{205,17,0,-42,17,42,93789u},{209,38,0,-42,39,42,94146u},{211,39,0,-42,39,42,94965u},
 {218,37,0,-42,37,42,95784u},{220,37,0,-43,37,43,96561u},{32,31,0,0,0,0,0u},{48,61,0,-65,61,66,97357u},
 {49,61,0,-64,61,64,99370u},{50,61,0,-65,61,65,101322u},{51,61,0,-65,61,66,103305u},{52,61,0,-64,61,64,105318u},
 {53,61,0,-64,61,65,107270u},{54,61,0,-65,61,66,109253u},{55,61,0,-64,61,64,111266u},{56,61,0,-65,61,66,113218u},
 {57,61,0,-65,61,66,115231u},{63,51,0,-64,51,64,117244u},{69,60,0,-64,60,64,118876u},{78,74,0,-64,74,64,120796u},
 {83,63,0,-65,63,66,123164u},{84,60,0,-64,60,64,125243u},
};
static const char fg_b64[] =
"AA7/4AAADv/gAAAO/+AAAA7/4AAADv/gAAAO/+AAAAz/0AAAC/+wAAAJ/5AAAAf/cAAAAAAAAAAAAAAAAA7/4AAADv/gAAAO/+AAAA7/4AAA76A/9gAO+gP/"
"YADvoD/2AA76A/9gAO+gP/YADvoD/2AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC/oAf9AAAAAA"
"DvcAr6AAAAAAL/QA33AAAAAAX/EB/0AAAAAAj9AF/xAAAE/////////gAE/////////gAAAF/xAv9AAAAAAJ/ABv8QAAAAAN+ACfwAAACP////////sACP//"
"//////sAAACvsAb+AAAAAADvgAr7AAAAAAL/QA73AAAAAAb+AD/zAAAAAAAAP4AAAAAAAAP4AAAAAAKM7/2mIAAD7/////0AAN/5T4JIsAA//zP4AAAABP/4"
"P4AAAAAv///8cwAAAL/////9QAABr/////8wAAAnv///+gAAAAP5Xv/AAAAAP4Cv+wBMcyP4Pf9wBP//////sAADi97/2lAAAAAAP4AAAAAAAAP4AAAAAAAA"
"P4AAAAAAXO60AAAAf9EAAAb///9QAALvQAAADv0i7+AAC/oAAAA/+ACP8wBf4QAAAE/2AG/0Ae9gAAAAP/gAj/MJ/AAAAAAO/SLv4D/zAAAAAAb///9Qz4BL"
"7sUAAFzuxAf9Ff///2AAAAAAL/QN/jLf4QAAAAC/oD/5AH/0AAAABf4QT/cAb/UAAAAe9gA/+QB/9AAAAJ+wAA3+Mt/hAAAE/yAABf///2AAAA34AAAAS+7F"
"AAAABK3uxyAAAAAACP////4AAAAAAv/8ITawAAAAAE//oAAAAAAAAAHv/zAAAAAAAAAK//0gAAAAAAAK///8EADf9wAJ////+gAO/1AD//wu//gD//IAj/9A"
"P//1n/0ACv/xAG////+AAJ//MACf///hAAX/+QAAv//2AAAM//ghXf//sAAAHP///////7AAAAa+/tpiz/+wAO+gAA76AADvoAAO+gAA76AADvoAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//EAAAv/kAAAT/8gAACv/AAAAf/2AAAG//IAAAr/4AAADf+wAAAP/6AAAB//kAAAH/+QAAAP/6AAAA"
"3/sAAACv/gAAAG//IAAAH/9gAAAK/7AAAAT/8gAAAL/5AAAAP/8QAe/zAAAAj/sAAAAf/0AAAAv/sAAABv/yAAAB//cAAADf+wAAAK/+AAAAn/8QAACP/yAA"
"AI//IAAAn/8QAACv/gAAAN/7AAAB//cAAAb/8gAAC/+wAAAf/0AAAI/7AAAB7/MAAAAAL6AAAAAAL6AAACxgL6AqgDz9j8r/kABL//6BAABL//6BADz9j8r/"
"kCxgL6AqgAAAL6AAAAAAL6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAH/gAAAAAAAAAH/gAAAAAAAAAH/gAAA"
"AAAAAAH/gAAAAACv////////IACv////////IACv////////IAAAAAH/gAAAAAAAAAH/gAAAAAAAAAH/gAAAAAAAAAH/gAAAAAAAAAH/gAAAAAC//yAAv/8g"
"AL//IADf/QAC//MABv9wAAr8AAAM///+AM///+AM///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv/8gAL//IAC//yAAv/8gAAAI/QAAAM+AAAAv9AAAB/4A"
"AAC/kAAAH/UAAAb+AAAAv6AAAB/1AAAF/xAAAK+wAAAO9gAABP8gAACfwAAADfcAAAP/IAAAj9AAAA34AAAAAABK3+tgAAAAn////8EAAI//YT7/wAAv/7AA"
"b/9gB//3AAL/+wC//1AAD//wDf/zAADv/yDv/zAADf/zDv/zAADf/zDf/zAADv/yC//1AAD//wB//3AAL/+wAv/7AAb/9gAI//YT7/wAAAn////8EAAABK7+"
"tgAAABSM//8gAAAI////8gAAAHtzz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/8gAAAAAAz/"
"8gAAAAAAz/8gAAAAAAz/8gAAAG///////AAG///////AADe97+tQAAA//////7EAA/+jFO//kAA/UAAE//8QA0AAAA//8wAAAAAA7/8wAAAAAC//8QAAAAAI"
"//oAAAAABP/+IAAAAATv/kAAAAAG//5AAAAAB//+MAAAAAn//SAAAAAK//wQAAAABP//////9gBP//////9gACa97+txAAAN/////+MAALgxFM//0AAAAAAD"
"//8gAAAAAA//8gAAAAAD//4AAAAAFM//UAAADP///DAAAADP///8IAAAAAE7//4QAAAAAA3/9gAAAAAAn/+AAAAAAAz/9gB6UxE6//4QCP/////+QAAVnO/t"
"phAAAAAAHf//AAAAAAr///AAAAAG////AAAAA//u//AAAAHf9e//AAAAr/kO//AAAF/9EO//AAAu/0AO//AADP+QAO//AAD/0QAO//AAD////////0D/////"
"///0AAAAAO//AAAAAAAO//AAAAAAAO//AAAAAAAO//AAAK//////kAAK//////kAAK/5AAAAAAAK/5AAAAAAAK/5AAAAAAAK/5AAAAAAAK/+7+yCAAAK////"
"/+UAAJhCE6//8gAAAAAAv/+AAAAAAAf/+wAAAAAAf/+wAAAAAAz/+ABLcxE6//4gBP/////+MAADi97+txAAAAAFrf7JMAAAG/////8QABz/5iElsQAI//MA"
"AAAAAe/5AAAAAABf/5rf61AACP//////kACf//oiv/9gCf//IAP//QCP/9AADv/xBv/8AADf/xA//9AADv/wAM//IAP/+wAE//oiv/8wAAb////+UAAAAp3+"
"2SAACP//////+ACP//////+AAAAAAB7/9wAAAAAH//4QAAAAAN//kAAAAABP//IAAAAAC//6AAAAAAL//zAAAAAAj/+wAAAAAB7/9AAAAAAG//wAAAAAAM//"
"YAAAAABP/9AAAAAACv/3AAAAAAL//hAAAAAAj/+AAAAAAAKM7+2UAAAE7/////gAAN//YT7/8wA//8AAf/+ABP/6AAX/+AAf/8AAf/9QAI//YT7/wAAAbf//"
"/pEAABnv///7MAAd/+QSv/8wB//3AAL/+wCf/0AAD//gCP/3AAL//QA//+QSv/+AAH//////sAAAOc7+2lAAAAF879pAAAAD3////5AAAd/+QX//cAB//3AA"
"3/8QC//zAAn/9wDf/yAAj/+gDP/zAAn//ACf/3AAz//QA//+MX///QAG///////AAAOt/rf/+QAAAAAAX/9AAAAAAA3/wAAKcxFM/+IAAM/////TAAACfO/r"
"YQAAAI//UAAI//UAAI//UAAI//UAAAAAAAAAAAAAAAAAAAAAAAAAAI//UAAI//UAAI//UAAI//UAAI//UAAI//UAAI//UAAI//UAAAAAAAAAAAAAAAAAAAAA"
"AAAAAI//UAAI//UAAI//UAAK/+IAAO/2AAA/+wAAB/4QAAAAAAAAAAACfCAAAAAAABa//yAAAAABW////BAAAAWu///HIAAAOe///HIAAAAAr//HIAAAAAAA"
"r/+2EAAAAAAAOe//+2EAAAAAAAWu//+3IAAAAAABW////BAAAAAAABa//yAAAAAAAAACfCAAAAAAAAAAAAAAr////////yAAr////////yAAr////////yAA"
"AAAAAAAAAAAAAAAAAAAAAAAAr////////yAAr////////yAAr////////yAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAmUAAAAAAAAAAr/2DAAAAAAAA"
"fv//2CAAAAAAAEnv//xyAAAAAAAEnv//xgAAAAAAAEnv/yAAAAAAAEnv/yAAAAAEnv//xgAAAEnv//xyAAAAfv//2CAAAAAAr/2DAAAAAAAAmUAAAAAAAAAA"
"AAAAAAAAAAABWs79pQAAf/////gAB6UgPf/yAAAAAJ//QAAAAB3/8wAAABz/+wAAABz/+xAAAAr/+wAAAAL//RAAAABP/6AAAAAAAAAAAAAAAAAAAAAABP/5"
"AAAAAE//kAAAAAT/+QAAAABP/5AAAAAAAASd7ttyAAAAAAAEz/////+BAAAAAG/9cxAlr/wQAAAF/4AAAAAD38AAAC/2AAAAAAAd9wAAr6AAbf1q+QP+AAH/"
"IAj///35AM9ABfsAL/sir/kAn2AH+QBv8QAf+QCfYAj3AI/gAA75AM9AB/gAb/EAH/kD/hAF+wAv+yGv+V74AAH/EAj///3//5AAAK+QAG39av2kAAAAL/YA"
"AAAAAAAAAAAG/3AAAAAHcAAAAAB//XMRJ9/hAAAAAATf/////mAAAAAAAAWd79pgAAAAAAAC///zAAAAAACP//+AAAAAAA3///0AAAAABP////QAAAAAn/9/"
"/6AAAAAe/9Df/hAAAAb/+Aj/9gAAAL//MC//sAAAL//QAM//IAAH//cAB//4AADf///////QAD////////9ACf/yAAAC//kA7/0AAAAN/+Ff/6AAAACf/1v/"
"9gAAAAX/+wD////+yTAAAA///////3AAAP//IAX//zAAD//yAAv/9wAA//8gAJ//gAAP//IAC//2AAD//yAF//4QAA///////TAAAP//////+QAAD//yACv/"
"+QAA//8gAB//8QAP//IAAO//MAD//yAAH//yAA//8gAr//wAAP///////jAAD/////63EAAAAAKM7+24MAABn/////+wABz//EETjrAAr/+wAAACgAP//yAA"
"AAAACP/7AAAAAAAM//cAAAAAAA3/9gAAAAAADf/2AAAAAAAM//cAAAAAAAj/+wAAAAAAA///IAAAAAAAr/+wAAACgAAc//xBE46wAAGf/////7AAAAKM7+24"
"MAD////tuDAAAAD///////sQAAD//yAUv//iAAD//yAACP/9AAD//yAAAN//YAD//yAAAH//sAD//yAAAE//8AD//yAAAD//8QD//yAAAD//8QD//yAAAE//"
"8AD//yAAAH//sAD//yAAAN//YAD//yAACf/9AAD//yAUv//iAAD///////sQAAD////tuDAAAAD///////MAD///////MAD//yAAAAAAD//yAAAAAAD//yAA"
"AAAAD//yAAAAAAD//yAAAAAAD//////8AAD//////8AAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD///////YAD///////YAD/////"
"//MAD///////MAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//////8AAD//////8AAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAA"
"AAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAAAAnve/tt0AAABn//////9AAAc//1RAVr9AACv/7EAAAApAAP//yAAAAAAAAj/+wAAAAAAAAz/9wAAAAAAAA3/"
"9gAA////cA3/9gAA////cAz/9wAAAH//cAj/+wAAAH//cAP//yAAAH//cACv/7AAAH//cAAc//xRAq//cAABn///////cAAAAozv7cpzAAD//yAAAL//YAD/"
"/yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAAAL//YAD/////////YAD/////////YAD//yAAAL//YAD//yAAAL//YAD/"
"/yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAAAL//YAD//yAA//8gAP//IAD//yAA//8gAP//IAD//yAA//8gAP//IAD//yAA//8gAP//"
"IAD//yAA//8gAP//IAD//yAAAP//IAAA//8gAAD//yAAAP//IAAA//8gAAD//yAAAP//IAAA//8gAAD//yAAAP//IAAA//8gAAD//yAAAP//IAAA//8gAAD/"
"/yAAAf//IAAE//4AAE3/+QBP//+xAE/tpQAAAP//IAAG//9gAP//IABv//YAAP//IAb//2AAAP//IH//9gAAAP//J///UAAAAP//r//1AAAAAP////9QAAAA"
"AP////cAAAAAAP////4wAAAAAP//7//jAAAAAP//Xf/+MAAAAP//It//4wAAAP//IC3//jAAAP//IALf/+QAAP//IAAt//5AAP//IAAC3//kAP//IAAAAAD/"
"/yAAAAAA//8gAAAAAP//IAAAAAD//yAAAAAA//8gAAAAAP//IAAAAAD//yAAAAAA//8gAAAAAP//IAAAAAD//yAAAAAA//8gAAAAAP//IAAAAAD//yAAAAAA"
"///////2AP//////9gD///cAAACf//0AAP///QAAAe///QAA////UAAH///9AAD////AAA3///0AAP/+7/MAX/7//QAA//6P+QC/9//9AAD//i//Ev/i//0A"
"AP/+C/95/5H//QAA//4E/97/Mf/9AAD//gDf//sB//0AAP/+AG//9QH//QAA//4AHv/QAf/9AAD//gAJ/3AB//0AAP/+AAAAAAH//QAA//4AAAAAAf/9AAD/"
"/gAAAAAB//0AAP//0AAAj/9gAP//9wAAj/9gAP///hAAj/9gAP///4AAj/9gAP///+EAj/9gAP/+z/gAj/9gAP/+T/8gj/9gAP/+C/+Qj/9gAP/+A//yj/9g"
"AP/+AK/6j/9gAP/+AC//v/9gAP/+AAn///9gAP/+AAL///9gAP/+AACP//9gAP/+AAAe//9gAP/+AAAH//9gAAAEne/sggAAAAAs//////kAAAAu//ggO//7"
"AAAM//cAAAz/9wAE//4AAABP/+AAn/+gAAAA7/9ADP/3AAAADP/3AN//YAAAAK//gA3/9gAAAAv/+ADP/3AAAADP/3AJ//oAAAAO//QAT//gAAAE//4AAM//"
"cAAAz/9wAALv/4IDv/+wAAACz/////+QAAAAAEne/sggAAAA/////tpQAAD///////sQAP//IATf/5AA//8gAF//4QD//yAAL//zAP//IAAv//MA//8gAF//"
"4QD//yAE3/+QAP//////+xAA/////9pQAAD//yAAAAAAAP//IAAAAAAA//8gAAAAAAD//yAAAAAAAP//IAAAAAAA//8gAAAAAAAABJ3v7IIAAAAAK//////5"
"AAAALv/4IDv/+gAAC//3AAAM//cABP/+AAAAT//gAJ//oAAAAO//QAz/9wAAAAz/9wDf/2AAAACv/4AN//YAAAAL//kAz/9wAAAAz/9wCf/5AAAADv/1AE//"
"4AAABP/+EADP/3AAAM//gAAC7/+CA7//wAAAAs//////sQAAAABJ3v//cAAAAAAAAAC//SAAAAAAAAAB3/0QAAAAAAAAAu/8EAAA/////skgAAAP//////9Q"
"AAD//yAY//4QAA//8gAN//UAAP//IAC//2AAD//yAAv/9QAA//8gAN//IAAP//IBj/+AAAD//////nAAAA//////6AAAAP//IE3/+AAAD//yAD//8wAA//8g"
"AK//sAAP//IAAv//QAD//yAACv/7AA//8gAAL//0AAF87+7KgQAALf/////zAADP/lETjvMAA//3AAABgwAG//YAAAAAAAb//TAAAAAAA////acwAAAAr///"
"//1QAAAJ//////cAAAAWrf///gAAAAAAOv//MAAAAAAA3/8wBIEAAADf/xAE/pQQKP/6AAT//////8EAAWm97/22AADf////////3f////////0AAAj/+QAA"
"AAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAAAAAAj/+QAA"
"AAAAj/+QAAAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA"
"//8gAAT//QAA7/8wAAX//AAA3/9AAAb/+wAAn/+AAAr/9wAAL//mEX//4QAABe/////9MAAAACe+/+txAAC//3AAAABv/7X//AAAAAz/9Q7/8gAAAv/+EJ//"
"gAAAf/+QA//9AAAN//QADf/0AAP//QAAf/+QAJ//gAAC//4ADv/yAAAL//UE//sAAABv/6Cv/2AAAAHv/y7/4QAAAAn/+//6AAAAAE////9AAAAAAN///9AA"
"AAAACP//+AAAAAAAL///MAAAP/+wAADv/0AAB//3Dv/gAAP//3AAC//zC//zAAf//7AADv/gCP/3AAr//+AAP/+wBP/6AA7+v/MAb/+AAf/+AC/7f/YAr/9A"
"AM//MG/3T/oA7/8QAI//YK/0D/0C//wAAF//oN/xC/8m//kAAB//0v/ACP9p//UAAA3/9/+ABP+d//EAAAn//v9QAf/v/9AAAAb///8QAM///5AAAAL///wA"
"AJ///2AAAADf//kAAF///yAAAACv//UAAB///gAAHv/0AAAG//0QX//hAALv/0AAr/+gAL//kAAB7/9Qb//RAAAE//4+//QAAAAJ////+AAAAAAd///8AAAA"
"AABP//8wAAAAAAf///YAAAAAA////+IAAAAAz//f/7AAAACP/8Hf/3AAAD//8gP//yAADf/3AAf//AAI//sAAAz/9wT//iAAAC//8x3/+QAAAL//wAT//0AA"
"Bf//MACf/9EAHv/3AAAd//gAr//AAAAE//80//8wAAAAn//N//gAAAAAHf///8AAAAAABP///zAAAAAAAJ//+AAAAAAAAC//8QAAAAAAAC//8AAAAAAAAC//"
"8AAAAAAAAC//8AAAAAAAAC//8AAAAAAAAC//8AAAAAAAAC//8AAAAAz///////+wDP///////7AAAAAADP//oAAAAACP//4gAAAABf//9QAAAAAu//+QAAAA"
"AM///AAAAAAJ///iAAAAAG///1AAAAAD7//4AAAAAB3//7AAAAAAr//+IAAAAAb///QAAAAAD///cAAAAAAP////////8A/////////wAv///4AC////gAL/"
"+AAAAv/4AAAC//gAAAL/+AAAAv/4AAAC//gAAAL/+AAAAv/4AAAC//gAAAL/+AAAAv/4AAAC//gAAAL/+AAAAv/4AAAC//gAAAL/+AAAAv///4AC////gN+A"
"AAAI/QAAAD/yAAAA33AAAAn8AAAAT/IAAADvYAAACvsAAABf8QAAAf9QAAAL+gAAAG/gAAAB/1AAAAv5AAAAf+AAAAL/QAAADPgAAACP0Aj///8wCP///zAA"
"AH//MAAAf/8wAAB//zAAAH//MAAAf/8wAAB//zAAAH//MAAAf/8wAAB//zAAAH//MAAAf/8wAAB//zAAAH//MAAAf/8wAAB//zAAAH//MAj///8wCP///zAA"
"AAAJ/9IAAAAAAACP//0QAAAAAAf//v/BAAAAAG/+Qa/8EAAABv+yAAf/sAAAX/gAAAA9+wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////wB/9gAAAACP8w"
"AAAACP0QAAAACPoAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"ACe9/+txAAAP/////9IAAMYxAn//oAAAAAAAz/4AABjO////8QA+//////8gC//4EAz/8gD//gAA3/8gD//gAE//8gDP/3FN//8gBP///7z/8gADvv1wz/8g"
"Av/6AAAAAAAC//oAAAAAAAL/+gAAAAAAAv/6AAAAAAAC//oAAAAAAAL/+gff6SAAAv/7z///4wAC///CFv/9AAL//yAAr/9QAv/9AABv/5AC//sAAE//sAL/"
"+wAAT/+wAv/9AABv/5AC//8gAK//UAL//8IW//0AAv/7z///4wAC//oH3+ogAAABa+/scQAD3////4AB7/+CE3cAj/+QAAAADf/zAAAAAP//AAAAAA//8AAA"
"AADf/zAAAAAI//kAAAAAHv/4ICdwAD3////4AAAWvv7HEAAAAAAA//4AAAAAAAD//gAAAAAAAP/+AAAAAAAA//4AAAAAAAD//gAABL7sUP/+AABv///4//4A"
"Av/+QE7//gAJ//YAB//+AA3/8gAC//4AD//wAAD//gAP//AAAP/+AA3/8gAC//4ACf/2AAf//gAC//5ATv/+AABv///4//4AAAS+7FD//gAAAXvv62AAAAPf"
"////wgAC7/5BTv/AAJ//UABv/1AN//EAAv/6AP///////8AP///////9AN/+AAAAAAAJ//UAAAAAAC7/5hEkfEAAPf/////0AAAWvv7bcwAAAq3//AAu///8"
"AH//gAAAr/8wAACv/zAAn/////ef////9wCv/zAAAK//MAAAr/8wAACv/zAAAK//MAAAr/8wAACv/zAAAK//MAAAr/8wAACv/zAAAAS+7FD//gAAb///+P/+"
"AAL//kBO//4ACf/3AAf//gAN//IAAv/+AA//8AAA//4AD//wAAD//gAN//IAAv/+AAn/9gAH//4AAv/+QE7//gAAb///+P/+AAAEvuxQ//0AAAAAAAL/+wAA"
"AAAACP/2AAB5QgKP/8AAAI/////8IAAAFr3+2lAAAAL/+gAAAAAAAv/6AAAAAAAC//oAAAAAAAL/+gAAAAAAAv/6AAAAAAAC//oH3+swAAL/+7////MAAv//"
"wxn/+gAC//8gAf/9AAL//AAA7/4AAv/7AADv/gAC//oAAO/+AAL/+gAA7/4AAv/6AADv/gAC//oAAO/+AAL/+gAA7/4AAv/6AADv/gAC//oAAv/6AAL/+gAC"
"//oAAAAAAAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAAAAAAAv/6AAAv/6AAAv/6"
"AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AAAv/6AABP/5AAGv/1AL//+wAL/9gQAAL/+gAAAAAAAv/6AAAAAAAC//oAAAAAAAL/"
"+gAAAAAAAv/6AAAAAAAC//oABv/9IAL/+gBv/9IAAv/6Bv/8EAAC//pv/8EAAAL//v/7EAAAAv///+EAAAAC////+gAAAAL/+8//oAAAAv/6HP/5AAAC//oB"
"3/+QAAL/+gAt//kAAv/6AALv/4AC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAL/+gAC//oAAv/6AAP/"
"+hjf1wBb7sUAAD//vP//+Y////YAA///si3//4FP/+AAP//xAI//0AC//yAD//wAB//4AAr/8wA//7AAb/9wAK//MAP/+gAG//cACv/zAD//oABv/3AAr/8w"
"A//6AAb/9wAK//MAP/+gAG//cACv/zAD//oABv/3AAr/8wA//6AAb/9wAK//MAL/+gff6zAAAv/7v///8wAC///DGf/6AAL//yAB//0AAv/8AADv/gAC//sA"
"AO/+AAL/+gAA7/4AAv/6AADv/gAC//oAAO/+AAL/+gAA7/4AAv/6AADv/gAC//oAAO/+AAABe+/sggAAA+/////lAALv/kA9//MAn/9wAF//sA3/8gAA//8A"
"//8AAA3/8g//8AAA3/8g3/8gAA//8An/9wAF//sALv/kA9//MAA+/////lAAABe+/sggAAL/+gff6SAAAv/7z///4wAC///CFv/9AAL//yAAr/9QAv/9AABv"
"/5AC//sAAE//sAL/+wAAT/+wAv/9AABv/5AC//8gAK//UAL//8IW//0AAv/7z///4wAC//oH3+ogAAL/+gAAAAAAAv/6AAAAAAAC//oAAAAAAAL/+gAAAAAA"
"Av/6AAAAAAAABL7sUP/+AABv///4//4AA//+QE7//gAJ//YAB//+AA3/8gAC//4AD//wAAD//gAP//AAAP/+AA3/8gAC//4ACf/2AAf//gAC//5ATv/+AABv"
"///4//4AAAS+7FD//gAAAAAAAP/+AAAAAAAA//4AAAAAAAD//gAAAAAAAP/+AAAAAAAA//4AAv/6GN/AL/+8//wC///UEAAv//MAAAL//QAAAC//sAAAAv/6"
"AAAAL/+gAAAC//oAAAAv/6AAAAL/+gAAAC//oAAAACnO/chAAD7/////QAr/wgE3xADf+gAAAAAM//2oUgAAf/////sQAH7////6AAAEac//8AAAAACv/wCZ"
"UhA9/8AK/////+QAFZzv7JIAAM//EAAADP/xAAAAz/8QAAv/////8L//////AAz/8QAAAM//EAAADP/xAAAAz/8QAAAM//EAAADP/xAAAAz/8QAAAK//YAAA"
"Bf///6AABs7/+gAE//kAAP/8AAT/+QAA//wABP/5AAD//AAE//kAAP/8AAT/+QAA//wABP/4AAD//AAE//kAAf/8AAT/+QAC//wAA//7AAf//AAB//9RXv/8"
"AACP///3//wAAAbP60D//AB//1AAAf/8Af/7AABv/2AK//EAC//hAE//cAL/+QAA3/wAf/9AAAj/8gz/0AAAL/+D//cAAAC//Y//EAAABf///6AAAAAO///0"
"AAAAAI///QAAAAAC//9wAAAf/6AAj/4ABP/2DP/QAM//IAj/8gj/8gH//2AM/9AF//YE//+gH/+gAf/5CP6v0E//YADP/Qz7b/KP/yAAj/8v9z/2z/0AAE//"
"n/QO+v/5AAAO///wCv//9QAAC///sAb///EAAAf//4AD///AAAAD//9AAO//gAAu/9EADP/0Bf/6AH//gACf/1P//AAAHP/t/+IAAALv//9AAAAAb//5AAAA"
"AJ///AAAAAX///+AAAAu/9v/9AAAz/8x7/4QCP/3AE//sF//sAAJ//eP/1AAAf/7L/+wAAb/9gr/8gAL//EE//cAH/+gAN/9AG//QABv/0DP/gAAHv+i//kA"
"AAn/+P/zAAAC////0AAAAL///3AAAABf//8gAAAADf/7AAAAAAj/9gAAAAAJ/+EAAAAAT/+QAAAAz//9EAAAAM/9kQAAAAv/////+wC//////7AAAAA+//sA"
"AAAt//9AAAAd//9QAAAL//9gAAAK//+AAAAJ//+gAAAH//+wAAAA///BAAAAD//////7AP//////sAAAAAW+/+AAAAAAX///4AAAAADP/1EAAAAAAN/9AAAA"
"AAAA7/sAAAAAAADv+wAAAAAAAO/7AAAAAAAB//oAAAAAACv/9gAAAABP//6AAAAAAE///6EAAAAAADv/9wAAAAAAAv/6AAAAAAAA7/sAAAAAAADv+wAAAAAA"
"AO/7AAAAAAAA3/0AAAAAAAC//1EAAAAAAF///+AAAAAABb7/4AAAP/QAAD/0AAA/9AAAP/QAAD/0AAA/9AAAP/QAAD/0AAA/9AAAP/QAAD/0AAA/9AAAP/QA"
"AD/0AAA/9AAAP/QAAD/0AAA/9AAAP/QAAD/0AAA/9AAAP/QAAE//2iAAAAAAT///4QAAAAAAGf/3AAAAAAAD//gAAAAAAAH/+QAAAAAAAf/5AAAAAAAB//kA"
"AAAAAAD//AAAAAAAAL//cQAAAAAAK///4AAAAAA8///gAAAAAM//ggAAAAAA//wAAAAAAAH/+QAAAAAAAf/5AAAAAAAB//kAAAAAAAP/+AAAAAAAGf/2AAAA"
"AE///+EAAAAAT//aIAAAAAAAAAAAAAAAAAAFvv63QQJ9IACf////////IACv////////EACtUQJZ3vyCAABQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAO/+AAAA7/4AAADv/gAAAO/+AAAAAAAAAAAAAAAAAH/3AAAAn/kAAAC/+wAAAM/9AAAA7/4AAADv/gAAAO/+AAAA7/4AAADv/g"
"AAAO/+AAAAbf1QAAB///9QAA7kFO0AAfsAC/EADuQU7QAAf///UAAAbP1QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAC//yAAv/8gAL//IAC//yAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz/8gAAAADP/yAAAAAM//IAAAAAz/8gAAAAAAAAAAAAAAAAAAAAAAz/8gAA"
"AAHv/wAAAACf/7AAAAB//+IAAAB///UAAAAv//YAAAAG//oAAAAAf/9wAAAAA//8ISW1AAn/////UAAFvv7JUAAAAAAAj/UAAAAAAABP9QAAAAAAAB31AAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAv//8wAAAAAAj///gAAAAAAN///9AAAAAAT////0AAAAAJ//f/+gAAAAHv/Q3/4QAAAG//gI//YAAAC//zAv/7AAAC//0A"
"DP/yAAB//3AAf/+AAA3///////0AA/////////QAn/8gAAAv/5AO/9AAAADf/hX/+gAAAAn/9b//YAAAAF//sAAAAAb/gAAAAAAC74AAAAAAAM9wAAAAAAAA"
"AAAAAAAAAAAAAAAAD///////MAD///////MAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD//////8AAD//////8AAD//yAAAAAAD//y"
"AAAAAAD//yAAAAAAD//yAAAAAAD//yAAAAAAD///////YAD///////YAAAHvwQAK/BAAb8EAAAAAAAAAAAAA//8gAP//IAD//yAA//8gAP//IAD//yAA//8g"
"AP//IAD//yAA//8gAP//IAD//yAA//8gAP//IAD//yAA//8gAAACzqMvgAAAAAAK////UAAAAAANsWzpAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//0AAAj/9g"
"AP//9wAAj/9gAP///hAAj/9gAP///4AAj/9gAP///+EAj/9gAP/+z/gAj/9gAP/+T/8gj/9gAP/+C/+Qj/9gAP/+A//yj/9gAP/+AK/6j/9gAP/+AC//v/9g"
"AP/+AAn///9gAP/+AAL///9gAP/+AACP//9gAP/+AAAe//9gAP/+AAAH//9gAAAAAAv+MAAAAAAAAAb+MAAAAAAAAALuMAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAABJ3v7IIAAAAALP/////5AAAALv/4IDv/+wAADP/3AAAM//cABP/+AAAAT//gAJ//oAAAAO//QAz/9wAAAAz/9wDf/2AAAACv/4AN//YAAAAL//gAz/"
"9wAAAAz/9wCf/6AAAADv/0AE//4AAABP/+AADP/3AAAM//cAAC7/+CA7//sAAAAs//////kAAAAABJ3v7IIAAAAAAAAAP/sAAAAAAAAAz7AAAAAAAAAI+gAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT/"
"/QAA//8gAAT//QAA//8gAAT//QAA7/8wAAX//AAA3/9AAAb/+wAAn/+AAAr/9wAAL//mEX//4QAABe/////9MAAAACe+/+txAAAAAAf/E/9QAAAAAAf/E/9Q"
"AAAAAAf/E/9QAAAAAAAAAAAAAAAAAAAAAAAAAAAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA//8gAAT/"
"/QAA//8gAAT//QAA//8gAAT//QAA//8gAAT//QAA7/8wAAX//AAA3/9AAAb/+wAAn/+AAAr/9wAAL//mEX//4QAABe/////9MAAAACe+/+txAAAAAAAAb/cA"
"AAAAAD/3AAAAAAAd+AAAAAAACvgAAAAAAAAAAAAAAAAAAAAAAAAAJ73/63EAAA//////0gAAxjECf/+gAAAAAADP/gAAGM7////xAD7//////yAL//gQDP/y"
"AP/+AADf/yAP/+AAT//yAM//cU3//yAE////vP/yAAO+/XDP/yAAAAAALvwQAAAAABz8EAAAAAAJ/BAAAAAABvwQAAAAAAAAAAAAAAAAAAAAAAAAAXvv62AA"
"AAPf////wgAC7/5BTv/AAJ//UABv/1AN//EAAv/6AP///////8AP///////9AN/+AAAAAAAJ//UAAAAAAC7/5hEkfEAAPf/////0AAAWvv7bcwAAAB39IAAK"
"/SAABv0gAAP+IAAAAAAAAAAAAAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAC//oAAAAAnoAKsAAAAAT/+h2gAA"
"AACPKP/2AAAAAJ0AfrEAAAAAAAAAAAAAAAAAAAAAAAAC//oH3+swAAL/+7////MAAv//wxn/+gAC//8gAf/9AAL//AAA7/4AAv/7AADv/gAC//oAAO/+AAL/"
"+gAA7/4AAv/6AADv/gAC//oAAO/+AAL/+gAA7/4AAv/6AADv/gAAAAAALvsQAAAAABz7EAAAAAAJ/BAAAAAABvwQAAAAAAAAAAAAAAAAAAAAAAAAAXvv7IIA"
"AAPv////5QAC7/5APf/zAJ//cABf/7AN//IAAP//AP//AAAN//IP//AAAN//IN//IAAP//AJ//cABf/7AC7/5APf/zAAPv////5QAAAXvv7IIAAAAAAADP4w"
"AAAAAACf4wAAAAAABf4wAAAAAAAu4wAAAAAAAAAAAAAAAAAAAAAAAAAE//kAAP/8AAT/+QAA//wABP/5AAD//AAE//kAAP/8AAT/+QAA//wABP/4AAD//AAE"
"//kAAf/8AAT/+QAC//wAA//7AAf//AAB//9RXv/8AACP///3//wAAAbP60D//AAAAJ/gX/MAAAAAn+Bf8wAAAACf4F/zAAAAAAAAAAAAAAAAAAAAAAAABP/5"
"AAD//AAE//kAAP/8AAT/+QAA//wABP/5AAD//AAE//kAAP/8AAT/+AAA//wABP/5AAH//AAE//kAAv/8AAP/+wAH//wAAf//UV7//AAAj///9//8AAAGz+tA"
"//wAAAH//9AAAAAf//0AAAAB///QAAAAH//9AAAAAf//0AAAAB///QAAAAH//9AAAAAf//wAAAAA7/+wAAAADP/5AAAAAK//cAAAAAn/9QAAAAB//zAAAAAA"
"AAAAAAAAAAAAAAAAH//9AAAAAf//0AAAAB///QAAAAH//9AAAAAf//0AAABf/gBf/gAABf/gBf/gAABf/gBf/gAABf/gBf/gAABf/gBf/gAABf/gBf/gAABf"
"/gBf/gAABf/gBf/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAL/1AB/+AAAAAAAADv8QBf+gAAAAAAAE/8AAn/cAAAAAAACP+AAN/zAAAAAAAAz/QAL/4AAAAAj///////////gAAI////////"
"///4AACP//////////+AAAAADP9AAv/gAAAAAAAB//EAX/oAAAAAAABP/AAJ/3AAAAAAAAf/gADf8wAAAAH///////////8AAB////////////AAAf//////"
"/////wAAAABv+QAL/0AAAAAAAAr/YAH/8AAAAAAAAO/yAE/7AAAAAAAAP/0ACP9wAAAAAAAH/5AAz/MAAAAAAAAAAF/QAAAAAAAAAAX9AAAAAAAAAABf0AAA"
"AAAAAGrf////9QAAAt///////1AAAd////////UAAH//5W/RNIxQAAv/+QX9AAAAAADP/7Bf0AAAAAAL//+6/QAAAAAAf/////63IAAAAe///////5EAAAPf"
"//////+gAAAAWu//////MAAAAABv6+//9wAAAAAF/QLv/4AAAAAAX9AM//cAC6cyBf0W//9AAM////////+wAAz///////+xAADP/////slAAAAAAAAF/QAA"
"AAAAAAAAX9AAAAAAAAAABf0AAAAAAAAAAF/QAAAAAAAFvv2jAAAAAG/5AAAAAJ////9QAAAC7+EAAAAG//UY//IAAAr/UAAAAAz/kADv+AAAX/sAAAAAD/9g"
"AL/7AAHv4gAAAAAf/1AAr/wACf9gAAAAAA//YAC/+wBP/AAAAAAADP+QAO/4AN/yAAAAAAAG//UY//II/4AAAAAAAACf////UD/9ADnf62AAAAW+/aMAz/MF"
"////+gAAAAAAAAf/kB7/kU7/cAAAAAAALv0Qf/4ACf/QAAAAAAC/9QC/+wAG//EAAAAABf+gAL/6AAX/8gAAAAAe/hAAr/sABv/xAAAAAJ/2AAB//gAJ/9AA"
"AAAE/7AAAB7/kU7/YAAAAB3/IAAABf////oAAAAAj/cAAAAAOd/rYAAAAAAEre7bhAAAAAAAAAG//////3AAAAAAAAr//////3AAAAAAAB///kEVv3AAAAAA"
"AE//+gAABWAAAAAAAC///QAAAAAAAAAAAAz//4AAAAAAAAAAAAb///YAAAAAAAAAAJ////9gAAD//0AACv/////1AAL//xAAb//6b///UAX//gAA3//QB///"
"9Av/+QAC//+AAI///4//9AAE//9wAAr/////wAAD//+gAAC/////MAAB7//0AAAc///3AAAAj//+cgJ+///9EAAAHP//////////wQAAAZ///////d///BAA"
"AAKM7+24QC3//7AAX/4AAAX/4AAAX/4AAAX/4AAAX/4AAAX/4AAAX/4AAAX/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAADP/1AAAABv/9AAAAAN//YAAAAG//4AAAAA3/+QAAAAT//0AAAACf/+AAAAAN//oAAAAB//9wAAAAX//0AAAABv//MAAAAI//8gAAAA"
"n//xAAAACP//IAAAAG//8wAAAAX//0AAAAAv//cAAAAA3/+gAAAACf/+AAAAAE//8wAAAADf/5AAAAAG//4AAAAADf/1AAAAAG//0AAAAADP/1AAAI//kAAA"
"AAHv/zAAAAAI//oAAAAAL//zAAAAAM//oAAAAAb//xAAAAAv//YAAAAA3/+gAAAACv/+AAAAAH//8gAAAAb//0AAAABf//UAAAAE//9gAAAAX//1AAAABv//"
"MAAAAH//8gAAAAr//QAAAADf/6AAAAAv//YAAAAG//8QAAAAz/+gAAAAL//zAAAACf/7AAAAAe//MAAAAI//kAAAAAAAAM9wAAAAAAAM9wAAAAlwAM9wAqQD"
"/9UM9xj/wBjv/O++/9UAAp////5wAAAAX//+IAAAAp////5wABjv++++/9UD/9UM9xj/wAlwAM9wAqQAAAAM9wAAAAAAAM9wAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/UAAAAAAAAAAAAN/1AAAAAAAAAAAADf9QAAAAAAAAAAAA3/UAAAAAAAAAAAAN/1"
"AAAAAAAAAAAADf9QAAAAAAAAAAAA3/UAAAAAAAD///////////gAAA///////////4AAAP//////////+AAAAAAAAN/1AAAAAAAAAAAADf9QAAAAAAAAAAAA"
"3/UAAAAAAAAAAAAN/1AAAAAAAAAAAADf9QAAAAAAAAAAAA3/UAAAAAAAAAAAAN/1AAAAAAAAL//8AAAC///AAAAv//wAAAL//8AAAE//9wAACP/8AAAAz/4g"
"AAAv/2AAAAb/sAAAAAf/////IAf/////IAf/////IAf/////IAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv//wAAAL//8AAAC///AAA"
"Av//wAAAL//8AAAAAAAO/xAAAAT/sAAAAJ/3AAAADv8gAAAD/8AAAACP+AAAAA3/MAAAAv/QAAAAf/gAAAAM/0AAAAH/4AAAAG/5AAAAC/9QAAAB/+EAAABf"
"+gAAAAr/YAAAAO/xAAAAT/sAAAAJ/2AAAADv8gAAAD/8AAAACP9wAAAA3/MAAAAAAAABe9/tkwAAAAAF7/////oQAAAF///////8AAAC7///////+AAAn//9"
"QSn///IAHv//QAAM//9wBP//4AAAf//7AH//+wAABP//4An//6AAAD///xCf//kAAAL///IJ//+QAAAv//8gn//6AAAD///xB///sAAAT//+AE///gAAB///"
"sAHv//QAAM//9wAJ///UAp///yAALv///////4AAAF///////8EAAABe/////6EAAAAAF73+2TAAAAABR77//+AAAAAA3/////4AAAAADf/////gAAAAAN//"
"///+AAAAAAy4Uv//4AAAAAAAAB///gAAAAAAAAH//+AAAAAAAAAf//4AAAAAAAAB///gAAAAAAAAH//+AAAAAAAAAf//4AAAAAAAAB///gAAAAAAAAH//+AA"
"AAAAAAAf//4AAAAAAAAB///gAAAAAAAAH//+AAAAAAv////////4AAC/////////gAAL////////+AAAv////////4AAFHrO/+yTAAAAC///////+xAAAL//"
"//////wAAAv////////3AACrdCETr///sAAAAAAAAL///QAAAAAAAAb//8AAAAAAAACf//gAAAAAAAA///8gAAAAAABO//9gAAAAAABv//9gAAAAAACP//9Q"
"AAAAAAGv//4wAAAAAAHP//0gAAAAAALf//sQAAAAAATv//kAAAAAAADP////////8QAM/////////xAAz/////////EADP////////8QAANqzf/slQAAAAT/"
"//////0wAABP///////+IAAE////////+AAATHQhE4///7AAAAAAAACf//sAAAAAAAAK//+AAAAAAAE4///hAAAACf/////TAAAAAJ////+hAAAAAAn/////"
"5gAAAACf//////YAAAAAABJt///gAAAAAAAAL///MAAAAAAAAv//8wAtlTEBJt///xAC/////////7AAL////////+IAAv///////7IAAAJqze/tuDAAAAAA"
"AAAd///0AAAAAAAJ////QAAAAAAF////9AAAAAAB7////0AAAAAAv/2///QAAAAAb/9K//9AAAAALv+Ar//0AAAADP/ACv//QAAACP/iAK//9AAAA//1AAr/"
"/0AAAd/5AACv//QAAJ/9EAAK//9AAAv//////////zC///////////ML//////////8wv//////////zAAAAAACv//QAAAAAAAAK//9AAAAAAAAAr//0AAAA"
"AAAACv//QAAAD////////xAAAP////////EAAA////////8QAAD////////xAAAP//MAAAAAAAAA//8wAAAAAAAAD//87+2lAAAAAP///////CAAAA//////"
"//4gAAD////////7AAANhTESjv//8gAAAAAAAD///2AAAAAAAADP//cAAAAAAAAM//9wAAAAAAAD///2AAunQhEo7///EADf////////kAAN////////wQAA"
"3///////oQAAAUi83/64IAAAAAAABa3v3JUQAAAAXf/////6AAAAf///////oAAAT///////+gAAHv//xSATWZAABv//oAAAAAAAAL//8nzu2TAAAA///t//"
"//+QAAL/////////kAA//////////0AE////chXv//oAP///oAAG///QAv//9wAAL//+AA7//3AAAv//4ACv//oAAG///AAE///3EV7//3AAC////////+EA"
"AC3///////QAAAAs/////+QAAAAABa3v22EAAAL/////////9AAv/////////0AC//////////QAL/////////4QAAAAAAAI//+AAAAAAAAB7//hAAAAAAAA"
"f//5AAAAAAAADv//IAAAAAAABv//oAAAAAAAAN//8wAAAAAAAF//+wAAAAAAAAz//0AAAAAAAAX//8AAAAAAAADP//UAAAAAAABP//0AAAAAAAAL//9gAAAA"
"AAAD///QAAAAAAAAr//3AAAAAAAAL//+EAAAAAAACf//gAAAAAAAAAWs7+24IAAAAD3//////4AAAB7///////9wAAj////////+EADP//wxF///8wAM//9A"
"AAz//0AAr//0AADP//IABP//wxF///sAAAj///////0gAAAEv////+cQAAACnv/////FAAAD7///////+QAA3//5IBXv//QAP//8AAAF//+gBP//wAAAX//7"
"AD///5IBXf//oADv////////9gAG/////////AAABu//////+xAAAAFq3v/sgwAAAAADnO/rcQAAAAAa/////+UAAAAc///////2AAAJ////////8wAB///5"
"IU3//6AAX//8AAA///8QB///kAAA///1AI//+QAAD///gAf//8AAA///+QA///+SFN///6AAz/////////oAA/////////+AAATv////z//2AAABfO/aOf//"
"MAAAAAAABP//wAADxzIBOf//9QAAP///////+gAAA////////BAAAD//////+QAAAAA3ve/bcgAAAAAN//8QAADf//EAAA3//xAAAN//8QAADf//EAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADf//EAAA3//xAAAN//8QAADf//EAAA3//xAAAA3//xAAAN//8QAADf//EAAA3//xAAAN//8QAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAN//8QAADf//EAAA3//xAAAN//8QAAD//7AAAE//4gAACP/2AAAAz/oAAAAf/hAAAAAAAAAAAAAAAASnAAAAAAAAAAADjf+AAA"
"AAAAAAAnz///gAAAAAAAFb/////EAAAAAASu////xyAAAAADjf///9gwAAAAAAz////oMAAAAAAAAP//6UAAAAAAAAAAD//+kwAAAAAAAAAAz////YMAAAAA"
"AAAAOO////2CAAAAAAAAAErv///8cgAAAAAAAAFb/////EAAAAAAAAACfP//+AAAAAAAAAAAA47/gAAAAAAAAAAAAASnAAAAAAAAAAAAAAAAAAAP////////"
"//+AAAD///////////gAAA///////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////+AAAD///////////gAAA//////"
"/////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMcQAAAAAAAAAAAAD/+1EAAAAAAAAAAA///+lAAAAAAAAAAJ7/"
"///YMAAAAAAAAAWu////xxAAAAAAAAAVv////7UQAAAAAAAAFr////5QAAAAAAAAACfP//gAAAAAAAAAAWv//4AAAAAAAAFr////5QAAAAABWv////tRAAAA"
"AFrv///8cQAAAAAJ7////YMAAAAAAAD///6UAAAAAAAAAA//tRAAAAAAAAAAAMcQAAAAAAAAAAAAAAAAAAAAAAAAAAAB////7aYAAAH//////9IAAf//////"
"/AAB2EIRXv//QAAAAAAJ//9gAAAAAAv//1AAAAAAf//+EAAAAAj///YAAAAAj///cAAAAAX///YAAAAADf//cAAAAAAv//0AAAAAAD//+gAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAE//+gAAAAAAT//6AAAAAABP//oAAAAAAE//+gAAAAAAT//6AAAAAAAAAAFqzv7JQAAAAAAAAAABj//////9YAAAAAAAAE7////////7EAAA"
"AAAG//+2MQI43//RAAAAAE//swAAAAAG7/wAAAAC7/kAAAAAAAAt/3AAAAn/kAAY39YP/ALv4QAAL/0QAt///3/8AG/2AAB/9AAL////7/wADvoAAM/QAE//"
"kin//AAK/QAA/5AAj/wAAM/8AAn/AAH/cAC/9wAAf/wACf8AAv9gAL/2AABf/AAL/QAB/4AAv/cAAH/8AB/6AAD/kACP/AAAz/wAn/YAAM/gAE//kin//Dr/"
"0AAAj/QAC////+////4wAAA//AAC3///f///0wAAAAr/gAAY39YP/aUAAAAAAv/4AAAAAAEAAAAAAAAAX/+yAAAAAAXBAAAAAAAH//+mIQJI3/sAAAAAAABe"
"////////5AAAAAAAAAKf//////kQAAAAAAAAAAJr3v22EAAAAAAAAAAH////IAAAAAAAAA3///+AAAAAAAAAT////+AAAAAAAACf////9AAAAAAAAe//3//6"
"AAAAAAAG//98//8QAAAAAAv//xb//2AAAAAAL//7Af//wAAAAACP//UAr//zAAAAAN//4ABP//gAAAAE//+QAA7//gAAAAr//zAACP//UAAAHv////////+g"
"AABv//////////EAAM//////////9wAC///////////8AAj//5AAAAAN//8wDv//QAAAAAj//5BP//4AAAAABP//4K//+QAAAAAA7//1AG/////+24QAAAAG"
"////////+xAAAG/////////7AAAG//////////MAAG///AABj///cAAG///AAADP//gAAG///AAADP//YAAG///AABf///IAAG/////////4AAAG////////"
"9gAAAG/////////mAAAG//////////YAAG///AABO///4QAG///AAAAf//8wAG///AAAAf//9QAG///AABO///9AAG//////////8QAG//////////cAAG//"
"///////4AAAG//////7bcgAAAAAAAnve/slRAAAAACv//////+cAAABe////////wAAAX/////////wAAC////xiASa/wAAK///5AAAAADkAAf//+wAAAAAA"
"AABf//9AAAAAAAAAB///8AAAAAAAAACf//0AAAAAAAAACf//0AAAAAAAAAB///8AAAAAAAAABf//9AAAAAAAAAAf//+wAAAAAAAAAK///5AAAAADkAAC////"
"xiASa/wAAAX/////////wAAABu////////wAAAACv//////+cAAAAAAnve/tpRAAAG/////tynIAAAAABv////////swAAAAb/////////9wAAAG////////"
"//+AAABv//wAEmz///9AAAb//8AAAAf///wAAG///AAAAAn///MABv//wAAAAB///3AAb//8AAAAAM//+gAG///AAAAACv//sABv//wAAAAAr//7AAb//8AA"
"AAAM//+gAG///AAAAAH///gABv//wAAAAJ///zAAb//8AAAAf///wAAG///AASbP///0AABv//////////gAAAb/////////9wAAAG////////+zAAAABv//"
"//7cpyAAAAAAb////////8AABv////////wAAG/////////AAAb////////8AABv//wAAAAAAAAG///AAAAAAAAAb//8AAAAAAAABv//wAAAAAAAAG//////"
"//9AAAb////////0AABv////////QAAG////////9AAAb//8AAAAAAAABv//wAAAAAAAAG///AAAAAAAAAb//8AAAAAAAABv////////8QAG/////////xAA"
"b/////////EABv////////8QAG/////////AAAb////////8AABv////////wAAG/////////AAAb//8AAAAAAAABv//wAAAAAAAAG///AAAAAAAAAb//8AA"
"AAAAAABv////////QAAG////////9AAAb////////0AABv////////QAAG///AAAAAAAAAb//8AAAAAAAABv//wAAAAAAAAG///AAAAAAAAAb//8AAAAAAAA"
"Bv//wAAAAAAAAG///AAAAAAAAAb//8AAAAAAAAAAAAJ63v7slRAAAAAAKv///////6EAAABe/////////zAAAF//////////8wAAL////XMQE3z/MAAK///6"
"EAAAAAKiAAH///wAAAAAAAAAAF///0AAAAAAAAAAB///8AAAAAAAAAAAn//9AAAE/////gAJ///QAABP////4AB///8AAAT////+AAX///QAAE/////gAB//"
"/7AAAAAf//4AAK///5AAAAH//+AAAv///8YhAU///gAABf//////////4AAABu/////////+AAAAAr///////+kwAAAAACe97+24UQAAAG///AAAAAb//9AA"
"Bv//wAAAAG///QAAb//8AAAABv//0AAG///AAAAAb//9AABv//wAAAAG///QAAb//8AAAABv//0AAG///AAAAAb//9AABv//wAAAAG///QAAb///////////"
"0AAG///////////9AABv///////////QAAb///////////0AAG///AAAAAb//9AABv//wAAAAG///QAAb//8AAAABv//0AAG///AAAAAb//9AABv//wAAAAG"
"///QAAb//8AAAABv//0AAG///AAAAAb//9AABv//wAAAAG///QAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv"
"//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wA"
"AABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAABv//wAAAB///wAAACf//sAAAHf//kAATv///UA"
"n////9AAn////0AAn///5AAAn+2mEAAAAG///AAAAD7//9IABv//wAAAPv//0gAAb//8AABO///RAAAG///AAE7//8EAAABv//wAT///wQAAAAb//8Bf///B"
"AAAAAG///F///7EAAAAABv//7///sAAAAAAAb/////+gAAAAAAAG/////+EAAAAAAABv/////7EAAAAAAAb//////7EAAAAAAG///b///8EAAAAABv//wb//"
"/8EAAAAAb//8AK///8EAAAAG///AAK///8EAAABv//wAAK///9EAAAb//8AAAJ///9IAAG///AAAAJ///9IABv//wAAAAI///9IAb//8AAAAAAAAb//8AAAA"
"AAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAA"
"AAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb//8AAAAAAAAb/////////EAb/////////EAb/////////EAb/////////EAb///9wAAAACf///0AABv"
"///+AAAAAf////QAAG////9QAAAI////9AAAb////8AAAA7////0AABv////9AAAb/////QAAG///f/6AADP/9//9AAAb//53/8gBP/8v//0AABv//h//4AL"
"//W///QAAG//+B7/4S//0L//9AAAb//4Cf/3n/9wv//0AABv//gC//3v/hC///QAAG//+AC////5AL//9AAAb//4AE////IAv//0AABv//gADf//oAC///QA"
"AG//+AAG//9AAL//9AAAb//4AADv/AAAv//0AABv//gAAAAAAAC///QAAG//+AAAAAAAAL//9AAAb//4AAAAAAAAv//0AABv//gAAAAAAAC///QAAG///7AA"
"AAL//9AABv///0AAAC///QAAb////AAAAv//0AAG////9QAAL//9AABv////0AAC///QAAb/////YAAv//0AAG///f/+EAL//9AABv//jP/4AC///QAAb//4"
"T//hAv//0AAG//+Ar/+QL//9AABv//gD//8i///QAAb//4AJ//ov//0AAG//+AAu//X//9AABv//gACP/9///QAAb//4AAHv////0AAG//+AAAf////9AABv"
"//gAAA3////QAAb//4AAAG////0AAG//+AAAAM///9AABv//gAAABP///QAAAAAFnO/tuDAAAAAAAAXf//////swAAAAAJ/////////2AAAACP//////////"
"UAAAT///+DEUr///4QAAv///QAAAB///+AAB///5AAAAAM///QAF///zAAAAAG///yAH///gAAAAAC///0AJ///QAAAAAB///1AJ///QAAAAAB///1AH///g"
"AAAAAC///0AF///zAAAAAG///yAB///5AAAAAM///QAAv///QAAAB///+AAAT///+DATr///4QAACP//////////UAAAAJ/////////2AAAAAAXf//////ww"
"AAAAAAAFnO/tuDAAAAAAb//////slAAAAAb////////8IAAAb/////////4gAAb/////////+wAAb//8AAFe///xAAb//8AAAF///0AAb//8AAAB///1AAb/"
"/8AAAF///0AAb//8AAFe///xAAb/////////+wAAb/////////4gAAb////////8IAAAb//////slAAAAAb//8AAAAAAAAAAb//8AAAAAAAAAAb//8AAAAAA"
"AAAAb//8AAAAAAAAAAb//8AAAAAAAAAAb//8AAAAAAAAAAb//8AAAAAAAAAAAAAEnO/tyEAAAAAAAAXf//////xAAAAAAI/////////3AAAACP//////////"
"UAAAP///+DEUr///4QAAv///QAAAB///+AAB///5AAAAAM///QAF///zAAAAAG///yAH///gAAAAAC///0AJ///QAAAAAB///1AJ///QAAAAAB///1AH///g"
"AAAAAC///0AF///zAAAAAG///yAC///4AAAAAM///QAAv///QAAAB///9wAAT///+DATr///0QAACP//////////QAAAAJ/////////kAAAAAAXf//////og"
"AAAAAAAEjN///+IAAAAAAAAAAAA+//wQAAAAAAAAAAAF//+wAAAAAAAAAAAAf//4AAAAAAAAAAAACf//YAAAb/////7bgwAAAABv////////kAAAAG//////"
"///4AAAAb/////////8QAABv//wAE7///0AAAG///AAAH///YAAAb//8AAAO//9AAABv//wAAB///yAAAG///AATv//6AAAAb////////9IAAABv///////o"
"EAAAAG///////+gAAAAAb////////6AAAABv//wAOv//9gAAAG///AAAr//+EAAAb//8AAAe//+AAABv//wAAAj///IAAG///AAAAe//+gAAb//8AAAAb///"
"MABv//wAAAAN//+wAAAEnO/+ynQAAAACz///////wAAAHf///////8AAAH/////////AAADP//tBAUjfwAAA7//gAAAABZAAAO//0AAAAAAAAADP//kgAAAA"
"AAAAb////ahRAAAAAAr//////8UAAAAAbf//////oAAAAAA3vf////gAAAAAAAAW3//+AAAAAAAAAC///xAAphAAAAAf//8QAM/qYxAUz//+AADP////////"
"+QAAz////////+IAAH7///////0wAAAAN6zv/slQAADf///////////t///////////+3///////////7f///////////gAAAB///zAAAAAAAAH///MAAAAA"
"AAAf//8wAAAAAAAB///zAAAAAAAAH///MAAAAAAAAf//8wAAAAAAAB///zAAAAAAAAH///MAAAAAAAAf//8wAAAAAAAB///zAAAAAAAAH///MAAAAAAAAf//"
"8wAAAAAAAB///zAAAAAAAAH///MAAAAAAAAf//8wAAAAAAAB///zAAAAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv"
"//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//9AAAAH///IA"
"AF///QAAAC///yAABP//8QAABP//8AAAH///YAAAr//8AAAAz//+YQKP//+AAAAF/////////+EAAAAJ////////9QAAAAAH///////kAAAAAAABe97+2mAA"
"AACv//kAAAAAAO//9U///gAAAAAF///gDv//UAAAAAr//5AI//+wAAAAH///MAL///EAAABv//wAAM//9wAAAM//9wAAb//8AAAC///xAAAe//8wAAf//6AA"
"AAr//4AADf//UAAABP//0AA///4AAAAA3//0AJ//+AAAAACP//oA7//zAAAAAC///hX//8AAAAAAC///av//YAAAAAAG///P//8QAAAAAAHv////+gAAAAAA"
"AJ/////0AAAAAAAAT////+AAAAAAAAAN////gAAAAAAAAAf///8gAAAAH///AAAAP///IAAAL//9AM//9AAAB///9QAABf//oAn//3AAAK///5AAAJ//9gBf"
"//sAAA7///wAAA3//zAB///gAAP////xAAH//+AADf//MABv/6//UABf//oAAJ//9wAK//P/+AAJ//9wAAX//6AA7/wO/8AAz//zAAAv//4AL/+Ar/8QH//+"
"AAAA3//zBv/0B//0Bf//sAAACf//YJ//ED//gI//9wAAAG//+g3/wADv+wz//0AAAAL//+L/+QAL//H///AAAAAN//+P/1AAf/+P//wAAAAAr//+//EAA//+"
"//+AAAAABv////0AAA7////0AAAAAC////+QAAC/////EAAAAADv///1AAAH////wAAAAAAK////IAAAT///+AAAAAAAf///0AAAAP///1AAAAz//6AAAAAu"
"//9gA///9QAAAM//+wAAf//+IAAH///hAAAL//+wAD///1AAAALv//cB3//5AAAAAG///yn//9EAAAAACv//3///QAAAAAAB7/////gAAAAAAABP////wAAA"
"AAAAAAn///8wAAAAAAAAHf///3AAAAAAAACf////8gAAAAAABP/////8AAAAAAAd//+e//+AAAAAAK///AT///MAAAAF///zAJ///RAAAC7//3AAHf//kAAA"
"v//8AAAD///0AAb//+IAAACP//4QLv//YAAAAAz//6Ad///AAAAACP//8wT///cAAAA///+AAJ///iAAAM///QAAHf//sAAI///zAAAE///2AD///4AAAACf"
"//4gz//8AAAAAB3//7f///MAAAAABP//////gAAAAAAAn/////wAAAAAAAAd////8wAAAAAAAAT///9wAAAAAAAAAJ///QAAAAAAAAAAj//8AAAAAAAAAACP"
"//wAAAAAAAAAAI///AAAAAAAAAAAj//8AAAAAAAAAACP//wAAAAAAAAAAI///AAAAAAAAAAAj//8AAAAAAAAAACP//wAAAAABv//////////sAb/////////"
"/7AG//////////+wBv//////////YAAAAAAABP//+AAAAAAAAC7//6AAAAAAAAHf//wQAAAAAAAL///SAAAAAAAAn//+MAAAAAAAB///9QAAAAAAAF///3AA"
"AAAAAAPv//kAAAAAAAAt//+wAAAAAAABz//9EAAAAAAACv//4gAAAAAAAI///0AAAAAAAAb///////////EL///////////xC///////////8Qv/////////"
"//EAn////9AACf////0AAJ/////QAAn//xAAAACf//EAAAAJ//8QAAAAn//xAAAACf//EAAAAJ//8QAAAAn//xAAAACf//EAAAAJ//8QAAAAn//xAAAACf//"
"EAAAAJ//8QAAAAn//xAAAACf//EAAAAJ//8QAAAAn//xAAAACf//EAAAAJ//8QAAAAn//xAAAACf////0AAJ/////QAAn////9AA3/MAAAAI/3AAAAA//AAA"
"AADv8gAAAAn/YAAAAE/7AAAAAO/xAAAACv9gAAAAX/oAAAAB/+EAAAAL/1AAAABv+QAAAAL/4AAAAAz/QAAAAH/4AAAAAv/QAAAADf8wAAAAj/gAAAAD/8AA"
"AAAO/yAAAACf9wAAAAT/sAAAAA7/EAH/////YAAf////9gAB/////2AAAABP//YAAAAE//9gAAAAT//2AAAABP//YAAAAE//9gAAAAT//2AAAABP//YAAAAE"
"//9gAAAAT//2AAAABP//YAAAAE//9gAAAAT//2AAAABP//YAAAAE//9gAAAAT//2AAAABP//YAAAAE//9gAAAAT//2AAAABP//YAAf////9gAB/////2AAH/"
"////YAAAAAAABv/8EAAAAAAAAAAF///7AAAAAAAAAAT////6AAAAAAAAA+//3//4AAAAAAAC3/+RTv/3AAAAAAHf/2AALP/2AAAAAc/9MAAACf/0AAAAv/sQ"
"AAAABe/jAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////"
"//////////////////8E7/gAAAAAAE7/UAAAAAAE7+IAAAAAAE78EAAAAAAD75AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAN63v/slAAAAAf/"
"//////sQAAB////////7AAAGtjIQFd//9AAAAAAAAAX//4AAABat7/////oAAE7///////+gAC/////////6AAj//9QQBP//oAC///QAAG//+gAL//9AAAz/"
"/6AAn//8MTv///oAA//////5//+gAAb////4T//6AAADrv6kBP//oAAAr//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAr//0AAAAAAAAAK//9AAAAAAA"
"AACv//QAAAAAAAAAr//0BK79kgAAAK//9H////9QAACv//n/////9AAAr///swO///0AAK///QAADf//QACv//cAAAj//4AAr//1AAAF//+wAK//9AAABP//"
"sACv//UAAAX//7AAr//3AAAI//+AAK///QAADf//QACv//+zAr///QAAr//5//////QAAK//9H////9QAACv//QErv2SAAAAAAKL7+2mEAAAGv/////7AAAd"
"//////+wAAv//+cgI3kABP//8wAAAAAAj//6AAAAAAAL//9gAAAAAADP//UAAAAAAAv//2AAAAAAAI//+gAAAAAABP//8wAAAAAAC///5yATiQAAHf//////"
"sAAAGv/////7AAAAA4vv7aYQAAAAAAAAAE//+gAAAAAAAABP//oAAAAAAAAAT//6AAAAAAAAAE//+gAAAAAAAABP//oAAAAAAAAAT//6AAAAKd/qQE//+gAA"
"Be////dP//oAAD//////n//6AADP//swK///+gAE///hAADf//oACP//kAAAf//6AAr//2AAAF//+gAL//9QAABP//oACv//YAAAX//6AAj//5AAAH//+gAE"
"///hAADf//oAAM//+zAr///6AAA//////5//+gAABe////dP//oAAAAp3+tAT//6AAAAA5zv7JMAAAAAG//////6EAAALf///////BAAC///sxKv//kABP//"
"wAAAz//xAI//9gAAB///YAv/////////+ADP/////////5AL//////////oAj//1AAAAAAAABP//sAAAAAAAAAv//7QQEkesAAAt////////4AAAK///////"
"/gAAAAOM7+3LhRAAAAAXzv//YAAd////9gAJ/////2AA3//1AAAAD//9AAAAAP//0AAAf///////F///////8X///////xAA///QAAAAD//9AAAAAP//0AAA"
"AA///QAAAAD//9AAAAAP//0AAAAA///QAAAAD//9AAAAAP//0AAAAA///QAAAAD//9AAAAAP//0AAAAAACnf6kBP//oAAATv///3T//6AAA//////5//+gAA"
"z//8MCv///oABP//4QAB7//6AAj//5AAAI//+gAK//9wAABf//oAC///UAAAT//6AAr//2AAAF//+gAI//+AAACP//oABP//4QAA7//6AADP//swK///+gAA"
"P/////+f//oAAATv///3T//6AAAAKd/rQF//+QAAAAAAAACf//YAAAAAAAAC7//yAAALlSECbv//kAAADf///////BAAAA3//////5EAAAACas7+23IAAAAA"
"r//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAr//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAr//0A639owAAAK//9G////9gAACv//n/////8gAA"
"r///swTv//cAAK///hAAb//6AACv//gAAE//+wAAr//1AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0AAA///sAAK//9AAAP//7AACv//QAAD//+wAA"
"r//0AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0AACv//QAAK//9AAAr//0AAAAAAAAAAAAAAAAr//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAA"
"r//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAACv//QAAAr//0AAAK//9AAACv//QAAAAAAAAAAAAAAAAACv//QAAAr//0AAAK"
"//9AAACv//QAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9AAACv//MAAAz//yAAFv//0ADv///2"
"AA7///oAAO/+tQAAAACv//QAAAAAAAAAr//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAr//0AAAAAAAAAK//9AAAAAAAAACv//QAAJ///SAAr//0AAr/"
"/9IAAK//9ACv//wQAACv//QK//+xAAAAr//0v//6AAAAAK///f//kAAAAACv////+AAAAAAAr/////oAAAAAAK//////oAAAAACv//bf//oAAAAAr//0Lv//"
"oAAAAK//9APv//oAAACv//QAPv//oAAAr//0AATv//oAAK//9AAAT///oACv//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv"
"//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv//QAAK//9AAAr//0AACv//QFvutAACjf61AAAAr//0j///9wTv///4AAAK//"
"+f////9u/////0AACv//+iGP///4Ea//+gAAr//9AAD///sAAv//0AAK//9wAA3//1AAD//+AACv//UAAM//8wAA7//wAAr//0AADP//IAAO//8AAK//9AAA"
"z//yAADv//AACv//QAAM//8gAA7//wAAr//0AADP//IAAO//8AAK//9AAAz//yAADv//AACv//QAAM//8gAA7//wAAr//0AADP//IAAO//8AAK//9AAAz//y"
"AADv//AAAK//9AOt/aMAAACv//Rv////YAAAr//5//////IAAK///7ME7//3AACv//4QAG//+gAAr//4AABP//sAAK//9QAAP//7AACv//QAAD//+wAAr//0"
"AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0AAA///sAAAAEnO/tpQAAAAAr//////1AAAAt////"
"////QAAL///DAp///hAE///hAAC///cAj//4AAAF///AC///UAAAL//+AM//9QAAAf//8Av//1AAAC///gCP//gAAAX//8AE///hAAC///cADP//wwKf//4Q"
"AC7///////9AAAAr//////1AAAAABJzv7aUAAAAAr//0BK79kgAAAK//9H////9QAACv//n/////9AAAr///swO///0AAK///QAADf//QACv//cAAAj//4AA"
"r//1AAAF//+wAK//9AAABP//sACv//UAAAX//7AAr//3AAAI//+AAK///QAADf//QACv//+zAr///QAAr//5//////QAAK//9H////9QAACv//QErv2SAAAA"
"r//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAr//0AAAAAAAAAK//9AAAAAAAAACv//QAAAAAAAAAACnf6kBP//oAAAXv///3T//6AAA//////5//+gAA"
"3//7MCv///oABP//4QAA3//6AAj//5AAAH//+gAK//9gAABf//oAC///UAAAT//6AAr//2AAAF//+gAI//+QAAB///oABP//4QAA3//6AADP//swK///+gAA"
"P/////+f//oAAAXv///3T//6AAAAKd/rQE//+gAAAAAAAABP//oAAAAAAAAAT//6AAAAAAAAAE//+gAAAAAAAABP//oAAAAAAAAAT//6AAAAAAAAAE//+gAA"
"r//0BL77AK//9I//+wCv//n///sAr//////7AK///9URWACv//4gAAAAr//5AAAAAK//9QAAAACv//QAAAAAr//0AAAAAK//9AAAAACv//QAAAAAr//0AAAA"
"AK//9AAAAACv//QAAAAAAnvv/cpzAAAF///////1AALv//////9QAG//9RATWMUACP/9AAAAAAAAf//9lkIAAAAD//////6TAAAH///////2AAADnv/////h"
"AAAAAUaO//9AAAAAAABv//UATIUyATz//zAF////////wABf///////CAAA2rN7+2lAAAAA///sAAAAD//+wAAAAP//7AAAAA///sAAAAD//+wAACf//////"
"+5///////7n///////sAP//7AAAAA///sAAAAD//+wAAAAP//7AAAAA///sAAAAD//+wAAAAP//7AAAAA///sAAAAB///0AAAADP////9QAE/////1AAA63/"
"//UAz//yAABf//kAAM//8gAAX//5AADP//IAAF//+QAAz//xAABf//kAAM//8QAAX//5AADP//EAAF//+QAAz//xAABf//kAAM//8QAAX//5AADP//EAAG//"
"+QAAz//yAACf//kAAL//9QAB7//5AACP//0wPP//+QAAL/////+f//kAAAb////1X//5AAAASu/ZMF//+QBv//cAAABP//oe//0AAACf//QJ//9AAAHv/9AD"
"//+QAAX//3AAz//gAAv//xAAb//1AB//+QAAHv/7AH//8wAACf//EM//wAAAA///c///YAAAAM//yP/+EAAAAG///v/5AAAAAA7////zAAAAAAn////AAAAA"
"AAL///9gAAAAAAC///4QAAAN//0AAE//8gAA7/+wCf//IAB///UABP//cAX//2AAv//5AAf//zAB//+QAO///QAL//4AAM//0AT///8gDv/6AACP//IH/73/"
"YE//9gAAT//1C/95/5B///IAAA//+Q7/Nf/Qv//QAAAL//0//gL/8v//kAAAB///n/sA3/n//1AAAAP////3AJ////8QAAAA7///8wBf///8AAAAAK///+AA"
"L///+AAAAABv//+wAA3///QAAAAAL///cAAJ///gAAAd//9AAAP//9ED///RAB3//0AAb//6AJ//9wAACv//Vf//sAAAAd//7v/9EAAAAD/////zAAAAAAb/"
"//9wAAAAAAHv//8QAAAAAAr///+wAAAAAG/////4AAAAA///zP//QAAAHf/+Iu//4QAAr//2AF//+wAH//+gAAr//4A///0QAAHf//R///cAAABf//ge//0A"
"AACv//MJ//9AAAHv/8AC//+gAAX//2AAr//xAAr//hAAT//3AB//+QAADP/9AG//8wAABv//QL//0AAAAO//of//cAAAAI//+P//EAAAAB/////6AAAAAAr/"
"///0AAAAAAP////QAAAAAADP//+AAAAAAABf//8gAAAAAAAO//sAAAAAAAAv//UAAAAAAAPP/9AAAAAAP////1AAAAAAP///+QAAAAAAP//bQAAAAAAG////"
"////4Ab////////gBv///////+AAAAAAPv//wAAAAALv//0gAAAALf//0gAAAALf//4gAAAAHf//4wAAAAHP//5AAAAAHP//9AAAAAC///9QAAAACf//9gAA"
"AAAL////////4Av////////gC////////+AAAAAAAozv/3AAAAAAAD7///9wAAAAAADP////cAAAAAAB///lEAAAAAAAA///kAAAAAAAAAT//3AAAAAAAAAE"
"//9gAAAAAAAABP//YAAAAAAAAAT//2AAAAAAAAAF//9gAAAAAAAACv//QAAAAAAAAn///hAAAAAACP////UAAAAAAAj///5QAAAAAAAI////+AAAAAAAAAFv"
"//8gAAAAAAAACP//UAAAAAAAAAX//2AAAAAAAAAE//9gAAAAAAAABP//YAAAAAAAAAT//2AAAAAAAAAD//+QAAAAAAAAAv//5BAAAAAAAADP////cAAAAAAA"
"Pv///3AAAAAAAAKM7/9wAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+g"
"AAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAf/oAAAB/+gAAAH/6AAAAj//sgQAAAAAAAI////4gAAAAAACP//"
"//oAAAAAAAABb///EAAAAAAAAAr//yAAAAAAAAAI//8wAAAAAAAAB///MAAAAAAAAAf//zAAAAAAAAAH//8wAAAAAAAAB///QAAAAAAAAAX//5AAAAAAAAAC"
"///3EAAAAAAAAG////9wAAAAAAAG////cAAAAAAAn////3AAAAAAA///5hAAAAAAAAb//3AAAAAAAAAH//9AAAAAAAAAB///MAAAAAAAAAf//zAAAAAAAAAH"
"//8wAAAAAAAACv//IAAAAAAAAV7//xAAAAAACP////sAAAAAAAj////iAAAAAAAI//7IEAAAAAAAAAAAAAAAAAAAEAAAAGvuyDAAAACHAAAE3////8chJt+A"
"AAD///////////cAAA/4MRSe////+RAAAMIAAAAWvf2TAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAf//0AAAAB///QAAAAH//9AAAAAf//0AAAAB///QAAAAAAAAAAAAAAAAAAAAAAf/8wAAAACf/1AAAAAK//cAAAAAz/+QAAAADv/7"
"AAAAAf//wAAAAB///QAAAAH//9AAAAAf//0AAAAB///QAAAAH//9AAAAAf//0AAAAB///QAAAABL7rQAAAAG////UAAAL/ohr+EAAH/QAA32AACPsAAK+AAA"
"f9AADfYAAC/5EZ/hAAAH////YAAAAEvutAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAC///AAAAv//wAAAL//8AAAC///AAAAv//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"X//5AAAAAABf//kAAAAAAF//+QAAAAAAX//5AAAAAABf//kAAAAAAAAAAAAAAAAAAAAAAAAAAABf//kAAAAAAH//+AAAAAAB3//1AAAAAAv//9EAAAAAn///"
"QAAAAAn///YAAAAAb///cAAAAADf//gAAAAAAP//4QAAAAAA///gAAAAAADf//kgI3tgAG///////2AACP//////YAAAOc7///9gAAAAAAA//5AAAAAAAAAA"
"AM/5AAAAAAAAAAAI/5AAAAAAAAAAAD/6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////yAAAAAAAAAN////gAAAAAAAAE/////gAAAAAAAAn///"
"//QAAAAAAAHv/9//+gAAAAAABv//fP//EAAAAAAL//8W//9gAAAAAC//+wH//8AAAAAAj//1AK//8wAAAADf/+AAT//4AAAABP//kAAO//4AAAAK//8wAAj/"
"/1AAAB7/////////oAAAb//////////xAADP//////////cAAv///////////AAI//+QAAAADf//MA7//0AAAAAI//+QT//+AAAAAAT//+Cv//kAAAAAAO//"
"9QAAAAAD//gAAAAAAAAAz/kAAAAAAAAAj/kAAAAAAAAAP/kAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABv////////wAAG/////////AAAb////////8AABv//"
"//////wAAG///AAAAAAAAAb//8AAAAAAAABv//wAAAAAAAAG///AAAAAAAAAb////////0AABv////////QAAG////////9AAAb////////0AABv//wAAAAA"
"AAAG///AAAAAAAAAb//8AAAAAAAABv//wAAAAAAAAG/////////xAAb/////////EABv////////8QAG/////////xAAAAz/0QAAf/0gAAL/0gAADP0gAAAA"
"AAAAAAAAAAAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv//wAAG///AAAb//8AABv"
"//wAAG///AAAb//8AABv//wAAAAABN6BAO4AAAAAAAAB7//TT8AAAAAAAABvoZ//9wAAAAAAAAj2AF3pAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAG//"
"/7AAAAL//9AABv///0AAAC///QAAb////AAAAv//0AAG////9QAAL//9AABv////0AAC///QAAb/////YAAv//0AAG///f/+EAL//9AABv//jP/4AC///QAA"
"b//4T//hAv//0AAG//+Ar/+QL//9AABv//gD//8i///QAAb//4AJ//ov//0AAG//+AAu//X//9AABv//gACP/9///QAAb//4AAHv////0AAG//+AAAf////9"
"AABv//gAAA3////QAAb//4AAAG////0AAG//+AAAAM///9AABv//gAAABP///QAAAAAAAALv+QAAAAAAAAAAAAv/oAAAAAAAAAAAAH/6AAAAAAAAAAAAAu+w"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFnO/tuDAAAAAAAAXf//////swAAAAAJ/////////2AAAACP//////////UAAAT///+DEUr///4QAA"
"v///QAAAB///+AAB///5AAAAAM///QAF///zAAAAAG///yAH///gAAAAAC///0AJ///QAAAAAB///1AJ///QAAAAAB///1AH///gAAAAAC///0AF///zAAAA"
"AG///yAB///5AAAAAM///QAAv///QAAAB///+AAAT///+DATr///4QAACP//////////UAAAAJ/////////2AAAAAAXf//////wwAAAAAAAFnO/tuDAAAAAA"
"AAAAAAn/4wAAAAAAAAAABP/jAAAAAAAAAAAB7+MAAAAAAAAAAACv4wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAb//8AAAAH///MAAG///AAAAB///z"
"AABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH/"
"//MAAG///AAAAB///zAABv//0AAAAf//8gAAX//9AAAAL///IAAE///xAAAE///wAAAf//9gAACv//wAAADP//5hAo///4AAAAX/////////4QAAAAn/////"
"///1AAAAAAf//////+QAAAAAAAF73v7aYAAAAAAAAA7/QI/6AAAAAAAAAO/0CP+gAAAAAAAADv9Aj/oAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb/"
"/8AAAAH///MAAG///AAAAB///zAABv//wAAAAf//8wAAb//8AAAAH///MAAG///QAAAB///yAABf//0AAAAv//8gAAT///EAAAT///AAAB///2AAAK///AAA"
"AM///mECj///gAAABf/////////hAAAACf////////UAAAAAB///////5AAAAAAAAXve/tpgAAAAAAAAAAAe/7AAAAAAAAAL/7AAAAAAAAAI/7AAAAAAAAAF"
"/7AAAAAAAAAC76AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3re/+yUAAAAB///////+xAAAH////////sAAAa2MhAV3//0AAAAAAAABf//gAAAFq3v////+g"
"AATv///////6AAL/////////oACP//1BAE//+gAL//9AAAb//6AAv//0AADP//oACf//wxO///+gAD//////n//6AABv////hP//oAAAOu/qQE//+gAAAAAA"
"AAn/4wAAAAAAAAX/4wAAAAAAAALv4wAAAAAAAAHf4wAAAAAAAACv4wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA5zv7JMAAAAAG//////6EAAALf///////B"
"AAC///sxKv//kABP//wAAAz//xAI//9gAAB///YAv/////////+ADP/////////5AL//////////oAj//1AAAAAAAABP//sAAAAAAAAAv//7QQEkesAAAt//"
"//////4AAAK////////gAAAAOM7+3LhRAAAAAG//UAAAP/9QAAAd/1AAAAv/UAAACP9QAAAAAAAAAAAAAAAAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9A"
"AACv//QAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9AAACv//QAAAr//0AAAK//9AAACv//QAAAAAA85wAM4QAAAAAAz/9wDvAAAAAAA/0r9k/AAAAAAAX4"
"Ac//cAAAAAAG5wAb+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK//9AOt/aMAAACv//Rv////YAAAr//5//////IAAK///7ME7//3AACv//4QAG//+gAAr//4"
"AABP//sAAK//9QAAP//7AACv//QAAD//+wAAr//0AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0AAA///sAAK//9AAAP//7AACv//QAAD//+wAAr//0"
"AAA///sAAAAAAAAJ/+MAAAAAAAAG/+MAAAAAAAAD7+MAAAAAAAAB3+MAAAAAAAAAr+MAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAASc7+2lAAAAACv//////U"
"AAAC3///////9AAAv//8MCn//+EAT//+EAAL//9wCP//gAAAX//8AL//9QAAAv//4Az//1AAAB///wC///UAAAL//+AI//+AAABf//wAT//+EAAL//9wAM//"
"/DAp///hAALv///////0AAACv//////UAAAAAEnO/tpQAAAAAAAAAAT/+AAAAAAAAAAe/4AAAAAAAAAAv/gAAAAAAAAACP+AAAAAAAAAAF/3AAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAM//8gAAX//5AADP//IAAF//+QAAz//yAABf//kAAM//8QAAX//5AADP//EAAF//+QAAz//xAABf//kAAM//8QAAX//5AADP//EA"
"AF//+QAAz//xAABv//kAAM//8gAAn//5AAC///UAAe//+QAAj//9MDz///kAAC//////n//5AAAG////9V//+QAAAErv2TBf//kAAAAG/8AP/zAAAAAABv/A"
"D/8wAAAAAAb/wA//MAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADP//IAAF//+QAAz//yAABf//kAAM//8gAAX//5AADP//EA"
"AF//+QAAz//xAABf//kAAM//8QAAX//5AADP//EAAF//+QAAz//xAABf//kAAM//8QAAb//5AADP//IAAJ//+QAAv//1AAHv//kAAI///TA8///5AAAv////"
"/5//+QAABv////Vf//kAAABK79kwX//5AAAAT///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAA"
"AE///7AAAAAAP///sAAAAAAv//+gAAAAAB///4AAAAAADv//YAAAAAAM//9QAAAAAAr//zAAAAAACf//EAAAAAAH//4AAAAAAAAAAAAAAAAAAAAAAAAAAABP"
"//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAAz/8wB//3AAAAz/8wB//3AAAAz/8wB//3AAAAz/8wB//3AAAAz/8wB//3AA"
"AAz/8wB//3AAAAz/8wB//3AAAAz/8wB//3AAAAz/8wB//3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAL/+AACf/xAAAAAAAAAA7/sAAN/8AAAAAAAAAAT/9wAC//gAAAAAAAAACP/zAAb/9AAAAAAAAAAM/+AACv/gAAAAAAAAAB//oAAO/7AAAAAADP////"
"/////////zAAAM//////////////MAAAz/////////////8wAADP/////////////zAAAAAAP/+AAC//kAAAAAAAAAB//0AAX/9QAAAAAAAAAK//EACf/yAA"
"AAAAAAAA7/wAAM/+AAAAAAAAAAL/+QAB//oAAAAAAK//////////////QAAAr/////////////9AAACv/////////////0AAAK//////////////QAAAAAA/"
"/4AAL/+AAAAAAAAAAH//QABv/0AAAAAAAAAAv/4AAK//EAAAAAAAAADv+wAA3/sAAAAAAAAABP/3AAP/9wAAAAAAAAAI//MABv/zAAAAAAAAAAAAAH/zAAAA"
"AAAAAAAAAH/zAAAAAAAAAAAAAH/zAAAAAAAAAAAAAH/zAAAAAAAAAAAWrO/+uEAAAAAAABn///////6SAAAAAc/////////9AAAACf/////////9AAAAH///"
"1I/0JZ79AAAAT///IH/zAABaAAAAX///AH/zAAAAAAAAT///UH/zAAAAAAAAH///+r/zAAAAAAAACv//////yVEAAAAAAt////////6BAAAAABr////////9"
"EAAAAAAnvv//////kAAAAAAAAI/73///8QAAAAAAAH/zB///9AAAAAAAAH/zAP//9QAASjAAAH/zAf//9AAAX/2FIH/0O///8QAAX///////////oAAAX///"
"///////9EAAABb////////+hAAAAAAFpzv/+ynIAAAAAAAAAAI/zAAAAAAAAAAAAAH/zAAAAAAAAAAAAAH/zAAAAAAAAAAAAAH/zAAAAAAAAAAAAAH/zAAAA"
"AAAAAErf7HEAAAAAAG//UAAAAAAK/////jAAAAAB7/oAAAAAAJ//////4gAAAAn/4gAAAAAD//9hPf/5AAAAT/9wAAAAAAn/+wAE//8AAADP/AAAAAAADP/2"
"AADv/zAAB//zAAAAAAAN//QAAN//UAAu/5AAAAAAAA3/9AAA3/9QAL/+EAAAAAAADP/2AADv/zAF//UAAAAAAAAI//sABP//AB3/sAAAAAAAAAP//2E9//kA"
"n/8gAAAAAAAAAJ//////4gP/9wAXzv6lAAAACv////4wDP/QA9////+xAAAASt/scQBv/0Ae//////oAAAAAAAAAAe/6AJ//0wb//0AAAAAAAAAK/+EA7/9Q"
"AK//oAAAAAAAAE//YAP//wAAX//QAAAAAAAB3/wABP/+AABP/+AAAAAAAAj/8wAE//4AAE//4AAAAAAAL/+AAAP//wAAX//QAAAAAAC//RAAAO//UACv/5AA"
"AAAABv/0AAAAn//TBv//QAAAAAAe/6AAAAAe//////oAAAAAAJ/+IAAAAAPf////sQAAAAAE//cAAAAAABfO/qUAAAAAAAAEne/tuFIAAAAAAAAAAALP////"
"//8AAAAAAAAAAC7///////8AAAAAAAAAAL////////8AAAAAAAAAAf///3ECWv8AAAAAAAAAA///+wAAACsAAAAAAAAAA////AAAAAAAAAAAAAAAAO///1AA"
"AAAAAAAAAAAAAH///+MAAAAAAAAAAAAAAE////4gAAAAAAAAAAAACP/////SAAAC///wAAAAn//////9EAAD///QAAAI///97///wQAG//+wAAAv///RPv//"
"/BAL//9wAACP//9ABP///7Ev//8wAADP//4AAF////u///0AAADv//wAAAb///////UAAADv//4AAAB//////8AAAADP//9QAAAJ/////iAAAACP///iAAAA"
"z///+AAAAAAv///+cgFb/////0AAAAAH/////////////+MAAAAAj/////////////4gAAAABN///////5Tv///RAAAAAASc7/7JUQBP///7AAAM//MAAAz/"
"8wAADP/zAAAM//MAAAz/8wAADP/zAAAM//MAAAz/8wAADP/zAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABv//gAAAAAAe//4QAAAAAI//+AAAAAAC///yAAAAAAj//7AAAAAAHv//UAAAAABv//4AAAAAAM//+gAA"
"AAAB///2AAAAAAX///IAAAAACf//4AAAAAAM///AAAAAAA7//7AAAAAAD///kAAAAAAf//+QAAAAAB///5AAAAAAD///kAAAAAAO//+gAAAAAAz//8AAAAAA"
"Cf//4AAAAAAG///yAAAAAAL///YAAAAAAM//+gAAAAAAb//+AAAAAAAe//9QAAAAAAn//6AAAAAAAv//8gAAAAAAj//4AAAAAAAe//4QAAAAAAb//4AAAB7/"
"/hAAAAAACP//gAAAAAAB7//yAAAAAACf//kAAAAAAD///yAAAAAADP//gAAAAAAH///gAAAAAAL///UAAAAAAN//+QAAAAAAr//+AAAAAAB///8gAAAAAE//"
"/1AAAAAAP///cAAAAAAf//+AAAAAAB///5AAAAAAH///kAAAAAAf//+AAAAAAD///3AAAAAAT///UAAAAAB///8gAAAAAK///gAAAAAA3//5AAAAAAL///UA"
"AAAAB///4AAAAAAM//+AAAAAAD///yAAAAAAn//5AAAAAAHv//IAAAAACP//gAAAAAAe//4QAAAAAAAACP9QAAAAAAAACP9QAAAAAAAACP9QAAAABbMACP9Q"
"AEwgDf+iCP9QTP+gGv//mf+L//6AACr//////oEAAAAp///+gQAAAAAq////kQAAACr//////oEAGv//mf97//6ADf+iCP9QS/+gBbMACP9QAEwgAAAACP9Q"
"AAAAAAAACP9QAAAAAAAACP9QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAv/8wAAAAAAAAAAAAAAC//zAAAAAAAAAAAAAAAL//MAAAAAAAAAAAAAAAv/8wAAAAAAAAAAAAAAC//zAAAAAAAAAAAAAAAL//"
"MAAAAAAAAAAAAAAAv/8wAAAAAAAAAAAAAAC//zAAAAAAAAAAAAAAAL//MAAAAAAAAAb/////////////0AAABv/////////////QAAAG/////////////9AA"
"AAb/////////////0AAAAAAAAAC//zAAAAAAAAAAAAAAAL//MAAAAAAAAAAAAAAAv/8wAAAAAAAAAAAAAAC//zAAAAAAAAAAAAAAAL//MAAAAAAAAAAAAAAA"
"v/8wAAAAAAAAAAAAAAC//zAAAAAAAAAAAAAAAL//MAAAAAAAAAAAAAAAv/8wAAAAAAAACP//9wAAAI///3AAAAj///cAAACP//9wAAAI///3AAAAr//+IAAA"
"Dv//YAAAA///sAAAAI//4gAAAAz/9QAAAAH/+gAAAAAC//////9AAv//////QAL//////0AC//////9AAv//////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAj///cAAACP//9wAAAI///3AAAAj///cAAACP//9wAAAI///3AAAAAAAG//QAAAAAv/4AAAAAH/"
"+gAAAABf/1AAAAAK//EAAAAA7/sAAAAAT/9gAAAACf/xAAAAAO/7AAAAAD//cAAAAAj/8gAAAADf/AAAAAA//4AAAAAH//MAAAAAz/0AAAAAL/+QAAAABv/0"
"AAAAAL/+AAAAAB//oAAAAAX/9QAAAACv/xAAAAAO/7AAAAAE//YAAAAAn/8QAAAADv+wAAAAA//3AAAAAI//IAAAAA3/wAAAAAAAAAACe9/tphAAAAAAAAGf"
"/////+YAAAAAAC3///////+QAAAAAN/////////4AAAACP///UEX////MAAAH///8gAAf///sAAAf///oAAAH///8gAAz///YAAAC///9gAA7///QAAACf//"
"+QAC////IAAAB////AAE////EAAABv///gAF////EAAABv///wAF////AAAABf///wAF////EAAABv///wAE////EAAABv///gAD////IAAAB////AAA7///"
"QAAACf//+QAAz///YAAADP//9gAAf///oAAAH///8gAAH///8wAAj///sAAACP///UEX////MAAAAN/////////4AAAAAC3///////+QAAAAAAGf/////+YA"
"AAAAAAACe9/tphAAAAAAACR6z///+gAAAAAAA///////+gAAAAAAA///////+gAAAAAAA///////+gAAAAAAA///////+gAAAAAAA9uGNv//+gAAAAAAAAAA"
"Bv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAA"
"AAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAAAABv//+gAAAAAAAP//////////9QAAAP//"
"////////9QAAAP//////////9QAAAP//////////9QAAAP//////////9QAAAles3v/sphAAAAAAT////////+cAAAAAT/////////+gAAAAT//////////4"
"AAAAT/2EIBS/////EAAASjAAAAAK////UAAAAAAAAAAB////cAAAAAAAAAAA7///gAAAAAAAAAAA////YAAAAAAAAAAF////EAAAAAAAAAAu///5AAAAAAAA"
"AALf///RAAAAAAAAAC3///0gAAAAAAAAA+///9IAAAAAAAAATv///CAAAAAAAAAG////sQAAAAAAAAB////6AAAAAAAAAAj///+AAAAAAAAAAK////cAAAAA"
"AAAAG////2AAAAAAAAAAX///////////sAAAX///////////sAAAX///////////sAAAX///////////sAAAX///////////sAAACv/////spiAAAAAACv//"
"//////kQAAAACv/////////BAAAACv/////////5AAAACbdDECS/////EAAAAAAAAAAK////QAAAAAAAAAAC////UAAAAAAAAAAB////UAAAAAAAAAAC////"
"IAAAAAAAAAAJ///7AAAAAAAAABS////iAAAAAAB///////sgAAAAAAB//////5EAAAAAAAB///////5wAAAAAAB////////5AAAAAAAAABN+////UAAAAAAA"
"AAAB3///sAAAAAAAAAAAj///4AAAAAAAAAAAj///4AAAlgAAAAAB3///wAAAv+lSEBN+////cAAAv//////////9EAAAv//////////TAAAAv////////+kQ"
"AAAAFHrN7/7blRAAAAAAAAAAAA3///+AAAAAAAAAAI////+AAAAAAAAAA/////+AAAAAAAAADP////+AAAAAAAAAf/////+AAAAAAAAC7//f//+AAAAAAAAL"
"//x///+AAAAAAABv//J///+AAAAAAALv/3B///+AAAAAAAr//AB///+AAAAAAF//8wB///+AAAAAAe//cAB///+AAAAACv/8AAB///+AAAAAT//zAAB///+A"
"AAAB3/+AAAB///+AAAAH//wAAAB///+AAAAH/////////////xAH/////////////xAH/////////////xAH/////////////xAH/////////////xAAAAAA"
"AAB///+AAAAAAAAAAAB///+AAAAAAAAAAAB///+AAAAAAAAAAAB///+AAAAABv/////////3AAAABv/////////3AAAABv/////////3AAAABv/////////3"
"AAAABv/////////3AAAABv//sAAAAAAAAAAABv//sAAAAAAAAAAABv//sAAAAAAAAAAABv//3O/ttyAAAAAABv////////kQAAAABv/////////RAAAABv//"
"///////8AAAABshTIBOP////YAAAAAAAAAAE////wAAAAAAAAAAAj///8QAAAAAAAAAAP///8wAAAAAAAAAAL///9AAAAAAAAAAAP///8wAAAAAAAAAAj///"
"8QAAWTAAAAAE////sAAAb/yEIBOP////UAAAb//////////6AAAAb/////////+wAAAAb////////+YAAAAAAli83v/slQAAAAAAAAAAFZzf////MAAAAAAG"
"7///////MAAAAAG/////////MAAAAAz/////////MAAAAJ///+hBATWMMAAABP///SAAAAAAAAAACv//8wAAAAAAAAAAL///oAAAAAAAAAAAX///Yozv7IIA"
"AAAAn///v/////+AAAAAv//////////6AAAAz///////////gAAA3////4EDv///4QAA3///+QAAHv//9gAAz///8wAACf//+gAAv///8AAABv///AAAj///"
"8AAABf///AAAX///8AAABv//+wAAHv//8wAACf//+AAACv//+QAAHv//9AAAAv///4EDv///wAAAAH/////////+MAAAAAj////////kAAAAAABu//////wg"
"AAAAAAABat7+yEAAAAAAv///////////4AAAv///////////4AAAv///////////4AAAv///////////4AAAv///////////gAAAAAAAAAAB7///IAAAAAAA"
"AAAH///6AAAAAAAAAAAO///zAAAAAAAAAABv//+wAAAAAAAAAADf//9QAAAAAAAAAAX///0AAAAAAAAAAAv///YAAAAAAAAAAD///+AAAAAAAAAAAK///3AA"
"AAAAAAAAAv///hAAAAAAAAAACf//+QAAAAAAAAAAHv//8gAAAAAAAAAAj///oAAAAAAAAAAB7///QAAAAAAAAAAG///8AAAAAAAAAAAN///1AAAAAAAAAABf"
"///QAAAAAAAAAADP//9gAAAAAAAAAAT///4QAAAAAAAAAAv///gAAAAAAAAAAAAnre/+ylEAAAAAABr///////5wAAAAAt/////////5AAAACv//////////"
"UAAAL////EEW7///sAAAT///4QAAb///4AAAX///sAAAL///8AAAT///sAAAL///0AAAHv//4QAAb///kAAAB////EEW7//+IAAAAI/////////jAAAAAAOv"
"/////+cQAAAAABff//////tAAAAAAt/////////5AAAAHf//+jEV3///gAAAf///oAAALv//8gAAz///QAAACv//9gAA3///IAAACP//+AAA3///QAAACv//"
"9wAAv///oAAALv//9QAAf///+jEV3///8QAAHv//////////kAAABO/////////8EAAAADv///////+BAAAAAAA4ve/+ymEAAAAAAAAWre/cgwAAAAAAAAbv"
"/////7IAAAAAAK////////4wAAAACP/////////hAAAAP///9xA8///6AAAAr///gAAB7///MAAA7///IAAAn///kAAC////AAAAb///4AAD///+AAAAX///"
"8gAD////AAAAb///9QAB////IAAAn///9gAA3///gAAB7///9wAAf///9xA8////9wAAHf//////////9gAAA+//////////9QAAACz/////3f//8wAAAABJ"
"3v62HP//4AAAAAAAAAAAH///oAAAAAAAAAAAn///QAAAAAAAAAAG///8AAAACLdCECW////zAAAACf////////9gAAAACf////////UAAAAACf//////+zAA"
"AAAACf///+23MAAAAAAAA////AAAAAP///wAAAAD///8AAAAA////AAAAAP///wAAAAD///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAP///wAAAAD///8AAAAA////AAAAAP///wAAAAD///8AAAAA////AAAAAP///wAAAAD///8AAAAA////AAAAAP///wAAAAD///8"
"AAAAA////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///8AAAAA////AAAAAP///wAAAAD///8AAAAA///"
"/AAAAAX///YAAAAJ//+wAAAADv/+IAAAAD//9gAAAAB//6AAAAAAv/4QAAAAAAAAAAAAAAAAAAAosAAAAAAAAAAAAAABfP/QAAAAAAAAAAAAFb///9AAAAAA"
"AAAAAErv////0AAAAAAAAAOe/////9kwAAAAAAAo3/////6UAAAAAAACfP/////pQAAAAAAAA7/////+lAAAAAAAAAAG////6UAAAAAAAAAAAAb///kQAAAA"
"AAAAAAAABv///+lAAAAAAAAAAAADv/////6UAAAAAAAAAAACfP/////pQAAAAAAAAAAAKN/////+lAAAAAAAAAAAA57/////2DAAAAAAAAAAAFrv////0AAA"
"AAAAAAAAABa////QAAAAAAAAAAAAAAF8/9AAAAAAAAAAAAAAAAAosAAAAAAAAAAAAAAAAAAAAAAG/////////////9AAAAb/////////////0AAABv//////"
"///////QAAAG/////////////9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABv/////////////Q"
"AAAG/////////////9AAAAb/////////////0AAABv/////////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABaUAAAAAAAAAAAAAAAAG/+lAAAAAAAAAAAAAAAb///2DAAAAAAAAAAAABv/////HIAAAAAAAAAABa//////7YQAA"
"AAAAAAAAFr//////pRAAAAAAAAAAAWz/////6UAAAAAAAAAAACfP/////oAAAAAAAAAAAAJ8////0AAAAAAAAAAAAABN///QAAAAAAAAAAACbP///9AAAAAA"
"AAAAFr/////+gAAAAAAAAWv/////6UAAAAAAABa//////7UQAAAAAAFr//////xhAAAAAAAABv/////XIAAAAAAAAAAG///9gwAAAAAAAAAAAAb/6UAAAAAA"
"AAAAAAAABaUAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABR6ze/spQAAAACv///////UAAAAr////////0AAAK/////////QAACv6EECn///9AAAhgAAAAv/"
"//cAAAAAAAAI///3AAAAAAAAC///9gAAAAAAAE////IAAAAAAAPv//+gAAAAAAA+///+EAAAAAAD7///4wAAAAAAHf///jAAAAAAAJ///+MAAAAAAADv//9A"
"AAAAAAAC///9AAAAAAAAA////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////AAAAAAAAAP///wAAAAAAAAD///8AAAAAAAAA////AAAAAAAAAP///wA"
"AAAAAAAD///8AAAAAAAAAAAAADi97+2nIAAAAAAAAAAAAABd///////7QAAAAAAAAAAATP/////////6EAAAAAAAAAb//+lSEBNr///TAAAAAAAAj//nEAAA"
"AAAr//4gAAAAAAb//CAAAAAAAABv/9EAAAAAP/+xAAAAAAAAAAX/+QAAAAC//RAAAAAAAAAAAG//MAAABP/zAAAErv2Bb/8QC/+QAAAL/5AAAI////1//xAE"
"//AAAC//MAAH/////+//EADv9AAAX/0AAC//9xF///8QAL/3AACP+QAAj/+AAAf//xAAn/gAAK/3AADP/xAAAf//EACP+QAAv/YAAO/+AAAA3/8QAJ/4AAC/"
"9gAA//wAAADP/xAAv/YAAK/3AADv/gAAAN//EAHv8gAAn/kAAM//EAAB//8QB//QAABv/QAAj/+AAAj//xA+/2AAAC//MAAv//cRb///N+/7AAAADP+gAAj/"
"////7////8EAAAAG//MAAJ////1////oAAAAAADf/RAABK79gW/9phAAAAAAAE//sAAAAAAAAAAAAAAAAAAACP/8EAAAAAAAAaQAAAAAAAAAn//nAAAAAABd"
"/RAAAAAAAAAH///pUhAkjf//cAAAAAAAAABN//////////kQAAAAAAAAAABt///////5MAAAAAAAAAAAAABIvv/clRAAAAAAAAAAAAAN////8gAAAAAAAAAA"
"A/////+AAAAAAAAAAACf/////QAAAAAAAAAADv/////0AAAAAAAAAAX//////5AAAAAAAAAAr//////+EAAAAAAAAB///+r///UAAAAAAAAG///6X///sAAA"
"AAAAAM///1Dv//8QAAAAAAAv///gCv//9wAAAAAACP//+QBf///AAAAAAADf//9AAO///zAAAAAAT///4AAJ///4AAAAAAn///kAAE///+AAAAAA7///QAAA"
"7///QAAAAF///+AAAAn///oAAAAL////////////4QAAAf////////////9gAAB/////////////+wAADP/////////////yAAP//////////////3AAj///"
"4QAAAAAK///9AA7///kAAAAAAE////ME////MAAAAAAA3///kK///8AAAAAAAAf///4AAA3//////+2oMAAAAAAN//////////wwAAAADf//////////4wAA"
"AA3///////////wAAAAN///4AAFN////MAAADf//+AAAA////2AAAA3///gAAADv//9wAAAN///4AAAA7///YAAADf//+AAAA////zAAAA3///gAAU3///wA"
"AAAN///////////iAAAADf/////////7EAAAAA3//////////6EAAAAN///////////9IAAADf//+AABKP///6AAAA3///gAAABv///yAAAN///4AAAAD///"
"9gAADf//+AAAAA7///gAAA3///gAAAAP///3AAAN///4AAAAb///9QAADf//+AAAKP////EAAA3///////////+gAAAN///////////8EAAADf//////////"
"kQAAAA3///////7KYQAAAAAAAAACac3v7JYQAAAAAAA6////////kgAAAACP/////////8AAAAC///////////wAAACv///////////AAAB/////6EEBJZ78"
"AAAe////wQAAAAAFkAAH////wQAAAAAAAAAAv///8wAAAAAAAAAAH////AAAAAAAAAAAAv///4AAAAAAAAAAAD////YAAAAAAAAAAAT///9QAAAAAAAAAAA/"
"///2AAAAAAAAAAAC////gAAAAAAAAAAAH////AAAAAAAAAAAAL////MAAAAAAAAAAAf////BAAAAAAAAAAAe////wQAAAAAFkAAAf////+hBASWe/AAAAK//"
"/////////8AAAAG///////////wAAAAAj//////////AAAAAADr///////+SAAAAAAACac3v7JYQAAAADf/////ty4UgAAAAAAAN//////////tAAAAAAA3/"
"//////////oQAAAADf///////////8EAAAAN/////////////AAAAA3///gAElnv////kAAADf//+AAAABr////yAAAN///4AAAAAK////kAAA3///gAAAAA"
"Hv///QAADf//+AAAAAAJ////IAAN///4AAAAAAX///9AAA3///gAAAAAA////2AADf//+AAAAAAC////YAAN///4AAAAAAP///9gAA3///gAAAAABf///0AA"
"Df//+AAAAAAJ////IAAN///4AAAAAB7///0AAA3///gAAAAAv///+QAADf//+AAAABv////yAAAN///4ABJZ7////5AAAA3////////////8AAAADf//////"
"/////8EAAAAN///////////6EAAAAA3/////////+0AAAAAADf/////ty4UQAAAAAAAN//////////9gAADf//////////YAAA3//////////2AAAN//////"
"////9gAADf//////////YAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN//////////sAAADf/////////7AAAA3///"
"//////+wAAAN//////////sAAADf/////////7AAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf"
"//+AAAAAAAAAAA3//////////7AAAN//////////+wAADf//////////sAAA3//////////7AAAN//////////+wAAAN//////////9gAADf//////////YA"
"AA3//////////2AAAN//////////9gAADf//////////YAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN//////////"
"sAAADf/////////7AAAA3/////////+wAAAN//////////sAAADf/////////7AAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAA"
"AAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN///4AAAAAAAAAAAAAAAB"
"Wc3v7cliAAAAAAAAAp/////////GEAAAAAB///////////9wAAAAC////////////3AAAACv////////////cAAABv////+lIQEljf9wAAAe////wgAAAAAA"
"OXAAAG////0QAAAAAAAAAAAAv///8wAAAAAAAAAAAAD////AAAAAAAAAAAAAAv///4AAAAAAAAAAAAAD////YAAACP/////2AAT///9QAAAI//////YAA///"
"/2AAAAj/////9gAC////cAAACP/////2AAH///+wAAAAAAr///YAAL////MAAAAACv//9gAAf////BAAAAAK///2AAAe////sgAAAAr///YAAAf////+lCAB"
"TP//9gAAAK/////////////2AAAAG/////////////YAAAAAj///////////1AAAAAADr////////7UAAAAAAAACac3v7bhRAAAAAA3///gAAAAAH///9QAA"
"Df//+AAAAAAf///1AAAN///4AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAAAAAf///1AAAN///4AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAA"
"AAAf///1AAAN///4AAAAAB////UAAA3/////////////9QAADf/////////////1AAAN//////////////UAAA3/////////////9QAADf/////////////1"
"AAAN///4AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAAAAAf///1AAAN///4AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAAAAAf///1AAAN///4"
"AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAAAAAf///1AAAN///4AAAAAB////UAAA3///gAAAAAH///9QAADf//+AAAAN///4AAAA3///gAAADf//+A"
"AAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///"
"gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN//"
"/4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN//"
"/4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAN///4AAAAAO///3AAAAAv///2AAAACv///zAAADr////gAA7/////+AAA7/////0QAA7////+"
"MAAA7///+hAAAA7+23IAAAAAAA3///gAAAABv///+QAADf//+AAAABv///+QAAAN///4AAABv///+QAAAA3///gAABv///+QAAAADf//+AABz///+QAAAAAN"
"///4ABz///+QAAAAAA3///gBz///+QAAAAAADf//+Bz///+QAAAAAAAN///5z///+QAAAAAAAA3///////+QAAAAAAAADf//////+QAAAAAAAAAN//////+Q"
"AAAAAAAAAA3//////8EAAAAAAAAADf///////BAAAAAAAAAN////////wQAAAAAAAA3///vv///8EAAAAAAADf//+D7////BAAAAAAAN///4A+////wQAAAA"
"AA3///gAPv///8EAAAAADf//+AAD7////BAAAAAN///4AAA+////wQAAAA3///gAAAPv///8EAAADf//+AAAAD7////BAAAN///4AAAAA+////wQAA3///gA"
"AAAAPv///8EADf//+AAAAAAAAAAN///4AAAAAAAAAA3///gAAAAAAAAADf//+AAAAAAAAAAN///4AAAAAAAAAA3///gAAAAAAAAADf//+AAAAAAAAAAN///4"
"AAAAAAAAAA3///gAAAAAAAAADf//+AAAAAAAAAAN///4AAAAAAAAAA3///gAAAAAAAAADf//+AAAAAAAAAAN///4AAAAAAAAAA3///gAAAAAAAAADf//+AAA"
"AAAAAAAN///4AAAAAAAAAA3///gAAAAAAAAADf//+AAAAAAAAAAN///4AAAAAAAAAA3//////////7AADf//////////sAAN//////////+wAA3/////////"
"/7AADf//////////sAAN////9wAAAAAAr////7AAAA3////9AAAAAAH/////sAAADf////9QAAAAB/////+wAAAN/////7AAAAAO/////7AAAA3/////8wAA"
"AF//////sAAADf/////5AAAAz/////+wAAAN//////4QAAP//////7AAAA3///r//3AACv//r///sAAADf//9O//0AAf//1f//+wAAAN///zn//1AH//91//"
"/7AAAA3///M///sA3//hX///sAAADf//8wv//yX//5Bf//+wAAAN///zBf//nP//IF///7AAAA3///MA3/////sAX///sAAADf//8wB/////9ABf//+wAAAN"
"///zAB7////QAF///7AAAA3///MACf///3AAX///sAAADf//8wAD///+EABf//+wAAAN///zAAC///kAAF///7AAAA3///MAAF//8gAAX///sAAADf//8wAA"
"AAAAAABf//+wAAAN///zAAAAAAAAAF///7AAAA3///MAAAAAAAAAX///sAAADf//8wAAAAAAAABf//+wAAAN///zAAAAAAAAAF///7AAAA3///+AAAAAC///"
"9QAADf///+EAAAAL///1AAAN////+QAAAAv///UAAA3/////IAAAC///9QAADf////+QAAAL///1AAAN//////IAAAv///UAAA3/////+gAAC///9QAADf//"
"////MAAL///1AAAN///6//+wAAv///UAAA3///Pv//QAC///9QAADf//82///AAL///1AAAN///zDf//UAv///UAAA3///MG///AC///9QAADf//8wDf//UL"
"///1AAAN///zAF///Qv///UAAA3///MADP//a///9QAADf//8wAE///r///1AAAN///zAAC///////UAAA3///MAAD//////9QAADf//8wAACv/////1AAAN"
"///zAAAD//////UAAA3///MAAACv////9QAADf//8wAAAC/////1AAAN///zAAAACf////UAAA3///MAAAAB7///9QAAAAAABIve/ttzAAAAAAAAAABt////"
"///8UAAAAAAAAb//////////oQAAAAAC7///////////0QAAAAHP////////////sAAAAJ////+kEBW/////cAAAL////2AAAAB////+EAAI////gAAAAACv"
"///2AADP///hAAAAAAL///+gAB////oAAAAAAAz///4AAv///3AAAAAAAI////AAT///9QAAAAAAB////yAE////UAAAAAAAb///8gBP///1AAAAAAAH////"
"IAL///9wAAAAAACP///wAB////oAAAAAAAz///4AAM///+EAAAAAAv///6AACP///4AAAAAAr///9gAAL////2AAAAB////+EAAAn////6QQFb////9wAAAB"
"z////////////7AAAAAC7///////////0QAAAAABz/////////+hAAAAAAAAbf///////FAAAAAAAAAABIve/ttzAAAAAAAADf//////7bhAAAAAAN//////"
"////1AAAAA3///////////YAAADf///////////0AAAN////////////wAAA3///gAATn////yAADf//+AAAAH////YAAN///4AAAAL///9wAA3///gAAAAv"
"///3AADf//+AAAAH////YAAN///4AAE5////8gAA3////////////AAADf///////////0AAAN///////////2AAAA3//////////UAAAADf//////7shAAA"
"AAAN///4AAAAAAAAAAAA3///gAAAAAAAAAAADf//+AAAAAAAAAAAAN///4AAAAAAAAAAAA3///gAAAAAAAAAAADf//+AAAAAAAAAAAAN///4AAAAAAAAAAAA"
"3///gAAAAAAAAAAADf//+AAAAAAAAAAAAAAAAASL3v7bdAAAAAAAAAAAbf///////WAAAAAAAAG//////////7EAAAAAAu///////////9IAAAABz///////"
"/////8AAAACf////pBAVv////3AAAC////9gAAAAf////hAACP///4AAAAAAr///9gAAz///4QAAAAAC////oAAf///6AAAAAAAM///+AAL///9wAAAAAACP"
"///xAE////UAAAAAAAf///8gBP///1AAAAAAAG////MAT///9QAAAAAAB////yAC////cAAAAAAAj///8QAf///6AAAAAAAM///9AADP///hAAAAAAL///+g"
"AAj///+AAAAAAK////UAAC////9QAAAAf////QAAAJ////+kEBW/////UAAAAd////////////+QAAAAAu///////////7AAAAAAAs//////////gAAAAAAA"
"AG3///////swAAAAAAAAAASL3v///8AAAAAAAAAAAAAAAH///5AAAAAAAAAAAAAAAK///2AAAAAAAAAAAAAAAc///0AAAAAAAAAAAAAAAu///iAAAAAAAAAA"
"AAAABP///BAAAA3//////+23MAAAAAAN//////////sgAAAADf//////////4gAAAA3///////////oAAAAN////////////EAAADf//+AABXf///0AAAA3/"
"//gAAAT///9QAAAN///4AAAB////QAAADf//+AAABP///xAAAA3///gAAV3///oAAAAN///////////RAAAADf/////////6EAAAAA3////////+QAAAAAAN"
"//////////YAAAAADf//////////UAAAAA3///gAKf///+EAAAAN///4AAB////4AAAADf//+AAADP///hAAAA3///gAAAX///9wAAAN///4AAAA3///4QAA"
"Df//+AAAAG////YAAA3///gAAAAN///9AAAN///4AAAAB////1AADf//+AAAAAHv///AAA3///gAAAAAj///9AAAABet7/7bhiAAAAAAGP////////1AAAAB"
"v/////////9gAAAJ//////////9gAAAf//////////9gAABv///4MQEljf9gAACP//9wAAAAADlQAACP//9AAAAAAAAAAAB///+gAAAAAAAAAAA////9lSAA"
"AAAAAAAL///////JUAAAAAAB3////////oEAAAAAGf////////0wAAAAABe+///////hAAAAAAAANY3////4AAAAAAAAAABN///8AAAAAAAAAAAF///+AABY"
"EAAAAAAD////AABf5xAAAAAH///9AABf//pjEBSf///7AABf///////////2AABf///////////QAABf//////////4wAAAWv////////7IAAAAAAUit7/7b"
"cgAAAM//////////////8M//////////////8M//////////////8M//////////////8M//////////////8AAAAACf///AAAAAAAAAAACf///AAAAAAAAA"
"AACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///A"
"AAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAA"
"AACf///AAAAAAAAAAACf///AAAAAAAAAAACf///AAAAAAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AA"
"AA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gA"
"AAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAM///4AAAAAO///2AAAAv///oAAAAB////"
"UAAACf///gAAAAX///8wAAAF////YAAADP///gAAAAHv///4IBS////6AAAAAJ////////////MAAAAAHf//////////gAAAAAAD3/////////oAAAAAAAAa"
"///////9YAAAAAAAAAAnre/tyVAAAAAAr///wAAAAAAAB////gT///8gAAAAAADP//+QDv//9wAAAAAAP///8wCP///QAAAAAAj///0AA////zAAAAAA3///"
"cAAM///4AAAAAE////IAAH///9AAAAAJ///7AAAB////QAAAAO///2AAAAv///kAAABP///hAAAAX///4AAACv//+gAAAADv//9QAAHv//9AAAAACf//+gAA"
"X///4AAAAABP///xAAv///gAAAAAAN///2AB////MAAAAAAI///7AG///8AAAAAAAC////IM///3AAAAAAAAz///cv///xAAAAAAAAb///x///+wAAAAAAAA"
"H////v//9QAAAAAAAACv//////4QAAAAAAAABf//////kAAAAAAAAAAO//////QAAAAAAAAAAJ/////9AAAAAAAAAAAD/////4AAAAAAAAAAAA3////yAAAA"
"AAAN///0AAAAB////gAAAAC///9QCv//9wAAAAr///8wAAAA////EAb///sAAAAO////YAAAA////QAC///+AAAAL////6AAAAf///kAAO///zAAAG/////Q"
"AAAL///2AACv//9wAACf////8gAADv//8gAAf///oAAA3/+///UAAD///+AAAD///+AAAf//bv/5AABv//+gAAAO///yAAX//yr//AAAr///cAAAC///9gAI"
"//4H//8QAN///zAAAAj///kADP/6A///QAL///4AAAAE///9AB//9wDv/4AF///7AAAAAf///xBP//MAv/+wCf//+AAAAADP//9Qf//gAH//4Az///QAAAAA"
"n///gL//sABP//Mf///xAAAAAF///8Dv/4AAH//3T///wAAAAAAf///z//9AAAz/+o///5AAAAAADf//+v//EAAI//7P//9QAAAAAAn//////AAABf//////"
"IAAAAAAG//////kAAAH//////QAAAAAAAv/////1AAAA3/////oAAAAAAADv////8QAAAJ/////2AAAAAAAAr////9AAAABv////8wAAAAAAAH////+QAAAA"
"L////+AAAAAAAAA/////YAAAAA7///+wAAAACv///hAAAAAAz///0AHv//+gAAAACP///zAAX///9QAAAD////gAAAr///4QAADP///AAAAB7///oAAI////"
"MAAAAF////UAP///9wAAAAAJ///+IN///8AAAAAAAd///7j///8gAAAAAABP///////3AAAAAAAACf//////wAAAAAAAAAHf/////iAAAAAAAAAAT/////YA"
"AAAAAAAAAB7////yAAAAAAAAAACf/////AAAAAAAAAAE//////9wAAAAAAAAHf//////8gAAAAAAAJ///+3///wAAAAAAAX///9j////cAAAAAAe///7AI//"
"//MAAAAAr///4QAM///8AAAABf///1AAA////4AAAB7///oAAACP///zAACv///hAAAADP///AAF////UAAAAAP///+AHv//+gAAAAAAf///8x7///4QAAAA"
"AG////kF////kAAAAAHv///hAL////QAAAAK////UAAu///9AAAAT///+gAABv///4AAAd///+EAAAC////yAAj///9QAAAALv//+wA////7AAAAAAf///9g"
"z///4gAAAAAAz///6P///2AAAAAAAC////////sAAAAAAAAH///////iAAAAAAAAAM//////cAAAAAAAAAA//////AAAAAAAAAAACP////IAAAAAAAAAAADv"
"//+QAAAAAAAAAAAA3///gAAAAAAAAAAAAN///4AAAAAAAAAAAADf//+AAAAAAAAAAAAA3///gAAAAAAAAAAAAN///4AAAAAAAAAAAADf//+AAAAAAAAAAAAA"
"3///gAAAAAAAAAAAAN///4AAAAAAAAAAAADf//+AAAAAAAAAAAAA3///gAAAAAAB/////////////7AAH/////////////sAAf////////////+wAB//////"
"///////7AAH/////////////QAAAAAAAAAAJ////YAAAAAAAAAAG////kAAAAAAAAAAE////sAAAAAAAAAAC7///0QAAAAAAAAABz///4gAAAAAAAAAAv///"
"9AAAAAAAAAAAj///9wAAAAAAAAAAX///+gAAAAAAAAAAP////AAAAAAAAAAALv///RAAAAAAAAAAHP///jAAAAAAAAAACv///1AAAAAAAAAAB////4AAAAAA"
"AAAABf///6AAAAAAAAAAA+///8EAAAAAAAAAAd/////////////yAH//////////////IAf/////////////8gB//////////////yAH//////////////IA"
"AB//////9AAAH//////0AAAf//////QAAB//////9AAAH///gAAAAAAf//+AAAAAAB///4AAAAAAH///gAAAAAAf//+AAAAAAB///4AAAAAAH///gAAAAAAf"
"//+AAAAAAB///4AAAAAAH///gAAAAAAf//+AAAAAAB///4AAAAAAH///gAAAAAAf//+AAAAAAB///4AAAAAAH///gAAAAAAf//+AAAAAAB///4AAAAAAH///"
"gAAAAAAf//+AAAAAAB///4AAAAAAH///gAAAAAAf//////QAAB//////9AAAH//////0AAAf//////QA3/wAAAAACP/yAAAAAD//cAAAAADv+wAAAAAJ//EA"
"AAAAT/9gAAAAAO/7AAAAAAr/8QAAAABf/1AAAAAB//oAAAAAC//gAAAAAG//QAAAAAL/+QAAAAAM/9AAAAAAf/8wAAAAA//4AAAAAA3/wAAAAACP/yAAAAAD"
"//cAAAAADv+wAAAAAJ//EAAAAAT/9gAAAAAO/7AAAAAAr/8QAAAABf/1AAAAAB//oAAAAAC//gAAAAAG//QAr/////+QAACv/////5AAAK//////kAAAr///"
"//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AAAAAAD///"
"kAAAAAAP//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AAAAAAD///kAAAAAAP//+QAAAAAA///5AA"
"AK//////kAAAr/////+QAACv/////5AAAK//////kAAAAAAAAAX//7AAAAAAAAAAAAAAT///+wAAAAAAAAAAAAT/////oAAAAAAAAAAATv/////6AAAAAAAA"
"AAPv//pe//+gAAAAAAAAPv/+YAK///kAAAAAAAPv/8IAAAf//5AAAAAAPv/4AAAAAD3/+QAAAALv/UAAAAAAAZ//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////"
"Ad//oAAAAAAAAc//YAAAAAAAAc//MAAAAAAAAc/9EAAAAAAAAc/7AAAAAAAAAc/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAUes3v7slQAAAAAA7////////lAAAAAO/////////3AAAADv////"
"/////zAAAA77YxACbf//+gAAAKMAAAAAHv//4AAAAAAAAAAAv///IAAAAFm97//////zAAAF3/////////9AAAX///////////QAAe///////////0AAX///"
"+DEAC///9AAH///5AAAA3///QAB///+QAABv///0AAb///9hE5////9AAB7///////////QAAH///////L///0AAAI/////6G///9AAAADnf7aQAv///QAAA"
"L///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAAAAAAAAAAAL///wAOd"
"7sggAAAAL///wJ/////mAAAAL///yv//////YAAAL///////////8wAAL////7MBbv//+wAAL////AAABf///yAAL///9AAAAM///3AAL///8AAAAI///6AA"
"L///0AAAAG///7AAL///wAAAAF///8AAL///0AAAAG///7AAL///8AAAAI///6AAL///9AAAAM///3AAL////AAABf///yAAL////7MBbv//+wAAL///////"
"////8wAAL///y///////YAAAL///wJ/////mAAAAL///wASd7sggAAAAAAAEjN79yVEAAAAF3//////9AAAAn////////QAACf////////0AAE////5yATjt"
"AADP///iAAAAGQAC////UAAAAAAABf///gAAAAAAAAf///sAAAAAAAAI///6AAAAAAAAB///+wAAAAAAAAX///4AAAAAAAAC////UAAAAAAAAM///+IAAAAZ"
"AABP///+cgE47QAACf////////0AAACf///////9AAAABd///////QAAAAAEjN79yWIAAAAAAAAAAAj///cAAAAAAAAAAAj///cAAAAAAAAAAAj///cAAAAA"
"AAAAAAj///cAAAAAAAAAAAj///cAAAAAAAAAAAj///cAAAAAAAAAAAj///cAAAAAa+/bUAj///cAAAA9/////Cj///cAAALv/////9n///cAAAz/////////"
"//cAAG////ogKP////cAAM///6AAAH////cAAv///yAAAA7///cABf///QAAAAr///cABv//+wAAAAj///cAB///+wAAAAj///cABv//+wAAAAj///cABf//"
"/QAAAAr///cAAv///yAAAA7///cAAM///6AAAH////cAAG////ogKP////cAAAz///////////cAAALv/////9n///cAAAA9/////Cj///cAAAAAa+/bYAj/"
"//cAAAAABZzv7aYQAAAAAABt//////5wAAAAAK////////+wAAAAn/////////+QAABP///oISbv//9AAAz///QAAAP///wAAv///AAAAAz///EAX///////"
"/////0AH////////////9QCP////////////YAf////////////2AF///5AAAAAAAAAAAv///QAAAAAAAAAADP//+AAAAAAChwAAT///+0EBJYz/gAAAn///"
"///////4AAAAr/////////+AAAAAbf////////gAAAAABZze/ty4UwAAAAAASd7///EAAAr/////8QAAn//////xAAH///////EABP///jAAAAAF///5AAAA"
"AAb///gAAABf////////kF////////+QX////////5Bf////////kAAG///4AAAAAAb///gAAAAABv//+AAAAAAG///4AAAAAAb///gAAAAABv//+AAAAAAG"
"///4AAAAAAb///gAAAAABv//+AAAAAAG///4AAAAAAb///gAAAAABv//+AAAAAAG///4AAAAAAb///gAAAAABv//+AAAAAAAAGvv22AI///3AAAALP////wo"
"///3AAAC7//////Z///3AAAM///////////3AABv///6MCj////3AADP//+wAACP///3AAH///8wAAAe///3AAX///0AAAAL///3AAb///sAAAAI///3AAf/"
"//oAAAAI///3AAb///sAAAAI///3AAX///0AAAAL///3AAH///8gAAAe///3AADP//+gAACP///3AABv///5ICj////3AAAM///////////3AAAC7//////Z"
"///3AAAALP////wo///3AAAAAGvv22AJ///2AAAAAAAAAAAO///zAAADkQAAAACP///gAAAD/5UgAlv///9wAAAD//////////wAAAAD/////////8EAAAAD"
"////////5wAAAAAAJpze/tuVAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAA"
"AAAAAAAv///AAAAAAAAAAAAv///AA43u2SAAAAAv///Aj////+UAAAAv///K//////8gAAAv//////////+gAAAv///////////xAAAv////swKf///0AAAv"
"///8AAAM///3AAAv///0AAAI///4AAAv///gAAAH///4AAAv///QAAAH///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG"
"///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAv///AAAAv///AAAAv///AAAAv"
"///AAAAAAAAAAAAAAAAAAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv"
"///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAAAAAAAAAAAAAAAAAA"
"AC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AA"
"AAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAA///+wAAAAb///kAAAFO///1AAL/////4AAC/////1AAAv////cAAAL//tkgAA"
"AAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///A"
"AAAc///9IAAv///AAAHP///SAAAv///AABz///0gAAAv///AAb///8EAAAAv///AG////BAAAAAv///Av///sQAAAAAv///L///7EAAAAAAv//////+wAAAA"
"AAAv//////sAAAAAAAAv//////5AAAAAAAAv///////jAAAAAAAv///c///+MAAAAAAv///Bz///4gAAAAAv///ALf///SAAAAAv///AAu///9IAAAAv///A"
"AD7///0QAAAv///AAAT////BAAAv///AAABf///8EAAv///AAAAG////sQAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///A"
"AAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///AAAAv///A"
"AAAv///AAAAv///AAAAv///AAAA////ABK39owAABr79kwAAAAP///wa////9wAs////9wAAAD///8v/////9i7/////9QAAA///////////7P//////0AAA"
"P///////////////////QAAD////+SFO////+SFe///3AAA////6AACP///6AAB///+gAAP///8wAAX///8wAAT///oAAD///+AAAE///+AAAD///7AAA///"
"/AAAA////AAAA///+wAAP///wAAAP///wAAAT///sAAD///8AAAD///8AAAE///7AAA////AAAA////AAABP//+wAAP///wAAAP///wAAAT///sAAD///8AA"
"AD///8AAAE///7AAA////AAAA////AAABP//+wAAP///wAAAP///wAAAT///sAAD///8AAAD///8AAAE///7AAA////AAAA////AAABP//+wAAAv///AA43u"
"2SAAAAAv///Aj////+UAAAAv///K//////8gAAAv//////////+gAAAv///////////xAAAv////swKf///0AAAv///8AAAM///3AAAv///0AAAI///4AAAv"
"///gAAAH///4AAAv///QAAAH///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG"
"///4AAAv///AAAAG///4AAAv///AAAAG///4AAAv///AAAAG///4AAAAABac7+23IAAAAAAAfv//////oQAAAAC/////////0wAAAK//////////4gAAX///"
"+jAX7///oAAM///6AAAF////MAL///8gAAAM///3AF///9AAAAB///+wB///+wAAAAX///wAj///oAAAAF///9AH///7AAAABf///ABf///QAAAAf///sAL/"
"//8gAAAM///3AAz///oAAAX///8wAF////owFu///6AAAK//////////4gAAAL/////////jAAAAAH7//////6EAAAAAABad7+23IAAAAAAv///AA53uyCAA"
"AAAv///An////+YAAAAv///K//////9gAAAv///////////zAAAv////swFu///7AAAv///8AAAF////IAAv///0AAAAz///cAAv///wAAAAj///oAAv///Q"
"AAAAb///sAAv///AAAAAX///wAAv///QAAAAb///sAAv///wAAAAj///oAAv///0AAAAz///cAAv///8AAAF////IAAv////swFu///7AAAv///////////z"
"AAAv///L//////9gAAAv///An////+YAAAAv///ABJ3uyCAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAv///A"
"AAAAAAAAAAAv///AAAAAAAAAAAAv///AAAAAAAAAAAAAAGvv22AI///3AAAAPf////wo///3AAAC7//////Z///3AAAM///////////3AABv///6ICj////3"
"AADP//+gAAB////3AAL///8gAAAO///3AAX///0AAAAK///3AAb///sAAAAI///3AAf///sAAAAI///3AAb///sAAAAI///3AAX///0AAAAK///3AAH///8g"
"AAAO///3AADP//+gAAB////3AABv///6ICj////3AAAM///////////3AAAC7//////Z///3AAAAPf////wo///3AAAAAGvv22AI///3AAAAAAAAAAAI///3"
"AAAAAAAAAAAI///3AAAAAAAAAAAI///3AAAAAAAAAAAI///3AAAAAAAAAAAI///3AAAAAAAAAAAI///3AAAAAAAAAAAI///3AAAv///AAYzvoAL///wE7//6"
"AC///8P///+gAv///N////oAL////////6AC/////mICaAAv///+IAAAAAL///9gAAAAAC////EAAAAAAv///QAAAAAAL///wAAAAAAC///8AAAAAAAv///A"
"AAAAAAL///wAAAAAAC///8AAAAAAAv///AAAAAAAL///wAAAAAAC///8AAAAAAAv///AAAAAAAAAFqzv7cuWMAAABu////////YAAF/////////2AADf////"
"////9gAC///7MQFHz/YAA///8QAAAAKVAAL///QAAAAAAAAA7///uGQgAAAAAH///////qUAAAAI////////0wAAACjP//////0AAAAAACRp7///UAAAAAAA"
"AD///4AAtAAAAAAv//+QAO/ZUhAUz///cADv/////////zAA7/////////kAAO////////+AAAAUes3v/tphAAAACf//9QAAAAAJ///1AAAAAAn///UAAAAA"
"Cf//9QAAAAAJ///1AAAAj/////////eP////////94/////////3j/////////cACf//9QAAAAAJ///1AAAAAAn///UAAAAACf//9QAAAAAJ///1AAAAAAn/"
"//UAAAAACf//9QAAAAAJ///1AAAAAAn///UAAAAACP//9wAAAAAH///9MAAAAAP//////+AAAM//////4AAAPv/////gAAABfO///+AAX///oAAACf//9QAA"
"X///oAAACf//9QAAX///oAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAA"
"Cf//9QAAX///kAAACv//9QAAX///oAAAC///9QAAX///sAAAH///9QAAT///4QAAn///9QAAH////CAp////9QAADf//////////9QAAB///////////9QAA"
"Ad//////yv//9QAAAD3////6Gf//9QAAAAF879pACf//9QBP//+QAAAAB///9w3//+EAAAAM///yCP//9QAAAD///7AC///6AAAAj///UAC///8QAADf//4A"
"AG///2AAA///+AAAHv//sAAJ///yAAAJ///yAA7//8AAAAP///cAT///YAAAAN///ACv//4QAAAAf///Ie//+QAAAAAf//+F///0AAAAAAr//9r//9AAAAAA"
"Bf//////cAAAAAAA7/////8QAAAAAACP////+gAAAAAAAC/////1AAAAAAAADP///+AAAAAAAAAG////gAAAAAr///EAAA3//1AAAK///yBv//9QAAL///gA"
"AA7//9AC///4AABv///AAAL///kADf//wAAJ////EABv//9QAK///xAA3///9AAK///xAAb///QAH////4AA3//8AAAv//+ABf/7//sAL///gAAA3//7AJ//"
"Xv/wBv//9AAACf//8Az/8a//QJ///xAAAF///zH//Qf/9w3//8AAAAH///dP/5A//7H///gAAAAN//+4//YA7/5f//9AAAAAn//+z/8gC//8///wAAAABf//"
"///QAH/////7AAAAAB/////6AAT/////cAAAAADP////YAAP////8wAAAAAI////8wAAv////gAAAAAAT////gAACP///7AAAAAAAf///6AAAE////cAAAAM"
"///3AAAAj///sALv//8wAAT///4QAF///8AAHf//9AAACf//+ACf//+AAAAB3///NP///AAAAAA////O///iAAAAAAf//////1AAAAAAAL/////6AAAAAAAA"
"Hv///9EAAAAAAAAK////kAAAAAAAAF/////0AAAAAAAC7/////4QAAAAAAz//////7AAAAAAj///m///9wAAAAT///0R7///MAAAHf//8wBf///RAACv//+A"
"AAn///kABv///AAAAd///1Au///zAAAAT///4m///4AAAAAI///1Dv//4AAAAA3//+AI///1AAAAP///kAL///sAAACP//8wAK///yAAAN///AAAT///cAAD"
"///2AAAM///QAAj///EAAAb///QADf//oAAAAe//+gA///9AAAAAj///EI///QAAAAAv//9g3//4AAAAAAv//8P///IAAAAABP//+///sAAAAAAA3/////9Q"
"AAAAAAB//////hAAAAAAAB7////5AAAAAAAACf////MAAAAAAAAD////wAAAAAAAAAC///9wAAAAAAAAAG///xAAAAAAAAAAr//6AAAAAAAAACj///QAAAAA"
"AAn/////sAAAAAAACf////4gAAAAAAAJ////5AAAAAAAAAn//sggAAAAAAAB//////////8gAf//////////IAH//////////yAB//////////8gAAAAAAA+"
"///9EAAAAAAC7///4gAAAAAAHf///jAAAAAAAc////QAAAAAABz///9QAAAAAAC////2AAAAAAAK////gAAAAAAAn///+QAAAAAAB////6AAAAAAAG////sA"
"AAAAAAT////BAAAAAAAH//////////8gB///////////IAf//////////yAH//////////8gAAAAAAAAWt7//gAAAAAAAAAc/////gAAAAAAAACv/////gAA"
"AAAAAAL//////gAAAAAAAAb///1RAAAAAAAAAAj///UAAAAAAAAAAAn///IAAAAAAAAAAAn///EAAAAAAAAAAAn///EAAAAAAAAAAAn///EAAAAAAAAAAAr/"
"//EAAAAAAAAAAAz///AAAAAAAAAAAC///9AAAAAAAAAAFd///6AAAAAAAAC//////iAAAAAAAAC/////ogAAAAAAAAC/////1QAAAAAAAAC//////0AAAAAA"
"AAAAFd///7AAAAAAAAAAAC///+AAAAAAAAAAAAz///EAAAAAAAAAAAr///EAAAAAAAAAAAn///EAAAAAAAAAAAn///EAAAAAAAAAAAn///IAAAAAAAAAAAj/"
"//UAAAAAAAAAAAf///1BAAAAAAAAAAP//////gAAAAAAAAC//////gAAAAAAAAAc/////gAAAAAAAAAAWt7//gAAAACv/xAAAACv/xAAAACv/xAAAACv/xAA"
"AACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAA"
"AACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAAAACv/xAA"
"AAC//+22EAAAAAAAAAC/////0wAAAAAAAAC//////QAAAAAAAAC//////1AAAAAAAAAAFM///5AAAAAAAAAAAC///7AAAAAAAAAAAA7//8AAAAAAAAAAAA3/"
"/8AAAAAAAAAAAA3//8AAAAAAAAAAAA3//8AAAAAAAAAAAA3//9AAAAAAAAAAAAz//+AAAAAAAAAAAAr///UAAAAAAAAAAAf///5iAAAAAAAAAAHf/////gAA"
"AAAAAAAY7////gAAAAAAAAA8/////gAAAAAAAALv/////gAAAAAAAAj///5iAAAAAAAAAAv///UAAAAAAAAAAA3//+AAAAAAAAAAAA3//9AAAAAAAAAAAA3/"
"/8AAAAAAAAAAAA3//8AAAAAAAAAAAA7//8AAAAAAAAAAAC///7AAAAAAAAAAE7///6AAAAAAAAC//////2AAAAAAAAC//////RAAAAAAAAC/////0wAAAAAA"
"AAC///63EAAAAAAAAAAAAAAAAAAAAAAAIAAAAABa3uyVEAAAAAfQAAAATf/////qYgE339AAAAX/////////////0AAABv/////////////QAAAG/7UgFI3/"
"////+RAAAAbUAAAAADe9/sggAAAAAxAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAB//+AAAAAAAJ//8QAAAAAAr//zAAAAAADP//UAAAAAAO//9gAAAAAB///4AAAAAAL///oAAAAAA///+wAAAAAE///7AAAAAA"
"T///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAAAE///7AAAAAAT///sAAAAABP//+wAAAAAAKd/ZIAAAAABf///+QAAAAD/////+IAAACv"
"+zE7/5AAAA79EAAd/gAAAP+gAACv8AAADv0QAB3+AAAAr/sxO/+QAAAD/////+IAAAAF////5QAAAAADrv2SAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAACP//9wAAAI///3AAAAj///cAAACP//9wAAAI///3AAAAj///cAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAADv//8QAAAAAAAA7///EAAAAAAAAO///xAAAAAAAADv//8QAAAAAAAA7///EAAAAAAAAO///xAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAO///xAAAAAAAAD///8AAAAAAAAF///+AAAAAAAAHf//+QAAAAAAAc///+IAAAAAAAv///9gAAAAAACv///4AAAAAAAH////kAAAAAAAH///+gAA"
"AAAAAG///9EAAAAAAACf//9wAAAAAAAAn///YAAAAAAAAI///5AAAAF3AABf///4ICWe+AAAHv////////gAAAX////////4AAAATf//////+AAAAAFa3v7c"
"p0AAAAAAAAAADP/6EAAAAAAAAAAAAAr/+AAAAAAAAAAAAAAH//UAAAAAAAAAAAAABP/kAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/"
"///yAAAAAAAAAAAD/////4AAAAAAAAAAAJ/////9AAAAAAAAAAAO//////QAAAAAAAAABf//////kAAAAAAAAACv//////4QAAAAAAAAH///6v//9QAAAAAA"
"AAb///pf//+wAAAAAAAAz///UO///xAAAAAAAC///+AK///3AAAAAAAI///5AF///8AAAAAAAN///0AA7///MAAAAABP///gAAn///gAAAAACf//+QAAT///"
"4AAAAADv//9AAADv//9AAAAAX///4AAACf//+gAAAAv////////////hAAAB/////////////2AAAH/////////////7AAAM//////////////IAA///////"
"////////cACP///hAAAAAAr///0ADv//+QAAAAAAT///8wT///8wAAAAAADf//+Qr///wAAAAAAAB////gAAAAAAAALv/3AAAAAAAAAAAd/+UAAAAAAAAAAA"
"v/0wAAAAAAAAAACP/BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADf//////////YAAA3//////////2AAAN//////////9gAADf//////////YAAA3/"
"/////////2AAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf/////////7AAAA3/////////+wAAAN//////////sAAA"
"Df/////////7AAAA3/////////+wAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAAAAAN///4AAAAAAAAAADf//+AAAAAAAAAAA3///gAAAAAAA"
"AAAN//////////+wAADf//////////sAAA3//////////7AAAN//////////+wAADf//////////sAAAAACv/8EAAAB//6AAAABf/3AAAAA+/1AAAAAAAAAA"
"AAAAAAAAAAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//"
"+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAN///4AAAA3///gAAADf//+AAAAAAAAAfugQAO"
"9gAAAAAAAAAAX//8EB/0AAAAAAAAAADP///Cf/EAAAAAAAAAAP+Rbv//kAAAAAAAAAAC/zACnuoQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"Df///4AAAAAL///1AAAN////4QAAAAv///UAAA3////5AAAAC///9QAADf////8gAAAL///1AAAN/////5AAAAv///UAAA3/////8gAAC///9QAADf/////6"
"AAAL///1AAAN//////8wAAv///UAAA3///r//7AAC///9QAADf//8+//9AAL///1AAAN///zb//8AAv///UAAA3///MN//9QC///9QAADf//8wb//8AL///1"
"AAAN///zAN//9Qv///UAAA3///MAX//9C///9QAADf//8wAM//9r///1AAAN///zAAT//+v///UAAA3///MAAL//////9QAADf//8wAAP//////1AAAN///z"
"AAAK//////UAAA3///MAAAP/////9QAADf//8wAAAK/////1AAAN///zAAAAL/////UAAA3///MAAAAJ////9QAADf//8wAAAAHv///1AAAAAAAAAACP/9IA"
"AAAAAAAAAAAAAF//sQAAAAAAAAAAAAAAPv+QAAAAAAAAAAAAAAAd/3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEi97+23MAAAAA"
"AAAAAG3///////xQAAAAAAABv/////////+hAAAAAALv///////////RAAAAAc////////////+wAAAAn////6QQFb////9wAAAv////YAAAAH////4QAAj/"
"//+AAAAAAK////YAAM///+EAAAAAAv///6AAH///+gAAAAAADP///gAC////cAAAAAAAj///8ABP///1AAAAAAAH////IAT///9QAAAAAABv///yAE////UA"
"AAAAAAf///8gAv///3AAAAAAAI////AAH///+gAAAAAADP///gAAz///4QAAAAAC////oAAI////gAAAAACv///2AAAv////YAAAAH////4QAACf////pBAV"
"v////3AAAAHP////////////sAAAAALv///////////RAAAAAAHP/////////6EAAAAAAABt///////8UAAAAAAAAAAEi97+23MAAAAAAAAAAAAAAAP//2AA"
"AAAAAAAAAAAAHf/kAAAAAAAAAAAAAADP/SAAAAAAAAAAAAAACv+xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAN///4AAAAAO///3AAAA3/"
"//gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA"
"7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAA"
"Df//+AAAAADv//9wAAAM///4AAAAAO///2AAAAv///oAAAAB////UAAACf///gAAAAX///8wAAAF////YAAADP///gAAAAHv///4IBS////6AAAAAJ//////"
"//////MAAAAAHf//////////gAAAAAAD3/////////oAAAAAAAAa///////9YAAAAAAAAAAnre/tyVAAAAAAAAAAAG//cA3/8QAAAAAAAAAAb/9wDf/xAAAA"
"AAAAAABv/3AN//EAAAAAAAAAAG//cA3/8QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4"
"AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO//"
"/3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAA3///gAAAAA7///cAAADf//+AAAAADv//9wAAAN///4AAAAAO///3AAAAz/"
"//gAAAAA7///YAAAC///+gAAAAH///9QAAAJ///+AAAABf///zAAAAX///9gAAAM///+AAAAAe////ggFL////oAAAAAn///////////8wAAAAAd////////"
"//+AAAAAAAPf////////+gAAAAAAABr///////1gAAAAAAAAACet7+3JUAAAAAAAAAAAAAAI//0gAAAAAAAAAAX//SAAAAAAAAAAAu/9IAAAAAAAAAAB3/0g"
"AAAAAAAAAACv/RAAAAAAAAAAAH/8EAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABR6ze/uyVAAAAAADv///////+UAAAAA7/////////cAAAAO//////"
"////MAAADvtjEAJt///6AAAAowAAAAAe///gAAAAAAAAAAC///8gAAAAWb3v//////MAAAXf/////////0AABf//////////9AAB7///////////QABf///4"
"MQAL///0AAf///kAAADf//9AAH///5AAAG////QABv///2ETn////0AAHv//////////9AAAf//////8v///QAAAj/////ob///0AAAAOd/tpAC///9AAAAA"
"AAAAAALv/4AAAAAAAAAAAM//gAAAAAAAAAAAn/9wAAAAAAAAAABv/3AAAAAAAAAAAD//cAAAAAAAAAAAHf9wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABZzv7aYQAAAAAABt//////5wAAAAAK////////+wAAAAn/////////+QAABP///oISbv//9AAAz///QAAAP///wAAv///AAAAAz///EAX///////////"
"/0AH////////////9QCP////////////YAf////////////2AF///5AAAAAAAAAAAv///QAAAAAAAAAADP//+AAAAAAChwAAT///+0EBJYz/gAAAn///////"
"///4AAAAr/////////+AAAAAbf////////gAAAAABZze/ty4UwAAAAAAAd//oAAAAAv/+QAAAAB//5AAAAAE//kAAAAALv+AAAAAAM/4AAAAAAAAAAAAAAAA"
"AAAAAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAA"
"L///wAAAAC///8AAAAAv///AAAAAL///wAAAAC///8AAAAAv///AAAAAL///wAAAAAAAAI7pIAH/QAAAAAAACP//9xb/MAAAAAAADv/////+AAAAAAAAL/cX"
"7//4AAAAAAAAT/EAKu6QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC///8ADje7ZIAAAAC///8CP////5QAAAC///8r//////yAA"
"AC///////////6AAAC////////////EAAC////+zAp////QAAC////wAAAz///cAAC////QAAAj///gAAC///+AAAAf///gAAC///9AAAAf///gAAC///8AA"
"AAb///gAAC///8AAAAb///gAAC///8AAAAb///gAAC///8AAAAb///gAAC///8AAAAb///gAAC///8AAAAb///gAAC///8AAAAb///gAAC///8AAAAb///gA"
"AC///8AAAAb///gAAAAAAAAAAu//cAAAAAAAAAABz/9wAAAAAAAAAACv/3AAAAAAAAAAAG//YAAAAAAAAAAAP/9gAAAAAAAAAAAd/2AAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAWnO/ttyAAAAAAAH7//////6EAAAAAv////////9MAAACv/////////+IAAF////owF+///6AADP//+gAABf///zAC////IAAA"
"DP//9wBf///QAAAAf///sAf///sAAAAF///8AI///6AAAABf///QB///+wAAAAX///wAX///0AAAAH///7AC////IAAADP//9wAM///6AAAF////MABf///6"
"MBbv//+gAACv/////////+IAAAC/////////4wAAAAB+//////+hAAAAAAAWne/ttyAAAAAAAAAAAAAAr//RAAAAAAAAAAAG//wQAAAAAAAAAAA//8EAAAAA"
"AAAAAAHf/BAAAAAAAAAAAAv/wQAAAAAAAAAAAI/8EAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAX///oAAACf//9QAAX///oAAACf//9QAAX///oAAA"
"Cf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACv//9QAA"
"X///oAAAC///9QAAX///sAAAH///9QAAT///4QAAn///9QAAH////CAp////9QAADf//////////9QAAB///////////9QAAAd//////yv//9QAAAD3////6"
"Gf//9QAAAAF879pACf//9QAAAAA//6AK//QAAAAAAAA//6AK//QAAAAAAAA//6AK//QAAAAAAAA//6AK//QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAX///oAAACf//9QAAX///oAAACf//9QAAX///oAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAA"
"Cf//9QAAX///kAAACf//9QAAX///kAAACf//9QAAX///kAAACv//9QAAX///oAAAC///9QAAX///sAAAH///9QAAT///4QAAn///9QAAH////CAp////9QAA"
"Df//////////9QAAB///////////9QAAAd//////yv//9QAAAD3////6Gf//9QAAAAF879pACf//9QAAAACP////gAAAAAAACP////gAAAAAAACP////gAAA"
"AAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP//"
"//gAAAAAAACP////gAAAAAAACP////gAAAAAAABv////YAAAAAAABP////QAAAAAAAA/////IAAAAAAAAf////EAAAAAAAAO///+AAAAAAAAAM///8AAAAAA"
"AAAL///6AAAAAAAAAJ///5AAAAAAAAAH///3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACP////gAAAAAAACP////gAAAAAAACP////"
"gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAABJzv7JQAAAAAAAAABP//sAAAAAAAAALP/////7IAAA"
"AAAAAN//8gAAAAAAAAPv///////iAAAAAAAH//+AAAAAAAAAHv////////0QAAAAAC7//RAAAAAAAACP//+yA8///3AAAAAAr//1AAAAAAAAAO///QAAHv//"
"0AAAAAT//7AAAAAAAAAE///2AAAI///yAAAADP//IAAAAAAAAAb///MAAAX///QAAAB///gAAAAAAAAAB///8QAAA///9gAAAe//0QAAAAAAAAAH///yAAAD"
"///1AAAK//9QAAAAAAAAAAb///MAAAX///QAAE//+wAAAAAAAAAAA///9gAACP//8gAAz//yAAAAAAAAAAAA7//9AAAe///QAAf//4AAAAAAAAAAAACP//+y"
"A8///3AAHv/9EAAAAAAAAAAAAB3////////8EACv//UAAAAAAAAAAAAAA+///////+IABP//sAAAAAAAAAAAAAAALP/////7IAAM//8gAAAAAAAAAAAAAAAA"
"Sd7+yUAAAH//+AAAA4zv7ZUAAAAAAAAAAAAAAAAB7//RAAGv/////9MAAAAAAAAAAAAAAAr//1AALf///////1AAAAAAAAAAAAAAT//7AADP////////4gAA"
"AAAAAAAAAADP//IABv///UAq///6AAAAAAAAAAAAB///gAAM///iAADP//8QAAAAAAAAAAAe//0QAB///6AAAG///1AAAAAAAAAAAK//9QAAT///YAAAL///"
"gAAAAAAAAAAE//+wAABf//9QAAAf//+QAAAAAAAAAAz//yAAAF///1AAAB///5AAAAAAAAAAb//4AAAAT///YAAAL///gAAAAAAAAAHv/9EAAAAf//+QAABf"
"//9QAAAAAAAACf//UAAAAAz//+IAAM///xAAAAAAAAA///sAAAAABv///DAq///6AAAAAAAAAM//8gAAAAAAz////////+IAAAAAAAAG//+AAAAAAAAt////"
"///+QAAAAAAAAB7//RAAAAAAAAGv/////8MAAAAAAAAAn//1AAAAAAAAAAOM7+2VAAAAAAAAAACf///yAAAAAAAAP///+QAAAAAAAAz///8gAAAAAAAF////"
"kAAAAAAAAN////MAAAAAAABf///7AAAAAAAADP///1AAAAAAAAT////hAAAAAAAAr///+gAAAAAAAB7///9QAAAAAAAG////8QAAAAAAAK////sAAAAAAAAO"
"////gAAAAAAAA/////UAAAAAAABv////IAAAAAAACf///+AAAAAAAAC////9AAAAAAAADf///7AAAAAAAAD////6AAAAAAAAD////5AAAAAAAAH////5AAAA"
"AAAAD////5AAAAAAAAD////6AAAAAAAADf///7AAAAAAAAC////9AAAAAAAACf///+AAAAAAAABv////IAAAAAAAA/////UAAAAAAAAO////gAAAAAAAAK//"
"//sAAAAAAAAG////8QAAAAAAAB////9QAAAAAAAAr///+QAAAAAAAAT////gAAAAAAAADP///1AAAAAAAABf///7AAAAAAAAAN////MAAAAAAAAF////kAAA"
"AAAAAAz///8QAAAAAAAAP///+QAAAAAAAACf///yAAAAAe///6AAAAAAAAAI////QAAAAAAAAB7///wAAAAAAAAAn///9QAAAAAAAAL////QAAAAAAAAC///"
"/2AAAAAAAABf///8AAAAAAAAAO////QAAAAAAAAJ////oAAAAAAAAE////8QAAAAAAAA7///9gAAAAAAAAv///+gAAAAAAAAf////gAAAAAAAAT////zAAAA"
"AAAAH////3AAAAAAAADv///6AAAAAAAADP///8AAAAAAAAC////+AAAAAAAACv////AAAAAAAACf////AAAAAAAACf////EAAAAAAACf////AAAAAAAACv//"
"//AAAAAAAAC////+AAAAAAAADP///8AAAAAAAADv///6AAAAAAAAL////3AAAAAAAAT////0AAAAAAAAf////gAAAAAAAAv///+wAAAAAAAA7///9gAAAAAA"
"AF////8QAAAAAAAJ////oAAAAAAAAO////QAAAAAAABf///8AAAAAAAAC////2AAAAAAAAL////QAAAAAAAAn///9QAAAAAAAB7///wAAAAAAAAI////QAAA"
"AAAAAe///6AAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAA"
"AAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+"
"AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAL//////////////////6AAAAAAL/"
"/////////////////6AAAAAAL//////////////////6AAAAAAL//////////////////6AAAAAAL//////////////////6AAAAAAAAAAAAAAb//+AAAAAA"
"AAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAA"
"b//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAA"
"AAAAAAAAAAb//+AAAAAAAAAAAAAAAAAAAAAAb//+AAAAAAAAAAAAAABf////wAAAAAX////8AAAAAF/////AAAAABf////wAAAAAX////8AAAAAF/////AAA"
"AABf////sAAAAAj////0AAAAAM////kAAAAAH////RAAAAAF////QAAAAACf//+QAAAAAA3//9EAAAAAAv//9AAAAAAAb//5AAAAAAAAj////////5AACP//"
"//////kAAI////////+QAAj////////5AACP////////kAAI////////+QAAj////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAF/////AAAAABf////wAAAAAX////8AAAAAF////"
"/AAAAABf////wAAAAAX////8AAAAAF/////AAAAABf////wAAAAAX////8AAAAAAAAAABf//oAAAAAAAr//1AAAAAAAO//8QAAAAAAT//7AAAAAAAJ//9gAA"
"AAAADf//EAAAAAAD///AAAAAAACP//cAAAAAAA3//yAAAAAAAv//0AAAAAAAf//4AAAAAAAL//8wAAAAAAH//+AAAAAAAG//+QAAAAAACv//QAAAAAAB7//g"
"AAAAAABf//oAAAAAAAn//1AAAAAAAO//8QAAAAAAT//7AAAAAAAI//9gAAAAAADf//IAAAAAAD///AAAAAAAB///cAAAAAAAz//zAAAAAAAv//0AAAAAAAb/"
"/4AAAAAAAL//9AAAAAAAH//+AAAAAAAF//+QAAAAAACv//UAAAAAAA7//gAAAAAABP//oAAAAAAAn//2AAAAAAAO//8QAAAAAAP//7AAAAAAAI//9wAAAAAA"
"Df//IAAAAAAAAAAAAAAVnO/+yVEAAAAAAAAAAAAY7//////+gQAAAAAAAAAD3/////////0wAAAAAAAATv//////////5AAAAAAAA+////////////4wAAAA"
"AAz/////////////wAAAAABv////+0EUv/////YAAAAA7////7AAAAv////+AAAABf////8gAAAC/////1AAAAr////7AAAAAL////+gAAAP////9wAAAAB/"
"////8AAAP/////QAAAAAT/////MAAG/////xAAAAAC/////2AACP////8AAAAAAP////+AAAn////+AAAAAADv////oAAK/////QAAAAAA3////6AAC/////"
"0AAAAAAN////+wAAz////9AAAAAADf////wAAL/////QAAAAAA3////7AACv////0AAAAAAO////+gAAn////+AAAAAADv////oAAI/////wAAAAAA/////4"
"AABv////8gAAAAAv////9gAAP/////QAAAAAT/////MAAA/////3AAAAAH/////wAAAK////+wAAAAC/////sAAABf////8gAAAC/////1AAAADv////sAAA"
"C/////4AAAAAb/////xBFM/////3AAAAAAz/////////////wAAAAAAD7////////////jAAAAAAAE////////////QAAAAAAAAD3/////////0wAAAAAAAA"
"ABjv//////6BAAAAAAAAAAAAFZzv/slRAAAAAAAAAAAAAlnf////8wAAAAAAAAABWd////////MAAAAAAAAADP/////////zAAAAAAAAAAz/////////8wAA"
"AAAAAAAM//////////MAAAAAAAAADP/////////zAAAAAAAAAAz//qYv////8wAAAAAAAAALpiAAD/////MAAAAAAAAAAAAAAA/////zAAAAAAAAAAAAAAAP"
"////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAAAA/////zAAAAAAAAAAAAAAAP////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAAAA/////zAAAAAAAA"
"AAAAAAAP////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAAAA/////zAAAAAAAAAAAAAAAP////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAAAA/////z"
"AAAAAAAAAAAAAAAP////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAAAA/////zAAAAAAAAAAAAAAAP////8wAAAAAAAAAAAAAAD/////MAAAAAAAAAAAAA"
"AA/////zAAAAAAAAAAAAAAAP////8wAAAAAAAAAJ///////////////QAAAACf//////////////0AAAAAn//////////////9AAAAAJ///////////////Q"
"AAAACf//////////////0AAAAAn//////////////9AAAAAAAUeb3v/tuEAAAAAAAAAAOM/////////9cAAAAAAABP////////////0wAAAAAAT/////////"
"////4wAAAAAE//////////////4gAAAABP//////////////oAAAAAT//9lSECXP//////EAAAAE/6QAAAAACP/////2AAAABJIAAAAAAACv////+QAAAAAA"
"AAAAAAAAP/////sAAAAAAAAAAAAAAA/////7AAAAAAAAAAAAAAAO////+wAAAAAAAAAAAAAAH/////gAAAAAAAAAAAAAAG/////0AAAAAAAAAAAAAADP////"
"0AAAAAAAAAAAAAAI/////2AAAAAAAAAAAAAAb/////wAAAAAAAAAAAAABv/////iAAAAAAAAAAAAAG/////+MAAAAAAAAAAAAAf/////5AAAAAAAAAAAAAB/"
"/////kAAAAAAAAAAAAAI/////+MAAAAAAAAAAAAAn/////4wAAAAAAAAAAAACf/////SAAAAAAAAAAAAAK/////9IAAAAAAAAAAAAAr/////wQAAAAAAAAAA"
"AAG//////BAAAAAAAAAAAAAb/////8EAAAAAAAAAAAABz/////sQAAAAAAAAAAAABf///////////////wAAAAX///////////////8AAAAF////////////"
"////AAAABf///////////////wAAAAX///////////////8AAAAF////////////////AAAAAAAAN6ze/u25YQAAAAAAAAAVrv////////+0AAAAAAAAf///"
"/////////6EAAAAAAH/////////////8AAAAAAB//////////////4AAAAAAf//////////////gAAAAAH/9ljEAJJ//////9AAAAAB5MAAAAAAD7/////cA"
"AAAAAAAAAAAAAG/////4AAAAAAAAAAAAAAAv////+AAAAAAAAAAAAAAAL/////UAAAAAAAAAAAAAAG/////yAAAAAAAAAAAAAAPv////oAAAAAAAAAAAASWf"
"/////RAAAAAAAAA//////////8IAAAAAAAAAP////////8UAAAAAAAAAAD////////2CAAAAAAAAAAA//////////5EAAAAAAAAAP//////////8EAAAAAAA"
"AD///////////8AAAAAAAAAAAAElnv/////2AAAAAAAAAAAAAAGv/////AAAAAAAAAAAAAAADP////8QAAAAAAAAAAAAAAf/////QAAAAAAAAAAAAAAF////"
"/1AAAAAAAAAAAAAAB/////9AAAAAAAAAAAAAAAz/////IAAADHIAAAAAAAGv/////gAAAA7/2WQhASSO//////kAAAAO///////////////zAAAADv//////"
"////////cAAAAA7/////////////+AAAAAAO/////////////lAAAAAADv///////////HEAAAAAAAE1irze7+7bliAAAAAAAAAAAAAAAAAM//////IAAAAA"
"AAAAAAAAf//////yAAAAAAAAAAAAA///////8gAAAAAAAAAAAAz///////IAAAAAAAAAAAB////////yAAAAAAAAAAAC////////8gAAAAAAAAAAC///////"
"//IAAAAAAAAAAH///9/////yAAAAAAAAAALv//9P////8gAAAAAAAAAL///5H/////IAAAAAAAAAb///0R/////yAAAAAAAAAu///0Af////8gAAAAAAAAv/"
"//kAH/////IAAAAAAABv///hAB/////yAAAAAAAB7///UAAf////8gAAAAAACv//+gAAH/////IAAAAAAF///+EAAB/////yAAAAAAHv//9gAAAf////8gAA"
"AAAK///7AAAAH/////IAAAAAX///4gAAAB/////yAAAAAN///2AAAAAf////8gAAAADv//wAAAAAH/////IAAAAA7/////////////////0AAO//////////"
"///////9AADv/////////////////QAA7/////////////////0AAO/////////////////9AADv/////////////////QAAAAAAAAAAAB/////yAAAAAAAA"
"AAAAAAAf////8gAAAAAAAAAAAAAAH/////IAAAAAAAAAAAAAAB/////yAAAAAAAAAAAAAAAf////8gAAAAAAAAAAAAAAH/////IAAAAAAC//////////////"
"YAAAAAAv/////////////2AAAAAAL/////////////9gAAAAAC//////////////YAAAAAAv/////////////2AAAAAAL/////////////9gAAAAAC////wA"
"AAAAAAAAAAAAAAAv///8AAAAAAAAAAAAAAAAL////AAAAAAAAAAAAAAAAC////wAAAAAAAAAAAAAAAAv///8AAAAAAAAAAAAAAAAL////Zzv7cpiAAAAAAAA"
"AC///////////7QAAAAAAAAv////////////kAAAAAAAL/////////////sAAAAAAC//////////////oAAAAAAv//////////////QAAAAAL/+3UhATff//"
"///8AAAAACxhAAAAAAGv/////zAAAAAAAAAAAAAAC/////9wAAAAAAAAAAAAAAP/////kAAAAAAAAAAAAAAA7////7AAAAAAAAAAAAAAAN/////AAAAAAAAA"
"AAAAAADv////sAAAAAAAAAAAAAAE/////5AAAAaBAAAAAAAAC/////9gAAAH/pMAAAAAAa//////IAAAB///2VIQE33/////+wAAAAf///////////////MA"
"AAAH//////////////9wAAAAB//////////////4AAAAAAf////////////+UAAAAAAAWe/////////9gQAAAAAAAAACaazu/t2nQAAAAAAAAAAAAAAABYve"
"/tuVEAAAAAAAAAAAGO////////tQAAAAAAAABu//////////9QAAAAAAAJ////////////UAAAAAAAr////////////1AAAAAACP////////////9QAAAAAD"
"//////1zEBJZ3/UAAAAADP////9gAAAAAAOlAAAAAF/////1AAAAAAAAAAAAAAC/////gAAAAAAAAAAAAAAC/////hAAAAAAAAAAAAAABv////oAAAAAAAAA"
"AAAAAAn////2AXve/chAAAAAAAAM////9I///////VAAAAAADv////7////////6EAAAAB///////////////7AAAAAf///////////////5AAAAL///////"
"/////////zAAAC///////nIBXP////+gAAAf//////MAAAHf////8QAAD/////+QAAAAX/////QAAA7/////UAAAAA/////2AAAM/////yAAAAAN////9wAA"
"Cf////8gAAAADP////cAAAb/////IAAAAA3////2AAAC/////1AAAAAP////9AAAAL////+QAAAAX/////EAAABf////8wAAAd////+wAAAADf////5yAVz/"
"////UAAAAAT//////////////AAAAAAAn////////////+IAAAAAAAr///////////4wAAAAAAAAj//////////CAAAAAAAAAAO////////WAAAAAAAAAAAA"
"A3ve/tuEAAAAAAAADv///////////////1AAAA7///////////////9QAAAO////////////////UAAADv///////////////1AAAA7///////////////9Q"
"AAAO////////////////IAAAAAAAAAAAAAAe////+gAAAAAAAAAAAAAAb/////MAAAAAAAAAAAAAAN////+wAAAAAAAAAAAAAAX/////QAAAAAAAAAAAAAAL"
"/////QAAAAAAAAAAAAAAP/////YAAAAAAAAAAAAAAK/////gAAAAAAAAAAAAAAL/////cAAAAAAAAAAAAAAI/////hAAAAAAAAAAAAAAHv////kAAAAAAAAA"
"AAAAAG/////yAAAAAAAAAAAAAADf////oAAAAAAAAAAAAAAE/////0AAAAAAAAAAAAAAC/////wAAAAAAAAAAAAAAD/////1AAAAAAAAAAAAAACf////0AAA"
"AAAAAAAAAAAB/////3AAAAAAAAAAAAAACP////4QAAAAAAAAAAAAAA7////4AAAAAAAAAAAAAABv////8gAAAAAAAAAAAAAA3////6AAAAAAAAAAAAAABP//"
"//8wAAAAAAAAAAAAAAv////7AAAAAAAAAAAAAAA/////9QAAAAAAAAAAAAAAn////9AAAAAAAAAAAAAAAf////9gAAAAAAAAAAAAAAf////+EAAAAAAAAAAA"
"AAAO////+AAAAAAAAAAAAAAAAAJpve/+25YgAAAAAAAAAAS/////////+0AAAAAAAACv///////////5AAAAAAAL/////////////7AAAAAAf///////////"
"///2AAAAAN///////////////QAAAAP/////+TETn/////8wAAAF/////1AAAAX/////UAAAB/////0AAAAA7////2AAAAb////7AAAAAM////9QAAAD////"
"/QAAAADv////IAAAAN////9QAAAG/////AAAAABf////+TETn/////QAAAAACP////////////9wAAAAAABe///////////lAAAAAAAAAW3////////GAAAA"
"AAAAAAS/////////+0AAAAAAAAG////////////6EAAAAAAd/////////////9EAAAAAv////+gxE37////7AAAABf////4wAAAD7////0AAAAv////3AAAA"
"AI////+gAAAO////8gAAAAA/////4AAAL/////AAAAAAH/////EAAD/////wAAAAAB/////yAAAv////8gAAAAA/////8QAAD/////cAAAAAj/////AAAAz/"
"///+MAAAA+/////AAAAI/////+cwAn7/////gAAAAv///////////////yAAAACP//////////////gAAAAACv////////////+gAAAAAACf///////////5"
"AAAAAAAAA6/////////6MAAAAAAAAAABab3v/tuWEAAAAAAAAAAAAEjN7+2nIAAAAAAAAAAAAX7///////owAAAAAAAAAD3/////////9wAAAAAAAAX/////"
"//////+QAAAAAAA+////////////9wAAAAAA3/////////////8gAAAABv/////EECf/////wAAAAA3////8AAAAT/////QAAAAv////9AAAAAr////6AAAA"
"b////+AAAAAG/////xAAAI/////AAAAAA/////9AAACf////sAAAAAP/////cAAAn////8AAAAAD/////6AAAI/////gAAAABv/////QAABv////8wAAAAr/"
"////4AAAL/////wAAABP//////AAAAz/////xBAn7//////wAAAF////////////////8QAAAL////////////////AAAAAc///////////////gAAAAAb//"
"///////f////0AAAAAAG3//////nX////7AAAAAAAAWc7+2mEH////+AAAAAAAAAAAAAAAC/////QAAAAAAAAAAAAAAC/////xAAAAAAAAAAAAAACf////oA"
"AAAAAAAAAAAAAG/////0AAAAAFkwAAAAAAf/////sAAAAABv/YUhATff/////yAAAAAAb/////////////YAAAAAAG////////////+QAAAAAABv////////"
"///4AAAAAAAAb//////////+UAAAAAAAAAbP///////+gQAAAAAAAAAAAmnO7+24QAAAAAAAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QA"
"AAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QAAAAADf////QA"
"AAAADf////QAAAAAAAAAAAAAAAAAAAAAAAOZAAAAAAAAAAAAAAAAAAAAAAJ9/6AAAAAAAAAAAAAAAAAAAAFs///6AAAAAAAAAAAAAAAAAAFb/////6AAAAAA"
"AAAAAAAAAABJ7//////6AAAAAAAAAAAAAAA43////////nAAAAAAAAAAAAAnz////////6UQAAAAAAAAAAAWv////////7YQAAAAAAAAAAAFr////////7YQ"
"AAAAAAAAAAADnv///////8YQAAAAAAAAAAAAHf///////8cgAAAAAAAAAAAAAAL//////8cgAAAAAAAAAAAAAAAAL////9ggAAAAAAAAAAAAAAAAAAL////8"
"cgAAAAAAAAAAAAAAAAAAL//////8cgAAAAAAAAAAAAAAAAHf///////8YQAAAAAAAAAAAAAAADnv///////7YQAAAAAAAAAAAAAAAFr////////7YQAAAAAA"
"AAAAAAAAAWv////////6UQAAAAAAAAAAAAAAAnz////////6UQAAAAAAAAAAAAAAA43////////nAAAAAAAAAAAAAAAABJ7//////6AAAAAAAAAAAAAAAAAA"
"Fb/////6AAAAAAAAAAAAAAAAAAAAFs///6AAAAAAAAAAAAAAAAAAAAAAKN/6AAAAAAAAAAAAAAAAAAAAAAAAOZAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAs"
"YQAAAAAAAAAAAAAAAAAAAAAAAv/6UAAAAAAAAAAAAAAAAAAAAAAv///pQAAAAAAAAAAAAAAAAAAAAv/////YMAAAAAAAAAAAAAAAAAAv///////HIAAAAAAA"
"AAAAAAAAAc////////+2EAAAAAAAAAAAAAAAJ9////////6kAAAAAAAAAAAAAAAAON////////6TAAAAAAAAAAAAAAAAON////////2CAAAAAAAAAAAAAAAA"
"Se////////xhAAAAAAAAAAAAAAAASe////////gAAAAAAAAAAAAAAAAASu//////oAAAAAAAAAAAAAAAAAAAWu////oAAAAAAAAAAAAAAAAAAASe////oAAA"
"AAAAAAAAAAAAAASe//////oAAAAAAAAAAAAAAASe////////gAAAAAAAAAAAAAON////////xhAAAAAAAAAAAAON////////2CAAAAAAAAAAAAON////////"
"6TAAAAAAAAAAAAJ8////////6lAAAAAAAAAAAAAc////////+2EAAAAAAAAAAAAAAv///////HIAAAAAAAAAAAAAAAAv/////YMAAAAAAAAAAAAAAAAAAv//"
"/pQAAAAAAAAAAAAAAAAAAAAv/7UAAAAAAAAAAAAAAAAAAAAAAsYQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVm97+3JUQAAAAAAAn"
"z////////oEAAAAADP//////////0gAAAADP///////////iAAAADP///////////6AAAADP////////////IAAADP/8hCAm3/////YAAADPpAAAAAHf////"
"kAAACUAAAAAACP////oAAAAAAAAAAAB/////oAAAAAAAAAAACf////gAAAAAAAAAAALv////QAAAAAAAAAAAv////+AAAAAAAAAAAL/////3AAAAAAAAAAG/"
"////+wAAAAAAAAABz/////wQAAAAAAAAAc/////8EAAAAAAAAACv////+xAAAAAAAAAAX/////sAAAAAAAAAAAz////8EAAAAAAAAAAB/////0AAAAAAAAAA"
"AC/////wAAAAAAAAAAAD/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////gAAAAAAAAAAAD/////gAAAA"
"AAAAAAAD/////gAAAAAAAAAAAD/////gAAAAAAAAAAAD/////gAAAAAAAAAAAD/////gAAAAAAAAAAAD/////gAAAAAAAAAAAD/////gAAAAAAAAAAAAAACP"
"//////IAAAAAAAAAAAAAAADf//////gAAAAAAAAAAAAAAAT///////0AAAAAAAAAAAAAAAr///////8wAAAAAAAAAAAAAB7///////+QAAAAAAAAAAAAAG//"
"///////gAAAAAAAAAAAAAL/////////1AAAAAAAAAAAAAv/////////6AAAAAAAAAAAAB/////z/////EAAAAAAAAAAADP////W/////YAAAAAAAAAAAP///"
"//Fv////wAAAAAAAAAAAj////6Af////8gAAAAAAAAAA7////1AL////+AAAAAAAAAAE/////xAG/////QAAAAAAAAAK////+gAB/////0AAAAAAAAAe////"
"9QAAv////5AAAAAAAABv////8QAAb////+EAAAAAAAC/////sAAAL/////UAAAAAAAL/////UAAADP////sAAAAAAAf/////EAAAB/////8QAAAAAA3////7"
"AAAAAv////9wAAAAAD/////2AAAAAM/////AAAAAAJ/////////////////zAAAAAO/////////////////4AAAABf/////////////////9AAAACv//////"
"////////////QAAAH///////////////////oAAAb///////////////////4QAAz////9AAAAAAAABP////9QAC/////4AAAAAAAAAN////+wAI/////yAA"
"AAAAAAAI/////yAN/////AAAAAAAAAAD/////3BP////9wAAAAAAAAAA3////8Cf////8gAAAAAAAAAAf/////MAAM/////////u25YQAAAAAAAADP//////"
"///////EAAAAAAAAz//////////////6EAAAAAAM///////////////7AAAAAADP///////////////2AAAAAAz////////////////QAAAAAM/////QAAAk"
"z/////8wAAAADP////0AAAAAv/////UAAAAAz////9AAAAAF/////2AAAAAM/////QAAAAA/////9gAAAADP////0AAAAAX/////QAAAAAz////9AAAAAL//"
"///xAAAAAM/////QAAAUv/////kAAAAADP///////////////RAAAAAAz//////////////9IAAAAAAM//////////////kAAAAAAADP//////////////sg"
"AAAAAAz///////////////5AAAAAAM////////////////4gAAAADP////0AAAAm3/////sAAAAAz////9AAAAABv/////MAAAAM/////QAAAAAD/////4AA"
"AADP////0AAAAAAO////+gAAAAz////9AAAAAADf////wAAAAM/////QAAAAAA7////8AAAADP////0AAAAAA/////+wAAAAz////9AAAAABv/////kAAAAM"
"/////QAAACbf/////1AAAADP////////////////4QAAAAz////////////////2AAAAAM////////////////oAAAAADP//////////////+QAAAAAAz///"
"//////////+jAAAAAAAM/////////+7bhRAAAAAAAAAAAAAAAEis7v7clzAAAAAAAAAAAAOe/////////pMAAAAAAAACr////////////6AAAAAAAG7/////"
"////////wAAAAAAI///////////////AAAAAAI///////////////8AAAAAG///////pUhATad//wAAAAC7/////+iAAAAAABb/AAAAAr/////9wAAAAAAAA"
"BJAAAAL/////+QAAAAAAAAAAAAAACP/////RAAAAAAAAAAAAAAAN/////2AAAAAAAAAAAAAAAC/////+EAAAAAAAAAAAAAAAX/////sAAAAAAAAAAAAAAACP"
"////+AAAAAAAAAAAAAAAAJ/////1AAAAAAAAAAAAAAAAr/////QAAAAAAAAAAAAAAACv////9AAAAAAAAAAAAAAAAK/////0AAAAAAAAAAAAAAAAn/////UA"
"AAAAAAAAAAAAAACP////9wAAAAAAAAAAAAAAAF/////7AAAAAAAAAAAAAAAAL/////4QAAAAAAAAAAAAAAAN/////2AAAAAAAAAAAAAAAAj/////0QAAAAAA"
"AAAAAAAAAv/////5AAAAAAAAAAAAAAAAr/////9wAAAAAAAABJAAAAAu//////ogAAAAAAS/wAAAAAb//////+lSEBNZ3//AAAAAAI///////////////8AA"
"AAAACP//////////////wAAAAAAAbv/////////////AAAAAAAACv////////////6AAAAAAAAADrv////////6TAAAAAAAAAAAASKzv/tynMAAAAAAAz///"
"///+7cuoYwAAAAAAAAAAAM/////////////pQAAAAAAAAADP//////////////swAAAAAAAAz///////////////+AAAAAAAAM////////////////+hAAAA"
"AADP////////////////+wAAAAAAz////9AAEjav//////+AAAAAAM/////QAAAAAp//////9AAAAADP////0AAAAAAF//////0AAAAAz////9AAAAAAAG//"
"////UAAAAM/////QAAAAAAAK/////7AAAADP////0AAAAAAAA//////xAAAAz////9AAAAAAAADP////9QAAAM/////QAAAAAAAAj/////gAAADP////0AAA"
"AAAAAF/////5AAAAz////9AAAAAAAABP////+wAAAM/////QAAAAAAAAP/////sAAADP////0AAAAAAAAD/////7AAAAz////9AAAAAAAABP////+wAAAM//"
"///QAAAAAAAAX/////kAAADP////0AAAAAAAAI/////3AAAAz////9AAAAAAAADP////9AAAAM/////QAAAAAAAD//////EAAADP////0AAAAAAACv////+w"
"AAAAz////9AAAAAAAG//////UAAAAM/////QAAAAAAb//////QAAAADP////0AAAAAKf//////QAAAAAz////9AAEjav//////+AAAAAAM//////////////"
"///7AAAAAADP////////////////oQAAAAAAz///////////////+AAAAAAAAM//////////////+zAAAAAAAADP////////////6TAAAAAAAAAAz//////+"
"7cuoYwAAAAAAAAAAAM//////////////+AAAAAz//////////////4AAAADP//////////////gAAAAM//////////////+AAAAAz//////////////4AAAA"
"DP//////////////gAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAA"
"AAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz/////////////+gAAAADP/////////////6AAAAAM//////////////oAAAAAz///////////"
"//+gAAAADP/////////////6AAAAAM//////////////oAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AA"
"AAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz///"
"////////////EAAADP//////////////8QAAAM///////////////xAAAAz///////////////EAAADP//////////////8QAAAM///////////////xAAAA"
"z//////////////4AAAADP//////////////gAAAAM//////////////+AAAAAz//////////////4AAAADP//////////////gAAAAM//////////////+A"
"AAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAA"
"AAAAAAAAz////9AAAAAAAAAAAAAADP/////////////6AAAAAM//////////////oAAAAAz/////////////+gAAAADP/////////////6AAAAAM////////"
"//////oAAAAAz/////////////+gAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM////"
"/QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM"
"/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAAAAAAAAADes3v/tyoUg"
"AAAAAAAAAAAAAo7//////////ZMAAAAAAAAAAZ//////////////0QAAAAAAAF7///////////////IAAAAAAAf////////////////yAAAAAAB/////////"
"////////8gAAAAAF///////7cyESNYv///IAAAAALv/////7MAAAAAAAFs/yAAAAAK//////kAAAAAAAAAAEsgAAAAL/////+gAAAAAAAAAAAAAAAAAI////"
"/9EAAAAAAAAAAAAAAAAADf////9gAAAAAAAAAAAAAAAAAC/////+EAAAAAAAAAAAAAAAAABf////+wAAAAAAAAAAAAAAAAAAj/////cAAAAAAAAAAAAAAAAA"
"AJ/////1AAAAAAAAAAAAAAAAAACv////9AAAAAAv////////UAAAr/////QAAAAAL////////1AAAK/////0AAAAAC////////9QAACf////9QAAAAAv////"
"////UAAAj/////cAAAAAL////////1AAAF/////7AAAAAC////////9QAAAv/////gAAAAAAAADP////UAAADf////9gAAAAAAAAz////1AAAAj/////0AAA"
"AAAAAM////9QAAAC//////gAAAAAAADP////UAAAAK//////cAAAAAAAz////1AAAAAu//////ogAAAAAM////9QAAAABv//////+mMQEkjv////UAAAAACP"
"/////////////////1AAAAAACP////////////////9QAAAAAABu////////////////UAAAAAAAAr//////////////tQAAAAAAAAADrv/////////7cgAA"
"AAAAAAAAAABIrO/+3bl0EAAAAAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAA"
"AG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM//"
"///QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG////"
"/0AAAAAM///////////////////0AAAAAM///////////////////0AAAAAM///////////////////0AAAAAM///////////////////0AAAAAM////////"
"///////////0AAAAAM///////////////////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAA"
"AM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG"
"/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM////"
"/QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAAAAAG/////0AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP"
"////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AA"
"AAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP//"
"//0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAAAADP////0AAAAAAAz////9"
"AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9"
"AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9"
"AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9AAAAAAAM/////QAAAAAADP////0AAAAAAAz////9"
"AAAAAAAM/////QAAAAAADP////0AAAAAAAz////8AAAAAAAO////+wAAAAAAL/////oAAAAAAI/////3AAAAAAT/////8wAAABOf/////9AAAJ////////9g"
"AACf///////7AAAAn///////0QAAAJ//////+hAAAACf////+1AAAAAAn/7cliAAAAAAAAAAz////9AAAAAAAD7/////wQAAAM/////QAAAAAAPv/////BAA"
"AADP////0AAAAAA+/////8EAAAAAz////9AAAAAD7/////wQAAAAAM/////QAAAAPv/////BAAAAAADP////0AAAA+/////8EAAAAAAAz////9AAAE7/////"
"wQAAAAAAAM/////QAATv/////BAAAAAAAADP////0ABO/////8EAAAAAAAAAz////9AE7/////wQAAAAAAAAAM/////QTv/////BAAAAAAAAAADP////1O//"
"///8EAAAAAAAAAAAz////+7/////wQAAAAAAAAAAAM///////////BAAAAAAAAAAAADP/////////8EAAAAAAAAAAAAAz/////////wQAAAAAAAAAAAAAM//"
"///////6AAAAAAAAAAAAAADP/////////5AAAAAAAAAAAAAAz//////////5AAAAAAAAAAAAAM///////////5AAAAAAAAAAAADP////7//////5AAAAAAAA"
"AAAAz////9T//////5AAAAAAAAAAAM/////QT//////5AAAAAAAAAADP////0AT//////5AAAAAAAAAAz////9AAT//////5AAAAAAAAAM/////QAAT/////"
"/5AAAAAAAADP////0AAAT//////5AAAAAAAAz////9AAAAT//////4AAAAAAAM/////QAAAAT//////4AAAAAADP////0AAAAAX//////4AAAAAAz////9AA"
"AAAAX//////4AAAAAM/////QAAAAAAX//////4AAAADP////0AAAAAAAX//////4AAAAz////9AAAAAAAAX//////4AAAM/////QAAAAAAAAAAAADP////0A"
"AAAAAAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAA"
"AAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAA"
"AAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAA"
"z////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAAz////9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP////0AAAAAAAAAAAAAz///"
"/9AAAAAAAAAAAAAM/////QAAAAAAAAAAAADP//////////////8QAAz///////////////EAAM///////////////xAADP//////////////8QAAz///////"
"////////EAAM///////////////xAADP//////cAAAAAAAAAr//////4AAAAAM///////QAAAAAAAAH///////gAAAAAz///////QAAAAAAAB///////+AAA"
"AADP//////+gAAAAAAAN///////4AAAAAM////////IAAAAAAF////////gAAAAAz///////9wAAAAAAv///////+AAAAADP///////9AAAAAAL////////4"
"AAAAAM////////9QAAAACP////////gAAAAAz////////7AAAAAe////////+AAAAADP////7///8gAAAG////7////4AAAAAM////+P///4AAAAz///2v//"
"//gAAAAAz////2r///4AAAP///96////+AAAAADP////ZP///2AACv///xr////4AAAAAM////9g3///wAAf///5Cv////gAAAAAz////2B////zAH////MK"
"////+AAAAADP////YB7///kA3///wAr////4AAAAAM////9gCf///hT///9gCv////gAAAAAz////2AD////a////hAK////+AAAAADP////YADP///f///4"
"AAr////4AAAAAM////9gAG////////IACv////gAAAAAz////2AADv//////sAAK////+AAAAADP////YAAI//////9QAAr////4AAAAAM////9gAAL/////"
"/QAACv////gAAAAAz////2AAAL/////3AAAK////+AAAAADP////YAAAX/////EAAAr////4AAAAAM////9gAAAN////oAAACv////gAAAAAz////2AAAAf/"
"//9AAAAK////+AAAAADP////YAAAAf///AAAAAr////4AAAAAM////9gAAAAAAAAAAAACv////gAAAAAz////2AAAAAAAAAAAAAK////+AAAAADP////YAAA"
"AAAAAAAAAAr////4AAAAAM////9gAAAAAAAAAAAACv////gAAAAAz////2AAAAAAAAAAAAAK////+AAAAADP////YAAAAAAAAAAAAAr////4AAAAAM//////"
"IAAAAAAA7////0AAAAAM//////oAAAAAAA7////0AAAAAM//////8wAAAAAA7////0AAAAAM//////+wAAAAAA7////0AAAAAM///////zAAAAAA7////0AA"
"AAAM///////7AAAAAA7////0AAAAAM////////QAAAAA7////0AAAAAM////////wAAAAA7////0AAAAAM////////9QAAAA7////0AAAAAM/////////QAA"
"AA7////0AAAAAM/////////2AAAA7////0AAAAAM////+f///9AAAA7////0AAAAAM////9q////YAAA7////0AAAAAM////9i////4QAA7////0AAAAAM//"
"//9gn///9wAA7////0AAAAAM////9gHv///hAA7////0AAAAAM////9gCP///4AA7////0AAAAAM////9gAe///+EA7////0AAAAAM////9gAH////gA7///"
"/0AAAAAM////9gAB7///8g7////0AAAAAM////9gAAf///+Q7////0AAAAAM////9gAADf///y7////0AAAAAM////9gAABv///67////0AAAAAM////9gAA"
"AN/////////0AAAAAM////9gAAAF/////////0AAAAAM////9gAAAAz////////0AAAAAM////9gAAAAX////////0AAAAAM////9gAAAADP///////0AAAA"
"AM////9gAAAABP///////0AAAAAM////9gAAAAAL///////0AAAAAM////9gAAAAAD///////0AAAAAM////9gAAAAAAr//////0AAAAAM////9gAAAAAAP/"
"/////0AAAAAM////9gAAAAAACv/////0AAAAAAAAAAADes7v7spzAAAAAAAAAAAAAAABff////////6BAAAAAAAAAAAABu///////////+cAAAAAAAAAABv/"
"/////////////CAAAAAAAAAc///////////////9IAAAAAAAHP////////////////0QAAAAAAn//////pQgFI7/////+wAAAAAE//////wgAAAAK//////2"
"AAAAAM/////8EAAAAAAL/////9AAAABP/////yAAAAAAAB7/////UAAACv////+QAAAAAAAAf/////sAAADv////8wAAAAAAAAH/////8QAAP/////0AAAAA"
"AAAAC/////9AAAb/////kAAAAAAAAACP////9wAAj/////cAAAAAAAAABf////+QAAn/////UAAAAAAAAABP////+wAAr/////QAAAAAAAAAA/////+wAAr/"
"////QAAAAAAAAAAv/////AAAr/////QAAAAAAAAAA/////+wAAn/////UAAAAAAAAAA/////+wAAj/////cAAAAAAAAABf////+QAAb/////kAAAAAAAAACP"
"////9wAAP/////0AAAAAAAAAC/////9AAADv////8wAAAAAAAAH/////8QAACv////+AAAAAAAAAf/////sAAABP/////yAAAAAAAB7/////UAAAAM/////8"
"EAAAAAAL/////9AAAAAE//////wgAAAAK//////2AAAAAAn//////pQgFI7/////+wAAAAAAHP////////////////0QAAAAAAAc///////////////9IAAA"
"AAAAABv//////////////CAAAAAAAAAABu///////////+cAAAAAAAAAAAABff////////6BAAAAAAAAAAAAAAADes7v/spzAAAAAAAAAAAAz/////////7c"
"pzAAAAAAAADP/////////////FAAAAAAAM//////////////+yAAAAAAz///////////////0gAAAADP///////////////9EAAAAM////////////////+A"
"AAAAz////9AAABSf/////+EAAADP////0AAAAAX/////9QAAAM/////QAAAAAJ/////5AAAAz////9AAAAAAT/////sAAADP////0AAAAAAv/////AAAAM//"
"///QAAAAAC/////8AAAAz////9AAAAAAT/////oAAADP////0AAAAACf////+QAAAM/////QAAAABf/////1AAAAz////9AAABOf/////+EAAADP////////"
"////////gAAAAM////////////////0QAAAAz///////////////0gAAAADP//////////////sgAAAAAM/////////////8YAAAAAAAz/////////7cpzAA"
"AAAAAADP////0AAAAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAAA"
"z////9AAAAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAAAM/////Q"
"AAAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAAAAAAAAAAA3rO7+7KdAAAAAAAAAAAAAAAAX3////////+ggAAAAAAAAAAAAbv///////////4AAAAAAAAAAAb"
"//////////////wgAAAAAAAAHP///////////////jAAAAAAABz////////////////9IAAAAAAJ//////6UIBSO//////sAAAAABP/////8IAAAACv/////"
"9gAAAADP/////BAAAAAAC//////hAAAAT/////8gAAAAAAAe/////2AAAAr/////kAAAAAAAAH/////7AAAA7/////MAAAAAAAAB//////EAAD/////9AAAA"
"AAAAAAv/////QAAG/////5AAAAAAAAAAj/////cAAI/////3AAAAAAAAAAX/////kAAJ/////1AAAAAAAAAAT/////sAAK/////0AAAAAAAAAAP/////sAAK"
"/////0AAAAAAAAAAL/////wAAK/////0AAAAAAAAAAP/////sAAJ/////1AAAAAAAAAAP/////oAAI/////2AAAAAAAAAAX/////kAAG/////5AAAAAAAAAA"
"j/////cAAD/////8AAAAAAAAAAv/////QAAA7/////IAAAAAAAAB/////+EAAAr/////gAAAAAAAAH/////6AAAAT/////4QAAAAAAAe/////1AAAADf////"
"+wAAAAAAC//////AAAAABf/////7IAAAACv/////9AAAAAAK//////6EEBSO//////kAAAAAAB3////////////////8EAAAAAAALf///////////////RAA"
"AAAAAAAb//////////////sQAAAAAAAAAAfv///////////nAAAAAAAAAAAAAX3/////////sQAAAAAAAAAAAAAAA3rN7/////4wAAAAAAAAAAAAAAAAAAAD"
"7////RAAAAAAAAAAAAAAAAAAAAb////7AAAAAAAAAAAAAAAAAAAACf////gAAAAAAAAAAAAAAAAAAAAM////9QAAAAAAAAAAAAAAAAAAAC7////zAAAAAAAA"
"AAAAAAAAAAAAT////9EAAAAAAAAAAAAAAAAAAAB/////sAAAAADP////////7tuFEAAAAAAAAAz/////////////ogAAAAAAAM//////////////9gAAAAAA"
"DP//////////////9gAAAAAAz///////////////4gAAAAAM////////////////gAAAAADP////0AABOO/////9AAAAAAz////9AAAABP/////xAAAAAM//"
"///QAAAAC/////8gAAAADP////0AAAAAf/////MAAAAAz////9AAAAAH/////yAAAAAM/////QAAAACP////8AAAAADP////0AAAAAv////8AAAAAAz////9"
"AAAABP////9gAAAAAM/////QAAE4/////8AAAAAADP//////////////0gAAAAAAz/////////////+xAAAAAAAM////////////+1AAAAAAAADP////////"
"////tAAAAAAAAAz/////////////+AAAAAAAAM//////////////+AAAAAAADP////0AAm3/////9AAAAAAAz////9AAAAv/////0AAAAAAM/////QAAAB3/"
"////YAAAAADP////0AAAAF/////+AAAAAAz////9AAAAAM/////2AAAAAM/////QAAAABf/////QAAAADP////0AAAAADP////9gAAAAz////9AAAAAAX///"
"//0AAAAM/////QAAAAAA3/////UAAADP////0AAAAAAG/////8AAAAz////9AAAAAAAN/////0AAAM/////QAAAAAABv/////AAADP////0AAAAAAADv////"
"9AAAAAAASL3v/ty5ZBAAAAAAAAAAB9//////////2kAAAAAAADz////////////4AAAAAAA+/////////////4AAAAAAHf/////////////4AAAAAAj/////"
"/////////4AAAAAA7////+hBACNp3//4AAAAAE/////SAAAAAABJ74AAAAAI////9gAAAAAAAAF3AAAAAJ////8wAAAAAAAAAAAAAAAK////9AAAAAAAAAAA"
"AAAAAK////+gAAAAAAAAAAAAAAAJ/////5IAAAAAAAAAAAAAAG//////+3QQAAAAAAAAAAAC/////////9liAAAAAAAAAAr///////////2CAAAAAAAALv//"
"//////////kQAAAAAABO/////////////TAAAAAAACz////////////+IAAAAAAABs////////////oAAAAAAAAAOM//////////8gAAAAAAAAAAFHvv////"
"//9wAAAAAAAAAAAAAEr/////+gAAAAAAAAAAAAAABf////+wAAAAAAAAAAAAAAAL////+wAAAAAAAAAAAAAAAJ////+gAAAGkwAAAAAAAAAM////+QAAAG/8"
"cgAAAAAABv////9QAAAG///9lkIQElv/////8QAAAG////////////////oAAAAG///////////////+IAAAAG///////////////0AAAAAF7///////////"
"//1AAAAAAABJ3//////////YEAAAAAAAAAAVeb3u/tynQAAAAAAAz///////////////////8s////////////////////LP///////////////////yz///"
"////////////////8s////////////////////LP///////////////////yAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/////AAAA"
"AAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/"
"////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAA"
"AAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8A"
"AAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAA"
"Cv////8AAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAK/////wAAAAAAAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAA"
"AACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0A"
"AAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz///"
"/9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM"
"/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAL/////QAAAAAACP////8gAAAAr////+AAAAAAAJ/////xAA"
"AACf////8AAAAAAAr/////AAAAAI/////zAAAAAADP////0AAAAAX/////YAAAAAAf////+gAAAAAf/////AAAAAAH/////2AAAAAAz/////gAAAAD7/////"
"IAAAAABf/////7UQE4//////oAAAAAAAz///////////////8wAAAAAAAu//////////////9wAAAAAAAATv////////////+QAAAAAAAAACz///////////"
"5gAAAAAAAAAAAGz////////+ggAAAAAAAAAAAAADac3v7ct0AAAAAAAAn/////IAAAAAAAAAAH/////zT/////cAAAAAAAAAAN/////ADf////wAAAAAAAAA"
"A/////9wCP////8gAAAAAAAACP////8gAv////+AAAAAAAAADf////sAAM/////QAAAAAAAAT/////UAAG/////zAAAAAAAAn////+EAAB/////5AAAAAAAA"
"7////6AAAAr////+AAAAAAAF/////0AAAAX/////QAAAAAAK/////QAAAADv////oAAAAAAf////+AAAAACf////4QAAAABv////8wAAAAA/////9QAAAAC/"
"////wAAAAAAN////+wAAAAH/////cAAAAAAH/////xAAAAf/////EAAAAAAC/////2AAAAz////7AAAAAAAAv////8AAAC/////1AAAAAAAAb/////IAAI//"
"///hAAAAAAAAH/////cAAN////+QAAAAAAAACv////wAA/////9AAAAAAAAABP////8wCP////0AAAAAAAAAAO////+ADv////gAAAAAAAAAAI/////QT///"
"//IAAAAAAAAAAD/////0n////8AAAAAAAAAAAAz////67////2AAAAAAAAAAAAf//////////xAAAAAAAAAAAAL/////////+gAAAAAAAAAAAAC/////////"
"9QAAAAAAAAAAAABv////////4AAAAAAAAAAAAAAe////////kAAAAAAAAAAAAAAK////////MAAAAAAAAAAAAAAE///////9AAAAAAAAAAAAAAAA3//////4"
"AAAAAAAAAAAAAAAAj//////yAAAAAAAACP////wAAAAAAA7////6AAAAAAAf////8wBP////8AAAAAAC/////9AAAAAABP////4AAf////9AAAAAAG//////"
"IAAAAACP////sAAM////9wAAAAAJ//////UAAAAAC/////cAAJ////+wAAAAAN//////kAAAAADv////QAAF/////gAAAAAf//////wAAAAAP/////EAAC//"
"///zAAAABf//////8QAAAAf////8AAAA3////2AAAACP//////9AAAAAr////4AAAAr////6AAAADP///f//+AAAAA7////1AAAAb////9AAAAD///9v//+w"
"AAAC/////xAAAAP/////IAAAT///wv///gAAAG/////QAAAADv////UAAAf///gN///zAAAJ////+QAAAAC/////kAAAv///UK///3AAAN////9gAAAAB///"
"//wAAA7///EG///6AAAf////8gAAAAA/////8QAD///9AC///+AABf////4AAAAAAP////9AAG///5AA7///IACP////oAAAAAAL////+AAK///2AAr///YA"
"DP////cAAAAAAI////+wAN///yAAf///kAH/////MAAAAAAE/////wAv///gAAP///0AT/////AAAAAAAB/////zBf//+gAADv//8Qj////7AAAAAAAAz///"
"/3Cf//9wAAC///9Qv////4AAAAAAAAn////7DP//8wAACP//+A7////0AAAAAAAAX////+H///8AAABP///D/////xAAAAAAAAL/////f///sAAAAf///3//"
"///AAAAAAAAADf////3///gAAAAM///9////+QAAAAAAAACv////////QAAAAJ////////9QAAAAAAAABv////////EAAAAF////////8gAAAAAAAAA/////"
"///8AAAAAC////////4AAAAAAAAAAO///////5AAAAAA3///////oAAAAAAAAAAL///////1AAAAAAr///////cAAAAAAAAAAH///////yAAAAAAb///////"
"MAAAAAAAAAAE///////QAAAAAAP//////+AAAAAAAAAAAA//////+gAAAAAADv/////7AAAAAAAAAAAAz/////9gAAAAAACv/////4AAAAAABf////+gAAAA"
"AAAAX/////sACv////9QAAAAAAAe/////iAAHv////4QAAAAAAr/////YAAAX/////sAAAAABf////+wAAAAr/////YAAAAB7////+IAAAAB7////+IAAACv"
"////9gAAAAAF/////7AAAF/////7AAAAAAAK/////2AAHv////4gAAAAAAAd/////iAK/////2AAAAAAAABP////+wX/////sAAAAAAAAACf////9+/////i"
"AAAAAAAAAAHf//////////UAAAAAAAAAAAT/////////+gAAAAAAAAAAAAn////////+EAAAAAAAAAAAAB3///////9QAAAAAAAAAAAAAE///////6AAAAAA"
"AAAAAAAAAK//////8QAAAAAAAAAAAAAALv//////cAAAAAAAAAAAAAAL////////MAAAAAAAAAAAAAb////////8AAAAAAAAAAAAAu/////////3AAAAAAAA"
"AAAAv//////////zAAAAAAAAAABv////+//////AAAAAAAAAAC7////9GP////+AAAAAAAAAC/////9ADf////8wAAAAAAAG/////5AAP/////wAAAAAAALv"
"////0QAAj/////gAAAAAAL/////0AAAAz/////MAAAAAf/////kAAAAD/////8AAAAAu/////RAAAAAH/////4AAAAz/////QAAAAAAM/////zAAB/////+Q"
"AAAAAAA//////QAC/////9EAAAAAAAB/////+ADP////9AAAAAAAAADP////8y//////UAAAAAAAAB7/////cH/////9EAAAAAAACv/////AAM/////5AAAA"
"AAAE//////IAA//////zAAAAAAHf////9wAACP/////AAAAAAI/////8AAAADf////9wAAAAP/////8wAAAAT/////4gAAAM/////4AAAAAAn/////sAAAf/"
"////0QAAAAAB3/////UAAu/////0AAAAAAAE/////+EAv/////kAAAAAAAAK/////5Bf/////RAAAAAAAAAe/////17/////QAAAAAAAAABf//////////+g"
"AAAAAAAAAACv/////////+EAAAAAAAAAAAHv////////9QAAAAAAAAAAAAb////////6AAAAAAAAAAAAAAv///////4gAAAAAAAAAAAAAC7//////2AAAAAA"
"AAAAAAAAAH//////sAAAAAAAAAAAAAAAAM/////yAAAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAAAK/////wAAAAAAAAAA"
"AAAAAACv////8AAAAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAA"
"AAAK/////wAAAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAAAr/////AAAAAAAAAAAAAAAAAK/////wAAAAAAAAAAAAAAAACv////8AAAAAAAAAAAAAAAAA"
"r/////AAAAAAAAAAb//////////////////AAAb//////////////////AAAb//////////////////AAAb//////////////////AAAb///////////////"
"///AAAb/////////////////+QAAAAAAAAAAAAAF//////0QAAAAAAAAAAAAA+/////+IAAAAAAAAAAAAAHf/////1AAAAAAAAAAAAAAv/////+AAAAAAAAA"
"AAAAAI//////sAAAAAAAAAAAAABf/////9EAAAAAAAAAAAAAPv/////jAAAAAAAAAAAAAB3/////9QAAAAAAAAAAAAAL//////gAAAAAAAAAAAAACP/////7"
"AAAAAAAAAAAAAAX//////RAAAAAAAAAAAAAC7/////4wAAAAAAAAAAAAAd//////UAAAAAAAAAAAAACv/////4AAAAAAAAAAAAAAj/////+wAAAAAAAAAAAA"
"AF//////0QAAAAAAAAAAAAAu//////MAAAAAAAAAAAAAHf/////1AAAAAAAAAAAAAAr/////+QAAAAAAAAAAAAAH//////sAAAAAAAAAAAAABP/////9EAAA"
"AAAAAAAAAALv/////zAAAAAAAAAAAAAAz//////////////////0AA7//////////////////0AA7//////////////////0AA7//////////////////0AA"
"7//////////////////0AA7//////////////////0AAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP//"
"//gAAAAAAACP////gAAAAAAACP////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///3AAAAAAAAAJ///5AAAAAAAAAL///6AAAAAA"
"AAAM///8AAAAAAAAAO///+AAAAAAAAAf////EAAAAAAAA/////IAAAAAAABP////QAAAAAAABv////YAAAAAAACP////gAAAAAAACP////gAAAAAAACP////"
"gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAACP////gAAAAAAA"
"CP////gAAAAAAACP////gAAAAAAACP////gAAAAAAF/////AAAAABf////wAAAAAX////8AAAAAF/////AAAAABf////wAAAAAX////8AAAAAF/////AAAAA"
"Bf////wAAAAAX////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////EAAAAAAAAAAAH/////EAAAAAAAAAAAH/////EAAAAAAAAAAAH/////EAAAAAAAAAAAH/////EAAAAAAAAA"
"AAH/////EAAAAAAAAAAAH/////EAAAAAAAAAAAH/////EAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////EAAA"
"AAAAAAAAL/////AAAAAAAAAAAAX////+AAAAAAAAAAAAz////7AAAAAAAAAAAJ/////1AAAAAAAAAACP/////AAAAAAAAAAAj/////4gAAAAAAAAAI/////+"
"QAAAAAAAAAB//////0AAAAAAAAAAP/////5AAAAAAAAAAAz/////QAAAAAAAAAAD/////2AAAAAAAAAAAI/////AAAAAAAAAAAAK////9gAAAAAAAAAAAM//"
"//9QAAAAAAAAAAAM////9gAAAAAASAAAAK/////RAAAABL+wAAAH/////9UgJI3/+wAAAD////////////+wAAAAv///////////+wAAAALv//////////+w"
"AAAAA+//////////+wAAAAABnv///////8YQAAAAAAAWnN7+24UQAAAAAAAAAAAAAAAB3//+QAAAAAAAAAAAAAAAAAAL///jAAAAAAAAAAAAAAAAAAB///4w"
"AAAAAAAAAAAAAAAAAAP//9IAAAAAAAAAAAAAAAAAAB3//SAAAAAAAAAAAAAAAAAAAK//wQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAj//////yAAAAAAAAAAAAAAAA3//////4AAAAAAAAAAAAAAAE///////9AAAAAAAAAAAAAAAK////////MAAAAAAAAAAAAAAe////////"
"kAAAAAAAAAAAAABv////////4AAAAAAAAAAAAAC/////////9QAAAAAAAAAAAAL/////////+gAAAAAAAAAAAAf////8/////xAAAAAAAAAAAAz////1v///"
"/2AAAAAAAAAAAD/////xb////8AAAAAAAAAAAI////+gH/////IAAAAAAAAAAO////9QC/////gAAAAAAAAABP////8QBv////0AAAAAAAAACv////oAAf//"
"//9AAAAAAAAAHv////UAAL////+QAAAAAAAAb/////EAAG/////hAAAAAAAAv////7AAAC/////1AAAAAAAC/////1AAAAz////7AAAAAAAH/////xAAAAf/"
"////EAAAAAAN////+wAAAAL/////cAAAAAA/////9gAAAADP////wAAAAACf////////////////8wAAAADv////////////////+AAAAAX/////////////"
"/////QAAAAr//////////////////0AAAB///////////////////6AAAG///////////////////+EAAM/////QAAAAAAAAT/////UAAv////+AAAAAAAAA"
"Df////sACP////8gAAAAAAAACP////8gDf////wAAAAAAAAAA/////9wT/////cAAAAAAAAAAN/////An/////IAAAAAAAAAAH/////zAAAAAAAAAACv//+A"
"AAAAAAAAAAAAAABv//9wAAAAAAAAAAAAAAA///9gAAAAAAAAAAAAAAAd//9QAAAAAAAAAAAAAAAK//5AAAAAAAAAAAAAAAAG//5AAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz//////////////4AAAADP//////////////gAAAAM//////////////+AAAAAz//////////////4AAAADP////"
"//////////gAAAAM//////////////+AAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP"
"////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP/////////////6AAAAAM//////////////oAAAAAz/////////////+gAA"
"AADP/////////////6AAAAAM//////////////oAAAAAz/////////////+gAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAA"
"AAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAAAAAAAAAAAADP////0AAAAAAAAAAAAAAM/////QAAAAAAAAAAAAAAz////9AAAA"
"AAAAAAAAAADP//////////////8QAAAM///////////////xAAAAz///////////////EAAADP//////////////8QAAAM///////////////xAAAAz/////"
"//////////EAAAAAAE///9IAAAAAHf//wQAAAAAL///BAAAAAAf//7EAAAAAA///oAAAAAAB3/+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAM/////QAAAADP//"
"//0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAA"
"AM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////"
"0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM/////QAAAADP////0AAAAAz////9AAAAAM"
"/////QAAAAAAAAAAKu60AAAO/zAAAAAAAAAAAAAAAD7///oQAf/yAAAAAAAAAAAAAAAL/////UGf/gAAAAAAAAAAAAAAAv/3Fu////+QAAAAAAAAAAAAAABP"
"/gACv///0QAAAAAAAAAAAAAABf/AAABs/qIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADP/////yAAAAAAAO////9A"
"AAAADP/////6AAAAAAAO////9AAAAADP//////MAAAAAAO////9AAAAADP//////sAAAAAAO////9AAAAADP//////8wAAAAAO////9AAAAADP//////+wAA"
"AAAO////9AAAAADP///////0AAAAAO////9AAAAADP///////8AAAAAO////9AAAAADP////////UAAAAO////9AAAAADP////////0AAAAO////9AAAAADP"
"////////9gAAAO////9AAAAADP////n////QAAAO////9AAAAADP////av///2AAAO////9AAAAADP////Yv///+EAAO////9AAAAADP////YJ////cAAO//"
"//9AAAAADP////YB7///4QAO////9AAAAADP////YAj///+AAO////9AAAAADP////YAHv///hAO////9AAAAADP////YAB////4AO////9AAAAADP////YA"
"Ae////IO////9AAAAADP////YAAH////kO////9AAAAADP////YAAA3///8u////9AAAAADP////YAAAb///+u////9AAAAADP////YAAADf////////9AAA"
"AADP////YAAABf////////9AAAAADP////YAAAAM////////9AAAAADP////YAAAAF////////9AAAAADP////YAAAAAz///////9AAAAADP////YAAAAAT/"
"//////9AAAAADP////YAAAAAC///////9AAAAADP////YAAAAAA///////9AAAAADP////YAAAAAAK//////9AAAAADP////YAAAAAAD//////9AAAAADP//"
"//YAAAAAAAr/////9AAAAAAAAAAAAAAABP///SAAAAAAAAAAAAAAAAAAAAHf//wQAAAAAAAAAAAAAAAAAAAAv//8EAAAAAAAAAAAAAAAAAAAAH//+xAAAAAA"
"AAAAAAAAAAAAAAA///oAAAAAAAAAAAAAAAAAAAAAHf/5AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3rO7+7KcwAAAAAAAAAAAAAAAX3///"
"/////+gQAAAAAAAAAAAAbv///////////nAAAAAAAAAAAb//////////////wgAAAAAAAAHP///////////////SAAAAAAABz////////////////9EAAAAA"
"AJ//////6UIBSO//////sAAAAABP/////8IAAAACv/////9gAAAADP/////BAAAAAAC//////QAAAAT/////8gAAAAAAAe/////1AAAAr/////kAAAAAAAAH"
"/////7AAAA7/////MAAAAAAAAB//////EAAD/////9AAAAAAAAAAv/////QAAG/////5AAAAAAAAAAj/////cAAI/////3AAAAAAAAAAX/////kAAJ/////1"
"AAAAAAAAAAT/////sAAK/////0AAAAAAAAAAP/////sAAK/////0AAAAAAAAAAL/////wAAK/////0AAAAAAAAAAP/////sAAJ/////1AAAAAAAAAAP/////"
"sAAI/////3AAAAAAAAAAX/////kAAG/////5AAAAAAAAAAj/////cAAD/////9AAAAAAAAAAv/////QAAA7/////MAAAAAAAAB//////EAAAr/////gAAAAA"
"AAAH/////7AAAAT/////8gAAAAAAAe/////1AAAADP/////BAAAAAAC//////QAAAABP/////8IAAAACv/////9gAAAAAJ//////6UIBSO//////sAAAAAAB"
"z////////////////9EAAAAAAAHP///////////////SAAAAAAAAAb//////////////wgAAAAAAAAAAbv///////////nAAAAAAAAAAAAAX3////////+gQ"
"AAAAAAAAAAAAAAA3rO7/7KcwAAAAAAAAAAAAAAAAAAAALv//4wAAAAAAAAAAAAAAAAAADP//0gAAAAAAAAAAAAAAAAAACf//0gAAAAAAAAAAAAAAAAAABf//"
"wQAAAAAAAAAAAAAAAAAAAu//wQAAAAAAAAAAAAAAAAAAAM//sQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz////9AA"
"AAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM////"
"/QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP"
"////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAA"
"AAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////"
"IAAAAL/////QAAAAAACP////8gAAAAr////+AAAAAAAJ/////xAAAACf////8AAAAAAAr/////AAAAAI/////zAAAAAADP////0AAAAAX/////YAAAAAAf//"
"//+gAAAAAf/////AAAAAAH/////2AAAAAAz/////gAAAAD7/////IAAAAABf/////7UQE4//////oAAAAAAAz///////////////8wAAAAAAAu//////////"
"////9wAAAAAAAATv////////////+QAAAAAAAAACz///////////5gAAAAAAAAAAAGz////////+ggAAAAAAAAAAAAADac3v7ct0AAAAAAAAAAAAAAAG///Q"
"AI///AAAAAAAAAAAAAAAb//9AAj//8AAAAAAAAAAAAAABv//0ACP//wAAAAAAAAAAAAAAG///QAI///AAAAAAAAAAAAAAAb//9AAj//8AAAAAAAAAAAAAABv"
"//0ACP//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADP////0AAAAAAAj/////IAAAAM//"
"///QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAA"
"DP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8g"
"AAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj///"
"//IAAAAM/////QAAAAAACP////8gAAAAz////9AAAAAAAI/////yAAAADP////0AAAAAAAj/////IAAAAM/////QAAAAAACP////8gAAAAv////9AAAAAAAI"
"/////yAAAACv////4AAAAAAAn/////EAAAAJ/////wAAAAAACv////8AAAAAj/////MAAAAAAM/////QAAAABf////9gAAAAAB/////6AAAAAB/////8AAAA"
"AAf/////YAAAAADP////+AAAAAPv////8gAAAAAF//////tRATj/////+gAAAAAADP///////////////zAAAAAAAC7//////////////3AAAAAAAABO////"
"/////////5AAAAAAAAAALP///////////mAAAAAAAAAAAAbP////////6CAAAAAAAAAAAAAANpze/ty3QAAAAAAAAAAAAAAAAAAAAAAAA2m97v7tuXQAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAEnv/////////+tQAAAAAAAAAAAAAAAAAAAAAAAABt//////////////6BAAAAAAAAAAAAAAAAAAAAAATf////////////////"
"5gAAAAAAAAAAAAAAAAAAABn///////////////////sgAAAAAAAAAAAAAAAAABz////////////////////+MAAAAAAAAAAAAAAAAC3/////////////////"
"/////kAAAAAAAAAAAAAAAB3///////////////////////4wAAAAAAAAAAAAAAz////////////////////////+IAAAAAAAAAAAAAj/////////////////"
"/////////AAAAAAAAAAAAAT///////////////////////////cAAAAAAAAAAADf//////////6EEBN9///////////yAAAAAAAAAAB///////////oQAAAA"
"B///////////oAAAAAAAAAAe//////////kAAAAAAAX//////////zAAAAAAAAAG//////////wAAAAAAAAJ//////////oAAAAAAAAA3/////////9AAAAA"
"AAAAHv/////////yAAAAAAAAT//////////AAAAAAAAAAI//////////cAAAAAAACf/////////2AAAAAAAAAAP//////////AAAAAAAAN//////////IAAA"
"AAAAAAAN//////////IAAAAAAD//////////0AAAAAAAAAAAr/////////9gAAAAAAb/////////+gAAAAAAAAAABv/////////6AAAAAACv/////////3AA"
"AAAAAAAAAE//////////0AAAAAAN//////////UAAAAAAAAAAAL//////////xAAAAAB//////////8wAAAAAAAAAAAP//////////QAAAAAP//////////y"
"AAAAAAAAAAAA3/////////9gAAAABf//////////AAAAAAAAAAAADP/////////5AAAAAH//////////4AAAAAAAAAAAAL//////////oAAAAAj/////////"
"/QAAAAAAAAAAAAr/////////+wAAAACf/////////9AAAAAAAAAAAACf/////////9AAAAAK//////////wAAAAAAAAAAAAJ//////////4AAAAAv///////"
"///AAAAAAAAAAAAAj//////////gAAAAC//////////7AAAAAAAAAAAACP//////////AAAAAM//////////sAAAAAAAAAAAAI//////////8AAAAAz/////"
"////+wAAAAAAAAAAAAj//////////wAAAAC//////////8AAAAAAAAAAAACP//////////AAAAAL//////////wAAAAAAAAAAAAI//////////4AAAAAr///"
"///////AAAAAAAAAAAAAn//////////gAAAACf/////////9AAAAAAAAAAAACf/////////9AAAAAI//////////0AAAAAAAAAAAAK//////////sAAAAAf/"
"/////////gAAAAAAAAAAAAv/////////+gAAAABf//////////EAAAAAAAAAAADP/////////5AAAAAD//////////8gAAAAAAAAAAAO//////////YAAAAA"
"H//////////0AAAAAAAAAAAA//////////9AAAAAAN//////////UAAAAAAAAAAAL//////////yAAAAAAr/////////+AAAAAAAAAAABP/////////9AAAA"
"AABv/////////6AAAAAAAAAAAH//////////oAAAAAAD//////////4AAAAAAAAAAAr/////////9gAAAAAADv/////////yAAAAAAAAAADv/////////yAA"
"AAAAAJ//////////cAAAAAAAAAA//////////8AAAAAAAAT//////////AAAAAAAAAAJ//////////cAAAAAAAAN//////////QAAAAAAAAB7/////////8g"
"AAAAAAAAb//////////QAAAAAAAAr/////////+gAAAAAAAAAe//////////oAAAAAAAb//////////zAAAAAAAAAAf//////////6EAAAAAj//////////6"
"AAAAAAAAAAAN///////////oQQE33///////////IAAAAAAAAAAAT///////////////////////////gAAAAAAAAAAAAJ//////////////////////////"
"wAAAAAAAAAAAAADP////////////////////////4gAAAAAAAAAAAAAB3///////////////////////4wAAAAAAAAAAAAAAAt//////////////////////"
"5AAAAAAAAAAAAAAAAAHP////////////////////4wAAAAAAAAAAAAAAAAABn///////////////////sgAAAAAAAAAAAAAAAAAAAE3////////////////+"
"YAAAAAAAAAAAAAAAAAAAAAAG3//////////////oEAAAAAAAAAAAAAAAAAAAAAAAAEnv//////////tRAAAAAAAAAAAAAAAAAAAAAAAAAAAANpve7/7bl0AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAli+//////////gAAAAAAAAAAAAAAAAAAAAAAAJYvv////////////+AAAAAAAAAAAAAAAAAAAACWL7///////////////"
"/4AAAAAAAAAAAAAAAAAAAB////////////////////gAAAAAAAAAAAAAAAAAAAH///////////////////+AAAAAAAAAAAAAAAAAAAAf////////////////"
"///4AAAAAAAAAAAAAAAAAAAB////////////////////gAAAAAAAAAAAAAAAAAAAH///////////////////+AAAAAAAAAAAAAAAAAAAAf//////////////"
"/////4AAAAAAAAAAAAAAAAAAAB////////////////////gAAAAAAAAAAAAAAAAAAAH///////////////////+AAAAAAAAAAAAAAAAAAAAf////////////"
"///////4AAAAAAAAAAAAAAAAAAAB///////adC//////////gAAAAAAAAAAAAAAAAAAAH///2nQQAAH/////////+AAAAAAAAAAAAAAAAAAAAdp0EAAAAAAf"
"/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"Af/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+AAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////gAAAAAAAAAAAAAAAAAAACv////////////////////////"
"////8wAAAAAAAAAK/////////////////////////////zAAAAAAAAAAr/////////////////////////////MAAAAAAAAACv//////////////////////"
"//////8wAAAAAAAAAK/////////////////////////////zAAAAAAAAAAr/////////////////////////////MAAAAAAAAACv////////////////////"
"////////8wAAAAAAAAAK/////////////////////////////zAAAAAAAAAAr/////////////////////////////MAAAAAAAAACv//////////////////"
"//////////8wAAAAAAAAAK/////////////////////////////zAAAAAAAAAAr/////////////////////////////MAAAAAAAAAAAAAAAA1ebze7/7tun"
"UgAAAAAAAAAAAAAAAAAAAAAAAAJZz/////////////2UAAAAAAAAAAAAAAAAAAAAFa7//////////////////XEAAAAAAAAAAAAAAAAmv///////////////"
"///////nAAAAAAAAAAAAAAAN/////////////////////////CAAAAAAAAAAAAAA3/////////////////////////5AAAAAAAAAAAAADf//////////////"
"////////////UAAAAAAAAAAAAN///////////////////////////0AAAAAAAAAAAA3///////////////////////////4QAAAAAAAAAADf////////////"
"///////////////6AAAAAAAAAAAN////////////////////////////8wAAAAAAAAAA3///////6nQhASWe/////////////7AAAAAAAAAADf/////pQAAA"
"AAAABu////////////8QAAAAAAAAAN////xhAAAAAAAAAALP///////////2AAAAAAAAAA3//8UAAAAAAAAAAAABz///////////oAAAAAAAAADf/VAAAAAA"
"AAAAAAAAAu///////////QAAAAAAAAAN+BAAAAAAAAAAAAAAAAj///////////AAAAAAAAAAkgAAAAAAAAAAAAAAAAAf//////////8QAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAz//////////yAAAAAAAAAAAAAAAAAAAAAAAAAAAACf//////////IAAAAAAAAAAAAAAAAAAAAAAAAAAAAI//////////8QAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAf//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAL//////////kAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAB7/////////9gAAAAAAAAAAAAAAAAAAAAAAAAAAAAX//////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAADP/////////6AAAAAAAAAAAA"
"AAAAAAAAAAAAAAAABv//////////MAAAAAAAAAAAAAAAAAAAAAAAAAAAAu//////////oAAAAAAAAAAAAAAAAAAAAAAAAAAAAL//////////4gAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAK//////////9gAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAJ///////////AAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAb///////////RAAAAAAAAAAAAAAAAAAAAAAAAAAAc///////////SAAAAAAAAAAAAAAAAAAAAAAAAAAA9///////////SAAAAAAAAAA"
"AAAAAAAAAAAAAAAABO///////////SAAAAAAAAAAAAAAAAAAAAAAAAAABf///////////SAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////BAAAAAAAAAA"
"AAAAAAAAAAAAAAAACf//////////+xAAAAAAAAAAAAAAAAAAAAAAAAAAG///////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAHP//////////+AAAAAAAAAAA"
"AAAAAAAAAAAAAAAALf//////////9gAAAAAAAAAAAAAAAAAAAAAAAAAATv//////////5QAAAAAAAAAAAAAAAAAAAAAAAAAAX///////////4wAAAAAAAAAA"
"AAAAAAAAAAAAAAAAf///////////0gAAAAAAAAAAAAAAAAAAAAAAAAAAn///////////sQAAAAAAAAAAAAAAAAAAAAAAAAABv///////////oAAAAAAAAAAA"
"AAAAAAAAAAAAAAABz///////////gAAAAAAAAAAAAAAAAAAAAAAAAAAC3///////////YAAAAAAAAAAAAAAAAAAAAAAAAAAE7//////////+QAAAAAAAAAAA"
"AAAAAAAAAAAAAAAF///////////9MAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////8IAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////"
"//////+QAAAAAAAAD//////////////////////////////5AAAAAAAAAP//////////////////////////////kAAAAAAAAA//////////////////////"
"////////+QAAAAAAAAD//////////////////////////////5AAAAAAAAAP//////////////////////////////kAAAAAAAAA////////////////////"
"//////////+QAAAAAAAAD//////////////////////////////5AAAAAAAAAP//////////////////////////////kAAAAAAAAA//////////////////"
"////////////+QAAAAAAAAD//////////////////////////////5AAAAAAAAAP//////////////////////////////kAAAAAAAAAAAAAAAABRom83u/+"
"7cuoYwAAAAAAAAAAAAAAAAAAAAAAAUit//////////////+4MAAAAAAAAAAAAAAAAAADfP///////////////////9cQAAAAAAAAAAAAAAAF////////////"
"///////////+cAAAAAAAAAAAAAAAX////////////////////////8IAAAAAAAAAAAAABf/////////////////////////kAAAAAAAAAAAAAF//////////"
"////////////////9AAAAAAAAAAAAAX//////////////////////////+IAAAAAAAAAAABf//////////////////////////+gAAAAAAAAAAAF////////"
"////////////////////QAAAAAAAAAAAX///////////////////////////+gAAAAAAAAAABf/////adTEQESWM//////////////EAAAAAAAAAAF///7Yg"
"AAAAAAAAAq////////////9AAAAAAAAAAAX/xRAAAAAAAAAAAABf///////////3AAAAAAAAAABaMAAAAAAAAAAAAAAAT///////////kAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAJ//////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAO//////////oAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAA3/////////+QAAAAAAAAAAAAAAAAAAAAAAAAAAAADf/////////3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////QAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAE//////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAAr/////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////zAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAXv/////////6AAAAAAAAAAAAAAAAAAAAAAAAAAADr//////////9EAAAAAAAAAAAAAAAAAAAAAAAEkad///////////+MAAAAAAAAA"
"AAAAAAAAAv///////////////////9MAAAAAAAAAAAAAAAAAAC///////////////////5EAAAAAAAAAAAAAAAAAAAL/////////////////+jAAAAAAAAAA"
"AAAAAAAAAAAv///////////////7YgAAAAAAAAAAAAAAAAAAAAAC////////////////6UAAAAAAAAAAAAAAAAAAAAAAL//////////////////WEAAAAAAA"
"AAAAAAAAAAAAAv///////////////////kAAAAAAAAAAAAAAAAAAAC////////////////////+QAAAAAAAAAAAAAAAAAAL/////////////////////sAAA"
"AAAAAAAAAAAAAAAv/////////////////////7AAAAAAAAAAAAAAAAAC//////////////////////9wAAAAAAAAAAAAAAAAAAAAABEkaM//////////////"
"IAAAAAAAAAAAAAAAAAAAAAAAAAAW3///////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////EAAAAAAAAAAAAAAAAAAAAAAAAAAABP////////"
"//9wAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAO//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAn/////"
"/////xAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////IAAAAAAAAAAAAAAAAAAAAAAAAAAAAF//////////8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAb///"
"///////zAAAAAAAAAAAAAAAAAAAAAAAAAAAACf//////////IAAAAAAAAAAAAAAAAAAAAAAAAAAAAO//////////8QAAAAAAAqMAAAAAAAAAAAAAAAAAAH//"
"/////////gAAAAAAAC/7QAAAAAAAAAAAAAAAAE///////////7AAAAAAAAL//8cQAAAAAAAAAAAAAH////////////cAAAAAAAAv////tyAAAAAAAAAAFd//"
"//////////8gAAAAAAAC///////qhTIQASNXv/////////////+gAAAAAAAAL//////////////////////////////zAAAAAAAAAv//////////////////"
"///////////5AAAAAAAAAC/////////////////////////////8EAAAAAAAAAL////////////////////////////9IAAAAAAAAAAv////////////////"
"///////////9IAAAAAAAAAAC///////////////////////////7EAAAAAAAAAAAL//////////////////////////mAAAAAAAAAAAAAv//////////////"
"//////////6BAAAAAAAAAAAAAAJ77////////////////////7YQAAAAAAAAAAAAAAAAAEet///////////////9piAAAAAAAAAAAAAAAAAAAAAAATV5rN3u"
"/+7cuoZBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK////////////EAAAAAAAAAAAAAAAAAAAAAAAAAAF////////////8QAAAAAAAAAAAAAAAAAAAAAA"
"AAAC7////////////xAAAAAAAAAAAAAAAAAAAAAAAAAAv/////////////EAAAAAAAAAAAAAAAAAAAAAAAAAb/////////////8QAAAAAAAAAAAAAAAAAAAA"
"AAAALv/////////////xAAAAAAAAAAAAAAAAAAAAAAAAC///////////////EAAAAAAAAAAAAAAAAAAAAAAABv//////////////8QAAAAAAAAAAAAAAAAAA"
"AAAAAu///////////////xAAAAAAAAAAAAAAAAAAAAAAAM////////////////EAAAAAAAAAAAAAAAAAAAAAAH////////////////8QAAAAAAAAAAAAAAAA"
"AAAAAC/////////////////xAAAAAAAAAAAAAAAAAAAAAAz/////////////////EAAAAAAAAAAAAAAAAAAAAAf///////3/////////8QAAAAAAAAAAAAAA"
"AAAAAAP///////qf/////////xAAAAAAAAAAAAAAAAAAAADP//////4Z//////////EAAAAAAAAAAAAAAAAAAACP//////9Qn/////////8QAAAAAAAAAAAA"
"AAAAAAA///////+gCf/////////xAAAAAAAAAAAAAAAAAAAN///////RAJ//////////EAAAAAAAAAAAAAAAAAAI///////0AAn/////////8QAAAAAAAAAA"
"AAAAAAAE///////5AACf/////////xAAAAAAAAAAAAAAAAAB3//////9EAAJ//////////EAAAAAAAAAAAAAAAAAn///////MAAAn/////////8QAAAAAAAA"
"AAAAAAAAT///////gAAACf/////////xAAAAAAAAAAAAAAAAHf//////wAAAAJ//////////EAAAAAAAAAAAAAAACf//////8wAAAAn/////////8QAAAAAA"
"AAAAAAAABP//////9wAAAACf/////////xAAAAAAAAAAAAAAAe///////AAAAAAJ//////////EAAAAAAAAAAAAAAK///////yAAAAAAn/////////8QAAAA"
"AAAAAAAAAF///////3AAAAAACf/////////xAAAAAAAAAAAAAB7//////7AAAAAAAJ//////////EAAAAAAAAAAAAAr//////+IAAAAAAAn/////////8QAA"
"AAAAAAAAAAX///////YAAAAAAACf/////////xAAAAAAAAAAAAHv//////sAAAAAAAAJ//////////EAAAAAAAAAAAC///////4QAAAAAAAAn/////////8Q"
"AAAAAAAAAABv//////9QAAAAAAAACf/////////xAAAAAAAAAAAu//////+gAAAAAAAAAJ//////////EAAAAAAAAAAL///////hAAAAAAAAAAn/////////"
"8QAAAAAAAAAB///////0AAAAAAAAAACf/////////xAAAAAAAAAAH//////5AAAAAAAAAAAJ//////////EAAAAAAAAAAf//////////////////////////"
"////////8wAAAB///////////////////////////////////zAAAAH///////////////////////////////////MAAAAf////////////////////////"
"//////////8wAAAB///////////////////////////////////zAAAAH///////////////////////////////////MAAAAf//////////////////////"
"////////////8wAAAB///////////////////////////////////zAAAAH///////////////////////////////////MAAAAf////////////////////"
"//////////////8wAAAB///////////////////////////////////zAAAAH///////////////////////////////////MAAAAAAAAAAAAAAAAAAAAAAA"
"n/////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//////////EAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAn/////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//////////EAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAn/////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//////////EAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAn/////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//////////EAAAAAAAAAAAAACv//////"
"////////////////////cAAAAAAAAAAAAK//////////////////////////9wAAAAAAAAAAAAr//////////////////////////3AAAAAAAAAAAACv////"
"//////////////////////cAAAAAAAAAAAAK//////////////////////////9wAAAAAAAAAAAAr//////////////////////////3AAAAAAAAAAAACv//"
"////////////////////////cAAAAAAAAAAAAK//////////////////////////9wAAAAAAAAAAAAr//////////////////////////3AAAAAAAAAAAACv"
"//////////////////////////cAAAAAAAAAAAAK//////////////////////////9wAAAAAAAAAAAAr//////////////////////////3AAAAAAAAAAAA"
"Cv///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAr///////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AACv///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAr///////+AAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAACv///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAr///////+AAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAACv///////4JYve/+7cqFIAAAAAAAAAAAAAAAAAAAAK///////////////////9lAAAAAAAAAAAAAAAAAAAr/////////////////////1xAAAAAAAA"
"AAAAAAAACv//////////////////////5gAAAAAAAAAAAAAAAK////////////////////////sgAAAAAAAAAAAAAAr////////////////////////+QAAA"
"AAAAAAAAAACv/////////////////////////0AAAAAAAAAAAAAK//////////////////////////9AAAAAAAAAAAAAr//////////////////////////+"
"IAAAAAAAAAAACv//////////////////////////+wAAAAAAAAAAAK////////////////////////////UAAAAAAAAAAAr/////24UyEBI2rv//////////"
"///QAAAAAAAAAACv//6mIAAAAAAAAAbf////////////UAAAAAAAAAAK/7UQAAAAAAAAAAAAj///////////+wAAAAAAAAAAmCAAAAAAAAAAAAAAAG//////"
"//////EAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////9QAAAAAAAAAAAAAAAAAAAAAAAAAAAA3//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAABf//"
"////////sAAAAAAAAAAAAAAAAAAAAAAAAAAAAB7//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAC///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ"
"//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAj//////////xAAAAAAAAAAAAAAAAAAAAAAAAAAAACP//////////EAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AJ//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAv//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////9AAAAAAAAAAAAAAAAAAAAAAAAAA"
"AABf//////////sAAAAAAAA5IAAAAAAAAAAAAAAAAAAN//////////9wAAAAAAAD/oEAAAAAAAAAAAAAAAAI///////////0AAAAAAAAP//pIAAAAAAAAAAA"
"AAAG///////////+AAAAAAAAA////7QAAAAAAAAAAAAZ////////////kAAAAAAAAD/////+lBAAAAAAAABt////////////8wAAAAAAAAP///////+4UyEB"
"I2rv////////////+gAAAAAAAAA//////////////////////////////iAAAAAAAAAD/////////////////////////////2AAAAAAAAAAP///////////"
"/////////////////6AAAAAAAAAAA////////////////////////////7AAAAAAAAAAAD///////////////////////////6AAAAAAAAAAAAP/////////"
"/////////////////4AAAAAAAAAAAAA//////////////////////////UAAAAAAAAAAAAAASe//////////////////////5wAAAAAAAAAAAAAAAABJ3///"
"///////////////9cQAAAAAAAAAAAAAAAAAAACac//////////////yDAAAAAAAAAAAAAAAAAAAAAAAAACV5vN3v/+3LlkEAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAlis3u/u3Ll1IAAAAAAAAAAAAAAAAAAAAAAAAAAEnf///////////+pzAAAAAAAAAAAAAAAAAAAAAAGO/////////////////ZQAAAAAAAAAAAAA"
"AAAAABjv///////////////////0AAAAAAAAAAAAAAAAAF3/////////////////////QAAAAAAAAAAAAAAAAK//////////////////////9AAAAAAAAAAA"
"AAAAAs///////////////////////0AAAAAAAAAAAAAAAt////////////////////////QAAAAAAAAAAAAAAt////////////////////////9AAAAAAAAA"
"AAAAAd/////////////////////////0AAAAAAAAAAAAAK//////////////////////////QAAAAAAAAAAAAH/////////////ZYyEBI1i+////9AAAAAAA"
"AAAAAC////////////owAAAAAAAABJ7//0AAAAAAAAAAAAv//////////8IAAAAAAAAAAAAEv/QAAAAAAAAAAAX//////////4AAAAAAAAAAAAAAAClAAAAA"
"AAAAAADP/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAABP/////////6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAL/////////+EAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAB//////////YAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAC/////////+AAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAf/////////zAAAAAAAAAAAAAAAAAAAAAAAAAAAAAE/////////9AAAAN6zu/u25YgAAAAAAAAAAAAAAAAj/////////oAA57/////////2CAAAA"
"AAAAAAAAAAC/////////+AO/////////////+iAAAAAAAAAAAAAN/////////2j///////////////+AAAAAAAAAAAAB//////////7/////////////////"
"wgAAAAAAAAAAL////////////////////////////+MAAAAAAAAABP/////////////////////////////jAAAAAAAAAG//////////////////////////"
"////4QAAAAAAAAf//////////////////////////////7AAAAAAAAB///////////////////////////////9wAAAAAAAI////////////////////////"
"///////+EAAAAAAAj//////////////oQgElr///////////+AAAAAAACP////////////+RAAAAADz//////////+AAAAAAAI////////////+QAAAAAAAc"
"//////////9QAAAAAAf////////////QAAAAAAAAP//////////6AAAAAAB////////////1AAAAAAAAAJ//////////0AAAAAAF///////////+AAAAAAAA"
"AAP//////////xAAAAAAT///////////oAAAAAAAAAAO//////////QAAAAAA///////////9wAAAAAAAAAAv/////////9QAAAAAB///////////0AAAAAA"
"AAAACf/////////2AAAAAADf//////////MAAAAAAAAAAI//////////cAAAAAAL//////////8wAAAAAAAAAAf/////////9wAAAAAAj//////////zAAAA"
"AAAAAAB//////////3AAAAAABf//////////MAAAAAAAAAAI//////////YAAAAAAB//////////9AAAAAAAAAAAn/////////9AAAAAAADP/////////3AA"
"AAAAAAAAC//////////yAAAAAAAH//////////oAAAAAAAAAAO/////////+AAAAAAAAL//////////gAAAAAAAAAD//////////sAAAAAAAAM//////////"
"UAAAAAAAAAn/////////9wAAAAAAAAX//////////QAAAAAAAAP//////////yAAAAAAAAAN//////////kAAAAAAAHP/////////7AAAAAAAAAAb///////"
"///5EAAAAAPP//////////UAAAAAAAAAAM///////////oQgElr///////////wAAAAAAAAAAAT///////////////////////////8wAAAAAAAAAAAI////"
"//////////////////////+AAAAAAAAAAAAAC//////////////////////////AAAAAAAAAAAAAAB3////////////////////////RAAAAAAAAAAAAAAAt"
"///////////////////////SAAAAAAAAAAAAAAAAHP////////////////////+xAAAAAAAAAAAAAAAAAAn///////////////////+AAAAAAAAAAAAAAAAA"
"AAAE3/////////////////wwAAAAAAAAAAAAAAAAAAAAAG3//////////////8UAAAAAAAAAAAAAAAAAAAAAAAAEnv//////////2DAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAANpve7/7cqFIAAAAAAAAAAAAAAAAAL///////////////////////////////9AAAAAAAAv///////////////////////////////0AAAAAAAC"
"////////////////////////////////QAAAAAAAL///////////////////////////////9AAAAAAAAv///////////////////////////////0AAAAAA"
"AC////////////////////////////////QAAAAAAAL///////////////////////////////9AAAAAAAAv///////////////////////////////0AAAA"
"AAAC////////////////////////////////QAAAAAAAL///////////////////////////////8gAAAAAAAv//////////////////////////////+gAA"
"AAAAAC///////////////////////////////zAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAN//////////UA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAF//////////0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAz/////////9gAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////g"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////3AAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////+EAAAAAAAAAAAAAAAAAAAAAAAAAAAAK//////////"
"kAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////8gAAAAAAAAAAAAAAAAAAAAAAAAAAAAj/////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv////////"
"/zAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAN//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAG////////"
"//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz/////////9QAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAC///////"
"///3AAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////+EAAAAAAAAAAAAAAAAAAAAAAAAAAAAK//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////"
"////8gAAAAAAAAAAAAAAAAAAAAAAAAAAAAj/////////+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv/////////zAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////"
"/////7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAN//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAG//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz///"
"//////9QAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////2AAAAAAAAAAAAAAAAAAAAAAAAAAAAA///"
"///////+EAAAAAAAAAAAAAAAAAAAAAAAAAAAAK//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAAj/"
"////////+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv/////////yAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAO"
"//////////MAAAAAAAAAAAAAAAAAAAAAAAAAAAAG//////////sAAAAAAAAAAAAAAAAAAAAAAAAAAAAAz/////////9QAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"T//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////2AAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AK//////////cAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////4QAAAAAAAAAAAAAAAAAAAAAAAAAAAAn/////////+AAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAHv/////////yAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAO//////////MAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAG//////////sAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/////////9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////AAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAC//////////1AAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAK//////////cAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAACWKvO7//u3KhjAAAAAAAAAAAAAAAAAAAAAAAAABau/////////////8cgAAAAAAAAAAAAAAAAAAAABK//////////////////xQAAAAAAAAAA"
"AAAAAAAAK/////////////////////1AAAAAAAAAAAAAAAAAf///////////////////////kAAAAAAAAAAAAAAAr////////////////////////8EAAAAA"
"AAAAAAAAr//////////////////////////BAAAAAAAAAAAAf///////////////////////////oAAAAAAAAAAAL////////////////////////////1AA"
"AAAAAAAACv////////////////////////////0AAAAAAAAAAv/////////////////////////////1AAAAAAAAAH////////////xjEBJa////////////"
"oAAAAAAAAAv//////////+QAAAAAA8///////////gAAAAAAAADv/////////+IAAAAAAAHf//////////IAAAAAAAAf//////////YAAAAAAAAD////////"
"//9AAAAAAAAC//////////4AAAAAAAAAC//////////1AAAAAAAAP/////////+gAAAAAAAAAH//////////YAAAAAAAAv/////////4AAAAAAAAAAX/////"
"////9QAAAAAAAB//////////cAAAAAAAAABf/////////0AAAAAAAADv////////+AAAAAAAAAAF//////////IAAAAAAAAL/////////6AAAAAAAAAAj///"
"//////4AAAAAAAAAf/////////4AAAAAAAAADP////////+gAAAAAAAAAv/////////2AAAAAAAAA//////////0AAAAAAAAAAr/////////4gAAAAAAAd//"
"///////9AAAAAAAAAAAu/////////+QAAAAAA9//////////QAAAAAAAAAAAb//////////8YxASWv//////////kAAAAAAAAAAAAI//////////////////"
"////////oAAAAAAAAAAAAACP////////////////////////oAAAAAAAAAAAAAAATv/////////////////////+YAAAAAAAAAAAAAAAABjv////////////"
"///////5IAAAAAAAAAAAAAAAAAABfP////////////////2CAAAAAAAAAAAAAAAAAAAAAn3///////////////5yAAAAAAAAAAAAAAAAAAAAS///////////"
"/////////FAAAAAAAAAAAAAAAAAEz//////////////////////VAAAAAAAAAAAAAAAI////////////////////////+RAAAAAAAAAAAAAb////////////"
"//////////////0gAAAAAAAAAAAc///////////////////////////9IAAAAAAAAAAK///////////5YhASWO///////////AAAAAAAAAAF//////////+R"
"AAAAAAB///////////cAAAAAAAAA7/////////9gAAAAAAAAPv/////////xAAAAAAAAb/////////+AAAAAAAAAAF//////////gAAAAAAADP/////////h"
"AAAAAAAAAADP/////////gAAAAAAAf/////////4AAAAAAAAAAAG//////////MAAAAAAE//////////QAAAAAAAAAAAL/////////9gAAAAAAf/////////"
"8gAAAAAAAAAAAP/////////5AAAAAACP/////////xAAAAAAAAAAAA7/////////oAAAAAAJ//////////EAAAAAAAAAAADf////////+wAAAAAAn///////"
"//8gAAAAAAAAAAAP/////////7AAAAAACP/////////0AAAAAAAAAAAC//////////sAAAAAAH//////////gAAAAAAAAAAAb/////////+gAAAAAAX/////"
"/////hAAAAAAAAAADP/////////4AAAAAAA///////////gAAAAAAAAABf//////////UAAAAAAA7//////////2AAAAAAAAA+//////////8gAAAAAACv//"
"////////+RAAAAAAB////////////QAAAAAAAF////////////6VIQEljv///////////3AAAAAAAADf//////////////////////////////EAAAAAAAAG"
"//////////////////////////////gAAAAAAAAAC/////////////////////////////0QAAAAAAAAAC7///////////////////////////8wAAAAAAAA"
"AAA+//////////////////////////9QAAAAAAAAAAAAPf////////////////////////5QAAAAAAAAAAAAABv///////////////////////wwAAAAAAAA"
"AAAAAAAF3////////////////////+cAAAAAAAAAAAAAAAAAAGz//////////////////XEAAAAAAAAAAAAAAAAAAAACe+/////////////8gwAAAAAAAAAA"
"AAAAAAAAAAAAAAA2ir3u//7tyoZBAAAAAAAAAAAAAAAAAAAAAAAAAAACWKze/+7bliAAAAAAAAAAAAAAAAAAAAAAAAAAAAKM///////////pQAAAAAAAAAAA"
"AAAAAAAAAAAAAEv//////////////9UAAAAAAAAAAAAAAAAAAAAAA7/////////////////9QAAAAAAAAAAAAAAAAAAAB////////////////////4AAAAAA"
"AAAAAAAAAAAAG/////////////////////+xAAAAAAAAAAAAAAAAHf//////////////////////0gAAAAAAAAAAAAAAHP///////////////////////8EA"
"AAAAAAAAAAAAC//////////////////////////AAAAAAAAAAAAACP//////////////////////////gAAAAAAAAAAAA///////////////////////////"
"/0AAAAAAAAAAAL///////////6YhAkjv//////////0AAAAAAAAAAE///////////TAAAAABn//////////2AAAAAAAAAAv//////////SAAAAAAAI//////"
"////4AAAAAAAAAH//////////0AAAAAAAADP/////////2AAAAAAAABv/////////6AAAAAAAAAE//////////wAAAAAAAAK//////////UAAAAAAAAADf//"
"///////zAAAAAAAA3/////////8AAAAAAAAAAI//////////gAAAAAAAH//////////AAAAAAAAAAAb//////////QAAAAAAA//////////6AAAAAAAAAAA/"
"//////////IAAAAAAF//////////kAAAAAAAAAAC//////////9QAAAAAAb/////////+AAAAAAAAAAAH//////////5AAAAAABv/////////4AAAAAAAAAA"
"Af//////////wAAAAAAG//////////kAAAAAAAAAAC///////////gAAAAAAb/////////+gAAAAAAAAAAP///////////IAAAAABf/////////8AAAAAAAA"
"AABv//////////8wAAAAAD//////////8AAAAAAAAAAI///////////1AAAAAAH//////////0AAAAAAAAAA3///////////YAAAAAAN//////////oAAAAA"
"AAAAP///////////9wAAAAAAn//////////zAAAAAAAADP///////////4AAAAAABP//////////0QAAAAAACP////////////gAAAAAAA7//////////9MA"
"AAAAGf////////////+QAAAAAAB////////////6YhAkjv/////////////5AAAAAAAB7///////////////////////////////gAAAAAAABv//////////"
"////////////////////+AAAAAAAAAv//////////////////////////////3AAAAAAAAAd//////////////////////////////YAAAAAAAAALv//////"
"//////////////////////9QAAAAAAAAAD3////////////////////////////zAAAAAAAAAAAs/////////////////9//////////IAAAAAAAAAAACP//"
"/////////////4X/////////4AAAAAAAAAAAAAKv////////////+iB/////////+wAAAAAAAAAAAAAAKN/////////+kwAJ/////////5AAAAAAAAAAAAAA"
"AAAmm97//spzAAAAz/////////UAAAAAAAAAAAAAAAAAAAAAAAAAAAAAL/////////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////AAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAM/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAF//////////IAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/////////sAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAn/////////9QAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////QAAAAAAAAAAA6QAAAAAAAAAAAAAAAf//////////1AAAAAAAAAA"
"AD/8UAAAAAAAAAAAACv//////////8AAAAAAAAAAAAP//+pAAAAAAAAAAp////////////MAAAAAAAAAAAA/////64UyEBI1nf////////////gAAAAAAAAA"
"AAAD//////////////////////////sAAAAAAAAAAAAAP/////////////////////////0QAAAAAAAAAAAAA/////////////////////////4gAAAAAAAA"
"AAAAAD////////////////////////4gAAAAAAAAAAAAAAP///////////////////////wgAAAAAAAAAAAAAAA///////////////////////oQAAAAAAAA"
"AAAAAAAD/////////////////////+UAAAAAAAAAAAAAAAAAP////////////////////pEAAAAAAAAAAAAAAAAAADjf////////////////6BAAAAAAAAAA"
"AAAAAAAAAAAAN77////////////ZQAAAAAAAAAAAAAAAAAAAAAAAAAACV5vN7v7tyoUgAAAAAAAAAAAAAAAAAAAAAAAAAAAUaKzd7/7tuXQQAAAAAAAAAAAA"
"AAAAAANp3////////////8cgAAAAAAAAAAAAACau/////////////////7MAAAAAAAAAAAAO////////////////////+hAAAAAAAAAAAO//////////////"
"///////+MAAAAAAAAAAO//////////////////////5AAAAAAAAAAO///////////////////////jAAAAAAAAAO///////////////////////9AAAAAAAA"
"AO////////////////////////cAAAAAAAAO////////////////////////4QAAAAAAAO////////////////////////9QAAAAAAAO//////2WMQAUjf//"
"////////+gAAAAAAAO////6DAAAAAAAI///////////gAAAAAAAO///FAAAAAAAAAAf//////////xAAAAAAAO/9UAAAAAAAAAAADP/////////zAAAAAAAO"
"5wAAAAAAAAAAAAB//////////0AAAAAAAKIAAAAAAAAAAAAABP/////////1AAAAAAAAAAAAAAAAAAAAAAA//////////0AAAAAAAAAAAAAAAAAAAAAABP//"
"///////zAAAAAAAAAAAAAAAAAAAAAAB//////////xAAAAAAAAAAAAAAAAAAAAAADf/////////QAAAAAAAAAAAAAAAAAAAAAAb/////////+QAAAAAAAAAA"
"AAAAAAAAAAAC7/////////9QAAAAAAAAAAAAAAAAAAAAAc//////////0AAAAAAAAAAAAAAAAAAAAAC///////////YAAAAAAAAAAAAAAAAAAAABv///////"
"///8AAAAAAAAAAAAAAAAAAAAAc///////////iAAAAAAAAAAAAAAAAAAAALf//////////9QAAAAAAAAAAAAAAAAAAAD7///////////cAAAAAAAAAAAAAAA"
"AAAAA+///////////4AAAAAAAAAAAAAAAAAAAAPv//////////+AAAAAAAAAAAAAAAAAAAAD7///////////cAAAAAAAAAAAAAAAAAAAAd///////////1AA"
"AAAAAAAAAAAAAAAAAAC///////////5AAAAAAAAAAAAAAAAAAAAAb//////////+MAAAAAAAAAAAAAAAAAAAAA7//////////jAAAAAAAAAAAAAAAAAAAAAF"
"//////////8wAAAAAAAAAAAAAAAAAAAAAJ//////////cAAAAAAAAAAAAAAAAAAAAAAN/////////+EAAAAAAAAAAAAAAAAAAAAAAP/////////6AAAAAAAA"
"AAAAAAAAAAAAAAAP/////////4AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf////"
"/////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAA"
"AAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf//////"
"///3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAA"
"AAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAAAAAAAf/////////3AAAAAAAAAAAAAAAAAADv////////////"
"////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////"
"////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////"
"////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////"
"////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv////////////////////////////sAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv////////////"
"///////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv////////////"
"///////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv////////////"
"///////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv///////////////////////////xAAAAAAAAAADv////////////"
"///////////////xAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AAAAAAAAAAAAAAAAAAAAAAAAAAAADv/////////5AA"
"AAAAAAAAAAAAAAAAAAAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////"
"////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////"
"////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////"
"////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////////////////////+gAAAAAAAADv////////////"
"////////////////+gAAAAAAAADv///////////AAAAAAAAAAAAAAAL/////////+QAAAAAAAAAA7///////////9QAAAAAAAAAAAAAC//////////kAAAAA"
"AAAAAO////////////0AAAAAAAAAAAAAAv/////////5AAAAAAAAAADv////////////YAAAAAAAAAAAAAL/////////+QAAAAAAAAAA7////////////+EA"
"AAAAAAAAAAAC//////////kAAAAAAAAAAO/////////////3AAAAAAAAAAAAAv/////////5AAAAAAAAAADv/////////////hAAAAAAAAAAAAL/////////"
"+QAAAAAAAAAA7/////////////+AAAAAAAAAAAAC//////////kAAAAAAAAAAO//////////////8gAAAAAAAAAAAv/////////5AAAAAAAAAADv////////"
"//////kAAAAAAAAAAAL/////////+QAAAAAAAAAA7///////////////IAAAAAAAAAAC//////////kAAAAAAAAAAO///////////////6AAAAAAAAAAAv//"
"///////5AAAAAAAAAADv///////////////zAAAAAAAAAAL/////////+QAAAAAAAAAA7///////////////+wAAAAAAAAAC//////////kAAAAAAAAAAO//"
"//////////////9AAAAAAAAAAv/////////5AAAAAAAAAADv////////////////wAAAAAAAAAL/////////+QAAAAAAAAAA7/////////////////UAAAAA"
"AAAC//////////kAAAAAAAAAAO/////////////////9AAAAAAAAAv/////////5AAAAAAAAAADv/////////////////2AAAAAAAAL/////////+QAAAAAA"
"AAAA7//////////////////QAAAAAAAC//////////kAAAAAAAAAAO/////////97///////9wAAAAAAAv/////////5AAAAAAAAAADv/////////H//////"
"//4QAAAAAAL/////////+QAAAAAAAAAA7/////////we////////gAAAAAAC//////////kAAAAAAAAAAO/////////8B////////+EAAAAAAv/////////5"
"AAAAAAAAAADv/////////ADf///////5AAAAAAL/////////+QAAAAAAAAAA7/////////wAb////////yAAAAAC//////////kAAAAAAAAAAO/////////8"
"AAz///////+gAAAAAv/////////5AAAAAAAAAADv/////////AAF////////8wAAAAL/////////+QAAAAAAAAAA7/////////wAAM////////sAAAAC////"
"//////kAAAAAAAAAAO/////////8AABP////////QAAAAv/////////5AAAAAAAAAADv/////////AAAC////////8AAAAL/////////+QAAAAAAAAAA7///"
"//////wAAAP////////1AAAC//////////kAAAAAAAAAAO/////////8AAAAr////////AAAAv/////////5AAAAAAAAAADv/////////AAAAC////////9g"
"AAL/////////+QAAAAAAAAAA7/////////wAAAAJ////////0AAC//////////kAAAAAAAAAAO/////////8AAAAAe////////YAAv/////////5AAAAAAAA"
"AADv/////////AAAAACP///////+EAL/////////+QAAAAAAAAAA7/////////wAAAAAHv///////3AC//////////kAAAAAAAAAAO/////////8AAAAAAf/"
"///////hAv/////////5AAAAAAAAAADv/////////AAAAAAB3///////+AL/////////+QAAAAAAAAAA7/////////wAAAAAAG////////8i//////////kA"
"AAAAAAAAAO/////////8AAAAAAAN////////kv/////////5AAAAAAAAAADv/////////AAAAAAABf////////T/////////+QAAAAAAAAAA7/////////wA"
"AAAAAADP///////8//////////kAAAAAAAAAAO/////////8AAAAAAAAT//////////////////5AAAAAAAAAADv/////////AAAAAAAAAv/////////////"
"////+QAAAAAAAAAA7/////////wAAAAAAAAD//////////////////kAAAAAAAAAAO/////////8AAAAAAAAAK/////////////////5AAAAAAAAAADv////"
"/////AAAAAAAAAAv////////////////+QAAAAAAAAAA7/////////wAAAAAAAAACf////////////////kAAAAAAAAAAO/////////8AAAAAAAAAAL/////"
"///////////5AAAAAAAAAADv/////////AAAAAAAAAAAj///////////////+QAAAAAAAAAA7/////////wAAAAAAAAAAB7///////////////kAAAAAAAAA"
"AO/////////8AAAAAAAAAAAH///////////////5AAAAAAAAAADv/////////AAAAAAAAAAAAe//////////////+QAAAAAAAAAA7/////////wAAAAAAAAA"
"AABv//////////////kAAAAAAAAAAO/////////8AAAAAAAAAAAADf/////////////5AAAAAAAAAADv/////////AAAAAAAAAAAAAX/////////////+QAA"
"AAAAAAAA7/////////wAAAAAAAAAAAAAz/////////////kAAAAAAAAAAO/////////8AAAAAAAAAAAAAF/////////////5AAAAAAAAAADv/////////AAA"
"AAAAAAAAAAAM////////////+QAAAAAAAAAA7/////////wAAAAAAAAAAAAABP////////////kAAAAAAAAAAO/////////8AAAAAAAAAAAAAAC/////////"
"///5AAAAAAAAAADv/////////AAAAAAAAAAAAAAAP///////////+QAAAAAAAAAAAAAAAAAAAVebzu/+7dy5dkIAAAAAAAAAAAAAAAAAAAAAAAAAA43/////"
"/////////sl0EAAAAAAAAAAAAAAAAAAAAG3////////////////////JUQAAAAAAAAAAAAAAAAXf///////////////////////6AAAAAAAAAAAAAAAa////"
"/////////////////////7AAAAAAAAAAAAAALf/////////////////////////7AAAAAAAAAAAAAC3//////////////////////////7AAAAAAAAAAAAAc"
"///////////////////////////7AAAAAAAAAAAACf///////////////////////////7AAAAAAAAAAAAT////////////////////////////7AAAAAAAA"
"AAAAz////////////////////////////7AAAAAAAAAAAD/////////////////////////////7AAAAAAAAAAAJ///////////+t1MRABI1et///////7AA"
"AAAAAAAAAO//////////5xAAAAAAAAAAFJ3////7AAAAAAAAAAAv/////////9IAAAAAAAAAAAAAAnz//7AAAAAAAAAABf/////////zAAAAAAAAAAAAAAAA"
"A577AAAAAAAAAAB/////////+wAAAAAAAAAAAAAAAAAAF5AAAAAAAAAACf////////9wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACv////////9QAAAAAAAAAA"
"AAAAAAAAAAAAAAAAAAAACv////////9gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACv////////+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACf/////////zAAAA"
"AAAAAAAAAAAAAAAAAAAAAAAAAAB//////////9MAAAAAAAAAAAAAAAAAAAAAAAAAAAAABf//////////+TAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv////////"
"////2EEAAAAAAAAAAAAAAAAAAAAAAAAAAN///////////////adBAAAAAAAAAAAAAAAAAAAAAAAH//////////////////2nQQAAAAAAAAAAAAAAAAAAAB//"
"///////////////////8hAAAAAAAAAAAAAAAAAAAj//////////////////////+kwAAAAAAAAAAAAAAAAHf///////////////////////8UAAAAAAAAAAA"
"AAAAA+/////////////////////////EAAAAAAAAAAAAAAAE7/////////////////////////kQAAAAAAAAAAAAAAPv/////////////////////////CAA"
"AAAAAAAAAAAAAb/////////////////////////9EAAAAAAAAAAAAAAAXf////////////////////////wAAAAAAAAAAAAAAAAFz///////////////////"
"////9wAAAAAAAAAAAAAAAAA43//////////////////////hAAAAAAAAAAAAAAAAAAA3rv///////////////////4AAAAAAAAAAAAAAAAAAAAACWc//////"
"///////////+AAAAAAAAAAAAAAAAAAAAAAAAA2rv//////////////MAAAAAAAAAAAAAAAAAAAAAAAAAADjv////////////cAAAAAAAAAAAAAAAAAAAAAAA"
"AAAAAG7///////////oAAAAAAAAAAAAAAAAAAAAAAAAAAAAAG///////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAe//////////0AAAAAAAAAAAAAAAAA"
"AAAAAAAAAAAAAH//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////0AAAAAAAAqIA"
"AAAAAAAAAAAAAAAAAAAB//////////0AAAAAAAAv+SAAAAAAAAAAAAAAAAAAAD//////////sAAAAAAAAv//kgAAAAAAAAAAAAAAAAAI//////////kAAAAA"
"AAAv///7QAAAAAAAAAAAAAAAAu//////////cAAAAAAAAv/////YMAAAAAAAAAAAAAPf//////////QAAAAAAAAv///////YQQAAAAAAAAAY7//////////+"
"EAAAAAAAAv/////////8llMRABJHv////////////6AAAAAAAAAv///////////////////////////////1AAAAAAAAAv//////////////////////////"
"/////QAAAAAAAAAv//////////////////////////////9QAAAAAAAAAv//////////////////////////////oAAAAAAAAAAv////////////////////"
"/////////9EAAAAAAAAAAv/////////////////////////////jAAAAAAAAAAAv////////////////////////////0gAAAAAAAAAAAZ7/////////////"
"/////////////6EAAAAAAAAAAAAABa7///////////////////////1QAAAAAAAAAAAAAAAABIz////////////////////FAAAAAAAAAAAAAAAAAAAAAUe+"
"//////////////63IAAAAAAAAAAAAAAAAAAAAAAAAAE2ibze7//u26hjAAAAAAAAAAAAAACP//////////////////////////////////////iP////////"
"//////////////////////////////iP//////////////////////////////////////iP//////////////////////////////////////iP////////"
"//////////////////////////////iP//////////////////////////////////////iP//////////////////////////////////////iP////////"
"//////////////////////////////iP//////////////////////////////////////iP//////////////////////////////////////iP////////"
"//////////////////////////////iP//////////////////////////////////////gAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAA"
"AAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////QAAAAAAAAAAAAAA=";

static uint32_t g_hr[HR_W * HR_H];         /* cuadro del menu */
static uint32_t g_bg[HR_W * HR_H];         /* fondo mosaico (se arma una vez) */
static uint8_t  g_fgd[FG_NDATA];           /* alfa de 4 bits de las letras, ya decodificado */
static int      g_hr_on;                   /* 1 = el cuadro que se esta armando es de 1280x720 */
static int      g_hr_ready;
static int      hr_usable(void);           /* definida junto al video (PS3 y PC) */

static void hr_b64(void)
{
    static signed char T[256];
    const char *p = fg_b64;
    uint32_t acc = 0;
    int bits = 0, i;
    size_t n = 0;
    for (i = 0; i < 256; i++) T[i] = -1;
    for (i = 0; i < 26; i++) { T['A' + i] = (signed char)i; T['a' + i] = (signed char)(26 + i); }
    for (i = 0; i < 10; i++) T['0' + i] = (signed char)(52 + i);
    T['+'] = 62; T['/'] = 63;
    for (; *p && n < FG_NDATA; p++) {
        if (T[(unsigned char)*p] < 0) continue;
        acc = (acc << 6) | (uint32_t)T[(unsigned char)*p];
        bits += 6;
        if (bits >= 8) { bits -= 8; g_fgd[n++] = (uint8_t)(acc >> bits); }
    }
}

static void hr_make_bg(void)
{
    static const uint8_t sh[4][3] = { {11, 20, 54}, {13, 24, 62}, {10, 18, 48}, {15, 28, 72} };
    uint32_t rs = 12345u;
    int tx, ty, x, y;
    for (ty = 0; ty < HR_H; ty += 32)
        for (tx = 0; tx < HR_W; tx += 32) {
            const uint8_t *c;
            int det;
            rs = rs * 1103515245u + 12345u;
            c = sh[(rs >> 16) & 3];
            det = ((rs >> 20) & 0xFF) < 56;
            for (y = 0; y < 32 && ty + y < HR_H; y++)
                for (x = 0; x < 32; x++) {
                    int r = c[0], g = c[1], b = c[2];
                    if (y < 2 || x < 2) { r = 24; g = 42; b = 100; }
                    if (y >= 30 || x >= 30) { r = 5; g = 10; b = 28; }
                    else if (det && x >= 12 && x < 20 && y >= 12 && y < 20) { r += 14; g += 14; b += 14; }
                    g_bg[(ty + y) * HR_W + tx + x] = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)b;
                }
        }
    /* vineta suave: oscurece hacia los bordes (aprox. sin raiz: d2 = dx^2 + dy^2, t = d2 acotado) */
    for (y = 0; y < HR_H; y++) {
        int dy = (y - 360) * 100 / 360;
        for (x = 0; x < HR_W; x++) {
            int dx = (x - 640) * 100 / 640;
            int d2 = dx * dx + dy * dy;                 /* 0 .. 20000 */
            int w = d2 > 10000 ? 10000 : d2;            /* 0..10000, cuadratica: centro claro */
            int f = w * 40 / 10000 * 256 / 100;         /* peso del color oscuro 0..~217 */
            uint32_t p = g_bg[y * HR_W + x];
            int r = (int)((p >> 16) & 255), g = (int)((p >> 8) & 255), b = (int)(p & 255);
            r = (r * (256 - f) + 2 * f) >> 8; g = (g * (256 - f) + 4 * f) >> 8; b = (b * (256 - f) + 14 * f) >> 8;
            g_bg[y * HR_W + x] = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)b;
        }
    }
}

static void hr_rect(int x0, int y0, int x1, int y1, uint32_t col, int alpha)   /* x1,y1 exclusivos; alpha 0..256 */
{
    int x, y;
    int cr = (int)((col >> 16) & 255), cg = (int)((col >> 8) & 255), cb = (int)(col & 255);
    if (x0 < 0) x0 = 0;
    if (y0 < 0) y0 = 0;
    if (x1 > HR_W) x1 = HR_W;
    if (y1 > HR_H) y1 = HR_H;
    for (y = y0; y < y1; y++)
        for (x = x0; x < x1; x++) {
            uint32_t *d = &g_hr[y * HR_W + x];
            if (alpha >= 256) { *d = 0xFF000000u | (col & 0xFFFFFF); continue; }
            {
                int r = (int)((*d >> 16) & 255), g = (int)((*d >> 8) & 255), b = (int)(*d & 255);
                r = (r * (256 - alpha) + cr * alpha) >> 8; g = (g * (256 - alpha) + cg * alpha) >> 8; b = (b * (256 - alpha) + cb * alpha) >> 8;
                *d = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)b;
            }
        }
}

static void hr_frame_rect(int x0, int y0, int x1, int y1, int t, uint32_t col)
{
    hr_rect(x0, y0, x1, y0 + t, col, 256); hr_rect(x0, y1 - t, x1, y1, col, 256);
    hr_rect(x0, y0, x0 + t, y1, col, 256); hr_rect(x1 - t, y0, x1, y1, col, 256);
}

static void hr_panel(int x0, int y0, int x1, int y1)
{
    hr_rect(x0, y0, x1, y1, 0xFF040818u, 200);
    hr_frame_rect(x0, y0, x1, y1, 3, HC_GRID);
    hr_frame_rect(x0 + 6, y0 + 6, x1 - 6, y1 - 6, 1, 0xFF182C6Eu);
}

static void hr_init(void)
{
    if (g_hr_ready) return;
    hr_b64();
    hr_make_bg();
    g_hr_ready = 1;
}

static void hr_begin(void)
{
    hr_init();
    memcpy(g_hr, g_bg, sizeof g_hr);
    g_hr_on = 1;
}

static const FGlyph *hr_glyph(int sz, int cp)
{
    int lo = fg_start[sz], hi = fg_start[sz + 1] - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (fg_tab[mid].cp == cp) return &fg_tab[mid];
        if (fg_tab[mid].cp < cp) lo = mid + 1; else hi = mid - 1;
    }
    return NULL;
}

/* siguiente caracter UTF-8 (solo 1 y 2 bytes: ASCII y Latin-1: acentos, n con tilde, signos de apertura) */
static int hr_next(int sz, const char **ps)
{
    const unsigned char *p = (const unsigned char *)*ps;
    int c = *p++;
    if (c >= 0xC2 && c <= 0xC3 && (*p & 0xC0) == 0x80) { c = ((c & 0x1F) << 6) | (*p & 0x3F); p++; }
    else if (c >= 0x80) c = '?';
    if (c < 32 || (c > 126 && c < 0xA0)) c = '?';
    if ((sz == FS_H || sz == FS_X) && c >= 'a' && c <= 'z') c -= 32;
    *ps = (const char *)p;
    return c;
}

static int hr_tw(const char *s, int sz)
{
    int w = 0;
    while (*s) {
        const FGlyph *g = hr_glyph(sz, hr_next(sz, &s));
        w += g ? g->adv : fg_asc[sz] / 3;
    }
    return w;
}

static void hr_glyph_draw(int x, int base, const FGlyph *g, uint32_t col)
{
    int gx, gy, cr = (int)((col >> 16) & 255), cg = (int)((col >> 8) & 255), cb = (int)(col & 255);
    if (!g || !g->w) return;
    for (gy = 0; gy < g->h; gy++) {
        int py = base + g->by + gy;
        if (py < 0 || py >= HR_H) continue;
        for (gx = 0; gx < g->w; gx++) {
            int px = x + g->bx + gx, idx = gy * g->w + gx, a;
            uint8_t v;
            if (px < 0 || px >= HR_W) continue;
            v = g_fgd[g->off + (uint32_t)(idx >> 1)];
            a = (idx & 1) ? (v & 15) : (v >> 4);
            if (!a) continue;
            a = a * 17; a += a >> 7;
            {
                uint32_t *d = &g_hr[py * HR_W + px];
                int r = (int)((*d >> 16) & 255), gg = (int)((*d >> 8) & 255), b = (int)(*d & 255);
                r = (r * (256 - a) + cr * a) >> 8; gg = (gg * (256 - a) + cg * a) >> 8; b = (b * (256 - a) + cb * a) >> 8;
                *d = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)gg << 8) | (uint32_t)b;
            }
        }
    }
}

/* texto con sombra; x = borde izquierdo, base = linea base. Devuelve el ancho. */
static int hr_text(int x, int base, const char *s, int sz, uint32_t col, int shadow)
{
    int x0 = x;
    while (*s) {
        const FGlyph *g = hr_glyph(sz, hr_next(sz, &s));
        if (g) {
            if (shadow) hr_glyph_draw(x + shadow, base + shadow, g, HC_SHAD);
            hr_glyph_draw(x, base, g, col);
            x += g->adv;
        } else x += fg_asc[sz] / 3;
    }
    return x - x0;
}

static uint32_t hr_col(uint32_t c)
{
    switch (c) {
    case 0xFFFFFFFFu: return HC_WHITE;
    case 0xFF8080A0u: return 0xFF8C9CD2u;       /* apagado, un poco mas claro para que se lea en la tele */
    case 0xFFC0C0FFu: return HC_DIM;
    case 0xFF80FF80u: return HC_GREEN;
    case 0xFFFFC040u: return HC_AMBER;
    case 0xFFFFFF40u: return HC_YEL;
    case 0xFFFFD040u: return HC_YEL;
    case 0xFFA0A0B0u: return 0xFFC8CCE0u;
    case 0xFF505068u: return HC_MUTE;
    default: return c;
    }
}

static void hr_tri(int x, int yc, int h)
{
    int i, j;
    for (i = 0; i < h; i++) {
        int half = i < h / 2 ? i : h - 1 - i;
        for (j = 0; j <= half; j++) hr_rect(x + j * 2, yc - h / 2 + i, x + j * 2 + 2, yc - h / 2 + i + 1, HC_WHITE, 256);
    }
}

/* Logo "NES" blanco + "NET" rojo con barra roja y la version chica a la derecha, centrado */
static void hr_logo(int y, const char *ver)
{
    int base = y * 3 + 44, wn = hr_tw("NES", FS_X), wt = hr_tw("NET", FS_X), wv = hr_tw(ver, FS_S);
    int total = 26 + wn + wt + 16 + wv, x = (HR_W - total) / 2, cap = fg_asc[FS_X] * 3 / 4;
    hr_rect(x, base - cap, x + 10, base, HC_RED, 256);
    x += 26;
    x += hr_text(x, base, "NES", FS_X, HC_WHITE, 4);
    x += hr_text(x, base, "NET", FS_X, HC_RED, 4);
    hr_text(x + 16, base, ver, FS_S, HC_DIM, 2);
}

/* Traduce una llamada de ui_text / ui_center (coordenadas del lienzo 256x240) al lienzo de 1280x720 */
static void hr_ui_text(int cx, int y, const char *s, int sc, uint32_t col, int center)
{
    const char *p = s;
    int sel, row, sz, w, x, yc, cap, base;
    if (!strncmp(s, "NESNET V", 8)) { hr_logo(y, s + 7); return; }
    sel = (s[0] == '>' && s[1] == ' ');
    row = sel || (s[0] == ' ' && s[1] == ' ');
    if (sel) p += 2;
    while (*p == ' ') p++;
    if (!*p) return;
    if (sc >= 2 && col == 0xFFFFD040u) {                  /* titulo de pantalla: barra roja + texto grande */
        sz = FS_H;
        w = hr_tw(p, sz);
        x = (HR_W - w - 26) / 2;
        yc = y * 3 + 21;
        cap = fg_asc[sz] * 3 / 4;
        base = yc + cap / 2;
        hr_rect(x, base - cap, x + 10, base, HC_RED, 256);
        hr_text(x + 26, base, p, sz, HC_WHITE, 3);
        return;
    }
    sz = sc >= 2 ? FS_H : FS_M;
    w = hr_tw(p, sz);
    if (w > 1180) { sz = sc >= 2 ? FS_L : FS_S; w = hr_tw(p, sz); }
    if (w > 1180) { sz = FS_S; w = hr_tw(p, sz); }
    yc = y * 3 + (21 * sc + 1) / 2;
    cap = fg_asc[sz] * 3 / 4;
    base = yc + cap / 2;
    if (center) x = (HR_W - w) / 2;
    else x = row ? cx - 16 + 52 : cx;
    if (!center && row) {                    /* filas "NOMBRE   VALOR" (MANDOS): el valor va en una segunda columna fija */
        const char *dbl = strstr(p, "  ");
        if (dbl && dbl[2]) {
            char nm[40];
            size_t n = (size_t)(dbl - p);
            const char *val = dbl;
            uint32_t c1 = sel ? (col == 0xFFFFFFFFu ? HC_WHITE : 0xFFE0E0EEu) : hr_col(col);
            while (*val == ' ') val++;
            if (n >= sizeof nm) n = sizeof nm - 1;
            memcpy(nm, p, n); nm[n] = 0;
            if (sel) {
                int x0 = cx - 16;
                hr_rect(x0, yc - 17, HR_W - x0, yc + 17, HC_RED, 256);
                hr_tri(x0 + 18, yc, 20);
            }
            hr_text(x, base, nm, sz, c1, 2);
            hr_text(x + 330, base, val, sz, c1, 2);
            return;
        }
    }
    if (sel) {
        int bh = center ? 44 : 34, x0, x1;
        if (center) { x0 = HR_W / 2 - 380; x1 = HR_W / 2 + 380; }
        else { x0 = cx - 16; x1 = HR_W - x0; }
        hr_rect(x0, yc - bh / 2, x1, yc - bh / 2 + bh, HC_RED, 256);
        hr_tri(x0 + 18, yc, 20);
        hr_text(x, base, p, sz, col == 0xFFFFFFFFu ? HC_WHITE : 0xFFE0E0EEu, 2);
    } else {
        hr_text(x, base, p, sz, hr_col(col), 2);
    }
}

/* Barra de volumen (10 tramos) para OPCIONES > SONIDO */
static void hr_vol_bar(int y, int n)
{
    int i, x0 = (HR_W - (10 * 56 + 9 * 10)) / 2, yc = y * 3 + 21;
    for (i = 0; i < 10; i++)
        hr_rect(x0 + i * 66, yc - 15, x0 + i * 66 + 56, yc + 15, i < n ? HC_GREEN : 0xFF28368Au, 256);
}

/* ---- piezas de los disenos aprobados (logo a la izquierda, cuadros, filas con barra roja, botones X / O abajo) ---- */
typedef struct { const char *b; const char *t; uint32_t c; } HHint;
#define HC_BX 0xFF3460D2u            /* boton X (azul) */
#define HC_BO 0xFFDE263Au            /* boton O (rojo) */
#define HC_BG 0xFF46466Eu            /* otros botones */

static void hr_px(int x, int y, uint32_t col, int a)
{
    uint32_t *d;
    int r, g, b;
    if (x < 0 || y < 0 || x >= HR_W || y >= HR_H) return;
    d = &g_hr[y * HR_W + x];
    r = (int)((*d >> 16) & 255); g = (int)((*d >> 8) & 255); b = (int)(*d & 255);
    r = (r * (256 - a) + (int)((col >> 16) & 255) * a) >> 8;
    g = (g * (256 - a) + (int)((col >> 8) & 255) * a) >> 8;
    b = (b * (256 - a) + (int)(col & 255) * a) >> 8;
    *d = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)b;
}

static void hr_disc(int cx, int cy, int r, uint32_t col)      /* circulo relleno con borde suave */
{
    int x, y;
    for (y = cy - r - 1; y <= cy + r + 1; y++)
        for (x = cx - r - 1; x <= cx + r + 1; x++) {
            int d2 = (x - cx) * (x - cx) + (y - cy) * (y - cy);
            if (d2 <= (r - 1) * (r - 1)) hr_px(x, y, col, 256);
            else if (d2 <= r * r) hr_px(x, y, col, 160);
        }
}

static int hr_badge(int x, int y, const char *label, uint32_t col)   /* devuelve el ancho */
{
    int w = 34, tw = hr_tw(label, FS_S);
    if (tw > 20) w = tw + 24;
    hr_disc(x + 17, y + 17, 17, HC_WHITE);
    hr_disc(x + 17, y + 17, 15, col);
    if (w > 34) {
        hr_disc(x + w - 17, y + 17, 17, HC_WHITE);
        hr_rect(x + 17, y, x + w - 17, y + 34, HC_WHITE, 256);
        hr_disc(x + w - 17, y + 17, 15, col);
        hr_rect(x + 17, y + 2, x + w - 17, y + 32, col, 256);
    }
    hr_text(x + (w - tw) / 2, y + 25, label, FS_S, HC_WHITE, 0);
    return w;
}

static void hr_hints(const HHint *h, int n)
{
    int i, total = 0, x, y = 668;
    for (i = 0; i < n; i++) total += (hr_tw(h[i].b, FS_S) > 20 ? hr_tw(h[i].b, FS_S) + 24 : 34) + 10 + hr_tw(h[i].t, FS_S);
    total += 44 * (n - 1);
    x = (HR_W - total) / 2;
    for (i = 0; i < n; i++) {
        int bw = hr_badge(x, y, h[i].b, h[i].c);
        x += bw + 10;
        x += hr_text(x, y + 25, h[i].t, FS_S, HC_DIM, 2) + 44;
    }
}

/* fondo + logo a la izquierda (barra roja, NES blanco, NET rojo, version) + subtitulo */
static void hr_head(const char *sub)
{
    int x = 96, base = 128;
    hr_begin();
    hr_rect(70, 52, 82, 144, HC_RED, 256);
    x += hr_text(x, base, "NES", FS_X, HC_WHITE, 4);
    x += hr_text(x, base, "NET", FS_X, HC_RED, 4);
    hr_text(x + 16, base + 4, "v1.9.8", FS_S, HC_DIM, 2);
    if (sub) hr_text(98, 172, sub, FS_M, HC_DIM, 2);
}

/* filas del menu: barra roja con flecha en la marcada; 'dis' = bits de filas apagadas (bloqueadas) */
static void hr_rows(int x, int y, int w, const char *const *rows, int n, int sel, unsigned dis, int rh)
{
    int i, bh = rh - 8;
    for (i = 0; i < n; i++) {
        int yy = y + i * rh, base = yy + bh / 2 + 12;
        if (i == sel) {
            hr_rect(x, yy, x + w, yy + bh, HC_RED, 256);
            hr_tri(x + 16, yy + bh / 2, 22);
            hr_text(x + 52, base, rows[i], FS_L, HC_WHITE, 2);
        } else {
            hr_text(x + 52, base, rows[i], FS_L, (dis >> i) & 1 ? HC_MUTE : HC_DIM, 2);
        }
    }
}

static void hr_textc(int cx, int base, const char *s, int sz, uint32_t col) { hr_text(cx - hr_tw(s, sz) / 2, base, s, sz, col, 2); }

static void hr_arrow(int cx, int cy, int up)       /* triangulo chico para "hay mas arriba / abajo" */
{
    int r;
    for (r = 0; r < 14; r++) {
        int half = up ? r : 13 - r;
        hr_rect(cx - half, cy - 7 + r, cx + half + 1, cy - 6 + r, HC_DIM, 256);
    }
}

/* fila "NOMBRE ... VALOR" con barra roja si esta marcada; el valor empieza en x + vx */
static void hr_row2(int x, int y, int w, int rh, const char *nm, const char *val, int sel, int vx)
{
    int bh = rh - 8, base = y + bh / 2 + 12;
    if (sel) { hr_rect(x, y, x + w, y + bh, HC_RED, 256); hr_tri(x + 16, y + bh / 2, 22); }
    hr_text(x + 52, base, nm, FS_L, sel ? HC_WHITE : HC_DIM, 2);
    if (val) hr_text(x + vx, base, val, FS_L, sel ? HC_WHITE : HC_DIM, 2);
}

/* Fondo del menu R3 en partida: la imagen del juego (16:9) oscurecida + un cuadro al centro */
static uint32_t g_bd[HR_W * HR_H];         /* fondo del menu R3 (juego oscurecido + cuadro), se arma una vez por apertura */
static int      g_bd_dirty;
static void hr_backdrop(const uint32_t *fb)
{
    int x, y;
    hr_init();
    if (g_bd_dirty) {
        for (y = 0; y < HR_H; y++) {
            const uint32_t *src = fb + (y / 3) * SCR_W;
            for (x = 0; x < HR_W; x++) {
                uint32_t c = src[x / 5];
                uint32_t v = ((((c >> 16) & 255) + ((c >> 8) & 255) + (c & 255)) / 3) >> 2;     /* gris al 25 % */
                g_hr[y * HR_W + x] = 0xFF000000u | (v << 16) | (v << 8) | v | 0x00020410u;
            }
        }
        hr_panel(290, 120, 990, 610);
        memcpy(g_bd, g_hr, sizeof g_hr);
        g_bd_dirty = 0;
    }
    memcpy(g_hr, g_bd, sizeof g_hr);
    g_hr_on = 1;
}

static void ui_text(int x, int y, const char *s, int sc, uint32_t col)
{
    if (g_hr_on) { hr_ui_text(x * 5, y, s, sc, col, 0); return; }
    for (; *s; s++, x += 6 * sc) {
        int c = (unsigned char)*s, cx, cy, i, j;
        if (c >= 'a' && c <= 'z') c -= 32;
        if (c == '_') c = '-';                /* v1.7: la fuente no trae _ ni [ ]: nombres de ROM mas legibles */
        else if (c == '[') c = '(';
        else if (c == ']') c = ')';
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
    if (g_hr_on) { hr_ui_text(0, y, s, sc, col, 1); return; }
    int w = (int)strlen(s) * 6 * sc - sc;
    ui_text((SCR_W - w) / 2, y, s, sc, col);
}

static void ui_clear(void)
{
    int i;
    if (hr_usable()) { hr_begin(); return; }      /* v1.9.7 */
    g_hr_on = 0;
    for (i = 0; i < SCR_W * SCR_H; i++) g_fb[i] = 0xFF101838;
}

/* ------------------------------------------------------------------ */
/* Plataforma: video, mando                                            */
/* ------------------------------------------------------------------ */
/* ------------------------------------------------------------------ */
/* Audio (v1.5)                                                        */
/* El nucleo entrega PCM de 16 bits estereo. Se re-muestrea a 48 kHz con un ajuste fino de   */
/* velocidad (maximo +-1 %) para seguir el reloj de la consola, y se escribe en el anillo de */
/* bloques de libaudio. Ninguna espera es bloqueante: si algo falla, el juego sigue sin sonido. */
/* ------------------------------------------------------------------ */
#define AU_BLK       256            /* muestras por bloque (AUDIO_BLOCK_SAMPLES) */
#define AU_NBLK      32             /* bloques del anillo (AUDIO_BLOCK_32, ~170 ms) */
#define AU_TARGET    8              /* bloques por delante que intento mantener (~43 ms) */
#define AU_PRIME     6              /* tras un corte, relleno con silencio hasta este nivel */
#define AU_URGENT    2              /* si no hay audio, mantengo al menos esto con silencio */
#define AU_QCAP      8192           /* cola de entrada (cuadros estereo) */
#define AU_OUT_RATE  48000.0
#define AU_FILL_T    (AU_TARGET * AU_BLK + 800.0)

static int      g_au_on;                    /* 1 = audio activo */
static double   g_au_inrate = 48000.0;      /* frecuencia que entrega el nucleo */
static int16_t  g_aq[AU_QCAP * 2];
static unsigned g_aq_head, g_aq_cnt;        /* cola circular de entrada (cuadros) */
static double   g_aq_pos;                   /* posicion fraccionaria respecto a head */
static float    g_au_ll, g_au_lr;           /* ultima muestra emitida (para el fundido a silencio) */
static int      g_au_queued;                /* bloques escritos por delante de la lectura */
static int      g_au_reprime;
static uint32_t g_au_lastrd, g_au_lastpush, g_au_lastpump, g_au_logt;
static uint32_t g_au_blocks, g_au_under, g_au_drop;
static double   g_au_step_s = 1.0;          /* paso suavizado */

#ifdef NESNET_PS3
static u32  g_au_port;
static audioPortConfig g_au_cfg;
static sys_event_queue_t g_au_q;
static sys_ipc_key_t g_au_key;
static int  g_au_init, g_au_portok, g_au_qok, g_au_started;

static uint32_t au_hw_readidx(void) { return (uint32_t)(*(volatile u64 *)(uintptr_t)g_au_cfg.readIndex); }
static float *au_hw_block(uint32_t i) { return (float *)(uintptr_t)g_au_cfg.audioDataStart + (size_t)i * AU_BLK * 2; }
static void au_hw_poll(void) { if (g_au_qok) sysEventQueueDrain(g_au_q); }

static void au_close(void)
{
    g_au_on = 0;
    if (g_au_started) { audioPortStop(g_au_port); g_au_started = 0; }
    if (g_au_qok) { audioRemoveNotifyEventQueue(g_au_key); sysEventQueueDestroy(g_au_q, 0); g_au_qok = 0; }
    if (g_au_portok) { audioPortClose(g_au_port); g_au_portok = 0; }
    if (g_au_init) { audioQuit(); g_au_init = 0; }
}
#else
static uint32_t au_hw_readidx(void) { return 0; }
static float *au_hw_block(uint32_t i) { static float b[AU_BLK * 2]; (void)i; return b; }
static void au_hw_poll(void) {}
static void au_close(void) {}
#endif

/* AUDIO-GENERIC-BEGIN */
static int      g_volume = 100;        /* v1.9: volumen 0..100 (100 = igual que siempre) */
static void au_reset(void)
{
    g_aq_head = 0; g_aq_cnt = 0; g_aq_pos = 0.0;
}

/* Recibe PCM del nucleo (se llama desde retro_run) */
static void au_push(const int16_t *d, size_t frames)
{
    size_t i;
    if (!g_au_on || !frames) return;
    g_au_lastpush = now_ms();
    if (frames > AU_QCAP) { d += (frames - AU_QCAP) * 2; frames = AU_QCAP; }
    if (g_aq_cnt + frames > AU_QCAP) {              /* la cola se llena: descarto lo mas viejo */
        unsigned over = (unsigned)(g_aq_cnt + frames - AU_QCAP);
        if (over > g_aq_cnt) over = g_aq_cnt;
        g_aq_head = (g_aq_head + over) % AU_QCAP;
        g_aq_cnt -= over;
        g_aq_pos -= (double)over;
        if (g_aq_pos < 0.0) g_aq_pos = 0.0;
        g_au_drop++;
    }
    for (i = 0; i < frames; i++) {
        unsigned w = (g_aq_head + g_aq_cnt) % AU_QCAP;
        if (g_volume >= 100) {                      /* volumen normal: las muestras pasan sin tocarse (igual que antes) */
            g_aq[w * 2]     = d[i * 2];
            g_aq[w * 2 + 1] = d[i * 2 + 1];
        } else {                                    /* v1.9: volumen bajado desde OPCIONES > SONIDO */
            g_aq[w * 2]     = (int16_t)((int)d[i * 2]     * g_volume / 100);
            g_aq[w * 2 + 1] = (int16_t)((int)d[i * 2 + 1] * g_volume / 100);
        }
        g_aq_cnt++;
    }
}

/* Paso de lectura de la entrada por cada muestra de salida: nominal +- 1 %, segun cuanto audio
 * hay acumulado (en la cola de salida + en la de entrada) respecto al objetivo. */
static double au_calc_step(void)
{
    double base = g_au_inrate / AU_OUT_RATE;
    double fill = (double)g_au_queued * AU_BLK + (double)g_aq_cnt / base;
    double e = (fill - AU_FILL_T) / AU_FILL_T;
    double s;
    if (e > 1.0) e = 1.0; else if (e < -1.0) e = -1.0;
    s = base * (1.0 + 0.01 * e);
    g_au_step_s += 0.05 * (s - g_au_step_s);
    if (g_au_step_s > base * 1.01) g_au_step_s = base * 1.01;
    if (g_au_step_s < base * 0.99) g_au_step_s = base * 0.99;
    return g_au_step_s;
}

static void au_silence_block(float *o)
{
    int i;
    for (i = 0; i < AU_BLK; i++) {
        g_au_ll *= 0.995f; g_au_lr *= 0.995f;
        if (g_au_ll > -1e-6f && g_au_ll < 1e-6f) g_au_ll = 0.0f;
        if (g_au_lr > -1e-6f && g_au_lr < 1e-6f) g_au_lr = 0.0f;
        o[i * 2] = g_au_ll; o[i * 2 + 1] = g_au_lr;
    }
}

/* Un bloque real: interpolacion lineal entre muestras de entrada. El que llama garantiza que
 * hay suficiente entrada (au_need). */
static int au_need(double step) { return (int)(g_aq_pos + AU_BLK * step) + 2; }

static void au_real_block(float *o, double step)
{
    int i, n;
    for (i = 0; i < AU_BLK; i++) {
        int k = (int)g_aq_pos;
        double fr = g_aq_pos - (double)k;
        unsigned a = (g_aq_head + (unsigned)k) % AU_QCAP, b = (g_aq_head + (unsigned)k + 1) % AU_QCAP;
        double l = (double)g_aq[a * 2]     + ((double)g_aq[b * 2]     - (double)g_aq[a * 2])     * fr;
        double r = (double)g_aq[a * 2 + 1] + ((double)g_aq[b * 2 + 1] - (double)g_aq[a * 2 + 1]) * fr;
        g_au_ll = (float)(l / 32768.0); g_au_lr = (float)(r / 32768.0);
        o[i * 2] = g_au_ll; o[i * 2 + 1] = g_au_lr;
        g_aq_pos += step;
    }
    n = (int)g_aq_pos;
    if (n > (int)g_aq_cnt) n = (int)g_aq_cnt;
    g_aq_head = (g_aq_head + (unsigned)n) % AU_QCAP;
    g_aq_cnt -= (unsigned)n;
    g_aq_pos -= (double)n;
    if (g_aq_pos < 0.0) g_aq_pos = 0.0;
}

/* Se llama muy seguido (desde pump()): repone bloques en el anillo segun avance el reloj de audio */
static void au_pump(void)
{
    uint32_t rd, now;
    int d, idle, guard = 0;
    double step;
    if (!g_au_on) return;
    now = now_ms();
    idle = (uint32_t)(now - g_au_lastpush) > 500;
    au_hw_poll();
    if (g_au_lastpump && (uint32_t)(now - g_au_lastpump) > 120) {
        /* el programa estuvo detenido: el anillo pudo dar la vuelta; lo dejo en silencio y empiezo de nuevo */
        int j;
        for (j = 0; j < AU_NBLK; j++) memset(au_hw_block((uint32_t)j), 0, AU_BLK * 2 * sizeof(float));
        g_au_queued = 0; g_au_reprime = 1;
        g_au_lastrd = au_hw_readidx() % AU_NBLK;
        if (!idle) g_au_under++;
    }
    g_au_lastpump = now;
    rd = au_hw_readidx() % AU_NBLK;
    d = (int)((rd + AU_NBLK - g_au_lastrd) % AU_NBLK);
    if (d > 0) {
        int j;
        for (j = 0; j < d; j++) memset(au_hw_block((g_au_lastrd + (uint32_t)j) % AU_NBLK), 0, AU_BLK * 2 * sizeof(float));
        if (d > g_au_queued) { if (!idle) { g_au_under++; g_au_reprime = 1; } g_au_queued = 0; }
        else g_au_queued -= d;
        g_au_lastrd = rd;
    }
    step = au_calc_step();
    while (g_au_queued < AU_TARGET && guard++ < AU_NBLK) {
        float *o = au_hw_block((rd + 1 + (uint32_t)g_au_queued) % AU_NBLK);
        if (g_au_reprime && g_au_queued < AU_PRIME) {
            au_silence_block(o);
            if (g_au_queued + 1 >= AU_PRIME) g_au_reprime = 0;
        } else if ((int)g_aq_cnt >= au_need(step)) {
            au_real_block(o, step);
            g_au_blocks++;
        } else if (g_au_queued < AU_URGENT) {
            au_silence_block(o);
        } else break;
        g_au_queued++;
    }
    if (!idle && (uint32_t)(now - g_au_logt) >= 2000) {
        g_au_logt = now;
        logf_("audio: bloques=%u cortes=%u descartes=%u cola=%d entrada=%u paso=%d/10000",
              (unsigned)g_au_blocks, (unsigned)g_au_under, (unsigned)g_au_drop,
              g_au_queued, (unsigned)g_aq_cnt, (int)(step * 10000.0));
    }
}
/* AUDIO-GENERIC-END */

#ifdef NESNET_PS3
static void au_open(void)
{
    audioPortParam pr;
    s32 r;
    g_au_on = 0;
    if (!g_cfg.audio) { logf_("audio: apagado (audio=off o R2 al abrir)"); return; }
    logf_("audio: llamando a audioInit...");
    r = audioInit();
    logf_("audio: audioInit=%08x", (unsigned)r);
    if (r != 0) return;
    g_au_init = 1;
    memset(&pr, 0, sizeof pr);
    pr.numChannels = AUDIO_PORT_2CH;
    pr.numBlocks   = AUDIO_BLOCK_32;
    pr.attrib      = AUDIO_PORT_INITLEVEL;
    pr.level       = 1.0f;
    logf_("audio: llamando a audioPortOpen...");
    r = audioPortOpen(&pr, &g_au_port);
    logf_("audio: audioPortOpen=%08x puerto=%u", (unsigned)r, (unsigned)g_au_port);
    if (r != 0) { au_close(); return; }
    g_au_portok = 1;
    r = audioGetPortConfig(g_au_port, &g_au_cfg);
    logf_("audio: config=%08x bloques=%u canales=%u indice=%08x datos=%08x", (unsigned)r,
          (unsigned)g_au_cfg.numBlocks, (unsigned)g_au_cfg.channelCount,
          (unsigned)g_au_cfg.readIndex, (unsigned)g_au_cfg.audioDataStart);
    if (r != 0 || g_au_cfg.numBlocks != AU_NBLK || g_au_cfg.channelCount != 2 ||
        !g_au_cfg.readIndex || !g_au_cfg.audioDataStart) {
        logf_("AVISO: el puerto de audio no tiene el formato esperado; sigo sin sonido");
        au_close(); return;
    }
    r = audioCreateNotifyEventQueue(&g_au_q, &g_au_key);
    logf_("audio: cola de eventos=%08x", (unsigned)r);
    if (r == 0) {
        g_au_qok = 1;
        r = audioSetNotifyEventQueue(g_au_key);
        logf_("audio: audioSetNotifyEventQueue=%08x", (unsigned)r);
        sysEventQueueDrain(g_au_q);
    } else {
        logf_("AVISO: sin cola de eventos de audio; sigo leyendo el indice directamente");
    }
    { int i; for (i = 0; i < AU_NBLK; i++) memset(au_hw_block((uint32_t)i), 0, AU_BLK * 2 * sizeof(float)); }
    g_au_lastrd = au_hw_readidx() % AU_NBLK;
    g_au_queued = 0; g_au_reprime = 1; g_au_lastpush = 0; g_au_lastpump = 0;
    logf_("audio: llamando a audioPortStart...");
    r = audioPortStart(g_au_port);
    logf_("audio: audioPortStart=%08x", (unsigned)r);
    if (r != 0) { au_close(); return; }
    g_au_started = 1;
    g_au_on = 1;
    logf_("audio: listo (anillo de %d bloques)", AU_NBLK);
}
#else
static void au_open(void) {}
#endif

/* v1.8.1: palanca izquierda como cruz. Los ejes van de 0 a 255 con el centro cerca de 128. La zona muerta es
 * amplia (50 de 128) para que un stick flojo o con deriva no mande movimientos sueltos. Funcion pura: se
 * puede probar en PC. Devuelve -1 (izq/arriba), 0 (centro) o +1 (der/abajo) para cada eje. */
#define STICK_DEAD 50
static int stick_axis(unsigned v)
{
    if (v < 128u - STICK_DEAD) return -1;
    if (v > 128u + STICK_DEAD) return 1;
    return 0;
}
static uint16_t stick_nes_bits(unsigned h, unsigned v)
{
    uint16_t b = 0;
    int ax = stick_axis(h), ay = stick_axis(v);
    if (ax < 0) b |= NB_LEFT;
    if (ax > 0) b |= NB_RIGHT;
    if (ay < 0) b |= NB_UP;
    if (ay > 0) b |= NB_DOWN;
    return b;
}

/* ------------------------------------------------------------------ */
/* v1.8.2: OPCIONES - mapeo de botones, turbo y pantalla               */
/* Todo esto es LOCAL. Por la red sigue viajando el estado de los botones del NES (el mensaje no cambia),   */
/* asi que el mapeo de cada jugador no hace falta enviarlo: cada consola traduce sus propios botones antes. */
/* Las funciones de esta seccion son puras (no tocan la PS3), asi que se prueban tal cual en PC.             */
/* ------------------------------------------------------------------ */
enum { PB_CROSS, PB_CIRCLE, PB_SQUARE, PB_TRIANGLE, PB_L1, PB_R1, PB_L2, PB_R2, PB_L3, PB_R3, PB_START, PB_SELECT, PB_COUNT };
#define PB_NONE   (-1)
#define PB_BIT(b) (1u << (b))
enum { MA_A, MA_B, MA_SEL, MA_START, MA_TA, MA_TB, MA_COUNT };    /* MA_TA / MA_TB = turbo A / turbo B */

static const char *const pb_names[PB_COUNT] = { "X", "O", "CUADRADO", "TRIANGULO", "L1", "R1", "L2", "R2", "L3", "R3", "START", "SELECT" };
static const char *const ma_names[MA_COUNT] = { "A", "B", "SELECT", "START", "TURBO A", "TURBO B" };

/* boton de la PS3 que dispara cada boton del NES, por mando. Los valores por defecto son EXACTAMENTE los de la v1.8.1
 * (O = A, X = B, SELECT, START); los turbo empiezan sin asignar. Las direcciones (cruz y palanca) no se remapean. */
static int g_map[2][MA_COUNT] = {
    { PB_CIRCLE, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE },
    { PB_CIRCLE, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE }
};
static unsigned g_turbo_cnt[2][2];     /* cuadros seguidos que lleva apretado cada turbo (A, B) de cada mando */
static int      g_screen;              /* 0 = original (pixeles cuadrados, como hasta ahora), 1 = 4:3 real, 2 = 16:9 estirada */
/* v1.9.3: la opcion de pantalla (g_screen) es solo para la imagen del JUEGO. Los menus y avisos (todo lo que se dibuja fuera de una
 * partida) usan siempre MENU_SCREEN, asi no cambian de tamano al mover ORIGINAL / 4:3 / 16:9. El ajuste de imagen (tamano y
 * desplazamiento, para el overscan de la TV) sigue valiendo para todo. Usan la pantalla elegida: session_loop / session_loop4
 * (g_ingame = 1 mientras corren; el menu de R2 sobre el juego cuenta como juego) y la pantalla AJUSTE DE IMAGEN (g_adjusting = 1),
 * que tiene que mostrar el marco con la geometria real del juego. */
#define MENU_SCREEN 2                  /* 2 = 16:9 a pantalla completa (1 = 4:3 centrado, 0 = original) */
static int      g_ingame;
static int      g_adjusting;
static int      g_netinfo;             /* v1.9: info de red en partida: 0 = solo al inicio (como siempre), 1 = siempre, 2 = no */
static char     g_last_rom[ROM_NAMELEN];   /* v1.9: nombre del archivo de la ultima ROM elegida */
static char     g_last_code[16];           /* v1.9.3: ultimo codigo de sala escrito al UNIRSE (10 digitos, o vacio) */
static int      g_showfps;             /* v1.9.2: 1 = FPS abajo a la derecha (en SOLO y online), 0 = no */
/* v1.9.2: ajuste de imagen (OPCIONES > AJUSTE DE IMAGEN): tamano en % de la imagen de la pantalla elegida y
 * desplazamiento en pixeles de la TV. Con los valores de siempre (100, 0, 0) se usa el dibujo de antes, sin cambios. */
#define IMG_SIZE_MIN   70
#define IMG_SHIFT_MAX  60
static int      g_img_size = 100;
static int      g_img_dx, g_img_dy;

static void map_defaults(int p)
{
    g_map[p][MA_A] = PB_CIRCLE; g_map[p][MA_B] = PB_CROSS;
    g_map[p][MA_SEL] = PB_SELECT; g_map[p][MA_START] = PB_START;
    g_map[p][MA_TA] = PB_NONE; g_map[p][MA_TB] = PB_NONE;
    g_turbo_cnt[p][0] = g_turbo_cnt[p][1] = 0;
}

/* Convierte los botones de PS3 apretados (mascara PB_BIT) y las direcciones ya calculadas (cruz + palanca) en el byte NES.
 * Turbo: mientras el boton esta apretado alterna 2 cuadros apretado / 2 sueltos (15 pulsos por segundo), empezando apretado. */
static uint16_t map_nes_bits(int port, uint32_t btns, uint16_t dirs)
{
    const int *m = g_map[port & 1];
    uint16_t b = (uint16_t)(dirs & (NB_UP | NB_DOWN | NB_LEFT | NB_RIGHT));
    int t;
    if (m[MA_A]     >= 0 && (btns & PB_BIT(m[MA_A])))     b |= NB_A;
    if (m[MA_B]     >= 0 && (btns & PB_BIT(m[MA_B])))     b |= NB_B;
    if (m[MA_SEL]   >= 0 && (btns & PB_BIT(m[MA_SEL])))   b |= NB_SEL;
    if (m[MA_START] >= 0 && (btns & PB_BIT(m[MA_START]))) b |= NB_START;
    for (t = 0; t < 2; t++) {
        int id = m[MA_TA + t];
        unsigned *c = &g_turbo_cnt[port & 1][t];
        if (id >= 0 && (btns & PB_BIT(id))) {
            if (((*c >> 1) & 1u) == 0) b |= (t == 0 ? NB_A : NB_B);
            *c = (*c + 1) & 0xFFFFu;
        } else {
            *c = 0;
        }
    }
    if ((b & NB_UP) && (b & NB_DOWN))    b &= (uint16_t)~NB_DOWN;
    if ((b & NB_LEFT) && (b & NB_RIGHT)) b &= (uint16_t)~NB_RIGHT;
    return b;
}

/* ¿Puede la accion 'act' del mando 'port' tomar el boton 'btn'? Reglas: solo los turbo pueden quedar sin boton;
 * R3 y L2 del mando 1 estan reservados (R3 abre el menu, L2 hace la captura); un boton que ya usa OTRA fila del mismo mando no se puede tomar
 * (nunca se mueve un boton ajeno: para cambiarlo, primero se libera en su fila). */
static int map_allowed(int port, int act, int btn)
{
    int a;
    if (btn == PB_NONE) return act >= MA_TA;
    if (btn < 0 || btn >= PB_COUNT) return 0;
    if (port == 0 && (btn == PB_R3 || btn == PB_L2)) return 0;
    for (a = 0; a < MA_COUNT; a++)
        if (a != act && g_map[port][a] == btn) return 0;
    return 1;
}

static void map_assign(int port, int act, int btn) { g_map[port][act] = btn; }

/* Pasa al siguiente (dir = +1) o anterior (dir = -1) boton permitido, saltando los que no se pueden tomar.
 * Orden: SIN ASIGNAR (solo turbo), X, O, CUADRADO, TRIANGULO, L1, R1, L2, R2, L3, R3, START, SELECT */
static void map_cycle(int port, int act, int dir)
{
    int n = PB_COUNT + 1, cur = g_map[port][act] + 1, i;
    for (i = 1; i <= n; i++) {
        int idx = (((cur + dir * i) % n) + n) % n;
        int btn = idx - 1;
        if (map_allowed(port, act, btn)) { map_assign(port, act, btn); return; }
    }
}

/* Comprueba un mapeo leido de archivo: botones normales siempre asignados, sin repetidos, sin R3 en el mando 1 */
static int map_valid(const int *m, int port)
{
    int a, c;
    for (a = 0; a < MA_COUNT; a++) {
        if (m[a] == PB_NONE) { if (a < MA_TA) return 0; continue; }
        if (m[a] < 0 || m[a] >= PB_COUNT) return 0;
        if (port == 0 && (m[a] == PB_R3 || m[a] == PB_L2)) return 0;
        for (c = a + 1; c < MA_COUNT; c++) if (m[c] == m[a]) return 0;
    }
    return 1;
}

/* Pantalla: ancho de salida (en pixeles de la TV) para un alto de salida 'oh'.
 *   0 original  = SCR_W * z  (pixeles cuadrados, 768x720 en 720p: lo de siempre)
 *   1 4:3 real  = oh * 4 / 3 (960x720 en 720p: columnas repetidas 3 o 4 veces, el 3,75 no es entero)
 *   2 16:9      = oh * 16 / 9 (1280x720 en 720p: cada columna x5 y cada fila x3, todo entero) */
#define COLMAP_MAX 2048
static const char *const screen_names[3] = { "ORIGINAL", "4:3 REAL", "16:9 ESTIRADA" };
static int screen_out_w(int mode, int dw, int oh, int z)
{
    int w;
    if (mode == 1) w = oh * 4 / 3;
    else if (mode == 2) w = oh * 16 / 9;
    else w = SCR_W * z;
    if (w > dw) w = dw;
    if (w > COLMAP_MAX) w = COLMAP_MAX;
    return w;
}

/* Dibuja el lienzo 256x240 en el buffer de pantalla 'base' (dw x dh, ARGB) centrado, escalado segun 'mode' (vertical entero z).
 * Cada 4 cuadros, DE CADA BUFFER, borra lo que queda fuera de la imagen (residuo del XMB / modo anterior); la imagen se repinta siempre.
 * fcnt = contador de cuadros de ese buffer. Version unica para la PS3 y para las pruebas de PC. */
static void canvas_blit_cpu(uint32_t *base, int dw, int dh, int mode, int z, const uint32_t *fb, unsigned *fcnt)
{
    static uint32_t row[COLMAP_MAX];
    static int cm[COLMAP_MAX];
    static int l_ow = -1;
    int oh = SCR_H * z, ow = screen_out_w(mode, dw, oh, z);
    int ox = (dw - ow) / 2, oy = (dh - oh) / 2, x, y, k;
    uint32_t *dst;
    if (z < 1 || ow < 1 || ox < 0 || oy < 0 || oy + oh > dh) return;
    if (ow != l_ow) { for (x = 0; x < ow; x++) cm[x] = x * SCR_W / ow; l_ow = ow; }
    if (((*fcnt)++ & 3) == 0) {
        int below = dh - oy - oh;
        if (oy > 0) memset(base, 0, (size_t)oy * dw * 4);
        if (below > 0) memset(base + (size_t)(oy + oh) * dw, 0, (size_t)below * dw * 4);
        if (ox > 0) {
            int right = dw - ox - ow;
            for (y = oy; y < oy + oh; y++) {
                memset(base + (size_t)y * dw, 0, (size_t)ox * 4);
                if (right > 0) memset(base + (size_t)y * dw + ox + ow, 0, (size_t)right * 4);
            }
        }
    }
    dst = base + (size_t)oy * dw + ox;
    for (y = 0; y < SCR_H; y++) {
        const uint32_t *src = fb + y * SCR_W;
        for (x = 0; x < ow; x++) row[x] = src[cm[x]];
        for (k = 0; k < z; k++) { memcpy(dst, row, (size_t)ow * 4); dst += dw; }
    }
}

/* v1.9.2: dibujo con ajuste de imagen (tamano en % del lienzo de la pantalla elegida y desplazamiento en pixeles de la TV).
 * Con size = 100 y dx = dy = 0 da EXACTAMENTE la misma imagen que canvas_blit_cpu (lo comprueba screentest); la PS3 sigue
 * usando canvas_blit_cpu mientras no se toque el ajuste. Si la imagen se sale por un borde se recorta: nunca escribe fuera.
 * Filas y columnas por vecino mas cercano (como el resto). Borra todo el buffer cuando cambia la posicion o el tamano
 * (2 veces seguidas: un buffer de pantalla cada vez) y despues cada 4 cuadros de cada buffer, como canvas_blit_cpu. */
static void canvas_blit_adj(uint32_t *base, int dw, int dh, int mode, int z, const uint32_t *fb, unsigned *fcnt,
                            int size, int dx, int dy)
{
    static uint32_t row[COLMAP_MAX];
    static int cm[COLMAP_MAX];
    static int l_ow = -1;
    static int geo[4] = { -1, -1, -1, -1 }, force_clear;
    int oh0 = SCR_H * z, ow0 = screen_out_w(mode, dw, oh0, z);
    int ow, oh, ox, oy, x0, x1, y0, y1, y, x, last_sy = -1;
    if (z < 1 || ow0 < 1) return;
    if (size < IMG_SIZE_MIN) size = IMG_SIZE_MIN;
    if (size > 100) size = 100;
    ow = ow0 * size / 100; oh = oh0 * size / 100;
    if (ow < 1) ow = 1;
    if (oh < 1) oh = 1;
    ox = (dw - ow) / 2 + dx; oy = (dh - oh) / 2 + dy;
    if (ow != l_ow) { for (x = 0; x < ow; x++) cm[x] = x * SCR_W / ow; l_ow = ow; }
    if (ox != geo[0] || oy != geo[1] || ow != geo[2] || oh != geo[3]) { geo[0] = ox; geo[1] = oy; geo[2] = ow; geo[3] = oh; force_clear = 2; }
    if (force_clear > 0) { force_clear--; (*fcnt)++; memset(base, 0, (size_t)dw * dh * 4); }
    else if (((*fcnt)++ & 3) == 0) memset(base, 0, (size_t)dw * dh * 4);
    x0 = ox < 0 ? 0 : ox;  x1 = ox + ow > dw ? dw : ox + ow;
    y0 = oy < 0 ? 0 : oy;  y1 = oy + oh > dh ? dh : oy + oh;
    if (x1 <= x0 || y1 <= y0) return;
    for (y = y0; y < y1; y++) {
        int sy = (y - oy) * SCR_H / oh;
        if (sy != last_sy) {
            const uint32_t *src = fb + sy * SCR_W;
            for (x = x0; x < x1; x++) row[x - x0] = src[cm[x - ox]];
            last_sy = sy;
        }
        memcpy(base + (size_t)y * dw + x0, row, (size_t)(x1 - x0) * 4);
    }
}

/* Guardado de las opciones: USRDIR/opciones.txt (aparte de config.txt, que el instalador puede reemplazar) */
static void opts_defaults(void)
{
    map_defaults(0); map_defaults(1);
    g_screen = 0;
    g_volume = 100;
    g_netinfo = 0;
    g_showfps = 0;
    g_img_size = 100; g_img_dx = 0; g_img_dy = 0;
    g_last_rom[0] = 0;
    g_last_code[0] = 0;
}

static void opts_save(void)
{
    char path[300], tmp[300];
    FILE *f;
    int p;
    snprintf(path, sizeof path, "%s/opciones.txt", g_dir);
    snprintf(tmp, sizeof tmp, "%s/opciones.tmp", g_dir);
    f = fopen(tmp, "w");
    if (!f) { logf_("AVISO: no pude guardar opciones.txt"); return; }
    fprintf(f, "# NesNet - opciones (las cambia el menu OPCIONES)\n");
    fprintf(f, "screen=%d\n", g_screen);
    fprintf(f, "volume=%d\n", g_volume);
    fprintf(f, "netinfo=%d\n", g_netinfo);
    fprintf(f, "fps=%d\n", g_showfps);
    fprintf(f, "imgsize=%d\n", g_img_size);
    fprintf(f, "imgx=%d\n", g_img_dx);
    fprintf(f, "imgy=%d\n", g_img_dy);
    if (g_last_rom[0]) fprintf(f, "rom=%s\n", g_last_rom);
    if (g_last_code[0]) fprintf(f, "code=%s\n", g_last_code);
    for (p = 0; p < 2; p++)
        fprintf(f, "pad%d=%d,%d,%d,%d,%d,%d\n", p + 1, g_map[p][0], g_map[p][1], g_map[p][2], g_map[p][3], g_map[p][4], g_map[p][5]);
    fclose(f);
    remove(path);
    if (rename(tmp, path) != 0) logf_("AVISO: no pude renombrar opciones.tmp");
}

static void opts_load(void)
{
    char path[300], line[200];
    FILE *f;
    opts_defaults();
    snprintf(path, sizeof path, "%s/opciones.txt", g_dir);
    f = fopen(path, "r");
    if (!f) { logf_("sin opciones.txt: pantalla y mandos por defecto"); return; }
    while (fgets(line, sizeof line, f)) {
        int v[MA_COUNT], p;
        if (line[0] == '#') continue;
        if (sscanf(line, "screen=%d", &v[0]) == 1) {
            if (v[0] >= 0 && v[0] <= 2) g_screen = v[0];
        } else if (sscanf(line, "volume=%d", &v[0]) == 1) {
            if (v[0] >= 0 && v[0] <= 100) g_volume = v[0];
        } else if (sscanf(line, "netinfo=%d", &v[0]) == 1) {
            if (v[0] >= 0 && v[0] <= 2) g_netinfo = v[0];
        } else if (sscanf(line, "fps=%d", &v[0]) == 1) {
            if (v[0] == 0 || v[0] == 1) g_showfps = v[0];
        } else if (sscanf(line, "imgsize=%d", &v[0]) == 1) {
            if (v[0] >= IMG_SIZE_MIN && v[0] <= 100) g_img_size = v[0];
        } else if (sscanf(line, "imgx=%d", &v[0]) == 1) {
            if (v[0] >= -IMG_SHIFT_MAX && v[0] <= IMG_SHIFT_MAX) g_img_dx = v[0];
        } else if (sscanf(line, "imgy=%d", &v[0]) == 1) {
            if (v[0] >= -IMG_SHIFT_MAX && v[0] <= IMG_SHIFT_MAX) g_img_dy = v[0];
        } else if (!strncmp(line, "rom=", 4)) {
            size_t n = strlen(line + 4);
            while (n > 0 && (line[4 + n - 1] == '\n' || line[4 + n - 1] == '\r')) n--;
            if (n > 0 && n < ROM_NAMELEN && !memchr(line + 4, '/', n) && line[4] != '.') { memcpy(g_last_rom, line + 4, n); g_last_rom[n] = 0; }
        } else if (!strncmp(line, "code=", 5)) {
            /* v1.9.3: solo se acepta si son exactamente 10 digitos */
            size_t n = strlen(line + 5), k;
            int okc;
            while (n > 0 && (line[5 + n - 1] == '\n' || line[5 + n - 1] == '\r')) n--;
            okc = (n == 10);
            for (k = 0; okc && k < n; k++) if (line[5 + k] < '0' || line[5 + k] > '9') okc = 0;
            if (okc) { memcpy(g_last_code, line + 5, 10); g_last_code[10] = 0; }
        } else if ((line[0] == 'p' && line[1] == 'a' && line[2] == 'd' && (line[3] == '1' || line[3] == '2') && line[4] == '=') &&
                   sscanf(line + 5, "%d,%d,%d,%d,%d,%d", &v[0], &v[1], &v[2], &v[3], &v[4], &v[5]) == 6) {
            p = line[3] - '1';
            if (map_valid(v, p)) { int a; for (a = 0; a < MA_COUNT; a++) g_map[p][a] = v[a]; }
            else logf_("AVISO: opciones.txt: mapeo del mando %d no valido, uso el de por defecto", p + 1);
        }
    }
    fclose(f);
    logf_("opciones: pantalla=%d volumen=%d info_red=%d fps=%d imagen=%d%%,%d,%d  mando1=%d,%d,%d,%d,%d,%d  mando2=%d,%d,%d,%d,%d,%d", g_screen, g_volume, g_netinfo,
          g_showfps, g_img_size, g_img_dx, g_img_dy,
          g_map[0][0], g_map[0][1], g_map[0][2], g_map[0][3], g_map[0][4], g_map[0][5],
          g_map[1][0], g_map[1][1], g_map[1][2], g_map[1][3], g_map[1][4], g_map[1][5]);
    if (g_last_rom[0]) logf_("opciones: ultima ROM = %s", g_last_rom);
}

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
    if (g_cfg.render && g_zoom > 3) g_zoom = 3;      /* escribir a mano en la VRAM es lento: x3 maximo (v1.3; antes x2) */
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

/* v1.9.7: copia el cuadro de menu de 1280x720 al buffer de pantalla (igual de ancho: fila por fila; otra resolucion: vecino mas cercano) */
static void hr_blit(uint32_t *base, int dw, int dh)
{
    int x, y;
    if (dw == HR_W && dh == HR_H) { memcpy(base, g_hr, sizeof g_hr); return; }
    for (y = 0; y < dh; y++) {
        const uint32_t *s = g_hr + (size_t)(y * HR_H / dh) * HR_W;
        uint32_t *d = base + (size_t)y * dw;
        for (x = 0; x < dw; x++) d[x] = s[x * HR_W / dw];
    }
}

static void gpu_blit_canvas(void)
{
    gcmTransferScale scale;
    gcmTransferSurface surface;
    int sel = g_texsel;
    float zoom = (float)g_zoom;

    if (g_cfg.render) {
        /* Modo CPU: sin transferencia ni clear ni blend de la GPU; escribo directo en el buffer de pantalla */
        static unsigned cpu_frame[2];     /* un contador por buffer de pantalla (v1.4) */
        int smode = (g_ingame || g_adjusting) ? g_screen : MENU_SCREEN;   /* v1.9.3 */
        if (!g_first) {
            int guard = 0;
            while (gcmGetFlipStatus() != 0 && guard++ < 15000) usleep(200);
        }
        g_stage = "cpu-copia";
        if (g_hr_on) {                    /* v1.9.7: cuadro de menu de 1280x720 */
            g_stage = "cpu-copia-hr";
            hr_blit((uint32_t *)g_cbuf[g_cur], (int)g_dw, (int)g_dh);
            g_hr_on = 0;
            cpu_frame[0] = cpu_frame[1] = 0;   /* al volver al juego se limpian los bordes enseguida */
            return;
        }
        /* v1.3: cada 4 cuadros DE CADA BUFFER se limpia lo que queda fuera del juego (bordes) para que no se quede el
         * residuo del XMB (reloj / bateria del mando); el juego mismo se repinta siempre.
         * v1.8.2: el escalado (modo de pantalla elegido en OPCIONES) y esa limpieza viven en canvas_blit_cpu. */
        if (g_img_size == 100 && g_img_dx == 0 && g_img_dy == 0)
            canvas_blit_cpu((uint32_t *)g_cbuf[g_cur], (int)g_dw, (int)g_dh, smode, g_zoom, (const uint32_t *)g_fb, &cpu_frame[g_cur & 1]);
        else   /* v1.9.2: con el ajuste de imagen tocado */
            canvas_blit_adj((uint32_t *)g_cbuf[g_cur], (int)g_dw, (int)g_dh, smode, g_zoom, (const uint32_t *)g_fb, &cpu_frame[g_cur & 1],
                            g_img_size, g_img_dx, g_img_dy);
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

static void pump(void) { sysUtilCheckCallback(); au_pump(); }

static void exit_cb(void)
{
    sysUtilUnregisterCallback(SYSUTIL_EVENT_SLOT0);
    au_close();
    if (g_ctx) { gcmSetWaitFlip(g_ctx); rsxFinish(g_ctx, 1); }
}

static void platform_init(void)
{
    gpu_init();
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
    /* v1.9: un mando apagado/desconectado (o sin lectura todavia) debe quedar con las palancas en el CENTRO (128).
     * Con 0 la palanca parecia empujada a la izquierda/arriba y el jugador 2 se movia solo (error de la v1.8.1 en adelante). */
    if (!pi.status[port]) { memset(&g_pd[port], 0, sizeof g_pd[port]); g_pd[port].ANA_L_H = g_pd[port].ANA_L_V = g_pd[port].ANA_R_H = g_pd[port].ANA_R_V = 128; return &g_pd[port]; }
    memset(&d, 0, sizeof d);
    ioPadGetData(port, &d);
    if (d.len > 0) g_pd[port] = d;
    else if (!g_pd[port].ANA_L_H && !g_pd[port].ANA_L_V) g_pd[port].ANA_L_H = g_pd[port].ANA_L_V = g_pd[port].ANA_R_H = g_pd[port].ANA_R_V = 128;   /* aun sin lectura valida */
    return &g_pd[port];
}

/* v1.8.2: botones de la PS3 apretados, como mascara PB_BIT (los que se pueden asignar en OPCIONES) */
static uint32_t pad_buttons(const padData *d)
{
    uint32_t m = 0;
    if (d->BTN_CROSS)    m |= PB_BIT(PB_CROSS);
    if (d->BTN_CIRCLE)   m |= PB_BIT(PB_CIRCLE);
    if (d->BTN_SQUARE)   m |= PB_BIT(PB_SQUARE);
    if (d->BTN_TRIANGLE) m |= PB_BIT(PB_TRIANGLE);
    if (d->BTN_L1)       m |= PB_BIT(PB_L1);
    if (d->BTN_R1)       m |= PB_BIT(PB_R1);
    if (d->BTN_L2)       m |= PB_BIT(PB_L2);
    if (d->BTN_R2)       m |= PB_BIT(PB_R2);
    if (d->BTN_L3)       m |= PB_BIT(PB_L3);
    if (d->BTN_R3)       m |= PB_BIT(PB_R3);
    if (d->BTN_START)    m |= PB_BIT(PB_START);
    if (d->BTN_SELECT)   m |= PB_BIT(PB_SELECT);
    return m;
}

static uint16_t pad_nes_bits(int port)
{
    padData *d = pad_read(port);
    uint16_t dirs = 0;
    if (d->BTN_UP)     dirs |= NB_UP;
    if (d->BTN_DOWN)   dirs |= NB_DOWN;
    if (d->BTN_LEFT)   dirs |= NB_LEFT;
    if (d->BTN_RIGHT)  dirs |= NB_RIGHT;
    dirs |= stick_nes_bits(d->ANA_L_H, d->ANA_L_V);       /* v1.8.1: palanca izquierda = cruz */
    return map_nes_bits(port, pad_buttons(d), dirs);      /* v1.8.2: botones segun OPCIONES > MANDOS (por defecto, igual que antes) */
}

static uint16_t ui_edges(void)
{
    padData *d = pad_read(0);
    uint16_t c = 0, e;
    if (d->BTN_UP)     c |= UI_UP;
    if (d->BTN_DOWN)   c |= UI_DOWN;
    if (d->BTN_LEFT)   c |= UI_LEFT;
    if (d->BTN_RIGHT)  c |= UI_RIGHT;
    {   /* v1.8.1: palanca izquierda tambien mueve los menus */
        uint16_t sb = stick_nes_bits(d->ANA_L_H, d->ANA_L_V);
        if (sb & NB_UP)    c |= UI_UP;
        if (sb & NB_DOWN)  c |= UI_DOWN;
        if (sb & NB_LEFT)  c |= UI_LEFT;
        if (sb & NB_RIGHT) c |= UI_RIGHT;
    }
    if (d->BTN_CROSS)  c |= UI_OK;
    if (d->BTN_CIRCLE) c |= UI_CANCEL;
    if (d->BTN_START)  c |= UI_START;
    e = c & ~g_ui_prev;
    g_ui_prev = c;
    return e;
}

/* v1.9.5: R3 (clic de la palanca izquierda) abre el menu en partida (antes R2: a un amigo se le escapaba el dedo y el menu abierto
 * frena la partida online). prime=1 solo memoriza el estado actual, para ignorar un R3 que siga apretado al empezar la partida. */
static int exit_pressed(int prime, uint32_t frame)
{
    static int prev;
    padData *d = pad_read(0);
    int now = d->BTN_R3 ? 1 : 0;
    int e = now && !prev;
    (void)frame;
    prev = now;
    return prime ? 0 : e;
}

/* v1.9.6: L2 del mando 1 = captura de pantalla (solo en partida; en OPCIONES > MANDOS el mando 1 no puede asignarse L2).
 * prime=1 solo memoriza el estado actual, para ignorar un L2 que siga apretado al empezar la partida. */
static int shot_pressed(int prime, uint32_t frame)
{
    static int prev;
    padData *d = pad_read(0);
    int now = d->BTN_L2 ? 1 : 0;
    int e = now && !prev;
    (void)frame;
    prev = now;
    return prime ? 0 : e;
}

/* v1.9.7: menus en 1280x720 solo en modo CPU (el de siempre), con pantalla de 640x360 o mas y fuera del AJUSTE DE IMAGEN */
static int hr_usable(void) { return g_cfg.render && !g_adjusting && g_dw >= 640 && g_dh >= 360; }

/* medidas reales de la pantalla de la consola (para que la captura salga del mismo tamano que la imagen del juego) */
static void shot_geometry(int *dw, int *dh, int *z) { *dw = (int)g_dw; *dh = (int)g_dh; *z = g_zoom; }

/* descarta pulsaciones viejas del menu (memoriza lo que esta apretado ahora) */
static void ui_prime(void) { (void)ui_edges(); }

#else /* ------------------------- version de pruebas (PC) ------------- */

static void pump(void) {}
static int hr_usable(void) { const char *e = getenv("NESNET_HR"); return !g_adjusting && !(e && e[0] == '0'); }   /* prueba v1.9.7: NESNET_HR=0 = dibujo viejo */
static void present(void);                 /* definida mas abajo (puede volcar capturas de pantalla) */
static void net_ensure(void) {}

/* Pulsaciones simuladas del menu: u d l r = direcciones, x = OK, o = cancelar, s = START.
 * Al agotarse el guion (si habia uno) la app se cierra, para que las pruebas terminen solas. */
static const char *g_ui_script = "";
static int g_ui_has_script;
static uint32_t g_exit_at = 0xFFFFFFFEu;   /* prueba: frame en el que "se aprieta R2" (NESNET_R2) */
static uint32_t g_exit_at2 = 0xFFFFFFFEu;  /* prueba v1.9.1: segundo R2 (NESNET_R2B) */
static uint16_t ui_edges(void)
{
    char c = *g_ui_script;
    if (!c) { if (g_ui_has_script) g_running = 0; return 0; }
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
static void ui_prime(void) {}
static int exit_pressed(int prime, uint32_t frame) { return !prime && (frame == g_exit_at || frame == g_exit_at2); }
/* prueba v1.9.6: "se aprieta L2" en los cuadros de NESNET_SHOTF=a,b,c (hasta 8) */
static uint32_t g_shot_at[8] = { NO_FRAME, NO_FRAME, NO_FRAME, NO_FRAME, NO_FRAME, NO_FRAME, NO_FRAME, NO_FRAME };
static int shot_pressed(int prime, uint32_t frame)
{
    int k;
    if (prime) return 0;
    for (k = 0; k < 8; k++) if (frame == g_shot_at[k]) return 1;
    return 0;
}
static void shot_geometry(int *dw, int *dh, int *z) { *dw = 1280; *dh = 720; *z = 3; }

/* Capturas de prueba: NESNET_SHOTDIR=carpeta NESNET_SHOTS=3,40,90 (numeros de present()) */
static void dump_ppm(const char *path);
static uint32_t g_present_n;
static void present(void)
{
    const char *dir = getenv("NESNET_SHOTDIR"), *lst = getenv("NESNET_SHOTS");
    heartbeat();
    g_present_n++;
    if (dir && lst) {
        const char *p = lst;
        while (*p) {
            if ((uint32_t)atoi(p) == g_present_n) {
                char path[400];
                snprintf(path, sizeof path, "%s/shot_%u.ppm", dir, (unsigned)g_present_n);
                dump_ppm(path);
            }
            while (*p && *p != ',') p++;
            if (*p == ',') p++;
        }
    }
    g_hr_on = 0;
}

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
    g_vid_fresh = 1;
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

static void audio_cb(int16_t l, int16_t r) { int16_t s2[2]; s2[0] = l; s2[1] = r; au_push(s2, 1); }
static size_t audio_batch_cb(const int16_t *d, size_t frames) { au_push(d, frames); return frames; }
static void input_poll_cb(void) {}
static int16_t input_state_cb(unsigned port, unsigned dev, unsigned idx, unsigned id)
{
    unsigned bit;
    (void)idx;
    if (port > (g_four ? 3u : 1u) || dev != RETRO_DEVICE_JOYPAD) return 0;
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

/* ------------------------------------------------------------------ */
/* Selector de ROMs (v1.7): USRDIR/roms/, reconocidas por su cabecera  */
/* ------------------------------------------------------------------ */
typedef struct { char name[ROM_NAMELEN]; uint32_t size; uint32_t crc; int has_crc; } RomEnt;   /* v1.9: tamano y CRC32 (el CRC se calcula al detenerse el cursor) */
static RomEnt g_roms[ROM_MAX];
static int    g_nroms;

static int name_cmp(const char *a, const char *b)
{
    for (;; a++, b++) {
        int x = (unsigned char)*a, y = (unsigned char)*b;
        if (x >= 'a' && x <= 'z') x -= 32;
        if (y >= 'a' && y <= 'z') y -= 32;
        if (x != y) return x < y ? -1 : 1;
        if (!x) return 0;
    }
}

static int rom_cmp(const void *a, const void *b)
{
    return name_cmp(((const RomEnt *)a)->name, ((const RomEnt *)b)->name);
}

/* 1 si el archivo es una ROM de NES: archivo normal, tamano razonable y cabecera iNES ("NES"+1A) o UNIF */
static int is_nes_file(const char *path)
{
    struct stat st;
    uint8_t h[4];
    FILE *f;
    int ok = 0;
    if (stat(path, &st) != 0 || !S_ISREG(st.st_mode)) return 0;
    if (st.st_size < 32 || st.st_size > 8 * 1024 * 1024) return 0;
    f = fopen(path, "rb");
    if (!f) return 0;
    if (fread(h, 1, 4, f) == 4) {
        if (h[0] == 'N' && h[1] == 'E' && h[2] == 'S' && h[3] == 0x1A) ok = 1;
        else if (h[0] == 'U' && h[1] == 'N' && h[2] == 'I' && h[3] == 'F') ok = 1;
    }
    fclose(f);
    return ok;
}

static void roms_scan(void)
{
    char dir[300], path[420];
    DIR *d;
    struct dirent *e;
    g_nroms = 0;
    snprintf(dir, sizeof dir, "%s/roms", g_dir);
    mkdir(dir, 0777);                    /* si no existe, la crea para que se sepa donde van las ROMs */
    d = opendir(dir);
    if (!d) { logf_("roms: no pude abrir %s (errno=%d)", dir, errno); return; }
    while ((e = readdir(d)) != NULL && g_nroms < ROM_MAX) {
        if (e->d_name[0] == '.') continue;
        if (strlen(e->d_name) >= ROM_NAMELEN) { logf_("roms: nombre demasiado largo, lo salto"); continue; }
        snprintf(path, sizeof path, "%s/%s", dir, e->d_name);
        if (!is_nes_file(path)) continue;
        snprintf(g_roms[g_nroms].name, ROM_NAMELEN, "%s", e->d_name);
        {
            struct stat st;
            g_roms[g_nroms].size = stat(path, &st) == 0 ? (uint32_t)st.st_size : 0;
            g_roms[g_nroms].crc = 0;
            g_roms[g_nroms].has_crc = 0;
        }
        g_nroms++;
    }
    closedir(d);
    if (g_nroms > 1) qsort(g_roms, (size_t)g_nroms, sizeof g_roms[0], rom_cmp);
    logf_("roms: %d ROM(s) en %s", g_nroms, dir);
}

/* Lee la ROM g_roms[idx] y la deja como la activa (g_rom/g_romcrc). 1 = bien */
static int rom_load(int idx)
{
    char path[420];
    uint8_t *buf = NULL;
    size_t sz = 0;
    snprintf(path, sizeof path, "%s/roms/%s", g_dir, g_roms[idx].name);
    if (!read_whole_file(path, &buf, &sz)) { logf_("roms: no pude leer %s", path); return 0; }
    free(g_rom);
    g_rom = buf;
    g_romsz = sz;
    g_romcrc = crc32_buf(g_rom, g_romsz);
    snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s", path);
    snprintf(g_rom_name, sizeof g_rom_name, "%s", g_roms[idx].name);
    logf_("ROM elegida: %s  %u bytes  crc32=%08X", g_rom_name, (unsigned)g_romsz, (unsigned)g_romcrc);
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
    {
        struct retro_system_av_info av;
        memset(&av, 0, sizeof av);
        retro_get_system_av_info(&av);
        if (av.timing.sample_rate >= 8000.0 && av.timing.sample_rate <= 96000.0) g_au_inrate = av.timing.sample_rate;
        logf_("audio: el nucleo entrega %d Hz a %d cuadros/s", (int)g_au_inrate, (int)(av.timing.fps + 0.5));
    }
    g_core_loaded = 1;
    return 1;
}

/* v1.8: copia de core_load() para el modo de 4. Declara los puertos 3 y 4 como mando (GAMEPAD): con eso FCEUmm
 * enciende solo el adaptador Four Score. Los juegos que no lo usan simplemente ignoran los mandos 3 y 4. */
static int core_load4(void)
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
    retro_set_controller_port_device(2, NES_DEV_GAMEPAD);   /* GAMEPAD de FCEUmm */
    retro_set_controller_port_device(3, NES_DEV_GAMEPAD);
    logf_("4 jugadores: puertos 3 y 4 como mando (Four Score)");
    {
        struct retro_system_av_info av;
        memset(&av, 0, sizeof av);
        retro_get_system_av_info(&av);
        if (av.timing.sample_rate >= 8000.0 && av.timing.sample_rate <= 96000.0) g_au_inrate = av.timing.sample_rate;
        logf_("audio: el nucleo entrega %d Hz a %d cuadros/s", (int)g_au_inrate, (int)(av.timing.fps + 0.5));
    }
    g_core_loaded = 1;
    return 1;
}

static void core_unload(void)
{
    if (g_core_loaded) { retro_unload_game(); g_core_loaded = 0; }
}

/* ------------------------------------------------------------------ */
/* v1.9: guardado de bateria (SRAM) - SOLO en el modo SOLO              */
/* Archivo: USRDIR/saves/<CRC32 de la ROM>.srm (asi renombrar la ROM no pierde el guardado).                      */
/* En online NO se carga ni se guarda nada: las dos consolas tienen que empezar con la misma memoria, si no se       */
/* desincronizan, y ademas una partida online no debe pisar tu guardado.                                          */
/* ------------------------------------------------------------------ */
#define SRAM_MAX 0x20000
static uint8_t g_sram_last[SRAM_MAX];     /* lo ultimo escrito en disco (para guardar solo si cambio) */
static size_t  g_sram_lastsz;
static int     g_sram_on;                 /* 1 = esta partida guarda (solo SOLO, y solo si el juego tiene bateria) */

static void sram_path(char *out, size_t cap)
{
    snprintf(out, cap, "%s/saves/%08X.srm", g_dir, (unsigned)g_romcrc);
}

static uint8_t *sram_ptr(size_t *sz)
{
    void *p = retro_get_memory_data(RETRO_MEMORY_SAVE_RAM);
    size_t n = retro_get_memory_size(RETRO_MEMORY_SAVE_RAM);
    if (!p || n == 0 || n > SRAM_MAX) return NULL;
    *sz = n;
    return (uint8_t *)p;
}

/* Llamar justo despues de core_load() en el modo SOLO: carga el guardado si existe */
static void sram_begin(void)
{
    size_t n = 0, fsz = 0;
    uint8_t *p, *buf = NULL;
    char path[420], tmp[440];
    int got;
    g_sram_on = 0; g_sram_lastsz = 0;
    p = sram_ptr(&n);
    if (!p) { logf_("guardado: este juego no usa memoria de bateria"); return; }
    g_sram_on = 1;
    sram_path(path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    got = read_whole_file(path, &buf, &fsz);
    if (!got) got = read_whole_file(tmp, &buf, &fsz);          /* si se corto la luz justo al guardar, queda el .tmp completo */
    if (got) {
        if (fsz == n) { memcpy(p, buf, n); logf_("guardado: cargado %s (%u bytes)", path, (unsigned)n); }
        else {
            char old[450];
            snprintf(old, sizeof old, "%s.old", path);
            remove(old);
            rename(path, old);                                   /* no lo borro: queda como .old */
            logf_("AVISO: el guardado tenia %u bytes y el juego pide %u: lo movi a .old y empiezo de cero", (unsigned)fsz, (unsigned)n);
        }
        free(buf);
    } else {
        logf_("guardado: partida nueva (aun no hay %s)", path);
    }
    memcpy(g_sram_last, p, n);
    g_sram_lastsz = n;
}

/* Escribe el guardado si cambio desde la ultima vez (force = siempre). */
static void sram_save(int force)
{
    size_t n = 0;
    uint8_t *p;
    char dir[320], path[420], tmp[440];
    FILE *f;
    int ok;
    if (!g_sram_on) return;
    p = sram_ptr(&n);
    if (!p || n != g_sram_lastsz) return;
    if (!force && !memcmp(p, g_sram_last, n)) return;
    snprintf(dir, sizeof dir, "%s/saves", g_dir);
    mkdir(dir, 0777);
    sram_path(path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    f = fopen(tmp, "wb");
    if (!f) { logf_("AVISO: no pude crear %s (errno=%d)", tmp, errno); return; }
    ok = fwrite(p, 1, n, f) == n;
    if (fclose(f) != 0) ok = 0;
    if (!ok) { logf_("AVISO: no pude escribir el guardado"); remove(tmp); return; }
    remove(path);
    if (rename(tmp, path) != 0) { logf_("AVISO: no pude renombrar el guardado (queda %s)", tmp); return; }
    memcpy(g_sram_last, p, n);
    logf_("guardado: escrito %s (%u bytes)", path, (unsigned)n);
}

/* ------------------------------------------------------------------ */
/* v1.9.1: estados guardados (savestates) - SOLO en el modo SOLO         */
/* Archivo: USRDIR/saves/<CRC32 de la ROM>_<ranura 1..3>.sta. En online NO existen (las dos consolas tendrian que     */
/* cargar el mismo estado a la vez y se desincronizarian).                                                         */
/* ------------------------------------------------------------------ */
#define STATE_SLOTS 6                     /* v1.9.4: 6 ranuras (antes 3); las 1 a 3 de antes siguen siendo las mismas */
#define STATE_MAX   0x200000
static int  g_state_slot;                 /* ranura elegida en el menu (0..STATE_SLOTS-1); se recuerda mientras la app esta abierta */
static char g_toast[48];                  /* aviso corto sobre la imagen (guardado, cargado, error) */
static int  g_toast_n;

static void toast(const char *s) { snprintf(g_toast, sizeof g_toast, "%s", s); g_toast_n = 150; }

static void state_path(int slot, char *out, size_t cap)
{
    snprintf(out, cap, "%s/saves/%08X_%d.sta", g_dir, (unsigned)g_romcrc, slot + 1);
}

static int state_exists(int slot)
{
    char path[420];
    FILE *f;
    state_path(slot, path, sizeof path);
    f = fopen(path, "rb");
    if (!f) return 0;
    fclose(f);
    return 1;
}

static int state_save(int slot)
{
    size_t n = retro_serialize_size();
    uint8_t *buf;
    char dir[320], path[420], tmp[440];
    FILE *f;
    int ok;
    if (n == 0 || n > STATE_MAX) { logf_("AVISO: estado: el nucleo pide %u bytes (no valido)", (unsigned)n); return 0; }
    buf = (uint8_t *)malloc(n);
    if (!buf) { logf_("AVISO: estado: sin memoria para %u bytes", (unsigned)n); return 0; }
    if (!retro_serialize(buf, n)) { free(buf); logf_("AVISO: estado: el nucleo no pudo guardar"); return 0; }
    snprintf(dir, sizeof dir, "%s/saves", g_dir);
    mkdir(dir, 0777);
    state_path(slot, path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    f = fopen(tmp, "wb");
    if (!f) { free(buf); logf_("AVISO: no pude crear %s (errno=%d)", tmp, errno); return 0; }
    ok = fwrite(buf, 1, n, f) == n;
    if (fclose(f) != 0) ok = 0;
    if (!ok) { free(buf); remove(tmp); logf_("AVISO: no pude escribir el estado"); return 0; }
    remove(path);
    if (rename(tmp, path) != 0) { free(buf); logf_("AVISO: no pude renombrar el estado (queda %s)", tmp); return 0; }
    logf_("estado: guardado ranura %d (%u bytes, crc %08X)", slot + 1, (unsigned)n, (unsigned)crc32_buf(buf, n));
    free(buf);
    return 1;
}

static int state_load(int slot)
{
    size_t n = retro_serialize_size(), fsz = 0;
    uint8_t *buf = NULL;
    char path[420];
    int ok;
    state_path(slot, path, sizeof path);
    if (!read_whole_file(path, &buf, &fsz)) { logf_("estado: la ranura %d esta vacia", slot + 1); return -1; }
    if (fsz != n) {
        free(buf);
        logf_("AVISO: estado: la ranura %d tiene %u bytes y el nucleo pide %u: no la cargo", slot + 1, (unsigned)fsz, (unsigned)n);
        return 0;
    }
    ok = retro_unserialize(buf, fsz) ? 1 : 0;
    logf_("estado: cargada ranura %d (%u bytes, crc %08X) %s", slot + 1, (unsigned)fsz, (unsigned)crc32_buf(buf, fsz), ok ? "OK" : "FALLO");
    free(buf);
    return ok;
}

/* v1.9.4: lee la ranura a memoria (para mandarsela al amigo en ONLINE). 1 = bien (el que llama libera *buf) */
static int state_read(int slot, uint8_t **buf, size_t *n)
{
    size_t want = retro_serialize_size(), fsz = 0;
    char path[420];
    uint8_t *b = NULL;
    state_path(slot, path, sizeof path);
    if (!read_whole_file(path, &b, &fsz)) { logf_("estado: la ranura %d esta vacia", slot + 1); return 0; }
    if (fsz != want || fsz == 0 || fsz > STATE_MAX) {
        free(b);
        logf_("AVISO: estado: la ranura %d tiene %u bytes y el nucleo pide %u: no la cargo", slot + 1, (unsigned)fsz, (unsigned)want);
        return 0;
    }
    *buf = b;
    *n = fsz;
    return 1;
}

/* ------------------------------------------------------------------ */
/* v1.9.6: CAPTURA DE PANTALLA (L2 del mando 1) -> USRDIR/screenshots/<ROM>_NNNN.png                                  */
/* Sale LIMPIA (solo el juego: sin FPS, info de red, avisos ni marco) y del tamano de la pantalla elegida en OPCIONES    */
/* (ORIGINAL 768x720, 4:3 960x720, 16:9 1280x720 en 720p), con el mismo escalado de canvas_blit_cpu, pero SIN el ajuste   */
/* de imagen (tamano / desplazamiento del overscan). Se toma justo despues de emular el cuadro, antes de dibujar textos.   */
/* PNG propio sin librerias: bloques "stored" de deflate (sin compresion), una fila por bloque, escrito en streaming       */
/* (no reserva memoria para la imagen). Solo es local: no toca la red ni el juego (en online cada consola captura lo suyo). */
/* ------------------------------------------------------------------ */
static void shot_geometry(int *dw, int *dh, int *z);

static uint32_t g_png_tab[256];
static int      g_png_tab_ok;

static uint32_t png_crc_upd(uint32_t c, const uint8_t *d, size_t n)
{
    if (!g_png_tab_ok) {
        uint32_t i;
        int k;
        for (i = 0; i < 256; i++) {
            uint32_t v = i;
            for (k = 0; k < 8; k++) v = (v & 1u) ? (0xEDB88320u ^ (v >> 1)) : (v >> 1);
            g_png_tab[i] = v;
        }
        g_png_tab_ok = 1;
    }
    while (n--) c = g_png_tab[(c ^ *d++) & 0xFFu] ^ (c >> 8);
    return c;
}

static void png_adler_upd(uint32_t *a, uint32_t *b, const uint8_t *d, size_t n)
{
    while (n) {
        size_t m = n > 5552 ? 5552 : n;
        n -= m;
        while (m--) { *a += *d++; *b += *a; }
        *a %= 65521u;
        *b %= 65521u;
    }
}

static void png_be32(uint8_t *p, uint32_t v) { p[0] = (uint8_t)(v >> 24); p[1] = (uint8_t)(v >> 16); p[2] = (uint8_t)(v >> 8); p[3] = (uint8_t)v; }

/* Escribe el lienzo 'fb' (256x240) como PNG RGB escalado igual que canvas_blit_cpu (modo mode, ancho de pantalla dw, vertical z).
 * 1 = bien (con el ancho y el alto en outw y outh), 0 = fallo (el archivo parcial se borra) */
static int shot_write_png(const char *path, const uint32_t *fb, int mode, int dw, int z, int *outw, int *outh)
{
    static const uint8_t sig[8]  = { 0x89, 'P', 'N', 'G', 0x0D, 0x0A, 0x1A, 0x0A };
    static const uint8_t iend[12] = { 0, 0, 0, 0, 'I', 'E', 'N', 'D', 0xAE, 0x42, 0x60, 0x82 };
    static uint8_t blk[5 + 1 + 3 * COLMAP_MAX];       /* cabecera del bloque (5) + filtro (1) + pixeles RGB */
    static int cm[COLMAP_MAX];
    int oh = SCR_H * z, ow = screen_out_w(mode, dw, oh, z);
    int rowb, x, y, k, ok, row = 0;
    uint32_t crc, ad_a = 1, ad_b = 0, idat_len;
    uint8_t hd[41], z2[2], tail[4];
    FILE *f;
    if (z < 1 || ow < 1) return 0;
    rowb = 1 + 3 * ow;
    for (x = 0; x < ow; x++) cm[x] = x * SCR_W / ow;
    f = fopen(path, "wb");
    if (!f) return 0;
    memcpy(hd, sig, 8);
    png_be32(hd + 8, 13); memcpy(hd + 12, "IHDR", 4);
    png_be32(hd + 16, (uint32_t)ow); png_be32(hd + 20, (uint32_t)oh);
    hd[24] = 8; hd[25] = 2; hd[26] = 0; hd[27] = 0; hd[28] = 0;                 /* 8 bits, RGB, sin interlace */
    png_be32(hd + 29, ~png_crc_upd(0xFFFFFFFFu, hd + 12, 17));
    idat_len = 2u + (uint32_t)oh * (uint32_t)(5 + rowb) + 4u;                  /* zlib: 2 de cabecera + bloques + 4 de Adler-32 */
    png_be32(hd + 33, idat_len); memcpy(hd + 37, "IDAT", 4);
    ok = fwrite(hd, 1, 41, f) == 41;
    crc = png_crc_upd(0xFFFFFFFFu, hd + 37, 4);
    z2[0] = 0x78; z2[1] = 0x01;
    crc = png_crc_upd(crc, z2, 2);
    ok = ok && fwrite(z2, 1, 2, f) == 2;
    blk[5] = 0;                                                                 /* filtro 0 (sin filtro) */
    for (y = 0; y < SCR_H && ok; y++) {
        const uint32_t *src = fb + y * SCR_W;
        uint8_t *p = blk + 6;
        for (x = 0; x < ow; x++) { uint32_t px = src[cm[x]]; *p++ = (uint8_t)(px >> 16); *p++ = (uint8_t)(px >> 8); *p++ = (uint8_t)px; }
        for (k = 0; k < z && ok; k++) {
            row++;
            blk[0] = (uint8_t)(row == oh ? 1 : 0);                              /* ultimo bloque */
            blk[1] = (uint8_t)(rowb & 0xFF); blk[2] = (uint8_t)((rowb >> 8) & 0xFF);
            blk[3] = (uint8_t)(~rowb & 0xFF); blk[4] = (uint8_t)((~rowb >> 8) & 0xFF);
            ok = fwrite(blk, 1, (size_t)(5 + rowb), f) == (size_t)(5 + rowb);
            crc = png_crc_upd(crc, blk, (size_t)(5 + rowb));
            png_adler_upd(&ad_a, &ad_b, blk + 5, (size_t)rowb);
        }
    }
    png_be32(tail, (ad_b << 16) | ad_a);
    ok = ok && fwrite(tail, 1, 4, f) == 4;
    crc = png_crc_upd(crc, tail, 4);
    png_be32(tail, ~crc);
    ok = ok && fwrite(tail, 1, 4, f) == 4;
    ok = ok && fwrite(iend, 1, 12, f) == 12;
    if (fclose(f) != 0) ok = 0;
    if (!ok) { remove(path); return 0; }
    if (outw) *outw = ow;
    if (outh) *outh = oh;
    return 1;
}

static char g_shot_last[48];                  /* ROM de la ultima captura y su ultimo numero (para no revisar desde el 1 cada vez) */
static int  g_shot_n;

/* Guarda la captura de 'fb'. Devuelve el numero de la captura (1..9999) o 0 si fallo */
static int shot_take(const uint32_t *fb)
{
    char dir[320], base[48], path[420], tmp[440];
    int dw = 1280, dh = 720, z = 3, mode, n, w = 0, h = 0, k = 0;
    uint32_t t0 = now_ms();
    size_t len, dot, j;
    shot_geometry(&dw, &dh, &z);
    (void)dh;
    mode = g_cfg.render ? g_screen : 0;       /* con el dibujo por GPU la pantalla siempre es ORIGINAL */
    snprintf(dir, sizeof dir, "%s/screenshots", g_dir);
    mkdir(dir, 0777);
    /* nombre: la ROM sin extension; solo letras, numeros, - y _ (lo demas pasa a _) */
    len = strlen(g_rom_name);
    dot = len;
    for (j = len; j > 0; j--) if (g_rom_name[j - 1] == '.') { dot = j - 1; break; }
    if (dot == 0) dot = len;
    for (j = 0; j < dot && k < 40; j++) {
        char c = g_rom_name[j];
        base[k++] = (char)(((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '-' || c == '_') ? c : '_');
    }
    base[k] = 0;
    if (!base[0]) snprintf(base, sizeof base, "captura");
    if (strcmp(base, g_shot_last)) { snprintf(g_shot_last, sizeof g_shot_last, "%s", base); g_shot_n = 0; }
    for (n = g_shot_n + 1; n < 10000; n++) {
        snprintf(path, sizeof path, "%s/%s_%04d.png", dir, base, n);
        if (!path_is_valid(path)) break;
    }
    if (n >= 10000) { logf_("AVISO: captura: ya hay 9999 capturas de este juego"); return 0; }
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    if (!shot_write_png(tmp, fb, mode, dw, z, &w, &h)) { logf_("AVISO: captura: no pude escribir %s (errno=%d)", tmp, errno); return 0; }
    remove(path);
    if (rename(tmp, path) != 0) { logf_("AVISO: captura: no pude renombrar (queda %s)", tmp); return 0; }
    g_shot_n = n;
    logf_("captura: guardada %s (%dx%d, pantalla=%s) en %u ms", path, w, h, screen_names[mode], (unsigned)(now_ms() - t0));
    return n;
}

/* Toma la captura de la imagen del juego (g_fb, todavia sin textos) y avisa en pantalla */
static void shot_do(void)
{
    char tb[48];
    int n = shot_take(g_fb);
    if (n > 0) snprintf(tb, sizeof tb, "CAPTURA GUARDADA %04d", n);
    else snprintf(tb, sizeof tb, "NO SE PUDO GUARDAR LA CAPTURA");
    toast(tb);
}

static void step_frame(uint16_t p1, uint16_t p2)
{
    g_pad[0] = p1;
    g_pad[1] = p2;
    retro_run();
}

/* v1.8: copia de step_frame() para 4 mandos */
static void step_frame4(uint16_t p1, uint16_t p2, uint16_t p3, uint16_t p4)
{
    g_pad[0] = p1;
    g_pad[1] = p2;
    g_pad[2] = p3;
    g_pad[3] = p4;
    retro_run();
}

/* ------------------------------------------------------------------ */
/* Red: mensajes de 16 bytes, TCP, poll() con espera propia            */
/* ------------------------------------------------------------------ */
enum { M_HELLO = 1, M_PING, M_PONG, M_CFG, M_START, M_INPUT, M_QUIT, M_REJECT, M_RESET, M_GAME, M_STATE };   /* v1.9.1: M_RESET (frame = cuadro en que ambos reinician); v1.9.2: M_GAME (cambio de juego) */
/* v1.9.4: M_STATE = el host manda un estado guardado: frame = cuadro en que los dos lo cargan, v1 = bytes, v2 = CRC32 de los datos;
 * justo despues de este mensaje de 16 bytes vienen v1 bytes sin marco (ver net_send_raw / net_recv_raw). */
/* v1.9.2: M_GAME, campo 'a': pregunta del host (v1 = CRC32 de la ROM, v2 = tamano) / "la tengo" / "no la tengo" /
 * corte (frame = cuadro en que los dos cambian, v1 = CRC32) / marca de fin de lo viejo (ver game_switch_apply) */
enum { GM_ASK = 1, GM_HAVE, GM_MISS, GM_GO, GM_MARK };

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

/* v1.9.4: bloques grandes sin marco (estados guardados), justo despues de un mensaje M_STATE. net_recv_raw primero vacia lo que
 * net_recv ya dejo leido en g_rx (el mensaje y los primeros bytes pueden llegar juntos). Cada espera se renueva con cada trozo
 * recibido o enviado: se rinde solo si pasan 20 s sin avanzar nada. */
static int net_send_raw(const uint8_t *src, size_t len)
{
    size_t off = 0;
    uint32_t t0 = now_ms();
    while (off < len) {
        int r = fd_wait(g_net, POLLOUT, 100), n;
        size_t chunk = len - off > 16384 ? 16384 : len - off;
        if (r < 0) return 0;
        if (r == 0) { if ((int)(now_ms() - t0) > 20000) return 0; continue; }
        n = (int)send(g_net, (const char *)src + off, chunk, 0);
        if (n <= 0) return 0;
        off += (size_t)n;
        t0 = now_ms();
    }
    return 1;
}

static int net_recv_raw(uint8_t *dst, size_t len)
{
    size_t got = 0;
    uint32_t t0 = now_ms();
    if (g_rxlen > 0) {
        size_t k = (size_t)g_rxlen < len ? (size_t)g_rxlen : len;
        memcpy(dst, g_rx, k);
        memmove(g_rx, g_rx + k, (size_t)g_rxlen - k);
        g_rxlen -= (int)k;
        got = k;
    }
    while (got < len) {
        int r = fd_wait(g_net, POLLIN, 200), n;
        size_t want = len - got > 65536 ? 65536 : len - got;
        if (r < 0) return 0;
        if (r == 0) { if ((int)(now_ms() - t0) > 20000) return 0; continue; }
        n = (int)recv(g_net, (char *)dst + got, (int)want, 0);
        if (n <= 0) return 0;
        got += (size_t)n;
        t0 = now_ms();
    }
    return 1;
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

/* v1.6: diagnostico de connect. kind: 0 ok, 1 sin respuesta (timeout), 2 rechazado o error de red, 3 sin socket */
static int      g_conn_kind;
static int      g_conn_err;
static uint32_t g_conn_ms;

static int tcp_connect(uint32_t ip, int port, int timeout_ms)
{
    struct sockaddr_in a;
    uint32_t t0 = now_ms();
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    g_conn_kind = 0; g_conn_err = 0; g_conn_ms = 0;
    if (fd < 0) { g_conn_kind = 3; g_conn_err = errno; goto fail; }
    sock_nonblock(fd, 1);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(ip);
    if (connect(fd, (struct sockaddr *)&a, sizeof a) < 0) {
        int err = 0, r;
        socklen_t l = sizeof err;
        r = fd_wait(fd, POLLOUT, timeout_ms);
        if (r <= 0) { g_conn_kind = (r == 0) ? 1 : 2; closesocket(fd); goto fail; }
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &l) == 0 && err != 0) {
            g_conn_kind = 2; g_conn_err = err; closesocket(fd); goto fail;
        }
    }
    sock_nonblock(fd, 0);
    sock_nodelay(fd);
    g_conn_ms = now_ms() - t0;
    return fd;
fail:
    g_conn_ms = now_ms() - t0;
    logf_("connect %u.%u.%u.%u:%d FALLO: %s (error=%d) tras %u ms",
          (unsigned)(ip >> 24), (unsigned)((ip >> 16) & 255), (unsigned)((ip >> 8) & 255), (unsigned)(ip & 255), port,
          g_conn_kind == 1 ? "SIN RESPUESTA (timeout)" : g_conn_kind == 3 ? "NO SE PUDO CREAR EL SOCKET" : "RECHAZADO O ERROR DE RED",
          g_conn_err, (unsigned)g_conn_ms);
    return -1;
}

static int tcp_listen(int port)
{
    struct sockaddr_in a;
    int one = 1, rb, rl;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) { logf_("escucha: socket() fallo (errno=%d)", errno); return -1; }
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    rb = bind(fd, (struct sockaddr *)&a, sizeof a);
    rl = rb < 0 ? -1 : listen(fd, 1);
    logf_("escucha: puerto TCP %d  bind=%d listen=%d", port, rb, rl);
    if (rb < 0 || rl < 0) { closesocket(fd); return -1; }
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

/* ------------------------------------------------------------------ */
/* UPnP (v1.6): el host abre su puerto TCP en el router y lee la IP del */
/* router. Los pasos (SSDP -> descripcion del router -> llamadas SOAP)  */
/* siguen el netplay de Melee-PS3 (ps3/net/upnp.c, GPLv2 o posterior),  */
/* que ya conecto entre estas dos casas; aqui es una version propia     */
/* sobre los sockets de NesNet.                                         */
/* ------------------------------------------------------------------ */
typedef struct {
    int      router;      /* un router contesto por UPnP */
    int      opened;      /* el puerto lleva a esta consola */
    int      http;        /* estado HTTP del AddPortMapping (0 = no hubo) */
    int      error;       /* codigo de error UPnP (0 = ninguno) */
    uint32_t public_ip;   /* IP WAN que dice el router (0 = no la dio) */
    uint32_t local_ip;    /* IP de esta consola en la LAN (0 = no se pudo leer) */
} Upnp;

#define UPNP_BUF 12288
static char     g_ubuf[UPNP_BUF];
static uint32_t g_ctl_ip;
static int      g_ctl_port;
static char     g_ctl_path[160], g_ctl_svc[96];
static int      g_upnp_added, g_upnp_port;

#define IP4(ip) (unsigned)((ip) >> 24), (unsigned)(((ip) >> 16) & 255), (unsigned)(((ip) >> 8) & 255), (unsigned)((ip) & 255)

static int ip_privada(uint32_t ip)
{
    return (ip >> 24) == 10 || (ip >> 20) == 0xAC1 || (ip >> 16) == 0xC0A8 || (ip >> 22) == ((100u << 2) | 1) ||
           (ip >> 24) == 127 || (ip >> 16) == 0xA9FE || ip == 0;
}

static void sa_fill(struct sockaddr_in *s, uint32_t ip, int port)
{
    memset(s, 0, sizeof *s);
#ifdef NESNET_PS3
    s->sin_len = sizeof *s;               /* PSL1GHT es BSD: con sin_len=0, sendto falla con ENOENT */
#endif
    s->sin_family = AF_INET;
    s->sin_port = htons((uint16_t)port);
    s->sin_addr.s_addr = htonl(ip);
}

/* IP de esta consola en su red local */
static uint32_t local_ip_get(void)
{
#ifdef NESNET_PS3
    static int loaded;
    union net_ctl_info info;
    if (!loaded) { loaded = 1; sysModuleLoad(SYSMODULE_NETCTL); netCtlInit(); }
    if (netCtlGetInfo(NET_CTL_INFO_IP_ADDRESS, &info) < 0) return 0;
    if (inet_addr(info.ip_address) == INADDR_NONE) return 0;
    return ntohl(inet_addr(info.ip_address));
#else
    const char *e = getenv("NESNET_LOCAL_IP");
    uint32_t ip;
    return (e && parse_ip(e, &ip)) ? ip : 0x7F000001u;
#endif
}

/* Un datagrama UDP y la primera respuesta (en resp). Devuelve los bytes o -1. Sigue atendiendo al sistema (pump). */
static int upnp_udp_ask(uint32_t ip, int port, const char *req, int len, char *resp, int cap, int ms)
{
    struct sockaddr_in s;
    struct timeval tv;
    uint32_t t0;
    int fd, n = -1;
    fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return -1;
    tv.tv_sec = 0; tv.tv_usec = 100000;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    sa_fill(&s, ip, port);
    if (sendto(fd, req, (size_t)len, 0, (struct sockaddr *)&s, sizeof s) == len) {
        t0 = now_ms();
        for (;;) {
            socklen_t sl = sizeof s;
            int r = (int)recvfrom(fd, resp, (size_t)cap, 0, (struct sockaddr *)&s, &sl);
            if (r > 0) { n = r; break; }
            if ((int)(now_ms() - t0) >= ms) break;
            pump();
            if (!g_running) break;
            sleep_ms(2);
        }
    }
    closesocket(fd);
    return n;
}

/* Pide por HTTP/TCP y deja la respuesta (terminada en 0) en g_ubuf. Devuelve los bytes o -1. */
static int upnp_http(uint32_t ip, int port, const char *req, int ms)
{
    int fd, len = 0, n;
    fd = tcp_connect(ip, port, ms);
    if (fd < 0) return -1;
    if (send(fd, req, (int)strlen(req), 0) <= 0) { closesocket(fd); return -1; }
    while (len < UPNP_BUF - 1 && fd_wait(fd, POLLIN, ms) > 0) {
        n = (int)recv(fd, g_ubuf + len, UPNP_BUF - 1 - len, 0);
        if (n <= 0) break;
        len += n;
    }
    closesocket(fd);
    g_ubuf[len] = 0;
    return len > 0 ? len : -1;
}

/* Texto entre <name> y </name> a partir de p; devuelve donde acaba o NULL */
static const char *x_tag(const char *p, const char *name, char *out, size_t cap)
{
    char open[64], close_[64];
    const char *s, *e;
    size_t n;
    snprintf(open, sizeof open, "<%s>", name);
    snprintf(close_, sizeof close_, "</%s>", name);
    s = strstr(p, open);
    if (!s) return NULL;
    e = strstr(s, close_);
    if (!e) return NULL;
    s += strlen(open);
    n = (size_t)(e - s) < cap - 1 ? (size_t)(e - s) : cap - 1;
    memcpy(out, s, n);
    out[n] = 0;
    return e;
}

/* "http://a.b.c.d[:puerto]/ruta" */
static int x_url(const char *url, uint32_t *ip, int *port, char *path, size_t cap)
{
    unsigned a, b, c, d, pt = 80;
    const char *slash;
    if (strncmp(url, "http://", 7) != 0 || sscanf(url + 7, "%u.%u.%u.%u", &a, &b, &c, &d) != 4) return 0;
    if (a > 255 || b > 255 || c > 255 || d > 255) return 0;
    slash = strchr(url + 7, '/');
    sscanf(url + 7, "%*[0-9.]:%u", &pt);
    *ip = (a << 24) | (b << 16) | (c << 8) | d;
    *port = (int)pt;
    snprintf(path, cap, "%s", slash ? slash : "/");
    return 1;
}

static int ci_prefix(const char *s, const char *pre)
{
    for (; *pre; s++, pre++) {
        char x = *s, y = *pre;
        if (x >= 'A' && x <= 'Z') x = (char)(x + 32);
        if (y >= 'A' && y <= 'Z') y = (char)(y + 32);
        if (x != y) return 0;
    }
    return 1;
}

/* Busca el router (SSDP), lee su descripcion y guarda la URL de control. 1 = encontrado */
static int upnp_discover(void)
{
    static const char search[] =
        "M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\nMX: 2\r\n"
        "ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n";
    char url[192], path[160], req[360], type[96], ctl[160];
    uint32_t dip = 0;
    int dport = 0, n;
    const char *p;
    url[0] = 0;
#ifdef NESNET_HOST
    if (getenv("NESNET_UPNP_URL")) snprintf(url, sizeof url, "%s", getenv("NESNET_UPNP_URL"));
#endif
    if (!url[0]) {
        n = upnp_udp_ask(0xEFFFFFFAu, 1900, search, (int)sizeof search - 1, g_ubuf, UPNP_BUF - 1, 2000);
        if (n <= 0) { logf_("upnp: SSDP sin respuesta en 2 s (el router no tiene UPnP o lo bloquea)"); return 0; }
        g_ubuf[n] = 0;
        p = g_ubuf;
        while (p && !ci_prefix(p, "location:")) { p = strchr(p, '\n'); p = p ? p + 1 : NULL; }
        if (!p || sscanf(p + 9, " %191s", url) != 1) { logf_("upnp: la respuesta SSDP no trae LOCATION"); return 0; }
    }
    if (!x_url(url, &dip, &dport, path, sizeof path)) { logf_("upnp: URL de descripcion no valida: %s", url); return 0; }
    snprintf(req, sizeof req, "GET %s HTTP/1.0\r\nHost: %u.%u.%u.%u:%d\r\nConnection: close\r\n\r\n", path, IP4(dip), dport);
    if (upnp_http(dip, dport, req, 3000) <= 0) { logf_("upnp: no pude leer la descripcion del router (%s)", url); return 0; }
    for (p = g_ubuf; (p = x_tag(p, "serviceType", type, sizeof type)) != NULL;) {
        if ((strstr(type, "WANIPConnection") || strstr(type, "WANPPPConnection")) && x_tag(p, "controlURL", ctl, sizeof ctl)) {
            snprintf(g_ctl_svc, sizeof g_ctl_svc, "%s", type);
            g_ctl_ip = dip; g_ctl_port = dport;
            if (ctl[0] == '/') { snprintf(g_ctl_path, sizeof g_ctl_path, "%s", ctl); return 1; }
            if (!strncmp(ctl, "http://", 7)) return x_url(ctl, &g_ctl_ip, &g_ctl_port, g_ctl_path, sizeof g_ctl_path);
            snprintf(g_ctl_path, sizeof g_ctl_path, "/%s", ctl);
            return 1;
        }
    }
    logf_("upnp: el router no ofrece WANIPConnection/WANPPPConnection");
    return 0;
}

/* Una llamada SOAP al router: estado HTTP (o -1); respuesta en g_ubuf; error UPnP en *err */
static int upnp_soap(const char *action, const char *args, int *err)
{
    static char body[1024], req[1792];
    char code[16], status[8];
    snprintf(body, sizeof body,
             "<?xml version=\"1.0\"?>\r\n<s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" "
             "s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><u:%s xmlns:u=\"%s\">%s</u:%s>"
             "</s:Body></s:Envelope>\r\n", action, g_ctl_svc, args, action);
    snprintf(req, sizeof req,
             "POST %s HTTP/1.0\r\nHost: %u.%u.%u.%u:%d\r\nContent-Type: text/xml; charset=\"utf-8\"\r\n"
             "Content-Length: %d\r\nSOAPAction: \"%s#%s\"\r\nConnection: close\r\n\r\n%s",
             g_ctl_path, IP4(g_ctl_ip), g_ctl_port, (int)strlen(body), g_ctl_svc, action, body);
    *err = 0;
    if (upnp_http(g_ctl_ip, g_ctl_port, req, 3000) <= 0 || sscanf(g_ubuf, "HTTP/%*s %7s", status) != 1) return -1;
    if (x_tag(g_ubuf, "errorCode", code, sizeof code)) *err = atoi(code);
    return atoi(status);
}

/* Abre el puerto TCP en el router hacia esta consola y lee la IP del router */
static void upnp_open(int port, Upnp *u)
{
    char args[640], ip[20], value[40];
    unsigned a, b, c, d;
    int status, err = 0, lease = 7200;

    memset(u, 0, sizeof *u);
    u->local_ip = local_ip_get();
    logf_("upnp: IP local de la consola = %u.%u.%u.%u", IP4(u->local_ip));
    if (!upnp_discover()) return;
    u->router = 1;
    logf_("upnp: router en %u.%u.%u.%u:%d servicio=%s", IP4(g_ctl_ip), g_ctl_port, g_ctl_svc);
    if (upnp_soap("GetExternalIPAddress", "", &err) == 200 && x_tag(g_ubuf, "NewExternalIPAddress", value, sizeof value) &&
        sscanf(value, "%u.%u.%u.%u", &a, &b, &c, &d) == 4 && a < 256 && b < 256 && c < 256 && d < 256) {
        u->public_ip = (a << 24) | (b << 16) | (c << 8) | d;
        logf_("upnp: IP WAN del router = %u.%u.%u.%u%s", IP4(u->public_ip), ip_privada(u->public_ip) ? "  (PRIVADA: CGNAT o doble NAT)" : "");
    } else {
        logf_("upnp: el router no dio su IP WAN (error=%d)", err);
    }
    if (!u->local_ip) { logf_("upnp: no conozco la IP local, no abro el puerto"); return; }
    snprintf(ip, sizeof ip, "%u.%u.%u.%u", IP4(u->local_ip));
    for (;;) {
        snprintf(args, sizeof args,
                 "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>"
                 "<NewInternalPort>%d</NewInternalPort><NewInternalClient>%s</NewInternalClient><NewEnabled>1</NewEnabled>"
                 "<NewPortMappingDescription>NesNet</NewPortMappingDescription><NewLeaseDuration>%d</NewLeaseDuration>",
                 port, port, ip, lease);
        status = upnp_soap("AddPortMapping", args, &err);
        if (err == 725 && lease != 0) { lease = 0; continue; }      /* el router solo acepta reglas permanentes */
        break;
    }
    u->http = status; u->error = err;
    if (status == 200) {
        u->opened = 1; g_upnp_added = 1; g_upnp_port = port;
    } else if (err == 718) {
        /* ya existia una regla: sirve si lleva a esta consola */
        snprintf(args, sizeof args,
                 "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>", port);
        u->opened = upnp_soap("GetSpecificPortMappingEntry", args, &err) == 200 &&
                    x_tag(g_ubuf, "NewInternalClient", value, sizeof value) && !strcmp(value, ip);
    }
    logf_("upnp: AddPortMapping TCP %d -> %s: http=%d error=%d abierto=%d", port, ip, status, u->error, u->opened);
}

/* Quita la regla que puso upnp_open (si puso alguna) */
static void upnp_close(void)
{
    char args[256];
    int err = 0;
    if (!g_upnp_added) return;
    g_upnp_added = 0;
    snprintf(args, sizeof args,
             "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>", g_upnp_port);
    upnp_soap("DeletePortMapping", args, &err);
    logf_("upnp: regla del puerto %d quitada del router (error=%d)", g_upnp_port, err);
}

/* v1.9.1: Codigo = IP publica del host como numero, en decimal de 10 digitos (con ceros a la izquierda).
 * El puerto ya NO viaja en el codigo: los dos usan el de config.txt (7777 por defecto). */
static void code_encode(uint32_t ip, int port, char *out)
{
    uint32_t v = ip;
    int i;
    (void)port;
    for (i = 9; i >= 0; i--) { out[i] = (char)('0' + (int)(v % 10)); v /= 10; }
    out[10] = 0;
}

static int code_decode(const char *code, uint32_t *ip, int *port)
{
    uint64_t v = 0;
    int i, n = 0;
    for (i = 0; code[i]; i++) {
        if (code[i] < '0' || code[i] > '9') continue;     /* ignora espacios y guiones */
        v = v * 10 + (uint64_t)(code[i] - '0');
        n++;
        if (n > 10) return 0;
    }
    if (n != 10 || v >= (1ULL << 32)) return 0;
    *ip = (uint32_t)v;
    *port = g_cfg.port;
    return *port > 0 && *ip != 0;
}

/* "1234567890" -> "123 456 7890" (solo para mostrarlo en pantalla) */
static void code_pretty(const char *code, char *out)
{
    int i, k = 0;
    for (i = 0; code[i] && i < 10; i++) {
        if (i == 3 || i == 6) out[k++] = ' ';
        out[k++] = code[i];
    }
    out[k] = 0;
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

/* v1.8: COPIA de handshake_host / handshake_client para el modo de 4 (protocolo PROTO_VER4). Misma logica. */
static int handshake_host4(int *outD)
{
    Msg m;
    uint32_t rtt[5];
    int i, D, r;

    r = net_recv(&m, 10000);
    if (r <= 0 || m.type != M_HELLO) { g_err = "EL AMIGO NO RESPONDIO"; return 0; }
    if (m.frame != PROTO_VER4) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 1; net_send(&m);
        g_err = "AMIGO EN OTRO MODO O VERSION DISTINTA"; return 0;
    }
    if (m.v1 != g_romcrc) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 2; net_send(&m);
        g_err = "ROM DISTINTA A LA DEL AMIGO"; return 0;
    }
    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = PROTO_VER4; m.v1 = g_romcrc;
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

static int handshake_client4(int *outD)
{
    Msg m;
    int r, D = 0, haveD = 0;
    uint32_t t0;

    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = PROTO_VER4; m.v1 = g_romcrc;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    r = net_recv(&m, 10000);
    if (r <= 0) { g_err = "EL HOST NO RESPONDIO"; return 0; }
    if (m.type == M_REJECT) { g_err = (m.v1 == 2) ? "ROM DISTINTA A LA DEL HOST" : "ESA SALA NO ES DE 4 (O VERSION DISTINTA)"; return 0; }
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

/* v1.7: mini menu de salida (se abre con R2). Devuelve 1 si confirma salir (X), 0 si sigue jugando (O).
 * Dibuja encima de la imagen del juego y la restaura al cerrar. */
static uint32_t g_fb_save[SCR_W * SCR_H];

static int exit_menu(int online) __attribute__((unused));
static int exit_menu(int online)
{
    int r = -1, x, y;
    memcpy(g_fb_save, g_fb, sizeof g_fb);
    g_stage = "menu-salir";
    ui_prime();
    while (g_running && r < 0) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_OK) r = 1;
        else if (e & UI_CANCEL) r = 0;
        for (y = 76; y < 164; y++)
            for (x = 20; x < 236; x++)
                g_fb[y * SCR_W + x] = (y < 78 || y >= 162 || x < 22 || x >= 234) ? 0xFFFFFFFF : 0xFF101838;
        ui_center(90, "SALIR DE LA PARTIDA?", 1, 0xFFFFFFFF);
        ui_center(116, "X: SI      O: NO", 1, 0xFFFFD040);
        if (online) ui_center(138, "TERMINA LA PARTIDA PARA LOS DOS", 1, 0xFFFFC040);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    memcpy(g_fb, g_fb_save, sizeof g_fb);
    g_stage = "juego";
    return r == 1;
}

/* v1.9.2: mientras hay una partida online abierta, los menus (R2 y el selector de juego) mandan un aviso corto (M_PING, que
 * la partida ignora) cada ~1 s: el otro lado solo se rinde tras 15 s sin recibir nada, y un menu abierto mas tiempo lo cortaba. */
static int      g_ka_on;                 /* 1 = hay partida online abierta */
static uint32_t g_ka_last;
static void ui_keepalive(void)
{
    uint32_t now;
    if (!g_ka_on || g_net < 0) return;
    now = now_ms();
    if (now - g_ka_last < 1000) return;
    g_ka_last = now;
    { Msg k; memset(&k, 0, sizeof k); k.type = M_PING; k.v1 = 0xFFFFFFFFu; (void)net_send(&k); }
}

static int ui_rom_select(int pick_only);     /* v1.9.2: definido mas abajo; con pick_only = 1 solo elige (no carga) */
static void ui_show(const char *l1, const char *l2, const char *l3);

enum { MK_CONT, MK_SAVE, MK_LOAD, MK_GAME, MK_RESET, MK_EXIT };

/* v1.9.1: menu de R2.
 *   SOLO:   CONTINUAR / GUARDAR ESTADO / CARGAR ESTADO / REINICIAR EL JUEGO / SALIR DE LA PARTIDA
 *   ONLINE: CONTINUAR / REINICIAR EL JUEGO / SALIR DE LA PARTIDA (reiniciar y salir valen para los dos; sin estados)
 *   v1.9.2: el HOST en online tiene ademas CAMBIAR DE JUEGO (despues de CONTINUAR).
 *   v1.9.4: el HOST en online tiene tambien GUARDAR ESTADO / CARGAR ESTADO (6 ranuras, las mismas que en SOLO); el invitado no.
 * Reiniciar, salir, cargar y sobreescribir piden confirmar con X.
 * Devuelve 0 = seguir jugando, 1 = salir, 2 = reiniciar, 3 = cambiar de juego, 10+n = guardar en la ranura n, 20+n = cargar la ranura n (n = 0..STATE_SLOTS-1). */
static int solo_menu(int online, int host)
{
    int kinds[6], nk = 0, sel = 0, r = -1, confirm = -1, x, y, i;
    int st = !online || host;                 /* v1.9.4: online, solo el HOST ve guardar/cargar estado */
    int ex[STATE_SLOTS];
    const char *note = NULL;
    kinds[nk++] = MK_CONT;
    if (st) { kinds[nk++] = MK_SAVE; kinds[nk++] = MK_LOAD; }
    if (online && host) kinds[nk++] = MK_GAME;
    kinds[nk++] = MK_RESET; kinds[nk++] = MK_EXIT;
    for (i = 0; i < STATE_SLOTS; i++) ex[i] = st ? state_exists(i) : 0;
    memcpy(g_fb_save, g_fb, sizeof g_fb);
    g_bd_dirty = 1;
    g_stage = "menu-solo";
    ui_prime();
    while (g_running && r < 0) {
        uint16_t e;
        int k;
        pump();
        ui_keepalive();
        e = ui_edges();
        if (confirm >= 0) {
            if (e & UI_OK) {
                if (confirm == MK_RESET) r = 2;
                else if (confirm == MK_EXIT) r = 1;
                else if (confirm == MK_SAVE) r = 10 + g_state_slot;
                else r = 20 + g_state_slot;
            } else if (e & UI_CANCEL) confirm = -1;
        } else {
            if (e & UI_UP)   { sel = (sel + nk - 1) % nk; note = NULL; }
            if (e & UI_DOWN) { sel = (sel + 1) % nk; note = NULL; }
            k = kinds[sel];
            if ((k == MK_SAVE || k == MK_LOAD) && (e & (UI_LEFT | UI_RIGHT))) {
                g_state_slot = (g_state_slot + ((e & UI_RIGHT) ? 1 : STATE_SLOTS - 1)) % STATE_SLOTS;
                note = NULL;
            }
            if (e & UI_CANCEL) r = 0;
            else if (e & (UI_OK | UI_START)) {
                if (k == MK_CONT) r = 0;
                else if (k == MK_SAVE) { if (ex[g_state_slot]) confirm = MK_SAVE; else r = 10 + g_state_slot; }
                else if (k == MK_LOAD) { if (ex[g_state_slot]) confirm = MK_LOAD; else note = "ESA RANURA ESTA VACIA"; }
                else if (k == MK_GAME) r = 3;          /* el selector de juegos hace de confirmacion (O: volver) */
                else confirm = k;
            }
        }
        if (hr_usable()) hr_backdrop(g_fb_save);     /* v1.9.7: juego oscurecido + cuadro, a 1280x720 */
        else
        for (y = 46; y < 198; y++)
            for (x = 20; x < 236; x++)
                g_fb[y * SCR_W + x] = (y < 48 || y >= 196 || x < 22 || x >= 234) ? 0xFFFFFFFF : 0xFF101838;
        if (g_hr_on) {
            static const HHint hs[2] = { { "X", "ELEGIR", HC_BX }, { "O", "SEGUIR", HC_BO } };
            static const HHint hc[2] = { { "X", "SÍ", HC_BX }, { "O", "NO", HC_BO } };
            if (confirm >= 0) {
                char l[48];
                const char *m2 = NULL, *m3 = NULL;
                uint32_t c2 = HC_DIM;
                if (confirm == MK_RESET) { snprintf(l, sizeof l, "¿REINICIAR EL JUEGO?"); m2 = online ? "Se reinicia para los dos" : "Lo guardado no se borra"; if (online) c2 = HC_AMBER; }
                else if (confirm == MK_EXIT) { snprintf(l, sizeof l, "¿SALIR DE LA PARTIDA?"); if (online) { m2 = "Termina la partida para los dos"; c2 = HC_AMBER; } }
                else if (confirm == MK_SAVE) snprintf(l, sizeof l, "¿SOBREESCRIBIR LA RANURA %d?", g_state_slot + 1);
                else {
                    snprintf(l, sizeof l, "¿CARGAR LA RANURA %d?", g_state_slot + 1);
                    m2 = online ? "Se pierde lo que llevan los dos" : "Se pierde lo que llevas"; c2 = HC_AMBER;
                    if (online) m3 = "Se envía al amigo (tarda unos segundos)";
                }
                hr_textc(640, 330, l, FS_L, HC_WHITE);
                if (m2) hr_textc(640, 392, m2, FS_M, c2);
                if (m3) hr_textc(640, 436, m3, FS_S, HC_DIM);
                hr_hints(hc, 2);
            } else {
                const char *rows[6];
                char rl[6][48];
                const char *hl = NULL;
                for (i = 0; i < nk; i++) {
                    switch (kinds[i]) {
                    case MK_CONT:  snprintf(rl[i], sizeof rl[i], "CONTINUAR"); break;
                    case MK_SAVE:  snprintf(rl[i], sizeof rl[i], "GUARDAR ESTADO < %d >", g_state_slot + 1); break;
                    case MK_LOAD:  snprintf(rl[i], sizeof rl[i], "CARGAR ESTADO < %d >%s", g_state_slot + 1, ex[g_state_slot] ? "" : " (vacía)"); break;
                    case MK_GAME:  snprintf(rl[i], sizeof rl[i], "CAMBIAR DE JUEGO"); break;
                    case MK_RESET: snprintf(rl[i], sizeof rl[i], "REINICIAR EL JUEGO"); break;
                    default:       snprintf(rl[i], sizeof rl[i], "SALIR DE LA PARTIDA"); break;
                    }
                    rows[i] = rl[i];
                }
                hr_text(322, 176, "MENÚ", FS_H, HC_YEL, 3);
                hr_rows(312, 200, 656, rows, nk, sel, 0, 56);
                if (kinds[sel] == MK_SAVE || kinds[sel] == MK_LOAD) hl = "IZQ/DER: cambiar de ranura";
                else if (online && kinds[sel] == MK_GAME) hl = "Se le pregunta antes a tu amigo";
                else if (online) hl = "Reiniciar y salir: para los dos";
                if (note) hr_text(322, 580, "Esa ranura está vacía", FS_S, HC_AMBER, 2);
                else if (hl) hr_text(322, 580, hl, FS_S, HC_DIM, 2);
                hr_hints(hs, 2);
            }
        } else if (confirm >= 0) {
            char l[40];
            if (confirm == MK_RESET) {
                ui_center(88, "REINICIAR EL JUEGO?", 1, 0xFFFFFFFF);
                ui_center(108, online ? "SE REINICIA PARA LOS DOS" : "LO GUARDADO NO SE BORRA", 1, online ? 0xFFFFC040 : 0xFFC0C0FF);
            } else if (confirm == MK_EXIT) {
                ui_center(88, "SALIR DE LA PARTIDA?", 1, 0xFFFFFFFF);
                if (online) ui_center(108, "TERMINA LA PARTIDA PARA LOS DOS", 1, 0xFFFFC040);
            } else if (confirm == MK_SAVE) {
                snprintf(l, sizeof l, "SOBREESCRIBIR LA RANURA %d?", g_state_slot + 1);
                ui_center(88, l, 1, 0xFFFFFFFF);
            } else {
                snprintf(l, sizeof l, "CARGAR LA RANURA %d?", g_state_slot + 1);
                ui_center(88, l, 1, 0xFFFFFFFF);
                ui_center(108, online ? "SE PIERDE LO QUE LLEVAN LOS DOS" : "SE PIERDE LO QUE LLEVAS", 1, 0xFFFFC040);
                if (online) ui_center(120, "SE ENVIA AL AMIGO (TARDA UNOS SEGUNDOS)", 1, 0xFFC0C0FF);
            }
            ui_center(136, "X: SI      O: NO", 1, 0xFFFFD040);
        } else {
            ui_center(56, "MENU", 1, 0xFFFFD040);
            for (i = 0; i < nk; i++) {
                char l[48];
                switch (kinds[i]) {
                case MK_CONT:  snprintf(l, sizeof l, "%s", "CONTINUAR"); break;
                case MK_SAVE:  snprintf(l, sizeof l, "GUARDAR ESTADO < %d >", g_state_slot + 1); break;
                case MK_LOAD:  snprintf(l, sizeof l, "CARGAR ESTADO < %d >%s", g_state_slot + 1, ex[g_state_slot] ? "" : " (VACIA)"); break;
                case MK_GAME:  snprintf(l, sizeof l, "%s", "CAMBIAR DE JUEGO"); break;
                case MK_RESET: snprintf(l, sizeof l, "%s", "REINICIAR EL JUEGO"); break;
                default:       snprintf(l, sizeof l, "%s", "SALIR DE LA PARTIDA"); break;
                }
                {
                    char l2[56];
                    snprintf(l2, sizeof l2, "%s %s", i == sel ? ">" : " ", l);
                    ui_center(68 + i * 14, l2, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
                }
            }
            if (note) ui_center(154, note, 1, 0xFFFFC040);
            ui_center(168, "ARRIBA/ABAJO + X   O: SEGUIR", 1, 0xFF8080A0);
            if (kinds[sel] == MK_SAVE || kinds[sel] == MK_LOAD) ui_center(181, "IZQ/DER: CAMBIAR DE RANURA", 1, 0xFF8080A0);
            else if (online && kinds[sel] == MK_GAME) ui_center(181, "SE LE PREGUNTA ANTES A TU AMIGO", 1, 0xFF8080A0);
            else if (online) ui_center(181, "REINICIAR Y SALIR: PARA LOS DOS", 1, 0xFF8080A0);
        }
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    memcpy(g_fb, g_fb_save, sizeof g_fb);
    g_stage = "juego";
    return r < 0 ? 0 : r;
}

/* role: 0 = host (P1), 1 = cliente (P2), -1 = local directo (2 mandos),
 *       -2 = referencia de pruebas: local con el mismo retraso D     */
/* v1.9: info de red en partida (solo dibujo; no toca la red). Mide cuanto tarda cada cuadro: si el juego tiene que
 * esperar al otro lado, el cuadro tarda mas de 24 ms (a 60 cuadros por segundo lo normal son 17 ms). */
static uint32_t g_ni_last, g_ni_t0, g_ni_n, g_ni_stall, g_ni_fps, g_ni_st;

static void netinfo_tick(void)
{
    uint32_t now = now_ms();
    if (g_ni_last && now - g_ni_last > 24 && now - g_ni_last < 1000) g_ni_stall++;   /* >1 s = menu abierto, no cuenta */
    g_ni_last = now;
    g_ni_n++;
    if (g_ni_t0 == 0 || now - g_ni_t0 >= 1000) {
        if (g_ni_t0) { g_ni_fps = g_ni_n; g_ni_st = g_ni_stall; }
        g_ni_n = 0; g_ni_stall = 0; g_ni_t0 = now;
    }
}

/* v1.9.2: FPS abajo a la derecha (OPCIONES > FPS EN PANTALLA). Usa la misma medicion de netinfo_tick (cuadros por segundo reales,
 * incluida la espera por el otro lado); el primer segundo sale "--". Solo dibujo: no toca la red ni el juego. */
static void ui_fps(void)
{
    char fp[16];
    int x0, x1, y0, y1, x, y;
    if (g_ni_fps) snprintf(fp, sizeof fp, "FPS %u", (unsigned)g_ni_fps); else snprintf(fp, sizeof fp, "FPS --");
    x0 = SCR_W - (int)strlen(fp) * 6 - 5; x1 = SCR_W; y0 = SCR_H - 13; y1 = SCR_H;        /* recuadro negro para que se lea sobre cualquier juego */
    for (y = y0; y < y1; y++) for (x = x0; x < x1; x++) g_fb[y * SCR_W + x] = 0xFF000000u;
    ui_text(SCR_W - (int)strlen(fp) * 6 - 3, SCR_H - 12, fp, 1, 0xFF80FF80);
}

static int netinfo_show(uint32_t frame)
{
    if (g_desyncs) return 1;                 /* el aviso rojo de desync siempre sale */
    if (g_netinfo == 2) return 0;
    if (g_netinfo == 1) return 1;
    return frame < 300;                      /* por defecto: como siempre, los primeros ~5 s */
}

/* v1.9.1: reinicios sincronizados. Quien pide reiniciar manda M_RESET con frame = F (= su cuadro actual + D) ANTES de su
 * entrada de ese cuadro; por el orden del TCP el otro lado lo lee antes de poder pasar del cuadro F, asi los dos llaman a
 * retro_reset() justo antes de emular el cuadro F. Si piden los dos a la vez, cada reinicio tiene su propio F. */
#define RST_MAX 4
static void rst_add(uint32_t *rst, uint32_t f)
{
    int k;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == f) return;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == NO_FRAME) { rst[k] = f; return; }
}
static int rst_due(uint32_t *rst, uint32_t frame)
{
    int k, due = 0;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == frame) { rst[k] = NO_FRAME; due = 1; }
    return due;
}
#ifdef NESNET_HOST
static uint32_t g_ref_reset[2] = { NO_FRAME, NO_FRAME };   /* pruebas: cuadros en que la referencia reinicia (NESNET_RESET_REF=a,b) */
#endif

/* ------------------------------------------------------------------ */
/* v1.9.2: CAMBIAR DE JUEGO en partida online (lo pide el HOST desde R2; vale para 1vs1 y para el modo de 4).        */
/*  1) El host elige la ROM en el selector (no la carga) y manda GM_ASK con su CRC32 y tamano. La partida SIGUE.        */
/*  2) El otro lado busca esa ROM en su carpeta roms (por CRC32, no por nombre) y contesta GM_HAVE o GM_MISS.          */
/*     Si no la tiene, el host avisa en pantalla y nadie cambia nada.                                                  */
/*  3) Con GM_HAVE el host manda GM_GO con el cuadro de corte S = su cuadro + D + 1 (igual que el reinicio de la        */
/*     v1.9.1: por el orden del TCP el otro lado lo lee antes de poder pasar de S) y los dos terminan la partida en    */
/*     ese cuadro SIN avisar de salida. Despues cada lado manda GM_MARK y descarta lo que llegue hasta recibir la del    */
/*     otro (entradas viejas ya adelantadas), carga la ROM, comprueba el CRC32 y empieza una partida nueva con el mismo  */
/*     delay D (sin repetir el handshake). Lo de antes (entradas, desync, reinicio) no cambia.                           */
/* ------------------------------------------------------------------ */
typedef struct {
    int      asked;      /* host: ya mando la pregunta y espera la respuesta */
    uint32_t asked_ms;   /* host: cuando la mando */
    int      have;       /* el que se une: ya contesto que si tiene la ROM */
    uint32_t go;         /* cuadro del corte (NO_FRAME = ninguno) */
    int      mark_rx;    /* ya llego la marca GM_MARK del otro lado (el bucle de la partida la puede leer antes de salir) */
} GameSw;
static GameSw   g_gsw;
static char     g_sw_name[ROM_NAMELEN];   /* ROM nueva: nombre del archivo en roms/ */
static uint32_t g_sw_crc, g_sw_size;
static int      g_sw_pending;             /* 1 = el bucle termino por un cambio de juego: run_online / run_online4 hacen el corte */
static char     g_pick_name[ROM_NAMELEN]; /* resultado de ui_rom_select(1) */
static uint32_t g_pick_crc, g_pick_size;

/* Busca en USRDIR/roms la ROM con ese CRC32 y tamano (solo lee los archivos que tienen ese tamano). 1 = la encontro */
static int rom_find_crc(uint32_t crc, uint32_t size, char *name_out)
{
    int i;
    roms_scan();
    for (i = 0; i < g_nroms; i++) {
        uint8_t *b = NULL;
        size_t bs = 0;
        char rp[420];
        uint32_t c;
        if (g_roms[i].size != size) continue;
        snprintf(rp, sizeof rp, "%s/roms/%s", g_dir, g_roms[i].name);
        if (!read_whole_file(rp, &b, &bs)) continue;
        c = crc32_buf(b, bs);
        free(b);
        if (c == crc && bs == size) { snprintf(name_out, ROM_NAMELEN, "%s", g_roms[i].name); return 1; }
    }
    return 0;
}

/* Atiende un M_GAME que llega durante la partida. role: 0 = host, 1 = el que se une; frame = cuadro actual de este lado.
 * 0 = fallo al mandar la respuesta (el que llama lo trata como conexion caida) */
static int gsw_on_msg(const Msg *m, int role, uint32_t frame, int D)
{
    Msg r;
    memset(&r, 0, sizeof r);
    r.type = M_GAME;
    if (role == 1 && m->a == GM_ASK) {
        char nm[ROM_NAMELEN];
        r.v1 = m->v1;
        if (g_gsw.go == NO_FRAME && rom_find_crc(m->v1, m->v2, nm)) {
            snprintf(g_sw_name, sizeof g_sw_name, "%s", nm);
            g_sw_crc = m->v1; g_sw_size = m->v2; g_gsw.have = 1;
            r.a = GM_HAVE;
            logf_("cambio de juego: tengo la ROM %s (crc32 %08X)", nm, (unsigned)m->v1);
        } else {
            r.a = GM_MISS;
            logf_("cambio de juego: NO tengo la ROM (crc32 %08X)", (unsigned)m->v1);
        }
        return net_send(&r);
    }
    if (role == 0 && m->a == GM_HAVE && g_gsw.asked && m->v1 == g_sw_crc) {
        uint32_t S = frame + (uint32_t)D + 1;
        g_gsw.asked = 0; g_gsw.go = S;
        r.a = GM_GO; r.frame = S; r.v1 = g_sw_crc;
        logf_("cambio de juego: el amigo tiene la ROM; los dos cambian a %s en el frame %u (ahora %u)", g_sw_name, (unsigned)S, (unsigned)frame);
        return net_send(&r);
    }
    if (role == 0 && m->a == GM_MISS && g_gsw.asked && m->v1 == g_sw_crc) {
        g_gsw.asked = 0;
        toast("TU AMIGO NO TIENE ESA ROM");
        logf_("cambio de juego: el amigo NO tiene la ROM %s", g_sw_name);
        return 1;
    }
    if (m->a == GM_MARK) {
        /* El otro lado ya salio de su partida. Despues de su marca no manda NADA hasta recibir la mia, asi que no hay datos
         * de la partida nueva mezclados con los de la vieja. Solo se anota: game_switch_apply no la espera de nuevo. */
        g_gsw.mark_rx = 1;
        return 1;
    }
    if (role == 1 && m->a == GM_GO && g_gsw.have && m->v1 == g_sw_crc) {
        g_gsw.have = 0; g_gsw.go = m->frame;
        logf_("cambio de juego: el host manda cambiar a %s en el frame %u (ahora %u)", g_sw_name, (unsigned)m->frame, (unsigned)frame);
        return 1;
    }
    return 1;
}

/* Host: abre el selector de juegos y, si elige uno distinto del actual, le pregunta al amigo. 0 = fallo al mandar */
static int gsw_ask_host(void)
{
    Msg q;
    if (g_gsw.asked || g_gsw.go != NO_FRAME) { toast("ESPERA: YA SE LE PREGUNTO"); return 1; }
#ifdef NESNET_HOST
    if (getenv("NESNET_STALL_MS")) {                              /* prueba: menu abierto mucho rato (comprueba el aviso de ui_keepalive) */
        uint32_t t0 = now_ms(), lim = (uint32_t)atoi(getenv("NESNET_STALL_MS"));
        while (g_running && now_ms() - t0 < lim) { pump(); ui_keepalive(); sleep_ms(50); }
    }
#endif
    if (!ui_rom_select(1)) return 1;                              /* volvio sin elegir */
    if (g_pick_crc == g_romcrc) { toast("YA ESTAS CON ESE JUEGO"); return 1; }
    snprintf(g_sw_name, sizeof g_sw_name, "%s", g_pick_name);
    g_sw_crc = g_pick_crc; g_sw_size = g_pick_size;
    memset(&q, 0, sizeof q);
    q.type = M_GAME; q.a = GM_ASK; q.v1 = g_sw_crc; q.v2 = g_sw_size;
    g_gsw.asked = 1; g_gsw.asked_ms = now_ms();
    toast("PREGUNTANDO A TU AMIGO...");
    logf_("cambio de juego: pregunto por %s (%u bytes, crc32 %08X)", g_sw_name, (unsigned)g_sw_size, (unsigned)g_sw_crc);
    return net_send(&q);
}

/* Despues de que session_loop termino por un cambio de juego (g_sw_pending), en las DOS consolas: marca de fin de lo viejo
 * (descarta lo que llegue hasta recibir la del otro), carga la ROM nueva y comprueba su CRC32. 1 = listo para la partida nueva */
static int game_switch_apply(void)
{
    Msg m;
    uint32_t t0 = now_ms();
    int i;
    ui_show("CAMBIANDO DE JUEGO...", g_sw_name, NULL);
    memset(&m, 0, sizeof m); m.type = M_GAME; m.a = GM_MARK;
    if (!net_send(&m)) { g_err = "SE PERDIO LA CONEXION"; return 0; }
    while (!g_gsw.mark_rx) {                                      /* si la marca ya llego durante la partida, no hay nada que esperar */
        int r = net_recv(&m, 100);
        if (r < 0) { g_err = "SE PERDIO LA CONEXION"; return 0; }
        if (r > 0) {
            if (m.type == M_GAME && m.a == GM_MARK) break;
            if (m.type == M_QUIT) { g_err = "EL AMIGO SALIO DE LA PARTIDA"; return 0; }
            continue;                                             /* entradas viejas y avisos: se descartan */
        }
        if (!g_running) return 0;
        if (now_ms() - t0 > 15000) { g_err = "EL AMIGO NO RESPONDE (15 S)"; return 0; }
    }
    for (i = 0; i < g_nroms; i++) if (!strcmp(g_roms[i].name, g_sw_name)) break;
    if (i >= g_nroms) { roms_scan(); for (i = 0; i < g_nroms; i++) if (!strcmp(g_roms[i].name, g_sw_name)) break; }
    if (i >= g_nroms || !rom_load(i)) { g_err = "NO PUDE CARGAR LA ROM NUEVA"; return 0; }
    if (g_romcrc != g_sw_crc) { g_err = "LA ROM NO ES LA DEL AMIGO"; return 0; }
    snprintf(g_last_rom, sizeof g_last_rom, "%s", g_rom_name);   /* el menu y el proximo arranque la recuerdan */
    opts_save();
    g_toast_n = 0;
    logf_("cambio de juego: listo, ROM nueva %s (crc32 %08X)", g_rom_name, (unsigned)g_romcrc);
    return 1;
}

/* ------------------------------------------------------------------ */
/* v1.9.4: GUARDAR / CARGAR ESTADO en partida online (solo el HOST; vale para 1vs1 y para el modo de 4).                 */
/* Guardar solo escribe la ranura del host (no toca la partida). Al CARGAR, el host le manda el estado al amigo           */
/* (M_STATE + datos) ANTES de su entrada de este cuadro y los dos lo cargan justo antes de emular el cuadro F = cuadro    */
/* actual + D (mismo truco que el reinicio sincronizado). Mientras llegan los datos los dos esperan (el juego se detiene  */
/* unos segundos); no se pierde ni se adelanta ningun cuadro.                                                            */
/* ------------------------------------------------------------------ */
/* Host: lee la ranura y la manda. 1 = enviado (queda pendiente en st_in), 0 = no se pudo leer (aviso en pantalla), -1 = se corto la conexion */
static int state_online_host_load(int slot, uint32_t frame, int D, uint8_t **st_in, size_t *st_in_n, uint32_t *st_in_F, const char *stage0)
{
    uint8_t *sb = NULL;
    size_t sn = 0;
    char tb[40];
    Msg rq;
    uint32_t F = frame + (uint32_t)D, t0 = now_ms();
    int ok;
    if (!state_read(slot, &sb, &sn)) {
        snprintf(tb, sizeof tb, "NO SE PUDO CARGAR (RANURA %d)", slot + 1);
        toast(tb);
        return 0;
    }
    memset(&rq, 0, sizeof rq);
    rq.type = M_STATE; rq.frame = F; rq.v1 = (uint32_t)sn; rq.v2 = crc32_buf(sb, sn);
    g_stage = "enviando-estado";
    ok = net_send(&rq) && net_send_raw(sb, sn);
    g_stage = stage0;
    logf_("estado: ranura %d (%u bytes, crc %08X) enviado en %u ms; los dos lo cargan en el frame %u (pedido en el %u)",
          slot + 1, (unsigned)sn, (unsigned)rq.v2, (unsigned)(now_ms() - t0), (unsigned)F, (unsigned)frame);
    free(*st_in);
    *st_in = sb; *st_in_n = sn; *st_in_F = F;
    return ok ? 1 : -1;
}

/* Invitado: recibe el estado entero (nunca se pasa de largo el cuadro de carga: no puede emular m->frame sin la entrada del host,
 * que viene DESPUES de este mensaje). 1 = guardado como pendiente; 0 = algo no cuadra (g_err puesto: se termina la partida con aviso,
 * porque cargarlo en un solo lado la desincronizaria); -1 = se corto la conexion */
static int state_online_guest_recv(const Msg *m, uint32_t frame, uint8_t **st_in, size_t *st_in_n, uint32_t *st_in_F, const char *stage0)
{
    uint8_t *sb;
    if (m->v1 == 0 || m->v1 > STATE_MAX || (size_t)m->v1 != retro_serialize_size() || m->frame < frame) {
        g_err = "ESTADO DEL HOST NO VALIDO";
        return 0;
    }
    sb = (uint8_t *)malloc(m->v1);
    if (!sb) { g_err = "SIN MEMORIA PARA EL ESTADO"; return 0; }
    g_stage = "recibiendo-estado";
    if (!net_recv_raw(sb, m->v1)) { free(sb); return -1; }
    g_stage = stage0;
    if (crc32_buf(sb, m->v1) != m->v2) { free(sb); g_err = "ESTADO RECIBIDO CON ERRORES"; return 0; }
    free(*st_in);
    *st_in = sb; *st_in_n = m->v1; *st_in_F = m->frame;
    logf_("estado recibido del host: %u bytes, crc %08X; lo cargo en el frame %u (voy en el %u)", (unsigned)m->v1, (unsigned)m->v2, (unsigned)m->frame, (unsigned)frame);
    return 1;
}

static int session_loop(int role, int D, uint32_t maxframes)
{
    /* v1.9.4: estado guardado pendiente de cargar en el cuadro st_in_F (el host lo lee de su ranura; el invitado lo recibe por red) */
    uint8_t *st_in = NULL;
    size_t st_in_n = 0;
    uint32_t st_in_F = NO_FRAME;
    const char *stage0;
    uint16_t loc[RING], rem[RING];
    uint8_t  have[RING];
    uint32_t mine_f[RING], mine_c[RING], rem_f[RING], rem_c[RING];
    uint32_t frame = 0, last_rx = now_ms();
    uint32_t rst[RST_MAX];
    int i, ended_ok = 1, peer_gone = 0, peer_quit = 0, user_exit = 0;
    char ov[64];

    memset(loc, 0, sizeof loc); memset(rem, 0, sizeof rem); memset(have, 0, sizeof have);
    for (i = 0; i < RING; i++) { mine_f[i] = NO_FRAME; rem_f[i] = NO_FRAME; mine_c[i] = rem_c[i] = 0; }
    for (i = 0; i < RST_MAX; i++) rst[i] = NO_FRAME;
    if (role >= 0) for (i = 0; i < D; i++) have[i] = 1;

    g_run_hash = 2166136261u; g_frames_done = 0; g_desyncs = 0; g_first_desync = NO_FRAME;
    g_stage = role == 0 ? "juego-host" : role == 1 ? "juego-cliente" : "juego-local";
    stage0 = g_stage;
    g_ingame = 1;                           /* v1.9.3: desde aqui la imagen usa la pantalla elegida en OPCIONES */
    memset(&g_gsw, 0, sizeof g_gsw); g_gsw.go = NO_FRAME; g_sw_pending = 0;      /* v1.9.2: cambio de juego */
    g_ka_on = role >= 0; g_ka_last = now_ms();
    g_ni_t0 = 0; g_ni_last = 0; g_ni_fps = 0;

#define COMPARE(f) do { uint32_t _f = (f); \
        if (mine_f[_f % RING] == _f && rem_f[_f % RING] == _f && \
            mine_c[_f % RING] != rem_c[_f % RING]) { \
            if (!g_desyncs) { g_first_desync = _f; logf_("DESYNC en frame %u", (unsigned)_f); } \
            g_desyncs++; \
            mine_f[_f % RING] = NO_FRAME; } } while (0)

    (void)exit_pressed(1, 0);               /* ignora un R2 que siga apretado desde antes */

    (void)shot_pressed(1, 0); g_shot_req = 0;          /* v1.9.6: lo mismo con L2 (captura) */

    while (g_running && (maxframes == 0 || frame < maxframes)) {
        uint16_t p1, p2;
        pump();
        /* v1.9.2: cambio de juego: llego el cuadro de corte (se mira ANTES de mandar la entrada de este cuadro) */
        if (g_gsw.go != NO_FRAME && frame >= g_gsw.go) { g_sw_pending = 1; goto out; }
        if (g_gsw.asked && now_ms() - g_gsw.asked_ms > 20000) { g_gsw.asked = 0; toast("TU AMIGO NO RESPONDIO"); logf_("cambio de juego: sin respuesta del amigo (20 s)"); }

        /* v1.7: R2 abre el menu de salir. Se mira antes de mandar la entrada de este frame; si sigue, el
         * otro lado simplemente espera como siempre. No cambia nada del protocolo ni del lockstep. */
        if (role != -2 && exit_pressed(0, frame) && !(st_in && st_in_F > frame)) {   /* v1.9.4: con un estado por cargarse en unos cuadros no se abre el menu */
            /* v1.9.1: SOLO = continuar / guardar y cargar estado / reiniciar / salir; online = continuar / reiniciar / salir */
            int xr = solo_menu(role >= 0, role == 0);
            if (xr == 1) { user_exit = 1; logf_("salida pedida por el jugador (R2) en frame %u", (unsigned)frame); goto out; }
            if (xr == 3 && role == 0) { if (!gsw_ask_host()) peer_gone = 1; }       /* v1.9.2: cambiar de juego (solo el host) */
            if (xr == 2) {
                if (role >= 0) {
                    Msg rq;
                    uint32_t F = frame + (uint32_t)D;
                    memset(&rq, 0, sizeof rq); rq.type = M_RESET; rq.frame = F;
                    if (!peer_gone && !net_send(&rq)) peer_gone = 1;
                    rst_add(rst, F);
                    logf_("reinicio pedido por el jugador (R2) en frame %u: los dos reinician en el frame %u", (unsigned)frame, (unsigned)F);
                } else {
                    retro_reset();
                    logf_("juego reiniciado por el jugador (R2) en frame %u", (unsigned)frame);
                }
            } else if (xr >= 10 && xr < 10 + STATE_SLOTS && (role == -1 || role == 0)) {   /* v1.9.4: el host tambien guarda en ONLINE (solo escribe su ranura: no toca la partida) */
                char tb[40];
                snprintf(tb, sizeof tb, state_save(xr - 10) ? "ESTADO GUARDADO EN RANURA %d" : "NO SE PUDO GUARDAR (RANURA %d)", xr - 9);
                toast(tb);
            } else if (xr >= 20 && xr < 20 + STATE_SLOTS && role == -1) {
                char tb[40];
                int lr = state_load(xr - 20);
                snprintf(tb, sizeof tb, lr > 0 ? "ESTADO CARGADO: RANURA %d" : "NO SE PUDO CARGAR (RANURA %d)", xr - 19);
                toast(tb);
            } else if (xr >= 20 && xr < 20 + STATE_SLOTS && role == 0) {
                /* v1.9.4: el host carga un estado EN ONLINE: se lo manda al amigo y los dos lo cargan en el mismo cuadro */
                if (!peer_gone && state_online_host_load(xr - 20, frame, D, &st_in, &st_in_n, &st_in_F, stage0) < 0) peer_gone = 1;
            }
            last_rx = now_ms();
            g_ni_t0 = 0; g_ni_last = 0;               /* v1.9.2: el FPS vuelve a medir despues del menu */
        }

        if (role != -2 && shot_pressed(0, frame)) g_shot_req = 1;        /* v1.9.6: L2 = captura (se toma despues de emular este cuadro) */
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
                } else if (m.type == M_RESET) {
                    rst_add(rst, m.frame);
                } else if (m.type == M_STATE) {                     /* v1.9.4: el host manda un estado guardado */
                    int sr = state_online_guest_recv(&m, frame, &st_in, &st_in_n, &st_in_F, stage0);
                    if (sr == 0) { ended_ok = 0; goto out; }
                    if (sr < 0) { if (!g_running) goto out; peer_gone = 1; continue; }
                    last_rx = now_ms();
                } else if (m.type == M_GAME) {                      /* v1.9.2: cambio de juego */
                    if (!gsw_on_msg(&m, role, frame, D)) peer_gone = 1;
                } else if (m.type == M_QUIT) {
                    peer_quit = 1; peer_gone = 1;
                }
                if (g_gsw.go != NO_FRAME && frame >= g_gsw.go) { g_sw_pending = 1; goto out; }   /* el corte llego mientras esperaba */
            }
            have[frame % RING] = 0;
            {
                uint16_t mine = loc[frame % RING], theirs = rem[frame % RING];
                p1 = (role == 0) ? mine : theirs;
                p2 = (role == 0) ? theirs : mine;
            }
        }

        /* v1.9.1: reinicio sincronizado (o, en las pruebas de PC, el de la referencia) justo antes de emular este cuadro */
        {
            int due = rst_due(rst, frame);
#ifdef NESNET_HOST
            if (role == -2 && (frame == g_ref_reset[0] || frame == g_ref_reset[1])) due = 1;
#endif
            if (due) { retro_reset(); logf_("reinicio aplicado en el frame %u", (unsigned)frame); }
        }
        if (st_in && st_in_F == frame) {                  /* v1.9.4: estado del host (el mismo bloque en los dos lados) justo antes de este cuadro */
            int okl = retro_unserialize(st_in, st_in_n) ? 1 : 0;
            logf_("estado cargado en el frame %u: %u bytes, crc %08X %s", (unsigned)frame, (unsigned)st_in_n, (unsigned)crc32_buf(st_in, st_in_n), okl ? "OK" : "FALLO");
            toast(role == 0 ? (okl ? "ESTADO CARGADO" : "NO SE PUDO CARGAR") : "EL HOST CARGO UN ESTADO");
            free(st_in);
            st_in = NULL; st_in_n = 0; st_in_F = NO_FRAME;
        }

#ifdef NESNET_HOST
        { const char *b = getenv("NESNET_BREAK");        /* prueba: corrompe a proposito un frame */
          if (b && role == 1 && frame >= (uint32_t)atoi(b) && frame < (uint32_t)atoi(b) + 30) p1 ^= 0xFF; }
#endif
        g_vid_fresh = 0;
        step_frame(p1, p2);
        if (g_shot_req && g_vid_fresh) { g_shot_req = 0; shot_do(); }   /* v1.9.6: captura limpia: g_fb todavia no tiene textos */

        mine_f[frame % RING] = frame;
        mine_c[frame % RING] = g_frame_crc;
        if (role >= 0) COMPARE(frame);
        g_run_hash = fnv_u32(g_run_hash, g_frame_crc);

        if (role >= 0 && netinfo_show(frame)) {
            if (g_desyncs) snprintf(ov, sizeof ov, "DESYNC EN FRAME %u", (unsigned)g_first_desync);
            else if (g_netinfo == 1) snprintf(ov, sizeof ov, "P%d DELAY %d (%dMS) FPS %u TRABAS %u", role + 1, D, D * 17, (unsigned)g_ni_fps, (unsigned)g_ni_st);
            else snprintf(ov, sizeof ov, "NESNET  P%d  DELAY %d", role + 1, D);
            ui_text(2, 2, ov, 1, g_desyncs ? 0xFFFF4040 : 0xFFFFFFFF);
        }
        if (g_toast_n > 0) { ui_text(4, 224, g_toast, 1, 0xFFFFFF40); g_toast_n--; }
        if (g_showfps && role != -2) ui_fps();                           /* v1.9.2: FPS en pantalla (SOLO y online) */
        present();
        if ((role >= 0 && g_netinfo == 1) || (g_showfps && role != -2)) netinfo_tick();
        frame++;
        g_frames_done = frame;
        if (role == -1 && (frame % 300) == 0) sram_save(0);      /* v1.9: guardado de bateria cada ~5 s si cambio (solo SOLO) */
    }
out:
    g_ingame = 0;                           /* v1.9.3: al salir de la partida, los menus vuelven a MENU_SCREEN */
    g_ka_on = 0;
    free(st_in);                            /* v1.9.4: estado pendiente que nunca llego a cargarse */
    st_in = NULL;
    if (role >= 0 && g_net >= 0 && !g_sw_pending) {       /* v1.9.2: en un cambio de juego no se avisa de salida */
        Msg q; memset(&q, 0, sizeof q); q.type = M_QUIT; net_send(&q);
        if (user_exit) {
            /* v1.7: vacia lo que el otro lado alcance a mandar (hasta 300 ms o hasta que cierre), para que
             * al cerrar el socket no se pierda el aviso de salida (cerrar con datos sin leer lo descarta) */
            uint32_t t0 = now_ms();
            while (now_ms() - t0 < 300) { if (net_recv(&q, 20) < 0) break; }
        }
    }
#undef COMPARE
    return ended_ok;
}

/* ------------------------------------------------------------------ */
/* v1.8: bucle de partida de 4 jugadores (COPIA adaptada de session_loop; el 1vs1 de arriba no se toca)  */
/* Cada consola manda en un solo mensaje sus 2 mandos: byte bajo = mando 1 de esa consola, byte alto = mando 2.   */
/* Host: mandos 1 y 2 (P1+P2). El que se une: mandos 3 y 4 (P3+P4).                                                */
/* ------------------------------------------------------------------ */
static uint16_t local_bits4(int role, uint32_t frame)
{
#ifdef NESNET_HOST
    int base = role == 1 ? 2 : 0;           /* pruebas: host = jugadores 0 y 1, cliente = jugadores 2 y 3 */
    return (uint16_t)(script_input(base, frame) | (script_input(base + 1, frame) << 8));
#else
    (void)role; (void)frame;
    return (uint16_t)((pad_nes_bits(0) & 0xFF) | ((pad_nes_bits(1) & 0xFF) << 8));
#endif
}

/* role: 0 = host (P1+P2), 1 = el que se une (P3+P4), -2 = referencia de pruebas: 4 jugadores locales con retraso D */
static int session_loop4(int role, int D, uint32_t maxframes)
{
    /* v1.9.4: estado guardado pendiente de cargar (igual que en el 1vs1) */
    uint8_t *st_in = NULL;
    size_t st_in_n = 0;
    uint32_t st_in_F = NO_FRAME;
    const char *stage0;
    uint16_t loc[RING], rem[RING];
    uint8_t  have[RING];
    uint32_t mine_f[RING], mine_c[RING], rem_f[RING], rem_c[RING];
    uint32_t frame = 0, last_rx = now_ms();
    uint32_t rst[RST_MAX];
    int i, ended_ok = 1, peer_gone = 0, peer_quit = 0, user_exit = 0;
    char ov[64];

    memset(loc, 0, sizeof loc); memset(rem, 0, sizeof rem); memset(have, 0, sizeof have);
    for (i = 0; i < RING; i++) { mine_f[i] = NO_FRAME; rem_f[i] = NO_FRAME; mine_c[i] = rem_c[i] = 0; }
    for (i = 0; i < RST_MAX; i++) rst[i] = NO_FRAME;
    if (role >= 0) for (i = 0; i < D; i++) have[i] = 1;

    g_run_hash = 2166136261u; g_frames_done = 0; g_desyncs = 0; g_first_desync = NO_FRAME;
    g_stage = role == 0 ? "juego4-host" : role == 1 ? "juego4-cliente" : "juego4-ref";
    stage0 = g_stage;
    g_ingame = 1;                           /* v1.9.3: desde aqui la imagen usa la pantalla elegida en OPCIONES */
    memset(&g_gsw, 0, sizeof g_gsw); g_gsw.go = NO_FRAME; g_sw_pending = 0;      /* v1.9.2: cambio de juego */
    g_ka_on = role >= 0; g_ka_last = now_ms();
    g_ni_t0 = 0; g_ni_last = 0; g_ni_fps = 0;

#define COMPARE4(f) do { uint32_t _f = (f); \
        if (mine_f[_f % RING] == _f && rem_f[_f % RING] == _f && \
            mine_c[_f % RING] != rem_c[_f % RING]) { \
            if (!g_desyncs) { g_first_desync = _f; logf_("DESYNC en frame %u", (unsigned)_f); } \
            g_desyncs++; \
            mine_f[_f % RING] = NO_FRAME; } } while (0)

    (void)exit_pressed(1, 0);               /* ignora un R2 que siga apretado desde antes */

    (void)shot_pressed(1, 0); g_shot_req = 0;          /* v1.9.6: lo mismo con L2 (captura) */

    while (g_running && (maxframes == 0 || frame < maxframes)) {
        uint16_t p1, p2, p3, p4;
        pump();
        /* v1.9.2: cambio de juego (igual que en el 1vs1) */
        if (g_gsw.go != NO_FRAME && frame >= g_gsw.go) { g_sw_pending = 1; goto out; }
        if (g_gsw.asked && now_ms() - g_gsw.asked_ms > 20000) { g_gsw.asked = 0; toast("TU AMIGO NO RESPONDIO"); logf_("cambio de juego: sin respuesta del amigo (20 s)"); }

        /* R2 del mando 1 de esta consola abre el menu (igual que en el 1vs1): continuar / reiniciar / salir */
        if (role != -2 && exit_pressed(0, frame) && !(st_in && st_in_F > frame)) {   /* v1.9.4: con un estado por cargarse en unos cuadros no se abre el menu */
            int xr = solo_menu(1, role == 0);
            if (xr == 1) { user_exit = 1; logf_("salida pedida por el jugador (R2) en frame %u", (unsigned)frame); goto out; }
            if (xr == 3 && role == 0) { if (!gsw_ask_host()) peer_gone = 1; }       /* v1.9.2: cambiar de juego (solo el host) */
            if (xr == 2) {
                Msg rq;
                uint32_t F = frame + (uint32_t)D;
                memset(&rq, 0, sizeof rq); rq.type = M_RESET; rq.frame = F;
                if (!peer_gone && !net_send(&rq)) peer_gone = 1;
                rst_add(rst, F);
                logf_("reinicio pedido por el jugador (R2) en frame %u: los dos reinician en el frame %u", (unsigned)frame, (unsigned)F);
            } else if (xr >= 10 && xr < 10 + STATE_SLOTS && role == 0) {          /* v1.9.4: el host guarda (solo escribe su ranura) */
                char tb[40];
                snprintf(tb, sizeof tb, state_save(xr - 10) ? "ESTADO GUARDADO EN RANURA %d" : "NO SE PUDO GUARDAR (RANURA %d)", xr - 9);
                toast(tb);
            } else if (xr >= 20 && xr < 20 + STATE_SLOTS && role == 0) {          /* v1.9.4: el host carga: se lo manda al amigo y los dos lo cargan en el mismo cuadro */
                if (!peer_gone && state_online_host_load(xr - 20, frame, D, &st_in, &st_in_n, &st_in_F, stage0) < 0) peer_gone = 1;
            }
            last_rx = now_ms();
            g_ni_t0 = 0; g_ni_last = 0;               /* v1.9.2: el FPS vuelve a medir despues del menu */
        }

        if (role != -2 && shot_pressed(0, frame)) g_shot_req = 1;        /* v1.9.6: L2 = captura (se toma despues de emular este cuadro) */
        if (role == -2) {
#ifdef NESNET_HOST
            uint32_t f0 = frame >= (uint32_t)D ? frame - (uint32_t)D : 0;
            int ok0 = frame >= (uint32_t)D;
            p1 = ok0 ? script_input(0, f0) : 0;
            p2 = ok0 ? script_input(1, f0) : 0;
            p3 = ok0 ? script_input(2, f0) : 0;
            p4 = ok0 ? script_input(3, f0) : 0;
#else
            p1 = p2 = p3 = p4 = 0;           /* la referencia solo existe en la version de pruebas (PC) */
#endif
        } else {
            Msg m;
            uint32_t tgt = frame + (uint32_t)D;
            uint16_t bits = local_bits4(role, frame);
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
                    if (m.v1 != NO_FRAME) { rem_f[m.v1 % RING] = m.v1; rem_c[m.v1 % RING] = m.v2; COMPARE4(m.v1); }
                } else if (m.type == M_RESET) {
                    rst_add(rst, m.frame);
                } else if (m.type == M_STATE) {                     /* v1.9.4: el host manda un estado guardado */
                    int sr = state_online_guest_recv(&m, frame, &st_in, &st_in_n, &st_in_F, stage0);
                    if (sr == 0) { ended_ok = 0; goto out; }
                    if (sr < 0) { if (!g_running) goto out; peer_gone = 1; continue; }
                    last_rx = now_ms();
                } else if (m.type == M_GAME) {                      /* v1.9.2: cambio de juego */
                    if (!gsw_on_msg(&m, role, frame, D)) peer_gone = 1;
                } else if (m.type == M_QUIT) {
                    peer_quit = 1; peer_gone = 1;
                }
                if (g_gsw.go != NO_FRAME && frame >= g_gsw.go) { g_sw_pending = 1; goto out; }   /* el corte llego mientras esperaba */
            }
            have[frame % RING] = 0;
            {
                uint16_t mine = loc[frame % RING], theirs = rem[frame % RING];
                uint16_t hb = (role == 0) ? mine : theirs;      /* bytes del host */
                uint16_t cb = (role == 0) ? theirs : mine;      /* bytes del que se une */
                p1 = hb & 0xFF; p2 = (uint16_t)(hb >> 8);
                p3 = cb & 0xFF; p4 = (uint16_t)(cb >> 8);
            }
        }

        /* v1.9.1: reinicio sincronizado (igual que en el 1vs1) */
        {
            int due = rst_due(rst, frame);
#ifdef NESNET_HOST
            if (role == -2 && (frame == g_ref_reset[0] || frame == g_ref_reset[1])) due = 1;
#endif
            if (due) { retro_reset(); logf_("reinicio aplicado en el frame %u", (unsigned)frame); }
        }
        if (st_in && st_in_F == frame) {                  /* v1.9.4: estado del host justo antes de este cuadro (igual que en el 1vs1) */
            int okl = retro_unserialize(st_in, st_in_n) ? 1 : 0;
            logf_("estado cargado en el frame %u: %u bytes, crc %08X %s", (unsigned)frame, (unsigned)st_in_n, (unsigned)crc32_buf(st_in, st_in_n), okl ? "OK" : "FALLO");
            toast(role == 0 ? (okl ? "ESTADO CARGADO" : "NO SE PUDO CARGAR") : "EL HOST CARGO UN ESTADO");
            free(st_in);
            st_in = NULL; st_in_n = 0; st_in_F = NO_FRAME;
        }

#ifdef NESNET_HOST
        { const char *b = getenv("NESNET_BREAK");        /* prueba: corrompe a proposito un frame */
          if (b && role == 1 && frame >= (uint32_t)atoi(b) && frame < (uint32_t)atoi(b) + 30) p3 ^= 0xFF; }
#endif
        g_vid_fresh = 0;
        step_frame4(p1, p2, p3, p4);
        if (g_shot_req && g_vid_fresh) { g_shot_req = 0; shot_do(); }   /* v1.9.6: captura limpia */

        mine_f[frame % RING] = frame;
        mine_c[frame % RING] = g_frame_crc;
        if (role >= 0) COMPARE4(frame);
        g_run_hash = fnv_u32(g_run_hash, g_frame_crc);

        if (role >= 0 && netinfo_show(frame)) {
            if (g_desyncs) snprintf(ov, sizeof ov, "DESYNC EN FRAME %u", (unsigned)g_first_desync);
            else if (g_netinfo == 1) snprintf(ov, sizeof ov, "4J %s DELAY %d (%dMS) FPS %u TRABAS %u", role == 0 ? "P1+P2" : "P3+P4", D, D * 17, (unsigned)g_ni_fps, (unsigned)g_ni_st);
            else snprintf(ov, sizeof ov, "NESNET 4J  %s  DELAY %d", role == 0 ? "P1+P2" : "P3+P4", D);
            ui_text(2, 2, ov, 1, g_desyncs ? 0xFFFF4040 : 0xFFFFFFFF);
        }
        if (g_toast_n > 0) { ui_text(4, 224, g_toast, 1, 0xFFFFFF40); g_toast_n--; }      /* v1.9.2: avisos tambien en el modo de 4 */
        if (g_showfps && role != -2) ui_fps();                           /* v1.9.2: FPS en pantalla */
        present();
        if ((role >= 0 && g_netinfo == 1) || (g_showfps && role != -2)) netinfo_tick();
        frame++;
        g_frames_done = frame;
    }
out:
    g_ingame = 0;                           /* v1.9.3: al salir de la partida, los menus vuelven a MENU_SCREEN */
    g_ka_on = 0;
    free(st_in);                            /* v1.9.4: estado pendiente que nunca llego a cargarse */
    st_in = NULL;
    if (role >= 0 && g_net >= 0 && !g_sw_pending) {       /* v1.9.2: en un cambio de juego no se avisa de salida */
        Msg q; memset(&q, 0, sizeof q); q.type = M_QUIT; net_send(&q);
        if (user_exit) {
            /* vacia lo que el otro lado alcance a mandar (hasta 300 ms o hasta que cierre), para que
             * al cerrar el socket no se pierda el aviso de salida */
            uint32_t t0 = now_ms();
            while (now_ms() - t0 < 300) { if (net_recv(&q, 20) < 0) break; }
        }
    }
#undef COMPARE4
#ifdef NESNET_HOST
    if (getenv("NESNET_RAMDUMP")) {            /* prueba: muestra lo que el juego leyo de los 4 mandos (RAM $00-$07) */
        const uint8_t *ram = (const uint8_t *)retro_get_memory_data(RETRO_MEMORY_SYSTEM_RAM);
        if (ram) printf("RAM role=%d: %02X %02X %02X %02X %02X %02X %02X %02X\n", role,
                        ram[0], ram[1], ram[2], ram[3], ram[4], ram[5], ram[6], ram[7]);
    }
#endif
    return ended_ok;
}

/* ------------------------------------------------------------------ */
/* Interfaz                                                            */
/* ------------------------------------------------------------------ */
static void code_pretty(const char *code, char *out);
/* v1.9.7: pantalla de "sala creada" (codigo, estado del puerto, esperando al amigo) */
static void hr_room_screen(const char *sub, const char *code, const char *l2, const char *l3, uint32_t col3)
{
    static const HHint hh[1] = { { "O", "CANCELAR", HC_BO } };
    char pc[24];
    int dots = (int)((now_ms() / 400) % 3), k;
    code_pretty(code, pc);
    hr_head(sub);
    hr_panel(230, 200, 1050, 600);
    hr_text(270, 252, "TU CÓDIGO DE SALA", FS_M, HC_DIM, 2);
    hr_text(270, 350, pc, FS_X, HC_YEL, 4);
    hr_text(270, 410, "Dáselo a tu amigo", FS_L, HC_WHITE, 2);
    hr_text(270, 452, l3, FS_M, hr_col(col3), 2);
    hr_text(270, 486, l2, FS_S, HC_DIM, 2);
    hr_text(270, 552, "Esperando al amigo...", FS_L, HC_WHITE, 2);
    for (k = 0; k < 3; k++) hr_rect(760 + k * 34, 534, 782 + k * 34, 556, k == dots ? HC_RED : 0xFF5A283Cu, 256);
    hr_hints(hh, 1);
}

static void ui_show(const char *l1, const char *l2, const char *l3)
{
    if (hr_usable()) {
        hr_head(NULL);
        hr_panel(230, 250, 1050, 480);
        if (l1) hr_textc(640, 340, l1, FS_L, HC_WHITE);
        if (l2) hr_textc(640, 396, l2, FS_M, HC_DIM);
        if (l3) hr_textc(640, 438, l3, FS_M, HC_DIM);
        present();
        return;
    }
    ui_clear();
    ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
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

/* Copia 'src' en 'dst' (cap bytes) acortando con "..." si no cabe en 'maxc' caracteres */
static void fit_name(char *dst, size_t cap, const char *src, int maxc)
{
    size_t n = strlen(src);
    if ((int)n <= maxc && n < cap) { snprintf(dst, cap, "%s", src); return; }
    if ((size_t)maxc >= cap) maxc = (int)cap - 1;
    memcpy(dst, src, (size_t)maxc);
    dst[maxc] = 0;
    if (maxc >= 3) { dst[maxc - 3] = '.'; dst[maxc - 2] = '.'; dst[maxc - 1] = '.'; }
}

/* ------------------------------------------------------------------ */
/* v1.9.8: caratulas. Lector de PNG propio (inflate + filtros), sin librerias externas.                 */
/* Soporta PNG de 1/2/4/8/16 bits, gris, RGB, paleta, gris+alfa y RGBA, con o sin entrelazado (Adam7). */
/* ------------------------------------------------------------------ */
#define CV_MAXDIM    1024            /* lado maximo aceptado (px) */
#define CV_MAXFILE   (3u << 20)      /* archivo maximo: 3 MB */
#define CV_MAXRAW    (9u << 20)      /* datos descomprimidos maximos: 9 MB */

#define CI_MAXBITS 15
#define CI_MAXL    286
#define CI_MAXD    30
#define CI_FIXL    288

typedef struct {
    const uint8_t *in; size_t inlen, incnt;
    uint32_t bitbuf; int bitcnt;
    uint8_t *out; size_t outlen, outcnt;
} CInf;

typedef struct { short *count; short *symbol; } CHuff;

static int ci_bits(CInf *s, int need)
{
    uint32_t val = s->bitbuf;
    while (s->bitcnt < need) {
        if (s->incnt >= s->inlen) return -1;
        val |= (uint32_t)s->in[s->incnt++] << s->bitcnt;
        s->bitcnt += 8;
    }
    s->bitbuf = val >> need;
    s->bitcnt -= need;
    return (int)(val & ((1u << need) - 1u));
}

static int ci_decode(CInf *s, const CHuff *h)
{
    int len, code = 0, first = 0, count, index = 0;
    for (len = 1; len <= CI_MAXBITS; len++) {
        int b = ci_bits(s, 1);
        if (b < 0) return -1;
        code |= b;
        count = h->count[len];
        if (code - count < first) return h->symbol[index + (code - first)];
        index += count; first += count; first <<= 1; code <<= 1;
    }
    return -10;
}

static int ci_construct(CHuff *h, const short *length, int n)
{
    int symbol, len, left;
    short offs[CI_MAXBITS + 1];
    for (len = 0; len <= CI_MAXBITS; len++) h->count[len] = 0;
    for (symbol = 0; symbol < n; symbol++) h->count[length[symbol]]++;
    if (h->count[0] == n) return 0;
    left = 1;
    for (len = 1; len <= CI_MAXBITS; len++) {
        left <<= 1;
        left -= h->count[len];
        if (left < 0) return left;
    }
    offs[1] = 0;
    for (len = 1; len < CI_MAXBITS; len++) offs[len + 1] = (short)(offs[len] + h->count[len]);
    for (symbol = 0; symbol < n; symbol++)
        if (length[symbol] != 0) h->symbol[offs[length[symbol]]++] = (short)symbol;
    return left;
}

static int ci_codes(CInf *s, const CHuff *lencode, const CHuff *distcode)
{
    static const short lens[29] = { 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258 };
    static const short lext[29] = { 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0 };
    static const short dists[30] = { 1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577 };
    static const short dext[30] = { 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13 };
    int symbol;
    do {
        symbol = ci_decode(s, lencode);
        if (symbol < 0) return symbol;
        if (symbol < 256) {
            if (s->outcnt == s->outlen) return 1;
            s->out[s->outcnt++] = (uint8_t)symbol;
        } else if (symbol > 256) {
            int len, b;
            size_t dist;
            symbol -= 257;
            if (symbol >= 29) return -10;
            b = ci_bits(s, lext[symbol]);
            if (b < 0) return -1;
            len = lens[symbol] + b;
            symbol = ci_decode(s, distcode);
            if (symbol < 0) return symbol;
            if (symbol >= 30) return -10;
            b = ci_bits(s, dext[symbol]);
            if (b < 0) return -1;
            dist = (size_t)dists[symbol] + (size_t)b;
            if (dist > s->outcnt) return -11;
            if (s->outcnt + (size_t)len > s->outlen) return 1;
            while (len--) { s->out[s->outcnt] = s->out[s->outcnt - dist]; s->outcnt++; }
        }
    } while (symbol != 256);
    return 0;
}

static int ci_stored(CInf *s)
{
    unsigned len;
    s->bitbuf = 0; s->bitcnt = 0;
    if (s->incnt + 4 > s->inlen) return 2;
    len = s->in[s->incnt++]; len |= (unsigned)s->in[s->incnt++] << 8;
    if (s->in[s->incnt++] != (~len & 0xFFu) || s->in[s->incnt++] != ((~len >> 8) & 0xFFu)) return -2;
    if (s->incnt + len > s->inlen) return 2;
    if (s->outcnt + len > s->outlen) return 1;
    while (len--) s->out[s->outcnt++] = s->in[s->incnt++];
    return 0;
}

static int ci_fixed(CInf *s)
{
    static int virgin = 1;
    static short lc[CI_MAXBITS + 1], ls[CI_FIXL], dc[CI_MAXBITS + 1], ds[CI_MAXD];
    static CHuff lencode, distcode;
    if (virgin) {
        short lengths[CI_FIXL];
        int sym;
        lencode.count = lc; lencode.symbol = ls; distcode.count = dc; distcode.symbol = ds;
        for (sym = 0; sym < 144; sym++) lengths[sym] = 8;
        for (; sym < 256; sym++) lengths[sym] = 9;
        for (; sym < 280; sym++) lengths[sym] = 7;
        for (; sym < CI_FIXL; sym++) lengths[sym] = 8;
        ci_construct(&lencode, lengths, CI_FIXL);
        for (sym = 0; sym < CI_MAXD; sym++) lengths[sym] = 5;
        ci_construct(&distcode, lengths, CI_MAXD);
        virgin = 0;
    }
    return ci_codes(s, &lencode, &distcode);
}

static int ci_dynamic(CInf *s)
{
    static const short order[19] = { 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15 };
    int nlen, ndist, ncode, index, err, b;
    short lengths[CI_MAXL + CI_MAXD];
    short lc[CI_MAXBITS + 1], ls[CI_MAXL], dc[CI_MAXBITS + 1], ds[CI_MAXD];
    CHuff lencode, distcode;
    b = ci_bits(s, 5); if (b < 0) return -1; nlen = b + 257;
    b = ci_bits(s, 5); if (b < 0) return -1; ndist = b + 1;
    b = ci_bits(s, 4); if (b < 0) return -1; ncode = b + 4;
    if (nlen > CI_MAXL || ndist > CI_MAXD) return -3;
    for (index = 0; index < ncode; index++) { b = ci_bits(s, 3); if (b < 0) return -1; lengths[order[index]] = (short)b; }
    for (; index < 19; index++) lengths[order[index]] = 0;
    lencode.count = lc; lencode.symbol = ls;
    err = ci_construct(&lencode, lengths, 19);
    if (err != 0) return -4;
    index = 0;
    while (index < nlen + ndist) {
        int symbol = ci_decode(s, &lencode);
        if (symbol < 0) return symbol;
        if (symbol < 16) lengths[index++] = (short)symbol;
        else {
            int len = 0, rep;
            if (symbol == 16) {
                if (index == 0) return -5;
                len = lengths[index - 1];
                b = ci_bits(s, 2); if (b < 0) return -1; rep = 3 + b;
            } else if (symbol == 17) { b = ci_bits(s, 3); if (b < 0) return -1; rep = 3 + b; }
            else { b = ci_bits(s, 7); if (b < 0) return -1; rep = 11 + b; }
            if (index + rep > nlen + ndist) return -6;
            while (rep--) lengths[index++] = (short)len;
        }
    }
    if (lengths[256] == 0) return -9;
    err = ci_construct(&lencode, lengths, nlen);
    if (err && (err < 0 || nlen != lencode.count[0] + lencode.count[1])) return -7;
    distcode.count = dc; distcode.symbol = ds;
    err = ci_construct(&distcode, lengths + nlen, ndist);
    if (err && (err < 0 || ndist != distcode.count[0] + distcode.count[1])) return -8;
    return ci_codes(s, &lencode, &distcode);
}

/* inflate de un flujo "raw deflate"; 0 = bien (la salida tiene que llenarse exacta) */
static int ci_inflate(const uint8_t *in, size_t inlen, uint8_t *out, size_t outlen)
{
    CInf s;
    int last, type, err = 0;
    s.in = in; s.inlen = inlen; s.incnt = 0; s.bitbuf = 0; s.bitcnt = 0;
    s.out = out; s.outlen = outlen; s.outcnt = 0;
    do {
        last = ci_bits(&s, 1);
        type = ci_bits(&s, 2);
        if (last < 0 || type < 0) { err = -1; break; }
        err = type == 0 ? ci_stored(&s) : type == 1 ? ci_fixed(&s) : type == 2 ? ci_dynamic(&s) : -1;
        if (err) break;
    } while (!last);
    if (s.outcnt == outlen) return 0;      /* si ya se lleno lo esperado, vale (aunque sobre flujo) */
    return err ? err : -12;
}

static uint32_t cv_be32(const uint8_t *p) { return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | (uint32_t)p[3]; }

/* quita los filtros PNG de "rows" filas de (1 + rb) bytes, en el mismo lugar */
static int cv_unfilter(uint8_t *buf, int rb, int rows, int bpb)
{
    int r, i;
    for (r = 0; r < rows; r++) {
        uint8_t *row = buf + (size_t)r * (size_t)(rb + 1);
        uint8_t ft = row[0];
        uint8_t *x = row + 1;
        const uint8_t *up = r ? row - (rb + 1) + 1 : NULL;
        if (ft > 4) return -1;
        for (i = 0; i < rb; i++) {
            int a = i >= bpb ? x[i - bpb] : 0;
            int b = up ? up[i] : 0;
            int c = (up && i >= bpb) ? up[i - bpb] : 0;
            int v = x[i];
            switch (ft) {
            case 1: v += a; break;
            case 2: v += b; break;
            case 3: v += (a + b) / 2; break;
            case 4: {
                int p = a + b - c, pa = p > a ? p - a : a - p, pb = p > b ? p - b : b - p, pc = p > c ? p - c : c - p;
                v += (pa <= pb && pa <= pc) ? a : (pb <= pc ? b : c);
                break;
            }
            default: break;
            }
            x[i] = (uint8_t)v;
        }
    }
    return 0;
}

typedef struct { int ct, depth, bpp, npal; uint8_t pal[256][4]; } CvFmt;

static uint32_t cv_pixel(const uint8_t *row, int x, const CvFmt *f, uint32_t bg)
{
    int r, g, b, a = 255, d = f->depth;
    switch (f->ct) {
    case 0: case 3: {
        int v, bit = x * d;
        if (d == 16) v = row[x * 2];
        else if (d == 8) v = row[x];
        else v = (row[bit >> 3] >> (8 - d - (bit & 7))) & ((1 << d) - 1);
        if (f->ct == 3) {
            if (v >= f->npal) v = 0;
            r = f->pal[v][0]; g = f->pal[v][1]; b = f->pal[v][2]; a = f->pal[v][3];
        } else {
            if (d < 8) v = v * 255 / ((1 << d) - 1);
            r = g = b = v;
        }
        break;
    }
    case 4: {
        int st = d == 16 ? 4 : 2;
        r = g = b = row[x * st];
        a = row[x * st + (d == 16 ? 2 : 1)];
        break;
    }
    case 2: {
        int st = d == 16 ? 6 : 3, o = d == 16 ? 2 : 1;
        r = row[x * st]; g = row[x * st + o]; b = row[x * st + 2 * o];
        break;
    }
    default: {   /* 6 */
        int st = d == 16 ? 8 : 4, o = d == 16 ? 2 : 1;
        r = row[x * st]; g = row[x * st + o]; b = row[x * st + 2 * o]; a = row[x * st + 3 * o];
        break;
    }
    }
    if (a < 255) {
        int br = (int)((bg >> 16) & 255), bgc = (int)((bg >> 8) & 255), bb = (int)(bg & 255);
        r = (r * a + br * (255 - a)) / 255; g = (g * a + bgc * (255 - a)) / 255; b = (b * a + bb * (255 - a)) / 255;
    }
    return 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)b;
}

/* Decodifica un PNG en memoria. Devuelve 0 = bien (*px = malloc de w*h ARGB opacos sobre "bg"; hay que liberarlo con free).
 * 1 = no es PNG, 2 = demasiado grande, 3 = formato no soportado, 4 = archivo danado, 5 = sin memoria */
static int cv_png_decode(const uint8_t *f, size_t fn, uint32_t bg, uint32_t **px, int *ow, int *oh)
{
    static const int XO[7] = { 0, 4, 0, 2, 0, 1, 0 }, YO[7] = { 0, 0, 4, 0, 2, 0, 1 };
    static const int DX[7] = { 8, 8, 4, 4, 2, 2, 1 }, DY[7] = { 8, 8, 8, 4, 4, 2, 2 };
    static const uint8_t sig[8] = { 137, 80, 78, 71, 13, 10, 26, 10 };
    size_t pos = 8, zlen = 0, zpos = 0, rawn = 0;
    uint32_t w = 0, h = 0;
    int have_ihdr = 0, interlace = 0, channels, pass, npass, rc = 4, bpb, ntrns = 0;
    CvFmt fm;
    uint8_t *z = NULL, *raw = NULL;
    uint32_t *out = NULL;
    int pw[7], ph[7], prb[7];
    size_t poff[7];

    *px = NULL; *ow = *oh = 0;
    memset(&fm, 0, sizeof fm);
    if (fn < 8 + 25 || memcmp(f, sig, 8)) return 1;
    /* 1a pasada: cabecera, paleta, transparencia y tamano del flujo comprimido */
    while (pos + 12 <= fn) {
        uint32_t len = cv_be32(f + pos);
        const uint8_t *t = f + pos + 4, *d = f + pos + 8;
        if (len > fn - pos - 12) { if (!have_ihdr) return 4; break; }
        if (!memcmp(t, "IHDR", 4)) {
            if (len < 13) return 4;
            w = cv_be32(d); h = cv_be32(d + 4);
            fm.depth = d[8]; fm.ct = d[9]; interlace = d[12];
            if (d[10] != 0 || d[11] != 0 || interlace > 1) return 3;
            have_ihdr = 1;
        } else if (!memcmp(t, "PLTE", 4) && have_ihdr) {
            uint32_t i;
            fm.npal = (int)(len / 3);
            if (fm.npal > 256) fm.npal = 256;
            for (i = 0; i < (uint32_t)fm.npal; i++) { fm.pal[i][0] = d[i * 3]; fm.pal[i][1] = d[i * 3 + 1]; fm.pal[i][2] = d[i * 3 + 2]; }
        } else if (!memcmp(t, "tRNS", 4) && have_ihdr && fm.ct == 3) {
            uint32_t i;
            for (i = 0; i < len && i < 256; i++) fm.pal[i][3] = d[i];
            ntrns = (int)(len < 256 ? len : 256);
        } else if (!memcmp(t, "IDAT", 4)) zlen += len;
        else if (!memcmp(t, "IEND", 4)) break;
        pos += 12 + (size_t)len;
    }
    if (!have_ihdr || zlen < 6) return 4;
    if (w < 1 || h < 1 || w > CV_MAXDIM || h > CV_MAXDIM) return 2;
    switch (fm.ct) {
    case 0: if (fm.depth != 1 && fm.depth != 2 && fm.depth != 4 && fm.depth != 8 && fm.depth != 16) return 3; channels = 1; break;
    case 2: if (fm.depth != 8 && fm.depth != 16) return 3; channels = 3; break;
    case 3: if (fm.depth != 1 && fm.depth != 2 && fm.depth != 4 && fm.depth != 8) return 3; channels = 1; break;
    case 4: if (fm.depth != 8 && fm.depth != 16) return 3; channels = 2; break;
    case 6: if (fm.depth != 8 && fm.depth != 16) return 3; channels = 4; break;
    default: return 3;
    }
    {   /* paleta: las entradas sin alfa explicito son opacas */
        int i;
        for (i = ntrns; i < 256; i++) fm.pal[i][3] = 255;
        if (fm.ct == 3 && fm.npal == 0) return 4;
    }
    fm.bpp = channels * fm.depth;
    bpb = fm.bpp >= 8 ? fm.bpp / 8 : 1;
    /* tamano de los datos descomprimidos */
    npass = interlace ? 7 : 1;
    for (pass = 0; pass < npass; pass++) {
        if (interlace) {
            pw[pass] = (int)w > XO[pass] ? ((int)w - XO[pass] + DX[pass] - 1) / DX[pass] : 0;
            ph[pass] = (int)h > YO[pass] ? ((int)h - YO[pass] + DY[pass] - 1) / DY[pass] : 0;
        } else { pw[pass] = (int)w; ph[pass] = (int)h; }
        prb[pass] = (pw[pass] * fm.bpp + 7) / 8;
        poff[pass] = rawn;
        if (pw[pass] > 0 && ph[pass] > 0) rawn += (size_t)ph[pass] * (size_t)(1 + prb[pass]);
    }
    if (rawn > CV_MAXRAW) return 2;
    z = (uint8_t *)malloc(zlen);
    raw = (uint8_t *)malloc(rawn ? rawn : 1);
    out = (uint32_t *)malloc((size_t)w * h * 4);
    if (!z || !raw || !out) { rc = 5; goto done; }
    /* 2a pasada: juntar los IDAT */
    pos = 8;
    while (pos + 12 <= fn && zpos < zlen) {
        uint32_t len = cv_be32(f + pos);
        if (len > fn - pos - 12) break;
        if (!memcmp(f + pos + 4, "IDAT", 4)) { memcpy(z + zpos, f + pos + 8, len); zpos += len; }
        else if (!memcmp(f + pos + 4, "IEND", 4)) break;
        pos += 12 + (size_t)len;
    }
    if (zpos != zlen) { rc = 4; goto done; }
    if ((z[0] & 15) != 8 || (((unsigned)z[0] << 8) | z[1]) % 31 != 0 || (z[1] & 32)) { rc = 3; goto done; }
    if (ci_inflate(z + 2, zlen - 2, raw, rawn) != 0) { rc = 4; goto done; }
    for (pass = 0; pass < npass; pass++) {
        uint8_t *pb = raw + poff[pass];
        int x, y;
        if (pw[pass] <= 0 || ph[pass] <= 0) continue;
        if (cv_unfilter(pb, prb[pass], ph[pass], bpb)) { rc = 4; goto done; }
        for (y = 0; y < ph[pass]; y++) {
            const uint8_t *row = pb + (size_t)y * (size_t)(1 + prb[pass]) + 1;
            for (x = 0; x < pw[pass]; x++) {
                int dx = interlace ? XO[pass] + x * DX[pass] : x, dy = interlace ? YO[pass] + y * DY[pass] : y;
                out[(size_t)dy * w + (size_t)dx] = cv_pixel(row, x, &fm, bg);
            }
        }
    }
    *px = out; *ow = (int)w; *oh = (int)h; out = NULL; rc = 0;
done:
    free(z); free(raw); free(out);
    return rc;
}

/* Reduce (o agranda) src de sw x sh para que quepa en bw x bh sin deformar; deja el resultado en dst (bw*bh) y su tamano en *ow,*oh */
static void cv_fit(const uint32_t *src, int sw, int sh, uint32_t *dst, int bw, int bh, int *ow, int *oh)
{
    int dw, dh, x, y;
    if ((long)sw * bh > (long)sh * bw) { dw = bw; dh = (int)((long)sh * bw / sw); }
    else { dh = bh; dw = (int)((long)sw * bh / sh); }
    if (dw < 1) dw = 1;
    if (dh < 1) dh = 1;
    *ow = dw; *oh = dh;
    for (y = 0; y < dh; y++) {
        for (x = 0; x < dw; x++) {
            uint32_t rr = 0, gg = 0, bb = 0;
            if (dw < sw || dh < sh) {            /* achicar: promedio del rectangulo de origen */
                int x0 = (int)((long)x * sw / dw), x1 = (int)((long)(x + 1) * sw / dw);
                int y0 = (int)((long)y * sh / dh), y1 = (int)((long)(y + 1) * sh / dh), xx, yy, n;
                if (x1 <= x0) x1 = x0 + 1;
                if (y1 <= y0) y1 = y0 + 1;
                if (x1 > sw) x1 = sw;
                if (y1 > sh) y1 = sh;
                n = (x1 - x0) * (y1 - y0);
                for (yy = y0; yy < y1; yy++)
                    for (xx = x0; xx < x1; xx++) {
                        uint32_t p = src[(size_t)yy * sw + xx];
                        rr += (p >> 16) & 255; gg += (p >> 8) & 255; bb += p & 255;
                    }
                rr /= (uint32_t)n; gg /= (uint32_t)n; bb /= (uint32_t)n;
            } else {                              /* agrandar: bilineal */
                long fx = dw > 1 ? (long)x * (sw - 1) * 256 / (dw - 1) : 0, fy = dh > 1 ? (long)y * (sh - 1) * 256 / (dh - 1) : 0;
                int x0 = (int)(fx >> 8), y0 = (int)(fy >> 8), x1 = x0 + 1 < sw ? x0 + 1 : x0, y1 = y0 + 1 < sh ? y0 + 1 : y0;
                int ax = (int)(fx & 255), ay = (int)(fy & 255), ch;
                uint32_t p00 = src[(size_t)y0 * sw + x0], p10 = src[(size_t)y0 * sw + x1], p01 = src[(size_t)y1 * sw + x0], p11 = src[(size_t)y1 * sw + x1];
                uint32_t v[3];
                for (ch = 0; ch < 3; ch++) {
                    int sft = 16 - 8 * ch;
                    int a = (int)((p00 >> sft) & 255), b = (int)((p10 >> sft) & 255), c = (int)((p01 >> sft) & 255), d = (int)((p11 >> sft) & 255);
                    int top = a * (256 - ax) + b * ax, bot = c * (256 - ax) + d * ax;
                    v[ch] = (uint32_t)((top * (256 - ay) + bot * ay) >> 16);
                }
                rr = v[0]; gg = v[1]; bb = v[2];
            }
            dst[(size_t)y * bw + x] = 0xFF000000u | (rr << 16) | (gg << 8) | bb;
        }
    }
}

/* ---- v1.9.8: cuadro de caratula en ELEGIR ROM (carpeta USRDIR/covers, mismo nombre que la ROM, .png) ---- */
#define CV_BX0 868            /* cuadro de la caratula (marco) */
#define CV_BX1 1188
#define CV_BY0 140
#define CV_BY1 548
#define CV_BW  312            /* area de imagen dentro del marco */
#define CV_BH  400
enum { CVS_PEND = 0, CVS_OK, CVS_NONE, CVS_BAD, CVS_BIG, CVS_UNSUP };
static uint32_t g_cv_px[CV_BW * CV_BH];
static int g_cv_w, g_cv_h, g_cv_state;
static char g_cv_file[ROM_NAMELEN + 8];      /* nombre de la caratula esperada: <ROM sin .nes>.png */

static int cv_lower(int c) { return (c >= 'A' && c <= 'Z') ? c + 32 : c; }
static int cv_ceq(const char *a, const char *b, size_t n)     /* n caracteres iguales sin distinguir mayusculas */
{
    size_t i;
    for (i = 0; i < n; i++) if (cv_lower((unsigned char)a[i]) != cv_lower((unsigned char)b[i])) return 0;
    return 1;
}
/* largo del nombre sin la extension ".nes" (cualquier mayuscula/minuscula) */
static size_t rom_base_len(const char *name)
{
    size_t n = strlen(name);
    if (n > 4 && name[n - 4] == '.' && cv_ceq(name + n - 3, "nes", 3)) return n - 4;
    return n;
}
static void rom_title(char *dst, size_t cap, const char *name)
{
    size_t n = rom_base_len(name);
    if (n >= cap) n = cap - 1;
    memcpy(dst, name, n);
    dst[n] = 0;
}
/* recorta por ancho en pixeles (con "..."), sin partir un caracter UTF-8 */
static void fit_px(char *dst, size_t cap, const char *src, int maxpx, int fs)
{
    size_t n;
    snprintf(dst, cap, "%s", src);
    if (hr_tw(dst, fs) <= maxpx) return;
    n = strlen(dst);
    while (n > 4) {
        n--;
        while (n > 4 && ((unsigned char)dst[n] & 0xC0) == 0x80) n--;
        dst[n] = '.'; dst[n + 1] = '.'; dst[n + 2] = '.'; dst[n + 3] = 0;
        if (hr_tw(dst, fs) <= maxpx) return;
    }
}
/* busca en covers/ un .png que se llame como la ROM (sin distinguir mayusculas). 1 = lo encontro y deja la ruta en path */
static int cv_find(const char *romname, char *path, size_t cap)
{
    char dir[300];
    DIR *d;
    struct dirent *e;
    size_t bl = rom_base_len(romname);
    int found = 0;
    snprintf(dir, sizeof dir, "%s/covers", g_dir);
    d = opendir(dir);
    if (!d) return 0;
    while ((e = readdir(d)) != NULL) {
        size_t n = strlen(e->d_name);
        if (n != bl + 4) continue;
        if (!cv_ceq(e->d_name, romname, bl) || e->d_name[bl] != '.' || !cv_ceq(e->d_name + bl + 1, "png", 3)) continue;
        snprintf(path, cap, "%s/%s", dir, e->d_name);
        found = 1;
        break;
    }
    closedir(d);
    return found;
}
/* carga la caratula de la ROM g_roms[idx] (o deja el motivo en g_cv_state) */
static void cv_update(int idx)
{
    char path[420];
    uint8_t *b = NULL;
    size_t bs = 0;
    uint32_t *px = NULL;
    int w = 0, h = 0, rc;
    struct stat st;
    snprintf(g_cv_file, sizeof g_cv_file, "%.*s.png", (int)rom_base_len(g_roms[idx].name), g_roms[idx].name);
    g_cv_state = CVS_NONE;
    if (!cv_find(g_roms[idx].name, path, sizeof path)) return;
    if (stat(path, &st) != 0) return;
    if ((unsigned long)st.st_size > CV_MAXFILE) { g_cv_state = CVS_BIG; logf_("caratula: %s pesa mas de 3 MB, no se muestra", g_cv_file); return; }
    if (!read_whole_file(path, &b, &bs)) { g_cv_state = CVS_BAD; return; }
    rc = cv_png_decode(b, bs, 0xFF02050Eu, &px, &w, &h);
    free(b);
    if (rc == 0) {
        cv_fit(px, w, h, g_cv_px, CV_BW, CV_BH, &g_cv_w, &g_cv_h);
        g_cv_state = CVS_OK;
    } else {
        g_cv_state = rc == 2 ? CVS_BIG : rc == 3 ? CVS_UNSUP : CVS_BAD;
        logf_("caratula: %s no se pudo leer (codigo %d)", g_cv_file, rc);
    }
    free(px);
}
static void cv_draw(void)
{
    int cx = (CV_BX0 + CV_BX1) / 2, y, x0, y0;
    char t[ROM_NAMELEN + 8];
    hr_rect(CV_BX0, CV_BY0, CV_BX1, CV_BY1, 0xFF02050Eu, 256);
    hr_frame_rect(CV_BX0, CV_BY0, CV_BX1, CV_BY1, 2, HC_GRID);
    if (g_cv_state == CVS_PEND) return;
    if (g_cv_state == CVS_OK) {
        x0 = CV_BX0 + 4 + (CV_BW - g_cv_w) / 2;
        y0 = CV_BY0 + 4 + (CV_BH - g_cv_h) / 2;
        for (y = 0; y < g_cv_h; y++) memcpy(&g_hr[(y0 + y) * HR_W + x0], &g_cv_px[(size_t)y * CV_BW], (size_t)g_cv_w * 4);
        return;
    }
    hr_textc(cx, 330, g_cv_state == CVS_NONE ? "Sin carátula" : g_cv_state == CVS_BIG ? "PNG muy grande" : g_cv_state == CVS_UNSUP ? "PNG no compatible" : "PNG inválido", FS_M, HC_DIM);
    if (g_cv_state == CVS_BIG) hr_textc(cx, 372, "máx. 1024 px y 3 MB", FS_S, HC_DIM);
    else hr_textc(cx, 372, g_cv_state == CVS_NONE ? "Pon en la carpeta covers:" : "Revisa el archivo:", FS_S, HC_DIM);
    fit_px(t, sizeof t, g_cv_file, CV_BW - 8, FS_S);
    hr_textc(cx, 408, t, FS_S, HC_YEL);
}

/* Selector de ROM: lista de USRDIR/roms. 1 = eligio y cargo una ROM, 0 = volvio sin elegir.
 * v1.9.2: con pick_only = 1 (el host en plena partida online) NO carga nada: deja nombre, CRC32 y tamano de la ROM elegida
 * en g_pick_* y devuelve 1; la partida sigue en marcha por debajo (ver gsw_ask_host). */
static int ui_rom_select(int pick_only)
{
    enum { VIS = 9 };
    int sel = 0, top = 0, i, last_sel = -1, hold = 0;
    g_stage = "elegir-rom";
    roms_scan();
    { char cdir[300]; snprintf(cdir, sizeof cdir, "%s/covers", g_dir); mkdir(cdir, 0777); }   /* v1.9.8: carpeta de caratulas */
    g_cv_state = CVS_PEND;
    for (i = 0; i < g_nroms; i++) if (g_rom_name[0] && !strcmp(g_roms[i].name, g_rom_name)) sel = i;
    while (g_running) {
        uint16_t e;
        char line[64], nm[48];
        pump();
        ui_keepalive();
        e = ui_edges();
        if (e & UI_CANCEL) return 0;
        if (g_nroms > 0) {
            if (e & UI_UP)    sel = (sel + g_nroms - 1) % g_nroms;
            if (e & UI_DOWN)  sel = (sel + 1) % g_nroms;
            if (e & UI_LEFT)  sel = sel - 10 < 0 ? 0 : sel - 10;
            if (e & UI_RIGHT) sel = sel + 10 >= g_nroms ? g_nroms - 1 : sel + 10;
            if ((e & (UI_OK | UI_START)) && pick_only) {
                uint8_t *b = NULL;
                size_t bs = 0;
                char rp[420];
                snprintf(rp, sizeof rp, "%s/roms/%s", g_dir, g_roms[sel].name);
                if (read_whole_file(rp, &b, &bs)) {
                    g_pick_crc = crc32_buf(b, bs); g_pick_size = (uint32_t)bs;
                    snprintf(g_pick_name, sizeof g_pick_name, "%s", g_roms[sel].name);
                    free(b);
                    return 1;
                }
                ui_message("NO PUDE LEER LA ROM", g_roms[sel].name, 300);
            } else if (e & (UI_OK | UI_START)) {
                ui_show("CARGANDO ROM...", g_roms[sel].name, NULL);
                if (rom_load(sel)) {
                    snprintf(g_last_rom, sizeof g_last_rom, "%s", g_rom_name);     /* v1.9: la recuerda para la proxima vez */
                    opts_save();
                    return 1;
                }
                ui_message("NO PUDE LEER LA ROM", g_roms[sel].name, 300);
            }
            if (sel < top) top = sel;
            if (sel >= top + VIS) top = sel - VIS + 1;
            /* v1.9: el CRC32 se calcula cuando el cursor se queda ~0,2 s sobre una ROM (no al pasar rapido) */
            if (sel != last_sel) { last_sel = sel; hold = 0; g_cv_state = CVS_PEND; }
            else if (hold < 1000) hold++;
            if (hold == 12 && hr_usable()) cv_update(sel);       /* v1.9.8: la caratula se carga cuando el cursor se queda ~0,2 s */
            if (hold == 12 && !g_roms[sel].has_crc) {
                uint8_t *b = NULL;
                size_t bs = 0;
                char rp[420];
                snprintf(rp, sizeof rp, "%s/roms/%s", g_dir, g_roms[sel].name);
                if (read_whole_file(rp, &b, &bs)) { g_roms[sel].crc = crc32_buf(b, bs); g_roms[sel].has_crc = 1; free(b); }
            }
        }
        if (hr_usable()) {
            static const HHint hh1[3] = { { "<>", "SALTAR 10", HC_BG }, { "X", "ELEGIR", HC_BX }, { "O", "VOLVER", HC_BO } };
            static const HHint hh0[1] = { { "O", "VOLVER", HC_BO } };
            hr_begin();
            hr_text(70, 100, "ELEGIR ROM", FS_H, HC_WHITE, 3);
            if (g_nroms == 0) {
                hr_panel(70, 130, 1210, 400);
                hr_text(110, 200, "NO HAY ROMS EN LA CARPETA:", FS_L, HC_WHITE, 2);
                hr_text(110, 250, "NESN00001/USRDIR/roms", FS_L, HC_YEL, 2);
                hr_text(110, 310, "Pon ahí tus ROMs de NES y vuelve a entrar aquí.", FS_M, HC_DIM, 2);
                hr_hints(hh0, 1);
            } else {
                snprintf(line, sizeof line, "%d / %d", sel + 1, g_nroms);
                hr_text(1210 - hr_tw(line, FS_L), 84, line, FS_L, HC_DIM, 2);
                hr_panel(70, 124, 1210, 558);
                for (i = 0; i < VIS && top + i < g_nroms; i++) {
                    int k = top + i, yy = 138 + i * 46;
                    char tt[ROM_NAMELEN + 4], nm2[ROM_NAMELEN + 4];
                    rom_title(tt, sizeof tt, g_roms[k].name);            /* v1.9.8: sin ".nes" y recortado por ancho */
                    fit_px(nm2, sizeof nm2, tt, 700, FS_L);
                    if (k == sel) {
                        hr_rect(86, yy, 852, yy + 42, HC_RED, 256);
                        hr_tri(100, yy + 21, 22);
                        hr_text(132, yy + 31, nm2, FS_L, HC_WHITE, 2);
                    } else hr_text(132, yy + 31, nm2, FS_L, HC_DIM, 2);
                }
                if (top > 0) hr_arrow(838, 156, 1);
                if (top + VIS < g_nroms) hr_arrow(838, 536, 0);
                cv_draw();
                hr_panel(70, 568, 1210, 656);
                fit_name(nm, sizeof nm, g_roms[sel].name, 60);
                hr_text(96, 604, nm, FS_M, HC_YEL, 2);
                if (g_roms[sel].has_crc) snprintf(line, sizeof line, "%u KB     CRC32 %08X", (unsigned)((g_roms[sel].size + 512) / 1024), (unsigned)g_roms[sel].crc);
                else snprintf(line, sizeof line, "%u KB     CRC32 ........", (unsigned)((g_roms[sel].size + 512) / 1024));
                hr_text(96, 640, line, FS_S, HC_DIM, 2);
                hr_hints(hh1, 3);
            }
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(14, "ELEGIR ROM", 2, 0xFFFFD040);
        if (g_nroms == 0) {
            ui_center(80, "NO HAY ROMS EN LA CARPETA:", 1, 0xFFFFFFFF);
            ui_center(100, "NESN00001/USRDIR/ROMS", 1, 0xFFC0C0FF);
            ui_center(124, "PON AHI TUS ROMS DE NES", 1, 0xFFC0C0FF);
            ui_center(140, "Y VUELVE A ENTRAR AQUI", 1, 0xFFC0C0FF);
        } else {
            snprintf(line, sizeof line, "%d / %d", sel + 1, g_nroms);
            ui_center(38, line, 1, 0xFFC0C0FF);
            for (i = 0; i < VIS && top + i < g_nroms; i++) {
                int k = top + i;
                fit_name(nm, sizeof nm, g_roms[k].name, 38);
                snprintf(line, sizeof line, "%s %s", k == sel ? ">" : " ", nm);
                ui_text(8, 52 + i * 12, line, 1, k == sel ? 0xFFFFFFFF : 0xFF8080A0);
            }
            if (top > 0)              ui_text(244, 52, "^", 1, 0xFFC0C0FF);
            if (top + VIS < g_nroms)  ui_text(244, 52 + (VIS - 1) * 12, "V", 1, 0xFFC0C0FF);
            {
                /* v1.9: nombre completo de la ROM marcada (hasta 2 lineas de 40 letras), tamano y CRC32 */
                const char *full = g_roms[sel].name;
                size_t fl = strlen(full);
                char l1[48], l2[48], l3[64], crc[12];
                snprintf(l1, sizeof l1, "%.40s", full);
                if (fl > 40) fit_name(l2, sizeof l2, full + 40, 40); else l2[0] = 0;
                if (g_roms[sel].has_crc) snprintf(crc, sizeof crc, "%08X", (unsigned)g_roms[sel].crc); else snprintf(crc, sizeof crc, "........");
                snprintf(l3, sizeof l3, "%u KB    CRC32 %s", (unsigned)((g_roms[sel].size + 512) / 1024), crc);
                ui_text(8, 164, l1, 1, 0xFFFFD040);
                if (l2[0]) ui_text(8, 175, l2, 1, 0xFFFFD040);
                ui_text(8, 188, l3, 1, 0xFFC0C0FF);
            }
        }
        if (g_nroms) ui_center(204, "IZQ/DER: SALTAR 10", 1, 0xFF8080A0);
        ui_center(218, g_nroms ? "X: ELEGIR   O: VOLVER" : "O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return 0;
}

/* v1.8.2: OPCIONES > PANTALLA. El modo se aplica en el acto al mover el cursor (esta misma pantalla ya sale con el modo elegido) */
static void ui_opt_screen(void)
{
    static const char *desc[3] = { "PIXELES CUADRADOS (COMO SIEMPRE)", "PROPORCION DE TV 4:3", "ESTIRADA A PANTALLA ANCHA 16:9" };
    int i;
    g_stage = "opciones-pantalla";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   { g_screen = (g_screen + 2) % 3; opts_save(); }
        if (e & UI_DOWN) { g_screen = (g_screen + 1) % 3; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "VOLVER", HC_BX }, { "O", "VOLVER", HC_BO } };
            hr_head("PANTALLA  ·  solo cambia la imagen del juego");
            hr_panel(70, 210, 900, 480);
            hr_rows(96, 232, 778, screen_names, 3, g_screen, 0, 58);
            hr_text(96, 446, desc[g_screen], FS_M, HC_GREEN, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "PANTALLA", 2, 0xFFFFD040);
        ui_center(46, "SOLO CAMBIA LA IMAGEN DEL JUEGO", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[48];
            snprintf(line, sizeof line, "%s %s", i == g_screen ? ">" : " ", screen_names[i]);
            ui_center(78 + i * 22, line, 1, i == g_screen ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(150, desc[g_screen], 1, 0xFF80FF80);
        if (!g_cfg.render) ui_center(170, "AVISO: EL MODO GPU NO USA ESTO", 1, 0xFFFFC040);
        ui_center(200, "ARRIBA/ABAJO: ELEGIR", 1, 0xFF8080A0);
        ui_center(214, "X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: pantalla = %s", screen_names[g_screen]);
}

/* v1.8.2: OPCIONES > MANDOS > MANDO n: un boton de la PS3 por cada boton del NES, y turbo A / turbo B.
 * IZQ/DER cambia el boton de la fila marcada y SALTA los que ya usa otra fila (no mueve botones ajenos). */
static void ui_opt_pad(int port)
{
    int sel = 0, i;          /* filas 0..5 = acciones, 6 = RESTAURAR ESTE MANDO, 7 = VOLVER */
    g_stage = "opciones-mando";
    ui_prime();
    while (g_running) {
        uint16_t e;
        char title[16];
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 7) % 8;
        if (e & UI_DOWN) sel = (sel + 1) % 8;
        if (e & UI_CANCEL) break;
        if (sel < MA_COUNT) {
            if (e & UI_LEFT)            { map_cycle(port, sel, -1); opts_save(); }
            if (e & (UI_RIGHT | UI_OK)) { map_cycle(port, sel, +1); opts_save(); }
        } else if (e & (UI_OK | UI_START)) {
            if (sel == 6) { map_defaults(port); opts_save(); }
            else break;
        }
        if (hr_usable()) {
            static const HHint hh[1] = { { "O", "VOLVER", HC_BO } };
            char sub[48];
            snprintf(sub, sizeof sub, "MANDO %d  ·  botones y turbo", port + 1);
            hr_head(sub);
            hr_panel(70, 206, 880, 606);
            for (i = 0; i < 8; i++) {
                const char *nm = i < MA_COUNT ? ma_names[i] : (i == 6 ? "RESTAURAR ESTE MANDO" : "VOLVER");
                const char *vv = i < MA_COUNT ? (g_map[port][i] == PB_NONE ? "NO" : pb_names[g_map[port][i]]) : NULL;
                hr_row2(86, 222 + i * 46, 780, 46, nm, vv, i == sel, 330);
            }
            hr_panel(910, 206, 1210, 606);
            hr_text(934, 252, "IZQ/DER", FS_M, HC_YEL, 2);
            hr_text(934, 290, "cambia el botón", FS_S, HC_DIM, 2);
            hr_text(934, 322, "(salta los usados)", FS_S, HC_DIM, 2);
            hr_text(934, 388, "TURBO", FS_M, HC_YEL, 2);
            hr_text(934, 426, "15 pulsos por", FS_S, HC_DIM, 2);
            hr_text(934, 458, "segundo", FS_S, HC_DIM, 2);
            if (port == 0) {
                hr_text(934, 524, "MANDO 1", FS_M, HC_AMBER, 2);
                hr_text(934, 562, "R3 = menú", FS_S, HC_AMBER, 2);
                hr_text(934, 594, "L2 = captura", FS_S, HC_AMBER, 2);
            }
            hr_hints(hh, 1);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        snprintf(title, sizeof title, "MANDO %d", port + 1);
        ui_center(14, title, 2, 0xFFFFD040);
        for (i = 0; i < 8; i++) {
            char line[56];
            uint32_t col = i == sel ? 0xFFFFFFFF : 0xFF8080A0;
            if (i < MA_COUNT)
                snprintf(line, sizeof line, "%s %-8s %s", i == sel ? ">" : " ", ma_names[i], g_map[port][i] == PB_NONE ? "NO" : pb_names[g_map[port][i]]);
            else
                snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", i == 6 ? "RESTAURAR ESTE MANDO" : "VOLVER");
            ui_text(40, 44 + i * 16, line, 1, col);
        }
        ui_center(176, "IZQ/DER: CAMBIAR (SALTA LOS USADOS)", 1, 0xFFC0C0FF);
        ui_center(190, "TURBO: 15 PULSOS POR SEGUNDO", 1, 0xFFC0C0FF);
        if (port == 0) ui_center(204, "MANDO 1: R3 = MENU   L2 = CAPTURA", 1, 0xFFFFC040);
        ui_center(218, "O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

static void ui_opt_pads(void)
{
    static const char *items[4] = { "MANDO 1", "MANDO 2", "RESTAURAR LOS DOS", "VOLVER" };
    int sel = 0, i;
    g_stage = "opciones-mandos";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 3) % 4;
        if (e & UI_DOWN) sel = (sel + 1) % 4;
        if (e & UI_CANCEL) break;
        if (e & (UI_OK | UI_START)) {
            if (sel < 2) { ui_opt_pad(sel); ui_prime(); g_stage = "opciones-mandos"; }
            else if (sel == 2) { map_defaults(0); map_defaults(1); opts_save(); }
            else break;
        }
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "ENTRAR", HC_BX }, { "O", "VOLVER", HC_BO } };
            hr_head("MANDOS  ·  botones y turbo de cada mando");
            hr_panel(70, 210, 900, 540);
            hr_rows(96, 232, 778, items, 4, sel, 0, 58);
            hr_text(96, 512, "Vale para SOLO, 1 vs 1 y 4 jugadores", FS_S, HC_DIM, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "MANDOS", 2, 0xFFFFD040);
        ui_center(46, "BOTONES Y TURBO DE CADA MANDO", 1, 0xFFC0C0FF);
        for (i = 0; i < 4; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", items[i]);
            ui_center(84 + i * 22, line, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(190, "VALE PARA SOLO, 1 VS 1 Y 4 JUGADORES", 1, 0xFF8080A0);
        ui_center(204, "ARRIBA/ABAJO + X", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

/* v1.9: OPCIONES > SONIDO (volumen 0 a 100, de 10 en 10; se guarda solo). En el menu no suena nada: se oye al jugar. */
static void ui_opt_sound(void)
{
    int i;
    g_stage = "opciones-sonido";
    ui_prime();
    while (g_running) {
        uint16_t e;
        char line[48], bar[16];
        pump();
        e = ui_edges();
        if (e & (UI_LEFT | UI_DOWN))  { g_volume = g_volume - 10 < 0 ? 0 : g_volume - 10; opts_save(); }
        if (e & (UI_RIGHT | UI_UP))   { g_volume = g_volume + 10 > 100 ? 100 : g_volume + 10; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        if (hr_usable()) {
            static const HHint hh[2] = { { "<>", "CAMBIAR", HC_BG }, { "O", "VOLVER", HC_BO } };
            char num[12];
            int nx;
            hr_head("SONIDO  ·  volumen");
            hr_panel(230, 210, 1050, 560);
            hr_text(270, 262, "VOLUMEN", FS_M, HC_DIM, 2);
            snprintf(num, sizeof num, "%d", g_volume);
            nx = 270 + hr_text(270, 360, num, FS_X, HC_YEL, 4);
            hr_text(nx + 8, 360, "%", FS_H, HC_YEL, 3);
            for (i = 0; i < 10; i++)
                hr_rect(270 + i * 76, 392, 270 + i * 76 + 66, 428, i < g_volume / 10 ? HC_GREEN : 0xFF28368Au, 256);
            hr_text(270, 484, g_volume == 0 ? "Silencio" : "100 % es el volumen de siempre", FS_S, HC_DIM, 2);
            if (!g_cfg.audio) hr_text(270, 524, "AVISO: SONIDO APAGADO (R2 AL ABRIR)", FS_S, HC_AMBER, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "SONIDO", 2, 0xFFFFD040);
        snprintf(line, sizeof line, "VOLUMEN  %d%%", g_volume);
        ui_center(76, line, 2, 0xFFFFFFFF);
        for (i = 0; i < 10; i++) bar[i] = (char)(i < g_volume / 10 ? '#' : '-');
        bar[10] = 0;
        if (g_hr_on) hr_vol_bar(108, g_volume / 10); else ui_center(108, bar, 2, 0xFF80FF80);
        ui_center(140, g_volume == 0 ? "SILENCIO" : "100% ES EL VOLUMEN DE SIEMPRE", 1, 0xFFC0C0FF);
        if (!g_cfg.audio) ui_center(158, "AVISO: SONIDO APAGADO (R2 AL ABRIR)", 1, 0xFFFFC040);
        ui_center(190, "IZQ/DER: BAJAR / SUBIR", 1, 0xFF8080A0);
        ui_center(204, "X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: volumen = %d", g_volume);
}

/* v1.9: OPCIONES > INFO DE RED: que se ve arriba a la izquierda durante una partida online (no cambia la red, solo lo que se dibuja) */
static void ui_opt_netinfo(void)
{
    static const char *names[3] = { "SOLO AL INICIO (5 S)", "SIEMPRE", "NO MOSTRAR" };
    static const char *desc[3] = { "COMO HASTA AHORA", "DELAY, FPS Y TRABAS EN VIVO", "SOLO SALE EL AVISO ROJO DE DESYNC" };
    int i;
    g_stage = "opciones-info-red";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   { g_netinfo = (g_netinfo + 2) % 3; opts_save(); }
        if (e & UI_DOWN) { g_netinfo = (g_netinfo + 1) % 3; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "VOLVER", HC_BX }, { "O", "VOLVER", HC_BO } };
            hr_head("INFO DE RED  ·  en partida online, arriba a la izquierda");
            hr_panel(70, 210, 900, 570);
            hr_rows(96, 232, 778, names, 3, g_netinfo, 0, 58);
            hr_text(96, 446, desc[g_netinfo], FS_M, HC_GREEN, 2);
            hr_text(96, 496, "DELAY = cuadros de espera (1 cuadro = 17 ms)", FS_S, HC_DIM, 2);
            hr_text(96, 532, "TRABAS = cuadros lentos en el último segundo", FS_S, HC_DIM, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "INFO DE RED", 2, 0xFFFFD040);
        ui_center(46, "EN PARTIDA ONLINE (ARRIBA A LA IZQUIERDA)", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[48];
            snprintf(line, sizeof line, "%s %s", i == g_netinfo ? ">" : " ", names[i]);
            ui_center(84 + i * 22, line, 1, i == g_netinfo ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(156, desc[g_netinfo], 1, 0xFF80FF80);
        ui_center(176, "DELAY = CUADROS DE ESPERA (1 CUADRO = 17 MS)", 1, 0xFF8080A0);
        ui_center(190, "TRABAS = CUADROS LENTOS EN EL ULTIMO SEGUNDO", 1, 0xFF8080A0);
        ui_center(210, "ARRIBA/ABAJO   X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: info de red = %d", g_netinfo);
}

/* v1.9.2: OPCIONES > AJUSTE DE IMAGEN: tamano (70 a 100 %) y desplazamiento horizontal / vertical (de 2 en 2 pixeles de la TV).
 * La imagen cambia en vivo; el marco blanco es el borde del lienzo: hay que ajustar hasta verlo entero en la TV. */
static void img_clamp(void)
{
    if (g_img_size < IMG_SIZE_MIN) g_img_size = IMG_SIZE_MIN;
    if (g_img_size > 100) g_img_size = 100;
    if (g_img_dx < -IMG_SHIFT_MAX) g_img_dx = -IMG_SHIFT_MAX;
    if (g_img_dx > IMG_SHIFT_MAX) g_img_dx = IMG_SHIFT_MAX;
    if (g_img_dy < -IMG_SHIFT_MAX) g_img_dy = -IMG_SHIFT_MAX;
    if (g_img_dy > IMG_SHIFT_MAX) g_img_dy = IMG_SHIFT_MAX;
}

static int hr_adj_ok(void)
{
    int a = g_adjusting, ok, dw, dh, z;
    g_adjusting = 0;
    ok = hr_usable();
    g_adjusting = a;
    shot_geometry(&dw, &dh, &z);
    return ok && dw == HR_W && dh == HR_H;
}

static void ui_opt_image(void)
{
    int sel = 0, i, x, y;
    g_stage = "opciones-imagen";
    g_adjusting = 1;                        /* v1.9.3: esta pantalla muestra el marco con la geometria real del juego */
    ui_prime();
    while (g_running) {
        uint16_t e;
        char line[48];
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 4) % 5;
        if (e & UI_DOWN) sel = (sel + 1) % 5;
        if (e & UI_CANCEL) break;
        if (sel <= 2 && (e & (UI_LEFT | UI_RIGHT))) {
            int dir = (e & UI_RIGHT) ? 1 : -1;
            if (sel == 0) g_img_size += dir;
            else if (sel == 1) g_img_dx += 2 * dir;
            else g_img_dy += 2 * dir;
            img_clamp();
            opts_save();
        }
        if (e & (UI_OK | UI_START)) {
            if (sel == 3) { g_img_size = 100; g_img_dx = 0; g_img_dy = 0; opts_save(); }
            else if (sel == 4) break;
        }
        ui_clear();
        if (!hr_adj_ok()) {
        ui_center(20, "AJUSTE DE IMAGEN", 2, 0xFFFFD040);
        for (i = 0; i < 5; i++) {
            uint32_t col = i == sel ? 0xFFFFFFFF : 0xFF8080A0;
            if (i == 0)      snprintf(line, sizeof line, "%s TAMANO          %d%%", i == sel ? ">" : " ", g_img_size);
            else if (i == 1) snprintf(line, sizeof line, "%s HORIZONTAL    %+d", i == sel ? ">" : " ", g_img_dx);
            else if (i == 2) snprintf(line, sizeof line, "%s VERTICAL      %+d", i == sel ? ">" : " ", g_img_dy);
            else             snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", i == 3 ? "RESTAURAR (100%, 0, 0)" : "VOLVER");
            ui_text(40, 56 + i * 16, line, 1, col);
        }
        ui_center(150, "IZQ/DER: CAMBIAR   ARRIBA/ABAJO: FILA", 1, 0xFFC0C0FF);
        ui_center(166, "AJUSTA HASTA VER EL MARCO BLANCO ENTERO", 1, 0xFF80FF80);
        ui_center(180, "(ES EL BORDE DE LA IMAGEN)", 1, 0xFF80FF80);
        if (!g_cfg.render) ui_center(196, "AVISO: EL MODO GPU NO USA ESTO", 1, 0xFFFFC040);
        ui_center(212, "O: VOLVER", 1, 0xFF8080A0);
        }
        /* marco blanco en el borde del lienzo, con una marca en cada esquina y en el centro de cada lado */
        for (x = 0; x < SCR_W; x++) { g_fb[x] = 0xFFFFFFFF; g_fb[(SCR_H - 1) * SCR_W + x] = 0xFFFFFFFF; }
        for (y = 0; y < SCR_H; y++) { g_fb[y * SCR_W] = 0xFFFFFFFF; g_fb[y * SCR_W + SCR_W - 1] = 0xFFFFFFFF; }
        for (i = 0; i < 8; i++) {
            g_fb[(1 + i) * SCR_W + 1] = 0xFFFF4040; g_fb[(1 + i) * SCR_W + SCR_W - 2] = 0xFFFF4040;
            g_fb[(SCR_H - 2 - i) * SCR_W + 1] = 0xFFFF4040; g_fb[(SCR_H - 2 - i) * SCR_W + SCR_W - 2] = 0xFFFF4040;
            g_fb[SCR_W + 1 + i] = 0xFFFF4040; g_fb[SCR_W + SCR_W - 2 - i] = 0xFFFF4040;
            g_fb[(SCR_H - 2) * SCR_W + 1 + i] = 0xFFFF4040; g_fb[(SCR_H - 2) * SCR_W + SCR_W - 2 - i] = 0xFFFF4040;
        }
        if (hr_adj_ok()) {          /* v1.9.7: el marco (con la geometria real) y encima el cuadro de ajustes a 1280x720 */
            static const HHint hh[2] = { { "<>", "CAMBIAR", HC_BG }, { "O", "VOLVER", HC_BO } };
            static unsigned fcn;
            int dw, dh, z;
            char v[24];
            shot_geometry(&dw, &dh, &z);
            hr_init();
            memset(g_hr, 0, sizeof g_hr);
            canvas_blit_adj(g_hr, dw, dh, g_screen, z, g_fb, &fcn, g_img_size, g_img_dx, g_img_dy);
            hr_panel(300, 150, 980, 590);
            hr_text(330, 204, "AJUSTE DE IMAGEN", FS_H, HC_YEL, 3);
            for (i = 0; i < 5; i++) {
                const char *nm = i == 0 ? "TAMAÑO" : i == 1 ? "HORIZONTAL" : i == 2 ? "VERTICAL" : i == 3 ? "RESTAURAR  (100 %, 0, 0)" : "VOLVER";
                v[0] = 0;
                if (i == 0) snprintf(v, sizeof v, "%d %%", g_img_size);
                else if (i == 1) snprintf(v, sizeof v, "%+d", g_img_dx);
                else if (i == 2) snprintf(v, sizeof v, "%+d", g_img_dy);
                hr_row2(320, 226 + i * 46, 640, 46, nm, v[0] ? v : NULL, i == sel, 400);
            }
            hr_text(330, 500, "Ajusta hasta ver el marco blanco entero", FS_S, HC_GREEN, 2);
            hr_text(330, 534, "(es el borde de la imagen)", FS_S, HC_GREEN, 2);
            hr_hints(hh, 2);
            g_hr_on = 1;
        }
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    g_adjusting = 0;
    logf_("opciones: imagen = %d%% %+d %+d", g_img_size, g_img_dx, g_img_dy);
}

static void ui_options(void)
{
    enum { N_OPT = 7 };
    static const char *items[N_OPT] = { "PANTALLA", "MANDOS (BOTONES Y TURBO)", "SONIDO (VOLUMEN)", "INFO DE RED EN PARTIDA", "AJUSTE DE IMAGEN", "", "VOLVER" };
    int sel = 0, i;
    g_stage = "opciones";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + N_OPT - 1) % N_OPT;
        if (e & UI_DOWN) sel = (sel + 1) % N_OPT;
        if (e & UI_CANCEL) break;
        if (sel == 5 && (e & (UI_OK | UI_START | UI_LEFT | UI_RIGHT))) { g_showfps = !g_showfps; opts_save(); }   /* FPS: se prende y apaga en esta misma fila */
        else if (e & (UI_OK | UI_START)) {
            if (sel == 0) { ui_opt_screen(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 1) { ui_opt_pads(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 2) { ui_opt_sound(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 3) { ui_opt_netinfo(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 4) { ui_opt_image(); ui_prime(); g_stage = "opciones"; }
            else break;
        }
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "ENTRAR", HC_BX }, { "O", "VOLVER", HC_BO } };
            char fps[40], val[24];
            const char *rows[7];
            for (i = 0; i < 7; i++) rows[i] = items[i];
            snprintf(fps, sizeof fps, "FPS EN PANTALLA: %s", g_showfps ? "SÍ" : "NO");
            rows[5] = fps;
            hr_head("OPCIONES  ·  se guardan solas");
            hr_panel(70, 210, 900, 650);
            hr_rows(96, 232, 778, rows, 7, sel, 0, 58);
            hr_panel(940, 210, 1210, 430);
            hr_text(962, 250, "Ahora", FS_M, HC_YEL, 2);
            hr_text(962, 290, "Pantalla:", FS_S, HC_DIM, 2);
            hr_text(962, 324, screen_names[g_screen], hr_tw(screen_names[g_screen], FS_M) > 236 ? FS_S : FS_M, HC_WHITE, 2);
            hr_text(962, 368, "Volumen:", FS_S, HC_DIM, 2);
            snprintf(val, sizeof val, "%d %%", g_volume);
            hr_text(962, 402, val, FS_M, HC_WHITE, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "OPCIONES", 2, 0xFFFFD040);
        ui_center(46, "SE GUARDAN SOLAS", 1, 0xFFC0C0FF);
        for (i = 0; i < N_OPT; i++) {
            char line[48];
            if (i == 5) snprintf(line, sizeof line, "%s FPS EN PANTALLA: %s", i == sel ? ">" : " ", g_showfps ? "SI" : "NO");
            else snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", items[i]);
            ui_center(66 + i * 18, line, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(200, "ARRIBA/ABAJO + X", 1, 0xFF8080A0);
        ui_center(214, "O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

static int ui_menu(void)
{
    static const char *items[6] = { "ELEGIR ROM", "CREAR SALA (HOST)", "UNIRSE A UNA SALA", "SOLO - 2 MANDOS", "MULTIJUGADOR DE 4", "OPCIONES" };
    static const int modes[6] = { MODE_ROM, MODE_HOST, MODE_JOIN, MODE_SOLO, MODE_FOUR, MODE_OPT };   /* mismo orden que items */
    int i;
    g_stage = "menu";
    ui_prime();
    while (g_running) {
        uint16_t e;
        char l[80], nm[48];
        pump();
        e = ui_edges();
        if (e & UI_UP)   g_menu_sel = (g_menu_sel + 5) % 6;
        if (e & UI_DOWN) g_menu_sel = (g_menu_sel + 1) % 6;
        if (e & UI_CANCEL) {
            /* v1.9.4: O en el menu principal sale al XMB, sin confirmar (igual que la salida del sistema: g_running = 0) */
            logf_("salida al XMB pedida con O en el menu principal");
            g_running = 0;
            return -1;
        }
        if (e & (UI_OK | UI_START)) {
            /* sin ROM elegida el juego queda en stand-by: solo se puede entrar a ELEGIR ROM y a OPCIONES */
            if (modes[g_menu_sel] != MODE_ROM && modes[g_menu_sel] != MODE_OPT && !g_rom) ui_message("PRIMERO ELIGE UNA ROM", "OPCION: ELEGIR ROM", 120);
            else return modes[g_menu_sel];
        }
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "ELEGIR", HC_BX }, { "O", "SALIR AL XMB", HC_BO } };
            unsigned dis = 0;
            for (i = 0; i < 6; i++) if (!g_rom && modes[i] != MODE_ROM && modes[i] != MODE_OPT) dis |= 1u << i;
            hr_head("NES CON NETPLAY PARA PS3");
            hr_panel(70, 210, 790, 652);
            if (g_rom) {
                fit_name(nm, sizeof nm, g_rom_name, 34);
                snprintf(l, sizeof l, "ROM: %s", nm);
                hr_text(96, 252, l, FS_M, HC_GREEN, 2);
            } else hr_text(96, 252, "ROM: NINGUNA (ELIGE UNA)", FS_M, HC_AMBER, 2);
            hr_rows(96, 280, 668, items, 6, g_menu_sel, dis, 58);
            hr_panel(830, 210, 1210, 440);
            hr_text(856, 252, "EN PARTIDA", FS_M, HC_YEL, 2);
            hr_text(856, 302, "R3", FS_M, HC_WHITE, 2);  hr_text(930, 302, "menú", FS_S, HC_DIM, 2);
            hr_text(856, 352, "L2", FS_M, HC_WHITE, 2);  hr_text(930, 352, "captura de pantalla", FS_S, HC_DIM, 2);
            hr_text(856, 402, "O", FS_M, HC_WHITE, 2);   hr_text(930, 402, "salir al XMB (aquí)", FS_S, HC_DIM, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
        ui_center(46, "NES CON NETPLAY PARA PS3", 1, 0xFFC0C0FF);
        if (g_rom) {
            fit_name(nm, sizeof nm, g_rom_name, 34);
            snprintf(l, sizeof l, "ROM: %s", nm);
            ui_center(66, l, 1, 0xFF80FF80);
        } else {
            ui_center(66, "ROM: NINGUNA (ELIGE UNA)", 1, 0xFFFFC040);
        }
        for (i = 0; i < 6; i++) {
            char line[40];
            uint32_t col = i == g_menu_sel ? 0xFFFFFFFF : 0xFF8080A0;
            if (!g_rom && modes[i] != MODE_ROM && modes[i] != MODE_OPT) col = i == g_menu_sel ? 0xFFA0A0B0 : 0xFF505068;   /* bloqueadas sin ROM */
            snprintf(line, sizeof line, "%s %s", i == g_menu_sel ? ">" : " ", items[i]);
            ui_center(90 + i * 17, line, 1, col);
        }
        ui_center(196, "ARRIBA/ABAJO + X", 1, 0xFF8080A0);
        ui_center(209, "EN PARTIDA: R3 = MENU   L2 = CAPTURA", 1, 0xFF8080A0);
        ui_center(222, "O: SALIR AL XMB", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

/* v1.8: submenu del modo de 4 jugadores. Devuelve MODE_HOST, MODE_JOIN o -1 (volver). Copia de la idea de ui_menu. */
static int ui_menu4(void)
{
    static const char *items[3] = { "CREAR SALA DE 4 (HOST)", "UNIRSE A SALA DE 4", "VOLVER" };
    int sel = 0, i;
    g_stage = "menu-4";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 2) % 3;
        if (e & UI_DOWN) sel = (sel + 1) % 3;
        if (e & UI_CANCEL) return -1;
        if (e & (UI_OK | UI_START)) return sel == 0 ? MODE_HOST : sel == 1 ? MODE_JOIN : -1;
        if (hr_usable()) {
            static const HHint hh[2] = { { "X", "ELEGIR", HC_BX }, { "O", "VOLVER", HC_BO } };
            hr_head("MULTIJUGADOR DE 4  ·  Four Score");
            hr_panel(70, 210, 790, 570);
            hr_text(96, 252, "HOST: mandos 1 y 2", FS_M, HC_GREEN, 2);
            hr_text(96, 290, "EL QUE SE UNE: mandos 3 y 4", FS_M, HC_GREEN, 2);
            hr_rows(96, 316, 668, items, 3, sel, 0, 58);
            hr_text(96, 540, "Solo juegos con Four Score", FS_S, HC_DIM, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
        ui_center(46, "MULTIJUGADOR DE 4 (FOUR SCORE)", 1, 0xFFC0C0FF);
        ui_center(66, "HOST: MANDOS 1 Y 2", 1, 0xFF80FF80);
        ui_center(80, "EL QUE SE UNE: MANDOS 3 Y 4", 1, 0xFF80FF80);
        for (i = 0; i < 3; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", items[i]);
            ui_center(110 + i * 22, line, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(190, "SOLO JUEGOS CON FOUR SCORE", 1, 0xFF8080A0);
        ui_center(204, "EN PARTIDA: R3 = MENU   L2 = CAPTURA", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

static int ui_enter_code(char *out)
{
    int d[10], pos = 0, i, saved = 0;
    memset(d, 0, sizeof d);
    /* v1.9.3: si hay un codigo guardado de la vez anterior, aparece ya escrito; se confirma con START (no se conecta solo) */
    if (strlen(g_last_code) == 10) {
        for (i = 0; i < 10; i++) d[i] = g_last_code[i] - '0';
        saved = 1;
    }
    while (g_running) {
        uint16_t e;
        char line[40];
        pump();
        e = ui_edges();
        if (e & UI_UP)    { d[pos] = (d[pos] + 1) % 10; saved = 0; }
        if (e & UI_DOWN)  { d[pos] = (d[pos] + 9) % 10; saved = 0; }
        if (e & UI_LEFT)  { if (pos > 0) pos--; }
        if (e & (UI_RIGHT | UI_OK)) { if (pos < 9) pos++; }
        if (e & UI_CANCEL) return 0;
        if (e & UI_START) {
            for (i = 0; i < 10; i++) out[i] = (char)('0' + d[i]);
            out[10] = 0;
            {
                uint32_t vip; int vport;
                if (strcmp(g_last_code, out) != 0 && code_decode(out, &vip, &vport)) {   /* lo recuerda para la proxima vez (aunque se apague la PS3); un codigo invalido no se guarda */
                    snprintf(g_last_code, sizeof g_last_code, "%.10s", out);
                    opts_save();
                    logf_("codigo de sala guardado en opciones.txt");
                }
            }
            return 1;
        }
        if (hr_usable()) {
            static const HHint hh[2] = { { "START", "CONECTAR", HC_BX }, { "O", "CANCELAR", HC_BO } };
            int adv = hr_tw("0", FS_X), tot = 10 * adv + 2 * 36, x0 = (HR_W - tot) / 2, k;
            hr_head("UNIRSE A UNA SALA");
            hr_panel(230, 200, 1050, 600);
            hr_text(270, 252, "ESCRIBE EL CÓDIGO DEL HOST", FS_M, HC_DIM, 2);
            for (k = 0; k < 10; k++) {
                char c1[2] = { (char)('0' + d[k]), 0 };
                int x = x0 + k * adv + (k >= 3 ? 36 : 0) + (k >= 6 ? 36 : 0);
                hr_text(x, 372, c1, FS_X, k == pos ? HC_YEL : HC_WHITE, 4);
                if (k == pos) hr_rect(x + 4, 392, x + adv - 8, 402, HC_YEL, 256);
            }
            snprintf(line, sizeof line, "Dígito %d de 10", pos + 1);
            hr_text(270, 460, line, FS_S, HC_DIM, 2);
            if (saved) hr_text(270, 500, "Último código usado: START para conectar", FS_S, HC_GREEN, 2);
            hr_text(270, 548, "ARRIBA/ABAJO cambia el dígito  ·  IZQ/DER mueve", FS_S, HC_DIM, 2);
            hr_hints(hh, 2);
            present();
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
            continue;
        }
        ui_clear();
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
        ui_center(60, "ESCRIBE EL CODIGO DEL HOST", 1, 0xFFFFFFFF);
        for (i = 0; i < 10; i++) {
            char c[2] = { (char)('0' + d[i]), 0 };
            int x = 24 + i * 20 + (i >= 3 ? 8 : 0) + (i >= 6 ? 8 : 0);     /* grupos 3-3-4 */
            ui_text(x, 100, c, 2, i == pos ? 0xFFFFFF40 : 0xFFFFFFFF);
            if (i == pos) ui_text(x, 118, "-", 2, 0xFFFFFF40);
        }
        snprintf(line, sizeof line, "DIGITO %d DE 10", pos + 1);
        ui_center(140, line, 1, 0xFFC0C0FF);
        if (saved) ui_center(154, "ULTIMO CODIGO USADO (START: CONECTAR)", 1, 0xFF80FF80);
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
    for (;;) {
        if (!core_load()) { net_close(); return 0; }
        ok = session_loop(is_host ? 0 : 1, D, g_maxframes);
        core_unload();
        if (!g_sw_pending) break;
        /* v1.9.2: cambio de juego: marca de fin, ROM nueva y otra sesion con el mismo delay (sin repetir el handshake) */
        g_sw_pending = 0;
        if (!game_switch_apply()) { ok = 0; break; }
    }
    net_close();
    return ok;
}

static int run_host_inner(void)
{
    uint32_t ip = 0;
    char code[20], l2[48], l3[48];
    int lfd, D = 0, got_ip = 0, mism = 0;
    uint32_t col3;
    Upnp up;

    net_ensure();
    memset(&up, 0, sizeof up);
    if (g_cfg.upnp) {
        g_stage = "upnp";
        ui_show("CREANDO SALA...", "ABRIENDO EL PUERTO (UPNP)", NULL);
        upnp_open(g_cfg.port, &up);
        if (!g_running) return 1;
    } else {
        logf_("upnp: apagado (upnp=off en config.txt)");
    }
    g_stage = "buscando-ip";
    ui_show("CREANDO SALA...", "BUSCANDO TU IP PUBLICA", NULL);
    if (g_cfg.public_ip[0] && parse_ip(g_cfg.public_ip, &ip)) { got_ip = 1; logf_("IP publica fijada a mano (public_ip=)"); }
    else if (get_public_ip(&ip)) got_ip = 1;
    else logf_("ipify: no pude obtener la IP publica");
    if (!got_ip && up.public_ip && !ip_privada(up.public_ip)) {
        ip = up.public_ip; got_ip = 1;
        logf_("uso la IP WAN que dio el router por UPnP");
    }
    if (!got_ip) { g_err = "NO PUDE OBTENER TU IP PUBLICA"; return 0; }
    if (up.public_ip && up.public_ip != ip) {
        mism = 1;
        logf_("AVISO: la IP del router (%u.%u.%u.%u) es distinta de la que ve internet (%u.%u.%u.%u): "
              "probable CGNAT o doble NAT, desde afuera no se llega al puerto", IP4(up.public_ip), IP4(ip));
    }
    code_encode(ip, g_cfg.port, code);
    logf_("sala creada: ip=%u.%u.%u.%u puerto=%d codigo=%s", IP4(ip), g_cfg.port, code);

    lfd = tcp_listen(g_cfg.port);
    if (lfd < 0) { g_err = "NO PUDE ABRIR EL PUERTO"; return 0; }

    snprintf(l2, sizeof l2, "PUERTO TCP %d", g_cfg.port);
    col3 = 0xFFFFC040;
    if (!g_cfg.upnp)                                   snprintf(l3, sizeof l3, "UPNP APAGADO: ABRE EL PUERTO");
    else if (!up.router)                               snprintf(l3, sizeof l3, "SIN UPNP: ABRE EL PUERTO A MANO");
    else if (up.public_ip && ip_privada(up.public_ip)) snprintf(l3, sizeof l3, "ROUTER SIN IP PUBLICA (CGNAT)");
    else if (mism)                                     snprintf(l3, sizeof l3, "ROUTER E INTERNET: IP DISTINTA");
    else if (up.opened)                              { snprintf(l3, sizeof l3, "UPNP: PUERTO ABIERTO"); col3 = 0xFF80FF80; }
    else                                               snprintf(l3, sizeof l3, "UPNP RECHAZADO: ABRE EL PUERTO");
    logf_("estado en pantalla: %s", l3);
    g_stage = "esperando-amigo";
    for (;;) {
        uint16_t e;
        pump();
        if (!g_running) { closesocket(lfd); return 1; }
        e = ui_edges();
        if (e & UI_CANCEL) { closesocket(lfd); g_err = ""; return 1; }
        if (hr_usable()) {
            hr_room_screen("CREAR SALA (HOST)", code, l2, l3, col3);
            present();
        } else {
        ui_clear();
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
        ui_center(64, "TU CODIGO DE SALA:", 1, 0xFFFFFFFF);
        { char pc[24]; code_pretty(code, pc); ui_center(84, pc, 2, 0xFFFFFF40); }
        ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
        ui_center(136, l2, 1, 0xFFC0C0FF);
        ui_center(154, l3, 1, col3);
        ui_center(176, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
        ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
        present();
        }
        {
            int r = fd_wait(lfd, POLLIN, 0);
            if (r > 0) {
                struct sockaddr_in pa;
                socklen_t pl = sizeof pa;
                int c;
                memset(&pa, 0, sizeof pa);
                c = accept(lfd, (struct sockaddr *)&pa, &pl);
                if (c >= 0) {
                    uint32_t pip = ntohl(pa.sin_addr.s_addr);
                    logf_("conexion entrante de %u.%u.%u.%u", IP4(pip));
                    g_net = c; sock_nodelay(c); break;
                }
                logf_("accept fallo (errno=%d)", errno);
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

static int run_host(void)
{
    int ok = run_host_inner();
    upnp_close();
    return ok;
}

static int run_client(void)
{
    char code[20];
    uint32_t ip;
    int port, D = 0;

    if (g_cfg.code[0]) snprintf(code, sizeof code, "%s", g_cfg.code);
    else if (!ui_enter_code(code)) { g_err = ""; return 1; }

    if (!code_decode(code, &ip, &port)) { logf_("codigo escrito=%s: INVALIDO", code); g_err = "CODIGO INVALIDO"; return 0; }
    logf_("codigo escrito=%s -> destino %u.%u.%u.%u:%d", code, IP4(ip), port);
    net_ensure();
    g_stage = "conectando";
    {
        char l2[48];
        snprintf(l2, sizeof l2, "%u.%u.%u.%u:%d", IP4(ip), port);
        ui_show("CONECTANDO...", l2, NULL);
    }
    g_net = tcp_connect(ip, port, 10000);
    if (g_net < 0) {
        g_err = g_conn_kind == 1 ? "SIN RESPUESTA DEL HOST (10 S)" : "EL HOST RECHAZO LA CONEXION";
        return 0;
    }
    logf_("connect OK en %u ms", (unsigned)g_conn_ms);
    ui_show("CONECTADO", "SINCRONIZANDO...", NULL);
    if (!handshake_client(&D)) { net_close(); return 0; }
    return run_online(0, D);
}

/* v1.8: COPIAS de run_host_inner / run_host / run_client para el modo de 4. El 1vs1 de arriba no se toca. */
/* v1.8: COPIA de run_online() para el modo de 4: carga el nucleo con 4 mandos (Four Score) y corre session_loop4 */
static int run_online4(int is_host, int D)
{
    int ok;
    g_four = 1;
    for (;;) {
        if (!core_load4()) { g_four = 0; net_close(); return 0; }
        ok = session_loop4(is_host ? 0 : 1, D, g_maxframes);
        core_unload();
        if (!g_sw_pending) break;
        g_sw_pending = 0;                                  /* v1.9.2: cambio de juego (igual que en el 1vs1) */
        if (!game_switch_apply()) { ok = 0; break; }
    }
    g_four = 0;
    net_close();
    return ok;
}

static int run_host4_inner(void)
{
    uint32_t ip = 0;
    char code[20], l2[48], l3[48];
    int lfd, D = 0, got_ip = 0, mism = 0;
    uint32_t col3;
    Upnp up;

    net_ensure();
    memset(&up, 0, sizeof up);
    if (g_cfg.upnp) {
        g_stage = "upnp";
        ui_show("CREANDO SALA...", "ABRIENDO EL PUERTO (UPNP)", NULL);
        upnp_open(g_cfg.port, &up);
        if (!g_running) return 1;
    } else {
        logf_("upnp: apagado (upnp=off en config.txt)");
    }
    g_stage = "buscando-ip";
    ui_show("CREANDO SALA...", "BUSCANDO TU IP PUBLICA", NULL);
    if (g_cfg.public_ip[0] && parse_ip(g_cfg.public_ip, &ip)) { got_ip = 1; logf_("IP publica fijada a mano (public_ip=)"); }
    else if (get_public_ip(&ip)) got_ip = 1;
    else logf_("ipify: no pude obtener la IP publica");
    if (!got_ip && up.public_ip && !ip_privada(up.public_ip)) {
        ip = up.public_ip; got_ip = 1;
        logf_("uso la IP WAN que dio el router por UPnP");
    }
    if (!got_ip) { g_err = "NO PUDE OBTENER TU IP PUBLICA"; return 0; }
    if (up.public_ip && up.public_ip != ip) {
        mism = 1;
        logf_("AVISO: la IP del router (%u.%u.%u.%u) es distinta de la que ve internet (%u.%u.%u.%u): "
              "probable CGNAT o doble NAT, desde afuera no se llega al puerto", IP4(up.public_ip), IP4(ip));
    }
    code_encode(ip, g_cfg.port, code);
    logf_("sala de 4 creada: ip=%u.%u.%u.%u puerto=%d codigo=%s", IP4(ip), g_cfg.port, code);

    lfd = tcp_listen(g_cfg.port);
    if (lfd < 0) { g_err = "NO PUDE ABRIR EL PUERTO"; return 0; }

    snprintf(l2, sizeof l2, "PUERTO TCP %d", g_cfg.port);
    col3 = 0xFFFFC040;
    if (!g_cfg.upnp)                                   snprintf(l3, sizeof l3, "UPNP APAGADO: ABRE EL PUERTO");
    else if (!up.router)                               snprintf(l3, sizeof l3, "SIN UPNP: ABRE EL PUERTO A MANO");
    else if (up.public_ip && ip_privada(up.public_ip)) snprintf(l3, sizeof l3, "ROUTER SIN IP PUBLICA (CGNAT)");
    else if (mism)                                     snprintf(l3, sizeof l3, "ROUTER E INTERNET: IP DISTINTA");
    else if (up.opened)                              { snprintf(l3, sizeof l3, "UPNP: PUERTO ABIERTO"); col3 = 0xFF80FF80; }
    else                                               snprintf(l3, sizeof l3, "UPNP RECHAZADO: ABRE EL PUERTO");
    logf_("estado en pantalla: %s", l3);
    g_stage = "esperando-amigo";
    for (;;) {
        uint16_t e;
        pump();
        if (!g_running) { closesocket(lfd); return 1; }
        e = ui_edges();
        if (e & UI_CANCEL) { closesocket(lfd); g_err = ""; return 1; }
        if (hr_usable()) {
            hr_room_screen("SALA DE 4 (HOST)", code, l2, l3, col3);
            present();
        } else {
        ui_clear();
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
        ui_center(64, "SALA DE 4 - TU CODIGO:", 1, 0xFFFFFFFF);
        { char pc[24]; code_pretty(code, pc); ui_center(84, pc, 2, 0xFFFFFF40); }
        ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
        ui_center(136, l2, 1, 0xFFC0C0FF);
        ui_center(154, l3, 1, col3);
        ui_center(176, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
        ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
        present();
        }
        {
            int r = fd_wait(lfd, POLLIN, 0);
            if (r > 0) {
                struct sockaddr_in pa;
                socklen_t pl = sizeof pa;
                int c;
                memset(&pa, 0, sizeof pa);
                c = accept(lfd, (struct sockaddr *)&pa, &pl);
                if (c >= 0) {
                    uint32_t pip = ntohl(pa.sin_addr.s_addr);
                    logf_("conexion entrante de %u.%u.%u.%u", IP4(pip));
                    g_net = c; sock_nodelay(c); break;
                }
                logf_("accept fallo (errno=%d)", errno);
            }
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
        }
    }
    closesocket(lfd);
    ui_show("AMIGO CONECTADO", "MIDIENDO LATENCIA...", NULL);
    if (!handshake_host4(&D)) { net_close(); return 0; }
    return run_online4(1, D);
}

static int run_host4(void)
{
    int ok = run_host4_inner();
    upnp_close();
    return ok;
}

static int run_client4(void)
{
    char code[20];
    uint32_t ip;
    int port, D = 0;

    if (g_cfg.code[0]) snprintf(code, sizeof code, "%s", g_cfg.code);
    else if (!ui_enter_code(code)) { g_err = ""; return 1; }

    if (!code_decode(code, &ip, &port)) { logf_("codigo escrito=%s: INVALIDO", code); g_err = "CODIGO INVALIDO"; return 0; }
    logf_("codigo escrito=%s -> destino %u.%u.%u.%u:%d", code, IP4(ip), port);
    net_ensure();
    g_stage = "conectando";
    {
        char l2[48];
        snprintf(l2, sizeof l2, "%u.%u.%u.%u:%d", IP4(ip), port);
        ui_show("CONECTANDO...", l2, NULL);
    }
    g_net = tcp_connect(ip, port, 10000);
    if (g_net < 0) {
        g_err = g_conn_kind == 1 ? "SIN RESPUESTA DEL HOST (10 S)" : "EL HOST RECHAZO LA CONEXION";
        return 0;
    }
    logf_("connect OK en %u ms", (unsigned)g_conn_ms);
    ui_show("CONECTADO", "SINCRONIZANDO...", NULL);
    if (!handshake_client4(&D)) { net_close(); return 0; }
    return run_online4(0, D);
}

static int run_solo(void)
{
    if (!core_load()) return 0;
    sram_begin();                         /* v1.9: carga el guardado de bateria (si el juego lo usa) */
    session_loop(-1, 0, g_maxframes);
    sram_save(0);                         /* v1.9: guarda al salir (si cambio) */
    g_sram_on = 0;
    core_unload();
    return 1;
}

/* ------------------------------------------------------------------ */
/* Programa                                                            */
/* ------------------------------------------------------------------ */
static int g_prepared;
static void app_prepare(const char *argv0)
{
    if (g_prepared) return;
    g_prepared = 1;
    if (argv0) {
        const char *s = strrchr(argv0, '/');
        if (s && s > argv0) {
            size_t n = (size_t)(s - argv0);
            if (n < sizeof g_dir) { memcpy(g_dir, argv0, n); g_dir[n] = 0; }
        }
    }
    {
        char p[300], q[300];
        snprintf(p, sizeof p, "%s/nesnet.log", g_dir);
        snprintf(q, sizeof q, "%s/nesnet.old.log", g_dir);
        remove(q);
        rename(p, q);                     /* conserva el log de la vez anterior */
        g_log = fopen(p, "w");
    }
    logf_("NesNet v1.9.8 (caratulas en ELEGIR ROM (USRDIR/covers, .png); menus en 1280x720 con fuente DejaVu Bold y fondo mosaico; L2 = captura de pantalla limpia en PNG; menu en partida con R3; 6 ranuras de estado; guardar/cargar estado online (host); O sale al XMB; menus siempre a pantalla completa; codigo de sala guardado al unirse) - dir=%s", g_dir);
    cfg_load();
    logf_("config: res=%d render=%s zoom=%d audio=%s", g_cfg.res, g_cfg.render ? "cpu" : "gpu", g_cfg.zoom, g_cfg.audio ? "on" : "off");
    opts_load();                          /* v1.8.2: pantalla y mandos guardados en opciones.txt */
}

static int app_main(const char *argv0)
{
    int choice = -1, from_cfg;

    app_prepare(argv0);

    /* v1.7: arranca en stand-by, sin ROM. La ROM se elige en el menu (ELEGIR ROM) antes de crear/unirse/jugar */
    logf_("stand-by: sin ROM elegida (roms en %s/roms)", g_dir);

    core_boot();

    /* v1.9: si hay una ultima ROM recordada y el archivo sigue en la carpeta, queda ya elegida (el juego sigue sin arrancar) */
    if (g_last_rom[0]) {
        int i, found = -1;
        roms_scan();
        for (i = 0; i < g_nroms; i++) if (!strcmp(g_roms[i].name, g_last_rom)) found = i;
        if (found >= 0 && rom_load(found)) { logf_("ultima ROM recordada y cargada: %s", g_rom_name); g_menu_sel = 1; }
        else logf_("la ultima ROM recordada (%s) ya no esta o no se pudo leer: stand-by", g_last_rom);
    }

    from_cfg = g_cfg.mode[0] != 0;
    if (from_cfg) { logf_("config.txt trae mode=%s: se ignora, primero hay que elegir ROM en el menu", g_cfg.mode); from_cfg = 0; }
    while (g_running) {
        int ok = 1;
        if (choice < 0) choice = ui_menu();
        if (choice < 0) break;
        if (choice == MODE_ROM) {
            if (ui_rom_select(0)) g_menu_sel = 1;          /* tras elegir, el cursor pasa a CREAR SALA */
            choice = -1;
            continue;
        }
        if (choice == MODE_OPT) {                         /* v1.8.2: OPCIONES (pantalla y mandos) no necesita ROM */
            ui_options();
            choice = -1;
            continue;
        }
        if (!g_rom) { choice = -1; continue; }             /* seguridad: sin ROM no se arranca nada */
        if (choice == MODE_FOUR) {
            /* v1.8: modo de 4 jugadores: submenu aparte con host y unirse (copias del 1vs1, otro protocolo) */
            int sub = ui_menu4();
            if (sub < 0) { choice = -1; continue; }         /* VOLVER / O: regresa al menu principal */
            logf_("modo elegido: MULTIJUGADOR DE 4 - %s", sub == MODE_HOST ? "CREAR SALA (host, mandos 1-2)" : "UNIRSE (mandos 3-4)");
            g_err = "";
            ok = sub == MODE_HOST ? run_host4() : run_client4();
            choice = -1;
        } else {
        logf_("modo elegido: %s", choice == MODE_SOLO ? "SOLO (2 mandos)" : choice == MODE_HOST ? "CREAR SALA (host)" : "UNIRSE (cliente)");
        g_err = "";
        if (choice == MODE_SOLO) ok = run_solo();
        else if (choice == MODE_HOST) ok = run_host();
        else ok = run_client();
        choice = -1;
        }
#ifdef NESNET_HOST
        if (g_maxframes && !g_ui_has_script) g_running = 0;   /* pruebas: una sola sesion (con guion, sigue hasta que se agote) */
#endif
        if (!ok || g_err[0]) {
            logf_("fin con error: %s", g_err);
            if (g_err[0]) ui_message(g_err, "X: VOLVER AL MENU", 600);
        }
    }
    logf_("salida");
    au_close();
    retro_deinit();
    if (g_log) fclose(g_log);
    return 0;
}

#ifdef NESNET_PS3
int main(int argc, const char *argv[])
{
    app_prepare(argc > 0 ? argv[0] : NULL);
    ioPadInit(7);
    /* Modo seguro sin tocar archivos: mantener L1 al arrancar = forzar 720p; R1 = render por CPU */
    {
        int i;
        for (i = 0; i < 25; i++) {            /* ~0,5 s para que el mando responda */
            padData *d = pad_read(0);
            if (d->BTN_L1) { g_cfg.res = 720; }
            if (d->BTN_R1) { g_cfg.render = 1; }
            if (d->BTN_R2) { g_cfg.audio = 0; }
            usleep(20000);
        }
        if (g_cfg.res || g_cfg.render) logf_("config final: res=%d render=%s", g_cfg.res, g_cfg.render ? "cpu" : "gpu");
    }
    platform_init();
    au_open();
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
    if (g_hr_on) {      /* v1.9.7: cuadro de menu de 1280x720 */
        fprintf(f, "P6\n%d %d\n255\n", HR_W, HR_H);
        for (i = 0; i < HR_W * HR_H; i++) {
            uint8_t px[3] = { (uint8_t)(g_hr[i] >> 16), (uint8_t)(g_hr[i] >> 8), (uint8_t)g_hr[i] };
            fwrite(px, 1, 3, f);
        }
        fclose(f);
        return;
    }
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
        ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
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
            if (hr_usable()) hr_room_screen("SALA DE 4 (HOST)", code, "puerto 7777", "UPNP: PUERTO ABIERTO", 0xFF80FF80u); else {
            ui_clear();
            ui_center(20, "NESNET V1.9.8", 2, 0xFFFFD040);
            ui_center(64, "TU CODIGO DE SALA:", 1, 0xFFFFFFFF);
            { char pc[24]; code_pretty(code, pc); ui_center(84, pc, 2, 0xFFFFFF40); }
            ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
            ui_center(136, "PUERTO 7777", 1, 0xFFC0C0FF);
            ui_center(170, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
            ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
            }
            snprintf(p, sizeof p, "%s/host.ppm", argv[2]); dump_ppm(p);
        }
        return 0;
    }

    if (argc < 4) { fprintf(stderr, "uso: %s ROM modo FRAMES [...]\n", argv[0]); return 2; }
    mode = argv[2];
    frames = (uint32_t)atoi(argv[3]);
    if (argc > 4) port = atoi(argv[4]);
    g_maxframes = frames;
    if (getenv("NESNET_UI")) { g_ui_script = getenv("NESNET_UI"); g_ui_has_script = 1; }   /* pruebas del menu de salir */
    if (getenv("NESNET_R2")) g_exit_at = (uint32_t)atoi(getenv("NESNET_R2"));
    if (getenv("NESNET_R2B")) g_exit_at2 = (uint32_t)atoi(getenv("NESNET_R2B"));
    if (getenv("NESNET_NETINFO")) g_netinfo = atoi(getenv("NESNET_NETINFO"));   /* prueba: modo de info de red */
    if (getenv("NESNET_FPS")) g_showfps = atoi(getenv("NESNET_FPS"));           /* prueba v1.9.2: FPS en pantalla */
    if (getenv("NESNET_SCREEN")) g_screen = atoi(getenv("NESNET_SCREEN"));       /* prueba v1.9.6: pantalla ORIGINAL / 4:3 / 16:9 (0, 1, 2) */
    if (getenv("NESNET_SHOTF")) {                                                /* prueba v1.9.6: "se aprieta L2" en estos cuadros (a,b,c) */
        const char *sl = getenv("NESNET_SHOTF");
        int si = 0;
        while (*sl && si < 8) { g_shot_at[si++] = (uint32_t)atoi(sl); while (*sl && *sl != ',') sl++; if (*sl == ',') sl++; }
        g_cfg.render = 1;
    }
    if (getenv("NESNET_RESET_REF")) {                                            /* prueba v1.9.1: reinicios de la referencia "a" o "a,b" */
        const char *rr = getenv("NESNET_RESET_REF");
        g_ref_reset[0] = (uint32_t)atoi(rr);
        if (strchr(rr, ',')) g_ref_reset[1] = (uint32_t)atoi(strchr(rr, ',') + 1);
    }
    signal(SIGPIPE, SIG_IGN);
    if (!strcmp(mode, "app")) {
        /* flujo real: lee DIR/config.txt y ejecuta app_main (argv[4] = carpeta) */
        char exe[300];
        int rc;
        snprintf(exe, sizeof exe, "%s/EBOOT.BIN", argv[4]);
        if (getenv("NESNET_UI")) { g_ui_script = getenv("NESNET_UI"); g_ui_has_script = 1; }
        if (getenv("NESNET_R2")) g_exit_at = (uint32_t)atoi(getenv("NESNET_R2"));
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
    if (getenv("NESNET_DIR")) snprintf(g_dir, sizeof g_dir, "%s", getenv("NESNET_DIR"));   /* prueba v1.9.2: carpeta propia (con roms/) por proceso */
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
    } else if (!strcmp(mode, "sticktest")) {
        /* v1.8.1: prueba de la palanca: recorre los 256 valores de cada eje y comprueba direcciones y zona muerta */
        unsigned v, bad = 0;
        for (v = 0; v < 256; v++) {
            uint16_t h = stick_nes_bits(v, 128), w = stick_nes_bits(128, v);
            int exp = v < 78 ? -1 : v > 178 ? 1 : 0;
            if (h != (exp < 0 ? NB_LEFT : exp > 0 ? NB_RIGHT : 0)) bad++;
            if (w != (exp < 0 ? NB_UP : exp > 0 ? NB_DOWN : 0)) bad++;
        }
        if (stick_nes_bits(0, 0) != (NB_LEFT | NB_UP) || stick_nes_bits(255, 255) != (NB_RIGHT | NB_DOWN) ||
            stick_nes_bits(255, 0) != (NB_RIGHT | NB_UP) || stick_nes_bits(0, 255) != (NB_LEFT | NB_DOWN) ||
            stick_nes_bits(128, 128) != 0 || stick_nes_bits(120, 140) != 0) bad++;
        printf("sticktest bad=%u (centro 128, zona muerta 78..178)\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "maptest")) {
        /* v1.8.2: pruebas del mapeo de botones, el turbo y el guardado de opciones (funciones puras) */
        unsigned bad = 0, n = 0, btns, d, p, i, f;
        const uint16_t dirbits[4] = { NB_UP, NB_DOWN, NB_LEFT, NB_RIGHT };
        /* 1) con el mapeo por defecto el resultado es IDENTICO a la formula de la v1.8.1 (todas las combinaciones de botones y direcciones) */
        opts_defaults();
        for (p = 0; p < 2; p++)
            for (btns = 0; btns < (1u << PB_COUNT); btns++)
                for (d = 0; d < 16; d++) {
                    uint16_t dirs = 0, ref = 0;
                    for (i = 0; i < 4; i++) if (d & (1u << i)) dirs |= dirbits[i];
                    if (btns & PB_BIT(PB_CIRCLE)) ref |= NB_A;
                    if (btns & PB_BIT(PB_CROSS))  ref |= NB_B;
                    if (btns & PB_BIT(PB_SELECT)) ref |= NB_SEL;
                    if (btns & PB_BIT(PB_START))  ref |= NB_START;
                    ref |= dirs;
                    if ((ref & NB_UP) && (ref & NB_DOWN))    ref &= (uint16_t)~NB_DOWN;
                    if ((ref & NB_LEFT) && (ref & NB_RIGHT)) ref &= (uint16_t)~NB_RIGHT;
                    n++;
                    if (map_nes_bits((int)p, btns, dirs) != ref) bad++;
                }
        printf("maptest defecto==v1.8.1: %u combinaciones, bad=%u\n", n, bad);
        /* 2) turbo: apretado 2 cuadros, suelto 2, empezando apretado; soltar reinicia; cada mando y cada turbo es independiente */
        {
            unsigned tb = 0;
            opts_defaults();
            g_map[0][MA_TA] = PB_SQUARE; g_map[0][MA_TB] = PB_TRIANGLE;
            for (f = 0; f < 16; f++) {
                uint16_t a = map_nes_bits(0, PB_BIT(PB_SQUARE), 0);
                int want = ((f >> 1) & 1) == 0;
                if (((a & NB_A) != 0) != want || (a & NB_B)) tb++;
            }
            (void)map_nes_bits(0, 0, 0);                                      /* soltar */
            for (f = 0; f < 6; f++) {                                         /* turbo B: tambien empieza apretado */
                uint16_t a = map_nes_bits(0, PB_BIT(PB_TRIANGLE), 0);
                int want = ((f >> 1) & 1) == 0;
                if (((a & NB_B) != 0) != want || (a & NB_A)) tb++;
            }
            (void)map_nes_bits(0, 0, 0);
            if (!(map_nes_bits(0, PB_BIT(PB_SQUARE), 0) & NB_A)) tb++;        /* primer cuadro tras apretar = apretado */
            (void)map_nes_bits(0, PB_BIT(PB_SQUARE), 0);
            if (map_nes_bits(0, PB_BIT(PB_SQUARE), 0) & NB_A) tb++;           /* tercer cuadro = suelto */
            for (f = 0; f < 8; f++) {                                         /* el mando 2 no tiene turbo asignado: nunca dispara */
                if (map_nes_bits(1, PB_BIT(PB_SQUARE) | PB_BIT(PB_TRIANGLE), 0) & (NB_A | NB_B)) tb++;
            }
            (void)map_nes_bits(0, 0, 0);
            for (f = 0; f < 8; f++) {                                         /* con A normal apretada, el turbo no la suelta */
                if (!(map_nes_bits(0, PB_BIT(PB_CIRCLE) | PB_BIT(PB_SQUARE), 0) & NB_A)) tb++;
            }
            printf("maptest turbo: bad=%u\n", tb);
            bad += tb;
        }
        /* 3) reglas de asignacion */
        {
            unsigned rb = 0, seen[PB_COUNT + 1], k;
            opts_defaults();
            map_cycle(0, MA_A, +1);                                           /* A: O -> CUADRADO (libre) */
            if (g_map[0][MA_A] != PB_SQUARE) rb++;
            opts_defaults();
            map_cycle(0, MA_A, -1);                                           /* A hacia atras: salta X (B), "sin asignar" (no vale), SELECT y START (usados) -> L3 (R3 esta reservado) */
            if (g_map[0][MA_A] != PB_L3 || g_map[0][MA_B] != PB_CROSS) rb++;
            opts_defaults();
            map_cycle(0, MA_TA, +1);                                          /* turbo A: sin asignar -> salta X y O (usados) -> CUADRADO */
            if (g_map[0][MA_TA] != PB_SQUARE) rb++;
            map_cycle(0, MA_TA, -1);                                          /* y hacia atras vuelve a sin asignar */
            if (g_map[0][MA_TA] != PB_NONE) rb++;
            map_assign(0, MA_TA, PB_NONE); map_assign(0, MA_TB, PB_NONE);     /* quitar un turbo ya quitado no toca nada mas */
            if (g_map[0][MA_TA] != PB_NONE || g_map[0][MA_TB] != PB_NONE || g_map[0][MA_A] != PB_CIRCLE) rb++;
            /* R3: el mando 1 nunca puede tenerlo; el mando 2 si. Se recorre todo el ciclo de un turbo */
            for (p = 0; p < 2; p++) {
                opts_defaults();
                memset(seen, 0, sizeof seen);
                for (k = 0; k < 40; k++) { map_cycle((int)p, MA_TA, +1); seen[g_map[p][MA_TA] + 1]++; }
                if (p == 0 && (seen[PB_R3 + 1] != 0 || seen[PB_L2 + 1] != 0)) rb++;   /* v1.9.6: R3 y L2 reservados en el mando 1 */
                if (p == 1 && (seen[PB_R3 + 1] == 0 || seen[PB_L2 + 1] == 0)) rb++;
                if (seen[0] == 0) rb++;                                       /* "sin asignar" tambien se alcanza */
                if (seen[PB_CROSS + 1] != 0 || seen[PB_CIRCLE + 1] != 0 || seen[PB_START + 1] != 0 || seen[PB_SELECT + 1] != 0) rb++;   /* nunca pisa botones usados */
            }
            /* mapeos guardados: validacion */
            {
                int ok[MA_COUNT]  = { PB_CIRCLE, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE };
                int dup[MA_COUNT] = { PB_CIRCLE, PB_CIRCLE, PB_SELECT, PB_START, PB_NONE, PB_NONE };
                int non[MA_COUNT] = { PB_NONE, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE };
                int r2[MA_COUNT]  = { PB_R3, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE };
                int big[MA_COUNT] = { PB_CIRCLE, PB_CROSS, PB_SELECT, PB_START, 99, PB_NONE };
                if (!map_valid(ok, 0) || !map_valid(ok, 1)) rb++;
                if (map_valid(dup, 0) || map_valid(non, 0) || map_valid(r2, 0) || map_valid(big, 1)) rb++;
                if (!map_valid(r2, 1)) rb++;                                  /* R3 vale en el mando 2 */
                {   /* v1.9.6: L2 reservado en el mando 1 (captura), libre en el mando 2 */
                    int l2m[MA_COUNT] = { PB_L2, PB_CROSS, PB_SELECT, PB_START, PB_NONE, PB_NONE };
                    if (map_valid(l2m, 0) || !map_valid(l2m, 1)) rb++;
                }
            }
            printf("maptest reglas: bad=%u\n", rb);
            bad += rb;
        }
        /* 4) fuzz: 300000 cambios al azar; el mapeo siempre queda valido (botones normales siempre con boton, sin repetidos, sin R2 en el mando 1) */
        {
            unsigned fb = 0;
            srand(12345);
            opts_defaults();
            for (f = 0; f < 300000; f++) {
                int pp = rand() & 1, act = rand() % MA_COUNT, dd = (rand() & 1) ? 1 : -1;
                if ((rand() % 50) == 0) map_defaults(pp);
                else if ((rand() % 7) == 0) { int b = (rand() % (PB_COUNT + 1)) - 1; if (map_allowed(pp, act, b)) map_assign(pp, act, b); }
                else map_cycle(pp, act, dd);
                if (!map_valid(g_map[0], 0) || !map_valid(g_map[1], 1)) fb++;
            }
            printf("maptest fuzz: bad=%u\n", fb);
            bad += fb;
        }
        /* 5) guardar y cargar */
        {
            unsigned sb = 0;
            char path[300], dir[] = "/tmp/nesnet_maptest";
            FILE *fp;
            int save_map[2][MA_COUNT], save_screen;
            mkdir(dir, 0755);
            snprintf(g_dir, sizeof g_dir, "%s", dir);
            g_log = NULL;
            opts_defaults();
            g_map[0][MA_A] = PB_SQUARE; g_map[0][MA_TA] = PB_L1; g_map[1][MA_TB] = PB_R2; g_screen = 2;
            opts_save();
            memcpy(save_map, g_map, sizeof save_map); save_screen = g_screen;
            opts_defaults();
            opts_load();
            if (memcmp(save_map, g_map, sizeof save_map) || g_screen != save_screen) sb++;
            /* archivo estropeado: lineas basura, mapeo invalido del mando 1, pantalla fuera de rango: valen los defectos / lo valido */
            snprintf(path, sizeof path, "%s/opciones.txt", dir);
            fp = fopen(path, "w");
            fprintf(fp, "basura\nscreen=9\npad1=3,3,3,3,3,3\npad2=1,0,11,10,-1,2\nxx=1\n");
            fclose(fp);
            opts_load();
            if (g_screen != 0) sb++;                                          /* 9 no vale: queda la de por defecto */
            if (g_map[0][MA_A] != PB_CIRCLE || g_map[0][MA_B] != PB_CROSS || g_map[0][MA_TA] != PB_NONE) sb++;   /* mando 1: invalido -> defecto */
            if (g_map[1][MA_TB] != PB_SQUARE || g_map[1][MA_SEL] != PB_SELECT || g_map[1][MA_TA] != PB_NONE) sb++;   /* mando 2: valido, se respeta */
            printf("maptest guardado: bad=%u\n", sb);
            bad += sb;
        }
        printf("maptest TOTAL bad=%u\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "imgtest")) {
        /* v1.9.2: ajuste de imagen (canvas_blit_adj) y guardado de las opciones nuevas */
        static const int dims[4][3] = { { 1280, 720, 3 }, { 1920, 1080, 3 }, { 1920, 1080, 4 }, { 720, 480, 2 } };
        static const int sizes[4] = { 100, 90, 80, 70 };
        static const int shifts[7][2] = { { 0, 0 }, { 2, 0 }, { 0, -2 }, { 60, 60 }, { -60, -60 }, { 60, -60 }, { -60, 60 } };
        static uint32_t fbuf[SCR_W * SCR_H], b0[1920 * 1080], b1[1920 * 1080], ref[1920 * 1080];
        unsigned bad = 0, ncheck = 0;
        int di, md, si, hi, x, y;
        for (y = 0; y < SCR_H; y++) for (x = 0; x < SCR_W; x++) fbuf[y * SCR_W + x] = 0xFF000000u | ((uint32_t)y << 8) | (uint32_t)x;
        for (di = 0; di < 4; di++) {
            int dw = dims[di][0], dh = dims[di][1], z = dims[di][2];
            for (md = 0; md < 3; md++) {
                /* 1) con 100 %, 0, 0 es IDENTICO a canvas_blit_cpu (lo que se usaba hasta la v1.9.1) */
                {
                    unsigned fa = 0, fb = 0;
                    size_t i;
                    for (i = 0; i < (size_t)dw * dh; i++) { b0[i] = 0xDEADBEEFu; b1[i] = 0xDEADBEEFu; }
                    canvas_blit_cpu(b0, dw, dh, md, z, fbuf, &fa);
                    canvas_blit_adj(b1, dw, dh, md, z, fbuf, &fb, 100, 0, 0);
                    ncheck++;
                    if (memcmp(b0, b1, (size_t)dw * dh * 4)) { bad++; printf("imgtest %dx%d modo=%d: 100%%,0,0 DIFIERE de canvas_blit_cpu\n", dw, dh, md); }
                }
                /* 2) cada tamano y desplazamiento contra el calculo pixel a pixel (con recorte), en dos buffers alternados
                 *    como en la PS3: tras cambiar la geometria, a las 2 llamadas (una por buffer) no queda ningun resto */
                for (si = 0; si < 4; si++)
                    for (hi = 0; hi < 7; hi++) {
                        int oh0 = SCR_H * z, ow0 = screen_out_w(md, dw, oh0, z);
                        int ow = ow0 * sizes[si] / 100, oh = oh0 * sizes[si] / 100;
                        int ox = (dw - ow) / 2 + shifts[hi][0], oy = (dh - oh) / 2 + shifts[hi][1];
                        unsigned fa = 0, fb = 0;
                        int k, errs = 0, dx, dy;
                        size_t i;
                        /* historia previa con OTRA geometria, para que haya restos que borrar */
                        for (i = 0; i < (size_t)dw * dh; i++) { b0[i] = 0xDEADBEEFu; b1[i] = 0xDEADBEEFu; }
                        canvas_blit_adj(b0, dw, dh, md, z, fbuf, &fa, 100, 0, 0);
                        canvas_blit_adj(b1, dw, dh, md, z, fbuf, &fb, 100, 0, 0);
                        for (k = 0; k < 4; k++) { canvas_blit_adj(b0, dw, dh, md, z, fbuf, &fa, 100, 0, 0); canvas_blit_adj(b1, dw, dh, md, z, fbuf, &fb, 100, 0, 0); }
                        for (k = 0; k < 2; k++) {          /* geometria nueva: una llamada por buffer */
                            canvas_blit_adj(b0, dw, dh, md, z, fbuf, &fa, sizes[si], shifts[hi][0], shifts[hi][1]);
                            canvas_blit_adj(b1, dw, dh, md, z, fbuf, &fb, sizes[si], shifts[hi][0], shifts[hi][1]);
                        }
                        for (dy = 0; dy < dh; dy++)
                            for (dx = 0; dx < dw; dx++) {
                                uint32_t want = 0;
                                if (dy >= oy && dy < oy + oh && dx >= ox && dx < ox + ow)
                                    want = fbuf[((dy - oy) * SCR_H / oh) * SCR_W + ((dx - ox) * SCR_W / ow)];
                                ref[(size_t)dy * dw + dx] = want;
                            }
                        for (i = 0; i < (size_t)dw * dh; i++) if (b0[i] != ref[i]) errs++;
                        for (i = 0; i < (size_t)dw * dh; i++) if (b1[i] != ref[i]) errs++;
                        ncheck++;
                        if (errs) { bad++; printf("imgtest %dx%d modo=%d tam=%d%% dx=%d dy=%d: %d pixeles mal\n", dw, dh, md, sizes[si], shifts[hi][0], shifts[hi][1], errs); }
                    }
            }
        }
        printf("imgtest imagen: %u comprobaciones, mal=%u\n", ncheck, bad);
        /* 3) las opciones nuevas se guardan y se leen (y valores fuera de rango o basura se ignoran) */
        {
            unsigned ob = 0;
            FILE *f;
            char p[300];
            snprintf(g_dir, sizeof g_dir, "/tmp/nn_img_test");
            { char cmd[320]; snprintf(cmd, sizeof cmd, "mkdir -p %s", g_dir); if (system(cmd)) ob++; }
            opts_defaults();
            if (g_showfps != 0 || g_img_size != 100 || g_img_dx != 0 || g_img_dy != 0) ob++;              /* valores de siempre por defecto */
            g_showfps = 1; g_img_size = 85; g_img_dx = -14; g_img_dy = 30;
            opts_save();
            opts_defaults();
            opts_load();
            if (g_showfps != 1 || g_img_size != 85 || g_img_dx != -14 || g_img_dy != 30) { ob++; printf("imgtest opciones: NO se leyeron bien (fps=%d size=%d dx=%d dy=%d)\n", g_showfps, g_img_size, g_img_dx, g_img_dy); }
            snprintf(p, sizeof p, "%s/opciones.txt", g_dir);
            f = fopen(p, "wb");
            if (f) { fprintf(f, "fps=7\nimgsize=5\nimgx=9999\nimgy=-9999\n"); fclose(f); }
            opts_defaults();
            opts_load();
            if (g_showfps != 0 || g_img_size != 100 || g_img_dx != 0 || g_img_dy != 0) { ob++; printf("imgtest opciones: valores malos NO se ignoraron\n"); }
            remove(p);
            opts_defaults();
            opts_load();                                                      /* sin archivo: valores de siempre */
            if (g_showfps != 0 || g_img_size != 100 || g_img_dx != 0 || g_img_dy != 0) ob++;
            printf("imgtest opciones: mal=%u\n", ob);
            bad += ob;
        }
        printf("imgtest TOTAL mal=%u\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "shottest")) {
        /* v1.9.6: el PNG de captura == lo que dibuja canvas_blit_cpu (la funcion de la pantalla de la PS3) recortado a la imagen.
         * argv[4] = carpeta de salida: para cada medida y modo deja ref_<d>_<m>.rgb (lo esperado) y png_<d>_<m>.png (lo guardado). */
        static const int dims[3][3] = { { 1280, 720, 3 }, { 1920, 1080, 3 }, { 720, 480, 2 } };
        static uint32_t fbuf[SCR_W * SCR_H], buf[1920 * 1080];
        const char *od = argc > 4 ? argv[4] : "/tmp";
        unsigned bad = 0;
        int di, md, x, y;
        for (y = 0; y < SCR_H; y++)
            for (x = 0; x < SCR_W; x++) {
                uint32_t v = (uint32_t)(x * 7919 + y * 104729 + (x ^ y) * 31);
                fbuf[y * SCR_W + x] = 0xFF000000u | ((v * 2654435761u) >> 8);
            }
        for (di = 0; di < 3; di++)
            for (md = 0; md < 3; md++) {
                int dw = dims[di][0], dh = dims[di][1], z = dims[di][2];
                int oh = SCR_H * z, ow = screen_out_w(md, dw, oh, z), ox = (dw - ow) / 2, oy = (dh - oh) / 2, w = 0, h = 0;
                unsigned fc = 0;
                char p1[400];
                FILE *f;
                size_t i;
                for (i = 0; i < (size_t)dw * dh; i++) buf[i] = 0xDEADBEEFu;
                canvas_blit_cpu(buf, dw, dh, md, z, fbuf, &fc);
                snprintf(p1, sizeof p1, "%s/ref_%d_%d.rgb", od, di, md);
                f = fopen(p1, "wb");
                for (y = 0; y < oh; y++)
                    for (x = 0; x < ow; x++) {
                        uint32_t px = buf[(size_t)(oy + y) * dw + ox + x];
                        uint8_t c3[3] = { (uint8_t)(px >> 16), (uint8_t)(px >> 8), (uint8_t)px };
                        fwrite(c3, 1, 3, f);
                    }
                fclose(f);
                snprintf(p1, sizeof p1, "%s/png_%d_%d.png", od, di, md);
                if (!shot_write_png(p1, fbuf, md, dw, z, &w, &h) || w != ow || h != oh) { bad++; printf("shottest: FALLO %dx%d modo %d\n", dw, dh, md); }
                else printf("shottest %dx%d modo %d: png %dx%d\n", dw, dh, md, w, h);
            }
        /* nombres: ROM con espacios, parentesis y corchetes; numeracion 0001, 0002...; otra ROM empieza de nuevo */
        {
            char nd[300], p2[420];
            int n1, n2, n3;
            snprintf(nd, sizeof nd, "%s/naming", od);
            mkdir(nd, 0777);
            snprintf(g_dir, sizeof g_dir, "%s", nd);
            g_cfg.render = 1; g_screen = 2;
            snprintf(g_rom_name, sizeof g_rom_name, "Super Mario Bros. 3 (USA) [!].nes");
            n1 = shot_take(fbuf); n2 = shot_take(fbuf);
            snprintf(g_rom_name, sizeof g_rom_name, "Otro Juego.nes");
            n3 = shot_take(fbuf);
            snprintf(g_rom_name, sizeof g_rom_name, "Super Mario Bros. 3 (USA) [!].nes");
            if (shot_take(fbuf) != 3) bad++;                                       /* vuelve a la primera ROM: sigue en 0003 */
            snprintf(p2, sizeof p2, "%s/screenshots/Super_Mario_Bros__3__USA______0003.png", nd);
            if (n1 != 1 || n2 != 2 || n3 != 1 || !path_is_valid(p2)) { bad++; printf("shottest: numeracion/nombres MAL (%d %d %d) %s\n", n1, n2, n3, p2); }
            else printf("shottest nombres OK: %s\n", p2);
            g_rom_name[0] = 0;
            if (shot_take(fbuf) != 1) bad++;
            snprintf(p2, sizeof p2, "%s/screenshots/captura_0001.png", nd);
            if (!path_is_valid(p2)) { bad++; printf("shottest: sin nombre de ROM deberia ser captura_0001.png\n"); }
        }
        printf("shottest TOTAL bad=%u\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "screentest")) {
        /* v1.8.2: pruebas del escalado de pantalla (canvas_blit_cpu, la misma funcion que usa la PS3) */
        static const int dims[4][3] = { { 1280, 720, 3 }, { 1920, 1080, 3 }, { 1920, 1080, 4 }, { 720, 480, 2 } };
        unsigned bad = 0;
        int di, md;
        static uint32_t fbuf[SCR_W * SCR_H], buf[1920 * 1080], ref[1920 * 1080];
        int x, y;
        for (y = 0; y < SCR_H; y++) for (x = 0; x < SCR_W; x++) fbuf[y * SCR_W + x] = 0xFF000000u | ((uint32_t)y << 8) | (uint32_t)x;
        for (di = 0; di < 4; di++) {
            int dw = dims[di][0], dh = dims[di][1], z = dims[di][2];
            for (md = 0; md < 3; md++) {
                int oh = SCR_H * z, ow = screen_out_w(md, dw, oh, z);
                int ox = (dw - ow) / 2, oy = (dh - oh) / 2, errs = 0, dx, dy;
                unsigned fc = 0;
                size_t i;
                for (i = 0; i < (size_t)dw * dh; i++) buf[i] = 0xDEADBEEFu;     /* basura previa: lo de fuera de la imagen debe quedar en 0 */
                canvas_blit_cpu(buf, dw, dh, md, z, fbuf, &fc);
                for (dy = 0; dy < dh; dy++)
                    for (dx = 0; dx < dw; dx++) {
                        uint32_t got = buf[(size_t)dy * dw + dx], want = 0;
                        if (dy >= oy && dy < oy + oh && dx >= ox && dx < ox + ow)
                            want = fbuf[((dy - oy) / z) * SCR_W + ((dx - ox) * SCR_W / ow)];
                        if (got != want) errs++;
                    }
                /* modo 0: identico, byte a byte, al escalado de la v1.8.1 (cada pixel repetido z veces) */
                if (md == 0) {
                    for (i = 0; i < (size_t)dw * dh; i++) ref[i] = 0;
                    for (dy = 0; dy < oh; dy++)
                        for (dx = 0; dx < SCR_W * z; dx++)
                            ref[(size_t)(oy + dy) * dw + ox + dx] = fbuf[(dy / z) * SCR_W + dx / z];
                    if (memcmp(buf, ref, (size_t)dw * dh * 4)) errs++;
                }
                /* repeticion de columnas en la primera fila: original a 720p = todas x3; 4:3 = 192 de x4 y 64 de x3; 16:9 = todas x5 */
                if (dw == 1280 && dh == 720) {
                    int run = 1, n3 = 0, n4 = 0, n5 = 0, nx = 0, row = oy * dw + ox;
                    for (dx = 1; dx <= ow; dx++) {
                        if (dx < ow && buf[row + dx] == buf[row + dx - 1]) { run++; continue; }
                        if (run == 3) n3++; else if (run == 4) n4++; else if (run == 5) n5++; else nx++;
                        run = 1;
                    }
                    if (md == 0 && !(ow == 768 && n3 == 256 && !n4 && !n5 && !nx)) errs++;
                    if (md == 1 && !(ow == 960 && n4 == 192 && n3 == 64 && !n5 && !nx)) errs++;
                    if (md == 2 && !(ow == 1280 && n5 == 256 && !n3 && !n4 && !nx)) errs++;
                }
                printf("screentest %dx%d z=%d modo=%d: imagen %dx%d en (%d,%d) errores=%d\n", dw, dh, z, md, ow, oh, ox, oy, errs);
                bad += (unsigned)errs;
            }
        }
        /* cambiar de modo no deja residuo: 16:9 durante 8 cuadros y luego original; a los 4 cuadros los bordes quedan limpios */
        {
            int dw = 1280, dh = 720, z = 3, k, dx, dy, errs = 0;
            unsigned fc = 0;
            size_t i;
            for (i = 0; i < (size_t)dw * dh; i++) buf[i] = 0;
            for (k = 0; k < 8; k++) canvas_blit_cpu(buf, dw, dh, 2, z, fbuf, &fc);
            for (k = 0; k < 4; k++) canvas_blit_cpu(buf, dw, dh, 0, z, fbuf, &fc);
            for (dy = 0; dy < dh; dy++)
                for (dx = 0; dx < dw; dx++)
                    if ((dx < 256 || dx >= 1024) && buf[(size_t)dy * dw + dx] != 0) errs++;
            printf("screentest cambio 16:9 -> original: residuos=%d\n", errs);
            bad += (unsigned)errs;
        }
        /* costo relativo en CPU (solo orientativo, en PC) */
        {
            int dw = 1280, dh = 720, z = 3, k;
            unsigned fc = 0;
            uint32_t t0;
            for (md = 0; md < 3; md++) {
                t0 = now_ms();
                for (k = 0; k < 600; k++) canvas_blit_cpu(buf, dw, dh, md, z, fbuf, &fc);
                printf("screentest tiempo modo %d: %u ms por 600 cuadros (PC)\n", md, (unsigned)(now_ms() - t0));
            }
        }
        printf("screentest TOTAL bad=%u\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "ref4")) {
        /* v1.8: referencia de 4 jugadores locales con el mismo retraso D */
        D = argc > 4 ? atoi(argv[4]) : 6;
        g_four = 1;
        core_load4(); session_loop4(-2, D, frames); core_unload();
        g_four = 0;
    } else if (!strcmp(mode, "host4")) {
        int lfd = tcp_listen(port);
        if (lfd < 0) { fprintf(stderr, "no puedo escuchar\n"); return 2; }
        if (argc > 5) g_cfg.delay = atoi(argv[5]);
        g_net = accept(lfd, NULL, NULL);
        closesocket(lfd);
        sock_nodelay(g_net);
        ok = handshake_host4(&D);
        if (ok) ok = run_online4(1, D);
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "client4")) {
        int tries;
        for (tries = 0; tries < 50 && g_net < 0; tries++) {
            g_net = tcp_connect(0x7F000001u, port, 2000);
            if (g_net < 0) sleep_ms(100);
        }
        if (g_net < 0) { fprintf(stderr, "no pude conectar\n"); return 2; }
        ok = handshake_client4(&D);
        if (ok) ok = run_online4(0, D);
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "reload")) {
        /* sesion solo, descarga, y luego sesion de referencia: debe dar igual que un proceso nuevo */
        core_load(); session_loop(-1, 0, 300); core_unload();
        D = 6;
        core_load(); session_loop(-2, D, frames); core_unload();
    } else if (!strcmp(mode, "codetest")) {
        /* v1.9.1: codigo de 10 digitos (solo la IP); el puerto sale de config.txt */
        char c[20], pc[24]; uint32_t ip; int p, n = 0, bad = 0;
        uint32_t t;
        g_cfg.port = 7777;
        for (t = 0; t < 200000; t++) {
            uint32_t a = t * 2654435761u;
            code_encode(a ? a : 1, 7777, c);
            if (strlen(c) != 10 || !code_decode(c, &ip, &p) || ip != (a ? a : 1) || p != 7777) bad++;
            code_pretty(c, pc);
            if (strlen(pc) != 12 || !code_decode(pc, &ip, &p) || ip != (a ? a : 1)) bad++;      /* con espacios tambien */
            n++;
        }
        code_encode(0xB92DC811u, 7777, c);                                  /* 185.45.200.17 */
        if (strcmp(c, "3106785297")) { bad++; printf("codetest muestra: %s\n", c); }
        code_encode(0x01020304u, 7777, c);
        if (strcmp(c, "0016909060")) { bad++; printf("codetest muestra2: %s\n", c); }
        if (code_decode("12345", &ip, &p) || code_decode("12345678901", &ip, &p) || code_decode("4294967296", &ip, &p) ||
            code_decode("0000000000", &ip, &p) || code_decode("123456789012345", &ip, &p)) { bad++; printf("codetest: acepto un codigo malo\n"); }
        printf("codetest n=%d bad=%d\n", n, bad);
        return bad != 0;
    } else if (!strcmp(mode, "statetest")) {
        /* v1.9.1: guardar y cargar estado. Tras cargar, los siguientes cuadros deben dar exactamente los mismos CRC de video. */
        static uint32_t ca[300], cb[300], cc[300];
        uint32_t f;
        size_t n;
        uint8_t *buf;
        unsigned bad = 0;
        core_load();
        n = retro_serialize_size();
        printf("statetest: el nucleo pide %u bytes de estado\n", (unsigned)n);
        for (f = 0; f < 300; f++) step_frame(script_input(0, f), script_input(1, f));
        buf = (uint8_t *)malloc(n);
        if (!buf || !retro_serialize(buf, n)) { printf("statetest: no pude serializar\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); ca[f - 300] = g_frame_crc; }
        if (!retro_unserialize(buf, n)) { printf("statetest: no pude cargar\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); cb[f - 300] = g_frame_crc; }
        for (f = 0; f < 300; f++) if (ca[f] != cb[f]) bad++;
        printf("statetest memoria: cuadros distintos tras cargar = %u\n", bad);
        /* por archivo: guardar en la ranura 2, seguir, cargar, repetir */
        retro_unserialize(buf, n);
        free(buf);
        mkdir("/tmp/nn_state_test", 0777);
        snprintf(g_dir, sizeof g_dir, "/tmp/nn_state_test");
        if (!state_save(1)) { printf("statetest: no pude guardar archivo\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); ca[f - 300] = g_frame_crc; }
        if (state_load(1) != 1) { printf("statetest: no pude cargar archivo\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); cc[f - 300] = g_frame_crc; }
        {
            unsigned bad2 = 0;
            for (f = 0; f < 300; f++) if (ca[f] != cc[f]) bad2++;
            printf("statetest archivo: cuadros distintos tras cargar = %u\n", bad2);
            bad += bad2;
        }
        printf("statetest existe(ranura 2)=%d existe(ranura 1)=%d\n", state_exists(1), state_exists(0));
        core_unload();
        return bad != 0;
    }
    printf("RESULT mode=%s frames=%u hash=%08X desyncs=%d D=%d first_desync=%d\n", mode,
           (unsigned)g_frames_done, (unsigned)g_run_hash, g_desyncs, D,
           g_first_desync == NO_FRAME ? -1 : (int)g_first_desync);
    return ok ? 0 : 1;
}
#endif
