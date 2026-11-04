# NesNet - NES con netplay para PS3 (PSL1GHT + FCEUmm)
# Requiere: PS3DEV y PSL1GHT en el entorno, y el nucleo FCEUmm ya compilado en
# fceumm/fceumm_libretro_psl1ght.a (lo hace el workflow de GitHub Actions).

TARGET   = NesNet
TITLE    = NesNet
APPID    = NESN00001
CONTENTID = UP0001-$(APPID)_00-0000000000000000

LRC      = fceumm/src/drivers/libretro/libretro-common

OFILES   = source/main.o \
           $(LRC)/compat/compat_strl.o \
           $(LRC)/string/stdstring.o \
           $(LRC)/encodings/encoding_utf.o

CFLAGS   = -O2 -Wall -std=gnu99 -mcpu=cell $(MACHDEP) -DNESNET_PS3 \
           -I$(PS3DEV)/ppu/include -I$(PSL1GHT)/ppu/include -I$(PSL1GHT)/ppu/include/simdmath \
           -I$(LRC)/include

LDFLAGS  = $(MACHDEP)

LIBS     = fceumm/fceumm_libretro_psl1ght.a \
           -lrsx -lgcm_sys -lio -lsysutil -lnet -lsysmodule -lrt -llv2 -lm

# Todo lo que haya en data/ se copia dentro del .pkg (data/USRDIR/config.txt)
PKGFILES = data

BUILDDIR = build

include $(PSL1GHT)/ppu_rules

# make trae LD=ld por defecto y base_rules solo lo cambia si no existe: forzar ppu-gcc
LD = $(CC)

pkg: $(TARGET).pkg

clean:
	rm -rf $(TARGET)*.pkg $(TARGET).self $(TARGET).elf $(OFILES) $(BUILDDIR)
