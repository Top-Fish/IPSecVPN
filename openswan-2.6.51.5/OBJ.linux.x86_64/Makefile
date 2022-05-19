srcdir=/mnt/hgfs/src_kernel/openswan-latest/openswan-2.6.51.5/
OBJDIR=OBJ.linux.x86_64
OBJDIRTOP=/mnt/hgfs/src_kernel/openswan-latest/openswan-2.6.51.5/OBJ.linux.x86_64
VPATH+=${srcdir}
OSDEP=linux
BUILDENV=linux
OPENSWANSRCDIR=/mnt/hgfs/src_kernel/openswan-latest/openswan-2.6.51.5
include ${srcdir}Makefile.top
programs install clean checkprograms:: 
	@for d in $(SUBDIRS) ; \
	do \
		(cd $$d && $(MAKE) OPENSWANSRCDIR=${OPENSWANSRCDIR} $@ ) || exit 1; \
	done; 
