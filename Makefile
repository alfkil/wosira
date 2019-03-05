OS	=
EXT	=
CC	= gcc
CCOUT	= -o 
COPTS	= -c -gstabs
LD	= $(CC)
LDOUT	= $(CCOUT)
LDFLAGS	= -lauto
include make.rules
