#!/bin/bash

inp=$1
raw="$1.raw"
breaks="$1.breaks"
./hex2raw < $1 > $raw

touch $breaks
echo "break getbuf" > $breaks
echo "set step-mode on" >> $breaks
echo "run -t nchepano < $raw" >>$breaks
#echo "layout regs" >> $breaks
gdb -x $breaks bufbomb
