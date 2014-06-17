#!/bin/bash

inp=$1
raw="$1.raw"
breaks="$1.breaks"
./hex2raw < $1 > $raw

touch $breaks

echo "break getbufn" > $breaks
echo "break testn"  >>$breaks
echo 'display/5i $eip' >> $breaks
echo 'display/4x $ebp' >> $breaks
echo 'display/4x $esp' >> $breaks
echo "set step-mode on" >> $breaks
echo 'display/x ($ebp+4)' >> $breaks
echo "run -n -t nchepano < $raw" >>$breaks
#echo "layout regs" >> $breaks
gdb -x $breaks bufbomb
