#!/bin/bash
# Test is all examples in the .org files are working with lean.js

LEAN_JS=lean.js
RUN_LEAN_JS=run_lean_js.sh

if [ $# -ne 1 ]; then
    echo "Usage: test.sh [file]"
    exit 1
fi

if [ ! -f ${LEAN_JS} ] ; then
    wget https://leanprover.github.io/lean.js/${LEAN_JS}
fi

if [ ! -f ${RUN_LEAN_JS} ] ; then
    wget https://raw.githubusercontent.com/leanprover/lean.js/master/${RUN_LEAN_JS}
    chmod +x ${RUN_LEAN_JS}
fi

ulimit -s unlimited
f=$1
i=0
in_code_block=0
lastbegin=0
linenum=0
echo "-- testing $f"
while read -r line; do
    linenum=$((linenum + 1))
    if [[ $line =~ ^#\+BEGIN_SRC\ lean ]]; then
        in_code_block=1
        i=$((i + 1))
        lastbegin=$linenum
        rm -f $f.$i.lean
        echo -E "import standard" >> $f.$i.lean
    elif [[ $line =~ ^#\+END_SRC ]]; then
        if [[ $in_code_block -eq 1 ]]; then
            if ./${RUN_LEAN_JS} ./${LEAN_JS} $f.$i.lean > $f.$i.produced.out; then
                echo "code fragment #$i worked"
            else
                echo "ERROR executing $f.$i.lean, for in_code_block block starting at $lastbegin, produced output:"
                cat  $f.$i.produced.out
                exit 1
            fi
        fi
        in_code_block=0
    elif [[ $in_code_block -eq 1 ]]; then
        echo -E "$line" >> $f.$i.lean
    fi
done < $f
rm -f $f.*.produced.out
rm -f $f.*.lean
exit 0
