#!/bin/sh

mkdir -p tmp
succ=0
unsucc=0

for x in ../tests/*.fut; do
#for x in ../tests/arraylit2.fut; do
    futhark fmt $x > tmp/fmt.fut
    if [ $(futhark hash $x ) = $(futhark hash tmp/fmt.fut ) ]; then
        futhark tokens $x | grep COMMENT > tmp/ogTok.fut
        futhark tokens tmp/fmt.fut | grep COMMENT > tmp/fmtTok.fut
        if ! cmp -s tmp/fmtTok.fut tmp/ogTok.fut; then
            echo "COMMENT ERROR $x"
            unsucc=$((unsucc+1))
        else
            succ=$((succ+1))
        fi
    else
        echo "HASH ERROR $x"
        unsucc=$((unsucc+1))
    fi
done
echo "Successes:     $succ"
echo "Fails:         $unsucc"