#!/bin/sh

mkdir -p allTmp
succ=0
unsucc=0

for x in ../tests/*.fut; do
    futhark fmt $x > allTmp/fmt.fut
    if [ $(futhark hash $x ) = $(futhark hash allTmp/fmt.fut ) ]; then
        futhark tokens $x | grep COMMENT > allTmp/ogTok.fut
        futhark tokens allTmp/fmt.fut | grep COMMENT > allTmp/fmtTok.fut
        if ! cmp -s allTmp/fmtTok.fut allTmp/ogTok.fut; then
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
for x in ../tests/*/*.fut; do
    futhark fmt $x > allTmp/fmt.fut
    if [ $(futhark hash $x ) = $(futhark hash allTmp/fmt.fut ) ]; then
        futhark tokens $x | grep COMMENT > allTmp/ogTok.fut
        futhark tokens allTmp/fmt.fut | grep COMMENT > allTmp/fmtTok.fut
        if ! cmp -s allTmp/fmtTok.fut allTmp/ogTok.fut; then
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
for x in ../tests/*/*/*.fut; do
    futhark fmt $x > allTmp/fmt.fut
    if [ $(futhark hash $x ) = $(futhark hash allTmp/fmt.fut ) ]; then
        futhark tokens $x | grep COMMENT > allTmp/ogTok.fut
        futhark tokens allTmp/fmt.fut | grep COMMENT > allTmp/fmtTok.fut
        if ! cmp -s allTmp/fmtTok.fut allTmp/ogTok.fut; then
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
for x in ../tests/*/*/*/*.fut; do
    futhark fmt $x > allTmp/fmt.fut
    if [ $(futhark hash $x ) = $(futhark hash allTmp/fmt.fut ) ]; then
        futhark tokens $x | grep COMMENT > allTmp/ogTok.fut
        futhark tokens allTmp/fmt.fut | grep COMMENT > allTmp/fmtTok.fut
        if ! cmp -s allTmp/fmtTok.fut allTmp/ogTok.fut; then
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