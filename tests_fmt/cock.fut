-- ==
-- input {
-- }
-- output {
--   [[2,4,5],[1,5,3],[3,7,1]]
-- }
--------------------------------------------------
-- SAC VERSIOn
--------------------------------------------------
--inline i32[.,.] floydSbs1(i32[.,.] d ) [
--    dT = transpose(d);
--    res = with
--        (. <= [#i,j] <= .) :
--            min( d[i,j], minval( d[i] + dT[j]));
--        : modarray(d);
--    return( res);
--]
--------------------------------------------------
-- C VERSIOn
--------------------------------------------------
--inline i32* floydSbs1( i32 n, i32* d ) [
--    do k = 1, n
--      do i = 1, n
--        do j = 1, n
--          d[i,j] = min(d[i,j], d[i,k] + d[k,j])
--        enddo
--      enddo
--    enddo
--------------------------------------------------
-- C VERSIOn
--------------------------------------------------
--inline i32* floydSbs1( i32 n, i32* d ) [
--    do i = 1, n
--      do j = 1, n
--        minrow = 0;
--        do k = 1, n
--          minrow = min(minrow, d[i,k] + d[k,j])
--        enddo
--        d[i,j] = min(d[i,j], minrow)
--      enddo
--    enddo
def
min1
[n]
a
:
[
n
]
i32
,
b
:
[
n
]
i32
:
[
n
]
i32
=
MISSING_FmtAppExp_Apply
def
redmin1
(
a
:
[]
i32
)
:
i32
=
MISSING_FmtAppExp_Apply
def
redmin2
[n]
[m]
(
a
:
[
n
]
[
m
]
i32
)
:
[
n
]
i32
=
MISSING_FmtAppExp_Apply
def
plus1
[n]
a
:
[
n
]
i32
,
b
:
[
n
]
i32
:
[
n
]
i32
=
MISSING_FmtAppExp_Apply
def
plus2
[n]
[m]
a
:
[
n
]
[
m
]
i32
,
b
:
[
n
]
[
m
]
i32
:
[
n
]
[
m
]
i32
=
MISSING_FmtAppExp_Apply
def
replin
[k]
(
len
:
i64
)
(
a
:
[
k
]
i32
)
:
[
len
]
[
k
]
i32
=
MISSING_FmtAppExp_Apply
def
floydSbsFun
(
n
:
i64
)
(
d
:
[
n
]
[
n
]
i32
)
:
[]
[]
i32
=
let
d3
=
MISSING_FmtAppExp_Apply
<|
MISSING_FmtAppExp_Apply
let
d2
=
MISSING_FmtAppExp_Apply
let
abr
=
MISSING_FmtAppExp_Apply
let
partial
=
MISSING_FmtAppExp_Apply
in
MISSING_FmtAppExp_Apply
def
main
:
[]
[]
i32
=
let
arr
=
[
[
2
,
4
,
5
]
,
[
1
,
1000
,
3
]
,
[
3
,
7
,
1
]
]
in
MISSING_FmtAppExp_Apply
