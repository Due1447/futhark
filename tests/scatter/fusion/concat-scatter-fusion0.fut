-- If both the indexes and values come from a concatenation of arrays
-- of the same size, that concatenation should be fused away.
-- ==
-- input { [0,0,0,0,0,0,0,0] [0, 2, 6] }
-- output { [1, 2, 1, 2, 0, 0, 1, 2] }
-- structure { Concat 0 Scatter 1 }

let main (arr: *[]i32) (xs: []i32) =
  let (is0, vs0, is1, vs1) = unzip4 (map (\x -> (x,1,x+1,2)) xs)
  in scatter arr (concat is0 is1) (concat vs0 vs1)
