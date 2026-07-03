import Mathlib.CategoryTheory.Sites.Plus

namespace CategoryTheory.GrothendieckTopology.PlusNotation

set_option quotPrecheck false in
scoped macro:max P:term noWs "⁺" : term => do
  let j := Lean.mkIdent `J
  `(GrothendieckTopology.plusObj $j $P)

end CategoryTheory.GrothendieckTopology.PlusNotation
