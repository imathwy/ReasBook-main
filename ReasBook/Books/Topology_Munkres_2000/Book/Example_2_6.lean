module

import Mathlib.Data.Set.Lattice.Image

/- Example 2.6 (1): Preimages preserve inclusions. -/
#check Set.preimage_mono

/- Example 2.6 (2): Preimages preserve binary unions. -/
#check Set.preimage_union

/- Example 2.6 (3): Preimages preserve arbitrary indexed unions. -/
#check Set.preimage_iUnion

/- Example 2.6 (4): Preimages preserve binary intersections. -/
#check Set.preimage_inter

/- Example 2.6 (5): Preimages preserve arbitrary indexed intersections. -/
#check Set.preimage_iInter

/- Example 2.6 (6): Preimages preserve set difference. -/
#check Set.preimage_sdiff

/- Example 2.6 (7): Images preserve inclusions. -/
#check Set.image_mono

/- Example 2.6 (8): Images preserve binary unions. -/
#check Set.image_union

/- Example 2.6 (9): Images preserve arbitrary indexed unions. No corresponding
unconditional equality is asserted here for images of intersections or differences. -/
#check Set.image_iUnion
