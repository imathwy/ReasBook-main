import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Example_9_4_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Example_9_4_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat

-- Semantic recall via `lean_leansearch`: `IsFiberBundleMap` is the canonical owner for these
-- bundle-map assertions, and local Chapter 9 precedent already contains the three Hopf-map bundle
-- theorems from Examples 9.4.8 and 9.4.9. This item is therefore kept as a labeled recall block
-- rather than duplicating those statements.

/- Problem 9.7.4. The Hopf maps already introduced in Examples 9.4.8 and 9.4.9 are bundle maps:
`hopfMap : 𝕊 3 → 𝕊 2` with fiber `Circle`, `quaternionicHopfMap : 𝕊 7 → 𝕊 4` with fiber `𝕊 3`,
and `cayleyHopfMap : 𝕊 15 → 𝕊 8` with fiber `𝕊 7`. -/
#check (hopfMap_isFiberBundle : IsFiberBundleMap Circle hopfMap)
#check (quaternionicHopfMap_isFiberBundle :
  IsFiberBundleMap (𝕊 3) quaternionicHopfMap)
#check (cayleyHopfMap_isFiberBundle : IsFiberBundleMap (𝕊 7) cayleyHopfMap)
