import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_5_3

/- Remark 20.5.5: the proof of the compact-support duality statement is organized as a sheaf-like
local-to-global argument. The global owner is the assembled duality map
`compactlySupportedPoincareDualityMap` and its isomorphism statement
`compactlySupportedPoincareDuality`; the component formula
`colimit_ι_compactlySupportedPoincareDualityMap` records that this global map is assembled from
the local cap-with-`[M]_K` maps, and the gluing step is supplied by the Mayer-Vietoris exactness
package `pairHomologyMayerVietorisExact₁/₂/₃` used in the local-to-global reduction of
ProofStep 20.4.4. This item is therefore recorded as a labeled recall block around those existing
owners rather than as a separate theorem. -/
#check compactlySupportedPoincareDualityMap
#check colimit_ι_compactlySupportedPoincareDualityMap
#check compactlySupportedPoincareDuality
#check pairHomologyMayerVietorisExact₁
#check pairHomologyMayerVietorisExact₂
#check pairHomologyMayerVietorisExact₃
