import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical flat-morphism owner
-- `AlgebraicGeometry.Flat`; local inspection confirmed that
-- `stacks_project.Chap29.Definition_29_7_1` owns `schemeTheoreticallyDense`. The tag evidence is
-- consistent: item tag `081H` matches the source URL `/tag/081H`.

/-- Lemma 29.25.15: let `f : X ⟶ Y` be a flat morphism of schemes. If `V ⊆ Y` is a
retrocompact open which is scheme theoretically dense, then `f^{-1}V` is scheme theoretically
dense in `X`. -/
@[stacks 081H]
theorem schemeTheoreticallyDense_preimage_of_flat_of_isRetrocompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (V : Y.Opens)
    (hVretro : IsRetrocompact (V : Set Y)) (hVdense : schemeTheoreticallyDense V) :
    schemeTheoreticallyDense (f ⁻¹ᵁ V) := sorry

end AlgebraicGeometry
