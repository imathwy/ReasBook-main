import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.ConditionRBasic

noncomputable section

universe u v

open CategoryTheory
open scoped Representation ZeroObject

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-
Route note.

The source exercise compares Serre's condition `(R)` with the base-change positive image/range
equality. In this theorem-local Lean surface, `SatisfiesConditionR` has already been normalized in
`ConditionRBasic` to that equality, so the proof below uses the definition directly and avoids the
older descent/decomposition support stack.
-/

/-- Exercise 16-16.3-8: for the modular system `(A, K, k)` under the large-field hypothesis on
`K`, the theorem-local condition `(R)` surface for the actual positive subset `R_K^+(G)` is
equivalent to the source-facing equality
`e(P_A^+(G)) = range(e) ∩ R_K^+(G)`, where
`e = projectiveGrothendieckBaseChangeHom K : P_A(G) → R_K(G)`. -/
theorem conditionR_iff_baseChange_image_eq_range_inter_positive
    [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionR_e16338 (R⁺[K](G)) A ↔
      e '' P⁺[A](G) =
        (((e).range : Set (finiteRepGrothendieckGroup K G)) ∩ R⁺[K](G)) := by
  -- Route correction: the theorem-local condition `(R)` surface is already the
  -- base-change positive image/range equality, so the target normalizes to `P ↔ P`.
  rfl

end

end Representation
