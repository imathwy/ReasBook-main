import Mathlib
import stacks_project.Chap15.Lemma_15_12_4
import stacks_project.Chap15.Lemma_15_51_3
import stacks_project.Chap15.Lemma_15_51_4
import stacks_project.Chap15.Lemma_15_51_10

-- Declarations for this item will be appended below by the statement pipeline.

open RingPairCat

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- Pair henselization exists as the right adjoint supplied by Lemma `15.12.1`. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [P.HasPropertyC] [P.HasPropertyD] [P.HasPropertyE]

-- Proof sketch: by Lemma `15.51.4`, it is enough to check the local formal fibres of the
-- henselization ring at maximal ideals. For a maximal ideal `m^h` of `A^h`, compare the completed
-- local ring of `(A^h)_(m^h)` with the completion of `A_m`, where `m` is the inverse image of
-- `m^h`. The completion comparison from Lemma `15.12.4`, the finite product description of the
-- fibre from Lemma `15.45.12`, property `(B)` for localization, and property `(E)` for separable
-- algebraic residue-field extensions transfer `P` from the formal fibres of `A` to those of
-- `A^h`.
/-- Lemma 15.51.7: if `A` is a `P`-ring and the field-algebra property `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then the canonical pair-henselization ring `A^h` of `(A, I)` is again a
`P`-ring. -/
theorem isPRing_henselizationRing
    (hA : IsPRing P A) :
    IsPRing P (henselizationRing (pairOfIdeal I)) := by
  let _ : IsPRing P A := hA
  let _ : IsNoetherianRing (henselizationRing (pairOfIdeal I)) :=
    henselizationRing_isNoetherian (pairOfIdeal I)
  sorry

end
