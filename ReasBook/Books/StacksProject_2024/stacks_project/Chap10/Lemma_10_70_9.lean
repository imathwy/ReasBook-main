import StacksProject_2024.stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open HomogeneousLocalization

section

variable {R : Type u} [CommRing R]

private theorem isReduced_polynomial [IsReduced R] : IsReduced (Polynomial R) := by
  constructor
  intro p hp
  ext i
  exact (Polynomial.isNilpotent_iff.mp hp i).eq_zero

variable (I : Ideal R) [IsReduced R]

/-- Supporting instance: if `R` is reduced, then the blowup algebra `Bl_I(R)` is reduced. -/
instance : IsReduced (reesAlgebra I) := by
  let _ : IsReduced (Polynomial R) := isReduced_polynomial
  exact isReduced_of_injective (reesAlgebra I).val Subtype.val_injective

/-- Supporting theorem: if `R` is reduced, then the blowup algebra `Bl_I(R)` is reduced. -/
theorem reesAlgebra_isReduced : IsReduced (reesAlgebra I) := by
  infer_instance

/-- Supporting instance: if `R` is reduced, then each affine blowup chart `R[I/a]` is reduced. -/
instance instIsReducedAffineBlowupChart (a : I) :
    IsReduced (affineBlowupChart I a) := by
  let _ : IsReduced (reesAlgebra I) := inferInstance
  let _ : IsReduced (Localization.Away (reesAlgebraDegreeOne I a)) := inferInstance
  exact isReduced_of_injective
    (algebraMap (affineBlowupChart I a) (Localization.Away (reesAlgebraDegreeOne I a)))
    (val_injective (Submonoid.powers (reesAlgebraDegreeOne I a)))

/-- Lemma 10.70.9 (Stacks tag `052S`): if `R` is reduced, then every affine blowup algebra
`R[I/a] = (Bl_I(R))_(a^(1))` is reduced. -/
theorem affineBlowupChart_isReduced (a : I) :
    IsReduced (affineBlowupChart I a) := by
  infer_instance

end
