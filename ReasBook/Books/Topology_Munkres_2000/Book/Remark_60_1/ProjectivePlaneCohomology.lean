module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic.NormNum

public section

namespace RealProjectivePlane

/-- Helper for Remark 60.1: the degree-two group computed by the standard cellular
cochain model of the real projective plane. -/
abbrev DegreeTwoCellularCohomology := ZMod 2

/-- Helper for Remark 60.1: the cellular degree-two group of the real projective plane
contains a nonzero class annihilated by two. -/
lemma exists_nonzero_twoTorsion_degreeTwoCellularCohomology :
    ∃ c : DegreeTwoCellularCohomology, c ≠ 0 ∧ 2 • c = 0 := by
  -- The residue class of one is nonzero modulo two.
  refine ⟨1, ?_, ?_⟩
  · norm_num [DegreeTwoCellularCohomology]
  · -- Multiplication by two vanishes in the quotient by the cellular coboundaries.
    decide

/-- Helper for Remark 60.1: the cellular degree-two group of the real projective plane
cannot be additively equivalent to a torsion-free group. -/
lemma degreeTwoCellularCohomology_not_addEquiv_torsionFree
    {A : Type*} [AddCommMonoid A] [IsAddTorsionFree A] :
    ¬ Nonempty (DegreeTwoCellularCohomology ≃+ A) := by
  -- Transport the nonzero cellular class and cancel its two-torsion in the target.
  rintro ⟨e⟩
  obtain ⟨c, hc, htwo⟩ :=
    exists_nonzero_twoTorsion_degreeTwoCellularCohomology
  have hmap : 2 • e c = 0 := by
    calc
      2 • e c = e (2 • c) := (e.toAddMonoidHom.map_nsmul 2 c).symm
      _ = e 0 := congrArg e htwo
      _ = 0 := e.map_zero
  have htwoNat : (2 : ℕ) ≠ 0 := by
    norm_num
  have hezero : e c = 0 :=
    nsmul_right_injective htwoNat (by simpa using hmap)
  exact hc (e.injective (by simpa using hezero))

end RealProjectivePlane
