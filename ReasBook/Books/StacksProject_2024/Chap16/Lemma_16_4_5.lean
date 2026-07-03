import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap16.Lemma_16_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open RamificationOneDvrFactorizationSituation

universe u v w

section

/-- A coarse statement-stage witness identifying `T` with one affine Néron blowup step of the
factorization situation `S`: the base and target DVRs are unchanged up to ring equivalence, and
the intermediate algebra of `T` is identified with the affine Néron blowup algebra attached to
`S`. -/
structure AffineNeronBlowupStepWitness
    (S T : RamificationOneDvrFactorizationSituation) where
  /-- The chosen parameter along which the affine Néron blowup is formed. -/
  parameter : S.R
  /-- The chosen parameter is a uniformizer candidate. -/
  parameter_irreducible : Irreducible parameter
  /-- The next stage has the same base DVR as the previous one, up to ring equivalence. -/
  baseRingEquiv : T.R ≃+* S.R
  /-- The next stage has the same target DVR as the previous one, up to ring equivalence. -/
  targetRingEquiv : T.L ≃+* S.L
  /-- The intermediate algebra of the next stage is the affine Néron blowup algebra of the
  previous stage. -/
  blowupAlgebraEquiv : T.A ≃+*
    affineBlowupChart S.p (neronBlowupParameter parameter parameter_irreducible)

/-- A finite tower of affine Néron blowups starting from `S` and ending at a stage smooth at its
center prime. -/
structure FiniteAffineNeronBlowupTower (S : RamificationOneDvrFactorizationSituation) where
  /-- The number of affine Néron blowup steps in the tower. -/
  length : ℕ
  /-- The factorization situations occurring in the tower. -/
  stages : Fin (length + 1) → RamificationOneDvrFactorizationSituation
  /-- The initial stage of the tower is the given situation `S`. -/
  start_eq : stages 0 = S
  /-- Each consecutive pair of stages is related by one affine Néron blowup step. -/
  step :
    ∀ i : Fin length, AffineNeronBlowupStepWitness (stages i.castSucc) (stages i.succ)
  /-- The terminal stage of the tower is smooth at its center prime. -/
  final_smooth :
    Algebra.SmoothAtPrime
      (stages (Fin.last length)).R
      (stages (Fin.last length)).A
      ⟨(stages (Fin.last length)).p, inferInstance⟩

variable (S : RamificationOneDvrFactorizationSituation)

-- Proof sketch: iterate the defect-reduction argument of Lemma `16.4.5`. Lemma `16.4.4` handles
-- the zero-defect case, while the Néron blowup comparison from Lemmas `16.4.2` and `16.4.3`
-- preserves the setup and decreases the torsion defect by at least `1` whenever the center is not
-- yet smooth. Since the defect is a natural number, the process terminates after finitely many
-- affine Néron blowups.
/-- Lemma 16.4.5: in Situation `16.4.1`, assume `R → A` is smooth at `𝔮 = ker(φ)`, formalized as
`Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩`, and that the special-fiber extension
`R / πR ⊆ Λ / πΛ` is separable. Then after finitely many affine Néron blowups one reaches a
factorization situation whose intermediate algebra is smooth over `R` at the center prime over
`𝔭`. In this statement-stage formalization, the finite sequence of blowups is recorded by
`FiniteAffineNeronBlowupTower S`. -/
theorem exists_finite_affine_neron_blowup_tower_with_smooth_center
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth_q : Algebra.SmoothAtPrime S.R S.A ⟨S.q, inferInstance⟩) :
    Nonempty (FiniteAffineNeronBlowupTower S) := sorry

end
