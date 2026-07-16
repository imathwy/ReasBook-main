import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_70_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_137_10
import StacksProject_2024.stacks_project.Chap16.Lemma_16_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation
open scoped AffineBlowupChart

universe u v w

section

/-- Helper for Lemma 16.4.5: an irreducible parameter of the source DVR maps into the center ideal
`𝔭 ⊆ A`. -/
lemma algebraMap_uniformizer_mem_p
    (S : RamificationOneDvrFactorizationSituation.{u, v, w}) {π : S.R} (hπ : Irreducible π) :
    algebraMap S.R S.A π ∈ S.p := by
  -- Proof comment: an irreducible element of a DVR lies in the maximal ideal, and the source
  -- maximal ideal maps into the center ideal `𝔭`.
  have hπmax : π ∈ maximalIdeal S.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (irreducible_iff.mp hπ).1
  exact S.map_maximalIdeal_le_p (Ideal.mem_map_of_mem (algebraMap S.R S.A) hπmax)

/-- Helper for Lemma 16.4.5: the distinguished parameter used for the affine Néron blowup is the
image of the chosen irreducible parameter inside the center ideal `𝔭 ⊆ A`. -/
noncomputable def neronBlowupParameter
    (S : RamificationOneDvrFactorizationSituation.{u, v, w}) (π : S.R) (hπ : Irreducible π) :
    S.p :=
  ⟨algebraMap S.R S.A π, algebraMap_uniformizer_mem_p S hπ⟩

/-- A coarse statement-stage witness identifying `T` with one affine Néron blowup step of the
factorization situation `S`: the base and target DVRs are unchanged up to ring equivalence, and
the intermediate algebra of `T` is identified with the affine Néron blowup algebra attached to
`S`. -/
structure AffineNeronBlowupStepWitness
    (S T : RamificationOneDvrFactorizationSituation.{u, v, w}) where
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
  blowupAlgebraEquiv :
    let A := S.A
    let pA : Ideal A := S.p
    let πA : pA := neronBlowupParameter S parameter parameter_irreducible
    T.A ≃+* A[pA / πA]

/-- A finite tower of affine Néron blowups starting from `S` and ending at a stage smooth at its
center prime. -/
structure FiniteAffineNeronBlowupTower
    (S : RamificationOneDvrFactorizationSituation.{u, v, w}) where
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
      (stages (Fin.last length)).pPoint

/-- Helper for Lemma 16.4.5: if the center prime is already smooth, the required affine Néron
blowup tower has length `0`. -/
lemma zeroStepTowerOfSmoothCenter
    (S : RamificationOneDvrFactorizationSituation.{u, v, w})
    (hsmooth_p : Algebra.SmoothAtPrime S.R S.A S.pPoint) :
    Nonempty (FiniteAffineNeronBlowupTower S) := by
  -- Proof comment: package the current factorization situation as a tower with no blowup steps.
  refine ⟨{
    length := 0
    stages := fun _ => S
    start_eq := rfl
    step := ?_
    final_smooth := ?_
  }⟩
  · -- Proof comment: a zero-step tower has no consecutive stages to check.
    intro i
    exact Fin.elim0 i
  · -- Proof comment: the terminal stage of the zero-step tower is the original smooth center.
    simpa using hsmooth_p

/-- Helper for Lemma 16.4.5: a tower starting from a non-smooth center must have positive
length. -/
lemma towerLength_pos_of_not_centerSmooth
    {S : RamificationOneDvrFactorizationSituation.{u, v, w}}
    (ht : FiniteAffineNeronBlowupTower S)
    (hnot_smooth : ¬ Algebra.SmoothAtPrime S.R S.A S.pPoint) :
    0 < ht.length := by
  -- Proof comment: if the tower had length `0`, then its terminal smoothness would already say
  -- that the initial center is smooth.
  cases ht with
  | mk length stages start_eq step final_smooth =>
      dsimp at hnot_smooth ⊢
      by_contra hlen
      have hlen' : length = 0 := Nat.eq_zero_of_not_pos hlen
      subst hlen'
      have hsmooth : Algebra.SmoothAtPrime S.R S.A S.pPoint := by
        cases start_eq
        simpa using final_smooth
      exact hnot_smooth hsmooth

/-- Helper for Lemma 16.4.5: prepend one affine Néron blowup step to an existing finite tower. -/
def prependAffineNeronBlowupTower
    (S : RamificationOneDvrFactorizationSituation.{u, v, w})
    {T : RamificationOneDvrFactorizationSituation}
    (hstep : AffineNeronBlowupStepWitness S T)
    (ht : FiniteAffineNeronBlowupTower T) :
    FiniteAffineNeronBlowupTower S := by
  -- Proof comment: add `S` as a new initial stage and shift the old tower forward by one index.
  refine {
    length := ht.length + 1
    stages := fun i ↦
      match i with
      | ⟨0, _⟩ => S
      | ⟨n + 1, hlt⟩ => ht.stages ⟨n, Nat.lt_of_succ_lt_succ hlt⟩
    start_eq := rfl
    step := ?_
    final_smooth := ?_
  }
  · -- Proof comment: the first edge is the new blowup step, and later edges come from `ht`.
    intro i
    refine Fin.cases ?_ ?_ i
    · change AffineNeronBlowupStepWitness S (ht.stages 0)
      rw [ht.start_eq]
      exact hstep
    · intro j
      simpa using ht.step j
  · -- Proof comment: the final stage is unchanged, so its smoothness is inherited from `ht`.
    simpa using ht.final_smooth

/-- Helper for Lemma 16.4.5: a positive-length tower decomposes into its first affine blowup step
and a tail tower. -/
lemma exists_step_and_tail_of_positiveTower
    {S : RamificationOneDvrFactorizationSituation.{u, v, w}}
    (ht : FiniteAffineNeronBlowupTower S) (hpos : 0 < ht.length) :
    ∃ T : RamificationOneDvrFactorizationSituation.{u, v, w},
      Nonempty (AffineNeronBlowupStepWitness S T) ∧ Nonempty (FiniteAffineNeronBlowupTower T) := by
  -- Proof comment: write the tower length as `n + 1`, read off the first step, and reindex the
  -- remaining stages to obtain the tail tower.
  cases ht with
  | mk length stages start_eq step final_smooth =>
      dsimp at hpos ⊢
      obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      subst hlen
      let T : RamificationOneDvrFactorizationSituation.{u, v, w} :=
        stages ⟨1, by simpa using Nat.succ_lt_succ (Nat.succ_pos n)⟩
      refine ⟨T, ?_, ?_⟩
      · -- Proof comment: the first edge of the original tower is the required initial blowup step.
        refine ⟨?_⟩
        have hstep0 := step ⟨0, Nat.succ_pos n⟩
        simpa [T, start_eq] using hstep0
      · -- Proof comment: drop the initial stage and shift every remaining index down by one.
        refine ⟨{
          length := n
          stages := fun i ↦ stages ⟨i.1 + 1, by
            simpa [Nat.add_assoc] using Nat.succ_lt_succ i.2⟩
          start_eq := rfl
          step := ?_
          final_smooth := ?_
        }⟩
        · intro i
          simpa [Nat.add_assoc] using step i.succ
        · simpa [Nat.add_assoc] using final_smooth

/-- Helper for Lemma 16.4.5: the induction state bundles the factorization situation together
with the parameter and auxiliary hypotheses that must survive each affine Néron blowup step. -/
structure NeronBlowupInductionState where
  /-- The current ramification-one DVR factorization situation. -/
  S : RamificationOneDvrFactorizationSituation.{u, v, w}
  /-- The chosen parameter used to form the affine Néron blowup. -/
  π : S.R
  /-- The chosen parameter is irreducible. -/
  hπ : Irreducible π
  /-- The induced special-fiber algebra structure. -/
  instSpecialFiberAlgebra :
    Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))
  /-- The special-fiber field extension is separable. -/
  hsep : Algebra.IsSeparable
    (S.R ⧸ Ideal.span ({π} : Set S.R))
    (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))
  /-- The generic point `q` is already smooth over the base DVR. -/
  hsmooth_q : Algebra.SmoothAtPrime S.R S.A S.qPoint

attribute [instance] NeronBlowupInductionState.instSpecialFiberAlgebra

/-- Helper for Lemma 16.4.5: the source theorem starts from the given situation viewed as a
bundled induction state. -/
noncomputable def initialNeronBlowupInductionState
    (S : RamificationOneDvrFactorizationSituation.{u, v, w})
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth_q : Algebra.SmoothAtPrime S.R S.A S.qPoint) :
    NeronBlowupInductionState :=
  -- Proof comment: this definition is only the transparent packaging of the theorem inputs into
  -- the induction-state record used by the strong-induction scaffold.
  { S := S
    π := π
    hπ := hπ
    instSpecialFiberAlgebra := inferInstance
    hsep := hsep
    hsmooth_q := hsmooth_q }

/-- Helper for Lemma 16.4.5: the center-smoothness predicate attached to a bundled induction
state. -/
abbrev centerSmooth (st : NeronBlowupInductionState.{u, v, w}) : Prop :=
  Algebra.SmoothAtPrime st.S.R st.S.A st.S.pPoint

/-- Helper for Lemma 16.4.5: if a bundled induction state with non-smooth center already admits a
finite affine Néron blowup tower, then its first blowup step leaves a tail tower of strictly
smaller length. -/
lemma exists_successorSituation_and_shorterTail_of_not_centerSmooth
    (st : NeronBlowupInductionState.{u, v, w})
    (ht : FiniteAffineNeronBlowupTower st.S)
    (hnot_smooth : ¬ centerSmooth st) :
    ∃ T : RamificationOneDvrFactorizationSituation.{u, v, w},
      Nonempty (AffineNeronBlowupStepWitness st.S T) ∧
        ∃ ht' : FiniteAffineNeronBlowupTower T, ht'.length < ht.length := by
  -- Proof comment: non-smoothness forces a positive tower length, so the first affine blowup step
  -- can be split off and the remaining stages form a strictly shorter tail tower.
  cases ht with
  | mk length stages start_eq step final_smooth =>
      dsimp [centerSmooth] at hnot_smooth ⊢
      have hposTower :
          0 <
            (FiniteAffineNeronBlowupTower.mk length stages start_eq step final_smooth :
              FiniteAffineNeronBlowupTower st.S).length := by
        exact towerLength_pos_of_not_centerSmooth
          (FiniteAffineNeronBlowupTower.mk length stages start_eq step final_smooth) hnot_smooth
      have hpos : 0 < length := by
        simpa using hposTower
      obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      subst hlen
      let T : RamificationOneDvrFactorizationSituation.{u, v, w} :=
        stages ⟨1, by simpa using Nat.succ_lt_succ (Nat.succ_pos n)⟩
      refine ⟨T, ?_, ?_⟩
      · -- Proof comment: the first edge of the existing tower supplies the required successor.
        refine ⟨?_⟩
        have hstep0 := step ⟨0, Nat.succ_pos n⟩
        simpa [T, start_eq] using hstep0
      · -- Proof comment: deleting the initial stage reindexes the tail into a shorter tower.
        refine ⟨{
          length := n
          stages := fun i ↦ stages ⟨i.1 + 1, by
            simpa [Nat.add_assoc] using Nat.succ_lt_succ i.2⟩
          start_eq := rfl
          step := ?_
          final_smooth := ?_
        }, Nat.lt_succ_self n⟩
        · intro i
          simpa [Nat.add_assoc] using step i.succ
        · simpa [Nat.add_assoc] using final_smooth

/-- Helper for Lemma 16.4.5: the `st.S.L`-module obtained by base changing the Kähler
differentials of `st.S.A` over `st.S.R`. -/
abbrev kaehlerDifferentialBaseChange (st : NeronBlowupInductionState.{u, v, w}) :=
  TensorProduct st.S.A st.S.L (_root_.KaehlerDifferential st.S.R st.S.A)

/-- Helper for Lemma 16.4.5: freeness of the base-changed Kähler differentials already implies
that the current center prime is smooth. -/
lemma centerSmooth_of_freeKaehlerDifferentialBaseChange
    (st : NeronBlowupInductionState.{u, v, w})
    (hfree : Module.Free st.S.L (kaehlerDifferentialBaseChange st)) :
    centerSmooth st := by
  -- Proof comment: Lemma `16.4.4` converts generic-point smoothness plus Kähler freeness into
  -- smoothness at the center prime.
  exact smoothAtPrime_p_of_smoothAtPrime_q_of_free_kaehlerDifferential_baseChange
    st.S st.hsmooth_q hfree

/-- Helper for Lemma 16.4.5: once the base-changed Kähler differentials are free, no affine Néron
blowup step is needed. -/
lemma zeroStepTowerOfFreeKaehlerDifferentialBaseChange
    (st : NeronBlowupInductionState.{u, v, w})
    (hfree : Module.Free st.S.L (kaehlerDifferentialBaseChange st)) :
    Nonempty (FiniteAffineNeronBlowupTower st.S) := by
  -- Proof comment: apply the zero-step tower constructor after translating freeness into
  -- center-smoothness.
  exact zeroStepTowerOfSmoothCenter st.S
    (centerSmooth_of_freeKaehlerDifferentialBaseChange st hfree)

/-- Helper for Lemma 16.4.5: a natural-number defect together with a strict successor step for
every non-smooth center is enough to produce a finite affine Néron blowup tower. -/
structure NeronBlowupDefectData where
  /-- The natural-number measure used for strong induction. -/
  defect : NeronBlowupInductionState.{u, v, w} → ℕ
  /-- Every non-smooth center admits one affine blowup step to a strictly smaller state. -/
  nextState_of_notSmoothCenter :
    ∀ st : NeronBlowupInductionState.{u, v, w},
      ¬ centerSmooth st →
        ∃ st' : NeronBlowupInductionState.{u, v, w},
          Nonempty (AffineNeronBlowupStepWitness st.S st'.S) ∧ defect st' < defect st

/-- Helper for Lemma 16.4.5: once the source proof provides a strictly decreasing defect on the
bundled induction states, strong induction assembles the finite affine Néron blowup tower. -/
lemma finiteTowerOfDefectData
    (D : NeronBlowupDefectData.{u, v, w}) (st : NeronBlowupInductionState.{u, v, w}) :
    Nonempty (FiniteAffineNeronBlowupTower st.S) := by
  -- Proof comment: use strong induction on the defect; smooth centers stop immediately, while a
  -- non-smooth center advances to a strictly smaller bundled state.
  have haux :
      ∀ n : ℕ,
        ∀ st : NeronBlowupInductionState.{u, v, w},
          D.defect st = n → Nonempty (FiniteAffineNeronBlowupTower st.S) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih st hdef
    by_cases hsmooth_p : centerSmooth st
    · -- Proof comment: a smooth center already gives the required tower with zero blowup steps.
      exact zeroStepTowerOfSmoothCenter st.S hsmooth_p
    · -- Proof comment: advance one affine blowup step and invoke the induction hypothesis on the
      -- strictly smaller defect.
      rcases D.nextState_of_notSmoothCenter st hsmooth_p with ⟨st', ⟨hstep⟩, hlt⟩
      have hlt' : D.defect st' < n := by
        simpa [hdef] using hlt
      rcases ih (D.defect st') hlt' st' rfl with ⟨ht'⟩
      exact ⟨prependAffineNeronBlowupTower st.S hstep ht'⟩
  exact haux (D.defect st) st rfl

/-- Helper for Lemma 16.4.5: the remaining missing source-proof input is a bundled defect package
whose one-step strict decrease is proved from the affine Néron blowup comparison. -/
lemma existsNeronBlowupDefectData : Nonempty (NeronBlowupDefectData.{u, v, w}) := by
  -- Route correction: the unresolved work is now isolated to the genuine mathematical input of
  -- Lemma `16.4.5`, namely packaging the source proof's defect and proving its strict decrease
  -- after one affine Néron blowup whenever the center is not yet smooth.
  -- TODO: the first missing ingredient is still an owner-level successor theorem in the current
  -- dependency closure. Concretely, `lake lean stacks_project/Chap16/Lemma_16_4_2.lean` fails at
  -- the localized/base-change comparison API with missing instances
  -- `Algebra (Localization.Away a) (localizedNeronBlowupTarget π hπ a)` and dependent transport
  -- failures around `localizedNeronBlowupSourceEquiv`, so this file should not duplicate that
  -- broken transport package locally. The local frontier is already verified by
  -- `exists_successorSituation_and_shorterTail_of_not_centerSmooth`: any completed tower for a
  -- non-smooth center splits into a first raw successor situation and a strictly shorter tail.
  -- What is still missing is the owner-level transport that upgrades that raw successor situation
  -- to a new bundled `NeronBlowupInductionState`. Once that owner API is repaired, one can
  -- construct from `st : NeronBlowupInductionState` the successor situation with algebra
  -- `st.S.A[st.S.p / πA]`, transport `hsep` and `hsmooth_q`, define the Kähler torsion defect,
  -- and prove its strict drop via
  -- `neronBlowup_surjection_baseChange_surjective_with_ker_awayTorsion`.
  sorry

-- Proof sketch: iterate the defect-reduction argument of Lemma `16.4.5`. Lemma `16.4.4` handles
-- the zero-defect case, while the Néron blowup comparison from Lemmas `16.4.2` and `16.4.3`
-- preserves the setup and decreases the torsion defect by at least `1` whenever the center is not
-- yet smooth. Since the defect is a natural number, the process terminates after finitely many
-- affine Néron blowups.
variable (S : RamificationOneDvrFactorizationSituation.{u, v, w})

/-- Lemma 16.4.5: in Situation `16.4.1`, assume `R → A` is smooth at `𝔮 = ker(φ)`, formalized as
`Algebra.SmoothAtPrime S.R S.A S.qPoint`, and that the special-fiber extension `R / πR ⊆ Λ / πΛ`
is separable. Then after finitely many affine Néron blowups one reaches a factorization
situation whose intermediate algebra is smooth over `R` at the center prime over `𝔭`. In this
statement-stage formalization, the finite sequence of blowups is recorded by
`FiniteAffineNeronBlowupTower S`. -/
theorem exists_finite_affine_neron_blowup_tower_with_smooth_center
    (π : S.R) (hπ : Irreducible π)
    [Algebra (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L))]
    (hsep : Algebra.IsSeparable
      (S.R ⧸ Ideal.span ({π} : Set S.R))
      (S.L ⧸ Ideal.span ({algebraMap S.R S.L π} : Set S.L)))
    (hsmooth_q : Algebra.SmoothAtPrime S.R S.A S.qPoint) :
    Nonempty (FiniteAffineNeronBlowupTower S) := by
  -- Proof comment: once the defect package exists, the theorem is just the strong-induction
  -- scaffold applied to the transparent initial bundled state.
  rcases (existsNeronBlowupDefectData.{u, v, w}) with ⟨D⟩
  exact finiteTowerOfDefectData D
    (initialNeronBlowupInductionState S π hπ hsep hsmooth_q)

end
