import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import stacks_proof.stacks_project.Chap09.Lemma_9_14_5
import stacks_proof.stacks_project.Chap09.Lemma_9_26_11
import stacks_proof.stacks_project.Chap09.Lemma_9_28_2
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_42_3
import Mathlib.Tactic.StacksAttribute


section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Helper for Lemma 10.42.4: the relative separable closure of a finitely generated field
extension is finite over the base field. -/
lemma finiteDimensional_separableClosure_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    FiniteDimensional k (separableClosure k K) := by
  -- The separable closure sits inside the finite-dimensional algebraic closure.
  letI : FiniteDimensional k (algebraicClosure k K) :=
    finiteDimensional_algebraicClosure k K
  letI : Algebra (separableClosure k K) (algebraicClosure k K) :=
    (IntermediateField.inclusion (le_algebraicClosure k K (separableClosure k K))).toAlgebra
  exact FiniteDimensional.left k (separableClosure k K) (algebraicClosure k K)

/-- Helper for Lemma 10.42.4: once a field extension `K / F` is finite-dimensional, the source
induction measure `[K : separableClosure F K]` is available because `K` is also finite-dimensional
over its relative separable closure. -/
lemma finiteDimensional_over_separableClosure_of_finiteDimensional
    (F : IntermediateField k K) [FiniteDimensional F K] :
    FiniteDimensional (separableClosure F K) K := by
  -- The relative separable closure is an intermediate field of the already finite extension
  -- `K / F`, so the top field stays finite-dimensional after enlarging the base to that closure.
  infer_instance

/-- Helper for Lemma 10.42.4: a transcendence-basis stage in a finitely generated extension gives
the finite relative degree over which the source induction on `[K : K_sep]` runs. -/
lemma finiteDimensional_over_separableClosure_of_isTranscendenceBasis
    [Algebra.EssFiniteType k K] {ι : Type*} {x : ι → K}
    (hx : IsTranscendenceBasis k x) :
    FiniteDimensional (separableClosure (IntermediateField.adjoin k (Set.range x)) K) K := by
  let F : IntermediateField k K := IntermediateField.adjoin k (Set.range x)
  -- The transcendence basis makes `K` algebraic over the generated rational-function stage.
  letI : Algebra.IsAlgebraic F K := by
    simpa [F] using hx.isAlgebraic_field
  -- Finite generation then upgrades algebraicity over `F` to a finite-dimensional extension.
  letI : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp k F K
  letI : Module.Finite F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : FiniteDimensional F K := by infer_instance
  -- Passing from `F` to its relative separable closure preserves finite-dimensionality.
  simpa [F] using
    (finiteDimensional_over_separableClosure_of_finiteDimensional (k := k) (K := K) F)

/-- Helper for Lemma 10.42.4: a finitely generated field extension admits a transcendence-basis
stage whose relative separable closure has finite index in the top field. -/
lemma exists_transcendence_basis_with_finiteDimensional_over_separableClosure
    [Algebra.EssFiniteType k K] :
    ∃ s : Set K,
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
        FiniteDimensional
          (separableClosure (IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K) K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  refine ⟨s, hs, ?_⟩
  -- This packages the verified prefix of the source proof before the positive-characteristic
  -- coefficient base-change step.
  exact finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := k) (K := K) hs

/-- Helper for Lemma 10.42.4: the source transcendence basis can be reindexed by
`Fin (Cardinal.toNat (Algebra.trdeg k K))` while keeping the finite relative degree
`[K : separableClosure(k(x_1, ..., x_r), K)]` needed for the source induction. -/
lemma exists_fin_reindexed_transcendence_basis_with_finiteDimensional_over_separableClosure
    [Algebra.EssFiniteType k K] :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K,
      IsTranscendenceBasis k x ∧
        FiniteDimensional
          (separableClosure (IntermediateField.adjoin k (Set.range x)) K) K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  obtain ⟨x, hx, hx_adjoin⟩ :=
    exists_fin_reindexed_transcendence_basis (k := k) (K := K) hs
  refine ⟨x, hx, ?_⟩
  -- Reindexing the transcendence basis preserves the generated rational-function stage.
  simpa [hx_adjoin] using
    finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := k) (K := K) hx

/-- Helper for Lemma 10.42.4: the inseparable degree over the transcendence-basis stage is
strictly positive, so the source induction never starts at `0`. -/
lemma finInsepDegree_pos_over_transcendence_basis_stage_aux
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x) :
    0 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  letI : FiniteDimensional (separableClosure F0 E) E := by
    -- The transcendence-basis stage makes the source inseparable-degree tail finite-dimensional.
    simpa [F0] using
      finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := F) (K := E) hx
  -- The induction measure is the positive finite rank over the relative separable closure.
  simpa [Field.finInsepDegree, F0] using
    (Module.finrank_pos (R := separableClosure F0 E) (M := E))

/-- Helper for Lemma 10.42.4: any finite-index transcendence-basis stage with separable top
already witnesses separable generation. -/
lemma isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range x)) E) :
    IsSeparablyGenerated F E := by
  -- The given transcendence basis is already in the exact Stacks-project shape.
  refine ⟨Set.range x, hx.to_subtype_range, ?_⟩
  simpa using hsep


end
