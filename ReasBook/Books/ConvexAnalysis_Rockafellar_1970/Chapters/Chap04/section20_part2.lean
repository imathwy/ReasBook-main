import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section20_part1

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Corollary 20.0.3: with an empty index family, any split-sum attainment
witness for the conjugate infimal convolution forces the target vector to be zero. -/
lemma helperForCorollary_20_0_3_attainment_target_eq_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ}
    (hAtt :
      ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    xStar = (0 : Fin n → ℝ) := by
  exact
    helperForCorollary_20_0_2_attainmentWitness_target_eq_zero_of_index_empty
      (g := fun i => fenchelConjugate n (f i)) (xStar := xStar) hAtt

/-- Helper for Corollary 20.0.3: for an empty index family, the split-attainment
condition is equivalent to the target covector being zero. -/
lemma helperForCorollary_20_0_3_exists_attainmentWitness_iff_target_eq_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    (∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      xStar = (0 : Fin n → ℝ) := by
  constructor
  · intro hAtt
    exact
      helperForCorollary_20_0_3_attainment_target_eq_zero_of_empty_index
        (f := f) (xStar := xStar) hAtt
  · intro hxStar
    subst hxStar
    exact
      helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
        (g := fun i => fenchelConjugate n (f i))

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target
covector makes attainment-witness existence equivalent to False. -/
lemma helperForCorollary_20_0_3_exists_attainmentWitness_iff_false_of_empty_index_of_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ)
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    (∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      False := by
  constructor
  · intro hAtt
    have hxStarZero : xStar = (0 : Fin n → ℝ) :=
      (helperForCorollary_20_0_3_exists_attainmentWitness_iff_target_eq_zero_of_empty_index
        (f := f) (xStar := xStar)).1 hAtt
    exact hxStar hxStarZero
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target
cannot admit any split-sum decomposition. -/
lemma helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
    {n : ℕ} {xStar : Fin n → ℝ}
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar := by
  intro hSplit
  rcases hSplit with ⟨xStarFamily, hsum⟩
  have hsumZero : (∑ i, xStarFamily i) = (0 : Fin n → ℝ) := by
    simp
  have hxStarZero : xStar = (0 : Fin n → ℝ) := hsum.symm.trans hsumZero
  exact hxStar hxStarZero

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target cannot
admit an attainment witness for the conjugate infimal convolution split. -/
lemma helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ}
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  intro hAtt
  rcases hAtt with ⟨xStarFamily, hsum, _hattain⟩
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := n) (xStar := xStar) hxStar ⟨xStarFamily, hsum⟩

/-- Helper for Corollary 20.0.3: if an empty-index model has at least one nonzero
covector, then the universal attainment claim is impossible. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_exists_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal)
    (hne : ∃ xStar : Fin n → ℝ, xStar ≠ (0 : Fin n → ℝ)) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hAll
  rcases hne with ⟨xStar, hxStar⟩
  exact
    helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
      (f := f) (xStar := xStar) hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: in dimension one, the constant-one covector is nonzero. -/
lemma helperForCorollary_20_0_3_unitCovector_ne_zero :
    (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
  intro h
  have h0 : (1 : ℝ) = 0 := by
    simpa using congrArg (fun g : Fin 1 → ℝ => g 0) h
  norm_num at h0

/-- Helper for Corollary 20.0.3: in any nonzero dimension, the constant-one covector
is nonzero. -/
lemma helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    (fun _ : Fin n => (1 : ℝ)) ≠ (0 : Fin n → ℝ) := by
  intro h
  have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
  let i0 : Fin n := ⟨0, hnPos⟩
  have h0 : (1 : ℝ) = 0 := by
    simpa using congrArg (fun g : Fin n → ℝ => g i0) h
  norm_num at h0

/-- Helper for Corollary 20.0.3: in nonzero dimension there exists a nonzero covector. -/
lemma helperForCorollary_20_0_3_exists_nonzero_covector_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    ∃ xStar : Fin n → ℝ, xStar ≠ (0 : Fin n → ℝ) := by
  refine ⟨fun _ : Fin n => (1 : ℝ), ?_⟩
  exact
    helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
      (n := n) hnZero

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
one cannot decompose every covector as a `Fin 0`-indexed split sum. -/
lemma helperForCorollary_20_0_3_universal_splitSum_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar) := by
  rcases
    helperForCorollary_20_0_3_exists_nonzero_covector_of_dim_ne_zero
      (n := n) hnZero with ⟨xStar, hxStar⟩
  intro hAll
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := n) (xStar := xStar) hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the constant-one covector admits no attainment witness for the conjugate split. -/
lemma helperForCorollary_20_0_3_no_attainment_witness_for_constOne_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = (fun _ : Fin n => (1 : ℝ)) ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i))
            (fun _ : Fin n => (1 : ℝ)) =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  exact
    helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
      (f := f)
      (xStar := fun _ : Fin n => (1 : ℝ))
      (helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
        (n := n) hnZero)

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the constant-one covector is an explicit target with no attainment witness. -/
lemma helperForCorollary_20_0_3_exists_counterexample_no_attainment_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ∃ xStar : Fin n → ℝ,
      ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  refine ⟨fun _ : Fin n => (1 : ℝ), ?_⟩
  exact
    helperForCorollary_20_0_3_no_attainment_witness_for_constOne_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the universal attainment claim is impossible. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  rcases
    helperForCorollary_20_0_3_exists_counterexample_no_attainment_of_empty_index_of_dim_ne_zero
      (f := f) hnZero with ⟨xStar, hxStar⟩
  exact
    fun hAll => hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: in the empty-index case, if universal attainment
holds, then the ambient dimension must be zero. -/
lemma helperForCorollary_20_0_3_dim_eq_zero_of_empty_index_of_universalAttainment
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal)
    (hAll :
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    n = 0 := by
  by_contra hnZero
  exact
    (helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero) hAll

/-- Helper for Corollary 20.0.3: with an empty index family, universal attainment fails
already for the one-dimensional constant-one target covector. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index
    (f : Fin 0 → (Fin 1 → ℝ) → EReal) :
    ¬ (∀ xStar : Fin 1 → ℝ,
        ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
              ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (n := 1) (f := f) Nat.one_ne_zero

/-- Helper for Corollary 20.0.3: in zero dimension, every covector is zero. -/
lemma helperForCorollary_20_0_3_covector_eq_zero_of_dim_zero
    (xStar : Fin 0 → ℝ) :
    xStar = (0 : Fin 0 → ℝ) := by
  ext i
  exact Fin.elim0 i

/-- Helper for Corollary 20.0.3: with an empty index family, universal attainment
is equivalent to the ambient dimension being zero. -/
lemma helperForCorollary_20_0_3_universalAttainment_iff_dim_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) :
    (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      n = 0 := by
  constructor
  · intro hAll
    exact
      helperForCorollary_20_0_3_dim_eq_zero_of_empty_index_of_universalAttainment
        (f := f) hAll
  · intro hnZero
    subst hnZero
    intro xStar
    have hxStarZero : xStar = (0 : Fin 0 → ℝ) :=
      helperForCorollary_20_0_3_covector_eq_zero_of_dim_zero xStar
    simpa [hxStarZero] using
      (helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
        (g := fun i => fenchelConjugate 0 (f i)))

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the full refinement-plus-universal-attainment conclusion is impossible. -/
lemma helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          ∃ xStarFamily : Fin 0 → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hConclusion
  exact
    (helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero) hConclusion.2

/-- Helper for Corollary 20.0.3: there is explicit empty-index data satisfying
all hypotheses while universal attainment fails in dimension one. -/
lemma helperForCorollary_20_0_3_exists_hypotheses_without_universalAttainment
    :
    ∃ f : Fin 0 → (Fin 1 → ℝ) → EReal,
      (∀ i, IsPolyhedralConvexFunction 1 (f i)) ∧
      (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      ¬ (∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · simpa using
      (Set.nonempty_univ : Set.Nonempty (Set.univ : Set (Fin 1 → ℝ)))
  · exact
      helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index
        (f := fun i => Fin.elim0 i)

/-- Helper for Corollary 20.0.3: in the concrete branch `m = 0`, `n = 1`,
the standard hypotheses do not imply universal split-attainment. -/
lemma helperForCorollary_20_0_3_not_imp_universalAttainment_in_empty_index_dim_one
    :
    ¬ (∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        ∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  intro hImp
  rcases helperForCorollary_20_0_3_exists_hypotheses_without_universalAttainment with
    ⟨f, hpoly, hproper, hdom, hNotAll⟩
  exact hNotAll (hImp f hpoly hproper hdom)

/-- Helper for Corollary 20.0.3: in the concrete branch `m = 0`, `n = 1`,
the full refinement-plus-universal-attainment conclusion cannot follow from the
standard hypotheses. -/
lemma helperForCorollary_20_0_3_not_imp_full_refinement_and_universalAttainment_in_empty_index_dim_one
    :
    ¬ (∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        fenchelConjugate 1 (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
          ∀ xStar : Fin 1 → ℝ,
            ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                  ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  intro hImp
  exact
    helperForCorollary_20_0_3_not_imp_universalAttainment_in_empty_index_dim_one
      (fun f hpoly hproper hdom => (hImp f hpoly hproper hdom).2)

/-- Helper for Corollary 20.0.3: the hypotheses do not imply the full
refinement-plus-universal-attainment conclusion in all dimensions/index sizes.
The branch `n = 1`, `m = 0` gives a concrete obstruction. -/
lemma helperForCorollary_20_0_3_not_forall_dimensions_refinement_and_universalAttainment
    :
    ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → ℝ) → EReal),
        (∀ i, IsPolyhedralConvexFunction n (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) →
        fenchelConjugate n (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
          ∀ xStar : Fin n → ℝ,
            ∃ xStarFamily : Fin m → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                  ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hAll
  have hDimOne :
      ∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        fenchelConjugate 1 (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
          ∀ xStar : Fin 1 → ℝ,
            ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                  ∑ i, fenchelConjugate 1 (f i) (xStarFamily i) := by
    intro f hpoly hproper hdom
    exact hAll 1 0 f hpoly hproper hdom
  exact
    helperForCorollary_20_0_3_not_imp_full_refinement_and_universalAttainment_in_empty_index_dim_one
      hDimOne

/-- Helper for Corollary 20.0.3: in the branch `m = 0`, `n = 1`, the constant-one
target covector cannot be represented as a `Fin 0`-indexed split sum. -/
lemma helperForCorollary_20_0_3_no_split_sum_for_unitCovector_of_empty_index
    :
    ¬ ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
        (∑ i, xStarFamily i) = (fun _ : Fin 1 => (1 : ℝ)) := by
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := 1)
      (xStar := fun _ : Fin 1 => (1 : ℝ))
      helperForCorollary_20_0_3_unitCovector_ne_zero

/-- Helper for Corollary 20.0.3: in the branch `m = 0` and `n ≠ 0`,
the standard polyhedral/proper/domain hypotheses still do not imply universal
split-attainment. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_under_hypotheses_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0)
    (_hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (_hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (_hdom :
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: in the branch `m = 0` and `n ≠ 0`,
the full refinement-plus-universal-attainment conclusion is incompatible even
under the standard polyhedral/proper/domain hypotheses. -/
lemma helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_under_hypotheses_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0)
    (_hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (_hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (_hdom :
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ¬ (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          ∃ xStarFamily : Fin 0 → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: when `0 < m`, each covector admits an attaining split
for the infimal convolution of conjugates. -/
theorem helperForCorollary_20_0_3_attainment_for_each_xStar_of_pos_m
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    ∀ xStar : Fin n → ℝ,
      ∃ xStarFamily : Fin m → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  intro xStar
  exact
    infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
      (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
      (hmPos := hmPos) (xStar := xStar)

/-- Helper for Corollary 20.0.3: if the index family is nonempty (`0 < m`), then the
polyhedral sum-conjugate identity and universal attainment conclusion both hold. -/
theorem helperForCorollary_20_0_3_refinement_and_attainment_of_pos_m
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  refine And.intro ?_ ?_
  · exact
      fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
  · intro xStar
    exact
      helperForCorollary_20_0_3_attainment_for_each_xStar_of_pos_m
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
        (hmPos := hmPos) xStar

/-- Corollary 20.0.3: In the polyhedral case, Theorem 20.0.1 yields the
sum-conjugate/infimal-convolution identity without closure, under the simpler condition
dom f₁ ∩ ⋯ ∩ dom fₘ ≠ ∅, and the infimum in the infimal convolution is attained. -/
theorem polyhedral_refinement_fenchelConjugate_sum_eq_infimalConvolutionFamily_and_attainment
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  exact
    helperForCorollary_20_0_3_refinement_and_attainment_of_pos_m
      (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom) (hmPos := hmPos)

/-- Helper for Theorem 20.0.4: every summand indexed by `Ipoly` is closed proper
polyhedral, hence equal to its convex-function closure. -/
lemma helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_mem_Ipoly
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (i : Fin m) (hi : i ∈ Ipoly) :
    convexFunctionClosure (f i) = f i := by
  have hpoly_i : IsPolyhedralConvexFunction n (f i) := (hpoly i).1 hi
  have hclosed : ClosedConvexFunction (f i) :=
    helperForCorollary_19_1_2_closed_of_polyhedral_proper
      (f := f i) hpoly_i (hproper i)
  have hbot : ∀ x : Fin n → ℝ, f i x ≠ (⊥ : EReal) := by
    intro x
    exact (hproper i).2.2 x (by simp)
  exact convexFunctionClosure_eq_of_closedConvexFunction (f := f i) hclosed hbot

/-- Helper for Theorem 20.0.4: unpack a witness from the mixed
`dom/ri`-intersection assumption into pointwise membership facts. -/
lemma helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ∃ x0 : EuclideanSpace ℝ (Fin n),
      (∀ i : Fin m, i ∈ Ipoly →
          x0 ∈ ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) ∧
      (∀ i : Fin m, i ∉ Ipoly →
          x0 ∈ euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  rcases hdom_ri with ⟨x0, hx0⟩
  rcases hx0 with ⟨hxLeft, hxRight⟩
  refine ⟨x0, ?_, ?_⟩
  · intro i hi
    have hxLeft :
        x0 ∈
          ⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      hxLeft
    exact (Set.mem_iInter.mp hxLeft) ⟨i, hi⟩
  · intro i hi
    have hxRight :
        x0 ∈
          ⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      hxRight
    exact (Set.mem_iInter.mp hxRight) ⟨i, hi⟩

/-- Helper for Theorem 20.0.4: mixed `dom/ri` qualification should identify the
sum-of-closures with the closure of the sum. -/
lemma helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly
    {α : Type*} [AddCommMonoid α] {m : ℕ}
    (Ipoly : Set (Fin m)) [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (g : Fin m → α) :
    (∑ i, g i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), g i) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), g i) := by
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin m)))
      (p := fun i : Fin m => i ∈ Ipoly) (f := g)).symm

/-- Helper for Theorem 20.0.4: rewrite both full sums into `Ipoly` and `Ipolyᶜ`
filter blocks, and remove closures on the polyhedral block. -/
lemma helperForTheorem_20_0_4_splitSums_poly_nonpoly_blocks
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) ∧
    (fun x => ∑ i, f i x) =
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  refine And.intro ?_ ?_
  · funext x
    have hsplit :
        (∑ i, convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) :=
      helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly (Ipoly := Ipoly)
        (g := fun i : Fin m => convexFunctionClosure (f i) x)
    have hpolyBlock :
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hiIpoly : i ∈ Ipoly := (Finset.mem_filter.mp hi).2
      simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g x)
        (helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_mem_Ipoly
          (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) i hiIpoly)
    calc
      (∑ i, convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) :=
        hsplit
      _ =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
        rw [hpolyBlock]
  · funext x
    exact
      helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly
        (Ipoly := Ipoly) (g := fun i : Fin m => f i x)

/-- Helper for Theorem 20.0.4: the mixed hypothesis yields nonempty intersection of
relative interiors on the nonpolyhedral block. -/
lemma helperForTheorem_20_0_4_nonpoly_hri_nonempty_iInter
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    Set.Nonempty
      (⋂ i : {i : Fin m // i ∉ Ipoly},
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, _hxPoly, hxNonpoly⟩
  refine ⟨x0, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  exact hxNonpoly i.1 i.2

/-- Helper for Theorem 20.0.4: the mixed qualification provides a common
effective-domain point for all nonpolyhedral indices. -/
lemma helperForTheorem_20_0_4_nonpoly_common_effectiveDomain_point
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    Set.Nonempty
      (⋂ i : {i : Fin m // i ∉ Ipoly},
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, _hxPoly, hxNonpoly⟩
  refine ⟨(x0 : Fin n → ℝ), ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  have hxri :
      x0 ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
    hxNonpoly i.1 i.2
  have hxpre :
      x0 ∈
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
    (euclideanRelativeInterior_subset_closure n
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))).1 hxri
  simpa [Set.mem_preimage] using hxpre

/-- Helper for Theorem 20.0.4: the filtered nonpolyhedral block is proper,
using the common effective-domain point extracted from the mixed qualification. -/
lemma helperForTheorem_20_0_4_nonpoly_filter_block_proper
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∉ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hdomJ :
      Set.Nonempty
        (⋂ j : J, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j)) := by
    simpa [J, fJ] using
      helperForTheorem_20_0_4_nonpoly_common_effectiveDomain_point
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri)
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hproperSumFin :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := fFin) (hproper := hproperFin) (hdom := hdomFin)
  have hsumFinToJ :
      (fun x => ∑ i : Fin k, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin k => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin k, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  simpa [hsumFinToFilter] using hproperSumFin

/-- Helper for Theorem 20.0.4: the nonpolyhedral filtered block satisfies the
Section 16 closure-of-sum identity under the extracted `ri` qualification. -/
lemma helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
      convexFunctionClosure
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∉ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hriJ :
      Set.Nonempty
        (⋂ j : J,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j))) := by
    simpa [J, fJ] using
      helperForTheorem_20_0_4_nonpoly_hri_nonempty_iInter
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri)
  have hriFin :
      Set.Nonempty
        (⋂ i : Fin k,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i))) := by
    rcases hriJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hsumFin :=
    section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
      (f := fFin) hproperFin hriFin
  have hleftFinToJ :
      (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) =
        (fun x => ∑ j : J, convexFunctionClosure (fJ j) x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => convexFunctionClosure (fJ j) x)
        (fun i : Fin k => convexFunctionClosure (fJ (eJ.symm i)) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hleftJToFilter :
      (fun x => ∑ j : J, convexFunctionClosure (fJ j) x) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => convexFunctionClosure (f i) x))
  have hrightFinToJ :
      (fun x => ∑ i : Fin k, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin k => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hrightJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hleft :
      (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
    exact hleftFinToJ.trans hleftJToFilter
  have hright :
      convexFunctionClosure (fun x => ∑ i : Fin k, fFin i x) =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    congr 1
    exact hrightFinToJ.trans hrightJToFilter
  calc
    (fun x =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
        (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) := hleft.symm
    _ = convexFunctionClosure (fun x => ∑ i : Fin k, fFin i x) := hsumFin
    _ = convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := hright

/-- Helper for Theorem 20.0.4: the polyhedral filtered block is proper and has a
domain witness extracted from the mixed qualification point. -/
lemma helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) ∧
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∈ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hdomJ :
      Set.Nonempty
        (⋂ j : J, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j)) := by
    rcases
      helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, hxPoly, _hxNonpoly⟩
    refine ⟨(x0 : Fin n → ℝ), ?_⟩
    refine Set.mem_iInter.2 ?_
    intro j
    simpa [J, fJ] using hxPoly j.1 j.2
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hproperSumFin :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := fFin) (hproper := hproperFin) (hdom := hdomFin)
  have hsumFinToJ :
      (fun x => ∑ i : Fin k, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin k => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin k, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  have hproperPoly :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    simpa [hsumFinToFilter] using hproperSumFin
  refine ⟨hproperPoly, ?_⟩
  have hdomPoly :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x)) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ)))
      (f := fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x)).1 hproperPoly.2.1
  rcases hdomPoly with ⟨x0, hx0⟩
  exact ⟨x0, hx0⟩

/-- Helper for Theorem 20.0.4: the mixed qualification yields a single witness that
lies in the polyhedral filtered-block effective domain and in the relative interior
of the nonpolyhedral filtered-block effective domain. -/
lemma helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) ∧
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x))) := by
  classical
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0E, hxPoly, hxNonpoly⟩
  let Jpoly : Type := {i : Fin m // i ∈ Ipoly}
  let fPolyJ : Jpoly → (Fin n → ℝ) → EReal := fun j => f j.1
  let kPoly : ℕ := Fintype.card Jpoly
  let ePoly : Jpoly ≃ Fin kPoly := Fintype.equivFin Jpoly
  let fPolyFin : Fin kPoly → (Fin n → ℝ) → EReal := fun i => fPolyJ (ePoly.symm i)
  have hnotbotPolyJ :
      ∀ j : Jpoly, ∀ x : Fin n → ℝ, fPolyJ j x ≠ (⊥ : EReal) := by
    intro j x
    exact (hproper j.1).2.2 x (by simp)
  have hnotbotPolyFin :
      ∀ i : Fin kPoly, ∀ x : Fin n → ℝ, fPolyFin i x ≠ (⊥ : EReal) := by
    intro i x
    simpa [fPolyFin] using hnotbotPolyJ (ePoly.symm i) x
  have hx0PolyInter :
      ((x0E : Fin n → ℝ) ∈
        ⋂ j : Jpoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyJ j)) := by
    refine Set.mem_iInter.2 ?_
    intro j
    have hxj :
        x0E ∈ ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j.1)) :=
      hxPoly j.1 j.2
    simpa [fPolyJ, Set.mem_preimage] using hxj
  have hdomEqPoly :
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i : Fin kPoly, fPolyFin i x) =
        ⋂ i : Fin kPoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyFin i) :=
    effectiveDomain_sum_eq_iInter_univ (f := fPolyFin) hnotbotPolyFin
  have hx0PolyInterFin :
      ((x0E : Fin n → ℝ) ∈
        ⋂ i : Fin kPoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyFin i)) := by
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0PolyInter) (ePoly.symm i)
  have hx0PolyDomFin :
      (x0E : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin kPoly, fPolyFin i x) := by
    exact hdomEqPoly.symm ▸ hx0PolyInterFin
  have hsumPolyFinToJ :
      (fun x => ∑ i : Fin kPoly, fPolyFin i x) =
        (fun x => ∑ j : Jpoly, fPolyJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv ePoly
        (fun j : Jpoly => fPolyJ j x)
        (fun i : Fin kPoly => fPolyJ (ePoly.symm i) x)
        (by intro j; simp)
    simpa [fPolyFin] using hsumEq.symm
  have hsumPolyJToFilter :
      (fun x => ∑ j : Jpoly, fPolyJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    funext x
    simpa [Jpoly, fPolyJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := fun i : Fin m => f i x))
  have hx0PolyDom :
      (x0E : Fin n → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    simpa [hsumPolyFinToJ, hsumPolyJToFilter] using hx0PolyDomFin
  let Jnonpoly : Type := {i : Fin m // i ∉ Ipoly}
  let fNonpolyJ : Jnonpoly → (Fin n → ℝ) → EReal := fun j => f j.1
  let kNonpoly : ℕ := Fintype.card Jnonpoly
  let eNonpoly : Jnonpoly ≃ Fin kNonpoly := Fintype.equivFin Jnonpoly
  let fNonpolyFin : Fin kNonpoly → (Fin n → ℝ) → EReal :=
    fun i => fNonpolyJ (eNonpoly.symm i)
  have htoLp :
      ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm :
        (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) =
      (fun a : Fin n → ℝ => WithLp.toLp 2 a) := rfl
  have hproperNonpolyFin :
      ∀ i : Fin kNonpoly,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i) := by
    intro i
    simpa [fNonpolyFin] using hproper (eNonpoly.symm i).1
  have hx0NonpolyInter :
      x0E ∈
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) := by
    refine Set.mem_iInter.2 ?_
    intro i
    have hxi :
        x0E ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f (eNonpoly.symm i).1)) :=
      hxNonpoly (eNonpoly.symm i).1 (eNonpoly.symm i).2
    simpa [fNonpolyFin, fNonpolyJ] using hxi
  have hx0NonpolyInterImage :
      x0E ∈
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) := by
    refine Set.mem_iInter.2 ?_
    intro i
    have hxiPre :
        x0E ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) :=
      (Set.mem_iInter.mp hx0NonpolyInter) i
    have hseti :
        ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) =
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
      · intro hx
        refine ⟨(x : Fin n → ℝ), hx, ?_⟩
        simp
    simpa [hseti] using hxiPre
  have hriNonpolyImage :
      Set.Nonempty
        (⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)))) :=
    ⟨x0E, hx0NonpolyInterImage⟩
  have hriEqNonpolyImage :
      euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x))) =
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) := by
    simpa [htoLp] using
      (ri_effectiveDomain_sum_eq_iInter (f := fNonpolyFin) hproperNonpolyFin) hriNonpolyImage
  have hx0NonpolyRiImageFin :
      x0E ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x))) := by
    exact hriEqNonpolyImage.symm ▸ hx0NonpolyInterImage
  have hsumNonpolyFinToJ :
      (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x) =
        (fun x => ∑ j : Jnonpoly, fNonpolyJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eNonpoly
        (fun j : Jnonpoly => fNonpolyJ j x)
        (fun i : Fin kNonpoly => fNonpolyJ (eNonpoly.symm i) x)
        (by intro j; simp)
    simpa [fNonpolyFin] using hsumEq.symm
  have hsumNonpolyJToFilter :
      (fun x => ∑ j : Jnonpoly, fNonpolyJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [Jnonpoly, fNonpolyJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hx0NonpolyRiImage :
      x0E ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x))) := by
    simpa [hsumNonpolyFinToJ, hsumNonpolyJToFilter] using hx0NonpolyRiImageFin
  refine ⟨(x0E : Fin n → ℝ), hx0PolyDom, ?_⟩
  simpa using hx0NonpolyRiImage

/-- Helper for Theorem 20.0.4: reduced mixed bridge after splitting into poly/nonpoly
filter blocks. -/
lemma helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered_of_Ipoly_empty
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))))
    (hIpolyEmpty : Ipoly = ∅) :
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
      convexFunctionClosure
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  have hleftFilter :
      Finset.univ.filter (fun i : Fin m => i ∈ Ipoly) = ∅ := by
    ext i
    simp [hIpolyEmpty]
  have hnonpoly :
      (fun x =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    simpa using
      helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
  calc
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
      funext x
      simp [hleftFilter]
    _ =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) :=
      hnonpoly
    _ =
        convexFunctionClosure
          (fun x =>
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
      simp [hleftFilter]

/-- Helper for Theorem 20.0.4: reduced mixed bridge after splitting into poly/nonpoly
filter blocks. -/
lemma helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
      convexFunctionClosure
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  classical
  by_cases hIpolyEmpty : Ipoly = ∅
  · exact
      helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered_of_Ipoly_empty
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri) hIpolyEmpty
  ·
    let p : (Fin n → ℝ) → EReal :=
      fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x
    let q : (Fin n → ℝ) → EReal :=
      fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x
    have hqClosure :
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
          convexFunctionClosure q := by
      simpa [q] using
        helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hpPack :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p ∧
          ∃ x0 : Fin n → ℝ,
            x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p := by
      simpa [p] using
        helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hcore :
        (fun x => p x + convexFunctionClosure q x) =
          convexFunctionClosure (fun x => p x + q x) := by
      rcases hpPack with ⟨_hproperP, _hdomP⟩
      have hdomRiWitness :
          ∃ x0 : Fin n → ℝ,
            x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
            (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
              euclideanRelativeInterior n
                ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
        simpa [p, q] using
          helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
            (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
      have _hproperQ :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
        simpa [q] using
          helperForTheorem_20_0_4_nonpoly_filter_block_proper
            (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
      rcases hdomRiWitness with ⟨_x0, _hx0DomP, _hx0RiQ⟩
      sorry
    have hleft :
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
          (fun x => p x + convexFunctionClosure q x) := by
      funext x
      have hqAt :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
            convexFunctionClosure q x := by
        simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g x) hqClosure
      simp [p, hqAt]
    calc
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
          (fun x => p x + convexFunctionClosure q x) := hleft
      _ = convexFunctionClosure (fun x => p x + q x) := hcore
      _ =
          convexFunctionClosure
            (fun x =>
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
        simp [p, q]

lemma helperForTheorem_20_0_4_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_mixed
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
      convexFunctionClosure (fun x => ∑ i, f i x) := by
  classical
  rcases
    helperForTheorem_20_0_4_splitSums_poly_nonpoly_blocks
      (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper)
      with ⟨hsplitClosure, hsplitRaw⟩
  calc
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) :=
      hsplitClosure
    _ =
        convexFunctionClosure
          (fun x =>
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) :=
      helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered
        (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)
    _ = convexFunctionClosure (fun x => ∑ i, f i x) := by
      simpa [hsplitRaw.symm]

/-- Theorem 20.0.4: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`, let
`I_poly` be the set of indices for which `fᵢ` is polyhedral, and let
`I_gen = I_polyᶜ`. If

`(⋂_{i ∈ I_poly} dom fᵢ) ∩ (⋂_{i ∈ I_gen} ri (dom fᵢ)) ≠ ∅`,

then

`(f₁ + ⋯ + fₘ)^* = cl (f₁^* □ ⋯ □ fₘ^*)`.

Here `dom fᵢ` is `effectiveDomain univ (f i)`, `ri` is `euclideanRelativeInterior`,
`^*` is `fenchelConjugate`, `□` is `infimalConvolutionFamily`, and `cl` is
`convexFunctionClosure`. -/
theorem fenchelConjugate_sum_eq_convexFunctionClosure_infimalConvolutionFamily_of_nonempty_iInter_dom_poly_iInter_ri_nonpoly
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  have hsum :
      (fun x => ∑ i, convexFunctionClosure (f i) x) =
        convexFunctionClosure (fun x => ∑ i, f i x) :=
    helperForTheorem_20_0_4_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_mixed
      (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)
  calc
    fenchelConjugate n (fun x => ∑ i, f i x) =
        fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) := by
          symm
          simpa using
            (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := fun x => ∑ i, f i x))
    _ = fenchelConjugate n (fun x => ∑ i, convexFunctionClosure (f i) x) := by
          simpa [hsum]
    _ = convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
          simpa using
            (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
              (f := f) hproper)

/-- Theorem 20.1: Let f₁, …, fₘ be proper convex functions on ℝⁿ such that
f₁, …, f_k are polyhedral. Assume

dom f₁ ∩ ⋯ ∩ dom f_k ∩ ri (dom f_{k+1}) ∩ ⋯ ∩ ri (dom fₘ) ≠ ∅.

Also assume `0 < m`.

Then (f₁ + ⋯ + fₘ)^* = f₁^* □ ⋯ □ fₘ^*, and for each x⋆ the infimum in the
infimal-convolution formula is attained by a decomposition x⋆ = x⋆₁ + ⋯ + x⋆ₘ. -/
theorem fenchelConjugate_sum_eq_infimalConvolutionFamily_of_first_polyhedral_and_nonempty_iInter_dom_iInter_ri
    {n m k : ℕ} (hk : k ≤ m) (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // k ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))))
    (hmPos : 0 < m) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := sorry

/-- Corollary 20.1.1: Let `f₁, …, fₘ` be closed proper convex functions on `ℝⁿ` such that
`f₁, …, f_k` are polyhedral. If

`dom f₁^* ∩ ⋯ ∩ dom f_k^* ∩ ri (dom f_{k+1}^*) ∩ ⋯ ∩ ri (dom fₘ^*) ≠ ∅`,

and `0 < m`,

then `f₁ □ ⋯ □ fₘ` is closed proper convex, and for every `x` the infimum in the
definition of `f₁ □ ⋯ □ fₘ` at `x` is attained. -/
theorem infimalConvolutionFamily_closed_proper_convex_and_attained_of_first_polyhedral_of_nonempty_iInter_dom_fenchelConjugate_iInter_ri
    {n m k : ℕ} (hk : k ≤ m) (f : Fin m → (Fin n → ℝ) → EReal)
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hdomStar_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))))
          ∩
          (⋂ i : {i : Fin m // k ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))))))
    (hmPos : 0 < m) :
    ClosedConvexFunction (infimalConvolutionFamily f) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (infimalConvolutionFamily f) ∧
      ∀ x : Fin n → ℝ,
        ∃ xFamily : Fin m → Fin n → ℝ,
          (∑ i, xFamily i) = x ∧
            infimalConvolutionFamily f x = ∑ i, f i (xFamily i) := sorry

/-- Theorem 20.2: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n`, with `C₁` polyhedral.
There exists a hyperplane that separates `C₁` and `C₂` properly and does not contain `C₂`
if and only if `C₁ ∩ ri C₂ = ∅` (with `ri` formalized as `intrinsicInterior`). -/
theorem exists_hyperplaneSeparatesProperly_not_contains_right_iff_inter_intrinsicInterior_eq_empty_of_left_polyhedral
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) :
    (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ (C₂ ⊆ H)) ↔
      C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) := sorry

/-- Corollary 20.2.1: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` with `C₁`
polyhedral. Then `C₁ ∩ ri C₂` is nonempty if and only if every `x⋆` satisfying
`δ*(x⋆ | C₁) ≤ -δ*(-x⋆ | C₂)` also satisfies `δ*(x⋆ | C₁) = δ*(x⋆ | C₂)`
(formalized with `ri = intrinsicInterior` and `δ* = deltaStar`). -/
theorem nonempty_inter_intrinsicInterior_iff_forall_deltaStar_le_neg_deltaStar_neg_imp_eq_of_left_polyhedral
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) :
    Set.Nonempty (C₁ ∩ intrinsicInterior ℝ C₂) ↔
      ∀ xStar : Fin n → ℝ,
        deltaStar C₁ xStar ≤ -deltaStar C₂ (-xStar) →
          deltaStar C₁ xStar = deltaStar C₂ xStar := sorry

/-- Theorem 20.3: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n`, with `C₁` polyhedral
and `C₂` closed. If every recession direction `z` of `C₁` such that `-z` is a recession
direction of `C₂` is also a recession direction of `C₂` (so `C₂` is linear in that
direction), then `C₁ + C₂` is closed. -/
theorem isClosed_add_of_nonempty_convex_left_polyhedral_right_closed_of_opposite_recession_imp_right_recession
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) (hC₂closed : IsClosed C₂)
    (hlinear :
      ∀ z : Fin n → ℝ,
        z ∈ Set.recessionCone C₁ → -z ∈ Set.recessionCone C₂ → z ∈ Set.recessionCone C₂) :
    IsClosed (C₁ + C₂) := sorry

/-- Corollary 20.3.1: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n` such that `C₁` is
polyhedral, `C₂` is closed, and `C₁ ∩ C₂ = ∅`. Suppose `C₁` and `C₂` have no common recession
directions except those in which `C₂` is linear (formalized as: if `z` is a recession direction of
both sets, then `-z` is also a recession direction of `C₂`). Then there exists a hyperplane
separating `C₁` and `C₂` strongly. -/
theorem exists_hyperplaneSeparatesStrongly_of_nonempty_convex_left_polyhedral_right_closed_of_inter_eq_empty_of_common_recession_imp_right_linear
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁) (hC₂closed : IsClosed C₂)
    (hdisj : C₁ ∩ C₂ = (∅ : Set (Fin n → ℝ)))
    (hcommon :
      ∀ z : Fin n → ℝ,
        z ∈ Set.recessionCone C₁ → z ∈ Set.recessionCone C₂ → -z ∈ Set.recessionCone C₂) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := sorry

/-- Theorem 20.4: Let `C` be a nonempty closed bounded convex set, and let `D` be a convex
set with `C ⊆ interior D`. Then there exists a polyhedral convex set `P` such that
`P ⊆ interior D` and `C ⊆ interior P`. -/
theorem exists_polyhedralConvexSet_between_closed_bounded_convex_and_interior_convex_superset
    {n : ℕ} (C D : Set (Fin n → ℝ))
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hCsubset : C ⊆ interior D) :
    ∃ P : Set (Fin n → ℝ),
      IsPolyhedralConvexSet n P ∧ P ⊆ interior D ∧ C ⊆ interior P := sorry

/-- Theorem 20.5: Every polyhedral convex set is locally simplicial. In particular,
every polytope is locally simplicial. -/
theorem polyhedral_and_polytope_are_locallySimplicial
    {n : ℕ} :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C → Set.LocallySimplicial n C) ∧
      (∀ P : Set (Fin n → ℝ), IsPolytope n P → Set.LocallySimplicial n P) := sorry


end Section20
end Chap04
