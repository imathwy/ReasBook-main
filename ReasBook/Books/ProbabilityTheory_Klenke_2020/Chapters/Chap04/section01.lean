import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_4_1_1 (from Items/Chap04) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable (hμ :
  ∃ a : NNReal,
    0 < a ∧ ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A ≠ 0 → (a : ENNReal) ≤ μ A)

include hμ

-- Proof sketch: use the hypothesis that every nonnull measurable set has measure bounded below by
-- a fixed positive constant to control the size of the level sets of `|f|`; this turns the
-- `ℒ^{p'}` summability condition into the stronger `ℒ^p` summability condition, as for sequence
-- spaces with counting measure.
/-- Exercise 4.1.1, canonical `Lp`-space form: if every measurable set has either zero measure or
measure at least some positive constant, then `L^{p'}(μ)` is a subspace of `L^p(μ)` for
`1 ≤ p' ≤ p ≤ ∞`. -/
theorem Lp_le_Lp_of_measure_lower_bound
    {p' p : ENNReal} (hp' : 1 ≤ p') (hp'le : p' ≤ p) :
    Lp ℝ p' μ ≤ Lp ℝ p μ := sorry

/-- Exercise 4.1.1 in textbook representative form: if every measurable set has either zero measure
or measure at least some positive constant, then `ℒ^{p'}(μ) ⊆ ℒ^p(μ)` for `1 ≤ p' ≤ p ≤ ∞`. -/
theorem memLp_of_memLp_of_measure_lower_bound
    {f : Ω → ℝ} {p' p : ENNReal}
    (hp' : 1 ≤ p') (hp'le : p' ≤ p) (hf : MemLp f p' μ) :
    MemLp f p μ := by
  let f' : Lp ℝ p' μ := hf.toLp f
  have hf' : ((f' : Ω →ₘ[μ] ℝ) ∈ Lp ℝ p μ) := Lp_le_Lp_of_measure_lower_bound hμ hp' hp'le f'.2
  exact MemLp.ae_eq hf.coeFn_toLp <| (Lp.mem_Lp_iff_memLp.1 hf')

/-! ### Lemma_4_1 (from Items/Chap04) -/
universe u

open MeasureTheory
open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the normal representation as the canonical finite sum of restricted
-- constant simple functions, then evaluate the lower integral of that finite sum by additivity and
-- `SimpleFunc.restrict_const_lintegral`.
/-- Lemma 4.1: a normal representation of a nonnegative simple function computes its lower
integral as the corresponding weighted measure sum. -/
theorem lintegral_eq_weighted_measure_sum_of_normal_representation
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal)
    {n : ℕ} (A : Fin n → Set Ω) (α : Fin n → ENNReal)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (_hA_disj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hfA : (f : Ω → ENNReal) = fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ α i) ω) :
    f.lintegral μ = ∑ i, α i * μ (A i) := by
  classical
  let g : SimpleFunc Ω ENNReal := ∑ i, (SimpleFunc.const Ω (α i)).restrict (A i)
  have hg_apply (ω : Ω) : g ω = ∑ i, ((SimpleFunc.const Ω (α i)).restrict (A i)) ω := by
    let s : Finset (Fin n) := Finset.univ
    change (s.sum fun i ↦ (SimpleFunc.const Ω (α i)).restrict (A i)) ω =
      s.sum fun i ↦ ((SimpleFunc.const Ω (α i)).restrict (A i)) ω
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert i s hi hs =>
        simp [hi, hs, SimpleFunc.coe_add, Pi.add_apply]
  have hfg : f = g := by
    ext ω
    rw [hfA]
    calc
      ∑ i, (A i).indicator (fun _ ↦ α i) ω
          = ∑ i, ((SimpleFunc.const Ω (α i)).restrict (A i)) ω := by
              refine Finset.sum_congr rfl (fun i _ ↦ ?_)
              rw [SimpleFunc.restrict_apply _ (hA_meas i)]
              rfl
      _ = g ω := by
        simpa using (hg_apply ω).symm
  rw [hfg]
  have hs :
      ∀ s : Finset (Fin n),
        (∑ i ∈ s, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ =
          ∑ i ∈ s, α i * μ (A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert i s hi hs =>
        simp [hi, hs, hA_meas i, SimpleFunc.add_lintegral, SimpleFunc.restrict_const_lintegral]
  simpa [g] using hs Finset.univ

/-- Textbook two-representation form of Lemma 4.1: two normal representations of the same
nonnegative simple function have the same weighted measure sum. -/
theorem weighted_measure_sum_eq_of_normal_representations
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal)
    {m n : ℕ} (A : Fin m → Set Ω) (B : Fin n → Set Ω)
    (α : Fin m → ENNReal) (β : Fin n → ENNReal)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hB_meas : ∀ j, MeasurableSet (B j))
    (hA_disj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hB_disj : Pairwise (fun i j ↦ Disjoint (B i) (B j)))
    (hfA : (f : Ω → ENNReal) = fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ α i) ω)
    (hfB : (f : Ω → ENNReal) = fun ω ↦ ∑ j, (B j).indicator (fun _ ↦ β j) ω) :
    ∑ i, α i * μ (A i) = ∑ j, β j * μ (B j) := by
  rw [← lintegral_eq_weighted_measure_sum_of_normal_representation μ f A α hA_meas hA_disj hfA,
    lintegral_eq_weighted_measure_sum_of_normal_representation μ f B β hB_meas hB_disj hfB]

/-! ### Exercise_4_1_2 (from Items/Chap04) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

-- Proof sketch: decompose the sigma-finite non-finite measure into countably many measurable
-- pieces of positive finite measure, then choose coefficients so that the resulting simple
-- function has finite `p`-seminorm but infinite `p'`-seminorm. The canonical `Lp` formulation is
-- a witness in the `AEEqFun`-based `L^p` space whose class does not belong to `L^{p'}`; the
-- textbook raw-function statement is the immediate representative-level corollary.
/-- Exercise 4.1.2, canonical `Lp`-space form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite but not
finite, then there exists an `L^p(μ)` class that does not belong to `L^{p'}(μ)`. -/
theorem exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω →ₘ[μ] ℝ, f ∈ Lp ℝ p μ ∧ f ∉ Lp ℝ p' μ := sorry

/-- Exercise 4.1.2 in textbook representative form: if `1 ≤ p' < p ≤ ∞` and `μ` is sigma-finite
but not finite, then there exists a real-valued function in `ℒ^p(μ)` that does not belong to
`ℒ^{p'}(μ)`. -/
theorem exists_memLp_not_memLp_of_sigmaFinite_not_isFiniteMeasure {p' p : ENNReal}
    (hp' : 1 ≤ p') (hpp : p' < p) (hμ : ¬ IsFiniteMeasure μ) :
    ∃ f : Ω → ℝ, MemLp f p μ ∧ ¬ MemLp f p' μ := by
  rcases exists_mem_Lp_not_mem_Lp_of_sigmaFinite_not_isFiniteMeasure hp' hpp hμ with
    ⟨f, hf, hf'⟩
  refine ⟨f, (Lp.mem_Lp_iff_memLp).1 hf, ?_⟩
  intro hfp'
  exact hf' <| (Lp.mem_Lp_iff_memLp).2 hfp'
