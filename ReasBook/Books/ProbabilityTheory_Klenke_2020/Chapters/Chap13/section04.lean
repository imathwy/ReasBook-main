import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_4_1 (from Items/Chap13) -/
open MeasureTheory Set

open scoped ENNReal

universe u

namespace MeasureTheory

section

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/- Layer triage for Exercise 13.4.1.
- `source-facing`: a tightness criterion for families of probability measures on
  `ProbabilityMeasure E`, phrased using small escape-mass events in the base space `E`.
- `core/canonical`: `IsTightMeasureSet` on measures over `ProbabilityMeasure E`.
- `bridge/view`: the chapter owner bridge
  `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt`, applied on the
  ambient space `ProbabilityMeasure E`, together with the canonical Prokhorov compactness API for
  compact families of probability measures on `E`.
-/

-- Proof sketch: first use the owner bridge
-- `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt` on the ambient space
-- `ProbabilityMeasure E` to reduce meta-tightness to compact control by subsets of
-- `ProbabilityMeasure E`. For the forward implication, apply this to a compact family of
-- probability measures on `E`, then use Prokhorov tightness on `E` to obtain one compact
-- `K ⊆ E` controlling the escape mass of every measure in the compact family. For the reverse
-- implication, choose compact sets in `E` for a summable sequence of tolerances, replace them by
-- finite unions to get a monotone compact sequence, and apply the Prokhorov compactness theorem
-- to the set of probability measures whose masses outside these compacts are uniformly small.
/-- Exercise 13.4.1: a family of probability measures on `ProbabilityMeasure E` is tight if and
only if, for every `ε > 0`, there is a compact set `K ⊆ E` such that every meta-measure in the
family gives mass `< ε` to the set of probability measures assigning mass `> ε` to `Kᶜ`. -/
theorem tight_probabilityMeasureFamily_iff_forall_exists_isCompact_small_escape
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E))) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' 𝒦) ↔
      ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
        ∀ μbar ∈ 𝒦,
          μbar {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε := sorry

end

end MeasureTheory

/-! ### Exercise_13_4_2 (from Items/Chap13) -/
open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {E : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace E]

namespace IsExchangeable

variable {X : ℕ → Ω → E} {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private theorem aemeasurable_swap (hX : IsExchangeable X μ) :
    AEMeasurable (Function.swap X) μ := by
  refine aemeasurable_pi_lambda _ fun i ↦ ?_
  simpa [Function.swap] using (hX.identDistrib 0 i).aemeasurable_snd

-- Proof sketch: apply `isExchangeable_iff_identDistrib_of_pairwise_distinct` to obtain equality in
-- law of all finite injective coordinate restrictions, then use
-- `ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib`, whose owner-level
-- finite-dimensional-marginal characterization of process laws is available under
-- `[IsFiniteMeasure μ]`.
/-- An exchangeable sequence on a finite-measure space has the same law as each strictly
increasing subsequence. -/
theorem identDistrib_subsequence (hX : IsExchangeable X μ) (n : ℕ → ℕ) (hn : StrictMono n) :
    IdentDistrib (Function.swap X) (Function.swap (X ∘ n)) μ μ := by
  let hXn : IsExchangeable (X ∘ n) μ := hX.comp_embedding ⟨n, hn.injective⟩
  rw [identDistrib_iff_forall_finset_identDistrib hX.aemeasurable_swap hXn.aemeasurable_swap]
  intro s
  let e := s.orderIsoOfFin rfl
  let u : Fin s.card ↪ ℕ := (s.orderEmbOfFin rfl).toEmbedding
  let v : Fin s.card ↪ ℕ := ⟨fun i ↦ n (u i), hn.injective.comp u.injective⟩
  have h_tuple :
      IdentDistrib
        (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω)
        (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) μ μ :=
    (isExchangeable_iff_identDistrib_of_pairwise_distinct X μ).mp hX _ u v
  let es : (Fin s.card → E) ≃ᵐ (s → E) := MeasurableEquiv.piCongrLeft (fun _ : s ↦ E) e
  have h_restrict := h_tuple.comp es.measurable
  have h_left :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω) =
        fun ω ↦ s.restrict (Function.swap X ω) := by
    funext ω
    ext j
    let xu : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (u i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xu (e.symm j)
    have hindex : u (e.symm j) = (j : ℕ) := by
      change (s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j) = (j : ℕ)
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xu, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Finset.restrict, hindex] using h
  have h_right :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) =
        fun ω ↦ s.restrict (Function.swap (X ∘ n) ω) := by
    funext ω
    ext j
    let xv : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (v i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xv (e.symm j)
    have hindex : v (e.symm j) = n j := by
      change n ((s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j)) = n j
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xv, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Function.comp, Finset.restrict,
      hindex] using h
  simpa [h_left, h_right] using h_restrict

end IsExchangeable

-- Proof sketch: for the easy direction, every strictly increasing subsequence restricts on each
-- finite coordinate set to an injective tuple, so equality of sequence laws follows from
-- `IsExchangeable.identDistrib_subsequence`. For the converse, apply the subsequence hypothesis to
-- subsequences encoding any prescribed finite injective tuple of indices and recover the
-- finite-dimensional injective-tuple criterion for exchangeability; the process-law step again uses
-- `ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib`, so the canonical statement
-- carries the ambient `[IsFiniteMeasure μ]` hypothesis.
/-- Exercise 13.4.2: an `E`-valued sequence is exchangeable if and only if every strictly
increasing subsequence has the same law as the whole sequence-valued random variable on a
finite-measure space. This is the zero-based Lean version of the textbook statement
`(X₁, X₂, …) =ᵈ (X_{n₁}, X_{n₂}, …)` for every `1 ≤ n₁ < n₂ < ⋯`. -/
theorem isExchangeable_iff_identDistrib_subsequence {X : ℕ → Ω → E} {μ : Measure Ω}
    [IsFiniteMeasure μ] :
    IsExchangeable X μ ↔
      ∀ n : ℕ → ℕ, StrictMono n →
        IdentDistrib (Function.swap X) (Function.swap (X ∘ n)) μ μ := by
  refine ⟨fun hX n hn ↦ hX.identDistrib_subsequence n hn, ?_⟩
  sorry

/-! ### Definition_13_4 (from Items/Chap13) -/
universe u

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction CompactlySupported

variable {E : Type u}

section RadonOwners

variable [TopologicalSpace E] [MeasurableSpace E]

/- Definition 13.4 (1): `𝓜(E)` is the set of measures satisfying the canonical owner predicate
`IsRadonMeasure`. -/
#check ({ μ : Measure E | IsRadonMeasure μ } : Set (Measure E))

/- The corresponding subtype `{ μ : Measure E // IsRadonMeasure μ }` is used later only as a
bridge/view carrier for topological constructions; it is not a second owner definition. -/
#check ({ μ : Measure E // IsRadonMeasure μ } : Type u)

end RadonOwners

section MeasureOwners

variable [MeasurableSpace E]

/- Definition 13.4 (2): the textbook space `𝓜_f(E)` of finite measures is the canonical owner
type `FiniteMeasure E`. -/
#check (FiniteMeasure E)

/- Definition 13.4 (3): the textbook space `𝓜_1(E)` of probability measures is the canonical
owner type `ProbabilityMeasure E`. -/
#check (ProbabilityMeasure E)

/- Definition 13.4 (4): for a finite measure `μ`, the textbook subprobability condition is the
canonical inequality `μ.mass ≤ 1`, expressed using the owner map `FiniteMeasure.mass`. -/
#check (FiniteMeasure.mass : FiniteMeasure E → NNReal)

end MeasureOwners

section FunctionOwners

variable [TopologicalSpace E]

/- Definition 13.4 (5): the textbook space `C(E)` is the canonical owner type `C(E, ℝ)`. -/
#check (C(E, ℝ))

/- Definition 13.4 (6): the textbook space `C_b(E)` is the canonical owner type `E →ᵇ ℝ`. -/
#check (E →ᵇ ℝ)

/- Definition 13.4 (7): the textbook space `C_c(E)` is the canonical owner type `C_c(E, ℝ)`. -/
#check (C_c(E, ℝ))

/- Definition 13.4 (8): every compactly supported continuous real-valued function canonically
defines a bounded continuous real-valued function via
`CompactlySupportedContinuousMap.toBoundedContinuousFunction`. -/
#check (CompactlySupportedContinuousMap.toBoundedContinuousFunction : C_c(E, ℝ) → E →ᵇ ℝ)

end FunctionOwners

/- Definition 13.4 (9): The textbook support
`\overline{f^{-1}(\mathbb{R} \setminus \{0\})}` is the canonical topological support `tsupport f`.
-/
recall tsupport

/- The textbook sup-norm convention is represented canonically in mathlib on bounded continuous and
compactly supported continuous functions. For arbitrary `C(E)`, the supremum norm requires extra
compactness or boundedness hypotheses, so that convention is left informal at this stage. -/
