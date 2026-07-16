import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Data.PNat.Notation
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Noetherian.Basic
import StacksProject_2024.stacks_project.Chap10.Lemma_10_5_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_6_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_13
import StacksProject_2024.stacks_project.Chap10.Lemma_10_78_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

open MvPolynomial
open DirectSum

/- Domain-style sampling:
* primary domain: finite-presentation criteria for flat finite modules over weighted-graded
  polynomial rings;
* sampled owner declarations:
  `Module.FinitePresentation`,
  `weightedHomogeneousSubmodule`,
  `DirectSum.Decomposition`,
  `GradedModule.linearEquiv`;
* best owner abstraction: the conclusion is the canonical owner
  `Module.FinitePresentation (MvPolynomial σ R) M`, and the graded-module structure is
  already expressed by mathlib's external owner pair
  `[DirectSum.Decomposition ℳ]` together with
  `[SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]`;
* primitive data: the weighted polynomial ring `MvPolynomial σ R` on a finite variable type `σ`,
  the positive weight function `w : σ → ℕ+`, and the `ℤ`-graded module structure `ℳ`;
* derived API: only the finite-presentation conclusion over `MvPolynomial σ R`;
* bridge/view: the source weights are positive naturals, viewed in the chapter's `ℤ`-graded
  module interface through the canonical coercion `ℕ+ → ℤ`.

Source/core/bridge triage:
* `source-facing`: the weighted-graded local finite-presentation theorem below;
* `core/canonical`: `Module.FinitePresentation` and the weighted grading owner
  `weightedHomogeneousSubmodule`;
* `bridge/view`: the passage from `w : σ → ℕ+` to the induced `ℤ`-grading. -/

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type*} [Finite σ]
variable {M : Type v} [AddCommMonoid M] [Module R M] [Module (MvPolynomial σ R) M]
variable [IsScalarTower R (MvPolynomial σ R) M]

local notation "P" => MvPolynomial σ R

/-- Helper for Lemma 15.25.3: the `d`th homogeneous projection obtained from the direct-sum
decomposition of the graded module. -/
def gradedPieceProjection (ℳ : ℤ → Submodule R M) [DecidableEq ℤ]
    [DirectSum.Decomposition ℳ] (d : ℤ) : M →ₗ[R] ℳ d :=
  (DirectSum.component R ℤ (fun i ↦ ℳ i) d).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: each graded piece is flat over the local base ring because it is a
retract of the ambient flat module. -/
theorem graded_piece_flat_of_flat
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DecidableEq ℤ]
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Flat R M] (d : ℤ) :
    Module.Flat R (ℳ d) := by
  let i : ℳ d →ₗ[R] M := (ℳ d).subtype
  let p : M →ₗ[R] ℳ d := gradedPieceProjection (ℳ := ℳ) d
  -- The homogeneous projection is a left inverse to the inclusion of the `d`th summand.
  have hp : p.comp i = LinearMap.id := by
    ext x
    simp [gradedPieceProjection, p, i]
  exact Module.Flat.of_retract i p hp

omit [Finite σ] in
/-- Helper for Lemma 15.25.3: a nonzero monomial exponent has positive weighted degree because
all variable weights are positive. -/
theorem weighted_degree_pos_of_ne_zero_exponent
    (w : σ → ℕ+) {d : σ →₀ ℕ} (hd : d ≠ 0) :
    0 < Finsupp.weight (fun i ↦ (w i : ℤ)) d := by
  classical
  -- Pick a variable that actually appears in the monomial.
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    apply hd
    ext j
    by_contra hj
    exact h ⟨j, hj⟩
  let wNat : σ → ℕ := fun j ↦ w j
  have hnat :
      0 < Finsupp.weight wNat d := by
    -- The natural-number weight dominates each positive variable weight appearing in `d`.
    have hle : wNat i ≤ Finsupp.weight wNat d :=
      Finsupp.le_weight_of_ne_zero' (w := wNat) hi
    exact lt_of_lt_of_le (w i).pos hle
  have hcast :
      (Finsupp.weight wNat d : ℤ) = Finsupp.weight (fun j ↦ (w j : ℤ)) d := by
    simp [wNat, Finsupp.weight_apply, Finsupp.sum]
  have hnat' : (0 : ℤ) < (Finsupp.weight wNat d : ℤ) := by
    exact_mod_cast hnat
  simpa [hcast] using hnat'

omit [Finite σ] in
/-- Helper for Lemma 15.25.3: every monomial has nonnegative weighted degree because the variable
weights are positive natural numbers. -/
theorem weighted_degree_nonneg
    (w : σ → ℕ+) (d : σ →₀ ℕ) :
    0 ≤ Finsupp.weight (fun i ↦ (w i : ℤ)) d := by
  let wNat : σ → ℕ := fun i ↦ w i
  have hcast :
      (Finsupp.weight wNat d : ℤ) = Finsupp.weight (fun i ↦ (w i : ℤ)) d := by
    simp [wNat, Finsupp.weight_apply, Finsupp.sum]
  have hnat : (0 : ℤ) ≤ (Finsupp.weight wNat d : ℤ) := by
    exact_mod_cast Nat.zero_le (Finsupp.weight wNat d)
  simpa [hcast] using hnat

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: a weighted-homogeneous polynomial of weighted degree zero is
constant. -/
theorem weighted_degree_zero_eq_constant
    (w : σ → ℕ+) {p : P}
    (hp : p ∈ weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) 0) :
    p = C (coeff 0 p) := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at hp
  -- Every nonconstant coefficient vanishes because its exponent has positive weighted degree.
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hweight_ne_zero : Finsupp.weight (fun i ↦ (w i : ℤ)) d ≠ 0 := by
      have hpos := weighted_degree_pos_of_ne_zero_exponent (w := w) hd
      exact ne_of_gt hpos
    have hcoeff : coeff d p = 0 :=
      MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hp d hweight_ne_zero
    rw [hcoeff, coeff_C, if_neg (by simpa [eq_comm] using hd)]

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the weighted degree-zero piece is exactly the line of constant
polynomials. -/
theorem weighted_degree_zero_part_eq_span_one
    (w : σ → ℕ+) :
    weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) 0 = R ∙ (1 : P) := by
  ext p
  constructor
  · intro hp
    -- Degree zero forces the polynomial to be the scalar multiple given by its constant term.
    rw [Submodule.mem_span_singleton]
    refine ⟨coeff 0 p, ?_⟩
    simpa [Algebra.smul_def] using
      (weighted_degree_zero_eq_constant (R := R) (σ := σ) (w := w) hp).symm
  · intro hp
    -- Constant polynomials are always weighted homogeneous of degree zero.
    rw [Submodule.mem_span_singleton] at hp
    rcases hp with ⟨r, rfl⟩
    rw [mem_weightedHomogeneousSubmodule]
    simpa [Algebra.smul_def] using
      (MvPolynomial.isWeightedHomogeneous_C (R := R) (w := fun i ↦ (w i : ℤ)) r)

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the weighted degree-zero piece is finite over the base ring. -/
theorem weighted_degree_zero_part_finite
    (w : σ → ℕ+) :
    Module.Finite R (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) 0) := by
  -- After identifying the degree-zero piece with the constant line, finiteness is immediate.
  rw [weighted_degree_zero_part_eq_span_one (R := R) (σ := σ) (w := w)]
  infer_instance

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the negative weighted-homogeneous pieces of the polynomial ring
vanish. -/
theorem weighted_homogeneous_piece_eq_bot_of_neg
    (w : σ → ℕ+) {e : ℤ} (he : e < 0) :
    weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) e = ⊥ := by
  ext p
  constructor
  · intro hp
    rw [Submodule.mem_bot]
    rw [mem_weightedHomogeneousSubmodule] at hp
    -- Every coefficient sits in a nonnegative weighted degree, so degree `e < 0` forces
    -- all coefficients to vanish.
    ext d
    have hweight_nonneg :
        0 ≤ Finsupp.weight (fun i ↦ (w i : ℤ)) d :=
      weighted_degree_nonneg (w := w) d
    have hweight_ne :
        Finsupp.weight (fun i ↦ (w i : ℤ)) d ≠ e := by
      intro hde
      linarith [hweight_nonneg, he, hde]
    exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hp d hweight_ne
  · intro hp
    rw [Submodule.mem_bot] at hp
    subst p
    simp

omit [IsLocalRing R] in
/-- Helper for Lemma 15.25.3: for a fixed natural weighted degree, only finitely many monomial
exponent vectors can occur. -/
theorem finite_exponents_of_fixed_nat_weight
    (w : σ → ℕ+) (e : ℕ) :
    {d : σ →₀ ℕ | Finsupp.weight (fun i ↦ (w i : ℕ)) d = e}.Finite := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let encode :
      {d : σ →₀ ℕ // Finsupp.weight (fun i ↦ (w i : ℕ)) d = e} → σ → Fin (e + 1) :=
    fun d i =>
      ⟨d.1 i, by
        -- Each coordinate is bounded by the total weighted degree because every weight is positive.
        by_cases hi : d.1 i = 0
        · simpa [hi]
        · have hi_support : i ∈ d.1.support := Finsupp.mem_support_iff.mpr hi
          have hterm :
              d.1 i * (w i : ℕ) ≤ Finsupp.weight (fun j ↦ (w j : ℕ)) d.1 := by
            -- Compare the `i`th term in the weight sum to the whole nonnegative sum.
            rw [Finsupp.weight_apply, Finsupp.sum]
            exact Finset.single_le_sum (f := fun j ↦ d.1 j * (w j : ℕ))
              (fun _ _ ↦ Nat.zero_le _)
              hi_support
          have hwi : 1 ≤ (w i : ℕ) := Nat.succ_le_of_lt (w i).pos
          have hbound : d.1 i ≤ e := by
            calc
              d.1 i = d.1 i * 1 := by simp
              _ ≤ d.1 i * (w i : ℕ) := Nat.mul_le_mul_left _ hwi
              _ ≤ e := by simpa [d.2] using hterm
          exact Nat.lt_succ_of_le hbound⟩
  have hencode : Function.Injective encode := by
    intro d₁ d₂ h
    apply Subtype.ext
    ext i
    exact congrArg (fun f ↦ (f i).val) h
  letI : Finite {d : σ →₀ ℕ // Finsupp.weight (fun i ↦ (w i : ℕ)) d = e} :=
    Finite.of_injective encode hencode
  simpa [Set.image_univ] using
    (Set.toFinite (Set.univ : Set {d : σ →₀ ℕ // Finsupp.weight (fun i ↦ (w i : ℕ)) d = e})).image
      (fun d ↦ d.1)

omit [IsLocalRing R] in
/-- Helper for Lemma 15.25.3: for a fixed nonnegative weighted degree, only finitely many
monomial exponent vectors can occur. -/
theorem finite_exponents_of_fixed_weight
    (w : σ → ℕ+) {e : ℤ} (he : 0 ≤ e) :
    {d : σ →₀ ℕ | Finsupp.weight (fun i ↦ (w i : ℤ)) d = e}.Finite := by
  classical
  let eNat : ℕ := Int.toNat e
  have heNat : ((eNat : ℕ) : ℤ) = e := by
    simpa [eNat] using (Int.toNat_of_nonneg he : ((Int.toNat e : ℕ) : ℤ) = e)
  have hcast :
      ∀ d : σ →₀ ℕ,
        ((Finsupp.weight (fun i ↦ (w i : ℕ)) d : ℕ) : ℤ) =
          Finsupp.weight (fun i ↦ (w i : ℤ)) d := by
    intro d
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hset :
      {d : σ →₀ ℕ | Finsupp.weight (fun i ↦ (w i : ℤ)) d = e} =
        {d : σ →₀ ℕ | Finsupp.weight (fun i ↦ (w i : ℕ)) d = eNat} := by
    ext d
    constructor
    · intro hd
      have hEqInt :
          ((Finsupp.weight (fun i ↦ (w i : ℕ)) d : ℕ) : ℤ) = (eNat : ℤ) := by
        rw [hcast d, hd, heNat]
      exact Int.ofNat_inj.mp hEqInt
    · intro hd
      calc
        Finsupp.weight (fun i ↦ (w i : ℤ)) d =
            ((Finsupp.weight (fun i ↦ (w i : ℕ)) d : ℕ) : ℤ) := by
              symm
              exact hcast d
        _ = (eNat : ℤ) := by simpa [hd]
        _ = e := heNat
  -- Transport the finite natural-degree exponent set across the coercion equality.
  simpa [hset] using finite_exponents_of_fixed_nat_weight (w := w) eNat

omit [IsLocalRing R] in
/-- Helper for Lemma 15.25.3: each weighted-homogeneous piece of the polynomial ring is a finite
`R`-module. -/
theorem weighted_homogeneous_piece_finite
    (w : σ → ℕ+) (e : ℤ) :
    Module.Finite R (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) e) := by
  classical
  by_cases he : e < 0
  · -- Negative weighted pieces vanish, so finiteness is immediate.
    rw [weighted_homogeneous_piece_eq_bot_of_neg (R := R) (σ := σ) (w := w) he]
    infer_instance
  · have hnonneg : 0 ≤ e := le_of_not_gt he
    let s : Set (σ →₀ ℕ) := {d | Finsupp.weight (fun i ↦ (w i : ℤ)) d = e}
    have hs_finite : s.Finite := finite_exponents_of_fixed_weight (σ := σ) (w := w) hnonneg
    letI : Finite s := hs_finite
    -- Rewrite the weighted piece as the supported-submodule indexed by the finite weight set.
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    -- Transport the standard finite-generation instance for finitely supported functions.
    let φ : (s →₀ R) →ₗ[R] Finsupp.supported R R s :=
      (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm
    have hφsurj : Function.Surjective φ := by
      simpa [φ] using (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm.surjective
    exact Module.Finite.of_surjective φ hφsurj

omit [IsLocalRing R] in
/-- Helper for Lemma 15.25.3: each weighted-homogeneous piece of the polynomial ring is a free
`R`-module. -/
theorem weighted_homogeneous_piece_free
    (w : σ → ℕ+) (e : ℤ) :
    Module.Free R (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ)) e) := by
  classical
  by_cases he : e < 0
  · -- Proof comment: a negative weighted piece is zero, hence free for the trivial reason that
    -- subsingleton modules are free.
    rw [weighted_homogeneous_piece_eq_bot_of_neg (R := R) (σ := σ) (w := w) he]
    exact Module.Free.of_subsingleton (R := R) (N := (⊥ : Submodule R P))
  · have hnonneg : 0 ≤ e := le_of_not_gt he
    let s : Set (σ →₀ ℕ) := {d | Finsupp.weight (fun i ↦ (w i : ℤ)) d = e}
    have hs_finite : s.Finite := finite_exponents_of_fixed_weight (σ := σ) (w := w) hnonneg
    letI : Finite s := hs_finite
    -- Proof comment: identify the weighted piece with finitely supported functions on the finite
    -- exponent set, and transfer freeness across that linear equivalence.
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Free.of_equiv
      (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: if finitely many elements `m i` span `M`, then the canonical map
from the finite free module with basis `Fin n` onto `M` is surjective. -/
theorem finite_cover_surjective_of_span_top
    {n : ℕ} (m : Fin n → M)
    (cover : (Fin n → P) →ₗ[P] M)
    (hcover : ∀ c, cover c = ∑ i, c i • m i)
    (hspan : Submodule.span P (Set.range m) = ⊤) :
    Function.Surjective cover := by
  intro x
  have hspan_le_range : Submodule.span P (Set.range m) ≤ LinearMap.range cover := by
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    refine LinearMap.mem_range.2 ?_
    refine ⟨Pi.single i (1 : P), ?_⟩
    -- Proof comment: the `i`th basis vector of the free source maps to the chosen generator.
    rw [hcover]
    simp
  have hx_span : x ∈ Submodule.span P (Set.range m) := by
    -- Proof comment: the hypothesis says these chosen generators span the whole module.
    rw [hspan]
    trivial
  exact LinearMap.mem_range.1 (hspan_le_range hx_span)

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: a finite spanning set can be refined to finitely many homogeneous
components by decomposing each generator into its direct-sum support. -/
theorem finite_homogeneous_refinement_of_span_top
    (w : σ → ℕ+)
    (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    (s : Finset M)
    (hs : Submodule.span P (s : Set M) = ⊤) :
    ∃ t : Finset M,
      (∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) ∧
        Submodule.span P (t : Set M) = ⊤ := by
  classical
  let pieces : M → Finset M := fun x ↦
    ((DirectSum.decompose ℳ x).support.image fun i ↦ ((DirectSum.decompose ℳ x i : ℳ i) : M))
  let t : Finset M := s.biUnion pieces
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    -- Every element of `t` is one homogeneous summand of some original generator.
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, (DirectSum.decompose ℳ y i).2⟩
  · apply top_le_iff.mp
    rw [← hs]
    refine Submodule.span_le.2 ?_
    intro x hx
    -- Reassemble each original generator from the homogeneous components now placed in `t`.
    rw [← DirectSum.sum_support_decompose ℳ x]
    exact Submodule.sum_mem _ fun i hi ↦ by
      apply Submodule.subset_span
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: a finite graded module admits finitely many homogeneous generators
indexed by `Fin n`, together with their degrees. -/
theorem exists_finite_homogeneous_cover_data
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Finite P M] :
    ∃ (n : ℕ) (deg : Fin n → ℤ) (m : Fin n → M),
      (∀ i, m i ∈ ℳ (deg i)) ∧
        Submodule.span P (Set.range m) = ⊤ := by
  classical
  have hfg_top : (⊤ : Submodule P M).FG :=
    (Module.Finite.iff_fg (R := P) (M := M)).mp inferInstance
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hfg_top
  let s : Finset M := hSfinite.toFinset
  have hs : Submodule.span P (s : Set M) = ⊤ := by
    simpa [s, hSfinite.coe_toFinset] using hSspan
  obtain ⟨t, ht_hom, ht_span⟩ :=
    finite_homogeneous_refinement_of_span_top (w := w) (ℳ := ℳ) s hs
  let deg : Fin t.card → ℤ := fun i ↦
    Classical.choose (ht_hom ((Finset.equivFin t).symm i) ((Finset.equivFin t).symm i).2)
  let m : Fin t.card → M := fun i ↦ ((Finset.equivFin t).symm i : M)
  refine ⟨t.card, deg, m, ?_, ?_⟩
  · intro i
    -- The `deg` function records the homogeneous degree of each chosen generator.
    exact Classical.choose_spec
      (ht_hom ((Finset.equivFin t).symm i) ((Finset.equivFin t).symm i).2)
  · -- Reindex the homogeneous finite set by `Fin t.card`.
    have hrange : Set.range m = (t : Set M) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ((Finset.equivFin t).symm i).2
      · intro hx
        refine ⟨Finset.equivFin t ⟨x, hx⟩, ?_⟩
        simp [m]
    rw [hrange]
    exact ht_span

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: the degree-`d` source of the homogeneous cover is the product of
the weighted polynomial pieces `P_{d - deg i}`. -/
abbrev degreewise_cover_source
    (w : σ → ℕ+) {n : ℕ} (deg : Fin n → ℤ) (d : ℤ) :=
  ∀ i : Fin n, weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)

omit [IsLocalRing R] in
/-- Helper for Lemma 15.25.3: each degreewise source of the homogeneous cover is a finite free
`R`-module. -/
theorem degreewise_cover_source_finite_free
    (w : σ → ℕ+) {n : ℕ} (deg : Fin n → ℤ) (d : ℤ) :
    Module.Finite R (degreewise_cover_source (R := R) (σ := σ) w deg d) ∧
      Module.Free R (degreewise_cover_source (R := R) (σ := σ) w deg d) := by
  letI :
      ∀ i : Fin n,
        Module.Finite R
          (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) :=
    fun i ↦ weighted_homogeneous_piece_finite (R := R) (σ := σ) (w := w) (d - deg i)
  letI :
      ∀ i : Fin n,
        Module.Free R
          (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) :=
    fun i ↦ weighted_homogeneous_piece_free (R := R) (σ := σ) (w := w) (d - deg i)
  -- Proof comment: the source is a finite product indexed by `Fin n`, so the standard finite/free
  -- Pi instances complete the argument.
  exact ⟨inferInstance, inferInstance⟩

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the homogeneous projection fixes an element already lying in the
`d`th graded piece. -/
theorem gradedPieceProjection_eq_self_of_mem
    (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    {d : ℤ} {x : M} (hx : x ∈ ℳ d) :
    ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d x : ℳ d) : M) = x := by
  -- Proof comment: the `d`th direct-sum component of a homogeneous element is the element itself.
  simpa [gradedPieceProjection] using
    DirectSum.decompose_of_mem_same ℳ hx

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the homogeneous projection kills an element lying in a different
graded piece. -/
theorem gradedPieceProjection_eq_zero_of_mem_ne
    (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    {d e : ℤ} {x : M} (hx : x ∈ ℳ e) (hde : d ≠ e) :
    gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d x = 0 := by
  -- Proof comment: distinct direct-sum components are orthogonal under the decomposition map.
  simpa [gradedPieceProjection] using DirectSum.decompose_of_mem_ne ℳ hx hde.symm

omit [IsLocalRing R] [Finite σ] [IsScalarTower R P M] in
/-- Helper for Lemma 15.25.3: projecting a homogeneous scalar multiple to degree `d` keeps the
term exactly in the matching degree and kills it in every other degree. -/
theorem gradedPieceProjection_smul_homogeneous
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {e g d : ℤ}
    (p : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)
    {x : M} (hx : x ∈ ℳ g) :
    ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d (((p : weightedHomogeneousSubmodule R
      (fun j ↦ (w j : ℤ)) e) : P) • x) : ℳ d) : M) =
      if d = e + g then ((p : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e) : P) • x
      else 0 := by
  have hsmul_mem :
      ((((p : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e) : P) : P) • x) ∈
        ℳ (e + g) := by
    -- Proof comment: the graded scalar action adds the polynomial degree `e` to the module degree
    -- `g`.
    simpa using SetLike.GradedSMul.smul_mem p.2 hx
  by_cases hdeg : d = e + g
  · -- Proof comment: in the matching degree, the projection is the identity on this homogeneous
    -- term.
    rw [if_pos hdeg]
    have hsmul_mem' :
        ((((p : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e) : P) : P) • x) ∈ ℳ d := by
      simpa [hdeg] using hsmul_mem
    exact gradedPieceProjection_eq_self_of_mem (R := R) (M := M) (ℳ := ℳ) (d := d) hsmul_mem'
  · -- Proof comment: away from the matching degree, the homogeneous projection vanishes.
    rw [if_neg hdeg]
    simpa using
      congrArg (fun y : ℳ d ↦ (y : M))
        (gradedPieceProjection_eq_zero_of_mem_ne (R := R) (M := M) (ℳ := ℳ)
          (d := d) (e := e + g) hsmul_mem hdeg)

/-- Helper for Lemma 15.25.3: projecting `p • x` to degree `d` only sees the `(d - g)` weighted
piece of `p` when `x` is homogeneous of degree `g`. -/
theorem gradedPieceProjection_polynomial_smul_homogeneous
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {g d : ℤ} (p : P) {x : M} (hx : x ∈ ℳ g) :
    ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d (p • x) : ℳ d) : M) =
      (((gradedPieceProjection
          (R := R) (M := P)
          (ℳ := fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)
          (d - g) p :
            weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - g)) : P) • x : M) := by
  classical
  let polyℳ : ℤ → Submodule R P := fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e
  let dec : ⨁ e, polyℳ e := DirectSum.decompose polyℳ p
  let s : Finset ℤ := dec.support
  -- Proof comment: decompose `p` into weighted-homogeneous summands and push the module
  -- projection through the resulting finite sum.
  rw [show p = ∑ i in s, ((dec i : polyℳ i) : P) by
    simpa [polyℳ, dec, s] using
      (DirectSum.sum_support_decompose polyℳ p).symm]
  rw [Finset.sum_smul]
  calc
    ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d
        (∑ i in s, (((dec i : polyℳ i) : P) • x)) :
          ℳ d) : M) =
        ∑ i in s, ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d
          (((dec i : polyℳ i) : P) • x) : ℳ d) : M) := by
        -- Proof comment: the homogeneous projection is `R`-linear, so it distributes over the
        -- finite sum of weighted-homogeneous summands.
        exact congrArg (fun y : ℳ d ↦ (y : M))
          ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d).map_sum fun i ↦
            (((dec i : polyℳ i) : P) • x))
    _ =
        ∑ i in s,
          (if d = i + g then
              (((dec i : polyℳ i) : P) • x)
            else 0) := by
        -- Proof comment: each homogeneous summand contributes only in its matching total degree.
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using
          gradedPieceProjection_smul_homogeneous (R := R) (σ := σ) (M := M) (w := w)
            (ℳ := ℳ) (e := i) (p := dec i)
            (d := d) (g := g) hx
    _ =
        (((dec (d - g) : polyℳ (d - g)) : P) • x : M) := by
        -- Proof comment: only the degree `(d - g)` polynomial summand survives in the sum.
        by_cases hmem : d - g ∈ s
        · rw [Finset.sum_eq_single_of_mem (i := d - g) hmem]
          · have hdeg : d = (d - g) + g := by omega
            simp [hdeg]
          · intro i hi hne
            have hdeg : d ≠ i + g := by
              intro h
              apply hne
              omega
            simp [hdeg]
        · have hzero :
            dec (d - g) = 0 := by
            exact Finsupp.not_mem_support_iff.mp hmem
          rw [Finset.sum_eq_zero]
          · simp [hzero]
          · intro i hi
            have hdeg : d ≠ i + g := by
              intro h
              apply hmem
              have hi' : i = d - g := by omega
              simpa [hi'] using hi
            simp [hdeg]
    _ =
        (((gradedPieceProjection
          (R := R) (M := P)
          (ℳ := fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)
          (d - g) p :
            weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - g)) : P) • x : M) := by
        -- Proof comment: the surviving direct-sum component is exactly the coefficient projection.
        simp [gradedPieceProjection, polyℳ, dec]

/-- Helper for Lemma 15.25.3: the coordinatewise weighted-degree projection. -/
abbrev coeffProjection_d
    (w : σ → ℕ+) [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    {n : ℕ} (deg : Fin n → ℤ) (d : ℤ) :
    (Fin n → P) →ₗ[R] degreewise_cover_source (R := R) (σ := σ) w deg d :=
  LinearMap.pi fun i ↦
    (gradedPieceProjection
        (R := R) (M := P)
        (ℳ := fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)
        (d - deg i)).comp
      (LinearMap.proj i)

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the `i`th degreewise term multiplies the chosen generator `m i` by
its matching weighted coefficient. -/
abbrev degreewise_cover_term
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M) (d : ℤ) (i : Fin n) :
    degreewise_cover_source (R := R) (σ := σ) w deg d →ₗ[R] M :=
  LinearMap.smulRight
    ((weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)).subtype.comp
      (LinearMap.proj i))
    (m i)

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: summing the degreewise coordinate maps gives the raw degree-`d`
cover into the ambient module `M`. -/
abbrev degreewise_cover_raw
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M) (d : ℤ) :
    degreewise_cover_source (R := R) (σ := σ) w deg d →ₗ[R] M :=
  ∑ i, degreewise_cover_term (R := R) (σ := σ) (M := M) w ℳ deg m d i

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the raw degreewise cover is the expected finite sum of weighted
coefficients times the chosen homogeneous generators. -/
theorem degreewise_cover_raw_apply
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M) (d : ℤ)
    (c : degreewise_cover_source (R := R) (σ := σ) w deg d) :
    degreewise_cover_raw (R := R) (σ := σ) (M := M) w ℳ deg m d c =
      ∑ i, ((c i : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) : P) • m i := by
  -- Proof comment: each summand is defined by projecting to one coordinate and then scaling `m i`.
  simp [degreewise_cover_raw, degreewise_cover_term]

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the raw degree-`d` cover lands in the `d`th graded piece of `M`. -/
theorem degreewise_cover_image_mem
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i)) (d : ℤ)
    (c : degreewise_cover_source (R := R) (σ := σ) w deg d) :
    degreewise_cover_raw (R := R) (σ := σ) (M := M) w ℳ deg m d c ∈ ℳ d := by
  -- Proof comment: each term has degree `(d - deg i) + deg i = d`, so the finite sum stays in
  -- the degree-`d` submodule.
  rw [degreewise_cover_raw_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hterm :
      (((c i : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) : P) • m i) ∈
        ℳ ((d - deg i) + deg i) := by
    simpa using SetLike.GradedSMul.smul_mem (c i).2 (hm i)
  simpa [sub_eq_add_neg, add_assoc] using hterm

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: the degreewise cover is the codomain-restricted raw cover landing in
the `d`th graded piece. -/
def degreewise_cover
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i)) (d : ℤ) :
    degreewise_cover_source (R := R) (σ := σ) w deg d →ₗ[R] ℳ d :=
  LinearMap.codRestrict (ℳ d)
    (degreewise_cover_raw (R := R) (σ := σ) (M := M) w ℳ deg m d)
    (degreewise_cover_image_mem (R := R) (σ := σ) (M := M) w ℳ deg m hm d)

omit [IsLocalRing R] [Finite σ] in
/-- Helper for Lemma 15.25.3: after forgetting the subtype, the degreewise cover agrees with the
same explicit finite sum as the raw cover. -/
theorem degreewise_cover_apply
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i)) (d : ℤ)
    (c : degreewise_cover_source (R := R) (σ := σ) w deg d) :
    ((degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d c : ℳ d) : M) =
      ∑ i, ((c i : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) : P) • m i := by
  -- Proof comment: codomain restriction does not change the underlying value in `M`.
  exact degreewise_cover_raw_apply (R := R) (σ := σ) (M := M) w ℳ deg m d c

/-- Helper for Lemma 15.25.3: the degreewise cover agrees with the degree-`d` projection of the
global cover after projecting each coefficient to weighted degree `d - deg i`. -/
theorem degreewise_cover_projection_formula
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i))
    (cover : (Fin n → P) →ₗ[P] M)
    (hcover : ∀ c, cover c = ∑ i, c i • m i)
    (d : ℤ) (c : Fin n → P) :
    ((degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d
        ((coeffProjection_d (R := R) (σ := σ) w deg d) c) : ℳ d) : M) =
      ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d
          ((cover.restrictScalars R) c) : ℳ d) : M) := by
  -- Proof comment: expand the degreewise cover on the left and the global cover on the right,
  -- then compare the two finite sums term-by-term.
  rw [degreewise_cover_apply]
  calc
    ∑ i,
        ((((coeffProjection_d (R := R) (σ := σ) w deg d c) i :
            weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) : P) • m i) =
      ∑ i, ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d (c i • m i) : ℳ d) : M) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- Proof comment: the projection of the coefficient `c i` is exactly the polynomial piece
        -- selected by the module projection formula for the homogeneous generator `m i`.
        simpa [coeffProjection_d] using
          (gradedPieceProjection_polynomial_smul_homogeneous (R := R) (σ := σ) (M := M)
            (w := w) (ℳ := ℳ) (g := deg i) (d := d) (p := c i) (hx := hm i)).symm
    _ = ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d
          (∑ i, c i • m i) : ℳ d) : M) := by
        -- Proof comment: reassemble the projected summands by linearity of
        -- `gradedPieceProjection`.
        symm
        exact congrArg (fun y : ℳ d ↦ (y : M))
          ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d).map_sum fun i ↦ c i • m i)
    _ = ((gradedPieceProjection (R := R) (M := M) (ℳ := ℳ) d
          ((cover.restrictScalars R) c) : ℳ d) : M) := by
        -- Proof comment: the chosen cover is defined by the same finite sum.
        simpa [hcover]

/-- Helper for Lemma 15.25.3: surjectivity of the global cover restricts to surjectivity in each
graded degree. -/
theorem homogeneous_cover_degree_surjective
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i))
    (cover : (Fin n → P) →ₗ[P] M)
    (hcover : ∀ c, cover c = ∑ i, c i • m i)
    (hcover_surj : Function.Surjective cover)
    (d : ℤ) :
    Function.Surjective (degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d) := by
  intro x
  obtain ⟨c, hc⟩ := hcover_surj (x : M)
  refine ⟨coeffProjection_d (R := R) (σ := σ) w deg d c, ?_⟩
  apply Subtype.ext
  -- Proof comment: choose a global preimage of `x` and project it to the degree-`d` source.
  change
    ((degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d
        ((coeffProjection_d (R := R) (σ := σ) w deg d) c) : ℳ d) : M) = x
  rw [degreewise_cover_projection_formula
    (R := R) (σ := σ) (M := M) (w := w) (ℳ := ℳ) deg m hm cover hcover d c]
  simpa [hc] using
    gradedPieceProjection_eq_self_of_mem (R := R) (M := M) (ℳ := ℳ) (d := d) x.2

/-- Helper for Lemma 15.25.3: a global kernel element projects degreewise to the corresponding
degreewise kernel piece. -/
theorem coeffProjection_mem_degreewise_kernel
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i))
    (cover : (Fin n → P) →ₗ[P] M)
    (hcover : ∀ c, cover c = ∑ i, c i • m i)
    {c : Fin n → P} (hc : cover c = 0) (d : ℤ) :
    coeffProjection_d (R := R) (σ := σ) w deg d c ∈
      LinearMap.ker (degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d) := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  -- Proof comment: the projection formula identifies the degreewise cover of the projected source
  -- with the `d`th graded projection of `cover c`, which is zero.
  change
    ((degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d
        (coeffProjection_d (R := R) (σ := σ) w deg d c) : ℳ d) : M) = 0
  rw [degreewise_cover_projection_formula
    (R := R) (σ := σ) (M := M) (w := w) (ℳ := ℳ) deg m hm cover hcover d c]
  simpa [hc]

/-- Helper for Lemma 15.25.3: for each degree, the kernel of the degreewise cover is finite free
over the local base ring. -/
theorem kernel_degree_piece_finite_free_of_cover
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition
      (fun e ↦ weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) e)]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ))) ℳ]
    [Module.Flat R M]
    {n : ℕ} (deg : Fin n → ℤ) (m : Fin n → M)
    (hm : ∀ i, m i ∈ ℳ (deg i))
    (cover : (Fin n → P) →ₗ[P] M)
    (hcover : ∀ c, cover c = ∑ i, c i • m i)
    (hcover_surj : Function.Surjective cover)
    (d : ℤ) :
    Module.Finite R
        (LinearMap.ker
          (degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d)) ∧
      Module.Flat R
        (LinearMap.ker
          (degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d)) ∧
      Module.Free R
        (LinearMap.ker
          (degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d)) := by
  let cover_d :
      degreewise_cover_source (R := R) (σ := σ) w deg d →ₗ[R] ℳ d :=
    degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hm d
  have hcover_d_surj : Function.Surjective cover_d :=
    homogeneous_cover_degree_surjective (R := R) (σ := σ) (M := M)
      (w := w) (ℳ := ℳ) deg m hm cover hcover hcover_surj d
  have hsource_ff :=
    degreewise_cover_source_finite_free (R := R) (σ := σ) (w := w) deg d
  letI : Module.Finite R (degreewise_cover_source (R := R) (σ := σ) w deg d) := hsource_ff.1
  letI : Module.Free R (degreewise_cover_source (R := R) (σ := σ) w deg d) := hsource_ff.2
  letI : Module.Flat R (degreewise_cover_source (R := R) (σ := σ) w deg d) := inferInstance
  have hgraded_finite : Module.Finite R (ℳ d) := Module.Finite.of_surjective cover_d hcover_d_surj
  letI : Module.Finite R (ℳ d) := hgraded_finite
  letI : Module.Flat R (ℳ d) :=
    graded_piece_flat_of_flat (R := R) (σ := σ) (M := M) (w := w) (ℳ := ℳ) d
  letI : Module.FinitePresentation R (ℳ d) := Module.finitePresentation_of_finite R (ℳ d)
  let S : CategoryTheory.ShortComplex (ModuleCat R) := cover_d.shortComplexKer
  have hS : S.ShortExact := by
    simpa [S, cover_d] using LinearMap.shortExact_shortComplexKer hcover_d_surj
  have hfinite_ker : Module.Finite R (LinearMap.ker cover_d) := by
    -- Proof comment: the kernel is the left term of the canonical short exact sequence
    -- `0 → ker cover_d → source_d → ℳ d → 0`, so finite presentation of the target and
    -- finiteness of the source give finiteness of the kernel.
    simpa [S, cover_d] using
      (Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
        ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
          hS.exact))
  letI : Module.Finite R (LinearMap.ker cover_d) := hfinite_ker
  have hflat_ker : Module.Flat R (LinearMap.ker cover_d) := by
    -- Proof comment: flatness of the left term follows from the short exact sequence because both
    -- the source and the target are already flat over `R`.
    simpa [S, cover_d] using CategoryTheory.ShortComplex.ShortExact.flat_X₁ hS
  letI : Module.Flat R (LinearMap.ker cover_d) := hflat_ker
  have hfree_ker : Module.Free R (LinearMap.ker cover_d) :=
    Module.free_of_flat_of_isLocalRing (R := R) (M := LinearMap.ker cover_d)
  exact ⟨hfinite_ker, hflat_ker, hfree_ker⟩

-- Proof sketch: choose homogeneous generators of the finite graded module `M` and present it by a
-- finite direct sum of weighted shifts of `MvPolynomial σ R`. Degreewise, the kernel has
-- short exact sequences whose middle and right terms are finite free over the local ring `R`, so
-- each graded piece of the kernel is finite free over `R`. After tensoring with the residue field,
-- the kernel over `MvPolynomial σ R ⊗[R] κ` is finitely generated because that polynomial
-- ring is Noetherian; then graded Nakayama lifts finitely many homogeneous generators back to the
-- kernel over `R`, giving a finite presentation of `M` over `MvPolynomial σ R`.
/-- Lemma 15.25.3: if `R` is a local ring, `MvPolynomial σ R` on a finite variable type `σ` is
given the weighted grading with variable-weights `w : σ → ℕ+` viewed as degrees in `ℤ`, and a
`ℤ`-graded module `M` over this polynomial ring is finite over `MvPolynomial σ R` and flat over
`R`, then `M` is finitely presented as an `MvPolynomial σ R`-module. -/
theorem finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Finite P M] [Module.Flat R M] :
    Module.FinitePresentation P M := by
  classical
  -- Route correction: start with the source proof's homogeneous finite cover before touching the
  -- kernel. This isolates the remaining work to the degreewise kernel/Nakayama argument.
  obtain ⟨n, deg, m, hm, hspan⟩ :=
    exists_finite_homogeneous_cover_data (R := R) (σ := σ) (M := M) (w := w) (ℳ := ℳ)
  let cover : (Fin n → P) →ₗ[P] M :=
    { toFun := fun c ↦ ∑ i, c i • m i
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        simp [Finset.smul_sum, smul_smul] }
  have hcover_surj : Function.Surjective cover := by
    -- Proof comment: package the standard span-to-surjection argument as a reusable helper.
    refine finite_cover_surjective_of_span_top (R := R) (σ := σ) (M := M) m cover ?_ hspan
    intro c
    rfl
  -- The remaining source-faithful step is to prove the kernel of `cover` is finite by analyzing
  -- its graded pieces, proving those pieces finite free over `R`, and then applying graded
  -- Nakayama after tensoring with the residue field.
  have hdeg_mem : ∀ i, m i ∈ ℳ (deg i) := hm
  clear hm
  let cover_d :
      ∀ d : ℤ, degreewise_cover_source (R := R) (σ := σ) w deg d →ₗ[R] ℳ d :=
    fun d ↦ degreewise_cover (R := R) (σ := σ) (M := M) w ℳ deg m hdeg_mem d
  have hsource_ff :
      ∀ d : ℤ,
        Module.Finite R (degreewise_cover_source (R := R) (σ := σ) w deg d) ∧
          Module.Free R (degreewise_cover_source (R := R) (σ := σ) w deg d) := by
    intro d
    -- Proof comment: the weighted direct-sum owner is now hidden behind a dedicated degreewise
    -- finite/free source lemma.
    exact degreewise_cover_source_finite_free (R := R) (σ := σ) (w := w) deg d
  have hcover_d_frontier :
      ∀ d : ℤ,
        ∀ c : degreewise_cover_source (R := R) (σ := σ) w deg d,
          ((cover_d d c : ℳ d) : M) =
            ∑ i,
              ((c i : weightedHomogeneousSubmodule R (fun j ↦ (w j : ℤ)) (d - deg i)) : P) •
                m i := by
    intro d c
    -- Proof comment: the explicit formula for the degreewise cover is now stabilized.
    exact degreewise_cover_apply (R := R) (σ := σ) (M := M) w ℳ deg m hdeg_mem d c
  -- TODO: use the projection adapter and the degreewise surjectivity lemma to pass from this
  -- stabilized degreewise source data to the residue-field argument. The remaining blocker is the
  -- missing weighted-polynomial direct-sum decomposition owner in the theorem context, which is
  -- needed to instantiate `coeffProjection_mem_degreewise_kernel` and
  -- `kernel_degree_piece_finite_free_of_cover` here without reopening the decomposition API in the
  -- theorem body.
  sorry

end
