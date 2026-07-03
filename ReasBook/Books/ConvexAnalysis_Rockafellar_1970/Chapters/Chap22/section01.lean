import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_22_1 (from Chap04) -/
open scoped BigOperators RealInnerProductSpace Rockafellar
open Set

noncomputable section

section

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E]
variable {I : Type*}

local notation "solutionSet[" a ", " α "]" =>
  ((linearInequalitySolutionSet (Set.range fun i ↦ (a i, α i))) : Set E)
local notation "ownerSolutionSet[" a ", " α "]" =>
  (LinearConstraintRelation.leFeasible (X := E) a α : Set E)
set_option linter.style.longLine false in
local notation "xorFiniteAffineCoreAlternative" =>
  xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate_of_finite_affine_core

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 22.1 gives Rockafellar's finite weak-inequality alternative.
- `core/canonical`: the primary reusable owner for coefficients is the pairing layer
  `a : I → Y` under `[HasLinearPairing E Y ℝ]`, with the multiplier-side cancellation stated
  intrinsically as pointwise vanishing weighted pairing sums.
- `bridge/view`: the linear-functional form
  `a : I → E →ₗ[ℝ] ℝ`, the continuous-dual form used by Theorem 21.4, and the inner-product
  vector form are retained as thin downstream bridges.

Layer target: make the pairing owner primary, and keep functional and vector statements as minimal
downstream bridges.

Abstraction checks for this item:
- Scalar layer: the public owner theorem remains over `ℝ` because the upstream Chapter 21
  alternative (`Theorem_21_4`) is currently built on `WithBotTop ℝ`/`EReal` convex-function
  infrastructure and multiplier certificates over `ℝ`.
- Ambient structure: no inner-product assumptions appear on the main owner theorem; the required
  ambient assumptions are exactly those inherited from the reused upstream owner theorem.
- Codomain layer: public theorem surfaces are pairing/linear-functional with codomain `ℝ`;
  `EReal` remains internal to the Chapter 21 affine-function bridge.
-/

private def weakLinearInequalityAffineMap
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (i : I) :
    E →ᵃ[ℝ] ℝ :=
  (a i).toAffineMap + AffineMap.const ℝ E (-α i)

omit [FiniteDimensional ℝ E] in
private theorem weakLinearInequalityAffineMap_apply
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (i : I) (x : E) :
    weakLinearInequalityAffineMap a α i x = a i x - α i := by
  simp [weakLinearInequalityAffineMap, sub_eq_add_neg]

private def weakLinearInequalityAffineFunction
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (i : I) : E → EReal :=
  (weakLinearInequalityAffineMap a α i).toEReal

private theorem ereal_sum_coe_eq [Fintype I] (g : I → ℝ) :
    ∑ i, ((g i : ℝ) : EReal) = ((∑ i, g i : ℝ) : EReal) := by
  let φ : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  change ∑ i, φ (g i) = φ (∑ i, g i)
  exact (map_sum φ g Finset.univ).symm

omit [FiniteDimensional ℝ E] in
private theorem weakLinearInequalityAffineCore
    [Finite I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    ∃ I₀ : Set I, I₀.Finite ∧
      (∀ i ∈ I₀, ∃ b : E →ᵃ[ℝ] ℝ,
        weakLinearInequalityAffineFunction a α i = b.toEReal) ∧
        (∀ i ∉ I₀,
          Function.IsClosedProperConvex (𝕜 := ℝ) (weakLinearInequalityAffineFunction a α i)) ∧
        ∀ y : E,
          (∀ i : I,
            y ∈ Function.recessionCone
              (Function.recessionFunction (weakLinearInequalityAffineFunction a α i))) →
          ∀ i ∉ I₀,
            y ∈ Function.lineal (weakLinearInequalityAffineFunction a α i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  refine ⟨Set.univ, Set.finite_univ, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact ⟨weakLinearInequalityAffineMap a α i, rfl⟩
  · intro i hi
    simp at hi
  · intro y hrec i hi
    simp at hi

omit [FiniteDimensional ℝ E] in
private theorem exists_nonpositive_weakLinearInequalityAffineFunction_iff
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    (∃ x : E, ∀ i : I, weakLinearInequalityAffineFunction a α i x ≤ 0) ↔
      ∃ x : E, ∀ i : I, a i x ≤ α i := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i
    have hxi' : ((a i x - α i : ℝ) : EReal) ≤ 0 := by
      simpa [weakLinearInequalityAffineFunction, weakLinearInequalityAffineMap_apply] using hx i
    have hxi'' : a i x - α i ≤ 0 := by
      exact_mod_cast hxi'
    exact sub_nonpos.mp hxi''
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i
    have hxi' : a i x - α i ≤ 0 := sub_nonpos.mpr (hx i)
    have hxi'' : ((a i x - α i : ℝ) : EReal) ≤ 0 := by
      exact_mod_cast hxi'
    simpa [weakLinearInequalityAffineFunction, weakLinearInequalityAffineMap_apply] using hxi''

omit [FiniteDimensional ℝ E] in
private theorem weakLinearInequalityAffineMap_sum_eq
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (w : I → ℝ) (x : E) :
    ∑ i, w i * weakLinearInequalityAffineMap a α i x =
      (∑ i, w i • a i) x - ∑ i, w i * α i := by
  calc
    ∑ i, w i * weakLinearInequalityAffineMap a α i x
        = ∑ i, w i * (a i x - α i) := by
            simp [weakLinearInequalityAffineMap_apply]
    _ = ∑ i, (w i * a i x - w i * α i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
    _ = (∑ i, w i * a i x) - ∑ i, w i * α i := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, (w i • a i) x) - ∑ i, w i * α i := by
          simp
    _ = (∑ i, w i • a i) x - ∑ i, w i * α i := by
          simp

omit [FiniteDimensional ℝ E] in
private theorem exists_finsupp_nonnegativeMultiplierCertificateOn_univ_iff
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    let f : I → E → EReal :=
      weakLinearInequalityAffineFunction a α
    (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.IsNonnegativeMultiplierCertificateOn Set.univ f epsilon) ↔
      ∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0 := by
  constructor
  · rintro ⟨weights, epsilon, hweights⟩
    rcases hweights with ⟨hweights_nonneg, hεpos, huniform_bound⟩
    let f : I → E → EReal :=
      weakLinearInequalityAffineFunction a α
    let w : I → ℝ := fun i ↦ weights i
    let s : E →ₗ[ℝ] ℝ := ∑ i, w i • a i
    let c : ℝ := ∑ i, w i * α i
    have hbound (x : E) : epsilon ≤ s x - c := by
      have hx : (epsilon : EReal) ≤ weights.sum (fun i a' ↦ (a' : EReal) * f i x) :=
        huniform_bound x (by simp)
      rw [Finsupp.sum_fintype _ _ fun i ↦ by simp] at hx
      have hx' :
          (epsilon : EReal) ≤
            ∑ i, ((w i * weakLinearInequalityAffineMap a α i x : ℝ) : EReal) := by
        simpa [f, w, weakLinearInequalityAffineFunction, EReal.coe_mul] using hx
      rw [ereal_sum_coe_eq (fun i ↦ w i * weakLinearInequalityAffineMap a α i x)] at hx'
      have hx'' : epsilon ≤ ∑ i, w i * weakLinearInequalityAffineMap a α i x := by
        exact_mod_cast hx'
      rw [weakLinearInequalityAffineMap_sum_eq a α w x] at hx''
      simpa [s, c] using hx''
    have hconst : epsilon ≤ -c := by
      simpa [c, s] using hbound (0 : E)
    have hs : s = 0 := by
      by_contra hs
      have hs_eval : ∃ x0 : E, s x0 ≠ 0 := by
        by_contra hs_eval
        apply hs
        ext x
        by_contra hx
        exact hs_eval ⟨x, hx⟩
      rcases hs_eval with ⟨x0, hx0⟩
      let t : ℝ := (c + epsilon - 1) / s x0
      have hbad := hbound (t • x0)
      have ht : s (t • x0) - c = epsilon - 1 := by
        calc
          s (t • x0) - c = t * s x0 - c := by simp
          _ = ((c + epsilon - 1) / s x0) * s x0 - c := by simp [t]
          _ = epsilon - 1 := by
            field_simp [hx0]
            ring
      rw [ht] at hbad
      linarith
    have hc : c < 0 := by
      linarith [hεpos, hconst]
    exact ⟨w, hweights_nonneg, by simpa [s, w] using hs, hc⟩
  · rintro ⟨w, hw_nonneg, hw_functionals, hw_constants⟩
    let f : I → E → EReal :=
      weakLinearInequalityAffineFunction a α
    let weights : I →₀ ℝ := Finsupp.equivFunOnFinite.symm w
    let c : ℝ := ∑ i, w i * α i
    let epsilon : ℝ := -c / 2
    refine ⟨weights, epsilon, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa [weights] using hw_nonneg i
    · have hneg : 0 < -c := by
        simpa [c] using neg_pos.mpr hw_constants
      have htwo : (0 : ℝ) < 2 := by norm_num
      dsimp [epsilon]
      positivity
    · intro x hx
      have hsum :
          weights.sum
              (fun i a' ↦ (a' : EReal) * weakLinearInequalityAffineFunction a α i x) =
            ((-c : ℝ) : EReal) := by
        rw [Finsupp.sum_fintype _ _ fun i ↦ by simp]
        calc
          ∑ i, ((weights i : ℝ) : EReal) * weakLinearInequalityAffineFunction a α i x
              = ∑ i, ((w i * weakLinearInequalityAffineMap a α i x : ℝ) : EReal) := by
                  simp [weights, weakLinearInequalityAffineFunction, EReal.coe_mul]
          _ = ((∑ i, w i * weakLinearInequalityAffineMap a α i x : ℝ) : EReal) := by
                rw [ereal_sum_coe_eq (fun i ↦ w i * weakLinearInequalityAffineMap a α i x)]
          _ = ((((∑ i, w i • a i) x - c : ℝ)) : EReal) := by
                rw [weakLinearInequalityAffineMap_sum_eq a α w x]
          _ = ((-c : ℝ) : EReal) := by
                simp [hw_functionals, c]
      have hεle : epsilon ≤ -c := by
        dsimp [epsilon]
        linarith [hw_constants]
      have hεle' : (epsilon : EReal) ≤ ((-c : ℝ) : EReal) := by
        exact_mod_cast hεle
      calc
        (epsilon : EReal) ≤ ((-c : ℝ) : EReal) := hεle'
        _ = weights.sum
              (fun i a' ↦ (a' : EReal) * weakLinearInequalityAffineFunction a α i x) := by
              symm
              exact hsum

omit [FiniteDimensional ℝ E] in
private theorem exists_function_weakLinearInequalityFarkasCertificate_iff_exists_finsupp
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    (∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • a i = 0) ∧
          (∑ i, w i * α i) < 0) ↔
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (weights.sum (fun i c ↦ c • a i) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  constructor
  · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
    refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_, ?_⟩
    · intro i
      simpa using hw_nonneg i
    · rw [Finsupp.sum_fintype _ _ fun i ↦ by simp]
      simpa using hw_sum
    · rw [Finsupp.sum_fintype _ _ fun i ↦ by simp]
      simpa using hw_α
  · rintro ⟨weights, hw_nonneg, hw_sum, hw_α⟩
    refine ⟨Finsupp.equivFunOnFinite weights, ?_, ?_, ?_⟩
    · intro i
      simpa using hw_nonneg i
    · have hw_sum' : ∑ i, Finsupp.equivFunOnFinite weights i • a i = 0 := by
        rw [Finsupp.sum_fintype _ _ fun i ↦ by simp] at hw_sum
        simpa using hw_sum
      exact hw_sum'
    · have hw_α' : (∑ i, Finsupp.equivFunOnFinite weights i * α i) < 0 := by
        rw [Finsupp.sum_fintype _ _ fun i ↦ by simp] at hw_α
        simpa using hw_α
      exact hw_α'

-- Proof sketch: apply Theorem 21.4 to affine functions `f i x = a i x - α i`.
-- The multiplier alternative gives a uniform positive lower bound on
-- `x ↦ (∑ i, w i • a i) x - ∑ i, w i * α i`; this forces the linear part to vanish.
/-- Canonical owner form of Theorem 22.1 on indexed weak systems: the weak feasible owner
`LinearConstraintRelation.leFeasible a α` is nonempty, or there is a nonnegative multiplier family
with vanishing weighted functional sum and strictly negative weighted scalar sum. -/
theorem xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (ownerSolutionSet[a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  have hmain :
      Xor'
        (∃ x : E, ∀ i : I, weakLinearInequalityAffineFunction a α i x ≤ 0)
        (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
          weights.IsNonnegativeMultiplierCertificateOn Set.univ
            (weakLinearInequalityAffineFunction a α) epsilon) :=
    xorFiniteAffineCoreAlternative
      (weakLinearInequalityAffineFunction a α)
      (weakLinearInequalityAffineCore a α)
  simpa [ownerSolutionSet, Set.Nonempty, LinearConstraintRelation.mem_leFeasible,
    exists_nonpositive_weakLinearInequalityAffineFunction_iff,
    exists_finsupp_nonnegativeMultiplierCertificateOn_univ_iff] using hmain

/-- Theorem 22.1 on the finite-family `Set.range` weak-system bridge surface: this is the
same owner-level alternative as
`xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate`,
re-expressed using `linearInequalitySolutionSet (Set.range ...)`. -/
theorem xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (solutionSet[a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  simpa [ownerSolutionSet, linearInequalitySolutionSet_range_eq_leFeasible] using
    (xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate
      (a := a) (α := α))

/-- Canonical finite-support owner form of Theorem 22.1: for a finite index type, the weak linear
solution set is nonempty, or there exists a finitely supported nonnegative multiplier certificate
whose weighted functional sum vanishes and whose weighted scalar sum is strictly negative. -/
theorem
    xor_linearInequalitySolutionSet_nonempty_or_finsupp_weak_linear_inequality_farkas_certificate
    [Finite I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (solutionSet[a, α]).Nonempty
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (weights.sum (fun i c ↦ c • a i) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hmain :
      Xor'
        (ownerSolutionSet[a, α]).Nonempty
        (∃ w : I → ℝ,
          (∀ i : I, 0 ≤ w i) ∧
            (∑ i, w i • a i = 0) ∧
              (∑ i, w i * α i) < 0) :=
    xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate a α
  simpa [ownerSolutionSet, linearInequalitySolutionSet_range_eq_leFeasible,
    exists_function_weakLinearInequalityFarkasCertificate_iff_exists_finsupp
    (a := a) (α := α)] using hmain

/-- Source-facing pointwise finite-support restatement of Theorem 22.1. -/
theorem xor_exists_feasible_point_or_finsupp_weak_linear_inequality_farkas_certificate
    [Finite I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, a i x ≤ α i)
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (weights.sum (fun i c ↦ c • a i) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  simpa [Set.Nonempty, mem_linearInequalitySolutionSet_range_iff] using
    xor_linearInequalitySolutionSet_nonempty_or_finsupp_weak_linear_inequality_farkas_certificate
      (I := I) a α

/-- Continuous-dual bridge form of Theorem 22.1, obtained from the canonical algebraic-functional
owner theorem by forgetting continuity. -/
theorem
    xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate_contDual
    [Fintype I] (a : I → E →L[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (solutionSet[a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  let aLin : I → E →ₗ[ℝ] ℝ := fun i ↦ (a i).toLinearMap
  have hmain :
      Xor'
        (solutionSet[aLin, α]).Nonempty
        (∃ w : I → ℝ,
          (∀ i : I, 0 ≤ w i) ∧
            (∑ i, w i • aLin i = 0) ∧
              (∑ i, w i * α i) < 0) :=
    xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate aLin α
  have hsolution :
      (solutionSet[aLin, α]).Nonempty ↔ (solutionSet[a, α]).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [mem_linearInequalitySolutionSet_range_iff] at hx ⊢
      intro i
      change (a i) x ≤ α i
      have hxi : (aLin i) x ≤ α i := hx i
      change (a i).toLinearMap x ≤ α i at hxi
      exact hxi
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [mem_linearInequalitySolutionSet_range_iff] at hx ⊢
      intro i
      change (a i).toLinearMap x ≤ α i
      exact hx i
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • aLin i = 0) ∧
            (∑ i, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      ext x
      have hw_sum_x : (∑ i, w i • aLin i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ => b x) hw_sum
      simpa [aLin] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      ext x
      have hw_sum_x : (∑ i, w i • a i) x = 0 := by
        simpa using congrArg (fun b : E →L[ℝ] ℝ => b x) hw_sum
      simpa [aLin] using hw_sum_x
  let qLin : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • aLin i = 0) ∧
          (∑ i, w i * α i) < 0
  let qCont : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • a i = 0) ∧
          (∑ i, w i * α i) < 0
  have hmain' : Xor' (solutionSet[aLin, α]).Nonempty qLin := by
    simpa [qLin] using hmain
  have hcertificate' : qLin ↔ qCont := by
    simpa [qLin, qCont] using hcertificate
  have hnotiff : ¬ ((solutionSet[a, α]).Nonempty ↔ qCont) := by
    intro hiff
    have hiffLin : (solutionSet[aLin, α]).Nonempty ↔ qLin :=
      (hsolution.trans hiff).trans hcertificate'.symm
    exact ((xor_iff_not_iff _ _).1 hmain') hiffLin
  exact (xor_iff_not_iff _ _).2 hnotiff

/-- Source-facing pointwise restatement of the continuous-dual bridge form of Theorem 22.1. -/
theorem xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate_contDual
    [Fintype I] (a : I → E →L[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, a i x ≤ α i)
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  have hsolution :
      (solutionSet[a, α]).Nonempty ↔ (∃ x : E, ∀ i : I, a i x ≤ α i) := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact (mem_linearInequalitySolutionSet_range_iff (a := a) (α := α) (x := x)).1 hx
    · rintro ⟨x, hx⟩
      exact ⟨x, (mem_linearInequalitySolutionSet_range_iff (a := a) (α := α) (x := x)).2 hx⟩
  let q : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • a i = 0) ∧
          (∑ i, w i * α i) < 0
  have hmain : Xor' (solutionSet[a, α]).Nonempty q := by
    simpa [q] using
      xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate_contDual
        a α
  have hnotiff : ¬ ((∃ x : E, ∀ i : I, a i x ≤ α i) ↔ q) := by
    intro hiff
    have hiffSolution : (solutionSet[a, α]).Nonempty ↔ q := by
      constructor
      · intro hs
        exact hiff.mp (hsolution.mp hs)
      · intro hq
        exact hsolution.mpr (hiff.mpr hq)
    exact
      ((xor_iff_not_iff (solutionSet[a, α]).Nonempty q).1 hmain)
        hiffSolution
  exact (xor_iff_not_iff _ _).2 hnotiff

/-- Source-facing pointwise restatement of Theorem 22.1 on the canonical pairing owner layer. -/
theorem xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate
    [Fintype I] (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, a i x ≤ α i)
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  have hsolution :
      (ownerSolutionSet[a, α]).Nonempty ↔ (∃ x : E, ∀ i : I, a i x ≤ α i) := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact (LinearConstraintRelation.mem_leFeasible a α x).1 hx
    · rintro ⟨x, hx⟩
      exact ⟨x, (LinearConstraintRelation.mem_leFeasible a α x).2 hx⟩
  let q : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • a i = 0) ∧
          (∑ i, w i * α i) < 0
  have hmain : Xor' (ownerSolutionSet[a, α]).Nonempty q := by
    simpa [q] using
      xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate a α
  have hnotiff : ¬ ((∃ x : E, ∀ i : I, a i x ≤ α i) ↔ q) := by
    intro hiff
    have hiffSolution : (ownerSolutionSet[a, α]).Nonempty ↔ q := by
      constructor
      · intro hs
        exact hiff.mp (hsolution.mp hs)
      · intro hq
        exact hsolution.mpr (hiff.mpr hq)
    exact
      ((xor_iff_not_iff (ownerSolutionSet[a, α]).Nonempty q).1 hmain)
        hiffSolution
  exact (xor_iff_not_iff _ _).2 hnotiff

end

section PairingFunctionalBridge

variable {E : Type*} {Y : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" a ", " α "]" =>
  ((linearInequalitySolutionSet (Set.range fun i ↦ (a i, α i))) : Set E)
local notation "ownerSolutionSet[" a ", " α "]" =>
  (LinearConstraintRelation.leFeasible (X := E) a α : Set E)

/-- Canonical owner form of Theorem 22.1 on the pairing layer: the weak feasible owner
`LinearConstraintRelation.leFeasible a α` is nonempty, or there is a nonnegative multiplier
family with vanishing weighted pairing sums and strictly negative weighted scalar sum. -/
theorem xor_leFeasible_nonempty_or_weak_pairing_inequality_farkas_certificate
    (a : I → Y) (α : I → ℝ) :
    Xor'
      (ownerSolutionSet[a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
            (∑ i, w i * α i) < 0) := by
  let aLin : I → E →ₗ[ℝ] ℝ :=
    fun i ↦ (HasLinearPairing.pairingLinear (𝕜 := ℝ) (X := E) (Y := Y)).flip (a i)
  have hmain :
      Xor'
        (ownerSolutionSet[aLin, α]).Nonempty
        (∃ w : I → ℝ,
          (∀ i : I, 0 ≤ w i) ∧
            (∑ i, w i • aLin i = 0) ∧
              (∑ i, w i * α i) < 0) :=
    xor_leFeasible_nonempty_or_weak_linear_inequality_farkas_certificate aLin α
  have hsolution :
      (ownerSolutionSet[aLin, α]).Nonempty ↔ (ownerSolutionSet[a, α]).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [LinearConstraintRelation.mem_leFeasible] at hx ⊢
      intro i
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hx i
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [LinearConstraintRelation.mem_leFeasible] at hx ⊢
      intro i
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hx i
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • aLin i = 0) ∧
            (∑ i, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
            (∑ i, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i, w i • aLin i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i, w i * ⟪x, a i⟫ₚ = 0 := hw_sum x
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
  let qLin : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∑ i, w i • aLin i = 0) ∧
          (∑ i, w i * α i) < 0
  let qPair : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
          (∑ i, w i * α i) < 0
  have hmain' : Xor' (ownerSolutionSet[aLin, α]).Nonempty qLin := by
    simpa [qLin] using hmain
  have hcertificate' : qLin ↔ qPair := by
    simpa [qLin, qPair] using hcertificate
  have hnotiff : ¬ ((ownerSolutionSet[a, α]).Nonempty ↔ qPair) := by
    intro hiff
    have hiffLin : (ownerSolutionSet[aLin, α]).Nonempty ↔ qLin :=
      (hsolution.trans hiff).trans hcertificate'.symm
    exact ((xor_iff_not_iff _ _).1 hmain') hiffLin
  exact (xor_iff_not_iff _ _).2 hnotiff

/-- Pairing `Set.range` bridge form of Theorem 22.1: this is the canonical pairing owner theorem
`xor_leFeasible_nonempty_or_weak_pairing_inequality_farkas_certificate`, restated on
`linearInequalitySolutionSet (Set.range ...)`. -/
theorem xor_linearInequalitySolutionSet_nonempty_or_weak_pairing_inequality_farkas_certificate
    (a : I → Y) (α : I → ℝ) :
    Xor'
      (solutionSet[a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
            (∑ i, w i * α i) < 0) := by
  simpa [ownerSolutionSet, linearInequalitySolutionSet_range_eq_leFeasible] using
    (xor_leFeasible_nonempty_or_weak_pairing_inequality_farkas_certificate
      (a := a) (α := α))

/-- Source-facing pointwise restatement of the pairing-owner form of Theorem 22.1. -/
theorem xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate
    (a : I → Y) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, ⟪x, a i⟫ₚ ≤ α i)
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
            (∑ i, w i * α i) < 0) := by
  have hsolution :
      (ownerSolutionSet[a, α]).Nonempty ↔ (∃ x : E, ∀ i : I, ⟪x, a i⟫ₚ ≤ α i) := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      exact (LinearConstraintRelation.mem_leFeasible a α x).1 hx
    · rintro ⟨x, hx⟩
      exact ⟨x, (LinearConstraintRelation.mem_leFeasible a α x).2 hx⟩
  let q : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
          (∑ i, w i * α i) < 0
  have hmain : Xor' (ownerSolutionSet[a, α]).Nonempty q := by
    simpa [q] using
      xor_leFeasible_nonempty_or_weak_pairing_inequality_farkas_certificate
        (E := E) (Y := Y) a α
  have hnotiff : ¬ ((∃ x : E, ∀ i : I, ⟪x, a i⟫ₚ ≤ α i) ↔ q) := by
    intro hiff
    have hiffSolution : (ownerSolutionSet[a, α]).Nonempty ↔ q := by
      constructor
      · intro hs
        exact hiff.mp (hsolution.mp hs)
      · intro hq
        exact hsolution.mpr (hiff.mpr hq)
    exact
      ((xor_iff_not_iff (ownerSolutionSet[a, α]).Nonempty q).1 hmain)
        hiffSolution
  exact (xor_iff_not_iff _ _).2 hnotiff

private theorem exists_function_weakPairingInequalityFarkasCertificate_iff_exists_finsupp
    (a : I → Y) (α : I → ℝ) :
    (∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
        (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
          (∑ i, w i * α i) < 0) ↔
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E, weights.sum (fun i c ↦ c * ⟪x, a i⟫ₚ) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  constructor
  · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
    refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_, ?_⟩
    · intro i
      simpa using hw_nonneg i
    · intro x
      rw [Finsupp.sum_fintype _ _ fun i ↦ by simp]
      simpa using hw_sum x
    · rw [Finsupp.sum_fintype _ _ fun i ↦ by simp]
      simpa using hw_α
  · rintro ⟨weights, hw_nonneg, hw_sum, hw_α⟩
    refine ⟨Finsupp.equivFunOnFinite weights, ?_, ?_, ?_⟩
    · intro i
      simpa using hw_nonneg i
    · intro x
      have hw_sum' : ∑ i, Finsupp.equivFunOnFinite weights i * ⟪x, a i⟫ₚ = 0 := by
        rw [Finsupp.sum_fintype _ _ fun i ↦ by simp] at hw_sum
        simpa using hw_sum
      exact hw_sum'
    · have hw_α' : (∑ i, Finsupp.equivFunOnFinite weights i * α i) < 0 := by
        rw [Finsupp.sum_fintype _ _ fun i ↦ by simp] at hw_α
        simpa using hw_α
      exact hw_α'

/-- Finite-support pairing-owner form of Theorem 22.1: for a finite index type, the weak
feasible owner set is nonempty, or there exists a finitely supported nonnegative multiplier
certificate with vanishing weighted pairing sums and strictly negative weighted scalar sum. -/
theorem xor_leFeasible_nonempty_or_finsupp_weak_pairing_inequality_farkas_certificate
    [Finite I] (a : I → Y) (α : I → ℝ) :
    Xor'
      (ownerSolutionSet[a, α]).Nonempty
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E, weights.sum (fun i c ↦ c * ⟪x, a i⟫ₚ) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hmain :
      Xor'
        (ownerSolutionSet[a, α]).Nonempty
        (∃ w : I → ℝ,
          (∀ i : I, 0 ≤ w i) ∧
            (∀ x : E, ∑ i, w i * ⟪x, a i⟫ₚ = 0) ∧
              (∑ i, w i * α i) < 0) :=
    xor_leFeasible_nonempty_or_weak_pairing_inequality_farkas_certificate a α
  simpa [exists_function_weakPairingInequalityFarkasCertificate_iff_exists_finsupp
    (a := a) (α := α)] using hmain

/-- Source-facing pointwise finite-support restatement of the pairing-owner form of
Theorem 22.1. -/
theorem xor_exists_feasible_point_or_finsupp_weak_pairing_inequality_farkas_certificate
    [Finite I] (a : I → Y) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, ⟪x, a i⟫ₚ ≤ α i)
      (∃ weights : I →₀ ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E, weights.sum (fun i c ↦ c * ⟪x, a i⟫ₚ) = 0) ∧
            (weights.sum (fun i c ↦ c * α i) < 0)) := by
  simpa [Set.Nonempty, LinearConstraintRelation.mem_leFeasible] using
    xor_leFeasible_nonempty_or_finsupp_weak_pairing_inequality_farkas_certificate
      (E := E) (Y := Y) a α

end PairingFunctionalBridge

section InnerProductSpecialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

/-- Inner-product specialization of Theorem 22.1, recovered from the functional-owner theorem via
the canonical Fréchet-Riesz bridge `InnerProductSpace.toDual`. -/
theorem xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate_innerProduct
    (a : I → E) (α : I → ℝ) :
    Xor'
      (∃ x : E, ∀ i : I, ⟪a i, x⟫ ≤ α i)
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • (InnerProductSpace.toDual ℝ E) (a i) = 0) ∧
            (∑ i, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
          (∑ i, w i • a i = 0) ∧
            (∑ i, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      apply (InnerProductSpace.toDual ℝ E).injective
      simpa using hw_sum
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      simpa using congrArg (InnerProductSpace.toDual ℝ E) hw_sum
  simpa [InnerProductSpace.toDual_apply_apply, Xor', hcertificate] using
    (xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate_contDual
      (fun i ↦ (InnerProductSpace.toDual ℝ E) (a i)) α)

end InnerProductSpecialization
