import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_9_2_0_2 (from Chap02) -/
noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark records three observations about the recession-side hypothesis in
  Theorem 9.2: it is automatic when `h` has no recession directions, therefore also when
  `dom(h)` is bounded, and it fails for the opening example of Section 9.
- `core/canonical`: the owner declarations are `recessionFunction`, `Function.recessionCone`, the
  effective-domain owner `dom(·)`, and the theorem-9.2 recession-kernel owner
  `LinearMap.noAsymmetricRecessionKernel`.
- `bridge/view`: the section-opening counterexample is expressed through the Chapter 2 owner
  `orthantExponential` together with the shared first-coordinate bridge.

Domain-style sampling used here:
- `recessionFunction` and `Function.recessionCone`;
- `linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel`;
- the boundedness owner `Bornology.IsBounded` on `dom(h)`;
- `orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero`.

Primitive data vs derived API:
- primitive inputs: the linear map `A`, the function `h`, and the source-visible condition that
  `h` has no recession directions, rendered as
  `Function.recessionCone ((h)₀⁺) = {0}`;
- derived API: the automatic validity of Theorem 9.2's recession-kernel hypothesis, its bounded
  effective-domain specialization, and the failure statement for the opening example.

Layer target: this item stays `source-facing`, but it is stated directly with the chapter's
canonical recession owners rather than through a new wrapper around Theorem 9.2.
-/

section

variable {𝕜 α E F : Type*}
variable [Semiring 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: if `((h)₀⁺) z ≤ 0`, then `z` belongs to
-- `Function.recessionCone ((h)₀⁺)`, hence the singleton hypothesis forces `z = 0`.
-- The second hypothesis then becomes `0 < ((h)₀⁺) 0`, contradicting the first
-- inequality. Thus the pair of recession inequalities can never occur, so the kernel condition in
-- Theorem 9.2 is vacuous.
/-- Remark 9.2.0.2: if `h` has no directions of recession, formalized by
`Function.recessionCone ((h)₀⁺) = {0}`, then the recession-side hypothesis in
Theorem 9.2 is automatically satisfied. -/
  theorem linearImage_recession_kernel_condition_of_no_recession_directions
      (A : E →ₗ[𝕜] F) (h : E → WithBotTop α)
      (hno_recession : Function.recessionCone ((h)₀⁺) = ({0} : Set E)) :
      A.noAsymmetricRecessionKernel h := by
  intro z hz hneg
  have hz_mem : z ∈ Function.recessionCone ((h)₀⁺) := by
    exact hz
  have hz_zero : z = 0 := by
    have hz_singleton : z ∈ ({0} : Set E) := by
      have hz_mem' : z ∈ Function.recessionCone ((h)₀⁺) := hz_mem
      rwa [hno_recession] at hz_mem'
    simpa [Set.mem_singleton_iff] using hz_singleton
  have hz_nonpos : ((h)₀⁺) 0 ≤ 0 := by
    have h0_mem : (0 : E) ∈ Function.recessionCone ((h)₀⁺) := by
      simpa [hz_zero] using hz_mem
    simpa [Function.mem_recessionCone_iff] using h0_mem
  have hz_pos : 0 < ((h)₀⁺) 0 := by
    simpa [hz_zero] using hneg
  exact (not_lt_of_ge hz_nonpos hz_pos).elim

end

section

variable {E : Type*} [NormedAddCommGroup E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]

private theorem not_isBounded_range_add_nat_smul
    {K : Type*} [RCLike K] [NormedSpace K E]
    (x y : E) (hy : y ≠ 0) :
    ¬ Bornology.IsBounded (Set.range fun n : ℕ ↦ x + n • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + n • y‖ ≤ R := by
    have hxR : x + n • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  have hny : (n : ℝ) * ‖y‖ ≤ R + ‖x‖ := by
    calc
      (n : ℝ) * ‖y‖ = ‖(n : K) • y‖ := by
        simp [norm_smul]
      _ = ‖n • y‖ := by simp [Nat.cast_smul_eq_nsmul]
      _ = ‖(x + n • y) - x‖ := by simp
      _ ≤ ‖x + n • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt : R + ‖x‖ < (n : ℝ) * ‖y‖ := by
    exact (div_lt_iff₀ hy_norm).mp hn
  exact not_lt_of_ge hny hgt

-- Proof sketch: boundedness of the effective domain rules out any nonzero translation direction
-- that preserves finiteness. For `y ≠ 0`, pick `x` in the effective domain with `x + y` outside
-- it; then the defining supremum formula for `((h)₀⁺) y` contains the value `⊤`, so `y` cannot
-- lie in `Function.recessionCone ((h)₀⁺)`. Nonemptiness of `dom(h)` supplies a finite base point.
/-- If the effective domain is nonempty and bounded, then the recession function is `⊤`
in every nonzero direction. -/
theorem recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    (h : E → WithBotTop α)
    (hdom_nonempty : (dom(h)).Nonempty)
    (hdom_bounded : Bornology.IsBounded dom(h))
    (y : E) (hy : y ≠ 0) :
    ((h)₀⁺) y = ⊤ := by
  have hx0_exists : ∃ x : E, h x < ⊤ := by
    rcases hdom_nonempty with ⟨x, hx⟩
    exact ⟨x, mem_effectiveDomain.mp hx⟩
  have hx_out :
      ∃ x : E, h x < ⊤ ∧ ¬ h (x + y) < ⊤ := by
    by_contra hx_out
    push Not at hx_out
    rcases hx0_exists with ⟨x0, hx0_top⟩
    have hrange_subset :
        Set.range (fun n : ℕ ↦ x0 + n • y) ⊆ dom(h) := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      induction n with
      | zero =>
          simpa [mem_effectiveDomain] using hx0_top
      | succ n ih =>
          have : h ((x0 + n • y) + y) < ⊤ := hx_out (x0 + n • y) ih
          simpa [mem_effectiveDomain, succ_nsmul, add_assoc] using this
    have hrange_bounded :
        Bornology.IsBounded (Set.range fun n : ℕ ↦ x0 + n • y) :=
      hdom_bounded.subset hrange_subset
    exact not_isBounded_range_add_nat_smul (K := K) x0 y hy hrange_bounded
  rcases hx_out with ⟨x, hx_top, hxy_not_top⟩
  have hxy_top : h (x + y) = ⊤ := le_antisymm le_top (le_of_not_gt hxy_not_top)
  rw [Function.recessionFunction_apply]
  refine le_antisymm le_top ?_
  refine le_sSup ?_
  exact ⟨x, by simpa [mem_effectiveDomain] using hx_top,
    by
      simpa [hxy_top, sub_eq_add_neg] using
        (WithBotTop.top_sub (x := h x) hx_top.ne).symm⟩

/-- If the effective domain is nonempty and bounded, then the function has no recession
directions. -/
theorem functionRecessionCone_eq_singleton_zero_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    (h : E → WithBotTop α)
    (hdom_nonempty : (dom(h)).Nonempty)
    (hdom_bounded : Bornology.IsBounded dom(h)) :
    Function.recessionCone ((h)₀⁺) = ({0} : Set E) := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff]
    by_contra hy_ne
    have hy_nonpos : ((h)₀⁺) y ≤ 0 := by
      rwa [Function.mem_recessionCone_iff] at hy
    have hy_top : ((h)₀⁺) y = ⊤ :=
      recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain (K := K)
        h hdom_nonempty hdom_bounded y hy_ne
    have htop_not_le : ¬ ((⊤ : WithBotTop α) ≤ 0) := by
      exact not_le_of_gt (WithBotTop.coe_lt_top (0 : α))
    exact htop_not_le (hy_top ▸ hy_nonpos)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Function.mem_recessionCone_iff, Function.recessionFunction_apply]
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, -, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero (x := h x))

end

end

section

open scoped Rockafellar

-- Proof sketch: if the theorem-9.2 kernel condition held for the opening example, Theorem 9.2
-- would make `(LinearMap.fst ℝ ℝ ℝ) ◁ orthantExponential` lower semicontinuous,
-- contradicting the existing Section 9 example theorem that it is not
-- lower semicontinuous at `0`.
/-- The opening example of Section 9 violates the recession-side hypothesis from Theorem 9.2. -/
theorem orthantExponential_violates_linearImage_recession_kernel_condition :
    ¬ (LinearMap.fst ℝ ℝ ℝ).noAsymmetricRecessionKernel orthantExponential := by
  intro hkernel
  have himage_lsc :
      LowerSemicontinuous ((LinearMap.fst ℝ ℝ ℝ) ◁ orthantExponential) :=
    linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel
      (LinearMap.fst ℝ ℝ ℝ)
      orthantExponential
      orthantExponential_isConvex
      orthantExponential_lowerSemicontinuous
      hkernel
  exact orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero
    (himage_lsc.lowerSemicontinuousAt 0)

end

/-! ### Corollary_9_2_1 (from Chap02) -/
open scoped BigOperators

noncomputable section

universe u

open scoped Rockafellar

section KernelCondition

variable {ι : Type u}
variable {E : Type*} [AddCommGroup E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]

namespace Function

/-- Finite-operational recession-kernel condition over a finite index set `s`: no family `z` with
`∑ i ∈ s, (f i)₀⁺ (z i) ≤ 0 < ∑ i ∈ s, (f i)₀⁺ (-z i)` has zero total sum over `s`. -/
def NoZeroSumAsymmetricRecessionOn (s : Finset ι) (f : ι → E → WithTopBot α) : Prop :=
  ∀ z : ι → E,
    (∑ i ∈ s, (f i)₀⁺ (z i)) ≤ 0 →
    (0 : WithTopBot α) < ∑ i ∈ s, (f i)₀⁺ (-z i) →
    (∑ i ∈ s, z i) ≠ 0

section FintypeFamily

variable [Fintype ι]

/-- Family-level recession-kernel condition used in Corollary 9.2.1: this is the
`Finset.univ` specialization of `NoZeroSumAsymmetricRecessionOn`. -/
def NoZeroSumAsymmetricRecession (f : ι → E → WithTopBot α) : Prop :=
  NoZeroSumAsymmetricRecessionOn (s := (Finset.univ : Finset ι)) f

end FintypeFamily

end Function

namespace Rockafellar

/-- Scoped notation for the family-level asymmetric recession-kernel owner in Corollary 9.2.1. -/
scoped notation "noZeroSumAsymmetricRecession[" f "]" =>
  Function.NoZeroSumAsymmetricRecession f

end Rockafellar

end KernelCondition

section

variable {ι : Type u} [Fintype ι]
variable
  {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
  [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable
  {α : Type*} [AddCommGroup α] [SMul 𝕜 α]
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.2.1 treats the infimal convolution of a finite family of closed
  proper convex functions and gives closedness, properness, convexity, attainment of the defining
  infimum, and the recession formula. The source nonemptiness assumption is mathematically active
  only in the attainment clause, because for an empty index type the canonical decomposition
  condition `∑ i, xs i = x` is solvable only at `x = 0`, while the lower-semicontinuity,
  properness, convexity, and recession statements still make sense for the owner
  `finiteInfimalConvolution`.
- `core/canonical`: the project owners are `finiteInfimalConvolution`,
  `Function.recessionFunction`, `LowerSemicontinuous`, `Function.IsProper`, and
  `Function.IsConvex`.
- `bridge/view`: Rockafellar's proof packages the family into a sum function on the product space
  and applies Theorem 9.2 to the addition map. The public API here keeps the source-facing owner
  `finiteInfimalConvolution` rather than introducing a second linear-image wrapper.
- ambient-space refinement: neither the owner `finiteInfimalConvolution` nor the specialization of
  Theorems 9.2 and 9.3 uses coordinates, so the public statements live on an arbitrary
  finite-dimensional Hausdorff topological vector space over the ordered scalar field `𝕜` rather
  than the concrete model `EuclideanSpace ℝ (Fin n)`.

Domain-style sampling used here:
- `finiteInfimalConvolution` and `finiteInfimalConvolution_eq_sInf_decompositions`;
- `recessionFunction`;
- `Function.linearImage` and the statement pattern of Theorem 9.2;
- `Function.isConvex_finiteInfimalConvolution`;
- `Function.NoZeroSumAsymmetricRecessionOn` with the `Fintype` specialization
  `Function.NoZeroSumAsymmetricRecession`.

Primitive data vs derived API:
- primitive inputs: the finite family `f : ι → E → WithTopBot α`, convexity and closedness of its
  members, the source-visible recession-kernel hypothesis, and for the clauses that only need
  exclusion of `-∞`, the pointwise hypothesis `∀ i x, ⊥ < f i x`; the properness and recession
  clauses additionally use the somewhere-finite data packaged by `Function.IsProper`, while
  `[Nonempty ι]` is needed only for the attainment clause;
- derived API: lower semicontinuity, properness, convexity, pointwise attainment, and the
  recession identity for `finiteInfimalConvolution f`.

Layer target: this item stays `source-facing`, stated directly for the chapter owner
`finiteInfimalConvolution`.
-/

variable (f : ι → E → WithTopBot α)

-- Proof sketch: form the sum function `h(xs) = ∑ i, f i (xs i)` on the product space `ι → E`.
-- Theorem 9.3 gives lower semicontinuity of `h`, while
-- `Function.isConvex_sum_of_bot_lt` gives convexity from `hf_convex` and the pointwise
-- `⊥`-avoidance hypothesis `hf_bot`. The addition map `A(xs) = ∑ i, xs i` turns
-- `finiteInfimalConvolution f` into the linear image function `Ah`, and the displayed hypothesis
-- is exactly Theorem 9.2's asymmetric recession-kernel condition for this addition map.
section

/-- Corollary 9.2.1 (1): under the stated zero-sum recession hypothesis, the infimal convolution
of a finite family of convex closed functions that are everywhere strictly above `⊥` is closed,
expressed by lower semicontinuity of `finiteInfimalConvolution f`. -/
theorem finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_bot : ∀ i x, ⊥ < f i x)
    : LowerSemicontinuous (finiteInfimalConvolution f) := sorry

end

section

-- Proof sketch: use the same sum-function and addition-map reduction as in part (1). Theorem 9.2
-- then gives properness of the linear image, and the linear image is exactly
-- `finiteInfimalConvolution f`.
/-- Corollary 9.2.1 (2): under the same hypothesis, the finite infimal convolution is proper. -/
theorem finiteInfimalConvolution_isProper_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_proper : ∀ i, (f i).IsProper)
    : (finiteInfimalConvolution f).IsProper := sorry

end

/- The convexity clause is exactly the existing finite-family owner theorem for
`finiteInfimalConvolution`. -/
recall Function.isConvex_finiteInfimalConvolution

section

-- Proof sketch: apply the attainment clause of Theorem 9.2 to the sum function on the product
-- space and the addition map. Translating the resulting point of the fiber `∑ i, xs i = x` back
-- through the definition of `finiteInfimalConvolution` gives an optimizing decomposition whenever
-- the value is finite, while in the case `finiteInfimalConvolution f x = ⊤` any decomposition of
-- `x` suffices.
variable [Nonempty ι]

/-- Corollary 9.2.1 (3): for each `x`, the infimum defining `finiteInfimalConvolution f x` is
attained by some decomposition `x = ∑ i, xs i`, assuming the finite index type is nonempty and
each summand is everywhere strictly above `⊥`. -/
theorem exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_bot : ∀ i x, ⊥ < f i x)
    (x : E) :
    ∃ xs : ι → E,
      (∑ i, xs i) = x ∧ finiteInfimalConvolution f x = ∑ i, f i (xs i) := sorry

end

section

-- Proof sketch: first identify `finiteInfimalConvolution f` with the linear image under the
-- addition map of the finite sum function on the product space. Theorem 9.3 computes the recession
-- function of that finite sum as the finite sum of the recession functions, and Theorem 9.2 then
-- transports recession functions across the addition map under the same kernel hypothesis.
/-- Corollary 9.2.1 (4): the recession function of the finite infimal convolution is the finite
infimal convolution of the recession functions,
`(f₁ □ ⋯ □ f_m)₀⁺ = f₁0⁺ □ ⋯ □ f_m0⁺`. -/
theorem
    recessionFunction_finiteInfimalConvolution_eq_of_no_zero_sum_asymmetric_recession
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hkernel : noZeroSumAsymmetricRecession[f])
    (hf_proper : ∀ i, (f i).IsProper)
    : (finiteInfimalConvolution f)₀⁺ =
        finiteInfimalConvolution (fun i ↦ (f i)₀⁺) := sorry

end

end

/-! ### Corollary_9_2_2 (from Chap02) -/
open scoped BigOperators Rockafellar

noncomputable section

section KernelBridge

variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable {E : Type*} [AddCommGroup E]
variable (f₁ f₂ : E → WithTopBot α)

/-- Binary bridge from Rockafellar's positivity hypothesis to the canonical family owner
`noZeroSumAsymmetricRecession[![f₁, f₂]]`. -/
theorem noZeroSumAsymmetricRecession_two_of_positive_recession_sum
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    noZeroSumAsymmetricRecession[![f₁, f₂]] := by
  intro z hz_nonpos hz_pos
  rw [Fin.sum_univ_two]
  intro hsum
  have hz1 : z 1 = -z 0 := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  by_cases hz0 : z 0 = 0
  · have hz1_zero : z 1 = 0 := by simpa [hz0] using hz1
    have hz_nonpos' : ((f₁)₀⁺) 0 + ((f₂)₀⁺) 0 ≤ 0 := by
      simpa [Fin.sum_univ_two, hz0, hz1_zero] using hz_nonpos
    have hz_pos' : (0 : WithTopBot α) < ((f₁)₀⁺) 0 + ((f₂)₀⁺) 0 := by
      simpa [Fin.sum_univ_two, hz0, hz1_zero] using hz_pos
    exact (not_lt_of_ge hz_nonpos') hz_pos'
  · have hz_nonpos' : ((f₁)₀⁺) (z 0) + ((f₂)₀⁺) (-z 0) ≤ 0 := by
      simpa [Fin.sum_univ_two, hz1] using hz_nonpos
    exact (not_lt_of_ge hz_nonpos') (hrecession (z 0) hz0)

end KernelBridge

section

variable
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable
  {α : Type*} [AddCommGroup α] [SMul 𝕜 α]
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.2.2 states that the binary infimal convolution `f₁ □ f₂` of two
  closed proper convex functions is again closed proper convex, and that its defining infimum is
  attained, provided the sum of the two recession functions is strictly positive away from `0`.
- `core/canonical`: the owner abstraction for this domain is the finite-family
  `finiteInfimalConvolution` API from Corollary 9.2.1 together with the chapter owners
  `(·)₀⁺`, `Function.IsConvex`, `Function.IsProper`,
  and `LowerSemicontinuous`.
- `bridge/view`: the binary operation `f₁ □ f₂` is the `Fin 2`
  specialization of `finiteInfimalConvolution`, via
  `finiteInfimalConvolution_two_eq_infimal_convolution`. Clause (3) is already owned upstream by
  `Function.IsConvex.infimal_convolution`, so this file should recall that theorem directly
  instead of introducing a parallel local name. The attainment clause is kept in the textbook
  variable order `f₁ (x - y) + f₂ y`, while the owner definition uses the equivalent one-parameter
  infimum `⨅ y, f₁ y + f₂ (x - y)`.

Domain-style sampling used here:
- `finiteInfimalConvolution_two_eq_infimal_convolution`;
- `finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession`;
- `exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession`;
- `Function.isConvex_finiteInfimalConvolution`;
- `Function.recessionFunction`;
- the finite-dimensional Hausdorff topological vector space ambient assumptions over the ordered
  scalar field `𝕜`, with codomain layer `WithTopBot α`, already used by Corollary 9.2.1.

Primitive data vs derived API:
- primitive inputs: the two functions `f₁`, `f₂` together with the convexity and closedness
  hypotheses, the pointwise lower-bound hypotheses `∀ x, ⊥ < fᵢ x` used by the closedness and
  attainment clauses, the properness hypotheses used only by the properness clause, and the
  owner-level binary recession-kernel hypothesis
  `noZeroSumAsymmetricRecession[![f₁, f₂]]`; the source-facing positivity
  condition is kept as a bridge implication into that owner hypothesis. Clause (3) adds no
  primitive data beyond
  the upstream owner theorem's convexity inputs;
- derived API: lower semicontinuity, properness, convexity, and pointwise attainment for
  `infimal_convolution f₁ f₂`.

Layer target: this item stays `source-facing`, but its binary statements are refined to the
existing finite-family owner pattern rather than treated as a separate root abstraction. The
closedness, properness, and attainment clauses are the `Fin 2` specialization of Corollary 9.2.1,
while the convexity clause is a `bridge/view` recall of the existing owner theorem
`Function.IsConvex.infimal_convolution` and therefore does not keep a second public theorem name
or the other clauses' stronger hypotheses as primitive data.

Ambient-space refinement: the binary specialization uses no coordinates. Since the upstream owner
API in Corollary 9.2.1 already lives on an arbitrary finite-dimensional Hausdorff topological
vector space over `𝕜`, this file stays at that intrinsic ambient level rather than specializing
back to the textbook display model `R^n`.
-/

section Binary

variable (f₁ f₂ : E → WithTopBot α)

-- Proof sketch: this binary statement is the `Fin 2` specialization of the owner theorem from
-- Corollary 9.2.1. The owner theorem for this clause needs only convexity, closedness, the
-- pointwise exclusion of `⊥`, and the recession hypothesis, so the redundant properness binders
-- are removed here as well. `finiteInfimalConvolution_two_eq_infimal_convolution` rewrites the
-- owner conclusion into lower semicontinuity of `f₁ □ f₂`.
theorem infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]]) :
    LowerSemicontinuous (f₁ □ f₂) := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  have hfin : LowerSemicontinuous (finiteInfimalConvolution F) :=
    finiteInfimalConvolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_bot := by
        intro i x
        fin_cases i
        · simpa [F] using hf₁_bot x
        · simpa [F] using hf₂_bot x)
  have hfin' : LowerSemicontinuous
      (Function.verticalInfimum (finiteInfimalConvolutionSupport F)) := by
    simpa [finiteInfimalConvolution] using hfin
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hfin'

/-- Corollary 9.2.2 (1): if
`f₁0⁺(z) + f₂0⁺(-z) > 0` for every nonzero `z`, then the infimal
convolution `f₁ □ f₂` is closed, expressed as lower semicontinuity. -/
theorem infimal_convolution_lowerSemicontinuous_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    LowerSemicontinuous (f₁ □ f₂) := by
  exact infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_bot hf₁_closed hf₂_convex hf₂_bot hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)

-- Proof sketch: apply the same `Fin 2` specialization of Corollary 9.2.1 and rewrite the owner
-- conclusion across `finiteInfimalConvolution_two_eq_infimal_convolution`.
theorem infimal_convolution_isProper_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_proper : f₁.IsProper)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_proper : f₂.IsProper)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]]) :
    (f₁ □ f₂).IsProper := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  have hfin : (finiteInfimalConvolution F).IsProper :=
    finiteInfimalConvolution_isProper_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_proper := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_proper
        · simpa [F] using hf₂_proper)
  have hfin' : Function.IsProper
      (Function.verticalInfimum (finiteInfimalConvolutionSupport F)) := by
    simpa [finiteInfimalConvolution] using hfin
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hfin'

/-- Corollary 9.2.2 (2): under the same recession-sum positivity hypothesis, the infimal
convolution `f₁ □ f₂` is proper. -/
theorem infimal_convolution_isProper_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_proper : f₁.IsProper)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_proper : f₂.IsProper)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z)) :
    (f₁ □ f₂).IsProper := by
  exact infimal_convolution_isProper_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_proper hf₁_closed hf₂_convex hf₂_proper hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)

/- Corollary 9.2.2 (3) is the direct canonical owner theorem for binary infimal convolution
convexity. Unlike the closedness and properness clauses, this conclusion uses only convexity of
the two inputs, so the faithful refined surface is a recall of
`Function.IsConvex.infimal_convolution` rather than a duplicate local wrapper. -/
recall Function.IsConvex.infimal_convolution

-- Proof sketch: specialize the attainment clause of Corollary 9.2.1 to the binary family
-- `![f₁, f₂]`. The resulting minimizing decomposition `x = x₁ + x₂` is then rewritten in the
-- textbook variable order by taking `y := x₂`, so `x₁ = x - y`.
theorem exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hkernel : noZeroSumAsymmetricRecession[![f₁, f₂]])
    (x : E) :
    ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  let F : Fin 2 → E → WithTopBot α := (![f₁, f₂] : Fin 2 → E → WithTopBot α)
  have hkernelF : Function.NoZeroSumAsymmetricRecession F := by
    simpa [F] using hkernel
  obtain ⟨xs, hsum, hvalue⟩ :=
    exists_sum_eq_finiteInfimalConvolution_of_no_zero_sum_asymmetric_recession
      (f := F)
      (hf_convex := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_convex
        · simpa [F] using hf₂_convex)
      (hf_closed := by
        intro i
        fin_cases i
        · simpa [F] using hf₁_closed
        · simpa [F] using hf₂_closed)
      (hkernel := hkernelF)
      (hf_bot := by
        intro i x'
        fin_cases i
        · simpa [F] using hf₁_bot x'
        · simpa [F] using hf₂_bot x')
      x
  refine ⟨xs 1, ?_⟩
  have hx0 : xs 0 = x - xs 1 := by
    rw [eq_sub_iff_add_eq]
    simpa [Fin.sum_univ_two, add_comm] using hsum
  have hvalue' :
      Function.verticalInfimum (finiteInfimalConvolutionSupport F) x =
        f₁ (x - xs 1) + f₂ (xs 1) := by
    simpa [finiteInfimalConvolution, F, Fin.sum_univ_two, hx0] using hvalue
  have htwo : Function.verticalInfimum (finiteInfimalConvolutionSupport F) = f₁ □ f₂ := by
    simpa [finiteInfimalConvolution, F] using
      finiteInfimalConvolution_two_eq_infimal_convolution (f := F)
  exact htwo ▸ hvalue'

/-- Corollary 9.2.2 (4): for every `x`, the infimum in the textbook formula
`(f₁ □ f₂)(x) = inf_y (f₁ (x - y) + f₂ y)` is attained by some `y`. -/
theorem exists_argmin_infimal_convolution_of_positive_recession_sum
    (hf₁_convex : f₁.IsConvex 𝕜)
    (hf₁_bot : ∀ x : E, ⊥ < f₁ x)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂_convex : f₂.IsConvex 𝕜)
    (hf₂_bot : ∀ x : E, ⊥ < f₂ x)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hrecession :
      ∀ z : E, z ≠ 0 → (0 : WithTopBot α) < ((f₁)₀⁺) z + ((f₂)₀⁺) (-z))
    (x : E) :
    ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  exact exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession
    (f₁ := f₁) (f₂ := f₂)
    hf₁_convex hf₁_bot hf₁_closed hf₂_convex hf₂_bot hf₂_closed
    (noZeroSumAsymmetricRecession_two_of_positive_recession_sum
      (f₁ := f₁) (f₂ := f₂) hrecession)
    x

end Binary

end

/-! ### Example_9_2_2_2 (from Chap02) -/
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Pointwise Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example specializes Corollary 9.2.2 to the case where `f₁` is the
  `0/+∞` indicator of `-C`, so that `f₁ □ f` becomes the infimum of `f` over the translate
  `C + x`.
- `core/canonical`: the owner declarations already present in the project are
  `indicatorFunction`, `infimal_convolution`, `recessionCone`, object-prefix
  `(·).recessionCone`, the
  recession owner `Function.recessionFunction` with chapter notation `(·)₀⁺`,
  `LowerSemicontinuous`, and `Function.IsConvex`.
- `bridge/view`: the textbook condition "no common direction of recession" is rendered by saying
  that the only vector lying in both `recessionCone C` and
  `((f)₀⁺).recessionCone` is `0`.

Domain-style sampling used here:
- `infimal_convolution` / `□` from Text 5.4.0;
- `exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession`,
  `infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession`, and
  `Function.IsConvex.infimal_convolution` in the Corollary 9.2.2 neighborhood;
- `indicatorFunction` from Definition 4.8.1 as the canonical `WithBotTop α` owner for the
  `0/+∞` indicator;
- `recessionCone`, object-prefix `(·).recessionCone`, and the chapter recession notation `(·)₀⁺`
  as the
  source-facing owners for recession directions of sets and functions.

Primitive data vs derived API:
- primitive inputs for the main identity: the set `C`, the function `f`, the point `x`, and the
  owner-level no-`⊥` guard `∀ y, ⊥ < f y` needed because `infimal_convolution` is computed in
  `WithBotTop α`;
- derived API: the recession-condition bridge and the attainment / lower-semicontinuity /
  convexity consequences under the closed proper convex hypotheses of the example.
- ambient-space refinement: the pointwise identity and the recession bridge use no coordinates or
  topology. The closedness/attainment consequences use the same ordered scalar-field finite-
  dimensional Hausdorff topological vector-space owner layer as Corollary 9.2.2, rather than the
  display model `EuclideanSpace ℝ (Fin n)`.
-/

section Core

section Pointwise

variable {E : Type*} [AddGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

-- Proof sketch: unfold `infimal_convolution` and split the infimum according to whether
-- `x - y ∈ -C`. This membership condition is equivalent to `y ∈ C + {x}`. The owner-level guard
-- `∀ y, ⊥ < f y` rules out the mixed `⊤ + ⊥ = ⊥` pathology in `WithBotTop α`, so the outside branch
-- simplifies to `⊤` and the remaining values are exactly the image set `f '' (C + {x})`.
/-- Example 9.2.2.2: specializing `f₁` to the `0/+∞` indicator of `-C`, the infimal convolution
`f₁ □ f` at `x` is the infimum of the values `f y` over the translate `C + {x}`. The closedness,
convexity, and nonemptiness assumptions from the prose are not needed for this pointwise identity;
the only extra hypothesis is the owner-level exclusion `∀ y, ⊥ < f y`, which prevents the
`WithBotTop α` addition pathology `⊤ + ⊥ = ⊥`. -/
theorem infimal_convolution_indicator_neg_eq_sInf_image_translate
    (C : Set E) (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) (x : E) :
    ((δ[α](· | -C)) □ f) x = sInf (f '' (C + {x})) := sorry

end Pointwise

section Scalar

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: identify the recession function `((δ[𝕜](· | -C))₀⁺)` of the `0/+∞` indicator of
-- `-C` with the indicator of the recession cone of `-C`, rewrite that cone as `- recessionCone C`,
-- and convert the no-common-direction intersection condition into Corollary 9.2.2's primitive
-- family-kernel owner `noZeroSumAsymmetricRecession`.
/-- The example's "no common direction of recession" hypothesis implies Corollary 9.2.2's
primitive recession-kernel owner for the indicator specialization to `-C`. -/
theorem noZeroSumAsymmetricRecession_indicator_neg_of_no_common_recession_direction
    (C : Set E) (f : E → WithBotTop 𝕜)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E)) :
    noZeroSumAsymmetricRecession[![(δ[𝕜](· | -C)), f]] := sorry

-- Proof sketch: `δ[𝕜](· | -C)` is convex because `-C` is convex, so the convexity clause of
-- Corollary 9.2.2 applies directly to the pair `δ[𝕜](· | -C)` and `f`.
/-- If `C` and `f` are convex, then the indicator-specialized infimal convolution from Example
9.2.2.2, equivalently the translate-infimum function `x ↦ inf {f y | y ∈ C + {x}}`, is convex. -/
theorem Function.IsConvex.indicator_neg_infimal_convolution
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    ((δ[𝕜](· | -C)) □ f).IsConvex 𝕜 := by
  have hindicator : (δ[𝕜](· | -C) : E → WithBotTop 𝕜).IsConvex 𝕜 :=
    (indicator_isConvex_iff (-C)).2 hC_convex.neg
  simpa using Function.IsConvex.infimal_convolution hindicator hf_convex

end Scalar

end Core

section Closed

variable {𝕜 : Type*} [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable {C : Set E} {f : E → WithBotTop 𝕜}

-- Proof sketch: apply Corollary 9.2.2 (4) to the pair consisting of the indicator of `-C` and
-- the given closed convex function `f`, using the previous bridge theorem to supply the recession
-- kernel hypothesis and the pointwise assumption `∀ x, ⊥ < f x` for the only function-side
-- exclusion of `-∞` needed by the owner theorem. Then rewrite the minimizing point into membership
-- of the translate `C + {x}` via the identity theorem above.
/-- Under the example's recession hypothesis, the infimum of `f` over each translate `C + {x}` is
attained. -/
theorem exists_mem_translate_eq_infimal_convolution_of_no_common_recession_direction
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E))
    (hC_nonempty : C.Nonempty)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (x : E) :
    ∃ y ∈ C + {x},
      ((δ[𝕜](· | -C)) □ f) x = f y := sorry

-- Proof sketch: first obtain the corollary's recession-kernel hypothesis from the previous
-- bridge theorem. Then specialize Corollary 9.2.2 (1) to the indicator of `-C`; here the only
-- function-side side condition beyond convexity and lower semicontinuity is the pointwise
-- exclusion `∀ x, ⊥ < f x`, so the unused nonemptiness/properness binders are removed.
/-- Under the example's recession hypothesis, the function `x ↦ inf_{y ∈ C + {x}} f y` is lower
semicontinuous, expressed through the canonical infimal convolution with the indicator of `-C`. -/
theorem indicator_neg_infimal_convolution_lowerSemicontinuous_of_no_common_recession_direction
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E))
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((δ[𝕜](· | -C)) □ f) := sorry

end Closed

/-! ### Example_9_2_2_3 (from Chap02) -/
noncomputable section

attribute [local instance] Classical.propDecidable

section OrderCore

open scoped Rockafellar

variable {X : Type*} [Preorder X]
variable {α : Type*} [CompleteSemilatticeInf α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example studies the function `g(x) = inf {f(y) | y ≥ x}` obtained by
  taking infima over order-upper sets.
- `core/canonical`: the owner abstractions already present in the project are the positive-cone
  owner `(ConvexCone.positive 𝕜 E : Set E)`, the order-upper-closure owner `upperClosure`, and the
  generic indicator-specialized infimal-convolution API from Example 9.2.2.2.
- `bridge/view`: the orthant upper set above `x` is rendered as `{y | y ≥ x}` and identified with
  the singleton specialization of `upperClosure_eq_add_orthant`; the source function
  `g` is then
  connected to the owner-side indicator infimal convolution by a thin specialization to
  `C = (ConvexCone.positive 𝕜 E : Set E)`.

Domain-style sampling used here:
- `ConvexCone.positive`;
- `upperClosure_eq_add_orthant`;
- `indicator` / `δ[α](· | C)`;
- `infimal_convolution_indicator_neg_eq_sInf_image_translate`;
- `Monotone`.

Primitive data vs derived API:
- primitive source-facing data: only `orthantInfimumMinorant`, defined through the canonical owner
  `upperClosure ({x} : Set X)`;
- derived API: the set-builder formula `{y | y ≥ x}`, the orthant-translate bridge, the
  indicator-infimal-convolution bridge under the owner-level no-`⊥` guard `∀ y, ⊥ < f y`,
  attainment, lower semicontinuity, properness, convexity, and the greatest-minorant property.

Layer target: this item stays `source-facing`. The public object remains the textbook minorant
`g(x) = inf {f(y) | y ≥ x}`, but its support lemmas and downstream statements reuse the chapter's
orthant owners instead of parallel local wrappers.
-/

/-- The function `g(x) = inf {f(y) | y ≥ x}` obtained by taking the infimum of `f` over the
orthant upper set above `x`. -/
def orthantInfimumMinorant (f : X → α) : X → α :=
  fun x ↦ sInf (f '' upperClosure ({x} : Set X))

private theorem upperClosure_singleton_eq_orthantUpperSet (x : X) :
    (upperClosure ({x} : Set X) : Set X) = {y : X | y ≥ x} := by
  ext y
  rw [upperClosure_singleton]
  simp [ge_iff_le]

/-- The defining formula for `orthantInfimumMinorant` is the infimum of `f` over the orthant upper
set above `x`. -/
theorem orthantInfimumMinorant_eq_sInf_image (f : X → α) (x : X) :
    orthantInfimumMinorant f x = sInf (f '' {y : X | y ≥ x}) :=
  by rw [orthantInfimumMinorant, upperClosure_singleton_eq_orthantUpperSet]

-- Proof sketch: the point `x` itself satisfies `x ≥ x`, so
-- `orthantInfimumMinorant f x ≤ f x`. If `h ≤ f` is monotone for `≥` and `y ≥ x`,
-- then `h x ≤ h y ≤ f y`; taking the infimum over all such `y` gives
-- `h x ≤ orthantInfimumMinorant f x`. Monotonicity of `orthantInfimumMinorant f` is kept in the
-- canonical order-theoretic owner form `Monotone`, and follows from inclusion of orthant upper
-- sets under `≥`.
/-- Example 9.2.2.3 in its order-theoretic owner form: `orthantInfimumMinorant f` is the greatest
minorant of `f` that is nondecreasing for the ambient order, canonically expressed as
`Monotone`. -/
theorem orthantInfimumMinorant_isGreatest_orthantMonotone_minorant
    (f : X → α) :
    IsGreatest
      {h : X → α | h ≤ f ∧ Monotone h}
      (orthantInfimumMinorant f) := sorry

end OrderCore

section OrthantOrderedModulePointwise

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

private theorem orthantUpperSet_eq_translate_nonnegativeOrthant (x : E) :
    {y : E | y ≥ x} = E≥0 + ({x} : Set E) := by
  calc
    {y : E | y ≥ x} = (upperClosure ({x} : Set E) : Set E) := by
      rw [upperClosure_singleton_eq_orthantUpperSet x]
    _ = ({x} : Set E) + E≥0 :=
      upperClosure_eq_add_orthant ({x} : Set E)
    _ = E≥0 + ({x} : Set E) := by rw [add_comm]

-- Proof sketch: specialize Example 9.2.2.2 to `C = E≥0`, using the
-- no-`⊥` guard on `f` needed by the `WithBotTop α` owner `infimal_convolution`, and then rewrite
-- the resulting
-- translate-infimum
-- formula using the private orthant-translate identification above and the canonical
-- `WithBotTop α`-valued indicator owner `indicatorFunction`.
/-- `orthantInfimumMinorant f` is the specialization of the canonical indicator infimal
convolution from Example 9.2.2.2 to the nonnegative orthant. As in that owner bridge, the
pointwise exclusion `∀ y, ⊥ < f y` is needed to avoid the mixed `⊤ + ⊥ = ⊥` branch of
`WithBotTop α` addition. -/
theorem orthantInfimumMinorant_eq_infimal_convolution_indicator_neg
    (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) :
    orthantInfimumMinorant f =
      ((δ[α](· | -E≥0)) □ f) := by
  sorry

end OrthantOrderedModulePointwise

section OrthantOrderedModuleClosed

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

section Ambient

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [T2Space E] [FiniteDimensional 𝕜 E]

-- Proof sketch: specialize the attainment clause of Example 9.2.2.2 to `C = E≥0`.
-- The resulting minimizing point lies in `E≥0 + ({x} : Set E)`, which is exactly the relation
-- `y ≥ x`.
/-- The infimum defining `orthantInfimumMinorant f x` is attained whenever the recession function
`(f)₀⁺` is strictly positive on every nonzero vector of the nonnegative orthant `E≥0`. -/
theorem exists_argmin_orthantInfimumMinorant_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z)
    (x : E) :
    ∃ y : E, y ≥ x ∧ orthantInfimumMinorant f x = f y := sorry

-- Proof sketch: identify `orthantInfimumMinorant f` with the orthant-indicator infimal
-- convolution and specialize the lower-semicontinuity clause from Example 9.2.2.2. As in the
-- upstream owner theorem, the only function-side exclusion of `-∞` needed here is the pointwise
-- hypothesis `∀ x, ⊥ < f x`.
/-- Under the same orthant recession hypothesis, `orthantInfimumMinorant f` is closed, expressed
as lower semicontinuity. -/
theorem orthantInfimumMinorant_lowerSemicontinuous_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z) :
    LowerSemicontinuous (orthantInfimumMinorant f) := sorry

-- Proof sketch: apply the properness clause of Corollary 9.2.2 to the pair consisting of `f` and
-- the `0/+∞` indicator of `-E≥0`, then rewrite the resulting
-- infimal convolution
-- as `orthantInfimumMinorant f`.
/-- Under the same orthant recession hypothesis, `orthantInfimumMinorant f` is proper. -/
theorem orthantInfimumMinorant_isProper_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z) :
    (orthantInfimumMinorant f).IsProper := sorry

end Ambient

end OrthantOrderedModuleClosed

section OrthantOrderedModuleConvex

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module 𝕜 E] [PosSMulMono 𝕜 E]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

-- Proof sketch: rewrite `orthantInfimumMinorant f` through the canonical owner bridge above, note
-- that `E≥0` is convex, and then apply the generic
-- indicator-specialized
-- convexity theorem. Unlike the closedness and properness clauses, this conclusion only uses the
-- convexity of `f`.
/-- If `f` is convex, then `orthantInfimumMinorant f` is convex. -/
theorem orthantInfimumMinorant_isConvex
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜) :
    (orthantInfimumMinorant f).IsConvex 𝕜 := by
  sorry

end OrthantOrderedModuleConvex

/-! ### Theorem_9_2 (from Chap02) -/
noncomputable section

open scoped Rockafellar

section

variable {𝕜 α : Type*} {E F : Type*}
variable [Semiring 𝕜]
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- The recession-kernel side condition in Theorem 9.2: no direction `z` with
`z ∈ Function.recessionCone ((h)₀⁺)` and `0 < ((h)₀⁺) (-z)` lies in the kernel of `A`. -/
def noAsymmetricRecessionKernel (A : E →ₗ[𝕜] F) (h : E → WithTopBot α) : Prop :=
  ∀ z : E, z ∈ Function.recessionCone ((h)₀⁺) → 0 < ((h)₀⁺) (-z) → z ∉ A.ker

end LinearMap

end

section Convexity

variable {𝕜 : Type*} {E F : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

variable (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜)

/- Theorem 9.2 (2): the convexity clause is already the chapter owner theorem
`Function.isConvex_linearImage`, so this file recalls that canonical result directly instead
of keeping a parallel exact-interface wrapper. -/
recall Function.isConvex_linearImage

end Convexity

section

variable
    {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 9.2 studies the image function `Ah` of a closed convex function `h`
  under a linear map `A`, with an additional recession-kernel hypothesis. The file keeps the
  source clauses split by their actual hypotheses: closedness, convexity, and attainment need only
  convexity plus lower semicontinuity, while properness of `h` is added only for the properness
  and recession-function clauses.
- `core/canonical`: the chapter owner abstractions already present are `Function.linearImage A h`
  for `Ah`, `recessionFunction h` for `(h)₀⁺`, `h.IsConvex`, `h.IsProper`, and
  `LowerSemicontinuous`.
- `bridge/view`: the theorem's epigraph argument runs through `linearImageEpigraph A h`, while
  the textbook notation `A((h)₀⁺)` is rendered canonically as `Function.linearImage A
  (recessionFunction h)`.

Domain-style sampling used here:
- `Function.linearImage` and `Function.linearImage_eq_sInf_image`;
- `linearImageEpigraph` together with
  `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom`;
- `recessionFunction`;
- `Function.isConvex_linearImage`.
- ambient-space refinement: the convexity owner `Function.linearImage` already lives on arbitrary
  scalar modules, while the closed-image, lower-semicontinuity, properness, recession, and
  attainment clauses pass through the closed-image epigraph route from Theorem 9.1 and therefore
  need the finite-dimensional Hausdorff topological-vector-space source together with a
  Hausdorff topological-vector-space target over the same ordered scalar field. Equivalently, the
  proof route needs `F × 𝕜`
  Hausdorff when identifying the closed image epigraph with `epi (A ◁ h)`. The Euclidean
  `R^n → R^m` presentation is therefore demoted to the `𝕜 = ℝ` specialization instead of remaining
  the
  public owner layer.

Primitive data vs derived API:
- primitive inputs: the linear map `A`, the function `h`, its convexity and closedness
  hypotheses, and the source-visible recession-kernel owner
  `A.noAsymmetricRecessionKernel h`;
- derived API: lower semicontinuity, convexity, the attainment statement for
  `Function.linearImage A h`, and, once properness of `h` is added, properness and the
  recession-image formula for `Ah`.

Layer target: this item stays `source-facing`, but it is written directly in terms of the chapter's
canonical owners `Function.linearImage` and `recessionFunction` rather than introducing a second
wrapper for Rockafellar's notation `Ah`.
-/

-- Proof sketch: apply Theorem 9.1 to the scalar epigraph of `h` and the linear map
-- `(x, μ) ↦ (A x, μ)`. Convexity and closedness of the epigraph come from `hh_convex` and
-- `hh_closed`, and the recession-kernel hypothesis translates the source condition into the
-- exclusion of downward vertical recession directions in the image epigraph. The resulting closed
-- image epigraph is exactly the epigraph of `Function.linearImage A h`.
variable (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜)

/-- Theorem 9.2 (1): under the stated recession-kernel hypothesis, the image function `Ah` is
closed, expressed here by lower semicontinuity of `Function.linearImage A h`. -/
theorem linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    :
    LowerSemicontinuous (A ◁ h) := sorry

-- Proof sketch: choose `x` with `h x < ⊤` using properness of `h`; then
-- `Function.linearImage A h (A x) ≤ h x < ⊤`, so `Ah` is somewhere finite. The closed-image
-- argument from part (1) rules out downward vertical lines in the image epigraph, hence every
-- value of `Ah` is strictly above `⊥`. Using the chapter characterization of properness gives the
-- conclusion.
/-- Theorem 9.2 (3): under the same hypotheses, the image function `Ah` is proper. -/
theorem linearImage_isProper_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (hh_proper : h.IsProper)
    :
    (A ◁ h).IsProper := sorry

-- Proof sketch: apply the recession-cone image formula from Theorem 9.1 to the scalar epigraph of
-- `h` under `(x, μ) ↦ (A x, μ)`. Identify the recession cone of `epi h` with the epigraph of
-- `(h)₀⁺` and the recession cone of `epi (Ah)` with the epigraph of `(Function.linearImage A h)₀⁺`.
-- Comparing the two epigraphs yields the stated
-- equality of recession functions.
/-- Theorem 9.2 (4): the recession function of `Ah` is the image under `A` of the recession
function of `h`, i.e. `(Ah)₀⁺ = A((h)₀⁺)`. -/
theorem
    recessionFunction_linearImage_eq_linearImage_recessionFunction_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (hh_proper : h.IsProper)
    :
    (A ◁ h)₀⁺ = (A ◁ ((h)₀⁺)) := sorry

-- Proof sketch: if `y ∈ dom(A ◁ h)`, then the vertical section of the image
-- epigraph above `y` is nonempty. Use `hh_convex` to make `linearImageEpigraph A h` convex,
-- combine the closedness from part (1) with the downward recession exclusion encoded by
-- `hkernel`, then apply
-- `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom` to obtain a
-- fiber point `x` with `A x = y` and `h x = Function.linearImage A h y`.
/-- Theorem 9.2 (5): for every `y` in the effective domain of `Ah`, the infimum defining `Ah(y)`
is attained by some `x` in the fiber `A x = y`. -/
theorem exists_preimage_eq_linearImage_of_mem_dom_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (y : F) (hy : y ∈ dom(A ◁ h)) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := sorry

end

end
