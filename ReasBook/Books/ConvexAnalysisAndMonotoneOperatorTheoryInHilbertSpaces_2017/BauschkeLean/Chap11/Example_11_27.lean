import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap02.Example_2_32_1
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Example_9_13
import BauschkeLean.Chap11.Corollary_11_9
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators InnerProductSpace Topology

universe u

namespace ERealFunction

section

/-- The real-valued weighted quadratic coordinate function used in the Hilbert-basis series
example. The weights are primitive nonnegative data, so no separate proof witness enters the
owner. -/
def weightedSquareCoordinate (ω : ℕ → NNReal) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ (ω n : ℝ) * t ^ 2

/-- The weighted quadratic coordinate function vanishes at the origin. -/
@[simp] theorem weightedSquareCoordinate_zero (ω : ℕ → NNReal) (n : ℕ) :
    weightedSquareCoordinate ω n 0 = 0 := by
  simp [weightedSquareCoordinate]

/-- Viewing the weighted quadratic coordinate through `toEReal` preserves the value at `0`. -/
@[simp] theorem weightedSquareCoordinate_toEReal_zero (ω : ℕ → NNReal) (n : ℕ) :
    (((weightedSquareCoordinate ω n).toEReal) 0 : EReal) = 0 := by
  simp [weightedSquareCoordinate]

/-- The weighted quadratic coordinate function is pointwise nonnegative. -/
-- Proof sketch: rewrite the explicit formula and use the nonnegativity built into `ωₙ : NNReal`
-- together with `0 ≤ t²`.
theorem weightedSquareCoordinate_nonneg (ω : ℕ → NNReal) (n : ℕ) (t : ℝ) :
    0 ≤ weightedSquareCoordinate ω n t := by
  -- Rewrite the coordinate explicitly and bound each factor from below by `0`.
  rw [weightedSquareCoordinate]
  exact mul_nonneg (by exact_mod_cast (ω n).2) (sq_nonneg t)

/-- The `toEReal` lift of the weighted quadratic coordinate function attains its minimum at `0`. -/
-- Proof sketch: rewrite both sides through `Function.toEReal_apply` and use the real-valued
-- nonnegativity of `t ↦ ωₙ t²`.
theorem weightedSquareCoordinate_toEReal_nonneg (ω : ℕ → NNReal) (n : ℕ) (t : ℝ) :
    (((weightedSquareCoordinate ω n).toEReal) 0 : EReal) ≤
      (weightedSquareCoordinate ω n).toEReal t :=
  by
  -- After coercing through `toEReal`, the claim is exactly the real nonnegativity statement.
  rw [weightedSquareCoordinate_toEReal_zero]
  simp only [Function.toEReal_apply]
  exact_mod_cast weightedSquareCoordinate_nonneg ω n t

/-- Helper for Example 11 27: the scalar square map belongs to `Γ(ℝ)` after coercion to `EReal`.
-/
private theorem square_coe_mem_gamma : (fun t : ℝ ↦ ((t ^ 2 : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- Use the quadratic gap identity on `ℝ`, then cast the Jensen inequality to `EReal`.
    intro x y a ha0 ha1
    have hgap :
        a * x ^ 2 + (1 - a) * y ^ 2 - (a * x + (1 - a) * y) ^ 2 =
          a * (1 - a) * (x - y) ^ 2 := by
      ring
    have hgap_nonneg : 0 ≤ a * (1 - a) * (x - y) ^ 2 := by
      exact mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha1)) (sq_nonneg (x - y))
    have hineq :
        (a * x + (1 - a) * y) ^ 2 ≤ a * x ^ 2 + (1 - a) * y ^ 2 := by
      nlinarith
    have hsub_cast : (((1 - a : ℝ)) : EReal) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hineq_cast :
        ((((a * x + (1 - a) * y) ^ 2 : ℝ)) : EReal) ≤
          (((a * x ^ 2 + (1 - a) * y ^ 2 : ℝ)) : EReal) := by
      exact_mod_cast hineq
    have hsum_cast :
        (((a * x ^ 2 + (1 - a) * y ^ 2 : ℝ)) : EReal) =
          (a : EReal) * ((x ^ 2 : ℝ) : EReal) + (1 - a : EReal) * ((y ^ 2 : ℝ) : EReal) := by
      calc
        (((a * x ^ 2 + (1 - a) * y ^ 2 : ℝ)) : EReal) =
            ((((a * x ^ 2 : ℝ)) : EReal) + ((((1 - a) * y ^ 2 : ℝ)) : EReal)) := by
              rw [EReal.coe_add]
        _ =
            (a : EReal) * ((x ^ 2 : ℝ) : EReal) +
              (((1 - a : ℝ)) : EReal) * ((y ^ 2 : ℝ) : EReal) := by
              rw [EReal.coe_mul, EReal.coe_mul]
        _ = (a : EReal) * ((x ^ 2 : ℝ) : EReal) + (1 - a : EReal) * ((y ^ 2 : ℝ) : EReal) := by
              rw [hsub_cast]
    simpa [smul_eq_mul] using hineq_cast.trans_eq hsum_cast
  · -- Continuity of the square map yields lower semicontinuity after coercion to `EReal`.
    simpa using (continuous_coe_real_ereal.comp (continuous_id.pow 2)).lowerSemicontinuous

/-- A weighted square belongs to `Γ₀(ℝ)` after passage to the canonical
`Function.toEReal` bridge. -/
-- Proof sketch: identify `t ↦ ωₙ t²` with a nonnegative scalar multiple of the squared norm on
-- `ℝ`, combine convexity and lower semicontinuity of the quadratic function, and observe that the
-- value at `0` is finite.
theorem weightedSquareCoordinate_mem_gammaZero (ω : ℕ → NNReal) (n : ℕ) :
    (weightedSquareCoordinate ω n).toEReal ∈ Γ₀(ℝ) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  have hscaled :
      (fun t : ℝ ↦ ((ω n : ℝ) : EReal) * ((t ^ 2 : ℝ) : EReal)) ∈ gamma ℝ :=
    const_mul_mem_gamma_of_nonneg square_coe_mem_gamma (by exact_mod_cast (ω n).2)
  -- The weighted coordinate is exactly the nonnegative scalar multiple of the square.
  simpa [weightedSquareCoordinate] using hscaled

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The weighted squared-coordinate series from Example 11.27, realized through the canonical
nonnegative inner-product series owner from Example 9.13. -/
noncomputable def weightedHilbertBasisSquareSeries (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) :
    H → Set.Ioi (⊥ : EReal) :=
  innerProductSeriesFunction b (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
    (weightedSquareCoordinate_toEReal_zero ω)
    (weightedSquareCoordinate_toEReal_nonneg ω)

/-- Coercing the weighted Hilbert-basis square series back to `EReal` recovers the coordinate
family sum. -/
@[simp] theorem weightedHilbertBasisSquareSeries_apply (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (x : H) :
    (weightedHilbertBasisSquareSeries ω b x : EReal) =
      familySum (fun n y ↦ ((weightedSquareCoordinate ω n).toEReal ⟪y, b n⟫_ℝ : EReal)) x := by
  simp [weightedHilbertBasisSquareSeries, innerProductSeriesFunction_apply]

/-- The weighted Hilbert-basis square series belongs to `Γ₀(H)`. -/
-- Proof sketch: specialize Example 9.13 to the coordinate family `t ↦ ωₙ t²`, using the
-- coordinate-level `Γ₀(ℝ)` result together with the facts that the family vanishes at `0` and is
-- pointwise minimized there.
theorem weightedHilbertBasisSquareSeries_mem_gammaZero (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) :
    weightedHilbertBasisSquareSeries ω b ∈ Γ₀(H) := by
  simpa [weightedHilbertBasisSquareSeries] using
    innerProductSeriesFunction_mem_gammaZero b
      (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
      (fun n ↦ weightedSquareCoordinate_mem_gammaZero ω n)
      (weightedSquareCoordinate_toEReal_zero ω)
      (weightedSquareCoordinate_toEReal_nonneg ω)

/-- Helper for Example 11 27: finite sums of real numbers commute with coercion to `EReal`. -/
private theorem finset_sum_coe_real_local {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    (((Finset.sum s r : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((r i : ℝ) : EReal)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    -- Peel off one real summand and use the induction hypothesis on the remaining finite set.
    simp [Finset.sum_insert, ha, hs, EReal.coe_add]

section

omit [CompleteSpace H]

/-- Helper for Example 11 27: every finite partial sum of the weighted series is a real cast. -/
private theorem weightedHilbertBasisSquareSeries_partialSum_eq_coe_real
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (J : Finset ℕ) (x : H) :
    Finset.sum J (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) =
      (((Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) : ℝ)) : EReal) := by
  -- Rewrite each lifted coordinate term to the cast of the underlying real coordinate value.
  simpa only [Function.toEReal_apply, weightedSquareCoordinate_nonneg] using
    (finset_sum_coe_real_local J
      (fun i : ℕ ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ)).symm

/-- Helper for Example 11 27: the real weighted partial sums satisfy the Bessel-type bound coming
from the uniform weight bound `ω i ≤ M`. -/
-- Route correction: prove the finite estimate entirely in `ℝ` via Bessel's inequality, then cast
-- the finished bound to `EReal` only once.
private theorem weightedHilbertBasisSquareSeries_real_partialSum_le_norm_sq
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) {M : NNReal} (hM : ∀ i, ω i ≤ M)
    (J : Finset ℕ) (x : H) :
    Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) ≤
      (M : ℝ) * ‖x‖ ^ 2 := by
  have hM_nonneg : 0 ≤ (M : ℝ) := by
    exact_mod_cast M.2
  have hbessel : Finset.sum J (fun i ↦ ‖⟪b i, x⟫_ℝ‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    -- The orthonormal Hilbert basis gives the standard finite Bessel bound.
    simpa using b.orthonormal.sum_inner_products_le (x := x) (s := J)
  calc
    Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) ≤
        Finset.sum J (fun i ↦ (M : ℝ) * ‖⟪b i, x⟫_ℝ‖ ^ 2) := by
          -- Compare each coordinate term using the pointwise weight bound `ω i ≤ M`.
          refine Finset.sum_le_sum ?_
          intro i hi
          have hM_real : (ω i : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast hM i
          have hterm :
              weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ =
                (ω i : ℝ) * ‖⟪b i, x⟫_ℝ‖ ^ 2 := by
            rw [weightedSquareCoordinate, real_inner_comm]
            simp [sq_abs]
          rw [hterm]
          exact mul_le_mul_of_nonneg_right hM_real (by positivity)
    _ = (M : ℝ) * Finset.sum J (fun i ↦ ‖⟪b i, x⟫_ℝ‖ ^ 2) := by
          -- Pull the constant weight bound out of the finite sum.
          rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ‖x‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left hbessel hM_nonneg

/-- Helper for Example 11 27: a weighted finite partial sum is controlled by the weight supremum
times `‖x‖²`. -/
private theorem weightedHilbertBasisSquareSeries_partialSum_le_weightSup_mul_norm_sq
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) {M : NNReal} (hM : ∀ i, ω i ≤ M)
    (J : Finset ℕ) (x : H) :
    Finset.sum J (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) ≤
      (((M : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  -- Rewrite the finite `EReal` partial sum as the cast of the real one and apply the real bound.
  rw [weightedHilbertBasisSquareSeries_partialSum_eq_coe_real]
  exact_mod_cast weightedHilbertBasisSquareSeries_real_partialSum_le_norm_sq ω b hM J x

end

/-- Helper for Example 11 27: every finite partial sum is bounded above by the finite value of the
series at an effective-domain point. -/
private theorem weightedHilbertBasisSquareSeries_partialSum_le_toReal_value
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) {x : H}
    (hx : x ∈ effectiveDomain (weightedHilbertBasisSquareSeries ω b)) (J : Finset ℕ) :
    Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) ≤
      (weightedHilbertBasisSquareSeries ω b x : EReal).toReal := by
  by_cases hJ : J.Nonempty
  · have hnat : ¬ Finite ℕ := by
      intro hfinite
      exact hfinite.false
    have hpartial_le :
        Finset.sum J (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) ≤
          (weightedHilbertBasisSquareSeries ω b x : EReal) := by
      -- Compare the chosen nonempty partial sum directly with the `iSup` defining the family sum.
      rw [
        weightedHilbertBasisSquareSeries_apply,
        familySum_eq_iSup_nonemptyFinitePartialSums _ hnat
      ]
      exact le_iSup
        (fun K : {s : Finset ℕ // s.Nonempty} ↦
          Finset.sum (K : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)))
        ⟨J, hJ⟩
    have hx_top : (weightedHilbertBasisSquareSeries ω b x : EReal) ≠ ⊤ := by
      exact ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (weightedHilbertBasisSquareSeries ω b x : EReal) ≠ ⊥ := by
      exact ne_of_gt (weightedHilbertBasisSquareSeries ω b x).2
    rw [weightedHilbertBasisSquareSeries_partialSum_eq_coe_real] at hpartial_le
    rw [← EReal.coe_toReal hx_top hx_bot] at hpartial_le
    exact_mod_cast hpartial_le
  · -- The empty partial sum is `0`, so nonnegativity of the series value suffices.
    have hnonneg : (0 : EReal) ≤ (weightedHilbertBasisSquareSeries ω b x : EReal) := by
      classical
      have hnat : ¬ Finite ℕ := by
        intro hfinite
        exact hfinite.false
      rw [
        weightedHilbertBasisSquareSeries_apply,
        familySum_eq_iSup_nonemptyFinitePartialSums _ hnat
      ]
      let J₀ : {s : Finset ℕ // s.Nonempty} := ⟨{0}, by simp⟩
      have hJ₀ :
          (0 : EReal) ≤
            Finset.sum (J₀ : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) := by
        exact Finset.sum_nonneg fun i hi ↦ by
          simpa [weightedSquareCoordinate_toEReal_zero ω i] using
            weightedSquareCoordinate_toEReal_nonneg ω i ⟪x, b i⟫_ℝ
      exact hJ₀.trans <|
        le_iSup
          (fun K : {s : Finset ℕ // s.Nonempty} ↦
            Finset.sum (K : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)))
          J₀
    simpa [Finset.not_nonempty_iff_eq_empty.mp hJ] using EReal.toReal_nonneg hnonneg

/-- Helper for Example 11 27: inserting a distinguished index into a nonnegative partial sum does
not decrease it, so the `iSup` is unchanged when we restrict to nonempty finite sets containing
that index. -/
private theorem familySum_eq_iSup_nonemptyFinitePartialSums_containing
    (g : ℕ → EReal) (hg_nonneg : ∀ i, 0 ≤ g i) (n : ℕ) :
    (⨆ J : {s : Finset ℕ // s.Nonempty}, Finset.sum (J : Finset ℕ) g) =
      ⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s}, Finset.sum (J : Finset ℕ) g := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun J ↦ ?_
    by_cases hn : n ∈ (J : Finset ℕ)
    · -- If `J` already contains `n`, it appears unchanged in the restricted supremum.
      exact le_iSup
        (fun K : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} ↦ Finset.sum (K : Finset ℕ) g)
        ⟨J, J.2, hn⟩
    · -- Otherwise insert `n`; nonnegativity makes the larger partial sum dominate the old one.
      have hle :
          Finset.sum (J : Finset ℕ) g ≤ Finset.sum (insert n (J : Finset ℕ)) g := by
        rw [Finset.sum_insert hn]
        exact le_add_of_nonneg_left (hg_nonneg n)
      exact hle.trans <|
        le_iSup
          (fun K : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} ↦ Finset.sum (K : Finset ℕ) g)
          ⟨insert n (J : Finset ℕ), Finset.insert_nonempty _ _, Finset.mem_insert_self _ _⟩
  · refine iSup_le fun J ↦ ?_
    exact le_iSup
      (fun K : {s : Finset ℕ // s.Nonempty} ↦ Finset.sum (K : Finset ℕ) g)
      ⟨J, J.2.1⟩

/-- Helper for Example 11 27: each weighted coordinate satisfies Jensen's inequality. -/
private theorem weightedSquareCoordinate_convex_combination_le
    (ω : ℕ → NNReal) (n : ℕ) {a b α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    weightedSquareCoordinate ω n (α * a + (1 - α) * b) ≤
      α * weightedSquareCoordinate ω n a + (1 - α) * weightedSquareCoordinate ω n b := by
  have hsq :
      (α * a + (1 - α) * b) ^ 2 ≤ α * a ^ 2 + (1 - α) * b ^ 2 := by
    have hgap :
        α * a ^ 2 + (1 - α) * b ^ 2 - (α * a + (1 - α) * b) ^ 2 =
          α * (1 - α) * (a - b) ^ 2 := by
      ring
    have hnonneg : 0 ≤ α * (1 - α) * (a - b) ^ 2 := by
      exact mul_nonneg (mul_nonneg hα0 (sub_nonneg.mpr hα1)) (sq_nonneg (a - b))
    nlinarith
  -- Multiply the scalar-square Jensen inequality by the nonnegative weight `ω n`.
  rw [weightedSquareCoordinate, weightedSquareCoordinate, weightedSquareCoordinate]
  have hω_nonneg : 0 ≤ (ω n : ℝ) := by
    exact_mod_cast (ω n).2
  nlinarith

/-- Helper for Example 11 27: the distinguished coordinate contributes the exact strict-convexity
gap `ωₙ α (1-α) (a-b)^2`. -/
private theorem weightedSquareCoordinate_gap_identity
    (ω : ℕ → NNReal) (n : ℕ) (a b α : ℝ) :
    (ω n : ℝ) * α * (1 - α) * (a - b) ^ 2 +
        weightedSquareCoordinate ω n (α * a + (1 - α) * b) =
      α * weightedSquareCoordinate ω n a + (1 - α) * weightedSquareCoordinate ω n b := by
  -- Expand the quadratic identity and regroup terms.
  rw [weightedSquareCoordinate, weightedSquareCoordinate, weightedSquareCoordinate]
  ring

section

omit [CompleteSpace H]

/-- Helper for Example 11 27: every finite partial sum containing the distinguished index carries
the same Jensen gap coming from that coordinate. -/
private theorem weightedHilbertBasisSquareSeries_partialSum_add_gap_le
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) {x y : H} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} {J : Finset ℕ} (hnJ : n ∈ J) :
    let z := α • x + (1 - α) • y
    let δ := (ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2
    δ + Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪z, b i⟫_ℝ) ≤
      α * Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
        (1 - α) * Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) := by
  -- Isolate the strict `n`th coordinate and keep the remaining Jensen estimate as a finite sum.
  dsimp
  have hα0' : 0 ≤ α := hα0.le
  have hα1' : α ≤ 1 := hα1.le
  have hz_coord :
      ∀ i : ℕ,
        ⟪α • x + (1 - α) • y, b i⟫_ℝ =
          α * ⟪x, b i⟫_ℝ + (1 - α) * ⟪y, b i⟫_ℝ := by
    intro i
    -- Rewrite the midpoint coordinate by linearity in the first slot.
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hgap :
      (ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 +
          weightedSquareCoordinate ω n ⟪α • x + (1 - α) • y, b n⟫_ℝ =
        α * weightedSquareCoordinate ω n ⟪x, b n⟫_ℝ +
          (1 - α) * weightedSquareCoordinate ω n ⟪y, b n⟫_ℝ := by
    -- The chosen coordinate contributes the exact strict-convexity gap.
    rw [hz_coord n]
    exact weightedSquareCoordinate_gap_identity ω n ⟪x, b n⟫_ℝ ⟪y, b n⟫_ℝ α
  have herase :
      Finset.sum (J.erase n)
          (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ) ≤
        α * Finset.sum (J.erase n)
            (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
          (1 - α) * Finset.sum (J.erase n)
            (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) := by
    -- Every remaining coordinate only needs the ordinary Jensen inequality.
    calc
      Finset.sum (J.erase n)
          (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ) ≤
          Finset.sum (J.erase n) (fun i ↦
            α * weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ +
              (1 - α) * weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            rw [hz_coord i]
            exact weightedSquareCoordinate_convex_combination_le ω i hα0' hα1'
      _ =
          α * Finset.sum (J.erase n) (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
            (1 - α) * Finset.sum (J.erase n)
              (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- Reassemble the erased coordinate and the remaining partial sums.
  calc
    (ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 +
        Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ)
      =
        ((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 +
            weightedSquareCoordinate ω n ⟪α • x + (1 - α) • y, b n⟫_ℝ) +
          Finset.sum (J.erase n)
            (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ) := by
          rw [(Finset.sum_erase_add J
            (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ) hnJ).symm]
          ring
    _ ≤
        (α * weightedSquareCoordinate ω n ⟪x, b n⟫_ℝ +
            (1 - α) * weightedSquareCoordinate ω n ⟪y, b n⟫_ℝ) +
          (α * Finset.sum (J.erase n)
              (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
            (1 - α) * Finset.sum (J.erase n)
              (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ)) := by
          exact add_le_add hgap.le herase
    _ =
        α * (weightedSquareCoordinate ω n ⟪x, b n⟫_ℝ +
            Finset.sum (J.erase n) (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ)) +
          (1 - α) * (weightedSquareCoordinate ω n ⟪y, b n⟫_ℝ +
            Finset.sum (J.erase n) (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ)) := by
          ring
    _ =
        α * Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
          (1 - α) * Finset.sum J (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) := by
          rw [(Finset.sum_erase_add J
            (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) hnJ).symm,
            (Finset.sum_erase_add J
              (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) hnJ).symm]
          ring

end

/-- The weighted Hilbert-basis square series is finite everywhere, hence real-valued in the
textbook sense. -/
-- Proof sketch: use Parseval to bound the weighted coordinate sum by
-- `(sSup (Set.range ω)) * ‖x‖²`; a uniform upper bound on the weights then keeps every value
-- finite.
theorem weightedHilbertBasisSquareSeries_effectiveDomain_eq_univ (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_bdd : BddAbove (Set.range ω)) :
    effectiveDomain (weightedHilbertBasisSquareSeries ω b) = Set.univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    let M : NNReal := sSup (Set.range ω)
    have hM : ∀ i, ω i ≤ M := by
      intro i
      exact le_csSup hω_bdd (Set.mem_range_self i)
    have hnat : ¬ Finite ℕ := by
      intro hfinite
      exact hfinite.false
    rw [mem_effectiveDomain_iff, weightedHilbertBasisSquareSeries_apply,
      familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    have hbound :
        (⨆ J : {s : Finset ℕ // s.Nonempty},
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal))) ≤
          (((M : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal) := by
      -- Every nonempty finite partial sum is bounded by the same finite real constant.
      refine iSup_le fun J ↦ ?_
      exact weightedHilbertBasisSquareSeries_partialSum_le_weightSup_mul_norm_sq ω b hM J x
    exact lt_of_le_of_lt hbound (EReal.coe_lt_top _)

/-- The real-valued representative of the weighted Hilbert-basis square series is continuous on the
whole Hilbert space. -/
-- Proof sketch: first place the series in `Γ₀(H)`, then use the previous theorem to identify the
-- effective domain with `univ`, and finally apply the Chapter 8 continuity criterion for convex
-- functions on the interior of their effective domain.
theorem weightedHilbertBasisSquareSeries_continuous (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_bdd : BddAbove (Set.range ω)) :
    Continuous fun x : H ↦ ((weightedHilbertBasisSquareSeries ω b x : EReal)).toReal :=
  by
  let contPts : Set H :=
    {x | ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball x ρ ⊆ effectiveDomain (weightedHilbertBasisSquareSeries ω b) ∧
      ContinuousAt
        (fun y : H ↦ ((weightedHilbertBasisSquareSeries ω b y : EReal)).toReal) x}
  have hf := weightedHilbertBasisSquareSeries_mem_gammaZero ω b
  have hcont_eq :
      contPts = interior (effectiveDomain (weightedHilbertBasisSquareSeries ω b)) := by
    -- Corollary 8.39 applies because the series is in `Γ₀(H)`, hence lower semicontinuous.
    simpa [contPts] using
      continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
        (weightedHilbertBasisSquareSeries ω b)
        hf.2
        (Or.inr <| Or.inl hf.1)
  rw [continuous_iff_continuousAt]
  intro x
  have hx_cont : x ∈ contPts := by
    rw [hcont_eq, weightedHilbertBasisSquareSeries_effectiveDomain_eq_univ ω b hω_bdd]
    simp
  rcases hx_cont with ⟨ρ, hρ, hball, hcont⟩
  exact hcont

-- Proof sketch for the upcoming strict-convexity proof: for distinct `x` and `y`, choose a basis
-- coordinate on which they differ; the corresponding weighted square term is then strictly convex,
-- while all remaining terms are merely convex, so the summed Jensen inequality is strict.
section

omit [CompleteSpace H]

/-- Helper for Example 11 27: distinct vectors differ on some Hilbert-basis coordinate. -/
private theorem basis_coordinate_ne_of_ne
    (b : HilbertBasis ℕ ℝ H) {x y : H} (hxy : x ≠ y) :
    ∃ n : ℕ, ⟪x, b n⟫_ℝ ≠ ⟪y, b n⟫_ℝ := by
  by_contra hcoord
  push Not at hcoord
  apply hxy
  apply b.repr.injective
  ext n
  -- Convert equality of all coordinates into equality of the Hilbert-basis representations.
  simpa [HilbertBasis.repr_apply_apply, real_inner_comm] using hcoord n

end

/-- Helper for Example 11 27: adding a finite real shift commutes with `iSup` in `EReal`. -/
private theorem ereal_iSup_add_of_real_shift_local
    {ι : Sort*} (r : ℝ) (φ : ι → EReal) :
    (⨆ i, φ i + ((r : ℝ) : EReal)) =
      (⨆ i, φ i) + ((r : ℝ) : EReal) := by
  have hleft :
      (⨆ i, φ i + ((r : ℝ) : EReal)) ≤
        (⨆ i, φ i) + ((r : ℝ) : EReal) := by
    refine iSup_le fun i ↦ ?_
    -- Each shifted term is bounded by the shifted supremum.
    exact add_le_add (le_iSup φ i) le_rfl
  have hright :
      (⨆ i, φ i) + ((r : ℝ) : EReal) ≤
        (⨆ i, φ i + ((r : ℝ) : EReal)) := by
    have hsub :
        (⨆ i, φ i) ≤ (⨆ i, φ i + ((r : ℝ) : EReal)) - ((r : ℝ) : EReal) := by
      refine iSup_le fun i ↦ ?_
      exact (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot r))
        (Or.inl (EReal.coe_ne_top r))).2 (le_iSup (fun i ↦ φ i + ((r : ℝ) : EReal)) i)
    exact (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot r))
      (Or.inl (EReal.coe_ne_top r))).1 hsub
  exact le_antisymm hleft hright

/-- Helper for Example 11 27: the positive coordinate gap survives after passing from finite
partial sums to the full weighted Hilbert-basis series. -/
private theorem weightedHilbertBasisSquareSeries_add_gap_le_affine
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) {x y : H} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} :
    let z := α • x + (1 - α) • y
    let δ := (ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2
    (((δ : ℝ) : EReal) + (weightedHilbertBasisSquareSeries ω b z : EReal)) ≤
      (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
        (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) := by
  dsimp
  have hnat : ¬ Finite ℕ := by
    intro hfinite
    exact hfinite.false
  have hz_nonneg :
      ∀ i, (0 : EReal) ≤
        ((weightedSquareCoordinate ω i).toEReal ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal) := by
    intro i
    -- Every coordinate contribution is bounded below by its value at the origin.
    simpa [weightedSquareCoordinate_toEReal_zero ω i] using
      weightedSquareCoordinate_toEReal_nonneg ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ
  have hsub_cast : (((1 - α : ℝ)) : EReal) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hpartial :
      ∀ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        (((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal) +
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
                ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) ≤
          (α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) +
            (1 - α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal)) := by
    intro J
    have hcast :
        (((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2) +
            Finset.sum (J : Finset ℕ)
              (fun i ↦ weightedSquareCoordinate ω i
                ⟪α • x + (1 - α) • y, b i⟫_ℝ) : ℝ)) : EReal) ≤
          (((α * Finset.sum (J : Finset ℕ)
                (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ) +
              (1 - α) * Finset.sum (J : Finset ℕ)
                (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ) : ℝ)) : EReal) := by
      exact_mod_cast
        weightedHilbertBasisSquareSeries_partialSum_add_gap_le ω b hα0 hα1 J.2.2
    let sz : ℝ := Finset.sum (J : Finset ℕ)
      (fun i ↦ weightedSquareCoordinate ω i ⟪α • x + (1 - α) • y, b i⟫_ℝ)
    let sx : ℝ := Finset.sum (J : Finset ℕ)
      (fun i ↦ weightedSquareCoordinate ω i ⟪x, b i⟫_ℝ)
    let sy : ℝ := Finset.sum (J : Finset ℕ)
      (fun i ↦ weightedSquareCoordinate ω i ⟪y, b i⟫_ℝ)
    have hsum_z :
        Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
              ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal)) =
          ((sz : ℝ) : EReal) := by
      simpa [sz] using
        weightedHilbertBasisSquareSeries_partialSum_eq_coe_real
          ω b (J : Finset ℕ) (α • x + (1 - α) • y)
    have hsum_x :
        Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) =
          ((sx : ℝ) : EReal) := by
      simpa [sx] using weightedHilbertBasisSquareSeries_partialSum_eq_coe_real
        ω b (J : Finset ℕ) x
    have hsum_y :
        Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal)) =
          ((sy : ℝ) : EReal) := by
      simpa [sy] using weightedHilbertBasisSquareSeries_partialSum_eq_coe_real
        ω b (J : Finset ℕ) y
    have hleft :
        (((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2) + sz : ℝ)) : EReal) =
          ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal) +
            ((sz : ℝ) : EReal) := by
      rw [EReal.coe_add]
    have hright :
        (((α * sx + (1 - α) * sy : ℝ)) : EReal) =
          (α : EReal) * ((sx : ℝ) : EReal) + (1 - α : EReal) * ((sy : ℝ) : EReal) := by
      calc
        (((α * sx + (1 - α) * sy : ℝ)) : EReal) =
            ((((α * sx : ℝ)) : EReal) + ((((1 - α) * sy : ℝ)) : EReal)) := by
              rw [EReal.coe_add]
        _ = (α : EReal) * ((sx : ℝ) : EReal) + (((1 - α : ℝ)) : EReal) * ((sy : ℝ) : EReal) := by
              rw [EReal.coe_mul, EReal.coe_mul]
        _ = (α : EReal) * ((sx : ℝ) : EReal) + (1 - α : EReal) * ((sy : ℝ) : EReal) := by
              rw [hsub_cast]
    -- Rewrite the casted real inequality into the `EReal` partial-sum form used by the series.
    rw [hsum_z, hsum_x, hsum_y]
    rw [← hleft, ← hright]
    exact hcast
  have hz_step :
      (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
            ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal)) +
          ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal)) ≤
        (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
          (α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) +
            (1 - α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal))) := by
    refine iSup_le fun J ↦ ?_
    -- Every partial sum containing the chosen coordinate carries the same positive gap.
    simpa [add_comm] using (hpartial J).trans <|
      le_iSup
        (fun K : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} ↦
          (α : EReal) *
              Finset.sum (K : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) +
            (1 - α : EReal) *
              Finset.sum (K : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal)))
        J
  have hx_containing :
      (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal))) ≤
        (weightedHilbertBasisSquareSeries ω b x : EReal) := by
    rw [weightedHilbertBasisSquareSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    refine iSup_le fun J ↦ ?_
    exact le_iSup
      (fun K : {s : Finset ℕ // s.Nonempty} ↦
        Finset.sum (K : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)))
      ⟨J, J.2.1⟩
  have hy_containing :
      (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal))) ≤
        (weightedHilbertBasisSquareSeries ω b y : EReal) := by
    rw [weightedHilbertBasisSquareSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    refine iSup_le fun J ↦ ?_
    exact le_iSup
      (fun K : {s : Finset ℕ // s.Nonempty} ↦
        Finset.sum (K : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal)))
      ⟨J, J.2.1⟩
  have hweighted :
      (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        (α : EReal) *
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) +
          (1 - α : EReal) *
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal))) ≤
        (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
          (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) := by
    have hsup :=
      weighted_iSup_le_weighted_iSup
        (J := {s : Finset ℕ // s.Nonempty ∧ n ∈ s})
        (u := fun J ↦ Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)))
        (v := fun J ↦ Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal)))
        hα0.le (sub_nonneg.mpr hα1.le)
    exact hsup.trans <| add_le_add
      (mul_le_mul_of_nonneg_left hx_containing (by exact_mod_cast hα0.le))
      (mul_le_mul_of_nonneg_left hy_containing
        (by exact_mod_cast sub_nonneg.mpr hα1.le))
  have hmid_apply :
      (weightedHilbertBasisSquareSeries ω b (α • x + (1 - α) • y) : EReal) =
        (⨆ J : {s : Finset ℕ // s.Nonempty},
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
              ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) := by
    rw [weightedHilbertBasisSquareSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
  have hmid_containing :
      (⨆ J : {s : Finset ℕ // s.Nonempty},
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
            ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) =
        (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
              ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) := by
    exact familySum_eq_iSup_nonemptyFinitePartialSums_containing
      (g := fun i ↦ ((weightedSquareCoordinate ω i).toEReal
        ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))
      hz_nonneg n
  -- Rewrite the full series at the midpoint as the restricted `iSup`, shift the `iSup` by `δ`,
  -- and then apply the partial-sum gap estimate.
  calc
    ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal) +
        (weightedHilbertBasisSquareSeries ω b (α • x + (1 - α) • y) : EReal)
      =
        ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal) +
          (⨆ J : {s : Finset ℕ // s.Nonempty},
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
                ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) := by
          rw [hmid_apply]
    _ =
        ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal) +
          (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
                ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal))) := by
          rw [hmid_containing]
    _ =
        (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
              ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal)) +
            ((((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ)) : EReal)) := by
          rw [add_comm,
            ← ereal_iSup_add_of_real_shift_local
              (((ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 : ℝ))
              (fun J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} ↦
                Finset.sum (J : Finset ℕ)
                  (fun i ↦ ((weightedSquareCoordinate ω i).toEReal
                    ⟪α • x + (1 - α) • y, b i⟫_ℝ : EReal)))]
    _ ≤
        (⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
          (α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) +
            (1 - α : EReal) *
              Finset.sum (J : Finset ℕ)
                (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪y, b i⟫_ℝ : EReal))) :=
          hz_step
    _ ≤
        (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
          (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) :=
          hweighted

/-- Positive weights make the weighted Hilbert-basis square series strictly convex. -/
-- Proof sketch: for distinct `x` and `y`, choose a basis coordinate on which they differ; the
-- corresponding weighted square term is then strictly convex, while all remaining terms are merely
-- convex, so the summed Jensen inequality is strict.
theorem weightedHilbertBasisSquareSeries_strictlyConvex (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) :
    StrictlyConvex (weightedHilbertBasisSquareSeries ω b) := by
  intro x hx y hy hxy α hα0 hα1
  obtain ⟨n, hcoord_ne⟩ := basis_coordinate_ne_of_ne b hxy
  let z : H := α • x + (1 - α) • y
  let δ : ℝ := (ω n : ℝ) * α * (1 - α) * (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2
  have hδ_pos : 0 < δ := by
    -- The chosen basis coordinate contributes a genuinely positive quadratic gap.
    dsimp [δ]
    have hωn_pos : 0 < (ω n : ℝ) := by
      exact_mod_cast hω_pos n
    have hcoord_sq_pos : 0 < (⟪x, b n⟫_ℝ - ⟪y, b n⟫_ℝ) ^ 2 := by
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hcoord_ne)
    have hone_sub : 0 < 1 - α := sub_pos.mpr hα1
    positivity
  have hgap_le :
      (((δ : ℝ) : EReal) + (weightedHilbertBasisSquareSeries ω b z : EReal)) ≤
        (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
          (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) := by
    -- The finite partial-sum gap survives after taking the `familySum` supremum.
    simpa [z, δ] using
      weightedHilbertBasisSquareSeries_add_gap_le_affine
        (ω := ω) (b := b) (x := x) (y := y) (α := α) hα0 hα1 (n := n)
  have hx_top : (weightedHilbertBasisSquareSeries ω b x : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hy_top : (weightedHilbertBasisSquareSeries ω b y : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have htermx_top :
      (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl ?_, Or.inl (EReal.coe_ne_top α), Or.inr hx_top⟩
    exact_mod_cast hα0.le
  have htermy_top :
      (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl ?_,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hy_top⟩
    exact_mod_cast sub_nonneg.mpr hα1.le
  have hrhs_top :
      (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
        (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) ≠ ⊤ := by
    exact EReal.add_ne_top htermx_top htermy_top
  have hz_top : (weightedHilbertBasisSquareSeries ω b z : EReal) ≠ ⊤ := by
    intro hz_top
    have hleft_top :
        (((δ : ℝ) : EReal) + (weightedHilbertBasisSquareSeries ω b z : EReal)) = ⊤ := by
      rw [hz_top]
      exact EReal.add_top_of_ne_bot (by exact EReal.coe_ne_bot δ)
    have : (⊤ : EReal) ≤
        (α : EReal) * (weightedHilbertBasisSquareSeries ω b x : EReal) +
          (1 - α : EReal) * (weightedHilbertBasisSquareSeries ω b y : EReal) := by
      exact hleft_top ▸ hgap_le
    exact hrhs_top (le_antisymm le_top this)
  have hmid_lt :
      (weightedHilbertBasisSquareSeries ω b z : EReal) <
        (((δ : ℝ) : EReal) + (weightedHilbertBasisSquareSeries ω b z : EReal)) := by
    -- Adding a positive finite amount to an `EReal` value strictly increases it.
    have hδ_ereal_pos : (0 : EReal) < (δ : EReal) := by
      exact_mod_cast hδ_pos
    have hz_bot : (weightedHilbertBasisSquareSeries ω b z : EReal) ≠ ⊥ := by
      exact ne_of_gt (weightedHilbertBasisSquareSeries ω b z).2
    simpa using
      EReal.add_lt_add_of_lt_of_le hδ_ereal_pos (show
        (weightedHilbertBasisSquareSeries ω b z : EReal) ≤
          (weightedHilbertBasisSquareSeries ω b z : EReal) by rfl) hz_bot hz_top
  -- Combine the strict increase by `δ` with the affine upper bound.
  exact hmid_lt.trans_le hgap_le

/-- The weighted Hilbert-basis square series vanishes at the origin. -/
-- Proof sketch: each coordinate of `0` is `0`, so every coordinate term vanishes and the whole
-- family sum is `0`.
theorem weightedHilbertBasisSquareSeries_zero (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) :
    (weightedHilbertBasisSquareSeries ω b 0 : EReal) = 0 := by
  simpa [weightedHilbertBasisSquareSeries] using
    innerProductSeriesFunction_zero b (fun n ↦ (weightedSquareCoordinate ω n).toEReal)
      (weightedSquareCoordinate_toEReal_zero ω)
      (weightedSquareCoordinate_toEReal_nonneg ω)

section

omit [CompleteSpace H]

/-- Helper for Example 11 27: on a basis ray, every coordinate term vanishes except the chosen
index. -/
private theorem weightedSquareCoordinate_toEReal_inner_smul_basis
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (c : ℝ) (n i : ℕ) :
    ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal) =
      if i = n then (((ω n : ℝ) * c ^ 2 : ℝ) : EReal) else 0 := by
  by_cases hi : i = n
  · subst hi
    -- On the distinguished basis vector, the inner product collapses to the scalar `c`.
    have hself : ⟪b i, b i⟫_ℝ = (1 : ℝ) := by
      simpa using (orthonormal_iff_ite.mp b.orthonormal) i i
    have hinner : ⟪c • b i, b i⟫_ℝ = c := by
      calc
        ⟪c • b i, b i⟫_ℝ = c * ⟪b i, b i⟫_ℝ := by
          simpa using real_inner_smul_left (x := b i) (y := b i) (r := c)
        _ = c * 1 := by rw [hself]
        _ = c := by ring
    rw [if_pos rfl, hinner]
    simp [weightedSquareCoordinate, Function.toEReal_apply]
  · -- Off the distinguished index, orthonormality kills the coordinate.
    have hni : n ≠ i := by simpa [eq_comm] using hi
    have hinner : ⟪c • b n, b i⟫_ℝ = 0 := by
      calc
        ⟪c • b n, b i⟫_ℝ = c * ⟪b n, b i⟫_ℝ := by
          simpa using real_inner_smul_left (x := b n) (y := b i) (r := c)
        _ = 0 := by simp [b.orthonormal.inner_eq_zero hni]
    rw [if_neg hi, hinner]
    exact weightedSquareCoordinate_toEReal_zero ω i

end

/-- Helper for Example 11 27: restricting the series to a basis ray leaves only one coordinate
term. -/
private theorem weightedHilbertBasisSquareSeries_apply_smul_basis
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (c : ℝ) (n : ℕ) :
    (weightedHilbertBasisSquareSeries ω b (c • b n) : EReal) =
      (((ω n : ℝ) * c ^ 2 : ℝ) : EReal) := by
  classical
  let A : EReal := (((ω n : ℝ) * c ^ 2 : ℝ) : EReal)
  have hnat : ¬ Finite ℕ := by
    intro hfinite
    exact hfinite.false
  have hnonneg :
      ∀ i, (0 : EReal) ≤ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal) := by
    intro i
    -- Each coordinate term is bounded below by its value at the origin.
    simpa [weightedSquareCoordinate_toEReal_zero ω i] using
      weightedSquareCoordinate_toEReal_nonneg ω i ⟪c • b n, b i⟫_ℝ
  rw [weightedHilbertBasisSquareSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
  change
    (⨆ J : {s : Finset ℕ // s.Nonempty},
      Finset.sum (J : Finset ℕ)
        (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal))) = A
  rw [familySum_eq_iSup_nonemptyFinitePartialSums_containing
    (g := fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal))
    hnonneg n]
  have hpartial :
      ∀ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal)) = A := by
    intro J
    -- Once `n ∈ J`, the finite partial sum has exactly one surviving coordinate.
    calc
      Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal)) =
        Finset.sum (J : Finset ℕ) (fun i ↦ if i = n then A else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [A] using weightedSquareCoordinate_toEReal_inner_smul_basis ω b c n i
      _ = A := by
        simp [A, J.2.2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun J ↦ ?_
    rw [hpartial J]
  · let J₀ : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} := ⟨{n}, by simp⟩
    have hJ₀ :
        Finset.sum (J₀ : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal)) ≤
          ⨆ J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s},
            Finset.sum (J : Finset ℕ)
              (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal)) :=
      le_iSup
        (fun J : {s : Finset ℕ // s.Nonempty ∧ n ∈ s} ↦
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪c • b n, b i⟫_ℝ : EReal)))
        J₀
    rwa [hpartial J₀] at hJ₀

/-- Helper for Example 11 27: every weighted coordinate sum is globally nonnegative. -/
private theorem weightedHilbertBasisSquareSeries_nonneg
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (x : H) :
    (0 : EReal) ≤ (weightedHilbertBasisSquareSeries ω b x : EReal) := by
  classical
  have hnat : ¬ Finite ℕ := by
    intro hfinite
    exact hfinite.false
  rw [weightedHilbertBasisSquareSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
  have hpartial :
      ∀ J : {s : Finset ℕ // s.Nonempty},
        (0 : EReal) ≤
          Finset.sum (J : Finset ℕ)
            (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)) := by
    intro J
    -- Each coordinate term is bounded below by its value at `0`, namely `0`.
    exact Finset.sum_nonneg fun i hi ↦ by
      simpa [weightedSquareCoordinate_toEReal_zero ω i] using
        weightedSquareCoordinate_toEReal_nonneg ω i ⟪x, b i⟫_ℝ
  let J₀ : {s : Finset ℕ // s.Nonempty} := ⟨{0}, by simp⟩
  exact (hpartial J₀).trans <|
    le_iSup
      (fun J : {s : Finset ℕ // s.Nonempty} ↦
        Finset.sum (J : Finset ℕ)
          (fun i ↦ ((weightedSquareCoordinate ω i).toEReal ⟪x, b i⟫_ℝ : EReal)))
      J₀

/-- Helper for Example 11 27: the origin minimizes the weighted Hilbert-basis square series. -/
private theorem weightedHilbertBasisSquareSeries_zero_mem_argmin
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) :
    (0 : H) ∈ Argmin (weightedHilbertBasisSquareSeries ω b).asEReal := by
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro x
  -- The value at the origin is `0`, and every other value is nonnegative.
  calc
    ((weightedHilbertBasisSquareSeries ω b 0 : Set.Ioi (⊥ : EReal)) : EReal) = 0 :=
      weightedHilbertBasisSquareSeries_zero ω b
    _ ≤ (weightedHilbertBasisSquareSeries ω b x : EReal) :=
      weightedHilbertBasisSquareSeries_nonneg ω b x

/-- Positive weights force the origin to be the unique minimizer of the weighted Hilbert-basis
square series. -/
-- Proof sketch: every term in the defining series is nonnegative, so the origin gives the minimal
-- value `0`; if `x ≠ 0`, some basis coordinate is nonzero, and the positivity of the
-- corresponding weight makes the value strictly positive.
theorem weightedHilbertBasisSquareSeries_argmin_eq_singleton (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) :
    Argmin (weightedHilbertBasisSquareSeries ω b).asEReal =
      ({(0 : H)} : Set H) := by
  -- The source route is uniqueness of minimizers from strict convexity plus the
  -- known minimizer `0`.
  have hzero : (0 : H) ∈ Argmin (weightedHilbertBasisSquareSeries ω b).asEReal :=
    weightedHilbertBasisSquareSeries_zero_mem_argmin ω b
  have hdom :
      (effectiveDomain (weightedHilbertBasisSquareSeries ω b)).Nonempty := by
    refine ⟨0, ?_⟩
    -- The origin has the finite value `0`, so it lies in the effective domain.
    rw [mem_effectiveDomain_iff, weightedHilbertBasisSquareSeries_zero]
    simp
  have hsub :
      (Argmin (weightedHilbertBasisSquareSeries ω b).asEReal).Subsingleton :=
    argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex hdom
      (weightedHilbertBasisSquareSeries_strictlyConvex ω b hω_pos)
  exact hsub.eq_singleton_of_mem hzero

/-- The weighted Hilbert-basis square series takes the value `ωₙ` on the `n`th basis vector. -/
-- Proof sketch: all basis coordinates of `b n` vanish except the `n`th one, whose squared norm is
-- `1`.
theorem weightedHilbertBasisSquareSeries_apply_basis (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    (weightedHilbertBasisSquareSeries ω b (b n) : EReal) = (ω n : ℝ) := by
  -- Specialize the basis-ray evaluation to the scalar `c = 1`.
  simpa using weightedHilbertBasisSquareSeries_apply_smul_basis ω b 1 n

private noncomputable def weightedHilbertBasisSquareSeriesPositiveEscapeSequence
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) : ℕ → H :=
  fun n ↦ (Real.sqrt (ω n : ℝ))⁻¹ • b n

-- Along the positive-weight escape sequence `yₙ = bₙ / √ωₙ`, the weighted series has the
-- constant value `1`.
private theorem weightedHilbertBasisSquareSeries_apply_positiveEscapeSequence (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) (n : ℕ) :
    (weightedHilbertBasisSquareSeries ω b
        (weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b n) : EReal) = 1 := by
  -- Reduce to the basis-ray evaluation and simplify the scalar coefficient.
  rw [weightedHilbertBasisSquareSeriesPositiveEscapeSequence]
  rw [weightedHilbertBasisSquareSeries_apply_smul_basis]
  have hω_nonneg : 0 ≤ (ω n : ℝ) := by
    exact_mod_cast (ω n).2
  have hω_real_pos : 0 < (ω n : ℝ) := by
    exact_mod_cast hω_pos n
  have hsqrt_pos : 0 < Real.sqrt (ω n : ℝ) := Real.sqrt_pos.mpr hω_real_pos
  have hvalue : (ω n : ℝ) * (Real.sqrt (ω n : ℝ))⁻¹ ^ 2 = 1 := by
    field_simp [pow_two, hsqrt_pos.ne']
    nlinarith [Real.sq_sqrt hω_nonneg]
  exact_mod_cast hvalue

section

omit [CompleteSpace H]

/-- Helper for Example 11 27: the positive escape sequence has norm equal to the reciprocal square
root of the weight. -/
private theorem weightedHilbertBasisSquareSeriesPositiveEscapeSequence_norm
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n) (n : ℕ) :
    ‖weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b n‖ =
      (Real.sqrt (ω n : ℝ))⁻¹ := by
  rw [weightedHilbertBasisSquareSeriesPositiveEscapeSequence, norm_smul,
    b.orthonormal.norm_eq_one n, mul_one]
  have hsqrt_pos : 0 < Real.sqrt (ω n : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hω_pos n)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (ω n : ℝ) := hsqrt_pos.le
  have hinv_nonneg : 0 ≤ (Real.sqrt (ω n : ℝ))⁻¹ := inv_nonneg.mpr hsqrt_nonneg
  -- The basis vector has norm `1`, so the norm is just the positive scalar coefficient.
  rw [Real.norm_eq_abs]
  exact abs_of_nonneg hinv_nonneg

/-- Helper for Example 11 27: if the weights tend to `0` through positive values, then the norms
of the positive escape sequence tend to `+∞`. -/
private theorem weightedHilbertBasisSquareSeriesPositiveEscapeSequence_norm_tendsto_atTop
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n)
    (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ ‖weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b n‖)
      atTop
      atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro R
  let S : ℝ := max R 0 + 1
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (ω n : ℝ) < (1 / S) ^ 2 := by
    -- The weights eventually lie below the square of the reciprocal tail threshold.
    exact hω_tendsto.eventually_lt_const (by positivity : (0 : ℝ) < (1 / S) ^ 2)
  filter_upwards [hsmall] with n hn
  have hsqrt_pos : 0 < Real.sqrt (ω n : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hω_pos n)
  have hsqrt_lt : Real.sqrt (ω n : ℝ) < 1 / S := by
    exact (Real.sqrt_lt' (by positivity : 0 < 1 / S)).2 hn
  have hS_lt : S < (Real.sqrt (ω n : ℝ))⁻¹ := by
    -- Inverting the small square-root bound turns it into a large norm lower bound.
    have hdiv : 1 / (1 / S) < 1 / Real.sqrt (ω n : ℝ) :=
      one_div_lt_one_div_of_lt hsqrt_pos hsqrt_lt
    simpa [one_div, hS_pos.ne'] using hdiv
  have hR_lt_S : R < S := by
    dsimp [S]
    linarith [le_max_left R 0]
  rw [weightedHilbertBasisSquareSeriesPositiveEscapeSequence_norm ω b hω_pos n]
  exact le_of_lt (lt_trans hR_lt_S hS_lt)

/-- Helper for Example 11 27: the positive escape sequence tends to the norm-at-infinity filter.
-/
private theorem weightedHilbertBasisSquareSeriesPositiveEscapeSequence_tendsto_normFilter
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H) (hω_pos : ∀ n, 0 < ω n)
    (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    Tendsto (weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b) atTop
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := by
  -- The comap target is exactly the statement that the norms go to `+∞`.
  simpa [comap_norm_atTop] using
    weightedHilbertBasisSquareSeriesPositiveEscapeSequence_norm_tendsto_atTop
      ω b hω_pos hω_tendsto

end

/-- The weighted Hilbert-basis square series is not coercive. -/
-- Proof sketch: if some weight vanishes, the whole ray through the corresponding basis vector has
-- constant value `0`, so coercivity already fails. Otherwise every weight is positive, and the
-- positive-weight escape sequence `yₙ = bₙ / √ωₙ` has norm tending to `+∞` because `ωₙ → 0`
-- while the function value stays identically equal to `1`.
theorem weightedHilbertBasisSquareSeries_not_coercive (ω : ℕ → NNReal)
    (b : HilbertBasis ℕ ℝ H) (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    ¬ Coercive (weightedHilbertBasisSquareSeries ω b).asEReal := by
  rw [coercive_iff_tendsto_norm_atTop]
  intro hcoer
  by_cases hzero : ∃ n, ω n = 0
  · rcases hzero with ⟨n, hn⟩
    let ray : ℕ → H := fun m ↦ ((m : ℝ) + 1) • b n
    have hshift : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hray_norm :
        Tendsto (fun m ↦ ‖ray m‖) atTop atTop := by
      have hray_norm_eq : (fun m ↦ ‖ray m‖) = fun m : ℕ ↦ (m : ℝ) + 1 := by
        funext m
        have hm_nonneg : 0 ≤ (m : ℝ) + 1 := by
          positivity
        simp [ray, norm_smul, b.orthonormal.norm_eq_one n, Real.norm_of_nonneg hm_nonneg]
      rw [hray_norm_eq]
      exact hshift
    have hray :
        Tendsto ray atTop (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := by
      simpa [comap_norm_atTop] using hray_norm
    have hvalues :
        (weightedHilbertBasisSquareSeries ω b).asEReal ∘ ray = fun _ : ℕ ↦ (0 : EReal) := by
      ext m
      -- On the zero-weight basis ray, every value of the series is `0`.
      simpa [Function.comp, ray, hn] using
        weightedHilbertBasisSquareSeries_apply_smul_basis ω b ((m : ℝ) + 1) n
    have hconst :
        Tendsto (fun _ : ℕ ↦ (0 : EReal)) atTop (𝓝 (⊤ : EReal)) := by
      simpa [hvalues] using hcoer.comp hray
    rw [EReal.tendsto_nhds_top_iff_real] at hconst
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconst 1)
    exact (not_lt_of_ge (show (0 : EReal) ≤ 1 by norm_num)) (hN N le_rfl)
  · have hω_pos : ∀ n, 0 < ω n := by
      intro n
      have hω_ne : ω n ≠ 0 := fun h ↦ hzero ⟨n, h⟩
      exact lt_of_le_of_ne (ω n).2 hω_ne.symm
    have hseq :
        Tendsto (weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b) atTop
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) :=
      weightedHilbertBasisSquareSeriesPositiveEscapeSequence_tendsto_normFilter
        ω b hω_pos hω_tendsto
    have hvalues :
        (weightedHilbertBasisSquareSeries ω b).asEReal ∘
            weightedHilbertBasisSquareSeriesPositiveEscapeSequence ω b =
          fun _ : ℕ ↦ (1 : EReal) := by
      ext n
      -- Along the positive escape sequence, the series values stay constant equal to `1`.
      simpa [Function.comp] using
        weightedHilbertBasisSquareSeries_apply_positiveEscapeSequence ω b hω_pos n
    have hconst :
        Tendsto (fun _ : ℕ ↦ (1 : EReal)) atTop (𝓝 (⊤ : EReal)) := by
      simpa [hvalues] using hcoer.comp hseq
    rw [EReal.tendsto_nhds_top_iff_real] at hconst
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconst 2)
    exact (not_lt_of_ge (show (1 : EReal) ≤ 2 by norm_num)) (hN N le_rfl)

omit [CompleteSpace H] in
/-- A Hilbert basis does not converge strongly to the origin. -/
-- Proof sketch: apply the orthonormal-sequence result from Example 2.32.1 to the orthonormal
-- family underlying the Hilbert basis.
theorem hilbertBasis_not_tendsto_zero_strongly (b : HilbertBasis ℕ ℝ H) :
    ¬ Tendsto b atTop (𝓝 (0 : H)) := by
  -- The Hilbert basis is an orthonormal sequence, so Example 2.32.1 applies directly.
  simpa using orthonormal_sequence_not_tendsto_zero_strongly b b.orthonormal

/-- Example 11 27: if `ωₙ → 0`, then the Hilbert basis itself is a minimizing sequence for the
weighted squared-coordinate series, and it converges weakly to `0`. -/
-- Proof sketch: the coordinate computation gives `f (b n) = ωₙ`, so `ωₙ → 0 = f 0` shows that
-- `b` is a minimizing sequence. Weak convergence follows from the orthonormal-sequence theorem
-- from Example 2.32.1 applied to the basis family.
theorem weightedHilbertBasisSquareSeries_basis_isMinimizingSequence_and_tendsto_weakly
    (ω : ℕ → NNReal) (b : HilbertBasis ℕ ℝ H)
    (hω_tendsto : Tendsto (fun n ↦ (ω n : ℝ)) atTop (𝓝 0)) :
    IsMinimizingSequence (weightedHilbertBasisSquareSeries ω b).asEReal b ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (b n)) atTop (𝓝 (0 : WeakSpace ℝ H)) := by
  refine ⟨?_, orthonormal_sequence_tendsto_zero_weakly b b.orthonormal⟩
  refine ⟨?_, ?_⟩
  · intro n
    -- The basis value is the finite real number `ωₙ`, so every term lies in the domain.
    simpa [mem_dom_iff] using
      (show ((weightedHilbertBasisSquareSeries ω b (b n) : EReal) < ⊤) by
        rw [weightedHilbertBasisSquareSeries_apply_basis]
        exact EReal.coe_lt_top (ω n : ℝ))
  · have hsInf_zero :
        sInf (Set.range (weightedHilbertBasisSquareSeries ω b).asEReal) = (0 : EReal) := by
      -- The origin is a global minimizer, so the infimum equals the value `f 0 = 0`.
      calc
        sInf (Set.range (weightedHilbertBasisSquareSeries ω b).asEReal) =
            ((weightedHilbertBasisSquareSeries ω b 0 : Set.Ioi (⊥ : EReal)) : EReal) := by
              symm
              exact (mem_argmin_iff_eq_sInf.mp
                (weightedHilbertBasisSquareSeries_zero_mem_argmin ω b))
        _ = 0 := weightedHilbertBasisSquareSeries_zero ω b
    have hω_tendsto_ereal : Tendsto (fun n ↦ ((ω n : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
      simpa using (continuous_coe_real_ereal.continuousAt.tendsto.comp hω_tendsto)
    have hvalues :
        (weightedHilbertBasisSquareSeries ω b).asEReal ∘ b =
          fun n ↦ ((ω n : ℝ) : EReal) := by
      ext n
      simpa [Function.comp] using weightedHilbertBasisSquareSeries_apply_basis ω b n
    -- Rewrite the function values on the basis sequence using the basis-ray evaluation.
    rw [hvalues, hsInf_zero]
    exact hω_tendsto_ereal

/- The minimizing Hilbert-basis sequence from Example 11.27 does not converge strongly to `0`;
this is exactly `hilbertBasis_not_tendsto_zero_strongly`. -/
recall hilbertBasis_not_tendsto_zero_strongly

end

end ERealFunction
