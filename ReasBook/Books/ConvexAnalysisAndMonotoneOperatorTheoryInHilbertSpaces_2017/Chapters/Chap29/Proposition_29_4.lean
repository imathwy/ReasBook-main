import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.WeakDual
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap24.Example_24_34

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open ERealFunction
open scoped InnerProductSpace Topology

noncomputable section

universe u

section

variable {I : Type u}

-- Semantic recall: `lean_leansearch` surfaced the ambient `PiLp`/weak-space owners but no direct
-- interval-box projector statement. The local Chapter 24 precedents are `projIccReal` for scalar
-- interval clamps on `ℝ` and `toWeakSpace`-based sequence statements for weak sequential
-- continuity.

/-- The coordinatewise closed interval box `∏ᵢ [aᵢ, bᵢ]` inside `ℓ²(I, ℝ)`. -/
def l2IntervalBox (a b : I → ℝ) : Set (ℓ²(I, ℝ)) :=
  {x | ∀ i, x i ∈ Set.Icc (a i) (b i)}

/-- Membership in the interval box `∏ᵢ [aᵢ, bᵢ]` is exactly coordinatewise membership. -/
@[simp] theorem mem_l2IntervalBox_iff
    (a b : I → ℝ) (x : ℓ²(I, ℝ)) :
    x ∈ l2IntervalBox a b ↔ ∀ i, x i ∈ Set.Icc (a i) (b i) :=
  Iff.rfl

/-- The coordinatewise interval clamps again form an `ℓ²(I, ℝ)` vector. -/
theorem memℓp_projIcc
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i)
    (x : ℓ²(I, ℝ)) :
    Memℓp (fun i ↦ projIccReal (le_trans (ha0 i) (h0b i)) (x i)) 2 := sorry

/-- The coordinatewise projector onto the interval box `∏ᵢ [aᵢ, bᵢ]`. -/
def l2IntervalProjection
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i) :
    ℓ²(I, ℝ) → ℓ²(I, ℝ) :=
  fun x ↦
    ⟨
      fun i ↦ projIccReal (le_trans (ha0 i) (h0b i)) (x i),
      memℓp_projIcc a b ha0 h0b x
    ⟩

/-- Evaluating the interval-box projector at coordinate `i` returns the clamp onto `[aᵢ, bᵢ]`. -/
@[simp] theorem l2IntervalProjection_apply
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i)
    (x : ℓ²(I, ℝ))
    (i : I) :
    l2IntervalProjection a b ha0 h0b x i =
      projIccReal (le_trans (ha0 i) (h0b i)) (x i) :=
  rfl

/-- The coordinatewise interval projector lands in the interval box. -/
@[simp] theorem l2IntervalProjection_mem
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i)
    (x : ℓ²(I, ℝ)) :
    l2IntervalProjection a b ha0 h0b x ∈ l2IntervalBox a b := by
  intro i
  rw [l2IntervalProjection_apply]
  rw [projIccReal_apply]
  exact (Set.projIcc (a i) (b i) (le_trans (ha0 i) (h0b i)) (x i)).2

/-- The interval box is nonempty when each coordinate interval contains `0`. -/
theorem l2IntervalBox_nonempty
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i) :
    (l2IntervalBox a b).Nonempty := sorry

/-- The coordinatewise closed interval box is a closed subset of `ℓ²(I, ℝ)`. -/
theorem l2IntervalBox_isClosed
    (a b : I → ℝ) :
    IsClosed (l2IntervalBox a b) := sorry

/-- The coordinatewise closed interval box is a convex subset of `ℓ²(I, ℝ)`. -/
theorem l2IntervalBox_convex
    (a b : I → ℝ) :
    Convex ℝ (l2IntervalBox a b) := sorry

/-- The interval box `∏ᵢ [aᵢ, bᵢ]` is a Chebyshev set in `ℓ²(I, ℝ)`. -/
theorem l2IntervalBox_isChebyshev
    (a b : I → ℝ)
    (ha0 : ∀ i, a i ≤ 0)
    (h0b : ∀ i, 0 ≤ b i) :
    IsChebyshev (l2IntervalBox a b) :=
  isChebyshev_of_nonempty_isClosed_convex
    (l2IntervalBox_nonempty a b ha0 h0b)
    (l2IntervalBox_isClosed a b)
    (l2IntervalBox_convex a b)

section

variable (a b : I → ℝ)
variable (ha0 : ∀ i, a i ≤ 0)
variable (h0b : ∀ i, 0 ≤ b i)

local notation "C" => l2IntervalBox a b
local notation "P_C" => P[C, l2IntervalBox_isChebyshev a b ha0 h0b]

/-- Proposition 29.4 (1): for the interval box `C = ∏ᵢ [aᵢ, bᵢ]` in `ℓ²(I, ℝ)` with `0 ∈ [aᵢ, bᵢ]`
for every `i`, the metric projection acts coordinatewise:
`P[C, hC_cheb] (ξᵢ)ᵢ = (P_[aᵢ,bᵢ] ξᵢ)ᵢ`. -/
theorem projectionPoint_l2IntervalBox_eq_coordinatewise_projIcc
    (x : ℓ²(I, ℝ)) :
    P_C x = l2IntervalProjection a b ha0 h0b x := sorry

/-- Proposition 29.4 (2): for the interval box `C = ∏ᵢ [aᵢ, bᵢ]` in `ℓ²(I, ℝ)` with `0 ∈ [aᵢ, bᵢ]`
for every `i`, weak convergence of a sequence implies weak convergence of its projected sequence. -/
theorem projectionPoint_l2IntervalBox_tendsto_toWeakSpace
    ⦃xSeq : ℕ → ℓ²(I, ℝ)⦄
    ⦃x : ℓ²(I, ℝ)⦄
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) x))) :
    Tendsto (fun n ↦ toWeakSpace ℝ (ℓ²(I, ℝ)) (P_C (xSeq n))) atTop
      (𝓝 (toWeakSpace ℝ (ℓ²(I, ℝ)) (P_C x))) := sorry

end

end

end
