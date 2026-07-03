

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_11 (from Chap03) -/
noncomputable section

section

variable {m n p : ℕ}

local notation "DualMultiplierSpace" => (Fin m → ℝ) × (Fin p → ℝ)

/- Definition 3.11 is a `source-facing` item in the affine-constrained duality API. The
`core/canonical` owners are Chapter 2's `effective_domain` for finite-valued loci and the chapter
declarations `lagrangianDualObjective` and `dualObjectiveValues` from `Theorem_3_24`. This file
therefore keeps only the source-facing `dom (-q)` and dual-value views, with `dom (-q)` defined
through the owner `effective_domain` rather than storing the derived lower-finiteness condition as
primitive data. -/
recall effective_domain
recall lagrangianDualObjective
recall dualObjectiveValues

variable (X : Set (Fin n → ℝ))
variable (f : (Fin n → ℝ) → ℝ)
variable (g : (Fin n → ℝ) → Fin m → ℝ)
variable (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)

local notation "q" => lagrangianDualObjective X f g A b

/-- The effective domain `dom (-q)` consists of the multiplier pairs whose inequality multiplier
is coordinatewise nonnegative and whose dual objective is strictly greater than `-∞`. -/
def affine_constrained_dual_effective_domain :
    Set DualMultiplierSpace :=
  {yz : DualMultiplierSpace | ∀ i : Fin m, 0 ≤ yz.1 i} ∩
    effective_domain (fun yz : DualMultiplierSpace ↦ -q yz.1 yz.2)

-- Proof sketch: unfold `affine_constrained_dual_effective_domain` to the owner
-- `effective_domain (-q)` and rewrite `-q(y, z) < ⊤` as `q(y, z) ≠ ⊥`, equivalently
-- `⊥ < q(y, z)`.
/-- A multiplier pair belongs to `dom (-q)` exactly when `y` is coordinatewise nonnegative and the
dual objective at `(y, z)` is greater than `-∞`. -/
@[simp] theorem mem_affine_constrained_dual_effective_domain
    (yz : DualMultiplierSpace) :
    yz ∈ affine_constrained_dual_effective_domain X f g A b ↔
      (∀ i : Fin m, 0 ≤ yz.1 i) ∧ ⊥ < q yz.1 yz.2 := by
  simp [affine_constrained_dual_effective_domain, effective_domain, lt_top_iff_ne_top,
    EReal.neg_eq_top_iff, bot_lt_iff_ne_bot]

/-- The dual optimal value is the supremum of the attained dual objective values. -/
def affine_constrained_dual_problem_value : EReal :=
  sSup (dualObjectiveValues X f g A b)

-- Proof sketch: values attained on `dom (-q)` are attained dual objective values, so the
-- `dom (-q)` supremum is bounded above by `sSup (dualObjectiveValues X f g A b)`. Conversely, any
-- attained value is either `⊥`, which is automatically below that supremum, or it comes from a
-- multiplier pair in `dom (-q)`.
/-- The textbook `sup_{(y,z) ∈ dom (-q)} q(y,z)` presentation of the dual value agrees with the
canonical supremum over the owner set `dualObjectiveValues`. -/
theorem affine_constrained_dual_problem_value_eq_sSup_image_effective_domain :
    affine_constrained_dual_problem_value X f g A b =
      sSup
        ((fun yz : DualMultiplierSpace ↦ q yz.1 yz.2) ''
          affine_constrained_dual_effective_domain X f g A b) := by
  rw [affine_constrained_dual_problem_value]
  apply le_antisymm
  · refine sSup_le ?_
    intro qValue hqValue
    rcases hqValue with ⟨y, z, hy, rfl⟩
    by_cases hbot : q y z = ⊥
    · simp [hbot]
    · exact le_sSup <| by
        refine ⟨(y, z), ?_, rfl⟩
        exact (mem_affine_constrained_dual_effective_domain X f g A b (y, z)).2
          ⟨hy, bot_lt_iff_ne_bot.mpr hbot⟩
  · refine sSup_le ?_
    intro qValue hqValue
    rcases hqValue with ⟨yz, hyz, rfl⟩
    exact le_sSup <| by
      exact ⟨yz.1, yz.2, hyz.1, rfl⟩

end

/-! ### Proposition_3_11 (from Chap03) -/
universe u v

open Filter
open InnerProductSpace (toDual)
open scoped Topology RealInnerProductSpace Gradient

noncomputable section

section

variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Finite ι] [Nonempty ι]

/- Proposition 3.11 is a `bridge/view` item on the chapter owner layer of finite nonempty index
types: the owner max rule is `directional_derivative_iSup_eq_iSup_active_indices`, and the owner
calculus bridges are `has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt` and
`directional_derivative_eq_of_mem_interior_of_hasFDerivAt`, organized around the chapter owner
predicate `is_differentiable_at`. The active-indexed gradient pairing formula is therefore derived
from those owner declarations rather than from a second local `Fin`-specific wrapper or a
proof-artifact `effective_domain`/global-`≠ ⊥` interface. -/
recall finite_domain
recall is_differentiable_at
recall directional_derivative_iSup_eq_iSup_active_indices
recall directional_derivative_eq_of_mem_interior_of_hasFDerivAt

-- Proof sketch: unpack `is_differentiable_at (f i) x` into the owner interior-finite-domain
-- hypothesis and differentiability of `y ↦ (f i y).toReal`. The former gives the local
-- finiteness needed to construct the directional derivative of each summand, and the latter
-- identifies that derivative with the inner product of the gradient against `d`. Applying the
-- finite-family active-index max rule and substituting these values yields the formula.
/-- Proposition 3.11: if each function in a finite family of extended-real-valued functions is
differentiable at `x` in the sense of Definition 3.10, then the directional derivative of the
pointwise maximum is the maximum of the active gradient pairings `⟪∇ f_i(x), d⟫`. -/
theorem directional_derivative_pointwise_max_eq_sup'_active_gradient_pairings
    (f : ι → E → EReal) (x d : E) (hdiff : ∀ i : ι, is_differentiable_at (f i) x) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
        ((⟪∇ (fun y ↦ (f i y).toReal) x, d⟫ : ℝ) : EReal) := by
  have hxfinite : ∀ i : ι, x ∈ interior (finite_domain (f i)) := fun i ↦ (hdiff i).1
  have hderiv :
      ∀ i : ι,
        HasFDerivAt (fun y ↦ (f i y).toReal)
          (toDual ℝ E (∇ (fun y ↦ (f i y).toReal) x)) x := by
    intro i
    exact (hdiff i).2.hasGradientAt.hasFDerivAt
  have hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal) := by
    intro i
    have hline :
        HasLineDerivAt ℝ (fun y ↦ (f i y).toReal)
          (⟪∇ (fun y ↦ (f i y).toReal) x, d⟫) x d := by
      simpa using (hderiv i).hasLineDerivAt d
    exact
      ⟨⟪∇ (fun y ↦ (f i y).toReal) x, d⟫,
        has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt (hxfinite i) hline⟩
  calc
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d
        = iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
            directional_derivative (f i) x d :=
      directional_derivative_iSup_eq_iSup_active_indices f x d hdir
    _ = iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
          ((⟪∇ (fun y ↦ (f i y).toReal) x, d⟫ : ℝ) : EReal) := by
      congr with i
      simpa using
        directional_derivative_eq_of_mem_interior_of_hasFDerivAt
          (hxfinite i) (hderiv i) d

end

/-! ### Theorem_3_11 (from Chap03) -/
/- Theorem 3.11 is recall-only in the chapter convex-analysis API. Its source-facing mathematical
content is already owned by
`directional_derivative_isGreatest_subgradient_pairings_at_interior_point` in
`Definition_3_9`, stated at the chapter owner abstraction `subdifferential`; this file therefore
reuses that exact theorem instead of keeping a second `StrongDual`-flavored wrapper API. -/
recall directional_derivative_isGreatest_subgradient_pairings_at_interior_point
