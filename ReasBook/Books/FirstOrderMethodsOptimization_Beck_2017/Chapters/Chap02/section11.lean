import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_11 (from Chap02) -/
universe u

variable {E : Type u} [SMul ℝ E] {S : Set E}

/-- Definition 2.11: A subset is a cone if it is closed under multiplication by nonnegative real
scalars. -/
def IsCone (S : Set E) : Prop :=
  ∀ ⦃a : NNReal⦄ ⦃x : E⦄, x ∈ S → a • x ∈ S

/-- A cone carries the canonical bundled `NNReal`-subaction on its underlying set. -/
def IsCone.toSubMulAction (hS : IsCone S) : SubMulAction NNReal E where
  carrier := S
  smul_mem' := fun _ _ hx ↦ hS hx

@[simp] theorem mem_toSubMulAction (hS : IsCone S) {x : E} :
    x ∈ hS.toSubMulAction ↔ x ∈ S :=
  Iff.rfl

-- Proof sketch: reinterpret nonnegative real scalars as `ℝ≥0` and use `NNReal.smul_def` to pass
-- between the canonical restricted scalar action and the textbook `0 ≤ a` formulation.
/-- A set is a cone exactly when every nonnegative scalar multiple of each of its points remains
in the set. -/
theorem isCone_iff_smul_mem :
    IsCone S ↔ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : E⦄, x ∈ S → a • x ∈ S := by
  constructor
  · intro hS a ha x hx
    change ((⟨a, ha⟩ : NNReal) • x) ∈ S
    exact hS hx
  · intro hS
    rintro ⟨a, ha⟩ x hx
    simpa [NNReal.smul_def] using hS ha hx

/-! ### Theorem_2_11 (from Chap02) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: apply `geometric_hahn_banach_closed_point` to the closed convex set `C` and the
-- point `y ∉ C`, obtaining a continuous linear functional `p` and a real number `α` with
-- `p x < α < p y` for all `x ∈ C`. Choose `x₀ ∈ C`; if `p = 0`, then `0 < α < 0`, impossible, so
-- `p ≠ 0`. Finally weaken the strict inequality on `C` to `p x ≤ α`.
/-- Theorem 2.11: strict separation theorem. A nonempty closed convex set in a real inner product
space and a point outside it can be strictly separated by a nonzero continuous linear functional. -/
theorem strict_separation_closed_convex_point {C : Set E} {y : E} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hy : y ∉ C) :
    ∃ p : StrongDual ℝ E, p ≠ 0 ∧ ∃ α : ℝ, p y > α ∧ ∀ x ∈ C, p x ≤ α := by
  obtain ⟨p, α, hpC, hpy⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hy
  obtain ⟨x₀, hx₀⟩ := hC_nonempty
  refine ⟨p, ?_, α, hpy, fun x hx ↦ (hpC x hx).le⟩
  intro hp0
  have hx₀_lt : (0 : ℝ) < α := by simpa [hp0] using hpC x₀ hx₀
  have hα_lt : α < 0 := by simpa [hp0] using hpy
  exact (not_lt_of_ge hx₀_lt.le hα_lt).elim

end
