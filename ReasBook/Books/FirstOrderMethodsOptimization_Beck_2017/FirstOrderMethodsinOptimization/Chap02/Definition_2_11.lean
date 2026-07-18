import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SMul ℝ E] {S : Set E}

/-- Definition 2.11: A subset is a cone if it is closed under multiplication by nonnegative real
scalars. -/
def IsNonnegativeCone (S : Set E) : Prop :=
  ∀ ⦃a : NNReal⦄ ⦃x : E⦄, x ∈ S → a • x ∈ S

/-- A cone carries the canonical bundled `NNReal`-subaction on its underlying set. -/
def IsNonnegativeCone.toSubMulAction (hS : IsNonnegativeCone S) : SubMulAction NNReal E where
  carrier := S
  smul_mem' := fun _ _ hx ↦ hS hx

@[simp] theorem mem_toSubMulAction (hS : IsNonnegativeCone S) {x : E} :
    x ∈ hS.toSubMulAction ↔ x ∈ S :=
  Iff.rfl

-- Proof sketch: reinterpret nonnegative real scalars as `ℝ≥0` and use `NNReal.smul_def` to pass
-- between the canonical restricted scalar action and the textbook `0 ≤ a` formulation.
/-- A set is a cone exactly when every nonnegative scalar multiple of each of its points remains
in the set. -/
theorem isCone_iff_smul_mem :
    IsNonnegativeCone S ↔ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : E⦄, x ∈ S → a • x ∈ S := by
  constructor
  · intro hS a ha x hx
    change ((⟨a, ha⟩ : NNReal) • x) ∈ S
    exact hS hx
  · intro hS
    rintro ⟨a, ha⟩ x hx
    simpa [NNReal.smul_def] using hS ha hx
