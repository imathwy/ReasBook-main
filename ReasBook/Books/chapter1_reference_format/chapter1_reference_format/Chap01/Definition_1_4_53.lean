import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-- To compare two norms on the same vector space, we bundle a norm as a definite seminorm.
This is a bridge/view over the chapter's canonical single-norm owner `NormedSpace.Core`. -/
abbrev VectorNorm (K : Type u) (V : Type v) [NormedField K] [AddCommGroup V] [Module K V] :=
  { p : Seminorm K V // ∀ x : V, p x = 0 → x = 0 }

namespace VectorNorm

variable {K : Type u} {V : Type v} [NormedField K] [AddCommGroup V] [Module K V]

instance : CoeFun (VectorNorm K V) fun _ ↦ V → ℝ :=
  ⟨fun p ↦ p.1⟩

/-- A bundled vector norm vanishes only at zero. -/
theorem eq_zero_of_map_eq_zero (p : VectorNorm K V) {x : V} : p x = 0 → x = 0 :=
  p.2 x

/-- A bundled vector norm recovers the textbook norm axioms from Definition 1.4.52. -/
def toNormedSpaceCore (p : VectorNorm K V) : let _ : Norm V := ⟨p.1⟩; NormedSpace.Core K V := by
  letI : Norm V := ⟨p.1⟩
  refine
    { toCore :=
        { norm_nonneg := apply_nonneg p.1
          norm_smul := map_smul_eq_mul p.1
          norm_triangle := map_add_le_add p.1 }
      norm_eq_zero_iff := ?_ }
  intro x
  constructor
  · exact p.eq_zero_of_map_eq_zero
  · intro hx
    exact hx ▸ p.1.map_zero'

/-- The normed additive-group structure canonically induced by a bundled vector norm. -/
abbrev toNormedAddCommGroup (p : VectorNorm K V) :
    let _ : Norm V := ⟨p.1⟩
    NormedAddCommGroup V := by
  letI : Norm V := ⟨p.1⟩
  exact NormedAddCommGroup.ofCore p.toNormedSpaceCore

/-- The normed-space structure canonically induced by a bundled vector norm. -/
abbrev toNormedSpace (p : VectorNorm K V) :
    let _ : Norm V := ⟨p.1⟩
    let _ : NormedAddCommGroup V := p.toNormedAddCommGroup
    NormedSpace K V := by
  letI : Norm V := ⟨p.1⟩
  letI : NormedAddCommGroup V := p.toNormedAddCommGroup
  exact NormedSpace.ofCore p.toNormedSpaceCore

/-- Definition 1.4.53: two norms on a `K`-vector space `V` are equivalent when they induce the
same topology; equivalently, there exists a constant `C > 1` such that
`C⁻¹ * ‖x‖₁ ≤ ‖x‖₂ ≤ C * ‖x‖₁` for every `x`. Here we formalize equivalence by this uniform
two-sided comparison. -/
def Equivalent (p q : VectorNorm K V) : Prop :=
  ∃ C : ℝ, 1 < C ∧ ∀ x : V, C⁻¹ * p x ≤ q x ∧ q x ≤ C * p x

end VectorNorm
