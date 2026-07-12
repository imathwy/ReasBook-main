import Mathlib.RepresentationTheory.Submodule
import Mathlib.RepresentationTheory.Subrepresentation

namespace Subrepresentation

section

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable {ρ : Representation k G V}

/-- A bundled subrepresentation defines an invariant submodule. -/
theorem toSubmodule_mem_invtSubmodule (W : Subrepresentation ρ) :
    W.toSubmodule ∈ ρ.invtSubmodule := by
  simpa [Representation.mem_invtSubmodule,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using W.apply_mem_toSubmodule

/-- Repackage an invariant submodule as a bundled subrepresentation. -/
def ofInvtSubmodule (W : ρ.invtSubmodule) : Subrepresentation ρ where
  toSubmodule := W
  apply_mem_toSubmodule g v hv := by
    have hW : (W : Submodule k V) ∈ Module.End.invtSubmodule (ρ g) :=
      (ρ.mem_invtSubmodule.mp W.property) g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hW
    exact hW v hv

@[simp] theorem toSubmodule_ofInvtSubmodule (W : ρ.invtSubmodule) :
    (Subrepresentation.ofInvtSubmodule W).toSubmodule = W := rfl

@[simp] theorem ofInvtSubmodule_toSubmodule (W : Subrepresentation ρ) :
    Subrepresentation.ofInvtSubmodule ⟨W.toSubmodule, W.toSubmodule_mem_invtSubmodule⟩ = W := by
  apply Subrepresentation.toSubmodule_injective
  rfl

/-- Disjointness of subrepresentations is equivalent to disjointness of their underlying
submodules. -/
@[simp] theorem disjoint_toSubmodule {W W' : Subrepresentation ρ} :
    Disjoint W.toSubmodule W'.toSubmodule ↔ Disjoint W W' := by
  rw [disjoint_iff, disjoint_iff]
  constructor
  · intro h
    apply Subrepresentation.toSubmodule_injective
    simpa using h
  · intro h
    simpa using congrArg Subrepresentation.toSubmodule h

/-- Codisjointness of subrepresentations is equivalent to codisjointness of their underlying
submodules. -/
@[simp] theorem codisjoint_toSubmodule {W W' : Subrepresentation ρ} :
    Codisjoint W.toSubmodule W'.toSubmodule ↔ Codisjoint W W' := by
  rw [codisjoint_iff, codisjoint_iff]
  constructor
  · intro h
    apply Subrepresentation.toSubmodule_injective
    simpa using h
  · intro h
    simpa using congrArg Subrepresentation.toSubmodule h

/-- Complementarity of subrepresentations is equivalent to complementarity of their underlying
submodules. -/
@[simp] theorem isCompl_toSubmodule {W W' : Subrepresentation ρ} :
    IsCompl W.toSubmodule W'.toSubmodule ↔ IsCompl W W' := by
  rw [_root_.isCompl_iff, _root_.isCompl_iff, disjoint_toSubmodule, codisjoint_toSubmodule]

end

end Subrepresentation
