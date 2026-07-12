import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Homeomorph.Defs

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this environment; the canonical owner below was checked
-- directly against mathlib's `Homeomorph`, `Subgroup`, and `MulAction` APIs.

universe uE uM

section CoveringAutomorphisms

variable {E : Type uE} [TopologicalSpace E]
variable {M : Type uM}

/-- Definition 7.50-extra-2: the automorphism group of a covering map `π : E → M`, also called
the group of deck transformations, is the subgroup of self-homeomorphisms of `E` satisfying
`π ∘ φ = π`. -/
def coveringAutomorphismGroup (π : E → M) : Subgroup (E ≃ₜ E) where
  carrier := { φ | π ∘ φ = π }
  one_mem' := rfl
  mul_mem' {φ} {ψ} hφ hψ := by
    ext x
    calc
      π ((φ * ψ) x) = π (ψ x) := by
        simpa using congrFun hφ (ψ x)
      _ = π x := by
        simpa using congrFun hψ x
  inv_mem' {φ} hφ := by
    ext x
    simpa using (congrFun hφ (φ⁻¹ x)).symm

/-- A self-homeomorphism belongs to the covering automorphism group exactly when it preserves the
covering map. -/
theorem mem_coveringAutomorphismGroup_iff (π : E → M) (φ : E ≃ₜ E) :
    φ ∈ coveringAutomorphismGroup π ↔ π ∘ φ = π :=
  Iff.rfl

/-- The covering automorphism group acts on the total space by evaluation. -/
instance coveringAutomorphismGroup_mulAction (π : E → M) :
    MulAction (coveringAutomorphismGroup π) E where
  smul := fun φ x ↦ (φ : E ≃ₜ E) x
  one_smul := fun _ ↦ rfl
  mul_smul := fun _ _ _ ↦ rfl

/-- For the induced action of the covering automorphism group, scalar multiplication is evaluation
of the underlying homeomorphism. -/
theorem coveringAutomorphismGroup_smul_def (π : E → M)
    (φ : coveringAutomorphismGroup π) (x : E) :
    φ • x = (φ : E ≃ₜ E) x :=
  rfl

end CoveringAutomorphisms
