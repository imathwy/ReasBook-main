import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the canonical support owner `moduleSupport`; the
-- Chapter 31 owner `Scheme.Modules.associatedPoints` already packages `Ass(ℱ)` stalkwise.

/-- Lemma 31.2.3: for a quasi-coherent `\mathcal O_X`-module `ℱ` on a scheme `X`, every
associated point of `ℱ` lies in the support of `ℱ`. -/
@[stacks 05AD]
theorem associatedPoints_subset_support :
    associatedPoints ℱ ⊆ moduleSupport ℱ := by
  intro x hx
  rw [mem_associatedPoints_iff] at hx
  rw [mem_moduleSupport_iff]
  by_contra hsupport
  push Not at hsupport
  haveI : Subsingleton ↑(RingedSpace.stalkModuleCat ℱ x) := ⟨fun m n ↦ by
    rw [hsupport m, hsupport n]⟩
  exact (not_isAssociatedPrime_of_subsingleton
    (R := X.presheaf.stalk x)
    (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (M := ↑(RingedSpace.stalkModuleCat ℱ x)))
    (associatedPrimesOfModule_subset_associatedPrimes
      (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) hx)

/-- A point associated to `ℱ` lies in the support of `ℱ`. -/
theorem mem_moduleSupport_of_mem_associatedPoints (x : X)
    (hx : x ∈ associatedPoints ℱ) :
    x ∈ moduleSupport ℱ :=
  associatedPoints_subset_support ℱ hx

end AlgebraicGeometry.Scheme.Modules
