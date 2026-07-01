import Mathlib

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

local notation "L²(" G ")" => G →₂[(Measure.haar : Measure G)] ℂ

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: the representation attached to a stable submodule agrees with the
owner `Representation.ofModule'` model on the same `ℂ[G]`-module. -/
theorem subrepresentation_equiv_ofModule'
    (ρ : Representation ℂ G L²(G)) (U : Subrepresentation ρ) :
    Nonempty
      ((Representation.ofModule' (k := ℂ) (G := G) U.asSubmodule).Equiv U.toRepresentation) := by
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  · refine
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := fun x ↦ by
          ext
          rfl
        right_inv := fun x ↦ by
          ext
          rfl
        map_add' := fun x y ↦ by
          ext
          rfl
        map_smul' := fun a x ↦ by
          ext
          rfl }
  · intro g
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, hx⟩
    have haction : MonoidAlgebra.single g (1 : ℂ) • (⟨x, hx⟩ : U.asSubmodule) =
        ((ρ g).restrict (U.apply_mem_toSubmodule g)) ⟨x, hx⟩ := by
      ext
      simp only [SetLike.mk_smul_mk, single_smul, one_smul, LinearMap.restrict_coe_apply]
      rfl
    simpa [Representation.ofModule', Subrepresentation.toRepresentation] using haction

/-- Helper for Remark 4-4.3-1: restricting the codomain of an intertwining map to a stable
subrepresentation preserves equivariance. -/
theorem intertwiningMap_codRestrict_isIntertwining
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ G X) (ρ : Representation ℂ G L²(G)) (U : Subrepresentation ρ)
    (f : τ.IntertwiningMap ρ) (hf : ∀ x, f x ∈ U.toSubmodule) :
    ∀ g x,
      (f.toLinearMap.codRestrict U.toSubmodule hf) (τ g x) =
        U.toRepresentation g ((f.toLinearMap.codRestrict U.toSubmodule hf) x) := by
  intro g x
  apply Subtype.ext
  simpa using congr($(f.isIntertwining' g) x)

end PeterWeyl

end Representation
