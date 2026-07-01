import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.EpiMono

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ v₁ v₂

namespace CategoryTheory
namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-
Domain-style sampling for Lemma 18.15.1:
- primary domain: adjunctions and categorical epimorphisms;
- sampled owner API:
  `Adjunction.faithful_R_of_epi_counit_app`,
  `Functor.ReflectsEpimorphisms`,
  `Functor.epi_of_epi_map`,
  `Functor.preservesEpimorphisms_of_adjunction`;
- source/core/bridge triage:
  `core/canonical`: the adjunction `L ⊣ R`;
  `bridge/view`: the Chapter 18 abelian-sheaf specialization of this adjunction theorem.

Primitive data are only the adjunction. Pointwise counit epimorphy, reflection of epimorphisms,
and faithfulness of the right adjoint are derived owner-level API, so this file should live at the
`Adjunction` owner rather than repackage the same mathematics with a separate sheaf-specific
functor triple.
-/

-- Proof sketch: if `R.map f` is epic, apply the left adjoint `L`, use naturality of the counit to
-- identify `L.map (R.map f) ≫ ε_Y` with `ε_X ≫ f`, and then cancel the epimorphic counit on the
-- left. Conversely, `R.map (ε_X)` is split epic by the triangle identity, so if `R` reflects
-- epimorphisms then `ε_X` is epic.
/-- Owner-level form of Lemma 18.15.1: for any adjunction, the counit components are epimorphisms
if and only if the right adjoint reflects epimorphisms. Applied to the inverse-image/direct-image
adjunction on abelian sheaves, this is the Stacks statement for `f⁻¹ f_* \mathcal F ⟶ \mathcal
F`. -/
theorem epi_counit_app_iff_reflectsEpimorphisms (adj : L ⊣ R) :
    (∀ X : D, Epi (adj.counit.app X)) ↔ R.ReflectsEpimorphisms := by
  constructor
  · intro hc
    refine ⟨fun {X Y} f hf ↦ ?_⟩
    haveI : Functor.PreservesEpimorphisms L := Functor.preservesEpimorphisms_of_adjunction adj
    haveI : Epi (R.map f) := hf
    have hEq : L.map (R.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f := by
      simpa using adj.counit.naturality f
    have hcomp : Epi (adj.counit.app X ≫ f) := by
      rw [← hEq]
      exact epi_comp' (inferInstance : Epi (L.map (R.map f))) (hc Y)
    exact (epi_comp_iff_of_epi (adj.counit.app X) f).1 hcomp
  · intro hR
    letI : R.ReflectsEpimorphisms := hR
    intro X
    haveI : IsSplitEpi (R.map (adj.counit.app X)) := by
      refine IsSplitEpi.mk' ⟨adj.unit.app (R.obj X), ?_⟩
      simp
    exact Functor.epi_of_epi_map R (show Epi (R.map (adj.counit.app X)) by infer_instance)

-- Proof sketch: by the previous theorem, reflection of epimorphisms makes all counit components
-- epic, and then the canonical owner theorem `Adjunction.faithful_R_of_epi_counit_app` applies.
/-- Corollary to Lemma 18.15.1: if the right adjoint reflects epimorphisms, then it is faithful.
For abelian sheaf direct images, this recovers the source-facing faithfulness consequence from the
canonical adjunction owner theorem. -/
theorem faithful_R_of_reflectsEpimorphisms (adj : L ⊣ R) (hR : R.ReflectsEpimorphisms) :
    R.Faithful := by
  have hc : ∀ X : D, Epi (adj.counit.app X) := (epi_counit_app_iff_reflectsEpimorphisms adj).2 hR
  letI (X : D) : Epi (adj.counit.app X) := hc X
  exact adj.faithful_R_of_epi_counit_app

end Adjunction
end CategoryTheory
