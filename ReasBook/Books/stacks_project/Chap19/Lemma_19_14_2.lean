import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}

/-- Lemma 19.14.2: in the Gabriel-Popescu setup for a separator `U`, if
`f : M ⟶ (preadditiveCoyonedaObj U).obj A` is injective, i.e. a monomorphism in the module
category, then its adjoint transpose `tensorObj U ⟶ A` is also a monomorphism. -/
-- Proof sketch: the Gabriel-Popescu theorem makes `preadditiveCoyonedaObj U` fully faithful when
-- `U` is a separator, so the counit of `tensorObjPreadditiveCoyonedaObjAdjunction U` is an
-- isomorphism. The transpose of `f` is `tensorObj U` applied to `f`, followed by this counit; the
-- first map is mono because `tensorObj U` preserves monomorphisms, and composing with an
-- isomorphism preserves monomorphisms.
theorem adjoint_map_mono_of_mono (hU : IsSeparator U)
    {f : M ⟶ (preadditiveCoyonedaObj U).obj A} (hf : Mono f) :
    Mono (((tensorObjPreadditiveCoyonedaObjAdjunction U).homEquiv M A).symm f) := by
  let adj := tensorObjPreadditiveCoyonedaObjAdjunction U
  letI : Mono f := hf
  letI : PreservesFiniteLimits (tensorObj U) := GabrielPopescu.preservesFiniteLimits U hU
  letI : (preadditiveCoyonedaObj U).Full := GabrielPopescu.full U hU
  letI : (preadditiveCoyonedaObj U).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU
  rw [adj.homEquiv_counit]
  have hmap : Mono ((tensorObj U).map f) := Functor.map_mono (tensorObj U) f
  have hsplit : IsSplitMono (adj.counit.app A) := by infer_instance
  have hCounit : Mono (adj.counit.app A) := by
    letI : IsSplitMono (adj.counit.app A) := hsplit
    infer_instance
  exact mono_comp' hmap hCounit

end CategoryTheory.IsGrothendieckAbelian
