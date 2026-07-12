import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}

/-
Domain-style sampling:
* primary domain: the Gabriel-Popescu adjunction for a separator in a Grothendieck abelian
  category, together with adjunction-level control of monomorphisms.
* sampled owner declarations:
  `tensorObjPreadditiveCoyonedaObjAdjunction`,
  `GabrielPopescu.full`,
  `GabrielPopescu.preservesFiniteLimits`,
  `Adjunction.counit_isIso_of_R_fully_faithful`.
* best owner abstraction: the canonical adjunction
  `tensorObj U ⊣ preadditiveCoyonedaObj U`.
* source/core/bridge triage:
  - `source-facing`: the Stacks statement that a mono into the Gabriel-Popescu embedding has mono
    adjoint transpose;
  - `core/canonical`: the adjunction above, together with the owner theorem
    `Adjunction.counit_isIso_of_R_fully_faithful`;
  - `bridge/view`: this file’s specialization of those owner facts to the separator hypothesis.
* primitive data: the separator witness `hU` and the mono `f`.
* derived API: preservation of monomorphisms by `tensorObj U`, fullness/faithfulness of
  `preadditiveCoyonedaObj U`, and the resulting counit isomorphism.
-/

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
  letI : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  rw [adj.homEquiv_counit]
  have hCounit : Mono (adj.counit.app A) := by
    simpa using (inferInstance : Mono ((asIso adj.counit).hom.app A))
  exact mono_comp' (Functor.map_mono (tensorObj U) f) hCounit

end CategoryTheory.IsGrothendieckAbelian
