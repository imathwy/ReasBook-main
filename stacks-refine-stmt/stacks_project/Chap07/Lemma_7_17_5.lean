import Mathlib
import stacks_project.Chap07.Definition_7_17_1
import stacks_project.Chap07.Definition_7_17_4
import stacks_project.Chap07.Lemma_7_12_4
import stacks_project.Chap07.Lemma_7_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

open Limits
open CategoryTheory.Presheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.5:
- core/canonical owner: `ObjectProperty.IsClosedUnderQuotients` applied to
  `Sheaf.IsQuasiCompactObject`
- source-facing statements: Lemma `7.17.5 (2)` on sheaves and Lemma `7.17.5 (1)` on site objects
- bridge/view: `Sheaf.isLocallySurjective_iff_epi`, `J.sheafifiedRepresentableMap`, together with
  `GrothendieckTopology.quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable`
- primitive data: the owner predicate `Sheaf.IsQuasiCompactObject`
- derived API: quotient stability for locally surjective morphisms and the site-side transfer along
  sheafified representables
-/

private theorem presheaf_isLocallySurjective_sigmaDesc_pullback_snd
    {F G : Cᵒᵖ ⥤ Type (max u v)} (q : F ⟶ G)
    {ι : Type*} (X : ι → Cᵒᵖ ⥤ Type (max u v))
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : Presheaf.IsLocallySurjective J (Limits.Sigma.desc α)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)) := by
  sorry

instance isQuasiCompactObject_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := by
  sorry

/-- Lemma 7.17.5 (2): a locally surjective image of a quasi-compact sheaf of sets is
quasi-compact. -/
theorem isQuasiCompactObject_of_isLocallySurjective
    {F G : Sheaf J (Type (max u v))} (π : F ⟶ G)
    (hπ : IsLocallySurjective π) (hF : F.IsQuasiCompactObject) :
    G.IsQuasiCompactObject := by
  sorry

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CategoryTheory.Sheaf
open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.17.5 (1): if `h[U]^#[J] ⟶ h[V]^#[J]` is locally surjective and `U` is quasi-compact,
then `V` is quasi-compact. -/
theorem quasiCompactObject_of_isLocallySurjective_sheafifiedRepresentableMap
    {U V : C} (f : U ⟶ V)
    (hf : IsLocallySurjective (J.sheafifiedRepresentableMap f))
    (hU : J.QuasiCompactObject U) :
    J.QuasiCompactObject V := by
  sorry

end CategoryTheory.GrothendieckTopology
