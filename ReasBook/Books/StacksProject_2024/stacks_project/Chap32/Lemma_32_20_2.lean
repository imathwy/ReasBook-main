import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.JacobsonSpace

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the canonical scheme-module owners
-- `Scheme.Modules`, `Scheme.Modules.pullback`, and `SheafOfModules.IsFinitePresentation`.
-- The right-hand category is therefore modeled as a categorical pullback of the two restriction
-- functors to `V.Modules`; its objects are exactly finitely presented modules on `U` and on the
-- stalk scheme, together with an isomorphism between their pullbacks to `V`.

/-- The object property selecting finitely presented `\mathcal O_X`-modules. -/
abbrev finitePresentationModuleProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun ℱ ↦ ℱ.IsFinitePresentation

/-- The full subcategory of finitely presented `\mathcal O_X`-modules. -/
abbrev FinitePresentationModules (X : Scheme.{u}) : Type (u + 1) :=
  (finitePresentationModuleProperty X).FullSubcategory

namespace FinitePresentationModules

/-- The inclusion from finitely presented modules into all modules on `X`. -/
abbrev inclusion (X : Scheme.{u}) : FinitePresentationModules X ⥤ X.Modules :=
  (finitePresentationModuleProperty X).ι

end FinitePresentationModules

/-- The category of gluing data for finitely presented modules on an open `U`, on a scheme `T`,
and on an open `V ⊆ T`: a finitely presented module on `U`, a finitely presented module on `T`,
and an isomorphism between their pullbacks to `V`. -/
abbrev finitePresentationModuleGluingCategory
    {S T : Scheme.{u}} (U : S.Opens) (V : T.Opens)
    (toU : V.toScheme ⟶ U.toScheme) : Type (u + 1) :=
  CategoricalPullback
    (FinitePresentationModules.inclusion U.toScheme ⋙ Scheme.Modules.pullback toU)
    (FinitePresentationModules.inclusion T ⋙ Scheme.Modules.pullback V.ι)

/-- Lemma 32.20.2: let `S` be a scheme and let `s` be a closed point such that
`U = S \ {s}` is quasi-compact over `S`. With
`T = Spec(\mathcal O_{S,s})` and `V = T \ {s}`, finitely presented
`\mathcal O_S`-modules are equivalent to triples consisting of a finitely presented
`\mathcal O_U`-module, a finitely presented `\mathcal O_T`-module, and an isomorphism between
their restrictions to `V`.

The hypotheses `hU` and `hV` identify the displayed opens with the complements from the source,
and `toU` is the canonical map from the punctured local scheme to the open complement. -/
@[stacks 0F21]
theorem finitePresentationModules_equivalence_puncturedLocalSpec
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens)
    (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (T : Scheme.{u}) (eT : T ≅ Spec (CommRingCat.of (S.presheaf.stalk s)))
    (V : T.Opens)
    (hV : (V : Set T) =
      ({(eT.inv.base) (IsLocalRing.closedPoint (S.presheaf.stalk s))} : Set T)ᶜ)
    (toU : V.toScheme ⟶ U.toScheme)
    (htoU : toU ≫ U.ι = V.ι ≫ eT.hom ≫ S.fromSpecStalk s) :
    Nonempty (FinitePresentationModules S ≌
      finitePresentationModuleGluingCategory U V toU) := sorry

end AlgebraicGeometry
