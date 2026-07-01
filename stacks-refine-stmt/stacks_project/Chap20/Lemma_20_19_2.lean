import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace TopCat
open TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for Lemma 20.19.2:
- primary domain: filtered colimits, cohomology presheaves, and higher direct images of abelian
  sheaves on topological spaces;
- sampled declarations in this domain:
  `CategoryTheory.Limits.colimit.post`,
  `CategoryTheory.Limits.colimit.ι_post`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `TopCat.Sheaf.pushforward`;
- best owner abstraction: the comparison morphism from the colimit of the objectwise cohomology
  presheaves to the cohomology presheaf of the colimit sheaf is already the canonical
  `colimit.post` for `cohomologyPresheafFunctor`;
- primitive-vs-derived split:
  the primitive data are the filtered diagram `ℱ` and the owner functor
  `cohomologyPresheafFunctor J p`;
  the old local comparison morphism and its component formula were derived API duplicating
  `colimit.post` and `colimit.ι_post`;
- source/core/bridge triage:
  `source-facing`: the higher-direct-image colimit theorem below;
  `core/canonical`: `colimit.post`;
  `bridge/view`: the basis hypothesis expressed on opens of the target space through the preimage
  opens `((Opens.map f).obj V)`.
-/

section

variable {C : Type u} [Category.{u} C]
variable {I : Type u} [Category.{u} I]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasExt (Sheaf J AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{u})]

end

variable {X Y : TopCat.{u}} {I : Type u} [Category.{u} I] [IsFiltered I]
variable (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (X.Sheaf AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Y.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]

-- Proof sketch: identify `R^p f_*` with the sheafification of the presheaf
-- `V ↦ H^p(f⁻¹(V), -)` via Lemma `20.7.3`, use that sheafification preserves colimits, and apply
-- the basis hypothesis to show that the colimit cohomology presheaf and the cohomology presheaf
-- of the colimit sheaf have isomorphic associated sheaves.
/-- Lemma 20.19.2: if the opens `V ⊆ Y` for which the canonical map
`\operatorname{colim}_i H^p(f^{-1}(V), \mathcal F_i) \to H^p(f^{-1}(V), \operatorname{colim}_i
\mathcal F_i)` is an isomorphism form a basis for the topology on `Y`, then the `p`-th higher
direct image of the colimit sheaf is canonically isomorphic to the colimit of the `p`-th higher
direct images. -/
theorem higherDirectImage_colimit_iso_of_basis_preimage_cohomology_colimit
    (ℱ : I ⥤ X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    (hBasis :
      IsTopologicalBasis
        (((↑) : Opens Y → Set Y) ''
          {V : Opens Y |
            IsIso
              ((colimit.post ℱ
                  (cohomologyPresheafFunctor (Opens.grothendieckTopology X) p)).app
                (op ((Opens.map f).obj V)))}) :
    IsIsomorphic
      (((pushforward AddCommGrpCat.{u} f).rightDerived p).obj (colimit ℱ))
      (colimit (ℱ ⋙ (pushforward AddCommGrpCat.{u} f).rightDerived p)) := sorry

end Sheaf
end CategoryTheory
