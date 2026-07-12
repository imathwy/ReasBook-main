import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import StacksProject_2024.Chap20.«20_2_0_2»

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
  `TopCat.Sheaf.higherDirectImageFunctor`,
  `TopCat.Sheaf.pushforward`;
- best owner abstraction: the comparison morphism from the colimit of the objectwise cohomology
  of the higher direct images to the higher direct image of the colimit sheaf is already the
  canonical `colimit.post` for `TopCat.Sheaf.higherDirectImageFunctor f p`, while the basis
  hypothesis is expressed
  by the canonical `colimit.post` for `cohomologyPresheafFunctor`;
- primitive-vs-derived split:
  the primitive data are the filtered diagram `ℱ` and the owner functor
  `TopCat.Sheaf.higherDirectImageFunctor f p`,
  together with the objectwise cohomology owner
  `cohomologyPresheafFunctor (Opens.grothendieckTopology X) p`;
  a bare `IsIsomorphic` between the source and target sheaves was only derived API, weaker than
  the canonical comparison-map statement already available from `colimit.post`;
- source/core/bridge triage:
  `source-facing`: the higher-direct-image colimit comparison theorem below and its explicit-basis
  companion API;
  `core/canonical`: `colimit.post`, `TopCat.Sheaf.higherDirectImageFunctor`, and
  `cohomologyPresheafFunctor`;
  `bridge/view`: the basis hypothesis expressed on opens of the target space through the preimage
  opens `Opens.comap f.hom V`.
-/

variable {X Y : TopCat.{u}} {I : Type u} [Category.{u} I] [IsFiltered I]
variable (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (X.Sheaf AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Y.Sheaf AddCommGrpCat.{u})]
variable [(pushforward AddCommGrpCat.{u} f).Additive]

/- The basiswise comparison is source-facing theorem API rather than an `IsIso` instance: until the
comparison is proved without proof debt, exposing it as instance data would introduce a public
sorry-backed inverse witness. -/
omit [IsFiltered I] [HasExt (X.Sheaf AddCommGrpCat.{u})] in
/-- Explicit-basis companion API for Lemma `20.19.2`: it is enough to choose a basis `𝓑` of opens
of `Y` on which the canonical maps
`colim_i H^p(f⁻¹(V), ℱ_i) ⟶ H^p(f⁻¹(V), colim_i ℱ_i)`
are isomorphisms. -/
theorem higherDirectImage_colimit_iso_of_preimage_cohomology_colimit_on_basis
    (ℱ : I ⥤ X.Sheaf AddCommGrpCat.{u}) (p : ℕ) {𝓑 : Set (Opens Y)}
    (h𝓑 : Opens.IsBasis 𝓑)
    (h𝓑iso : ∀ ⦃V : Opens Y⦄, V ∈ 𝓑 →
      IsIso
        (((colimit.post ℱ
            (cohomologyPresheafFunctor (Opens.grothendieckTopology X) p)).app
          (op (Opens.comap f.hom V))))) :
    IsIso (colimit.post ℱ (TopCat.Sheaf.higherDirectImageFunctor f p)) := by
  sorry

-- Proof sketch: identify `R^p f_*` with the sheafification of the presheaf
-- `V ↦ H^p(f⁻¹(V), -)` via Lemma `20.7.3`, use that sheafification preserves colimits, and apply
-- the basis hypothesis to show that the colimit cohomology presheaf and the cohomology presheaf
-- of the colimit sheaf induce an isomorphism on the canonical higher-direct-image comparison map.
/- The source-facing theorem wrapper likewise drops the unused section variables so its public
surface matches the actual mathematical inputs. -/
omit [IsFiltered I] [HasExt (X.Sheaf AddCommGrpCat.{u})] in
/-- Lemma 20.19.2: if the opens `V ⊆ Y` for which the canonical map
`colim_i H^p(f⁻¹(V), ℱ_i) ⟶ H^p(f⁻¹(V), colim_i ℱ_i)` is an isomorphism form a basis for the
topology on `Y`, then the canonical map
`colim_i R^p f _* ℱ_i ⟶ R^p f _* (colim_i ℱ_i)` is an isomorphism. -/
@[stacks 0H7A]
theorem higherDirectImage_colimit_iso_of_basis_preimage_cohomology_colimit
    (ℱ : I ⥤ X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    (hBasis :
      Opens.IsBasis
        {V : Opens Y |
          IsIso
            (((colimit.post ℱ
                (cohomologyPresheafFunctor (Opens.grothendieckTopology X) p)).app
              (op (Opens.comap f.hom V))))}) :
    IsIso (colimit.post ℱ (TopCat.Sheaf.higherDirectImageFunctor f p)) :=
  higherDirectImage_colimit_iso_of_preimage_cohomology_colimit_on_basis
    f ℱ p hBasis (fun V hV ↦ by simpa using hV)

end Sheaf
end CategoryTheory
