import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_19_1 (from Chap20) -/
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The functor sending an `\mathcal O_X`-module to its degree-`q` cohomology on the open subset
`U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (q : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) q ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The canonical morphism from the filtered colimit of the groups `H^q(U, \mathcal F_i)` to the
cohomology group `H^q(U, \operatorname{colim}_i \mathcal F_i)`. -/
noncomputable def ringedSpaceModuleCohomologyColimitComparison
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {I : Type v} [SmallCategory I]
    (U : Opens X.carrier) (q : ℕ)
    (ℱ : I ⥤ SheafOfModules (ringedSpaceRingCatSheaf X))
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q)] :
    colimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q) ⟶
      (ringedSpaceModuleCohomologyAtOpenFunctor X U q).obj (colimit ℱ) :=
  colimit.desc _ ((ringedSpaceModuleCohomologyAtOpenFunctor X U q).mapCocone (colimit.cocone ℱ))

-- Proof sketch: first prove the degree-zero statement for every compact open simultaneously, using
-- that filtered colimits commute with sections on compact opens in a prespectral space whose
-- compact opens are stable under binary intersections. Then choose functorial injective embeddings
-- of the diagram, use exactness of filtered colimits of abelian groups and the vanishing of higher
-- Čech cohomology for injectives on finite covers by compact opens, and conclude by induction on
-- `q`.
/-- Lemma 20.19.1: if the underlying topological space of a ringed space `X` has a basis of
quasi-compact opens and the intersection of any two quasi-compact opens is quasi-compact, then for
every filtered diagram `(\mathcal F_i)` of `\mathcal O_X`-modules, every quasi-compact open subset
`U`, and every `q \geq 0`, the canonical map
`colim_i H^q(U, \mathcal F_i) \to H^q(U, \operatorname{colim}_i \mathcal F_i)` is an
isomorphism. -/
theorem ringedSpaceModuleCohomologyColimitComparison_isIso_of_isCompact
    {X : RingedSpace.{u}}
    [PrespectralSpace X.carrier]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (hinter : ∀ U V : Opens X.carrier, IsCompact (U : Set X.carrier) →
      IsCompact (V : Set X.carrier) → IsCompact ((U ⊓ V : Opens X.carrier) : Set X.carrier))
    (U : Opens X.carrier) (hU : IsCompact (U : Set X.carrier)) (q : ℕ)
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (ℱ : I ⥤ SheafOfModules (ringedSpaceRingCatSheaf X))
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q)] :
    IsIso (ringedSpaceModuleCohomologyColimitComparison U q ℱ) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_19_2 (from Chap20) -/
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

/-! ### Lemma_20_19_3 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

/-- A compatible inverse-limit situation of abelian sheaves on a cofiltered diagram of topological
spaces, together with the chosen limiting sheaf on the inverse limit space. -/
structure SpectralInverseLimitAbelianSheafSituation
    {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v}) [HasLimit F] where
  /-- The abelian sheaf `\mathcal F_i` on the stage `X_i`. -/
  stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v}
  /-- The transition map `\mathcal F_i \to f_{a,*}\mathcal F_j` attached to `a : j ⟶ i`. -/
  stageMap : ∀ {j i : I} (a : j ⟶ i),
    stageSheaf i ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j)
  /-- The sheaf `\mathcal F` on the inverse-limit space `X = \varprojlim X_i`. -/
  limitSheaf : (limit F).Sheaf AddCommGrpCat.{max u v}
  /-- The comparison map `\mathcal F_i \to p_{i,*}\mathcal F` to the pushforward of the limit
  sheaf along the projection `p_i : X \to X_i`. -/
  limitMap : ∀ i : I,
    stageSheaf i ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj limitSheaf
  /-- For a fixed stage `i`, quasi-compact open `U_i`, and degree `p`, the chosen over-category
  diagram `a : j ⟶ i ↦ H^p(f_a^{-1}(U_i), \mathcal F_j)`, expressed in the library-facing
  pushforward form. -/
  projectionOpenCohomologyDiagram :
    ∀ (i : I) (_Ui : Opens (F.obj i)) (_p : ℕ), (Over i)ᵒᵖ ⥤ AddCommGrpCat.{max u v}

variable {X Y : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

-- Proof sketch: pushforward along `f` is right adjoint to inverse image, and inverse image of
-- abelian sheaves is exact, so pushforward preserves injective resolutions. Since sections of
-- `f_* \mathcal F` on `U` are sections of `\mathcal F` on `f^{-1}(U)`, the derived functors
-- computing these two cohomology groups agree.
/-- The cohomology of the pushforward sheaf on an open `U ⊆ Y` identifies with the cohomology of
the original sheaf on the inverse-image open `f^{-1}(U)`. -/
theorem pushforward_cohomologyOnOpen_isomorphic_preimage
    (f : X ⟶ Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens Y) (p : ℕ) :
    IsIsomorphic (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj ℱ).H' p U)
      (ℱ.H' p ((Opens.map f).obj U)) := sorry

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v}) [HasLimit F]
variable [∀ j : I, SpectralSpace ↥(F.obj j)]
variable [HasSheafify (Opens.grothendieckTopology ↥(limit F)) AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf (Opens.grothendieckTopology ↥(limit F))
  AddCommGrpCat.{max u v})]

-- Proof sketch: first identify the source with the colimit of the degree-`p` cohomology objects
-- of the stage sheaves over the over-category of arrows `a : j ⟶ i`, using the pushforward form
-- of cohomology on inverse-image opens. Then choose compatible injective embeddings stagewise,
-- reduce to vanishing for the colimit sheaf on quasi-compact opens, and finish with the Čech
-- acyclicity argument from the preceding lemmas together with exactness of filtered colimits.
/-- Lemma 20.19.3: in the inverse-limit situation for spectral spaces and compatible abelian
sheaves, if `U_i ⊆ X_i` is quasi-compact open, then the filtered colimit of the groups
`H^p(f_a^{-1}(U_i), \mathcal F_j)` over arrows `a : j ⟶ i` is canonically isomorphic to
`H^p(p_i^{-1}(U_i), \mathcal F)`. -/
theorem spectralInverseLimit_projectionOpenCohomology_isomorphic
    (S : SpectralInverseLimitAbelianSheafSituation F)
    (i : I) (Ui : Opens (F.obj i)) (hUi : IsCompact (Ui : Set (F.obj i))) (p : ℕ)
    [HasColimit (S.projectionOpenCohomologyDiagram i Ui p)] :
    IsIsomorphic
      (colimit (S.projectionOpenCohomologyDiagram i Ui p))
      (S.limitSheaf.H' p ((Opens.map (limit.π F i)).obj Ui)) := sorry

-- Proof sketch: apply Lemma `20.19.3` to the top open `U_i = X_i`, which is quasi-compact for a
-- spectral space, and rewrite `p_i^{-1}(X_i)` as the whole inverse-limit space `X`.
/-- The global cohomology of the limit sheaf is the filtered colimit of the stagewise global
cohomology groups in the inverse-limit situation of Lemma `20.19.3`. -/
theorem spectralInverseLimit_globalCohomology_isomorphic
    (S : SpectralInverseLimitAbelianSheafSituation F) (i : I) (p : ℕ)
    [HasColimit (S.projectionOpenCohomologyDiagram i (⊤ : Opens (F.obj i)) p)] :
    IsIsomorphic
      (colimit (S.projectionOpenCohomologyDiagram i (⊤ : Opens (F.obj i)) p))
      (S.limitSheaf.H' p (⊤ : Opens ↥(limit F))) := sorry

end Sheaf
end CategoryTheory
