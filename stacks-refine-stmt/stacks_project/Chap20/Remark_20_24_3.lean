import Mathlib
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The structural ring-sheaf morphism attached to the inclusion of an open subspace. -/
noncomputable abbrev ringedSpaceOpenSubsetStructureSheafHom {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    ringedSpaceRingCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} U.inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
    (ringedSpaceRingCatSheaf X)

/-- Restriction of an `\mathcal O_X`-module to an open subspace `U`. -/
noncomputable abbrev restrictedRingedSpaceModule {X : RingedSpace.{u}}
    (U : Opens X.carrier) (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (SheafOfModules.pullback (ringedSpaceOpenSubsetStructureSheafHom U)).obj ℱ

/-- Pushforward of modules from the open subspace `U` back to the ambient ringed space. -/
noncomputable abbrev ringedSpaceModulePushforwardFromOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
        (ringedSpaceRingCatSheaf X)) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pushforward (ringedSpaceOpenSubsetStructureSheafHom U)

/-- The finite intersection attached to a Čech multi-index in an open family `𝒰`. -/
abbrev cechIntersection {X : RingedSpace.{u}} {ι : Type u}
    (𝒰 : ι → Opens X.carrier) {n : ℕ} (σ : Fin n → ι) : Opens X.carrier :=
  ⨅ a, 𝒰 (σ a)

/-- The bundled topological space associated to an open subset `U ⊆ X`. -/
abbrev openSubsetSpace (X : TopCat.{u}) (U : Opens X) :=
  (Opens.toTopCat X).obj U

/-- Pushforward of an abelian sheaf from an open subset `U ⊆ X` to the ambient space `X`. -/
abbrev openPushforwardAb {X : TopCat.{u}} (U : Opens X) :
    (openSubsetSpace X U).Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)

/-- Evaluation of an abelian sheaf on `X` at the open subset `V`. -/
abbrev abelianSheafSectionsFunctor (X : TopCat.{u}) (V : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)

/-- The canonical map from the coproduct of pushed-forward abelian sheaves to the product of the
same family. -/
noncomputable def openPushforwardCoproductToProduct {X : TopCat.{u}} {ι : Type u} [DecidableEq ι]
    (U : ι → Opens X) (ℱ : ∀ i, (openSubsetSpace X (U i)).Sheaf AddCommGrpCat.{u}) :
    (∐ fun i ↦ (openPushforwardAb (U i)).obj (ℱ i)) ⟶
      ∏ᶜ fun i ↦ (openPushforwardAb (U i)).obj (ℱ i) :=
  Pi.lift fun i ↦ Sigma.π (fun j ↦ (openPushforwardAb (U j)).obj (ℱ j)) i

-- Proof sketch: on the open `V`, sections of each summand are sections on `V ∩ U i`, and local
-- finiteness implies that every section of the coproduct sheaf has only finitely many nonzero
-- components near each point. Hence the canonical map from sections of the coproduct sheaf to the
-- product of the section groups is bijective.
/-- Remark 20.24.3: for a locally finite family of open subsets `U i ⊆ X` and abelian sheaves
`ℱ i` on the open subspaces `U i`, the canonical map from sections on `V` of the coproduct sheaf
`∐ i, (j_i)_* ℱ i` to the product of the section groups over `V` is an isomorphism. -/
theorem locallyFinite_openPushforward_sections_comparison_isIso {X : TopCat.{u}} {ι : Type u}
    [DecidableEq ι]
    (U : ι → Opens X) (hU : LocallyFinite fun i ↦ (U i : Set X))
    (ℱ : ∀ i, (openSubsetSpace X (U i)).Sheaf AddCommGrpCat.{u}) (V : Opens X) :
    IsIso ((abelianSheafSectionsFunctor X V).map (openPushforwardCoproductToProduct U ℱ)) :=
  sorry

-- Proof sketch: the previous sections computation holds for every open `V ⊆ X`. Since the
-- forgetful functor from abelian sheaves to presheaves reflects isomorphisms, the canonical map
-- from the coproduct of the pushed-forward sheaves to their product is therefore an isomorphism.
/-- The coproduct of a locally finite family of pushed-forward abelian sheaves identifies with the
product of the same family. -/
theorem locallyFinite_openPushforward_comparison_isIso {X : TopCat.{u}} {ι : Type u}
    [DecidableEq ι]
    (U : ι → Opens X) (hU : LocallyFinite fun i ↦ (U i : Set X))
    (ℱ : ∀ i, (openSubsetSpace X (U i)).Sheaf AddCommGrpCat.{u}) :
    IsIso (openPushforwardCoproductToProduct U ℱ) :=
  sorry

-- Proof sketch: apply the previous comparison theorem to the locally finite family of finite
-- intersections `U_{i₀} ∩ ⋯ ∩ U_{i_p}` and to the restricted sheaves on those intersections. This
-- turns the product term from Lemma `20.24.1` into the corresponding coproduct term.
/-- The canonical comparison for the degree-`p` Čech term attached to a locally finite family of
open subsets is an isomorphism, so the product term of Lemma `20.24.1` may be viewed as the
corresponding coproduct of pushforwards from the intersections. -/
theorem openCoverModuleCechTerm_comparison_isIso {X : RingedSpace.{u}} {ι : Type u}
    [DecidableEq ι]
    (𝒰 : ι → Opens X.carrier) (h𝒰lf : LocallyFinite fun i ↦ (𝒰 i : Set X.carrier))
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) :
    IsIso (Pi.lift fun σ : Fin (p + 1) → ι ↦
      Sigma.π
        (fun τ : Fin (p + 1) → ι ↦
          (ringedSpaceModulePushforwardFromOpen (cechIntersection 𝒰 τ)).obj
            (restrictedRingedSpaceModule (cechIntersection 𝒰 τ) ℱ))
        σ) :=
  sorry

end AlgebraicGeometry
