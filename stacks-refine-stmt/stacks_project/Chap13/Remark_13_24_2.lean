import stacks_project.Chap13.Remark_13_18_5
import stacks_project.Chap13.Lemma_13_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomotopyCategory
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The source category `InjRes(𝒜)` of bounded-below injective-resolution arrows
`K^• ⟶ I^•`, where `I^•` is termwise injective and the arrow is a quasi-isomorphism. -/
abbrev InjRes (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  ObjectProperty.FullSubcategory
    (fun X :
      Comma
        (𝟭 (Plus 𝒜))
        (ObjectProperty.ι
          (fun K : Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n))) ↦
      QuasiIso X.hom.hom)

namespace InjRes

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

private abbrev rawInclusion :
    InjRes 𝒜 ⥤
      Comma
        (𝟭 (Plus 𝒜))
        (ObjectProperty.ι
          (fun K : Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n))) :=
  ObjectProperty.ι _

/- Domain-style sampling:
- primary domain: the source category of bounded-below injective resolutions and the induced
  functors to `Comp⁺(𝒜)` and `K⁺(\mathcal I)`;
- relevant owner declarations in this domain:
  `CategoryTheory.Comma`,
  `CategoryTheory.Comma.fst`,
  `CategoryTheory.Comma.snd`,
  `CochainComplex.InjectivePlus.toHomotopy`;
- best owner abstraction: the source remark is about the actual category `InjRes(𝒜)` of arrows
  `K^• ⟶ I^•`; its forgetful and target functors should therefore be modeled by the canonical
  comma-category projections rather than by a new bespoke wrapper structure;
- primitive data: an object of `InjRes(𝒜)` is a commutative-arrow datum `K ⟶ I` with `I`
  bounded below and termwise injective, together with the quasi-isomorphism property;
- derived API: the source functor `s`, the target functor `t`, the induced objectwise
  `ResolutionFunctorOne`, and the comparison with a homotopy resolution functor.

Source/core/bridge triage:
- `source-facing`: `InjRes 𝒜` together with its functors `s` and `t`;
- `core/canonical`: `Comma`, `Comma.fst`, `Comma.snd`, and `InjectivePlus.toHomotopy`;
- `bridge/view`: `toResolutionFunctorOne`, transporting a functor `inj : Comp⁺(𝒜) ⥤ InjRes(𝒜)`
  with `inj ⋙ s = 𝟭` to the earlier source-facing owner `ResolutionFunctorOne 𝒜`.
-/

/-- The source functor `s : InjRes(𝒜) ⥤ Comp⁺(𝒜)` forgetting the injective-resolution target. -/
abbrev s : InjRes 𝒜 ⥤ Plus 𝒜 :=
  rawInclusion ⋙ Comma.fst _ _

/-- The target functor `t : InjRes(𝒜) ⥤ K⁺(\mathcal I)` forgetting the source complex and
passing the bounded-below injective target to the homotopy category. -/
abbrev t : InjRes 𝒜 ⥤ K⁺ᵢ(𝒜) :=
  rawInclusion ⋙ Comma.snd _ _ ⋙ CochainComplex.InjectivePlus.toHomotopy 𝒜

private theorem obj_left_eq
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜)) (K : Plus 𝒜) :
    (rawInclusion.obj (inj.obj K)).left = K := by
  simpa [s, rawInclusion] using Functor.congr_obj hs K

private theorem map_left_naturality
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    {K L : Plus 𝒜} (α : K ⟶ L) :
    eqToHom (obj_left_eq inj hs K).symm ≫ (rawInclusion.map (inj.map α)).left =
      α ≫ eqToHom (obj_left_eq inj hs L).symm := by
  sorry

/-- An object of `InjRes(𝒜)` determines an injective resolution of its source complex. -/
abbrev toInjectiveResolution (I : InjRes 𝒜) :
    InjectiveResolution ((s.obj I).obj) where
  complex := (rawInclusion.obj I).right
  ι := (rawInclusion.obj I).hom.hom
  quasiIso := by
    simpa [rawInclusion] using I.property

/-- A functor `inj : Comp⁺(𝒜) ⥤ InjRes(𝒜)` with `inj ⋙ s = 𝟭` induces the objectwise source
owner `ResolutionFunctorOne 𝒜` of Lemma 13.23.3. -/
noncomputable def toResolutionFunctorOne
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜)) :
    ResolutionFunctorOne 𝒜 :=
  fun K ↦
    let X := rawInclusion.obj (inj.obj K)
    let hK : X.left = K := obj_left_eq inj hs K
    { complex := X.right
      ι := eqToHom (congrArg (fun Y : Plus 𝒜 ↦ Y.obj) hK).symm ≫ X.hom.hom
      quasiIso := by
        sorry }

theorem toResolutionFunctorOne_ι
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜)) (K : Plus 𝒜) :
    (toResolutionFunctorOne inj hs K).ι =
      eqToHom (congrArg (fun Y : Plus 𝒜 ↦ Y.obj) (obj_left_eq inj hs K)).symm ≫
        (rawInclusion.obj (inj.obj K)).hom.hom := by
  rfl

/-- The induced `ResolutionFunctorOne` is the bridge from the source functor `inj` to the
homotopy-resolution-functor owner. -/
abbrev RealizedBy
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    (j : CategoryTheory.HomotopyResolutionFunctor 𝒜) : Prop :=
  (toResolutionFunctorOne inj hs).RealizedBy j

theorem homotopyObj_eq
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜)) (K : Plus 𝒜) :
    (toResolutionFunctorOne inj hs).homotopyObj K = (inj ⋙ t).obj K := by
  sorry

abbrev tMap
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    {K L : Plus 𝒜} (α : K ⟶ L) :
    (toResolutionFunctorOne inj hs).homotopyObj K ⟶
      (toResolutionFunctorOne inj hs).homotopyObj L :=
  eqToHom (homotopyObj_eq inj hs K).symm ≫
    (inj ⋙ t).map α ≫
      eqToHom (homotopyObj_eq inj hs L)

end InjRes

namespace ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- If `j` realizes the objectwise resolution functor `R`, then its value on `K` is canonically
isomorphic to the chosen object `R.homotopyObj K`. -/
noncomputable def realizedIso (R : ResolutionFunctorOne 𝒜)
    {j : CategoryTheory.HomotopyResolutionFunctor 𝒜}
    (hj : R.RealizedBy j) (K : Plus 𝒜) :
    j.toFunctor.obj ((Qplus).obj K) ≅ R.homotopyObj K :=
  Classical.choose (hj K)

private theorem realizedIso_hom_spec (R : ResolutionFunctorOne 𝒜)
    {j : CategoryTheory.HomotopyResolutionFunctor 𝒜}
    (hj : R.RealizedBy j) (K : Plus 𝒜) :
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map (R.realizedIso hj K).hom = R.homotopyι K := by
  obtain ⟨hι, -⟩ := Classical.choose_spec (hj K)
  exact hι

@[reassoc]
theorem ι_app_realizedIso_hom
    (R : ResolutionFunctorOne 𝒜) {j : CategoryTheory.HomotopyResolutionFunctor 𝒜}
    (hj : R.RealizedBy j) (K : Plus 𝒜) :
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map (R.realizedIso hj K).hom = R.homotopyι K := by
  exact R.realizedIso_hom_spec hj K

@[reassoc]
theorem homotopyι_realizedIso_inv
    (R : ResolutionFunctorOne 𝒜) {j : CategoryTheory.HomotopyResolutionFunctor 𝒜}
    (hj : R.RealizedBy j) (K : Plus 𝒜) :
    R.homotopyι K ≫ (KinjIncl).map (R.realizedIso hj K).inv = j.ι.app ((Qplus).obj K) := by
  apply (cancel_mono ((KinjIncl).map (R.realizedIso hj K).hom)).1
  simpa [Category.assoc] using (ι_app_realizedIso_hom R hj K).symm

theorem homotopyι_map_commSq
    (R : ResolutionFunctorOne 𝒜) (j : CategoryTheory.HomotopyResolutionFunctor 𝒜)
    (hj : R.RealizedBy j) {K L : Plus 𝒜} (α : K ⟶ L) :
    CommSq
      (R.homotopyι K)
      ((Qplus).map α)
      ((KinjIncl).map
        ((R.realizedIso hj K).inv ≫ j.toFunctor.map ((Qplus).map α) ≫
          (R.realizedIso hj L).hom))
      (R.homotopyι L) := by
  refine CommSq.mk ?_
  have h₁ :
      R.homotopyι K ≫
          (KinjIncl).map
            ((R.realizedIso hj K).inv ≫ j.toFunctor.map ((Qplus).map α) ≫
              (R.realizedIso hj L).hom) =
        R.homotopyι K ≫ (KinjIncl).map (R.realizedIso hj K).inv ≫
          (KinjIncl).map (j.toFunctor.map ((Qplus).map α)) ≫
            (KinjIncl).map (R.realizedIso hj L).hom := by
    simp
  have h₂ :
      R.homotopyι K ≫ (KinjIncl).map (R.realizedIso hj K).inv ≫
          (KinjIncl).map (j.toFunctor.map ((Qplus).map α)) ≫
            (KinjIncl).map (R.realizedIso hj L).hom =
        j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map (j.toFunctor.map ((Qplus).map α)) ≫
          (KinjIncl).map (R.realizedIso hj L).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ (KinjIncl).map (j.toFunctor.map ((Qplus).map α)) ≫
          (KinjIncl).map (R.realizedIso hj L).hom)
        (homotopyι_realizedIso_inv R hj K)
  have h₃ :
      j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map (j.toFunctor.map ((Qplus).map α)) ≫
          (KinjIncl).map (R.realizedIso hj L).hom =
        (Qplus).map α ≫ j.ι.app ((Qplus).obj L) ≫
          (KinjIncl).map (R.realizedIso hj L).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ (KinjIncl).map (R.realizedIso hj L).hom)
        ((j.ι.naturality ((Qplus).map α)).symm)
  have h₄ :
      (Qplus).map α ≫ j.ι.app ((Qplus).obj L) ≫
          (KinjIncl).map (R.realizedIso hj L).hom =
        (Qplus).map α ≫ R.homotopyι L := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ (Qplus).map α ≫ f) (ι_app_realizedIso_hom R hj L)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end ResolutionFunctorOne

namespace InjRes

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

private theorem t_map_commSq
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    {K L : Plus 𝒜} (α : K ⟶ L) :
    let R := toResolutionFunctorOne inj hs
    R.homotopyι K ≫ (KinjIncl).map (tMap inj hs α) =
      (Qplus).map α ≫ R.homotopyι L := by
  sorry

private theorem t_map_unique
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    {K L : Plus 𝒜} (α : K ⟶ L)
    {a :
      (toResolutionFunctorOne inj hs).homotopyObj K ⟶
        (toResolutionFunctorOne inj hs).homotopyObj L}
    (ha :
      (toResolutionFunctorOne inj hs).homotopyι K ≫ (KinjIncl).map a =
        (Qplus).map α ≫ (toResolutionFunctorOne inj hs).homotopyι L) :
    a = tMap inj hs α := by
  sorry

-- Proof sketch: the transported morphism coming from `j.toFunctor.map (Qplus.map α)` satisfies
-- the same comparison square as the actual source-side morphism `(inj ⋙ t).map α`, and Remark
-- 13.18.5 gives uniqueness of such lifts into the bounded-below injective target.
/-- Remark 13.24.2: if `inj : Comp⁺(𝒜) ⥤ InjRes(𝒜)` satisfies `s ∘ inj = id` and `j` realizes
the induced `ResolutionFunctorOne`, then after transporting along the canonical objectwise
isomorphisms from `ResolutionFunctorOne.RealizedBy`, the morphism that `j` assigns to `α`
coincides with the source-side morphism induced by `inj(α)` on injective targets, i.e. with the
morphism component of `t ∘ inj`. -/
theorem map_eq_t_map
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    (j : CategoryTheory.HomotopyResolutionFunctor 𝒜) (hj : RealizedBy inj hs j)
    {K L : Plus 𝒜} (α : K ⟶ L) :
    let R := toResolutionFunctorOne inj hs
    (R.realizedIso hj K).inv ≫ j.toFunctor.map ((Qplus).map α) ≫
        (R.realizedIso hj L).hom =
      tMap inj hs α := by
  let R := toResolutionFunctorOne inj hs
  have hmap :
      R.homotopyι K ≫
          (KinjIncl).map
            ((R.realizedIso hj K).inv ≫ j.toFunctor.map ((Qplus).map α) ≫
              (R.realizedIso hj L).hom) =
        (Qplus).map α ≫ R.homotopyι L :=
    (R.homotopyι_map_commSq j hj α).w
  exact t_map_unique inj hs α hmap

end InjRes

end CochainComplex
