import StacksProject_2024.Chap13.Remark_13_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomotopyCategory
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Remark 13.24.2: the bounded-below cochain complexes whose terms are injective
objects. -/
abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  ObjectProperty.FullSubcategory
    (fun K : Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n))

namespace InjectivePlus

/-- A bounded-below complex of injectives coerces to its underlying bounded-below complex. -/
instance : CoeOut (InjectivePlus 𝒜) (Plus 𝒜) where
  coe I := I.obj

/-- A bounded-below complex of injectives coerces to its underlying cochain complex. -/
instance : CoeOut (InjectivePlus 𝒜) (CochainComplex 𝒜 ℤ) where
  coe I := I.obj.obj

/-- Each term of a bounded-below complex of injectives is injective. -/
theorem term_mem (I : InjectivePlus 𝒜) (n : ℤ) :
    Injective ((I : CochainComplex 𝒜 ℤ).X n) := by
  simpa using I.property n

end InjectivePlus

/-- Helper for Remark 13.24.2: an injective resolution of a cochain complex is a quasi-isomorphism
to a bounded-below complex of injective objects. -/
structure InjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The resolving bounded-below complex of injective objects. -/
  complex : InjectivePlus 𝒜
  /-- The comparison map from `K` to the resolving complex. -/
  ι : K ⟶ complex
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso ι

attribute [instance] InjectiveResolution.quasiIso

namespace InjectiveResolution

/-- An injective resolution coerces to its bounded-below injective target. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (InjectiveResolution K) (InjectivePlus 𝒜) where
  coe I := I.complex

/-- An injective resolution coerces to its bounded-below target complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (InjectiveResolution K) (Plus 𝒜) where
  coe I := I.complex

/-- An injective resolution coerces to its underlying target cochain complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (InjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe I := I.complex

/-- Each term of the resolving complex in an injective resolution is injective. -/
theorem injective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) (n : ℤ) :
    Injective ((I : CochainComplex 𝒜 ℤ).X n) := by
  simpa using I.complex.term_mem n

attribute [instance] InjectiveResolution.injective

end InjectiveResolution

/-- Helper for Remark 13.24.2: a resolution functor 1 chooses an injective resolution for each
bounded-below complex. -/
abbrev ResolutionFunctorOne (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  (K : Plus 𝒜) → InjectiveResolution K.obj

end CochainComplex

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Remark 13.24.2: the bounded-below homotopy objects whose terms are injective. -/
abbrev boundedBelowInjectiveHomotopyProperty :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- Helper for Remark 13.24.2: the bounded-below homotopy category of complexes of injectives. -/
abbrev boundedBelowInjectiveHomotopyCat :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

namespace CochainComplex.InjectivePlus

/-- The quotient functor from bounded-below complexes of injectives to `K⁺(\mathcal I)`. -/
abbrev toHomotopy :
    CochainComplex.InjectivePlus 𝒜 ⥤ K⁺ᵢ(𝒜) :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).lift
    (ObjectProperty.ι
      (fun K : CochainComplex.Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n)) ⋙
        HomotopyCategory.Plus.quotient 𝒜)
    (fun I n ↦ by simpa using I.term_mem n)

end CochainComplex.InjectivePlus

namespace boundedBelowInjectiveHomotopyCat

/-- An object of `K⁺(\mathcal I)` determines its underlying bounded-below complex of injectives. -/
abbrev toInjectivePlus (I : K⁺ᵢ(𝒜)) : CochainComplex.InjectivePlus 𝒜 :=
  let K : K⁺(𝒜) := I.obj
  ⟨⟨K.obj.as, K.property⟩, fun n ↦ by
    simpa using I.property n⟩

end boundedBelowInjectiveHomotopyCat

/-- Helper for Remark 13.24.2: a homotopy resolution functor on bounded-below complexes. -/
structure HomotopyResolutionFunctor where
  /-- The underlying functor `K⁺(\mathcal A) ⥤ K⁺(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphism is a quasi-isomorphism after forgetting injectivity. -/
  quasiIso_app (K : K⁺(𝒜)) :
      (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
        (HomotopyCategory.plus 𝒜).ι (ι.app K)

end CategoryTheory

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- The chosen injective resolution `j(K)` viewed as an object of `K⁺(\mathcal I)`. -/
abbrev homotopyObj (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    K⁺ᵢ(𝒜) :=
  ⟨(Qplus).obj (R K : Plus 𝒜), fun n ↦ by
    simpa using (R K).injective n⟩

/-- The comparison map `K ⟶ j(K)` viewed in `K⁺(\mathcal A)`. -/
abbrev homotopyι (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    (Qplus).obj K ⟶ (KinjIncl).obj (R.homotopyObj K) :=
  (Qplus).map ⟨(R K).ι⟩

/-- A homotopy resolution functor realizes `R` when its object and comparison map agree with the
chosen resolutions after transport by the canonical objectwise isomorphisms. -/
def RealizedBy (R : ResolutionFunctorOne 𝒜)
    (j : CategoryTheory.HomotopyResolutionFunctor 𝒜) : Prop :=
  ∀ K : Plus 𝒜, ∃! eK : j.toFunctor.obj ((Qplus).obj K) ≅ R.homotopyObj K,
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map eK.hom = homotopyι R K

end ResolutionFunctorOne

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
  -- Proof comment: `Functor.congr_hom hs α` is exactly the left-edge transport identity
  -- coming from the strict equality `inj ⋙ s = 𝟭`.
  simpa [s, rawInclusion, Category.assoc] using
    congrArg (fun f ↦ eqToHom (obj_left_eq inj hs K).symm ≫ f) (Functor.congr_hom hs α)

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
        -- Proof comment: transport the source complex along the equality `X.left = K`; the
        -- transport map is an isomorphism, so composing it with the given quasi-isomorphism
        -- `X.hom.hom` stays a quasi-isomorphism.
        let _ : QuasiIso (eqToHom (congrArg (fun Y : Plus 𝒜 ↦ Y.obj) hK).symm) := by
          infer_instance
        let hX : QuasiIso X.hom.hom := by
          simpa [X, rawInclusion] using (inj.obj K).property
        exact (quasiIso_iff_comp_left _ _).2 hX }

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
  -- Proof comment: both sides are the same bounded-below injective target of `inj.obj K`,
  -- presented through the two owner APIs `homotopyObj` and `t`.
  rfl

abbrev tMap
    (inj : Plus 𝒜 ⥤ InjRes 𝒜) (hs : inj ⋙ s = 𝟭 (Plus 𝒜))
    {K L : Plus 𝒜} (α : K ⟶ L) :
    (toResolutionFunctorOne inj hs).homotopyObj K ⟶
      (toResolutionFunctorOne inj hs).homotopyObj L :=
  (inj ⋙ t).map α

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
  -- Route correction: keep the source proof on the comma-category square for `inj.map α`
  -- and transport that single square to `K^+(\mathcal A)`.
  dsimp [ResolutionFunctorOne.homotopyι, tMap]
  let XK := rawInclusion.obj (inj.obj K)
  let XL := rawInclusion.obj (inj.obj L)
  -- Proof comment: `inj.map α` is a morphism in the comma category, so its commutative square
  -- identifies the target map with the unique right edge over the transported left edge.
  have hcomma :
      eqToHom (obj_left_eq inj hs K).symm ≫ XK.hom ≫
          (ObjectProperty.ι
            (fun K : Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n))).map
            (rawInclusion.map (inj.map α)).right =
        α ≫ eqToHom (obj_left_eq inj hs L).symm ≫ XL.hom := by
    calc
      eqToHom (obj_left_eq inj hs K).symm ≫ XK.hom ≫
          (ObjectProperty.ι
            (fun K : Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n))).map
            (rawInclusion.map (inj.map α)).right =
        eqToHom (obj_left_eq inj hs K).symm ≫ (rawInclusion.map (inj.map α)).left ≫ XL.hom := by
          simpa [XK, XL, Category.assoc] using
            congrArg
              (fun f ↦ eqToHom (obj_left_eq inj hs K).symm ≫ f)
              (rawInclusion.map (inj.map α)).w.symm
      _ = α ≫ eqToHom (obj_left_eq inj hs L).symm ≫ XL.hom := by
        simpa [XK, XL, Category.assoc] using
          congrArg (fun f ↦ f ≫ XL.hom) (map_left_naturality inj hs α)
  -- Proof comment: applying the quotient functor turns the transported square into the desired
  -- commutative square in the bounded-below homotopy category.
  have hplus :
      ((⟨(toResolutionFunctorOne inj hs K).ι⟩ : K ⟶ XK.right.obj) ≫
          (rawInclusion.map (inj.map α)).right.hom) =
        α ≫ (⟨(toResolutionFunctorOne inj hs L).ι⟩ : L ⟶ XL.right.obj) := by
    ext i
    simpa [XK, XL, toResolutionFunctorOne_ι, rawInclusion, Category.assoc] using
      congrArg (fun f ↦ f.hom.f i) hcomma
  have hQ := congrArg (fun f ↦ (Qplus).map f) hplus
  simpa [Functor.map_comp, Category.assoc] using hQ

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
  let R := toResolutionFunctorOne inj hs
  have hprecomp :
      R.homotopyι K ≫ (KinjIncl).map a =
        R.homotopyι K ≫ (KinjIncl).map (tMap inj hs α) := by
    -- Proof comment: both candidates satisfy the same comparison square over `α`, so they agree
    -- after precomposition with the chosen quasi-isomorphism `K ⟶ j(K)`.
    exact ha.trans (t_map_commSq inj hs α).symm
  have hambient :
      (HomotopyCategory.plus 𝒜).ι.map ((KinjIncl).map a) =
        (HomotopyCategory.plus 𝒜).ι.map ((KinjIncl).map (tMap inj hs α)) := by
    let hbij :=
      homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective
        (R K).ι ((R.homotopyObj L).toInjectivePlus)
    -- Proof comment: after forgetting bounded-below structure, `R.homotopyι K` is the ambient
    -- homotopy-class of `(R K).ι`, so Remark 13.18.5 makes precomposition injective.
    apply hbij.injective
    simpa [R, ResolutionFunctorOne.homotopyι, Functor.map_comp, Category.assoc] using
      congrArg ((HomotopyCategory.plus 𝒜).ι.map) hprecomp
  have hKinj :
      (KinjIncl).map a = (KinjIncl).map (tMap inj hs α) := by
    exact (HomotopyCategory.plus 𝒜).ι.map_injective hambient
  -- Proof comment: the injective full-subcategory inclusion is faithful, so ambient equality
  -- of the underlying homotopy morphisms reflects back to `K⁺ᵢ(\mathcal A)`.
  exact (CategoryTheory.ObjectProperty.ι
    (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)).map_injective hKinj

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
