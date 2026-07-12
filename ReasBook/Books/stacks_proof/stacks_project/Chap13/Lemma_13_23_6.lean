import Mathlib
import Mathlib.CategoryTheory.Localization.Predicate
import StacksProject_2024.Chap04.Lemma_4_2_18
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open CochainComplex
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 13.23.6: the quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms
whose images in the ambient homotopy category are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.plus 𝒜).ι

scoped[CategoryTheory] notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A

/-- Helper for Lemma 13.23.6: the unbounded derived-category quotient sends bounded-below
homotopy objects to bounded-below derived objects. -/
theorem qh_obj_mem_t_plus
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.plus 𝒜 K := by
    simpa [K, HomotopyCategory.plus] using X.property
  rcases hK with ⟨n, hn⟩
  let _ : K.IsStrictlyGE n := by simpa [K] using hn
  let _ : K.IsGE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
  exact (t.plus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

/-- Helper for Lemma 13.23.6: the canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow
    :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  (t.plus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_plus

/-- Helper for Lemma 13.23.6: the canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)` sends
bounded-below quasi-isomorphisms to isomorphisms. -/
private theorem mapBoundedBelowHomotopyToDerivedBelow_map_isIso
    {X Y : K⁺(𝒜)} (f : X ⟶ Y) (hf : Qis⁺(𝒜) f) :
    IsIso (mapBoundedBelowHomotopyToDerivedBelow.map f) := by
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  have hUnderlying :
      IsIso (((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Forget to the ambient homotopy category and use the ordinary derived localization.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.plus 𝒜).ι.map f)
      (by simpa [boundedBelowHomotopyQuasiIso] using hf)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := by
    -- Transport invertibility across the comparison with the ambient derived quotient.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus)
        f)).2 hUnderlying
  let _ : IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := hLifted
  exact isIso_of_fully_faithful ιplus (mapBoundedBelowHomotopyToDerivedBelow.map f)

/-- Helper for Lemma 13.23.6: the object property on `K^+(\mathcal A)` cutting out bounded-below
complexes whose terms are injective objects of `𝒜`. -/
abbrev boundedBelowInjectiveHomotopyProperty (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- Helper for Lemma 13.23.6: the full subcategory `K^+(\mathcal I)` of bounded-below complexes
with injective terms. -/
abbrev boundedBelowInjectiveHomotopyCat (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

namespace boundedBelowInjectiveHomotopyCat

/-- Helper for Lemma 13.23.6: an object of `K^+(\mathcal I)` is represented by a bounded-below
cochain complex. -/
theorem plus (I : K⁺ᵢ(𝒜)) :
    CochainComplex.plus 𝒜 I.obj.obj.as := by
  simpa [HomotopyCategory.plus] using I.obj.property

/-- Helper for Lemma 13.23.6: the representing complex of an object of `K^+(\mathcal I)` has
injective terms. -/
theorem term_injective (I : K⁺ᵢ(𝒜)) (n : ℤ) :
    Injective (I.obj.obj.as.X n) := by
  simpa using I.property n

/-- Helper for Lemma 13.23.6: the representing complex of an object of `K^+(\mathcal I)` is
K-injective. -/
theorem isKInjective (I : K⁺ᵢ(𝒜)) :
    CochainComplex.IsKInjective I.obj.obj.as := by
  let C : CochainComplex 𝒜 ℤ := I.obj.obj.as
  have hC : CochainComplex.plus 𝒜 C := by
    simpa [C] using plus I
  obtain ⟨a, ha⟩ := hC
  let _ : C.IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective (C.X n) := by
    intro n
    simpa [C] using term_injective I n
  simpa [C] using CochainComplex.isKInjective_of_injective C a

end boundedBelowInjectiveHomotopyCat

/-- Helper for Lemma 13.23.6: a homotopy resolution functor chooses, functorially on
`K^+(\mathcal A)`, a bounded-below injective replacement together with a quasi-isomorphism from
the identity. -/
structure HomotopyResolutionFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] where
  /-- The underlying functor `K^+(\mathcal A) ⥤ K^+(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a bounded-below complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphisms are quasi-isomorphisms. -/
  quasiIso_app (K : K⁺(𝒜)) : Qis⁺(𝒜) (ι.app K)

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "KinjIncl" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜))
local notation "IToD" => KinjIncl ⋙ Q

/- Domain-style sampling for Lemma 13.23.6:
- primary domain: localization of the bounded-below homotopy category at quasi-isomorphisms and
  the comparison with bounded-below complexes of injectives;
- sampled owner declarations:
  `Functor.IsLocalization`,
  `Localization.lift`,
  `Localization.fac`,
  `Localization.liftNatIso`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`;
- best owner abstraction: the core/canonical factorization of a resolution functor through
  `D^+(\mathcal A)` is owned by `Localization.lift` for the localization functor
  `Q : K^+(\mathcal A) ⥤ D^+(\mathcal A)`, while the source-facing uniqueness statement should be
  expressed through the canonical lifting isomorphism API rather than by strict functor equality;
- primitive data: the functor `j.toFunctor : K^+(\mathcal A) ⥤ K^+(\mathcal I)` and the fact
  that it inverts bounded-below quasi-isomorphisms;
- derived API: the factorization through `D^+(\mathcal A)` and the resulting quasi-inverse
  equivalence statement for that factorization.

Source/core/bridge triage:
- `source-facing`: the canonical factorization of a homotopy resolution functor through
  `D^+(\mathcal A)` and its quasi-inverse equivalence statement;
- `core/canonical`: the canonical injective-to-derived functor
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`;
- `bridge/view`: the quasi-inverse natural isomorphisms obtained by combining the chosen
  homotopy resolution functor with the bounded-below injective Hom-to-derived bijection.
-/

namespace HomotopyResolutionFunctor

/-- Helper for Lemma 13.23.6: morphisms between bounded-below injective complexes are detected
faithfully after passing to `D^+(\mathcal A)`. -/
private theorem iToD_map_bijective (X Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
          mapBoundedBelowHomotopyToDerivedBelow).map : (X ⟶ Y) → _) := by
  let Q' : K⁺(𝒜) ⥤ D⁺(𝒜) := mapBoundedBelowHomotopyToDerivedBelow
  let KinjIncl' : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
    ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  let IToD' : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := KinjIncl' ⋙ Q'
  let KplusIncl := (ObjectProperty.ι (HomotopyCategory.plus 𝒜) : K⁺(𝒜) ⥤ _)
  let Qplus := KplusIncl ⋙ DerivedCategory.Qh
  let DplusIncl := (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) : D⁺(𝒜) ⥤ _)
  -- First forget the injective structure inside the bounded-below homotopy category.
  have hIncl :
      Function.Bijective
        (KinjIncl'.map : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
    simpa [KinjIncl'] using (Functor.FullyFaithful.ofFullyFaithful KinjIncl').map_bijective X Y
  -- Then compare `K^+(\mathcal A) ⟶ D^+(\mathcal A)` with the ambient derived localization.
  have hQ :
      Function.Bijective
        (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) := by
    have hAmbient :
        Function.Bijective
          (Qplus.map :
            (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      have hKplusIncl :
          Function.Bijective
            (KplusIncl.map :
              (X.obj ⟶ Y.obj) → (X.obj.obj ⟶ Y.obj.obj)) := by
        simpa using
          (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X.obj Y.obj
      have hQh :
          Function.Bijective
            (DerivedCategory.Qh.map :
              (X.obj.obj ⟶ Y.obj.obj) →
                (DerivedCategory.Qh.obj X.obj.obj ⟶ DerivedCategory.Qh.obj Y.obj.obj)) := by
        let _ : CochainComplex.IsKInjective Y.obj.obj.as :=
          boundedBelowInjectiveHomotopyCat.isKInjective Y
        simpa using
          CochainComplex.IsKInjective.Qh_map_bijective (K := X.obj.obj) (L := Y.obj.obj.as)
      simpa [Functor.comp_map] using hQh.comp hKplusIncl
    have hDplusIncl :
        Function.Bijective
          (DplusIncl.map :
            (Q'.obj X.obj ⟶ Q'.obj Y.obj) →
              (DplusIncl.obj (Q'.obj X.obj) ⟶ DplusIncl.obj (Q'.obj Y.obj))) := by
      simpa using
        (Functor.FullyFaithful.ofFullyFaithful DplusIncl).map_bijective
          (Q'.obj X.obj) (Q'.obj Y.obj)
    have hcomp :
        DplusIncl.map ∘
            (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) =
          (Qplus.map : (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      funext f
      rfl
    exact (Function.Bijective.of_comp_iff' hDplusIncl _).mp (hcomp ▸ hAmbient)
  simpa [IToD', Q', KinjIncl', Functor.comp_map] using hQ.comp hIncl

/-- Helper for Lemma 13.23.6: a homotopy resolution functor sends bounded-below
quasi-isomorphisms to isomorphisms. -/
private theorem isInvertedBy (j : HomotopyResolutionFunctor 𝒜) :
    MorphismProperty.IsInvertedBy (Qis⁺(𝒜)) j.toFunctor := by
  intro X Y f hf
  have hfQ : IsIso ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map f) :=
    mapBoundedBelowHomotopyToDerivedBelow_map_isIso f hf
  have hιX :
      IsIso ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map (j.ι.app X)) :=
    mapBoundedBelowHomotopyToDerivedBelow_map_isIso (j.ι.app X) (j.quasiIso_app X)
  have hιY :
      IsIso ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map (j.ι.app Y)) :=
    mapBoundedBelowHomotopyToDerivedBelow_map_isIso (j.ι.app Y) (j.quasiIso_app Y)
  have hIToD :
      IsIso (Functor.map IToD (j.toFunctor.map f)) := by
    let qιX :=
      (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map (j.ι.app X)
    let qιY :=
      (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map (j.ι.app Y)
    let qf := (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map f
    have hnat := congrArg (Functor.map Q) (j.ι.naturality f)
    rw [Functor.map_comp, Functor.comp_map, Functor.map_comp] at hnat
    have hEq :
        Functor.map IToD (j.toFunctor.map f) =
          inv qιX ≫ qf ≫ qιY := by
      have h1 :
          Functor.map IToD (j.toFunctor.map f) =
            inv qιX ≫ (qιX ≫ Functor.map IToD (j.toFunctor.map f)) := by
        simp [qιX]
      have h2 :
          inv qιX ≫ (qιX ≫ Functor.map IToD (j.toFunctor.map f)) =
            inv qιX ≫ (qf ≫ qιY) := by
        simpa [qιX, qιY, qf, Functor.comp_map] using
          congrArg (fun k ↦ inv qιX ≫ k) hnat.symm
      have h3 : inv qιX ≫ (qf ≫ qιY) = inv qιX ≫ qf ≫ qιY := by
        rfl
      exact h1.trans (h2.trans h3)
    let _ : IsIso qιX := by simpa [qιX] using hιX
    let _ : IsIso qf := by simpa [qf] using hfQ
    let _ : IsIso qιY := by simpa [qιY] using hιY
    have hCompIso :
        IsIso (inv qιX ≫ qf ≫ qιY) := by
      let eιX : _ := asIso qιX
      let ef : _ := asIso qf
      let eιY : _ := asIso qιY
      refine ⟨⟨eιY.inv ≫ ef.inv ≫ eιX.hom, ?_, ?_⟩⟩
      · simp [eιX, ef, eιY, Category.assoc]
      · simp [eιX, ef, eιY, Category.assoc]
    rw [hEq]
    exact hCompIso
  obtain ⟨g, hg⟩ :=
    (iToD_map_bijective (X := j.toFunctor.obj Y) (Y := j.toFunctor.obj X)).surjective
      (inv (Functor.map IToD (j.toFunctor.map f)))
  have hleft : j.toFunctor.map f ≫ g = 𝟙 _ := by
    apply (iToD_map_bijective (X := j.toFunctor.obj X) (Y := j.toFunctor.obj X)).injective
    change Functor.map IToD (j.toFunctor.map f ≫ g) = Functor.map IToD (𝟙 _)
    rw [Functor.map_comp, hg, Functor.map_id]
    simp
  have hright : g ≫ j.toFunctor.map f = 𝟙 _ := by
    apply (iToD_map_bijective (X := j.toFunctor.obj Y) (Y := j.toFunctor.obj Y)).injective
    change Functor.map IToD (g ≫ j.toFunctor.map f) = Functor.map IToD (𝟙 _)
    rw [Functor.map_comp, hg, Functor.map_id]
    simp
  exact ⟨⟨g, hleft, hright⟩⟩

/-- Helper for Lemma 13.23.6: every bounded-below derived object is represented by a
bounded-below homotopy object. -/
noncomputable def boundedBelowDerivedPreimage (X : D⁺(𝒜)) :
    Σ Y : K⁺(𝒜), X ≅ (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).obj Y := by
  let n : ℤ := Classical.choose X.property
  let hn : X.obj.IsGE n := Classical.choose_spec X.property
  let _ : X.obj.IsGE n := hn
  let hrep := DerivedCategory.exists_iso_Q_obj_of_isGE X.obj n
  let K : CochainComplex 𝒜 ℤ := Classical.choose hrep
  let hK : K.IsStrictlyGE n := Classical.choose (Classical.choose_spec hrep)
  let e : X.obj ≅ DerivedCategory.Q.obj K :=
    Classical.choice (Classical.choose_spec (Classical.choose_spec hrep))
  let Y : K⁺(𝒜) := ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj K, by
    refine ⟨n, ?_⟩
    simpa [HomotopyCategory.quotient_obj_as] using hK⟩
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let eQ :
      ιplus.obj
          ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).obj Y) ≅
        DerivedCategory.Q.obj K := by
    calc
      ιplus.obj
          ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).obj Y) ≅
        DerivedCategory.Qh.obj Y.obj :=
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus).app Y
      _ ≅ DerivedCategory.Q.obj K := by
        simpa [Y] using (DerivedCategory.quotientCompQhIso 𝒜).app K
  exact ⟨Y, (Functor.FullyFaithful.ofFullyFaithful ιplus).preimageIso (e ≪≫ eQ.symm)⟩

/-- Helper for Lemma 13.23.6: the canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)` is
essentially surjective. -/
theorem q_essSurj : Functor.EssSurj Q :=
  Functor.essSurj_of_objwise_iso Q
    (fun X ↦ (boundedBelowDerivedPreimage X).1)
    (fun X ↦ (boundedBelowDerivedPreimage X).2)

/-- Helper for Lemma 13.23.6: the comparison morphisms identify the bounded-below localization
with first resolving and then passing to `D^+(\mathcal A)`. -/
private noncomputable def toDerivedIso (j : HomotopyResolutionFunctor 𝒜) :
    Q ≅ j.toFunctor ⋙ IToD := by
  let τ : Q ⟶ j.toFunctor ⋙ IToD :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight j.ι Q ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom
  have hτ : ∀ X, IsIso (τ.app X) := by
    intro X
    have hι :
        IsIso ((Functor.whiskerRight j.ι Q).app X) := by
      simpa using
        mapBoundedBelowHomotopyToDerivedBelow_map_isIso (j.ι.app X) (j.quasiIso_app X)
    change IsIso
      ((Functor.leftUnitor Q).inv.app X ≫
        (Functor.whiskerRight j.ι Q).app X ≫
        (Functor.associator j.toFunctor KinjIncl Q).hom.app X)
    infer_instance
  exact NatIso.ofComponents (fun X ↦ asIso (τ.app X)) (fun f ↦ τ.naturality f)

/-- Helper for Lemma 13.23.6: the canonical functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)` is an
equivalence once a homotopy resolution functor has been fixed. -/
private theorem injective_homotopy_to_derived_isEquivalence
    (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence IToD := by
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := IToD
  obtain ⟨hFF⟩ :
      Nonempty F.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    simpa [F] using iToD_map_bijective (X := X) (Y := Y)
  let _ : F.Full := hFF.full
  let _ : F.Faithful := hFF.faithful
  let _ : Functor.EssSurj Q := q_essSurj
  simpa [F] using F.fully_faithful_isEquivalence_of_objwise_iso
    (fun X ↦ j.toFunctor.obj (Functor.objPreimage Q X))
    (fun X ↦
      (Functor.objObjPreimageIso Q X).symm ≪≫
        j.toDerivedIso.app (Functor.objPreimage Q X))

/-- Helper for Lemma 13.23.6: the factorization functor is the quasi-inverse to the canonical
injective-to-derived functor. -/
noncomputable abbrev lift (j : HomotopyResolutionFunctor 𝒜) :
    D⁺(𝒜) ⥤ K⁺ᵢ(𝒜) :=
  letI : Functor.IsEquivalence IToD := injective_homotopy_to_derived_isEquivalence j
  (Functor.asEquivalence IToD).inverse

/-- Helper for Lemma 13.23.6: the identity of `D^+(\mathcal A)` is isomorphic to resolving and
then applying the canonical functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)`. -/
private noncomputable def lift_unitIso (j : HomotopyResolutionFunctor 𝒜) :
    𝟭 (D⁺(𝒜)) ≅ j.lift ⋙ IToD := by
  letI : Functor.IsEquivalence IToD := injective_homotopy_to_derived_isEquivalence j
  simpa [lift] using (Functor.asEquivalence IToD).counitIso.symm

/-- Lemma 13.23.6: the canonical localization lift of a homotopy resolution functor is an
equivalence of categories, with quasi-inverse the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)`. -/
@[stacks 05TK]
theorem lift_isEquivalence (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence j.lift := by
  let _ : Functor.IsEquivalence IToD := by
    simpa using injective_homotopy_to_derived_isEquivalence j
  dsimp [lift]
  infer_instance

end HomotopyResolutionFunctor

end

end CategoryTheory
