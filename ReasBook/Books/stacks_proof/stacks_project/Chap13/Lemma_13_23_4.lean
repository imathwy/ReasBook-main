import Mathlib
import StacksProject_2024.Chap13.Definition_13_23_2
import StacksProject_2024.Chap13.Lemma_13_18_3
import StacksProject_2024.Chap13.Lemma_13_18_8
import StacksProject_2024.Chap13.Lemma_13_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open CochainComplex
open DerivedCategory.TStructure

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions in the homotopy category and their
  functorial uniqueness;
- sampled owner declarations:
  `CochainComplex.ResolutionFunctorOne`,
  `CochainComplex.ResolutionFunctorOne.RealizedBy`,
  `CochainComplex.exists_homotopyResolutionFunctor_of_resolutionFunctorOne`,
  `CategoryTheory.HomotopyResolutionFunctor`;
- best owner abstraction: the primitive source-facing data is
  `CochainComplex.ResolutionFunctorOne 𝒜`, while
  `CategoryTheory.HomotopyResolutionFunctor 𝒜` is the canonical homotopy-category owner obtained
  from it by the bridge theorem `exists_homotopyResolutionFunctor_of_resolutionFunctorOne`;
- primitive data: an objectwise choice of bounded-below injective resolutions of complexes;
- derived API: existence of a homotopy resolution functor and the unique compatible natural
  isomorphism between two such functors.

Source/core/bridge triage:
- `source-facing`: existence of a resolution functor 1 and the comparison isomorphism between two
  resulting homotopy resolution functors;
- `core/canonical`: `CategoryTheory.HomotopyResolutionFunctor 𝒜`;
- `bridge/view`: the realization theorem
  `CochainComplex.exists_homotopyResolutionFunctor_of_resolutionFunctorOne`.
-/

-- Proof sketch: for each bounded-below complex `K`, Lemma 13.18.3 provides an injective
-- resolution of `K.obj`; collecting these choices gives the primitive source-facing data of a
-- resolution functor 1.
/-- If an abelian category has enough injectives, then bounded-below cochain complexes admit a
resolution functor 1 in the sense of Definition 13.23.2. -/
theorem exists_resolutionFunctorOne [EnoughInjectives 𝒜] :
    Nonempty (ResolutionFunctorOne 𝒜) := by
  classical
  refine ⟨fun K ↦ ?_⟩
  let hplus : ∃ a : ℤ, K.obj.IsStrictlyGE a := (CochainComplex.plus_iff 𝒜 K.obj).mp K.property
  let a : ℤ := Classical.choose hplus
  let hK : K.obj.IsStrictlyGE a := Classical.choose_spec hplus
  exact Classical.choice <|
    nonempty_injectiveResolution_of_eventually_isZero_homology <|
      ⟨a, fun n hn ↦ by
        let _ : K.obj.IsStrictlyGE a := hK
        simpa using K.obj.isZero_of_isGE a n hn⟩

-- Proof sketch: first choose a resolution functor 1 using `exists_resolutionFunctorOne`, then
-- apply the bridge theorem
-- `CochainComplex.exists_homotopyResolutionFunctor_of_resolutionFunctorOne` to realize it
-- in the homotopy category.
-- Route correction: the owner API for `HomotopyResolutionFunctor` and `K⁺ᵢ(𝒜)` is imported
-- directly from `Definition_13_23_2`, so validating this uniqueness proof no longer depends on
-- the later exactness file `Lemma_13_23_5`.
/-- Lemma 13.23.4 (1): if an abelian category has enough injectives, then bounded-below cochain
complexes admit a homotopy resolution functor. -/
@[stacks 013X]
theorem exists_homotopyResolutionFunctor [EnoughInjectives 𝒜] :
    Nonempty (HomotopyResolutionFunctor 𝒜) := by
  obtain ⟨R⟩ : Nonempty (ResolutionFunctorOne 𝒜) := exists_resolutionFunctorOne
  obtain ⟨J, -⟩ := exists_homotopyResolutionFunctor_of_resolutionFunctorOne R
  exact ⟨J⟩

local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KplusIncl" => (ObjectProperty.ι (HomotopyCategory.plus 𝒜) : K⁺(𝒜) ⥤ K(𝒜))
local notation "Qplus" => KplusIncl ⋙ DerivedCategory.Qh

/-- Helper for Lemma 13.23.4: the comparison morphism of a homotopy resolution functor is a
quasi-isomorphism after forgetting from `K^+(\mathcal A)` to `K(\mathcal A)`. -/
private theorem homotopyResolutionFunctor_quasiIso_ambient
    (J : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) :
    HomotopyCategory.quasiIso 𝒜 (up ℤ) (KplusIncl.map (J.ι.app X)) := by
  -- Proof comment: this is exactly the owner field `quasiIso_app`, unpacked from the inverse-image
  -- formulation on `K^+(\mathcal A)`.
  exact J.quasiIso_app X

/-- Helper for Lemma 13.23.4: morphisms from a bounded-below homotopy object to a bounded-below
injective target are detected uniquely in the ambient derived category. -/
private theorem boundedBelowHomotopyToDerived_map_bijective
    (X : K⁺(𝒜)) (Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (Qplus.map : (X ⟶ KinjIncl.obj Y) →
        (Qplus.obj X ⟶ Qplus.obj (KinjIncl.obj Y))) := by
  let hKplusIncl :
      Function.Bijective
        (KplusIncl.map :
          (X ⟶ KinjIncl.obj Y) →
            (X.obj ⟶ (KinjIncl.obj Y).obj)) := by
    simpa using
      (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X (KinjIncl.obj Y)
  let hQh :
      Function.Bijective
        (DerivedCategory.Qh.map :
          (X.obj ⟶ (KinjIncl.obj Y).obj) →
            (DerivedCategory.Qh.obj X.obj ⟶ DerivedCategory.Qh.obj (KinjIncl.obj Y).obj)) := by
    simpa using
      homotopyCategory_to_derived_bijective_of_boundedBelow_injective X.obj.as Y.toInjectivePlus
  simpa [Qplus] using hQh.comp hKplusIncl

/-- Helper for Lemma 13.23.4: a map from `X` into an injective target `Y` factors uniquely through
the canonical resolution morphism `X ⟶ J(X)`. -/
private theorem existsUnique_homotopyResolutionFunctor_lift
    (J : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) (Y : K⁺ᵢ(𝒜))
    (s : X ⟶ KinjIncl.obj Y) :
    ∃! a : J.toFunctor.obj X ⟶ Y, J.ι.app X ≫ KinjIncl.map a = s := by
  classical
  have hJ :
      IsIso (Qplus.map (J.ι.app X)) := by
    -- The resolution map becomes an isomorphism after passing to the ambient derived category.
    simpa [Qplus] using
      (Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso 𝒜 (up ℤ)) _
        (homotopyResolutionFunctor_quasiIso_ambient (J := J) X))
  let t :
      Qplus.obj (KinjIncl.obj (J.toFunctor.obj X)) ⟶ Qplus.obj (KinjIncl.obj Y) :=
    inv (Qplus.map (J.ι.app X)) ≫ Qplus.map s
  obtain ⟨g, hg⟩ :=
    (boundedBelowHomotopyToDerived_map_bijective
      (X := KinjIncl.obj (J.toFunctor.obj X)) (Y := Y)).surjective t
  let a : J.toFunctor.obj X ⟶ Y := KinjIncl.preimage g
  have ha_map : KinjIncl.map a = g := by
    simpa [a] using KinjIncl.map_preimage g
  refine ⟨a, ?_, ?_⟩
  · -- Apply the derived-category injectivity to recover the desired compatibility in `K⁺(𝒜)`.
    apply (boundedBelowHomotopyToDerived_map_bijective (X := X) (Y := Y)).injective
    rw [Functor.map_comp, ha_map, hg]
    simp [t, Category.assoc]
  · intro b hb
    -- Two lifts are equal once their images in the ambient derived category agree.
    apply KinjIncl.map_injective
    apply (boundedBelowHomotopyToDerived_map_bijective
      (X := KinjIncl.obj (J.toFunctor.obj X)) (Y := Y)).injective
    have hbQ : Qplus.map (KinjIncl.map b) = t := by
      have h := congrArg Qplus.map hb
      rw [Functor.map_comp] at h
      have h' := congrArg (fun k ↦ inv (Qplus.map (J.ι.app X)) ≫ k) h
      simpa [t, Category.assoc] using h'
    rw [ha_map]
    exact hg.trans hbQ.symm

/-- Helper for Lemma 13.23.4: for a fixed bounded-below complex, two injective resolutions admit a
unique comparison morphism. -/
private theorem existsUnique_homotopyResolutionFunctor_component
    (J J' : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) :
    ∃! a : J.toFunctor.obj X ⟶ J'.toFunctor.obj X,
      J.ι.app X ≫ KinjIncl.map a = J'.ι.app X := by
  -- This is the universal lift specialized to the canonical map into `J'(X)`.
  simpa using
    existsUnique_homotopyResolutionFunctor_lift
      (J := J) (X := X) (Y := J'.toFunctor.obj X) (s := J'.ι.app X)

/-- Helper for Lemma 13.23.4: compatibility with the canonical quasi-isomorphisms forces the
comparison morphisms to be natural. -/
private theorem homotopyResolutionFunctor_component_natural
    {J J' : HomotopyResolutionFunctor 𝒜} {X Y : K⁺(𝒜)} (f : X ⟶ Y)
    {aX : J.toFunctor.obj X ⟶ J'.toFunctor.obj X}
    {aY : J.toFunctor.obj Y ⟶ J'.toFunctor.obj Y}
    (haX : J.ι.app X ≫ KinjIncl.map aX = J'.ι.app X)
    (haY : J.ι.app Y ≫ KinjIncl.map aY = J'.ι.app Y) :
    J.toFunctor.map f ≫ aY = aX ≫ J'.toFunctor.map f := by
  have hleft :
      J.ι.app X ≫ KinjIncl.map (J.toFunctor.map f ≫ aY) = f ≫ J'.ι.app Y := by
    -- The left composite factors through `J(Y)` and then uses the chosen comparison `aY`.
    calc
      J.ι.app X ≫ KinjIncl.map (J.toFunctor.map f ≫ aY)
          = J.ι.app X ≫ KinjIncl.map (J.toFunctor.map f) ≫ KinjIncl.map aY := by
        simp [Functor.map_comp, Category.assoc]
      _ = f ≫ J.ι.app Y ≫ KinjIncl.map aY := by
        simpa [Functor.comp_map, Category.assoc] using
          congrArg (fun k ↦ k ≫ KinjIncl.map aY) (J.ι.naturality f)
      _ = f ≫ J'.ι.app Y := by rw [haY]
  have hright :
      J.ι.app X ≫ KinjIncl.map (aX ≫ J'.toFunctor.map f) = f ≫ J'.ι.app Y := by
    -- The right composite first uses `aX` and then the functoriality of `J'`.
    calc
      J.ι.app X ≫ KinjIncl.map (aX ≫ J'.toFunctor.map f)
          = J.ι.app X ≫ KinjIncl.map aX ≫ KinjIncl.map (J'.toFunctor.map f) := by
        simp [Functor.map_comp, Category.assoc]
      _ = J'.ι.app X ≫ KinjIncl.map (J'.toFunctor.map f) := by rw [haX]
      _ = f ≫ J'.ι.app Y := by
        simpa [Functor.comp_map, Category.assoc] using J'.ι.naturality f
  obtain ⟨c, -, huniq⟩ :=
    existsUnique_homotopyResolutionFunctor_lift
      (J := J) (X := X) (Y := J'.toFunctor.obj Y) (s := f ≫ J'.ι.app Y)
  calc
    J.toFunctor.map f ≫ aY = c := huniq _ hleft
    _ = aX ≫ J'.toFunctor.map f := (huniq _ hright).symm

/-- Helper for Lemma 13.23.4: every comparison morphism between two injective resolutions is an
isomorphism. -/
private theorem homotopyResolutionFunctor_component_isIso
    {J J' : HomotopyResolutionFunctor 𝒜} {X : K⁺(𝒜)}
    {a : J.toFunctor.obj X ⟶ J'.toFunctor.obj X}
    (ha : J.ι.app X ≫ KinjIncl.map a = J'.ι.app X) :
    IsIso a := by
  obtain ⟨b, hb, -⟩ := existsUnique_homotopyResolutionFunctor_component J' J X
  have hab : a ≫ b = 𝟙 (J.toFunctor.obj X) := by
    obtain ⟨c, -, huniq⟩ :=
      existsUnique_homotopyResolutionFunctor_lift
        (J := J) (X := X) (Y := J.toFunctor.obj X) (s := J.ι.app X)
    have hcomp :
        J.ι.app X ≫ KinjIncl.map (a ≫ b) = J.ι.app X := by
      -- Composing the two comparison maps still solves the same lifting problem for `J(X)`.
      calc
        J.ι.app X ≫ KinjIncl.map (a ≫ b)
            = J.ι.app X ≫ KinjIncl.map a ≫ KinjIncl.map b := by
          simp [Functor.map_comp, Category.assoc]
        _ = J'.ι.app X ≫ KinjIncl.map b := by rw [ha]
        _ = J.ι.app X := by rw [hb]
    have hid :
        J.ι.app X ≫ KinjIncl.map (𝟙 (J.toFunctor.obj X)) = J.ι.app X := by
      simp
    calc
      a ≫ b = c := huniq _ hcomp
      _ = 𝟙 (J.toFunctor.obj X) := (huniq _ hid).symm
  have hba : b ≫ a = 𝟙 (J'.toFunctor.obj X) := by
    obtain ⟨c, -, huniq⟩ :=
      existsUnique_homotopyResolutionFunctor_lift
        (J := J') (X := X) (Y := J'.toFunctor.obj X) (s := J'.ι.app X)
    have hcomp :
        J'.ι.app X ≫ KinjIncl.map (b ≫ a) = J'.ι.app X := by
      -- The symmetric argument shows that `b` is also a two-sided inverse.
      calc
        J'.ι.app X ≫ KinjIncl.map (b ≫ a)
            = J'.ι.app X ≫ KinjIncl.map b ≫ KinjIncl.map a := by
          simp [Functor.map_comp, Category.assoc]
        _ = J.ι.app X ≫ KinjIncl.map a := by rw [hb]
        _ = J'.ι.app X := by rw [ha]
    have hid :
        J'.ι.app X ≫ KinjIncl.map (𝟙 (J'.toFunctor.obj X)) = J'.ι.app X := by
      simp
    calc
      b ≫ a = c := huniq _ hcomp
      _ = 𝟙 (J'.toFunctor.obj X) := (huniq _ hid).symm
  exact ⟨⟨b, hab, hba⟩⟩

/-- Helper for Lemma 13.23.4: any natural isomorphism compatible with the canonical resolution
maps induces the corresponding objectwise lifting equation. -/
private theorem homotopyResolutionFunctorIso_component_eq
    {J J' : HomotopyResolutionFunctor 𝒜} (e : J.toFunctor ≅ J'.toFunctor)
    (he : J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι) (X : K⁺(𝒜)) :
    J.ι.app X ≫ KinjIncl.map (e.hom.app X) = J'.ι.app X := by
  -- Proof comment: evaluate the natural-transformation equality at `X` to recover the
  -- objectwise lifting condition used in the uniqueness argument.
  simpa [Category.assoc] using congrArg (fun α ↦ α.app X) he

-- Proof sketch: for two homotopy resolution functors, compare their underlying objectwise choices
-- of injective resolutions. The objectwise comparison maps are uniquely determined by the
-- compatibility with the quasi-isomorphisms from `K`, and these unique componentwise maps
-- assemble into a unique natural isomorphism.
/-- Any comparison natural isomorphism between two homotopy resolution functors compatible with
the canonical quasi-isomorphisms exists and is unique. -/
theorem existsUnique_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃! e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
  classical
  have hcomp :
      ∀ X : K⁺(𝒜), ∃ a : J.toFunctor.obj X ⟶ J'.toFunctor.obj X,
        J.ι.app X ≫ KinjIncl.map a = J'.ι.app X := by
    intro X
    obtain ⟨a, ha, -⟩ := existsUnique_homotopyResolutionFunctor_component J J' X
    exact ⟨a, ha⟩
  choose a ha using hcomp
  have hcomp' :
      ∀ X : K⁺(𝒜), ∃ b : J'.toFunctor.obj X ⟶ J.toFunctor.obj X,
        J'.ι.app X ≫ KinjIncl.map b = J.ι.app X := by
    intro X
    obtain ⟨b, hb, -⟩ := existsUnique_homotopyResolutionFunctor_component J' J X
    exact ⟨b, hb⟩
  choose b hb using hcomp'
  let η : J.toFunctor ⟶ J'.toFunctor :=
    { app := a
      naturality := fun X Y f ↦
        homotopyResolutionFunctor_component_natural
          (J := J) (J' := J') f (ha X) (ha Y) }
  let η' : J'.toFunctor ⟶ J.toFunctor :=
    { app := b
      naturality := fun X Y f ↦
        homotopyResolutionFunctor_component_natural
          (J := J') (J' := J) f (hb X) (hb Y) }
  have hηη' : η ≫ η' = 𝟙 J.toFunctor := by
    ext X
    obtain ⟨c, -, huniq⟩ :=
      existsUnique_homotopyResolutionFunctor_lift
        (J := J) (X := X) (Y := J.toFunctor.obj X) (s := J.ι.app X)
    have hcompab :
        J.ι.app X ≫ KinjIncl.map (a X ≫ b X) = J.ι.app X := by
      -- The composite `a_X ≫ b_X` solves the same universal lifting problem as the identity.
      calc
        J.ι.app X ≫ KinjIncl.map (a X ≫ b X)
            = J.ι.app X ≫ KinjIncl.map (a X) ≫ KinjIncl.map (b X) := by
          simp [Functor.map_comp, Category.assoc]
        _ = J'.ι.app X ≫ KinjIncl.map (b X) := by rw [ha X]
        _ = J.ι.app X := by rw [hb X]
    have hid :
        J.ι.app X ≫ KinjIncl.map (𝟙 (J.toFunctor.obj X)) = J.ι.app X := by
      simp
    calc
      (η ≫ η').app X = a X ≫ b X := by rfl
      _ = c := huniq _ hcompab
      _ = 𝟙 (J.toFunctor.obj X) := (huniq _ hid).symm
  have hη'η : η' ≫ η = 𝟙 J'.toFunctor := by
    ext X
    obtain ⟨c, -, huniq⟩ :=
      existsUnique_homotopyResolutionFunctor_lift
        (J := J') (X := X) (Y := J'.toFunctor.obj X) (s := J'.ι.app X)
    have hcompba :
        J'.ι.app X ≫ KinjIncl.map (b X ≫ a X) = J'.ι.app X := by
      -- The symmetric comparison shows that `b_X ≫ a_X` is also the identity.
      calc
        J'.ι.app X ≫ KinjIncl.map (b X ≫ a X)
            = J'.ι.app X ≫ KinjIncl.map (b X) ≫ KinjIncl.map (a X) := by
          simp [Functor.map_comp, Category.assoc]
        _ = J.ι.app X ≫ KinjIncl.map (a X) := by rw [hb X]
        _ = J'.ι.app X := by rw [ha X]
    have hid :
        J'.ι.app X ≫ KinjIncl.map (𝟙 (J'.toFunctor.obj X)) = J'.ι.app X := by
      simp
    calc
      (η' ≫ η).app X = b X ≫ a X := by rfl
      _ = c := huniq _ hcompba
      _ = 𝟙 (J'.toFunctor.obj X) := (huniq _ hid).symm
  let e : J.toFunctor ≅ J'.toFunctor :=
    { hom := η
      inv := η'
      hom_inv_id := hηη'
      inv_hom_id := hη'η }
  have he : J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
    -- The assembled natural isomorphism has exactly the componentwise compatibility used to build
    -- each `a_X`.
    ext X
    simpa [e, η] using ha X
  refine ⟨e, he, ?_⟩
  intro e' he'
  ext X
  have hcompat : J.ι.app X ≫ KinjIncl.map (e'.hom.app X) = J'.ι.app X :=
    homotopyResolutionFunctorIso_component_eq e' he' X
  obtain ⟨c, -, huniq⟩ := existsUnique_homotopyResolutionFunctor_component J J' X
  calc
    e'.hom.app X = c := huniq _ hcompat
    _ = a X := (huniq _ (ha X)).symm

/-- Lemma 13.23.4 (2): any two homotopy resolution functors are isomorphic by a natural
isomorphism compatible with the comparison quasi-isomorphisms. -/
@[stacks 013X]
theorem exists_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃ e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
  obtain ⟨e, he, -⟩ := existsUnique_homotopyResolutionFunctorIso J J'
  exact ⟨e, he⟩

-- Proof sketch: the compatibility with the comparison quasi-isomorphisms makes the component on
-- each bounded-below complex the unique comparison map between two injective resolutions, so this
-- is the `Subsingleton` consequence of
-- `existsUnique_homotopyResolutionFunctorIso`; the enough-injectives hypothesis is redundant once the
-- two homotopy resolution functors are already given.
/-- Lemma 13.23.4 (3): the comparison natural isomorphism between two homotopy resolution
functors is unique. -/
@[stacks 013X]
theorem subsingleton_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    Subsingleton
      { e : J.toFunctor ≅ J'.toFunctor //
          J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι } := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨e, _, huniq⟩ := existsUnique_homotopyResolutionFunctorIso J J'
  apply Subtype.ext
  calc
    a.1 = e := huniq a.1 a.2
    _ = b.1 := (huniq b.1 b.2).symm

end CategoryTheory
