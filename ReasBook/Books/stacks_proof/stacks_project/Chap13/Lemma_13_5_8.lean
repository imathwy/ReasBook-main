import Mathlib
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap04.Lemma_4_27_21
import StacksProject_2024.Chap04.Remark_4_27_15
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Lemma_13_5_7
import StacksProject_2024.Chap13.Remark_13_5_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped MorphismPropertyOver

noncomputable section

universe v u

namespace CategoryTheory

section

/- 
Domain-style sampling:
- primary domain: morphisms of localizers and the induced functors between localization categories;
- relevant owner declarations inspected upstream:
  `Localization.LocalizerMorphism`,
  `LocalizerMorphism.localizedFunctor`,
  `LocalizerMorphism.IsLocalizedEquivalence`,
  `ObjectProperty.FullSubcategory`.

Source/core/bridge triage:
- `source-facing`: the restricted system on `P.FullSubcategory` and the hypothesis that every
  object of `D` is reached from `P.FullSubcategory` by a morphism of `S`;
- `core/canonical`: `LocalizerMorphism`, `localizedFunctor`, and
  `LocalizerMorphism.IsLocalizedEquivalence`;
- `bridge/view`: the inclusion-induced localizer morphism
  `fullSubcategoryLocalizerMorphism` and its induced localization functor
  `fullSubcategoryLocalizationFunctor`.

Primitive data here are the object property `P`, the morphism property `S`, and the inclusion
`P.ι : P.FullSubcategory ⥤ D`. The localized comparison functor and its equivalence property are
derived from the canonical localizer-morphism owner, so the public equivalence statements should
stay at that plain localizer layer. Triangulated compatibility is additional structure used only by
the companion `CommShift` and `IsTriangulated` instances below.
-/

section Localizer

variable {D : Type u} [Category.{v} D]
variable (P : ObjectProperty D)
variable (S : MorphismProperty D)

/-- The multiplicative system on `P.FullSubcategory` obtained by restricting `S` along the
inclusion `P.ι : P.FullSubcategory ⥤ D`. -/
abbrev fullSubcategoryLocalizationSystem : MorphismProperty P.FullSubcategory :=
  S.inverseImage P.ι

/-- Helper for Lemma 13.5.8: the restricted system admits right fractions once every ambient
auxiliary object can be refined back into the full subcategory by a morphism of `S`. -/
theorem fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_cover
    [IsSaturatedMultiplicativeSystem S] :
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) →
    HasRightCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
  intro hP
  refine
    { toIsMultiplicative := inferInstance
      exists_rightFraction := ?_
      ext := ?_ }
  · intro X Y φ
    -- Start from the ambient right-fraction witness and then refine its source back into `P`.
    obtain ⟨ψ, hψ⟩ :=
      (LeftFraction.mk φ.f.hom φ.s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using φ.hs)).exists_rightFraction
    obtain ⟨Z, u, hu⟩ := hP ψ.X'
    refine
      ⟨RightFraction.mk (ObjectProperty.homMk (u ≫ ψ.s))
        (by
          simpa [fullSubcategoryLocalizationSystem] using S.comp_mem _ _ hu ψ.hs)
        (ObjectProperty.homMk (u ≫ ψ.f)), ?_⟩
    -- Forgetting to `D`, this is exactly the ambient compatibility square precomposed with `u`.
    apply P.ι.map_injective
    simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hψ
  · intro X Y Y' f₁ f₂ s hs hfs
    -- Apply ambient right-cancellation and then refine the new source back into `P`.
    obtain ⟨X', t, ht, hfac⟩ :=
      HasRightCalculusOfFractions.ext f₁.hom f₂.hom s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using hs)
        (by simpa using congrArg (fun k ↦ k.hom) hfs)
    obtain ⟨Z, u, hu⟩ := hP X'
    refine ⟨Z, ObjectProperty.homMk (u ≫ t), ?_, ?_⟩
    · simpa [fullSubcategoryLocalizationSystem] using S.comp_mem _ _ hu ht
    · apply P.ι.map_injective
      simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hfac

/-- Helper for Lemma 13.5.8: the restricted arrows are exactly the arrows of the full subcategory
whose image in the ambient localization becomes an isomorphism. -/
theorem fullSubcategoryLocalizationSystem_eq_inverseImage_isomorphisms_of_localized_inclusion
    [IsSaturatedMultiplicativeSystem S] :
    fullSubcategoryLocalizationSystem P S =
      (isomorphisms S.Localization).inverseImage (P.ι ⋙ S.Q) := by
  ext X Y f
  constructor
  · intro hf
    -- Any restricted denominator is inverted by the ambient localization functor.
    simpa [fullSubcategoryLocalizationSystem] using
      (Localization.inverts S.Q S f.hom (by simpa [fullSubcategoryLocalizationSystem] using hf))
  · intro hf
    -- Conversely, saturation identifies the inverse-image isomorphisms with `S` itself.
    have hsat :
        S.saturatedClosure (P.ι.map f) := by
      simpa [MorphismProperty.saturatedClosure] using hf
    exact (MorphismProperty.saturatedClosure_le S le_rfl) _ hsat

/-- The localizer morphism induced by the inclusion `P.FullSubcategory ⥤ D`. -/
abbrev fullSubcategoryLocalizerMorphism :
    LocalizerMorphism (fullSubcategoryLocalizationSystem P S) S :=
  LocalizerMorphism.ofEq rfl

/-- The functor on localizations induced by the inclusion `P.FullSubcategory ⥤ D`. -/
noncomputable abbrev fullSubcategoryLocalizationFunctor :
    (fullSubcategoryLocalizationSystem P S).Localization ⥤ S.Localization :=
  (fullSubcategoryLocalizerMorphism P S).localizedFunctor
    (fullSubcategoryLocalizationSystem P S).Q S.Q

/-- Helper for Lemma 13.5.8: the localized inclusion is essentially surjective once every
ambient object is covered by an `S`-morphism from the full subcategory. -/
theorem fullSubcategoryLocalizationFunctor_essSurj
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizationFunctor P S).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let X := S.Q.objPreimage Y
  -- Choose an `S`-cover of a representative of `Y`.
  obtain ⟨X', s, hs⟩ := hP X
  refine ⟨(fullSubcategoryLocalizationSystem P S).Q.obj X', ⟨?_⟩⟩
  -- Compare the two localization functors through the canonical comparison square,
  -- then invert the chosen denominator and the ambient essential-surjectivity isomorphism.
  let e₁ :
      (fullSubcategoryLocalizationFunctor P S).obj
          ((fullSubcategoryLocalizationSystem P S).Q.obj X') ≅
        S.Q.obj (P.ι.obj X') :=
    (((fullSubcategoryLocalizerMorphism P S).catCommSq
      (fullSubcategoryLocalizationSystem P S).Q S.Q).iso.app X').symm
  let e₂ : S.Q.obj (P.ι.obj X') ≅ S.Q.obj X := by
    letI := Localization.inverts S.Q S _ hs
    exact asIso (S.Q.map s)
  let e₃ : S.Q.obj X ≅ Y := S.Q.objObjPreimageIso Y
  exact e₁ ≪≫ e₂ ≪≫ e₃

/- The remaining source-faithful step is the Hom-colimit comparison: use
`right_localization_hom_colimit` for the restricted and ambient systems, compare the diagrams via
the denominator-refinement functor, and then invoke finality on the opposite denominator
categories. -/
/-- Helper for Lemma 13.5.8: conjugating by isomorphisms gives a bijection on Hom-sets. -/
private theorem hom_transport_bijective {C : Type u} [Category.{v} C]
    {X₁ X₂ Y₁ Y₂ : C} (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) :
    Function.Bijective (fun f : X₂ ⟶ Y₂ ↦ eX.hom ≫ f ≫ eY.inv) := by
  constructor
  · intro f g hfg
    -- Proof comment: apply the inverse transport on both sides to cancel the chosen isomorphisms.
    simpa [Category.assoc] using congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) hfg
  · intro f
    -- Proof comment: the inverse transport is given by conjugating with the opposite isomorphisms.
    refine ⟨eX.inv ≫ f ≫ eY.hom, ?_⟩
    simp [Category.assoc]

/-- Helper for Lemma 13.5.8: forgetting the full-subcategory structure turns a restricted roof
into the ambient roof with the same numerator and denominator. -/
private abbrev fullSubcategory_rightFraction_toAmbient
    {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y) :
    S.RightFraction (P.ι.obj X) (P.ι.obj Y) :=
  RightFraction.mk φ.s.hom
    (by simpa [fullSubcategoryLocalizationSystem] using φ.hs) φ.f.hom

/-- Helper for Lemma 13.5.8: after transporting through the localizer comparison square, the
unfolded image of a restricted roof is the expected ambient numerator over denominator. -/
private theorem fullSubcategoryLocalizationFunctor_transport_map_of_right_fraction_data
    [IsSaturatedMultiplicativeSystem S] {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y)
    [IsIso (S.Q.map φ.s.hom)]
    [IsIso ((fullSubcategoryLocalizationFunctor P S).map
      ((fullSubcategoryLocalizationSystem P S).Q.map φ.s))] :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv =
      inv (S.Q.map φ.s.hom) ≫ S.Q.map φ.f.hom := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eA : S.Q.obj (P.ι.obj φ.X') ≅ G.obj (W.Q.obj φ.X') := η.app φ.X'
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  have hs_nat :
      S.Q.map φ.s.hom ≫ eX.hom = eA.hom ≫ G.map (W.Q.map φ.s) := by
    -- Proof comment: naturality for the comparison isomorphism identifies the two denominators.
    simpa [W, G, η, Functor.comp_map] using NatTrans.naturality η.hom φ.s
  have hf_nat :
      S.Q.map φ.f.hom ≫ eY.hom = eA.hom ≫ G.map (W.Q.map φ.f) := by
    -- Proof comment: the same naturality relation transports the numerator.
    simpa [W, G, η, Functor.comp_map] using NatTrans.naturality η.hom φ.f
  have hsinv :
      eX.hom ≫ inv (G.map (W.Q.map φ.s)) =
        inv (S.Q.map φ.s.hom) ≫ eA.hom := by
    -- Proof comment: invert the denominator square once so the final computation is a flat `calc`.
    apply (cancel_mono (G.map (W.Q.map φ.s))).1
    calc
      (eX.hom ≫ inv (G.map (W.Q.map φ.s))) ≫ G.map (W.Q.map φ.s)
          = eX.hom := by
              simp
      _ = inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.s.hom ≫ eX.hom) := by
              simp
      _ = inv (S.Q.map φ.s.hom) ≫ (eA.hom ≫ G.map (W.Q.map φ.s)) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ inv (S.Q.map φ.s.hom) ≫ k) hs_nat
      _ = (inv (S.Q.map φ.s.hom) ≫ eA.hom) ≫ G.map (W.Q.map φ.s) := by
              simp [Category.assoc]
  -- Proof comment: now rewrite the transported denominator and numerator once, then cancel the
  -- target comparison isomorphism.
  have htransport :
      eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv =
        inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.f.hom ≫ eY.hom) ≫ eY.inv := by
    show
        eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv =
          inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.f.hom ≫ eY.hom) ≫ eY.inv
    calc
      eX.hom ≫ (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ eY.inv
          = (eX.hom ≫ inv (G.map (W.Q.map φ.s))) ≫ G.map (W.Q.map φ.f) ≫ eY.inv := by
              simp [Category.assoc]
      _ = (inv (S.Q.map φ.s.hom) ≫ eA.hom) ≫ G.map (W.Q.map φ.f) ≫ eY.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ G.map (W.Q.map φ.f) ≫ eY.inv) hsinv
      _ = inv (S.Q.map φ.s.hom) ≫ (eA.hom ≫ G.map (W.Q.map φ.f)) ≫ eY.inv := by
              simp [Category.assoc]
      _ = inv (S.Q.map φ.s.hom) ≫ (S.Q.map φ.f.hom ≫ eY.hom) ≫ eY.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ inv (S.Q.map φ.s.hom) ≫ k ≫ eY.inv) hf_nat.symm
  simpa [Category.assoc] using htransport
/-- Helper for Lemma 13.5.8: after transporting through the localizer comparison square, the
image of a restricted right fraction is exactly the corresponding ambient right fraction. -/
private theorem fullSubcategoryLocalizationFunctor_transport_rightFraction
    [IsSaturatedMultiplicativeSystem S] {X Y : P.FullSubcategory}
    (φ : (fullSubcategoryLocalizationSystem P S).RightFraction X Y) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    eX.hom ≫ G.map (φ.map W.Q (Localization.inverts W.Q W)) ≫ eY.inv =
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ).map S.Q
        (Localization.inverts S.Q S) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eA : S.Q.obj (P.ι.obj φ.X') ≅ G.obj (W.Q.obj φ.X') := η.app φ.X'
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W _ φ.hs
  letI : IsIso (S.Q.map φ.s.hom) := by
    simpa [W, fullSubcategoryLocalizationSystem] using
      (Localization.inverts S.Q S φ.s.hom φ.hs)
  letI : IsIso (G.map (W.Q.map φ.s)) := by infer_instance
  -- Proof comment: after unfolding `RightFraction.map`, the comparison is the flat transport
  -- identity proved just above.
  simpa [fullSubcategory_rightFraction_toAmbient, MorphismProperty.RightFraction.map,
    Functor.map_comp, map_inv, Category.assoc] using
    (fullSubcategoryLocalizationFunctor_transport_map_of_right_fraction_data
      (P := P) (S := S) φ)

/-- Helper for Lemma 13.5.8: refining the source of an ambient right fraction by an arrow of `S`
does not change the represented localized morphism. -/
private theorem ambient_right_fraction_precompose_mem_eq
    [IsSaturatedMultiplicativeSystem S] {A B : D} (φ : S.RightFraction A B) {A' : D}
    (u : A' ⟶ φ.X') (hu : S u) :
    (RightFraction.mk (u ≫ φ.s) (S.comp_mem _ _ hu φ.hs) (u ≫ φ.f)).map S.Q
        (Localization.inverts S.Q S) =
      φ.map S.Q (Localization.inverts S.Q S) := by
  -- Proof comment: this is the canonical `map_eq_iff` refinement witness with identity on the
  -- old roof and precomposition by `u` on the refined roof.
  symm
  exact (MorphismProperty.RightFraction.map_eq_iff S.Q S φ
    (RightFraction.mk (u ≫ φ.s) (S.comp_mem _ _ hu φ.hs) (u ≫ φ.f))).2
      ⟨A', u, 𝟙 _, by simp, by simp,
        by simpa [Category.assoc] using S.comp_mem _ _ hu φ.hs⟩

/-- Helper for Lemma 13.5.8: on localization objects coming directly from
`P.FullSubcategory`, the induced functor is bijective on morphisms. -/
private theorem fullSubcategoryLocalizationFunctor_conjugated_map_surjective_on_Q_obj
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s)
    (X Y : P.FullSubcategory) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    Function.Surjective
      (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : HasRightCalculusOfFractions W :=
    fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_cover
      (P := P) (S := S) hP
  dsimp [W, G, η, eX, eY]
  intro f
  -- Proof comment: represent the ambient morphism by a right roof and refine its source back
  -- into `P`; the refined roof then has a canonical preimage in the restricted localization.
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S f
  obtain ⟨Z, u, hu⟩ := hP φ.X'
  let ψ : W.RightFraction X Y :=
    RightFraction.mk (ObjectProperty.homMk (u ≫ φ.s))
      (by
        simpa [W, fullSubcategoryLocalizationSystem, Category.assoc] using
          S.comp_mem _ _ hu φ.hs)
      (ObjectProperty.homMk (u ≫ φ.f))
  refine ⟨ψ.map W.Q (Localization.inverts W.Q W), ?_⟩
  calc
    eX.hom ≫ G.map (ψ.map W.Q (Localization.inverts W.Q W)) ≫ eY.inv
        =
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) ψ).map S.Q
        (Localization.inverts S.Q S) := by
          simpa [W, G, η, eX, eY] using
            fullSubcategoryLocalizationFunctor_transport_rightFraction
              (P := P) (S := S) ψ
    _ = φ.map S.Q (Localization.inverts S.Q S) := by
      -- Proof comment: precomposing an ambient roof by the `S`-cover `u` does not change its
      -- image in the ambient localization.
      simpa [ψ, fullSubcategory_rightFraction_toAmbient] using
        ambient_right_fraction_precompose_mem_eq (S := S) φ u hu
    _ = f := hφ.symm

/-- Helper for Lemma 13.5.8: after conjugating into the ambient localization, equality of images
comes from a common refined roof already inside `P.FullSubcategory`. -/
private theorem fullSubcategoryLocalizationFunctor_conjugated_map_injective_on_Q_obj
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s)
    (X Y : P.FullSubcategory) :
    let W := fullSubcategoryLocalizationSystem P S
    let G := fullSubcategoryLocalizationFunctor P S
    let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
    let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
    let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
    Function.Injective
      (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  letI : HasRightCalculusOfFractions W :=
    fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_cover
      (P := P) (S := S) hP
  dsimp [W, G, η, eX, eY]
  intro g₁ g₂ hgg
  -- Proof comment: write both restricted morphisms as roofs, move the equality to the ambient
  -- localization, refine the ambient common source back into `P`, and compare the restricted roofs.
  obtain ⟨φ₁, hφ₁⟩ := Localization.exists_rightFraction W.Q W g₁
  obtain ⟨φ₂, hφ₂⟩ := Localization.exists_rightFraction W.Q W g₂
  have hmapEq :
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₁).map S.Q
          (Localization.inverts S.Q S)
        =
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₂).map S.Q
          (Localization.inverts S.Q S) := by
    calc
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₁).map S.Q
          (Localization.inverts S.Q S)
          =
        eX.hom ≫ G.map g₁ ≫ eY.inv := by
            simpa [W, G, η, eX, eY, hφ₁] using
              (fullSubcategoryLocalizationFunctor_transport_rightFraction
                (P := P) (S := S) φ₁).symm
      _ = eX.hom ≫ G.map g₂ ≫ eY.inv := hgg
      _ =
        (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₂).map S.Q
          (Localization.inverts S.Q S) := by
            simpa [W, G, η, eX, eY, hφ₂] using
              fullSubcategoryLocalizationFunctor_transport_rightFraction
                (P := P) (S := S) φ₂
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff S.Q S
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₁)
      (fullSubcategory_rightFraction_toAmbient (P := P) (S := S) φ₂)).1 hmapEq
  obtain ⟨Z', u, hu⟩ := hP Z
  have hrel : MorphismProperty.RightFractionRel φ₁ φ₂ := by
    -- Proof comment: precompose the ambient common refinement by the chosen cover of `Z` so the
    -- resulting comparison lives again in the restricted system.
    refine ⟨Z', ObjectProperty.homMk (u ≫ t₁), ObjectProperty.homMk (u ≫ t₂), ?_, ?_, ?_⟩
    · apply P.ι.map_injective
      simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hst
    · apply P.ι.map_injective
      simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hft
    · simpa [W, fullSubcategoryLocalizationSystem, Category.assoc] using
        S.comp_mem _ _ hu ht
  have hfracEq :
      φ₁.map W.Q (Localization.inverts W.Q W) =
        φ₂.map W.Q (Localization.inverts W.Q W) := by
    exact (MorphismProperty.RightFraction.map_eq_iff W.Q W φ₁ φ₂).2 hrel
  rw [hφ₁, hφ₂]
  exact hfracEq

/-- Helper for Lemma 13.5.8: on localization objects coming directly from
`P.FullSubcategory`, the induced functor is bijective on morphisms. -/
private theorem fullSubcategoryLocalizationFunctor_map_bijective_on_Q_obj
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s)
    (X Y : P.FullSubcategory) :
    Function.Bijective
      ((fullSubcategoryLocalizationFunctor P S).map :
        ((fullSubcategoryLocalizationSystem P S).Q.obj X ⟶
            (fullSubcategoryLocalizationSystem P S).Q.obj Y) →
          ((fullSubcategoryLocalizationFunctor P S).obj
              ((fullSubcategoryLocalizationSystem P S).Q.obj X) ⟶
            (fullSubcategoryLocalizationFunctor P S).obj
              ((fullSubcategoryLocalizationSystem P S).Q.obj Y))) := by
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  let η := ((fullSubcategoryLocalizerMorphism P S).catCommSq W.Q S.Q).iso
  let eX : S.Q.obj (P.ι.obj X) ≅ G.obj (W.Q.obj X) := η.app X
  let eY : S.Q.obj (P.ι.obj Y) ≅ G.obj (W.Q.obj Y) := η.app Y
  have hTarget :
      Function.Bijective
        (fun f : G.obj (W.Q.obj X) ⟶ G.obj (W.Q.obj Y) ↦ eX.hom ≫ f ≫ eY.inv) :=
    hom_transport_bijective eX eY
  have hConjugated :
      Function.Bijective
        (fun g : W.Q.obj X ⟶ W.Q.obj Y ↦ eX.hom ≫ G.map g ≫ eY.inv) := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: injectivity is controlled in the ambient localization by refining a
      -- common source back into the full subcategory.
      simpa [W, G, η, eX, eY] using
        fullSubcategoryLocalizationFunctor_conjugated_map_injective_on_Q_obj
          (P := P) (S := S) hP X Y
    · -- Proof comment: surjectivity follows by refining any ambient roof into one whose source
      -- already lies in `P.FullSubcategory`.
      simpa [W, G, η, eX, eY] using
        fullSubcategoryLocalizationFunctor_conjugated_map_surjective_on_Q_obj
          (P := P) (S := S) hP X Y
  exact (Function.Bijective.of_comp_iff' hTarget _).mp hConjugated

/-- Helper for Lemma 13.5.8: after comparing the two right-fraction Hom colimits along the
denominator-refinement functor, the localized inclusion is fully faithful. -/
noncomputable def fullSubcategoryLocalizationFunctor_fullyFaithful
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizationFunctor P S).FullyFaithful := by
  classical
  let W := fullSubcategoryLocalizationSystem P S
  let G := fullSubcategoryLocalizationFunctor P S
  have hFF : Nonempty G.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    let X' : P.FullSubcategory := W.Q.objPreimage X
    let Y' : P.FullSubcategory := W.Q.objPreimage Y
    let eX : W.Q.obj X' ≅ X := W.Q.objObjPreimageIso X
    let eY : W.Q.obj Y' ≅ Y := W.Q.objObjPreimageIso Y
    let eGX : G.obj (W.Q.obj X') ≅ G.obj X := G.mapIso eX
    let eGY : G.obj (W.Q.obj Y') ≅ G.obj Y := G.mapIso eY
    have hSource :
        Function.Bijective
          (fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) :=
      hom_transport_bijective eX eY
    have hTarget :
        Function.Bijective
          (fun f : G.obj X ⟶ G.obj Y ↦ eGX.hom ≫ f ≫ eGY.inv) :=
      hom_transport_bijective eGX eGY
    have hQobj :
        Function.Bijective
          (G.map :
            (W.Q.obj X' ⟶ W.Q.obj Y') →
              (G.obj (W.Q.obj X') ⟶ G.obj (W.Q.obj Y'))) :=
      fullSubcategoryLocalizationFunctor_map_bijective_on_Q_obj
        (P := P) (S := S) hP X' Y'
    have hTransportedModel :
        Function.Bijective
          (((G.map) :
              (W.Q.obj X' ⟶ W.Q.obj Y') →
                (G.obj (W.Q.obj X') ⟶ G.obj (W.Q.obj Y'))) ∘
            fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) :=
      Function.Bijective.comp hQobj hSource
    have hcomp :
        ((G.map) ∘ fun f : X ⟶ Y ↦ eX.hom ≫ f ≫ eY.inv) =
          (fun f : X ⟶ Y ↦ eGX.hom ≫ G.map f ≫ eGY.inv) := by
      -- Proof comment: functoriality matches the source and target transports through `G`.
      funext f
      simp [Function.comp, eGX, eGY, Functor.map_comp]
    have hTransported :
        Function.Bijective
          (fun f : X ⟶ Y ↦ eGX.hom ≫ G.map f ≫ eGY.inv) := by
      simpa [hcomp] using hTransportedModel
    exact (Function.Bijective.of_comp_iff' hTarget _).mp hTransported
  exact Classical.choice hFF

-- Proof sketch: the composite `P.ι ⋙ S.Q` inverts exactly the restricted system
-- `S.inverseImage P.ι`, so the induced functor on localizations is the canonical comparison
-- functor. The hypothesis gives essential surjectivity after localization because every object of
-- `D` is reached from an object of `P.FullSubcategory` by a morphism of `S`. For full faithfulness,
-- use the colimit description of morphisms in a right-fraction localization and refine every
-- denominator in `S` to one whose source lies in `P.FullSubcategory`.
/-- The owner-level localizer-morphism formulation of Lemma 13.5.8. -/
theorem fullSubcategoryLocalizerMorphism_isLocalizedEquivalence
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizerMorphism P S).IsLocalizedEquivalence := by
  -- Route correction: finish on the source proof’s denominator-colimit route, using the
  -- structural full-faithfulness helper rather than the discarded unrestricted saturation route.
  letI : (fullSubcategoryLocalizationFunctor P S).Full :=
    (fullSubcategoryLocalizationFunctor_fullyFaithful (P := P) (S := S) hP).full
  letI : (fullSubcategoryLocalizationFunctor P S).Faithful :=
    (fullSubcategoryLocalizationFunctor_fullyFaithful (P := P) (S := S) hP).faithful
  letI : (fullSubcategoryLocalizationFunctor P S).EssSurj :=
    fullSubcategoryLocalizationFunctor_essSurj P S hP
  letI : (fullSubcategoryLocalizationFunctor P S).IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk'
    (fullSubcategoryLocalizerMorphism P S)
    (fullSubcategoryLocalizationSystem P S).Q S.Q
    (fullSubcategoryLocalizationFunctor P S)

/-- Lemma 13.5.8: let `D` be a category, let `P.FullSubcategory ⊆ D` be a full subcategory, and
let `S` be a saturated multiplicative system. If every object of `D` receives a morphism in `S`
from an object of `P.FullSubcategory`, then the induced functor
`(S.inverseImage P.ι)⁻¹(P.FullSubcategory) ⥤ S⁻¹D` is an equivalence. -/
@[stacks 0GSL]
theorem fullSubcategoryLocalization_inclusion_isEquivalence
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    Functor.IsEquivalence (fullSubcategoryLocalizationFunctor P S) := by
  letI := fullSubcategoryLocalizerMorphism_isLocalizedEquivalence P S hP
  change
    ((fullSubcategoryLocalizerMorphism P S).localizedFunctor
      (fullSubcategoryLocalizationSystem P S).Q S.Q).IsEquivalence
  infer_instance

end Localizer

section Triangulated

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]
variable (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation]

/-- Helper for Lemma 13.5.8: inside the triangulated setting, the restricted multiplicative
system is the canonical cone-defined system attached to the kernel of the exact functor
`P.ι ⋙ S.Q`. -/
theorem fullSubcategoryLocalizationSystem_eq_kernel_trW_of_localized_inclusion :
    fullSubcategoryLocalizationSystem P S =
      (Functor.kernel (P.ι ⋙ S.Q)).trW := by
  -- Both sides identify with the arrows whose image under `P.ι ⋙ S.Q` is an isomorphism.
  calc
    fullSubcategoryLocalizationSystem P S =
        (isomorphisms S.Localization).inverseImage (P.ι ⋙ S.Q) :=
      fullSubcategoryLocalizationSystem_eq_inverseImage_isomorphisms_of_localized_inclusion P S
    _ = (Functor.kernel (P.ι ⋙ S.Q)).trW := by
      symm
      exact kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor (P.ι ⋙ S.Q)

/-
The restriction of a triangulation-compatible multiplicative system to a full pretriangulated
subcategory remains compatible with the triangulated structure.
-/
omit [IsSaturatedMultiplicativeSystem S] in
/-- Helper for Lemma 13.5.8: the triangle-completion axiom `MS6` for `S` transports along the
full-subcategory inclusion `P.ι`. -/
lemma fullSubcategoryLocalizationSystem_triangle_completion
    (T₁ T₂ : Triangle P.FullSubcategory)
    (hT₁ : T₁ ∈ distTriang P.FullSubcategory)
    (hT₂ : T₂ ∈ distTriang P.FullSubcategory)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (ha : fullSubcategoryLocalizationSystem P S a)
    (hb : fullSubcategoryLocalizationSystem P S b)
    (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), fullSubcategoryLocalizationSystem P S c ∧
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  -- Proof comment: map the distinguished triangles and the commutative square into `D`,
  -- complete it there by ambient `MS6`, and then package the third map back in the full
  -- subcategory.
  obtain ⟨c, hc, hc₂, hc₃⟩ := S.compatible_with_triangulation
    (P.ι.mapTriangle.obj T₁) (P.ι.mapTriangle.obj T₂)
    (P.ι.map_distinguished T₁ hT₁) (P.ι.map_distinguished T₂ hT₂)
    a.hom b.hom
    (by simpa [fullSubcategoryLocalizationSystem] using ha)
    (by simpa [fullSubcategoryLocalizationSystem] using hb)
    (by simpa using congrArg (fun k ↦ k.hom) hab)
  refine ⟨ObjectProperty.homMk c, ?_, ?_, ?_⟩
  · simpa [fullSubcategoryLocalizationSystem] using hc
  · -- Proof comment: the ambient `mor₂`-compatibility is already an equality in the full
    -- subcategory once we forget with the faithful inclusion.
    apply P.ι.map_injective
    simpa using hc₂
  · -- Proof comment: the shifted comparison also descends because the induced shift on the full
    -- subcategory is defined by preimage along `P.ι`.
    apply P.ι.map_injective
    apply (cancel_mono ((P.ι.commShiftIso (1 : ℤ)).hom.app T₂.obj₁)).1
    have hnat :
        P.ι.map T₁.mor₃ ≫
            (P.ι.map ((shiftFunctor P.FullSubcategory (1 : ℤ)).map a) ≫
              (P.ι.commShiftIso (1 : ℤ)).hom.app T₂.obj₁) =
          P.ι.map T₁.mor₃ ≫
            ((P.ι.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫
              (shiftFunctor D (1 : ℤ)).map a.hom) := by
      -- Proof comment: whisker the `CommShift` naturality square by `T₁.mor₃` before rewriting
      -- the full-subcategory maps.
      have hshift := congrArg
        (fun k ↦ P.ι.map T₁.mor₃ ≫ k)
        (P.ι.commShiftIso_hom_naturality a (1 : ℤ))
      simpa [Functor.map_preimage, Category.assoc] using hshift
    have hc₃' :
        P.ι.map T₁.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫
            (shiftFunctor D (1 : ℤ)).map a.hom =
          P.ι.map (ObjectProperty.homMk c) ≫ P.ι.map T₂.mor₃ ≫
            (P.ι.commShiftIso (1 : ℤ)).hom.app T₂.obj₁ := by
      simpa [Functor.map_preimage, Category.assoc] using hc₃
    simpa [Category.assoc] using hnat.trans hc₃'

instance fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation :
    (fullSubcategoryLocalizationSystem P S).IsCompatibleWithTriangulation := by
  -- Route correction: the ambient `kernel.trW` compatibility shortcut needs `[IsTriangulated D]`,
  -- so we instead apply Remark 13.5.3 directly to the restricted system.
  let hMS6 := fullSubcategoryLocalizationSystem_triangle_completion (P := P) (S := S)
  have hMS5 :
      ∀ ⦃X Y : P.FullSubcategory⦄ (s : X ⟶ Y),
        fullSubcategoryLocalizationSystem P S (s⟦(1 : ℤ)⟧') ↔
          fullSubcategoryLocalizationSystem P S s := by
    intro X Y s
    -- Proof comment: after forgetting to `D`, the shifted morphism in the full subcategory is
    -- is canonically isomorphic to the ambient shifted morphism; transport across the
    -- `CommShift` isomorphism and then use the ambient shift-compatibility of `S`.
    change S ((s⟦(1 : ℤ)⟧').hom) ↔ S s.hom
    let eX := (P.ι.commShiftIso (1 : ℤ)).app X
    let eY := (P.ι.commShiftIso (1 : ℤ)).app Y
    have hrewrite :
        (s⟦(1 : ℤ)⟧').hom ≫ eY.hom = eX.hom ≫ (s.hom)⟦(1 : ℤ)⟧' := by
      simpa [Functor.map_preimage, eX, eY] using P.ι.commShiftIso_hom_naturality s (1 : ℤ)
    calc
      S ((s⟦(1 : ℤ)⟧').hom) ↔
          S ((s⟦(1 : ℤ)⟧').hom ≫ eY.hom) := by
            exact (S.cancel_right_of_respectsIso ((s⟦(1 : ℤ)⟧').hom) eY.hom).symm
      _ ↔ S (eX.hom ≫ (s.hom)⟦(1 : ℤ)⟧') := by
            rw [hrewrite]
            rfl
      _ ↔ S ((s.hom)⟦(1 : ℤ)⟧') := by
            exact S.cancel_left_of_respectsIso eX.hom ((s.hom)⟦(1 : ℤ)⟧')
      _ ↔ S s.hom := IsCompatibleWithShift.iff S s.hom (1 : ℤ)
  exact isCompatibleWithTriangulation_of_mem_shift_one_iff_of_triangleCompletion
    (fullSubcategoryLocalizationSystem P S) hMS6 hMS5

local instance fullSubcategoryLocalizerMorphism_commShift :
    (fullSubcategoryLocalizerMorphism P S).functor.CommShift ℤ := by
  change P.ι.CommShift ℤ
  infer_instance

local instance fullSubcategoryLocalizationFunctor_commShift :
    (fullSubcategoryLocalizationFunctor P S).CommShift ℤ :=
  (fullSubcategoryLocalizerMorphism P S).commShift ℤ
    (fullSubcategoryLocalizationSystem P S).Q S.Q
    (fullSubcategoryLocalizationFunctor P S)
    (Localization.fac
      (P.ι ⋙ S.Q)
      ((fullSubcategoryLocalizerMorphism P S).inverts S.Q)
      (fullSubcategoryLocalizationSystem P S).Q).symm

/-- The localized inclusion functor is exact for the canonical pretriangulated structures on the
source and target localizations; its `CommShift ℤ` structure is inherited from the generic
`LocalizerMorphism.localizedFunctor` instance. -/
noncomputable instance [HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S)] :
    (fullSubcategoryLocalizationFunctor P S).IsTriangulated := by
  -- Route correction: exactness of the localized inclusion only needs the restricted system
  -- to admit left fractions, not the stronger unrestricted saturation helper above.
  let F : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  -- Apply the generic exact-factorization theorem to the composite `P.ι ⋙ S.Q`.
  simpa [F, fullSubcategoryLocalizationFunctor] using
    (exact_factorization_isTriangulated
      (S := fullSubcategoryLocalizationSystem P S) (F := F) hF)

end Triangulated

end

end CategoryTheory
