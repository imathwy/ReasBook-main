import Mathlib
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.UnivLE
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_42_4 (from Chap07) -/
open CategoryTheory Opposite CategoryTheory.GrothendieckTopology.Plus

universe u₁ u₂ u₃ v₁ v₂ v₃ w r

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Domain-style sampling for Lemma 7.42.4:
- primary domain: sheafification comparison for inverse image along continuous, almost
  cocontinuous functors of sites;
- sampled owner declarations:
  `Functor.IsAlmostCocontinuous`,
  `GrothendieckTopology.IsSheafTheoreticallyEmpty`,
  `GrothendieckTopology.sheafTheoreticallyEmpty_iff_forall_unique_sections`,
  `Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom`;
- best owner abstraction: the canonical comparison morphism
  `sheafifyLift J (whiskerLeft u.op <| toSheafify K G) ...`, determined directly by the weak
  sheafification universal property;
- primitive data: the site functor `u`, the topologies `J` and `K`, weak sheafification on both
  sites, the continuity and almost-cocontinuity hypotheses, the presheaf `G`, and the
  singleton-over-sheaf-theoretically-empty hypothesis on `G`;
- derived API: under the stronger cocontinuity hypothesis, the identification of the source
  comparison morphism with the `hom` of the `G`-component of the canonical mathlib
  compatibility isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks Project theorem that the comparison morphism
  `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism under continuity, almost cocontinuity, and the
  singleton condition on sheaf-theoretically empty objects;
- `core/canonical`: the canonical comparison morphism produced by `sheafifyLift`;
- `bridge/view`: when `u` is cocontinuous, the theorem
  `pushforwardContinuousSheafificationCompatibility_hom_app_hom` identifies that source-facing
  comparison morphism with the component of the canonical mathlib compatibility isomorphism.

The previous refinement failed by rebuilding the proof through custom local bijectivity helpers.
The stronger cocontinuous compatibility bridge from mathlib is still useful as a recall below, but
it does not close the almost-cocontinuous theorem directly. The remaining source-faithful route is
to construct local injectivity and surjectivity for the whiskered sheafification unit, using cover
lifting together with the empty-image uniqueness hypothesis. -/

/-- Helper for Lemma 7.42.4: composing a sheaf of `Type w`-valued presheaves with the relevant
`ULift` functor preserves the sheaf condition. -/
private instance uliftFunctor_hasSheafCompose_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) where
  isSheaf P hP := by
    -- Rewrite the sheaf condition into the concrete type-valued form where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.42.4: the identity functor on `Type w` preserves sheafification
tautologically. -/
private instance preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (𝟭 (Type w)) where
  le P Q f hf := by
    -- Whiskering by the identity functor leaves the `W`-morphism unchanged.
    simpa using hf

/-- Helper for Lemma 7.42.4: the concrete `Plus` map is locally injective in any universe of
types. -/
private theorem toPlus_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toPlus P) := by
  -- Compare representatives of equal `Plus` sections on a covering sieve.
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact L.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `Plus` map is locally surjective in any universe of
types. -/
private theorem toPlus_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toPlus P) := by
  -- Every `Plus` section is locally represented by an actual presheaf section.
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine L.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. } }
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `plus-plus` model of sheafification is locally
injective in any universe of types. -/
private theorem concrete_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    toPlus_isLocallyInjective_type (L := L) P
  letI : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallyInjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as the composite of the two `Plus` maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.42.4: the concrete `plus-plus` model of sheafification is locally
surjective in any universe of types. -/
private theorem concrete_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    toPlus_isLocallySurjective_type (L := L) P
  letI : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    toPlus_isLocallySurjective_type (L := L) (L.plusObj P)
  -- Rewrite the concrete sheafification unit as the composite of the two `Plus` maps.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.42.4: local injectivity reflects across whiskering by the relevant
`ULift` functor. -/
private theorem locallyInjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃))))] :
    Presheaf.IsLocallyInjective L η where
  equalizerSieve_mem {X} x y h := by
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).obj X := ULift.up y
    -- Lift the equal pair, use local injectivity upstairs, then descend with `ULift.down`.
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃)))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))
        x' y'
    have hS : S ∈ L X.unop := by
      exact
        Presheaf.equalizerSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃))))
          x' y' hUp
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.42.4: local injectivity of type-valued presheaf maps is preserved by
whiskering with the ambient `ULift` functor. -/
private theorem isLocallyInjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective L η] :
    Presheaf.IsLocallyInjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))) where
  equalizerSieve_mem {X} x y h := by
    -- The `ULift` whiskering only repackages sections, so the equalizer sieve is unchanged.
    have hDown : η.app X x.down = η.app X y.down := by
      change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
      exact ULift.up.inj h
    have hSieve :
        Presheaf.equalizerSieve
            (F := P ⋙
              (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
                Type w ⥤ Type (max w (max u₃ v₃))))
            x y =
          Presheaf.equalizerSieve (F := P) x.down y.down := by
      ext Y f
      constructor
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down) at hEq
        exact ULift.up.inj hEq
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down)
        exact congrArg ULift.up hEq
    rw [hSieve]
    exact Presheaf.equalizerSieve_mem L η x.down y.down hDown

/-- Helper for Lemma 7.42.4: whiskering a type-valued presheaf morphism by `ULift` does not
change its image sieve. -/
private theorem imageSieve_whisker_ulift
    {E : Type u₃} [Category.{v₃} E]
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q) {X : E}
    (x :
      (Q ⋙
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))).obj (op X)) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))) x =
      Presheaf.imageSieve η x.down := by
  ext Y f
  constructor
  · rintro ⟨y, hy⟩
    -- Any lifted local preimage descends by `ULift.down`.
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    -- Conversely, any ordinary local preimage lifts back via `ULift.up`.
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.42.4: local surjectivity of type-valued presheaf maps is preserved by
whiskering with the ambient `ULift` functor. -/
private theorem isLocallySurjective_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L η] :
    Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))) where
  imageSieve_mem {X} x := by
    -- After identifying the image sieve with the unlifted one, reuse local surjectivity of `η`.
    simpa [imageSieve_whisker_ulift (η := η) x] using
      (Presheaf.imageSieve_mem L η x.down)

/-- Helper for Lemma 7.42.4: local surjectivity reflects across whiskering by the relevant
`ULift` functor. -/
private theorem locallySurjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃))))] :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).obj (op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))
        x'
    -- Lift the target section to the ambient universe, then descend a local preimage.
    have hS : S ∈ L X := by
      exact
        Presheaf.imageSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃))))
          x'
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))).obj (op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))).app (op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).map f.op x' at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    change ULift.up (η.app (op Y) y.down) = ULift.up (Q.map f.op x) at hy
    exact ULift.up.inj hy

/-- Helper for Lemma 7.42.4: after enlarging the target universe so that the concrete
`plus-plus` model is available, the abstract sheafification unit is locally injective. -/
private theorem large_toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type (max w (max u₃ v₃))) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  let _ : Presheaf.IsLocallyInjective L
      (L.toSheafify (P ⋙ forget (Type (max w (max u₃ v₃))))) :=
    concrete_toSheafify_isLocallyInjective_type
      (L := L) (P := P ⋙ forget (Type (max w (max u₃ v₃))))
  -- Compare the abstract unit with the concrete `plus-plus` unit and transfer local injectivity.
  rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso
      ((plusPlusIsoSheafify L (Type (max w (max u₃ v₃)))
        (P ⋙ forget (Type (max w (max u₃ v₃))))).hom) := by
    infer_instance
  let _ : IsIso
      ((sheafifyComposeIso L (forget (Type (max w (max u₃ v₃)))) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: after enlarging the target universe so that the concrete
`plus-plus` model is available, the abstract sheafification unit is locally surjective. -/
private theorem large_toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type (max w (max u₃ v₃))) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let _ : Presheaf.IsLocallySurjective L
      (L.toSheafify (P ⋙ forget (Type (max w (max u₃ v₃))))) :=
    concrete_toSheafify_isLocallySurjective_type
      (L := L) (P := P ⋙ forget (Type (max w (max u₃ v₃))))
  -- Compare the abstract unit with the concrete `plus-plus` unit and transfer local surjectivity.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso
      ((plusPlusIsoSheafify L (Type (max w (max u₃ v₃)))
        (P ⋙ forget (Type (max w (max u₃ v₃))))).hom) := by
    infer_instance
  let _ : IsIso
      ((sheafifyComposeIso L (forget (Type (max w (max u₃ v₃)))) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: preserving sheafification for the relevant `ULift` functor is
equivalent to invertibility of the canonical sheaf-composition comparison. -/
private theorem uliftFunctor_preservesSheafification_type_iff
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) ↔
      IsIso (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max w (max u₃ v₃))))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  -- Rewrite preservation into the owner comparison for the chosen adjunctions.
  change L.PreservesSheafification F ↔
    IsIso (sheafComposeNatTrans L F
      (sheafificationAdjunction L (Type w))
      (plusPlusAdjunction L Ts))
  rw [GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
    (J := L) (F := F)
    (adj₁ := sheafificationAdjunction L (Type w))
    (adj₂ := plusPlusAdjunction L Ts)]

/-- Helper for Lemma 7.42.4: the specialized `ULift` sheafification comparison is an isomorphism
exactly when the whiskered small-universe unit is a `W`-morphism upstairs. -/
private theorem uliftFunctor_comparison_app_isIso_iff_whiskered_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P) ↔
      L.W
        (Functor.whiskerRight (toSheafify L P)
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let adj₁ := sheafificationAdjunction L (Type w)
  let adj₂ := sheafificationAdjunction L Ts
  let η := (sheafComposeNatTrans L F adj₁ adj₂).app P
  have hW :
      L.W ((sheafToPresheaf L Ts).map η) ↔ IsIso η := by
    -- Passing to underlying presheaves detects isomorphisms for sheaf morphisms.
    simpa [η] using (L.W_sheafToPresheaf_map_iff_isIso η)
  have hfac :
      toSheafify L (P ⋙ F) ≫ (sheafToPresheaf L Ts).map η =
        Functor.whiskerRight (toSheafify L P) F := by
    -- This is the defining factorization of `sheafComposeNatTrans`.
    simpa [η, adj₁, adj₂, F] using
      (sheafComposeNatTrans_fac L F adj₁ adj₂ P)
  -- Normalize the componentwise isomorphism question to a `W`-statement and peel off the
  -- large-universe sheafification unit.
  change IsIso η ↔ L.W (Functor.whiskerRight (toSheafify L P) F)
  rw [← hW, ← hfac]
  exact
    (((GrothendieckTopology.W (J := L) (A := Ts)).precomp_iff
      (W' := GrothendieckTopology.W (J := L) (A := Ts))
      (toSheafify L (P ⋙ F))
      ((sheafToPresheaf L Ts).map η)
      (L.W_toSheafify (P ⋙ F))).symm)

/-- Helper for Lemma 7.42.4: in the large universe of types used for `ULift`, the class `W`
coincides with local bijectivity because the large-universe sheafification unit is already
locally bijective. -/
private theorem large_type_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))] :
    L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) := by
  let T := Type (max w (max u₃ v₃))
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ forget T)
    -- Rewrite the abstract large-universe unit as the concrete one followed by comparison
    -- isomorphisms that preserve local injectivity.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective L (L.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (L := L) (P := P ⋙ forget T)
    -- The same large-universe comparison transports local surjectivity to the abstract unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := T)

/-- Helper for Lemma 7.42.4: once the small-universe sheafification unit is known to be locally
injective and locally surjective on every `Type w`-valued presheaf, `W` agrees with local
bijectivity on `Type w`. -/
private theorem small_type_WEqualsLocallyBijective_of_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.WEqualsLocallyBijective (Type w) := by
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P) := hInj
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P) := hSurj
  let _ : L.PreservesSheafification (forget (Type w)) := by
    -- The forgetful functor on `Type w` is the identity, so it preserves sheafification
    -- tautologically.
    simpa using
      (preservesSheafification_id_type (L := L) :
        L.PreservesSheafification (𝟭 (Type w)))
  let _ : L.HasSheafCompose (forget (Type w)) := by
    -- Sheaf composition with the identity-on-types forgetful functor is available by instance
    -- search.
    infer_instance
  -- Package the two local-bijectivity hypotheses into the canonical `WEqualsLocallyBijective`
  -- structure.
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := Type w)

/-- Helper for Lemma 7.42.4: once the small-universe sheafification unit is locally bijective,
its `ULift`-whiskering already lies in `W` in the large target universe. -/
private theorem whiskered_toSheafify_W_of_small_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w)
    [Presheaf.IsLocallyInjective L (toSheafify L P)]
    [Presheaf.IsLocallySurjective L (toSheafify L P)] :
    L.W
      (Functor.whiskerRight (toSheafify L P)
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts :=
    CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let _ : L.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (L := L)
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight (toSheafify L P) F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := toSheafify L P)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight (toSheafify L P) F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := toSheafify L P)
  -- Once the whiskered unit is locally bijective in the large universe, `W` follows directly.
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight (toSheafify L P) F))

/-- Helper for Lemma 7.42.4: after enlarging the target universe, the sheafification unit itself
is already a `W`-morphism. -/
private theorem ulifted_toSheafify_W
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    L.W
      (toSheafify L
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let _ : L.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (L := L)
  -- Once `W` is identified with local bijectivity in the large universe, the large sheafification
  -- unit lies in `W` automatically.
  simpa [F] using (L.W_toSheafify (P ⋙ F))

/-- Helper for Lemma 7.42.4: if the small universe `Type w` carried the extra multicospan-limit
and cover-colimit owners used by the concrete sheafification theorem, then the relevant `ULift`
functor would preserve sheafification by the generic concrete-category criterion. -/
private theorem uliftFunctor_preservesSheafification_type_of_small_owners
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') (Type w)]
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  -- Supply the small-owner hypotheses explicitly so the generic concrete-category theorem applies
  -- without the global instance-search timeout seen in the unconditional goal.
  let _ :
      ∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
        Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') Ts := by
    intro J'
    infer_instance
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ Ts := by
    intro X
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ F := by
    intro X
    infer_instance
  let _ :
      ∀ (X : E) (S : L.Cover X) (P : Eᵒᵖ ⥤ Type w),
        Limits.PreservesLimit (S.index P).multicospan F := by
    intro X S P
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget (Type w)) := by
    infer_instance
  let _ : Limits.PreservesLimitsOfSize.{max v₃ u₃, max v₃ u₃} (forget Ts) := by
    infer_instance
  let _ : (forget (Type w)).ReflectsIsomorphisms := by
    infer_instance
  let _ : (forget Ts).ReflectsIsomorphisms := by
    infer_instance
  simpa [F] using
    (CategoryTheory.GrothendieckTopology.instPreservesSheafification
      (J := L) (F := F))

/-- Helper for Lemma 7.42.4: the owner comparison against `plusPlusAdjunction` factors through
the `plusPlusSheafIsoPresheafToSheaf` isomorphism and the large sheafification comparison. -/
private theorem ulift_plus_plus_comparison_component_fac
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).hom ≫
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P) =
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let α :
      (plusPlusSheaf L Ts).obj (P ⋙ F) ⟶
        (sheafCompose L F).obj ((presheafToSheaf L (Type w)).obj P) :=
    ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
      (sheafComposeNatTrans L F
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L Ts)).app P
  apply sheafComposeNatTrans_app_uniq
  -- First rewrite the `plus-plus` unit through the comparison with abstract sheafification.
  change
    (plusPlusAdjunction L Ts).unit.app (P ⋙ F) ≫
        (sheafToPresheaf L Ts).map α =
      Functor.whiskerRight ((sheafificationAdjunction L (Type w)).unit.app P) F
  simp only [α, Functor.map_comp]
  change
    L.toSheafify (P ⋙ F) ≫
        (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
          (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P) =
      Functor.whiskerRight ((sheafificationAdjunction L (Type w)).unit.app P) F
  have hplus :
      L.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom =
        toSheafify L (P ⋙ F) := by
    simpa [plusPlusIsoSheafify] using
      (toSheafify_plusPlusIsoSheafify_hom (J := L) (D := Ts) (P := P ⋙ F))
  have hplus' :
      L.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫
            (sheafToPresheaf L Ts).map
              ((sheafComposeNatTrans L F
                (sheafificationAdjunction L (Type w))
                (sheafificationAdjunction L Ts)).app P) =
        toSheafify L (P ⋙ F) ≫
          (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (sheafToPresheaf L Ts).map
            ((sheafComposeNatTrans L F
              (sheafificationAdjunction L (Type w))
              (sheafificationAdjunction L Ts)).app P))
        hplus
  rw [hplus']
  -- The remaining identity is exactly the defining factorization of `sheafComposeNatTrans`.
  simpa [Ts, F] using
    sheafComposeNatTrans_fac L F
      (sheafificationAdjunction L (Type w))
      (sheafificationAdjunction L Ts) P

/-- Helper for Lemma 7.42.4: after cancelling the `plusPlusSheafIsoPresheafToSheaf`
comparison on the left, the owner comparison against `plusPlusAdjunction` is exactly the large
sheafification comparison. -/
private theorem ulift_plus_plus_comparison_component_cancel_left
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).inv ≫
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P) =
      (sheafComposeNatTrans L
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))
        (sheafificationAdjunction L (Type w))
        (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  let e := (plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)
  have h :=
    ulift_plus_plus_comparison_component_fac (L := L) (P := P)
  have h' := congrArg (fun k ↦ e.inv ≫ k) h
  -- Cancel the left comparison isomorphism to isolate the large sheafification comparison.
  simpa [e, Ts, F, Category.assoc] using h'.symm

/-- Helper for Lemma 7.42.4: re-expanding the cancelled comparison shows that the owner
comparison against `plusPlusAdjunction` is the `plusPlusSheafIsoPresheafToSheaf` isomorphism
followed by the large sheafification comparison. -/
private theorem ulift_plus_plus_comparison_component_eq_large_comparison
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    (sheafComposeNatTrans L
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃)))
      (sheafificationAdjunction L (Type w))
      (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P =
      ((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))).hom ≫
        (sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  have hcancel :=
    ulift_plus_plus_comparison_component_cancel_left (L := L) (P := P)
  have h' := congrArg
    (fun k ↦
      ((plusPlusSheafIsoPresheafToSheaf L Ts).app (P ⋙ F)).hom ≫ k)
    hcancel
  -- Reinsert the cancelled isomorphism to recover the original owner comparison.
  simpa [Ts, F, Category.assoc] using h'

/-- Helper for Lemma 7.42.4: once the large sheafification comparison is invertible at `P`, the
owner comparison against `plusPlusAdjunction` is invertible as well. -/
private theorem ulift_plus_plus_comparison_component_isIso_of_large_comparison
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w)
    [IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P)] :
    IsIso
      ((sheafComposeNatTrans L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))
          (sheafificationAdjunction L (Type w))
          (plusPlusAdjunction L (Type (max w (max u₃ v₃))))).app P) := by
  -- Reduce the `plus-plus` comparison to the large comparison and compose the two isomorphisms.
  rw [ulift_plus_plus_comparison_component_eq_large_comparison (L := L) (P := P)]
  let _ :
      IsIso
        (((plusPlusSheafIsoPresheafToSheaf L (Type (max w (max u₃ v₃)))).app
            (P ⋙
              (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
                Type w ⥤ Type (max w (max u₃ v₃))))).hom) := by
    infer_instance
  let hLarge :
      IsIso
        ((sheafComposeNatTrans L
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃)))
            (sheafificationAdjunction L (Type w))
            (sheafificationAdjunction L (Type (max w (max u₃ v₃))))).app P) :=
    inferInstance
  exact IsIso.comp_isIso' inferInstance hLarge

/-- Helper for Lemma 7.42.4: once `W` is identified with local bijectivity in both the small and
large type universes, the relevant `ULift` functor preserves sheafification. -/
private theorem uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [L.WEqualsLocallyBijective (Type w)]
    [L.WEqualsLocallyBijective (Type (max w (max u₃ v₃)))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  refine ⟨?_⟩
  intro P Q f hf
  let _ : Presheaf.IsLocallyInjective L f := (L.W_iff_isLocallyBijective f).1 hf |>.1
  let _ : Presheaf.IsLocallySurjective L f := (L.W_iff_isLocallyBijective f).1 hf |>.2
  -- `ULift` leaves the local equalizer and image sieves unchanged, so local bijectivity
  -- transports directly across whiskering.
  let _ : Presheaf.IsLocallyInjective L (Functor.whiskerRight f F) :=
    isLocallyInjective_whisker_ulift (L := L) (η := f)
  let _ : Presheaf.IsLocallySurjective L (Functor.whiskerRight f F) :=
    isLocallySurjective_whisker_ulift (L := L) (η := f)
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := L) (f := Functor.whiskerRight f F))

/-- Helper for Lemma 7.42.4: once the small `Type w` sheafification unit is locally bijective on
every presheaf, the relevant `ULift` functor preserves sheafification by comparing `W` with local
bijectivity in both universes. -/
private theorem uliftFunctor_preservesSheafification_type_of_small_unit_local_bijectivity
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    (hInj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective L (toSheafify L P))
    (hSurj :
      ∀ P : Eᵒᵖ ⥤ Type w,
        Presheaf.IsLocallySurjective L (toSheafify L P)) :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) := by
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_unit_local_bijectivity.{u₃, v₃, w}
      E _ L inferInstance hInj hSurj
  let _ : L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) :=
    large_type_WEqualsLocallyBijective (L := L)
  -- Once `W` agrees with local bijectivity in both universes, the abstract `ULift` comparison
  -- theorem supplies sheafification preservation.
  exact
    @uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: if the walking multicospans and cover categories used by the
concrete `plus-plus` model already shrink to `Type w`, then the generic small-owner criterion
proves that the relevant `ULift` functor preserves sheafification. -/
private theorem uliftFunctor_preservesSheafification_type_of_small_shapes
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
      Small.{w} (Limits.WalkingMulticospan J')]
    [∀ X : E, Small.{w} (L.Cover X)ᵒᵖ] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) := by
  let _ :
      ∀ (J' : Limits.MulticospanShape.{max v₃ u₃, max v₃ u₃}),
        Limits.HasLimitsOfShape (Limits.WalkingMulticospan J') (Type w) := by
    intro J'
    infer_instance
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w) := by
    intro X
    infer_instance
  -- Once the indexing shapes are genuinely `w`-small, the concrete small-owner theorem applies.
  exact
    @uliftFunctor_preservesSheafification_type_of_small_owners.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: when the shape universe of the site already embeds into `w`, the
concrete `plus-plus` model gives local injectivity of the small sheafification unit directly. -/
private theorem small_type_toSheafify_isLocallyInjective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w) := by
    intro X
    infer_instance
  let _ : ∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P') := by
    intro P' X S
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w)) := by
    intro X
    infer_instance
  let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget (Type w))) :=
    concrete_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ forget (Type w))
  -- Compare the abstract small-universe unit with the concrete `plus-plus` model in `Type w`.
  rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify L (Type w) (P ⋙ forget (Type w))).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso L (forget (Type w)) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: when the shape universe of the site already embeds into `w`, the
concrete `plus-plus` model gives local surjectivity of the small sheafification unit directly. -/
private theorem small_type_toSheafify_isLocallySurjective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let _ : ∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w) := by
    intro X
    infer_instance
  let _ : ∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P') := by
    intro P' X S
    infer_instance
  let _ : ∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w)) := by
    intro X
    infer_instance
  let _ : Presheaf.IsLocallySurjective L (L.toSheafify (P ⋙ forget (Type w))) :=
    concrete_toSheafify_isLocallySurjective_type (L := L) (P := P ⋙ forget (Type w))
  -- Compare the abstract small-universe unit with the concrete `plus-plus` model in `Type w`.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify L (Type w) (P ⋙ forget (Type w))).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso L (forget (Type w)) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.42.4: in the easy universe branch `UnivLE.{max u₃ v₃, w}`, both local
injectivity and local surjectivity of the small sheafification unit are already available from the
concrete `plus-plus` model. -/
private theorem small_type_toSheafify_isLocallyBijective_of_univLE
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{max u₃ v₃, w}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  constructor
  · -- The concrete `plus-plus` comparison gives the injective half in this branch.
    exact small_type_toSheafify_isLocallyInjective_of_univLE (L := L) P
  · -- The same comparison gives the surjective half in the same branch.
    exact small_type_toSheafify_isLocallySurjective_of_univLE (L := L) P

/-- Helper for Lemma 7.42.4: in the complementary universe branch `UnivLE.{w, max u₃ v₃}`, the
canonical small-model transport theorem would recover `W =` local bijectivity on `Type w` once
the two remaining owner-level instances are available. -/
private theorem small_type_WEqualsLocallyBijective_of_small_model_transport
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [∀ X : Eᵒᵖ,
      Limits.HasLimitsOfShape
        (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op) (Type w)]
    [GrothendieckTopology.WEqualsLocallyBijective
      ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L) (Type w)] :
    L.WEqualsLocallyBijective (Type w) := by
  let _ : CategoryTheory.EssentiallySmall.{max u₃ v₃} E :=
    CategoryTheory.essentiallySmallSelf (C := E)
  -- Transport `W =` local bijectivity back from the canonical `max u₃ v₃`-small model.
  simpa using
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (J := L) (A := Type w) :
        L.WEqualsLocallyBijective (Type w))

/-- Helper for Lemma 7.42.4: if `G.op` is right adjoint, then every structured-arrow category on
`G.op` has an initial object, so `Type w`-valued diagrams on it admit limits. -/
private theorem right_adjoint_op_structuredArrow_hasLimits_type
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : A ⥤ B) [G.op.IsRightAdjoint] (X : Bᵒᵖ) :
    Limits.HasLimitsOfShape (StructuredArrow X G.op) (Type w) := by
  -- A right adjoint gives the source proof's canonical initial object in each structured-arrow
  -- category.
  let _ : Limits.HasInitial (StructuredArrow X G.op) := by
    exact (CategoryTheory.mkInitialOfLeftAdjoint G.op
      (Adjunction.ofIsRightAdjoint G.op) X).hasInitial
  -- Any diagram indexed by a category with an initial object has a limit.
  exact ⟨fun F ↦ by infer_instance⟩

/-- Helper for Lemma 7.42.4: the inverse side of the canonical small-model equivalence satisfies
the structured-arrow limit owner needed by `WEqualsLocallyBijective.ofEssentiallySmall`. -/
private theorem small_model_structuredArrow_hasLimits_type
    {E : Type u₃} [Category.{v₃} E] (X : Eᵒᵖ) :
    Limits.HasLimitsOfShape
      (StructuredArrow X (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.op) (Type w) := by
  -- The inverse of an equivalence remains a right adjoint after taking opposites.
  exact right_adjoint_op_structuredArrow_hasLimits_type
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse) X

/-- Helper for Lemma 7.42.4: weak sheafification on `Type w` transports from the original site to
the induced topology on the canonical small model. -/
private theorem small_model_inducedTopology_hasWeakSheafify_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] :
    HasWeakSheafify
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  let e := CategoryTheory.equivSmallModel.{max u₃ v₃} E
  let _ : ∀ X : (SmallModel.{max u₃ v₃, v₃, u₃} E)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X e.functor.op) (Type w) := by
    intro X
    -- The forward equivalence functor is also right adjoint after taking opposites.
    exact right_adjoint_op_structuredArrow_hasLimits_type e.functor X
  let _ :
      (e.functor.sheafPushforwardContinuous (Type w) L (e.inverse.inducedTopology L)).IsEquivalence := by
    infer_instance
  -- Transport weak sheafification across the dense-subsite equivalence to the induced topology.
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    L (e.inverse.inducedTopology L) e.functor (Type w)

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, composing
`Type w`-valued sheaves with the identity functor still preserves the sheaf condition. -/
private theorem small_model_inducedTopology_hasSheafCompose_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    ((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L).HasSheafCompose
      (𝟭 (Type w)) := by
  -- The identity-on-types functor has the same sheaf-composition owner on every site.
  exact inferInstance

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, the identity
functor on `Type w` preserves sheafification tautologically. -/
private theorem small_model_inducedTopology_preservesSheafification_id_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    GrothendieckTopology.PreservesSheafification
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (𝟭 (Type w)) := by
  -- The source and target weak-sheafification units are unchanged under the identity functor.
  exact preservesSheafification_id_type
    (L := (CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)

/-- Helper for Lemma 7.42.4: under a universe inequality `UnivLE.{w, r}`, a function between
`Type w` objects transports to their `Shrink` models in `Type r`. -/
@[implicit_reducible] private noncomputable def type_shrink_map
    [UnivLE.{w, r}] {X Y : Type w} (f : X ⟶ Y) :
    Shrink.{r} X → Shrink.{r} Y :=
  fun x => equivShrink Y (f ((equivShrink X).symm x))

/-- Helper for Lemma 7.42.4: `type_shrink_map` respects identities. -/
private theorem type_shrink_map_id
    [UnivLE.{w, r}] (X : Type w) :
    type_shrink_map (𝟙 X) = id := by
  -- The shrink/unshrink transport cancels on identity maps.
  funext x
  change equivShrink X ((𝟙 X) ((equivShrink X).symm x)) = x
  simp

/-- Helper for Lemma 7.42.4: `type_shrink_map` respects composition. -/
private theorem type_shrink_map_comp
    [UnivLE.{w, r}] {X Y Z : Type w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    type_shrink_map (f ≫ g) = type_shrink_map g ∘ type_shrink_map f := by
  -- The shrink transport is functorial because `equivShrink` is an equivalence on each object.
  funext x
  change equivShrink Z (g (f ((equivShrink X).symm x))) =
    equivShrink Z (g ((equivShrink Y).symm (equivShrink Y (f ((equivShrink X).symm x)))))
  simp

/-- Helper for Lemma 7.42.4: the ordinary forgetful functor from `Type w` still reflects
isomorphisms on the induced topology site. -/
private theorem small_model_inducedTopology_forget_reflectsIsomorphisms_type
    {E : Type u₃} [Category.{v₃} E] :
    (CategoryTheory.forget (Type w)).ReflectsIsomorphisms := by
  -- This is the standard `Type`-valued reflection of isomorphisms.
  infer_instance

/-- Helper for Lemma 7.42.4: on the induced topology of the canonical small model, the generic
concrete-category criterion upgrades weak sheafification to `W =` local bijectivity as soon as a
resized concrete-category forgetful functor on `Type w` is available and preserves sheafification.
-/
private theorem small_model_inducedTopology_WEqualsLocallyBijective_type_of_resized_forget
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    {FD : Type w → Type w → Type*} {CD : Type w → Type (max u₃ v₃)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{max u₃ v₃} (Type w) FD]
    [HasWeakSheafify (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (Type w)]
    [(((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)).HasSheafCompose
      (forget (Type w))]
    [GrothendieckTopology.PreservesSheafification
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L))
      (forget (Type w))]
    [(CategoryTheory.forget (Type w)).ReflectsIsomorphisms] :
    GrothendieckTopology.WEqualsLocallyBijective
      (((CategoryTheory.equivSmallModel.{max u₃ v₃} E).inverse.inducedTopology L)) (Type w) := by
  -- The induced topology is now in the exact situation of the standard `Type`-valued criterion.
  infer_instance

/-- Helper for Lemma 7.42.4: formal universe bridge for the complementary `UnivLE` branch.

The source statement is the almost-cocontinuous sheafification comparison
`(u^p G)^# = u^p(G^#)` under the sheaf-theoretically-empty hypothesis. The current formal route
reduces one branch to proving that the resized `Type w` sheafification unit is locally bijective;
this helper is that transport bridge, not a change to the mathematical statement. -/
private theorem small_type_WEqualsLocallyBijective_of_univLE_opposite
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{w, max u₃ v₃}] :
    L.WEqualsLocallyBijective (Type w) := by
  -- Source-facing repair target: package `type_shrink_map` as the resized carrier transport
  -- showing that sheafification on `Type w` is preserved after embedding into
  -- `Type (max u₃ v₃)`. Then `Presheaf.isLocallyInjective_toSheafify'` and
  -- `Presheaf.isLocallySurjective_toSheafify'` supply the local-bijectivity owner.
  sorry

/-- Helper for Lemma 7.42.4: in the complementary universe branch `UnivLE.{w, max u₃ v₃}`, the
small-universe `toSheafify` unit is locally injective once `W` has been identified with local
bijectivity on `Type w`. -/
private theorem small_type_toSheafify_isLocallyInjective_of_univLE_opposite_direct
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{w, max u₃ v₃}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_univLE_opposite.{u₃, v₃, w}
      E _ L inferInstance inferInstance
  -- Once `W` agrees with local bijectivity on `Type w`, the small sheafification unit is a
  -- standard instance.
  infer_instance

/-- Helper for Lemma 7.42.4: in the complementary universe branch `UnivLE.{w, max u₃ v₃}`, the
small-universe `toSheafify` unit is locally surjective once the same `W`-transport has been
constructed. -/
private theorem small_type_toSheafify_isLocallySurjective_of_univLE_opposite_direct
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [UnivLE.{w, max u₃ v₃}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_univLE_opposite.{u₃, v₃, w}
      E _ L inferInstance inferInstance
  -- The surjective half is the same standard consequence of the `W`-transport bridge.
  infer_instance

/-- Helper for Lemma 7.42.4: in the complementary universe branch `UnivLE.{w, max u₃ v₃}`, the
relevant `ULift` functor preserves sheafification once the small- and large-universe `W`
descriptions are both available. -/
private theorem uliftFunctor_preservesSheafification_type_of_univLE_opposite
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [UnivLE.{w, max u₃ v₃}] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) := by
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_univLE_opposite.{u₃, v₃, w}
      E _ L inferInstance inferInstance
  let _ : L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) :=
    large_type_WEqualsLocallyBijective (L := L)
  -- Once `W` agrees with local bijectivity in both universes, the abstract `ULift`
  -- preservation theorem closes the branch without re-entering the circular small-unit route.
  exact
    @uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: once the complementary `UnivLE` branch supplies sheafification
preservation for the relevant `ULift` functor, local bijectivity of the small sheafification unit
follows by transporting the large-universe statement back across `ULift`. -/
private theorem small_type_toSheafify_isLocallyBijective_of_preserves_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  have hWhiskerInj :
      Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : Presheaf.IsLocallyInjective L (toSheafify L (P ⋙ F)) :=
      large_toSheafify_isLocallyInjective_type (L := L) (P := P ⋙ F)
    -- Rewrite the whiskered small unit to the large unit before reflecting local injectivity.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  have hWhiskerSurj :
      Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := by
    let _ : Presheaf.IsLocallySurjective L (toSheafify L (P ⋙ F)) :=
      large_toSheafify_isLocallySurjective_type (L := L) (P := P ⋙ F)
    -- The same comparison identifies the whiskered small unit with the large unit upstairs.
    rw [← sheafComposeIso_hom_fac (J := L) (F := F) (P := P)]
    infer_instance
  constructor
  · letI : Presheaf.IsLocallyInjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerInj
    -- Reflect local injectivity back down through `ULift`.
    simpa [F] using
      (locallyInjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallyInjective L (toSheafify L P))
  · letI : Presheaf.IsLocallySurjective L
        (Functor.whiskerRight (toSheafify L P) F) := hWhiskerSurj
    -- Reflect local surjectivity back down through `ULift`.
    simpa [F] using
      (locallySurjective_of_whisker_ulift (L := L) (η := toSheafify L P) :
        Presheaf.IsLocallySurjective L (toSheafify L P))

/-- Helper for Lemma 7.42.4: once the complementary `UnivLE` branch supplies sheafification
preservation for the relevant `ULift` functor, local bijectivity of the small sheafification unit
follows by transporting the large-universe statement back across `ULift`. -/
private theorem small_type_toSheafify_isLocallyBijective_of_univLE_opposite
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [UnivLE.{w, max u₃ v₃}]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) ∧
      Presheaf.IsLocallySurjective L (toSheafify L P) := by
  let Ts := Type (max w (max u₃ v₃))
  let F : Type w ⥤ Ts := CategoryTheory.uliftFunctor.{max u₃ v₃, w}
  -- Route correction: isolate the remaining blocker to the preservation instance, then reuse the
  -- already verified `ULift` transport of the large-unit local bijectivity.
  let _ : L.PreservesSheafification F :=
    @uliftFunctor_preservesSheafification_type_of_univLE_opposite.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance
  simpa [F, Ts] using
    small_type_toSheafify_isLocallyBijective_of_preserves_ulift (L := L) (P := P)

/-- Helper for Lemma 7.42.4: once the relevant `ULift` functor is known to preserve
sheafification, the injective half of the small sheafification unit follows by the already
verified transport of large-universe local bijectivity. -/
private theorem small_type_toSheafify_isLocallyInjective_of_preserves_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  -- Project the injective half from the established local-bijectivity transport theorem.
  exact (small_type_toSheafify_isLocallyBijective_of_preserves_ulift (L := L) (P := P)).1

/-- Helper for Lemma 7.42.4: once the relevant `ULift` functor is known to preserve
sheafification, the surjective half of the small sheafification unit follows by the same
large-universe transport route. -/
private theorem small_type_toSheafify_isLocallySurjective_of_preserves_ulift
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))]
    [L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃)))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  -- Project the surjective half from the same transported local-bijectivity package.
  exact (small_type_toSheafify_isLocallyBijective_of_preserves_ulift (L := L) (P := P)).2

/-- Helper for Lemma 7.42.4: on `Type w`-valued presheaves, the sheafification unit is locally
injective by the generic concrete-category sheafification theorem. -/
private theorem small_type_toSheafify_isLocallyInjective_direct
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  rcases univLE_total.{max u₃ v₃, w} with hSmall | hLarge
  · letI : UnivLE.{max u₃ v₃, w} := hSmall
    -- In the easy branch, the concrete `plus-plus` model already provides local injectivity.
    exact (small_type_toSheafify_isLocallyBijective_of_univLE (L := L) P).1
  · letI : UnivLE.{w, max u₃ v₃} := hLarge
    let _ : HasWeakSheafify L (Type (max w (max u₃ v₃))) := by infer_instance
    let _ :
        L.PreservesSheafification
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))) :=
      @uliftFunctor_preservesSheafification_type_of_univLE_opposite.{u₃, v₃, w}
        E _ L inferInstance inferInstance inferInstance
    -- In the complementary branch, the remaining work is exactly the branch-specific
    -- `ULift`-preservation theorem; local injectivity then follows from the proved transport
    -- helper.
    exact small_type_toSheafify_isLocallyInjective_of_preserves_ulift (L := L) P

/-- Helper for Lemma 7.42.4: on `Type w`-valued presheaves, the sheafification unit is locally
surjective by the generic concrete-category sheafification theorem. -/
private theorem small_type_toSheafify_isLocallySurjective_direct
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  rcases univLE_total.{max u₃ v₃, w} with hSmall | hLarge
  · letI : UnivLE.{max u₃ v₃, w} := hSmall
    -- In the easy branch, the concrete `plus-plus` model already provides local surjectivity.
    exact (small_type_toSheafify_isLocallyBijective_of_univLE (L := L) P).2
  · letI : UnivLE.{w, max u₃ v₃} := hLarge
    let _ : HasWeakSheafify L (Type (max w (max u₃ v₃))) := by infer_instance
    let _ :
        L.PreservesSheafification
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))) :=
      @uliftFunctor_preservesSheafification_type_of_univLE_opposite.{u₃, v₃, w}
        E _ L inferInstance inferInstance inferInstance
    -- The complementary branch uses the same `ULift`-preservation frontier, then projects the
    -- surjective half from the transported local-bijectivity theorem.
    exact small_type_toSheafify_isLocallySurjective_of_preserves_ulift (L := L) P

/-- Helper for Lemma 7.42.4: the relevant `ULift` functor preserves sheafification once the
canonical comparison is known to be invertible. -/
private theorem uliftFunctor_preservesSheafification_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [HasWeakSheafify L (Type (max w (max u₃ v₃)))] :
    L.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} : Type w ⥤ Type (max w (max u₃ v₃))) := by
  -- Route correction: remove the stalled `UnivLE` split and build the small-universe `W`
  -- structure directly from the generic local bijectivity of `toSheafify` on `Type w`.
  let _ : L.WEqualsLocallyBijective (Type (max w (max u₃ v₃))) :=
    large_type_WEqualsLocallyBijective (L := L)
  let _ : L.WEqualsLocallyBijective (Type w) :=
    @small_type_WEqualsLocallyBijective_of_unit_local_bijectivity.{u₃, v₃, w}
      E _ L inferInstance
      (fun P ↦ small_type_toSheafify_isLocallyInjective_direct (L := L) P)
      (fun P ↦ small_type_toSheafify_isLocallySurjective_direct (L := L) P)
  -- With `W` identified with local bijectivity in both universes, the abstract `ULift`
  -- preservation theorem applies without any universe case split.
  exact
    @uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective.{u₃, v₃, w}
      E _ L inferInstance inferInstance inferInstance inferInstance

/-- Helper for Lemma 7.42.4: for `Type w`-valued presheaves, the concrete `plus-plus`
sheafification model already gives local injectivity of the sheafification unit. -/
private lemma toSheafify_isLocallyInjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  -- Reuse the direct small-universe unit property instead of routing through `ULift`.
  exact small_type_toSheafify_isLocallyInjective_direct (L := L) P

/-- Helper for Lemma 7.42.4: for `Type w`-valued presheaves, the concrete `plus-plus`
sheafification model already gives local surjectivity of the sheafification unit. -/
private lemma toSheafify_isLocallySurjective_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)] (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  -- Reuse the direct small-universe unit property instead of routing through `ULift`.
  exact small_type_toSheafify_isLocallySurjective_direct (L := L) P

omit [HasWeakSheafify K (Type w)] in
/-- Helper for Lemma 7.42.4: the singleton-on-empty hypothesis survives one application of
the `plus` construction. -/
private lemma plus_preserves_singleton_on_sheaf_theoretically_empty
    (G : Dᵒᵖ ⥤ Type w)
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Dᵒᵖ ⥤ Type w, ∀ X : D, ∀ S : K.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    ∀ V : D, K.IsSheafTheoreticallyEmpty V →
      Nonempty (Unique ((K.plusObj G).obj (op V))) := by
  intro V hV
  obtain ⟨hUniqueG⟩ := hG V hV
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  refine ⟨{
    default := (K.toPlus G).app (op V) hUniqueG.default
    uniq := ?_
  }⟩
  intro s
  let S : K.Cover V := ⟨⊥, hV⟩
  -- The empty cover gives a vacuous separatedness witness, so every `Plus` section is equal to
  -- the one induced from the unique original section.
  exact
    GrothendieckTopology.Plus.sep (J := K) G S _ _
      (fun I ↦ False.elim (by simpa using I.hf))

/-- Helper for Lemma 7.42.4: on a sheaf-theoretically empty object, every section of the
sheafification of `G` has a preimage in `G`. -/
private lemma empty_branch_has_preimage
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V))))
    (V : D) (hV : K.IsSheafTheoreticallyEmpty V) (s : (sheafify K G).obj (op V)) :
    ∃ t : G.obj (op V), (toSheafify K G).app (op V) t = s := by
  -- Rewrite emptiness as the covering condition for the bottom sieve so the sheaf target applies.
  obtain ⟨hUniqueG⟩ := hG V hV
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  have hUniqueSh : Unique ((sheafify K G).obj (op V)) :=
    CategoryTheory.Limits.Types.isTerminalEquivUnique _
      (((presheafToSheaf K (Type w)).obj G).isTerminalOfBotCover V hV)
  refine ⟨hUniqueG.default, ?_⟩
  -- Compare both sections with the unique section of the sheafification.
  calc
    (toSheafify K G).app (op V) hUniqueG.default = hUniqueSh.default := hUniqueSh.uniq _
    _ = s := (hUniqueSh.uniq s).symm

/-
The next helper only uses the almost-cocontinuity lifting statement on `u`; the weak sheafify
data on `J` and continuity of `u` are not needed in its proof.
-/
omit [HasWeakSheafify J (Type w)] [u.IsContinuous J K] in
/-- Helper for Lemma 7.42.4: the whiskered sheafification unit is locally injective along an
almost cocontinuous functor once the empty-image branch is singleton-valued. -/
private lemma whisker_toSheafify_isLocallyInjective
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    Presheaf.IsLocallyInjective J (Functor.whiskerLeft u.op (toSheafify K G)) where
  equalizerSieve_mem {X} x y h := by
    letI instWhiskerBaseInjective : Presheaf.IsLocallyInjective K (toSheafify K G) :=
      toSheafify_isLocallyInjective_type (L := K) G
    let T : K.Cover (u.obj X.unop) :=
      ⟨Presheaf.equalizerSieve (F := G) x y,
        Presheaf.equalizerSieve_mem K (toSheafify K G) x y h⟩
    obtain ⟨S, hS⟩ := Functor.cover_lift_factors u J K T
    -- Lift the equalizer cover and split into the empty-image branch or the factorization branch.
    refine J.superset_covering ?_ S.condition
    intro Y f hf
    let I : S.Arrow := ⟨Y, f, hf⟩
    rcases hS I with hEmpty | ⟨j, g, hg⟩
    · obtain ⟨hUnique⟩ := hG (u.obj Y) hEmpty
      -- On the empty branch, every section over `u.obj Y` is equal.
      exact
        (hUnique.uniq (G.map (u.map f).op x)).trans
          (hUnique.uniq (G.map (u.map f).op y)).symm
    · -- On the factorization branch, pull the equalizer relation back along the factorization.
      have hj : G.map j.f.op x = G.map j.f.op y := by
        simpa [T] using j.hf
      calc
        G.map (u.map f).op x = G.map g.op (G.map j.f.op x) := by
          rw [← hg]
          simp [op_comp]
        _ = G.map g.op (G.map j.f.op y) := by rw [hj]
        _ = G.map (u.map f).op y := by
          rw [← hg]
          simp [op_comp]

omit [HasWeakSheafify J (Type w)] [u.IsContinuous J K] in
/-- Helper for Lemma 7.42.4: the whiskered sheafification unit is locally surjective along an
almost cocontinuous functor once empty-image branches admit preimages. -/
private lemma whisker_toSheafify_isLocallySurjective
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    Presheaf.IsLocallySurjective J (Functor.whiskerLeft u.op (toSheafify K G)) where
  imageSieve_mem {U} s := by
    letI instWhiskerBaseSurjective : Presheaf.IsLocallySurjective K (toSheafify K G) :=
      toSheafify_isLocallySurjective_type (L := K) G
    let T : K.Cover (u.obj U) :=
      ⟨Presheaf.imageSieve (toSheafify K G) s,
        Presheaf.imageSieve_mem K (toSheafify K G) s⟩
    obtain ⟨S, hS⟩ := Functor.cover_lift_factors u J K T
    -- Lift the image cover and again split into the empty-image branch or a genuine refinement.
    refine J.superset_covering ?_ S.condition
    intro Y f hf
    let I : S.Arrow := ⟨Y, f, hf⟩
    rcases hS I with hEmpty | ⟨j, g, hg⟩
    · -- On the empty branch, the pulled-back target section has a preimage by uniqueness.
      simpa using
        empty_branch_has_preimage (K := K) G hG (u.obj Y) hEmpty
          ((sheafify K G).map (u.map f).op s)
    · rcases (show Presheaf.imageSieve (toSheafify K G) s j.f from by simpa [T] using j.hf) with
        ⟨t, ht⟩
      refine ⟨G.map g.op t, ?_⟩
      -- On the factorization branch, pull back a chosen local preimage along the factorization.
      calc
        (toSheafify K G).app (op (u.obj Y)) (G.map g.op t) =
            (sheafify K G).map g.op ((toSheafify K G).app (op j.Y) t) := by
              exact FunctorToTypes.naturality _ _ (toSheafify K G) g.op t
        _ = (sheafify K G).map g.op ((sheafify K G).map j.f.op s) := by
          simpa using congrArg ((sheafify K G).map g.op) ht
        _ = (sheafify K G).map (u.map f).op s := by
          rw [← hg]
          simp [op_comp]

/-- Helper for Lemma 7.42.4: once `W` agrees with local bijectivity on `Type w`, any locally
bijective map into a sheaf induces an isomorphism after `J`-sheafification. -/
private theorem sheafifyLift_isIso_of_locallyBijective
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type w)]
    [L.WEqualsLocallyBijective (Type w)]
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf L Q)
    [Presheaf.IsLocallyInjective L η] [Presheaf.IsLocallySurjective L η] :
    IsIso (sheafifyLift L η hQ) := by
  have hW : L.W η := L.W_of_isLocallyBijective η
  have hmap : IsIso ((presheafToSheaf L (Type w)).map η) := (L.W_iff η).1 hW
  letI instMapIso : IsIso ((presheafToSheaf L (Type w)).map η) := hmap
  have hmap_hom : IsIso (((presheafToSheaf L (Type w)).map η).hom) := by
    -- Forgetting from sheaves to presheaves does not change the component morphism.
    change IsIso ((sheafToPresheaf L (Type w)).map ((presheafToSheaf L (Type w)).map η))
    infer_instance
  letI instMapHomIso : IsIso (((presheafToSheaf L (Type w)).map η).hom) := hmap_hom
  letI instIsoSheafifyInv : IsIso ((isoSheafify L hQ).inv) := by infer_instance
  have hcomp :
      sheafifyLift L η hQ =
        ((presheafToSheaf L (Type w)).map η).hom ≫ (isoSheafify L hQ).inv := by
    -- Route correction: isolate the universal-property step so the main theorem only needs to
    -- supply local bijectivity for the whiskered unit.
    rw [isoSheafify_inv]
    symm
    exact sheafifyMap_sheafifyLift L η (𝟙 Q) hQ
  -- The comparison is a composition of the sheafified map and the target sheaf's inverse unit.
  rw [hcomp]
  infer_instance

/-- Lemma 7.42.4: if `u : (C, J) ⥤ (D, K)` is continuous and almost cocontinuous, and if the
presheaf `G` is singleton-valued on every sheaf-theoretically empty object of `(D, K)`, then the
canonical comparison morphism `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism. -/
theorem pushforwardContinuousSheafificationComparison_isIso_of_isAlmostCocontinuous
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    IsIso
      (sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
        ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property) := by
  letI instToSheafifyInjective : ∀ P : Cᵒᵖ ⥤ Type w, Presheaf.IsLocallyInjective J (toSheafify J P) :=
    fun P ↦ toSheafify_isLocallyInjective_type (L := J) P
  letI instToSheafifySurjective : ∀ P : Cᵒᵖ ⥤ Type w, Presheaf.IsLocallySurjective J (toSheafify J P) :=
    fun P ↦ toSheafify_isLocallySurjective_type (L := J) P
  letI instWEqualsLocallyBijective : J.WEqualsLocallyBijective (Type w) :=
    -- Package the already-established local bijectivity of `toSheafify J P`.
    @small_type_WEqualsLocallyBijective_of_unit_local_bijectivity.{u₁, v₁, w}
      C _ J inferInstance
      (fun P ↦ toSheafify_isLocallyInjective_type (L := J) P)
      (fun P ↦ toSheafify_isLocallySurjective_type (L := J) P)
  let η : u.op ⋙ G ⟶ u.op ⋙ sheafify K G := Functor.whiskerLeft u.op (toSheafify K G)
  let hQ :
      Presheaf.IsSheaf J (u.op ⋙ sheafify K G) :=
    ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property
  letI instEtaInjective : Presheaf.IsLocallyInjective J η :=
    whisker_toSheafify_isLocallyInjective
      (u := u) (J := J) (K := K) G hG
  letI instEtaSurjective : Presheaf.IsLocallySurjective J η :=
    whisker_toSheafify_isLocallySurjective
      (u := u) (J := J) (K := K) G hG
  -- Route correction: the main theorem now delegates the final sheafification comparison step
  -- to the abstract local-bijectivity criterion, so the remaining blocker is only the source-side
  -- construction of `J.WEqualsLocallyBijective (Type w)`.
  simpa [η, hQ] using
    (sheafifyLift_isIso_of_locallyBijective (L := J) (η := η) hQ :
      IsIso (sheafifyLift J η hQ))

section CocontinuousBridge

variable [u.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]

/- Companion bridge: under the stronger cocontinuity hypothesis, the source comparison morphism is
exactly the `hom` of the `G`-component of the canonical mathlib compatibility isomorphism
`u.pushforwardContinuousSheafificationCompatibility (Type w) J K`. -/
recall pushforwardContinuousSheafificationCompatibility_hom_app_hom

omit [u.IsAlmostCocontinuous J K] in
/-
The cocontinuous bridge does not use the almost-cocontinuity hypothesis from the surrounding
section.
-/
/-- Helper for Lemma 7.42.4: under the stronger cocontinuous and right-Kan-extension hypotheses,
the source comparison map is an isomorphism because it is the underlying morphism of mathlib's
compatibility isomorphism. -/
private theorem pushforwardContinuousSheafificationComparison_isIso_of_isCocontinuous
    (G : Dᵒᵖ ⥤ Type w) :
    IsIso
      (sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
        ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property) := by
  let e :
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op ⋙ presheafToSheaf J (Type w)).obj G ≅
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G :=
    asIso ((u.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app G)
  have hcomp :
      sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
          ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property =
        e.hom.hom := by
    -- Rewrite the source-facing comparison morphism as the underlying morphism of `e.hom`.
    exact (u.pushforwardContinuousSheafificationCompatibility_hom_app_hom (Type w) J K G).symm
  -- Use the inverse of the sheaf-level isomorphism to build an inverse on underlying presheaves.
  refine ⟨⟨e.inv.hom, ?_, ?_⟩⟩
  · rw [hcomp]
    exact ObjectProperty.isoHom_inv_id_hom e
  · rw [hcomp]
    exact ObjectProperty.isoInv_hom_id_hom e
end CocontinuousBridge

end

end CategoryTheory.Functor
