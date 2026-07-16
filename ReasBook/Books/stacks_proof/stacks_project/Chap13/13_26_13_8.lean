import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Definition_13_14_10
import stacks_proof.stacks_project.Chap13.«13_26_13_1»
import stacks_proof.stacks_project.Chap13.Lemma_13_20_1
import stacks_proof.stacks_project.Chap13.Lemma_13_20_2
import stacks_proof.stacks_project.Chap13.Lemma_13_26_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} {ℬ : Type u}
  [Category.{v} 𝒜] [Category.{v} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat ℬ) (up ℤ))]

/- Domain-style sampling for 13.26.13.8:
- primary domain: bounded-below filtered derived functors and the compatibility of forgetting the
  filtration with the filtered right derived functor;
- sampled owner declarations in this domain:
  `Functor.rightDerivedUnique`,
  `filteredBoundedDerivedForgetFunctor`,
  `Functor.totalRightDerived`;
- best owner abstraction: `Functor.rightDerivedUnique`, specialized all the way to the chapter
  forget-compatibility comparison between `RTFilt T ⋙ filteredBoundedDerivedForgetFunctor` and
  `filteredBoundedDerivedForgetFunctor ⋙
    QMapT.totalRightDerived Qplus (boundedBelowHomotopyQuasiIso 𝒜)`;
- primitive data: the concrete Chapter `13` source functor on `K⁺(Fil^f(𝒜))` obtained by
  applying `T` termwise and then forgetting the target filtration, together with the two canonical
  comparison maps from this source functor to the two chapter composites;
- derived API: the canonical comparison isomorphism and its factorization identity, already owned
  by `Functor.rightDerivedUnique` and `Functor.rightDerived_fac`.

Source/core/bridge triage:
- `source-facing`: the forget-compatibility isomorphism from `(13.26.13.8)`;
- `core/canonical`: `Functor.rightDerivedUnique`;
- `bridge/view`: the two concrete Chapter `13` right derived functor structures on the source
  functor obtained by applying `T` and then forgetting the target filtration.

This item is therefore the Chapter `13` specialization of the canonical uniqueness theorem for
right derived functors, and its main entry should compare the concrete owners already present in
the project rather than a generic pasted equality composite. -/

variable (T : 𝒜 ⥤ₗ ℬ)

local instance : PreservesFiniteLimits T.obj :=
  T.property

local instance : PreservesBinaryBiproducts T.obj :=
  preservesBinaryBiproducts_of_preservesBinaryProducts T.obj

local instance : T.obj.Additive :=
  Functor.additive_of_preservesBinaryBiproducts T.obj

local notation "W" => FQis⁺(𝒜)
local notation "QFiltA" => mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜
local notation "QFiltB" => mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ
local notation "Tplus" =>
  mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)
local notation "QForgetB" => filteredBoundedHomotopyToDerivedByForget ℬ
local notation "ForgetDerivedA" => filteredBoundedDerivedForgetFunctor 𝒜
local notation "ForgetDerivedB" => filteredBoundedDerivedForgetFunctor ℬ
local notation "KForgetA" => mapBoundedBelowHomotopyCategory (finiteFilteredObjectForgetFunctor 𝒜)

variable [Functor.HasRightDerivedFunctor (Tplus ⋙ QFiltB) W]

local instance : Functor.IsLocalization QFiltA W :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

local notation "QplusA" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "QMapT" => mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj
local notation "QisPlusA" => boundedBelowHomotopyQuasiIso 𝒜
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)

variable [Functor.HasRightDerivedFunctor QMapT QisPlusA]

local instance : Functor.IsLocalization QplusA QisPlusA :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local notation "ForgetSource" => Tplus ⋙ QForgetB
local notation "RTFilt" => Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W
local notation "RT" => Functor.totalRightDerived QMapT QplusA QisPlusA
local notation "RTForget" => RTFilt ⋙ ForgetDerivedB
local notation "ForgetRT" => ForgetDerivedA ⋙ RT

/-- Helper for 13.26.13.8: the source functor written as
`(Tplus ⋙ QFiltB) ⋙ ForgetDerivedB`. -/
theorem forget_source_eq_filtered_then_forget :
    ForgetSource = (Tplus ⋙ QFiltB) ⋙ ForgetDerivedB := by
  -- Both sides are the same Chapter 13 composite after unfolding the abbreviations.
  rfl

/-- Helper for 13.26.13.8: the source functor written as
`KForgetA ⋙ QMapT`. -/
theorem forget_source_eq_forget_then_plain :
    ForgetSource = KForgetA ⋙ QMapT := by
  -- The forgetful homotopy functor followed by the ordinary derived lift is definitional here.
  rfl

/-- Helper for 13.26.13.8: the bounded-below forgetful localization bridge. -/
theorem forget_localization_bridge :
    KForgetA ⋙ QplusA = QFiltA ⋙ ForgetDerivedA := by
  -- This is the same bounded-below forget functor viewed through the two localization owners.
  rfl

/-- Helper for 13.26.13.8: the target bounded-below forgetful source functor written as
`QFiltB ⋙ ForgetDerivedB`. -/
theorem forget_target_eq_filtered_then_forget :
    QForgetB = QFiltB ⋙ ForgetDerivedB := by
  -- Both target-side functors are the same bounded-below forgetful composite after unfolding.
  rfl

/-- Helper for 13.26.13.8: the bounded-below forgetful functor on filtered derived categories is
the canonical right derived functor of the bounded-below forgetful source functor. -/
theorem forget_target_is_right_derived :
    Functor.IsRightDerivedFunctor ForgetDerivedB
      (eqToHom (forget_target_eq_filtered_then_forget (ℬ := ℬ)))
      (FQis⁺(ℬ)) := by
  -- Since `QForgetB` already inverts filtered quasi-isomorphisms, the target forgetful functor
  -- is obtained directly from `Functor.isRightDerivedFunctor_of_inverts`.
  simpa [forget_target_eq_filtered_then_forget] using
    (Functor.isRightDerivedFunctor_of_inverts (FQis⁺(ℬ)) ForgetDerivedB
      (eqToIso (forget_target_eq_filtered_then_forget (ℬ := ℬ))).symm)

local notation "IFiltIncl" =>
  mapBoundedBelowHomotopyCategory (filteredInjectiveInclusion 𝒜)
local notation "WIFilt" => W.inverseImage IFiltIncl

/-- Helper for 13.26.13.8: the filtered-injective inclusion as a localizer morphism from the
pulled-back bounded filtered quasi-isomorphisms to the ambient bounded filtered quasi-isomorphisms.
-/
local abbrev ΦIFilt : LocalizerMorphism WIFilt W :=
  LocalizerMorphism.ofEq rfl

/-- Helper for 13.26.13.8: a pulled-back filtered quasi-isomorphism between bounded-below
filtered-injective complexes is already an isomorphism. -/
theorem filtered_injective_quasi_iso_is_iso
    {X Y : K⁺(𝓘^f(𝒜))} (f : X ⟶ Y) (hf : WIFilt f) :
    IsIso f := by
  -- The filtered-injective comparison functor is an equivalence, and the filtered localization
  -- sends the underlying quasi-isomorphism to an isomorphism.
  let F : K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) := filteredInjectiveHomotopyToFilteredDerived 𝒜
  letI : Functor.IsEquivalence F := by
    simpa [F] using filteredInjectiveHomotopyToFilteredDerived_isEquivalence (𝒜 := 𝒜)
  letI : F.Full := (Functor.asEquivalence F).fullyFaithfulFunctor.full
  letI : F.Faithful := (Functor.asEquivalence F).fullyFaithfulFunctor.faithful
  have : IsIso (F.map f) := by
    change IsIso (QFiltA.map (IFiltIncl.map f))
    exact Localization.inverts QFiltA W _ hf
  exact isIso_of_fully_faithful F f

/-- Helper for 13.26.13.8: the filtered-injective inclusion induces an equivalence on localized
categories. -/
theorem filtered_injective_localizer_isLocalizedEquivalence :
    (ΦIFilt (𝒜 := 𝒜)).IsLocalizedEquivalence := by
  let F : K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) := filteredInjectiveHomotopyToFilteredDerived 𝒜
  letI : Functor.IsEquivalence F := by
    simpa [F] using filteredInjectiveHomotopyToFilteredDerived_isEquivalence (𝒜 := 𝒜)
  have hWIFilt :
      WIFilt ≤ MorphismProperty.isomorphisms (K⁺(𝓘^f(𝒜))) := by
    intro X Y f hf
    -- On the filtered-injective source, pulled-back quasi-isomorphisms are already isomorphisms.
    exact filtered_injective_quasi_iso_is_iso (𝒜 := 𝒜) f hf
  letI : Functor.IsLocalization F WIFilt :=
    Functor.IsLocalization.of_isEquivalence F WIFilt hWIFilt
  -- The localized comparison for `ΦIFilt` is therefore represented by the same equivalence `F`.
  simpa [F, ΦIFilt, IFiltIncl] using
    (LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
      (Φ := ΦIFilt (𝒜 := 𝒜))
      (L₂ := QFiltA))

/-- Helper for 13.26.13.8: the filtered-injective localizer bridge carries the right derivability
structure needed to test right-derived comparison maps on filtered-injective models. -/
theorem filtered_injective_localizer_right_derivability :
    (ΦIFilt (𝒜 := 𝒜)).IsRightDerivabilityStructure := by
  letI := filtered_injective_localizer_isLocalizedEquivalence (𝒜 := 𝒜)
  -- A localized equivalence already carries the required right derivability structure.
  simpa using (LocalizerMorphism.IsRightDerivabilityStructure.mk' (ΦIFilt (𝒜 := 𝒜)))

/-- Helper for 13.26.13.8: the ordinary bounded-below derived functor of `T` inverts
quasi-isomorphisms between bounded-below injective complexes. -/
theorem qMapT_inverts_injective_quasi_isos
    {X Y : K⁺ᵢ(𝒜)} (f : X ⟶ Y)
    (hf : QisPlusA ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map f)) :
    IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).map
      ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map f)) := by
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) :=
    (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) :
      K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙ QplusA
  letI : Functor.IsEquivalence F := by
    simpa [F] using boundedBelowInjectiveHomotopyToDerived_isEquivalence (𝒜 := 𝒜)
  letI : F.Full := (Functor.asEquivalence F).fullyFaithfulFunctor.full
  letI : F.Faithful := (Functor.asEquivalence F).fullyFaithfulFunctor.faithful
  have : IsIso (F.map f) := by
    -- The ordinary bounded-below localization inverts the quasi-isomorphism `hf`.
    change IsIso
      ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map
        ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map f))
    exact Localization.inverts QplusA QisPlusA _ hf
  have : IsIso f := isIso_of_fully_faithful F f
  -- Once the map is already an isomorphism in `K^+(\mathcal I)`, every functor sends it to an
  -- isomorphism, in particular `QMapT`.
  infer_instance

/-- Helper for 13.26.13.8: the source functor obtained by applying `T` and then forgetting the
target filtration inverts the pulled-back quasi-isomorphisms on filtered-injective models. -/
theorem filtered_injective_localizer_derives_forget_source :
    (ΦIFilt (𝒜 := 𝒜)).Derives (ForgetSource (T := T)) := by
  intro X Y f hf
  let g : (filteredInjectiveForgetHomotopyFunctor 𝒜).obj X ⟶
      (filteredInjectiveForgetHomotopyFunctor 𝒜).obj Y :=
    (filteredInjectiveForgetHomotopyFunctor 𝒜).map f
  have hforget : IsIso (((QFiltA ⋙ ForgetDerivedA).map (IFiltIncl.map f))) := by
    -- Forgetting the filtration preserves the localized isomorphism coming from `hf`.
    have hQ : IsIso (QFiltA.map (IFiltIncl.map f)) := Localization.inverts QFiltA W _ hf
    change IsIso (ForgetDerivedA.map (QFiltA.map (IFiltIncl.map f)))
    infer_instance
  have hcomparison :
      ((QFiltA ⋙ ForgetDerivedA).map (IFiltIncl.map f)) =
        ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜)).map
          ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map g)) := by
    -- Compare the filtered and ordinary forgetful localization routes on filtered-injective
    -- complexes.
    simpa [filteredInjectiveHomotopyToFilteredDerived, IFiltIncl, KinjIncl, QplusA, g,
      Functor.comp_map] using
      congrArg (fun F => F.map f)
        (filteredInjectiveHomotopyToFilteredDerived_forget_comm (𝒜 := 𝒜))
  rw [hcomparison] at hforget
  have hg_quasi :
      QisPlusA ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map g) := by
    -- Once the forgotten map is an isomorphism in the derived category, it is an ordinary
    -- bounded-below quasi-isomorphism.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
        ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map g))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    simpa [QplusA] using hforget
  have hqMap :
      IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).map
        ((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)).map g)) :=
    qMapT_inverts_injective_quasi_isos (T := T) g hg_quasi
  -- Rewrite the filtered-injective source restriction through the ordinary injective comparison.
  simpa [forget_source_eq_forget_then_plain (T := T), IFiltIncl, KinjIncl, g, Functor.comp_map]
    using hqMap

/-- Helper for 13.26.13.8: the filtered source functor itself is already derived on
filtered-injective models. -/
theorem filtered_injective_localizer_derives_filtered_source :
    (ΦIFilt (𝒜 := 𝒜)).Derives (Tplus ⋙ QFiltB) := by
  intro X Y f hf
  -- On filtered-injective complexes, pulled-back filtered quasi-isomorphisms are already
  -- isomorphisms before applying the filtered source functor.
  haveI : IsIso f := filtered_injective_quasi_iso_is_iso (𝒜 := 𝒜) f hf
  change IsIso ((Tplus ⋙ QFiltB).map (IFiltIncl.map f))
  infer_instance

-- The comparison map toward the composite `RTFilt ⋙ ForgetDerivedB` is assembled from the
-- filtered total right derived unit followed by the target forgetful functor.
local abbrev αforget :
    ForgetSource ⟶ QFiltA ⋙ RTForget :=
  eqToHom (forget_source_eq_filtered_then_forget (T := T)) ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit (Tplus ⋙ QFiltB) QFiltA W)
      ForgetDerivedB ≫
    (Functor.associator QFiltA RTFilt ForgetDerivedB).hom

-- The comparison map toward `ForgetDerivedA ⋙ RT` is obtained by rewriting the source through
-- the ordinary bounded-below derived functor of `T`.
local abbrev βforget :
    ForgetSource ⟶ QFiltA ⋙ ForgetRT :=
  eqToHom (forget_source_eq_forget_then_plain (T := T)) ≫
    Functor.whiskerLeft KForgetA
      (Functor.totalRightDerivedUnit QMapT QplusA QisPlusA) ≫
    (Functor.associator KForgetA QplusA RT).hom ≫
    Functor.whiskerRight (eqToHom (forget_localization_bridge (𝒜 := 𝒜))) RT ≫
    (Functor.associator QFiltA ForgetDerivedA RT).hom

/-- Helper for 13.26.13.8: on filtered-injective models, the `αforget` comparison is an
isomorphism. -/
theorem alphaforget_app_isIso_on_filtered_injective
    (X : K⁺(𝓘^f(𝒜))) :
    IsIso (((αforget (T := T)).app (IFiltIncl.obj X))) := by
  let hΦ := filtered_injective_localizer_derives_filtered_source (𝒜 := 𝒜) (ℬ := ℬ) (T := T)
  have hUnit :
      IsIso ((((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W).app (IFiltIncl.obj X))) := by
    -- The filtered-injective model already computes the filtered right derived functor source.
    exact hΦ.isIso (((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)) X
  have hWhisker :
      IsIso
        (((Functor.whiskerRight
            ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
            ForgetDerivedB).app (IFiltIncl.obj X))) := by
    -- Whiskering by the target forgetful functor preserves the filtered-unit isomorphism.
    change IsIso
      (ForgetDerivedB.map (((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W).app
        (IFiltIncl.obj X)))
    infer_instance
  -- After rewriting the source equality, `αforget` is the whiskered filtered unit followed by
  -- the canonical associator.
  simpa [αforget, forget_source_eq_filtered_then_forget (T := T)] using
    (show IsIso
      ((((Functor.whiskerRight
            ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
            ForgetDerivedB).app (IFiltIncl.obj X)) ≫
          (Functor.associator QFiltA RTFilt ForgetDerivedB).hom.app
            (IFiltIncl.obj X)) from
      inferInstance)

/-- Helper for 13.26.13.8: on filtered-injective models, the `βforget` comparison is an
isomorphism. -/
theorem betaforget_app_isIso_on_filtered_injective
    (X : K⁺(𝓘^f(𝒜))) :
    IsIso (((βforget (T := T)).app (IFiltIncl.obj X))) := by
  let J : K⁺ᵢ(𝒜) := (filteredInjectiveForgetHomotopyFunctor 𝒜).obj X
  have hcomp :
      QMapT.ComputesRightDerivedAt QisPlusA (KinjIncl.obj J) := by
    -- The forgotten filtered-injective model is a bounded-below injective complex, so the
    -- ordinary bounded-below right derived functor is computed there.
    simpa [J, KinjIncl] using
      (boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := QMapT) (I := boundedBelowInjectiveHomotopyCat.toInjectivePlus J))
  have hunit :
      IsIso ((Functor.totalRightDerivedUnit QMapT QplusA QisPlusA).app (KinjIncl.obj J)) := by
    -- Convert the computation statement to the canonical total-right-derived unit criterion.
    exact (Functor.computesRightDerivedAt_iff
      (F := QMapT) (S := QisPlusA) (X := KinjIncl.obj J)).1 hcomp
  -- The `βforget` comparison is the same unit after rewriting the source through the forgetful
  -- localization bridge and evaluating at the filtered-injective model.
  simpa [βforget, forget_source_eq_forget_then_plain (T := T),
    forget_localization_bridge (𝒜 := 𝒜), IFiltIncl, KinjIncl, J, Functor.comp_obj] using hunit

/-- Helper for 13.26.13.8: the composite `RTFilt ⋙ ForgetDerivedB` is a right derived functor of
the concrete source functor obtained by applying `T` and then forgetting the target filtration. -/
theorem rt_forget_is_rightDerived :
    Functor.IsRightDerivedFunctor RTForget αforget W := by
  -- Route correction: the filtered-injective source model is now reduced to the concrete fact
  -- that pulled-back quasi-isomorphisms are already isomorphisms there, so the remaining blocker
  -- is the chapter-level identification of `αforget` on those models with the canonical
  -- comparison supplied by the filtered-injective resolution computation.
  letI := filtered_injective_localizer_right_derivability (𝒜 := 𝒜)
  let hΦ := filtered_injective_localizer_derives_forget_source (T := T)
  -- The derivability-structure criterion reduces the right-derived proof to the filtered-injective
  -- test objects, where `alphaforget_app_isIso_on_filtered_injective` supplies the comparison isos.
  exact hΦ.isRightDerivedFunctor_of_isIso (αforget (T := T))
    (fun X ↦ alphaforget_app_isIso_on_filtered_injective (T := T) X)

/-- Helper for 13.26.13.8: the composite `ForgetDerivedA ⋙ RT` is a right derived functor of the
same source functor after rewriting through the ordinary bounded-below localization bridge. -/
theorem forget_rt_is_rightDerived :
    Functor.IsRightDerivedFunctor ForgetRT βforget W := by
  -- Route correction: the target forgetful right-derived witness is now available, so the
  -- remaining blocker is the filtered-injective normalization of `βforget` against the ordinary
  -- injective resolution comparison after forgetting the filtration.
  letI := filtered_injective_localizer_right_derivability (𝒜 := 𝒜)
  let hΦ := filtered_injective_localizer_derives_forget_source (T := T)
  -- The same filtered-injective criterion applies to the ordinary derived comparison after
  -- transporting it across the forgetful localization bridge.
  exact hΦ.isRightDerivedFunctor_of_isIso (βforget (T := T))
    (fun X ↦ betaforget_app_isIso_on_filtered_injective (T := T) X)

/- Canonical owner recall: the forget-filtration comparison from `13.26.13.8` is the specialized
uniqueness isomorphism for right derived functors. -/
recall Functor.rightDerivedUnique

/- 13.26.13.8: forgetting the filtration commutes with the filtered right derived functor via the
canonical comparison isomorphism between the two Chapter `13` right derived functors of the same
source functor on `K⁺(Fil^f(𝒜))`. -/
/-- 13.26.13.8: forgetting the filtration commutes with the filtered right derived functor via the
canonical uniqueness isomorphism between the two Chapter `13` right derived functors of the same
source functor. -/
@[stacks 015V]
noncomputable def forget_filtered_rightDerived_iso :
    RTForget ≅ ForgetRT := by
  -- Once both right-derived structures are available, the comparison is
  -- exactly `Functor.rightDerivedUnique`.
  letI := rt_forget_is_rightDerived (T := T)
  letI := forget_rt_is_rightDerived (T := T)
  exact (RTForget).rightDerivedUnique ForgetRT αforget βforget W

/- The defining relation for this chapter-level comparison isomorphism is the canonical owner
lemma `Functor.rightDerived_fac`. -/
recall Functor.rightDerived_fac

/-- Helper for 13.26.13.8: the comparison isomorphism satisfies the canonical
`Functor.rightDerived_fac` relation. -/
theorem forget_filtered_rightDerived_iso_fac :
    αforget ≫ Functor.whiskerLeft QFiltA
      ((RTForget).rightDerivedDesc
        αforget
        W
        ForgetRT
        βforget) =
      βforget := by
  -- This is the standard factorization identity for the chosen right-derived comparison.
  letI := rt_forget_is_rightDerived (T := T)
  letI := forget_rt_is_rightDerived (T := T)
  exact (RTForget).rightDerived_fac αforget W ForgetRT βforget

end

end CategoryTheory
