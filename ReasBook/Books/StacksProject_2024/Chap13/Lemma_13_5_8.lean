import Mathlib
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap04.Lemma_4_27_21
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Lemma_13_5_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

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
/-- Helper for Lemma 13.5.8: after comparing the two right-fraction Hom colimits along the
denominator-refinement functor, the localized inclusion is fully faithful. -/
-- TODO: the remaining blocker is to package the diagram-level natural isomorphism between the
-- restricted Hom diagram and the ambient Hom diagram precomposed with the opposite
-- denominator-refinement functor, and then identify the induced map on colimits with
-- `fullSubcategoryLocalizationFunctor P S`. The right-fraction comparison infrastructure is now
-- in place, but the final colimit-level identification still needs a dedicated adapter lemma.
noncomputable def fullSubcategoryLocalizationFunctor_fullyFaithful
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizationFunctor P S).FullyFaithful := sorry

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

/-- The restriction of a triangulation-compatible multiplicative system to a full
pretriangulated subcategory remains compatible with the triangulated structure. -/
-- TODO: the remaining blocker is to transport the ambient triangle-completion axiom along `P.ι`
-- and use `P.ι.commShiftIso_hom_naturality` to rewrite the shifted third-edge equation back in
-- the full subcategory.
instance fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation :
    (fullSubcategoryLocalizationSystem P S).IsCompatibleWithTriangulation := sorry

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
