import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small
import StacksProject_2024.stacks_project.Chap08.Lemma_8_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling:
- primary domain: stacks over a site, fiber categories of a projection, and small full
  subcategories cut out by fiberwise representative systems;
- inspected owner-level declarations:
  `ObjectProperty.EssentiallySmall.exists_small`,
  `ObjectProperty.essSurj_ιOfLE_iff`,
  `ObjectProperty.fullyFaithfulι`,
  `fullSubcategory_projection_isStackOnSite`;
- best owner abstraction: an `ObjectProperty S` on the total category, whose fiberwise inverse
  images along `Functor.Fiber.fiberInclusion` recover the chosen representative systems;
- primitive data: fiberwise essential smallness of `(⊤ : ObjectProperty (p.Fiber U))`;
- derived API: the small full subcategory `P.FullSubcategory`, its restricted projection
  `P.ι ⋙ p`, and essential surjectivity of `P.ι`.

Source/core/bridge triage:
- `source-facing`: the explicit representative-set wording for a fiber, and the existence of a
  small full subcategory carrying the same stack;
- `core/canonical`: `ObjectProperty.EssentiallySmall`, `ObjectProperty.ι`, and `IsStackOnSite`;
- `bridge/view`: the comparison between fiberwise representative systems and the total
  `ObjectProperty S`. -/

/-- For a fixed fiber of `p`, the source wording "there is a set of representatives of the
isomorphism classes" is the explicit form of the canonical smallness notion
`ObjectProperty.EssentiallySmall (⊤ : ObjectProperty (p.Fiber U))`. -/
theorem fiber_essentiallySmall_iff_exists_isoClass_representatives
    (p : S ⥤ C) (U : C) :
    ObjectProperty.EssentiallySmall.{max u₁ u₂} (⊤ : ObjectProperty (p.Fiber U)) ↔
      ∃ P : ObjectProperty (p.Fiber U),
        ObjectProperty.Small.{max u₁ u₂} P ∧
          ∀ x : p.Fiber U, ∃ y : p.Fiber U, P y ∧ Nonempty (x ≅ y) := by
  constructor
  · intro _
    obtain ⟨P, _, hP⟩ :=
      ObjectProperty.EssentiallySmall.exists_small.{max u₁ u₂}
        (⊤ : ObjectProperty (p.Fiber U))
    refine ⟨P, inferInstance, fun x ↦ ?_⟩
    have hx : P.isoClosure x := by
      rw [← hP]
      trivial
    simpa [ObjectProperty.prop_isoClosure_iff] using hx
  · rintro ⟨P, _, hP⟩
    refine ⟨⟨P, inferInstance, ?_⟩⟩
    intro x _
    obtain ⟨y, hy, ⟨e⟩⟩ := hP x
    exact ⟨y, hy, ⟨e⟩⟩

/-- A full subcategory of `S` cut out by an object property is a small stack presentation of `p`
when it is small, its restricted projection is a stack over `J`, and its inclusion is essentially
surjective. -/
class IsSmallStackSubcategoryPresentation
    (J : GrothendieckTopology C) (p : S ⥤ C) (P : ObjectProperty S) : Prop where
  small : ObjectProperty.Small.{max u₁ u₂} P
  isStackOnSite : IsStackOnSite J (P.ι ⋙ p)
  essSurj : P.ι.EssSurj

/-- Remark 8.4.9: if each fiber of a category over `C` admits a set of representatives for its
isomorphism classes and the projection is already a stack over `(C, J)`, then one can cut down to
a small full subcategory whose restricted projection is again a stack and whose inclusion into the
ambient category is essentially surjective. Full faithfulness of the inclusion is canonical via
`P.fullyFaithfulι`. -/
theorem exists_small_full_subcategory_of_fiberwise_representatives
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsStackOnSite J p]
    (hrep :
      ∀ U : C, ObjectProperty.EssentiallySmall.{max u₁ u₂} (⊤ : ObjectProperty (p.Fiber U))) :
    ∃ P : ObjectProperty S, IsSmallStackSubcategoryPresentation J p P := by
  letI (U : C) : ObjectProperty.EssentiallySmall.{max u₁ u₂}
      (⊤ : ObjectProperty (p.Fiber U)) := hrep U
  choose Q hQsmall hQeq using fun U : C ↦
    ObjectProperty.EssentiallySmall.exists_small.{max u₁ u₂}
      (⊤ : ObjectProperty (p.Fiber U))
  letI : ∀ U : C, ObjectProperty.Small.{max u₁ u₂} (Q U) := hQsmall
  let P : ObjectProperty S := fun x ↦ Q (p.obj x) (mk rfl)
  let Pfiber (U : C) : ObjectProperty (p.Fiber U) :=
    P.inverseImage (fiberInclusion : p.Fiber U ⥤ S)
  have hPsmall : ObjectProperty.Small.{max u₁ u₂} P := by
    let f : (Σ U : C, Subtype (Q U)) → Subtype P := fun z ↦ by
      rcases z with ⟨U, x⟩
      refine ⟨x.1.1, ?_⟩
      cases x with
      | mk x hx =>
          cases x with
          | mk x hx' =>
              cases hx'
              simpa [P] using hx
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      refine ⟨⟨p.obj x, ⟨Functor.Fiber.mk rfl, hx⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
    exact small_of_surjective hf
  have hPfiber :
      ∀ U : C, Pfiber U = Q U := by
    intro U
    funext x
    cases x with
    | mk x hx =>
        cases hx
        rfl
  have hpullback :
      ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
        (Pfiber V).isoClosure
          (f ^*[canonicalPullbackChoice p] x) := by
    intro U V f x hx
    simp [hPfiber V, ← hQeq V]
  have hlocal :
      ∀ ⦃U : C⦄ (𝒰 : J.Cover U) (x : p.Fiber U)
        (hx : ∀ I : 𝒰.Arrow,
          (Pfiber I.Y).isoClosure
            (I.f ^*[canonicalPullbackChoice p] x)),
        (Pfiber U).isoClosure x := by
    intro U 𝒰 x hx
    simp [hPfiber U, ← hQeq U]
  let hTopIncl : P ≤ (⊤ : ObjectProperty S) := fun _ _ ↦ trivial
  have hTop : (⊤ : ObjectProperty S) ≤ P.isoClosure := by
    intro x _
    have hx : (Q (p.obj x)).isoClosure (mk rfl) := by
      rw [← hQeq (p.obj x)]
      trivial
    rw [ObjectProperty.prop_isoClosure_iff] at hx
    rcases hx with ⟨y, hy, ⟨e⟩⟩
    refine ⟨y.1, ?_, ⟨(fiberInclusion : p.Fiber (p.obj x) ⥤ S).mapIso e⟩⟩
    change Pfiber (p.obj x) y
    rw [hPfiber (p.obj x)]
    exact hy
  have hEssSurjTop : (ObjectProperty.ιOfLE hTopIncl).EssSurj := by
    rw [ObjectProperty.essSurj_ιOfLE_iff hTopIncl]
    exact hTop
  letI : (ObjectProperty.ιOfLE hTopIncl).EssSurj := hEssSurjTop
  letI : ((⊤ : ObjectProperty S).ι).EssSurj := by
    change (ObjectProperty.topEquivalence S).functor.EssSurj
    infer_instance
  refine ⟨P, ?_⟩
  refine ⟨hPsmall, fullSubcategory_projection_isStackOnSite J p P hpullback hlocal, ?_⟩
  simpa using
    (inferInstance :
      (((ObjectProperty.ιOfLE hTopIncl) ⋙ ((⊤ : ObjectProperty S).ι))).EssSurj)

end
