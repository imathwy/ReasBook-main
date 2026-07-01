import Mathlib
import stacks_project.Chap04.Definition_4_34_2
import stacks_project.Chap04.«4_34_2_4»
import stacks_project.Chap04.Definition_4_35_1
import stacks_project.Chap04.Lemma_4_35_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ u₁

namespace CategoryTheory

open CategoryOver Functor Functor.Fiber IsHomLift

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 4.35.12:
- primary domain: relative/absolute inertia projections over a fixed base and the owner predicate
  `IsFibredInGroupoids`;
- inspected owner-level declarations:
  `relativeInertiaProjection`,
  `CategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaProjection_isFibered`,
  `IsFibredInGroupoids`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `RelativeInertiaHom.isIso_of_isIso`;
- best owner abstraction: the core theorem should live on the raw projection
  `relativeInertiaProjection p p`; the `Cat/C` theorem for `absoluteInertiaOver 𝒮` is only the
  source-facing bridge obtained by packaging the same owner;
- primitive data: only a functor `p : S ⥤ C` together with the existing
  `IsFibredInGroupoids p` structure;
- derived API: the bridge theorem and bundled instance for `absoluteInertiaOver`, obtained by
  reusing the existing fibredness owner theorem and checking that each inertia fiber is again a
  groupoid.

Source/core/bridge triage:
- `source-facing`: `absoluteInertiaProjection_isFibredInGroupoids`;
- `core/canonical`: `relativeInertiaProjection`, `Functor.Fiber`, and
  `IsFibredInGroupoids`;
- `bridge/view`: the definitional identification
  `(absoluteInertiaOver (BasedCategory.ofFunctor p)).p = relativeInertiaProjection p p`. -/

variable {S : Type u₁} [Category.{v₁} S]

section

variable (p : S ⥤ C) [IsFibredInGroupoids p]

private theorem relativeInertiaProjection_fiber_hom_isIso
    (U : C) {X Y : (relativeInertiaProjection p p).Fiber U} (φ : X ⟶ Y) :
    IsIso φ := by
  let q := relativeInertiaProjection p p
  letI : q.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift (𝟙 U) φ.1.φ := by
    refine of_fac' p (𝟙 U) φ.1.φ ?_ ?_ ?_
    · simpa [q, relativeInertiaProjection] using domain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using codomain_eq q (𝟙 U) φ.1
    · simpa [q, relativeInertiaProjection] using fac' q (𝟙 U) φ.1
  letI : IsIso (homMk p U φ.1.φ) :=
    IsFibredInGroupoids.hom_isIso U (homMk p U φ.1.φ)
  letI : IsIso φ.1.φ := by
    simpa using
      (inferInstance : IsIso ((fiberInclusion : p.Fiber U ⥤ _).map (homMk p U φ.1.φ)))
  letI : IsIso φ.1 := RelativeInertiaHom.isIso_of_isIso φ.1
  letI : q.IsHomLift (𝟙 U) (inv φ.1) := by
    simpa [q] using lift_id_inv_isIso q U φ.1
  refine ⟨?_⟩
  use ⟨inv φ.1, inferInstance⟩
  constructor
  · apply Fiber.hom_ext
    change φ.1 ≫ inv φ.1 = 𝟙 X.1
    simp
  · apply Fiber.hom_ext
    change inv φ.1 ≫ φ.1 = 𝟙 Y.1
    simp

private instance relativeInertiaProjection_fiber_isGroupoid
    (U : C) :
    IsGroupoid ((relativeInertiaProjection p p).Fiber U) where
  all_isIso := relativeInertiaProjection_fiber_hom_isIso p U

-- Proof sketch: reuse the canonical owner theorem
-- `CategoryOver.absoluteInertiaProjection_isFibered` for the projection part, then apply
-- Lemma `4.35.2` and check directly that each inertia fiber is a groupoid because a morphism in
-- the inertia fiber is a vertical morphism in `S`, hence an isomorphism.
/-- Owner-level form of Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then its absolute
inertia projection `relativeInertiaProjection p p : I_S ⥤ C` is again fibred in groupoids. The
source-facing `Cat/C` packaging is the companion theorem
`CategoryOver.absoluteInertiaProjection_isFibredInGroupoids`. -/
theorem relativeInertiaProjection_isFibredInGroupoids :
    IsFibredInGroupoids (relativeInertiaProjection p p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (relativeInertiaProjection p p)
      ?_
      ?_
  · simpa using
      absoluteInertiaProjection_isFibered
        (FibredCategoryOver.ofFunctor p)
  · intro U
    infer_instance

end

-- Proof sketch: this is only the `Cat/C` bridge form of
-- `relativeInertiaProjection_isFibredInGroupoids`, since `(absoluteInertiaOver 𝒮).p` is
-- definitionally `relativeInertiaProjection 𝒮.p 𝒮.p`.
namespace CategoryOver

/-- Lemma 4.35.12: if `p : S ⥤ C` is fibred in groupoids, then the inertia fibred category
`I_S → C` is again fibred in groupoids over `C`. -/
theorem absoluteInertiaProjection_isFibredInGroupoids
    (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p := by
  simpa [absoluteInertiaOver] using relativeInertiaProjection_isFibredInGroupoids 𝒮.p

instance (𝒮 : BasedCategory.{v₁, u₁} C) [IsFibredInGroupoids 𝒮.p] :
    IsFibredInGroupoids (absoluteInertiaOver 𝒮).p :=
  absoluteInertiaProjection_isFibredInGroupoids 𝒮

end CategoryOver

end CategoryTheory
