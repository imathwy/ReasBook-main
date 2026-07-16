import Mathlib
import StacksProject_2024.stacks_project.Chap04.«4_34_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS uS'

namespace CategoryTheory

namespace CategoryOver

open BasedCategory
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {S : BasedCategory.{v, uS} C} {S' : BasedCategory.{v, uS'} C}

private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

private theorem idFunctor_isFibered : (𝟭 C).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  exact ⟨R, f, idFunctor_isStronglyCartesian f⟩

/- Domain-style sampling for `4.34.2.4`:
- primary domain: categories over a fixed base `C`, extending the owner objects
  `relativeInertiaOver F` and `absoluteInertiaOver S` introduced in `4.34.2.1`.
- owner abstraction: the chapter owner objects already live upstream; this file adds only the
  further bridge data built from them, namely fibredness of the absolute projection and the
  comparison map to absolute inertia.
- refinement target: reuse the owner declarations from `4.34.2.1` directly and keep this file in
  the `bridge/view` layer. -/

/-- The projection from the absolute inertia of a fibred category over `C` is fibred. -/
theorem absoluteInertiaProjection_isFibered
    (X : FibredCategoryOver.{u, v, u, v} C) :
    (CategoryOver.absoluteInertiaOver X.toCategoryOver).p.IsFibered := by
  let pBased : X.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (𝟭 C) :=
    X.toBasedCategory.toBase
  have hF : pBased.PreservesStronglyCartesian := by
    intro a b φ hφ
    simpa [pBased, BasedCategory.toBase] using idFunctor_isStronglyCartesian (X.p.map φ)
  letI : (𝟭 C).IsFibered := idFunctor_isFibered
  let F : X ⟶ FibredCategoryOver.ofFunctor (𝟭 C) :=
    FibredCategoryMor.ofBasedFunctor pBased hF
  simpa [CategoryOver.absoluteInertiaOver, pBased, F] using relativeInertiaProjection_isFibered F

instance (X : FibredCategoryOver.{u, v, u, v} C) :
    (CategoryOver.absoluteInertiaOver X.toCategoryOver).p.IsFibered :=
  absoluteInertiaProjection_isFibered X

/-- 4.34.2.4: forgetting the condition that the automorphism becomes the identity in `S'` defines
the canonical comparison morphism `\mathcal{I}_{\mathcal{S}/\mathcal{S}'} \to
\mathcal{I}_{\mathcal{S}}`. -/
abbrev relativeInertiaToAbsoluteInertia (F : S ⥤ᵇ S') :
    relativeInertiaOver F ⥤ᵇ CategoryOver.absoluteInertiaOver S :=
  { toFunctor := relativeInertiaMap (𝟭 S.obj) S'.p (eqToIso F.w)
    w := rfl }

-- Proof sketch: unfold the based functor defining the comparison morphism.
/-- The comparison morphism has the expected underlying relative inertia functor. -/
theorem relativeInertiaToAbsoluteInertia_toFunctor (F : S ⥤ᵇ S') :
    (relativeInertiaToAbsoluteInertia F).toFunctor =
      relativeInertiaMap (𝟭 S.obj) S'.p (eqToIso F.w) := sorry

end CategoryOver
end CategoryTheory
