import Mathlib
import stacks_project.Chap12.Definition_12_27_5
import stacks_project.Chap12.Lemma_12_29_3

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Source/core/bridge triage for Lemma 12.29.5:
- source-facing: the final construction of `HasFunctorialInjectiveEmbeddings B`.
- core/canonical: `Adjunction.injectivePresentationOfMap`, the owner
  `HasFunctorialInjectiveEmbeddings A`, and the exactness/faithfulness package from
  `enoughInjectives_of_rightAdjoint_of_preservesMonomorphisms`.
- bridge/view: the transferred arrow functor on `B`, obtained by applying the right adjoint `u` to
  the chosen injective targets of `v.obj X`.

The owner abstraction is `HasFunctorialInjectiveEmbeddings B`. The transferred arrow functor is
real mathematical bridge data here, so this file should construct it directly rather than routing
through the non-canonical intermediate statement `EnoughInjectives B`. -/

noncomputable section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (u : A ⥤ B) (v : B ⥤ A) [v.Additive] (adj : v ⊣ u)
variable [v.PreservesMonomorphisms] [HasFunctorialInjectiveEmbeddings A]

/-- The injective target in `B` obtained by applying the right adjoint to the chosen injective
target of `v.obj X`. -/
private noncomputable abbrev adjointInjectiveUnder (X : B) : B :=
  u.obj (HasFunctorialInjectiveEmbeddings.under (v.obj X))

/-- The transferred injective embedding of `X`. -/
private noncomputable abbrev adjointInjectiveι (X : B) :
    X ⟶ adjointInjectiveUnder u v X :=
  adj.homEquiv X _ (HasFunctorialInjectiveEmbeddings.ι (v.obj X))

/-- The morphism between transferred injective targets induced by `f`. -/
private noncomputable abbrev adjointInjectiveUnderMap {X Y : B} (f : X ⟶ Y) :
    adjointInjectiveUnder u v X ⟶ adjointInjectiveUnder u v Y :=
  u.map (HasFunctorialInjectiveEmbeddings.underMap (v.map f))

omit [Abelian A] [Abelian B] [v.Additive] [v.PreservesMonomorphisms] in
/-- Naturality of the transferred injective embeddings. -/
private lemma adjointInjectiveι_naturality {X Y : B} (f : X ⟶ Y) :
    CommSq
      f
      (adjointInjectiveι u v adj X)
      (adjointInjectiveι u v adj Y)
      (adjointInjectiveUnderMap u v f) := by
  have h :
      (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm
          (f ≫ adjointInjectiveι u v adj Y) =
        (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm
          (adjointInjectiveι u v adj X ≫ adjointInjectiveUnderMap u v f) := by
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
    simpa [adjointInjectiveι, adjointInjectiveUnderMap] using
      (HasFunctorialInjectiveEmbeddings.ι_naturality (v.map f)).w
  exact CommSq.mk <|
    (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm.injective h

/-- The transferred injective-presentation arrow of `X`. -/
private noncomputable abbrev adjointInjectiveArrow (X : B) : Arrow B :=
  Arrow.mk (adjointInjectiveι u v adj X)

/-- The commutative square on transferred injective embeddings induced by `f`. -/
private noncomputable def adjointInjectiveArrowMap {X Y : B} (f : X ⟶ Y) :
    adjointInjectiveArrow u v adj X ⟶ adjointInjectiveArrow u v adj Y :=
  Arrow.homMk f (adjointInjectiveUnderMap u v f) (adjointInjectiveι_naturality u v adj f).w

/-- Lemma 12.29.5: if `u` is right adjoint to `v`, if `v` preserves monomorphisms, if `A`
has functorial injective embeddings, and if `v.obj X` being zero forces `X` to be zero, then `B`
has functorial injective embeddings. The separate enough-injectives hypothesis is absorbed by the
existing instance coming from functorial injective embeddings on `A`. -/
@[reducible]
def hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    (hzero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    HasFunctorialInjectiveEmbeddings B := by
  let hExact : exactFunctor B A v :=
    (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
  letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
  letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
  letI : v.Faithful :=
    Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  refine
    { J :=
        { obj := adjointInjectiveArrow u v adj
          map := adjointInjectiveArrowMap u v adj
          map_id := by
            intro X
            ext
            · rfl
            ·
              simpa [adjointInjectiveArrowMap, adjointInjectiveUnderMap,
                HasFunctorialInjectiveEmbeddings.underMap]
                using congrArg Arrow.Hom.right (HasFunctorialInjectiveEmbeddings.J.map_id (v.obj X))
          map_comp := by
            intro X Y Z f g
            ext
            · rfl
            ·
              simpa [adjointInjectiveArrowMap, adjointInjectiveUnderMap,
                HasFunctorialInjectiveEmbeddings.underMap, Functor.map_comp]
                using congrArg Arrow.Hom.right
                  (HasFunctorialInjectiveEmbeddings.J.map_comp (v.map f) (v.map g)) }
      leftFunc_comp_J := rfl
      mono_obj := ?_
      injective_obj := ?_ }
  · intro X
    simpa [adjointInjectiveι] using
      (adj.injectivePresentationOfMap X
        (HasFunctorialInjectiveEmbeddings.presentation (v.obj X))).mono
  · intro X
    simpa [adjointInjectiveUnder] using
      adj.map_injective (HasFunctorialInjectiveEmbeddings.under (v.obj X))
        (HasFunctorialInjectiveEmbeddings.under_injective (v.obj X))

end

end CategoryTheory
