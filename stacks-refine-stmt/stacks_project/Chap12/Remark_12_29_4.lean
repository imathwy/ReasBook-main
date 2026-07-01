import Mathlib
import stacks_project.Chap12.Lemma_12_10_7
import stacks_project.Chap12.Lemma_12_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Domain-style sampling for Remark 12.29.4:
- primary domain: adjunctions, exact functors, faithfulness, and zero-object detection in abelian
  categories;
- sampled owner declarations:
  * `preservesMonomorphisms_iff_exact_of_leftAdjoint`
  * `Functor.faithful_of_exact_of_kernel_le_isZero`
  * `Functor.Faithful.map_injective`
  * `Functor.isZero`
- best owner abstraction: an adjunction `adj : v ⊣ u` together with the owner predicates
  `v.PreservesMonomorphisms` and `v.Faithful`; the textbook zero-object detection condition is the
  source-facing bridge to the faithful owner.
- primitive data: the adjunction `adj`, additivity of `v`, monomorphism preservation for `v`, and
  for the concrete zero-functor example a single nonzero object of `ModuleCat (ZMod 2)`; the
  adjunction between the two zero functors is a private bridge used only to verify the hypotheses
  of the example.
- derived API: exactness of `v`, preservation of zero morphisms by faithful left adjoints, and the
  concrete zero-functor counterexample on `ModuleCat (ZMod 2)`.

Source/core/bridge triage:
- `source-facing`: the remark's zero-object detection criterion and the counterexample via the zero
  functor;
- `core/canonical`: `exactFunctor`, `Functor.Faithful`, `Functor.isZero`, and the owner theorem
  `preservesMonomorphisms_iff_exact_of_leftAdjoint`;
- `bridge/view`: the iff theorem below, which translates the source wording into the canonical
  faithful-functor owner, plus the private zero-functor adjunction used in the counterexample.
-/

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

section

/-- The zero functors between abelian categories are adjoint. -/
private noncomputable def zeroAdjunction : (0 : B ⥤ A) ⊣ (0 : A ⥤ B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun _ ↦ 0
          invFun := fun _ ↦ 0
          left_inv := fun f ↦ (Functor.zero_obj X).eq_of_src _ _
          right_inv := fun g ↦ (Functor.zero_obj Y).eq_of_tgt _ _ }
      homEquiv_naturality_left_symm := by aesop_cat
      homEquiv_naturality_right := by aesop_cat }

/-- The zero functor between abelian categories preserves monomorphisms because it is exact. -/
private theorem zeroFunctor_preservesMonomorphisms : (0 : B ⥤ A).PreservesMonomorphisms := by
  let hZeroFunctor : IsZero (0 : B ⥤ A) :=
    Functor.isZero _ fun _ ↦ by simp
  letI : PreservesLimitsOfSize.{v₂, u₂} (0 : B ⥤ A) :=
    Functor.preservesLimitsOfSize_of_isZero _ hZeroFunctor
  letI : PreservesColimitsOfSize.{v₂, u₂} (0 : B ⥤ A) :=
    Functor.preservesColimitsOfSize_of_isZero _ hZeroFunctor
  let hExact : exactFunctor B A (0 : B ⥤ A) :=
    (exactFunctor_iff (0 : B ⥤ A)).2
      ⟨PreservesLimitsOfSize.preservesFiniteLimits (0 : B ⥤ A),
        PreservesColimitsOfSize.preservesFiniteColimits (0 : B ⥤ A)⟩
  exact (preservesMonomorphisms_iff_exact_of_leftAdjoint zeroAdjunction).2 hExact

/-- Remark 12.29.4: under the adjunction and monomorphism-preserving hypotheses of Lemma
12.29.3, the first sentence says that the condition that `v.obj X` being zero forces `X` to be
zero is equivalent to `v` being faithful. -/
-- Proof sketch: if `v` is faithful, then additivity gives preservation of zero morphisms, so
-- `v.map (𝟙 X) = 0` implies `𝟙 X = 0`, hence `X` is zero. Conversely, conditions (1) and (2)
-- imply that `v` is exact, and exactness plus the zero-object detection hypothesis force any
-- morphism mapped to zero by `v` to have zero coimage, hence to be the zero morphism.
theorem zeroObjectDetection_iff_faithful_of_rightAdjoint_of_preservesMonomorphisms
    (u : A ⥤ B) (v : B ⥤ A) [v.Additive] (adj : v ⊣ u)
    [v.PreservesMonomorphisms] :
    (∀ X : B, IsZero (v.obj X) → IsZero X) ↔ v.Faithful := by
  constructor
  · intro hzero
    let hExact : exactFunctor B A v :=
      (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
    exact Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  · intro hfaithful
    letI : v.Faithful := hfaithful
    letI : v.IsLeftAdjoint := adj.isLeftAdjoint
    intro X hX
    refine (IsZero.iff_id_eq_zero X).2 <| v.zero_of_map_zero (𝟙 X) <| by
      simpa using (IsZero.iff_id_eq_zero (v.obj X)).1 hX

end

section ConcreteCounterexample

/-- Remark 12.29.4: taking both functors to be zero on `ModuleCat (ZMod 2)` gives a concrete
counterexample. The zero functor is adjoint to itself and preserves monomorphisms, but it neither
detects zero objects nor is faithful. -/
theorem zeroFunctor_counterexample :
    (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).IsLeftAdjoint ∧
      (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).PreservesMonomorphisms ∧
        (¬ ∀ X : ModuleCat.{0} (ZMod 2),
            IsZero (((0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).obj X)) → IsZero X) ∧
        ¬ (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).Faithful := by
  let C := ModuleCat.{0} (ZMod 2)
  let X : C := ModuleCat.of (ZMod 2) (ZMod 2)
  have hX : ¬ IsZero X := by
    letI : Simple X := by infer_instance
    exact Simple.not_isZero X
  refine ⟨zeroAdjunction.isLeftAdjoint, zeroFunctor_preservesMonomorphisms, ?_, ?_⟩
  · intro hzero
    exact hX <| hzero X (Functor.zero_obj X)
  · intro hfaithful
    have hmap : (0 : C ⥤ C).map (𝟙 X) = (0 : C ⥤ C).map (0 : X ⟶ X) := by simp
    exact hX <| (IsZero.iff_id_eq_zero X).2 <| hfaithful.map_injective hmap

end ConcreteCounterexample

end CategoryTheory
