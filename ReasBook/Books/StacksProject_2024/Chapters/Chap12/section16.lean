import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_16_1 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

scoped notation "Gr(" 𝒜 ")" => GradedObject ℤ 𝒜

namespace GradedObject

section Eval

variable {β : Type*} {C : Type u} [Category.{v} C]

noncomputable instance [Preadditive C] : Preadditive (GradedObject β C) := by
  let E := piEquivalenceFunctorDiscrete β C
  exact Preadditive.ofFullyFaithful E.fullyFaithfulFunctor

private noncomputable def evalIsoEvaluation (p : β) :
    (eval p : GradedObject β C ⥤ C) ≅
      (piEquivalenceFunctorDiscrete β C).functor ⋙
        (evaluation (Discrete β) C).obj (Discrete.mk p) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp)

instance [Preadditive C] (p : β) : (eval p : GradedObject β C ⥤ C).Additive := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.Additive := E.fullyFaithfulFunctor.additive_ofFullyFaithful
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : H.Additive := inferInstance
  exact Functor.additive_of_iso (evalIsoEvaluation p).symm

noncomputable instance [HasFiniteLimits C] (p : β) :
    PreservesFiniteLimits (eval p : GradedObject β C ⥤ C) := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : PreservesFiniteLimits E.functor := PreservesLimits.preservesFiniteLimits E.functor
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : PreservesFiniteLimits H := inferInstance
  letI : PreservesFiniteLimits (E.functor ⋙ H) := comp_preservesFiniteLimits E.functor H
  exact preservesFiniteLimits_of_natIso (evalIsoEvaluation p).symm

noncomputable instance [HasFiniteColimits C] (p : β) :
    PreservesFiniteColimits (eval p : GradedObject β C ⥤ C) := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : PreservesFiniteColimits E.functor := PreservesColimits.preservesFiniteColimits E.functor
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : PreservesFiniteColimits H := inferInstance
  letI : PreservesFiniteColimits (E.functor ⋙ H) := comp_preservesFiniteColimits E.functor H
  exact preservesFiniteColimits_of_natIso (evalIsoEvaluation p).symm

end Eval

end GradedObject

end CategoryTheory

section

variable (𝒜 : Type u) [Category.{v} 𝒜]

/- Domain-style sampling for Definition 12.16.1:
- primary domain: category-theoretic graded objects and their pointwise category structure;
- sampled owner API:
  `CategoryTheory.GradedObject`,
  `GradedObject.categoryOfGradedObjects`,
  `GradedObject.eval`,
  `piEquivalenceFunctorDiscrete`;
- source/core/bridge triage:
  `source-facing`: the textbook category `Gr(𝒜)` of `ℤ`-graded objects;
  `core/canonical`: the owner type `GradedObject ℤ 𝒜`;
  `bridge/view`: the equivalence `piEquivalenceFunctorDiscrete`, used downstream in
  [Lemma_12_16_2](/volume/math/AI4M/users/zcwang/StacksProject_2024/StacksProject_2024/Items/Chap12/Lemma_12_16_2.lean)
  to transfer abelianity from the functor category.

Primitive data are only the ambient category `𝒜` and the grading set `ℤ`. The pointwise category
structure and evaluation functors are derived owner API from mathlib, so there is no room here for
a second local wrapper for `Gr(𝒜)`.
-/

/- Source-facing notation: the Stacks Project writes the category of graded objects in `𝒜` as
`Gr(𝒜)`. This is notation for the canonical owner `GradedObject ℤ 𝒜`. -/
#check Gr(𝒜)

variable (A B : Gr(𝒜))

/- Definition 12.16.1: the category `Gr(𝒜)` of graded objects is the canonical mathlib owner
type `GradedObject ℤ 𝒜`. Its objects are families `A : ℤ → 𝒜`, and its morphisms are families
`f : ∀ i : ℤ, A i ⟶ B i` with the pointwise category structure. Although the source states this
for an additive category, the owner construction itself only needs `[Category 𝒜]`. -/
#check (A ⟶ B)

/- Companion recalls: the category structure on `Gr(𝒜)` is the canonical pointwise owner
instance on `GradedObject ℤ 𝒜`, and the standard projections to degree `i` are the evaluation
functors `GradedObject.eval i : Gr(𝒜) ⥤ 𝒜`. -/
recall GradedObject.categoryOfGradedObjects
recall GradedObject.eval

end

/-! ### Lemma_12_16_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/- Lemma 12.16.2 is a `bridge/view` item in the category-theoretic domain of graded objects and
functor categories. The source-facing owner object is `GradedObject β C`, while the canonical core
owner of the abelian structure is the functor category `Discrete β ⥤ C` via
`piEquivalenceFunctorDiscrete β C` together with the owner instance
`FunctorCategory.functorCategoryAbelian`. There is no extra primitive data here: the
`Preadditive` and finite-product structures on graded objects are only internal support transported
across this equivalence, and the abelian structure is then the canonical transfer via
`abelianOfEquivalence`. -/

/-- Lemma 12.16.2: if `C` is an abelian category, then the category of `β`-graded objects in `C`
is abelian. -/
noncomputable instance (β : Type w) (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (GradedObject β C) := by
  let E := piEquivalenceFunctorDiscrete β C
  letI : Preadditive (GradedObject β C) := Preadditive.ofFullyFaithful E.fullyFaithfulFunctor
  letI : HasFiniteProducts (GradedObject β C) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  exact abelianOfEquivalence E.functor

/-- Graded objects in an abelian category carry the canonical homology package induced by the
abelian structure. -/
noncomputable instance (β : Type w) (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryWithHomology (GradedObject β C) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject β C)) = GradedObject.hasZeroMorphisms β :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    @_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject β C) _ _

end CategoryTheory

/-! ### Remark_12_16_3_Warning (from Chap12) -/
open CategoryTheory.Limits
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

/- Domain-style note: this file is a `bridge/view` item in the category-theoretic domain of graded
objects and exact coproducts. The source-facing owner is `GradedObject.total`, and the sampled
core/canonical declarations are `piEquivalenceFunctorDiscrete β C`, `Sigma.isoColimit`,
`HasExactColimitsOfShape`, and functor-category `evaluation`. There is no new primitive data to
package here: the only local bridge is the natural isomorphism identifying
`GradedObject.total` with the colimit functor on `Discrete β ⥤ C`, and the degreewise kernel claim
is then the standard evaluation-functor fact transported back to graded objects. -/

-- Proof sketch: use the standard counterexample cited in the remark, namely the opposite of the
-- category of abelian sheaves on `ℝ`; countable products there are not exact, so after passing to
-- the opposite category countable coproducts are not exact.
/-- Supporting counterexample for Remark 12.16.3: there exists an abelian category with coproducts
in which countable coproducts are not exact. -/
private theorem exists_abelian_category_with_coproducts_not_countableAB4 :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C) (_ : HasCoproducts C),
      ¬ CountableAB4 C := sorry

private noncomputable def gradedObjectTotalIsoColim (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts C] :
    (piEquivalenceFunctorDiscrete β C).inverse ⋙ GradedObject.total β C ≅
      (colim : (Discrete β ⥤ C) ⥤ C) :=
  NatIso.ofComponents (fun F ↦ Sigma.isoColimit F) <| by
    intro F G α
    apply Sigma.hom_ext
    intro i
    dsimp [GradedObject.total]
    rw [Sigma.ι_map_assoc, Sigma.ι_isoColimit_hom_assoc, Sigma.ι_isoColimit_hom]
    exact (colimit.ι_map α (Discrete.mk i)).symm

private theorem hasExactColimitsOfShape_discrete_int_of_leftExact_gradedObject_total
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts C]
    (h : leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C)) :
    HasExactColimitsOfShape (Discrete ℤ) C := by
  let E := piEquivalenceFunctorDiscrete ℤ C
  let htotal : PreservesFiniteLimits (GradedObject.total ℤ C) :=
    (leftExactFunctor_iff (GradedObject.total ℤ C)).1 h
  letI : PreservesFiniteLimits (E.inverse ⋙ GradedObject.total ℤ C) :=
    ⟨fun J _ _ ↦
      let hE : PreservesLimitsOfShape J E.inverse := by
        infer_instance
      let hshape : PreservesLimitsOfShape J (GradedObject.total ℤ C) :=
        @CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits _ _ _ _
          (GradedObject.total ℤ C) htotal J _ _
      @CategoryTheory.Limits.comp_preservesLimitsOfShape _ _ _ _ J _ _ _ E.inverse
        (GradedObject.total ℤ C) hE hshape⟩
  exact ⟨preservesFiniteLimits_of_natIso (gradedObjectTotalIsoColim ℤ C)⟩

-- Proof sketch: `GradedObject.total ℤ C` identifies with the colimit functor on
-- `Discrete ℤ ⥤ C`; if it were left exact, then exactness of `ℤ`-indexed coproducts would follow.
-- Transporting along `Equiv.intEquivNat` gives exactness of `ℕ`-indexed coproducts, hence
-- `CountableAB4 C`.
/-- If the total functor on `Gr(C)` is left exact, then countable coproducts in the ambient
abelian category are exact. -/
theorem countableAB4_of_leftExact_gradedObject_total {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts C]
    (h : leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C)) : CountableAB4 C := by
  letI : HasExactColimitsOfShape (Discrete ℤ) C :=
    hasExactColimitsOfShape_discrete_int_of_leftExact_gradedObject_total h
  letI : HasExactColimitsOfShape (Discrete ℕ) C :=
    HasExactColimitsOfShape.of_domain_equivalence C (Discrete.equivalence Equiv.intEquivNat)
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_hasExactColimitsOfShape_nat C

-- Proof sketch: exactness implies left exactness. Hence, in the supporting counterexample above,
-- exactness of `GradedObject.total ℤ C` would force `CountableAB4 C`, contradiction.
/-- Remark 12.16.3 (Warning): the total functor
`Gr(C) ⥤ C`, `A ↦ ∐ fun i : ℤ ↦ A i`, need not be exact in general. -/
theorem exists_abelian_category_with_gradedObject_total_not_exact :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C) (_ : HasCoproducts C),
      ¬ exactFunctor (Gr(C)) C (GradedObject.total ℤ C) := by
  rcases exists_abelian_category_with_coproducts_not_countableAB4 with ⟨C, _, _, _, hC⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, ?_⟩
  intro h
  exact hC (countableAB4_of_leftExact_gradedObject_total h.1)

/-- Companion strengthening of Remark 12.16.3: in the same counterexample, the total functor on
graded objects is not left exact. -/
theorem exists_abelian_category_with_gradedObject_total_not_leftExact :
    ∃ (C : Type u) (_ : Category.{v} C) (_ : Abelian C) (_ : HasCoproducts C),
      ¬ leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C) := by
  rcases exists_abelian_category_with_coproducts_not_countableAB4 with ⟨C, _, _, _, hC⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, ?_⟩
  intro h
  exact hC (countableAB4_of_leftExact_gradedObject_total h)

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

local instance gradedObjectEvalPreservesZeroMorphisms (i : ℤ) :
    Functor.PreservesZeroMorphisms (GradedObject.eval i : Gr(C) ⥤ C) where
  map_zero _ _ := rfl

/- Remark 12.16.3 (Warning): although `GradedObject.total` need not be left exact in general,
kernels in a category of graded objects are still computed componentwise. Concretely, evaluation at
degree `i` preserves finite limits, so the standard kernel comparison map for `GradedObject.eval i`
is an isomorphism. -/
theorem gradedObject_kernel_degreewise [Abelian C] {A B : Gr(C)} (φ : A ⟶ B) (i : ℤ) :
    IsIso (kernelComparison φ (GradedObject.eval i : Gr(C) ⥤ C)) := by
  let E := piEquivalenceFunctorDiscrete ℤ C
  letI : PreservesLimit (parallelPair φ 0) (GradedObject.eval i : Gr(C) ⥤ C) := by
    simpa [E, GradedObject.eval] using
      (inferInstance : PreservesLimit (parallelPair φ 0)
        (E.functor ⋙ (evaluation (Discrete ℤ) C).obj (Discrete.mk i)))
  infer_instance

end CategoryTheory

/-! ### Definition_12_16_4 (from Chap12) -/
open CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜]
variable (A : GradedObjectWithShift (1 : ℤ) 𝒜) (k : ℤ)

/- Domain-style sampling:
- primary domain: shifts of graded objects indexed by `ℤ`;
- sampled owner declarations:
  `shiftFunctor`,
  `GradedObject.hasShift`,
  `GradedObject.shiftFunctor_obj_apply`,
  `GradedObject.shiftFunctor_map_apply`.

Source/core/bridge triage:
- `core/canonical`: the `HasShift`/`shiftFunctor` owner on `GradedObjectWithShift (1 : ℤ) 𝒜`;
- `source-facing`: the shifted graded object `A⟦k⟧`;
- `bridge/view`: the component formula from `GradedObject.shiftFunctor_obj_apply`.

Primitive data are only the owner shift functor. The component formula `(A⟦k⟧) i = A (i + k)` and
the corresponding map formula are derived API, so this file should remain a canonical recall item
rather than introducing a parallel local wrapper for graded-object shifts.

Definition 12.16.4: for a graded object `A`, the `k`-shift `A[k]` is the canonical owner object
`A⟦k⟧`. -/
#check A⟦k⟧

/- Companion recall: `GradedObject.shiftFunctor_obj_apply` computes the components of the canonical
graded-object shift, giving `(A⟦k⟧) i = A (i + k)` for grading step `1 : ℤ`. -/
recall GradedObject.shiftFunctor_obj_apply
