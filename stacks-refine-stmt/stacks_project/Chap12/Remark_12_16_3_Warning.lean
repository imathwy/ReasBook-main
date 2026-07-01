import Mathlib
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import stacks_project.Chap12.Definition_12_16_1
import stacks_project.Chap12.Lemma_12_16_2

-- Declarations for this item will be appended below by the statement pipeline.

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
