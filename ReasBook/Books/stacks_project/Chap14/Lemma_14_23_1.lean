import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial

universe v u

namespace AlgebraicTopology.DoldKan

@[inherit_doc]
scoped[DoldKan] notation "s[" X "]" => AlgebraicTopology.AlternatingFaceMapComplex.obj X

end AlgebraicTopology.DoldKan

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteLimits A] [HasFiniteColimits A]

/- Domain-style sampling for Lemma 14.23.1:
- primary domain: exact functors and the alternating face map complex on simplicial objects of a
  preadditive category with finite limits and finite colimits;
- sampled owner declarations:
  `exactFunctor`,
  `exactFunctor_iff`,
  `AlgebraicTopology.alternatingFaceMapComplex`,
  `AlgebraicTopology.map_alternatingFaceMapComplex`;
- best owner abstraction: the canonical exactness predicate
  `exactFunctor (SimplicialObject A) (ChainComplex A ℕ)` applied to the owner functor
  `alternatingFaceMapComplex A`;
- primitive data: the ambient category `A` together with its preadditive structure and finite
  limits and finite colimits;
- derived API: the source-facing exactness theorem used later to deduce exactness of the
  normalized Moore complex.

Source/core/bridge triage:
- `source-facing`: the exactness statement for the specific functor denoted `s` in the Stacks text;
- `core/canonical`: `exactFunctor`, together with the owner functor `alternatingFaceMapComplex A`;
- `bridge/view`: this theorem is the source-facing specialization of the canonical exact-functor
  owner predicate, with no extra wrapper structure. -/

private def alternatingFaceMapComplexCompEvalIso (n : ℕ) :
    alternatingFaceMapComplex A ⋙ HomologicalComplex.eval A (ComplexShape.down ℕ) n ≅
      (evaluation SimplexCategoryᵒᵖ A).obj (Opposite.op ⦋n⦌) :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)
    (fun {X Y} f ↦ by simp [alternatingFaceMapComplex_map_f])

omit [HasFiniteColimits A] in
private theorem alternatingFaceMapComplex_preservesFiniteLimits :
    PreservesFiniteLimits (alternatingFaceMapComplex A) :=
  ⟨fun _ _ _ ↦
    HomologicalComplex.preservesLimitsOfShape_of_eval (alternatingFaceMapComplex A)
      (fun n ↦
        preservesLimitsOfShape_of_natIso (alternatingFaceMapComplexCompEvalIso n).symm)⟩

omit [HasFiniteLimits A] in
private theorem alternatingFaceMapComplex_preservesFiniteColimits :
    PreservesFiniteColimits (alternatingFaceMapComplex A) :=
  ⟨fun _ _ _ ↦
    HomologicalComplex.preservesColimitsOfShape_of_eval (alternatingFaceMapComplex A)
      (fun n ↦
        preservesColimitsOfShape_of_natIso (alternatingFaceMapComplexCompEvalIso n).symm)⟩

-- Proof sketch: by Lemma 14.22.1, exactness in the simplicial-object and chain-complex
-- categories of a preadditive category with finite limits and finite colimits is detected
-- degreewise. The functor
-- `AlgebraicTopology.alternatingFaceMapComplex A` is defined degreewise from evaluation on the
-- simplicial object, so it preserves exact short complexes objectwise and hence is exact.
/-- Lemma 14.23.1: the functor `s`, i.e. the alternating face map complex functor
`AlgebraicTopology.alternatingFaceMapComplex A`, is exact. -/
theorem alternatingFaceMapComplex_exact :
    exactFunctor (SimplicialObject A) (ChainComplex A ℕ) (alternatingFaceMapComplex A) := by
  exact (exactFunctor_iff _).2
    ⟨alternatingFaceMapComplex_preservesFiniteLimits,
      alternatingFaceMapComplex_preservesFiniteColimits⟩

end

end CategoryTheory
