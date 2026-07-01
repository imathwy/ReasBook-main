import Mathlib.Tactic.Recall
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import stacks_project.Chap12.Lemma_12_19_12

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace ShortComplex

open FilteredObject FilteredObject.Hom

/- Domain-style sampling for Lemma 12.19.15:
- primary domain: filtered objects in an abelian category, viewed through short-complex exactness
- sampled owner declarations:
  `FilteredObject.IsFinite`,
  `FilteredObject.Hom.Strict`,
  `associatedGradedFunctor`,
  `GradedObject.eval`,
  `ShortComplex.Exact.map`
- owner abstraction used here: exactness of a short complex after applying the canonical filtered
  functors `associatedGradedFunctor`, `stageFunctor`, and `quotientFunctor`
- primitive data: a short complex `S : ShortComplex (FilteredObject 𝒜)` and finiteness of its
  three filtered terms
- derived API: degreewise exactness, stage exactness, quotient exactness, strictness, and
  exactness of the underlying short complex
- source/core/bridge triage:
  `(1)` is a `source-facing` bridge theorem obtained from the canonical owner
  `ShortComplex.Exact.map` by evaluating the associated graded short complex in degree `p`;
  `(2)` through `(5)` are `source-facing` bridge theorems for filtered short complexes. 
-/

variable {S : ShortComplex (FilteredObject 𝒜)}

/-- Lemma 12.19.15 (1): if the associated graded complex is exact, then
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` is exact for every `p`. This is the source-facing specialization of
the owner theorem `ShortComplex.Exact.map` along the evaluation functor `GradedObject.eval p`. -/
theorem gradedPiece_exact_of_associatedGraded_exact
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) (p : ℤ) :
    ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)) := by
  let E := piEquivalenceFunctorDiscrete ℤ 𝒜
  letI : Functor.PreservesHomology (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜) :=
    { preservesKernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesLimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p)))
      preservesCokernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesColimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p))) }
  simpa using hgr.map (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜)

section FiniteFiltrations

variable (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
  (hgr : ShortComplex.Exact (S.map associatedGradedFunctor))

-- Proof sketch: argue by induction on the common finite length of the filtrations, peeling off the
-- top nonzero step and applying the short exact sequence relating `F^p` to the associated graded
-- piece and the quotient filtration.
/-- Lemma 12.19.15 (2): if the filtrations are finite and the associated graded complex is exact,
then `F^p(A) ⟶ F^p(B) ⟶ F^p(C)` is exact for every `p`. -/
theorem stage_exact_of_associatedGraded_exact
    (p : ℤ) :
    ShortComplex.Exact (S.map (stageFunctor p)) := sorry

-- Proof sketch: perform the same finite-length induction on the quotient filtrations
-- `A / F^n A`, `B / F^n B`, and `C / F^n C`, using exactness of the graded pieces to identify the
-- successive quotients.
/-- Lemma 12.19.15 (3): if the filtrations are finite and the associated graded complex is exact,
then `A / F^p(A) ⟶ B / F^p(B) ⟶ C / F^p(C)` is exact for every `p`. -/
theorem quotient_exact_of_associatedGraded_exact
    (p : ℤ) :
    ShortComplex.Exact (S.map (quotientFunctor p)) := sorry

-- Proof sketch: apply the stage exactness and the underlying exactness to identify the images of
-- `S.f` and `S.g` on each filtration level with the intersections required in the
-- definition of strictness.
/-- Lemma 12.19.15 (4): if the filtrations are finite and the associated graded complex is exact,
then both maps of filtered objects are strict. -/
theorem strict_of_associatedGraded_exact
    : Strict S.f ∧ Strict S.g := sorry

-- Proof sketch: apply the quotient exactness at a stage above the top nonzero filtration step, so
-- the quotients identify with the original objects and the quotient complex becomes the underlying
-- short complex.
/-- Lemma 12.19.15 (5): if the filtrations are finite and the associated graded complex is exact,
then the underlying sequence `A.obj ⟶ B.obj ⟶ C.obj` is exact. -/
theorem underlying_exact_of_associatedGraded_exact
    : ShortComplex.Exact (S.map FilteredObject.forget) := sorry

end FiniteFiltrations

end ShortComplex

end CategoryTheory
