import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Topology.CWComplex.Abstract.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_2_2

open CategoryTheory
open scoped Topology.Homotopy

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no ready-made compact-CW criterion for the realization
-- counit surfaced in the current environment, while Chapter 16 already fixes the canonical map
-- `sSetTopAdj.counit.app X`. The source-faithful finite singular datum is therefore a
-- finite subcomplex `A : (TopCat.toSSet.obj X).Subcomplex`, whose realization maps to `X` through
-- the inclusion `A.ι` followed by the counit.

/-- The comparison map from the realization of a finite singular subcomplex of `X` to `X`. -/
abbrev finiteSingularRealizationEvaluation (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex) :
    SSet.toTop.obj A.toSSet ⟶ X :=
  SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app X

/-- A map from `K` to `X` factors through the realization of a finite singular subcomplex of `X`
up to homotopy. Compactness of `K` is an ambient hypothesis only in the compact-CW applications
below, not part of this factoring predicate itself. -/
def FactorsThroughFiniteSingularRealization (K : TopCat.{u}) (X : TopCat.{u}) (f : C(K, X)) :
    Prop :=
  ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (g : C(K, SSet.toTop.obj A.1.toSSet)),
      ((finiteSingularRealizationEvaluation X A.1).hom.comp g).Homotopic f

/-- For a fixed domain `K` and finite singular subcomplex `A` of `X`, the comparison map
`finiteSingularRealizationEvaluation X A` reflects homotopies out of `K`. Compactness of `K`
enters only in the compact-CW hypotheses of the main theorem. -/
def FiniteSingularRealizationEvaluationReflectsHomotopy (K : TopCat.{u}) (X : TopCat.{u})
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }) : Prop :=
  ∀ {g₀ g₁ : C(K, SSet.toTop.obj A.1.toSSet)},
    (((finiteSingularRealizationEvaluation X A.1).hom.comp g₀).Homotopic
      ((finiteSingularRealizationEvaluation X A.1).hom.comp g₁)) →
      g₀.Homotopic g₁

/-- Proof step 16.3.5: to prove that the canonical map `Γ X ⟶ X` is a weak equivalence, it
suffices to translate maps from compact CW domains into finite singular data, formalized here as
factorizations through realizations of finite subcomplexes `A : (TopCat.toSSet.obj X).Subcomplex`,
and then to lift homotopies on each such finite datum. The theorem records that these two
finite-reduction hypotheses suffice to conclude
`IsWeakEquivalence ((sSetTopAdj.counit.app X).hom)`. In the source proof, the finite-datum
homotopies are built using the universal simplex coordinates carried in mathlib by
`SimplexCategory.toTopHomeo`.
-/
theorem isWeakEquivalence_singularRealizationEvaluation_of_compactCWFiniteReduction
    (X : TopCat.{u})
    (hfactor :
      ∀ {K : TopCat.{u}} [CompactSpace K] (hK : TopCat.CWComplex K) (f : C(K, X)),
        FactorsThroughFiniteSingularRealization K X f)
    (hlift :
      ∀ {K : TopCat.{u}} [CompactSpace K] (hK : TopCat.CWComplex K)
        {A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }},
          FiniteSingularRealizationEvaluationReflectsHomotopy K X A) :
    IsWeakEquivalence ((sSetTopAdj.counit.app X).hom) := sorry
