import Nesterov.Chap05.Definition_5_0_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.16 lies in the finite-dimensional Chapter 5 self-concordant minimization domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, specialized here to the whole-space owner
  `IsSelfConcordantOnWith Set.univ Mf f`;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, likewise specialized to
  `Set.univ`;
* `IsMinOn` and `isMinOn_univ_iff` in mathlib, the canonical owner and textbook bridge for
  whole-space minimizers;
* `isMinOn_iff_eq_sInf_range` from `Chap03/Definition_3_33`, the project owner bridge between
  whole-space attainment and the infimum of `Set.range f`.

Source/core/bridge triage:
* source-facing: bounded-below existence and uniqueness of a global minimizer of `f`;
* core/canonical: `IsSelfConcordantOnWith Set.univ Mf f`,
  `HasPositiveDefiniteHessianOn Set.univ f`, and `IsMinOn f Set.univ x`;
* bridge/view: the attained-infimum identity `f xStar = sInf (Set.range f)`.

Primitive data:
* the ambient objective `f : E → ℝ`;
* self-concordance of `f` on `Set.univ`;
* positive definiteness of its Hessian on `Set.univ`;
* lower boundedness of the range `Set.range f`.

Derived API:
* existence of a global minimizer of `f`;
* uniqueness of that minimizer.

The previous revision incorrectly strengthened the textbook finite-dimensional whole-space
attainment theorem to an arbitrary complete real inner-product space, where bounded below need not
imply attainment. The public owner is restored here to the source-faithful whole-space
finite-dimensional formulation. -/

namespace IsSelfConcordantOnWith

section

variable {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith Set.univ Mf f] [HasPositiveDefiniteHessianOn Set.univ f]

-- Proof sketch: boundedness below is expressed by `BddBelow (Set.range f)`, the canonical
-- whole-space image owner. Positive-definite Hessian on `Set.univ` supplies the strict convexity
-- needed for uniqueness once existence is obtained.
/-- Theorem 5.1.16: on a finite-dimensional real inner-product space, if a self-concordant
objective on the whole space has positive-definite Hessian everywhere and is bounded below, then
it attains a unique global minimum. -/
theorem existsUnique_isMinOn_of_bddBelow
    (hbelow : BddBelow (Set.range f)) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  sorry

end

end IsSelfConcordantOnWith

end
