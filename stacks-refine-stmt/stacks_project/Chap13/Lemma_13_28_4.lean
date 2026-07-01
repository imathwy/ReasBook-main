import Mathlib
import stacks_project.Chap12.Definition_12_11_1
import stacks_project.Chap13.Definition_13_28_1
import stacks_project.Chap13.Lemma_13_6_4

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 13.28.4:
- primary domain: triangulated Grothendieck groups and homological functors to abelian categories;
- sampled owner declarations:
  `Functor.IsHomological`,
  `Functor.shiftVanishingBounded`,
  `Functor.mem_shiftVanishingBounded_iff`,
  `Functor.ShiftSequence.tautological`,
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.TriangulatedK0.of`,
  `CategoryTheory.TriangulatedK0.lift`;
- source-facing layer: Lemma 13.28.4 constructs the Euler-characteristic map on `K₀` attached to a
  homological functor with finite shift support;
- core/canonical owners: the owner functor `H`, the chapter-level object property
  `H.shiftVanishingBounded`, the global pointwise boundedness hypothesis
  `∀ X, H.shiftVanishingBounded X`, the quotient owner
  `CategoryTheory.TriangulatedK0`, and its class map `CategoryTheory.TriangulatedK0.of`;
- bridge/view: the passage from the global boundedness hypothesis to the finite support of the
  alternating Euler summand, and then to the class-evaluation formula for the induced map.

Primitive data split into two layers:
- source-facing global input for the `K₀` map: the pointwise boundedness hypothesis
  `∀ X, H.shiftVanishingBounded X`;
- objectwise support control is derived API, expressed canonically by the companion theorem
  `eulerClass_hasFiniteSupport` for the alternating summand
  `fun i ↦ i.negOnePow • K₀[(H.shift i).obj X]`.
The raw free-abelian-group lift and the quotient-descending kernel argument are derived
implementation data, so they should not remain part of the public surface. Since the main
constructions are attached to the functor itself, the public API should live under the owner
namespace `Functor`, with the object-level Euler class given intrinsically by `∑ᶠ` and the `K₀`
map consuming the global containment hypothesis.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped BigOperators

noncomputable section

namespace CategoryTheory

universe u₁ u₂ v₁ v₂

namespace Functor

section EulerClass

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [H.ShiftSequence ℤ]

/-- If `X` lies in the bounded shift-vanishing owner for `H`, then the corresponding alternating
Euler-class summand has finite support. -/
theorem eulerClass_hasFiniteSupport (X : D) (hX : H.shiftVanishingBounded X) :
    Function.HasFiniteSupport
      (fun i : ℤ ↦ i.negOnePow • K₀[(H.shift i).obj X]) := sorry

/-- The alternating-sum Euler class attached to an object `X` and a shifted homological functor
`H`, expressed canonically as a `finsum`; finite support is supplied separately by
`eulerClass_hasFiniteSupport` when needed. -/
def eulerClass (X : D) : AbelianK0 A :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(H.shift i).obj X]

end EulerClass

section EulerK0Map

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]

-- Proof sketch: for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`, the long exact homology
-- sequence of the homological functor breaks into short exact pieces in `A`. Additivity in the
-- abelian Grothendieck group then gives
-- `∑ (-1)^i [H(X₂[i])] = ∑ (-1)^i [H(X₁[i])] + ∑ (-1)^i [H(X₃[i])]`, and the finite-support
-- hypothesis ensures the alternating sums are genuine finite sums.
/-- Distinguished-triangle relations are killed by the alternating-sum map attached to a
homological functor whose values lie in `H.shiftVanishingBounded` on every object. -/
private theorem relations_le_ker_eulerClass
    (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0.relations D ≤
      (FreeAbelianGroup.lift
        fun X ↦ H.eulerClass X).ker := sorry

/-- Lemma 13.28.4: a homological functor from a triangulated category to an abelian category,
whose shifted values are nonzero in only finitely many degrees on each object, induces a canonical
homomorphism `K₀(\mathcal D) → K₀(\mathcal A)` sending `[X]` to the alternating sum
`∑ (-1)^i [H(X[i])]`. -/
def eulerK0Map (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0 D →+ AbelianK0 A :=
  TriangulatedK0.lift
    (fun X ↦ H.eulerClass X)
    (relations_le_ker_eulerClass H hH)

-- Proof sketch: `eulerK0Map` is the quotient lift of the objectwise Euler-class function
-- `X ↦ H.eulerClass X`, so evaluating it on the class of an
-- object `X` reduces to
-- the defining alternating-sum formula on generators.
/-- The induced map on `K₀` sends the class of `X` to the alternating sum of the classes of the
shifted objects `H(X[i])`. -/
@[simp] theorem eulerK0Map_apply_of
    (hH : ∀ X : D, H.shiftVanishingBounded X) (X : D) :
    H.eulerK0Map hH (TriangulatedK0.of X) = H.eulerClass X := by
  simpa using
    TriangulatedK0.lift_of
      (fun Y ↦ H.eulerClass Y)
      (relations_le_ker_eulerClass H hH)
      X

end EulerK0Map

end Functor
end CategoryTheory
