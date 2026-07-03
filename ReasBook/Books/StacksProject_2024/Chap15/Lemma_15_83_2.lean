import Mathlib
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Definition_15_83_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling for Lemma 15.83.2:
- primary domain: commutative algebra of perfect ring maps, compared with perfect modules over a
  surjective polynomial presentation;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `ModuleCat.IsPerfect`,
  `Module.FinitePresentationRelativeTo`,
  `ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms`;
- best owner abstraction: the source-facing theorem belongs on the ring-map owner
  `(algebraMap A B).IsPerfectRingMap`, while the polynomial-presentation side should speak
  directly in the canonical module owner `ModuleCat.IsPerfect`, not via the restriction functor as
  public data;
- primitive vs. derived:
  primitive data are a surjective polynomial presentation `α : A[x₁, ..., xₙ] → B` and the
  induced `A[x₁, ..., xₙ]`-module structure on `B`;
  derived API is the finite projective resolution reformulation from Lemma `15.75.3`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `RingHom.IsPerfectRingMap` and `ModuleCat.IsPerfect`;
- `bridge/view`: restriction of scalars along a polynomial presentation.

The statement should therefore keep the source-facing equivalence while using the induced module
structure on `B` as the public owner-level formulation, rather than the functorial bridge term.
-/

-- Proof sketch: if `A → B` is perfect, then it is finite type, so choose a surjective polynomial
-- presentation `MvPolynomial (Fin n) A →ₐ[A] B`. The pseudo-coherence and finite tor dimension
-- hypotheses then show that `B`, viewed through this presentation, is a perfect module over the
-- polynomial ring. Conversely, if such a presentation makes the restricted
-- `MvPolynomial (Fin n) A`-module `B` perfect, then `A → B` is pseudo-coherent and `B` has
-- finite tor dimension over `A`, hence the ring map is perfect.
/-- Lemma 15.83.2: a ring map `A → B` is perfect if and only if there exists a surjective
polynomial presentation `MvPolynomial (Fin n) A →ₐ[A] B` such that `B`, viewed as a module over
`MvPolynomial (Fin n) A`, is perfect. By Lemma `15.75.3`, this is equivalent to requiring a
finite resolution by finite projective `MvPolynomial (Fin n) A`-modules. -/
theorem isPerfectRingMap_iff_exists_polynomialPresentation_with_perfect_restrictedModule :
    (algebraMap A B).IsPerfectRingMap ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B),
        Function.Surjective α ∧
          let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
          (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := sorry

end

end Algebra
