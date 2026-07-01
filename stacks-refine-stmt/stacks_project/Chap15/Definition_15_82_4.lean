import Mathlib
import stacks_project.Chap15.Lemma_15_65_5
import stacks_project.Chap15.Lemma_15_82_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
/- Domain-style sampling for Definition 15.82.4:
- primary domain: relative pseudo-coherence for cochain complexes and modules over an `R`-algebra
  `A` of finite type over `R`;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation`,
  `cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation`;
- best owner abstraction: the source-facing owners are the relative predicates
  `CochainComplex.IsMPseudoCoherentRelativeTo` and
  `CochainComplex.IsPseudoCoherentRelativeTo`; the absolute pseudo-coherence owners on the
  restricted complexes over polynomial presentation rings remain the canonical core notions;
- primitive vs. derived:
  primitive data are the universal tests over surjective polynomial presentations of the finite
  type `R`-algebra `A`;
  derived API is the "some presentation" criterion and the module specialization
  `M ↦ M[0]`, exposed both for bundled `ModuleCat A` objects and for ordinary unbundled
  `A`-modules;
- source/core/bridge triage:
  `source-facing`: the relative pseudo-coherence predicates for cochain complexes and modules;
  `core/canonical`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent` over
    the presentation rings;
  `bridge/view`: restriction of scalars along a polynomial presentation, plus the thin unbundled
    module surface `Module.IsMPseudoCoherentRelativeTo` /
    `Module.IsPseudoCoherentRelativeTo`.
- layer: this file stays source-facing and reuses the established presentationwise owner API
  instead of keeping redundant local `_def` / `_iff` wrappers around definitional equalities.
-/

namespace CochainComplex

/-- Definition 15.82.4 (1): a cochain complex of `A`-modules is `m`-pseudo-coherent relative to
`R` if it satisfies the equivalent conditions of Lemma `15.82.3`, equivalently if it is
`m`-pseudo-coherent over every surjective polynomial presentation of `A` over `R`. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- Relative `m`-pseudo-coherence can be checked on some surjective polynomial presentation of the
finite type `R`-algebra `A`. -/
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := by
  simpa [IsMPseudoCoherentRelativeTo] using
    (cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
      K m).symm

/-- Definition 15.82.4 (2): a cochain complex of `A`-modules is pseudo-coherent relative to `R`
if it is `m`-pseudo-coherent relative to `R` for every integer `m`. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Relative pseudo-coherence is equivalent to pseudo-coherence over every surjective polynomial
presentation of the finite type `R`-algebra `A`. -/
theorem isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A]
    (K : CpxA) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
        (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
  constructor
  · intro hK n α hα
    exact
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α)).out 1 0).mp
        (fun m ↦ hK m n α hα)
  · intro hK m n α hα
    have hPresentation :
        ∀ m : ℤ, (K.polynomialPresentationRestriction α).IsMPseudoCoherent m :=
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α)).out 0 1).mp
        (hK n α hα)
    exact hPresentation m

/-- Relative pseudo-coherence can be checked on some surjective polynomial presentation of the
finite type `R`-algebra `A`. -/
theorem isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
  calc
    K.IsPseudoCoherentRelativeTo R ↔
        ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
          (K.polynomialPresentationRestriction α).IsPseudoCoherent :=
      isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation K
    _ ↔
        ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
          Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
      simpa using
        (cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
          K).symm

end CochainComplex

/-- Definition 15.82.4 (3): an `A`-module is `m`-pseudo-coherent relative to `R` if the
degree-zero cochain complex `M[0]` is `m`-pseudo-coherent relative to `R`. -/
abbrev ModuleCat.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) (m : ℤ) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsMPseudoCoherentRelativeTo R m

/-- Definition 15.82.4 (4): an `A`-module is pseudo-coherent relative to `R` if the degree-zero
cochain complex `M[0]` is pseudo-coherent relative to `R`. -/
abbrev ModuleCat.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

namespace Module

/-- Relative `m`-pseudo-coherence for an ordinary `A`-module, viewed through the canonical bundled
module object. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type u_1) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  (ModuleCat.of A M).IsMPseudoCoherentRelativeTo R m

/-- Relative pseudo-coherence for an ordinary `A`-module, viewed through the canonical bundled
module object. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : Type u_1) [AddCommGroup M] [Module A M] : Prop :=
  (ModuleCat.of A M).IsPseudoCoherentRelativeTo R

end Module

end
