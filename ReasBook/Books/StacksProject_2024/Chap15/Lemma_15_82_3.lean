import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_5

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

/- Domain-style sampling for Lemma 15.82.3:
- primary domain: pseudo-coherence for cochain complexes after restriction along surjective
  polynomial presentations of an `R`-algebra `A`, with finite type only needed for the
  some-presentation/every-presentation equivalences;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `isMPseudoCoherent_iff_restrictScalars_evalAtZero`,
  `cochainComplex_pseudoCoherent_tfae`;
- best owner abstraction: the canonical owner is the restricted cochain complex over the
  presentation ring, together with the project-level cochain-complex predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; the “some/every
  presentation” formulations are source-facing quantifiers over that owner, not separate public
  data;
- primitive vs. derived:
  primitive data are a surjective polynomial presentation
  `α : MvPolynomial (Fin n) R →ₐ[R] A` and the associated restricted complex;
  derived API is the existential or universal quantification over all such presentations;
- source/core/bridge triage:
  `source-facing`: the two equivalences in Lemma 15.82.3;
  `core/canonical`: `CochainComplex.IsMPseudoCoherent` and
    `CochainComplex.IsPseudoCoherent`;
  `bridge/view`: restriction of scalars along a polynomial presentation.
- layer: this file stays source-facing and deletes redundant public wrappers around the bridge
  data. -/

namespace CochainComplex

/-- Restrict a cochain complex of `A`-modules along a polynomial presentation of `A` over `R`. -/
abbrev polynomialPresentationRestriction
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

end CochainComplex

-- Proof sketch: compare a chosen surjective polynomial presentation with an arbitrary one by
-- adjoining both sets of variables and mapping the added variables to chosen lifts. After a change
-- of coordinates, the comparison maps are iterated evaluation-at-zero maps, so repeated
-- applications of Lemma `15.82.2` transfer `m`-pseudo-coherence from the chosen presentation to
-- every presentation, and the converse direction is immediate.
/-- Lemma 15.82.3: for a finite type ring map `R → A`, a cochain complex of `A`-modules is
`m`-pseudo-coherent over some surjective polynomial presentation of `A` over `R` if and only if it
is `m`-pseudo-coherent over every such presentation. -/
theorem cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) (m : ℤ) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsMPseudoCoherent m :=
    sorry

-- Proof sketch: use the previous equivalence for every integer `m`; then invoke Lemma `15.65.5`
-- on each presentation ring to pass between pseudo-coherence and `m`-pseudo-coherence for all
-- `m`.
/-- Pseudo-coherence relative to `R` can likewise be checked on one surjective polynomial
presentation of the finite type `R`-algebra `A`. -/
theorem cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsPseudoCoherent := sorry

end
