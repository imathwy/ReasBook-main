import Mathlib
import stacks_project.Chap15.Definition_15_82_4
import stacks_project.Chap15.Lemma_15_65_10

noncomputable section

open CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

private abbrev polynomialPresentationRestrictionDerived {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (K : DModA) :
    DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) :=
  (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K

/-- A derived `A`-complex is `m`-pseudo-coherent relative to `R` if it becomes
`m`-pseudo-coherent after restriction along every surjective polynomial presentation of `A`
over `R`. -/
abbrev DerivedCategory.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    (polynomialPresentationRestrictionDerived α K).IsMPseudoCoherent m

/-- A derived `A`-complex is pseudo-coherent relative to `R` if it is `m`-pseudo-coherent
relative to `R` for every integer `m`. -/
abbrev DerivedCategory.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/- Domain-style sampling for Lemma 15.82.10:
- primary domain: relative pseudo-coherence in `D(A)` for a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherent_of_homology`;
- best owner abstraction: the canonical owner for the derived notion is
  `DerivedCategory.IsMPseudoCoherentRelativeTo`, with the ambient algebra inferred strictly from
  the derived object;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence predicates from Definition `15.82.4` together
  with the derived-category owner `DerivedCategory.IsMPseudoCoherentRelativeTo` introduced here;
  derived API is the bounded-above homology criterion proved here by applying the absolute lemma
  presentationwise after restriction of scalars;
- source/core/bridge triage:
  `source-facing`: the bounded-above homology criteria from Lemma `15.82.10`;
  `core/canonical`: the existing relative pseudo-coherence owners `IsMPseudoCoherentRelativeTo`
    and `IsPseudoCoherentRelativeTo`;
  `bridge/view`: passage to each surjective polynomial presentation and application of
    `boundedAbove_isMPseudoCoherent_of_homology`.
- layer: this file stays source-facing and reuses the existing canonical owners instead of keeping
  a parallel `...RelativeToBase` vocabulary.
-/

-- Proof sketch: fix a surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`. The
-- cohomology modules of the restricted complex are exactly the cohomology modules of `K` viewed as
-- modules over `R[x₁, ..., xₙ]`, so the hypothesis gives the `(m - i)`-pseudo-coherence needed to
-- apply Lemma `15.65.10` over the polynomial ring.
/-- Lemma 15.82.10 (1): if a bounded-above derived `A`-complex has cohomology modules that are
`(m - i)`-pseudo-coherent relative to `R` in every degree, then the complex is `m`-pseudo-coherent
relative to `R`. -/
theorem boundedAbove_isMPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus) (m : ℤ)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.obj.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: for each surjective polynomial presentation of `A` over `R`, the restricted
-- cohomology modules are pseudo-coherent over that presentation ring by hypothesis. Apply the
-- pseudo-coherent variant of Lemma `15.65.10` presentationwise.
/-- Lemma 15.82.10 (2): if every cohomology module of a bounded-above derived `A`-complex is
pseudo-coherent relative to `R`, then the complex itself is pseudo-coherent relative to `R`. -/
theorem boundedAbove_isPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsPseudoCoherentRelativeTo R) :
    K.obj.IsPseudoCoherentRelativeTo R := by
  intro m
  exact boundedAbove_isMPseudoCoherentRelativeTo_of_homology K m fun i ↦ hH i (m - i)

end

end CategoryTheory
