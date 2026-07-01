import Mathlib
import stacks_project.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Algebra.FiniteType A B]

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.82.15:
- primary domain: relative pseudo-coherence in derived categories over a tower `R → A → B` of
  finite type algebras;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherentRelativeTo_of_homology`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: the chapter owner predicates
  `DerivedCategory.IsMPseudoCoherentRelativeTo R K m` and
  `DerivedCategory.IsPseudoCoherentRelativeTo R K`, together with the thin module bridge
  `Module.IsPseudoCoherentRelativeTo R A A` for the intermediate algebra;
- primitive vs. derived:
  primitive data are the finite-type hypotheses on `R → A` and `A → B` together with the
  pseudo-coherence of `A` relative to `R`; the finite-type structure on `R → B` is derived by the
  canonical transitivity instance and should not remain on the public theorem surface;
- source/core/bridge triage:
  `source-facing`: the comparison lemmas below for relative pseudo-coherence across the
    intermediate algebra `A`;
  `core/canonical`: the owner predicates `DerivedCategory.IsMPseudoCoherentRelativeTo` and
    `DerivedCategory.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the internal passage from the tower hypotheses to the induced finite-type
    structure on `R → B`.
- layer: this refinement stays source-facing and keeps the induced `R → B` finite-type witness
  internal, without adding a public wrapper.
-/

-- Proof sketch: expand relative pseudo-coherence over `A` using a surjective polynomial
-- presentation `A[y₁, ..., yₙ] → B`. Choose a surjective polynomial presentation `R[x₁, ..., xₘ] → A`.
-- By the hypothesis on `A`, the algebra `A[y₁, ..., yₙ]` is pseudo-coherent over the polynomial
-- ring `R[x₁, ..., xₘ, y₁, ..., yₙ]` via flat base change, using Lemma `15.65.13`. Then apply
-- Lemma `15.65.11` to compare `m`-pseudo-coherence over these two presentation rings, and quantify
-- over all presentations.
/-- Lemma 15.82.15 (1): if `A → B` is a finite type map of finite type `R`-algebras and `A`,
viewed as an `A`-module, is pseudo-coherent relative to `R`, then a derived `B`-complex is
`m`-pseudo-coherent relative to `A` if and only if it is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB) (m : ℤ)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: apply part `(1)` for every integer `m`. Pseudo-coherence is equivalent to
-- `m`-pseudo-coherence for all `m`, so the relative pseudo-coherent statement follows by
-- unfolding the definition on both sides.
/-- Lemma 15.82.15 (2): under the same hypotheses, a derived `B`-complex is pseudo-coherent
relative to `A` if and only if it is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory
