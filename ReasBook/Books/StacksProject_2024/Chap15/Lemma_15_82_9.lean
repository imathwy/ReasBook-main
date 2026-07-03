import Mathlib
import StacksProject_2024.Chap15.Definition_15_82_4
import StacksProject_2024.Chap15.Lemma_15_65_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

/- Domain-style sampling for Lemma 15.82.9:
- primary domain: relative pseudo-coherence for bounded-above cochain complexes of `A`-modules
  over a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CochainComplex.minus`,
  `CochainComplex.IsMPseudoCoherentRelativeTo`,
  `CochainComplex.IsPseudoCoherentRelativeTo`,
  `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`;
- best owner abstraction: the source-facing owners are the relative predicates
  `CochainComplex.IsMPseudoCoherentRelativeTo` and
  `CochainComplex.IsPseudoCoherentRelativeTo`, while bounded-above should be expressed through the
  chapter owner `CochainComplex.minus` rather than the duplicate existential presentation
  `∃ b, K.IsStrictlyLE b`;
- primitive vs. derived:
  primitive data are the bounded-above cochain complex `K : CpxA` and the termwise relative
  pseudo-coherence hypotheses on `K.X i`;
  derived API is the resulting relative pseudo-coherence of `K`;
- source/core/bridge triage:
  `source-facing`: the two termwise bounded-above criteria below;
  `core/canonical`: `CochainComplex.minus`, `CochainComplex.IsMPseudoCoherentRelativeTo`, and
    `CochainComplex.IsPseudoCoherentRelativeTo`;
  `bridge/view`: restriction along surjective polynomial presentations together with the absolute
    bounded-above criterion of `CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise`.
- layer: this file stays source-facing and reuses the existing bounded-above owner instead of
  restating it as an existential bound. -/

-- Proof sketch: fix a surjective polynomial presentation `α : R[x_1, ..., x_n] → A`. By the
-- relative hypotheses, every term of the restricted complex is `(m - i)`-pseudo-coherent over the
-- polynomial ring. Apply Lemma `15.65.9` to that restricted bounded-above complex, and then
-- quantify over all presentations.
/-- Lemma 15.82.9 (1): if `R → A` is finite type and a bounded-above cochain complex of
`A`-modules has term `K.X i` `(m - i)`-pseudo-coherent relative to `R` for every `i`, then the
complex is `m`-pseudo-coherent relative to `R`. -/
theorem cochainComplex_isMPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    (K : CpxA) (m : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: for each surjective polynomial presentation of `A` over `R`, every term of the
-- restricted complex is pseudo-coherent over the polynomial ring. Apply Lemma `15.65.9` in its
-- pseudo-coherent form to the restricted bounded-above complex, and then quantify over all
-- presentations.
/-- Lemma 15.82.9 (2): if `R → A` is finite type and a bounded-above cochain complex of
`A`-modules has pseudo-coherent terms relative to `R`, then the complex is pseudo-coherent
relative to `R`. -/
theorem cochainComplex_isPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    (K : CpxA)
    (hbounded : CochainComplex.minus (ModuleCat A) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := sorry

end
