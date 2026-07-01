import Mathlib
import stacks_project.Chap15.Definition_15_105_1
import stacks_project.Chap15.Lemma_15_105_7
import stacks_project.Chap15.Lemma_15_105_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.105.17:
- primary domain: weakly étale commutative algebra and the induced residue-field extensions along
  primes in a fiber;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Algebra.IsWeaklyEtale.baseChange`,
  `weaklyEtale_over_field_tfae`,
  `Ideal.primesOver`;
- best owner abstraction: the theorem is `source-facing`, but the prime-over-prime input should be
  expressed by the canonical owner set `p.primesOver B` rather than by a raw ideal plus separate
  `[IsPrime]` and `[LiesOver]` arguments;
- primitive data: the weakly étale owner on `A → B`, the prime `p : Ideal A`, and the chosen
  prime over `p` packaged as `q : p.primesOver B`;
- derived API: the induced `p.ResidueField`-algebra structure on `q.1.ResidueField`, together
  with the algebraicity and separability assertions and their atomic projection lemmas.

Source/core/bridge triage:
- `source-facing`: `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`;
- `core/canonical`: `Algebra.IsWeaklyEtale`, `Ideal.primesOver`, and `Ideal.ResidueField`;
- `bridge/view`: base change to the fiber over `p` via `Algebra.IsWeaklyEtale.baseChange`,
  followed by the field-case filtered-colimit characterization `weaklyEtale_over_field_tfae`.
-/

-- Proof sketch: base change the weakly étale map `A → B` along `A → κ(p)` using Lemma
-- `15.105.7`, so `κ(p) → B ⊗[A] κ(p)` is weakly étale. By Lemma `15.105.16`, the fiber algebra is
-- a filtered colimit of étale `κ(p)`-algebras. For a prime `q` over `p`, the residue field
-- `κ(q)` is the residue field of a prime of this fiber algebra, so Algebra Lemma `10.143.4`
-- yields algebraicity and separability over `κ(p)`.
/-- Lemma 15.105.17: if `A → B` is weakly étale, then for every prime `q` of `B` lying over a
prime `p` of `A`, the induced residue-field extension `κ(q) / κ(p)` is algebraic and separable. -/
theorem residueField_isAlgebraic_and_separable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.1.ResidueField := sorry

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is algebraic. -/
theorem residueField_isAlgebraic_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).1

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is separable. -/
theorem residueField_isSeparable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsSeparable p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).2

end
