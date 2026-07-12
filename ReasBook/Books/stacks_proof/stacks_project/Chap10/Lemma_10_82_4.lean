import Mathlib
import StacksProject_2024.Chap10.Example_10_82_2
import StacksProject_2024.Chap10.Theorem_10_82_3

universe u

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.FinitePresentation R S.X₃]

/- Domain-style sampling:
- primary domain: universally exact short exact sequences of modules and their splitting criteria;
- sampled owner declarations of the same kind:
  `CategoryTheory.ShortComplex.UniversallyExact`,
  `CategoryTheory.ShortComplex.Splitting`,
  `CategoryTheory.ShortComplex.Splitting.ofExactOfSection`,
  `CategoryTheory.ShortComplex.Splitting.universallyExact`;
- best owner abstraction: the core owners are `S.UniversallyExact` and `S.Splitting`, while the
  finite-presentation hypothesis on `S.X₃` is auxiliary input used to bridge between them through
  the Chapter 10 TFAE criterion;
- primitive data: the short complex `S`, the universal exactness predicate, and the canonical
  splitting owner `S.Splitting`;
- derived API: the `Hom`-surjectivity criterion on finitely presented modules supplied by
  `universallyExact_tfae`.

Layering:
- this numbered item is `bridge/view`: it does not introduce a new owner notion, but refines the
  source statement to the canonical owners `S.UniversallyExact` and `S.Splitting`.
-/

-- Proof sketch: a splitting makes the sequence universally exact because tensoring preserves split
-- exact sequences. Conversely, `S.UniversallyExact` already contains short exactness; under finite
-- presentation of `S.X₃`, universal injectivity of the first map yields the `Hom`-lifting
-- criterion against `S.X₃`. Applying it to `𝟙 S.X₃` produces a section of `S.g`, and a section of
-- the quotient map of a short exact sequence gives a splitting.
/-- Lemma 10.82.4: for a short exact sequence of `R`-modules whose cokernel `S.X₃` is finitely
presented, universal exactness is equivalent to the sequence being split. -/
@[stacks 058L]
theorem universallyExact_iff_split_of_finitePresentation_X₃ :
    S.UniversallyExact ↔ Nonempty S.Splitting := by
  constructor
  · intro hU
    have hS : S.ShortExact := hU.shortExact
    have hsurj : HomSurjectiveOnFinitelyPresented S :=
      ((universallyExact_tfae hS).out 0 4).mp hU
    obtain ⟨s, hs⟩ := hsurj S.X₃ (𝟙 S.X₃)
    exact ⟨Splitting.ofExactOfSection S hS.exact s hs hS.mono_f⟩
  · rintro ⟨s⟩
    exact s.universallyExact

end

end CategoryTheory.ShortComplex
