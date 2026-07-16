import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Etale
import stacks_proof.stacks_project.Chap10.Lemma_10_112_1
import stacks_proof.stacks_project.Chap10.Lemma_10_125_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Algebra.HasGoingDown

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.Etale A B]

/- Domain-style sampling for Lemma 15.44.2:
- primary domain: local commutative algebra of étale maps, prime localizations, and Krull
  dimension;
- sampled owner declarations of the same kind:
  `ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing`,
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`;
- owner abstraction: the canonical local rings
  `Localization.AtPrime (q.under A)` and `Localization.AtPrime q`, together with the Chapter 10
  owner inequalities comparing their Krull dimensions;
- primitive data: the étale algebra `A → B` and the prime `q` of `B`;
- derived API: faithful flatness of the induced local map, surjectivity/generalization lifting on
  spectra, and quasi-finiteness at `q`.

Layer triage:
- `source-facing`: equality of the Krull dimensions of the localizations at `q ∩ A` and `q`;
- `core/canonical`: the Chapter 10 owner inequalities on the canonical localizations;
- `bridge/view`: this file specializes those owner inequalities to the étale situation and
  packages them as the textbook equality statement.
-/

-- Proof sketch: this is the specialization of the chapter-10 owner theorems to the étale case.
-- Since an étale algebra is flat, the local map `A_(q ∩ A) → B_q` is flat; because it is also a
-- local map of local rings, it is faithfully flat. Thus `Spec(B_q) → Spec(A_(q ∩ A))` is
-- surjective, and flatness gives going down, so Lemma `10.112.1` yields
-- `dim(A_(q ∩ A)) ≤ dim(B_q)`. Since an étale algebra is quasi-finite at every prime, Lemma
-- `10.125.4` gives the reverse inequality `dim(B_q) ≤ dim(A_(q ∩ A))`.
/-- Lemma 15.44.2: if `A → B` is an étale ring map and `q` is a prime ideal of `B`, then the
local rings `A_(q ∩ A)` and `B_q` have the same Krull dimension. -/
@[stacks 07QP]
theorem ringKrullDim_localizationAtPrime_eq_of_etale (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under A)) = ringKrullDim (Localization.AtPrime q) := by
  have hAB :
      ringKrullDim (Localization.AtPrime (q.under A)) ≤
        ringKrullDim (Localization.AtPrime q) := by
    letI :
        Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using
      ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
        (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (.inr <| iff_generalizingMap_primeSpectrumComap.mp inferInstance)
  have hBA :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under A)) := by
    simpa using ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  exact le_antisymm hAB hBA

end
