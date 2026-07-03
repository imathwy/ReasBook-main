import Mathlib
import StacksProject_2024.Chap10.Definition_10_60_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {Λ : Type u} [CommRing Λ]
variable (q : PrimeSpectrum Λ)

local notation "Λq" => Localization.AtPrime q.asIdeal

/- Domain-style sampling pass.

Primary domains:
* regular local rings and regular systems of parameters in localizations;
* finite-family prefix ideals and quotient-element annihilator/torsion ideals in commutative
  algebra.

Sampled owner declarations:
* `IsLocalRing.parameterIdeal`;
* `IsLocalRing.IsRegularSystemOfParameters`;
* `isRegularLocalRing_iff_exists_regularSystemOfParameters`;
* `exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing`;
* `Ideal.torsionOf`;
* `Submodule.annihilator_span_singleton`.

Owner abstractions:
* the regular-system owner `IsRegularSystemOfParameters` in the local ring
  `Λq`;
* the successive quotient ideals are expressed directly by `Ideal.span` of the earlier `e`-th
  powers of the lifted family, rather than by a parallel local owner;
* the element-annihilator owner `Ideal.torsionOf` for quotient elements.

Primitive data: a chosen family in the maximal ideal of the localization.

Derived API: a lift of that family to `Λ`, the `n`-th-power containment in `I`, and the
successive quotient annihilator equalities for the lifted family.

Source/core/bridge triage:
* source-facing: the lifted elements `π₁, …, π_d ∈ Λ` with their power and annihilator
  conditions;
* core/canonical: `IsLocalRing.IsRegularSystemOfParameters` on
  `Λq`, together with direct `Ideal.span` expressions for the successive quotient ideals and
  `Ideal.torsionOf` for the quotient-element annihilator ideals;
* bridge/view: the equality identifying the localized images of the lifted family with the chosen
  regular system of parameters.
-/

-- Proof sketch: choose `d` generators of the maximal ideal of the regular local ring
-- `Λq`, clear denominators so that their `n`-th powers lie in `I`,
-- and then inductively multiply later generators by elements outside `q` using Ogoma's lemma so
-- that the annihilator equality holds in each successive quotient.
/-- Lemma 16.10.2: let `Λ` be a Noetherian ring, let `I ⊆ q` be an ideal contained in a prime
`q`, and let `n`, `e`, `d` be integers with `0 < e`. Assume that `q^n` becomes contained in `I`
after localizing at `q`, and that `Λq` is a regular local ring of dimension `d`. Then there are
elements `π₁, …, π_d` of `Λ` whose localized images form a regular system of parameters of `Λ_q`,
whose `n`-th powers lie in `I`, and whose images in each successive quotient by the earlier
`e`-th powers have the same annihilator as the squares of those images. -/
theorem exists_parameters_generating_localized_prime_pow_mem_ideal_and_annihilator_stable
    (I : Ideal Λ) (n e d : ℕ)
    (he : 0 < e) (hIq : I ≤ q.asIdeal)
    (hqpow : Ideal.map (algebraMap Λ Λq) (q.asIdeal ^ n) ≤ Ideal.map (algebraMap Λ Λq) I)
    [IsNoetherianRing Λ]
    [IsRegularLocalRing Λq]
    (hdim : ringKrullDim Λq = d) :
    ∃ (π : Fin d → Λ) (x : Fin d → maximalIdeal Λq),
      IsRegularSystemOfParameters x ∧
        (∀ i, (x i : Λq) = algebraMap Λ Λq (π i)) ∧
        (∀ i, (π i) ^ n ∈ I) ∧
        ∀ i : Fin d,
          let J : Ideal Λ := Ideal.span (Set.range fun j : Fin i.1 ↦ π (Fin.castLE
            (Nat.le_of_lt i.isLt) j) ^ e)
          Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J (π i)) =
            Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J ((π i) ^ 2)) := sorry

end
