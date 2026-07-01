import Mathlib
import stacks_project.Chap10.Definition_10_160_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {B : Type u} [CommRing B] [IsDomain B]

/- Domain-style sampling:
* primary domain: characteristic-`p` commutative algebra of domains, fraction fields, Kähler
  differentials, and absolute derivations;
* sampled owner declarations of the same kind:
  `Derivation`,
  `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `Derivation.localizationExtension`;
* best owner abstraction: this numbered item stays `source-facing`; the canonical owner for the
  output is `Derivation ℤ B B`, while the non-`p`th-power input is measured intrinsically in the
  fraction field `FractionRing B`;
* primitive data: the ambient characteristic-`p` domain `B`, the finite-type-over-some-complete-
  local-ring hypothesis, the element `f : B`, and the fraction-field non-`p`th-power hypothesis on
  `f`;
* derived API: the fraction-field differential obstruction from
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`, the existence of a fraction-field derivation
  not killing `f` via `KaehlerDifferential.linearMapEquivDerivation`, and the descent/clearing-
  denominators step yielding a derivation `B → B`.

Source/core/bridge triage:
* `source-facing`: `exists_derivation_with_nonzero_apply_of_not_exists_pth_root`;
* `core/canonical`: `Derivation ℤ B B`, `FractionRing B`, and the universal derivation
  `KaehlerDifferential.D`;
* `bridge/view`: the finite complete-local presentation supplied by `hB` and the fraction-field
  derivation construction/descent used in the proof sketch.
-/

-- Proof sketch: choose a Noetherian complete local ring `R` and a finite type map `R → B` from
-- the given existential hypothesis.
-- Replacing `R` by its image in `B` reduces to the case where `R` is a domain of characteristic
-- `p`. Cohen structure and the finite-type reduction from the source then replace `B` by a finite
-- extension of a mixed power-series/polynomial ring. Lemma `10.158.2` shows that the absolute
-- differential of `f` in `FractionRing B` is nonzero because `f` is not a `p`th power, and Lemma
-- `15.46.5` allows one to choose a derivation of the fraction field that does not kill `f`.
-- Clearing denominators yields the required derivation `B → B`.
/-- Lemma 15.48.5: if `B` is a domain of characteristic `p` which is of finite type over some
Noetherian complete local ring, and `f` is not a `p`th power in `FractionRing B`, then there
exists a derivation `D : B → B` with `D(f) ≠ 0`. -/
theorem exists_derivation_with_nonzero_apply_of_not_exists_pth_root
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hB :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B)
    (f : B)
    (hf : ¬ ∃ g : FractionRing B, g ^ p = algebraMap B (FractionRing B) f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := sorry

end
