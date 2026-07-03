import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for principal-power ideals.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `principalPowerIdeal`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Tor`,
  `IsZero`.
* owner abstraction: the canonical Tor object `Tor (ModuleCat R) 1` together with the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong`; the source-facing ideal owner is `principalPowerIdeal`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the positive integer `n`.
* derived API: the Tor-vanishing conclusion for the principal ideal `(f^n)`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and
  `principalPowerIdeal` and `IsZero` are `core/canonical`; the tensor-base-change argument from
  Lemma `15.89.9` is the supporting `bridge/view`.
-/

-- Proof sketch: tensor the short exact sequence
-- `0 → principalPowerIdeal f n → R → R ⧸ principalPowerIdeal f n → 0` with `R'`.
-- The needed exactness package is the Beauville-Laszlo glueing-pair owner
-- `IsBeauvilleLaszloGlueingPairAlong f`.
-- Under those hypotheses, the argument from the source reduces the vanishing of
-- `Tor_1^R(R', f^n R)` to injectivity on the `f^n`-torsion submodule after base change; Lemma
-- `15.89.9` identifies that base change with the original torsion submodule, and Lemma `15.91.6`
-- supplies the required injectivity for a glueing pair.
/-- Lemma 15.91.13: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every positive
integer `n` the first Tor group `Tor_1^R(R', f^n R)` vanishes. In Lean, `f^n R` is represented by
the chapter owner `principalPowerIdeal f n`, and vanishing is recorded by the canonical owner
`IsZero` of the Tor object. -/
theorem torOne_extension_principalPowIdeal_isZero_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (n : ℕ+) :
    IsZero (Tor[R, 1](R', principalPowerIdeal f (n : ℕ))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end
