import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import stacks_project.Chap15.Definition_15_61_1
import stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped IdealPowerTorsion

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the quotient by `f^∞`-torsion.
* sampled owner declarations:
  `Ideal.primaryComponent`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `Tor`,
  `IsZero`.
* owner abstraction: the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` for the exact
  Beauville-Laszlo hypotheses, together with the canonical torsion owner `R[f^∞]`; the Tor
  bifunctor `Tor (ModuleCat R) 1` is the ambient canonical owner.
* primitive data: the algebra map `R → R'` and the element `f : R`.
* derived API: the vanishing statement for `Tor₁^R(R', R / R[f^∞])`, recorded by the canonical
  zero-object interface `IsZero`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `R[f^∞]`, and
  `Tor` and `IsZero` are `core/canonical`.
-/

-- Proof sketch: write `R / R[f^∞]` as the filtered colimit of the quotients `R / R[f^n]`, or
-- equivalently of the principal ideals `(f^n)`. The functor `Tor_1^R(R', -)` commutes with filtered
-- colimits, so the previous lemma reduces the claim to the vanishing of
-- `Tor_1^R(R', (f^n))` for each positive integer `n`.
/-- Lemma 15.91.14: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the first Tor group
`Tor_1^R(R', R / R[f^\infty])` vanishes. Lean records this vanishing with the canonical owner
`IsZero` of the Tor object, with `R[f^\infty]` represented by the chapter notation for the
principal-ideal primary component. -/
theorem torOne_extension_quotientByFPowerTorsion_isZero_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R', R ⧸ (R[f^∞] : Submodule R R))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end
