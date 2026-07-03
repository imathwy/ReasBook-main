import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import stacks_project.Chap15.Definition_15_61_1
import stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the cokernel of
  `M → M_f`.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `LocalizedModule.mkLinearMap`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `Tor`.
* owner abstraction: the source-facing quotient owner is the canonical module quotient
  `LocalizedModule.Away f M ⧸ range(M → M_f)`, while the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` supplies the Beauville-Laszlo
  hypotheses and the chapter owner notation `Tor[R, 1](R', -)` exposes the ambient canonical Tor
  object `Tor (ModuleCat R) 1`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the explicit `R`-module `M`.
* derived API: the Tor-vanishing conclusion for the canonical quotient `M_f / M`.
* triage: the quotient `LocalizedModule.Away f M ⧸ range(M → M_f)` is `source-facing`;
  `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and `IsZero` are `core/canonical`; and
  `ModuleCat.cokernelIsoRangeQuotient` is the supporting `bridge/view` identifying the
  categorical cokernel with the quotient model.
-/
-- Proof sketch: rewrite the categorical cokernel of `M → M_f` as the source-facing quotient
-- `M_f / M` via `ModuleCat.cokernelIsoRangeQuotient`, then replace that quotient by the filtered
-- colimit of the quotients `M / f^n M` after killing `f`-power torsion. Lemma `15.91.14` handles
-- the cyclic torsion case, and Lemma `15.89.9` identifies the relevant base changes needed to
-- descend from a free `R / R[f^∞]`-presentation to a general module.
/-- Lemma 15.91.15: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every
`R`-module `M` the first Tor group `Tor_1^R(R', \operatorname{Coker}(M → M_f))` vanishes. Lean
states this directly for the canonical quotient
`LocalizedModule.Away f M ⧸ range(M → M_f)`, with `ModuleCat.cokernelIsoRangeQuotient`
remaining only as the internal bridge from the categorical cokernel, and records the vanishing by
the canonical owner `IsZero` of the chapter Tor notation `Tor[R, 1](R', -)`. -/
theorem torOne_extension_cokernel_toLocalizationAway_isZero_of_glueingPair
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R',
      LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  sorry

end
