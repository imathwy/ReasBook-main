import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Lemma_15_91_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for the completion pair, expressed through
  principal-power torsion and completion maps;
- sampled owner declarations:
  `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`,
  `Tor[R, p](M, N)`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `AdicCompletion.of`,
  `Submodule.torsionBy`,
  `isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair`,
  `AdicCompletion.of_injective_iff`,
  `LinearMap.injective_domRestrict_iff`;
- best owner abstraction: the canonical glueability owner
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`, with the principal-component
  comparison map `tensorBaseChangeUnitPrimaryComponent` specialized to
  `R' = principalAdicCompletion f`; the source-facing completion bridge is the restriction
  `fTorsionToAdicCompletion M f` of `AdicCompletion.of (principalIdeal f) M` to the
  canonical finite-stage torsion submodule `M[f^1]`.

Primitive-vs-derived split:
- primitive data: a commutative ring `R`, an `R`-module `M`, an element `f : R`, and in the
  completion case the owner map
  `tensorBaseChangeUnitPrimaryComponent (principalAdicCompletion f) (principalIdeal f) M`
  together with the canonical completion map `AdicCompletion.of (principalIdeal f) M`;
- derived API: the source-facing bridge maps to the full completion tensor product and to the
  module completion itself, together with the remark’s injectivity and Tor-vanishing criteria.

Layer triage:
- `source-facing`: the completion-valued criteria stated in Remark `15.91.11`;
- `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`,
  `principalAdicCompletion`, and
  `tensorBaseChangeUnitPrimaryComponent (principalAdicCompletion f) (principalIdeal f) M`;
- `bridge/view`: `completionFPowerTorsionToCompletionTensor` and
  `fTorsionToAdicCompletion`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']

/-- The map `M[f^∞] → M ⊗[R] R^∧` obtained by composing the Beauville-Laszlo torsion comparison
with the inclusion of `(M ⊗[R] R^∧)[f^∞]` into the full tensor product. -/
abbrev completionFPowerTorsionToCompletionTensor
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (M[f^∞] : Submodule R M) →ₗ[R] M ⊗[R] principalAdicCompletion f :=
  let A := principalAdicCompletion f
  let targetTorsion : Submodule R (A ⊗[R] M) :=
    ((Ideal.map (algebraMap R A) (principalIdeal f)).primaryComponent (A ⊗[R] M)).restrictScalars R
  let hsource : (principalIdeal f).primaryComponent M = (M[f^∞] : Submodule R M) :=
    Module.primaryComponent_principalIdeal_eq_fPowerTorsion f
  let η : (M[f^∞] : Submodule R M) →ₗ[R] targetTorsion :=
    (tensorBaseChangeUnitPrimaryComponent A (principalIdeal f) M).comp
      (LinearEquiv.ofEq _ _ hsource).symm.toLinearMap
  (TensorProduct.comm R A M).toLinearMap.comp <|
    targetTorsion.subtype.comp η

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The canonical map `M[f^1] → M^∧` to the `(f)`-adic completion of `M`, modeled as the
restriction of `AdicCompletion.of (principalIdeal f) M` to the canonical finite-stage
`f`-torsion submodule `M[f^1]`. -/
abbrev fTorsionToAdicCompletion (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (M[f^1] : Submodule R M) →ₗ[R] AdicCompletion (principalIdeal f) M :=
  (AdicCompletion.of (principalIdeal f) M).domRestrict (M[f^1] : Submodule R M)

/-- The source-facing completion-tensor map is injective exactly when the canonical Beauville-
Laszlo torsion comparison map into the completion-side `f^∞`-torsion submodule is injective. -/
theorem completionFPowerTorsionToCompletionTensor_injective_iff
    (f : R) :
    Function.Injective (completionFPowerTorsionToCompletionTensor M f) ↔
      Function.Injective
        (tensorBaseChangeUnitPrimaryComponent
          (principalAdicCompletion f)
          (principalIdeal f)
          M) := sorry

-- Proof sketch: specialize the completion-side Beauville-Laszlo criterion, then compose the
-- target with the inclusion of the completion-side `f^∞`-torsion submodule into the full tensor
-- product `M ⊗[R] R^∧`.
/-- Remark 15.91.11 (1): the module `M` is glueable along the completion map exactly when the
natural map `M[f^∞] → M ⊗[R] R^∧` is injective. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
    (f : R) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) := sorry

/-- A nonzero `f^∞`-torsion class mapping to zero in `M ⊗[R] R^∧` obstructs Beauville-Laszlo
glueability for the completion pair. -/
theorem not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    (f : R)
    {x : M[f^∞]} (hx_ne : x ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor M f x = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := by
  intro hshortExact
  have hinj :
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) :=
    (isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
      f).mp hshortExact
  have hx : x = 0 := by
    apply hinj
    simpa using hcompletion
  exact hx_ne hx

-- Proof sketch: by the previous clause, glueability along the completion map is implied by
-- injectivity of
-- `M[f^∞] → M ⊗[R] R^∧`. Injectivity on the smaller source `M[f^1]` gives a sufficient criterion
-- for that torsion map to be injective.
/-- Remark 15.91.11 (2): injectivity of `M[f^1] → M^∧` is a sufficient condition for `M` to be
glueable along the completion map. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_injective_fTorsionToAdicCompletion
    (f : R)
    (hinj : Function.Injective (fTorsionToAdicCompletion M f)) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := sorry

-- Proof sketch: `fTorsionToAdicCompletion M f` is the restriction of
-- `AdicCompletion.of (principalIdeal f) M` to `M[f^1]`. By
-- `LinearMap.injective_domRestrict_iff`, injectivity of this restricted map is equivalent to
-- `M[f^1] ∩ ker(AdicCompletion.of ...) = 0`, and `AdicCompletion.of_injective_iff` identifies that
-- kernel with the intersection of the principal powers in the source-facing separatedness
-- criterion.
/-- Remark 15.91.11 (3): the map `M[f^1] → M^∧` is injective if and only if the intersection
`M[f^1] ∩ ⋂_{n > 0} f^n M` is zero. -/
theorem fTorsionToAdicCompletion_injective_iff_torsion_inf_principalPowers_eq_bot
    (f : R)
    :
    Function.Injective (fTorsionToAdicCompletion M f) ↔
      (M[f^1] : Submodule R M) ⊓
          ⨅ n : ℕ+, principalPowerIdeal f (n : ℕ) • (⊤ : Submodule R M) =
        ⊥ := sorry

-- Proof sketch: apply Algebra Lemma `10.75.2` to the Beauville-Laszlo short exact sequence
-- `0 → R' → R'_f → C → 0`. Vanishing of `Tor₁^R(M, R'_f)` gives the needed injectivity in the
-- tensor sequence, and the glueing-pair hypothesis supplies the rest of the Beauville-Laszlo
-- exactness package.
/-- Remark 15.91.11 (4): if `(R → R', f)` is a Beauville-Laszlo glueing pair and
`Tor₁^R(M, R'_f) = 0`, then `M` is glueable for `(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_torOne_localizedTarget_isZero
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hTor :
      Limits.IsZero (Tor[R, 1](M, Localization.Away (algebraMap R R' f)))) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: localizing `Tor₁^R(M, R')` away from `f` identifies it with
-- `Tor₁^R(M, R'_f)`. Hence vanishing after localizing away from `f` is equivalent to saying that
-- every element of `Tor₁^R(M, R')` is killed by some power of `f`.
/-- Remark 15.91.11 (5): the vanishing of `Tor₁^R(M, R'_f)` is equivalent to saying that
`Tor₁^R(M, R')` is torsion for the powers of `f`. -/
theorem torOne_extension_isTorsion'_powers_iff_torOne_localizedTarget_isZero
    (f : R) :
    Module.IsTorsion'
        (Tor[R, 1](M, R'))
        (Submonoid.powers f) ↔
      Limits.IsZero (Tor[R, 1](M, Localization.Away (algebraMap R R' f))) := sorry

-- Proof sketch: flat modules have vanishing first Tor against every `R`-module. Apply the
-- previous criterion with `R'_f`.
/-- Remark 15.91.11 (6): every flat `R`-module is Beauville-Laszlo glueable for a glueing pair
`(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_flat_module
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R M] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: if `R → R'` is flat, then so is the localization `R'_f`, so
-- `Tor₁^R(M, R'_f)` vanishes for every `R`-module `M`. Apply clause `(4)`.
/-- Remark 15.91.11 (7): if `R → R'` is flat, then every `R`-module is Beauville-Laszlo glueable
for `(R → R', f)`. -/
theorem isBeauvilleLaszloGlueableAlong_of_flat_extension
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R R'] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

-- Proof sketch: Remark `15.91.8` gives the canonical Beauville-Laszlo glueing-pair owner for the
-- completion map over a Noetherian ring, and the adic-completion flatness instance supplies the
-- flat-extension hypothesis needed by clause `(7)`.
/-- Remark 15.91.11 (8): if `R` is Noetherian, then every `R`-module is glueable for the
completion pair `(R → R^∧, f)`. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_isNoetherianRing
    (f : R) [IsNoetherianRing R] :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := sorry

end
