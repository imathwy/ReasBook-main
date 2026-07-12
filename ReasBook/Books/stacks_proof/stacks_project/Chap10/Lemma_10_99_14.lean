import StacksProject_2024.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion
import StacksProject_2024.Chap10.Lemma_10_39_18
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits IsLocalRing
open LocalizedModule
open scoped TensorProduct

universe u

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S R' S' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable [IsLocalRing R'] [IsLocalRing S']
variable [IsNoetherianRing R'] [IsNoetherianRing S']
variable (W : Submonoid (S ⊗[R] R'))
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S'] [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalization W S']
variable [IsLocalHom (algebraMap R' S')]

variable {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module.Finite S M]

local notation "M'" => S' ⊗[S] M

/- Domain-style sampling:
- primary domain: local flatness criteria under localized tensor-product base change in
  commutative algebra;
- sampled owner declarations of the same kind:
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Tor₁[R](M, N)`,
  `Module.Flat`,
  `flat_tensorProduct_of_flat_of_isLocalization_tensorProduct`;
- best owner abstraction: the flatness owner is `Module.Flat`, and the homological input should use
  the chapter owner notation `Tor₁[R'](M', R' ⧸ I')` rather than a raw derived-functor term;
- primitive data: the local Noetherian target map `R' → S'`, the ideal `I` of `R` together with
  properness of its image `I' = Ideal.map (algebraMap R R') I`, the finite `S`-module `M`, and
  the localization presentation of `S'` over `S ⊗[R] R'`;
- derived API: flatness of `M' = S' ⊗[S] M` over `R'`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.14 itself;
- `core/canonical`: `Module.Flat` together with the chapter owner notation `Tor₁`;
- `bridge/view`: localization/base-change transport of quotient flatness to the square over
  `R' → S'`, followed by the canonical variant local criterion `10.99.10`; the source-side
  local/Noetherian square belongs only to one proof route and is not primitive public data here.
-/

-- Proof sketch: because `S'` is a localization of `S ⊗[R] R'`, the module
-- `M'` is a localization of the ordinary base change `R' ⊗[R] M`. The hypothesis
-- that `M / IM` is flat over `R / I` localizes to flatness of `M' / I'M'` over `R' / I'`.
-- Applying the variant local criterion for flatness over the local map `R' → S'`, it remains to
-- use the assumed vanishing of `Tor₁^{R'}(M', R' / I')`.
omit [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.99.14: base changing the flat quotient `M / IM` from `R / I` to
`R' / I'` identifies the result with the quotient of `R' ⊗[R] M` by `I'`. -/
lemma flat_base_changed_quotient_of_flat_mod_ideal
    (I : Ideal R)
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat (R' ⧸ Ideal.map (algebraMap R R') I)
      ((R' ⊗[R] M) ⧸
        ((Ideal.map (algebraMap R R') I) •
          (⊤ : Submodule R' (R' ⊗[R] M)))) := by
  let A : Type u := R ⧸ I
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A' : Type u := R' ⧸ I'
  letI : CommRing A := inferInstance
  letI : CommRing A' := inferInstance
  letI : Algebra R A := Ideal.Quotient.algebra _
  letI : Algebra R' A' := Ideal.Quotient.algebra _
  letI : Algebra A A' := Ideal.Quotient.algebraQuotientOfLEComap
    (show I ≤ Ideal.comap (algebraMap R R') I' from Ideal.le_comap_map)
  letI : IsScalarTower R A A' := by infer_instance
  let e₁ : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[A] A ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M I).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₂ : A' ⊗[A] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[A'] A' ⊗[A] (A ⊗[R] M) :=
    LinearEquiv.baseChange A A'
      (M ⧸ (I • ⊤ : Submodule R M)) (A ⊗[R] M) e₁
  let e₃ : A' ⊗[A] (A ⊗[R] M) ≃ₗ[A'] A' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' M
  let e₄ : A' ⊗[R] M ≃ₗ[A'] A' ⊗[R'] (R' ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' A' A' M).symm
  let e₅ : A' ⊗[R'] (R' ⊗[R] M) ≃ₗ[A']
      ((R' ⊗[R] M) ⧸ (I' • (⊤ : Submodule R' (R' ⊗[R] M)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (R' ⊗[R] M) I').extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) := hflat
  have hbase :
      Module.Flat A' (A' ⊗[A] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Module.Flat.baseChange (R := A) (S := A') (M := M ⧸ (I • ⊤ : Submodule R M))
  letI : Module.Flat A' (A' ⊗[A] (M ⧸ (I • ⊤ : Submodule R M))) := hbase
  -- Proof comment: rewrite the base-changed quotient step-by-step into the textbook model
  -- `((R' ⊗[R] M) / I'M)`.
  exact Module.Flat.of_linearEquiv (e₂.trans (e₃.trans (e₄.trans e₅))).symm

/-- Helper for Lemma 10.99.14: the public tensor module `S' ⊗[S] M` is the localization of the
pushout module `((S ⊗[R] R') ⊗[S] M)` at `W`. -/
noncomputable def tensor_localizedModule_equiv :
    M' ≃ₗ[R'] LocalizedModule W ((S ⊗[R] R') ⊗[S] M) := by
  let e :
      S' ⊗[S ⊗[R] R'] ((S ⊗[R] R') ⊗[S] M) ≃ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⊗[R] R') S' S' M).restrictScalars
      (S ⊗[R] R')
  let f :
      ((S ⊗[R] R') ⊗[S] M) →ₗ[S ⊗[R] R'] S' ⊗[S] M :=
    e.toLinearMap.comp (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1)
  letI : IsLocalizedModule W f := by
    letI :
        IsLocalizedModule W
          (TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) :=
      inferInstance
    exact IsLocalizedModule.of_linearEquiv (S := W)
      (f := TensorProduct.mk (S ⊗[R] R') S' ((S ⊗[R] R') ⊗[S] M) 1) e
  -- Proof comment: package the source identity `S' ⊗[S] M = W⁻¹((S ⊗[R] R') ⊗[S] M)` as a
  -- reusable linear equivalence over `R'`.
  exact
    (IsLocalizedModule.linearEquiv W f
      (LocalizedModule.mkLinearMap W ((S ⊗[R] R') ⊗[S] M))).restrictScalars R'

omit [IsLocalRing R'] [IsNoetherianRing R'] [Module R M] [IsScalarTower R S M]
  [Module.Finite S M] in
/-- Helper for Lemma 10.99.14: the pushout quotient by the image of `I'` matches the ordinary
base-changed quotient after applying the canonical `cancelBaseChange` comparison. -/
lemma pushout_ideal_smul_top_restrictScalars
    (I : Ideal R) :
    let I' : Ideal R' := Ideal.map (algebraMap R R') I
    let A : Type u := S ⊗[R] R'
    let P : Type u := A ⊗[S] M
    let J : Ideal A := Ideal.map (algebraMap R' A) I'
    Submodule.restrictScalars R' (J • (⊤ : Submodule A P)) =
      (I' • (⊤ : Submodule R' P)) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  -- Proof comment: the `R'`-ideal action on the pushout module is exactly the restricted
  -- `A`-ideal action through the mapped ideal `J`.
  simpa [I', J] using
    (Ideal.smul_restrictScalars
      (R := R') (S := A) (M := P) I' (⊤ : Submodule A P))

omit [IsLocalRing R'] [IsNoetherianRing R'] [Module.Finite S M] in
/-- Helper for Lemma 10.99.14: after rewriting the pushout denominator as an `R'`-ideal multiple,
`cancelBaseChange` sends it to the denominator on `R' ⊗[R] M`. -/
lemma pushout_cancelBaseChange_maps_denominator
    (I : Ideal R) :
    let I' : Ideal R' := Ideal.map (algebraMap R R') I
    let A : Type u := S ⊗[R] R'
    let P : Type u := A ⊗[S] M
    let J : Ideal A := Ideal.map (algebraMap R' A) I'
    let eBase : P ≃ₗ[R'] R' ⊗[R] M := Algebra.IsPushout.cancelBaseChange R R' S A M
    (Submodule.restrictScalars R' (J • (⊤ : Submodule A P))).map eBase.toLinearMap =
      I' • (⊤ : Submodule R' (R' ⊗[R] M)) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  let eBase : P ≃ₗ[R'] R' ⊗[R] M := Algebra.IsPushout.cancelBaseChange R R' S A M
  -- Proof comment: first rewrite the source denominator via the restricted-scalar identity, then
  -- use surjectivity of `cancelBaseChange` to simplify the image of `I' • ⊤`.
  have hden :
      Submodule.restrictScalars R' (J • (⊤ : Submodule A P)) =
        (I' • (⊤ : Submodule R' P)) :=
    pushout_ideal_smul_top_restrictScalars (I := I)
  have hmap :=
    congrArg (fun K : Submodule R' P => K.map eBase.toLinearMap) hden
  simpa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.2 eBase.surjective] using hmap

omit [IsLocalRing R'] [IsNoetherianRing R'] [Module.Finite S M] in
/-- Helper for Chap10 Lemma 10 99 14: `cancelBaseChange` sends the `I'`-multiple of the
pushout module to the `I'`-multiple of the ordinary base-changed module. -/
lemma cancelBaseChange_maps_baseIdeal_smul_top
    (I : Ideal R) :
    let I' : Ideal R' := Ideal.map (algebraMap R R') I
    let A : Type u := S ⊗[R] R'
    let P : Type u := A ⊗[S] M
    let eBase : P ≃ₗ[R'] R' ⊗[R] M := Algebra.IsPushout.cancelBaseChange R R' S A M
    (I' • (⊤ : Submodule R' P)).map eBase.toLinearMap =
      I' • (⊤ : Submodule R' (R' ⊗[R] M)) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let eBase : P ≃ₗ[R'] R' ⊗[R] M := Algebra.IsPushout.cancelBaseChange R R' S A M
  -- Proof comment: the image of `I' • ⊤` is `I' • range(eBase)`, and the comparison
  -- equivalence is surjective.
  simpa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.2 eBase.surjective]

/-- Helper for Lemma 10.99.14: the pushout quotient by the image of `I'` matches the ordinary
base-changed quotient after applying the canonical `cancelBaseChange` comparison. -/
instance pushout_quotient_module_over_base_ideal_quotient
    (I : Ideal R) :
    Module (R' ⧸ Ideal.map (algebraMap R R') I)
      (((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R' (S ⊗[R] R')) (Ideal.map (algebraMap R R') I)) •
          (⊤ : Submodule (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)))) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  let T : Type u := A ⧸ J
  letI : Algebra (R' ⧸ I') T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R') (A := A) (p := I') (P := J) Ideal.le_comap_map
  exact Module.compHom _ (algebraMap (R' ⧸ I') T)

/-- Helper for Chap10 Lemma 10 99 14: the pushout quotient scalar action through `R' ⧸ I'`
is compatible with the original `R'`-action. -/
instance pushout_quotient_isScalarTower_over_base_ideal_quotient
    (I : Ideal R) :
    IsScalarTower R' (R' ⧸ Ideal.map (algebraMap R R') I)
      (((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R' (S ⊗[R] R')) (Ideal.map (algebraMap R R') I)) •
          (⊤ : Submodule (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)))) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  let T : Type u := A ⧸ J
  letI : Algebra (R' ⧸ I') T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R') (A := A) (p := I') (P := J) Ideal.le_comap_map
  -- Proof comment: the quotient module is a module over `A / J`, and the `R' / I'`-action is
  -- obtained by composing the quotient algebra map.
  change IsScalarTower R' (R' ⧸ I') (P ⧸ (J • (⊤ : Submodule A P)))
  exact IsScalarTower.of_compHom R' (R' ⧸ I') (P ⧸ (J • (⊤ : Submodule A P)))

/-- Helper for Lemma 10.99.14: the pushout quotient by the image of `I'` matches the ordinary
base-changed quotient after applying the canonical `cancelBaseChange` comparison. -/
noncomputable def pushout_quotient_linear_equiv_over_quotient
    (I : Ideal R) :
    ((((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R R') I) •
          (⊤ : Submodule R' ((S ⊗[R] R') ⊗[S] M)))) ≃ₗ[
          R' ⧸ Ideal.map (algebraMap R R') I]
      ((R' ⊗[R] M) ⧸
          ((Ideal.map (algebraMap R R') I) •
          (⊤ : Submodule R' (R' ⊗[R] M))))) :=
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let eBase : P ≃ₗ[R'] R' ⊗[R] M := Algebra.IsPushout.cancelBaseChange R R' S A M
  let eR :
      (P ⧸ (I' • (⊤ : Submodule R' P))) ≃ₗ[R']
        ((R' ⊗[R] M) ⧸ (I' • (⊤ : Submodule R' (R' ⊗[R] M)))) :=
    Submodule.Quotient.equiv _ _ eBase (cancelBaseChange_maps_baseIdeal_smul_top (I := I))
  eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

omit [IsLocalRing R'] [IsNoetherianRing R'] [Module.Finite S M] in
/-- Helper for Lemma 10.99.14: after restricting scalars from the pushout ring to `R'`, the
pushout quotient by the image of `I'` is flat over `R' ⧸ I'` once `M / IM` is flat over `R / I`.
-/
lemma flat_pushout_quotient_of_flat_mod_ideal
    (I : Ideal R)
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat (R' ⧸ Ideal.map (algebraMap R R') I)
      (((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R' (S ⊗[R] R')) (Ideal.map (algebraMap R R') I)) •
          (⊤ : Submodule (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)))) := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  -- Proof comment: first move the flat base-changed quotient to the restricted-scalar pushout
  -- quotient, then change only the owner of the same denominator.
  have hbase :
      Module.Flat (R' ⧸ I')
        ((R' ⊗[R] M) ⧸ (I' • (⊤ : Submodule R' (R' ⊗[R] M)))) :=
    flat_base_changed_quotient_of_flat_mod_ideal (R' := R') (I := I) hflat
  have hrestricted :
      Module.Flat (R' ⧸ I')
        (P ⧸ (I' • (⊤ : Submodule R' P))) := by
    letI :
        Module.Flat (R' ⧸ I')
          ((R' ⊗[R] M) ⧸ (I' • (⊤ : Submodule R' (R' ⊗[R] M)))) := hbase
    exact Module.Flat.of_linearEquiv (pushout_quotient_linear_equiv_over_quotient (I := I))
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  let eDenom :
      (P ⧸ (I' • (⊤ : Submodule R' P))) ≃ₗ[R']
        (P ⧸ ((J • (⊤ : Submodule A P)).restrictScalars R')) :=
    Submodule.quotEquivOfEq _ _ (pushout_ideal_smul_top_restrictScalars (I := I)).symm
  let eRestrict :
      (P ⧸ ((J • (⊤ : Submodule A P)).restrictScalars R')) ≃ₗ[R']
        (P ⧸ (J • (⊤ : Submodule A P))) :=
    Submodule.Quotient.restrictScalarsEquiv R' (J • (⊤ : Submodule A P))
  let eOwner :
      (P ⧸ (I' • (⊤ : Submodule R' P))) ≃ₗ[R' ⧸ I']
        (P ⧸ (J • (⊤ : Submodule A P))) :=
    (eDenom.trans eRestrict).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  letI : Module.Flat (R' ⧸ I') (P ⧸ (I' • (⊤ : Submodule R' P))) := hrestricted
  exact Module.Flat.of_linearEquiv eOwner.symm

/-- Helper for Lemma 10.99.14: the restricted-scalar pushout quotient is the same quotient viewed
over the genuine pushout ring. -/
noncomputable def pushout_quotient_owner_transport_over_ideal_quotient
    (I : Ideal R) :
    (((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R R') I) •
          (⊤ : Submodule R' ((S ⊗[R] R') ⊗[S] M)))) ≃ₗ[
        R' ⧸ Ideal.map (algebraMap R R') I]
    (((S ⊗[R] R') ⊗[S] M) ⧸
        ((Ideal.map (algebraMap R' (S ⊗[R] R')) (Ideal.map (algebraMap R R') I)) •
          (⊤ : Submodule (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)))) :=
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let P : Type u := A ⊗[S] M
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  let eDenom :
      (P ⧸ (I' • (⊤ : Submodule R' P))) ≃ₗ[R']
        (P ⧸ ((J • (⊤ : Submodule A P)).restrictScalars R')) :=
    Submodule.quotEquivOfEq _ _ (pushout_ideal_smul_top_restrictScalars (I := I)).symm
  let eRestrict :
      (P ⧸ ((J • (⊤ : Submodule A P)).restrictScalars R')) ≃ₗ[R']
        (P ⧸ (J • (⊤ : Submodule A P))) :=
    Submodule.Quotient.restrictScalarsEquiv R' (J • (⊤ : Submodule A P))
  (eDenom.trans eRestrict).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

omit [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.99.14: after localizing the pushout ring, the image of the ideal generated
from `I'` agrees with the direct image of `I'` itself. -/
lemma localized_pushout_mapped_ideal_eq
    (I : Ideal R) :
    let I' : Ideal R' := Ideal.map (algebraMap R R') I
    let A : Type u := S ⊗[R] R'
    let J : Ideal A := Ideal.map (algebraMap R' A) I'
    Ideal.map (algebraMap A (Localization W)) J =
      Ideal.map (algebraMap R' (Localization W)) I' := by
  let I' : Ideal R' := Ideal.map (algebraMap R R') I
  let A : Type u := S ⊗[R] R'
  let J : Ideal A := Ideal.map (algebraMap R' A) I'
  -- Proof comment: the two ideal maps differ only by the parenthesization of the same composite
  -- ring map `R' → S ⊗[R] R' → W⁻¹(S ⊗[R] R')`.
  simpa [J] using
    (Ideal.map_map (I := I') (f := algebraMap R' A) (g := algebraMap A (Localization W)))

/-- Helper for Chap10 Lemma 10 99 14: flatness of the pushout quotient transports through the
localization presentation `S' = W⁻¹(S ⊗[R] R')` to the target quotient by `I'`. -/
lemma flat_target_quotient_of_flat_pushout_quotient
    (I : Ideal R)
    (hpush :
      Module.Flat (R' ⧸ Ideal.map (algebraMap R R') I)
        (((S ⊗[R] R') ⊗[S] M) ⧸
          ((Ideal.map (algebraMap R' (S ⊗[R] R')) (Ideal.map (algebraMap R R') I)) •
            (⊤ : Submodule (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M))))) :
    Module.Flat (R' ⧸ Ideal.map (algebraMap R R') I)
      (M' ⧸ ((Ideal.map (algebraMap R R') I) • (⊤ : Submodule R' M'))) := by
  -- TODO: construct the quotient-localization linear equivalence from
  -- `M' ⧸ I'M'` to the localization of the pushout quotient, using
  -- `tensor_localizedModule_equiv`, `localizedQuotientEquiv`, and
  -- `localized_pushout_mapped_ideal_eq`; then transport `hpush` through localization.
  sorry

/-- Helper for Lemma 10.99.14: the remaining flatness input is the quotient module
`(S' ⊗[S] M) / I'M'`. -/
lemma flat_target_quotient_of_flat_mod_ideal
    (I : Ideal R)
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
      Module.Flat (R' ⧸ Ideal.map (algebraMap R R') I)
      (M' ⧸ ((Ideal.map (algebraMap R R') I) • (⊤ : Submodule R' M'))) := by
  -- Proof comment: the remaining source step is isolated in
  -- `flat_target_quotient_of_flat_pushout_quotient`; all algebraic pushout quotient flatness has
  -- already been proved above.
  exact flat_target_quotient_of_flat_pushout_quotient I
    (flat_pushout_quotient_of_flat_mod_ideal I hflat)

/-- Lemma 10.99.14: in a commutative square of local homomorphisms of local Noetherian rings, let
`I` be an ideal of `R` such that `I' = Ideal.map (algebraMap R R') I` is proper, and let `M` be
a finite `S`-module. Put `M' = S' ⊗[S] M`. If `R' → S'` is a local homomorphism of Noetherian
local rings, if `S'` is a localization of `S ⊗[R] R'`, if `M / IM` is flat over `R / I`, and if
`Tor₁^{R'}(M', R' / I')` vanishes, then `M'` is flat over `R'`. -/
@[stacks 00MO]
theorem flat_tensorProduct_of_flat_mod_ideal_and_tor_one_quotient_vanishing_of_isLocalization_tensorProduct
    (I : Ideal R) (hI : Ideal.map (algebraMap R R') I ≠ ⊤)
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hTor :
      IsZero (Tor₁[R'](M', R' ⧸ Ideal.map (algebraMap R R') I))) :
    Module.Flat R' M' := by
  letI : Module.Finite S' M' :=
    Module.Finite.base_change (R := S) (A := S') (M := M)
  apply
    flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
      (R := R') (S := S') (M := M')
  · exact hI
  · simpa using hTor
  · -- Proof comment: the textbook quotient-flatness step is isolated in the helper above so the
    -- final criterion application stays flat and source-faithful.
    exact flat_target_quotient_of_flat_mod_ideal I hflat

end
