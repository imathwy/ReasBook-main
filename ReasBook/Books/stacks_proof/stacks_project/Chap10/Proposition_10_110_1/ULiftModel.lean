import stacks_proof.stacks_project.Chap10.Proposition_10_110_1.SameUniverseProjective
import stacks_proof.stacks_project.Chap10.Proposition_10_110_1.SurjectiveDepth

universe u v

open CategoryTheory ChainComplex
open scoped ENat

section

variable {R : Type u} [CommRing R]

/-- Helper for Proposition 10.110.1: the common-universe `ULift` ring model preserves Krull
dimension. -/
lemma ringKrullDim_eq_of_ulift_ring_model :
    ringKrullDim (ULift.{v} R) = ringKrullDim R := by
  -- `ULift.ringEquiv` identifies the lifted ring with the original ring.
  simpa using ringKrullDim_eq_of_ringEquiv (ULift.ringEquiv : ULift.{v} R ≃+* R)

/-- Helper for Proposition 10.110.1: regular-locality survives passage to the common-universe
`ULift` ring model. -/
lemma isRegularLocalRing_of_ulift_ring_model [IsRegularLocalRing R] :
    IsRegularLocalRing (ULift.{v} R) := by
  -- The lifted ring is ring-equivalent to `R`, so the regular-local owner transports directly.
  exact IsRegularLocalRing.of_ringEquiv (R := R) (ULift.ringEquiv : ULift.{v} R ≃+* R).symm

/-- Helper for Proposition 10.110.1: the canonical algebra map from the lifted ring back to `R`
is surjective. -/
lemma algebraMap_surjective_of_ulift_ring_model :
    letI : Algebra (ULift.{v} R) R :=
      (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom.toAlgebra
    Function.Surjective (algebraMap (ULift.{v} R) R) := by
  letI : Algebra (ULift.{v} R) R :=
    (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom.toAlgebra
  -- `ULift.ringEquiv` identifies the lifted ring with `R`, so the algebra map is just that
  -- surjective ring equivalence in map form.
  simpa using (ULift.ringEquiv : ULift.{v} R ≃+* R).surjective

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.110.1: the default `ULift` scalar action on `M` lies in a scalar
tower over the original `R`-action. -/
lemma ulift_ring_module_isScalarTower :
    IsScalarTower (ULift.{v} R) R M := by
  -- The `ULift` action is defined by `ULift.down`, so the scalar-tower law is inherited
  -- directly from the original `R`-module structure on `M`.
  infer_instance

variable [IsRegularLocalRing R] [Module.Finite R M]

/-- Helper for Proposition 10.110.1: viewing `M` as a module over `ULift R` via the canonical
ring equivalence does not change its depth. -/
lemma moduleDepth_eq_of_ulift_ring_restrictScalars
    [IsLocalRing (ULift.{v} R)]
    [Module.Finite (ULift.{v} R) M] :
    moduleDepth (ULift.{v} R) M = moduleDepth R M := by
  letI : IsRegularLocalRing (ULift.{v} R) := isRegularLocalRing_of_ulift_ring_model (R := R)
  letI : IsNoetherianRing (ULift.{v} R) := inferInstance
  letI : Algebra (ULift.{v} R) R :=
    (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom.toAlgebra
  have htower : IsScalarTower (ULift.{v} R) R M :=
    { smul_assoc := fun a r m ↦ by
        -- The lifted scalar action is still defined by `ULift.down`, so the tower law reduces
        -- to the original `R`-module associativity on `M`.
        simpa using (mul_smul (ULift.down a) r m) }
  -- The lifted scalar action is exactly restriction of scalars along the surjective map
  -- `ULift R → R`, so the general surjective-local depth comparison applies directly.
  exact
    @moduleDepth_eq_of_surjective_local_algebra
      (ULift.{v} R) R _ _ _ _ _ _ _ M _ _ _ htower _ _
      (algebraMap_surjective_of_ulift_ring_model (R := R))

/-- Helper for Proposition 10.110.1: the common-universe `ULift` model preserves the module
depth appearing in the source proof. -/
lemma moduleDepth_eq_of_ulift_ring_model
    [IsLocalRing (ULift.{v} R)]
    [Module.Finite (ULift.{v} R) M] :
    moduleDepth (ULift.{v} R) (ULift.{u} M) = moduleDepth R M := by
  -- First remove the module lift by the canonical linear equivalence `ULift.moduleEquiv`.
  -- Then compare the remaining depth with the original `R`-module via restricted scalars.
  calc
    moduleDepth (ULift.{v} R) (ULift.{u} M) = moduleDepth (ULift.{v} R) M := by
      simpa using
        moduleDepth_eq_of_equiv
          (R := ULift.{v} R)
          (e := (ULift.moduleEquiv : ULift.{u} M ≃ₗ[ULift.{v} R] M))
    _ = moduleDepth R M :=
      moduleDepth_eq_of_ulift_ring_restrictScalars (R := R) (M := M)

/-- Helper for Proposition 10.110.1: the same-universe `ULift` ring/module model already
realizes the source-faithful bounded finite free resolution upstairs. -/
lemma hasFiniteFreeResolutionLengthLE_of_ulift_ring_model
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasFiniteFreeResolutionLengthLE (ULift.{v} R) (ULift.{u} M) (d - e) := by
  let Rw : Type (max u v) := ULift.{v} R
  let Mw : Type (max u v) := ULift.{u} M
  letI : IsRegularLocalRing Rw := isRegularLocalRing_of_ulift_ring_model (R := R)
  letI : IsNoetherianRing Rw := inferInstance
  letI : Module.Finite Rw M :=
    Module.Finite.of_restrictScalars_finite (R := R) (A := Rw) (M := M)
  letI : Module.Finite Rw Mw :=
    Module.Finite.equiv (ULift.moduleEquiv (R := Rw) (M := M)).symm
  -- Route correction: recover the upstairs finite free resolution from the same-universe owner
  -- theorem only after rewriting the lifted dimension and depth back to the source invariants.
  have hdimw : ringKrullDim Rw = d := by
    calc
      ringKrullDim Rw = ringKrullDim R := by
        simpa [Rw] using ringKrullDim_eq_of_ulift_ring_model (R := R)
      _ = d := hdim
  have hdepthw : moduleDepth Rw Mw = e := by
    calc
      moduleDepth Rw Mw = moduleDepth R M := by
        simpa [Rw, Mw] using moduleDepth_eq_of_ulift_ring_model (R := R) (M := M)
      _ = e := hdepth
  have hpd : HasProjectiveDimensionLE (ModuleCat.of Rw Mw) (d - e) :=
    hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing_same_universe
      (R := Rw) (M₀ := Mw) hdimw hdepthw
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := Rw) (M := Mw) (d - e)).mp hpd

end
