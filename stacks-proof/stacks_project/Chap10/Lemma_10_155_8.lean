import Mathlib
import stacks_project.Chap10.Lemma_10_155_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

end LocalRingLocalization

section

variable {R S Rh Sh : Type u}
variable [CommRing R] [CommRing S] [CommRing Rh] [CommRing Sh]
variable [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra R Rh] [Algebra R Sh]
variable [Algebra (Localization.AtPrime p) Rh] [IsHenselizationOf (Localization.AtPrime p) Rh]
variable [Algebra (Localization.AtPrime q) Sh] [IsHenselizationOf (Localization.AtPrime q) Sh]
variable [Algebra (Localization.AtPrime p) Sh]
variable [IsScalarTower R (Localization.AtPrime p) Rh]
variable [IsScalarTower R (Localization.AtPrime p) Sh]
variable [IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Sh]

local notation "Rₚ" => Localization.AtPrime p
local notation "S_q" => Localization.AtPrime q
local notation "TensorRing" => Rh ⊗[R] S

private noncomputable abbrev henselizationToSh : Rh →ₐ[Rₚ] Sh :=
  @henselizationMap Rₚ Rh Sh _ _ _ _ _ _ _ S_q _ _ _ _ _ _ _

/-- The canonical map `S → S_q^h` obtained by composing `S → S_q` with the henselization
structure map `S_q → Sh`. -/
noncomputable def sourceToLocalizedHenselization : S →ₐ[R] Sh where
  toRingHom := (algebraMap S_q Sh).comp (algebraMap S S_q)
  commutes' r := by
    change (algebraMap S_q Sh) ((algebraMap S S_q) ((algebraMap R S) r)) = (algebraMap R Sh) r
    rw [← IsScalarTower.algebraMap_apply R S S_q]
    rw [IsScalarTower.algebraMap_apply R Rₚ S_q]
    rw [← IsScalarTower.algebraMap_apply Rₚ S_q Sh]
    exact (IsScalarTower.algebraMap_apply R Rₚ Sh r).symm

/-- The canonical tensor-product comparison map `Rʰ ⊗[R] S → S_q^h`. -/
noncomputable abbrev henselizationTensorMap : TensorRing →ₐ[R] Sh :=
  Algebra.TensorProduct.lift
    ((henselizationToSh p q : Rh →ₐ[Rₚ] Sh).restrictScalars R)
    (sourceToLocalizedHenselization p q)
    (fun _ _ ↦ Commute.all _ _)

/-- The canonical prime of `Rʰ ⊗[R] S` cut out by the maximal ideal of `S_q^h`. -/
noncomputable abbrev henselizationTensorPrime : Ideal TensorRing :=
  Ideal.comap ((henselizationTensorMap p q).toRingHom) (maximalIdeal Sh)

local instance localizationAtPrime_isLocalHom :
    IsLocalHom (algebraMap Rₚ S_q) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p))

local notation "sourceToSh" => (sourceToLocalizedHenselization p q : S →ₐ[R] Sh)
local notation "tensorToSh" =>
  ((@henselizationTensorMap R S Rh Sh _ _ _ _ _ p _ q _ _ _ _ _ _ _ _ _ _ _ _ :
      TensorRing →ₐ[R] Sh))
local notation "tensorPrime" =>
  ((@henselizationTensorPrime R S Rh Sh _ _ _ _ _ p _ q _ _ _ _ _ _ _ _ _ _ _ _ :
      Ideal TensorRing))

/- Domain-style sampling:
- primary domain: henselization base change along `R → S`, expressed through the tensor product
  of a henselization of `R_p` with the target algebra `S`;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `henselizationMap`,
  `Localization.localAlgHom`,
  `Localization.localRingHom`,
  `RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base`;
- best owner abstraction:
  `source-facing`: the canonical prime of `Rʰ ⊗[R] S` cut out by `maximalIdeal Sh` and the
    induced henselization statement;
  `core/canonical`: `IsHenselizationOf`, `Localization.localRingHom`, and
    the comparison `henselizationMap` from Lemma `10.155.6`;
  `bridge/view`: the canonical source map `S → Sh`, the public tensor comparison map to `Sh`, and
    the contracted prime they define;
- primitive data: the henselization owners on `Rₚ` and `S_q`;
- derived API: the local comparison `Rh → Sh`, the canonical source map `S → S_q → Sh`, the
  tensor-product map, its contracted prime, and the induced localization algebra structure.

This file should therefore expose the canonical `S → Sh` bridge, the tensor comparison map, and
the induced prime as public bridge declarations, while keeping the localization algebra structure
itself derived.
-/

local instance tensorPrime_isPrime :
    Ideal.IsPrime tensorPrime :=
  Ideal.comap_isPrime _ (maximalIdeal Sh)

noncomputable abbrev henselizationTensorLocalizationToSh :
    Localization.AtPrime tensorPrime →+* Sh :=
  (IsLocalization.algEquiv
      (maximalIdeal Sh).primeCompl
      (Localization.AtPrime (maximalIdeal Sh))
      Sh : Localization.AtPrime (maximalIdeal Sh) →+* Sh).comp <|
    Localization.localRingHom
      tensorPrime
      (maximalIdeal Sh)
      ((henselizationTensorMap p q).toRingHom)
      rfl

/-- The canonical algebra structure on `Sh` over the localization of `Rʰ ⊗[R] S` at the tensor
prime cut out by `maximalIdeal Sh`. -/
noncomputable instance henselizationTensorPrime_algebra :
    Algebra (Localization.AtPrime tensorPrime) Sh :=
  RingHom.toAlgebra (henselizationTensorLocalizationToSh p q)

/-- The localized tensor-product map to `Sh` agrees with the unlocalized tensor map on pure
source elements. -/
theorem henselizationTensorLocalizationToSh_algebraMap (x : TensorRing) :
    henselizationTensorLocalizationToSh p q
        (algebraMap TensorRing (Localization.AtPrime tensorPrime) x) =
      tensorToSh x := by
  rw [henselizationTensorLocalizationToSh, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  simpa using
    (IsLocalization.algEquiv_apply
      (maximalIdeal Sh).primeCompl
      (Localization.AtPrime (maximalIdeal Sh))
      Sh
      (algebraMap Sh (Localization.AtPrime (maximalIdeal Sh)) (tensorToSh x)))

-- Proof sketch: the tensor-product map to `Sh` restricts on the left to the local map `Rh → Sh`.
-- Since that map is local, the inverse image of `maximalIdeal Sh` is `maximalIdeal Rh`. Unfold the
-- definition of the tensor prime and rewrite the comap along the composite with the left
-- inclusion.
/-- The tensor-product prime lies over the maximal ideal of `Rh`. -/
theorem henselizationTensorPrime_comap_includeLeft :
    Ideal.comap
        (includeLeftRingHom : Rh →+* (Rh ⊗[R] S))
        tensorPrime =
      maximalIdeal Rh := sorry

-- Proof sketch: the tensor-product map to `Sh` restricts on the right to the composite
-- `S → S_q → Sh`. The maximal ideal of `Sh` therefore pulls back to the prime `q` of `S`. Unfold
-- the tensor prime and rewrite the resulting comap along the right inclusion.
/-- The tensor-product prime lies over the chosen prime `q` of `S`. -/
theorem henselizationTensorPrime_comap_includeRight :
    Ideal.comap
        (includeRight : S →ₐ[R] (Rh ⊗[R] S)).toRingHom
        tensorPrime =
      q := sorry

-- Proof sketch: by Lemma `10.155.7`, both henselizations are filtered colimits of étale
-- neighborhoods over their respective local rings; then Lemma `10.143.3` and Lemma `10.154.5`
-- show that the local ring `Sh_(m_Sh)`, hence canonically `Sh` itself, is a filtered colimit of
-- étale algebras over the localized tensor product. The tensor-product prime is the unique prime
-- over `maximalIdeal Rh` and `q` cut out by the map to `Sh`, so Lemma `10.154.7` identifies this
-- local ring with the henselization of that localization.
/-- Lemma 10.155.8: if `Rh` and `Sh` are henselizations of `R_p` and `S_q`, and `Rh → Sh` is the
local ring map induced by Lemma `10.155.6`, then `Sh`, canonically viewed as the localization of
`Sh` at its maximal ideal, is a henselization of the localization of `Rʰ ⊗[R] S` at the
canonical prime cut out by `maximalIdeal Sh`, i.e. the prime lying over `maximalIdeal Rh` and
`q`. -/
theorem isHenselizationOf_localizationAt_henselizationTensorPrime :
    IsHenselizationOf
      (Localization.AtPrime tensorPrime)
      Sh :=
  sorry

end
