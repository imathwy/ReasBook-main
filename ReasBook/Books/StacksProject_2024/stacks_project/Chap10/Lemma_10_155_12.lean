import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

noncomputable section

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

end LocalRingLocalization

section

variable {R S Rsh Ssh : Type u}
variable [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
variable [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra R Rsh] [Algebra R Ssh] [Algebra S Ssh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable [IsScalarTower R (Localization.AtPrime p) Rsh]
variable [IsScalarTower R (Localization.AtPrime q) Ssh]
variable [IsScalarTower R S Ssh]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q
local notation "TensorRing" => Rsh ⊗[R] S

noncomputable local instance localizationAtPrime_algebra :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra

local instance localizationAtPrime_isLocalHom :
    IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p))

noncomputable local instance residueFieldSourceAlgebra :
    Algebra (ResidueField Rp) (ResidueField Rsh) :=
  (ResidueField.map (algebraMap Rp Rsh)).toAlgebra

noncomputable local instance residueFieldTargetAlgebra :
    Algebra (ResidueField Sq) (ResidueField Ssh) :=
  (ResidueField.map (algebraMap Sq Ssh)).toAlgebra

variable (φ : ResidueField Rsh →+* ResidueField Ssh)
variable (hφ :
  φ.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
    (ResidueField.map (algebraMap (Localization.AtPrime q) Ssh)).comp
      (ResidueField.map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))

/-- The canonical comparison map `Rˢʰ → Sˢʰ` induced by the compatible residue-field map `φ`. -/
noncomputable abbrev strictHenselizationComparison :
    let _ : Algebra Rp Ssh :=
      ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
    let _ : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
    Rsh →ₐ[Rp] Ssh := by
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  exact Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ

/-- The canonical map `S → S_q → Sˢʰ` over `R`. -/
noncomputable def sourceToLocalizedStrictHenselization : S →ₐ[R] Ssh where
  toRingHom := (algebraMap Sq Ssh).comp (algebraMap S Sq)
  commutes' r := by
    change (algebraMap Sq Ssh) ((algebraMap S Sq) ((algebraMap R S) r)) = (algebraMap R Ssh) r
    rw [← IsScalarTower.algebraMap_apply R S Sq]
    rw [← IsScalarTower.algebraMap_apply R Sq Ssh]

/-- The canonical tensor-product comparison map `Rˢʰ ⊗[R] S → Sˢʰ`. -/
noncomputable abbrev strictHenselizationTensorMap : TensorRing →ₐ[R] Ssh := by
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp Ssh := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    symm
    change (algebraMap Sq Ssh)
        ((algebraMap Rp Sq) ((algebraMap R Rp) r)) = (algebraMap R Ssh) r
    rw [show (algebraMap Rp Sq) ((algebraMap R Rp) r) =
        (algebraMap S Sq) ((algebraMap R S) r) by
          simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]]
    rw [← IsScalarTower.algebraMap_apply R S Sq]
    rw [← IsScalarTower.algebraMap_apply R Sq Ssh]
  exact Algebra.TensorProduct.lift
    ((strictHenselizationComparison p q φ hφ).restrictScalars R)
    (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh)
    (fun _ _ ↦ Commute.all _ _)

/-- The canonical prime of `Rˢʰ ⊗[R] S` cut out by the maximal ideal of `Sˢʰ`. -/
noncomputable abbrev strictHenselizationTensorPrime : Ideal TensorRing :=
  Ideal.comap (strictHenselizationTensorMap p q φ hφ).toRingHom (maximalIdeal Ssh)

local notation "tensorToSsh" =>
  strictHenselizationTensorMap p q φ hφ
local notation "tensorPrime" =>
  strictHenselizationTensorPrime p q φ hφ

/- 
Domain-style sampling:
- primary domain: strict henselization base change along `R → S`, expressed through the tensor
  product `Rˢʰ ⊗[R] S` and the comparison induced from `Rₚ → S_q`;
- sampled owner declarations of the same kind:
  `IsStrictHenselizationOf`,
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`,
  `Localization.localRingHom`,
  `henselizationTensorMap` / `henselizationTensorPrime` from Lemma `10.155.8`;
- best owner abstraction:
  - `source-facing`: the tensor-product prime cut out by the strict-henselization comparison and
    the resulting strict-henselization statement;
  - `core/canonical`: `IsStrictHenselizationOf`, `Localization.localRingHom`, and the strict-
    henselization comparison theorem `10.155.10`;
  - `bridge/view`: the explicit residue-field comparison `φ`, from which the comparison
    `Rˢʰ → Sˢʰ` is derived, rather than stored as primitive public algebra data;
- primitive data: the strict henselization owners on `Rₚ` and `S_q`, together with the
  compatible residue-field map `φ`;
- derived API: the comparison map `Rˢʰ → Sˢʰ`, the tensor-product map `Rˢʰ ⊗[R] S → Sˢʰ`, its
  contracted prime, and the induced localized algebra structure on `Sˢʰ`.

This file therefore treats the residue-field comparison as the source-facing compatibility input
and derives the strict-henselization comparison map from Lemma `10.155.10`, instead of accepting
an arbitrary `Rˢʰ`-algebra structure on `Sˢʰ`.
-/

local instance strictHenselizationTensorPrime_isPrime :
    Ideal.IsPrime tensorPrime :=
  Ideal.comap_isPrime _ (maximalIdeal Ssh)

noncomputable abbrev strictHenselizationTensorLocalizationToSsh :
    Localization.AtPrime tensorPrime →+* Ssh :=
  (IsLocalization.algEquiv
      (maximalIdeal Ssh).primeCompl
      (Localization.AtPrime (maximalIdeal Ssh))
      Ssh : Localization.AtPrime (maximalIdeal Ssh) →+* Ssh).comp <|
    Localization.localRingHom
      tensorPrime
      (maximalIdeal Ssh)
      (strictHenselizationTensorMap p q φ hφ).toRingHom
      rfl

/-- The canonical algebra structure on `Sˢʰ` over the localization of `Rˢʰ ⊗[R] S` at the tensor
prime cut out by `maximalIdeal Sˢʰ`, using the comparison map induced from the compatible
residue-field data `φ`. -/
noncomputable instance strictHenselizationTensorPrime_algebra :
    Algebra (Localization.AtPrime tensorPrime) Ssh :=
  RingHom.toAlgebra (strictHenselizationTensorLocalizationToSsh p q φ hφ)

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- The localized tensor-product map to `Sˢʰ` agrees with the unlocalized tensor map on pure
source elements. -/
theorem strictHenselizationTensorLocalizationToSsh_algebraMap (x : TensorRing) :
    strictHenselizationTensorLocalizationToSsh p q φ hφ
        (algebraMap TensorRing (Localization.AtPrime tensorPrime) x) =
      tensorToSsh x := by
  rw [strictHenselizationTensorLocalizationToSsh, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  simpa using
    (IsLocalization.algEquiv_apply
      (maximalIdeal Ssh).primeCompl
      (Localization.AtPrime (maximalIdeal Ssh))
      Ssh
      (algebraMap Ssh (Localization.AtPrime (maximalIdeal Ssh)) (tensorToSsh x)))

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the left to the local comparison map
-- `Rˢʰ → Sˢʰ` derived from Lemma `10.155.10`. Since that map is local, the inverse image of
-- `maximalIdeal Sˢʰ` is `maximalIdeal Rˢʰ`. Unfold the tensor prime and rewrite the comap along
-- the left inclusion.
/-- The tensor-product prime lies over the maximal ideal of `Rˢʰ`. -/
theorem strictHenselizationTensorPrime_comap_includeLeft :
    Ideal.comap
        (includeLeftRingHom : Rsh →+* (Rsh ⊗[R] S))
        tensorPrime =
      maximalIdeal Rsh := sorry

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the right to the composite
-- `S → S_q → Sˢʰ`. The maximal ideal of `Sˢʰ` therefore pulls back to the chosen prime `q` of
-- `S`. Unfold the tensor prime and rewrite the resulting comap along the right inclusion.
/-- The tensor-product prime lies over the chosen prime `q` of `S`. -/
theorem strictHenselizationTensorPrime_comap_includeRight :
    Ideal.comap
        (includeRight : S →ₐ[R] (Rsh ⊗[R] S)).toRingHom
        tensorPrime =
      q := sorry

-- Proof sketch: this is the strict-henselian analogue of Lemma `10.155.8`, now using the
-- comparison map `Rˢʰ → Sˢʰ` determined by Lemma `10.155.10` from the compatible residue-field map
-- `φ`. Replacing the henselian colimit argument by the strict-henselian one from Lemma
-- `10.155.11` identifies `Sˢʰ`, canonically viewed through the localization of its maximal ideal,
-- with the strict henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime
-- over `maximalIdeal Rˢʰ` and `q`.
/-- Lemma 10.155.12: let `Rsh` and `Ssh` be strict henselizations of `R_p` and `S_q`, and fix a
residue-field map `φ : κ(Rˢʰ) → κ(Sˢʰ)` compatible with the canonical map `κ(Rₚ) → κ(S_q)`. Then
`Sˢʰ`, canonically identified with the localization of `Sˢʰ` at its maximal ideal, is a strict
henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime cut out by the
induced strict-henselization comparison `Rˢʰ → Sˢʰ`. -/
theorem isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime :
    IsStrictHenselizationOf
      (Localization.AtPrime tensorPrime)
      Ssh := sorry

end
