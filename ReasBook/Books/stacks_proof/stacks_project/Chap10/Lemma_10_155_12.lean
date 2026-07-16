import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_2
import stacks_proof.stacks_project.Chap10.Lemma_10_154_5
import stacks_proof.stacks_project.Chap10.Lemma_10_155_10
import stacks_proof.stacks_project.Chap10.Lemma_10_155_12.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing
open CategoryTheory Limits

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

noncomputable section

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

/-- Helper for Chap10 Lemma 10 155 12: tensor commutativity carries the left `S`-algebra
structure on `S ⊗[R] Rˢʰ` to the right `S`-algebra structure on `Rˢʰ ⊗[R] S`. -/
private theorem tensorProductCommRightAlgEquiv_commutes (s : S) :
    (Algebra.TensorProduct.comm R S Rsh).toRingEquiv
        (algebraMap S (S ⊗[R] Rsh) s) =
      algebraMap S (Rsh ⊗[R] S) s := by
  -- On pure source elements, the tensor commutativity map simply moves `s` to the right tensor
  -- factor.
  simp
  rfl

/-- Helper for Chap10 Lemma 10 155 12: tensor commutativity as an `S`-algebra equivalence
between the two base-change presentations. -/
private noncomputable def tensorProductCommRightAlgEquiv :
    S ⊗[R] Rsh ≃ₐ[S] Rsh ⊗[R] S where
  __ := (Algebra.TensorProduct.comm R S Rsh).toRingEquiv
  commutes' := tensorProductCommRightAlgEquiv_commutes

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

/-- Helper for Chap10 Lemma 10 155 12: pin the commutative-ring instance on the localized
tensor product so ind-étale ring-hom statements use the `CommRing` instance path. -/
local instance strictHenselizationTensorPrime_localization_commRing :
    CommRing (Localization.AtPrime tensorPrime) :=
  inferInstance

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
/-- Helper for Chap10 Lemma 10 155 12: the localized tensor-product map to `Sˢʰ` is local. -/
private theorem strictHenselizationTensorLocalizationToSsh_isLocalHom :
    IsLocalHom (algebraMap (Localization.AtPrime tensorPrime) Ssh) := by
  -- The algebra map is the composite of the canonical local map between prime localizations and
  -- the localization equivalence from `Sˢʰ` localized at its maximal ideal back to `Sˢʰ`.
  change IsLocalHom (strictHenselizationTensorLocalizationToSsh p q φ hφ)
  rw [strictHenselizationTensorLocalizationToSsh]
  infer_instance

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

omit [Algebra R Rsh] [Algebra R Ssh] [Algebra S Ssh]
  [IsScalarTower R Rp Rsh] [IsScalarTower R Sq Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the chosen strict-henselization comparison is a local
homomorphism. -/
private theorem strictHenselizationComparison_isLocalHomLocal :
    IsLocalHom (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) := by
  -- The comparison map was defined as the chosen witness of the unique local lifting theorem.
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  let hexists :=
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ
  let hchosen := Classical.choose_spec hexists
  rcases hchosen with ⟨hlocal, -⟩
  simpa [strictHenselizationComparison] using hlocal

omit [Algebra S Ssh] [IsStrictHenselizationOf Sq Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the route `R → R_p → S_q → Sˢʰ` agrees with the
given `R`-algebra structure on `Sˢʰ`. -/
private theorem localizationAtPrimeToStrictHenselization_algebraMap (r : R) :
    (algebraMap Sq Ssh) ((algebraMap Rp Sq) ((algebraMap R Rp) r)) =
      (algebraMap R Ssh) r := by
  -- The map `R_p → S_q` was built from the localization of `R → S`, so it carries the image of
  -- `r` to the image of `r` through `S`, and the scalar tower to `Sˢʰ` finishes the comparison.
  have hlocal :
      (algebraMap Rp Sq) ((algebraMap R Rp) r) =
        (algebraMap S Sq) ((algebraMap R S) r) := by
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]
  rw [hlocal]
  rw [← IsScalarTower.algebraMap_apply R S Sq]
  rw [← IsScalarTower.algebraMap_apply R Sq Ssh]

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the tensor comparison restricts on the left to the
strict-henselization comparison. -/
private theorem strictHenselizationTensorMap_comp_includeLeft :
    (strictHenselizationTensorMap p q φ hφ).toRingHom.comp
        (includeLeftRingHom : Rsh →+* TensorRing) =
      (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) := by
  -- Unfold the tensor comparison to the universal lift and apply its left computation rule.
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp Ssh := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    symm
    exact localizationAtPrimeToStrictHenselization_algebraMap p q r
  ext x
  simp [strictHenselizationTensorMap]

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the tensor comparison restricts on the right to the
canonical map `S → S_q → Sˢʰ`. -/
private theorem strictHenselizationTensorMap_comp_includeRight :
    (strictHenselizationTensorMap p q φ hφ).toRingHom.comp
        (includeRight : S →ₐ[R] TensorRing).toRingHom =
      (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh).toRingHom := by
  -- Unfold the tensor comparison to the universal lift and apply its right computation rule.
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp Ssh := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    symm
    exact localizationAtPrimeToStrictHenselization_algebraMap p q r
  ext x
  simp [strictHenselizationTensorMap]

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the source map `S → S_q → Sˢʰ` contracts the maximal
ideal of `Sˢʰ` to `q`. -/
private theorem sourceToLocalizedStrictHenselization_comap_maximalIdeal :
    Ideal.comap (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh).toRingHom
        (maximalIdeal Ssh) =
      q := by
  -- First contract along the local strict-henselization map, then along the prime localization.
  calc
    Ideal.comap (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh).toRingHom
        (maximalIdeal Ssh)
        =
          Ideal.comap (algebraMap S Sq)
            (Ideal.comap (algebraMap Sq Ssh) (maximalIdeal Ssh)) := by
          simp [sourceToLocalizedStrictHenselization, Ideal.comap_comap]
    _ = Ideal.comap (algebraMap S Sq) (maximalIdeal Sq) := by
          rw [IsLocalRing.maximalIdeal_comap (algebraMap Sq Ssh)]
    _ = q := by
          simpa using (Localization.AtPrime.comap_maximalIdeal (R := S) (I := q))

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the left to the local comparison map
-- `Rˢʰ → Sˢʰ` derived from Lemma `10.155.10`. Since that map is local, the inverse image of
-- `maximalIdeal Sˢʰ` is `maximalIdeal Rˢʰ`. Unfold the tensor prime and rewrite the comap along
-- the left inclusion.
omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- The tensor-product prime lies over the maximal ideal of `Rˢʰ`. -/
theorem strictHenselizationTensorPrime_comap_includeLeft :
    Ideal.comap
        (includeLeftRingHom : Rsh →+* (Rsh ⊗[R] S))
        tensorPrime =
      maximalIdeal Rsh := by
  -- After composing comaps, the left computation lemma identifies the contraction with the
  -- maximal-ideal comap of the local comparison map.
  letI : IsLocalHom (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) :=
    strictHenselizationComparison_isLocalHomLocal p q φ hφ
  rw [strictHenselizationTensorPrime, Ideal.comap_comap,
    strictHenselizationTensorMap_comp_includeLeft]
  exact IsLocalRing.maximalIdeal_comap (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh)

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the right to the composite
-- `S → S_q → Sˢʰ`. The maximal ideal of `Sˢʰ` therefore pulls back to the chosen prime `q` of
-- `S`. Unfold the tensor prime and rewrite the resulting comap along the right inclusion.
omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- The tensor-product prime lies over the chosen prime `q` of `S`. -/
theorem strictHenselizationTensorPrime_comap_includeRight :
    Ideal.comap
        (includeRight : S →ₐ[R] (Rsh ⊗[R] S)).toRingHom
        tensorPrime =
      q := by
  -- The right computation lemma reduces the contraction to the composite `S → S_q → Sˢʰ`.
  rw [strictHenselizationTensorPrime, Ideal.comap_comap,
    strictHenselizationTensorMap_comp_includeRight]
  exact sourceToLocalizedStrictHenselization_comap_maximalIdeal (q := q)

noncomputable local instance strictHenselizationTensorPrime_sqAlgebra :
    Algebra Sq (Localization.AtPrime tensorPrime) :=
  (Localization.localRingHom q tensorPrime
    (includeRight : S →ₐ[R] TensorRing).toRingHom
    (strictHenselizationTensorPrime_comap_includeRight p q φ hφ).symm).toAlgebra

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the canonical map from `S_q` to the localized tensor
product is local. -/
private theorem strictHenselizationTensorLocalization_sq_isLocalHom :
    IsLocalHom (algebraMap Sq (Localization.AtPrime tensorPrime)) := by
  -- This is the local homomorphism induced by localizing the right tensor inclusion at the
  -- contraction equality just proved.
  simpa [RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom q tensorPrime
      (includeRight : S →ₐ[R] TensorRing).toRingHom
      (strictHenselizationTensorPrime_comap_includeRight p q φ hφ).symm)

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the composite `S_q → A → Sˢʰ` is the original
strict-henselization structure map, where `A` is the localized tensor product. -/
private theorem strictHenselizationTensorLocalization_comp_sq :
    (algebraMap (Localization.AtPrime tensorPrime) Ssh).comp
        (algebraMap Sq (Localization.AtPrime tensorPrime)) =
      algebraMap Sq Ssh := by
  -- It is enough to compare the two maps on the dense image of `S` in its localization `S_q`.
  refine IsLocalization.ringHom_ext q.primeCompl ?_
  ext x
  calc
    (((algebraMap (Localization.AtPrime tensorPrime) Ssh).comp
        (algebraMap Sq (Localization.AtPrime tensorPrime))).comp
        (algebraMap S Sq)) x
        = strictHenselizationTensorLocalizationToSsh p q φ hφ
            (algebraMap TensorRing (Localization.AtPrime tensorPrime)
              ((includeRight : S →ₐ[R] TensorRing) x)) := by
          rw [RingHom.comp_apply, RingHom.comp_apply]
          rw [show (algebraMap Sq (Localization.AtPrime tensorPrime)) =
              Localization.localRingHom q tensorPrime
                (includeRight : S →ₐ[R] TensorRing).toRingHom
                (strictHenselizationTensorPrime_comap_includeRight p q φ hφ).symm from rfl]
          rw [Localization.localRingHom_to_map]
          rw [show (algebraMap (Localization.AtPrime tensorPrime) Ssh) =
              strictHenselizationTensorLocalizationToSsh p q φ hφ from rfl]
          rw [show (includeRight : S →ₐ[R] TensorRing).toRingHom x =
              (includeRight : S →ₐ[R] TensorRing) x from rfl]
    _ = tensorToSsh ((includeRight : S →ₐ[R] TensorRing) x) := by
          rw [strictHenselizationTensorLocalizationToSsh_algebraMap]
    _ = (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh) x := by
          exact congrFun
            (congrArg DFunLike.coe
              (strictHenselizationTensorMap_comp_includeRight p q φ hφ)) x
    _ = ((algebraMap Sq Ssh).comp (algebraMap S Sq)) x := rfl

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the compatibility of the localized tensor map with
`S_q → Sˢʰ` holds pointwise. -/
private theorem strictHenselizationTensorLocalization_comp_sq_apply (x : Sq) :
    (algebraMap (Localization.AtPrime tensorPrime) Ssh)
        ((algebraMap Sq (Localization.AtPrime tensorPrime)) x) =
      algebraMap Sq Ssh x := by
  -- This packages the ring-hom equality above as the rewrite form needed when transporting
  -- future localized ind-étale witnesses through the common target `Sˢʰ`.
  exact congrFun
    (congrArg DFunLike.coe
      (strictHenselizationTensorLocalization_comp_sq p q φ hφ)) x

/-- Helper for Chap10 Lemma 10 155 12: the current tensor ring `Rˢʰ ⊗[R] S` is ind-étale over
`S`. -/
private theorem strictHenselizationTensorRing_isFilteredColimitOfEtale_overS
    (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    [IsScalarTower R (Localization.AtPrime p) Rsh] :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap S TensorRing) := by
  -- First compose the prime localization `R → R_p` with the strict henselization
  -- `R_p → Rˢʰ`, giving an ind-étale presentation of `Rˢʰ` over `R`.
  have hRp : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap R (Localization.AtPrime p)) :=
    isFilteredColimitOfEtale_localizationMap (A := R) p.primeCompl
  have hRshRp : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap (Localization.AtPrime p) Rsh) :=
    IsStrictHenselizationOf.isFilteredColimitOfEtale
      (R := Localization.AtPrime p) (S := Rsh)
  have hRshComp : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      ((algebraMap (Localization.AtPrime p) Rsh).comp
        (algebraMap R (Localization.AtPrime p))) :=
    RingHom.isFilteredColimitOfEtale_comp
      (algebraMap R (Localization.AtPrime p))
      (algebraMap (Localization.AtPrime p) Rsh) hRp hRshRp
  have hRsh : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap R Rsh) := by
    -- The composite just constructed is the ambient `R`-algebra map to `Rˢʰ`.
    have hmap :
        (algebraMap (Localization.AtPrime p) Rsh).comp
            (algebraMap R (Localization.AtPrime p)) =
          algebraMap R Rsh := by
      ext r
      exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) Rsh r).symm
    simpa [hmap] using hRshComp
  have hBase : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap S (S ⊗[R] Rsh)) :=
    isFilteredColimitOfEtale_tensorBaseChangeSameUniverse
      (A := R) (B := Rsh) (T := S) hRsh
  -- Finally switch from `S ⊗[R] Rˢʰ` to the file's chosen tensor order `Rˢʰ ⊗[R] S`.
  exact isFilteredColimitOfEtale_of_algEquiv
    (A := S) (B := S ⊗[R] Rsh) (C := TensorRing)
    (tensorProductCommRightAlgEquiv (R := R) (S := S) (Rsh := Rsh)) hBase

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the localized tensor ring is ind-étale over the original
ring `S`. -/
private theorem strictHenselizationTensorLocalization_isFilteredColimitOfEtale_overS :
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap S (Localization.AtPrime tensorPrime)) := by
  -- Compose the ind-étale tensor-ring map with the étale localization at `tensorPrime`.
  have hTensor : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap S TensorRing) :=
    strictHenselizationTensorRing_isFilteredColimitOfEtale_overS (p := p)
  have hLoc : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap TensorRing (Localization.AtPrime tensorPrime)) :=
    isFilteredColimitOfEtale_localizationMap (A := TensorRing) (tensorPrime).primeCompl
  have hComp : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      ((algebraMap TensorRing (Localization.AtPrime tensorPrime)).comp
        (algebraMap S TensorRing)) :=
    RingHom.isFilteredColimitOfEtale_comp
      (algebraMap S TensorRing)
      (algebraMap TensorRing (Localization.AtPrime tensorPrime)) hTensor hLoc
  -- The composite is the canonical `S`-algebra map into the localized tensor ring.
  have hmap :
      (algebraMap TensorRing (Localization.AtPrime tensorPrime)).comp
          (algebraMap S TensorRing) =
        algebraMap S (Localization.AtPrime tensorPrime) := by
    ext s
    exact IsScalarTower.algebraMap_apply S TensorRing (Localization.AtPrime tensorPrime) s
  simpa [hmap] using hComp

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the localized tensor product is ind-étale over `S_q`. -/
private theorem strictHenselizationTensorLocalization_isFilteredColimitOfEtale_overSq :
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap Sq (Localization.AtPrime tensorPrime)) := by
  -- Route correction: avoid the blocked `S_q ⊗[R_p] Rˢʰ` comparison.  Both `S_q` and the
  -- localized tensor ring are ind-étale over `S`, so the common-base theorem gives the desired
  -- map directly.
  letI : IsScalarTower S Sq (Localization.AtPrime tensorPrime) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext s
      symm
      have hAlgMapSq : (algebraMap Sq (Localization.AtPrime tensorPrime)) =
          Localization.localRingHom q tensorPrime
            (includeRight : S →ₐ[R] TensorRing).toRingHom
            (strictHenselizationTensorPrime_comap_includeRight p q φ hφ).symm := rfl
      rw [hAlgMapSq, RingHom.comp_apply]
      rw [Localization.localRingHom_to_map]
      exact (IsScalarTower.algebraMap_apply S TensorRing
        (Localization.AtPrime tensorPrime) s).symm
  have hSq : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap S Sq) :=
    isFilteredColimitOfEtale_localizationMap (A := S) q.primeCompl
  have hTensorLoc : RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap S (Localization.AtPrime tensorPrime)) :=
    strictHenselizationTensorLocalization_isFilteredColimitOfEtale_overS p q φ hφ
  exact RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    hSq hTensorLoc

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the final map from the localized tensor product to
`Sˢʰ` is ind-étale. -/
private theorem strictHenselizationTensorLocalization_isFilteredColimitOfEtale :
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap (Localization.AtPrime tensorPrime) Ssh) := by
  -- The common-base theorem reduces the final ind-étale field to the known strict
  -- henselization `S_q → Sˢʰ` and the isolated `S_q → A` premise above.
  letI : IsScalarTower Sq (Localization.AtPrime tensorPrime) Ssh :=
    IsScalarTower.of_algebraMap_eq'
      (strictHenselizationTensorLocalization_comp_sq p q φ hφ).symm
  exact RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    (strictHenselizationTensorLocalization_isFilteredColimitOfEtale_overSq p q φ hφ)
    (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := Sq) (S := Ssh))

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Helper for Chap10 Lemma 10 155 12: the final localized tensor map sends the maximal ideal
onto the maximal ideal of `Sˢʰ`. -/
private theorem strictHenselizationTensorLocalization_map_maximalIdeal :
    Ideal.map (algebraMap (Localization.AtPrime tensorPrime) Ssh)
        (maximalIdeal (Localization.AtPrime tensorPrime)) =
      maximalIdeal Ssh := by
  -- One inclusion is locality of the final map; the other transports the known equality for
  -- `S_q → Sˢʰ` across the local map `S_q → A`.
  letI : IsLocalHom (algebraMap (Localization.AtPrime tensorPrime) Ssh) :=
    strictHenselizationTensorLocalizationToSsh_isLocalHom p q φ hφ
  letI : IsLocalHom (algebraMap Sq (Localization.AtPrime tensorPrime)) :=
    strictHenselizationTensorLocalization_sq_isLocalHom p q φ hφ
  apply le_antisymm
  · exact IsLocalRing.map_maximalIdeal_le (algebraMap (Localization.AtPrime tensorPrime) Ssh)
  · calc
      maximalIdeal Ssh =
          Ideal.map (algebraMap Sq Ssh) (maximalIdeal Sq) := by
            exact (IsStrictHenselizationOf.map_maximalIdeal (R := Sq) (S := Ssh)).symm
      _ = Ideal.map
            ((algebraMap (Localization.AtPrime tensorPrime) Ssh).comp
              (algebraMap Sq (Localization.AtPrime tensorPrime)))
            (maximalIdeal Sq) := by
            rw [strictHenselizationTensorLocalization_comp_sq]
      _ = Ideal.map (algebraMap (Localization.AtPrime tensorPrime) Ssh)
            (Ideal.map (algebraMap Sq (Localization.AtPrime tensorPrime))
              (maximalIdeal Sq)) := by
            rw [Ideal.map_map]
      _ ≤ Ideal.map (algebraMap (Localization.AtPrime tensorPrime) Ssh)
            (maximalIdeal (Localization.AtPrime tensorPrime)) := by
            exact Ideal.map_mono
              (IsLocalRing.map_maximalIdeal_le
                (algebraMap Sq (Localization.AtPrime tensorPrime)))

-- Proof sketch: this is the strict-henselian analogue of Lemma `10.155.8`, now using the
-- comparison map `Rˢʰ → Sˢʰ` determined by Lemma `10.155.10` from the compatible residue-field map
-- `φ`. Replacing the henselian colimit argument by the strict-henselian one from Lemma
-- `10.155.11` identifies `Sˢʰ`, canonically viewed through the localization of its maximal ideal,
-- with the strict henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime
-- over `maximalIdeal Rˢʰ` and `q`.
omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- Chap10 Lemma 10 155 12: let `Rsh` and `Ssh` be strict henselizations of `R_p` and `S_q`, and fix a
residue-field map `φ : κ(Rˢʰ) → κ(Sˢʰ)` compatible with the canonical map `κ(Rₚ) → κ(S_q)`. Then
`Sˢʰ`, canonically identified with the localization of `Sˢʰ` at its maximal ideal, is a strict
henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime cut out by the
induced strict-henselization comparison `Rˢʰ → Sˢʰ`. -/
@[stacks 08HV]
theorem isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime :
    IsStrictHenselizationOf
      (Localization.AtPrime tensorPrime)
      Ssh := by
  -- The final structure now assembles field-by-field from the local map, the isolated
  -- ind-étale field, and the maximal-ideal transport lemma.
  letI : IsLocalHom (algebraMap (Localization.AtPrime tensorPrime) Ssh) :=
    strictHenselizationTensorLocalizationToSsh_isLocalHom p q φ hφ
  exact
    { isFilteredColimitOfEtale :=
        strictHenselizationTensorLocalization_isFilteredColimitOfEtale p q φ hφ
      map_maximalIdeal := strictHenselizationTensorLocalization_map_maximalIdeal p q φ hφ }

end
