import Mathlib
import StacksProject_2024.Chap10.Lemma_10_153_4
import StacksProject_2024.Chap10.Lemma_10_154_7
import StacksProject_2024.Chap10.Lemma_10_155_6
import StacksProject_2024.Chap10.Lemma_10_155_8

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

noncomputable section

/-- Helper for Chap10 Lemma 10 156 1: an etale algebra map is a filtered colimit of etale
algebras in the chapter's source-facing wrapper. -/
private theorem filteredColimitOfEtale_of_etaleAlgebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).Etale) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Translate to the raw categorical owner and use the one-object ind-etale presentation.
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap A B))
      (by simpa [CommRingCat.etale] using hAB)

/-- Helper for Chap10 Lemma 10 156 1: a henselian local ring is its own henselization. -/
private lemma henselianSelf_isHenselizationOf {A : Type u} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] : IsHenselizationOf A A := by
  refine { isFilteredColimitOfEtale := ?_, map_maximalIdeal := ?_, residueField_bijective := ?_ }
  · -- The identity map is etale, hence gives a one-object ind-etale presentation.
    exact filteredColimitOfEtale_of_etaleAlgebraMap
      (RingHom.Etale.of_bijective (by simpa using Function.bijective_id))
  · -- The identity algebra map fixes the maximal ideal.
    simp
  · -- The induced residue-field map is the identity.
    simpa using (Function.bijective_id : Function.Bijective (fun x : ResidueField A => x))

/-- Helper for Chap10 Lemma 10 156 1: a local endomorphism of a henselization over its base is
the identity. -/
private lemma henselizationEndomorphism_eq_id {A Ah : Type u} [CommRing A] [IsLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (f : Ah →ₐ[A] Ah) (hf : IsLocalHom (f : Ah →+* Ah)) :
    f = AlgHom.id A Ah := by
  letI : IsLocalHom (algebraMap A A) := by
    simpa using (inferInstance : IsLocalHom (RingHom.id A))
  letI : IsScalarTower A A Ah := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨_, _, huniq⟩ :=
    existsUnique_algHom_between_henselizations_of_localHom
      (R := A) (S := A) (Rh := Ah) (Sh := Ah)
  have hidLocal : IsLocalHom ((AlgHom.id A Ah : Ah →ₐ[A] Ah) : Ah →+* Ah) := by
    simpa using (inferInstance : IsLocalHom (RingHom.id Ah))
  -- Both endomorphisms are the unique local `A`-algebra endomorphism of the henselization.
  exact (huniq f hf).trans (huniq (AlgHom.id A Ah) hidLocal).symm

/-- Helper for Chap10 Lemma 10 156 1: a henselization over a henselian base is finite. -/
private lemma henselizationAlgebraMap_finite_of_henselian {A Ah : Type u}
    [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] :
    RingHom.Finite (algebraMap A Ah) := by
  letI : IsHenselizationOf A A := henselianSelf_isHenselizationOf
  letI : IsLocalHom (algebraMap A A) := by
    simpa using (inferInstance : IsLocalHom (RingHom.id A))
  letI : IsScalarTower A A A := IsScalarTower.of_algebraMap_eq' rfl
  let g : Ah →ₐ[A] A := henselizationMap (R := A) (S := A) (Rh := Ah) (Sh := A)
  have hgLocal : IsLocalHom (g : Ah →+* A) :=
    henselizationMap_isLocalHom (R := A) (S := A) (Rh := Ah) (Sh := A)
  letI : IsLocalHom ((Algebra.ofId A Ah : A →ₐ[A] Ah) : A →+* Ah) := by
    simpa using (inferInstance : IsLocalHom (algebraMap A Ah))
  letI : IsLocalHom (g : Ah →+* A) := hgLocal
  have hcompLocal : IsLocalHom (((Algebra.ofId A Ah).comp g : Ah →ₐ[A] Ah) :
      Ah →+* Ah) := by
    exact RingHom.isLocalHom_comp
      ((Algebra.ofId A Ah : A →ₐ[A] Ah) : A →+* Ah) (g : Ah →+* A)
  have hcomp : (Algebra.ofId A Ah).comp g = AlgHom.id A Ah :=
    henselizationEndomorphism_eq_id ((Algebra.ofId A Ah).comp g) hcompLocal
  refine RingHom.Finite.of_surjective (algebraMap A Ah) ?_
  intro y
  refine ⟨g y, ?_⟩
  -- The inverse comparison shows every henselization element comes from the henselian base.
  exact congrFun (congrArg DFunLike.coe hcomp) y

/-
Lemma 10.156.1 (1): this is the owner-level henselization statement already proved in
Lemma `10.155.8` for the canonical local map between localizations. The present file uses that
source-facing statement directly rather than keeping a parallel local alias.
-/
recall isHenselizationOf_localizationAt_henselizationTensorPrime

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable {Rph Sqh : Type u} [CommRing Rph] [CommRing Sqh]
variable [Algebra (Localization.AtPrime p) Rph]
variable [IsHenselizationOf (Localization.AtPrime p) Rph]
variable [Algebra (Localization.AtPrime q) Sqh]
variable [IsHenselizationOf (Localization.AtPrime q) Sqh]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q

noncomputable local instance : Algebra Rp Sq :=
  (Localization.localRingHom p q (algebraMap R S) (Ideal.over_def q p)).toAlgebra

local instance : IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (Ideal.over_def q p)

local notation "comparison" =>
  @henselizationMapRingHom Rp Rph Sqh _ _ _ _ _ _ Sq _ _ _ _ _ _

/-- Helper for Chap10 Lemma 10 156 1: quasi-finiteness at `q` base-changes to the canonical
tensor prime of `R_p^h ⊗[R] S`. -/
private lemma quasiFiniteAt_henselizationTensorPrime
    [Algebra R Rph] [Algebra R Sqh] [Algebra Rp Sqh]
    [IsScalarTower R Rp Rph] [IsScalarTower R Rp Sqh] [IsScalarTower Rp Sq Sqh]
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.FiniteType.QuasiFiniteAt Rph (Rph ⊗[R] S)
      (henselizationTensorPrime (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q) := by
  letI : Algebra.FiniteType R S := hqf.finiteType
  have hquasi : Algebra.QuasiFiniteAt Rph
      (henselizationTensorPrime (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q) := by
    letI : Algebra.QuasiFiniteAt R q := hqf.toQuasiFiniteAt
    exact Algebra.QuasiFiniteAt.baseChange (R := R) q
      (A := Rph)
      (henselizationTensorPrime (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q)
      (by
        -- The tensor prime contracts to the original prime along the right tensor factor.
        exact (henselizationTensorPrime_comap_includeRight
          (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q).symm)
  exact Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt hquasi

/-- Helper for Chap10 Lemma 10 156 1: the public henselization comparison factors through the
localized tensor product used in Lemma 10.155.8. -/
private lemma henselizationMapRingHom_eq_tensorLocalization_comp
    [Algebra R Rph] [Algebra R Sqh] [Algebra Rp Sqh]
    [IsScalarTower R Rp Rph] [IsScalarTower R Rp Sqh] [IsScalarTower Rp Sq Sqh] :
    comparison =
      (henselizationTensorLocalizationToSh
        (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q).comp
        ((algebraMap (Rph ⊗[R] S)
          (Localization.AtPrime
            (henselizationTensorPrime (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q))).comp
          (Algebra.TensorProduct.includeLeftRingHom : Rph →+* Rph ⊗[R] S)) := by
  -- The localized tensor map restricts on the left tensor factor to the comparison map.
  exact (henselizationTensorLocalizationToSh_comp_includeLeft
    (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q).symm

/- Domain-style sampling:
- primary domain: local commutative algebra of henselizations along the canonical local map
  `Localization.AtPrime p → Localization.AtPrime q`;
- sampled owner declarations of the same kind:
  `Algebra.FiniteType.QuasiFiniteAt`,
  `IsHenselizationOf`,
  `henselizationMap`,
  `moduleFinite_localizationAtPrime_of_quasiFiniteAt_over_maximalIdeal`,
  `henselizationTensorPrime`,
  `isHenselizationOf_localizationAt_henselizationTensorPrime`;
- best owner abstraction: this file is a `bridge/view` refinement over the owner layer
  `IsHenselizationOf`, while the source-facing quasi-finite input remains
  `Algebra.FiniteType.QuasiFiniteAt R S q`; the `Rₚ`-algebra structure and tower on `Sqh` must be
  derived internally from the canonical local map `Rₚ → S_q → S_q^h`, while the comparison
  `Rₚ^h → S_q^h` itself must be the canonical owner map `henselizationMap`;
- primitive data: the henselization owners on `R_p` and `S_q`, the canonical local map
  `R_p → S_q`, and the source-facing quasi-finite package at `q`;
- derived API: the canonical comparison `henselizationMap : R_p^h → S_q^h`, its finiteness
  property, and the tensor-localization owner theorem already provided upstream by Lemma
  `10.155.8`.

Source/core/bridge triage:
- `source-facing`: the quasi-finite finiteness of the induced map `R_p^h → S_q^h`;
- `core/canonical`: `IsHenselizationOf`, `henselizationMap`, and
  `isHenselizationOf_localizationAt_henselizationTensorPrime`;
- `bridge/view`: the canonical comparison morphism `henselizationMap`.
-/

-- Proof sketch: after identifying `S_q^h` with the localization of `R_p^h ⊗[R_p] S_q` from
-- clause (1), apply the quasi-finite finiteness statement over the henselian base `R_p^h` to that
-- localization and then use the canonical identification of `S_q^h` with its localization at the
-- maximal ideal.
/-- Chap10 Lemma 10 156 1: under the same quasi-finite hypothesis at `q`, the canonical
comparison map `R_p^h → S_q^h` given by `henselizationMap` is finite. -/
@[stacks 05WP]
theorem henselizationMap_finite_of_quasiFiniteAt
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    RingHom.Finite comparison := by
  letI : Algebra R Rph :=
    RingHom.toAlgebra ((algebraMap Rp Rph).comp (algebraMap R Rp))
  letI : IsScalarTower R Rp Rph :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Rp Sqh :=
    RingHom.toAlgebra ((algebraMap Sq Sqh).comp (algebraMap Rp Sq))
  letI : IsScalarTower Rp Sq Sqh :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R Sqh :=
    RingHom.toAlgebra ((algebraMap Rp Sqh).comp (algebraMap R Rp))
  letI : IsScalarTower R Rp Sqh :=
    IsScalarTower.of_algebraMap_eq' rfl
  let tensorPrime : Ideal (Rph ⊗[R] S) :=
    henselizationTensorPrime (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q
  let A : Type u := Localization.AtPrime tensorPrime
  letI : Ideal.IsPrime tensorPrime := by
    dsimp [tensorPrime]
    infer_instance
  let Q : PrimeSpectrum (Rph ⊗[R] S) := ⟨tensorPrime, inferInstance⟩
  have hqfTensor : Algebra.FiniteType.QuasiFiniteAt Rph (Rph ⊗[R] S) Q.asIdeal := by
    simpa [Q, tensorPrime] using
      quasiFiniteAt_henselizationTensorPrime
        (R := R) (S := S) (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hqf
  have hleft : Ideal.comap (algebraMap Rph (Rph ⊗[R] S)) Q.asIdeal =
      maximalIdeal Rph := by
    simpa [Q, tensorPrime] using
      henselizationTensorPrime_comap_includeLeft
        (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q
  have hAfiniteModule : Module.Finite Rph A := by
    dsimp [A]
    exact moduleFinite_localizationAtPrime_of_quasiFiniteAt_over_maximalIdeal
      (R := Rph) (S := Rph ⊗[R] S) Q hleft hqfTensor
  have hAfinite : RingHom.Finite (algebraMap Rph A) := by
    rw [RingHom.finite_algebraMap]
    exact hAfiniteModule
  letI : HenselianLocalRing A := by
    dsimp [A]
    exact localizationAtPrime_henselianLocalRing_of_quasiFiniteAt_over_maximalIdeal
      (R := Rph) (S := Rph ⊗[R] S) Q hleft hqfTensor
  letI : Algebra A Sqh := by
    dsimp [A]
    infer_instance
  letI : IsHenselizationOf A Sqh := by
    dsimp [A]
    simpa [tensorPrime] using
      isHenselizationOf_localizationAt_henselizationTensorPrime
        (R := R) (S := S) (Rh := Rph) (Sh := Sqh) p q
  have hSqhfinite : RingHom.Finite (algebraMap A Sqh) :=
    henselizationAlgebraMap_finite_of_henselian (A := A) (Ah := Sqh)
  have hRphA :
      algebraMap Rph A =
        (algebraMap (Rph ⊗[R] S) A).comp
          (Algebra.TensorProduct.includeLeftRingHom : Rph →+* Rph ⊗[R] S) := by
    rw [IsScalarTower.algebraMap_eq Rph (Rph ⊗[R] S) A]
    simp [Algebra.TensorProduct.algebraMap_def]
  have hfiniteComp : RingHom.Finite
      ((algebraMap A Sqh).comp
        ((algebraMap (Rph ⊗[R] S) A).comp
          (Algebra.TensorProduct.includeLeftRingHom : Rph →+* Rph ⊗[R] S))) := by
    rw [← hRphA]
    exact RingHom.Finite.comp hSqhfinite hAfinite
  -- The comparison is the finite composite through the localized tensor product.
  rw [henselizationMapRingHom_eq_tensorLocalization_comp
    (R := R) (S := S) (p := p) (q := q) (Rph := Rph) (Sqh := Sqh)]
  simpa [A, tensorPrime] using hfiniteComp

end
