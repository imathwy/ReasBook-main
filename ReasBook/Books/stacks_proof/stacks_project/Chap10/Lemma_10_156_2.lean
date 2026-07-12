import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_1
import StacksProject_2024.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and quotient rings at the closed
  point;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `Ideal.Quotient.nontrivial`,
  `isLocalHom_of_le_jacobson_bot`,
  `IsLocalRing.le_maximalIdeal`,
  `IsLocalRing.of_surjective'`;
- best owner abstraction: the main result stays source-facing as a quotient theorem for the owner
  `IsHenselizationOf`, while the local-ring structure on `R ⧸ I` is derived API belonging under
  the owner namespace `IsLocalRing`;
- primitive data: the henselization owner on `R → Rh` and the properness hypothesis `I ≠ ⊤`;
- derived API: the induced local-ring structure on `R ⧸ I` and the inclusion
  `I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI`.

Source/core/bridge triage:
- `source-facing`: `henselization_quotient_isHenselizationOf_quotient`;
- `core/canonical`: `IsHenselizationOf`, `HenselianLocalRing`, `IsLocalHom`;
- `bridge/view`: `IsLocalRing.quotient`.
-/

namespace IsLocalRing

-- Proof sketch: if `I ≠ ⊤`, then `R ⧸ I` is nontrivial by `Ideal.Quotient.nontrivial`; the
-- quotient map `R → R ⧸ I` is surjective, so `IsLocalRing.of_surjective'` transports the
-- local-ring structure.
/-- The quotient of a local ring by a proper ideal is again a local ring. -/
theorem quotient (I : Ideal R) (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) := by
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

end IsLocalRing

end

section

variable {R Rh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

namespace HenselianLocalRing

/-- Helper for Chap10 Lemma 10 156 2: a quotient of a henselian local ring by a proper ideal is
again henselian local. -/
theorem quotient {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) : HenselianLocalRing (A ⧸ I) := by
  let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  refine HenselianLocalRing.mk ?_
  intro f hf a₀ ha₀ hderiv
  obtain ⟨a₀', rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hflifts : f ∈ Polynomial.lifts q := by
    -- Proof comment: lift the polynomial coefficients through the quotient map before applying
    -- henselianity upstairs.
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective q Ideal.Quotient.mk_surjective f
  obtain ⟨g, hgmap, _hgdeg, hgmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hflifts hf
  have hcomap :
      Ideal.comap q (maximalIdeal (A ⧸ I)) = maximalIdeal A :=
    ((local_hom_TFAE q).out 0 4 rfl rfl).mp inferInstance
  have heval_mem : Polynomial.eval a₀' g ∈ maximalIdeal A := by
    -- Proof comment: the lifted value lies in the source maximal ideal because its quotient lies
    -- in the quotient maximal ideal.
    have hqeval :
        q (Polynomial.eval a₀' g) ∈ maximalIdeal (A ⧸ I) := by
      have hqeval_eq :
          q (Polynomial.eval a₀' g) = Polynomial.eval (q a₀') f := by
        rw [← hgmap]
        simp [q]
      simpa [hqeval_eq] using ha₀
    rw [← hcomap]
    exact hqeval
  have hqderiv :
      IsUnit (q (Polynomial.eval a₀' g.derivative)) := by
    -- Proof comment: derivative evaluation commutes with the quotient lift of the polynomial.
    have hqderiv_eq :
        q (Polynomial.eval a₀' g.derivative) =
          Polynomial.eval (q a₀') (Polynomial.derivative f) := by
      rw [← hgmap, Polynomial.derivative_map]
      simp [q]
    simpa [hqderiv_eq] using hderiv
  have hderivA : IsUnit (Polynomial.eval a₀' g.derivative) :=
    (isUnit_map_iff q (Polynomial.eval a₀' g.derivative)).mp hqderiv
  obtain ⟨a, haroot, hadiff⟩ :=
    HenselianLocalRing.is_henselian g hgmonic a₀' heval_mem hderivA
  refine ⟨q a, ?_, ?_⟩
  · -- Proof comment: map the lifted root back down to the quotient polynomial.
    rw [← hgmap]
    simpa [q, Polynomial.IsRoot] using congrArg q haroot
  · -- Proof comment: the upstairs congruence modulo the maximal ideal maps to the quotient
    -- maximal ideal.
    have hqdiff :
        q (a - a₀') ∈ Ideal.map q (maximalIdeal A) :=
      Ideal.mem_map_of_mem q hadiff
    have hmap :
        Ideal.map q (maximalIdeal A) = maximalIdeal (A ⧸ I) :=
      IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
    rw [hmap] at hqdiff
    simpa [q, map_sub] using hqdiff

end HenselianLocalRing

/-- Helper for Chap10 Lemma 10 156 2: the maximal ideal of a proper quotient of a local ring is
the image of the source maximal ideal. -/
lemma maximalIdeal_quotient_eq_map {A : Type u} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
    Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) = maximalIdeal (A ⧸ I) := by
  let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
  -- Proof comment: the quotient map is surjective, so the standard local-ring image formula
  -- identifies the target maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 156 2: a compatible quotient of a local homomorphism is local
when the target quotient is proper. -/
lemma quotientMap_isLocalHom_of_le_of_ne_top
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    {I : Ideal A} {J : Ideal B} (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hJ : J ≠ ⊤) :
    IsLocalHom (Ideal.quotientMap J (algebraMap A B) hIJ) := by
  let _ : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let _ : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  refine ⟨?_⟩
  intro x hxunit
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hBunit : IsUnit (algebraMap A B a) := by
    -- Proof comment: a unit after the target quotient was already a unit in the local target.
    apply (isUnit_map_iff (Ideal.Quotient.mk J) (algebraMap A B a)).mp
    simpa [Ideal.quotientMap_mk] using hxunit
  have hAunit : IsUnit a := (isUnit_map_iff (algebraMap A B) a).mp hBunit
  exact (Ideal.Quotient.mk I).isUnit_map hAunit

namespace RingHom.IsFilteredColimitOfEtale

/-- Helper for Chap10 Lemma 10 156 2: filtered colimits of étale maps remain so after quotienting
the source and target by the image ideal. -/
theorem quotient {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A)
    (h : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u}
      (algebraMap (A ⧸ I) (B ⧸ Ideal.map (algebraMap A B) I)) := by
  let T : Type u := (A ⧸ I) ⊗[A] B
  let e : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] T :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hbase :
      RingHom.IsFilteredColimitOfEtale.{u, u, u}
        (algebraMap (A ⧸ I) T) := by
    -- Proof comment: first move ind-étaleness through the universal base change
    -- `A → A ⧸ I`.
    simpa [T] using
      RingHom.filteredColimitOfEtale_baseChange (R' := A ⧸ I) h
  let X : CommRingCat := CommRingCat.of (A ⧸ I)
  let Y : CommRingCat := CommRingCat.of T
  let Z : CommRingCat := CommRingCat.of (B ⧸ Ideal.map (algebraMap A B) I)
  let fbase : X ⟶ Y := CommRingCat.ofHom (algebraMap (A ⧸ I) T)
  let eCat : Y ≅ Z := RingEquiv.toCommRingCatIso e.symm.toRingEquiv
  have hraw :
      CategoryTheory.MorphismProperty.ind.{u, u, u + 1} CommRingCat.etale
        fbase := by
    -- Proof comment: work at the raw `ind etale` owner, where postcomposition by an isomorphism
    -- is built into `RespectsIso`.
    simpa [fbase] using
      (RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale
        (R := A ⧸ I) (A := T)).2 hbase
  have hpost :
      CategoryTheory.MorphismProperty.ind.{u, u, u + 1} CommRingCat.etale
        (fbase ≫ eCat.hom) := by
    exact MorphismProperty.RespectsIso.postcomp
      (P := CategoryTheory.MorphismProperty.ind CommRingCat.etale)
      eCat.hom fbase hraw
  have hmap :
      fbase ≫ eCat.hom =
        CommRingCat.ofHom (algebraMap (A ⧸ I) (B ⧸ Ideal.map (algebraMap A B) I)) := by
    -- Proof comment: the tensor-product quotient equivalence is an algebra equivalence over
    -- `A ⧸ I`, so its inverse carries the tensor structural map to the quotient structural map.
    ext x
    change e.symm ((algebraMap A (A ⧸ I) x) ⊗ₜ[A] (1 : B)) =
      algebraMap A (B ⧸ Ideal.map (algebraMap A B) I) x
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [AlgEquiv.symm_apply_eq]
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ Ideal.map (algebraMap A B) I)]
    rw [Ideal.Quotient.algebraMap_eq (Ideal.map (algebraMap A B) I)]
    change 1 ⊗ₜ[A] (algebraMap A B) x =
      e (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) (algebraMap A B x))
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk
      (B := B) (I := I) (algebraMap A B x)).symm
  rw [hmap] at hpost
  exact (RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale
    (R := A ⧸ I) (A := B ⧸ Ideal.map (algebraMap A B) I)).1 hpost

end RingHom.IsFilteredColimitOfEtale

/-- Helper for Chap10 Lemma 10 156 2: quotienting a local ring by a proper ideal does not change
its residue field. -/
lemma residueField_map_quotient_mk_bijective {A : Type u} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
    let _ : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Function.Bijective (ResidueField.map (Ideal.Quotient.mk I)) := by
  let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  constructor
  · -- Proof comment: residue fields are fields, so any nonzero ring map out of one is injective.
    exact RingHom.injective (ResidueField.map q)
  · intro y
    -- Proof comment: lift a target residue class first to the quotient ring and then to the
    -- original ring.
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue A a, rfl⟩

/-- Helper for Chap10 Lemma 10 156 2: a residue-field bijection remains a bijection after
passing to compatible proper quotients. -/
lemma residueField_map_quotient_bijective
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    {I : Ideal A} {J : Ideal B}
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J) (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    (hqLocal : IsLocalHom (Ideal.quotientMap J (algebraMap A B) hIJ))
    (hf : Function.Bijective (ResidueField.map (algebraMap A B))) :
    let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
    let _ : IsLocalRing (B ⧸ J) := IsLocalRing.quotient J hJ
    let _ : IsLocalHom (Ideal.quotientMap J (algebraMap A B) hIJ) := hqLocal
    Function.Bijective (ResidueField.map (Ideal.quotientMap J (algebraMap A B) hIJ)) := by
  let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
  let _ : IsLocalRing (B ⧸ J) := IsLocalRing.quotient J hJ
  let qA : A →+* A ⧸ I := Ideal.Quotient.mk I
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  let qAB : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J (algebraMap A B) hIJ
  let _ : IsLocalHom qA := IsLocalHom.of_surjective qA Ideal.Quotient.mk_surjective
  let _ : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let _ : IsLocalHom qAB := hqLocal
  have hqA : Function.Bijective (ResidueField.map qA) :=
    residueField_map_quotient_mk_bijective I hI
  have hqB : Function.Bijective (ResidueField.map qB) :=
    residueField_map_quotient_mk_bijective J hJ
  have hring :
      qAB.comp qA = qB.comp (algebraMap A B) := by
    -- Proof comment: this is the defining square for the induced quotient map.
    ext a
    simp [qA, qB, qAB, Ideal.quotientMap_mk]
  have hres :
      (ResidueField.map qAB).comp (ResidueField.map qA) =
        (ResidueField.map qB).comp (ResidueField.map (algebraMap A B)) := by
    -- Proof comment: pass the quotient square to residue fields.
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    simp [ResidueField.map_residue, qA, qB, qAB, Ideal.quotientMap_mk]
  have hcomp :
      Function.Bijective
        ((ResidueField.map qAB) ∘ (ResidueField.map qA)) := by
    have hright :
        Function.Bijective
          ((ResidueField.map qB) ∘ (ResidueField.map (algebraMap A B))) :=
      hqB.comp hf
    simpa [RingHom.comp_apply, Function.comp_def, hres] using hright
  exact (Function.Bijective.of_comp_iff (ResidueField.map qAB) hqA).mp hcomp

-- Proof sketch: apply the quotient case of the henselization comparison from Lemma `10.156.1` to
-- the surjective local map `R → R ⧸ I`. The quotient `Rh ⧸ Ideal.map (algebraMap R Rh) I`
-- inherits the filtered-colimit-of-étale, local, maximal-ideal, and residue-field conditions, so
-- it is a henselization of `R ⧸ I`.
/-- Chap10 Lemma 10 156 2: if `Rh` is a henselization of the local ring `R` and `I` is a proper
ideal of `R` (equivalently, in a local ring, `I ⊆ maximalIdeal R`), then the quotient
`Rh ⧸ Ideal.map (algebraMap R Rh) I` is a henselization of the quotient ring `R ⧸ I`. -/
@[stacks 05WQ]
theorem henselization_quotient_isHenselizationOf_quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) := by
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
  let J : Ideal Rh := Ideal.map (algebraMap R Rh) I
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hJle : J ≤ maximalIdeal Rh := by
    -- Proof comment: the image of `I` lands inside the image of the source maximal ideal, which
    -- is the target maximal ideal for a henselization.
    calc
      J = Ideal.map (algebraMap R Rh) I := rfl
      _ ≤ Ideal.map (algebraMap R Rh) (maximalIdeal R) := Ideal.map_mono hImax
      _ = maximalIdeal Rh := IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)
  have hJ : J ≠ ⊤ := by
    -- Proof comment: a top image ideal would force the maximal ideal of `Rh` to be top.
    intro htop
    have htop_le : (⊤ : Ideal Rh) ≤ maximalIdeal Rh := by
      simpa [htop] using hJle
    have hmax_top : maximalIdeal Rh = ⊤ := le_antisymm le_top htop_le
    exact (IsLocalRing.maximalIdeal.isMaximal Rh).ne_top hmax_top
  let _ : IsLocalRing (Rh ⧸ J) := IsLocalRing.quotient J hJ
  let _ : HenselianLocalRing (Rh ⧸ J) := HenselianLocalRing.quotient J hJ
  let q : R ⧸ I →+* Rh ⧸ J :=
    Ideal.quotientMap J (algebraMap R Rh) Ideal.le_comap_map
  have hqLocal : IsLocalHom q :=
    quotientMap_isLocalHom_of_le_of_ne_top
      (A := R) (B := Rh) (I := I) (J := J) Ideal.le_comap_map hJ
  let _ : IsLocalHom q := hqLocal
  let _ : IsLocalHom (algebraMap (R ⧸ I) (Rh ⧸ J)) := by
    simpa [q] using hqLocal
  change IsHenselizationOf (R ⧸ I) (Rh ⧸ J)
  refine
    { isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · -- Proof comment: ind-étaleness descends by base change along `R → R ⧸ I` and the canonical
    -- tensor-product quotient identification.
    exact RingHom.IsFilteredColimitOfEtale.quotient I
      (IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
  · -- Proof comment: normalize both quotient maximal ideals as images of the corresponding
    -- upstairs maximal ideals, then use the henselization maximal-ideal equality.
    change Ideal.map q (maximalIdeal (R ⧸ I)) = maximalIdeal (Rh ⧸ J)
    calc
      Ideal.map q (maximalIdeal (R ⧸ I))
          = Ideal.map q (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) := by
            rw [maximalIdeal_quotient_eq_map (A := R) I hI]
      _ = Ideal.map (q.comp (Ideal.Quotient.mk I)) (maximalIdeal R) := by
            rw [Ideal.map_map]
      _ = Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap R Rh)) (maximalIdeal R) := by
            congr 1
      _ = Ideal.map (Ideal.Quotient.mk J)
            (Ideal.map (algebraMap R Rh) (maximalIdeal R)) := by
            rw [Ideal.map_map]
      _ = Ideal.map (Ideal.Quotient.mk J) (maximalIdeal Rh) := by
            rw [IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)]
      _ = maximalIdeal (Rh ⧸ J) := maximalIdeal_quotient_eq_map (A := Rh) J hJ
  · -- Proof comment: the residue-field map on quotients is bijective by the commutative square
    -- between the two quotient maps and the original henselization residue-field bijection.
    exact residueField_map_quotient_bijective
      (A := R) (B := Rh) (I := I) (J := J) Ideal.le_comap_map hI hJ hqLocal
      (IsHenselizationOf.residueField_bijective (R := R) (S := Rh))

end
