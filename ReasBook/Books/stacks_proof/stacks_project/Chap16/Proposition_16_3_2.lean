import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_136_1
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Lemma_10_136_4
import stacks_proof.stacks_project.Chap10.Lemma_10_136_18
import stacks_proof.stacks_project.Chap10.Lemma_10_136_17
import stacks_proof.stacks_project.Chap10.Lemma_10_137_12
import stacks_proof.stacks_project.Chap10.Lemma_10_137_16
import stacks_proof.stacks_project.Chap10.Lemma_10_137_9
import stacks_proof.stacks_project.Chap10.Lemma_10_143_10
import stacks_proof.stacks_project.Chap15.Lemma_15_9_1
import stacks_proof.stacks_project.Chap15.Lemma_15_9_10
import stacks_proof.stacks_project.Chap15.Lemma_15_9_8
import stacks_proof.stacks_project.Chap16.Definition_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open Ideal.Quotient PrimeSpectrum Topology
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A₀ : Type v} [CommRing A₀] [Algebra (R ⧸ I) A₀]

/- Domain-style sampling for lifting smooth and syntomic quotient algebras:
* primary domain: commutative algebra of smooth and syntomic ring maps over quotient rings;
* core/canonical owners: `RingHom.Syntomic` for clause `(1)` and `Smooth (R ⧸ I) A₀` for
  clause `(2)`;
* relevant upstream declarations inspected for this owner choice:
  `RingHom.Syntomic` in `Definition_10_136_1`,
  `Algebra.Smooth` in mathlib `RingTheory/Smooth/Basic`,
  the owner-style quotient-lift theorem `exists_etale_lift_of_quotient` in
  `Lemma_10_143_10`,
  and the chartwise smooth quotient-lift theorem
  `exists_standardSmooth_lift_cover_of_quotient_smooth` in Chapter 10.

Source/core/bridge triage:
* `source-facing`: the two existence theorems below, matching Proposition `16.3.2`;
* `core/canonical`: the owner predicates `RingHom.Syntomic` and `Smooth`;
* `bridge/view`: the reduction comparison
  `(A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀`.

Primitive data are only the quotient ideal `I` and the quotient algebra `A₀` with its canonical
owner hypothesis. The reduction isomorphism is derived bridge data, so no additional wrapper
structure is introduced here.
-/

/-- Helper for Proposition 16.3.2: a ring equivalence is syntomic. -/
private theorem syntomic_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    e.toRingHom.Syntomic := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  -- Proof comment: a ring equivalence is smooth, hence syntomic, for the algebra structure coming
  -- from the equivalence itself.
  have hSmooth : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
  have hAlgSmooth : Smooth A B := by
    exact (RingHom.smooth_algebraMap).1 <| by
      simpa [RingHom.algebraMap_toAlgebra] using hSmooth
  letI : Smooth A B := hAlgSmooth
  simpa [RingHom.algebraMap_toAlgebra] using (Algebra.smooth_syntomic (R := A) (S := B))

/-- Helper for Proposition 16.3.2: if the closed fiber `V(J)` admits syntomic basic-open
neighborhoods, then one quotient-unit localization is already syntomic. -/
private theorem existsQuotientUnitAndSyntomicAwayOfZeroLocus
    {A : Type u} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (J : Ideal A)
    (hJ : ∀ q ∈ V((J : Set A)), ∃ f : A, q ∈ D(f) ∧ (algebraMap R (Localization.Away f)).Syntomic) :
    ∃ g : A, IsUnit (Ideal.Quotient.mk J g) ∧ (algebraMap R (Localization.Away g)).Syntomic := by
  have hRespectsIso :
      RingHom.RespectsIso (fun {R S} [CommRing R] [CommRing S] ↦ RingHom.Syntomic) :=
    RingHom.Syntomic.stableUnderComposition.respectsIso
      (fun {R S} _ _ e ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using
          (syntomic_of_ringEquiv (e := e)))
  have hVCompact : IsCompact (V((J : Set A))) := by
    -- Proof comment: the closed fiber is compact because it is a closed subset of `Spec(A)`.
    simpa using (isClosed_zeroLocus (J : Set A)).isCompact
  choose f hfmem hfSyntomic using fun q : V((J : Set A)) ↦ hJ q.1 q.2
  obtain ⟨t, ht⟩ :=
    hVCompact.elim_finite_subcover
      (fun q : V((J : Set A)) ↦ (D(f q) : Set (PrimeSpectrum A)))
      (fun q ↦ (D(f q)).2)
      (by
        intro q hq
        exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hfmem ⟨q, hq⟩⟩)
  let U : Set (PrimeSpectrum A) := ⋃ q : t, (D(f q.1) : Set (PrimeSpectrum A))
  have hUcompact : IsCompact U := by
    -- Proof comment: a finite union of the chosen principal opens is compact.
    simpa [U] using isCompact_iUnion fun q : t ↦ isCompact_basicOpen (f q.1)
  have hUopen : IsOpen U := by
    -- Proof comment: the same finite union remains open.
    simpa [U] using isOpen_iUnion fun q : t ↦ (D(f q.1)).2
  obtain ⟨K, -, hUeq⟩ := isCompact_isOpen_iff_ideal.mp ⟨hUcompact, hUopen⟩
  have hVU : V((J : Set A)) ⊆ U := by
    -- Proof comment: the finite family still covers every point of the closed fiber.
    intro q hq
    rcases Set.mem_iUnion₂.mp (ht hq) with ⟨x, hxt, hxq⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hxq⟩
  have hZI : V((J : Set A)) ⊆ (zeroLocus (K : Set A))ᶜ := by
    -- Proof comment: rewrite the finite union as the complement of `V(K)`.
    simpa [hUeq] using hVU
  have hdisj :
      Disjoint
        (closure (comap (RingHom.id A) '' zeroLocus (K : Set A) : Set (PrimeSpectrum A)))
        (V((J : Set A))) := by
    -- Proof comment: `V(K)` is disjoint from the closed fiber because its complement contains the
    -- finite neighborhood covering `V(J)`.
    rw [closure_image_comap_zeroLocus (RingHom.id A) K]
    exact Set.disjoint_left.2 fun q hqK hqJ ↦ (hZI hqJ) hqK
  obtain ⟨g, hgbar, hgK⟩ :=
    exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
      (RingHom.id A) J K hdisj
  have hDg : (D(g) : Set (PrimeSpectrum A)) ⊆ U := by
    -- Proof comment: the element produced by Lemma `15.9.8` cuts out a principal open inside the
    -- finite neighborhood `U`.
    rw [← hUeq, basicOpen_eq_zeroLocus_compl]
    simpa only [RingHom.id_apply] using
      Set.compl_subset_compl.mpr (zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hgK))
  let Ag : Type u := Localization.Away g
  let _ : CommRing Ag := inferInstance
  have hspan :
      Ideal.span (Set.range fun x : t ↦ algebraMap A Ag (f x.1)) = ⊤ := by
    -- Proof comment: after localizing at `g`, the finitely many inherited charts still cover
    -- `Spec(A_g)`.
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply TopologicalSpace.Opens.ext
    ext q
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
      Set.mem_univ, iff_true]
    have hqg : PrimeSpectrum.comap (algebraMap A Ag) q ∈ (D(g) : Set (PrimeSpectrum A)) := by
      rw [← PrimeSpectrum.localization_away_comap_range Ag g]
      exact ⟨q, rfl⟩
    rcases Set.mem_iUnion.mp (hDg hqg) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change q ∈
      (TopologicalSpace.Opens.comap ⟨PrimeSpectrum.comap (algebraMap A Ag),
        PrimeSpectrum.continuous_comap (algebraMap A Ag)⟩ (PrimeSpectrum.basicOpen (f x.1)) :
        Set (PrimeSpectrum Ag))
    simpa [PrimeSpectrum.comap_basicOpen] using hx
  have hloc :
      RingHom.Locally RingHom.Syntomic (algebraMap R Ag) := by
    -- Proof comment: each inherited chart of `A_g` is syntomic because it is an iterated
    -- localization of one of the original syntomic charts.
    refine RingHom.locally_of_exists hRespectsIso (algebraMap R Ag)
      (fun x : t ↦ algebraMap A Ag (f x.1)) hspan
      (fun x : t ↦ Localization.Away (algebraMap A Ag (f x.1))) ?_
    intro x
    let T₁ : Type u := Localization.Away (algebraMap A (Localization.Away (f x.1)) g)
    let T₂ : Type u := Localization.Away (algebraMap A Ag (f x.1))
    let e : T₁ ≃ₐ[R] T₂ :=
      (IsLocalization.algEquiv (Submonoid.powers (g * f x.1)) T₁ T₂).restrictScalars R
    have hLocalizeChart :
        (algebraMap (Localization.Away (f x.1)) T₁).Syntomic := by
      letI : Etale (Localization.Away (f x.1)) T₁ :=
        Algebra.Etale.of_isLocalizationAway (algebraMap A (Localization.Away (f x.1)) g)
      exact Algebra.smooth_syntomic (R := Localization.Away (f x.1)) (S := T₁)
    have hT₁ :
        (algebraMap R T₁).Syntomic := by
      have hcomp :
          (algebraMap (Localization.Away (f x.1)) T₁).comp
              (algebraMap R (Localization.Away (f x.1))) =
            algebraMap R T₁ := by
        ext r
        rfl
      exact hcomp ▸ RingHom.Syntomic.comp (hfSyntomic x.1) hLocalizeChart
    have hEquiv :
        (e.toRingEquiv.toRingHom).Syntomic :=
      syntomic_of_ringEquiv (e := e.toRingEquiv)
    have hT₂ :
        (algebraMap R T₂).Syntomic := by
      have hcomp :
          (e.toRingEquiv.toRingHom).comp (algebraMap R T₁) = algebraMap R T₂ := by
        ext r
        exact e.commutes r
      exact hcomp ▸ RingHom.Syntomic.comp hT₁ hEquiv
    simpa [Ag, RingHom.algebraMap_toAlgebra, T₂] using hT₂
  have hSyntomicAg : (algebraMap R Ag).Syntomic :=
    (RingHom.locally_iff_of_localizationSpanTarget hRespectsIso
      RingHom.Syntomic.ofLocalizationSpanTarget (algebraMap R Ag)).mp hloc
  exact ⟨g, hgbar ▸ isUnit_one, hSyntomicAg⟩

/-- Helper for Proposition 16.3.2: if the closed fiber `V(J)` lies in the smooth locus, then one
basic open still containing the closed fiber is already smooth. -/
private theorem existsQuotientUnitAndSmoothAwayOfZeroLocusSubsetSmoothLocus
    {A : Type*} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (J : Ideal A) (hJ : V((J : Set A)) ⊆ smoothLocus R A) :
    ∃ g : A, IsUnit (Ideal.Quotient.mk J g) ∧ Smooth R (Localization.Away g) := by
  have hVCompact : IsCompact (V((J : Set A))) := by
    simpa using (isClosed_zeroLocus (J : Set A)).isCompact
  have hqSmooth : ∀ q : V((J : Set A)), ∃ f : A, q.1 ∈ D(f) ∧ Smooth R (Localization.Away f) := by
    intro q
    have hq' : SmoothAtPrime R A q.1 := by
      -- Convert smooth-locus membership at the closed-fiber point into a smooth basic-open chart.
      exact (smoothAtPrime_iff_isSmoothAt R A q.1).2 <| by
        simpa [smoothLocus] using hJ q.2
    rcases hq' with ⟨f, hfq, hfSmooth⟩
    exact ⟨f, hfq, hfSmooth⟩
  choose f hfmem hfSmooth using hqSmooth
  obtain ⟨t, ht⟩ :=
    hVCompact.elim_finite_subcover
      (fun q : V((J : Set A)) ↦ (D(f q) : Set (PrimeSpectrum A)))
      (fun q ↦ (D(f q)).2)
      (by
        intro q hq
        exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hfmem ⟨q, hq⟩⟩)
  let U : Set (PrimeSpectrum A) := ⋃ q : t, (D(f q.1) : Set (PrimeSpectrum A))
  have hUcompact : IsCompact U := by
    simpa [U] using isCompact_iUnion fun q : t ↦ isCompact_basicOpen (f q.1)
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_iUnion fun q : t ↦ (D(f q.1)).2
  have hUsmooth : U ⊆ smoothLocus R A := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨x, hx⟩
    have hchart : (D(f x.1) : Set (PrimeSpectrum A)) ⊆ smoothLocus R A := by
      rw [basicOpen_subset_smoothLocus_iff_smooth]
      exact hfSmooth x.1
    exact hchart hx
  obtain ⟨K, -, hUeq⟩ := isCompact_isOpen_iff_ideal.mp ⟨hUcompact, hUopen⟩
  have hVU : V((J : Set A)) ⊆ U := by
    intro q hq
    rcases Set.mem_iUnion₂.mp (ht hq) with ⟨x, hxt, hxq⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hxq⟩
  have hZI : V((J : Set A)) ⊆ (zeroLocus (K : Set A))ᶜ := by
    simpa [hUeq] using hVU
  have hdisj :
      Disjoint
        (closure (comap (RingHom.id A) '' zeroLocus (K : Set A) : Set (PrimeSpectrum A)))
        (V((J : Set A))) := by
    rw [closure_image_comap_zeroLocus (RingHom.id A) K]
    exact Set.disjoint_left.2 fun q hqK hqJ ↦ (hZI hqJ) hqK
  obtain ⟨g, hgbar, hgK⟩ :=
    exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
      (RingHom.id A) J K hdisj
  have hDg : (D(g) : Set (PrimeSpectrum A)) ⊆ U := by
    rw [← hUeq, basicOpen_eq_zeroLocus_compl]
    simpa only [RingHom.id_apply] using
      Set.compl_subset_compl.mpr (zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hgK))
  have hDgSmooth : (D(g) : Set (PrimeSpectrum A)) ⊆ smoothLocus R A := by
    intro q hq
    exact hUsmooth (hDg hq)
  refine ⟨g, hgbar ▸ isUnit_one, ?_⟩
  -- The chosen principal open lies inside the smooth locus, so the away-localization is smooth.
  exact (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := A) (f := g)).mp hDgSmooth

/-- Helper for Proposition 16.3.2: the direct product-localization carries the canonical
`A[g]`-algebra structure from the away-to-away map. -/
private noncomputable instance awayChartMulAlgebra
    {A : Type*} [CommRing A] (g t : A) :
    Algebra (Localization.Away g) (Localization.Away (g * t)) :=
  (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away g)
    (P := Localization.Away (g * t))
    g t).toAlgebra

/-- Helper for Proposition 16.3.2: the product-localization realizes the scalar tower
`A → A[g] → A[g * t]`. -/
private instance awayChartMulScalarTower
    {A : Type*} [CommRing A] (g t : A) :
    IsScalarTower A (Localization.Away g) (Localization.Away (g * t)) :=
  IsScalarTower.of_algebraMap_eq' <|
    RingHom.ext fun a ↦ by
      simpa using
        (IsLocalization.Away.awayToAwayRight_eq
          (S := Localization.Away g)
          (P := Localization.Away (g * t))
          g t a).symm

/-- Helper for Proposition 16.3.2: the direct localization `A[g * t]` is the away-localization of
the `g`-chart at the image of `t`. -/
private theorem awayChart_isLocalizationAway_mul
    {A : Type*} [CommRing A] (g t : A) :
    IsLocalization.Away (algebraMap A (Localization.Away g) t) (Localization.Away (g * t)) := by
  let B := Localization.Away g
  let D := Localization.Away (algebraMap A B t)
  let _ : IsScalarTower A B D := inferInstance
  let φA : D ≃ₐ[A] Localization.Away (g * t) :=
    IsLocalization.algEquiv (Submonoid.powers (g * t)) D (Localization.Away (g * t))
  let φB : D ≃ₐ[B] Localization.Away (g * t) :=
    { φA with
      commutes' := by
        have hmaps :
            ((φA : D →+* Localization.Away (g * t)).comp (algebraMap B D)) =
              algebraMap B (Localization.Away (g * t)) := by
          apply IsLocalization.ringHom_ext (Submonoid.powers g)
          ext a
          have hbaseD :
              algebraMap B D (algebraMap A B a) = algebraMap A D a := by
            simpa [B] using congrArg (fun ψ : A →+* D ↦ ψ a)
              (IsScalarTower.algebraMap_eq A B D)
          have hbaseGT :
              algebraMap B (Localization.Away (g * t)) (algebraMap A B a) =
                algebraMap A (Localization.Away (g * t)) a := by
            simpa [B] using
              (congrArg (fun ψ : A →+* Localization.Away (g * t) ↦ ψ a)
                (IsScalarTower.algebraMap_eq A B (Localization.Away (g * t)))).symm
          simp only [RingHom.comp_apply]
          calc
            φA (algebraMap B D (algebraMap A B a)) = φA (algebraMap A D a) := by rw [hbaseD]
            _ = algebraMap A (Localization.Away (g * t)) a := by simpa using φA.commutes a
            _ = algebraMap B (Localization.Away (g * t)) (algebraMap A B a) := by rw [hbaseGT]
        intro b
        exact congrArg (fun ψ : B →+* Localization.Away (g * t) ↦ ψ b) hmaps }
  -- Proof comment: transport the canonical iterated-localization structure across the
  -- direct-vs-iterated algebra equivalence.
  simpa [B, D] using
    (IsLocalization.isLocalization_of_algEquiv
      (M := Submonoid.powers (algebraMap A B t))
      (S := D)
      (P := Localization.Away (g * t))
      φB)

/-- Helper for Proposition 16.3.2: further localizing a syntomic away-localization stays
syntomic. -/
private theorem syntomic_localizationAway_mul
    {A : Type*} [CommRing A] [Algebra R A] (g t : A)
    (hg : (algebraMap R (Localization.Away g)).Syntomic) :
    (algebraMap R (Localization.Away (g * t))).Syntomic := by
  letI :
      IsLocalization.Away
        (algebraMap A (Localization.Away g) t)
        (Localization.Away (g * t)) := by
    -- Proof comment: rewrite the direct product-localization as the away-localization of the
    -- `g`-chart at the image of `t`.
    simpa [mul_comm] using awayChart_isLocalizationAway_mul (g := g) (t := t)
  letI : Etale (Localization.Away g) (Localization.Away (g * t)) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap A (Localization.Away g) t)
  letI : IsScalarTower R (Localization.Away g) (Localization.Away (g * t)) :=
    IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun r ↦ by
        simpa [awayChartMulAlgebra, IsScalarTower.algebraMap_eq R A (Localization.Away g),
          IsScalarTower.algebraMap_eq R A (Localization.Away (g * t))] using
          (IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away g)
            (P := Localization.Away (g * t))
            g t (algebraMap R A r)).symm
  have hLocal :
      (algebraMap (Localization.Away g) (Localization.Away (g * t))).Syntomic :=
    -- Proof comment: every away-localization of the `g`-chart is smooth, hence syntomic.
    Algebra.smooth_syntomic (R := Localization.Away g) (S := Localization.Away (g * t))
  have hcomp :
      (algebraMap (Localization.Away g) (Localization.Away (g * t))).comp
          (algebraMap R (Localization.Away g)) =
        algebraMap R (Localization.Away (g * t)) := by
    -- Proof comment: the direct map `R → A[g * t]` factors through the intermediate `g`-chart.
    ext r
    simpa using
      (congrArg (fun ψ : R →+* Localization.Away (g * t) ↦ ψ r)
        (IsScalarTower.algebraMap_eq R (Localization.Away g) (Localization.Away (g * t)))).symm
  exact hcomp ▸ RingHom.Syntomic.comp hg hLocal

/-- Helper for Proposition 16.3.2: further localizing a smooth away-localization stays smooth. -/
private theorem smooth_localizationAway_mul
    {A : Type*} [CommRing A] [Algebra R A] (g t : A)
    (hg : Smooth R (Localization.Away g)) :
    Smooth R (Localization.Away (g * t)) := by
  letI :
      IsLocalization.Away
        (algebraMap A (Localization.Away g) t)
        (Localization.Away (g * t)) := by
    -- Proof comment: replace the direct product-localization by the standard iterated
    -- away-localization of the `g`-chart.
    simpa [mul_comm] using awayChart_isLocalizationAway_mul (g := g) (t := t)
  letI : IsScalarTower R (Localization.Away g) (Localization.Away (g * t)) :=
    IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun r ↦ by
        simpa [awayChartMulAlgebra, IsScalarTower.algebraMap_eq R A (Localization.Away g),
          IsScalarTower.algebraMap_eq R A (Localization.Away (g * t))] using
          (IsLocalization.Away.awayToAwayRight_eq
            (S := Localization.Away g)
            (P := Localization.Away (g * t))
            g t (algebraMap R A r)).symm
  letI : Smooth (Localization.Away g) (Localization.Away (g * t)) :=
    Smooth.of_isLocalization_Away (algebraMap A (Localization.Away g) t)
  -- Proof comment: compose the original smooth `g`-chart with the new localization step.
  exact Smooth.comp R (Localization.Away g) (Localization.Away (g * t))

/-- Helper for Proposition 16.3.2: if a prime `p` of `R` contains `I`, then its residue field
inherits the canonical quotient algebra structure over `R ⧸ I`. -/
private noncomputable abbrev residueFieldQuotientAlgebra
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) :
    Algebra (R ⧸ I) p.asIdeal.ResidueField :=
  RingHom.toAlgebra <|
    Ideal.Quotient.lift I (algebraMap R p.asIdeal.ResidueField) fun a ha ↦ by
      -- Proof comment: elements of `I` vanish in the residue field because `I ⊆ p`.
      simpa [Ideal.algebraMap_quotient_residueField_mk] using (hpI ha : a ∈ p.asIdeal)

/-- Helper for Proposition 16.3.2: after base change from `R ⧸ I` to the residue field of a prime
`p ⊇ I`, the reduction `A / IA` identifies with the usual closed fiber of `A` at `p`. -/
private noncomputable abbrev closedFiberModIdealAlgEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) := by
  let _ : Algebra (R ⧸ I) p.asIdeal.ResidueField :=
    residueFieldQuotientAlgebra (I := I) p hpI
  letI : IsScalarTower R (R ⧸ I) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  -- Proof comment: first rewrite `A / IA` as the canonical quotient tensor model over `R ⧸ I`,
  -- then cancel the redundant middle base change.
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I)).trans <|
      Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) p.asIdeal.ResidueField
        p.asIdeal.ResidueField A

/-- Helper for Proposition 16.3.2: smoothness of the reduction modulo `I` makes each closed-fiber
prime of a syntomic lift smooth on the corresponding fiber ring. -/
private theorem fiberSmoothAtPrime_of_smoothReduction
    {A : Type*} [CommRing A] [Algebra R A]
    (e : (A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀)
    [Smooth (R ⧸ I) A₀]
    (q : PrimeSpectrum A)
    (hq : q ∈ V((Ideal.map (algebraMap R A) I : Set A))) :
    SmoothAtPrime (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber A)
      (fiberPrimeAt R A q) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  have hpI : I ≤ p.asIdeal := by
    -- Proof comment: a prime of `A` in `V(IA)` contracts to a prime of `R` containing `I`.
    intro x hx
    exact hq (Ideal.mem_map_of_mem (algebraMap R A) hx)
  let _ : Algebra (R ⧸ I) p.asIdeal.ResidueField :=
    residueFieldQuotientAlgebra (I := I) p hpI
  letI : IsScalarTower R (R ⧸ I) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  let eFiber :=
    -- Proof comment: rewrite the closed fiber as the residue-field base change of `A₀`.
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      e.symm).trans <|
      closedFiberModIdealAlgEquiv (I := I) (A := A) p hpI
  have hsmoothBase :
      Smooth p.asIdeal.ResidueField
        (TensorProduct (R ⧸ I) p.asIdeal.ResidueField A₀) := by
    -- Proof comment: smoothness survives the residue-field base change from `R ⧸ I`.
    infer_instance
  have hsmoothFiber : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber A) := by
    -- Proof comment: transport the smooth base-changed model back to the actual fiber ring.
    letI :
        Smooth p.asIdeal.ResidueField
          (TensorProduct (R ⧸ I) p.asIdeal.ResidueField A₀) := hsmoothBase
    exact Smooth.of_equiv eFiber
  letI : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber A) := hsmoothFiber
  -- Proof comment: every prime of a smooth algebra is smooth, in particular the canonical fiber
  -- prime above `q`.
  exact
    (smooth_iff_forall_smoothAtPrime (R := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber A)).1
      inferInstance (fiberPrimeAt R A q)

/-- Helper for Proposition 16.3.2: a finite presentation of `A₀` over `R ⧸ I` lifts to one
global `R`-model whose reduction modulo `I` is canonically `A₀`. -/
private theorem presentationModelLiftOfQuotient
    {ι : Type*} {σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation (R ⧸ I) A₀ ι σ) :
    let Rbar : Type u := R ⧸ I
    letI : Algebra R A₀ :=
      RingHom.toAlgebra ((algebraMap Rbar A₀).comp (Ideal.Quotient.mk I))
    letI : IsScalarTower R Rbar A₀ := IsScalarTower.of_algebraMap_eq' rfl
    letI : P.HasCoeffs R := presentation_hasCoeffs_of_quotient (R := R) (I := I) P
    FinitePresentation R (P.ModelOfHasCoeffs R) ∧
      Nonempty
        ((P.ModelOfHasCoeffs R ⧸ Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) ≃ₐ[R ⧸ I] A₀) := by
  let Rbar : Type u := R ⧸ I
  letI : Algebra R A₀ :=
    RingHom.toAlgebra ((algebraMap Rbar A₀).comp (Ideal.Quotient.mk I))
  letI : IsScalarTower R Rbar A₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : P.HasCoeffs R := presentation_hasCoeffs_of_quotient (R := R) (I := I) P
  constructor
  · -- Proof comment: descend the presentation coefficients from `R ⧸ I` to `R`.
    simpa [Rbar] using
      (Presentation.finitePresentation_modelOfHasCoeffs_base
        (R := R) (S := Rbar) (P := A₀) (A0 := R) P)
  · -- Proof comment: the descended presentation reduces back to the original quotient algebra.
    exact ⟨reduced_presentation_quotient_equiv (R := R) (I := I) (Sbar := A₀) P⟩

/-- Helper for Proposition 16.3.2: every prime of `A₀` lies on a basic-open chart whose lift over
`R` is a relative global complete intersection. -/
private theorem chartDataAtClosedFiberPrime
    (hA₀ : (algebraMap (R ⧸ I) A₀).Syntomic)
    (q₀ : PrimeSpectrum A₀) :
    ∃ g : A₀, q₀ ∈ D(g) ∧
      ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
  classical
  obtain ⟨s, hsTop, hs⟩ :=
    exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic
      (R := R) (I := I) (Sbar := A₀) hA₀
  have hgExists : ∃ g ∈ s, g ∉ q₀.asIdeal := by
    by_contra hgExists
    have hsq : ∀ g ∈ s, g ∈ q₀.asIdeal := by
      intro g hg
      by_contra hgq
      exact hgExists ⟨g, hg, hgq⟩
    have hspan : Ideal.span s ≤ q₀.asIdeal := by
      rw [Ideal.span_le]
      exact hsq
    have htop : (⊤ : Ideal A₀) ≤ q₀.asIdeal := by
      simpa [hsTop] using hspan
    exact q₀.2.ne_top (le_antisymm htop le_top)
  rcases hgExists with ⟨g, hgs, hgq⟩
  rcases hs g hgs with ⟨S, _, _, hS, eS⟩
  refine ⟨g, hgq, S, inferInstance, inferInstance, hS, eS⟩

/-- Helper for Proposition 16.3.2: construct a finitely presented lift of `A₀` over `R` whose
closed fiber is locally syntomic along `V(IA)`. -/
private theorem existsLiftWithClosedFiberLocallySyntomic
    (hA₀ : (algebraMap (R ⧸ I) A₀).Syntomic) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : FinitePresentation R A),
      Nonempty ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀) ∧
        ∀ q ∈ V((Ideal.map (algebraMap R A) I : Set A)),
          ∃ f : A, q ∈ D(f) ∧ (algebraMap R (Localization.Away f)).Syntomic := by
  -- Route correction: the remaining work should stay on the presentation/equivalence surface.
  -- First pick the global model from `presentationModelLiftOfQuotient`, then transport each
  -- closed-fiber prime to `A₀`, extract chart data with `chartDataAtClosedFiberPrime`, and finally
  -- compare the corresponding localization of the global model with that lifted chart.
  sorry

/-- Helper for Proposition 16.3.2: if a syntomic lift has smooth reduction modulo `I`, then the
closed fiber is contained in the smooth locus of the lift. -/
private theorem closedFiber_subset_smoothLocus_of_smoothReduction
    {A : Type*} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (hA : (algebraMap R A).Syntomic)
    (e : (A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀)
    [Smooth (R ⧸ I) A₀] :
    V((Ideal.map (algebraMap R A) I : Set A)) ⊆ smoothLocus R A := by
  -- Route correction: the intended proof transports smoothness of the quotient algebra to the
  -- closed fiber via `closedFiberModIdealAlgEquiv`, then applies Lemma `10.137.16` primewise.
  intro q hq
  have hfp : ∃ g : A, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g) := by
    -- Proof comment: global finite presentation already gives the local witness with `g = 1`.
    refine ⟨1, ?_, inferInstance⟩
    intro h1
    have htop : q.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem q.asIdeal h1 isUnit_one
    exact (Ideal.IsPrime.ne_top (I := q.asIdeal) inferInstance) htop
  have hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl).Flat := by
    -- Proof comment: flatness localizes from the syntomic map `R → A`.
    exact RingHom.Flat.localRingHom hA.flat q.asIdeal (q.asIdeal.under R) rfl
  have hqSmoothAt : SmoothAtPrime R A q := by
    -- Proof comment: apply the Chapter 10 local criterion using the transported smooth fiber.
    exact
      Algebra.smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
        q hfp hflat
        (fiberSmoothAtPrime_of_smoothReduction (I := I) (A₀ := A₀) (A := A) e q hq)
  -- Proof comment: convert the source-facing smoothness-at-prime statement into smooth-locus
  -- membership.
  simpa [smoothLocus] using (smoothAtPrime_iff_isSmoothAt R A q).mp hqSmoothAt

/-- Helper for Proposition 16.3.2: localizing at an element equal to `1` modulo the extended ideal
preserves the closed-fiber quotient equivalence. -/
private theorem quotientEquiv_afterLocalizingEqOneModMappedIdeal
    {A : Type*} [CommRing A] [Algebra R A]
    (e : (A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀)
    {s : A} (hs : Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) s = 1) :
    Nonempty (((Localization.Away s) ⧸ Ideal.map (algebraMap R (Localization.Away s)) I) ≃ₐ[R ⧸ I] A₀) := by
  let J : Ideal A := Ideal.map (algebraMap R A) I
  let eLoc : (A ⧸ J) ≃ₐ[A ⧸ J]
      ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) J) :=
    quotientAlgEquiv_localizationAway_of_eq_one_mod_ideal (A := A) (I := J) hs
  have hMap :
      Ideal.map (algebraMap A (Localization.Away s)) J =
        Ideal.map (algebraMap R (Localization.Away s)) I := by
    -- Proof comment: extending `I` first to `A` and then to `A_s` agrees with extending `I`
    -- directly to `A_s`.
    simpa [J, IsScalarTower.algebraMap_eq R A (Localization.Away s)] using
      (Ideal.map_map (f := algebraMap R A) (g := algebraMap A (Localization.Away s)) (I := I))
  let T₁ :=
    ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) J)
  let T₀ :=
    ((Localization.Away s) ⧸ Ideal.map (algebraMap R (Localization.Away s)) I)
  letI : Algebra (R ⧸ I) T₁ :=
    ((algebraMap (A ⧸ J) T₁).comp (algebraMap (R ⧸ I) (A ⧸ J))).toAlgebra
  letI : IsScalarTower (R ⧸ I) (A ⧸ J) T₁ := IsScalarTower.of_algebraMap_eq' rfl
  let eMap : T₀ ≃ₐ[R ⧸ I] T₁ :=
    { (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap).symm with
      commutes' := by
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        apply (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap).injective
        have hleft :
            (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap)
                ((Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap).symm
                  ((algebraMap (R ⧸ I) T₀) ((Ideal.Quotient.mk I) r))) =
              (algebraMap (R ⧸ I) T₀) ((Ideal.Quotient.mk I) r) :=
          (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap).apply_symm_apply
            ((algebraMap (R ⧸ I) T₀) ((Ideal.Quotient.mk I) r))
        calc
          (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap)
              ((Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap).symm.toFun
                ((algebraMap (R ⧸ I) T₀) ((Ideal.Quotient.mk I) r))) =
              (algebraMap (R ⧸ I) T₀) ((Ideal.Quotient.mk I) r) := by
                simpa using hleft
          _ = (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap)
                ((algebraMap (R ⧸ I) T₁) ((Ideal.Quotient.mk I) r)) := by
                  change
                    Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.Away s)) I)
                        (algebraMap R (Localization.Away s) r) =
                      (Ideal.quotientEquivAlgOfEq (Localization.Away s) hMap)
                        (Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.Away s)) J)
                          (algebraMap A (Localization.Away s) (algebraMap R A r)))
                  rw [Ideal.quotientEquivAlgOfEq_mk]
                  simpa [IsScalarTower.algebraMap_eq R A (Localization.Away s)] }
  -- Proof comment: first identify the localized closed fiber with the original one, then compose
  -- with the given reduction equivalence to `A₀`.
  exact ⟨eMap.trans ((eLoc.restrictScalars (R ⧸ I)).symm.trans e)⟩

-- Proof sketch: use the local complete intersection description of syntomic algebras over the
-- quotient `R ⧸ I`, lift a suitable complete-intersection presentation to a syntomic `R`-algebra,
-- and then shrink near `V (IA)` so that the reduction modulo `I` remains isomorphic to `A₀`.
/-- Proposition 16.3.2 (1): every syntomic algebra over the quotient ring `R ⧸ I` lifts to a
syntomic `R`-algebra whose reduction modulo `I` is isomorphic to the given algebra. -/
@[stacks 07M8]
theorem exists_syntomic_lift_of_quotient
    (hA₀ : (algebraMap (R ⧸ I) A₀).Syntomic) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A)
      (_ : (algebraMap R A).Syntomic),
      Nonempty ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀) := by
  let Rbar : Type u := R ⧸ I
  obtain ⟨A, _, _, _, e, hloc⟩ := existsLiftWithClosedFiberLocallySyntomic
    (I := I) (A₀ := A₀) hA₀
  let J : Ideal A := Ideal.map (algebraMap R A) I
  obtain ⟨g, hgUnit, hgSyntomic⟩ :=
    existsQuotientUnitAndSyntomicAwayOfZeroLocus (R := R) (A := A) (J := J) hloc
  rcases hgUnit with ⟨u, hu⟩
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : A ⧸ J)
  let s : A := g * t
  have hs : Ideal.Quotient.mk J s = 1 := by
    -- Proof comment: replace the closed-fiber unit `g` by a congruent element `s` that is
    -- literally `1` modulo `J`, so the quotient-localization comparison applies directly.
    calc
      Ideal.Quotient.mk J s = Ideal.Quotient.mk J g * Ideal.Quotient.mk J t := by
        simp [s]
      _ = ↑u * ↑(u⁻¹) := by rw [hu, ht]
      _ = 1 := by simp
  have hsSyntomic : (algebraMap R (Localization.Away s)).Syntomic := by
    -- Proof comment: one more localization inside the chosen syntomic chart remains syntomic.
    simpa [s] using
      syntomic_localizationAway_mul (R := R) (A := A) (g := g) (t := t) hgSyntomic
  let S := Localization.Away s
  let T : Type (max u v) := ULift.{v} S
  letI : CommRing T := inferInstance
  letI : Algebra R T := inferInstance
  let fUL : S →ₐ[R] T :=
    { toRingHom :=
        { toFun := ULift.up
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      commutes' := fun _ ↦ rfl }
  have hfUL : Function.Bijective fUL := by
    constructor
    · intro x y hxy
      exact congrArg ULift.down hxy
    · intro y
      refine ⟨y.down, ?_⟩
      cases y
      rfl
  let eUL : S ≃ₐ[R] T := AlgEquiv.ofBijective fUL hfUL
  have hSyntomicT : (algebraMap R T).Syntomic := by
    have hEquiv : (eUL.toRingEquiv.toRingHom).Syntomic :=
      syntomic_of_ringEquiv (e := eUL.toRingEquiv)
    have hcomp : (eUL.toRingEquiv.toRingHom).comp (algebraMap R S) = algebraMap R T := by
      ext r
      rfl
    exact hcomp ▸ RingHom.Syntomic.comp hsSyntomic hEquiv
  have hquotS :
      Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[Rbar] A₀) :=
    quotientEquiv_afterLocalizingEqOneModMappedIdeal (I := I) (A₀ := A₀)
      (A := A) (Classical.choice e) hs
  have hULmap :
      Ideal.map (algebraMap R S) I =
        (Ideal.map (algebraMap R T) I).map (eUL.symm : T →+* S) := by
    calc
      Ideal.map (algebraMap R S) I
          = Ideal.map (((eUL.symm : T →+* S).comp (algebraMap R T))) I := by
              congr 1
              ext r
              simpa using eUL.symm.commutes r
      _ = (Ideal.map (algebraMap R T) I).map (eUL.symm : T →+* S) := by
            rw [Ideal.map_map]
  let eULquotR :
      (T ⧸ Ideal.map (algebraMap R T) I) ≃ₐ[R] (S ⧸ Ideal.map (algebraMap R S) I) :=
    Ideal.quotientEquivAlg _ _ eUL.symm hULmap
  let eULquot :
      (T ⧸ Ideal.map (algebraMap R T) I) ≃ₐ[Rbar] (S ⧸ Ideal.map (algebraMap R S) I) :=
    { __ := eULquotR
      commutes' := by
        rintro ⟨r⟩
        change Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (eUL.symm (algebraMap R T r)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (algebraMap R S r)
        exact congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (eUL.symm.commutes r) }
  -- Proof comment: `ULift` moves the final localization into the exported universe, and the
  -- quotient comparison follows by transporting the localized reduction equivalence across that
  -- algebra equivalence.
  refine ⟨T, inferInstance, inferInstance, hSyntomicT, ?_⟩
  rcases hquotS with ⟨eS⟩
  exact ⟨eULquot.trans eS⟩

-- Proof sketch: first apply clause `(1)` to obtain a syntomic lift over `R`; then use the
-- canonical owner theorem `smooth_syntomic` to view the quotient algebra as syntomic, and then
-- use the openness of the smooth locus to localize the resulting lift so that it becomes smooth
-- while preserving the reduction modulo `I`.
/-- Proposition 16.3.2 (2): every smooth algebra over the quotient ring `R ⧸ I` lifts to a smooth
`R`-algebra whose reduction modulo `I` is isomorphic to the given algebra. -/
@[stacks 07M8]
theorem exists_smooth_lift_of_quotient [Smooth (R ⧸ I) A₀] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Smooth R A),
      Nonempty ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀) := by
  have hA₀Syntomic : (algebraMap (R ⧸ I) A₀).Syntomic :=
    Algebra.smooth_syntomic (R := R ⧸ I) (S := A₀)
  obtain ⟨A, _, _, hA, e⟩ := exists_syntomic_lift_of_quotient (I := I) (A₀ := A₀) hA₀Syntomic
  let _ : FinitePresentation R A := (RingHom.finitePresentation_algebraMap.mp hA.finitePresentation)
  let J : Ideal A := Ideal.map (algebraMap R A) I
  have hClosed :
      V((J : Set A)) ⊆ smoothLocus R A :=
    closedFiber_subset_smoothLocus_of_smoothReduction (I := I) (A₀ := A₀) hA (Classical.choice e)
  obtain ⟨g, hgUnit, hgSmooth⟩ :=
    existsQuotientUnitAndSmoothAwayOfZeroLocusSubsetSmoothLocus (R := R) (J := J) hClosed
  rcases hgUnit with ⟨u, hu⟩
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : A ⧸ J)
  let s : A := g * t
  have hs : Ideal.Quotient.mk J s = 1 := by
    -- Proof comment: replace the closed-fiber unit `g` by an element congruent to `1` modulo `J`
    -- so that the quotient comparison from Lemma `15.9.10` applies directly.
    calc
      Ideal.Quotient.mk J s = Ideal.Quotient.mk J g * Ideal.Quotient.mk J t := by
        simp [s]
      _ = ↑u * ↑(u⁻¹) := by rw [hu, ht]
      _ = 1 := by simp
  have hsSmooth : Smooth R (Localization.Away s) := by
    -- Proof comment: one more localization inside a smooth chart remains smooth.
    simpa [s] using
      smooth_localizationAway_mul (R := R) (g := g) (t := t) hgSmooth
  -- Proof comment: the final localization still reduces to `A₀` because `s` is `1` modulo `IA`.
  exact
    ⟨Localization.Away s, inferInstance, inferInstance, hsSmooth,
      quotientEquiv_afterLocalizingEqOneModMappedIdeal (I := I) (A₀ := A₀)
        (A := A) (Classical.choice e) hs⟩

end

end Algebra
