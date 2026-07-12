import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_106_4
import StacksProject_2024.Chap10.Theorem_10_34_1_Hilbert_Nullstellensatz
import StacksProject_2024.Chap10.Lemma_10_114_5
import StacksProject_2024.Chap10.Lemma_10_140_3.LocalDimension
import StacksProject_2024.Chap10.Lemma_10_116_6
import StacksProject_2024.Chap10.Lemma_10_135_6
import StacksProject_2024.Chap10.Lemma_10_137_18
import StacksProject_2024.Chap10.Lemma_10_140_1
import StacksProject_2024.Chap10.«10_138_12_1»

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

attribute [local instance] Ideal.Quotient.field

/-- Helper for Chap10 Lemma 10 140 3: an ideal maps into the comap of its image under an algebra
equivalence. -/
private theorem ideal_le_comap_map_algEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I ≤ Ideal.comap e.toAlgHom (I.map e.toRingHom) := by
  -- Proof comment: every element of `I` maps into the image ideal, hence lies in its comap.
  intro x hx
  exact Ideal.mem_map_of_mem e.toRingHom hx

/-- Helper for Chap10 Lemma 10 140 3: the image ideal under an algebra equivalence maps back into
the original ideal under the inverse equivalence. -/
private theorem ideal_map_algEquiv_le_comap_symm {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.map e.toRingHom ≤ Ideal.comap e.symm.toAlgHom I := by
  -- Proof comment: rewrite the image ideal as the inverse-image ideal along the inverse
  -- equivalence.
  intro y hy
  change y ∈ Ideal.comap e.toRingEquiv.symm I
  rw [← Ideal.map_comap_of_equiv (I := I) e.toRingEquiv]
  exact hy

/-- Helper for Chap10 Lemma 10 140 3: the forward cotangent map induced by an algebra
equivalence. -/
private noncomputable def cotangentMapAlgEquivForward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent →ₗ[R] (I.map e.toRingHom).Cotangent :=
  I.mapCotangent (I.map e.toRingHom) e.toAlgHom (ideal_le_comap_map_algEquiv e I)

/-- Helper for Chap10 Lemma 10 140 3: the backward cotangent map induced by the inverse algebra
equivalence. -/
private noncomputable def cotangentMapAlgEquivBackward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    (I.map e.toRingHom).Cotangent →ₗ[R] I.Cotangent :=
  (I.map e.toRingHom).mapCotangent I e.symm.toAlgHom
    (ideal_map_algEquiv_le_comap_symm e I)

/-- Helper for Chap10 Lemma 10 140 3: the cotangent maps induced by an algebra equivalence are
inverse to one another. -/
private theorem cotangentMapAlgEquiv_forward_comp_backward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    cotangentMapAlgEquivForward e I ∘ₗ cotangentMapAlgEquivBackward e I = LinearMap.id := by
  -- Proof comment: check the identity on cotangent quotient generators of the image ideal.
  ext y
  obtain ⟨y, rfl⟩ := (I.map e.toRingHom).toCotangent_surjective y
  rw [LinearMap.comp_apply]
  unfold cotangentMapAlgEquivForward cotangentMapAlgEquivBackward
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
  apply (I.map e.toRingHom).toCotangent_eq.mpr
  simp

/-- Helper for Chap10 Lemma 10 140 3: the inverse cotangent composite induced by an algebra
equivalence is the identity. -/
private theorem cotangentMapAlgEquiv_backward_comp_forward {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    cotangentMapAlgEquivBackward e I ∘ₗ cotangentMapAlgEquivForward e I = LinearMap.id := by
  -- Proof comment: the same generator check works on the original cotangent quotient.
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [LinearMap.comp_apply]
  unfold cotangentMapAlgEquivForward cotangentMapAlgEquivBackward
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
  apply I.toCotangent_eq.mpr
  simp

/-- Helper for Chap10 Lemma 10 140 3: an algebra equivalence transports cotangent spaces of
ideals. -/
private noncomputable def cotangentEquivMapAlgEquiv {R : Type u} [CommRing R]
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent :=
  LinearEquiv.ofLinear (cotangentMapAlgEquivForward e I) (cotangentMapAlgEquivBackward e I)
    (cotangentMapAlgEquiv_forward_comp_backward e I)
    (cotangentMapAlgEquiv_backward_comp_forward e I)

/-- Helper for Chap10 Lemma 10 140 3: after extending scalars from the closed-point quotient to
the residue field of the localization, the quotient cotangent module becomes the local cotangent
space. -/
private theorem closedPointFinrankResidueTensorCotangent_eq_localization
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
    (m : Ideal T) [m.IsMaximal] :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.ResidueField (Localization.AtPrime m) ⊗[T ⧸ m] m.Cotangent) =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
  let Tm := Localization.AtPrime m
  let κm := IsLocalRing.ResidueField Tm
  letI : IsScalarTower T (T ⧸ m) m.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (R := T) (I := m))
  haveI : Algebra.IsEpi T (T ⧸ m) :=
    Algebra.isEpi_of_surjective_algebraMap T (T ⧸ m) Ideal.Quotient.mk_surjective
  -- First cancel the redundant quotient base change from `T` to `T ⧸ m`.
  let eQuot : κm ⊗[T ⧸ m] m.Cotangent ≃ₗ[κm] κm ⊗[T] m.Cotangent :=
    let e₁ : (T ⧸ m) ⊗[T] m.Cotangent ≃ₗ[T ⧸ m] m.Cotangent :=
      TensorProduct.lid' T (T ⧸ m) m.Cotangent
    let e₂ : κm ⊗[T ⧸ m] ((T ⧸ m) ⊗[T] m.Cotangent) ≃ₗ[κm]
        κm ⊗[T] m.Cotangent :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange T (T ⧸ m) κm κm m.Cotangent
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κm κm) e₁.symm).trans e₂
  -- Then insert the localization base change and identify the localized cotangent ideal.
  let eLocBase : κm ⊗[T] m.Cotangent ≃ₗ[κm] κm ⊗[Tm] (Tm ⊗[T] m.Cotangent) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T Tm κm κm m.Cotangent).symm
  let tensorIdeal : Ideal (Tm ⊗[T] T) :=
    m.map (Algebra.TensorProduct.includeRight.toRingHom : T →+* Tm ⊗[T] T)
  let eTensorCot : κm ⊗[Tm] (Tm ⊗[T] m.Cotangent) ≃ₗ[κm]
      κm ⊗[Tm] tensorIdeal.Cotangent :=
    let e : Tm ⊗[T] m.Cotangent ≃ₗ[Tm] tensorIdeal.Cotangent :=
      Ideal.tensorCotangentEquiv T Tm m
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κm κm) e
  let eRid : Tm ⊗[T] T ≃ₐ[Tm] Tm := Algebra.TensorProduct.rid T Tm Tm
  have hTensorIdeal :
      tensorIdeal.map eRid.toRingHom = m.map (algebraMap T Tm) := by
    -- Proof comment: collapsing the trivial tensor factor identifies the extended ideal with the
    -- ordinary localized ideal.
    simpa [Tm, tensorIdeal, eRid, Algebra.smul_def] using
      (show
        Ideal.map
            (Algebra.TensorProduct.rid T Tm Tm).toRingHom
            (Ideal.map
              (Algebra.TensorProduct.includeRight.toRingHom : T →+* Tm ⊗[T] T) m) =
          Ideal.map (algebraMap T Tm) m by
            rw [Ideal.map_map]
            congr 1
            ext x
            simp [Algebra.smul_def])
  let eRidCot : tensorIdeal.Cotangent ≃ₗ[Tm] (m.map (algebraMap T Tm)).Cotangent :=
    (cotangentEquivMapAlgEquiv eRid tensorIdeal).trans
      (Ideal.Cotangent.equivOfEq _ _ hTensorIdeal)
  have hMax :
      m.map (algebraMap T Tm) = IsLocalRing.maximalIdeal Tm := by
    simpa using (Localization.AtPrime.map_eq_maximalIdeal (I := m))
  let eMaxCot : tensorIdeal.Cotangent ≃ₗ[Tm] IsLocalRing.CotangentSpace Tm :=
    eRidCot.trans (Ideal.Cotangent.equivOfEq _ _ hMax)
  let eCot : κm ⊗[Tm] tensorIdeal.Cotangent ≃ₗ[κm] κm ⊗[Tm] IsLocalRing.CotangentSpace Tm :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κm κm) eMaxCot
  letI : IsScalarTower Tm κm (IsLocalRing.CotangentSpace Tm) :=
    Module.IsTorsionBySet.isScalarTower
      (Ideal.isTorsionBySet_cotangent (R := Tm) (I := IsLocalRing.maximalIdeal Tm))
  haveI : Algebra.IsEpi Tm κm :=
    Algebra.isEpi_of_surjective_algebraMap Tm κm Ideal.Quotient.mk_surjective
  let eLid : κm ⊗[Tm] IsLocalRing.CotangentSpace Tm ≃ₗ[κm] IsLocalRing.CotangentSpace Tm :=
    TensorProduct.lid' Tm κm (IsLocalRing.CotangentSpace Tm)
  -- Proof comment: the composite equivalence is the closed-point cotangent comparison from the
  -- quotient presentation to the localized local-ring owner.
  let e : κm ⊗[T ⧸ m] m.Cotangent ≃ₗ[κm] IsLocalRing.CotangentSpace Tm :=
    (((eQuot.trans eLocBase).trans eTensorCot).trans eCot).trans eLid
  exact e.finrank_eq

/-- Helper for Chap10 Lemma 10 140 3: at a closed point, quotient cotangent dimension agrees with
the cotangent-space dimension of the local ring. -/
private theorem closedPointFinrankQuotientCotangent_eq_localization
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
    (m : Ideal T) [m.IsMaximal] :
    Module.finrank (T ⧸ m) m.Cotangent =
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
  -- Proof comment: base change from the quotient field to the localized residue field preserves
  -- finrank, and the previous helper identifies that base change with the local cotangent space.
  rw [← Module.finrank_baseChange
    (R := IsLocalRing.ResidueField (Localization.AtPrime m)) (S := T ⧸ m)
    (M' := m.Cotangent)]
  exact closedPointFinrankResidueTensorCotangent_eq_localization (K := K) (T := T) m

/-- Helper for Chap10 Lemma 10 140 3: in a Noetherian local ring, the cotangent-space dimension
dominates the Krull dimension. -/
private theorem ringKrullDim_le_finrank_cotangentSpace_local
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  calc
    ringKrullDim R ≤ (IsLocalRing.maximalIdeal R).spanFinrank :=
      ringKrullDim_le_spanFinrank_maximalIdeal (R := R)
    _ = (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :
        WithBot ℕ∞) := by
      exact_mod_cast
        IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)

/-- Helper for Chap10 Lemma 10 140 3: over an algebraically closed field, a closed-point
Kähler-fiber bound forces regularity of the local ring. -/
private theorem closedPointIsRegularLocalRing_of_kaehlerFiberFinrank_le
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hle : Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) ≤
      ringKrullDim (Localization.AtPrime m)) :
    IsRegularLocalRing (Localization.AtPrime m) := by
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  have hfiber :
      Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) =
        Module.finrank (T ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent (k := K) (S := T) m
  have hcot :
      Module.finrank (T ⧸ m) m.Cotangent =
        Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
    closedPointFinrankQuotientCotangent_eq_localization (K := K) (T := T) m
  have hcot_le :
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) ≤
        ringKrullDim (Localization.AtPrime m) := by
    -- Proof comment: rewrite the Kähler-fiber bound through the cotangent-space comparison.
    simpa [hfiber, hcot] using hle
  have hdim_le :
      ringKrullDim (Localization.AtPrime m) ≤
        Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
    ringKrullDim_le_finrank_cotangentSpace_local (R := Localization.AtPrime m)
  -- Proof comment: the universal cotangent inequality and the assumed reverse inequality force the
  -- regular-local characterization to hold with equality.
  exact
    (IsRegularLocalRing.iff_finrank_cotangentSpace (R := Localization.AtPrime m)).mpr
      (le_antisymm hcot_le hdim_le)

/-- Helper for Chap10 Lemma 10 140 3: over an algebraically closed field, regularity at a closed
point forces the Kähler-fiber dimension equality. -/
private theorem closedPointKaehlerFiberFinrank_eq_of_regularLocal
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) =
      ringKrullDim (Localization.AtPrime m) := by
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  have hfiber :
      Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) =
        Module.finrank (T ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent (k := K) (S := T) m
  have hcot :
      Module.finrank (T ⧸ m) m.Cotangent =
        Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
          (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
    closedPointFinrankQuotientCotangent_eq_localization (K := K) (T := T) m
  have hregEq :
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) =
      ringKrullDim (Localization.AtPrime m) :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace (R := Localization.AtPrime m)).mp hreg
  -- Proof comment: the closed-point Kähler fiber is the cotangent space `m / m²`, so the regular
  -- local equality rewrites directly to the desired quotient-fiber equality.
  simpa [hfiber, hcot] using hregEq

/-- Helper for Chap10 Lemma 10 140 3: localizing at a prime cannot increase Krull dimension. -/
private theorem ringKrullDimLocalizationAtPrime_le_ringKrullDim
    {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim A := by
  -- Proof comment: rewrite the local dimension as the height of `q`, then apply the global height
  -- bound.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- Helper for Chap10 Lemma 10 140 3: étale maps preserve the Krull dimension of prime
localizations. -/
private theorem ringKrullDimLocalizationAtPrime_eq_of_etale
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under A)) =
      ringKrullDim (Localization.AtPrime q) := by
  have hAB :
      ringKrullDim (Localization.AtPrime (q.under A)) ≤
        ringKrullDim (Localization.AtPrime q) := by
    letI :
        Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using
      ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
        (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (.inr <|
          Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance)
  have hBA :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under A)) := by
    -- Proof comment: étale maps are quasi-finite, so the local quasi-finite bound gives the
    -- reverse inequality.
    simpa using ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  exact le_antisymm hAB hBA

/-- Helper for Chap10 Lemma 10 140 3: the contraction of a closed point along an étale polynomial
presentation is maximal. -/
private theorem isMaximal_comap_etaleMvPolynomial_closedPoint
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal] {n : ℕ}
    (φ : MvPolynomial (Fin n) K →ₐ[K] T) :
    (Ideal.comap φ.toRingHom m).IsMaximal := by
  let ψ : MvPolynomial (Fin n) K →ₐ[K] T ⧸ m :=
    (Ideal.Quotient.mkₐ K m).comp φ
  let e : K ≃ₐ[K] T ⧸ m := by
    let eResidue : (T ⧸ m) ≃ₐ[K] m.ResidueField :=
      AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom K (T ⧸ m) m.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField m)
    letI : Module.Finite K m.ResidueField :=
      finite_residueField_of_isMaximal_of_finiteType K m
    letI : Module.Finite K (T ⧸ m) := Module.Finite.equiv eResidue.toLinearEquiv.symm
    letI : Algebra.IsIntegral K (T ⧸ m) := Algebra.IsIntegral.of_finite K (T ⧸ m)
    exact AlgEquiv.ofBijective
      (Algebra.ofId K (T ⧸ m))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))
  have hψ_surj : Function.Surjective ψ := by
    -- Proof comment: constants in the polynomial algebra already hit every point of the base
    -- field-quotient `T ⧸ m`.
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    refine ⟨MvPolynomial.C y, ?_⟩
    simp [ψ, e]
  have hker :
      RingHom.ker ψ.toRingHom = Ideal.comap φ.toRingHom m := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  -- Proof comment: the composite polynomial evaluation at the closed point is surjective onto the
  -- field quotient `T ⧸ m`, so its kernel is maximal.
  simpa [hker] using RingHom.ker_isMaximal_of_surjective ψ.toRingHom hψ_surj

/-- Helper for Chap10 Lemma 10 140 3: at a closed point of a standard smooth algebra over an
algebraically closed field, the local Krull dimension equals the relative dimension. -/
  private theorem closedPointLocalRingKrullDim_eq_of_standardSmooth
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] {n : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension n K T] (m : Ideal T) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n := by
  obtain ⟨φ, hφEtale⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K T
  letI : Algebra (MvPolynomial (Fin n) K) T := φ.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) K) T := hφEtale
  let m0 : Ideal (MvPolynomial (Fin n) K) := Ideal.comap φ.toRingHom m
  have hm0_max : m0.IsMaximal :=
    isMaximal_comap_etaleMvPolynomial_closedPoint (K := K) (T := T) m φ
  let m0Max : MaximalSpectrum (MvPolynomial (Fin n) K) := ⟨m0, hm0_max⟩
  have hpoly :
      ringKrullDim (Localization.AtPrime m0) = n := by
    simpa [m0Max] using ringKrullDim_localizationAtMaximal_mvPolynomial (m := m0Max)
  -- Proof comment: contract the closed point to affine space, compute the polynomial local
  -- dimension there, and transfer it back through the étale localization comparison.
  calc
    ringKrullDim (Localization.AtPrime m) =
        ringKrullDim (Localization.AtPrime m0) := by
          simpa [m0] using
            (ringKrullDimLocalizationAtPrime_eq_of_etale
              (A := MvPolynomial (Fin n) K) (B := T) m).symm
    _ = n := hpoly

/-- Helper for Chap10 Lemma 10 140 3: a closed point of a standard smooth finite type algebra
over an algebraically closed field has regular local ring. -/
private theorem closedPointIsRegularLocalRing_of_standardSmooth
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [Algebra.IsStandardSmooth K T]
    (m : Ideal T) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) := by
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth K T›.out
  letI : Finite σ := hσ
  letI : Finite ι := hι
  let n := P.dimension
  letI : Algebra.IsStandardSmoothOfRelativeDimension n K T :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hrankOmega :
      Module.rank T Ω[T⁄K] = n := by
    simpa [n] using P.rank_kaehlerDifferential (R := K) (S := T)
  have hfiber :
      Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) = n := by
    have hrankFiber :
        Module.rank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) = n := by
      rw [Module.rank_baseChange]
      simpa [hrankOmega]
    exact Module.finrank_eq_of_rank_eq hrankFiber
  have hdim :
      ringKrullDim (Localization.AtPrime m) = n :=
    closedPointLocalRingKrullDim_eq_of_standardSmooth (K := K) (T := T) (n := n) m
  -- Proof comment: standard smoothness gives the fiber rank `n`, the local étale model gives the
  -- same local dimension, and the existing closed-point criterion upgrades this equality to
  -- regularity.
  exact
    closedPointIsRegularLocalRing_of_kaehlerFiberFinrank_le
      (K := K) (T := T) m (le_of_eq (hfiber.trans hdim.symm))

/-- Helper for Chap10 Lemma 10 140 3: every prime localization of a standard smooth finite type
algebra over an algebraically closed field is a regular local ring. -/
private theorem isRegularLocalRing_localizationAtPrime_of_standardSmooth
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [Algebra.IsStandardSmooth K T]
    (q : Ideal T) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let Tq := Localization.AtPrime q
  letI : Algebra.FiniteType K Tq := inferInstance
  letI : Algebra.IsStandardSmooth K Tq :=
    isStandardSmooth_localizationPreserves q.primeCompl Tq inferInstance
  let m : Ideal Tq := IsLocalRing.maximalIdeal Tq
  letI : m.IsMaximal := inferInstance
  have hclosed : IsRegularLocalRing (Localization.AtPrime m) :=
    closedPointIsRegularLocalRing_of_standardSmooth (K := K) (T := Tq) m
  letI : IsLocalization m.primeCompl Tq :=
    IsLocalization.at_units m.primeCompl fun x hx ↦
      (IsLocalRing.notMem_maximalIdeal).mp hx
  let eLoc : Localization.AtPrime m ≃ₐ[K] Tq :=
    IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) Tq
  -- Proof comment: after localizing the standard smooth algebra at `q`, the resulting local ring
  -- is recovered by localizing once more at its maximal ideal, where the closed-point criterion
  -- applies directly.
  exact IsRegularLocalRing.of_ringEquiv eLoc.toRingEquiv

/-- Helper for Chap10 Lemma 10 140 3: local topological dimension at a prime is the Krull
dimension of the local ring plus the residue-field transcendence degree. -/
private theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- Route correction: use the theorem-local support file to avoid the broken import chain through
  -- `Lemma_10_116_3`, while keeping the same local-dimension formula.
  simpa using
    topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField_viaMinimalPrimes
      (k := k) (S := S) x

/-- Helper for Chap10 Lemma 10 140 3: at a closed point, the local topological dimension equals
the Krull dimension of the corresponding local ring. -/
private theorem topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtPrime
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
    (q : PrimeSpectrum T) [q.asIdeal.IsMaximal] :
    topologicalKrullDimAt q = ringKrullDim (Localization.AtPrime q.asIdeal) := by
  let m : MaximalSpectrum T := ⟨q.asIdeal, inferInstance⟩
  have hm : m.toPrimeSpectrum = q := by
    ext x
    rfl
  have hclosed :
      topologicalKrullDimAt m.toPrimeSpectrum =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
    -- Proof comment: the closed point has a unique maximal ideal above it, so the infimum
    -- formula for local topological dimension collapses to the localization at `m`.
    rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
      (k := K) (S := T) m.toPrimeSpectrum]
    letI : Subsingleton {n : MaximalSpectrum T // m.asIdeal ≤ n.asIdeal} := by
      refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
      have ha : m.asIdeal = a.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
      have hb : m.asIdeal = b.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
      exact ha.symm.trans hb
    let e : {n : MaximalSpectrum T // m.asIdeal ≤ n.asIdeal} := ⟨m, le_rfl⟩
    simpa [e] using
      (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))
  simpa [hm] using hclosed

/-- Helper for Chap10 Lemma 10 140 3: tensoring a finite-type algebra with a field extension
preserves the local topological Krull dimension at corresponding primes. -/
private theorem primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    {K : Type*} [Field K] [Algebra k K]
    (x : PrimeSpectrum S) (xK : PrimeSpectrum (K ⊗[k] S))
    (hxK :
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom xK =
        x) :
    topologicalKrullDimAt x = topologicalKrullDimAt xK := by
  -- Proof comment: this is exactly Lemma `10.116.6`.
  simpa using
    (_root_.primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
      (k := k) (K := K) (S := S) x xK hxK)

/-- Helper for Chap10 Lemma 10 140 3: the residue field of the maximal ideal in a local ring
agrees with the canonical local-ring residue field. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    A ⧸ IsLocalRing.maximalIdeal A ≃+* IsLocalRing.ResidueField A :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_residue (R := A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A)))

/-- Helper for Chap10 Lemma 10 140 3: the maximal-ideal residue-field identification sends the
quotient class of `a` to the usual local-ring residue of `a`. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A
        (algebraMap A (A ⧸ IsLocalRing.maximalIdeal A) a) =
      IsLocalRing.residue A a := by
  dsimp [maximalIdealResidueFieldEquiv]
  rw [Ideal.quotEquivOfEq_mk]

/-- Helper for Chap10 Lemma 10 140 3: at a closed point, the residue field of the localization is
canonically the same as the residue field of the original maximal ideal. -/
private noncomputable def closedPointLocalizationResidueFieldAlgEquiv
    {K : Type*} [CommRing K] {T : Type*} [CommRing T] [Algebra K T]
    (m : Ideal T) [m.IsMaximal] :
    IsLocalRing.ResidueField (Localization.AtPrime m) ≃ₐ[K] m.ResidueField := by
  let A := Localization.AtPrime m
  let eQuot : T ⧸ m ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal m A
  let eLoc : T ⧸ m ≃ₐ[K] IsLocalRing.ResidueField A := by
    refine AlgEquiv.ofRingEquiv (f := eQuot.trans (maximalIdealResidueFieldEquiv A)) ?_
    intro x
    change maximalIdealResidueFieldEquiv A
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap T A (algebraMap K T x))) =
      algebraMap K (IsLocalRing.ResidueField A) x
    rw [maximalIdealResidueFieldEquiv_apply_algebraMap]
    rw [IsLocalRing.ResidueField.algebraMap_eq A]
  let eResidue : T ⧸ m ≃ₐ[K] m.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (T ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  exact eLoc.symm.trans eResidue

/-- Helper for Chap10 Lemma 10 140 3: after base change to the algebraic closure of `κ(q)`, there
is a closed point above `q` whose local dimension matches the downstairs target dimension. -/
private theorem exists_closedPoint_over_residueFieldClosure
    (q : Ideal S) [q.IsPrime] :
    let K := AlgebraicClosure (Ideal.ResidueField q)
    let S_K := K ⊗[k] S
    ∃ qK : PrimeSpectrum S_K,
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK =
        ⟨q, inferInstance⟩ ∧
      qK.asIdeal.IsMaximal ∧
      ringKrullDim (Localization.AtPrime qK.asIdeal) =
        ringKrullDim (Localization.AtPrime q) +
          Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := by
  let K := AlgebraicClosure (Ideal.ResidueField q)
  let S_K := K ⊗[k] S
  let qPoint : PrimeSpectrum S := ⟨q, inferInstance⟩
  let ψS : S →ₐ[k] K :=
    (IsScalarTower.toAlgHom k (Ideal.ResidueField q) K).comp
      (IsScalarTower.toAlgHom k S (Ideal.ResidueField q))
  let ψ : S_K →ₐ[k] K :=
    Algebra.TensorProduct.productMap (AlgHom.id k K) ψS
  let qK : PrimeSpectrum S_K := ⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩
  have hψ_surj : Function.Surjective ψ := by
    -- Proof comment: the left tensor factor already maps identically to `K`.
    intro z
    refine ⟨(Algebra.TensorProduct.includeLeft : K →ₐ[k] S_K) z, ?_⟩
    simp [ψ]
  have hqK :
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK =
        qPoint := by
    apply PrimeSpectrum.ext
    ext x
    -- Proof comment: the right tensor inclusion is sent to the composite `S → κ(q) → K`, whose
    -- kernel is exactly `q`.
    change ψ ((Algebra.TensorProduct.includeRight : S →ₐ[k] S_K) x) = 0 ↔ x ∈ q
    simp [ψ, ψS, Ideal.algebraMap_residueField_eq_zero]
  have hqK_max : qK.asIdeal.IsMaximal := by
    -- Proof comment: a surjective map from the tensor product to the field `K` cuts out a maximal
    -- kernel.
    simpa [qK] using RingHom.ker_isMaximal_of_surjective ψ.toRingHom hψ_surj
  letI : qK.asIdeal.IsMaximal := hqK_max
  letI : Algebra.FiniteType K S_K := Algebra.FiniteType.baseChange K
  letI : Module.Finite K qK.asIdeal.ResidueField :=
    finite_residueField_of_isMaximal_of_finiteType K qK.asIdeal
  letI : Algebra.IsAlgebraic K qK.asIdeal.ResidueField :=
    Algebra.IsAlgebraic.of_finite K qK.asIdeal.ResidueField
  have hqK_top :
      topologicalKrullDimAt qK = ringKrullDim (Localization.AtPrime qK.asIdeal) := by
    -- Proof comment: `qK` is already a closed point, so the closed-point dimension formula from
    -- Lemma `10.114.6` gives the required identification directly.
    simpa using
      topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtPrime
        (K := K) (T := S_K) qK
  have hdim_baseChange :
      topologicalKrullDimAt qPoint = topologicalKrullDimAt qK := by
    simpa [qPoint] using
      (primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
        (k := k) (K := K) (S := S) qPoint qK hqK)
  have hdim_down :
      topologicalKrullDimAt qPoint =
        ringKrullDim (Localization.AtPrime q) +
          Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := by
    simpa [qPoint] using
      (topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
        (k := k) (S := S) qPoint)
  refine ⟨qK, hqK, hqK_max, ?_⟩
  -- Proof comment: identify the upstairs closed-point dimension with the downstairs topological
  -- dimension, then rewrite that downstairs dimension by the Chapter 10 local formula.
  calc
    ringKrullDim (Localization.AtPrime qK.asIdeal) = topologicalKrullDimAt qK := hqK_top.symm
    _ = topologicalKrullDimAt qPoint := hdim_baseChange.symm
    _ = ringKrullDim (Localization.AtPrime q) +
          Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := hdim_down

/-- Helper for Chap10 Lemma 10 140 3: at the closed point of `T`, the conormal map
`m / m² → κ(m) ⊗[Tₘ] Ω[Tₘ⁄K]` is injective because the residue field `κ(m)` is formally smooth
over `K`. -/
private theorem closedPointResidueCotangentToKaehler_injective
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal] :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor K (Localization.AtPrime m)
        (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
  let A := Localization.AtPrime m
  let κ := IsLocalRing.ResidueField A
  let eκ : κ ≃ₐ[K] m.ResidueField := closedPointLocalizationResidueFieldAlgEquiv (K := K) m
  letI : PerfectField K := inferInstance
  letI : Module.Finite K m.ResidueField :=
    finite_residueField_of_isMaximal_of_finiteType K m
  letI : Module.Finite K κ := Module.Finite.equiv eκ.toLinearEquiv
  letI : Algebra.IsAlgebraic K κ := Algebra.IsAlgebraic.of_finite K κ
  letI : Algebra.IsSeparable K κ := by
    infer_instance
  letI : Algebra.FormallyEtale K κ := Algebra.FormallyEtale.of_isSeparable K κ
  letI : Algebra.FormallySmooth K κ := inferInstance
  have hsurj : Function.Surjective (algebraMap A κ) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq A] using
      (IsLocalRing.residue_surjective (R := A))
  have hsurjLift :
      Function.Surjective (IsScalarTower.toAlgHom K A κ).kerSquareLift := by
    exact Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hsqz :
      RingHom.ker (IsScalarTower.toAlgHom K A κ).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let σ : κ →ₐ[K] A ⧸ RingHom.ker (algebraMap A κ) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id K κ)
      (IsScalarTower.toAlgHom K A κ).kerSquareLift
      hsurjLift
      ⟨2, hsqz⟩
  have hσ :
      (IsScalarTower.toAlgHom K A κ).kerSquareLift.comp σ =
        AlgHom.id K κ := by
    simpa [σ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective
        (AlgHom.id K κ)
        (IsScalarTower.toAlgHom K A κ).kerSquareLift
        hsurjLift
        ⟨2, hsqz⟩ : _)
  obtain ⟨l, hl⟩ := ((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩)
  exact LinearMap.injective_of_comp_eq_id _ _ hl

/-- Helper for Chap10 Lemma 10 140 3: after localizing at a closed point, the Kähler fiber over
the residue field has dimension equal to the Krull dimension of the local ring. -/
private theorem closedPointLocalizationKaehlerFiberFinrank_eq_of_regularLocal
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        ((IsLocalRing.ResidueField (Localization.AtPrime m)) ⊗[Localization.AtPrime m]
          Ω[Localization.AtPrime m⁄K]) =
      ringKrullDim (Localization.AtPrime m) := by
  let A := Localization.AtPrime m
  let κ := IsLocalRing.ResidueField A
  let eLoc :
      κ ⊗[A] Ω[A⁄K] ≃ₗ[κ] κ ⊗[T] Ω[T⁄K] :=
    (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl κ κ)
        (KaehlerDifferential.tensorKaehlerEquiv K T A A).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T A κ κ Ω[T⁄K])
  haveI : Algebra.IsEpi T (T ⧸ m) :=
    Algebra.isEpi_of_surjective_algebraMap T (T ⧸ m) Ideal.Quotient.mk_surjective
  let eQuot :
      κ ⊗[T ⧸ m] ((T ⧸ m) ⊗[T] Ω[T⁄K]) ≃ₗ[κ] κ ⊗[T] Ω[T⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      T (T ⧸ m) κ κ Ω[T⁄K]
  have hfiber :
      Module.finrank κ (κ ⊗[T] Ω[T⁄K]) =
        Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) := by
    rw [← eQuot.finrank_eq]
    exact Module.finrank_baseChange
  calc
    Module.finrank κ (κ ⊗[A] Ω[A⁄K]) =
        Module.finrank κ (κ ⊗[T] Ω[T⁄K]) := by
          rw [← eLoc.finrank_eq]
    _ = Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) := hfiber
    _ = ringKrullDim (Localization.AtPrime m) :=
          closedPointKaehlerFiberFinrank_eq_of_regularLocal (K := K) (T := T) m hreg

/-- Helper for Chap10 Lemma 10 140 3: at a closed point over an algebraically closed field, the
conormal map `m / m² → κ(m) ⊗[Tₘ] Ω[Tₘ⁄K]` is bijective because the residue field is just `K`, so
the last Kähler term vanishes. -/
private theorem closedPointResidueCotangentToKaehler_bijective
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    Function.Bijective
      (KaehlerDifferential.kerCotangentToTensor K (Localization.AtPrime m)
        (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
  let A := Localization.AtPrime m
  let κ := IsLocalRing.ResidueField A
  have hInjective :
      Function.Injective (KaehlerDifferential.kerCotangentToTensor K A κ) :=
    closedPointResidueCotangentToKaehler_injective (K := K) (T := T) m
  have hsource :
      Module.finrank κ (IsLocalRing.CotangentSpace A) = ringKrullDim A :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp hreg
  have htarget :
      Module.finrank κ (κ ⊗[A] Ω[A⁄K]) = ringKrullDim A :=
    closedPointLocalizationKaehlerFiberFinrank_eq_of_regularLocal
      (K := K) (T := T) m hreg
  have hdim :
      Module.finrank κ (IsLocalRing.CotangentSpace A) =
        Module.finrank κ (κ ⊗[A] Ω[A⁄K]) := by
    rw [hsource, htarget]
  exact ⟨hInjective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hInjective⟩

/-- Helper for Chap10 Lemma 10 140 3: a localization of affine `n`-space at a closed point is a
regular local ring. -/
private theorem localizedMvPolynomial_regularLocal
    {K : Type*} [Field K] {n : ℕ} (m0 : Ideal (MvPolynomial (Fin n) K)) [m0.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m0) := by
  let m0Max : MaximalSpectrum (MvPolynomial (Fin n) K) := ⟨m0, inferInstance⟩
  -- Proof comment: affine space is regular, so every maximal localization is regular local.
  simpa [m0Max] using isRegularLocalRing_localizationAtMaximal_mvPolynomial (m := m0Max)

/-- Helper for Chap10 Lemma 10 140 3: a surjective polynomial presentation stays surjective after
localizing at a closed point. -/
private theorem localizedPresentation_surjective
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπ : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal] :
    Function.Surjective
      (Localization.localRingHom (Ideal.comap π.toRingHom m) m π.toRingHom rfl) := by
  -- Proof comment: write a target element as a fraction in `Tₘ`, lift numerator and denominator
  -- through `π`, and rebuild the corresponding fraction in the source localization.
  intro y
  rcases IsLocalization.exists_mk'_eq m.primeCompl y with ⟨a, s, rfl⟩
  rcases hπ a with ⟨x, rfl⟩
  rcases hπ s with ⟨t, ht⟩
  let t' : (Ideal.comap π.toRingHom m).primeCompl := ⟨t, by
    intro htmem
    exact s.2 (by
      change π.toRingHom t ∈ m at htmem
      simpa [ht] using htmem)⟩
  refine
    ⟨IsLocalization.mk'
      (Localization.AtPrime (Ideal.comap π.toRingHom m)) x t', ?_⟩
  rw [Localization.localRingHom_mk']
  have hs_eq :
      (⟨π.toRingHom t, by
        exact Localization.le_comap_primeCompl_iff.mpr
          (ge_of_eq
            (rfl : Ideal.comap π.toRingHom m = m.comap π.toRingHom))
            t'.2⟩ :
        m.primeCompl) = s := by
    exact Subtype.ext ht
  rw [hs_eq]
  rfl

/-- Helper for Chap10 Lemma 10 140 3: a surjective polynomial presentation maps the maximal-ideal
complement onto the maximal-ideal complement after contraction. -/
private theorem localizedPresentation_primeCompl_map_eq
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπ : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal] :
    Submonoid.map π.toRingHom (Ideal.comap π.toRingHom m).primeCompl = m.primeCompl := by
  -- Proof comment: lift each denominator in `T \ m` through the surjective polynomial
  -- presentation, while the forward inclusion is just contraction along `π`.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases hπ y with ⟨x, rfl⟩
    exact ⟨x, hy, rfl⟩

/-- Helper for Chap10 Lemma 10 140 3: the kernel of the localized presentation is the
localization of the original polynomial-presentation kernel. -/
private theorem localizedPresentation_ker_localRingHom_eq
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπ : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal] :
    RingHom.ker
        (Localization.localRingHom
          (Ideal.comap π.toRingHom m) m π.toRingHom rfl) =
      Ideal.map
        (algebraMap (MvPolynomial (Fin n) K)
          (Localization.AtPrime (Ideal.comap π.toRingHom m)))
        (RingHom.ker π.toRingHom) := by
  -- Proof comment: once the denominator submonoids are matched, the general localization kernel
  -- formula computes the kernel of the localized presentation.
  simpa [Localization.localRingHom] using
    (IsLocalization.ker_map
      (S := Localization.AtPrime (Ideal.comap π.toRingHom m))
      (Q := Localization.AtPrime m)
      (g := π.toRingHom)
      (localizedPresentation_primeCompl_map_eq (π := π) hπ m))

/-- Helper for Chap10 Lemma 10 140 3: finite presentation makes the localized presentation kernel
finitely generated. -/
private theorem localizedPresentation_kernel_fg
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FinitePresentation K T]
    {n : ℕ} (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπ : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal] :
    (RingHom.ker
        (Localization.localRingHom
          (Ideal.comap π.toRingHom m) m π.toRingHom rfl)).FG := by
  -- Proof comment: finite generation of the original presentation kernel localizes through the
  -- kernel formula proved just above.
  have hker_fg : (RingHom.ker π.toRingHom).FG := by
    simpa using Algebra.FinitePresentation.ker_fG_of_surjective (f := π) hπ
  rw [localizedPresentation_ker_localRingHom_eq (π := π) hπ m]
  exact Ideal.FG.map hker_fg _

/-- Helper for Chap10 Lemma 10 140 3: the localized polynomial presentation commutes with the two
`K`-algebra structures. -/
private theorem localizedPresentation_toAlgHom_commutes
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (m : Ideal T) [m.IsMaximal] (r : K) :
    Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl
        (algebraMap K (Localization.AtPrime (Ideal.comap π.toRingHom m)) r) =
      algebraMap K (Localization.AtPrime m) r := by
  -- Proof comment: compare both scalar maps by first spelling them through the polynomial algebra
  -- and then pushing them across the localized presentation map.
  calc
    Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl
        (algebraMap K (Localization.AtPrime (Ideal.comap π.toRingHom m)) r) =
      Localization.localRingHom
          (Ideal.comap π.toRingHom m) m π.toRingHom rfl
          (algebraMap (MvPolynomial (Fin n) K)
            (Localization.AtPrime (Ideal.comap π.toRingHom m))
            (algebraMap K (MvPolynomial (Fin n) K) r)) := by
        rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
          (Localization.AtPrime (Ideal.comap π.toRingHom m))]
    _ = algebraMap T (Localization.AtPrime m)
          (π.toRingHom (algebraMap K (MvPolynomial (Fin n) K) r)) := by
        rw [Localization.localRingHom_to_map]
    _ = algebraMap T (Localization.AtPrime m) (algebraMap K T r) := by
        exact congrArg (algebraMap T (Localization.AtPrime m)) (π.commutes r)
    _ = algebraMap K (Localization.AtPrime m) r := by
        rw [← IsScalarTower.algebraMap_apply K T (Localization.AtPrime m)]

/-- Helper for Chap10 Lemma 10 140 3: the canonical algebra structure on the localized
presentation is compatible with the base-field scalar tower. -/
private theorem localizedPresentation_isScalarTower
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (m : Ideal T) [m.IsMaximal] :
    let P := Localization.AtPrime (Ideal.comap π.toRingHom m)
    let A := Localization.AtPrime m
    let φ : P →+* A := Localization.localRingHom
      (Ideal.comap π.toRingHom m) m π.toRingHom rfl
    letI : Algebra P A := φ.toAlgebra
    IsScalarTower K P A := by
  -- Proof comment: reduce the scalar-tower identity to the pointwise compatibility of the
  -- localized presentation with the two `K`-algebra structures.
  dsimp only
  let φ : Localization.AtPrime (Ideal.comap π.toRingHom m) →+* Localization.AtPrime m :=
    Localization.localRingHom (Ideal.comap π.toRingHom m) m π.toRingHom rfl
  letI : Algebra (Localization.AtPrime (Ideal.comap π.toRingHom m))
      (Localization.AtPrime m) := φ.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact (localizedPresentation_toAlgHom_commutes (π := π) m r).symm

/-- Helper for Chap10 Lemma 10 140 3: the identity map has kernel generated by the empty regular
sequence. -/
private theorem ringHom_id_kernelIsGeneratedByRegularSequence
    (A : Type*) [CommRing A] [Nontrivial A] :
    (RingHom.id A).KernelIsGeneratedByRegularSequence := by
  -- Proof comment: the identity kernel is `⊥`, generated by the empty regular sequence.
  refine ⟨[], ?_, ?_⟩
  · simpa using (RingTheory.Sequence.IsRegular.nil A A)
  · rw [Ideal.ofList_nil]
    exact ((RingHom.injective_iff_ker_eq_bot (RingHom.id A)).mp Function.injective_id).symm

/-- Helper for Chap10 Lemma 10 140 3: regularity of the target local ring forces the localized
presentation kernel to be generated by a regular sequence. -/
private theorem localizedPresentation_kernelIsGeneratedByRegularSequence
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπ : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    (Localization.localRingHom
      (Ideal.comap π.toRingHom m) m π.toRingHom rfl).KernelIsGeneratedByRegularSequence := by
  let A := Localization.AtPrime m
  let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
  let P := Localization.AtPrime m'
  let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
  have hsource : IsRegularLocalRing P := localizedMvPolynomial_regularLocal m'
  have hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπ m
  letI : IsRegularLocalRing A := hreg
  letI : IsRegularLocalRing P := hsource
  have hid :
      (RingHom.id A).KernelIsGeneratedByRegularSequence :=
    ringHom_id_kernelIsGeneratedByRegularSequence A
  let htfae :=
    ker_generatedBy_regularSequence_tfae_of_surjective_local_of_isRegularLocalRing
      (A := P) (B := A) (C := A) (φ := φ) (ψ := RingHom.id A) hφsurj
      (fun a ↦ ⟨a, rfl⟩)
  -- Proof comment: specialize the regular-local kernel TFAE to the factorization `P --φ--> A --id--> A`.
  have hcomp :
      ((RingHom.id A).comp φ).KernelIsGeneratedByRegularSequence :=
    (htfae.out 2 0).mp hid
  simpa [A, P, φ] using hcomp

/-- Helper for Chap10 Lemma 10 140 3: if `d` elements generate an `R`-module over a local ring,
then the residue-field fiber has vector-space dimension at most `d`. -/
private theorem residueTensorFinrank_le_of_span_eq_top
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {d : ℕ} (xs : Fin d → M) (hxs : Submodule.span R (Set.range xs) = ⊤) :
    Module.finrank (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] M) ≤ d := by
  letI : Module.Finite R M := Module.Finite.of_fg <| by
    refine ⟨Finset.univ.image xs, ?_⟩
    simpa [hxs]
  have hR :
      Submodule.span R
          (Set.range ((TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) ∘ xs)) = ⊤ := by
    -- Proof comment: tensoring the spanning submodule with the residue field still spans.
    have h :=
      (IsLocalRing.map_tensorProduct_mk_eq_top
        (N := Submodule.span R (Set.range xs)) (M := M)).2 hxs
    rw [Submodule.map_span] at h
    simpa [Set.range_comp] using h
  have hκ :
      Submodule.span (IsLocalRing.ResidueField R)
          (Set.range ((TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) ∘ xs)) = ⊤ := by
    -- Proof comment: the same family spans after promoting scalars from `R` to the residue field.
    rw [← Submodule.restrictScalars_eq_top_iff R (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] M)]
    rw [Submodule.restrictScalars_span R (IsLocalRing.ResidueField R) Ideal.Quotient.mk_surjective]
    exact hR
  simpa using finrank_le_of_span_eq_top hκ

/-- Helper for Chap10 Lemma 10 140 3: an `A`-linear map between modules over the residue field of
a local ring is automatically linear over that residue field. -/
private noncomputable def residueFieldLinearMap
    {A : Type*} [CommRing A] [IsLocalRing A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (IsLocalRing.ResidueField A) M] [Module (IsLocalRing.ResidueField A) N]
    [Module A M] [IsScalarTower A (IsLocalRing.ResidueField A) M]
    [Module A N] [IsScalarTower A (IsLocalRing.ResidueField A) N]
    (f : M →ₗ[A] N) :
    M →ₗ[IsLocalRing.ResidueField A] N :=
  -- Proof comment: surjectivity of `A → κ(A)` upgrades `A`-linearity to `κ(A)`-linearity.
  f.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := A))

/-- Helper for Chap10 Lemma 10 140 3: generators of the kernel ideal of a surjective extension
generate its cotangent module. -/
private theorem extensionCotangent_span_eq_top_of_span_eq_ker
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (Pext : Algebra.Extension R S) {d : ℕ} (xs : Fin d → Pext.Ring)
    (hxs : Ideal.span (Set.range xs) = Pext.ker) :
    Submodule.span S
        (Set.range fun i ↦
          Pext.Cotangent.mk
            (⟨xs i, by
              rw [← hxs]
              exact Ideal.subset_span (Set.mem_range_self i)⟩ : Pext.ker)) =
      ⊤ := by
  let ys : Fin d → Pext.Cotangent := fun i ↦
    Algebra.Extension.Cotangent.mk (P := Pext)
      (⟨xs i, by
        rw [← hxs]
        exact Ideal.subset_span (Set.mem_range_self i)⟩ : Pext.ker)
  have hspan_le : Ideal.span (Set.range xs) ≤ Pext.ker := by
    rw [hxs]
  apply Submodule.eq_top_iff'.2
  intro z
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Pext) z
  have hyspan : (y : Pext.Ring) ∈ Ideal.span (Set.range xs) := by
    simpa [hxs] using y.2
  refine Submodule.span_induction
    (p := fun x hx ↦
      Algebra.Extension.Cotangent.mk (P := Pext) (⟨x, hspan_le hx⟩ : Pext.ker) ∈
        Submodule.span S (Set.range ys))
    ?_ ?_ ?_ ?_ hyspan
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · simpa using (Submodule.zero_mem (Submodule.span S (Set.range ys)))
  · intro x y hx hy hxmem hymem
    simpa using (Submodule.add_mem (Submodule.span S (Set.range ys)) hxmem hymem)
  · intro a x hx hxmem
    have hsmul :
        algebraMap Pext.Ring S a •
            Algebra.Extension.Cotangent.mk (P := Pext) (⟨x, hspan_le hx⟩ : Pext.ker) ∈
          Submodule.span S (Set.range ys) :=
      Submodule.smul_mem (Submodule.span S (Set.range ys)) (algebraMap Pext.Ring S a) hxmem
    -- Proof comment: multiplication by an element of the presentation ring acts through its image
    -- in the quotient algebra `S`.
    simpa using
      (show Algebra.Extension.Cotangent.mk (P := Pext) (a • (⟨x, hspan_le hx⟩ : Pext.ker)) ∈
          Submodule.span S (Set.range ys) from hsmul)

/-- Helper for Chap10 Lemma 10 140 3: the source cotangent-space term in the localized
presentation has finrank equal to the local Krull dimension of the polynomial source. -/
private theorem closedPointPresentationSourceFinrank_eq_ringKrullDim
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπsurj : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal] :
    let A := Localization.AtPrime m
    let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
    let P := Localization.AtPrime m'
    let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
    letI : Algebra P A := φ.toAlgebra
    letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
    let Pext : Algebra.Extension K A :=
      Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom K P A)
        (localizedPresentation_surjective π hπsurj m)
    let κ := IsLocalRing.ResidueField A
    Module.finrank κ (κ ⊗[A] Pext.CotangentSpace) = ringKrullDim P := by
  dsimp only
  let A := Localization.AtPrime m
  let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
  let P := Localization.AtPrime m'
  let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
  let hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπsurj m
  let Pext : Algebra.Extension K A :=
    Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom K P A) hφsurj
  let κ := IsLocalRing.ResidueField A
  have hm'_max : m'.IsMaximal := Ideal.comap_isMaximal_of_surjective π.toRingHom hπsurj
  have hregP : IsRegularLocalRing P := by
    -- Proof comment: the localized polynomial source is a regular local ring at the contracted
    -- closed point.
    simpa [P, m'] using localizedMvPolynomial_regularLocal (K := K) m'
  let κP := IsLocalRing.ResidueField P
  letI : Algebra κP κ := (IsLocalRing.ResidueField.map φ).toAlgebra
  letI : IsScalarTower P κP κ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simpa using IsLocalRing.ResidueField.map_residue φ r
  let eCotP :
      IsLocalRing.CotangentSpace P ≃ₗ[P]
        (RingHom.ker (algebraMap P κP)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ (IsLocalRing.ker_residue (R := P)).symm
  let fP : IsLocalRing.CotangentSpace P →ₗ[κP] κP ⊗[P] Ω[P⁄K] :=
    residueFieldLinearMap (A := P)
      ((KaehlerDifferential.kerCotangentToTensor K P κP).comp eCotP.toLinearMap)
  have hbijP : Function.Bijective fP := by
    -- Proof comment: at the closed point of the polynomial source, the residue cotangent map is
    -- bijective.
    simpa [fP, residueFieldLinearMap, eCotP, IsLocalRing.ResidueField.algebraMap_eq P] using
      closedPointResidueCotangentToKaehler_bijective
        (K := K) (T := MvPolynomial (Fin n) K) m' hregP
  have hmiddleP :
      Module.finrank κP (κP ⊗[P] Ω[P⁄K]) = ringKrullDim P := by
    let eP : IsLocalRing.CotangentSpace P ≃ₗ[κP] κP ⊗[P] Ω[P⁄K] :=
      LinearEquiv.ofBijective fP hbijP
    -- Proof comment: rewrite the source Kähler fiber through the cotangent-space bijection and
    -- then invoke the regular-local characterization.
    calc
      Module.finrank κP (κP ⊗[P] Ω[P⁄K]) =
          Module.finrank κP (IsLocalRing.CotangentSpace P) := by
            rw [← eP.finrank_eq]
      _ = ringKrullDim P := by
            exact (IsRegularLocalRing.iff_finrank_cotangentSpace (R := P)).mp hregP
  let eOwner :
      κ ⊗[A] Pext.CotangentSpace ≃ₗ[κ] κ ⊗[P] Ω[P⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange P A κ κ Ω[P⁄K]
  let eResidue :
      κ ⊗[κP] (κP ⊗[P] Ω[P⁄K]) ≃ₗ[κ] κ ⊗[P] Ω[P⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange P κP κ κ Ω[P⁄K]
  -- Proof comment: compare the owner cotangent space with the polynomial-source Kähler
  -- differentials by base change through the residue-field tower.
  calc
    Module.finrank κ (κ ⊗[A] Pext.CotangentSpace) =
        Module.finrank κ (κ ⊗[P] Ω[P⁄K]) := by
          rw [← eOwner.finrank_eq]
    _ = Module.finrank κ (κ ⊗[κP] (κP ⊗[P] Ω[P⁄K])) := by
          rw [← eResidue.finrank_eq]
    _ = Module.finrank κP (κP ⊗[P] Ω[P⁄K]) := by
          rw [Module.finrank_baseChange (R := κ) (S := κP)
            (M' := κP ⊗[P] Ω[P⁄K])]
    _ = ringKrullDim P := hmiddleP

/-- Helper for Chap10 Lemma 10 140 3: the target Kähler-fiber term in the localized
presentation has finrank equal to the local Krull dimension of the target regular local ring. -/
private theorem closedPointPresentationTargetFinrank_eq_ringKrullDim
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    let A := Localization.AtPrime m
    let κ := IsLocalRing.ResidueField A
    Module.finrank κ (κ ⊗[A] Ω[A⁄K]) = ringKrullDim A := by
  dsimp only
  let A := Localization.AtPrime m
  let κ := IsLocalRing.ResidueField A
  let eCotA :
      IsLocalRing.CotangentSpace A ≃ₗ[A]
        (RingHom.ker (algebraMap A κ)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ (IsLocalRing.ker_residue (R := A)).symm
  let fA : IsLocalRing.CotangentSpace A →ₗ[κ] κ ⊗[A] Ω[A⁄K] :=
    residueFieldLinearMap (A := A)
      ((KaehlerDifferential.kerCotangentToTensor K A κ).comp eCotA.toLinearMap)
  have hbijA : Function.Bijective fA := by
    -- Proof comment: at the closed point of the target, the cotangent-to-Kähler comparison is
    -- bijective.
    simpa [fA, residueFieldLinearMap, eCotA, IsLocalRing.ResidueField.algebraMap_eq A] using
      closedPointResidueCotangentToKaehler_bijective (K := K) (T := T) m hreg
  let eA : IsLocalRing.CotangentSpace A ≃ₗ[κ] κ ⊗[A] Ω[A⁄K] :=
    LinearEquiv.ofBijective fA hbijA
  -- Proof comment: convert the Kähler-fiber term to the cotangent space and then apply regular
  -- locality of `A`.
  calc
    Module.finrank κ (κ ⊗[A] Ω[A⁄K]) =
        Module.finrank κ (IsLocalRing.CotangentSpace A) := by
          rw [← eA.finrank_eq]
    _ = ringKrullDim A := by
          exact (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp hreg

/-- Helper for Chap10 Lemma 10 140 3: exactness plus a surjective right map and the expected
finrank gap force injectivity of the left map. -/
private theorem exactSurjective_injective_of_finrankGap
    {F : Type*} [Field F]
    {U : Type*} {V : Type*} {W : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F U] [Module F V] [Module F W]
    [FiniteDimensional F U] [FiniteDimensional F V] [FiniteDimensional F W]
    (α : U →ₗ[F] V) (β : V →ₗ[F] W) {d : ℕ}
    (hexact : Function.Exact α β) (hβsurj : Function.Surjective β)
    (hsource_le : Module.finrank F U ≤ d)
    (hgap : Module.finrank F V = Module.finrank F W + d) :
    Function.Injective α := by
  have hrange_eq_ker : LinearMap.range α = LinearMap.ker β :=
    LinearMap.exact_iff.mp hexact
  have hkerβ :
      Module.finrank F (LinearMap.ker β) = d := by
    have hβrank := LinearMap.finrank_range_add_finrank_ker β
    -- Proof comment: surjectivity turns rank-nullity for `β` into the prescribed finrank gap.
    rw [LinearMap.range_eq_top.mpr hβsurj, finrank_top, hgap] at hβrank
    omega
  have hrangeα :
      Module.finrank F (LinearMap.range α) = d := by
    -- Proof comment: exactness identifies the image of `α` with the kernel of `β`.
    simpa [hrange_eq_ker] using hkerβ
  have hsource_ge :
      d ≤ Module.finrank F U := by
    -- Proof comment: the range of `α` cannot exceed the finrank of its source.
    simpa [hrangeα] using LinearMap.finrank_range_le α
  have hsource :
      Module.finrank F U = d :=
    le_antisymm hsource_le hsource_ge
  have hkerα_finrank :
      Module.finrank F (LinearMap.ker α) = 0 := by
    have hαrank := LinearMap.finrank_range_add_finrank_ker α
    -- Proof comment: once the source finrank also equals `d`, the kernel of `α` must vanish.
    rw [hrangeα, hsource] at hαrank
    omega
  have hkerα : LinearMap.ker α = ⊥ := by
    simpa using hkerα_finrank
  exact LinearMap.ker_eq_bot.mp hkerα

/-- Helper for Chap10 Lemma 10 140 3: the owner base-changed cotangent-complex map in the
localized presentation is injective once the target is regular local and the kernel is generated
by a regular sequence. -/
private theorem closedPointPresentationOwnerBaseChange_injective
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπsurj : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m))
    (hφregseq :
      (Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl).KernelIsGeneratedByRegularSequence) :
    let A := Localization.AtPrime m
    let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
    let P := Localization.AtPrime m'
    let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
    letI : Algebra P A := φ.toAlgebra
    letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
    let hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπsurj m
    let Pext : Algebra.Extension K A :=
      Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom K P A) hφsurj
    let κ := IsLocalRing.ResidueField A
    Function.Injective (LinearMap.baseChange κ Pext.cotangentComplex) := by
  dsimp only
  let A := Localization.AtPrime m
  let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
  let P := Localization.AtPrime m'
  let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
  let hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπsurj m
  let Pext : Algebra.Extension K A :=
    Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom K P A) hφsurj
  let κ := IsLocalRing.ResidueField A
  letI : Module.Finite A Pext.Cotangent := by
    have hφfg : (RingHom.ker φ).FG := by
      -- Proof comment: finite presentation localizes to finite generation of the presentation
      -- kernel.
      simpa [A, P, φ, m'] using localizedPresentation_kernel_fg (π := π) hπsurj m
    simpa [Pext, φ] using Pext.Cotangent.finite (by simpa [Pext, φ] using hφfg)
  letI : Module.Finite A Pext.CotangentSpace := by
    infer_instance
  letI : Module.Finite A Ω[A⁄K] := KaehlerDifferential.finite K A
  obtain ⟨d, hd, x, hxspan⟩ :=
    ((ker_generatedBy_regularSequence_tfae_of_surjective_local_of_isRegularLocalRing
      φ (RingHom.id A) hφsurj (fun a ↦ ⟨a, rfl⟩)).out 0 1).mp (by
        simpa [A, P, φ, m'] using hφregseq)
  have hsource_le :
      Module.finrank κ (κ ⊗[A] Pext.Cotangent) ≤ d := by
    -- Proof comment: the regular-sequence generators span the owner conormal module, so their
    -- number bounds the residue-field finrank from above.
    apply residueTensorFinrank_le_of_span_eq_top
    simpa [Pext, φ] using
      extensionCotangent_span_eq_top_of_span_eq_ker Pext x (by
        simpa [Pext, φ] using hxspan)
  have hmiddle :
      Module.finrank κ (κ ⊗[A] Pext.CotangentSpace) = ringKrullDim P := by
    -- Proof comment: isolate the source finrank computation in the polynomial presentation once.
    simpa [A, P, φ, Pext, κ, m'] using
      closedPointPresentationSourceFinrank_eq_ringKrullDim
        (K := K) (T := T) (n := n) π hπsurj m
  have htarget :
      Module.finrank κ (κ ⊗[A] Ω[A⁄K]) = ringKrullDim A := by
    -- Proof comment: similarly isolate the target finrank computation from regularity of `A`.
    simpa [A, κ] using
      closedPointPresentationTargetFinrank_eq_ringKrullDim
        (K := K) (T := T) m hreg
  let α : κ ⊗[A] Pext.Cotangent →ₗ[κ] κ ⊗[A] Pext.CotangentSpace :=
    Pext.cotangentComplex.baseChange κ
  let β : κ ⊗[A] Pext.CotangentSpace →ₗ[κ] κ ⊗[A] Ω[A⁄K] :=
    Pext.toKaehler.baseChange κ
  have hβsurj : Function.Surjective β := by
    -- Proof comment: base change preserves surjectivity of the owner map to Kähler
    -- differentials.
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective κ Pext.toKaehler_surjective
  have hexact : Function.Exact α β := by
    -- Proof comment: tensoring the owner cotangent sequence with the residue field preserves its
    -- exactness.
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact κ Pext.exact_cotangentComplex_toKaehler Pext.toKaehler_surjective
  have hgap :
      Module.finrank κ (κ ⊗[A] Pext.CotangentSpace) =
        Module.finrank κ (κ ⊗[A] Ω[A⁄K]) + d := by
    -- Proof comment: rewrite the regular-sequence codimension identity in the two stabilized
    -- finrank normal forms.
    rw [hmiddle, htarget]
    exact hd.symm
  -- Proof comment: the generic exactness/rank lemma packages the remaining rank-nullity endgame.
  exact exactSurjective_injective_of_finrankGap α β hexact hβsurj hsource_le hgap

/-- Helper for Chap10 Lemma 10 140 3: owner injectivity transports to the displayed cotangent
complex base-change map once the localized presentation spelling is fixed. -/
private theorem closedPointCotangentComplexBaseChange_injective
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπsurj : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m))
    (hφregseq :
      (Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl).KernelIsGeneratedByRegularSequence) :
    let A := Localization.AtPrime m
    let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
    let P := Localization.AtPrime m'
    Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange K A P (IsLocalRing.ResidueField A)) := by
  dsimp only
  let A := Localization.AtPrime m
  let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
  let P := Localization.AtPrime m'
  let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
  let hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπsurj m
  let Pext : Algebra.Extension K A :=
    Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom K P A) hφsurj
  let κ := IsLocalRing.ResidueField A
  have hOwnerInj :
      Function.Injective (LinearMap.baseChange κ Pext.cotangentComplex) := by
    -- Proof comment: first prove injectivity on the owner extension map, where the exact
    -- cotangent sequence and the finrank identities are stated canonically.
    simpa [A, P, φ, Pext, κ, m'] using
      closedPointPresentationOwnerBaseChange_injective
        (K := K) (T := T) (n := n) π hπsurj m hreg hφregseq
  -- Proof comment: the displayed cotangent-complex map is the owner map rewritten through the
  -- standard extension/displayed comparison.
  simpa [κ, Pext, φ] using
    (cotangentComplexBaseChange_injective_iff_owner_baseChange_injective
      (R := K) (P := Pext) (S̄ := κ)).2 hOwnerInj

/-- Helper for Chap10 Lemma 10 140 3: the localized target ring is formally smooth once its local
presentation has regular-sequence kernel and regular-local target. -/
private theorem closedPointFormalSmooth_of_regularLocal
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] {n : ℕ}
    (π : MvPolynomial (Fin n) K →ₐ[K] T) (hπsurj : Function.Surjective π)
    (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m))
    (hφregseq :
      (Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl).KernelIsGeneratedByRegularSequence) :
    let A := Localization.AtPrime m
    Algebra.FormallySmooth K A := by
  dsimp only
  let A := Localization.AtPrime m
  let m' : Ideal (MvPolynomial (Fin n) K) := Ideal.comap π.toRingHom m
  let P := Localization.AtPrime m'
  let φ : P →+* A := Localization.localRingHom m' m π.toRingHom rfl
  letI : Algebra P A := φ.toAlgebra
  letI : IsScalarTower K P A := localizedPresentation_isScalarTower (π := π) m
  let hφsurj : Function.Surjective φ := localizedPresentation_surjective π hπsurj m
  have hφfg : (RingHom.ker φ).FG := by
    -- Proof comment: finite presentation of `T` over the field `K` keeps the localized
    -- presentation kernel finitely generated.
    letI : Algebra.FinitePresentation K T :=
      (show Algebra.FiniteType K T ↔ Algebra.FinitePresentation K T from
        Algebra.FinitePresentation.of_finiteType).mp inferInstance
    simpa [P, A, φ, m'] using localizedPresentation_kernel_fg (π := π) hπsurj m
  letI : Algebra.FormallySmooth K P := inferInstance
  letI : Module.Finite P Ω[P⁄K] := KaehlerDifferential.finite K P
  letI : Module.Projective P Ω[P⁄K] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential (R := K) (A := P)
  letI : Module.Free P Ω[P⁄K] := Module.free_of_flat_of_isLocalRing
  have hcotangentInj :
      Function.Injective
        (KaehlerDifferential.cotangentComplexBaseChange K A P
          (IsLocalRing.ResidueField A)) := by
    -- Proof comment: the owner/displayed cotangent-complex comparison proved above already gives
    -- the injective Jacobian map in the stabilized local presentation normal form.
    simpa [A, P, φ, m'] using
      closedPointCotangentComplexBaseChange_injective
        (K := K) (T := T) (n := n) π hπsurj m hreg hφregseq
  -- Proof comment: apply the local Jacobian criterion in the canonical localized polynomial
  -- presentation once all finiteness and freeness side conditions have been installed.
  exact
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
      (R := K) (S := A) (P := P) hφsurj hφfg).2 hcotangentInj

/-- Helper for Chap10 Lemma 10 140 3: over a field, finite type algebras are finitely
presented. -/
private theorem finitePresentation_of_finiteType_field
    {R : Type*} [Field R] {A : Type*} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    Algebra.FinitePresentation R A := by
  -- Proof comment: over a field, finite type and finite presentation are equivalent.
  exact
    (show Algebra.FiniteType R A ↔ Algebra.FinitePresentation R A from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance

/-- Helper for Chap10 Lemma 10 140 3: over an algebraically closed field, a regular local ring at
a closed point should already be smooth at that point. -/
private theorem closedPointIsSmoothAt_of_regularLocal
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (m : Ideal T) [m.IsMaximal]
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    IsSmoothAt K m := by
  letI : Algebra.FinitePresentation K T := finitePresentation_of_finiteType_field
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp inferInstance
  have hφregseq :
      (Localization.localRingHom
        (Ideal.comap π.toRingHom m) m π.toRingHom rfl).KernelIsGeneratedByRegularSequence :=
    localizedPresentation_kernelIsGeneratedByRegularSequence
      (K := K) (T := T) π hπsurj m hreg
  -- Proof comment: after choosing any finite polynomial presentation of `T`, the previous helper
  -- upgrades the regular-local closed point to formal smoothness of the localization.
  simpa using
    closedPointFormalSmooth_of_regularLocal
      (K := K) (T := T) (n := n) π hπsurj m hreg hφregseq

/-- Helper for Chap10 Lemma 10 140 3: replacing the residue field of a maximal ideal by the
quotient field does not change the Kähler-fiber dimension. -/
private theorem finrank_residueField_kaehlerFiber_eq_quotient
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
    (m : Ideal T) [m.IsMaximal] :
    Module.finrank m.ResidueField (m.ResidueField ⊗[T] Ω[T⁄K]) =
      Module.finrank (T ⧸ m) ((T ⧸ m) ⊗[T] Ω[T⁄K]) := by
  -- Proof comment: the quotient-to-residue-field map is an isomorphism at a maximal ideal, and
  -- cancelling the intermediate tensor over `T ⧸ m` preserves finrank.
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange T (T ⧸ m) m.ResidueField
    m.ResidueField Ω[T⁄K]
  rw [← e.finrank_eq]
  exact Module.finrank_baseChange

/-- Helper for Chap10 Lemma 10 140 3: the canonical closed point over the residue-field closure
contracts back to the original prime ideal. -/
private theorem closedPointOverResidueClosure_comapAsIdeal
    (q : Ideal S) [q.IsPrime] :
    let K := AlgebraicClosure (Ideal.ResidueField q)
    let S_K := K ⊗[k] S
    ∀ qK : PrimeSpectrum S_K,
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK =
        ⟨q, inferInstance⟩ →
      q = Ideal.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK.asIdeal := by
  intro K S_K qK hqK
  -- Proof comment: the prime-spectrum contraction equality is definitionally the same statement
  -- after converting the prime to its underlying ideal.
  simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hqK).symm

/-- Helper for Chap10 Lemma 10 140 3: the Kähler-fiber dimension is unchanged after passing from
`q` to the closed point of `K ⊗[k] S` lying over `q`. -/
private theorem kaehlerFiberFinrank_eq_of_residueClosureBaseChange
    (q : Ideal S) [q.IsPrime] :
    let K := AlgebraicClosure (Ideal.ResidueField q)
    let S_K := K ⊗[k] S
    ∀ qK : PrimeSpectrum S_K,
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK =
        ⟨q, inferInstance⟩ →
      Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) =
        Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K]) := by
  intro K S_K qK hqK
  have hqIdeal :
      q =
        Ideal.comap (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom qK.asIdeal :=
    closedPointOverResidueClosure_comapAsIdeal (k := k) (S := S) q qK hqK
  let κmap : Ideal.ResidueField q →+* qK.asIdeal.ResidueField :=
    Ideal.ResidueField.map q qK.asIdeal
      (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom hqIdeal
  letI : Algebra (Ideal.ResidueField q) qK.asIdeal.ResidueField := κmap.toAlgebra
  letI : IsScalarTower S (Ideal.ResidueField q) qK.asIdeal.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simpa using Ideal.ResidueField.map_algebraMap q qK.asIdeal
      (Algebra.TensorProduct.includeRight : S →ₐ[k] S_K).toRingHom hqIdeal x
  letI : Algebra.IsPushout k K S S_K := Algebra.TensorProduct.isPushout
  -- Proof comment: first base change the downstairs fiber along `κ(q) → κ(qK)`.
  rw [← Module.finrank_baseChange
    (R := qK.asIdeal.ResidueField) (S := Ideal.ResidueField q)
    (M' := (Ideal.ResidueField q) ⊗[S] Ω[S⁄k])]
  let eResidue :
      qK.asIdeal.ResidueField ⊗[Ideal.ResidueField q]
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) ≃ₗ[qK.asIdeal.ResidueField]
        qK.asIdeal.ResidueField ⊗[S] Ω[S⁄k] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S (Ideal.ResidueField q)
      qK.asIdeal.ResidueField qK.asIdeal.ResidueField Ω[S⁄k]
  let eBaseSource :
      qK.asIdeal.ResidueField ⊗[S] Ω[S⁄k] ≃ₗ[qK.asIdeal.ResidueField]
        qK.asIdeal.ResidueField ⊗[S_K] (S_K ⊗[S] Ω[S⁄k]) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S S_K
      qK.asIdeal.ResidueField qK.asIdeal.ResidueField Ω[S⁄k]).symm
  let eBaseKaehler :
      qK.asIdeal.ResidueField ⊗[S_K] (S_K ⊗[S] Ω[S⁄k]) ≃ₗ[qK.asIdeal.ResidueField]
        qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K] :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl qK.asIdeal.ResidueField qK.asIdeal.ResidueField)
      (KaehlerDifferential.tensorKaehlerEquiv k K S S_K)
  -- Proof comment: then identify the upstairs fiber via the tensor-product Kähler base-change
  -- equivalence `S_K ⊗[S] Ω[S⁄k] ≃ Ω[S_K⁄K]`.
  exact (eResidue.trans eBaseSource).trans eBaseKaehler |>.finrank_eq

/-- Helper for Chap10 Lemma 10 140 3: over an algebraically closed field, smoothness at a prime
already forces the corresponding localization to be regular local. -/
private theorem regularLocalRing_of_isSmoothAt_viaResidueClosure
    {K : Type*} [Field K] [IsAlgClosed K] {T : Type*} [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T]
    (q : Ideal T) [q.IsPrime] (hsmooth : IsSmoothAt K q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  letI : Algebra.FinitePresentation K T := finitePresentation_of_finiteType_field
  obtain ⟨g, hgq, hstd⟩ :=
    IsSmoothAt.exists_notMem_isStandardSmooth (R := K) (S := T) q
  let qAway : Ideal (Localization.Away g) :=
    Ideal.map (algebraMap T (Localization.Away g)) q
  have hdisj :
      Disjoint ((Submonoid.powers g : Submonoid T) : Set T) (q : Set T) := by
    -- Proof comment: the chosen basic-open parameter avoids `q`, so no power of it can lie in
    -- the prime ideal.
    rw [Set.disjoint_iff]
    intro x hxpow hxq
    rcases hxpow with ⟨n, rfl⟩
    cases n with
    | zero =>
        simpa using hxq
    | succ n =>
        exact hgq ((Ideal.IsPrime.mem_of_pow_mem inferInstance (Nat.succ_ne_zero _) hxq))
  have hqAwayPrime : qAway.IsPrime := by
    -- Proof comment: localization away from `g` transports the prime `q` to the induced prime on
    -- the basic open `D(g)`.
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers g) (Localization.Away g) q inferInstance hdisj
  have hqAwayComap :
      Ideal.comap (algebraMap T (Localization.Away g)) qAway = q := by
    exact IsLocalization.comap_map_of_isPrime_disjoint
      (Submonoid.powers g) (Localization.Away g) inferInstance hdisj
  letI : qAway.IsPrime := hqAwayPrime
  have hregAway :
      IsRegularLocalRing (Localization.AtPrime qAway) :=
    isRegularLocalRing_localizationAtPrime_of_standardSmooth
      (K := K) (T := Localization.Away g) qAway
  letI : IsRegularLocalRing (Localization.AtPrime qAway) := hregAway
  letI : IsLocalization.AtPrime (Localization.AtPrime qAway) q := by
    simpa [hqAwayComap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g) (Localization.AtPrime qAway) qAway)
  let eUp :
      Localization.AtPrime q ≃ₐ[K] Localization.AtPrime qAway :=
    IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q) (Localization.AtPrime qAway)
  -- Route correction: stop before any residue-closure descent. The standard-smooth neighborhood
  -- already gives the required regularity after comparing the two prime localizations.
  have hregUp : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.of_ringEquiv eUp.symm.toRingEquiv
  exact hregUp

/-- Helper for Chap10 Lemma 10 140 3: smoothness at `q` forces the Kähler fiber to have the
expected point-dimension. -/
private theorem kaehlerFiberFinrank_eq_target_of_isSmoothAt
    (q : Ideal S) [q.IsPrime] (hsmooth : IsSmoothAt k q) :
    Module.finrank (Ideal.ResidueField q)
        ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) =
      ringKrullDim (Localization.AtPrime q) +
        Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := by
  let K := AlgebraicClosure (Ideal.ResidueField q)
  let S_K := K ⊗[k] S
  letI : Algebra.FiniteType K S_K := Algebra.FiniteType.baseChange K
  obtain ⟨qK, hqK, hqKmax, hdim⟩ :=
    exists_closedPoint_over_residueFieldClosure (k := k) (S := S) q
  letI : qK.asIdeal.IsMaximal := hqKmax
  have hsmoothUp : IsSmoothAt K qK.asIdeal := by
    -- Proof comment: pass to the closed point of the residue-field-closure base change, where
    -- smoothness is equivalent by the field-extension transport theorem.
    simpa [K, S_K, hqK] using
      (isSmoothAt_iff_isSmoothAt_tensor_fieldExtension
        (k := k) (K := K) (S := S) qK).mp hsmooth
  have hregUp : IsRegularLocalRing (Localization.AtPrime qK.asIdeal) :=
    regularLocalRing_of_isSmoothAt_viaResidueClosure
      (K := K) (T := S_K) qK.asIdeal hsmoothUp
  have hfiberUp :
      Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K]) =
        ringKrullDim (Localization.AtPrime qK.asIdeal) :=
    closedPointKaehlerFiberFinrank_eq_of_regularLocal
      (K := K) (T := S_K) qK.asIdeal hregUp
  -- Proof comment: compute the closed-point fiber upstairs from regularity, then transport both
  -- the Kähler-fiber finrank and the local dimension back downstairs.
  calc
    Module.finrank (Ideal.ResidueField q)
        ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) =
      Module.finrank qK.asIdeal.ResidueField
        (qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K]) := by
          exact kaehlerFiberFinrank_eq_of_residueClosureBaseChange
            (k := k) (S := S) q qK hqK
    _ = ringKrullDim (Localization.AtPrime qK.asIdeal) := hfiberUp
    _ = ringKrullDim (Localization.AtPrime q) +
          Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := hdim

/-- Helper for Chap10 Lemma 10 140 3: the Kähler-fiber dimension bound at `q` implies smoothness
at `q`. -/
private theorem isSmoothAt_of_kaehlerFiberFinrank_le_target
    (q : Ideal S) [q.IsPrime]
    (hle : Module.finrank (Ideal.ResidueField q)
        ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) ≤
      ringKrullDim (Localization.AtPrime q) +
        Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q))) :
    IsSmoothAt k q := by
  let K := AlgebraicClosure (Ideal.ResidueField q)
  let S_K := K ⊗[k] S
  letI : Algebra.FiniteType K S_K := Algebra.FiniteType.baseChange K
  obtain ⟨qK, hqK, hqKmax, hdim⟩ :=
    exists_closedPoint_over_residueFieldClosure (k := k) (S := S) q
  letI : qK.asIdeal.IsMaximal := hqKmax
  have hleUp :
      Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K]) ≤
        ringKrullDim (Localization.AtPrime qK.asIdeal) := by
    -- Proof comment: the residue-closure base change preserves the Kähler-fiber finrank, and the
    -- chosen closed point packages the matching local dimension identity upstairs.
    calc
      Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[S_K] Ω[S_K⁄K]) =
        Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) := by
            symm
            exact kaehlerFiberFinrank_eq_of_residueClosureBaseChange
              (k := k) (S := S) q qK hqK
      _ ≤ ringKrullDim (Localization.AtPrime q) +
            Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) := hle
      _ = ringKrullDim (Localization.AtPrime qK.asIdeal) := hdim.symm
  have hregUp : IsRegularLocalRing (Localization.AtPrime qK.asIdeal) :=
    closedPointIsRegularLocalRing_of_kaehlerFiberFinrank_le
      (K := K) (T := S_K) qK.asIdeal hleUp
  have hsmoothUp : IsSmoothAt K qK.asIdeal :=
    closedPointIsSmoothAt_of_regularLocal (K := K) (T := S_K) qK.asIdeal hregUp
  -- Proof comment: the closed-point criterion proves smoothness after residue-field closure, and
  -- the field-extension transport theorem descends it back to `q`.
  simpa [K, S_K, hqK] using
    (isSmoothAt_iff_isSmoothAt_tensor_fieldExtension
      (k := k) (K := K) (S := S) qK).mpr hsmoothUp

/-- Helper for Chap10 Lemma 10 140 3: the Kähler-fiber dimension bound at `q` forces the local
ring `S_q` to be regular. -/
private theorem isRegularLocalRing_of_isSmoothAt_aux
    {K : Type*} [Field K] {T : Type*} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
    (q : Ideal T) [q.IsPrime] (hsmooth : IsSmoothAt K q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨g, hgq, hstd⟩ :=
    IsSmoothAt.exists_notMem_isStandardSmooth (R := K) (S := T) q
  let qAway : Ideal (Localization.Away g) :=
    Ideal.map (algebraMap T (Localization.Away g)) q
  have hdisj :
      Disjoint ((Submonoid.powers g : Submonoid T) : Set T) (q : Set T) := by
    -- Proof comment: the standard-smooth neighborhood parameter `g` avoids `q`, so no power of
    -- `g` can lie in the prime ideal.
    rw [Set.disjoint_iff]
    intro x hxpow hxq
    rcases hxpow with ⟨n, rfl⟩
    cases n with
    | zero =>
        simpa using hxq
    | succ n =>
        exact hgq ((Ideal.IsPrime.mem_of_pow_mem inferInstance (Nat.succ_ne_zero _) hxq))
  have hqAwayPrime : qAway.IsPrime := by
    -- Proof comment: localizing away from `g` transports `q` to the corresponding prime upstairs.
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers g) (Localization.Away g) q inferInstance hdisj
  have hqAwayComap :
      Ideal.comap (algebraMap T (Localization.Away g)) qAway = q := by
    exact IsLocalization.comap_map_of_isPrime_disjoint
      (Submonoid.powers g) (Localization.Away g) inferInstance hdisj
  letI : qAway.IsPrime := hqAwayPrime
  have hregAway :
      IsRegularLocalRing (Localization.AtPrime qAway) :=
    isRegularLocalRing_localizationAtPrime_of_standardSmooth
      (K := K) (T := Localization.Away g) qAway
  letI : IsRegularLocalRing (Localization.AtPrime qAway) := hregAway
  letI : IsLocalization.AtPrime (Localization.AtPrime qAway) q := by
    -- Proof comment: the prime-localization of the away-localization is another model for `T_q`.
    simpa [hqAwayComap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g) (Localization.AtPrime qAway) qAway)
  let eUp :
      Localization.AtPrime q ≃ₐ[K] Localization.AtPrime qAway :=
    IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q) (Localization.AtPrime qAway)
  -- Route correction: use the standard-smooth neighborhood directly, instead of rebuilding the
  -- regularity criterion from the cotangent exact sequence.
  exact IsRegularLocalRing.of_ringEquiv eUp.symm.toRingEquiv

/-- Chap10 Lemma 10 140 3. Let `k` be a field, let `S` be a finite type `k`-algebra, and let `q`
be a prime ideal of `S`, corresponding to `x ∈ Spec(S)`. Then the following are equivalent:
`S` is smooth at `q` over `k`; the Kähler fiber `κ(q) ⊗[S] Ω[S⁄k]` has dimension at most the
point-dimension of `Spec(S)` at `x`, formalized as
`ringKrullDim (Localization.AtPrime q) + Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q))`;
and this dimension is exactly that same point-dimension. Moreover, if these conditions hold, then
the local ring `S_q`, formalized as `Localization.AtPrime q`, is regular. -/
@[stacks 00TT]
theorem isSmoothAt_tfae_finrank_kaehlerFiber_le_eq (q : Ideal S) [q.IsPrime] :
    List.TFAE
      ([ IsSmoothAt k q
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) ≤
            ringKrullDim (Localization.AtPrime q) +
              Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q))
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) =
            ringKrullDim (Localization.AtPrime q) +
              Cardinal.toNat (Algebra.trdeg k (Ideal.ResidueField q)) ] : List Prop) := by
  -- Proof comment: assemble the equivalence from the already-proved smoothness-to-equality,
  -- equality-to-inequality, and inequality-to-smoothness implications.
  tfae_have 1 → 3 := by
    intro hsmooth
    exact kaehlerFiberFinrank_eq_target_of_isSmoothAt (k := k) (S := S) q hsmooth
  tfae_have 3 → 2 := by
    intro heq
    -- Proof comment: the equality immediately gives the required upper bound.
    exact le_of_eq heq
  tfae_have 2 → 1 := by
    intro hle
    exact isSmoothAt_of_kaehlerFiberFinrank_le_target (k := k) (S := S) q hle
  tfae_finish

/-- If `S` is smooth at the prime `q` over the field `k`, formalized as `IsSmoothAt k q`,
then the local ring `S_q` is regular. -/
theorem isRegularLocalRing_of_isSmoothAt (q : Ideal S) [q.IsPrime] (hsmooth : IsSmoothAt k q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  -- Proof comment: smoothness gives a standard-smooth neighborhood of `q`, and smooth algebras
  -- over a field are regular rings; localizing at `q` preserves regularity.
  exact isRegularLocalRing_of_isSmoothAt_aux (K := k) (T := S) q hsmooth

end

end Algebra
