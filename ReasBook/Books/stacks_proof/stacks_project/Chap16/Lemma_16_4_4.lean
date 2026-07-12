import Mathlib
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_125_6
import StacksProject_2024.Chap10.Lemma_10_131_12
import StacksProject_2024.Chap10.Lemma_10_137_11
import StacksProject_2024.Chap10.Lemma_10_137_16
import StacksProject_2024.Chap10.Lemma_10_140_3
import StacksProject_2024.Chap16.Situation_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Ideal IsLocalRing
open RamificationOneDvrFactorizationSituation

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

section

/-- Helper for Lemma 16.4.4: flat finite type over the valuation ring `S.R` upgrades the algebra
`S.A` to finite presentation over `S.R`. -/
theorem finitePresentation_toA (S : RamificationOneDvrFactorizationSituation) :
    Algebra.FinitePresentation S.R S.A := by
  -- A discrete valuation ring is Noetherian, so finite type already implies finite presentation.
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Helper for Lemma 16.4.4: the prime `q = ker(φ)` lies over the generic point of `Spec(S.R)`. -/
theorem q_under_eq_bot (S : RamificationOneDvrFactorizationSituation) :
    S.q.under S.R = (⊥ : Ideal S.R) := by
  -- An element of `R` lands in `ker(φ)` exactly when its image in `Λ` vanishes.
  have hinj : Function.Injective (algebraMap S.R S.L) :=
    FaithfulSMul.algebraMap_injective S.R S.L
  ext x
  constructor
  · intro hx
    rw [Ideal.under_def, Ideal.mem_comap, S.mem_q_iff] at hx
    rw [Ideal.mem_bot]
    exact hinj <| by
      simpa [IsScalarTower.algebraMap_eq S.R S.A S.L] using hx
  · intro hx
    rw [Ideal.mem_bot] at hx
    rw [Ideal.under_def, Ideal.mem_comap, S.mem_q_iff]
    simpa [IsScalarTower.algebraMap_eq S.R S.A S.L, hx]

/-- Helper for Lemma 16.4.4: the prime `p = φ⁻¹(maximalIdeal Λ)` lies over the closed point of
`Spec(S.R)`. -/
theorem p_under_eq_maximalIdeal (S : RamificationOneDvrFactorizationSituation) :
    S.p.under S.R = maximalIdeal S.R := by
  -- The contraction of the maximal ideal along the local map `R → Λ` is the maximal ideal of `R`.
  simpa [RamificationOneDvrFactorizationSituation.p, Ideal.under_def, Ideal.comap_comap,
    IsScalarTower.algebraMap_eq S.R S.A S.L] using
    (IsLocalRing.maximalIdeal_comap (algebraMap S.R S.L))

/-- Helper for Lemma 16.4.4: the generic point `q` specializes to the closed point `p`. -/
theorem q_le_p (S : RamificationOneDvrFactorizationSituation) :
    S.q ≤ S.p := by
  -- Elements vanishing in `Λ` automatically land in its maximal ideal.
  intro x hx
  rw [S.mem_p_iff]
  rw [S.mem_q_iff] at hx
  simpa [hx] using (show (0 : S.L) ∈ maximalIdeal S.L from Ideal.zero_mem _)

/-- Helper for Lemma 16.4.4: the generic point `q` lies strictly below the closed point `p`. -/
theorem q_lt_p (S : RamificationOneDvrFactorizationSituation) :
    S.q < S.p := by
  -- The contraction data distinguish `q` from `p`, so the specialization is strict.
  refine lt_of_le_of_ne (q_le_p S) ?_
  intro hqp
  have hunder :
      S.q.under S.R = S.p.under S.R := congrArg (fun I : Ideal S.A ↦ I.under S.R) hqp
  have hmax_bot : maximalIdeal S.R = (⊥ : Ideal S.R) := by
    calc
      maximalIdeal S.R = S.p.under S.R := (p_under_eq_maximalIdeal S).symm
      _ = S.q.under S.R := hunder.symm
      _ = ⊥ := q_under_eq_bot S
  exact IsDiscreteValuationRing.not_a_field S.R hmax_bot

/-- Helper for Lemma 16.4.4: localizing the domain `S.R` at its generic point gives a
zero-dimensional local ring. -/
theorem ringKrullDim_localizationAtPrime_bot_eq_zero_of_domain
    (R : Type*) [CommRing R] [IsDomain R] :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal R)) = 0 := by
  -- Identify the generic localization with the fraction field and use that fields have dimension
  -- zero.
  letI : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal R).primeCompl)
        (Localization.AtPrime (⊥ : Ideal R)))
  let e : FractionRing R ≃ₐ[R] Localization.AtPrime (⊥ : Ideal R) :=
    FractionRing.algEquiv R (Localization.AtPrime (⊥ : Ideal R))
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing R)

/-- Helper for Lemma 16.4.4: localizing a discrete valuation ring at its maximal ideal preserves
the one-dimensionality of the base. -/
theorem ringKrullDim_localizationAtPrime_maximalIdeal_eq_one_of_dvr
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ringKrullDim (Localization.AtPrime (maximalIdeal R)) = 1 := by
  -- Rewrite the localized dimension as the height of the maximal ideal, then use the standard
  -- one-dimensionality of a nonfield DVR.
  calc
    ringKrullDim (Localization.AtPrime (maximalIdeal R)) = (maximalIdeal R).height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal R) _
    _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one R (IsDiscreteValuationRing.not_isField R)

/-- Helper for Lemma 16.4.4: the generic fiber of the free `S.L`-module
`S.L ⊗[S.A] Ω[S.A⁄S.R]` has the same rank as the original module over `S.L`. -/
theorem fractionRingL_finrank_tensor_kaehler_eq
    (S : RamificationOneDvrFactorizationSituation)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Module.finrank (FractionRing S.L) ((FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) =
      Module.finrank S.L (S.L ⊗[S.A] Ω[S.A⁄S.R]) := by
  letI : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R]) := hfree
  -- Finite free modules keep their rank after extending scalars to the fraction field.
  exact Module.finrank_baseChange
    (S := S.L) (R := FractionRing S.L) (M' := S.L ⊗[S.A] Ω[S.A⁄S.R])

/-- Helper for Lemma 16.4.4: the special fiber of the free `S.L`-module
`S.L ⊗[S.A] Ω[S.A⁄S.R]` has the same rank as the original module over `S.L`. -/
theorem residueFieldL_finrank_tensor_kaehler_eq
    (S : RamificationOneDvrFactorizationSituation)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Module.finrank (maximalIdeal S.L).ResidueField
        (((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) =
      Module.finrank S.L (S.L ⊗[S.A] Ω[S.A⁄S.R]) := by
  letI : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R]) := hfree
  -- The same base-change rank formula applies to the residue-field fiber.
  exact Module.finrank_baseChange
    (S := S.L) (R := (maximalIdeal S.L).ResidueField)
    (M' := S.L ⊗[S.A] Ω[S.A⁄S.R])

/-- Helper for Lemma 16.4.4: the generic and special fibers of the free `S.L`-module
`S.L ⊗[S.A] Ω[S.A⁄S.R]` have the same finite dimension. -/
theorem fractionRingL_finrank_eq_residueFieldL_finrank_tensor_kaehler
    (S : RamificationOneDvrFactorizationSituation)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Module.finrank (FractionRing S.L) ((FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) =
      Module.finrank (maximalIdeal S.L).ResidueField
        (((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) := by
  -- Compare both fibers with the common rank over `S.L`.
  rw [fractionRingL_finrank_tensor_kaehler_eq S hfree,
    residueFieldL_finrank_tensor_kaehler_eq S hfree]

/-- Helper for Lemma 16.4.4: if the generic fiber of the free `S.L`-module
`S.L ⊗[S.A] Ω[S.A⁄S.R]` has dimension `d`, then the special fiber over `Λ / πΛ` has the same
dimension. -/
theorem residueFieldL_finrank_eq_d_of_generic_rank
    (S : RamificationOneDvrFactorizationSituation)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) {d : ℕ}
    (hd :
      Module.finrank (FractionRing S.L)
          ((FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) = d) :
    Module.finrank (maximalIdeal S.L).ResidueField
        (((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) = d := by
  -- Compare the generic and special fibers through the common `S.L`-rank.
  rw [← fractionRingL_finrank_eq_residueFieldL_finrank_tensor_kaehler S hfree]
  exact hd

/-- Helper for Lemma 16.4.4: the residue field of the generic point of the domain `S.R` is its
fraction field. This packages the flatness needed for generic-fiber base change. -/
theorem genericResidueField_isFractionRing (S : RamificationOneDvrFactorizationSituation) :
    IsFractionRing S.R ((⊥ : Ideal S.R).ResidueField) := by
  -- Identify `R / (0)` with `R`, then apply the standard fraction-field owner theorem.
  let e : S.R ≃ₐ[S.R] S.R ⧸ (⊥ : Ideal S.R) := (AlgEquiv.quotientBot S.R S.R).symm
  refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
  intro x
  change algebraMap S.R ((⊥ : Ideal S.R).ResidueField) x =
    algebraMap (S.R ⧸ (⊥ : Ideal S.R)) ((⊥ : Ideal S.R).ResidueField) (Ideal.Quotient.mk _ x)
  symm
  exact show
      algebraMap (S.R ⧸ (⊥ : Ideal S.R)) ((⊥ : Ideal S.R).ResidueField)
          (Ideal.Quotient.mk (⊥ : Ideal S.R) x) =
        algebraMap S.R ((⊥ : Ideal S.R).ResidueField) x by
    rfl

/-- Helper for Lemma 16.4.4: equal prime ideals have canonically equivalent residue fields as
algebras over the ambient base ring. -/
noncomputable def residueFieldAlgEquivOfEq
    {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[R] J.ResidueField := by
  cases h
  exact (AlgEquiv.refl : I.ResidueField ≃ₐ[R] I.ResidueField)

/-- Helper for Lemma 16.4.4: equal prime ideals have canonically equivalent localizations at the
corresponding prime. -/
noncomputable def localizationAtPrimeAlgEquivOfEq
    {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I = J) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J := by
  cases h
  exact (AlgEquiv.refl : Localization.AtPrime I ≃ₐ[R] Localization.AtPrime I)

/-- Helper for Lemma 16.4.4: after identifying `q ∩ R` with the zero ideal, the generic base
field `κ(q ∩ R)` is canonically the fraction field of `S.R`. -/
noncomputable def genericResidueField_algEquiv_fractionRing
    (S : RamificationOneDvrFactorizationSituation) :
    FractionRing S.R ≃ₐ[S.R] ((S.q.under S.R).ResidueField) := by
  -- Route correction: package the source proof's generic base field once, so later rank
  -- transport can use a concrete fraction-field owner instead of repeated `q ∩ R = (0)` rewrites.
  letI : IsFractionRing S.R ((⊥ : Ideal S.R).ResidueField) := genericResidueField_isFractionRing S
  let e₀ : FractionRing S.R ≃ₐ[S.R] ((⊥ : Ideal S.R).ResidueField) :=
    FractionRing.algEquiv S.R ((⊥ : Ideal S.R).ResidueField)
  let e₁ : ((⊥ : Ideal S.R).ResidueField) ≃ₐ[S.R] ((S.q.under S.R).ResidueField) :=
    residueFieldAlgEquivOfEq (R := S.R) (q_under_eq_bot S).symm
  exact e₀.trans e₁

/-- Helper for Lemma 16.4.4: the canonical prime of the fiber over `q` contracts back to `q`. -/
theorem fiberPrimeAt_comap_eq
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A) :
    PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] ((q.asIdeal.under R).Fiber A)).toRingHom)
        (fiberPrimeAt R A q) =
      q := by
  -- Unfold the defining equivalence between primes of the fiber and primes above `q ∩ R`.
  change
    ((PrimeSpectrum.preimageEquivFiber R A (PrimeSpectrum.comap (algebraMap R A) q)).symm
      (fiberPrimeAt R A q)).1 = q
  exact congrArg
    (fun x :
      PrimeSpectrum.comap (algebraMap R A) ⁻¹'
        ({PrimeSpectrum.comap (algebraMap R A) q} : Set (PrimeSpectrum R)) ↦ x.1)
    ((PrimeSpectrum.preimageEquivFiber R A (PrimeSpectrum.comap (algebraMap R A) q)).symm_apply_apply
      ⟨q, rfl⟩)

/-- Helper for Lemma 16.4.4: base changing the basic open `D(g)` along `R → K` is the basic
open cut out by the image of `g` in `K ⊗[R] A`. -/
noncomputable def tensor_localizationAway_algEquiv_includeRight
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    {K : Type*} [CommRing K] [Algebra R K] (g : A) :
    K ⊗[R] Localization.Away g ≃ₐ[K]
      Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) g) := by
  -- Reassociate the base change to `((K ⊗[R] A) ⊗[A] A[1 / g])`, swap the `A`-tensor factors,
  -- and then apply the owner localization equivalence on the right tensor factor.
  let F := K ⊗[R] A
  let e₁ : K ⊗[R] Localization.Away g ≃ₐ[K] F ⊗[A] Localization.Away g :=
    (Algebra.IsPushout.cancelBaseChangeAlg R K A F (Localization.Away g)).symm
  let e₂ : F ⊗[A] Localization.Away g ≃ₐ[F] Localization.Away g ⊗[A] F :=
    Algebra.TensorProduct.commRight A F (Localization.Away g)
  let e₃ : Localization.Away g ⊗[A] F ≃ₐ[F]
      Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[R] F) g) :=
    IsLocalization.Away.tensorRightEquiv F g (Localization.Away g)
  refine
    { __ := e₁.toRingEquiv.trans e₂.toRingEquiv |>.trans e₃.toRingEquiv
      commutes' := ?_ }
  intro x
  change e₃ (e₂ (e₁ (algebraMap K (K ⊗[R] Localization.Away g) x))) = _
  calc
    e₃ (e₂ (e₁ (algebraMap K (K ⊗[R] Localization.Away g) x)))
        = e₃ (e₂ (algebraMap K (F ⊗[A] Localization.Away g) x)) := by
            rw [e₁.commutes]
    _ = e₃ (e₂ (algebraMap F (F ⊗[A] Localization.Away g) (algebraMap K F x))) := by
          rw [IsScalarTower.algebraMap_apply K F (F ⊗[A] Localization.Away g)]
    _ = e₃ (algebraMap F (Localization.Away g ⊗[A] F) (algebraMap K F x)) := by
          rw [e₂.commutes]
    _ = algebraMap F
          (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[R] F) g))
          (algebraMap K F x) := by
          rw [e₃.commutes]
    _ = algebraMap K
          (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[R] F) g)) x := by
          rw [IsScalarTower.algebraMap_apply K F
            (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[R] F) g))]

/-- Helper for Lemma 16.4.4: smoothness at `q` base-changes to the generic fiber over
`q ∩ R = (0)`. This isolates the source proof's first geometric move before any rank transport. -/
theorem genericFiber_smoothAtPrime_at_qFiber
    (S : RamificationOneDvrFactorizationSituation)
    (hAq : Algebra.SmoothAtPrime S.R S.A S.qPoint) :
    Algebra.SmoothAtPrime (S.q.under S.R).ResidueField
      ((S.q.under S.R).Fiber S.A) (fiberPrimeAt S.R S.A S.qPoint) := by
  -- Route correction: use a standard-smooth basic open around `q`, then base change that chart
  -- to the generic fiber and identify the result with the corresponding away-localization.
  letI : Algebra.FinitePresentation S.R S.A := finitePresentation_toA S
  letI : IsSmoothAt S.R S.q := by
    simpa using (smoothAtPrime_iff_isSmoothAt S.R S.A S.qPoint).mp hAq
  obtain ⟨g, hgq, hstd⟩ := IsSmoothAt.exists_notMem_isStandardSmooth S.R S.q
  refine ⟨
    (Algebra.TensorProduct.includeRight :
      S.A →ₐ[S.R] ((S.q.under S.R).Fiber S.A)) g,
    ?_,
    ?_⟩
  · -- The image of `g` still avoids the fiber prime because that prime contracts back to `q`.
    let iq :
        S.A →ₐ[S.R] (((S.q.under S.R).ResidueField) ⊗[S.R] S.A) :=
      Algebra.TensorProduct.includeRight
    intro hgFiber
    have hgcomap :
        g ∈ (PrimeSpectrum.comap iq.toRingHom (fiberPrimeAt S.R S.A S.qPoint)).asIdeal := by
      change iq g ∈ (fiberPrimeAt S.R S.A S.qPoint).asIdeal
      simpa using hgFiber
    have hideal :
        (PrimeSpectrum.comap iq.toRingHom (fiberPrimeAt S.R S.A S.qPoint)).asIdeal =
          S.qPoint.asIdeal := by
      simpa using congrArg PrimeSpectrum.asIdeal
        (fiberPrimeAt_comap_eq (R := S.R) (A := S.A) S.qPoint)
    exact hgq <| by
      have hgqPoint : g ∈ S.qPoint.asIdeal := by
        rw [← hideal]
        exact hgcomap
      simpa using hgqPoint
  · -- Standard smoothness survives base change, and the tensor/away comparison transports it to
    -- the desired principal localization in the fiber ring.
    let iq :
        S.A →ₐ[S.R] (((S.q.under S.R).ResidueField) ⊗[S.R] S.A) :=
      Algebra.TensorProduct.includeRight
    let e :
        ((S.q.under S.R).ResidueField) ⊗[S.R] Localization.Away g ≃ₐ[
          (S.q.under S.R).ResidueField]
          Localization.Away (iq g) :=
      tensor_localizationAway_algEquiv_includeRight
        (R := S.R) (A := S.A) (K := (S.q.under S.R).ResidueField) g
    letI : IsStandardSmooth S.R (Localization.Away g) := hstd
    letI :
        IsStandardSmooth (S.q.under S.R).ResidueField
          (((S.q.under S.R).ResidueField) ⊗[S.R] Localization.Away g) := by
      infer_instance
    letI : IsStandardSmooth (S.q.under S.R).ResidueField (Localization.Away (iq g)) :=
      IsStandardSmooth.of_algEquiv e
    infer_instance

/-- Helper for Lemma 16.4.4: the height jump from `q < p` already yields the additive comparison
`dim_q(A/R) + 1 ≤ dim_p(A/R) + 1` from the source proof. -/
theorem relativeDimensionAt_q_add_one_le_relativeDimensionAt_p_add_one
    (S : RamificationOneDvrFactorizationSituation) :
    relativeDimensionAt S.R S.A S.qPoint + 1 ≤
      relativeDimensionAt S.R S.A S.pPoint + 1 := by
  letI : IsNoetherianRing S.A := Algebra.FiniteType.isNoetherianRing S.R S.A
  letI : Algebra.HasGoingDown S.R S.A := by infer_instance
  let qR : Ideal S.R := S.q.under S.R
  let pR : Ideal S.R := S.p.under S.R
  have hq_formula :
      ringKrullDim (Localization.AtPrime S.q) =
        ringKrullDim (Localization.AtPrime qR) +
          relativeDimensionAt S.R S.A S.qPoint := by
    -- This is the flat local dimension formula at the generic point `q`.
    simpa [qR, relativeDimensionAt, RamificationOneDvrFactorizationSituation.qPoint] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        (R := S.R) (S := S.A) S.qPoint
  have hp_formula :
      ringKrullDim (Localization.AtPrime S.p) =
        ringKrullDim (Localization.AtPrime pR) +
          relativeDimensionAt S.R S.A S.pPoint := by
    -- Apply the same formula at the closed point `p`.
    simpa [pR, relativeDimensionAt, RamificationOneDvrFactorizationSituation.pPoint] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        (R := S.R) (S := S.A) S.pPoint
  have hq_base_zero : ringKrullDim (Localization.AtPrime qR) = 0 := by
    -- After contracting `q` to the zero ideal, the base localization is the fraction field.
    have hqR : qR = ⊥ := by
      simpa [qR] using q_under_eq_bot S
    let e : Localization.AtPrime qR ≃ₐ[S.R] Localization.AtPrime (⊥ : Ideal S.R) :=
      localizationAtPrimeAlgEquivOfEq (R := S.R) hqR
    calc
      ringKrullDim (Localization.AtPrime qR) =
          ringKrullDim (Localization.AtPrime (⊥ : Ideal S.R)) := by
            exact ringKrullDim_eq_of_ringEquiv e.toRingEquiv
      _ = 0 := ringKrullDim_localizationAtPrime_bot_eq_zero_of_domain (R := S.R)
  have hp_base_one : ringKrullDim (Localization.AtPrime pR) = 1 := by
    -- After contracting `p` to the maximal ideal, the base localization is one-dimensional.
    have hpR : pR = maximalIdeal S.R := by
      simpa [pR] using p_under_eq_maximalIdeal S
    let e : Localization.AtPrime pR ≃ₐ[S.R] Localization.AtPrime (maximalIdeal S.R) :=
      localizationAtPrimeAlgEquivOfEq (R := S.R) hpR
    calc
      ringKrullDim (Localization.AtPrime pR) =
          ringKrullDim (Localization.AtPrime (maximalIdeal S.R)) := by
            exact ringKrullDim_eq_of_ringEquiv e.toRingEquiv
      _ = 1 := ringKrullDim_localizationAtPrime_maximalIdeal_eq_one_of_dvr (R := S.R)
  have hq_eq :
      relativeDimensionAt S.R S.A S.qPoint =
        ringKrullDim (Localization.AtPrime S.q) := by
    -- Over the generic point of `Spec R`, the base contribution vanishes.
    rw [hq_base_zero, zero_add] at hq_formula
    simpa using hq_formula.symm
  have hp_eq :
      ringKrullDim (Localization.AtPrime S.p) =
        relativeDimensionAt S.R S.A S.pPoint + 1 := by
    -- Over the closed point of the DVR, the base contributes exactly `1`.
    rw [hp_base_one] at hp_formula
    calc
      ringKrullDim (Localization.AtPrime S.p) = 1 + relativeDimensionAt S.R S.A S.pPoint :=
        hp_formula
      _ = relativeDimensionAt S.R S.A S.pPoint + 1 := by rw [add_comm]
  have hheight :
      ringKrullDim (Localization.AtPrime S.q) + 1 ≤
        ringKrullDim (Localization.AtPrime S.p) := by
    -- Strict specialization gives the corresponding height jump in `Spec A`.
    have hprime :
        S.q.primeHeight + 1 ≤ S.p.primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt (q_lt_p S)
    have hprime' :
        ((S.q.primeHeight : ℕ∞) : WithBot ℕ∞) + 1 ≤
          ((S.p.primeHeight : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast hprime
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height S.q (Localization.AtPrime S.q),
      Ideal.height_eq_primeHeight,
      IsLocalization.AtPrime.ringKrullDim_eq_height S.p (Localization.AtPrime S.p),
      Ideal.height_eq_primeHeight]
    exact hprime'
  calc
    relativeDimensionAt S.R S.A S.qPoint + 1 =
        ringKrullDim (Localization.AtPrime S.q) + 1 := by rw [hq_eq]
    _ ≤ ringKrullDim (Localization.AtPrime S.p) := hheight
    _ = relativeDimensionAt S.R S.A S.pPoint + 1 := hp_eq

/-- Helper for Lemma 16.4.4: the generic residue field `κ(q ∩ R)` used in the source proof. -/
noncomputable abbrev qFiberBase (S : RamificationOneDvrFactorizationSituation) :=
  (S.q.under S.R).ResidueField

/-- Helper for Lemma 16.4.4: the generic fiber algebra `κ(q ∩ R) ⊗[R] A`. -/
noncomputable abbrev qFiberRing (S : RamificationOneDvrFactorizationSituation) :=
  (S.q.under S.R).Fiber S.A

/-- Helper for Lemma 16.4.4: the canonical prime of the generic fiber lying over `q`. -/
noncomputable abbrev qFiberPrime (S : RamificationOneDvrFactorizationSituation) :
    PrimeSpectrum (qFiberRing S) :=
  fiberPrimeAt S.R S.A S.qPoint

/-- Helper for Lemma 16.4.4: the closed residue field `κ(p ∩ R)` used in the source proof. -/
noncomputable abbrev pFiberBase (S : RamificationOneDvrFactorizationSituation) :=
  (S.p.under S.R).ResidueField

/-- Helper for Lemma 16.4.4: the closed fiber algebra `κ(p ∩ R) ⊗[R] A`. -/
noncomputable abbrev pFiberRing (S : RamificationOneDvrFactorizationSituation) :=
  (S.p.under S.R).Fiber S.A

/-- Helper for Lemma 16.4.4: the canonical prime of the closed fiber lying over `p`. -/
noncomputable abbrev pFiberPrime (S : RamificationOneDvrFactorizationSituation) :
    PrimeSpectrum (pFiberRing S) :=
  fiberPrimeAt S.R S.A S.pPoint

/-- Helper for Lemma 16.4.4: a prime of a global fiber is determined by its contraction back to
the original prime of `Spec A`. -/
theorem fiberPrimeAt_eq_of_includeRight_comap_eq
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A)
    (r : PrimeSpectrum ((q.asIdeal.under R).Fiber A))
    (h :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight :
            A →ₐ[R] ((q.asIdeal.under R).Fiber A)).toRingHom) r =
        q) :
    r = fiberPrimeAt R A q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  -- Proof comment: move `r` back through the spectrum/fiber equivalence and use the contraction
  -- hypothesis to identify the corresponding prime of `A`.
  have hs :
      ((PrimeSpectrum.preimageEquivFiber R A p).symm r) = ⟨q, by simp [p]⟩ := by
    apply Subtype.ext
    simpa [p] using h
  have h1 :
      r =
        PrimeSpectrum.preimageEquivFiber R A p
          (((PrimeSpectrum.preimageEquivFiber R A p).symm r)) := by
    symm
    exact (PrimeSpectrum.preimageEquivFiber R A p).apply_symm_apply r
  have h2 :
      PrimeSpectrum.preimageEquivFiber R A p
          (((PrimeSpectrum.preimageEquivFiber R A p).symm r)) =
        PrimeSpectrum.preimageEquivFiber R A p ⟨q, by rfl⟩ := by
    rw [hs]
  have h3 :
      PrimeSpectrum.preimageEquivFiber R A p ⟨q, by rfl⟩ = fiberPrimeAt R A q := by
    simp [fiberPrimeAt, p]
  exact h1.trans (h2.trans h3)

/-- Helper for Lemma 16.4.4: the generic fiber is finitely presented over its base field. -/
theorem qFiberFinitePresentation (S : RamificationOneDvrFactorizationSituation) :
    Algebra.FinitePresentation (qFiberBase S) (qFiberRing S) := by
  -- Proof comment: finite type over a field is finite presentation, and fiber formation is a
  -- base change of the given finite-type algebra `S.A`.
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Helper for Lemma 16.4.4: the closed fiber is finitely presented over its base field. -/
theorem pFiberFinitePresentation (S : RamificationOneDvrFactorizationSituation) :
    Algebra.FinitePresentation (pFiberBase S) (pFiberRing S) := by
  -- Proof comment: as for the generic fiber, finite type is preserved under base change to the
  -- residue field and hence upgrades to finite presentation over that field.
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Helper for Lemma 16.4.4: the generic `Λ`-fiber finrank of `Ω[A⁄R]`. -/
noncomputable abbrev fractionRingLKaehlerFinrank
    (S : RamificationOneDvrFactorizationSituation) : ℕ :=
  Module.finrank (FractionRing S.L)
    ((FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]))

/-- Helper for Lemma 16.4.4: the closed `Λ / πΛ`-fiber finrank of `Ω[A⁄R]`. -/
noncomputable abbrev residueFieldLKaehlerFinrank
    (S : RamificationOneDvrFactorizationSituation) : ℕ :=
  Module.finrank (maximalIdeal S.L).ResidueField
    (((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]))

/-- Helper for Lemma 16.4.4: the zero-residue field of `Frac(Λ)` used to keep the generic
transport on the residue-field side of the cotangent criterion. -/
noncomputable abbrev qFiberTargetField
    (S : RamificationOneDvrFactorizationSituation) :=
  FractionRing S.L

/-- Helper for Lemma 16.4.4: `qFiberTargetField S` carries the expected field structure. -/
noncomputable instance qFiberTargetFieldAddCommMonoid
    (S : RamificationOneDvrFactorizationSituation) : AddCommMonoid (qFiberTargetField S) := by
  change AddCommMonoid (FractionRing S.L)
  infer_instance

/-- Helper for Lemma 16.4.4: `qFiberTargetField S` carries the expected field structure. -/
noncomputable instance qFiberTargetFieldField
    (S : RamificationOneDvrFactorizationSituation) : Field (qFiberTargetField S) := by
  delta qFiberTargetField
  infer_instance

/-- Helper for Lemma 16.4.4: a ring map to a field with kernel exactly the prime `I` factors
through the residue field of `I`. -/
noncomputable def residueFieldLiftOfComapEqField
    {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
    (I : Ideal A) [I.IsPrime]
    (hf : Ideal.comap (algebraMap A K) (⊥ : Ideal K) = I) :
    I.ResidueField →ₐ[A] K := by
  -- Proof comment: `liftₐ` applies because `I` maps to zero and every element outside `I`
  -- maps to a nonzero, hence invertible, element of the field `K`.
  refine Ideal.ResidueField.liftₐ I (IsScalarTower.toAlgHom A A K) ?_ ?_
  · intro x hx
    change algebraMap A K x = 0
    rw [← Ideal.mem_comap, hf]
    exact hx
  · intro x hx
    change IsUnit (algebraMap A K x)
    refine isUnit_iff_ne_zero.mpr ?_
    intro hzero
    apply hx
    rw [← hf, Ideal.mem_comap, hzero]
    exact Ideal.zero_mem _

/-- Helper for Lemma 16.4.4: the residue-field lift recovers the original field-valued map after
precomposing with the quotient map to the residue field. -/
theorem residueFieldLiftOfComapEqField_comp_toAlgHom
    {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
    (I : Ideal A) [I.IsPrime]
    (hf : Ideal.comap (algebraMap A K) (⊥ : Ideal K) = I) :
    (residueFieldLiftOfComapEqField (A := A) (K := K) I hf).comp
        (IsScalarTower.toAlgHom A A I.ResidueField) =
      IsScalarTower.toAlgHom A A K := by
  -- Proof comment: this is the owner computation rule for `Ideal.ResidueField.liftₐ`.
  simpa [residueFieldLiftOfComapEqField, hf] using
    (Ideal.ResidueField.liftₐ_comp_toAlgHom
      I (IsScalarTower.toAlgHom A A K)
      (by
        intro x hx
        change algebraMap A K x = 0
        rw [← Ideal.mem_comap, hf]
        exact hx)
      (by
        intro x hx
        change IsUnit (algebraMap A K x)
        refine isUnit_iff_ne_zero.mpr ?_
        intro hzero
        apply hx
        rw [← hf, Ideal.mem_comap, hzero]
        exact Ideal.zero_mem _))

/-- Helper for Lemma 16.4.4: in `WithBot ℕ∞`, a finite bound can cancel the trailing `+ 1`
appearing in the source proof's dimension comparison. -/
theorem natCast_le_of_add_one_le_add_one
    {n : ℕ} {d : WithBot ℕ∞}
    (h : ((n : WithBot ℕ∞) + 1) ≤ d + 1) :
    (n : WithBot ℕ∞) ≤ d := by
  -- Proof comment: split according to whether `d` is bottom, finite, or top; only the finite
  -- case needs an ordinary natural-number cancellation.
  cases d with
  | bot =>
      simp at h
  | coe d =>
      cases d with
      | top =>
          simp
      | coe m =>
          have hm : n + 1 ≤ m + 1 := by
            exact_mod_cast h
          exact_mod_cast Nat.succ_le_succ_iff.mp hm

/-- Helper for Lemma 16.4.4: the Kähler fiber over the generic fiber prime. -/
noncomputable abbrev qFiberKaehlerFiber
    (S : RamificationOneDvrFactorizationSituation) :=
  ((qFiberPrime S).asIdeal.ResidueField) ⊗[qFiberRing S] Ω[qFiberRing S⁄qFiberBase S]

/-- Helper for Lemma 16.4.4: the generic Kähler fiber is naturally a module over `κ(q)`. -/
noncomputable instance qFiberKaehlerFiberModule
    (S : RamificationOneDvrFactorizationSituation) :
    Module (qFiberPrime S).asIdeal.ResidueField (qFiberKaehlerFiber S) := by
  -- Proof comment: expand the abbreviation once and use the canonical left tensor-module.
  delta qFiberKaehlerFiber
  infer_instance

/-- Helper for Lemma 16.4.4: the Kähler fiber over the closed fiber prime. -/
noncomputable abbrev pFiberKaehlerFiber
    (S : RamificationOneDvrFactorizationSituation) :=
  ((pFiberPrime S).asIdeal.ResidueField) ⊗[pFiberRing S] Ω[pFiberRing S⁄pFiberBase S]

/-- Helper for Lemma 16.4.4: the closed Kähler fiber is naturally a module over `κ(p)`. -/
noncomputable instance pFiberKaehlerFiberModule
    (S : RamificationOneDvrFactorizationSituation) :
    Module (pFiberPrime S).asIdeal.ResidueField (pFiberKaehlerFiber S) := by
  -- Proof comment: the closed fiber has the same canonical left tensor-module structure.
  delta pFiberKaehlerFiber
  infer_instance

/-- Helper for Lemma 16.4.4: evaluate the generic fiber `κ(q ∩ R) ⊗[R] A` inside
`Frac(Λ)`. This is the source proof's generic-point comparison map. -/
noncomputable def qFiberEvaluationMap
    (S : RamificationOneDvrFactorizationSituation) :
    qFiberRing S →ₐ[S.R] FractionRing S.L := by
  letI : Algebra S.R (FractionRing S.L) := inferInstance
  letI : FaithfulSMul S.R (FractionRing S.L) := by
    exact (faithfulSMul_iff_algebraMap_injective S.R (FractionRing S.L)).2
      (FaithfulSMul.algebraMap_injective S.R (FractionRing S.L))
  let hκ : FractionRing S.R ≃ₐ[S.R] qFiberBase S :=
    genericResidueField_algEquiv_fractionRing S
  let fracRToFracL : FractionRing S.R →+* FractionRing S.L :=
    IsFractionRing.lift (K := FractionRing S.R) (L := FractionRing S.L)
      (g := algebraMap S.R (FractionRing S.L))
      (FaithfulSMul.algebraMap_injective S.R (FractionRing S.L))
  let κToFracL : qFiberBase S →ₐ[S.R] FractionRing S.L :=
    { toRingHom := fracRToFracL.comp hκ.symm.toRingHom
      commutes' := by
        intro r
        -- Proof comment: both routes out of `κ(q ∩ R)` are induced from the same map
        -- `R → Frac(Λ)`.
        change fracRToFracL (hκ.symm (algebraMap S.R (qFiberBase S) r)) =
          algebraMap S.R (FractionRing S.L) r
        rw [hκ.symm.commutes]
        simpa [fracRToFracL] using
          IsFractionRing.lift_algebraMap
            (A := S.R)
            (K := FractionRing S.R)
            (L := FractionRing S.L)
            (g := algebraMap S.R (FractionRing S.L))
            (FaithfulSMul.algebraMap_injective S.R (FractionRing S.L))
            r }
  exact
    Algebra.TensorProduct.lift
      κToFracL
      (IsScalarTower.toAlgHom S.R S.A (FractionRing S.L))
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Lemma 16.4.4: the generic evaluation map cuts out exactly the canonical prime of
the generic fiber lying over `q`. -/
theorem qFiberEvaluationMap_comap_eq_qFiberPrime
    (S : RamificationOneDvrFactorizationSituation) :
    Ideal.comap (qFiberEvaluationMap S).toRingHom (⊥ : Ideal (FractionRing S.L)) =
      (qFiberPrime S).asIdeal := by
  let r : PrimeSpectrum (qFiberRing S) :=
    ⟨Ideal.comap (qFiberEvaluationMap S).toRingHom (⊥ : Ideal (FractionRing S.L)), inferInstance⟩
  have hcomap :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] qFiberRing S).toRingHom) r =
        S.qPoint := by
    apply PrimeSpectrum.ext
    ext x
    -- Proof comment: on the `A`-generator, the generic evaluation map is just `A → Λ → Frac(Λ)`.
    change qFiberEvaluationMap S
        ((Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] qFiberRing S) x) ∈
          (⊥ : Ideal (FractionRing S.L)) ↔
        x ∈ S.q
    rw [Ideal.mem_bot]
    have hfrac :
        algebraMap S.A (FractionRing S.L) x = 0 ↔ S.phi x = 0 := by
      constructor
      · intro hx
        have hinj : Function.Injective (algebraMap S.L (FractionRing S.L)) :=
          FaithfulSMul.algebraMap_injective S.L (FractionRing S.L)
        apply hinj
        simpa [IsScalarTower.algebraMap_eq S.A S.L (FractionRing S.L)] using hx
      · intro hx
        simpa [IsScalarTower.algebraMap_eq S.A S.L (FractionRing S.L), hx]
    simpa [qFiberEvaluationMap, S.mem_q_iff] using hfrac
  have hr : r = qFiberPrime S :=
    fiberPrimeAt_eq_of_includeRight_comap_eq S.qPoint r hcomap
  simpa [r] using congrArg PrimeSpectrum.asIdeal hr

/-- Helper for Lemma 16.4.4: evaluate the closed fiber `κ(p ∩ R) ⊗[R] A` inside the residue field
`κ(maximalIdeal Λ)`. This is the source proof's special-fiber comparison map. -/
noncomputable def pFiberEvaluationMap
    (S : RamificationOneDvrFactorizationSituation) :
    pFiberRing S →ₐ[S.R] (maximalIdeal S.L).ResidueField := by
  let κToRes : pFiberBase S →ₐ[S.R] (maximalIdeal S.L).ResidueField :=
    Ideal.ResidueField.mapₐ (S.p.under S.R) (maximalIdeal S.L) (Algebra.ofId S.R S.L) <| by
      simpa [p_under_eq_maximalIdeal S] using
        (IsLocalRing.maximalIdeal_comap (algebraMap S.R S.L)).symm
  exact
    Algebra.TensorProduct.lift
      κToRes
      (IsScalarTower.toAlgHom S.R S.A ((maximalIdeal S.L).ResidueField))
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Lemma 16.4.4: the closed evaluation map cuts out exactly the canonical prime of
the closed fiber lying over `p`. -/
theorem pFiberEvaluationMap_comap_eq_pFiberPrime
    (S : RamificationOneDvrFactorizationSituation) :
    Ideal.comap (pFiberEvaluationMap S).toRingHom
        (⊥ : Ideal ((maximalIdeal S.L).ResidueField)) =
      (pFiberPrime S).asIdeal := by
  let r : PrimeSpectrum (pFiberRing S) :=
    ⟨Ideal.comap (pFiberEvaluationMap S).toRingHom
        (⊥ : Ideal ((maximalIdeal S.L).ResidueField)), inferInstance⟩
  have hcomap :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] pFiberRing S).toRingHom) r =
        S.pPoint := by
    apply PrimeSpectrum.ext
    ext x
    -- Proof comment: on the `A`-generator, the closed evaluation map is just `A → Λ → κ(Λ)`.
    have hzero :
        algebraMap S.L ((maximalIdeal S.L).ResidueField) (S.phi x) = 0 ↔
          S.phi x ∈ maximalIdeal S.L := by
      constructor
      · intro hx
        let hinj :
            Function.Injective
              (algebraMap (S.L ⧸ maximalIdeal S.L) ((maximalIdeal S.L).ResidueField)) :=
          FaithfulSMul.algebraMap_injective
            (S.L ⧸ maximalIdeal S.L) ((maximalIdeal S.L).ResidueField)
        have hx' :
            algebraMap (S.L ⧸ maximalIdeal S.L) ((maximalIdeal S.L).ResidueField)
              ((Ideal.Quotient.mk (maximalIdeal S.L)) (S.phi x)) = 0 := by
          simpa [Ideal.Quotient.algebraMap_eq (maximalIdeal S.L)] using hx
        have hq :
            (Ideal.Quotient.mk (maximalIdeal S.L)) (S.phi x) = 0 := by
          apply hinj
          simpa using hx'
        exact (Ideal.Quotient.eq_zero_iff_mem).mp hq
      · intro hx
        have hq :
            (Ideal.Quotient.mk (maximalIdeal S.L)) (S.phi x) = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).2 hx
        change
          algebraMap (S.L ⧸ maximalIdeal S.L) ((maximalIdeal S.L).ResidueField)
            ((Ideal.Quotient.mk (maximalIdeal S.L)) (S.phi x)) = 0
        simpa [Ideal.Quotient.algebraMap_eq (maximalIdeal S.L)] using
          congrArg
            (algebraMap (S.L ⧸ maximalIdeal S.L) ((maximalIdeal S.L).ResidueField)) hq
    change pFiberEvaluationMap S
        ((Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] pFiberRing S) x) ∈
          (⊥ : Ideal ((maximalIdeal S.L).ResidueField)) ↔
        x ∈ S.p
    rw [Ideal.mem_bot]
    have hphiL : algebraMap S.A S.L x = S.phi x := by
      rfl
    have hunit :
        algebraMap S.L ((maximalIdeal S.L).ResidueField) ((algebraMap S.A S.L) x) = 0 ↔
          ¬ IsUnit ((algebraMap S.A S.L) x) := by
      simpa [hphiL] using hzero
    calc
      pFiberEvaluationMap S
          ((Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] pFiberRing S) x) = 0 ↔
          algebraMap S.L ((maximalIdeal S.L).ResidueField) ((algebraMap S.A S.L) x) = 0 := by
            simp [pFiberEvaluationMap, IsScalarTower.algebraMap_eq S.A S.L
              ((maximalIdeal S.L).ResidueField)]
      _ ↔ ¬ IsUnit ((algebraMap S.A S.L) x) := hunit
      _ ↔ x ∈ S.p := by
            simpa [hphiL, S.mem_p_iff]
  have hr : r = pFiberPrime S :=
    fiberPrimeAt_eq_of_includeRight_comap_eq S.pPoint r hcomap
  simpa [r] using congrArg PrimeSpectrum.asIdeal hr

/-- Helper for Lemma 16.4.4: the generic fiber evaluates canonically in `Frac(Λ)`. -/
noncomputable instance qFiberRingFractionRingLAlgebra
    (S : RamificationOneDvrFactorizationSituation) :
    Algebra (qFiberRing S) (FractionRing S.L) :=
  RingHom.toAlgebra (qFiberEvaluationMap S).toRingHom

/-- Helper for Lemma 16.4.4: the closed fiber evaluates canonically in `κ(maximalIdeal Λ)`. -/
noncomputable instance pFiberRingResidueFieldLAlgebra
    (S : RamificationOneDvrFactorizationSituation) :
    Algebra (pFiberRing S) ((maximalIdeal S.L).ResidueField) :=
  RingHom.toAlgebra (pFiberEvaluationMap S).toRingHom

/-- Helper for Lemma 16.4.4: the generic fiber prime residue field maps directly to `Frac(Λ)`. -/
noncomputable abbrev qFiberResidueFieldLift
    (S : RamificationOneDvrFactorizationSituation) :
    (qFiberPrime S).asIdeal.ResidueField →ₐ[qFiberRing S] FractionRing S.L :=
  residueFieldLiftOfComapEqField
    (qFiberPrime S).asIdeal
    (qFiberEvaluationMap_comap_eq_qFiberPrime S)

/-- Helper for Lemma 16.4.4: `Frac(Λ)` is a `κ(qFiberPrime)`-algebra via the generic residue-field
lift. -/
noncomputable instance qFiberPrimeResidueFieldFractionRingLAlgebra
    (S : RamificationOneDvrFactorizationSituation) :
    Algebra (qFiberPrime S).asIdeal.ResidueField (FractionRing S.L) :=
  RingHom.toAlgebra (qFiberResidueFieldLift S).toRingHom

/-- Helper for Lemma 16.4.4: the generic residue-field lift recovers the evaluation map on the
fiber ring. -/
theorem qFiberResidueFieldLift_comp_toAlgHom
    (S : RamificationOneDvrFactorizationSituation) :
    (qFiberResidueFieldLift S).comp
        (IsScalarTower.toAlgHom
          (qFiberRing S) (qFiberRing S) (qFiberPrime S).asIdeal.ResidueField) =
      IsScalarTower.toAlgHom (qFiberRing S) (qFiberRing S) (FractionRing S.L) := by
  -- Proof comment: this is the generic specialization of the owner computation rule for the
  -- residue-field lift constructed from a field-valued map with prescribed kernel.
  simpa [qFiberResidueFieldLift] using
    residueFieldLiftOfComapEqField_comp_toAlgHom
      (I := (qFiberPrime S).asIdeal)
      (hf := qFiberEvaluationMap_comap_eq_qFiberPrime S)

/-- Helper for Lemma 16.4.4: the generic residue-field lift gives the expected scalar tower
`qFiberRing S → κ(qFiberPrime) → Frac(Λ)`. -/
theorem qFiberResidueFieldLift_isScalarTower
    (S : RamificationOneDvrFactorizationSituation) :
    IsScalarTower (qFiberRing S) (qFiberPrime S).asIdeal.ResidueField (FractionRing S.L) := by
  -- Proof comment: evaluate the computation rule on each element of `qFiberRing S`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  exact congrArg
    (fun f : qFiberRing S →ₐ[qFiberRing S] FractionRing S.L => f x)
    (qFiberResidueFieldLift_comp_toAlgHom S)

/-- Helper for Lemma 16.4.4: the closed fiber prime residue field maps directly to
`κ(maximalIdeal Λ)`. -/
noncomputable abbrev pFiberResidueFieldLift
    (S : RamificationOneDvrFactorizationSituation) :
    (pFiberPrime S).asIdeal.ResidueField →ₐ[pFiberRing S] (maximalIdeal S.L).ResidueField :=
  residueFieldLiftOfComapEqField
    (pFiberPrime S).asIdeal
    (pFiberEvaluationMap_comap_eq_pFiberPrime S)

/-- Helper for Lemma 16.4.4: `κ(maximalIdeal Λ)` is a `κ(pFiberPrime)`-algebra via the closed
residue-field lift. -/
noncomputable instance pFiberPrimeResidueFieldResidueFieldLAlgebra
    (S : RamificationOneDvrFactorizationSituation) :
    Algebra (pFiberPrime S).asIdeal.ResidueField ((maximalIdeal S.L).ResidueField) :=
  RingHom.toAlgebra (pFiberResidueFieldLift S).toRingHom

/-- Helper for Lemma 16.4.4: the closed residue-field lift recovers the evaluation map on the
fiber ring. -/
theorem pFiberResidueFieldLift_comp_toAlgHom
    (S : RamificationOneDvrFactorizationSituation) :
    (pFiberResidueFieldLift S).comp
        (IsScalarTower.toAlgHom
          (pFiberRing S) (pFiberRing S) (pFiberPrime S).asIdeal.ResidueField) =
      IsScalarTower.toAlgHom
        (pFiberRing S) (pFiberRing S) ((maximalIdeal S.L).ResidueField) := by
  -- Proof comment: this is the closed-fiber specialization of the same residue-field lift rule.
  simpa [pFiberResidueFieldLift] using
    residueFieldLiftOfComapEqField_comp_toAlgHom
      (I := (pFiberPrime S).asIdeal)
      (hf := pFiberEvaluationMap_comap_eq_pFiberPrime S)

/-- Helper for Lemma 16.4.4: the closed residue-field lift gives the expected scalar tower
`pFiberRing S → κ(pFiberPrime) → κ(maximalIdeal Λ)`. -/
theorem pFiberResidueFieldLift_isScalarTower
    (S : RamificationOneDvrFactorizationSituation) :
    IsScalarTower (pFiberRing S) (pFiberPrime S).asIdeal.ResidueField
      ((maximalIdeal S.L).ResidueField) := by
  -- Proof comment: evaluate the computation rule on each element of `pFiberRing S`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  exact congrArg
    (fun f : pFiberRing S →ₐ[pFiberRing S] (maximalIdeal S.L).ResidueField => f x)
    (pFiberResidueFieldLift_comp_toAlgHom S)

/-- Helper for Lemma 16.4.4: extending scalars from `κ(qFiberPrime)` to `Frac(Λ)` cancels the
redundant middle residue-field tensor in the generic Kähler fiber. -/
noncomputable def qFiberKaehlerResidueFieldCancel
    (S : RamificationOneDvrFactorizationSituation) :
    (FractionRing S.L) ⊗[(qFiberPrime S).asIdeal.ResidueField]
        (qFiberKaehlerFiber S) ≃ₗ[FractionRing S.L]
      (FractionRing S.L) ⊗[qFiberRing S] Ω[qFiberRing S⁄qFiberBase S] :=
  letI : Algebra (qFiberRing S) (FractionRing S.L) :=
    RingHom.toAlgebra (qFiberEvaluationMap S).toRingHom
  letI : Algebra (qFiberPrime S).asIdeal.ResidueField (FractionRing S.L) :=
    RingHom.toAlgebra (qFiberResidueFieldLift S).toRingHom
  letI : IsScalarTower
      (qFiberRing S) (qFiberPrime S).asIdeal.ResidueField (FractionRing S.L) :=
    qFiberResidueFieldLift_isScalarTower S
  -- Proof comment: `cancelBaseChange` is exactly the owner-level equivalence collapsing
  -- `Frac(Λ) ⊗[κ(qFiberPrime)] (κ(qFiberPrime) ⊗[qFiberRing] Ω)` to `Frac(Λ) ⊗[qFiberRing] Ω`.
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    (qFiberRing S)
    ((qFiberPrime S).asIdeal.ResidueField)
    (FractionRing S.L)
    (FractionRing S.L)
    Ω[qFiberRing S⁄qFiberBase S]

/-- Helper for Lemma 16.4.4: the generic fiber Kähler module rewrites to the concrete
`Frac(Λ)`-tensor of `Λ ⊗[A] Ω[A⁄R]` in two owner-level steps. -/
noncomputable def qFiberKaehlerToFractionRingLTensor
    (S : RamificationOneDvrFactorizationSituation) :
    (FractionRing S.L) ⊗[qFiberRing S] Ω[qFiberRing S⁄qFiberBase S] ≃ₗ[FractionRing S.L]
      (FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
  letI : Algebra (qFiberRing S) (FractionRing S.L) :=
    RingHom.toAlgebra (qFiberEvaluationMap S).toRingHom
  -- Route correction: split the generic transport into the Kähler base-change equivalence on the
  -- fiber ring, then the final scalar cancellation from `A` through `Λ`.
  let e₁ :
      (FractionRing S.L) ⊗[qFiberRing S] Ω[qFiberRing S⁄qFiberBase S] ≃ₗ[FractionRing S.L]
        (FractionRing S.L) ⊗[qFiberRing S]
          ((qFiberRing S) ⊗[S.A] Ω[S.A⁄S.R]) :=
    LinearEquiv.lTensor (FractionRing S.L)
      (KaehlerDifferential.tensorKaehlerEquiv S.R (qFiberBase S) S.A (qFiberRing S))
  let e₂ :
      (FractionRing S.L) ⊗[qFiberRing S] ((qFiberRing S) ⊗[S.A] Ω[S.A⁄S.R]) ≃ₗ[FractionRing S.L]
        (FractionRing S.L) ⊗[S.A] Ω[S.A⁄S.R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      S.A
      (qFiberRing S)
      (FractionRing S.L)
      (FractionRing S.L)
      Ω[S.A⁄S.R]
  let e₃ :
      (FractionRing S.L) ⊗[S.A] Ω[S.A⁄S.R] ≃ₗ[FractionRing S.L]
        (FractionRing S.L) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      S.A
      S.L
      (FractionRing S.L)
      (FractionRing S.L)
      Ω[S.A⁄S.R]).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 16.4.4: extending scalars from `κ(pFiberPrime)` to `κ(maximalIdeal Λ)`
cancels the redundant middle residue-field tensor in the closed Kähler fiber. -/
noncomputable def pFiberKaehlerResidueFieldCancel
    (S : RamificationOneDvrFactorizationSituation) :
    ((maximalIdeal S.L).ResidueField) ⊗[(pFiberPrime S).asIdeal.ResidueField]
        (pFiberKaehlerFiber S) ≃ₗ[((maximalIdeal S.L).ResidueField)]
      ((maximalIdeal S.L).ResidueField) ⊗[pFiberRing S] Ω[pFiberRing S⁄pFiberBase S] :=
  letI : Algebra (pFiberRing S) ((maximalIdeal S.L).ResidueField) :=
    RingHom.toAlgebra (pFiberEvaluationMap S).toRingHom
  letI : Algebra (pFiberPrime S).asIdeal.ResidueField ((maximalIdeal S.L).ResidueField) :=
    RingHom.toAlgebra (pFiberResidueFieldLift S).toRingHom
  letI : IsScalarTower
      (pFiberRing S) (pFiberPrime S).asIdeal.ResidueField ((maximalIdeal S.L).ResidueField) :=
    pFiberResidueFieldLift_isScalarTower S
  -- Proof comment: this is the closed-fiber version of the same residue-field cancellation.
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    (pFiberRing S)
    ((pFiberPrime S).asIdeal.ResidueField)
    ((maximalIdeal S.L).ResidueField)
    ((maximalIdeal S.L).ResidueField)
    Ω[pFiberRing S⁄pFiberBase S]

/-- Helper for Lemma 16.4.4: the closed fiber Kähler module rewrites to the concrete
`κ(maximalIdeal Λ)`-tensor of `Λ ⊗[A] Ω[A⁄R]` in two owner-level steps. -/
noncomputable def pFiberKaehlerToResidueFieldLTensor
    (S : RamificationOneDvrFactorizationSituation) :
    ((maximalIdeal S.L).ResidueField) ⊗[pFiberRing S] Ω[pFiberRing S⁄pFiberBase S] ≃ₗ[
        ((maximalIdeal S.L).ResidueField)]
      ((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
  letI : Algebra (pFiberRing S) ((maximalIdeal S.L).ResidueField) :=
    RingHom.toAlgebra (pFiberEvaluationMap S).toRingHom
  -- Route correction: as on the generic side, separate the Kähler rewrite from the final
  -- scalar cancellation to keep the transport layer stable.
  let e₁ :
      ((maximalIdeal S.L).ResidueField) ⊗[pFiberRing S] Ω[pFiberRing S⁄pFiberBase S] ≃ₗ[
          ((maximalIdeal S.L).ResidueField)]
        ((maximalIdeal S.L).ResidueField) ⊗[pFiberRing S]
          ((pFiberRing S) ⊗[S.A] Ω[S.A⁄S.R]) :=
    LinearEquiv.lTensor ((maximalIdeal S.L).ResidueField)
      (KaehlerDifferential.tensorKaehlerEquiv S.R (pFiberBase S) S.A (pFiberRing S))
  let e₂ :
      ((maximalIdeal S.L).ResidueField) ⊗[pFiberRing S]
          ((pFiberRing S) ⊗[S.A] Ω[S.A⁄S.R]) ≃ₗ[((maximalIdeal S.L).ResidueField)]
        ((maximalIdeal S.L).ResidueField) ⊗[S.A] Ω[S.A⁄S.R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      S.A
      (pFiberRing S)
      ((maximalIdeal S.L).ResidueField)
      ((maximalIdeal S.L).ResidueField)
      Ω[S.A⁄S.R]
  let e₃ :
      ((maximalIdeal S.L).ResidueField) ⊗[S.A] Ω[S.A⁄S.R] ≃ₗ[((maximalIdeal S.L).ResidueField)]
        ((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      S.A
      S.L
      ((maximalIdeal S.L).ResidueField)
      ((maximalIdeal S.L).ResidueField)
      Ω[S.A⁄S.R]).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 16.4.4: after extending scalars from the residue field of the generic
fiber prime to the zero-residue field of `Frac(Λ)`, the Kähler fiber of `A/R` over `q`
becomes the generic `Λ`-fiber of `Ω[A⁄R]`. -/
noncomputable def qFiberKaehlerBaseChangeLinearEquiv
    (S : RamificationOneDvrFactorizationSituation) :
    qFiberTargetField S ⊗[(qFiberPrime S).asIdeal.ResidueField]
        (qFiberKaehlerFiber S) ≃ₗ[qFiberTargetField S]
      (qFiberTargetField S) ⊗[S.L]
        (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
  -- Proof comment: the generic transport is the composition of the residue-field cancellation
  -- with the stable Kähler/base-change rewrite to the concrete `Λ`-tensor model.
  (qFiberKaehlerResidueFieldCancel S).trans (qFiberKaehlerToFractionRingLTensor S)

/-- Helper for Lemma 16.4.4: after extending scalars from the residue field of the closed
fiber prime to `κ(maximalIdeal Λ)`, the Kähler fiber of `A/R` over `p` becomes the closed
`Λ / πΛ`-fiber of `Ω[A⁄R]`. -/
noncomputable def pFiberKaehlerBaseChangeLinearEquiv
    (S : RamificationOneDvrFactorizationSituation) :
    ((maximalIdeal S.L).ResidueField) ⊗[(pFiberPrime S).asIdeal.ResidueField]
        (pFiberKaehlerFiber S) ≃ₗ[((maximalIdeal S.L).ResidueField)]
      ((maximalIdeal S.L).ResidueField) ⊗[S.L]
        (S.L ⊗[S.A] Ω[S.A⁄S.R]) :=
  -- Proof comment: the closed transport uses the same two-step route as the generic one.
  (pFiberKaehlerResidueFieldCancel S).trans (pFiberKaehlerToResidueFieldLTensor S)

/-- Helper for Lemma 16.4.4: the generic-fiber TFAE finrank can be rewritten as the generic
`Λ`-fiber rank of `Ω[A⁄R]`. -/
theorem qFiberKaehlerFiberFinrank_eq_fractionRingLKaehlerFinrank
    (S : RamificationOneDvrFactorizationSituation)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Module.finrank (qFiberPrime S).asIdeal.ResidueField (qFiberKaehlerFiber S) =
      fractionRingLKaehlerFinrank S := by
  -- Proof comment: base change from `κ(qFiberPrime)` to `Frac(Λ)` and rewrite the resulting
  -- tensor by the transport equivalence above.
  calc
    Module.finrank (qFiberPrime S).asIdeal.ResidueField (qFiberKaehlerFiber S) =
        Module.finrank (qFiberTargetField S)
          (qFiberTargetField S ⊗[(qFiberPrime S).asIdeal.ResidueField] (qFiberKaehlerFiber S)) := by
          symm
          exact Module.finrank_baseChange
            (S := (qFiberPrime S).asIdeal.ResidueField)
            (R := qFiberTargetField S)
            (M' := qFiberKaehlerFiber S)
    _ = Module.finrank (qFiberTargetField S)
          ((qFiberTargetField S) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) := by
          exact LinearEquiv.finrank_eq (qFiberKaehlerBaseChangeLinearEquiv S)
    _ = fractionRingLKaehlerFinrank S := by
          rfl

/-- Helper for Lemma 16.4.4: the closed-fiber TFAE finrank is exactly the `κ(maximalIdeal Λ)`-rank
of the closed `Λ / πΛ`-fiber of `Ω[A⁄R]`. -/
theorem pFiberKaehlerFiberFinrank_eq_residueFieldLKaehlerFinrank
    (S : RamificationOneDvrFactorizationSituation) :
    Module.finrank (pFiberPrime S).asIdeal.ResidueField (pFiberKaehlerFiber S) =
      residueFieldLKaehlerFinrank S := by
  -- Proof comment: the closed-fiber transport is the same base-change-and-rewrite argument as on
  -- the generic fiber, with target field `κ(maximalIdeal Λ)`.
  calc
    Module.finrank (pFiberPrime S).asIdeal.ResidueField (pFiberKaehlerFiber S) =
        Module.finrank ((maximalIdeal S.L).ResidueField)
          (((maximalIdeal S.L).ResidueField) ⊗[(pFiberPrime S).asIdeal.ResidueField]
            (pFiberKaehlerFiber S)) := by
          symm
          exact Module.finrank_baseChange
            (S := (pFiberPrime S).asIdeal.ResidueField)
            (R := (maximalIdeal S.L).ResidueField)
            (M' := pFiberKaehlerFiber S)
    _ = Module.finrank ((maximalIdeal S.L).ResidueField)
          (((maximalIdeal S.L).ResidueField) ⊗[S.L] (S.L ⊗[S.A] Ω[S.A⁄S.R])) := by
          exact LinearEquiv.finrank_eq (pFiberKaehlerBaseChangeLinearEquiv S)
    _ = residueFieldLKaehlerFinrank S := by
          rfl

/-- Helper for Lemma 16.4.4: the generic smoothness at `q` and the free `Λ`-module structure on
`Λ ⊗[A] Ω[A⁄R]` force the closed `Λ / πΛ`-fiber rank to be at most `dim_p(A/R)`. -/
theorem closedFiberKaehlerFinrank_le_relativeDimensionAtP
    (S : RamificationOneDvrFactorizationSituation)
    (hAq : Algebra.SmoothAtPrime S.R S.A S.qPoint)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    (residueFieldLKaehlerFinrank S : WithBot ℕ∞) ≤
      relativeDimensionAt S.R S.A S.pPoint := by
  letI : Algebra.FinitePresentation (qFiberBase S) (qFiberRing S) := qFiberFinitePresentation S
  have hqSmooth :
      IsSmoothAt (qFiberBase S) (qFiberPrime S).asIdeal := by
    -- Proof comment: rewrite the generic-fiber smoothness theorem into the ideal-level owner
    -- used by the cotangent-space TFAE.
    exact
      (smoothAtPrime_iff_isSmoothAt
        (R := qFiberBase S) (S := qFiberRing S) (q := qFiberPrime S)).mp
        (genericFiber_smoothAtPrime_at_qFiber S hAq)
  have hqDim :
      (fractionRingLKaehlerFinrank S : WithBot ℕ∞) = relativeDimensionAt S.R S.A S.qPoint := by
    have hTfae :=
      Algebra.isSmoothAt_tfae_finrank_kaehlerFiber_le_eq
        (k := qFiberBase S) (S := qFiberRing S) (q := (qFiberPrime S).asIdeal)
    have hEq := (hTfae.out 0 2) hqSmooth
    rw [qFiberKaehlerFiberFinrank_eq_fractionRingLKaehlerFinrank S hfree] at hEq
    simpa [relativeDimensionAt, fiberLocalRingAt, qFiberPrime, qFiberRing, qFiberBase] using hEq
  have hqToP :
      (fractionRingLKaehlerFinrank S : WithBot ℕ∞) + 1 ≤
        relativeDimensionAt S.R S.A S.pPoint + 1 := by
    simpa [hqDim] using relativeDimensionAt_q_add_one_le_relativeDimensionAt_p_add_one S
  have hfracLe :
      (fractionRingLKaehlerFinrank S : WithBot ℕ∞) ≤ relativeDimensionAt S.R S.A S.pPoint :=
    natCast_le_of_add_one_le_add_one hqToP
  have hcompare :
      (residueFieldLKaehlerFinrank S : WithBot ℕ∞) =
        (fractionRingLKaehlerFinrank S : WithBot ℕ∞) := by
    exact congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞))
      (fractionRingL_finrank_eq_residueFieldL_finrank_tensor_kaehler S hfree).symm
  rw [hcompare]
  exact hfracLe

/-- Helper for Lemma 16.4.4: the remaining source-proof blocker is smoothness of the closed fiber
at `p`, obtained by transporting the generic Kähler rank from `q` to the `κ(p)`-fiber. -/
theorem fiber_smoothAtPrime_at_p_of_smoothAtPrime_q_and_free_baseChange
    (S : RamificationOneDvrFactorizationSituation)
    (hAq : Algebra.SmoothAtPrime S.R S.A S.qPoint)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Algebra.SmoothAtPrime (S.p.under S.R).ResidueField
      ((S.p.under S.R).Fiber S.A) (fiberPrimeAt S.R S.A S.pPoint) := by
  letI : Algebra.FinitePresentation (pFiberBase S) (pFiberRing S) := pFiberFinitePresentation S
  have hTfae :=
    Algebra.isSmoothAt_tfae_finrank_kaehlerFiber_le_eq
      (k := pFiberBase S) (S := pFiberRing S) (q := (pFiberPrime S).asIdeal)
  have hbound :
      Module.finrank (pFiberPrime S).asIdeal.ResidueField (pFiberKaehlerFiber S) ≤
        ringKrullDim (Localization.AtPrime (pFiberPrime S).asIdeal) := by
    -- Proof comment: rewrite the closed-fiber finrank bound into the exact clause expected by the
    -- cotangent-space TFAE at `pFiberPrime`.
    rw [pFiberKaehlerFiberFinrank_eq_residueFieldLKaehlerFinrank S]
    simpa [relativeDimensionAt, fiberLocalRingAt, pFiberPrime, pFiberRing, pFiberBase] using
      closedFiberKaehlerFinrank_le_relativeDimensionAtP S hAq hfree
  have hpSmooth :
      IsSmoothAt (pFiberBase S) (pFiberPrime S).asIdeal :=
    (hTfae.out 1 0) hbound
  -- Proof comment: convert the ideal-level smoothness back to the source-facing prime-spectrum
  -- formulation used by the outer theorem.
  exact
    (smoothAtPrime_iff_isSmoothAt
      (R := pFiberBase S) (S := pFiberRing S) (q := pFiberPrime S)).2 hpSmooth

/-
Domain-style sampling pass for Lemma 16.4.4.

Primary domain: source-facing smoothness at prime-spectrum points in a DVR factorization
situation, together with freeness of the base-changed cotangent module `Λ ⊗[A] Ω[A⁄R]`.

Sampled owner declarations:
* `Algebra.SmoothAtPrime`;
* `Algebra.smoothAtPrime_iff_isSmoothAt`;
* `RamificationOneDvrFactorizationSituation.qPoint`;
* `RamificationOneDvrFactorizationSituation.pPoint`;
* `Module.Free`.

Best owner abstraction: the chapter’s source-facing smoothness owner is
`Algebra.SmoothAtPrime` on prime-spectrum points, together with the canonical freeness owner
`Module.Free` on the base-changed Kähler module. The factorization data are already owned by
`RamificationOneDvrFactorizationSituation`; the points of `Spec(S.A)` are canonically `S.qPoint`
and `S.pPoint`. The local predicate `IsSmoothAt` is only a proof bridge via
`smoothAtPrime_iff_isSmoothAt`.

Primitive-vs-derived split:
* primitive data: `S : RamificationOneDvrFactorizationSituation`, smoothness at `S.qPoint`, and
  freeness of `S.L ⊗[S.A] Ω[S.A⁄S.R]`;
* derived API: the induced `S.A`-algebra structure on `S.L`, the scalar tower `S.R → S.A → S.L`,
  the ideals `S.q` and `S.p`, the corresponding points `S.qPoint` and `S.pPoint`, and the local
  criterion bridge `smoothAtPrime_iff_isSmoothAt`.

Source/core/bridge triage:
* `source-facing`: the textbook criterion formulated from a surjection `B ↠ A` and the freeness of
  the cokernel of `I / I² ⊗[A] Λ → Ω[B⁄R] ⊗[B] Λ`;
* `core/canonical`: `RamificationOneDvrFactorizationSituation`, `S.qPoint`, `S.pPoint`,
  `Algebra.SmoothAtPrime`, and `Module.Free`;
* `bridge/view`: the theorem below, which replaces the source cokernel by the canonically
  identified module `S.L ⊗[S.A] Ω[S.A⁄S.R]` and uses `smoothAtPrime_iff_isSmoothAt` internally.
-/

-- Proof sketch: in the source proof, the exact conormal sequence for a surjection `B ↠ A`
-- identifies the cokernel hypothesis with freeness of `S.L ⊗[S.A] Ω[S.A⁄S.R]`, after which the
-- auxiliary presentation `B ↠ A` disappears. Smoothness at `S.qPoint` gives the generic-point
-- control needed for the cotangent criterion, and flatness of `S.A` over `S.R` compares the fiber
-- dimensions at `S.q` and `S.p`. Then rewrite through `smoothAtPrime_iff_isSmoothAt` and apply
-- the local cotangent-space criterion for smoothness at `S.pPoint`.
/-- Lemma 16.4.4, owner-level reformulation: in a ramification-one DVR factorization situation
`S`, if `S.A` is smooth over `S.R` at `S.qPoint` and
`S.L ⊗[S.A] Ω[S.A⁄S.R]` is a free `S.L`-module, then `S.A` is smooth over `S.R` at `S.pPoint`. -/
@[stacks 0BJ5]
theorem smoothAtPrime_p_of_smoothAtPrime_q_of_free_kaehlerDifferential_baseChange
    (S : RamificationOneDvrFactorizationSituation)
    (hAq : Algebra.SmoothAtPrime S.R S.A S.qPoint)
    (hfree : Module.Free S.L (S.L ⊗[S.A] Ω[S.A⁄S.R])) :
    Algebra.SmoothAtPrime S.R S.A S.pPoint := by
  -- Route correction: keep the source proof route and reduce the target to smoothness of the
  -- closed fiber at `p`; the only unresolved step is transporting the generic Kähler rank to that
  -- fiber.
  letI : Algebra.FinitePresentation S.R S.A := finitePresentation_toA S
  -- A global finite-presentation witness gives the neighborhood input required by Lemma `10.137.16`.
  have hfp :
      ∃ g : S.A, g ∉ S.pPoint.asIdeal ∧ Algebra.FinitePresentation S.R (Localization.Away g) := by
    refine ⟨1, ?_, inferInstance⟩
    simpa using S.pPoint.asIdeal.ne_top
  -- Flatness localizes from `R → A` to the local map at `p`.
  have hflat :
      (Localization.localRingHom (S.pPoint.asIdeal.under S.R) S.pPoint.asIdeal
        (algebraMap S.R S.A) rfl).Flat := by
    have hflatAlg : (algebraMap S.R S.A).Flat := by
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    exact RingHom.Flat.localRingHom hflatAlg S.pPoint.asIdeal (S.pPoint.asIdeal.under S.R) rfl
  -- Once the closed fiber is smooth at the canonical fiber prime, the local smoothness criterion
  -- finishes the argument.
  exact Algebra.smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
    S.pPoint hfp hflat
    (fiber_smoothAtPrime_at_p_of_smoothAtPrime_q_and_free_baseChange S hAq hfree)

end
