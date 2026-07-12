import Mathlib
import StacksProject_2024.Chap09.Lemma_9_14_2
import StacksProject_2024.Chap09.Lemma_9_14_5
import StacksProject_2024.Chap10.Lemma_10_97_8
import StacksProject_2024.Chap10.Lemma_10_164_4
import StacksProject_2024.Chap10.Remark_10_160_9
import StacksProject_2024.Chap15.Lemma_15_43_4
import StacksProject_2024.Chap15.Lemma_15_46_5
import StacksProject_2024.Chap15.Lemma_15_48_1
import StacksProject_2024.Chap15.Lemma_15_48_4
import StacksProject_2024.Chap15.Lemma_15_48_5
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Polynomial

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable (n : ℕ)

local notation "A" => mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (𝔭 : PrimeSpectrum A)

/-- Helper for Lemma 15.50.5: rewrite the geometric-regularity test tensor
`L ⊗[K] ((A_𝔭)^∧ ⊗[A] K)` into the source-facing ring `((A_𝔭)^∧ ⊗[A] L)`. -/
private noncomputable def formalFiber_fractionRing_tensorBaseChangeRingEquiv
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    L ⊗[K] (R̂_[𝔭] ⊗[A] K) ≃+* R̂_[𝔭] ⊗[A] L :=
  -- First reorder the inner tensor into the canonical `K ⊗[A] R̂_[𝔭]` form, then cancel the
  -- successive base change `A → K → L`, and finally commute back to the source-facing order.
  ((Algebra.TensorProduct.congr
      (AlgEquiv.refl : L ≃ₐ[K] L)
      (Algebra.TensorProduct.commRight A K (R̂_[𝔭])).symm).toRingEquiv).trans <|
    ((Algebra.TensorProduct.cancelBaseChange A K K L (R̂_[𝔭])).toRingEquiv.trans <|
      (Algebra.TensorProduct.commRight A L (R̂_[𝔭])).toRingEquiv)

/-- Helper for Lemma 15.50.5: if every source-facing tensor
`R̂_[𝔭] ⊗[A] L` is regular after finite purely inseparable base change `L/K`, then the generic
formal fiber over `K` is geometrically regular. -/
private theorem genericFormalFiber_isGeometricallyRegular_of_source_tensor_regular
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hL :
      ∀ {L : Type u} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
        [FiniteDimensional K L] [IsPurelyInseparable K L],
          IsRegularRing (R̂_[𝔭] ⊗[A] L)) :
    IsGeometricallyRegular K (R̂_[𝔭] ⊗[A] K) := by
  rw [Algebra.isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro L _ _ _ _
  let e :
      L ⊗[K] (R̂_[𝔭] ⊗[A] K) ≃+* R̂_[𝔭] ⊗[A] L :=
    formalFiber_fractionRing_tensorBaseChangeRingEquiv (A := A) (𝔭 := 𝔭)
  let _ : IsRegularRing (R̂_[𝔭] ⊗[A] L) := hL
  -- Transport regularity back across the explicit tensor/base-change equivalence.
  exact
    isRegularRing_of_faithfullyFlat e.toRingHom
      (RingHom.FaithfullyFlat.of_bijective e.bijective)

/-- Helper for Lemma 15.50.5: every finite purely inseparable test field extension used in the
geometric-regularity criterion admits the textbook finite `p`-root tower from Lemma `9.14.5`. -/
private theorem exists_source_pthRootTower
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L] :
    ∃ m : ℕ, ∃ α : Fin m → L, IsPthRootTower K p α := by
  -- This is the exact source reduction from an arbitrary finite purely inseparable extension to a
  -- finite tower of degree-`p` adjunctions.
  simpa using exists_pthRoot_tower_of_finite_purelyInseparable (F := K) (E := L) p

/-- Helper for Lemma 15.50.5: stage `0` of the textbook `p`-root tower is the base field. -/
private theorem finiteGeneratorStage_zero_eq_bot
    {K L : Type u} [Field K] [Field L] [Algebra K L] {m : ℕ} (α : Fin m → L) :
    finiteGeneratorStage K α (0 : Fin (m + 1)) = ⊥ := by
  -- At stage `0` there are no earlier generators, so the adjoined set is empty.
  ext x
  simp [finiteGeneratorStage, finiteGeneratorPrefix]

/-- Helper for Lemma 15.50.5: the zeroth source stage is canonically the base field `K`. -/
private noncomputable def finiteGeneratorStage_zero_algEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L] {m : ℕ} (α : Fin m → L) :
    finiteGeneratorStage K α (0 : Fin (m + 1)) ≃ₐ[K] K :=
  -- First collapse the zeroth stage to `⊥`, then use the canonical bottom-stage equivalence.
  (IntermediateField.equivOfEq (finiteGeneratorStage_zero_eq_bot (K := K) α)).trans
    (IntermediateField.botEquiv K L)

/-- Helper for Lemma 15.50.5: tensoring with the zeroth source stage is the same as tensoring
with the base field `K`. -/
private noncomputable def sourceTensor_zeroStage_ringEquiv
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ} (α : Fin m → L) :
    R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (0 : Fin (m + 1)) ≃+* R̂_[𝔭] ⊗[A] K :=
  -- Transport the right tensor factor along the explicit stage-`0` equivalence.
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : R̂_[𝔭] ≃ₐ[A] R̂_[𝔭])
      (finiteGeneratorStage_zero_algEquiv (K := K) (L := L) α).restrictScalars A).toRingEquiv

/-- Helper for Lemma 15.50.5: the successor source stage is obtained by adjoining the next
generator to the previous stage. -/
private theorem finiteGeneratorStage_succ_eq_adjoin
    {K L : Type u} [Field K] [Field L] [Algebra K L] {m : ℕ} (α : Fin m → L) (i : Fin m) :
    finiteGeneratorStage K α (Fin.succ i) =
      (IntermediateField.adjoin (finiteGeneratorStage K α (Fin.castSucc i))
        ({α i} : Set L)).restrictScalars K := by
  have hprefix :
      finiteGeneratorPrefix α (Fin.succ i) =
        Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i)) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff.mp hj with hjlt | hjeq
      · exact Or.inr ⟨j, hjlt, rfl⟩
      · left
        exact congrArg α (Fin.ext hjeq)
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨i, Nat.lt_succ_self i.1, rfl⟩
      · rcases hx with ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
  -- Re-express the successor prefix as the old prefix together with the new generator.
  rw [finiteGeneratorStage, hprefix]
  -- Then use the canonical adjoin-by-insert identity.
  simpa [finiteGeneratorStage] using
    (Algebra.adjoin_insert_adjoin (R := K)
      (s := finiteGeneratorPrefix α (Fin.castSucc i)) (x := α i))

/-- Helper for Lemma 15.50.5: each successor step in the textbook `p`-root tower is already an
explicit degree-`p` `AdjoinRoot` extension of the previous stage. -/
private noncomputable theorem degree_p_stage_field_presentation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {m : ℕ} (α : Fin m → L) (hα : IsPthRootTower K p α) (i : Fin m) :
    let M := finiteGeneratorStage K α (Fin.castSucc i)
    let N := finiteGeneratorStage K α (Fin.succ i)
    ∃ fM : M, Nonempty (N ≃ₐ[M] AdjoinRoot (X ^ p - C fM)) := by
  let M := finiteGeneratorStage K α (Fin.castSucc i)
  let N := finiteGeneratorStage K α (Fin.succ i)
  have hfM_mem : α i ^ p ∈ M := hα.pth_power_mem i
  let fM : M := ⟨α i ^ p, hfM_mem⟩
  have hnot_pth_power : ¬ ∃ β : M, β ^ p = fM := by
    intro hβ
    apply hα.not_pth_power i
    rcases hβ with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    -- Coercing the equation down to `L` recovers the source non-`p`th-power clause.
    simpa [fM] using congrArg (fun x : M ↦ (x : L)) hβ
  have hpoly_irreducible : Irreducible (X ^ p - C fM : Polynomial M) := by
    -- The previous-stage element `fM` was chosen so that it is not already a `p`th power.
    exact X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) hnot_pth_power
  have hpoly_root : aeval (α i) (X ^ p - C fM : Polynomial M) = 0 := by
    -- The next generator is, by construction, a root of `X ^ p - fM`.
    change eval₂ (algebraMap M L) (α i) (X ^ p - C fM) = 0
    simpa [fM] using (root_X_pow_sub_C_pow p (α i : L))
  have hpoly_monic : (X ^ p - C fM : Polynomial M).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C fM (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hroot_integral : IsIntegral M (α i : L) := by
    -- The displayed monic equation makes the successor generator integral over the previous stage.
    exact ⟨X ^ p - C fM, hpoly_monic, hpoly_root⟩
  have hminpoly :
      minpoly M (α i : L) = (X ^ p - C fM : Polynomial M) := by
    -- Irreducibility of the explicit `p`-power polynomial identifies it with the minimal
    -- polynomial of the successor generator.
    exact (minpoly.eq_of_irreducible_of_monic hpoly_irreducible hpoly_root hpoly_monic).symm
  have hstage :
      N = (M⟮(α i : L)⟯).restrictScalars K := by
    -- Route correction: normalize the abstract successor stage to the canonical simple extension
    -- owner before introducing any finite-model or derivation data.
    simpa [M, N] using (finiteGeneratorStage_succ_eq_adjoin (K := K) α i)
  refine ⟨fM, ?_⟩
  refine ⟨(IntermediateField.equivOfEq hstage).trans ?_⟩
  -- After rewriting the owner polynomial, the successor stage is the explicit `AdjoinRoot`.
  exact
    ((minpoly.equivAdjoin (R := M) (x := (α i : L)) hroot_integral).symm.trans
      (AdjoinRoot.algEquivOfEq M (minpoly M (α i : L)) (X ^ p - C fM : Polynomial M) hminpoly))

/-- Helper for Lemma 15.50.5: tensoring the explicit successor-stage presentation on the right
factor rewrites the successor tensor ring as a tensor with the corresponding `AdjoinRoot`. -/
private noncomputable theorem degree_p_stage_tensor_rightPresentation
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {m : ℕ} (α : Fin m → L) (hα : IsPthRootTower K p α) (i : Fin m) :
    let M := finiteGeneratorStage K α (Fin.castSucc i)
    let N := finiteGeneratorStage K α (Fin.succ i)
    ∃ fM : M, Nonempty
      ((R̂_[𝔭] ⊗[A] N) ≃+* (R̂_[𝔭] ⊗[A] AdjoinRoot (X ^ p - C fM))) := by
  let M := finiteGeneratorStage K α (Fin.castSucc i)
  let N := finiteGeneratorStage K α (Fin.succ i)
  obtain ⟨fM, eN⟩ := degree_p_stage_field_presentation (p := p) (K := K) (L := L) α hα i
  refine ⟨fM, ?_⟩
  -- Transport the right tensor factor along the explicit stage presentation over the predecessor
  -- field, leaving the completed-localization factor unchanged.
  refine ⟨(Algebra.TensorProduct.congr
    (AlgEquiv.refl : R̂_[𝔭] ≃ₐ[A] R̂_[𝔭])
    (eN.choose.restrictScalars A)).toRingEquiv⟩

/-- Helper for Lemma 15.50.5: regularity can be transported across a ring equivalence. -/
private theorem isRegularRing_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) [IsRegularRing S] :
    IsRegularRing R := by
  -- Transport regularity back along the faithfully flat map induced by the equivalence.
  exact
    isRegularRing_of_faithfullyFlat e.toRingHom
      (RingHom.FaithfullyFlat.of_bijective e.bijective)

/-- Helper for Lemma 15.50.5: the completed localization `(A_𝔭)^∧` is a regular local ring for
`A = k[[x_1, ..., x_n]][y_1, ..., y_n]`. -/
private theorem mixedPowerSeries_completedLocalization_isRegularLocalRing
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsRegularLocalRing (R̂_[𝔭]) := by
  let _ : IsRegularLocalRing (MvPowerSeries (Fin n) k) := inferInstance
  let _ : IsRegularRing (MvPowerSeries (Fin n) k) := inferInstance
  let _ : Algebra.Smooth (MvPowerSeries (Fin n) k) A := inferInstance
  have hA_reg : IsRegularRing A := by
    -- The mixed source ring is a polynomial algebra smooth over the regular local power-series
    -- base, so the source ring itself is regular.
    exact isRegularRing_of_smooth
  have hlocal_reg : IsRegularLocalRing (Localization.AtPrime 𝔭.asIdeal) := by
    let _ : IsRegularRing A := hA_reg
    -- Localizing a regular ring at the chosen prime yields a regular local ring.
    simpa using (IsRegularRing.isRegularLocalRing_atPrime 𝔭 :
      IsRegularLocalRing (Localization.AtPrime 𝔭.asIdeal))
  -- Lemma `15.43.4` transfers regular-locality from the localization to its maximal-ideal
  -- completion.
  exact
    (isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion
      (Localization.AtPrime 𝔭.asIdeal)).mp hlocal_reg

/-- Helper for Lemma 15.50.5: tensoring the completed localization with the fraction field is the
same as localizing the completed localization away from the image of the source nonzerodivisors.
-/
private noncomputable def base_tensor_fractionField_ringEquiv_localization
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] :
    R̂_[𝔭] ⊗[A] K ≃+*
      Localization (Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A)) := by
  let eFrac : Localization (nonZeroDivisors A) ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) (Localization (nonZeroDivisors A)) K
  -- Commute the tensor factors so the fraction-field localization sits on the left, then replace
  -- the chosen fraction field by the canonical localization and apply the standard base-change
  -- description of localization.
  exact
    ((Algebra.TensorProduct.commRight A K (R̂_[𝔭])).toRingEquiv.trans <|
      ((Algebra.TensorProduct.congr eFrac.symm
        (AlgEquiv.refl : R̂_[𝔭] ≃ₐ[A] R̂_[𝔭])).toRingEquiv.trans <|
        (Localization.tensorRightAlgEquiv (nonZeroDivisors A) (R̂_[𝔭])).toRingEquiv))

/-- Helper for Lemma 15.50.5: localizing the regular local ring `(A_𝔭)^∧` away from the image of
the source nonzerodivisors stays regular. -/
private theorem base_localization_regular_of_regular_completedLocalization
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsRegularLocalRing (R̂_[𝔭])] :
    IsRegularRing
      (Localization (Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A))) := by
  let T := Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A)
  refine ⟨fun q ↦ ?_⟩
  let qBase : PrimeSpectrum (R̂_[𝔭]) := PrimeSpectrum.comap (algebraMap (R̂_[𝔭]) (Localization T)) q
  have hqBase :
      IsRegularLocalRing (Localization.AtPrime qBase.asIdeal) :=
    Lemma_10_110_6.isRegularLocalRing_localizationAtPrime qBase
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) qBase.asIdeal := by
    simpa [T, qBase] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
        (Localization.AtPrime q.asIdeal) q.asIdeal)
  let eLoc : Localization.AtPrime qBase.asIdeal ≃ₐ[R̂_[𝔭]] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv qBase.asIdeal.primeCompl (Localization.AtPrime qBase.asIdeal)
      (Localization.AtPrime q.asIdeal)
  -- The prime localization of the localization ring agrees with the corresponding prime
  -- localization of `(A_𝔭)^∧`, so regular-locality transports across the canonical equivalence.
  exact hqBase.of_equiv eLoc.toRingEquiv

/-- Helper for Lemma 15.50.5: the stage-`0` source tensor ring
`(A_𝔭)^∧ ⊗[A] K` is regular. -/
private theorem mixedPowerSeries_source_tensor_regular_base
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsRegularRing (R̂_[𝔭] ⊗[A] K) := by
  -- Route correction: isolate the textbook base case before the tower induction, so the remaining
  -- blocker is only the explicit source-model comparison.
  have hcompletion_reg : IsRegularLocalRing (R̂_[𝔭]) :=
    mixedPowerSeries_completedLocalization_isRegularLocalRing
      (p := p) (k := k) (n := n) (𝔭 := 𝔭) (K := K)
  let _ : IsRegularLocalRing (R̂_[𝔭]) := hcompletion_reg
  let e :
      R̂_[𝔭] ⊗[A] K ≃+*
        Localization (Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A)) :=
    base_tensor_fractionField_ringEquiv_localization (A := A) (𝔭 := 𝔭) (K := K)
  have hloc :
      IsRegularRing
        (Localization (Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A))) :=
    base_localization_regular_of_regular_completedLocalization
      (A := A) (𝔭 := 𝔭) (K := K)
  let _ :
      IsRegularRing
        (Localization (Algebra.algebraMapSubmonoid (R̂_[𝔭]) (nonZeroDivisors A))) := hloc
  -- The stage-`0` tensor ring is exactly that localization written in source-facing tensor form.
  exact isRegularRing_of_ringEquiv e.symm

/-- Helper for Lemma 15.50.5: once the predecessor stage in the textbook `p`-root tower is
regular, the source-faithful degree-`p` successor stage is regular as well. -/
private theorem degree_p_stage_regular
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {m : ℕ} (α : Fin m → L) (hα : IsPthRootTower K p α) (i : Fin m)
    (hM :
      IsRegularRing (R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (Fin.castSucc i))) :
    IsRegularRing (R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (Fin.succ i)) := by
  have hpresentation :=
    degree_p_stage_field_presentation (p := p) (K := K) (L := L) α hα i
  have htensorPresentation :=
    degree_p_stage_tensor_rightPresentation (A := A) (𝔭 := 𝔭) (p := p) (K := K) (L := L) α hα i
  let _ := hpresentation
  let _ := htensorPresentation
  let _ := hM
  -- Route correction: the successor tensor ring is now normalized in two verified stages:
  -- first the field-side successor becomes an explicit `AdjoinRoot` over the predecessor field,
  -- then tensoring preserves that right-factor presentation. The remaining blocker is no longer
  -- the stage presentation itself, but the source-faithful upgrade from
  -- `R̂_[𝔭] ⊗[A] AdjoinRoot (X ^ p - C fM)` to an `AdjoinRoot` over the predecessor tensor ring,
  -- together with transport of the derivation hitting a unit.
  -- TODO: replace the tensored right-factor `AdjoinRoot` by the textbook
  -- `AdjoinRoot (X ^ p - C fR)` over `R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (Fin.castSucc i)`,
  -- using the universal-property comparison from `Example_15_116_2`; then build the compatible
  -- derivation on the predecessor tensor ring by starting from the finite source model over `A`,
  -- extending it through localization/completion/fraction-field localization via Lemma `15.48.1`,
  -- and finish with Lemma `15.48.4`.
  sorry

/-- Helper for Lemma 15.50.5: after reducing a finite purely inseparable extension to the
textbook `p`-root tower, the remaining argument is a flat induction on the tower stages. -/
private theorem source_tensor_regular_of_pthRootTower
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {m : ℕ} (α : Fin m → L) (hα : IsPthRootTower K p α) :
    IsRegularRing (R̂_[𝔭] ⊗[A] L) := by
  have hstage :
      ∀ j : Fin (m + 1), IsRegularRing (R̂_[𝔭] ⊗[A] finiteGeneratorStage K α j) := by
    intro j
    refine Fin.induction ?_ ?_ j
    · let e₀ :
          R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (0 : Fin (m + 1)) ≃+* R̂_[𝔭] ⊗[A] K :=
        sourceTensor_zeroStage_ringEquiv (A := A) (𝔭 := 𝔭) (K := K) (L := L) α
      have hbase : IsRegularRing (R̂_[𝔭] ⊗[A] K) :=
        mixedPowerSeries_source_tensor_regular_base (A := A) (𝔭 := 𝔭) (K := K)
      let _ : IsRegularRing (R̂_[𝔭] ⊗[A] K) := hbase
      -- Initialize the tower induction by transporting the base field case to stage `0`.
      exact isRegularRing_of_ringEquiv e₀.symm
    · intro i hi
      -- Move from the predecessor stage to the degree-`p` successor using the source step.
      exact degree_p_stage_regular (A := A) (𝔭 := 𝔭) (p := p) (K := K) (L := L) α hα i hi
  let elast :
      R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (Fin.last m) ≃+* R̂_[𝔭] ⊗[A] L :=
    (Algebra.TensorProduct.congr
        (AlgEquiv.refl : R̂_[𝔭] ≃ₐ[A] R̂_[𝔭])
        (((IntermediateField.equivOfEq hα.stage_top).trans
          (IntermediateField.topEquiv K L)).restrictScalars A)).toRingEquiv
  let _ : IsRegularRing (R̂_[𝔭] ⊗[A] finiteGeneratorStage K α (Fin.last m)) :=
    hstage (Fin.last m)
  -- The top stage is the whole extension field, so the induction output is the desired tensor
  -- ring after one final transport.
  exact isRegularRing_of_ringEquiv elast.symm

/-- Helper for Lemma 15.50.5: after reducing to the textbook `p`-root tower, the remaining proof
is the source induction on the tower stages. -/
private theorem source_tensor_regular_of_finite_purelyInseparable
    {K L : Type u} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L] :
    IsRegularRing (R̂_[𝔭] ⊗[A] L) := by
  obtain ⟨m, α, hα⟩ := exists_source_pthRootTower (K := K) (L := L) (p := p)
  -- Route correction: once the extension is expressed as the textbook `p`-root tower, the proof
  -- closes by the stagewise induction packaged in `source_tensor_regular_of_pthRootTower`.
  exact source_tensor_regular_of_pthRootTower (A := A) (𝔭 := 𝔭) (p := p) (K := K) (L := L) α hα

/- Domain triage:
- primary domain: mixed power-series/polynomial rings, completed localizations, and geometric
  regularity of generic formal fibers in commutative algebra;
- sampled owner declarations:
  `mixedPowerSeriesPolynomialRing`,
  `CompletedLocalizationAtPrime`,
  `IsGeometricallyRegular`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: this numbered lemma is `source-facing`, while the public surface should
  use the canonical chapter owners `mixedPowerSeriesPolynomialRing` and `R̂_[𝔭]`; the prime-pair
  formal-fiber criterion from Lemma `15.50.2` is only a `bridge/view`;
- primitive data: the ambient ring
  `A = mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k`, a fraction field `K` of `A`, and a
  prime `𝔭 : Spec A`;
- derived API: geometric regularity of the generic formal fiber `R̂_[𝔭] ⊗[A] K`.
-/
-- Proof sketch: use the characteristic-`p` criterion for geometric regularity over the field `K`
-- by testing finite purely inseparable extensions `L/K`. Realize such an `L` as the fraction
-- field of a finite purely inseparable extension of the mixed power-series/polynomial ring,
-- reduce by induction to the degree-`p` case, identify the base change of the completed
-- localization with an `AdjoinRoot (X ^ p - f)` over a regular intermediate ring, and then apply
-- the derivation-extension and regularity criteria from Lemmas `15.48.1`, `15.48.4`, and
-- `15.48.5`.
/-- Lemma 15.50.5: let `A = k[[x_1, ..., x_n]][y_1, ..., y_n]` over a field `k` of
characteristic `p`, and let `K` be a fraction field of `A`. For every prime `𝔭` of `A`, the
generic formal fiber `(A_𝔭)^∧ ⊗[A] K` is geometrically regular over `K`. -/
@[stacks 07PR]
theorem mixedPowerSeriesPolynomialRing_formalFiber_fractionRing_isGeometricallyRegular
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    : IsGeometricallyRegular K (R̂_[𝔭] ⊗[A] K) := by
  -- The fraction field of the characteristic-`p` source ring still has characteristic `p`.
  let _ : CharP K p := inferInstance
  refine genericFormalFiber_isGeometricallyRegular_of_source_tensor_regular
      (A := A) (𝔭 := 𝔭) ?_
  intro L _ _ _ _
  -- The tensor/base-change front end is finished; only the source tower induction remains.
  exact source_tensor_regular_of_finite_purelyInseparable (A := A) (𝔭 := 𝔭) (K := K) (L := L)

end

end
