import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_43_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_37_12
import StacksProject_2024.stacks_project.Chap10.Lemma_10_147_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_151_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_151_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_163_9
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum Topology
open scoped TensorProduct
open scoped PrimeSpectrum

universe u v w

noncomputable section

/-
Domain-style sampling for Lemma 15.115.9:
- primary domain: ramification theory for the canonical field branches of the tensor-product base
  change `K₁ ⊗[K] L` attached to an extension of discrete valuation rings `A ⊂ B`;
- sampled owner declarations:
  `IsUnramifiedWithRespectTo`,
  `IsTamelyRamifiedWithRespectTo`,
  `IsUnramifiedWithRespectTo.iff_isUnramifiedAt`,
  `IsArtinianRing.equivPi`;
- best owner abstraction: the field factors of `K₁ ⊗[K] L` should be owned canonically by
  `m : MaximalSpectrum (K₁ ⊗[K] L)` and the quotient field `(K₁ ⊗[K] L) ⧸ m.asIdeal`, while the
  unramified/tame conditions are derived branchwise properties on those canonical factors;
- primitive-vs-derived split: the primitive branch data are the canonical maximal ideals of `KL`,
  together with the canonical Artinian owner `IsArtinianRing.equivPi KL`; the ramification
  predicates on the branch quotients are the mathematical content of this file.

Source/core/bridge triage:
- `source-facing`: the statement that every field factor of `KL = K₁ ⊗[K] L` is unramified or
  tamely ramified with respect to `B`;
- `core/canonical`: `MaximalSpectrum KL`, the quotient fields `KL ⧸ m.asIdeal`, and the canonical
  decomposition `IsArtinianRing.equivPi KL`;
- `bridge/view`: none exported; the file stays on the canonical branch owner instead of packaging
  the decomposition as arbitrary existential data.
-/

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
variable [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]

local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "KL" => K1 ⊗[K] L

/-- Helper for Lemma 15.115.9: the tensor product `K₁ ⊗[K] L` carries the `B`-algebra structure
coming from the right tensor factor. -/
local instance fractionRingTensorProduct_algebra : Algebra B KL :=
  RingHom.toAlgebra
    (((Algebra.TensorProduct.includeRight : L →ₐ[K] KL).toRingHom).comp
      (algebraMap B L))

/-- Helper for Lemma 15.115.9: the canonical branch field attached to
`m : MaximalSpectrum (K₁ ⊗[K] L)`. -/
private abbrev tensorBranchField (m : MaximalSpectrum KL) :=
  KL ⧸ m.asIdeal

/-- Helper for Lemma 15.115.9: the canonical branch quotient is a field. -/
private abbrev tensorBranchField_field (m : MaximalSpectrum KL) :
    Field (tensorBranchField m) :=
  Ideal.Quotient.field m.asIdeal

local instance tensorBranchField_commRing (m : MaximalSpectrum KL) :
    CommRing (tensorBranchField m) :=
  Ideal.Quotient.commRing m.asIdeal

/-- Helper for Lemma 15.115.9: the branch quotient inherits the `L = FractionRing B`-algebra
structure from the ambient tensor product. -/
private abbrev tensorBranchField_fractionRingAlgebra (m : MaximalSpectrum KL) :
    Algebra L (tensorBranchField m) :=
  RingHom.toAlgebra ((Ideal.Quotient.mk m.asIdeal).comp (algebraMap L KL))

/-- Helper for Lemma 15.115.9: the branch quotient inherits the `B`-algebra structure by composing
`B → L` with the right-factor map into the tensor product and then quotienting by `m`. -/
private abbrev tensorBranchField_algebra (m : MaximalSpectrum KL) :
    Algebra B (tensorBranchField m) :=
  RingHom.toAlgebra
    (((Ideal.Quotient.mk m.asIdeal).comp
      ((algebraMap L KL).comp (algebraMap B L))))

/-- Helper for Lemma 15.115.9: the branch quotient sits in the scalar tower
`B → L → (K₁ ⊗[K] L)/m`. -/
private theorem tensorBranchField_isScalarTower (m : MaximalSpectrum KL) :
    @IsScalarTower B L (tensorBranchField m)
      OreLocalization.instSMulOfIsScalarTower
      (tensorBranchField_fractionRingAlgebra m).toSMul
      (tensorBranchField_algebra m).toSMul := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  rfl

/-- Helper for Lemma 15.115.9: the separable tensor base change `K₁ ⊗[K] L` is reduced. -/
private theorem fractionRingTensorProduct_isReduced :
    IsReduced KL := by
  -- A separable extension stays reduced after tensoring with the reduced `K`-algebra `L`.
  let _ : Algebra.IsSeparableOver K K1 := inferInstance
  simpa using (Lemma_10_43_6 : IsReduced (K1 ⊗[K] L))

/-- Helper for Lemma 15.115.9: the nilradical of the separable tensor base change vanishes. -/
private theorem fractionRingTensorProduct_nilradical_eq_bot :
    nilradical KL = (⊥ : Ideal KL) := by
  -- Once the tensor product is reduced, its nilradical is the zero ideal.
  let _ : IsReduced KL := fractionRingTensorProduct_isReduced
  simpa using (nilradical_eq_zero (R := KL))

/-- Helper for Lemma 15.115.9: maximality of an ideal is preserved under a ring equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Map maximality through the surjective equivalence map.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le (f := e.toRingHom) e.surjective ?_
  intro x hx
  change e x = 0 at hx
  have hx0 : x = 0 := e.injective (by simpa using hx)
  simpa [hx0]

/-- Helper for Lemma 15.115.9: transporting an ideal across a compatible ring equivalence and then
contracting back to the base agrees with contracting the original ideal. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  -- Rewrite the contraction through `e`; surjectivity then recovers the original ideal.
  ext x
  rw [Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    simpa [Ideal.mem_comap] using (show f x ∈ q from (e.injective hyx) ▸ hy)
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Lemma 15.115.9: a lies-over relation is preserved when the target ring is
transported across a compatible ring equivalence. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions through the equivalence and reuse the original lies-over equality.
  rw [Ideal.liesOver_iff, Ideal.under_def]
  calc
    p = q.comap (algebraMap R S) := q.over_def p
    _ = (Ideal.map e.toRingHom q).comap (algebraMap R T) :=
      (ideal_map_comap_eq_of_ringEquiv_comp
        (f := algebraMap R S) (g := algebraMap R T) e he q).symm

/-- Helper for Lemma 15.115.9: the integral closure `integralClosure A K₁` is flat over `A`
because it is torsion-free over the Bezout domain underlying the base DVR. -/
private theorem integralClosure_flat_over_base_fraction_extension :
    Module.Flat A (integralClosure A K1) := by
  -- Injectivity of `A → integralClosure A K₁` gives faithful scalar action, hence torsion-freeness.
  let _ : FaithfulSMul A (integralClosure A K1) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A K1)).mpr
      (algebraMap_injective_of_field_isFractionRing A (integralClosure A K1) K K1)
  let _ : Module.IsTorsionFree A (integralClosure A K1) :=
    Module.IsTorsionFree.trans_faithfulSMul A (integralClosure A K1) (integralClosure A K1)
  have htor : Submodule.torsion A (integralClosure A K1) = ⊥ :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance
  -- Over the DVR `A`, torsion-free modules are flat.
  exact
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout
      (R := A) (M := integralClosure A K1)).2 htor

/-- Helper for Lemma 15.115.9: the residue field at the zero prime of a domain is canonically its
fraction field. -/
private noncomputable def zeroPrime_residueField_algEquiv_fractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    -- The zero-prime quotient is just `R`, so its residue field is another fraction-ring model.
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap R ((⊥ : Ideal R).ResidueField) x =
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal R) x) =
          algebraMap R ((⊥ : Ideal R).ResidueField) x by
      rfl
  -- The standard fraction-ring equivalence identifies the two generic-point owners.
  exact FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)

/-- Helper for Lemma 15.115.9: the zero ideal of `integralClosure A K₁` contracts to the zero
ideal of `A`. -/
private theorem bot_under_eq_bot_of_integralClosure :
    ((⊥ : Ideal (integralClosure A K1)).under A) = ⊥ := by
  -- Compare the zero element in the integral closure with its image in the ambient field `K₁`.
  ext a
  constructor
  · intro ha
    change algebraMap A (integralClosure A K1) a = 0 at ha
    have hK1' : ((algebraMap A (integralClosure A K1) a : integralClosure A K1) : K1) = 0 := by
      simpa using congrArg (fun z : integralClosure A K1 ↦ (z : K1)) ha
    have hK1 : algebraMap A K1 a = 0 := by
      simpa using hK1'
    have hK : algebraMap A K a = 0 := by
      apply FaithfulSMul.algebraMap_injective (FractionRing A) K1
      simpa [IsScalarTower.algebraMap_apply A K K1] using hK1
    exact IsFractionRing.injective A K (by simpa using hK)
  · intro ha
    have ha0 : a = 0 := by
      simpa using ha
    simpa [ha0]

/-- Helper for Lemma 15.115.9: a prime of `integralClosure A K₁` whose contraction to `A` is
zero must be the generic point. -/
private theorem zero_contraction_prime_eq_bot_of_integralClosure
    (q : PrimeSpectrum (integralClosure A K1))
    (hq : q.asIdeal.under A = ⊥) :
    q.asIdeal = ⊥ := by
  by_contra hqne
  letI : q.asIdeal.IsPrime := q.isPrime
  have hqmax : q.asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (R := integralClosure A K1) (p := q.asIdeal) inferInstance hqne
  have hunderMax : (q.asIdeal.under A).IsMaximal := by
    -- Integrality of the normalization sends maximal ideals back to maximal ideals.
    simpa [Ideal.under_def] using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal)
  have hmaxbot : IsLocalRing.maximalIdeal A = ⊥ := by
    -- The only maximal ideal of the DVR would then contract to `0`, forcing a field.
    simpa [hq] using (IsLocalRing.eq_maximalIdeal hunderMax).symm
  exact IsDiscreteValuationRing.not_a_field A hmaxbot

/-- Helper for Lemma 15.115.9: a closed-fiber prime of `integralClosure A K₁` is unramified over
`A` as soon as `K₁` is unramified with respect to `A`. -/
private theorem closedFiber_branch_isUnramifiedAt
    (hK1 : IsUnramifiedWithRespectTo A K1)
    (q : PrimeSpectrum (integralClosure A K1))
    (hq : q.asIdeal.under A = IsLocalRing.maximalIdeal A) :
    Algebra.IsUnramifiedAt A q.asIdeal := by
  have hqmax_comap :
      (Ideal.comap (algebraMap A (integralClosure A K1)) q.asIdeal).IsMaximal := by
    -- The closed fiber is exactly the maximal ideal of the local base ring.
    simpa [Ideal.under_def, hq] using
      (IsLocalRing.maximalIdeal.isMaximal A :
        Ideal.IsMaximal (IsLocalRing.maximalIdeal A))
  letI : q.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal hqmax_comap
  letI : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff q.asIdeal (IsLocalRing.maximalIdeal A)).2 hq.symm
  letI : Module.IsTorsionFree A K1 := .trans_faithfulSMul A K K1
  letI : Module.IsTorsionFree A (integralClosure A K1) := IsIntegralClosure.isTorsionFree A K1
  letI : IsUnramifiedWithRespectTo A K1 := hK1
  -- This is exactly the branchwise owner theorem from Definition `15.112.7`.
  exact
    ((IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A)).1 hK1) q.asIdeal

/-- Helper for Lemma 15.115.9: the zero ideal of `integralClosure A K₁` lies over the zero ideal
of the base DVR. -/
private lemma zeroIdeal_liesOver_bot_of_integralClosure :
    (⊥ : Ideal (integralClosure A K1)).LiesOver (⊥ : Ideal A) := by
  -- The zero ideal contracts to zero because the normalization embeds into the ambient field.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.under_def] using (bot_under_eq_bot_of_integralClosure (A := A) (K1 := K1)).symm

/-- Helper for Lemma 15.115.9: the zero-prime residue-field extension of `integralClosure A K₁`
is the given generic fraction-field extension in disguise, hence separable. -/
private theorem zeroPrime_residueField_separable_of_fraction_extension
    [(⊥ : Ideal (integralClosure A K1)).LiesOver (⊥ : Ideal A)]
    [Algebra ((⊥ : Ideal A).ResidueField)
      ((⊥ : Ideal (integralClosure A K1)).ResidueField)] :
    Algebra.IsSeparable ((⊥ : Ideal A).ResidueField)
      ((⊥ : Ideal (integralClosure A K1)).ResidueField) := by
  let A1 := integralClosure A K1
  let _ : IsFractionRing A1 K1 := integralClosure.isFractionRing_of_finite_extension K K1
  let eFrac : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  let eZero : FractionRing A ≃ₐ[A] ((⊥ : Ideal A).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing A
  let eBase : K ≃ₐ[A] ((⊥ : Ideal A).ResidueField) := eFrac.symm.trans eZero
  let eFracTop : FractionRing A1 ≃ₐ[A1] K1 := FractionRing.algEquiv A1 K1
  let eZeroTop : FractionRing A1 ≃ₐ[A1] ((⊥ : Ideal A1).ResidueField) :=
    zeroPrime_residueField_algEquiv_fractionRing A1
  let eTop : K1 ≃ₐ[A1] ((⊥ : Ideal A1).ResidueField) := eFracTop.symm.trans eZeroTop
  have hcomm_pointwise (x : K) :
      eTop (algebraMap K K1 x) =
        algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField) (eBase x) := by
    have hfrac :
        algebraMap K K1 x =
          eFracTop (algebraMap (FractionRing A) (FractionRing A1) (eFrac.symm x)) := by
      -- Proof comment: first compare `K1` with the canonical fraction-ring model of `A1`.
      simpa [eFrac] using
        IsFractionRing.algEquiv_commutes eFrac eFracTop (eFrac.symm x)
    have hzero :
        algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField) (eBase x) =
          eZeroTop (algebraMap (FractionRing A) (FractionRing A1) (eFrac.symm x)) := by
      -- Proof comment: the same compatibility holds for the zero-prime residue-field models.
      simpa [eBase, eZero] using
        IsFractionRing.algEquiv_commutes eZero eZeroTop (eFrac.symm x)
    calc
      eTop (algebraMap K K1 x)
          = eZeroTop (algebraMap (FractionRing A) (FractionRing A1) (eFrac.symm x)) := by
              rw [hfrac]
              simp [eTop]
      _ =
        algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField) (eBase x) := by
          simpa using hzero.symm
  have hcomm :
      RingHom.comp
          (algebraMap ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField))
          eBase.toRingHom =
        RingHom.comp eTop.toRingHom (algebraMap K K1) := by
    -- Proof comment: repackage the pointwise compatibility as the square needed for transport of
    -- separability.
    ext x
    simpa using (hcomm_pointwise x).symm
  -- Proof comment: separability transports across the compatible source and target
  -- fraction-field/residue-field equivalences.
  simpa using
    (Algebra.IsSeparable.of_equiv_equiv eBase.toRingEquiv eTop.toRingEquiv hcomm)

/-- Helper for Lemma 15.115.9: the generic point of the normalization is étale over the base DVR.
-/
private theorem zeroPrime_isEtaleAt_integralClosure :
    Algebra.IsEtaleAt A (⊥ : Ideal (integralClosure A K1)) := by
  let A1 := integralClosure A K1
  let _ : (⊥ : Ideal A1).LiesOver (⊥ : Ideal A) :=
    zeroIdeal_liesOver_bot_of_integralClosure (A := A) (K1 := K1)
  let _ : Algebra ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField) := inferInstance
  let _ : Algebra.IsSeparable ((⊥ : Ideal A).ResidueField) ((⊥ : Ideal A1).ResidueField) :=
    zeroPrime_residueField_separable_of_fraction_extension (A := A) (K1 := K1)
  let _ : Module.Finite A A1 := IsIntegralClosure.finite A K K1 A1
  let _ : Module.FinitePresentation A A1 := Module.finitePresentation_of_finite A A1
  let _ : Algebra.FinitePresentation A A1 := Algebra.FinitePresentation.of_finitePresentation A A1
  have hflatAlg : (algebraMap A A1).Flat := by
    -- Proof comment: global flatness of the normalization localizes to the generic-point map.
    exact RingHom.flat_algebraMap_iff.mpr <|
      integralClosure_flat_over_base_fraction_extension (A := A) (K1 := K1)
  have hflat :
      (Localization.localRingHom (⊥ : Ideal A) (⊥ : Ideal A1)
        (algebraMap A A1) ((⊥ : Ideal A1).over_def (⊥ : Ideal A))).Flat := by
    -- Proof comment: pass the global flat algebra map to the induced local map at `⊥`.
    exact RingHom.Flat.localRingHom hflatAlg (⊥ : Ideal A1) (⊥ : Ideal A)
      ((⊥ : Ideal A1).over_def (⊥ : Ideal A))
  have hmax :
      (⊥ : Ideal A).map (algebraMap A (Localization.AtPrime (⊥ : Ideal A1))) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal A1)) := by
    letI : IsFractionRing A1 (Localization.AtPrime (⊥ : Ideal A1)) := by
      delta IsFractionRing
      simpa [Ideal.primeCompl_bot] using
        (inferInstance :
          IsLocalization ((⊥ : Ideal A1).primeCompl)
            (Localization.AtPrime (⊥ : Ideal A1)))
    let _ : Field (Localization.AtPrime (⊥ : Ideal A1)) :=
      IsFractionRing.toField A1
    have hfield : IsField (Localization.AtPrime (⊥ : Ideal A1)) := by
      exact Field.toIsField _
    have hmaxbot :
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal A1)) = ⊥ := by
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    -- Proof comment: the localization at the zero prime is a field, so both sides are `⊥`.
    simpa [hmaxbot]
  -- Proof comment: Lemma `10.143.7` now applies directly at the zero prime.
  exact
    Algebra.isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField
      (R := A) (S := A1) (p := ⊥) (q := ⊥) hflat hmax

/-- Helper for Lemma 15.115.9: the generic point of the normalization is étale over the base DVR
when the fraction-field extension is finite separable. -/
private theorem integralClosure_zero_contraction_isEtaleAt_of_separable_fraction_extension
    (q : PrimeSpectrum (integralClosure A K1))
    (hq : q.asIdeal.under A = ⊥) :
    Algebra.IsEtaleAt A q.asIdeal := by
  have hqbot : q.asIdeal = ⊥ :=
    zero_contraction_prime_eq_bot_of_integralClosure (A := A) (K1 := K1) q hq
  -- Reduce the generic-contraction branch to the zero-prime owner theorem.
  simpa [hqbot] using zeroPrime_isEtaleAt_integralClosure (A := A) (K1 := K1)

/-- Helper for Lemma 15.115.9: every contracted prime in the local base is either the generic
point or the closed point. -/
private lemma prime_under_eq_bot_or_maximalIdeal
    (q : PrimeSpectrum (integralClosure A K1)) :
    q.asIdeal.under A = ⊥ ∨ q.asIdeal.under A = IsLocalRing.maximalIdeal A := by
  by_cases hq : q.asIdeal.under A = ⊥
  · exact Or.inl hq
  · have hprime : (q.asIdeal.under A).IsPrime := by
      simpa [Ideal.under_def] using
        (Ideal.comap_isPrime (algebraMap A (integralClosure A K1)) q.asIdeal)
    have hmax : (q.asIdeal.under A).IsMaximal :=
      Ideal.IsPrime.isMaximal (R := A) (p := q.asIdeal.under A) hprime hq
    exact Or.inr (IsLocalRing.eq_maximalIdeal hmax)

/-- Helper for Lemma 15.115.9: if every prime of a finitely presented algebra is étale, then the
whole algebra is étale. -/
private theorem etale_of_forall_prime_isEtaleAt_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (h : ∀ q : PrimeSpectrum S, Algebra.IsEtaleAt R q.asIdeal) :
    Algebra.Etale R S := by
  have hsubset : (D((1 : S)) : Set (PrimeSpectrum S)) ⊆ Algebra.etaleLocus R S := by
    intro q hq
    -- Proof comment: every prime is étale by hypothesis, hence belongs to the étale locus.
    exact (Algebra.mem_etaleLocus_iff (R := R) (A := S) (p := q)).2 (h q)
  have hAway : Algebra.Etale R (Localization.Away (1 : S)) :=
    (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R) (A := S)).1 hsubset
  let eS : S ≃ₐ[S] Localization.Away (1 : S) :=
    IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  let e : Localization.Away (1 : S) ≃ₐ[R] S := eS.symm.restrictScalars R
  -- Proof comment: localizing away from `1` does nothing, so the global étale structure on
  -- `S[1⁻¹]` transports back to `S`.
  let _ : Algebra.Etale R (Localization.Away (1 : S)) := hAway
  exact Algebra.Etale.of_equiv e

/-- Helper for Lemma 15.115.9: if `K₁ / FractionRing A` is unramified with respect to `A`, then
the normalization `integralClosure A K₁` is étale over `A`. -/
private theorem integralClosure_etale_of_unramified_fraction_extension
    (hK1 : IsUnramifiedWithRespectTo A K1) :
    Algebra.Etale A (integralClosure A K1) := by
  let A1 := integralClosure A K1
  let _ : Module.Flat A A1 :=
    integralClosure_flat_over_base_fraction_extension (A := A) (K1 := K1)
  let _ : Module.Finite A A1 := IsIntegralClosure.finite A K K1 A1
  let _ : Module.FinitePresentation A A1 := Module.finitePresentation_of_finite A A1
  let _ : Algebra.FinitePresentation A A1 := Algebra.FinitePresentation.of_finitePresentation A A1
  refine etale_of_forall_prime_isEtaleAt_finitePresentation (R := A) (S := A1) ?_
  intro q
  rcases prime_under_eq_bot_or_maximalIdeal (A := A) (K1 := K1) q with hq | hq
  · -- Proof comment: the generic-contraction branch is the zero-prime case isolated above.
    exact
      integralClosure_zero_contraction_isEtaleAt_of_separable_fraction_extension
        (A := A) (K1 := K1) q hq
  · let _ : q.asIdeal.IsPrime := q.isPrime
    let _ : Algebra.IsUnramifiedAt A q.asIdeal :=
      closedFiber_branch_isUnramifiedAt (A := A) (K1 := K1) hK1 q hq
    -- Proof comment: on the closed fiber, unramifiedness plus global flatness upgrades to local
    -- étaleness by the standard finite-presentation criterion.
    simpa using
      (Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := A) (S := A1) q.asIdeal)

/-- Helper for Lemma 15.115.9: an integral domain model that is étale over the base DVR realizes
an unramified fraction-field extension. -/
private theorem isUnramifiedWithRespectTo_of_integral_etale_fractionRing_model
    {R : Type v} [CommRing R] [IsDomain R] [Algebra A R]
    {F : Type w} [Field F] [Algebra A F] [Algebra (FractionRing A) F]
    [IsScalarTower A (FractionRing A) F] [Algebra R F] [IsScalarTower A R F]
    [FiniteDimensional (FractionRing A) F] [Algebra.IsSeparable (FractionRing A) F]
    [IsFractionRing R F] [Algebra.IsIntegral A R] [Algebra.Etale A R] :
    IsUnramifiedWithRespectTo A F := by
  letI : IsNormalRing R := by
    -- Smooth algebras over the normal base DVR remain normal.
    exact isNormalRing_of_smooth
  letI : IsIntegrallyClosed R := by
    exact isIntegrallyClosed_of_isNormalRing
  letI : IsIntegralClosure R A F :=
    -- Replace the chosen integral model by the canonical integral closure once and for all.
    IsIntegralClosure.of_isIntegrallyClosed R A F
  let e : R ≃ₐ[A] integralClosure A F :=
    IsIntegralClosure.equiv A R F (integralClosure A F)
  have hEtaleIntegralClosure : Algebra.Etale A (integralClosure A F) := by
    -- Étaleness transports across the canonical normalization equivalence.
    exact Algebra.Etale.of_equiv e
  letI : Algebra.Etale A (integralClosure A F) := hEtaleIntegralClosure
  refine ((IsUnramifiedWithRespectTo.iff_isUnramifiedAt (A := A)).2 ?_)
  intro P _ _
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (Ideal.under A P) := Ideal.over_under P
  refine (Algebra.isUnramifiedAt_iff_map_eq A (Ideal.under A P) P).2 ?_
  refine ⟨?_, ?_⟩
  · -- Global étaleness gives finite separable residue-field extensions on every branch.
    exact
      (residueField_finite_and_separable_of_exists_etale_away
        (R := A) (S := integralClosure A F) P
        ⟨1, by
          simpa [Ideal.eq_top_iff_one] using
            (show P ≠ ⊤ from Ideal.IsPrime.ne_top (I := P) inferInstance),
          inferInstance⟩).2
  · -- The source map to the localization hits the maximal ideal on the branch neighborhood.
    simpa using
      (show Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.under A P) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) from by
        simpa using
          (map_eq_maximalIdeal_of_exists_etale_away
            (R := A) (S := integralClosure A F) P
            ⟨1, by
              simpa [Ideal.eq_top_iff_one] using
                (show P ≠ ⊤ from Ideal.IsPrime.ne_top (I := P) inferInstance),
              inferInstance⟩))

/-- Helper for Lemma 15.115.9: a ring map from a finite product of commutative rings to a domain
factors through one coordinate projection. -/
private theorem algHom_to_domain_factors_through_product_component
    {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    {T : Type*} [CommRing T] [IsDomain T]
    (φ : (Π i, R i) →+* T) :
    ∃ i, ∃ ψ : R i →+* T, φ = ψ.comp (Pi.evalRingHom R i) := by
  let p : PrimeSpectrum (Π i, R i) :=
    ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  -- Pick the factor selected by the prime kernel of the map to the domain.
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hker :
      RingHom.ker (Pi.evalRingHom R i) ≤ RingHom.ker φ := by
    intro x hx
    -- Elements killed by the chosen projection map to `0`, hence lie in the selected prime.
    have hx0 : Pi.evalRingHom R i x = 0 := by
      simpa [RingHom.mem_ker] using hx
    have hxq : Pi.evalRingHom R i x ∈ q.asIdeal := by
      simpa [hx0] using (q.asIdeal.zero_mem : (0 : R i) ∈ q.asIdeal)
    -- Rewrite the target kernel through the prime-spectrum identification.
    rw [show RingHom.ker φ = p.asIdeal by rfl, ← hq, PrimeSpectrum.comap_asIdeal]
    exact hxq
  let ψ : R i →+* T :=
    (Pi.evalRingHom R i).liftOfSurjective (Function.surjective_eval i) ⟨φ, hker⟩
  refine ⟨i, ψ, ?_⟩
  -- Surjectivity of the coordinate projection characterizes the descended factor map.
  simpa [ψ] using
    (RingHom.liftOfSurjective_comp (f := Pi.evalRingHom R i)
      (hf := Function.surjective_eval i) ⟨φ, hker⟩).symm

/-- Helper for Lemma 15.115.9: a surjective algebra map from a finite product of fields to a
field is already an algebra isomorphism on one factor. -/
private theorem surjective_algHom_from_product_of_fields_factors
    {k : Type*} [Field k] {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, Field (F i)]
    {N : Type*} [Field N] [Algebra k N] [∀ i, Algebra k (F i)]
    (φ : (Π i, F i) →ₐ[k] N) (hφ : Function.Surjective φ) :
    ∃ i, Nonempty (F i ≃ₐ[k] N) := by
  obtain ⟨i, ψ, hψ⟩ :=
    algHom_to_domain_factors_through_product_component (R := F) (T := N) φ.toRingHom
  let ψA : F i →ₐ[k] N :=
    { toRingHom := ψ
      commutes' := by
        intro x
        -- Compare the factorization on the constant tuple coming from the base field.
        have hconst :=
          congrArg
            (fun f : (Π j, F j) →+* N ↦ f (algebraMap k (Π j, F j) x))
            hψ
        simpa using hconst.symm }
  have hsurjψ : Function.Surjective ψA := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    refine ⟨x i, ?_⟩
    -- Evaluate the factorization on the chosen preimage tuple.
    have hx := congrArg (fun f : (Π j, F j) →+* N ↦ f x) hψ
    simpa [ψA] using hx.symm
  -- A surjective algebra hom between fields is bijective, hence an algebra equivalence.
  exact ⟨i, ⟨AlgEquiv.ofBijective ψA ⟨ψA.injective, hsurjψ⟩⟩⟩

-- Proof sketch: `K1 / K` is finite separable, so `KL = K1 ⊗[K] L` is a reduced Artinian
-- `L`-algebra. Its canonical branch fields are therefore indexed by `m : MaximalSpectrum KL`,
-- with branch quotient `KL ⧸ m.asIdeal`. Let `A1` be the integral closure of `A` in `K1`.
-- Unramifiedness of `K1 / K` identifies `A1` as finite étale over `A`; base change to `B`
-- preserves finite étaleness, so the integral closure of `B` in each canonical branch quotient is
-- étale over `B`, which is exactly unramifiedness with respect to `B`.
/-- Lemma 15.115.9: if `A ⊂ B` is an extension of discrete valuation rings and
`K1 / FractionRing A` is a finite separable extension that is unramified with respect to `A`,
then every canonical branch field `((K1 ⊗[FractionRing A] FractionRing B) ⧸ m.asIdeal)` indexed by
`m : MaximalSpectrum (K1 ⊗[FractionRing A] FractionRing B)` is unramified with respect to `B`. -/
theorem isUnramifiedWithRespectTo_fractionRingTensorProduct_branch
    {A : Type u} {B : Type v} {K1 : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
    [IsScalarTower A (FractionRing A) K1]
    [FiniteDimensional (FractionRing A) K1]
    [Algebra.IsSeparable (FractionRing A) K1]
    (m : MaximalSpectrum (K1 ⊗[FractionRing A] FractionRing B))
    (hK1 : IsUnramifiedWithRespectTo A K1) :
    show Prop from
      @IsUnramifiedWithRespectTo B (tensorBranchField m)
        _ _ _
        (tensorBranchField_field m)
        (tensorBranchField_algebra m)
        (tensorBranchField_fractionRingAlgebra m)
        (tensorBranchField_isScalarTower m) := by
          -- Route correction: the old blocker was the reduced-versus-unreduced tensor owner.
          -- The branch-selection step from a product of fields is now isolated above in
          -- `surjective_algHom_from_product_of_fields_factors`; this removes the old
          -- normalization-comparison loop from the closing part of the proof.
          -- The remaining gap is now only the tensor-factor endgame: build the finite étale
          -- integral model `B ⊗[A] integralClosure A K₁`, split it into Dedekind-domain factors,
          -- and feed the resulting generic-fiber product map into that branch-selection lemma.
          let _ := hK1
          let _ : Module.Flat A (integralClosure A K1) :=
            integralClosure_flat_over_base_fraction_extension (A := A) (K1 := K1)
          let _ : Algebra.Etale A (integralClosure A K1) :=
            integralClosure_etale_of_unramified_fraction_extension
              (A := A) (K1 := K1) hK1
          -- TODO: base-change this étale integral model to `B`, split
          -- `B ⊗[A] integralClosure A K1` into Dedekind-domain factors, and invoke the
          -- product-factorization helper on the resulting generic-fiber map to
          -- `tensorBranchField m`.
          sorry

-- Proof sketch: use the same canonical decomposition `IsArtinianRing.equivPi KL`. By Lemma
-- `15.115.6`, after enlarging `K1` if necessary one reduces to the Kummer description from Lemma
-- `15.115.7`; then Abhyankar's lemma gives tame ramification for the intermediate branches over
-- `B`, and Lemma `15.115.5` passes tameness from the localized branches back to each canonical
-- branch quotient `KL ⧸ m.asIdeal`.
/-- If `K1 / FractionRing A` is tamely ramified with respect to `A`, then every canonical branch
field `((K1 ⊗[FractionRing A] FractionRing B) ⧸ m.asIdeal)` is tamely ramified with respect to
`B`. -/
theorem isTamelyRamifiedWithRespectTo_fractionRingTensorProduct_branch
    {A : Type u} {B : Type v} {K1 : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
    [IsScalarTower A (FractionRing A) K1]
    [FiniteDimensional (FractionRing A) K1]
    [Algebra.IsSeparable (FractionRing A) K1]
    (m : MaximalSpectrum (K1 ⊗[FractionRing A] FractionRing B))
    (hK1 : IsTamelyRamifiedWithRespectTo A K1) :
    show Prop from
      @IsTamelyRamifiedWithRespectTo B (tensorBranchField m)
        _ _ _
        (tensorBranchField_field m)
        (tensorBranchField_algebra m)
        (tensorBranchField_fractionRingAlgebra m)
        (tensorBranchField_isScalarTower m) := by
          -- Route correction: the reducedness step is now isolated globally, so the tame proof is
          -- blocked only by the same finite-étale branch extraction needed in the unramified
          -- theorem before the `15.115.7` Kummer reduction can be applied.
          let _ := hK1
          -- TODO: first finish the unramified branch theorem using the finite étale factor route;
          -- only then reuse it inside the Kummer reduction from Lemma `15.115.7`.
          sorry

end
