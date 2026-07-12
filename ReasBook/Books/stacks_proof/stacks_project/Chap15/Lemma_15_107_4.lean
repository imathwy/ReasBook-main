import Mathlib
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_155_2
import StacksProject_2024.Chap15.Lemma_15_18_2
import StacksProject_2024.Chap15.Lemma_15_45_2
import StacksProject_2024.Chap15.Lemma_15_105_14.Index
import StacksProject_2024.Chap15.Lemma_15_105_23
import StacksProject_2024.Chap15.Lemma_15_106_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

universe u v w

noncomputable section

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

section StrictHenselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ash : Type u} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

-- Route correction: work file-locally with the reduced normalization setup so this item no longer
-- depends on the currently broken `Definition_15_107_1` import chain.
local notation:max "(" R ")" "_red" => R ⧸ nilradical R
local notation "A′" => integralClosure (A)_red (FractionRing (A)_red)
local notation "A′sh" => A′ ⊗[A] Ash
local notation "κ" => ResidueField A

/-- Helper for Lemma 15.107.4: the reduction `(A)_red` of a local ring is again local. -/
local instance unibranchReduction_isLocalRing : IsLocalRing (A)_red := by
  let _ : Nontrivial (A ⧸ nilradical A) := Ideal.Quotient.nontrivial_iff.2 <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      (nilradical_le_prime (maximalIdeal A))
  simpa [Ideal.Quotient.algebraMap_eq] using
    (IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective :
      IsLocalRing (A ⧸ nilradical A))

/-- Helper for Lemma 15.107.4: the quotient map `A → (A)_red` is local. -/
local instance unibranchReduction_isLocalHom : IsLocalHom (algebraMap A (A)_red) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.107.4: the reduced normalization inherits its `A`-algebra structure. -/
local instance unibranchNormalization_algebra : Algebra A A′ :=
  ((algebraMap (A)_red A′).comp (algebraMap A (A)_red)).toAlgebra

/-- Helper for Lemma 15.107.4: the reduced normalization sits in the expected scalar tower over
`A → (A)_red`. -/
local instance unibranchNormalization_isScalarTower : IsScalarTower A (A)_red A′ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Helper for Lemma 15.107.4: the reduced normalization is integral over the original local
ring. -/
local instance unibranchNormalization_isIntegral : Algebra.IsIntegral A A′ :=
  Algebra.IsIntegral.trans (A)_red

/-- Helper for Lemma 15.107.4: any maximal ideal of the reduced normalization contracts to the
closed point of `A`. -/
theorem unibranchNormalization_comap_maximalIdeal
    {m : Ideal A′} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap A A′) m = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

local instance unibranchNormalizationTensorLeftAlgebra : Algebra A′ A′sh :=
  Algebra.TensorProduct.leftAlgebra

/-- Helper for Lemma 15.107.4: the left tensor-factor algebra structure gives the expected
`A'`-module structure on `A' ⊗[A] Ash`. -/
local instance unibranchNormalizationTensorLeftModule : Module A′ A′sh :=
  (unibranchNormalizationTensorLeftAlgebra (A := A) (Ash := Ash)).toModule

/-- Helper for Lemma 15.107.4: the maximal-ideal residue field agrees with the usual residue field
of a local ring. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.107.4: the maximal-ideal residue-field equivalence sends quotient classes
to the usual local residue classes. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      IsLocalRing.residue A a := by
  -- Compare both sides through the inverse equivalence arising from the quotient-residue-field map.
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (IsLocalRing.residue A a) by rfl]
  change
    maximalIdealResidueFieldEquiv A
        ((maximalIdealResidueFieldEquiv A).symm (IsLocalRing.residue A a)) =
      IsLocalRing.residue A a
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (IsLocalRing.residue A a)

/-- Helper for Lemma 15.107.4: the inverse maximal-ideal residue-field equivalence sends the
local residue class of `a` back to the quotient class of `a`. -/
private theorem maximalIdealResidueFieldEquiv_symm_apply_residue
    (a : A) :
    (maximalIdealResidueFieldEquiv A).symm (IsLocalRing.residue A a) =
      algebraMap A (maximalIdeal A).ResidueField a := by
  -- Apply the forward comparison and then invert the equivalence.
  apply (maximalIdealResidueFieldEquiv A).injective
  simp [maximalIdealResidueFieldEquiv_apply_algebraMap (A := A)]

/-- Helper for Lemma 15.107.4: quotienting a local ring by its maximal ideal gives the usual
residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (R ⧸ maximalIdeal R) ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).trans
    (maximalIdealResidueFieldEquiv R)

/-- Helper for Lemma 15.107.4: the residue field at a maximal point of the reduced normalization
is canonically a `κ(A)`-algebra. -/
private noncomputable def unibranchNormalizationResidueFieldMap
    (m : MaximalSpectrum A′) :
    κ →+* m.asIdeal.ResidueField :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A A′)
      (unibranchNormalization_comap_maximalIdeal (A := A) m.isMaximal).symm).comp
    (maximalIdealResidueFieldEquiv A).symm.toRingHom

/-- Helper for Lemma 15.107.4: each maximal-point residue field of the reduced normalization
inherits its canonical `κ(A)`-algebra structure. -/
private noncomputable instance maximalSpectrumResidueFieldAlgebra
    (m : MaximalSpectrum A′) :
    Algebra κ m.asIdeal.ResidueField :=
  (unibranchNormalizationResidueFieldMap (A := A) m).toAlgebra

/-- Helper for Lemma 15.107.4: the residue field of the chosen strict henselization is naturally a
`κ(A)`-algebra. -/
local instance strictHenselizationResidueFieldAlgebra : Algebra κ (ResidueField Ash) :=
  RingHom.toAlgebra (ResidueField.map (algebraMap A Ash))

private noncomputable abbrev maximalSpectrumToResidueField
    (m : MaximalSpectrum A′) :
    A′ →+* m.asIdeal.ResidueField :=
  (algebraMap (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField).comp (Ideal.Quotient.mk m.asIdeal)

/-- Helper for Lemma 15.107.4: the canonical quotient map from the reduced normalization to the
residue field at a maximal point is surjective. -/
private theorem maximalSpectrumToResidueField_surjective
    (m : MaximalSpectrum A′) :
    Function.Surjective (maximalSpectrumToResidueField m) := by
  -- Every residue-field element comes from the maximal quotient, and every quotient class comes
  -- from an element of the original ring.
  intro x
  rcases (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal).2 x with ⟨y, rfl⟩
  rcases Ideal.Quotient.mk_surjective y with ⟨z, rfl⟩
  exact ⟨z, rfl⟩

/-- Helper for Lemma 15.107.4: the maximal quotient `A′ / m` is canonically the residue field
`κ(m)` of the maximal ideal `m`. -/
private noncomputable abbrev quotient_residueField_algEquiv_of_maximal
    (m : MaximalSpectrum A′) :
    (A′ ⧸ m.asIdeal) ≃ₐ[A′ ⧸ m.asIdeal] m.asIdeal.ResidueField :=
  AlgEquiv.ofBijective
    (Algebra.ofId (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal)

/-- Helper for Lemma 15.107.4: the quotient-to-residue-field equivalence sends the class of
`a : A'` to the corresponding residue-field class. -/
private theorem quotient_residueField_algEquiv_of_maximal_apply_mk
    (m : MaximalSpectrum A′) (a : A′) :
    quotient_residueField_algEquiv_of_maximal (A := A) m (Ideal.Quotient.mk m.asIdeal a) =
      algebraMap A′ m.asIdeal.ResidueField a := by
  -- Proof comment: this algebra equivalence is built from the canonical quotient map, so on a
  -- quotient class it is definitionally the usual residue-field map.
  rfl

/-- Helper for Lemma 15.107.4: the residue field at a maximal ideal is integral over the
corresponding quotient ring because the quotient map is an isomorphism. -/
private theorem quotient_isIntegral_residueField
    (m : MaximalSpectrum A′) :
    Algebra.IsIntegral (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField := by
  -- Source route: because `A′ / m → κ(m)` is surjective, every residue-field element comes from
  -- a quotient element, and that quotient element is integral by the monic polynomial `X - C y`.
  rw [← algebraMap_isIntegral_iff]
  intro x
  change IsIntegral (A′ ⧸ m.asIdeal) x
  rcases (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal).2 x with ⟨y, rfl⟩
  -- Transport the canonical self-integrality statement across the quotient-to-residue-field map.
  simpa using
    (isIntegral_algebraMap :
      IsIntegral (A′ ⧸ m.asIdeal) (algebraMap (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField y))

/-- Helper for Lemma 15.107.4: the residue-field map `κ(A) → κ(m')` composed with the quotient
map `A → κ(A)` agrees with the direct composite `A → A' → κ(m')`. -/
private theorem unibranchNormalizationResidueFieldMap_comp_residue
    (m : MaximalSpectrum A′) :
    (unibranchNormalizationResidueFieldMap (A := A) m).comp (IsLocalRing.residue A) =
      (maximalSpectrumToResidueField m).comp (algebraMap A A′) := by
  -- Both maps are determined by the image of an element `a : A`, so rewrite that image on each
  -- side to the same quotient-residue-class in `κ(m')`.
  ext a
  change
    Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A A′)
        (unibranchNormalization_comap_maximalIdeal (A := A) m.isMaximal).symm
        ((maximalIdealResidueFieldEquiv A).symm (IsLocalRing.residue A a)) =
      (algebraMap (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField) (Ideal.Quotient.mk m.asIdeal
        (algebraMap A A′ a))
  rw [maximalIdealResidueFieldEquiv_symm_apply_residue (A := A)]
  rw [Ideal.ResidueField.map_algebraMap]
  rfl

/-- Helper for Lemma 15.107.4: the residue field at a maximal point of the reduced normalization
inherits its canonical `A'`-algebra structure from the quotient map. -/
private noncomputable instance maximalSpectrumBaseAlgebra
    (m : MaximalSpectrum A′) :
    Algebra A′ m.asIdeal.ResidueField :=
  RingHom.toAlgebra (maximalSpectrumToResidueField m)

/-- Helper for Lemma 15.107.4: an integral local homomorphism induces an integral extension on
residue fields. -/
private theorem residueField_isIntegral_of_local_integral_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S] :
    Algebra.IsIntegral (ResidueField R) (ResidueField S) := by
  let ρ : ResidueField R →+* ResidueField S :=
    IsLocalRing.ResidueField.map (algebraMap R S)
  -- First view `ResidueField S` as an integral `R`-algebra through the tower `R → S → κ(S)`.
  have hbase : (algebraMap R (ResidueField S)).IsIntegral := by
    let _ : Algebra.IsIntegral S (ResidueField S) := inferInstance
    exact algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.trans S)
  -- Then descend integrality across the quotient map `R → κ(R)`.
  have hcomp : (ρ.comp (IsLocalRing.residue R)).IsIntegral := by
    simpa [ρ, RingHom.comp_assoc, IsLocalRing.ResidueField.map_residue] using hbase
  have hρ : ρ.IsIntegral :=
    RingHom.IsIntegral.tower_top (IsLocalRing.residue R) ρ hcomp
  exact algebraMap_isIntegral_iff.mp (by simpa [ρ] using hρ)

/-- Helper for Lemma 15.107.4: the closed fiber of the chosen strict henselization over the closed
point of `A` is canonically the residue field of `Ash`. -/
private noncomputable def strictHenselization_closedFiber_ringEquiv :
    Ideal.Fiber (maximalIdeal A) Ash ≃+* ResidueField Ash :=
  (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal A) Ash ≃ₐ[A]
        Ash ⧸ Ideal.map (algebraMap A Ash) (maximalIdeal A)).toRingEquiv.trans <|
    Ideal.quotEquivOfEq IsStrictHenselizationOf.map_maximalIdeal |>.trans
      (maximalIdealQuotientResidueFieldEquiv Ash)

/-- Helper for Lemma 15.107.4: the closed fiber of the strict henselization is canonically the
residue field of `Ash` as a `κ(A)`-algebra. -/
private noncomputable def strictHenselization_closedFiber_algEquiv :
    Ideal.Fiber (maximalIdeal A) Ash ≃ₐ[κ] ResidueField Ash := by
  refine AlgEquiv.ofRingEquiv
    (f := strictHenselization_closedFiber_ringEquiv (A := A) (Ash := Ash)) ?_
  intro x
  -- Compare both `κ(A)`-scalar structures on residue classes lifted from `A`.
  obtain ⟨a, rfl⟩ := (maximalIdeal A).algebraMap_residueField_surjective x
  change
    strictHenselization_closedFiber_ringEquiv (A := A) (Ash := Ash)
        (algebraMap A (Ideal.Fiber (maximalIdeal A) Ash) a) =
      algebraMap A (ResidueField Ash) a
  simp [strictHenselization_closedFiber_ringEquiv, maximalIdealQuotientResidueFieldEquiv,
    maximalIdealResidueFieldEquiv_apply_algebraMap]

/-- Helper for Lemma 15.107.4: the closed-point residue field of the strict henselization is
separable over the residue field of the base local ring. -/
private theorem strictHenselization_closedPoint_residueField_isSeparable :
    Algebra.IsSeparable κ (ResidueField Ash) := by
  let hWeakA : Algebra.IsWeaklyEtale A Ash :=
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsStrictHenselizationOf.isFilteredColimitOfEtale
  let hWeakκ : Algebra.IsWeaklyEtale κ (Ideal.Fiber (maximalIdeal A) Ash) :=
    Algebra.IsWeaklyEtale.baseChange
      (A := A) (A' := κ) (B := Ash) hWeakA
  let hSepFiber :
      Algebra.IsSeparable κ (Ideal.Fiber (maximalIdeal A) Ash) :=
    isSeparable_of_isField_of_isWeaklyEtale_over_field
      (K := κ) (B := Ideal.Fiber (maximalIdeal A) Ash) inferInstance
  -- Transport separability across the canonical closed-fiber/residue-field algebra equivalence.
  exact AlgEquiv.Algebra.isSeparable
    (strictHenselization_closedFiber_algEquiv (A := A) (Ash := Ash)).symm

/-- Helper for Lemma 15.107.4: the residue field at a maximal point of the reduced normalization
is algebraic over the residue field of the local base ring. -/
private theorem maximal_point_residueField_isAlgebraic
    (m : MaximalSpectrum A′) :
    Algebra.IsAlgebraic κ m.asIdeal.ResidueField := by
  let f : A →+* m.asIdeal.ResidueField :=
    (maximalSpectrumToResidueField m).comp (algebraMap A A′)
  have hf_integral : f.IsIntegral := by
    let _ : Algebra A m.asIdeal.ResidueField := f.toAlgebra
    let φ : A′ →ₐ[A] m.asIdeal.ResidueField :=
      { toRingHom := maximalSpectrumToResidueField m
        commutes' := fun _ ↦ rfl }
    intro x
    rcases maximalSpectrumToResidueField_surjective (A := A) m x with ⟨z, rfl⟩
    -- Every element of `κ(m)` comes from `A'`, and `A'` is integral over `A`.
    exact IsIntegral.map φ (Algebra.IsIntegral.isIntegral z)
  have hκ_integral : (unibranchNormalizationResidueFieldMap (A := A) m).IsIntegral :=
    RingHom.IsIntegral.tower_top (IsLocalRing.residue A)
      (unibranchNormalizationResidueFieldMap (A := A) m) <| by
        -- Replace the composite through `κ(A)` by the direct map `A → κ(m)`.
        simpa [f, unibranchNormalizationResidueFieldMap_comp_residue (A := A) m] using hf_integral
  have hInt : Algebra.IsIntegral κ m.asIdeal.ResidueField := by
    rw [← algebraMap_isIntegral_iff]
    exact hκ_integral
  exact Algebra.IsIntegral.isAlgebraic

/-- Helper for Lemma 15.107.4: the closed-point residue field of the strict henselization is
algebraic over the residue field of the base local ring. -/
private theorem strictHenselization_closedPoint_residueField_isAlgebraic :
    Algebra.IsAlgebraic κ (ResidueField Ash) := by
  -- Algebraicity is the field-theoretic corollary of the stronger separability bridge above.
  exact (strictHenselization_closedPoint_residueField_isSeparable (A := A) (Ash := Ash)).isAlgebraic

/-- Helper for Lemma 15.107.4: the residue field of the chosen strict henselization is a
separable closure of `κ(A)`. -/
private theorem strictHenselization_residueField_isSepClosure :
    IsSepClosure κ (ResidueField Ash) := by
  let _ : Algebra.IsAlgebraic κ (ResidueField Ash) :=
    strictHenselization_closedPoint_residueField_isAlgebraic (A := A) (Ash := Ash)
  -- A strict henselization is strictly henselian, so its residue field is separably closed.
  infer_instance

/-- Helper for Lemma 15.107.4: the fiber of `A' ⊗[A] A^sh → A'` over a maximal point `m`
rewrites to the right-ordered tensor `κ(m) ⊗[A] A^sh`. -/
private noncomputable def maximal_point_fiber_rightOrder_algEquiv
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField ⊗[A′] A′sh) ≃ₐ[m.asIdeal.ResidueField]
      (m.asIdeal.ResidueField ⊗[A] Ash) :=
  -- TODO: first package a timeout-free owner-to-explicit-tensor identification
  -- `m.asIdeal.Fiber A′sh ≃ₐ[m.asIdeal.ResidueField] (m.asIdeal.ResidueField ⊗[A′] A′sh)`, then
  -- compose it with `fiber_tensor_base_change_rightOrderAlgEquiv`.
  sorry

/-- Helper for Lemma 15.107.4: the geometric fiber of
`A' ⊗[A] A^sh → A'` over a maximal ideal `m` is the source tensor model
`κ(m) ⊗[κ(A)] ResidueField Ash`. -/
private noncomputable def fiber_ringEquiv_residueField_tensor_strictHenselization
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField ⊗[A′] A′sh) ≃+* (m.asIdeal.ResidueField ⊗[κ] ResidueField Ash) :=
  -- TODO: use `maximalSpectrum_residueField_isScalarTower` to make the tower
  -- `A → A′ → κ(m)` explicit, then compose the two `cancelBaseChange` equivalences with
  -- `strictHenselization_closedFiber_ringEquiv`. The remaining blocker is a timeout while Lean
  -- elaborates the intermediate tensor-product instances.
  sorry

/-- Helper for Lemma 15.107.4: prime ideals of `L ⊗[κ] Ksep` are classified by `κ`-algebra
embeddings `L → Kbar` once `Ksep` is a separable closure and `Kbar` is an algebraic closure. -/
private noncomputable def primeSpectrum_tensor_sepClosure_equiv_algHom
    {L : Type u} [Field L] [Algebra κ L] [Algebra.IsAlgebraic κ L]
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    {Ksep : Type v} [Field Ksep] [Algebra κ Ksep] [IsSepClosure κ Ksep]
    (τ : Ksep →ₐ[κ] Kbar) :
    (L →ₐ[κ] Kbar) ≃ PrimeSpectrum (L ⊗[κ] Ksep) :=
  sorry

/-- Helper for Lemma 15.107.4: after specializing the tensor-prime classification to the residue
field of a maximal point `m`, embeddings `κ(m) → Kbar` classify primes of the source tensor model
`κ(m) ⊗[κ(A)] ResidueField Ash`. -/
private noncomputable def algHomEquiv_primeSpectrum_residueField_tensor_strictHenselization
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar)
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField →ₐ[κ] Kbar) ≃
      PrimeSpectrum (m.asIdeal.ResidueField ⊗[κ] ResidueField Ash) :=
  by
    let _ : Algebra.IsAlgebraic κ m.asIdeal.ResidueField :=
      maximal_point_residueField_isAlgebraic (A := A) m
    let _ : IsSepClosure κ (ResidueField Ash) :=
      strictHenselization_residueField_isSepClosure (A := A) (Ash := Ash)
    -- Specialize the tensor-prime classifier to `L = κ(m)` and `Ksep = ResidueField Ash`.
    exact
      primeSpectrum_tensor_sepClosure_equiv_algHom
        (L := m.asIdeal.ResidueField) (Kbar := Kbar) (Ksep := ResidueField Ash) τ

/-- The canonical fiber point attached to a `κ`-algebra embedding
`κ(m') = Ideal.ResidueField m.asIdeal → Kbar`. -/
noncomputable def fiberPrimeOfAlgHom
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar)
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField →ₐ[κ] Kbar) → PrimeSpectrum (m.asIdeal.Fiber A′sh) :=
  -- TODO: after the split fiber rewrite is stabilized, define this by classifying primes of the
  -- tensor model and transporting them back across `fiber_ringEquiv_residueField_tensor_strictHenselization`.
  sorry

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch normalization, strict henselization, and
  fibers of the spectral map after tensor-product base change;
- sampled owner declarations of the same kind:
  `unibranchNormalization`,
  `IsStrictHenselizationOf`,
  `fiberPrimeAt`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `Ideal.Fiber`;
- best owner abstraction: the source-facing ring is `A′ = unibranchNormalization A`, and the
  canonical bridge from the spectral fiber over a prime to a ring object is the fiber ring
  `m.Fiber A′sh`, whose spectrum is identified upstream by `PrimeSpectrum.preimageHomeomorphFiber`
  and whose distinguished points over primes of `A′sh` are owned by `fiberPrimeAt`;
- primitive data: the local ring `A`, its chosen strict henselization `Ash`, the normalization
  owner `A′`, and a maximal point `m : MaximalSpectrum A′`;
- derived API: the residue-field algebraicity statement, the fiber-point counting statement over
  `m`, and the minimal/maximal-prime comparison statements on `A′sh`.

Source/core/bridge triage:
- `source-facing`: the five clauses of Lemma 15.107.4;
- `core/canonical`: `unibranchNormalization`, `IsStrictHenselizationOf`, `Ideal.Fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`, `minimalPrimes`, `Ideal.comap`;
- `bridge/view`: the tensor-product base change `A′sh = A′ ⊗[A] Ash`.
-/

-- Proof sketch: the map `A → A'` is integral, so the induced extension of residue fields at a
-- maximal ideal `m' ⊂ A'` is algebraic over the residue field of the contracted maximal ideal of
-- `A`; locality of `A → A'` identifies this contracted maximal ideal with `maximalIdeal A`.
/-- Lemma 15.107.4 (1): for a maximal ideal `m' ⊂ A'`, the residue field
`κ(m') = Ideal.ResidueField m'.asIdeal` is algebraic over `κ = A / maximalIdeal A`. -/
@[stacks 0C25]
theorem unibranchNormalization_residueField_isAlgebraic
    (m : MaximalSpectrum A′) :
    Algebra.IsAlgebraic κ m.asIdeal.ResidueField := by
  -- Reuse the earlier closed-point algebraicity helper so the clause-(2) classifier stays
  -- dependency-closed without depending on this later theorem declaration.
  exact maximal_point_residueField_isAlgebraic (A := A) m

-- Proof sketch: `PrimeSpectrum.preimageHomeomorphFiber` identifies primes of the fiber ring
-- `m'.Fiber A′sh` with primes of `A′sh` lying over `m'`. Choosing a compatible `κ`-algebra map
-- `ResidueField Ash →ₐ[κ] Kbar` turns a
-- `κ`-algebra embedding `κ(m') → Kbar` into a unique fiber point, and every fiber point arises
-- uniquely in this way.
/-- Lemma 15.107.4 (2): let `m' ⊂ A'` be maximal, let `Kbar` be an algebraic closure of `κ`, and
choose a compatible `κ`-algebra map `ResidueField Ash →ₐ[κ] Kbar`. Then fiber points of
`m'.Fiber A′sh = κ(m') ⊗[A'] (A' ⊗[A] Ash)` are canonically in bijection with `κ`-algebra
embeddings `κ(m') → Kbar`. -/
@[stacks 0C25]
theorem fiberPrimeOfAlgHom_bijective
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar)
    (m : MaximalSpectrum A′) :
    Function.Bijective (fiberPrimeOfAlgHom τ m) := by
  -- TODO: once `fiberPrimeOfAlgHom` is defined via the stabilized fiber/tensor transport, its
  -- bijectivity is the composition of the tensor-prime classifier with the prime-spectrum
  -- bijection induced by the fiber ring equivalence.
  sorry

/-- Equivalence form of Lemma 15.107.4 (2). -/
noncomputable def fiberPrimeOfAlgHomEquiv
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar)
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField →ₐ[κ] Kbar) ≃ PrimeSpectrum (m.asIdeal.Fiber A′sh) :=
  -- TODO: package the bijective fiber-point classifier as an equivalence once the fiber transport
  -- above is in place.
  sorry

-- Proof sketch: compare minimal primes of `A′sh` and `Ash` by tensoring with the total ring
-- of fractions of `Ared`; as in the henselization case, both spectra identify with the minimal
-- primes lying over the minimal primes of `A`, and the tensor-factor `A′` does not change the
-- generic fiber.
/-- Lemma 15.107.4 (3): the map `Spec(A′sh) → Spec(Ash)` induced by the right tensor-factor map
`Ash → A′sh` is bijective on minimal primes. -/
@[stacks 0C25]
theorem unibranchNormalizationTensorStrictHenselization_bijOn_minimalPrimes
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn
      (Ideal.comap ((includeRight : Ash →ₐ[A] A′sh).toRingHom))
      (minimalPrimes A′sh)
      (minimalPrimes Ash) := by
  -- TODO: follow the generic-fiber comparison over the total fraction ring of `(A)_red` and show
  -- that minimal primes on both sides are exactly the primes lying over minimal primes of `A`.
  sorry

-- Proof sketch: normality of `A′sh` gives that each localization at a maximal ideal is a
-- domain, while the henselian-pair connectivity argument for the closed fiber shows that the
-- closed subset defined by a minimal prime meets the closed fiber in exactly one point.
/-- Lemma 15.107.4 (4): every minimal prime of `(A')^sh = A' ⊗[A] A^sh` is contained in a unique
maximal ideal. -/
@[stacks 0C25]
theorem unibranchNormalizationTensorStrictHenselization_minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal A′sh} (hp : p ∈ minimalPrimes A′sh) :
    ∃! m : Ideal A′sh, m.IsMaximal ∧ p ≤ m := by
  -- TODO: combine normality of `A′sh` with the henselian-pair connectedness argument on the
  -- closed fiber to force the closed subset `V(p)` to meet the closed fiber in exactly one point.
  sorry

-- Proof sketch: after clause `(4)`, each minimal prime determines a unique maximal ideal. Since
-- the localizations of `A′sh` at maximal ideals are normal domains, a maximal ideal cannot
-- contain two distinct minimal primes.
/-- Lemma 15.107.4 (5): every maximal ideal of `(A')^sh = A' ⊗[A] A^sh` contains a unique minimal
prime. -/
@[stacks 0C25]
theorem unibranchNormalizationTensorStrictHenselization_maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal A′sh} (hm : m.IsMaximal) :
    ∃! p : Ideal A′sh, p ∈ minimalPrimes A′sh ∧ p ≤ m := by
  -- TODO: localize at `m`, use the expected normal-domain structure on the localization to get a
  -- unique minimal prime there, and transport that uniqueness back to `A′sh`.
  sorry

end StrictHenselization
