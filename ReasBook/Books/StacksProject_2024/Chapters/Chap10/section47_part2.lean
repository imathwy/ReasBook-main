import Mathlib
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_47_10 (from Chap10) -/
open AlgebraicGeometry CommRingCat
open scoped RatFunc TensorProduct

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.47.10: irreducibility of `Spec R` is equivalent to the existence of a
unique minimal prime ideal of `R`. -/
private theorem irreducibleSpace_primeSpectrum_iff_existsUnique_minimalPrime
    {R : Type u} [CommRing R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ ∃! p : Ideal R, p ∈ minimalPrimes R := by
  constructor
  · intro hR
    -- Proof comment: in an irreducible prime spectrum, the nilradical is prime, so it is the
    -- unique minimal prime.
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
    letI : (nilradical R).IsPrime := hR
    have hminimal : minimalPrimes R = {nilradical R} := by
      simpa [minimalPrimes, nilradical] using
        (show (nilradical R).minimalPrimes = {nilradical R} from
          Ideal.minimalPrimes_eq_subsingleton_self)
    refine ⟨nilradical R, ?_, ?_⟩
    · rw [hminimal]
      simp
    · intro q hq
      rw [hminimal] at hq
      simpa using hq
  · rintro ⟨p, hp, hp_unique⟩
    -- Proof comment: a unique minimal prime forces the nilradical to equal that prime ideal.
    have hminimal : minimalPrimes R = {p} := by
      ext q
      constructor
      · intro hq
        simpa using hp_unique q hq
      · rintro rfl
        exact hp
    have hsInf : sInf (minimalPrimes R) = nilradical R := by
      rw [minimalPrimes, nilradical]
      exact Ideal.sInf_minimalPrimes
    have hnil : nilradical R = p := by
      rw [← hsInf, hminimal]
      simp
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    simpa [hnil] using Ideal.minimalPrimes_isPrime hp

/-- Helper for Lemma 10.47.10: irreducibility of prime spectra descends along injective ring
homomorphisms. -/
private theorem irreducibleSpace_primeSpectrum_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum S) → IrreducibleSpace (PrimeSpectrum R) := by
  intro hS
  -- Proof comment: compare nilradicals through the injective map and pull primality back.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS ⊢
  letI : (nilradical S).IsPrime := hS
  have hcomap : Ideal.comap f (nilradical S) = nilradical R := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical S)

/-- Helper for Lemma 10.47.10: localizing away from an element preserves irreducibility of prime
spectra as soon as the localized ring is nontrivial. -/
private theorem irreducibleSpace_primeSpectrum_localizationAway
    {R : Type u} [CommRing R] (r : R) [Nontrivial (Localization.Away r)]
    (hR : IrreducibleSpace (PrimeSpectrum R)) :
    IrreducibleSpace (PrimeSpectrum (Localization.Away r)) := by
  let f : PrimeSpectrum (Localization.Away r) → PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away r))
  let hf : Topology.IsOpenEmbedding f :=
    PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away r) r
  have hrange : Set.range f = PrimeSpectrum.basicOpen r := by
    simpa [f] using
      (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)
  have hbasic_nonempty : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum (Localization.Away r)))
    refine ⟨f x, ?_⟩
    rw [← hrange]
    exact Set.mem_range_self x
  have hbasic_preirreducible : IsPreirreducible (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    -- Proof comment: any nonempty open subset of an irreducible space is preirreducible.
    letI : IrreducibleSpace (PrimeSpectrum R) := hR
    have huniv : IsIrreducible (Set.univ : Set (PrimeSpectrum R)) :=
      IrreducibleSpace.isIrreducible_univ (PrimeSpectrum R)
    simpa using huniv.2.open_subset (PrimeSpectrum.basicOpen r).2 (by intro x _; trivial)
  have hrange_irreducible : IsIrreducible (Set.range f) := by
    rw [hrange]
    exact ⟨hbasic_nonempty, hbasic_preirreducible⟩
  let e : PrimeSpectrum (Localization.Away r) ≃ₜ Set.range f :=
    (Homeomorph.Set.univ _).symm.trans <|
      (Homeomorph.setCongr (by ext x; simp [f])).trans <|
        hf.toIsEmbedding.homeomorphOfSubsetRange (by intro x hx; exact hx)
  exact (e.irreducibleSpace_iff).2 (Subtype.irreducibleSpace hrange_irreducible)

/-- Helper for Lemma 10.47.10: the one-variable polynomial ring over `K` is the tensor product
`K ⊗[k] k[X]`. -/
noncomputable def one_variable_polynomial_tensor_ringEquiv :
    K ⊗[k] Polynomial k ≃+* Polynomial K :=
  let e₁ : K ⊗[k] Polynomial k ≃ₐ[k] K ⊗[k] MvPolynomial PUnit.{1} k :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[k] K)
      (MvPolynomial.pUnitAlgEquiv.{u, 0} k).symm).restrictScalars k
  let e₂ : K ⊗[k] MvPolynomial PUnit.{1} k ≃ₐ[k] MvPolynomial PUnit.{1} K :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := PUnit.{1}) k K).restrictScalars k
  let e₃ : MvPolynomial PUnit.{1} K ≃ₐ[k] Polynomial K :=
    (MvPolynomial.pUnitAlgEquiv.{u, 0} K).restrictScalars k
  ((e₁.trans e₂).trans e₃).toRingEquiv

/-- Helper for Lemma 10.47.10: for any compatible `k`- and `k[X]`-algebra structure on `Ω`,
the polynomial pushout square cancels the `k[X]`-base change. -/
private noncomputable def polynomial_baseChange_ringEquiv_over_ratFuncBase
    {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower k (Polynomial k) Ω] :
    Polynomial K ⊗[Polynomial k] Ω ≃+* K ⊗[k] Ω := by
  -- Proof comment: `Polynomial K` is the pushout of `k → K` and `k → k[X]`, so
  -- `cancelBaseChangeAlg` rewrites the polynomial tensor directly as the field tensor.
  exact (Algebra.IsPushout.cancelBaseChangeAlg k K (Polynomial k) (Polynomial K) Ω).toRingEquiv

-- Proof sketch: for the forward implication, identify `K(t)` with the localization of
-- `K ⊗[k] k(t)` at the nonzero polynomials and use stability of irreducibility under
-- localization. For the reverse implication, for any field extension `k' / k`, compare
-- `K ⊗[k] k'` with its localization `K(t) ⊗[k(t)] k'(t)`; injectivity together with the
-- minimal-prime comparison lemmas recovers irreducibility before localization.
/-- Lemma 10.47.10: a field extension `K / k` is geometrically irreducible if and only if the
induced extension on one-variable rational function fields `K(t) / k(t)` is geometrically
irreducible. -/
@[stacks 0G31]
theorem isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) := by
  -- TODO: finish the source-faithful comparison by packaging the remaining localization and
  -- reverse injectivity steps.
  -- The polynomial pushout bridge is now isolated in
  -- `polynomial_baseChange_ringEquiv_over_ratFuncBase`; what remains is:
  -- 1. transport irreducibility through the non-away localization from
  --    `Polynomial K ⊗[Polynomial k] Ω` to `K⟮X⟯ ⊗[Polynomial k] Ω`, and then across the
  --    localization-base-change equivalence to `K⟮X⟯ ⊗[k⟮X⟯] Ω`;
  -- 2. construct the omitted injective comparison
  --    `K ⊗[k] k' → K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯`.
  sorry

/-- Compatibility alias for the rational-function-field criterion for geometric irreducibility. -/
abbrev Lemma_10_47_10 :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) :=
  isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible

end

end Algebra

/-! ### Lemma_10_47_11 (from Chap10) -/
open AlgebraicGeometry CommRingCat
open CategoryTheory MorphismProperty
open scoped RatFunc

namespace Algebra

open IntermediateField

noncomputable section

universe u

section

variable {M L K : Type u}
variable [Field M] [Field L] [Field K]
variable [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]

attribute [local instance] Polynomial.algebra

private theorem adjoinSimple_restrictScalars_le (x : K) :
    M⟮x⟯ ≤ (L⟮x⟯).restrictScalars M := by
  rw [adjoin_simple_le_iff]
  exact mem_adjoin_simple_self L x

noncomputable instance adjoinSimpleAlgebra (x : K) : Algebra M⟮x⟯ L⟮x⟯ :=
  (IntermediateField.inclusion (adjoinSimple_restrictScalars_le x)).toAlgebra

variable [GeometricallyIrreducible (Spec.map (ofHom (algebraMap M L)))]

-- Proof sketch: use `RatFunc.algEquivOfTranscendental` to identify `M(x)` and `L(x)` with the
-- one-variable rational function fields over `M` and `L`, transport geometric irreducibility
-- across those algebra equivalences, and then apply Lemma 10.47.10 to `L / M`.
/-- Lemma 10.47.11 (Tag `0G32`): let `K/L/M` be a tower of fields with `L / M` geometrically
irreducible. If `x ∈ K` is transcendental over `L`, then `L(x) / M(x)` is geometrically
irreducible. -/
@[stacks 0G32]
theorem Lemma_10_47_11 (x : K)
    (hx : Transcendental L x) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap M⟮x⟯ L⟮x⟯))) := by
  letI : IsScalarTower M M⟮x⟯ L⟮x⟯ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let xMap : M⟮x⟯ →ₐ[M] L⟮x⟯ := IsScalarTower.toAlgHom M M⟮x⟯ L⟮x⟯
  let hxM : Transcendental M x := Transcendental.of_tower_top M hx
  let eM : M⟮X⟯ ≃ₐ[M] M⟮x⟯ := RatFunc.algEquivOfTranscendental x hxM
  let eL : L⟮X⟯ ≃ₐ[M] L⟮x⟯ := (RatFunc.algEquivOfTranscendental x hx).restrictScalars M
  let eMhom : M⟮X⟯ →ₐ[M] M⟮x⟯ := eM.toAlgHom
  let eLinv : L⟮x⟯ →ₐ[M] L⟮X⟯ := eL.symm.toAlgHom
  let XMap : M⟮X⟯ →ₐ[M] L⟮X⟯ := IsScalarTower.toAlgHom M M⟮X⟯ L⟮X⟯
  let eMComm : of M⟮X⟯ ≅ of M⟮x⟯ := eM.toRingEquiv.toCommRingCatIso
  let eLComm : of L⟮X⟯ ≅ of L⟮x⟯ := eL.toRingEquiv.toCommRingCatIso
  let iM : Spec (of M⟮x⟯) ≅ Spec (of M⟮X⟯) :=
    Scheme.Spec.mapIso eMComm.op
  let iL : Spec (of L⟮x⟯) ≅ Spec (of L⟮X⟯) :=
    Scheme.Spec.mapIso eLComm.op
  have hX : GeometricallyIrreducible (Spec.map (ofHom (algebraMap M⟮X⟯ L⟮X⟯))) :=
    Lemma_10_47_10.mp
      (inferInstance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap M L))))
  have hcomp_alg :
      (eLinv.comp (xMap.comp eMhom) : M⟮X⟯ →ₐ[M] L⟮X⟯) = XMap := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial M))
    apply Polynomial.algHom_ext
    change eL.symm (xMap (eM RatFunc.X)) = XMap RatFunc.X
    have heM : eM RatFunc.X = AdjoinSimple.gen M x := by
      ext
      simp [eM]
    have heL : eL.symm (AdjoinSimple.gen L x) = RatFunc.X := by
      simp [eL]
    rw [heM]
    change eL.symm (AdjoinSimple.gen L x) = XMap RatFunc.X
    rw [heL]
    symm
    rw [← RatFunc.algebraMap_X]
    change (IsFractionRing.lift (FaithfulSMul.algebraMap_injective (Polynomial M) L⟮X⟯))
        RatFunc.X = RatFunc.X
    rw [← RatFunc.algebraMap_X]
    have hpolyX : (algebraMap (Polynomial M) L⟮X⟯) Polynomial.X = RatFunc.X := by
      change
        (algebraMap (Polynomial L) L⟮X⟯)
            ((Polynomial.mapRingHom (algebraMap M L)) Polynomial.X) = RatFunc.X
      rw [show (Polynomial.mapRingHom (algebraMap M L)) Polynomial.X = Polynomial.X by simp]
      rw [RatFunc.algebraMap_X]
    simpa [hpolyX] using IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective (Polynomial M) L⟮X⟯) Polynomial.X
  have hcomp_cat :
      (ofHom eMhom.toRingHom ≫ ofHom xMap.toRingHom ≫
          ofHom eLinv.toRingHom : of M⟮X⟯ ⟶ of L⟮X⟯) =
        ofHom (algebraMap M⟮X⟯ L⟮X⟯) := by
    ext g
    simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgEquiv.toRingEquiv_toRingHom, xMap,
      XMap] using
      congrArg (fun f : M⟮X⟯ →ₐ[M] L⟮X⟯ ↦ f g) hcomp_alg
  have hcomp_spec :
      Spec.map (ofHom eLinv.toRingHom) ≫
        Spec.map (ofHom xMap.toRingHom) ≫
        Spec.map (ofHom eMhom.toRingHom) =
      Spec.map (ofHom (algebraMap M⟮X⟯ L⟮X⟯)) := by
    simpa [← Spec.map_comp, Category.assoc] using
      congrArg
        (fun f : of M⟮X⟯ ⟶ of L⟮X⟯ ↦ Spec.map f)
        hcomp_cat
  have htransport :
      GeometricallyIrreducible
        (Spec.map (ofHom eLinv.toRingHom) ≫
          Spec.map (ofHom xMap.toRingHom) ≫
          Spec.map (ofHom eMhom.toRingHom)) := by
    rw [hcomp_spec]
    exact hX
  have hmid :
      GeometricallyIrreducible
        (Spec.map (ofHom xMap.toRingHom) ≫ Spec.map (ofHom eMhom.toRingHom)) := by
    refine (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyIrreducible : MorphismProperty Scheme) iL.symm.hom _).mp ?_
    simpa [iL, eL, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_inv,
      AlgEquiv.toRingEquiv_toRingHom, Category.assoc] using htransport
  have hGI : GeometricallyIrreducible (Spec.map (ofHom xMap.toRingHom)) := by
    refine (MorphismProperty.cancel_right_of_respectsIso
      (@GeometricallyIrreducible : MorphismProperty Scheme) _ iM.hom).mp ?_
    simpa [iM, eM, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom,
      AlgEquiv.toRingEquiv_toRingHom, Category.assoc] using hmid
  simpa [xMap] using hGI

end

end

end Algebra

/-! ### Lemma_10_47_12 (from Chap10) -/
open AlgebraicGeometry CommRingCat IntermediateField

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

-- Proof sketch: for the forward implication, if `α` is separable over `k`, then the simple
-- extension `k⟮α⟯ / k` is a finite separable subextension of `K`; geometric irreducibility forces
-- this subextension to be trivial, so `α` lies in `k`. For the converse, the hypothesis says the
-- algebraic closure of `k` inside `K` is purely inseparable over `k`; combine Lemma `10.47.8`
-- with the geometric irreducibility of purely inseparable extensions and then apply transitivity
-- from Lemma `10.47.9`.
/-- Lemma 10.47.12: a field extension `K / k` is geometrically irreducible exactly when its
relative separable closure in `K` is trivial. -/
theorem isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      separableClosure k K = ⊥ := sorry

/-- Lemma 10.47.12, source form: a field extension `K / k` is geometrically irreducible exactly
when every separable element of `K` already lies in the base field `k`. -/
theorem isGeometricallyIrreducibleOver_iff_forall_separable_mem_bot :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      ∀ α : K, IsSeparable k α → α ∈ (⊥ : IntermediateField k K) := by
  refine isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot.trans ?_
  constructor
  · intro h α hα
    simpa [h] using (mem_separableClosure_iff.2 hα : α ∈ separableClosure k K)
  · intro h
    exact bot_unique fun α hα ↦ h α (mem_separableClosure_iff.1 hα)

end

end Algebra

/-! ### Lemma_10_47_13 (from Chap10) -/
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

-- Proof sketch: apply Lemma `10.47.12` with base field `separableClosure k K`; the required
-- triviality of the relative separable closure is exactly `separableClosure.separableClosure_eq_bot`.
/-- Lemma 10.47.13: if `k' = separableClosure k K` is the subextension of elements separably
algebraic over `k`, then `K` is geometrically irreducible over `k'`. -/
@[instance]
theorem isGeometricallyIrreducibleOver_separableClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap (separableClosure k K) K))) := by
  simpa [isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot] using
    separableClosure.separableClosure_eq_bot k K

-- Proof sketch: Lemma `9.26.11` makes the relative algebraic closure `algebraicClosure k K`
-- finite-dimensional over `k`; the relative separable closure is an intermediate field of that
-- algebraic closure, so it is finite-dimensional as well.
/-- If `K / k` is a finitely generated field extension, then the relative separable closure of `k`
in `K` has finite degree over `k`. -/
theorem finiteDimensional_separableClosure_of_essFiniteType [Algebra.EssFiniteType k K] :
    FiniteDimensional k (separableClosure k K) := by
  letI : FiniteDimensional k (algebraicClosure k K) :=
    finiteDimensional_algebraicClosure k K
  letI : Algebra (separableClosure k K) (algebraicClosure k K) :=
    (IntermediateField.inclusion (le_algebraicClosure k K (separableClosure k K))).toAlgebra
  exact FiniteDimensional.left k (separableClosure k K) (algebraicClosure k K)

end

end Algebra

/-! ### Lemma_10_47_14 (from Chap10) -/
open scoped Pointwise TensorProduct

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

local notation "TensorRing" => SeparableClosure k ⊗[k] K
local notation "SpecTensor" => PrimeSpectrum TensorRing

/-- The Galois group acts on `SeparableClosure k ⊗[k] K` through the canonical automorphisms of
the left tensor factor. This ring automorphism is the owner abstraction from which the spectrum
action is derived. -/
private noncomputable def tensorLeftGaloisAut :
    Gal(SeparableClosure k / k) →* TensorRing ≃ₐ[k] TensorRing where
  toFun σ := Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)
  map_one' := by
    change Algebra.TensorProduct.congr
        (AlgEquiv.refl : SeparableClosure k ≃ₐ[k] SeparableClosure k)
        (AlgEquiv.refl : K ≃ₐ[k] K) = AlgEquiv.refl
    simp
  map_mul' σ τ := by
    change Algebra.TensorProduct.congr
        ((τ : SeparableClosure k ≃ₐ[k] SeparableClosure k).trans σ)
        ((AlgEquiv.refl : K ≃ₐ[k] K).trans (AlgEquiv.refl : K ≃ₐ[k] K)) =
      (Algebra.TensorProduct.congr τ (AlgEquiv.refl : K ≃ₐ[k] K)).trans
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K))
    simpa using
      (Algebra.TensorProduct.congr_trans
        τ σ (AlgEquiv.refl : K ≃ₐ[k] K) (AlgEquiv.refl : K ≃ₐ[k] K))

local notation "tensorAut" =>
  (tensorLeftGaloisAut :
    Gal(SeparableClosure k / k) →*
      (SeparableClosure k ⊗[k] K) ≃ₐ[k] (SeparableClosure k ⊗[k] K))

noncomputable local instance tensorLeftGaloisMulSemiringAction :
    MulSemiringAction (Gal(SeparableClosure k / k)) TensorRing :=
  MulSemiringAction.compHom (SeparableClosure k ⊗[k] K) tensorAut

noncomputable local instance :
    SMul (Gal(SeparableClosure k / k)) SpecTensor where
  smul σ := PrimeSpectrum.comap ((tensorAut σ).symm.toRingHom)

noncomputable local instance :
    MulAction (Gal(SeparableClosure k / k)) SpecTensor where
  one_smul p := by
    change PrimeSpectrum.comap ((tensorAut 1).symm.toRingHom) p = p
    rw [show tensorAut 1 = 1 by exact map_one tensorAut]
    rfl
  mul_smul σ τ p := by
    change PrimeSpectrum.comap ((tensorAut (σ * τ)).symm.toRingHom) p =
      PrimeSpectrum.comap ((tensorAut σ).symm.toRingHom)
        (PrimeSpectrum.comap ((tensorAut τ).symm.toRingHom) p)
    rw [show tensorAut (σ * τ) = tensorAut σ * tensorAut τ by
      exact map_mul tensorAut σ τ]
    rfl

/-- The Galois action on `Spec(SeparableClosure k ⊗[k] K)` is induced by the inverse tensor
automorphism acting on the left tensor factor. -/
theorem galoisTensorPrimeSpectrum_smul_def (σ : Gal(SeparableClosure k / k))
    (p : SpecTensor) :
    σ • p =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)).symm.toRingHom p :=
  rfl

-- Proof sketch: first replace `K` by the relative separable closure `separableClosure k K` using
-- Lemmas `10.47.13` and `10.47.7`, which identifies the two prime spectra. For the separable
-- extension, primes of `SeparableClosure k ⊗[k] separableClosure k K` correspond to `k`-embeddings
-- `separableClosure k K → SeparableClosure k`, and `Gal(SeparableClosure k / k)` acts transitively
-- on those embeddings by postcomposition.
/-- Lemma 10.47.14: the Galois group of the separable closure acts transitively on the prime
spectrum of `SeparableClosure k ⊗[k] K`. Equivalently, any two primes are conjugate under the
canonical action induced from the left tensor factor. -/
@[instance]
theorem galoisTensorPrimeSpectrum_transitive :
    MulAction.IsPretransitive (Gal(SeparableClosure k / k)) SpecTensor := by
  sorry

/-- Textbook unpacking of Lemma 10.47.14: any two primes are conjugate under the canonical
Galois action. -/
theorem galoisTensorPrimeSpectrum_exists_smul_eq (p q : SpecTensor) :
    ∃ σ : Gal(SeparableClosure k / k), σ • p = q :=
  MulAction.exists_smul_eq (Gal(SeparableClosure k / k)) p q

end
