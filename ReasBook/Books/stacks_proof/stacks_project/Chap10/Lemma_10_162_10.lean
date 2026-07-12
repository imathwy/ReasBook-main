import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1
import StacksProject_2024.Chap10.Definition_10_162_9
import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap10.Lemma_10_40_4
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_97_5
import StacksProject_2024.Chap10.Lemma_10_97_7
import StacksProject_2024.Chap10.Lemma_10_162_2
import StacksProject_2024.Chap10.Lemma_10_162_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped TensorProduct

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local rings, their minimal-prime quotients,
  and the finite normalization (`N-1`) consequence;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `IsN1Ring`,
  and the canonical minimal-prime index type `minimalPrimes R`;
- best owner abstraction: the ambient owner is `IsAnalyticallyUnramified R`, while minimal-prime
  inputs should use the canonical `minimalPrimes R` owner rather than a separate prime-spectrum
  point together with a membership proof;
- primitive data vs. derived API: the primitive source data are the ring `R`, the owner
  hypothesis `[IsAnalyticallyUnramified R]`, and the minimal-prime family. Reducedness of `R`,
  analytic unramifiedness of each minimal-prime quotient, and the `N-1` finiteness statement are
  derived theorem-level API and should not be repackaged as extra structures.
-/

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

local instance (p : minimalPrimes R) : IsLocalRing (R ⧸ p.1) :=
  primeSpectrum_quotient_isLocalRing ⟨p.1, inferInstance⟩

local instance (p : minimalPrimes R) : IsNoetherianRing (R ⧸ p.1) :=
  inferInstance

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

/-- Helper for Chap10 Lemma 10 162 10: the completion of a minimal-prime quotient carries the
canonical commutative ring structure. -/
noncomputable local instance (p : minimalPrimes R) :
    CommRing (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)) :=
  AdicCompletion.instCommRing (I := maximalIdeal (R ⧸ p.1))

/-- Helper for Chap10 Lemma 10 162 10: the completed minimal-prime quotient is an algebra over
the quotient ring. -/
noncomputable local instance (p : minimalPrimes R) :
    Algebra (R ⧸ p.1) (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)) :=
  AdicCompletion.instAlgebra (I := maximalIdeal (R ⧸ p.1))

/-- Helper for Chap10 Lemma 10 162 10: quotienting `RCompletion` by the extension of a minimal
prime is the same as tensoring `RCompletion` with the corresponding prime quotient. -/
private noncomputable def minimalPrime_completionQuotient_tensorQuotient_algEquiv
    (p : minimalPrimes R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) ≃ₐ[RCompletion]
      (RCompletion ⊗[R] (R ⧸ p.1)) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) (B := RCompletion) p.1

/-- Helper for Chap10 Lemma 10 162 10: the tensor model of the completed minimal-prime quotient
is the `maximalIdeal R`-adic module completion of `R ⧸ p`. -/
private noncomputable def minimalPrime_tensor_moduleCompletion_linearEquiv
    (p : minimalPrimes R) :
    (RCompletion ⊗[R] (R ⧸ p.1)) ≃ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.1) :=
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := maximalIdeal R)
    (M := R ⧸ p.1)

/-- Helper for Chap10 Lemma 10 162 10: the quotient `RCompletion ⧸ pRCompletion` matches the
`maximalIdeal R`-adic module completion of the minimal-prime quotient. -/
private noncomputable def minimalPrime_completionQuotient_moduleCompletion_linearEquiv
    (p : minimalPrimes R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) ≃ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.1) :=
  (minimalPrime_completionQuotient_tensorQuotient_algEquiv R p).toLinearEquiv.trans
    (minimalPrime_tensor_moduleCompletion_linearEquiv R p)

/-- Helper for Chap10 Lemma 10 162 10: on quotient representatives, the quotient-completion
comparison sends a class from `RCompletion` to the expected scalar multiple of the completed
class of `1`. -/
private lemma minimalPrime_completionQuotient_moduleCompletion_linearEquiv_mk
    (p : minimalPrimes R) (b : RCompletion) :
    minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b) =
      b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.1) 1 := by
  -- Proof comment: evaluate the two-step quotient/tensor/completion bridge on a representative.
  rw [minimalPrime_completionQuotient_moduleCompletion_linearEquiv, LinearEquiv.trans_apply]
  change
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) (R ⧸ p.1)
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot RCompletion p.1)
          (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b)) =
      b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.1) 1
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul]

/-- Helper for Chap10 Lemma 10 162 10: the quotient-completion comparison is injective. -/
private lemma minimalPrime_completionQuotient_moduleCompletion_injective
    (p : minimalPrimes R) :
    Function.Injective (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p) := by
  -- Proof comment: the comparison map is a linear equivalence, hence injective.
  exact (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p).injective

/-- Helper for Chap10 Lemma 10 162 10: the canonical map from a Noetherian local ring to its
maximal-ideal adic completion is injective. -/
private lemma maximalIdealAdicCompletion_algebraMap_injective :
    Function.Injective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  -- Proof comment: rewrite the algebra map as the canonical completion map, whose injectivity is
  -- exactly Hausdorffness of the maximal-adic topology on a Noetherian local ring.
  intro x y hxy
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at hxy
  exact AdicCompletion.of_injective (maximalIdeal R) R hxy

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 162 10: every minimal prime of a Noetherian ring is the annihilator
`Ideal.torsionOf R R f` of some element `f : R`. -/
private lemma minimalPrime_eq_torsionOf_self (p : minimalPrimes R) :
    ∃ f : R, p.1 = Ideal.torsionOf R R f := by
  -- Proof comment: view a minimal prime over `⊥ = Module.annihilator R R` as an associated
  -- prime, then use the project bridge from associated primes to exact annihilators.
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have hpmin : p.1 ∈ (Module.annihilator R R).minimalPrimes := by
    simp [hann, minimalPrimes]
  have hpAssociated : p.1 ∈ associatedPrimes R R :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (R := R) (M := R) hpmin
  have hpAssociatedModule : Ideal.IsAssociatedToModule R R p.1 :=
    (Ideal.isAssociatedToModule_iff_isAssociatedPrime R R p.1).2 hpAssociated
  rcases hpAssociatedModule with ⟨_, f, hf⟩
  exact ⟨f, hf⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: flat base change carries the annihilator
`Ideal.torsionOf R R f` to the annihilator of `algebraMap R S f`. -/
private lemma map_torsionOf_self_eq_torsionOf_algebraMap_of_flat
    {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S] (f : R) :
    Ideal.map (algebraMap R S) (Ideal.torsionOf R R f) =
      Ideal.torsionOf S S (algebraMap R S f) := by
  let e : (S ⊗[R] R) ≃ₗ[S] S :=
    (Algebra.TensorProduct.rid R S S).toLinearEquiv
  have htarget :
      Ideal.torsionOf S (S ⊗[R] R) ((1 : S) ⊗ₜ[R] f) =
        Ideal.torsionOf S S (algebraMap R S f) := by
    -- Proof comment: identify the base-changed cyclic generator with `algebraMap R S f` through
    -- the right tensor unitor.
    ext x
    rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    constructor
    · intro hx
      have h := congrArg e hx
      simpa [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm, mul_left_comm,
        mul_assoc] using h
    · intro hx
      apply e.injective
      rw [map_smul, map_zero]
      simpa [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm, mul_left_comm,
        mul_assoc] using hx
  -- Proof comment: combine the existing flat base-change theorem with the tensor-unitor
  -- normalization above.
  exact
    (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
      (S := S) (M := R) f).trans htarget

/-- Helper for Chap10 Lemma 10 162 10: in a reduced ring, the annihilator of one element is a
radical ideal. -/
private lemma torsionOf_self_isRadical_of_isReduced
    {S : Type u} [CommRing S] [IsReduced S] (f : S) :
    (Ideal.torsionOf S S f).IsRadical := by
  -- Proof comment: square membership in the annihilator makes `(x * f) ^ 2` vanish, so reducedness
  -- forces `x * f = 0`.
  rw [Ideal.isRadical_iff_pow_one_lt 2 one_lt_two]
  intro x hx
  rw [Ideal.mem_torsionOf_iff] at hx ⊢
  have hxmul : x ^ 2 * f = 0 := by
    simpa [smul_eq_mul] using hx
  have hnil : (x * f) ^ 2 = 0 := by
    calc
      (x * f) ^ 2 = f * (x ^ 2 * f) := by ring
      _ = 0 := by rw [hxmul, mul_zero]
  have hzero : x * f = 0 := IsReduced.eq_zero _ ⟨2, hnil⟩
  simpa [smul_eq_mul, mul_comm] using hzero

/-- Helper for Chap10 Lemma 10 162 10: after analytically unramified completion, the extension of
a minimal prime to `RCompletion` is radical. -/
private lemma minimalPrimeMapCompletion_isRadical [IsAnalyticallyUnramified R]
    (p : minimalPrimes R) :
    (Ideal.map (algebraMap R RCompletion) p.1).IsRadical := by
  -- Proof comment: replace the minimal prime by an annihilator, use flatness of completion to
  -- base-change that annihilator, and then apply reducedness of the completion.
  letI : IsReduced RCompletion :=
    (IsAnalyticallyUnramified.completion_isReduced : IsReduced RCompletion)
  letI : Module.Flat R RCompletion := inferInstance
  obtain ⟨f, hp⟩ := minimalPrime_eq_torsionOf_self R p
  rw [hp, map_torsionOf_self_eq_torsionOf_algebraMap_of_flat]
  exact torsionOf_self_isRadical_of_isReduced (algebraMap R RCompletion f)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the quotient map `R → R ⧸ p` is a local homomorphism. -/
private lemma minimalPrimeQuotient_isLocalHom (p : minimalPrimes R) :
    IsLocalHom (algebraMap R (R ⧸ p.1)) := by
  -- Proof comment: the quotient map is surjective, and surjective maps out of a local ring are
  -- local homomorphisms.
  simpa using IsLocalHom.of_surjective (Ideal.Quotient.mk p.1)
    Ideal.Quotient.mk_surjective

local instance (p : minimalPrimes R) : IsLocalHom (algebraMap R (R ⧸ p.1)) :=
  minimalPrimeQuotient_isLocalHom R p

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the completion map to `R ⧸ p` kills the extended minimal
prime in `R^∧`. -/
private lemma minimalPrime_completionMap_ker_le (p : minimalPrimes R) :
    Ideal.map (algebraMap R RCompletion) p.1 ≤
      RingHom.ker (maximalIdealCompletionMap (algebraMap R (R ⧸ p.1))) := by
  -- Proof comment: reduce membership in the extended ideal to a source element of `p`, then use
  -- functoriality of maximal-ideal completion for the quotient map.
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hcomp :=
    DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R (R ⧸ p.1))) x
  rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
  rw [Ideal.mem_comap, RingHom.mem_ker]
  rw [hcomp]
  change
    algebraMap (R ⧸ p.1)
        (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1))
        (Ideal.Quotient.mk p.1 x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Helper for Chap10 Lemma 10 162 10: the canonical map from `R^∧ / pR^∧` to the actual
maximal-ideal completion of `R ⧸ p`. -/
private noncomputable def minimalPrime_completionQuotient_to_quotientCompletion
    (p : minimalPrimes R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) →+*
      AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1) :=
  Ideal.Quotient.lift
    (Ideal.map (algebraMap R RCompletion) p.1)
    (maximalIdealCompletionMap (algebraMap R (R ⧸ p.1)))
    (minimalPrime_completionMap_ker_le R p)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: on representatives, the quotient-completion map is the
completed image of the quotient class. -/
private lemma minimalPrime_completionQuotient_to_quotientCompletion_mk
    (p : minimalPrimes R) (x : R) :
    minimalPrime_completionQuotient_to_quotientCompletion R p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1)
          (algebraMap R RCompletion x)) =
      AdicCompletion.of (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)
        (Ideal.Quotient.mk p.1 x) := by
  -- Proof comment: unfold the factor map, use functoriality of completion, and identify the
  -- target algebra map with the canonical completion map.
  rw [minimalPrime_completionQuotient_to_quotientCompletion, Ideal.Quotient.lift_mk]
  have hcomp :=
    DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R (R ⧸ p.1))) x
  rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
  calc
    (maximalIdealCompletionMap (algebraMap R (R ⧸ p.1))) ((algebraMap R RCompletion) x) =
        algebraMap (R ⧸ p.1)
          (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1))
          ((algebraMap R (R ⧸ p.1)) x) := hcomp
    _ =
        AdicCompletion.of (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)
          (Ideal.Quotient.mk p.1 x) := by
        change
          algebraMap (R ⧸ p.1)
            (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1))
            (Ideal.Quotient.mk p.1 x) =
            AdicCompletion.of (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)
              (Ideal.Quotient.mk p.1 x)
        simpa using
          (AdicCompletion.algebraMap_apply
            (I := maximalIdeal (R ⧸ p.1)) (R := R ⧸ p.1) (S := R ⧸ p.1)
            (Ideal.Quotient.mk p.1 x))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the maximal ideal of a minimal-prime quotient is the
image of the maximal ideal of the source. -/
private lemma minimalPrimeQuotient_map_maximalIdeal_eq (p : minimalPrimes R) :
    Ideal.map (Ideal.Quotient.mk p.1) (maximalIdeal R) =
      maximalIdeal (R ⧸ p.1) := by
  -- Proof comment: the quotient map is surjective, so the target maximal ideal is the image of
  -- the source maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p.1)
    Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the closed-point quotient of a minimal-prime quotient is
the residue field of the source local ring. -/
private noncomputable def minimalPrimeQuotient_residueField_ringEquiv (p : minimalPrimes R) :
    ((R ⧸ p.1) ⧸ Ideal.map (Ideal.Quotient.mk p.1) (maximalIdeal R)) ≃+*
      R ⧸ maximalIdeal R :=
  DoubleQuot.quotQuotEquivQuotOfLE
    (IsLocalRing.le_maximalIdeal (Ideal.minimalPrimes_isPrime p.2).ne_top)

/-- Helper for Chap10 Lemma 10 162 10: the image of the maximal ideal in a minimal-prime
quotient is finitely generated. -/
private instance minimalPrimeQuotient_map_maximalIdeal_fg
    (p : minimalPrimes R) :
    (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)).FG := by
  -- Proof comment: finite generation is inherited from the Noetherian source maximal ideal and
  -- preserved by ideal maps.
  simpa using ((maximalIdeal R).fg_of_isNoetherianRing.map (algebraMap R (R ⧸ p.1)))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the closed-point quotient of `R ⧸ p` is finite over the
residue field of `R`. -/
private lemma minimalPrimeQuotient_closedPoint_quotient_finite
    (p : minimalPrimes R) :
    Module.Finite (R ⧸ maximalIdeal R)
      ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) := by
  let eResidue := minimalPrimeQuotient_residueField_ringEquiv R p
  letI : Module.Finite (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) := by
    infer_instance
  have halg :
      algebraMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) =
        eResidue.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    -- Proof comment: both residue-field maps agree after precomposing with the quotient map
    -- from `R`.
    ext r
    rw [show
        (algebraMap (R ⧸ maximalIdeal R)
            ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))).comp
          (Ideal.Quotient.mk (maximalIdeal R)) =
            DoubleQuot.quotQuotMk p.1 (maximalIdeal R) by
          rfl]
    exact congrFun
      (congrArg DFunLike.coe <| by
          simpa [minimalPrimeQuotient_residueField_ringEquiv] using
            (DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk
              (R := R) (I := p.1) (J := maximalIdeal R)
              (IsLocalRing.le_maximalIdeal (Ideal.minimalPrimes_isPrime p.2).ne_top)).symm)
      r
  -- Proof comment: transport the finite self-module structure on the residue field across the
  -- double-quotient equivalence.
  have hsurj :
      Function.Surjective
        (Algebra.linearMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) := by
    intro y
    refine ⟨eResidue y, ?_⟩
    change
      algebraMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (eResidue y) = y
    rw [halg]
    exact eResidue.symm_apply_apply y
  exact Module.Finite.of_surjective
    (Algebra.linearMap (R ⧸ maximalIdeal R)
      ((R ⧸ p.1) ⧸ Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)))
    hsurj

/-- Helper for Chap10 Lemma 10 162 10: the mapped-maximal-ideal completion of `R ⧸ p` carries
the canonical commutative ring structure. -/
noncomputable local instance minimalPrime_mapMaximalIdeal_adicCompletion_commRing
    (p : minimalPrimes R) :
    CommRing
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)) :=
  AdicCompletion.instCommRing
    (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 10: the mapped-maximal-ideal completion of `R ⧸ p` is an
algebra over `R ⧸ p`. -/
noncomputable local instance minimalPrime_mapMaximalIdeal_adicCompletion_quotientAlgebra
    (p : minimalPrimes R) :
    Algebra (R ⧸ p.1)
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)) :=
  AdicCompletion.instAlgebra
    (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 10: the mapped-maximal-ideal completion of `R ⧸ p` is an
algebra over the source ring. -/
noncomputable local instance minimalPrime_mapMaximalIdeal_adicCompletion_baseAlgebra
    (p : minimalPrimes R) :
    Algebra R
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)) :=
  AdicCompletion.instAlgebra
    (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 10: the genuine maximal-ideal completion of `R ⧸ p`
identifies with the completion for the image of `maximalIdeal R`. -/
private noncomputable def minimalPrime_maximalIdealCompletionAlgEquivMapped
    (p : minimalPrimes R) :
    AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1) ≃ₐ[R ⧸ p.1]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  maximalIdealCompletionAlgEquivMadicCompletion
    ((maximalIdeal R).fg_of_isNoetherianRing)
    (minimalPrimeQuotient_closedPoint_quotient_finite R p)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the `maximalIdeal R`-power stage on `R ⧸ p` agrees with
the stage cut out by the mapped maximal ideal. -/
private theorem minimalPrimeQuotient_stage_smul_top_eq_stage_map
    (p : minimalPrimes R) (n : ℕ) :
    (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1))) =
      Submodule.restrictScalars R
        ((((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n :
            Ideal (R ⧸ p.1)) : Submodule (R ⧸ p.1) (R ⧸ p.1))) := by
  -- Proof comment: rewrite the scalar-power stage as an ideal image, then identify the image of
  -- the maximal ideal in the quotient.
  rw [Ideal.smul_top_eq_map (R := R) (S := R ⧸ p.1) (I := maximalIdeal R ^ n)]
  simp [Ideal.map_pow, minimalPrimeQuotient_map_maximalIdeal_eq R p]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: after restricting scalars, a mapped-maximal-ideal stage is
the corresponding `maximalIdeal R`-adic module stage. -/
private theorem minimalPrimeQuotient_ring_stage_restrictScalars_eq_module_stage
    (p : minimalPrimes R) (n : ℕ) :
    (((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.1) (R ⧸ p.1))).restrictScalars R :
        Submodule R (R ⧸ p.1)) =
      (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1))) := by
  -- Proof comment: move from ring-linear stages to ideal-as-submodule stages, then use the
  -- quotient-stage identification.
  calc
    (((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.1) (R ⧸ p.1))).restrictScalars R :
        Submodule R (R ⧸ p.1)) =
        Submodule.restrictScalars R
          ((((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n :
              Ideal (R ⧸ p.1)) : Submodule (R ⧸ p.1) (R ⧸ p.1))) := by
          ext x
          simp
    _ = (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1))) := by
          symm
          exact minimalPrimeQuotient_stage_smul_top_eq_stage_map R p n

/-- Helper for Chap10 Lemma 10 162 10: finite stages of the mapped-maximal-ideal completion agree
with the finite stages of the `maximalIdeal R`-adic module completion. -/
private noncomputable def minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage
    (p : minimalPrimes R) (n : ℕ) :
    ((R ⧸ p.1) ⧸
        (((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
            (⊤ : Submodule (R ⧸ p.1) (R ⧸ p.1))))) ≃ₗ[R]
      ((R ⧸ p.1) ⧸
        (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1)))) :=
  ((Submodule.Quotient.restrictScalarsEquiv R
      ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
        (⊤ : Submodule (R ⧸ p.1) (R ⧸ p.1)))).symm).trans
    (Submodule.quotEquivOfEq _ _
      (minimalPrimeQuotient_ring_stage_restrictScalars_eq_module_stage R p n))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the finite-stage comparison sends quotient
representatives to the same representative. -/
private theorem minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_mk
    (p : minimalPrimes R) (n : ℕ) (x : R ⧸ p.1) :
    minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- Proof comment: unfold the comparison; both quotient equivalences are identity on
  -- representatives after the stage equality is applied.
  rw [minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage]
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the inverse finite-stage comparison also sends quotient
representatives to the same representative. -/
private theorem minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk
    (p : minimalPrimes R) (n : ℕ) (x : R ⧸ p.1) :
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- Proof comment: apply the forward comparison to reduce the inverse computation to the
  -- representative computation above.
  apply (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).injective
  rw [LinearEquiv.apply_symm_apply,
    minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_mk]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the finite-stage comparison commutes with transition
maps. -/
private theorem minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_factor
    (p : minimalPrimes R) {m n : ℕ} (h : m ≤ n)
    (z :
      (R ⧸ p.1) ⧸
        (((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.1) (R ⧸ p.1))))) :
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.1) h
        (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n z) =
      minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p m
        (AdicCompletion.transitionMap
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1) h z) := by
  -- Proof comment: transition-map naturality is checked on quotient representatives, where
  -- both finite-stage comparisons are the identity map.
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the inverse finite-stage comparison commutes with
transition maps. -/
private theorem minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_symm_factor
    (p : minimalPrimes R) {m n : ℕ} (h : m ≤ n)
    (z :
      (R ⧸ p.1) ⧸
        (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1)))) :
    AdicCompletion.transitionMap
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) h
        ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm z) =
      (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p m).symm
        (AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.1) h z) := by
  -- Proof comment: the inverse naturality statement is again representative-wise identity.
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

/-- Helper for Chap10 Lemma 10 162 10: the mapped-maximal-ideal ring completion is complete for
the ambient `maximalIdeal R`-adic module topology. -/
private theorem minimalPrimeQuotient_ringCompletion_isAdicComplete_as_module
    (p : minimalPrimes R) :
    IsAdicComplete (maximalIdeal R)
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)) := by
  have hcomplete_map :
      IsAdicComplete
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1)) :=
    AdicCompletion.isAdicComplete (minimalPrimeQuotient_map_maximalIdeal_fg R p)
  -- Proof comment: completeness transports through the quotient algebra map.
  exact (IsAdicComplete.map_algebraMap_iff
    (R := R) (S := R ⧸ p.1)
    (I := maximalIdeal R)
    (M := AdicCompletion
      (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
      (R ⧸ p.1))).mp hcomplete_map

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: coordinatewise inverse finite-stage comparison gives a
compatible point in the mapped-maximal-ideal completion. -/
private theorem minimalPrime_moduleCompletion_to_ringCompletionFun_compatible
    (p : minimalPrimes R)
    (x : AdicCompletion (maximalIdeal R) (R ⧸ p.1)) :
    ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1) h
          ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
            (x.val n)) =
        (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p m).symm
          (x.val m) := by
  -- Proof comment: move transition maps through the inverse finite-stage comparison, then use the
  -- compatibility condition already stored in the source completion point.
  intro m n h
  rw [minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_symm_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 162 10: the coordinatewise forward comparison as a function on
completion points. -/
private noncomputable def minimalPrime_moduleCompletion_to_ringCompletionFun
    (p : minimalPrimes R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.1) →
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  fun x ↦
    ⟨fun n ↦
        (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
          (x.val n),
      minimalPrime_moduleCompletion_to_ringCompletionFun_compatible R p x⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the coordinatewise forward comparison preserves
addition. -/
private theorem minimalPrime_moduleCompletion_to_ringCompletionFun_map_add
    (p : minimalPrimes R)
    (x y : AdicCompletion (maximalIdeal R) (R ⧸ p.1)) :
    minimalPrime_moduleCompletion_to_ringCompletionFun R p (x + y) =
      minimalPrime_moduleCompletion_to_ringCompletionFun R p x +
        minimalPrime_moduleCompletion_to_ringCompletionFun R p y := by
  -- Proof comment: equality of completion points is checked at each coordinate, where the
  -- finite-stage comparison is linear.
  ext n
  exact map_add
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
    (x.val n) (y.val n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the coordinatewise forward comparison preserves source
scalar multiplication. -/
private theorem minimalPrime_moduleCompletion_to_ringCompletionFun_map_smul
    (p : minimalPrimes R) (r : R)
    (x : AdicCompletion (maximalIdeal R) (R ⧸ p.1)) :
    minimalPrime_moduleCompletion_to_ringCompletionFun R p (r • x) =
      r • minimalPrime_moduleCompletion_to_ringCompletionFun R p x := by
  -- Proof comment: the finite-stage comparison is `R`-linear, so scalar compatibility holds
  -- coordinate by coordinate.
  ext n
  exact map_smul
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
    r (x.val n)

/-- Helper for Chap10 Lemma 10 162 10: the module-completion model of `R ⧸ p` maps to its
mapped-maximal-ideal ring completion. -/
private noncomputable def minimalPrime_moduleCompletion_to_ringCompletion
    (p : minimalPrimes R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.1) →ₗ[R]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  { toFun := minimalPrime_moduleCompletion_to_ringCompletionFun R p
    map_add' := minimalPrime_moduleCompletion_to_ringCompletionFun_map_add R p
    map_smul' := minimalPrime_moduleCompletion_to_ringCompletionFun_map_smul R p }

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the forward comparison sends `of x` to the same completed
element in the mapped-maximal-ideal ring completion. -/
private theorem minimalPrime_moduleCompletion_to_ringCompletion_of
    (p : minimalPrimes R) (x : R ⧸ p.1) :
    minimalPrime_moduleCompletion_to_ringCompletion R p
        (AdicCompletion.of (maximalIdeal R) (R ⧸ p.1) x) =
      AdicCompletion.of
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) x := by
  -- Proof comment: after rebuilding the forward map by coordinates, the dense-element
  -- computation is the inverse finite-stage representative computation at every stage.
  ext n
  exact minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk R p n x

/-- Helper for Chap10 Lemma 10 162 10: the `n`th finite-stage map used to lift the reverse
completion comparison. -/
private noncomputable def minimalPrime_ringCompletion_to_moduleCompletionStageMap
    (p : minimalPrimes R) (n : ℕ) :
    AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) →ₗ[R]
      (R ⧸ p.1) ⧸ (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.1))) :=
  (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).toLinearMap.comp
    ((AdicCompletion.eval
      (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
      (R ⧸ p.1) n).restrictScalars R)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the finite-stage maps defining the reverse comparison
are pointwise compatible with the `maximalIdeal R`-adic transition maps. -/
private theorem minimalPrime_ringCompletion_to_moduleCompletion_compatible_apply
    (p : minimalPrimes R) {m n : ℕ} (h : m ≤ n)
    (y :
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)) :
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.1) h
        (minimalPrime_ringCompletion_to_moduleCompletionStageMap R p n y) =
      minimalPrime_ringCompletion_to_moduleCompletionStageMap R p m y := by
  -- Proof comment: the finite-stage comparison commutes with transition maps, and the source
  -- completion coordinates are themselves compatible with transition maps.
  rw [minimalPrime_ringCompletion_to_moduleCompletionStageMap]
  rw [minimalPrime_ringCompletion_to_moduleCompletionStageMap]
  change
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.1) h
        (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n (y.val n)) =
      minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p m (y.val m)
  rw [minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 162 10: the mapped-maximal-ideal ring completion maps back to the
`maximalIdeal R`-adic module completion. -/
private noncomputable def minimalPrime_ringCompletion_to_moduleCompletion
    (p : minimalPrimes R) :
    AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) →ₗ[R]
      AdicCompletion (maximalIdeal R) (R ⧸ p.1) :=
  AdicCompletion.lift (maximalIdeal R)
    (minimalPrime_ringCompletion_to_moduleCompletionStageMap R p)
    (fun h ↦ LinearMap.ext (minimalPrime_ringCompletion_to_moduleCompletion_compatible_apply R p h))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the reverse comparison fixes completed elements coming
from the quotient ring. -/
private theorem minimalPrime_ringCompletion_to_moduleCompletion_of
    (p : minimalPrimes R) (x : R ⧸ p.1) :
    minimalPrime_ringCompletion_to_moduleCompletion R p
        (AdicCompletion.of
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1) x) =
      AdicCompletion.of (maximalIdeal R) (R ⧸ p.1) x := by
  -- Proof comment: evaluate the lifted reverse comparison at every finite stage, then use the
  -- finite-stage representative computation.
  ext n
  rw [minimalPrime_ringCompletion_to_moduleCompletion]
  change
    minimalPrime_ringCompletion_to_moduleCompletionStageMap R p n
        (AdicCompletion.of
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1) x) =
      Submodule.Quotient.mk x
  simpa [minimalPrime_ringCompletion_to_moduleCompletionStageMap] using
    minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_mk R p n x

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the two completion comparisons are inverse on the
`maximalIdeal R`-adic module completion. -/
private theorem minimalPrime_completionComparison_left_inv
    (p : minimalPrimes R) :
    Function.LeftInverse
      (minimalPrime_ringCompletion_to_moduleCompletion R p)
      (minimalPrime_moduleCompletion_to_ringCompletion R p) := by
  -- Proof comment: after evaluating at a finite stage, the composite is
  -- `E_n (E_n.symm _)`, hence the identity.
  intro x
  ext n
  rw [minimalPrime_ringCompletion_to_moduleCompletion]
  change
    minimalPrime_ringCompletion_to_moduleCompletionStageMap R p n
        (minimalPrime_moduleCompletion_to_ringCompletion R p x) =
      x.val n
  rw [minimalPrime_ringCompletion_to_moduleCompletionStageMap,
    minimalPrime_moduleCompletion_to_ringCompletion]
  change
    minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n
        ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
          (x.val n)) =
      x.val n
  exact (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).apply_symm_apply
    (x.val n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the two completion comparisons are inverse on the
mapped-maximal-ideal ring completion. -/
private theorem minimalPrime_completionComparison_right_inv
    (p : minimalPrimes R) :
    Function.RightInverse
      (minimalPrime_ringCompletion_to_moduleCompletion R p)
      (minimalPrime_moduleCompletion_to_ringCompletion R p) := by
  -- Proof comment: the other composite has finite-stage coordinate `E_n.symm (E_n _)`, so it is
  -- also the identity.
  intro y
  ext n
  change
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
        ((minimalPrime_ringCompletion_to_moduleCompletion R p y).val n) =
      y.val n
  rw [minimalPrime_ringCompletion_to_moduleCompletion]
  change
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
        (minimalPrime_ringCompletion_to_moduleCompletionStageMap R p n y) =
      y.val n
  rw [minimalPrime_ringCompletion_to_moduleCompletionStageMap]
  exact (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm_apply_apply
    (y.val n)

/-- Helper for Chap10 Lemma 10 162 10: the module completion of `R ⧸ p` canonically identifies
with its mapped-maximal-ideal ring completion. -/
private noncomputable def minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv
    (p : minimalPrimes R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.1) ≃ₗ[R]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  { minimalPrime_moduleCompletion_to_ringCompletion R p with
    invFun := minimalPrime_ringCompletion_to_moduleCompletion R p
    left_inv := minimalPrime_completionComparison_left_inv R p
    right_inv := minimalPrime_completionComparison_right_inv R p }

/-- Helper for Chap10 Lemma 10 162 10: the multiplicative comparison from
`R^∧ / pR^∧` to the mapped-maximal-ideal completion of `R ⧸ p`. -/
private noncomputable def minimalPrime_completionQuotient_to_mappedCompletion
    (p : minimalPrimes R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) →+*
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  (minimalPrime_maximalIdealCompletionAlgEquivMapped R p).toRingEquiv.toRingHom.comp
    (minimalPrime_completionQuotient_to_quotientCompletion R p)

/-- Helper for Chap10 Lemma 10 162 10: on source representatives from `R`, the multiplicative
comparison sends the class of `x` to the completed class of `x mod p`. -/
private theorem minimalPrime_completionQuotient_to_mappedCompletion_mk
    (p : minimalPrimes R) (x : R) :
    minimalPrime_completionQuotient_to_mappedCompletion R p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1)
          (algebraMap R RCompletion x)) =
      AdicCompletion.of
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) (Ideal.Quotient.mk p.1 x) := by
  -- Proof comment: unfold the composed ring hom, use the quotient-completion computation, and
  -- then apply the maximal-ideal/mapped-ideal comparison on completed source elements.
  rw [minimalPrime_completionQuotient_to_mappedCompletion, RingHom.comp_apply,
    minimalPrime_completionQuotient_to_quotientCompletion_mk]
  exact maximalIdealCompletionAlgEquivMadicCompletion_of
    ((maximalIdeal R).fg_of_isNoetherianRing)
    (minimalPrimeQuotient_closedPoint_quotient_finite R p)
    (Ideal.Quotient.mk p.1 x)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: finite-stage scalar multiplication by a source quotient
class on the completed class of `1` is the finite-stage quotient map to `R ⧸ p`. -/
private theorem minimalPrimeQuotient_stage_smulOne_mk
    (p : minimalPrimes R) (n : ℕ) (x : R) :
    (minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
        ((Ideal.Quotient.mk (maximalIdeal R ^ n) x) •
          Submodule.Quotient.mk (1 : R ⧸ p.1)) =
      Submodule.Quotient.mk (Ideal.Quotient.mk p.1 x) := by
  -- Proof comment: both sides are represented by the image of `x` in `R ⧸ p`; the finite-stage
  -- comparison is identity on representatives.
  rw [Module.Quotient.mk_smul_mk]
  simpa [Algebra.smul_def] using
    minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk R p n
      (Ideal.Quotient.mk p.1 x)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: after converting the finite mapped stage from a
submodule quotient to an ideal quotient, scalar multiplication by a source quotient class agrees
with the finite-stage quotient map. -/
private theorem minimalPrimeQuotient_stage_factor_smulOne_eq_quotientMap
    (p : minimalPrimes R) (n : ℕ) (q : R ⧸ maximalIdeal R ^ n) :
    Ideal.Quotient.factor
        (show
          ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
              (⊤ : Ideal (R ⧸ p.1))) ≤
            (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n by
          simp)
        ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
          (q • Submodule.Quotient.mk (1 : R ⧸ p.1))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        q := by
  -- Proof comment: quotient induction reduces the factor statement to the representative
  -- computation above, where both sides are the ideal-quotient class of `x mod p`.
  refine Quotient.inductionOn' q ?_
  intro x
  let hstage :
      ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
          (⊤ : Ideal (R ⧸ p.1))) ≤
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n := by
    simp
  change
    Ideal.Quotient.factor hstage
        ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
          ((Ideal.Quotient.mk (maximalIdeal R ^ n) x) •
            Submodule.Quotient.mk (1 : R ⧸ p.1))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        (Ideal.Quotient.mk (maximalIdeal R ^ n) x)
  rw [minimalPrimeQuotient_stage_smulOne_mk]
  rfl

/-- Helper for Chap10 Lemma 10 162 10: the linear quotient-completion comparison has the same
finite-stage coordinates as the quotient map induced by `R → R ⧸ p`. -/
private theorem minimalPrime_completionQuotient_linearComparison_eval
    (p : minimalPrimes R) (n : ℕ) (b : RCompletion) :
    AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        n
        (minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv R p
          (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p
            (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        (AdicCompletion.evalₐ (maximalIdeal R) n b) := by
  -- Proof comment: rewrite the quotient-to-module comparison on representatives and then read
  -- the coordinatewise constructed mapped-completion comparison at stage `n`.
  rw [minimalPrime_completionQuotient_moduleCompletion_linearEquiv_mk]
  rw [minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv]
  change
    AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) n
        (minimalPrime_moduleCompletion_to_ringCompletionFun R p
          (b • (AdicCompletion.of (maximalIdeal R) (R ⧸ p.1)) 1)) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  let hstage :
      ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n •
          (⊤ : Ideal (R ⧸ p.1))) ≤
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n := by
    simp
  change
    Ideal.Quotient.factor hstage
        ((minimalPrime_moduleCompletion_to_ringCompletionFun R p
          (b • (AdicCompletion.of (maximalIdeal R) (R ⧸ p.1)) 1)).val n) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  change
    Ideal.Quotient.factor hstage
        ((minimalPrimeQuotient_ringCompletionStageLinearEquivModuleStage R p n).symm
          (b.val n • Submodule.Quotient.mk (1 : R ⧸ p.1))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.1))
        ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            maximalIdeal R ≤
              Ideal.comap (algebraMap R (R ⧸ p.1))
                (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))) n).trans
          (Ideal.le_comap_pow (algebraMap R (R ⧸ p.1)) n)))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  rw [AdicCompletion.val_smul_eq_evalₐ_smul]
  exact minimalPrimeQuotient_stage_factor_smulOne_eq_quotientMap R p n
    (AdicCompletion.evalₐ (maximalIdeal R) n b)

/-- Helper for Chap10 Lemma 10 162 10: the multiplicative quotient-completion map has the same
underlying function as the bijective linear comparison of completions. -/
private theorem minimalPrime_completionQuotient_to_mappedCompletion_eq_linearComparison
    (p : minimalPrimes R)
    (z : RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) :
    minimalPrime_completionQuotient_to_mappedCompletion R p z =
      minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv R p
        (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p z) := by
  -- Proof comment: quotient induction reduces to a representative `b : R^∧`; finite-stage
  -- extensionality compares the ring-hom side with the linear-comparison coordinate formula.
  refine Quotient.inductionOn' z ?_
  intro b
  apply AdicCompletion.ext_evalₐ
  intro n
  change
    (AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) n)
        (minimalPrime_completionQuotient_to_mappedCompletion R p
          (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b)) =
      (AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) n)
        (minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv R p
          (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p
            (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b))
  )
  rw [minimalPrime_completionQuotient_to_mappedCompletion, RingHom.comp_apply,
    minimalPrime_completionQuotient_to_quotientCompletion, Ideal.Quotient.lift_mk]
  change
    (AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) n)
        ((minimalPrime_maximalIdealCompletionAlgEquivMapped R p)
          ((maximalIdealCompletionMap (algebraMap R (R ⧸ p.1))) b)) =
      (AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R)) n)
        (minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv R p
          (minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p
            (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) b))
  )
  rw [minimalPrime_maximalIdealCompletionAlgEquivMapped]
  exact
    (maximalIdealCompletionAlgEquivMadicCompletion_eval_base
      ((maximalIdeal R).fg_of_isNoetherianRing)
      (minimalPrimeQuotient_closedPoint_quotient_finite R p) n b).trans
      (minimalPrime_completionQuotient_linearComparison_eval R p n b).symm

/-- Helper for Chap10 Lemma 10 162 10: the quotient of the completion by the extended minimal
prime is ring-equivalent to the mapped-maximal-ideal completion of the quotient. -/
private noncomputable def minimalPrime_completionQuotient_mappedMaximalCompletion_ringEquiv
    (p : minimalPrimes R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) ≃+*
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1) :=
  -- Proof comment: package the actual ring hom; bijectivity follows from its pointwise equality
  -- with the composite of two linear equivalences.
  RingEquiv.ofBijective (minimalPrime_completionQuotient_to_mappedCompletion R p) <| by
    let e₁ := minimalPrime_completionQuotient_moduleCompletion_linearEquiv R p
    let e₂ := minimalPrime_moduleCompletion_mappedMaximalCompletion_linearEquiv R p
    constructor
    · intro x y hxy
      apply e₁.injective
      apply e₂.injective
      calc
        e₂ (e₁ x) = minimalPrime_completionQuotient_to_mappedCompletion R p x := by
          exact (minimalPrime_completionQuotient_to_mappedCompletion_eq_linearComparison R p x).symm
        _ = minimalPrime_completionQuotient_to_mappedCompletion R p y := hxy
        _ = e₂ (e₁ y) := by
          exact minimalPrime_completionQuotient_to_mappedCompletion_eq_linearComparison R p y
    · intro y
      refine ⟨e₁.symm (e₂.symm y), ?_⟩
      rw [minimalPrime_completionQuotient_to_mappedCompletion_eq_linearComparison]
      simpa [e₁, e₂] using e₂.apply_symm_apply y

-- Proof sketch: the completion map `R → AdicCompletion (maximalIdeal R) R` is faithfully flat, so
-- it is injective. If the completion is reduced, then a nilpotent element of `R` maps to `0`, hence
-- already vanishes in `R`.
/-- Chap10 Lemma 10 162 10 (1): an analytically unramified Noetherian local ring is reduced. -/
@[stacks 032Y]
theorem isReduced_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsReduced R := by
  -- Proof comment: reducedness descends along the injective map into the reduced completion.
  exact isReduced_of_injective
    (algebraMap R (AdicCompletion (maximalIdeal R) R))
    (maximalIdealAdicCompletion_algebraMap_injective R)

/-- Helper for Chap10 Lemma 10 162 10: analytic unramifiedness descends from `R` to the quotient
by a minimal prime. -/
private lemma minimalPrimeQuotient_completion_isReduced [IsAnalyticallyUnramified R]
    (p : minimalPrimes R) :
    IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)) := by
  have hrad :
      (Ideal.map (algebraMap R RCompletion) p.1).IsRadical :=
    minimalPrimeMapCompletion_isRadical R p
  have hquot :
      IsReduced (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) :=
    (Ideal.isRadical_iff_quotient_reduced
      (Ideal.map (algebraMap R RCompletion) p.1)).1 hrad
  -- Proof comment: transport reducedness first across the quotient-to-mapped-completion ring
  -- equivalence, then back across the equivalence from the genuine maximal-ideal completion.
  let eQuot := minimalPrime_completionQuotient_mappedMaximalCompletion_ringEquiv R p
  have hmapped :
      IsReduced
        (AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1)) := by
    letI : IsReduced (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.1) := hquot
    exact isReduced_of_injective eQuot.symm.toRingHom eQuot.symm.injective
  let eMapped := minimalPrime_maximalIdealCompletionAlgEquivMapped R p
  constructor
  intro x hx
  apply eMapped.toRingEquiv.injective
  rw [map_zero]
  exact @IsReduced.eq_zero _ _ _ hmapped (eMapped.toRingEquiv x)
    (hx.map eMapped.toRingEquiv.toRingHom)

-- Proof sketch: for a minimal prime `p`, use exactness of completion on the quotient `R ⧸ p.asIdeal`
-- to identify its completion with the quotient of the completion of `R`. Reducedness of the latter
-- modulo the extended minimal prime shows the quotient ring is analytically unramified.
/-- Chap10 Lemma 10 162 10 (2): if `R` is analytically unramified, then every minimal prime of
`R` is analytically unramified. -/
@[stacks 032Y]
theorem minimalPrime_isAnalyticallyUnramified_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] (p : minimalPrimes R) :
    PrimeSpectrum.IsAnalyticallyUnramified (R := R) ⟨p.1, inferInstance⟩ := by
  -- Proof comment: the owner class only stores reducedness of the quotient completion, supplied by
  -- the quotient-completion bridge above.
  exact ⟨minimalPrimeQuotient_completion_isReduced R p⟩

/-- Helper for Chap10 Lemma 10 162 10: the intersection of the extensions of the minimal
primes to the completion of a reduced Noetherian local ring is zero. -/
private lemma iInf_mappedMinimalPrimes_completion_eq_bot [IsReduced R] :
    (⨅ p : minimalPrimes R, Ideal.map (algebraMap R RCompletion) p.1) =
      (⊥ : Ideal RCompletion) := by
  classical
  letI : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  letI : Module.Flat R RCompletion := inferInstance
  have hsource : (⨅ p : minimalPrimes R, (p.1 : Ideal R)) = (⊥ : Ideal R) := by
    -- Proof comment: minimal primes intersect to the nilradical, and reducedness makes the
    -- nilradical the zero ideal.
    have hsInf' : sInf ((⊥ : Ideal R).minimalPrimes) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes
    have hrad : (⊥ : Ideal R).radical = (⊥ : Ideal R) := by
      simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R
    have hmin : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
      simpa [minimalPrimes] using hsInf'.trans hrad
    simpa [sInf_eq_iInf'] using hmin
  have hmap :
      Ideal.map (algebraMap R RCompletion) (⨅ p : minimalPrimes R, (p.1 : Ideal R)) =
        (⨅ p : minimalPrimes R, Ideal.map (algebraMap R RCompletion) p.1) := by
    -- Proof comment: flatness of completion lets ideal extension commute with this finite
    -- intersection of minimal primes.
    simpa [Finset.inf_eq_iInf, Function.comp_def] using
      (map_finset_inf (f := Ideal.mapInfTopHom (R := R) (S := RCompletion)) Finset.univ
        (fun p : minimalPrimes R ↦ (p.1 : Ideal R)))
  calc
    (⨅ p : minimalPrimes R, Ideal.map (algebraMap R RCompletion) p.1) =
        Ideal.map (algebraMap R RCompletion) (⨅ p : minimalPrimes R, (p.1 : Ideal R)) :=
          hmap.symm
    _ = Ideal.map (algebraMap R RCompletion) (⊥ : Ideal R) := by
          rw [hsource]
    _ = (⊥ : Ideal RCompletion) := by
          simp

/-- Helper for Chap10 Lemma 10 162 10: the canonical product map from the completion to the
mapped-maximal completions of the minimal-prime quotients. -/
private noncomputable def completionToMappedMinimalPrimeCompletions :
    RCompletion →+*
      (∀ p : minimalPrimes R,
        AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1)) :=
  Pi.ringHom fun p ↦
    (minimalPrime_completionQuotient_mappedMaximalCompletion_ringEquiv R p).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1))

/-- Helper for Chap10 Lemma 10 162 10: a dependent product of reduced commutative rings is
reduced. -/
private lemma isReduced_pi_of_forall
    {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]
    (hA : ∀ i, IsReduced (A i)) :
    IsReduced (∀ i, A i) := by
  -- Proof comment: a nilpotent function has nilpotent value in every coordinate, so all
  -- coordinates vanish by the reducedness of the factors.
  constructor
  intro x hx
  funext i
  letI : IsReduced (A i) := hA i
  exact IsReduced.eq_zero (x i) (hx.map (Pi.evalRingHom A i))

/-- Helper for Chap10 Lemma 10 162 10: the product map from the completion to the mapped
minimal-prime quotient completions is injective for a reduced base. -/
private lemma completionToMappedMinimalPrimeCompletions_injective [IsReduced R] :
    Function.Injective (completionToMappedMinimalPrimeCompletions R) := by
  -- Proof comment: compute the kernel coordinatewise. Each coordinate has the same kernel as the
  -- quotient map because the quotient-completion comparison is injective.
  rw [RingHom.injective_iff_ker_eq_bot]
  calc
    RingHom.ker (completionToMappedMinimalPrimeCompletions R) =
        ⨅ p : minimalPrimes R,
          RingHom.ker
            (((minimalPrime_completionQuotient_mappedMaximalCompletion_ringEquiv R p).toRingHom).comp
              (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1))) := by
          rw [completionToMappedMinimalPrimeCompletions, Pi.ker_ringHom]
    _ = ⨅ p : minimalPrimes R, Ideal.map (algebraMap R RCompletion) p.1 := by
          ext x
          rw [Ideal.mem_iInf, Ideal.mem_iInf]
          constructor
          · intro hx p
            let e := minimalPrime_completionQuotient_mappedMaximalCompletion_ringEquiv R p
            have hxcoord :
                ((e.toRingHom).comp
                  (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1))) x = 0 :=
              RingHom.mem_ker.mp (hx p)
            have hquot :
                Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.1) x = 0 := by
              apply e.injective
              change
                e.toRingHom (Ideal.Quotient.mk
                  (Ideal.map (algebraMap R RCompletion) p.1) x) =
                  e.toRingHom 0
              simpa [RingHom.comp_apply, e] using hxcoord
            exact Ideal.Quotient.eq_zero_iff_mem.mp hquot
          · intro hx p
            rw [RingHom.mem_ker, RingHom.comp_apply]
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hx p), map_zero]
            rfl
    _ = (⊥ : Ideal RCompletion) :=
          iInf_mappedMinimalPrimes_completion_eq_bot R

/-- Helper for Chap10 Lemma 10 162 10: reducedness of the completion is detected on the completed
quotients by the minimal primes of a reduced Noetherian local ring. -/
private lemma completion_isReduced_of_reduced_of_minimalPrimeQuotient_completions
    [IsReduced R]
    (hmin :
      ∀ p : minimalPrimes R,
        IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1))) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  -- Proof comment: transport reducedness of each actual quotient completion to the mapped
  -- completion used by the product embedding.
  have hmapped :
      ∀ p : minimalPrimes R,
        IsReduced
        (AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
          (R ⧸ p.1)) := by
    intro p
    let e := (minimalPrime_maximalIdealCompletionAlgEquivMapped R p).symm.toRingEquiv
    constructor
    intro x hx
    apply e.injective
    change e.toRingHom x = e.toRingHom 0
    exact
      @IsReduced.eq_zero
        (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)) _ _
        (hmin p) (e.toRingHom x) (hx.map e.toRingHom)
  -- Proof comment: the product of reduced mapped completions is reduced, and reducedness descends
  -- along the injective product map from `R^∧`.
  have hproduct :
      IsReduced
        (∀ p : minimalPrimes R,
          AdicCompletion
            (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
            (R ⧸ p.1)) :=
    isReduced_pi_of_forall hmapped
  let P :=
    ∀ p : minimalPrimes R,
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.1)) (maximalIdeal R))
        (R ⧸ p.1)
  exact @isReduced_of_injective RCompletion P _ _ (RCompletion →+* P) _ _
    (completionToMappedMinimalPrimeCompletions R)
    (completionToMappedMinimalPrimeCompletions_injective R) hproduct

-- Proof sketch: embed `R` into the product of the quotient rings by its minimal primes. Exactness
-- of completion gives an embedding of the completion of `R` into the product of the completions of
-- those quotients, and each factor is reduced by the analytic unramifiedness hypothesis.
/-- Chap10 Lemma 10 162 10 (3): if `R` is reduced and each minimal prime of `R` is analytically
unramified, then `R` is analytically unramified. -/
@[stacks 032Y]
theorem isAnalyticallyUnramified_of_isReduced_of_minimalPrimes
    [IsReduced R]
    (hmin : ∀ p : minimalPrimes R,
      PrimeSpectrum.IsAnalyticallyUnramified (R := R) ⟨p.1, inferInstance⟩) :
    IsAnalyticallyUnramified R := by
  -- Proof comment: first turn each analytic quotient hypothesis into the reducedness of its
  -- completion, then assemble the ambient analytic-unramified owner.
  have hminReduced :
      ∀ p : minimalPrimes R,
        IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)) := by
    intro p
    letI : IsAnalyticallyUnramified (R ⧸ p.1) := by
      simpa [PrimeSpectrum.IsAnalyticallyUnramified] using hmin p
    exact (IsAnalyticallyUnramified.completion_isReduced :
      IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.1)) (R ⧸ p.1)))
  exact ⟨completion_isReduced_of_reduced_of_minimalPrimeQuotient_completions R hminReduced⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the tensor-left unitor identifies `R ⊗[R] R^∧` with the
reduced completion. -/
private lemma tensorLeftCompletion_isReduced
    [IsReduced RCompletion] :
    IsReduced (R ⊗[R] RCompletion) := by
  -- Proof comment: the tensor-left unitor identifies `R ⊗[R] RCompletion` with the reduced
  -- completion.
  let e : R ⊗[R] RCompletion ≃ₐ[R] RCompletion := Algebra.TensorProduct.lid R RCompletion
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Chap10 Lemma 10 162 10: `FractionRing R ⊗[R] R^∧` carries the canonical
`R^∧`-algebra structure from the right tensor factor. -/
noncomputable local instance fractionRingTensorCompletion_rightAlgebra :
    Algebra RCompletion (FractionRing R ⊗[R] RCompletion) :=
  Algebra.TensorProduct.rightAlgebra (R := R) (A := FractionRing R) (B := RCompletion)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: the base change of `FractionRing R` along the completion
is the localization of `RCompletion` at the image of `nonZeroDivisors R`. -/
private lemma fractionRingTensorCompletion_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid RCompletion (nonZeroDivisors R))
      (FractionRing R ⊗[R] RCompletion) := by
  -- Route correction: replace the manual tensor-right localization plumbing by the canonical
  -- base-change instance for localizations.
  -- Proof comment: `FractionRing R` is the localization of `R` at `nonZeroDivisors R`, so after
  -- tensoring over `R` with `RCompletion` the result is the localization of `RCompletion` at the
  -- image submonoid.
  let _ : IsLocalization (nonZeroDivisors R) (FractionRing R) := inferInstance
  exact IsLocalization.tensorRight
    (R := R) (S := RCompletion) (A := FractionRing R) (M := nonZeroDivisors R)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: after tensoring the completion with the fraction ring on
the left, reducedness follows from localization. -/
private lemma fractionRingTensorCompletion_isReduced
    [IsReduced RCompletion] :
    IsReduced (FractionRing R ⊗[R] RCompletion) := by
  let M := Algebra.algebraMapSubmonoid RCompletion (nonZeroDivisors R)
  let hSource : IsReduced RCompletion := inferInstance
  let _ :
      IsLocalization M
        (FractionRing R ⊗[R] RCompletion) :=
    fractionRingTensorCompletion_isLocalization (R := R)
  -- Proof comment: once the tensor product is identified as the localization of the reduced
  -- completion, reducedness follows directly from the localization theorem.
  exact isReduced_localizationPreserves M (FractionRing R ⊗[R] RCompletion) hSource

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: tensoring the reduced completion with `FractionRing R`
over `R` gives a reduced ring. -/
private lemma completionTensorFractionRing_isReduced
    [IsReduced RCompletion] :
    IsReduced (RCompletion ⊗[R] FractionRing R) := by
  have hReduced : IsReduced (FractionRing R ⊗[R] RCompletion) :=
    fractionRingTensorCompletion_isReduced (R := R)
  letI : IsReduced (FractionRing R ⊗[R] RCompletion) := hReduced
  let e : (RCompletion ⊗[R] FractionRing R) ≃ₐ[R] (FractionRing R ⊗[R] RCompletion) :=
    (Algebra.TensorProduct.comm R (FractionRing R) RCompletion).symm
  -- Proof comment: commute tensor factors to return to the target orientation.
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Chap10 Lemma 10 162 10: the maximal-ideal completion of a Noetherian local ring is
complete local. -/
private lemma completion_isCompleteLocalRing :
    IsCompleteLocalRing RCompletion := by
  have hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    letI : Field (R ⧸ (maximalIdeal R) ^ 1) := by
      let e : R ⧸ (maximalIdeal R) ^ 1 ≃+* R ⧸ maximalIdeal R :=
        Ideal.quotEquivOfEq (pow_one (maximalIdeal R))
      exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
    have hker :
        Ideal.map (algebraMap R RCompletion) (maximalIdeal R) =
          RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1) := by
      simpa [pow_one] using
        completionIdeal_pow_eq_ker_evalₐ (maximalIdeal R)
          (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) 1
    simpa [hker] using
      (RingHom.ker_isMaximal_of_surjective
        (AdicCompletion.evalₐ (maximalIdeal R) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal R) 1) :
          Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1)))
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) RCompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (R := R) (I := maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).2
  letI : IsLocalRing RCompletion := by
    exact @isLocalRing_of_isAdicComplete_maximal RCompletion _
      (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) hmax hcomplete
  have hmap :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R) = maximalIdeal RCompletion := by
    exact IsLocalRing.eq_maximalIdeal hmax
  have hintrinsic :
      IsAdicComplete (maximalIdeal RCompletion) RCompletion := by
    rw [← hmap]
    exact hcomplete
  exact { toIsAdicComplete := hintrinsic }

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 10: after base change to the maximal-ideal completion, the
fraction ring remains essentially finite type over the completion. -/
private lemma completionTensorFractionRing_essFiniteType :
    Algebra.EssFiniteType RCompletion (RCompletion ⊗[R] FractionRing R) := by
  letI : Algebra.EssFiniteType R (FractionRing R) :=
    Algebra.EssFiniteType.of_isLocalization (S := FractionRing R) (nonZeroDivisors R)
  exact Algebra.EssFiniteType.baseChange R (FractionRing R) RCompletion

/-- Helper for Chap10 Lemma 10 162 10: the completed base change of `FractionRing R`. -/
private abbrev completionFractionRingBaseChange :=
  RCompletion ⊗[R] FractionRing R

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change. -/
private noncomputable abbrev completionFractionRingIntegralClosure :=
  integralClosure RCompletion (completionFractionRingBaseChange R)

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change carries
its canonical commutative ring structure. -/
noncomputable local instance completionFractionRingIntegralClosure_commRing :
    CommRing (completionFractionRingIntegralClosure R) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change is an
`R^∧`-algebra. -/
noncomputable local instance completionFractionRingIntegralClosure_algebra :
    Algebra RCompletion (completionFractionRingIntegralClosure R) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change is an
additive commutative group. -/
noncomputable local instance completionFractionRingIntegralClosure_addCommGroup :
    AddCommGroup (completionFractionRingIntegralClosure R) :=
  (completionFractionRingIntegralClosure_commRing (R := R)).toAddCommGroup

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change is an
additive commutative monoid. -/
noncomputable local instance completionFractionRingIntegralClosure_addCommMonoid :
    AddCommMonoid (completionFractionRingIntegralClosure R) :=
  (completionFractionRingIntegralClosure_addCommGroup (R := R)).toAddCommMonoid

/-- Helper for Chap10 Lemma 10 162 10: the integral closure of the completed base change is an
`R^∧`-module. -/
noncomputable local instance completionFractionRingIntegralClosure_module :
    Module RCompletion (completionFractionRingIntegralClosure R) :=
  Algebra.toModule

/-- Helper for Chap10 Lemma 10 162 10: the source normalization inside `FractionRing R`. -/
private noncomputable abbrev fractionRingIntegralClosure :=
  integralClosure R (FractionRing R)

/-- Helper for Chap10 Lemma 10 162 10: the source normalization is a commutative ring. -/
noncomputable local instance fractionRingIntegralClosure_commRing :
    CommRing (fractionRingIntegralClosure R) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 162 10: the source normalization is an `R`-algebra. -/
noncomputable local instance fractionRingIntegralClosure_algebra :
    Algebra R (fractionRingIntegralClosure R) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 162 10: the source normalization is an additive commutative
group. -/
noncomputable local instance fractionRingIntegralClosure_addCommGroup :
    AddCommGroup (fractionRingIntegralClosure R) :=
  (fractionRingIntegralClosure_commRing (R := R)).toAddCommGroup

/-- Helper for Chap10 Lemma 10 162 10: the source normalization is an additive commutative
monoid. -/
noncomputable local instance fractionRingIntegralClosure_addCommMonoid :
    AddCommMonoid (fractionRingIntegralClosure R) :=
  (fractionRingIntegralClosure_addCommGroup (R := R)).toAddCommMonoid

/-- Helper for Chap10 Lemma 10 162 10: the source normalization is an `R`-module. -/
noncomputable local instance fractionRingIntegralClosure_module :
    Module R (fractionRingIntegralClosure R) :=
  Algebra.toModule

/-- Helper for Chap10 Lemma 10 162 10: the normalization of the completed tensor product with the
fraction ring is finite over the completion. -/
private lemma completionIntegralClosure_fractionRing_finite_target
    [IsReduced RCompletion] :
    Module.Finite RCompletion
      (completionFractionRingIntegralClosure R) := by
  letI : IsNoetherianRing RCompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (R := R) (I := maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).1
  letI : IsCompleteLocalRing RCompletion := completion_isCompleteLocalRing (R := R)
  letI : NagataRing RCompletion :=
    nagataRing_of_noetherian_completeLocalRing (R := RCompletion)
  letI : Algebra.EssFiniteType RCompletion (completionFractionRingBaseChange R) :=
    completionTensorFractionRing_essFiniteType (R := R)
  letI : IsReduced (completionFractionRingBaseChange R) :=
    completionTensorFractionRing_isReduced (R := R)
  -- Proof comment: the completed tensor product is a reduced essentially-finite-type algebra
  -- over the Nagata ring `RCompletion`, so the standard finite-normalization theorem applies.
  exact integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced
    (R := RCompletion) (S := completionFractionRingBaseChange R)

/-- Helper for Chap10 Lemma 10 162 10: flat base change to the completion keeps the
integral-closure comparison injective. -/
private lemma completionTensor_toIntegralClosure_injective :
    Function.Injective (TensorProduct.toIntegralClosure R RCompletion (FractionRing R)) := by
  -- Proof comment: the completion is flat over `R`, so Mathlib's injectivity theorem applies
  -- directly to the comparison map.
  exact TensorProduct.toIntegralClosure_injective_of_flat

/-- Helper for Chap10 Lemma 10 162 10: after base change to the maximal-ideal completion, the
normalization of `R` in `FractionRing R` is finite. -/
private lemma completionTensorIntegralClosure_fractionRing_finite
    [IsReduced RCompletion] :
    Module.Finite RCompletion (RCompletion ⊗[R] fractionRingIntegralClosure R) := by
  letI : IsNoetherianRing RCompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (R := R) (I := maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).1
  letI :
      Module.Finite RCompletion
        (completionFractionRingIntegralClosure R) :=
    completionIntegralClosure_fractionRing_finite_target (R := R)
  have htopFG :
      (⊤ : Submodule RCompletion (completionFractionRingIntegralClosure R)).FG := by
    rw [← Module.Finite.iff_fg]
    infer_instance
  have htopNoeth :
      IsNoetherian RCompletion
        (⊤ : Submodule RCompletion (completionFractionRingIntegralClosure R)) :=
    isNoetherian_of_fg_of_noetherian
      (⊤ : Submodule RCompletion (completionFractionRingIntegralClosure R)) htopFG
  letI : IsNoetherian RCompletion (completionFractionRingIntegralClosure R) :=
    (isNoetherian_top_iff
      (R := RCompletion) (M := completionFractionRingIntegralClosure R)).mp htopNoeth
  -- Proof comment: finite generation descends along the injective comparison into the finite
  -- normalization over the completion.
  exact Module.Finite.of_injective
    (TensorProduct.toIntegralClosure R RCompletion (FractionRing R)).toLinearMap
    (completionTensor_toIntegralClosure_injective (R := R))

/-- Helper for Chap10 Lemma 10 162 10: after base change to the maximal-ideal completion, the
source normalization is finite over the completion. -/
noncomputable local instance completionTensorIntegralClosure_fractionRing_moduleFinite
    [IsReduced RCompletion] :
    Module.Finite RCompletion (RCompletion ⊗[R] fractionRingIntegralClosure R) :=
  completionTensorIntegralClosure_fractionRing_finite (R := R)

/-- Helper for Chap10 Lemma 10 162 10: a Noetherian local ring with reduced maximal-ideal
completion has finite normalization in its total fraction ring. -/
private lemma integralClosure_fractionRing_finite_of_reduced_completion
    [IsReduced (AdicCompletion (maximalIdeal R) R)] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  -- Proof comment: first prove finiteness after tensoring with the faithfully flat completion,
  -- then descend finite generation back to `R`.
  have hff : (algebraMap R RCompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R
  -- Route correction: replace the bespoke descent wrapper by the canonical faithfully-flat module
  -- instance and the standard finite-tensor descent theorem.
  letI : Module.FaithfullyFlat R RCompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have hfiniteTensor :
      Module.Finite RCompletion (RCompletion ⊗[R] fractionRingIntegralClosure R) :=
    completionTensorIntegralClosure_fractionRing_finite (R := R)
  -- Proof comment: the completion map is faithfully flat, so finite generation of the completed
  -- tensor product descends directly to the original normalization.
  simpa [fractionRingIntegralClosure] using
    (@Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
      R _ RCompletion _ _ (fractionRingIntegralClosure R) _ _ _ hfiniteTensor)

-- Proof sketch: the completion of `R` is reduced, so its minimal-prime decomposition identifies
-- its total quotient ring with a finite product of fields. The integral closure over the completion
-- is finite by the domain case on each factor, and faithful flatness of completion descends a
-- finite generating set to the integral closure of `R` in `Q(R)`.
/-- Chap10 Lemma 10 162 10 (4): if `R` is analytically unramified, then the integral closure of
`R` in its total ring of fractions is finite over `R`. -/
@[stacks 032Y]
theorem integralClosure_fractionRing_finite_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  -- Proof comment: analytic unramifiedness is exactly the reduced-completion input required by the
  -- finite-normalization bridge.
  exact integralClosure_fractionRing_finite_of_reduced_completion R

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

-- Proof sketch: apply part (4) to obtain finiteness of the integral closure of `R` in
-- `FractionRing R`; this is exactly the defining field of `IsN1Ring R`.
/-- Chap10 Lemma 10 162 10 (5): an analytically unramified Noetherian local domain is `N-1`. -/
@[stacks 032Y]
theorem isN1Ring_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsN1Ring R := by
  -- Proof comment: the defining field of `IsN1Ring` is precisely the finiteness statement from
  -- part (4).
  exact IsN1Ring.mk (integralClosure_fractionRing_finite_of_isAnalyticallyUnramified R)

end
