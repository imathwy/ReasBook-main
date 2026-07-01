import Mathlib
import stacks_project.Chap10.Lemma_10_47_3

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
open Polynomial

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Helper for Lemma 10.47.8: every coefficient of a monic divisor of the mapped minimal
polynomial is already in the base field because it is algebraic over `k`. -/
private theorem coeff_mem_bot_of_monic_dvd_mapped_minpoly
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥) {q : Polynomial K} (hq_monic : q.Monic)
    (hq_dvd : q ∣ (minpoly k pb.gen).map (algebraMap k K)) :
    ∀ i : ℕ, q.coeff i ∈ (⊥ : IntermediateField k K) := by
  intro i
  -- Proof comment: divisors of a monic polynomial with coefficients in `k` have integral
  -- coefficients, hence algebraic coefficients; `hclosed` then collapses them to `k`.
  have hcoeff_integral : IsIntegral k (q.coeff i) := by
    simpa using
      Polynomial.isIntegral_coeff_of_dvd
        (minpoly k pb.gen) q (minpoly.monic pb.isIntegral_gen) hq_monic hq_dvd i
  have hcoeff_mem : q.coeff i ∈ algebraicClosure k K := by
    exact mem_algebraicClosure_iff'.mpr hcoeff_integral
  simpa [hclosed] using hcoeff_mem

/-- Helper for Lemma 10.47.8: the minimal polynomial of a primitive element stays irreducible
after base change from `k` to `K` when `k` is algebraically closed in `K`. -/
private theorem mapped_minpoly_irreducible_of_algebraicClosure_eq_bot
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥) :
    Irreducible ((minpoly k pb.gen).map (algebraMap k K)) := by
  let pK : Polynomial K := (minpoly k pb.gen).map (algebraMap k K)
  have hpK_monic : pK.Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  refine (hpK_monic.irreducible_iff_natDegree).2 ?_
  refine ⟨?_, ?_⟩
  · -- Proof comment: mapping the nonconstant minimal polynomial keeps positive degree.
    intro hpK_one
    have hdeg : 0 < pK.natDegree := by
      change 0 < ((minpoly k pb.gen).map (algebraMap k K)).natDegree
      rw [(minpoly.monic pb.isIntegral_gen).natDegree_map]
      exact minpoly.natDegree_pos pb.isIntegral_gen
    simpa [hpK_one] using hdeg
  · intro q r hq_monic hr_monic hqr
    have hq_dvd : q ∣ pK := ⟨r, hqr.symm⟩
    have hr_dvd : r ∣ pK := ⟨q, by rw [mul_comm, hqr]⟩
    have hq_lifts : q ∈ Polynomial.lifts (algebraMap k K) := by
      refine q.lifts_iff_coeff_lifts.mpr ?_
      intro i
      simpa [Algebra.mem_bot, Set.mem_range] using
        coeff_mem_bot_of_monic_dvd_mapped_minpoly
          (k := k) (K := K) pb hclosed hq_monic hq_dvd i
    have hr_lifts : r ∈ Polynomial.lifts (algebraMap k K) := by
      refine r.lifts_iff_coeff_lifts.mpr ?_
      intro i
      simpa [Algebra.mem_bot, Set.mem_range] using
        coeff_mem_bot_of_monic_dvd_mapped_minpoly
          (k := k) (K := K) pb hclosed hr_monic hr_dvd i
    obtain ⟨q0, hq0_map, hq0_deg, hq0_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hq_lifts hq_monic
    obtain ⟨r0, hr0_map, hr0_deg, hr0_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hr_lifts hr_monic
    have hfactor0 : q0 * r0 = minpoly k pb.gen := by
      -- Proof comment: once both factors descend coefficientwise, injectivity of `map`
      -- transports the factorization back to `k[X]`.
      apply Polynomial.map_injective (algebraMap k K) (FaithfulSMul.algebraMap_injective k K)
      simpa [pK, Polynomial.map_mul, hq0_map, hr0_map] using hqr
    rcases (minpoly.irreducible pb.isIntegral_gen).isUnit_or_isUnit hfactor0.symm with
        hq0_unit | hr0_unit
    · left
      have hq0_one : q0 = 1 := hq0_monic.eq_one_of_isUnit hq0_unit
      have hq0_nat : q0.natDegree = 0 := by simpa [hq0_one]
      simpa [hq0_deg] using hq0_nat
    · right
      have hr0_one : r0 = 1 := hr0_monic.eq_one_of_isUnit hr0_unit
      have hr0_nat : r0.natDegree = 0 := by simpa [hr0_one]
      simpa [hr0_deg] using hr0_nat

/-- Helper for Lemma 10.47.8: a finite separable base change tensor product is generated over `K`
by `1 ⊗ pb.gen`. -/
private theorem tensorProduct_gen_adjoin_eq_top_of_powerBasis
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L) :
    Algebra.adjoin K ({((1 : K) ⊗ₜ[k] pb.gen)} : Set (K ⊗[k] L)) = ⊤ := by
  -- Proof comment: transport the primitive-element generator across the standard tensor-product
  -- adjoin lemma.
  simpa [Set.image_singleton] using
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := K) ({pb.gen} : Set L) pb.adjoin_gen_eq_top)

/-- Helper for Lemma 10.47.8: after finite separable base change, the tensor product with `K`
is a domain. -/
private theorem isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (hclosed : algebraicClosure k K = ⊥) :
    IsDomain (K ⊗[k] L) := by
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let x : K ⊗[k] L := (1 : K) ⊗ₜ[k] pb.gen
  have hpK_irreducible :
      Irreducible ((minpoly k pb.gen).map (algebraMap k K)) :=
    mapped_minpoly_irreducible_of_algebraicClosure_eq_bot (k := k) (K := K) pb hclosed
  have hpK_monic : ((minpoly k pb.gen).map (algebraMap k K)).Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  have hx_aeval : Polynomial.aeval x ((minpoly k pb.gen).map (algebraMap k K)) = 0 := by
    -- Proof comment: `x = 1 ⊗ pb.gen` is exactly the image of `pb.gen` under
    -- `TensorProduct.includeRight`, so the mapped minimal polynomial vanishes at `x`.
    rw [Polynomial.aeval_map_algebraMap (R := k) (A := K) (x := x) (p := minpoly k pb.gen)]
    change Polynomial.aeval
        ((Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)) pb.gen)
        (minpoly k pb.gen) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hx_integral : IsIntegral K x := by
    -- Proof comment: the mapped minimal polynomial is monic and annihilates `x`.
    exact ⟨_, hpK_monic, hx_aeval⟩
  have hminpoly :
      minpoly K x = (minpoly k pb.gen).map (algebraMap k K) := by
    -- Proof comment: identify the `K`-minimal polynomial of the tensor generator by the usual
    -- `irreducible + monic + root` characterization.
    exact (minpoly.eq_of_irreducible_of_monic hpK_irreducible hx_aeval hpK_monic).symm
  have hAdjoinRootDomain : IsDomain (AdjoinRoot (minpoly K x)) := by
    -- Proof comment: the minimal polynomial is prime because it is irreducible over a field.
    have hprime : Prime (minpoly K x) := by
      rw [hminpoly]
      exact hpK_irreducible.prime
    exact AdjoinRoot.isDomain_of_prime hprime
  have hAdjoinDomain : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := by
    have hToAdjoin_injective :
        Function.Injective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x)) := by
      -- Proof comment: if a class in `AdjoinRoot` maps to zero in the adjoin algebra, represent
      -- it by a polynomial `p`; then `p(x) = 0`, so `minpoly K x ∣ p`, hence the class is zero.
      refine (injective_iff_map_eq_zero _).2 ?_
      intro y hy
      obtain ⟨p, rfl⟩ := (AdjoinRoot.mk_surjective (g := minpoly K x)) y
      rw [AdjoinRoot.Minpoly.coe_toAdjoin, AdjoinRoot.liftAlgHom_mk] at hy
      have hy' : Polynomial.aeval x p = 0 := by
        -- Proof comment: forget from the adjoin subalgebra back to the ambient tensor product.
        have hy'' :
            ((Polynomial.aeval ⟨x, self_mem_adjoin_singleton K x⟩ p :
              Algebra.adjoin K ({x} : Set (K ⊗[k] L))) : K ⊗[k] L) = 0 := by
          exact congrArg
            (fun z : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) => (z : K ⊗[k] L))
            hy
        rw [Polynomial.aeval_subalgebra_coe] at hy''
        exact hy''
      exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd K x hy')
    have hToAdjoin_surjective :
        Function.Surjective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x)) :=
      AdjoinRoot.Minpoly.toAdjoin.surjective (R := K) (x := x)
    let eAdjoin :
        AdjoinRoot (minpoly K x) ≃ₐ[K] Algebra.adjoin K ({x} : Set (K ⊗[k] L)) :=
      AlgEquiv.ofBijective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x))
        ⟨hToAdjoin_injective, hToAdjoin_surjective⟩
    letI : IsDomain (AdjoinRoot (minpoly K x)) := hAdjoinRootDomain
    exact MulEquiv.isDomain (AdjoinRoot (minpoly K x)) eAdjoin.toMulEquiv.symm
  have hgen : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) = ⊤ := by
    -- Proof comment: the primitive element already generates the whole tensor product.
    simpa [x] using tensorProduct_gen_adjoin_eq_top_of_powerBasis (k := k) (K := K) pb
  let eTop : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) ≃ₐ[K] K ⊗[k] L :=
    (Subalgebra.equivOfEq _ _ hgen).trans Subalgebra.topEquiv
  -- Proof comment: transport the domain structure from the adjoin-root model to the full tensor
  -- product using the generator-equals-top identification.
  letI : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := hAdjoinDomain
  exact MulEquiv.isDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) eTop.toMulEquiv.symm

/-- Lemma 10.47.8: if `k` is algebraically closed in the field extension `K`, then `K` is
geometrically irreducible over `k`. -/
@[stacks 037P]
theorem isGeometricallyIrreducibleOver_of_algebraicClosure_eq_bot
    (hclosed : algebraicClosure k K = ⊥) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_finiteSeparable_baseChange]
  intro L _ _ _ _
  -- Proof comment: by Lemma `10.47.3` it is enough to test finite separable extensions, and the
  -- primitive-element/irreducible-polynomial argument shows each base-change tensor product is a
  -- domain.
  letI : IsDomain (K ⊗[k] L) :=
    isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
      (k := k) (K := K) (L := L) hclosed
  infer_instance

end

end Algebra
