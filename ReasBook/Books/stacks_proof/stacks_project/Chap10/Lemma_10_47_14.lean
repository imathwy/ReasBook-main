import Mathlib
import StacksProject_2024.Chap09.Lemma_9_15_7
import StacksProject_2024.Chap10.Lemma_10_36_20
import StacksProject_2024.Chap10.Lemma_10_47_7
import StacksProject_2024.Chap10.Lemma_10_47_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise TensorProduct
open AlgebraicGeometry CommRingCat
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "TensorRing" => SeparableClosure k ⊗[k] K
local notation "SpecTensor" => PrimeSpectrum TensorRing
local notation "Omega" => SeparableClosure k
local notation "kSep" => separableClosure k K
local notation "SepTensorRing" => Omega ⊗[k] kSep
local notation "SepSpecTensor" => PrimeSpectrum SepTensorRing
local notation "IterTensorRing" => SepTensorRing ⊗[kSep] K
local notation "IterSpecTensor" => PrimeSpectrum IterTensorRing
noncomputable local instance sepTensorCommRing : CommRing SepTensorRing := by
  exact Algebra.TensorProduct.instCommRing (R := k) (A := Omega) (B := kSep)
noncomputable local instance sepTensorRightAlgebra : Algebra kSep SepTensorRing :=
  Algebra.TensorProduct.rightAlgebra
noncomputable local instance sepTensorLeftAlgebra : Algebra Omega SepTensorRing :=
  Algebra.TensorProduct.leftAlgebra
noncomputable local instance sepTensorRightModule : Module kSep SepTensorRing :=
  @Algebra.toModule kSep SepTensorRing
    (inferInstance : CommSemiring kSep) (inferInstance : Semiring SepTensorRing)
    sepTensorRightAlgebra
noncomputable local instance sepTensorSelfSMul : SMul SepTensorRing SepTensorRing :=
  instSMulOfMul
noncomputable local instance sepTensorSelfModule : Module SepTensorRing SepTensorRing :=
  Semiring.toModule
noncomputable local instance iterTensorCommRing : CommRing IterTensorRing := by
  exact Algebra.TensorProduct.instCommRing (R := kSep) (A := SepTensorRing) (B := K)
noncomputable local instance iterTensorLeftAlgebra : Algebra SepTensorRing IterTensorRing :=
  by
    exact Algebra.TensorProduct.leftAlgebra (R := kSep) (S := SepTensorRing) (A := SepTensorRing)
      (B := K)

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
theorem galoisTensorPrimeSpectrum_smul_def (σ : Gal(SeparableClosure k/k))
    (p : SpecTensor) :
    σ • p =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)).symm.toRingHom p :=
  rfl

noncomputable local instance tensorRingTopologicalSpace : TopologicalSpace TensorRing := ⊥

noncomputable local instance tensorRingDiscreteTopology : DiscreteTopology TensorRing := ⟨rfl⟩

/-- Helper for Lemma 10.47.14: in the right-basis expansion of `SeparableClosure k ⊗[k] K`, the
Galois action acts coefficientwise on the `SeparableClosure k` coefficients. -/
private theorem tensor_rightBasis_coeff_smul
    {ι : Type*} [DecidableEq ι] (bK : Module.Basis ι k K)
    (σ : Gal(SeparableClosure k/k)) (x : TensorRing) :
    TensorProduct.equivFinsuppOfBasisRight bK (σ • x) =
      (TensorProduct.equivFinsuppOfBasisRight bK x).mapRange (fun a ↦ σ a) (by simp) := by
  classical
  ext i
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    have hmap_zero : (fun a : SeparableClosure k ↦ σ a) 0 = 0 := by
      simp
    have hleft :
        ((TensorProduct.equivFinsuppOfBasisRight bK) (σ • a ⊗ₜ[k] b)) i =
          (bK.repr b) i • (σ a) := by
      exact
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
          (𝒞 := bK) (m := σ • a) (n := b) (i := i)
    have hright :
        ((Finsupp.mapRange (fun a ↦ σ a) hmap_zero
            ((TensorProduct.equivFinsuppOfBasisRight bK) (a ⊗ₜ[k] b))) i) =
          (bK.repr b) i • (σ a) := by
      simp
    rw [hleft, hright]
  · intro x y hx hy
    simp [hx, hy]

noncomputable local instance tensorRingContinuousSMul :
    ContinuousSMul (Gal(SeparableClosure k / k)) TensorRing := by
  classical
  let bK : Module.Basis (Module.Free.ChooseBasisIndex k K) k K := Module.Free.chooseBasis k K
  refine (continuousSMul_iff_stabilizer_isOpen).2 ?_
  intro x
  let c := TensorProduct.equivFinsuppOfBasisRight bK x
  let H : Subgroup (Gal(SeparableClosure k / k)) :=
    ⨅ i ∈ c.support, MulAction.stabilizer (Gal(SeparableClosure k / k)) (c i)
  have hH_open : IsOpen (H : Set (Gal(SeparableClosure k / k))) := by
    have hHset :
        (H : Set (Gal(SeparableClosure k / k))) =
          ⋂ i ∈ c.support,
            (MulAction.stabilizer (Gal(SeparableClosure k / k)) (c i) :
              Set (Gal(SeparableClosure k / k))) := by
      ext σ
      simp [H]
    rw [hHset]
    exact isOpen_biInter_finset fun i hi ↦ stabilizer_isOpen_of_isIntegral (c i)
  have hH_le : H ≤ MulAction.stabilizer (Gal(SeparableClosure k / k)) x := by
    intro σ hσ
    have hcoeff :
        (TensorProduct.equivFinsuppOfBasisRight bK x).mapRange (fun a ↦ σ a) (by simp) =
          TensorProduct.equivFinsuppOfBasisRight bK x := by
      ext i
      by_cases hi : i ∈ c.support
      · have hfix : σ • c i = c i := by
          exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ i) hi
        simpa [c, hi] using hfix
      · have hci : c i = 0 := by
          simpa [Finsupp.mem_support_iff] using hi
        simp [c, hci]
    have hsigma :
        TensorProduct.equivFinsuppOfBasisRight bK (σ • x) =
          TensorProduct.equivFinsuppOfBasisRight bK x := by
      rw [tensor_rightBasis_coeff_smul (bK := bK), hcoeff]
    exact (TensorProduct.equivFinsuppOfBasisRight bK).injective hsigma
  exact Subgroup.isOpen_mono hH_le hH_open

noncomputable local instance tensorRingSmulCommClass :
    SMulCommClass (Gal(SeparableClosure k / k)) K TensorRing where
  smul_comm σ x z := by
    change (tensorAut σ) ((algebraMap K TensorRing x) * z) =
        (algebraMap K TensorRing x) * (tensorAut σ z)
    rw [map_mul]
    congr 1
    change Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)
          ((1 : SeparableClosure k) ⊗ₜ[k] x) = (1 : SeparableClosure k) ⊗ₜ[k] x
    simp

noncomputable local instance tensorRingIsInvariant :
    Algebra.IsInvariant K TensorRing (Gal(SeparableClosure k / k)) where
  isInvariant x hx := by
    classical
    let bK : Module.Basis (Module.Free.ChooseBasisIndex k K) k K := Module.Free.chooseBasis k K
    let c := TensorProduct.equivFinsuppOfBasisRight bK x
    have hcoeff_bot :
        ∀ i, c i ∈ (⊥ : IntermediateField k (SeparableClosure k)) := by
      intro i
      have hfixed : ∀ σ : Gal(SeparableClosure k / k), σ (c i) = c i := by
        intro σ
        have hσ :
            TensorProduct.equivFinsuppOfBasisRight bK (σ • x) =
              (TensorProduct.equivFinsuppOfBasisRight bK x).mapRange (fun a ↦ σ a) (by simp) :=
          tensor_rightBasis_coeff_smul (bK := bK) σ x
        have hσ' := congrArg (fun d ↦ d i) hσ
        have hleft : ((TensorProduct.equivFinsuppOfBasisRight bK) (σ • x)) i = c i := by
          simpa [c] using
            congrArg (fun z ↦ (TensorProduct.equivFinsuppOfBasisRight bK z) i) (hx σ)
        have hσ'' :
            ((TensorProduct.equivFinsuppOfBasisRight bK) (σ • x)) i = σ (c i) := by
          simpa [c] using hσ'
        have hci : c i = σ (c i) := hleft.symm.trans hσ''
        exact hci.symm
      exact (InfiniteGalois.mem_bot_iff_fixed (k := k) (K := SeparableClosure k) (c i)).2 hfixed
    let coeffLift : Module.Free.ChooseBasisIndex k K → k :=
      fun i ↦ Classical.choose (IntermediateField.mem_bot.mp (hcoeff_bot i))
    let y : K := c.sum fun i _ ↦ coeffLift i • bK i
    refine ⟨y, ?_⟩
    have hcoeffLift : ∀ i, algebraMap k (SeparableClosure k) (coeffLift i) = c i := by
      intro i
      exact Classical.choose_spec (IntermediateField.mem_bot.mp (hcoeff_bot i))
    rw [show algebraMap K TensorRing y = (1 : SeparableClosure k) ⊗ₜ[k] y by rfl]
    calc
      (1 : SeparableClosure k) ⊗ₜ[k] y
          = ∑ i ∈ c.support, (1 : SeparableClosure k) ⊗ₜ[k] (coeffLift i • bK i) := by
              simp [y, Finsupp.sum, TensorProduct.tmul_sum]
      _ = ∑ i ∈ c.support, c i ⊗ₜ[k] bK i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              (1 : SeparableClosure k) ⊗ₜ[k] (coeffLift i • bK i)
                  = coeffLift i • ((1 : SeparableClosure k) ⊗ₜ[k] bK i) := by
                      rw [TensorProduct.tmul_smul]
              _ = (algebraMap k (SeparableClosure k) (coeffLift i)) ⊗ₜ[k] bK i := by
                    simpa [Algebra.smul_def] using
                      (TensorProduct.smul_tmul' (coeffLift i) (1 : SeparableClosure k) (bK i))
              _ = c i ⊗ₜ[k] bK i := by
                    rw [hcoeffLift i]
      _ = c.sum (fun i a ↦ a ⊗ₜ[k] bK i) := by
            simp [Finsupp.sum]
      _ = (TensorProduct.equivFinsuppOfBasisRight bK).symm c := by
            symm
            exact TensorProduct.equivFinsuppOfBasisRight_symm_apply bK c
      _ = x := by
            simp [c]

/-- Helper for Lemma 10.47.14: the spectrum action agrees with the ideal-level pointwise action. -/
private theorem tensorPrime_asIdeal_smul
    (σ : Gal(SeparableClosure k/k)) (p : SpecTensor) :
    (σ • p).asIdeal = σ • p.asIdeal :=
  by
    change Ideal.comap ((tensorAut σ).symm.toRingHom) p.asIdeal =
      Ideal.map ((tensorAut σ).toRingEquiv : TensorRing ≃+* TensorRing) p.asIdeal
    exact Ideal.comap_symm ((tensorAut σ).toRingEquiv) (I := p.asIdeal)

-- Proof sketch: first replace `K` by the relative separable closure `separableClosure k K` using
-- Lemmas `10.47.13` and `10.47.7`, which identifies the two prime spectra. For the separable
-- extension, primes of `SeparableClosure k ⊗[k] separableClosure k K` correspond to `k`-embeddings
-- `separableClosure k K → SeparableClosure k`, and `Gal(SeparableClosure k / k)` acts transitively
-- on those embeddings by postcomposition.
/-- Lemma 10.47.14: the Galois group of the separable closure acts transitively on the prime
spectrum of `SeparableClosure k ⊗[k] K`. Equivalently, any two primes are conjugate under the
canonical action induced from the left tensor factor. -/
@[stacks 04KP, instance]
theorem galoisTensorPrimeSpectrum_transitive :
    MulAction.IsPretransitive (Gal(SeparableClosure k / k)) SpecTensor := by
  refine ⟨?_⟩
  intro p q
  have hp_under : Ideal.under K p.asIdeal = ⊥ := by
    letI : (Ideal.under K p.asIdeal).IsPrime := by
      simpa [Ideal.under_def] using Ideal.comap_isPrime (algebraMap K TensorRing) p.asIdeal
    exact Ideal.eq_bot_of_prime (Ideal.under K p.asIdeal)
  have hq_under : Ideal.under K q.asIdeal = ⊥ := by
    letI : (Ideal.under K q.asIdeal).IsPrime := by
      simpa [Ideal.under_def] using Ideal.comap_isPrime (algebraMap K TensorRing) q.asIdeal
    exact Ideal.eq_bot_of_prime (Ideal.under K q.asIdeal)
  have htrans : ∃ σ : Gal(SeparableClosure k / k), q.asIdeal = σ • p.asIdeal := by
    exact
      @Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
        K TensorRing
        inferInstance inferInstance inferInstance
        (Gal(SeparableClosure k / k))
        inferInstance inferInstance
        (tensorRingSmulCommClass (k := k) (K := K))
        inferInstance inferInstance inferInstance inferInstance
        tensorRingTopologicalSpace tensorRingDiscreteTopology tensorRingContinuousSMul
        tensorRingIsInvariant
        p.asIdeal q.asIdeal inferInstance inferInstance
        (hp_under.trans hq_under.symm)
  rcases htrans with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  apply PrimeSpectrum.ext
  simpa [tensorPrime_asIdeal_smul] using hσ.symm

/-- Textbook unpacking of Lemma 10.47.14: any two primes are conjugate under the canonical
Galois action. -/
theorem galoisTensorPrimeSpectrum_exists_smul_eq (p q : SpecTensor) :
    ∃ σ : Gal(SeparableClosure k / k), σ • p = q := by
  -- Proof comment: this is the elementwise form of the pretransitivity instance proved above.
  letI : MulAction.IsPretransitive (Gal(SeparableClosure k / k)) SpecTensor :=
    galoisTensorPrimeSpectrum_transitive
  simpa using (MulAction.exists_smul_eq (Gal(SeparableClosure k / k)) p q)

end
