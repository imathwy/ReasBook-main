import stacks_proof.stacks_project.Chap10.Lemma_10_64_3.SemilocalPrime
import stacks_proof.stacks_project.Chap10.Lemma_10_64_3.TensorQuotient

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open scoped TensorProduct

namespace Ideal

variable (𝔭 : Ideal R) [𝔭.IsPrime]
variable [(𝔭.map (algebraMap R S)).IsPrime]

local notation "𝔭S" => 𝔭.map (algebraMap R S)
local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S (Ideal.primeCompl 𝔭))
local notation "S𝔮" => Localization.AtPrime 𝔭S

attribute [local instance] semilocal_map_prime_isPrime
attribute [local instance] semilocalToLocalAlgebra

/-- Helper for Lemma 10.64.3: over a domain, any nonzero scalar acts regularly on a finitely
supported family of copies of that domain. -/
lemma isSMulRegular_finsupp_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} {g : A} (hg : g ≠ 0) :
    IsSMulRegular (ι →₀ A) g := by
  -- Check regularity coordinatewise, where cancellation reduces to the domain structure on `A`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro f hf
  ext i
  have hcoord := congrArg (fun h : ι →₀ A => h i) hf
  simp only [Finsupp.smul_apply, smul_eq_mul] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hg

/-- Helper for Lemma 10.64.3: over a domain, any nonzero scalar acts regularly on the tensor of
that domain with a vector space over the base field. -/
lemma isSMulRegular_tensor_vectorSpace_of_ne_zero
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsDomain A]
    {V : Type*} [AddCommGroup V] [Module κ V]
    {g : A} (hg : g ≠ 0) :
    IsSMulRegular (A ⊗[κ] V) g := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex κ V) κ V :=
    Module.Basis.ofVectorSpace κ V
  let e :
      A ⊗[κ] V ≃ₗ[A] (Module.Basis.ofVectorSpaceIndex κ V →₀ A) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (R := κ) (A := A) (V := V) b
  have hregular_finsupp :
      IsSMulRegular (Module.Basis.ofVectorSpaceIndex κ V →₀ A) g :=
    isSMulRegular_finsupp_of_ne_zero
      (A := A) (ι := Module.Basis.ofVectorSpaceIndex κ V) hg
  -- Transport the coordinatewise regularity back through the tensor/finsupp linear equivalence.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply e.injective
  have hz' : g • e z = 0 := by
    simpa using congrArg e hz
  exact hregular_finsupp.right_eq_zero_of_smul hz'

/-- Helper for Lemma 10.64.3: each denominator outside the semilocalized prime already acts
regularly on the first quotient `Sₚ / J`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma semilocal_denominator_class_ne_zero
    (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) :
    Ideal.Quotient.mk (map (algebraMap S Sₚ) 𝔭S) (c : Sₚ) ≠ 0 := by
  -- The quotient class is zero exactly when the denominator lies in the prime, which is excluded
  -- by the defining property of `primeCompl`.
  intro hc
  exact c.2 <| by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hc

/-- Helper for Lemma 10.64.3: each denominator outside the semilocalized prime already acts
regularly on the first quotient `Sₚ / J`, where `J = map (algebraMap S Sₚ) 𝔭S`. -/
lemma semilocal_denominator_isSMulRegular_prime_quotient
    (c : Ideal.primeCompl (map (algebraMap S Sₚ) 𝔭S)) :
    IsSMulRegular (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) (c : Sₚ) := by
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  have hc :
      algebraMap Sₚ (Sₚ ⧸ J) c ∈ nonZeroDivisors (Sₚ ⧸ J) := by
    -- The quotient class of `c` is literally the image of an element of `J.primeCompl`.
    have hc_map :
        algebraMap Sₚ (Sₚ ⧸ J) c ∈
          Algebra.algebraMapSubmonoid (Sₚ ⧸ J) (Ideal.primeCompl J) := by
      change algebraMap Sₚ (Sₚ ⧸ J) c ∈ Submonoid.map (algebraMap Sₚ (Sₚ ⧸ J))
        (Ideal.primeCompl J)
      exact ⟨c, c.2, rfl⟩
    exact semilocal_denominator_nonZeroDivisors_prime_quotient
      (R := R) (S := S) (𝔭 := 𝔭) hc_map
  -- Read the quotient-ring nonzerodivisor statement as injectivity of multiplication by `c`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
  have hx' : algebraMap Sₚ (Sₚ ⧸ J) c * x = 0 := by
    change algebraMap Sₚ (Sₚ ⧸ J) c * x = 0 at hx
    exact hx
  exact (mem_nonZeroDivisors_iff_left.mp hc) x hx'

/-- Helper for Lemma 10.64.3: the literal next-power submodule inside `I ^ m` is the ideal-smul
submodule `I • ⊤`. -/
lemma pow_succ_submoduleOf_eq_ideal_smul_top
    {A : Type*} [CommRing A] (I : Ideal A) (m : ℕ) :
    ((I ^ (m + 1) : Ideal A).submoduleOf (I ^ m)) =
      I • (⊤ : Submodule A (I ^ m : Ideal A)) := by
  -- Rewrite `I ^ (m + 1)` as `I * I ^ m`, then use the standard membership test for `I • ⊤`.
  ext x
  simp [Submodule.submoduleOf, Submodule.mem_smul_top_iff, pow_succ']

/-- Helper for Lemma 10.64.3: the semilocal prime quotient inherits the expected algebra
structure over the localized residue ring `Rₚ / 𝔭Rₚ`. -/
noncomputable local instance semilocal_prime_quotient_residue_algebra :
    Algebra (Rₚ ⧸ map (algebraMap R Rₚ) 𝔭)
      (Sₚ ⧸ map (algebraMap S Sₚ) 𝔭S) := by
  let J₀ : Ideal Rₚ := map (algebraMap R Rₚ) 𝔭
  let J : Ideal Sₚ := map (algebraMap S Sₚ) 𝔭S
  have hle : J₀ ≤ Ideal.comap (algebraMap Rₚ Sₚ) J := by
    exact Ideal.map_le_iff_le_comap.mp <|
      le_of_eq (localized_prime_map_eq_semilocalized_prime
        (R := R) (S := S) (𝔭 := 𝔭))
  exact Ideal.Quotient.algebraQuotientOfLEComap hle

/-- Helper for Lemma 10.64.3: after applying the right tensor-unit equivalence
`Sₚ ⊗[Rₚ] Rₚ ≃ Sₚ`, the base change of the localized prime power becomes the corresponding
semilocal prime power. -/
lemma semilocal_power_ideal_baseChange_map_eq
    (m : ℕ) :
    Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
      (((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ).baseChange Sₚ) =
        ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
  let J₀m : Ideal Rₚ := (map (algebraMap R Rₚ) 𝔭) ^ m
  calc
    Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
        (J₀m.baseChange Sₚ)
        =
          Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
            (Submodule.span Sₚ (⇑(TensorProduct.mk Rₚ Sₚ Rₚ 1) '' ↑J₀m)) := by
              rw [Submodule.baseChange_eq_span, Submodule.map_coe]
    _ = Submodule.span Sₚ (((J₀m : Set Rₚ).image (algebraMap Rₚ Sₚ))) := by
          -- Proof comment: `rid` sends the generator `1 ⊗ x` to the localization image of `x`.
          rw [Submodule.map_span]
          congr 1
          ext x
          constructor <;> intro hx
          · rcases hx with ⟨y, hy, rfl⟩
            rcases hy with ⟨z, hz, rfl⟩
            refine ⟨z, hz, ?_⟩
            simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
          · rcases hx with ⟨y, hy, rfl⟩
            refine ⟨1 ⊗ₜ[Rₚ] y, ?_, ?_⟩
            · exact ⟨y, hy, rfl⟩
            · simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
    _ = map (algebraMap Rₚ Sₚ) J₀m := by
          rw [Ideal.map, Ideal.submodule_span_eq]
    _ = ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
          rw [Ideal.map_pow, localized_prime_map_eq_semilocalized_prime]

/-- Helper for Lemma 10.64.3: the semilocal power ideal is the flat base change of the localized
base prime power. -/
noncomputable def semilocal_power_ideal_baseChange_linearEquiv
    (m : ℕ) :
    Sₚ ⊗[Rₚ] ((map (algebraMap R Rₚ) 𝔭) ^ m : Ideal Rₚ) ≃ₗ[Sₚ]
      ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) := by
  let _ : Module.Flat Rₚ Sₚ :=
    (Module.flat_iff_of_isLocalization
      (R := R) (S := Rₚ) (p := Ideal.primeCompl 𝔭) (M := Sₚ)).mpr inferInstance
  let J₀m : Ideal Rₚ := (map (algebraMap R Rₚ) 𝔭) ^ m
  let e₁ :
      Sₚ ⊗[Rₚ] J₀m ≃ₗ[Sₚ] J₀m.baseChange Sₚ :=
    Submodule.toBaseChange.toLinearEquiv Sₚ J₀m
  let e₂ :
      J₀m.baseChange Sₚ ≃ₗ[Sₚ]
        Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
          (J₀m.baseChange Sₚ) :=
    J₀m.baseChange Sₚ |>.equivMapOfInjective
      (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
      (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).injective
  let e₃ :
      Submodule.map (TensorProduct.AlgebraTensorModule.rid Rₚ Sₚ Sₚ).toLinearMap
          (J₀m.baseChange Sₚ) ≃ₗ[Sₚ]
        ((map (algebraMap S Sₚ) 𝔭S) ^ m : Ideal Sₚ) :=
    LinearEquiv.ofEq _ _ <| by
      simpa [J₀m] using
        semilocal_power_ideal_baseChange_map_eq (R := R) (S := S) (𝔭 := 𝔭) m
  -- Proof comment: first identify the tensor with the literal base-change submodule, then push
  -- that submodule across the tensor-unit map to the semilocal power ideal.
  exact e₁.trans (e₂.trans e₃)


end Ideal

end
