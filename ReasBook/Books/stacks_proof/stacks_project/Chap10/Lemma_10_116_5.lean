import StacksProject_2024.Chap10.Lemma_10_115_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable {K : Type w} [Field K] [Algebra k K]

/-- Helper for Lemma 10.116.5: a finite injective map from a polynomial algebra over a field
computes the Krull dimension of the target. -/
private lemma ringKrullDim_eq_of_finite_injective_polynomial_algebra
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A] {d : ℕ}
    (g : MvPolynomial (Fin d) F →ₐ[F] A)
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim A = d := by
  let _ : Algebra (MvPolynomial (Fin d) F) A := g.toAlgebra
  -- A finite algebra map is integral, so the target has the same Krull dimension as the source.
  have hg_integral : (algebraMap (MvPolynomial (Fin d) F) A).IsIntegral := by
    simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral
  let _ : Algebra.IsIntegral (MvPolynomial (Fin d) F) A :=
    algebraMap_isIntegral_iff.mp hg_integral
  have hdim :
      ringKrullDim (MvPolynomial (Fin d) F) = ringKrullDim A :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (by simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
  have hpoly : ringKrullDim (MvPolynomial (Fin d) F) = d := by
    -- Polynomial rings over fields have Krull dimension equal to the number of variables.
    simp
  exact hdim.symm.trans hpoly

/-- Helper for Lemma 10.116.5: tensoring a finite injective polynomial normalization map with a
field extension preserves injectivity after identifying the tensor source with a polynomial ring
over the larger field. -/
private lemma tensor_baseChange_polynomial_algHom_restrictScalars
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) :
    (AlgHom.restrictScalars k
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) =
      (Algebra.TensorProduct.map (AlgHom.id k K) g).comp
        ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) := by
  apply MvPolynomial.algHom_ext'
  · ext c
    -- Both maps send the coefficient field `K` to the left tensor factor.
    simp [MvPolynomial.algebraTensorAlgEquiv]
  · intro i
    -- On variables, the tensor/equivalence composite lands at `1 ⊗ g(X_i)`.
    simp

/-- Helper for Lemma 10.116.5: tensoring a finite injective polynomial normalization map with a
field extension preserves injectivity after identifying the tensor source with a polynomial ring
over the larger field. -/
private lemma tensor_baseChange_polynomial_algHom_injective
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) (hg_injective : Function.Injective g) :
    Function.Injective
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S) := by
  have hraw :
      Function.Injective
        ((Algebra.TensorProduct.map (AlgHom.id k K) g).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    have hmap :
        Function.Injective
          (Algebra.TensorProduct.map (AlgHom.id k K) g :
            K ⊗[k] MvPolynomial (Fin d) k →ₐ[k] K ⊗[k] S) := by
      -- Over a field, tensoring with `K` preserves injectivity of the normalization map.
      simpa using TensorProduct.map_injective_of_flat_flat
        (AlgHom.id k K).toLinearMap g.toLinearMap
        Function.injective_id hg_injective
    exact hmap.comp (MvPolynomial.algebraTensorAlgEquiv k K).symm.injective
  have hrestricted :
      Function.Injective
        ((AlgHom.restrictScalars k
          (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
            MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) :
          MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    simpa [tensor_baseChange_polynomial_algHom_restrictScalars (K := K) g] using hraw
  simpa using hrestricted

/-- Helper for Lemma 10.116.5: tensoring a finite polynomial normalization map with a field
extension preserves finiteness after identifying the tensor source with a polynomial ring over the
larger field. -/
private lemma tensor_baseChange_polynomial_algHom_finite
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) (hg_finite : AlgHom.Finite g) :
    AlgHom.Finite
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S) := by
  have hraw :
      AlgHom.Finite
        ((Algebra.TensorProduct.map (AlgHom.id k K) g).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    have hmap :
        AlgHom.Finite
          (Algebra.TensorProduct.map (AlgHom.id k K) g :
            K ⊗[k] MvPolynomial (Fin d) k →ₐ[k] K ⊗[k] S) := by
      -- Finiteness is stable under tensor base change along the field extension.
      simpa using RingHom.Finite.tensorProductMap
        (f := AlgHom.id k K) (g := g) (AlgHom.Finite.id k K) hg_finite
    have hequiv :
        AlgHom.Finite
          (((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom).restrictScalars k :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] MvPolynomial (Fin d) k) := by
      -- An algebra equivalence is finite, so precomposing with the polynomial/tensor equivalence
      -- keeps the normalization finite.
      simpa using RingEquiv.finite (MvPolynomial.algebraTensorAlgEquiv k K).symm.toRingEquiv
    exact AlgHom.Finite.comp hmap hequiv
  have hrestricted :
      AlgHom.Finite
        (AlgHom.restrictScalars k
          (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
            MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) := by
    simpa [tensor_baseChange_polynomial_algHom_restrictScalars (K := K) g] using hraw
  simpa using hrestricted

/-
Source/core/bridge triage:
* primary domain: Krull dimension of finite-type algebras over a field under scalar extension;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether-normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
    Lemma `10.115.4`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension` from Lemma `10.116.6`;
* layer: `bridge/view`, since the source-facing statement is a global equality for `ringKrullDim`,
  while the owner-level content lives in Noether normalization, integral invariance of Krull
  dimension, and the local topological-dimension comparison under field extension;
* primitive data vs derived API: no additional public data are primitive here beyond the field
  extension `k → K` and the finite-type `k`-algebra `S`. The equality itself is derived API and
  should remain a thin theorem rather than a new wrapper or packaged construction.
-/

-- Proof sketch: apply Noether normalization to the finite type `k`-algebra `S` to get a finite
-- injective map from a polynomial ring `k[y₁, …, y_d]` with `d = ringKrullDim S`. Base change this
-- map along `k → K` to obtain a finite injective map `K[y₁, …, y_d] → K ⊗[k] S`, then use the
-- polynomial-ring dimension computation over a field together with invariance of Krull dimension
-- under finite injective integral extensions.
/-- Lemma 10.116.5: if `S` is a finite type `k`-algebra and `K / k` is a field extension, then the
Krull dimension of `S` equals the Krull dimension of the base change `K ⊗[k] S`. -/
@[stacks 00P3]
theorem ringKrullDim_tensorProduct_eq_of_fieldExtension :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · haveI := hS
    haveI : Subsingleton (K ⊗[k] S) := inferInstance
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · haveI := hS
    obtain ⟨d, g, hg_injective, hg_finite⟩ := exists_finite_inj_algHom_of_fg k S
    let gK : MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i)
    have hSdim : ringKrullDim S = d :=
      ringKrullDim_eq_of_finite_injective_polynomial_algebra g hg_injective hg_finite
    have hgK_injective : Function.Injective gK := by
      -- Base change along the field extension preserves injectivity of the normalization map.
      simpa [gK] using tensor_baseChange_polynomial_algHom_injective (K := K) g hg_injective
    have hgK_finite : AlgHom.Finite gK := by
      -- The same base change also preserves finiteness of the normalization map.
      simpa [gK] using tensor_baseChange_polynomial_algHom_finite (K := K) g hg_finite
    have hKdim : ringKrullDim (K ⊗[k] S) = d :=
      ringKrullDim_eq_of_finite_injective_polynomial_algebra gK hgK_injective hgK_finite
    exact hSdim.trans hKdim.symm

end
