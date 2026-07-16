import stacks_proof.stacks_project.Chap10.Definition_10_43_1
import stacks_proof.stacks_project.Chap10.Lemma_10_25_2
import stacks_proof.stacks_project.Chap10.Lemma_10_43_2
import stacks_proof.stacks_project.Chap10.Lemma_10_44_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra
open scoped TensorProduct

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

local instance (p : minimalPrimes S) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.43.7 (Tag 07K2): if the left tensor factor is a field extension, then the
canonical map from tensoring with a product to the product of tensor factors is injective. -/
lemma piRightHom_injective_of_field_left
    {K : Type*} [Field K] [Algebra k K]
    {ι : Type*} (M : ι → Type*)
    [∀ i, CommRing (M i)] [∀ i, Algebra k (M i)] :
    Function.Injective (Algebra.TensorProduct.piRightHom k K K M) := by
  classical
  let ιK := Module.Free.ChooseBasisIndex k K
  let b : Module.Basis ιK k K := Module.Free.chooseBasis k K
  let g := TensorProduct.piRightHom k K K M
  have hg : Function.Injective g := by
    intro x y hxy
    -- Compare coefficients against a `k`-basis of `K` and reduce injectivity to each component.
    let z : K ⊗[k] (∀ i, M i) := x - y
    have hzero : g z = 0 := by
      rw [show z = x - y by rfl, map_sub, hxy, sub_self]
    let c : ιK →₀ ∀ i, M i := TensorProduct.equivFinsuppOfBasisLeft b z
    have hc : c = 0 := by
      apply Finsupp.ext
      intro i
      ext j
      let cj : ιK →₀ M j := c.mapRange (fun f ↦ f j) (by simp)
      -- Evaluating the tensor-to-product map at `j` produces the basis expansion in the `j`-th
      -- factor, so zero image forces all coefficients in that factor to vanish.
      have hrepr : z = (TensorProduct.equivFinsuppOfBasisLeft b).symm c := by
        simpa [c] using ((TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z).symm
      have hj_repr :
          g z j = cj.sum (fun i' m ↦ b i' ⊗ₜ[k] m) := by
        rw [hrepr]
        rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum]
        rw [Finsupp.sum_mapRange_index]
        · rw [Finsupp.sum, Finsupp.sum]
          simp [g]
        · intro a
          simp
      have hj_zero : cj.sum (fun i' m ↦ b i' ⊗ₜ[k] m) = 0 := by
        simpa [hj_repr] using congrArg (fun f ↦ f j) hzero
      have hcj : cj = 0 :=
        TensorProduct.sum_tmul_basis_left_eq_zero (ℬ := b) cj hj_zero
      simpa [cj] using congrArg (fun d : ιK →₀ M j ↦ d i) hcj
    have hz : z = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
      simpa [c] using hc
    exact sub_eq_zero.mp (by simpa [z] using hz)
  simpa [g] using hg

/-- Helper for Lemma 10.43.7 (Tag 07K2): the algebraic-closure base change of the product of the
minimal-prime localizations is reduced because it embeds into the product of the reduced tensor
factors. -/
lemma isReduced_algebraicClosure_tensor_minimalPrimeLocalizations
    (hlocal :
      ∀ p : minimalPrimes S,
        IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    IsReduced (AlgebraicClosure k ⊗[k] (∀ p : minimalPrimes S, Localization.AtPrime p.1)) := by
  let f := Algebra.TensorProduct.piRightHom k (AlgebraicClosure k) (AlgebraicClosure k)
    (fun p : minimalPrimes S ↦ Localization.AtPrime p.1)
  have hf : Function.Injective f := by
    -- The source proof uses that a field is a free module over the base field.
    simpa using
      piRightHom_injective_of_field_left (k := k) (K := AlgebraicClosure k)
        (fun p : minimalPrimes S ↦ Localization.AtPrime p.1)
  have hfactor :
      ∀ p : minimalPrimes S, IsReduced (AlgebraicClosure k ⊗[k] Localization.AtPrime p.1) :=
    fun p ↦ by
      let _ : IsGeometricallyReduced k (Localization.AtPrime p.1) := hlocal p
      infer_instance
  let _ : ∀ p : minimalPrimes S, IsReduced (AlgebraicClosure k ⊗[k] Localization.AtPrime p.1) :=
    hfactor
  -- Descend reducedness from the product of reduced tensor factors along the injective map `f`.
  exact isReduced_of_injective f hf

-- Source-facing theorem with owner abstraction `Algebra.IsGeometricallyReduced`.
-- Proof sketch: first use `Algebra.isReduced_of_isGeometricallyReduced` on each minimal-prime
-- localization; the explicit reducedness hypothesis `hS : IsReduced S` is needed to apply the
-- canonical embedding into the product of these localizations from Lemma `10.25.2`. After
-- tensoring that embedding with `AlgebraicClosure k`, flatness preserves injectivity, while each
-- tensor factor is reduced by the geometric reducedness hypothesis on the corresponding
-- localization. Therefore `AlgebraicClosure k ⊗[k] S` is reduced.
/-- Lemma 10.43.7 (Tag 07K2): if a `k`-algebra is reduced and the localizations at all of its
minimal prime ideals are geometrically reduced over `k`, then the algebra is geometrically reduced
over `k`. -/
@[stacks 07K2]
theorem isGeometricallyReduced_of_forall_minimalPrime_localization
    (hS : IsReduced S)
    (hlocal :
      ∀ p : minimalPrimes S,
        IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    IsGeometricallyReduced k S := by
  let _ : IsReduced S := hS
  let T := ∀ p : minimalPrimes S, Localization.AtPrime p.1
  let f : S →ₐ[k] T := IsScalarTower.toAlgHom k S T
  have hembed : Function.Injective f := by
    -- Lemma `10.25.2` gives the canonical embedding into the product of minimal-prime
    -- localizations once `S` is known to be reduced.
    simpa [f] using (algebraMap_embedding_into_product_of_fields (R := S)).1
  let _ : IsGeometricallyReduced k T := by
    -- The source proof first shows that the algebraic-closure base change of the product ring is
    -- reduced by embedding it into the product of the geometrically reduced local factors.
    exact ⟨isReduced_algebraicClosure_tensor_minimalPrimeLocalizations
      (k := k) (S := S) hlocal⟩
  -- Finally descend geometric reducedness along the injective canonical algebra map `S → T`.
  exact IsGeometricallyReduced.of_injective f hembed

end
