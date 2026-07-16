import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_25_1
import stacks_proof.stacks_project.Chap10.Definition_10_66_1
import stacks_proof.stacks_project.Chap10.Lemma_10_40_4
import stacks_proof.stacks_project.Chap10.Lemma_10_42_3
import stacks_proof.stacks_project.Chap10.Lemma_10_43_6
import stacks_proof.stacks_project.Chap10.Lemma_10_66_2
import stacks_proof.stacks_project.Chap10.Lemma_10_66_13
import stacks_proof.stacks_project.Chap10.Lemma_10_66_4
import stacks_proof.stacks_project.Chap10.Lemma_10_66_15
import stacks_proof.stacks_project.Chap10.Lemma_10_66_16

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

/- The finite-extension part of the source proof reduces weak association of a field tensor product
to weak association of a finite direct sum of copies of the original module. The next helpers
package exactly that direct-sum descent. -/
/-- Helper for Lemma 10.66.19: weakly associated primes of a binary product are exactly the union
of the weakly associated primes of the two factors. -/
theorem weaklyAssociatedPrimes_prod
    {M' : Type*} [AddCommGroup M'] [Module R M']
    {M'' : Type*} [AddCommGroup M''] [Module R M''] :
    weaklyAssociatedPrimes R (M' × M'') =
      weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' := by
  -- Compare the split exact sequence `0 → M' → M' × M'' → M'' → 0` with Lemma `10.66.4`.
  refine
    (weaklyAssociatedPrimes.subset_union_of_exact
      (R := R) (M' := M') (M := M' × M'') (M'' := M'')
      (f := LinearMap.inl R M' M'') (g := LinearMap.snd R M' M'')
      LinearMap.inl_injective Function.Exact.inl_snd).antisymm ?_
  rw [Set.union_subset_iff]
  exact
    ⟨weaklyAssociatedPrimes.subset_of_injective
        (R := R) (f := LinearMap.inl R M' M'') LinearMap.inl_injective,
      weaklyAssociatedPrimes.subset_of_injective
        (R := R) (f := LinearMap.inr R M' M'') LinearMap.inr_injective⟩

/-- Helper for Lemma 10.66.19: finitely supported functions on `Option ι` split into their
distinguished `none` coordinate and the remaining `some` coordinates. -/
noncomputable def optionFinsuppLinearEquiv
    {ι : Type*} :
    (Option ι →₀ M) ≃ₗ[R] M × (ι →₀ M) where
  toFun f := (f none, f.some)
  invFun fg := (fg.2.embDomain Function.Embedding.some).update none fg.1
  left_inv f := by
    -- Check equality coordinatewise on the distinguished coordinate and on the ordinary ones.
    ext a
    cases a with
    | none =>
        simp [Finsupp.update]
    | some i =>
        simp [Finsupp.update]
  right_inv fg := by
    -- The inverse reconstructs the `none` coordinate together with the original tail.
    apply Prod.ext
    · simp [Finsupp.update]
    · ext i
      simp [Finsupp.update]
  map_add' f g := by
    -- Both coordinates are computed pointwise, so additivity is immediate.
    apply Prod.ext
    · simp
    · ext i
      simp
  map_smul' a f := by
    -- The same pointwise description gives compatibility with the `R`-action.
    apply Prod.ext
    · simp
    · ext i
      simp

/-- Helper for Lemma 10.66.19: for a finite index type, a weakly associated prime of a finitely
supported direct sum of copies of `M` is already weakly associated to one copy of `M`. -/
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp_finite
    {ι : Type*} [Finite ι] :
    weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M := by
  classical
  refine
    Finite.induction_empty_option
      (P := fun ι ↦ weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M)
      ?_ ?_ ?_ ι
  · intro α β e h p hp
    -- Reindexing a finitely supported family does not change its weakly associated primes.
    have hEq :
        weaklyAssociatedPrimes R (α →₀ M) = weaklyAssociatedPrimes R (β →₀ M) := by
      simpa using
        (LinearEquiv.weaklyAssociatedPrimes_eq
          (Finsupp.mapDomain.linearEquiv M R e))
    rw [← hEq] at hp
    exact h hp
  · intro p hp
    -- The empty direct sum is the zero module, hence it has no weakly associated primes.
    have hEmpty : weaklyAssociatedPrimes R (PEmpty →₀ M) = ∅ :=
      weaklyAssociatedPrimes.eq_empty_of_subsingleton
    rw [hEmpty] at hp
    exact hp.elim
  · intro α _ h p hp
    -- Split the `Option α`-indexed direct sum into one copy of `M` and the tail indexed by `α`.
    have hEq :
        weaklyAssociatedPrimes R (Option α →₀ M) =
          weaklyAssociatedPrimes R (M × (α →₀ M)) := by
      simpa using
        (LinearEquiv.weaklyAssociatedPrimes_eq
          (optionFinsuppLinearEquiv (R := R) (M := M) (ι := α)))
    have hp' : p ∈ weaklyAssociatedPrimes R (M × (α →₀ M)) := by
      rw [← hEq]
      exact hp
    have hpUnion :
        p ∈ weaklyAssociatedPrimes R M ∪ weaklyAssociatedPrimes R (α →₀ M) := by
      simpa [weaklyAssociatedPrimes_prod (R := R) (M' := M) (M'' := α →₀ M)] using hp'
    rcases hpUnion with hpM | hpTail
    · exact hpM
    · exact h hpTail

/-- Helper for Lemma 10.66.19: weak association for an arbitrary finitely supported direct sum of
copies of `M` descends to weak association of `M` by restricting a witness to its finite support. -/
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp
    {ι : Type*} :
    weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M := by
  classical
  intro p hp
  rw [mem_weaklyAssociatedPrimes_iff] at hp
  rcases hp with ⟨f, hf⟩
  let s : Set ι := f.support
  let f' : s →₀ M := Finsupp.subtypeDomain (· ∈ s) f
  have hsFinite : Finite s := by
    classical
    exact Set.toFinite _
  let fEmb : (s →₀ M) →ₗ[R] (ι →₀ M) :=
    Finsupp.lmapDomain M R (Subtype.val : s → ι)
  have hfEmb_injective : Function.Injective fEmb := by
    exact
      (Finsupp.leftInverse_lcomapDomain_mapDomain
        (R := R) (M := M) (Subtype.val : s → ι) Subtype.val_injective).injective
  have hfEmb_apply : fEmb f' = f := by
    -- Restricting `f` to its support and extending again recovers `f`.
    have hExtend :
        Finsupp.embDomain (Function.Embedding.subtype fun i ↦ i ∈ s) f' = f := by
      simpa [Finsupp.extendDomain_eq_embDomain_subtype, s, f'] using
        (Finsupp.extendDomain_subtypeDomain (P := fun i ↦ i ∈ s) f
          (by
            intro i hi
            simpa [s] using hi))
    calc
      fEmb f' =
          Finsupp.embDomain (Function.Embedding.subtype fun i ↦ i ∈ s) f' := by
            simp [fEmb, Finsupp.lmapDomain_apply, Finsupp.embDomain_eq_mapDomain]
      _ = f := hExtend
  have hf' :
      p ∈ weaklyAssociatedPrimes R (s →₀ M) := by
    rw [mem_weaklyAssociatedPrimes_iff]
    refine ⟨f', ?_⟩
    have hminimal_emb :
        p ∈ (Ideal.torsionOf R (ι →₀ M) (fEmb f')).minimalPrimes := by
      simpa [hfEmb_apply] using hf
    have htorsion :
        Ideal.torsionOf R (ι →₀ M) (fEmb f') =
          Ideal.torsionOf R (s →₀ M) f' := by
      simpa [fEmb] using
        (weaklyAssociatedPrimes.Ideal.torsionOf_map_eq_of_injective
          (R := R) (f := fEmb) hfEmb_injective f')
    simpa [htorsion] using hminimal_emb
  letI : Finite s := hsFinite
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp_finite
      (R := R) (M := M) hf'

/-- Helper for Lemma 10.66.19: if the canonical owner base change `Mₖ`, regarded as an
`R`-module, has a weakly associated prime `p`, then `p` is already weakly associated to `M`. -/
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
    {p : Ideal R} (hp : p ∈ weaklyAssociatedPrimes R Mₖ) :
    p ∈ weaklyAssociatedPrimes R M := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex k K) k K :=
    Module.Basis.ofVectorSpace k K
  let eRing :
      Rₖ ≃ₗ[R] (Module.Basis.ofVectorSpaceIndex k K →₀ R) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (A := R) (R := k) (V := K) b
  let eModule :
      Mₖ ≃ₗ[R] ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) :=
    LinearEquiv.rTensor M eRing
  let eFinsupp :
      ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) ≃ₗ[R]
        (Module.Basis.ofVectorSpaceIndex k K →₀ M) :=
    TensorProduct.finsuppScalarLeft R M (Module.Basis.ofVectorSpaceIndex k K)
  have hEqModule :
      weaklyAssociatedPrimes R Mₖ =
        weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) := by
    simpa [eModule] using LinearEquiv.weaklyAssociatedPrimes_eq eModule
  have hpTensor :
      p ∈ weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) := by
    -- Re-express the owner base change by expanding the `K`-factor against a vector-space basis.
    rw [← hEqModule]
    exact hp
  have hEqFinsupp :
      weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) =
        weaklyAssociatedPrimes R (Module.Basis.ofVectorSpaceIndex k K →₀ M) := by
    simpa [eFinsupp] using LinearEquiv.weaklyAssociatedPrimes_eq eFinsupp
  have hpFinsupp :
      p ∈ weaklyAssociatedPrimes R (Module.Basis.ofVectorSpaceIndex k K →₀ M) := by
    -- Tensoring with the free module `ι →₀ R` is the finitely supported direct sum of copies of `M`.
    rw [← hEqFinsupp]
    exact hpTensor
  -- The earlier direct-sum descent now removes the remaining basis index set.
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp
      (R := R) (M := M) hpFinsupp

end
