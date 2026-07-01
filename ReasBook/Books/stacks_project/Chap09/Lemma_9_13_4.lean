import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/- Domain-style sampling:
- primary domain: tensor products of field extensions and comparison maps to products indexed by
  algebra embeddings;
- sampled owner declarations: `Algebra.TensorProduct.commRight`,
  `Algebra.TensorProduct.productLeftAlgHom`, `Pi.algHom`, `Algebra.TensorProduct.piRight`,
  `Field.finSepDegree_eq_of_isAlgClosed`;
- best owner abstraction here: the single `L`-algebra homomorphism into the function-space
  product, assembled canonically from the pointwise `productLeftAlgHom`s via `Pi.algHom`. -/

/-- The `L`-algebra homomorphism induced by the comparison map
`α ⊗ β ↦ (σ(α)β)_σ`. -/
noncomputable def tensorProductToPiAlgHom : K ⊗[F] L →ₐ[L] ((K →ₐ[F] L) → L) :=
  Pi.algHom L (fun _ : K →ₐ[F] L ↦ L) fun σ ↦
    (Algebra.TensorProduct.productLeftAlgHom (AlgHom.id L L) σ).comp
      (Algebra.TensorProduct.commRight F L K).symm.toAlgHom

/-- The comparison algebra homomorphism sends `α ⊗ β` to the family `σ ↦ σ(α)β`. -/
-- Proof sketch: evaluate the canonical `Pi.algHom` at `σ`, unfold the swapped tensor-product
-- factor order, and compute `productLeftAlgHom` on a pure tensor.
theorem tensorProductToPiAlgHom_apply_tmul
    (α : K) (β : L) (σ : K →ₐ[F] L) :
    tensorProductToPiAlgHom (α ⊗ₜ[F] β) σ = σ α * β := by
  simp [tensorProductToPiAlgHom, mul_comm]

variable [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed L]

/-- Lemma 9.13.4: for a finite separable extension `K/F` and an algebraically closed extension
field `L/F`, the comparison `L`-algebra homomorphism
`K ⊗[F] L → ((K →ₐ[F] L) → L)` given by `α ⊗ β ↦ (σ(α)β)_σ` is bijective. -/
-- Proof sketch: compare the `L`-dimensions of source and target using finiteness of `K/F` and the
-- cardinality formula for `F`-embeddings into an algebraically closed field, then use Dedekind
-- linear independence of embeddings to show that the kernel is trivial.
theorem tensorProductToPiAlgHom_bijective :
    Function.Bijective (tensorProductToPiAlgHom : K ⊗[F] L → (K →ₐ[F] L) → L) := by
  let n := Module.finrank F K
  let b := Module.finBasis F K
  -- Reindex the embeddings by `Fin n` using the separable-degree count.
  have hEmbNat : Nat.card (K →ₐ[F] L) = n := by
    calc
      Nat.card (K →ₐ[F] L) = Field.finSepDegree F K := by
        symm
        simpa using (Field.finSepDegree_eq_of_isAlgClosed F K L)
      _ = Module.finrank F K := by
        simpa using (Field.finSepDegree_eq_finrank_of_isSeparable F K)
  let e : (K →ₐ[F] L) ≃ Fin n := Finite.equivFinOfCardEq hEmbNat
  -- Evaluate an `F`-linear map on the chosen basis of `K`.
  let evBasis : (K →ₗ[F] L) →ₗ[L] Fin n → L :=
    { toFun := fun f j ↦ f (b j)
      map_add' := by
        intro f g
        ext j
        simp
      map_smul' := by
        intro c f
        ext j
        simp }
  let M : Matrix (Fin n) (Fin n) L := fun i j ↦ e.symm i (b j)
  let S : K ⊗[F] L ≃ₗ[L] Fin n → L :=
    (Algebra.TensorProduct.commRight F L K).symm.toLinearEquiv.trans
      (Algebra.TensorProduct.basis L b).equivFun
  let T : ((K →ₐ[F] L) → L) ≃ₗ[L] Fin n → L := LinearEquiv.funCongrLeft L L e.symm
  let f : (Fin n → L) →ₗ[L] Fin n → L :=
    T.toLinearMap.comp
      (((tensorProductToPiAlgHom : K ⊗[F] L →ₐ[L] ((K →ₐ[F] L) → L)).toLinearMap).comp
        S.symm.toLinearMap)
  -- Dedekind linear independence survives evaluation on the basis because that evaluation map is
  -- injective.
  have hevBasis_inj : Function.Injective evBasis := by
    intro φ ψ hφψ
    ext x
    rw [← b.sum_repr x]
    simp_rw [map_sum, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z ↦ (b.repr x) i • z) (congrFun hφψ i)
  have hM_rows : LinearIndependent L M.row := by
    have hevBasis_ker : LinearMap.ker evBasis = ⊥ := LinearMap.ker_eq_bot.mpr hevBasis_inj
    have hEmb : LinearIndependent L (fun σ : K →ₐ[F] L ↦ evBasis (AlgHom.toLinearMap σ)) := by
      simpa using (linearIndependent_algHom_toLinearMap F K L).map' evBasis hevBasis_ker
    simpa [M, Matrix.row, evBasis] using hEmb.comp e.symm e.symm.injective
  have hM_unit : IsUnit M := (Matrix.linearIndependent_rows_iff_isUnit).mp hM_rows
  -- In basis coordinates, the comparison map is exactly multiplication by the evaluation matrix.
  have hf_eq : f = Matrix.toLin' M := by
    apply LinearMap.toMatrix'.injective
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp [f, T, S, M, tensorProductToPiAlgHom_apply_tmul]
  have hf_inj : Function.Injective f := by
    rw [hf_eq]
    exact (Matrix.mulVec_injective_iff_isUnit).2 hM_unit
  have hf_surj : Function.Surjective f := by
    rw [hf_eq]
    exact (Matrix.mulVec_surjective_iff_isUnit).2 hM_unit
  constructor
  · -- Injectivity follows after transporting the kernel statement through the coordinate changes.
    intro x y hxy
    apply S.injective
    apply hf_inj
    simpa [f] using congrArg T hxy
  · -- Surjectivity is the same coordinate argument, using that an invertible square matrix is onto.
    intro g
    obtain ⟨v, hv⟩ := hf_surj (T g)
    refine ⟨S.symm v, ?_⟩
    apply T.injective
    simpa [f] using hv

/-- The comparison map of Lemma 9.13.4 as an explicit `L`-algebra equivalence. -/
noncomputable def tensorProductToPiAlgEquiv : K ⊗[F] L ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgEquiv.ofBijective
    tensorProductToPiAlgHom
    tensorProductToPiAlgHom_bijective
