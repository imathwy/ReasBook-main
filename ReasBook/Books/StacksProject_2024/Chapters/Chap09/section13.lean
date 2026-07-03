import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_13_1 (from Chap09) -/
/- Lemma 9.13.1: pairwise distinct multiplicative characters `χ₁, …, χₙ : G → L` of a monoid
with values in a field are linearly independent. This is the finite-family specialization of the
canonical mathlib theorem `linearIndependent_monoidHom`, which states that all multiplicative
characters `G →* L` are linearly independent as functions `G → L`; applying it to an injective
family `χ : Fin n → G →* L` gives the textbook statement. -/
recall linearIndependent_monoidHom

/-! ### Lemma_9_13_2 (from Chap09) -/
universe u v

/-
Domain-style sampling:
- primary domain: Dedekind linear independence of multiplicative characters and its specialization
  to power characters `e ↦ α ^ e`;
- sampled owner declarations:
  `linearIndependent_monoidHom`,
  `powersHom`,
  `Fintype.linearIndependent_iff`;
- best owner abstraction: `linearIndependent_monoidHom` is the canonical owner, while the
  textbook power-sum statement is the source-facing specialization obtained by composing that owner
  with the family `α : ι → L` through `powersHom`;
- primitive data vs. derived API:
  primitive data is the finite nonempty family `α : ι → L` together with injectivity;
  derived API is the character family `powersHom L ∘ α : ι → Multiplicative ℕ →* L`, its
  coercion to functions, and the nontrivial linear combination with all coefficients equal to `1`.

Source/core/bridge triage:
- `source-facing`: existence of an exponent with nonzero power-sum;
- `core/canonical`: `linearIndependent_monoidHom`;
- `bridge/view`: `powersHom L ∘ α`.
-/

/-- Lemma 9.13.2: for a nonempty finite family of pairwise distinct elements of a commutative
ring without zero divisors, some power-sum `∑ i, αᵢ^e` is nonzero. The source states this over a
field, but the canonical owner theorem `linearIndependent_monoidHom` already works over any
commutative domain. -/
-- Proof sketch: apply the canonical owner theorem `linearIndependent_monoidHom` to the
-- multiplicative characters `χ : ι → Multiplicative ℕ →* L` given by `powersHom L ∘ α`. The
-- coefficient family with every coefficient equal to `1` is nonzero because the index type is
-- nonempty, so linear independence yields an exponent where the corresponding power-sum does not
-- vanish.
theorem exists_power_sum_ne_zero
    {L : Type u} [CommRing L] [IsDomain L] {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ι → L) (hα : Function.Injective α) :
    ∃ e : ℕ, ∑ i, α i ^ e ≠ 0 := by
  let χ : ι → Multiplicative ℕ →* L := powersHom L ∘ α
  have hχ : LinearIndependent L fun i ↦ (χ i : Multiplicative ℕ → L) := by
    simpa [χ] using
      (linearIndependent_monoidHom (Multiplicative ℕ) L).comp χ
        (by simpa [χ] using ((powersHom L).injective.comp hα))
  have hsum_ne : ∑ i, (1 : L) • (χ i : Multiplicative ℕ → L) ≠ 0 := by
    intro hsum
    have hone := (Fintype.linearIndependent_iff.mp hχ) (fun _ ↦ (1 : L)) hsum
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact one_ne_zero (hone i)
  by_contra h
  apply hsum_ne
  ext e
  simpa [χ] using (not_exists.mp h e.toAdd)

/-! ### Lemma_9_13_3 (from Chap09) -/
universe u v w x

/-
Domain-style sampling:
- primary domain: Dedekind linear independence of families of algebra morphisms and their
  underlying linear/function realizations;
- sampled declarations:
  `linearIndependent_monoidHom`,
  `linearIndependent_algHom_toLinearMap`,
  `AlgHom.toLinearMap`,
  `LinearMap.ltoFun`;
- best owner abstraction: `linearIndependent_algHom_toLinearMap` is the canonical owner in the
  `AlgHom` domain; the present lemma is only the thin source-facing bridge from that owner to the
  same family viewed as plain functions;
- primitive data vs. derived API:
  primitive data is the family `σ : ι → A →ₐ[R] B` with injective indexing;
  derived API is the induced family of linear maps `fun i ↦ (σ i).toLinearMap` and the resulting
  linear independence of the underlying functions `fun i ↦ (σ i : A → B)`.

Source/core/bridge triage:
- `source-facing`: `linearIndependent_extension_morphisms`;
- `core/canonical`: `linearIndependent_algHom_toLinearMap`;
- `bridge/view`: `LinearMap.ltoFun`.
-/
recall linearIndependent_algHom_toLinearMap

/-- Lemma 9.13.3: pairwise distinct morphisms of `F`-extensions `σ₁, …, σₙ : K →ₐ[F] L` are
`L`-linearly independent as functions `K → L`; equivalently, every nontrivial finite
`L`-linear combination of the `σᵢ` is nonzero at some element of `K`. The source states this for
field extensions indexed by `Fin n`, but the canonical owner theorem already works for any
injectively indexed family of `R`-algebra morphisms from a semiring-algebra `A` to a commutative
domain `B`. -/
-- Proof sketch: apply the canonical owner theorem
-- `linearIndependent_algHom_toLinearMap` to the family of algebra morphisms, then pass from the
-- resulting family of linear maps to the same family seen as functions via `LinearMap.ltoFun`.
theorem linearIndependent_extension_morphisms
    {R : Type u} {A : Type v} {B : Type w} {ι : Type x}
    [CommSemiring R] [Semiring A] [Algebra R A]
    [CommRing B] [IsDomain B] [Algebra R B]
    (σ : ι → A →ₐ[R] B) (hσ : Function.Injective σ) :
    LinearIndependent B (fun i ↦ (σ i : A → B)) := by
  -- First move to the canonical owner theorem about algebra morphisms viewed as linear maps.
  have hσ' : LinearIndependent B (fun i ↦ (σ i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap R A B).comp σ hσ
  -- The forgetful map from linear maps to plain functions is injective, so its kernel is trivial.
  have hker : LinearMap.ker (LinearMap.ltoFun R A B B) = ⊥ := by
    ext f
    simp [LinearMap.ext_iff]
  -- Transport linear independence across that injective forgetful map and identify the functions.
  simpa using hσ'.map' (LinearMap.ltoFun R A B B) hker

/-! ### Lemma_9_13_4 (from Chap09) -/
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
