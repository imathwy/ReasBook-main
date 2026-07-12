import Mathlib
import StacksProject_2024.Chap11.Lemma_11_4_4
import StacksProject_2024.Chap11.Theorem_11_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open Matrix

universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)

local notation "C" => centralizer k (B : Set A)

private theorem centralizer_commutes (b : B) (c : C) :
    Commute (b : A) (c : A) := by
  change (b : A) * (c : A) = (c : A) * (b : A)
  exact c.2 b b.2

section TensorProductSimplicity

variable {A' : Type v} [Ring A'] [Algebra k A'] [IsSimpleRing A']

/-- Helper for Lemma 11.7.2: centrality of a matrix algebra forces centrality of its division-ring
coefficients. -/
private lemma isCentral_of_matrix (n : ℕ) [NeZero n] (K : Type v) [DivisionRing K] [Algebra k K]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) K)] :
    Algebra.IsCentral k K := by
  -- Pull a central scalar matrix back to its diagonal entry in the coefficient division ring.
  refine ⟨fun x hx ↦ ?_⟩
  have hxM : scalar (Fin n) x ∈ (Subalgebra.center k K).map (scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) K ↦ M i i) ha).symm

/-- Helper for Lemma 11.7.2: tensoring on the left by a central division algebra preserves
simplicity. -/
private lemma tensorProduct_isSimple_of_simple_right_division
    {K : Type v} [DivisionRing K] [Algebra k K] [Algebra.IsCentral k K] :
    IsSimpleRing (K ⊗[k] A') := by
  -- Commute the factors to reuse the simple-right-factor theorem from Lemma 11.4.4.
  let h : IsSimpleRing (A' ⊗[k] K) :=
    isSimpleRing_tensorProduct_of_isSimpleRing (k := k) (A := A') (K := K)
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k K A').symm.toRingEquiv h

/-- Helper for Lemma 11.7.2: a finite-dimensional central simple left tensor factor makes the full
tensor product simple. -/
private theorem tensorProduct_isSimple_of_finite_central_left_factor
    {A₁ : Type v} [Ring A₁] [Algebra k A₁] [IsSimpleRing A₁]
    [FiniteDimensional k A₁] [Algebra.IsCentral k A₁] :
    IsSimpleRing (A₁ ⊗[k] A') := by
  -- Follow the source proof through a Wedderburn matrix presentation of the left factor.
  letI : IsArtinianRing A₁ := IsArtinianRing.of_finite k A₁
  obtain ⟨n, hn, K, hKdiv, hKalg, hKfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A₁
  letI : NeZero n := hn
  letI : DivisionRing K := hKdiv
  letI : Algebra k K := hKalg
  letI : Module.Finite k K := hKfinite
  letI : FiniteDimensional k K := inferInstance
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) K) := Algebra.IsCentral.of_algEquiv k A₁ _ e
  letI : Algebra.IsCentral k K := isCentral_of_matrix (k := k) n K
  have hTensor : IsSimpleRing (K ⊗[k] A') :=
    tensorProduct_isSimple_of_simple_right_division (k := k) (A' := A')
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hMatrix : IsSimpleRing (Matrix (Fin n) (Fin n) (K ⊗[k] A')) :=
    IsSimpleRing.matrix (Fin n) (K ⊗[k] A')
  have hmul : n * 1 = n := by
    simp
  let eA' : A' ≃ₐ[k] Matrix (Fin 1) (Fin 1) A' :=
    ((reindexAlgEquiv k A' finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      A₁ ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' :=
    Algebra.TensorProduct.congr e eA'
  let eKronecker :
      Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' ≃ₐ[k]
        Matrix (Fin n × Fin 1) (Fin n × Fin 1) (K ⊗[k] A') :=
    Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin 1) k k K A'
  let eProd : Fin n × Fin 1 ≃ Fin n :=
    finProdFinEquiv.trans (finCongr hmul)
  let eTensorMatrix :
      A₁ ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) (K ⊗[k] A') :=
    eTensor.trans <| eKronecker.trans <| reindexAlgEquiv k (K ⊗[k] A') eProd
  -- Transport simplicity back along the canonical tensor/matrix equivalence.
  exact IsSimpleRing.of_ringEquiv eTensorMatrix.symm.toRingEquiv hMatrix

end TensorProductSimplicity

variable [IsSimpleRing B] [Algebra.IsCentral k B]

/-- Helper for Lemma 11.7.2: the tensor product of the simple central algebra `B` with its
centralizer in `A` is simple. -/
private theorem centralizer_tensorProduct_isSimpleRing :
    IsSimpleRing (B ⊗[k] C) := by
  -- The source proof first makes the tensor-product domain simple using the finite-central tensor
  -- product criterion.
  letI : IsSimpleRing C := B.isSimpleRing_centralizer A
  exact tensorProduct_isSimple_of_finite_central_left_factor (k := k) (A' := C)

/-- Helper for Lemma 11.7.2: the tensor product `B ⊗[k] C_A(B)` has the same `k`-dimension as
`A`. -/
private theorem centralizer_tensorProduct_finrank_eq :
    Module.finrank k (B ⊗[k] C) = Module.finrank k A := by
  -- Rewrite the tensor-product dimension and then insert Theorem 11.7.1.
  calc
    Module.finrank k (B ⊗[k] C) = Module.finrank k B * Module.finrank k C := by
      rw [Module.finrank_tensorProduct]
    _ = Module.finrank k A := by
      simpa using (B.finrank_mul_finrank_centralizer A).symm

/-- Helper for Lemma 11.7.2: the canonical multiplication map from `B ⊗[k] C_A(B)` onto `A` is
surjective. -/
private theorem centralizer_tensorProduct_surjective :
    Function.Surjective
      (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := by
  let μ : B ⊗[k] C →ₐ[k] A :=
    lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)
  let f : (B ⊗[k] C) →ₗ[k] A := μ.toLinearMap
  haveI : IsSimpleRing (B ⊗[k] C) := centralizer_tensorProduct_isSimpleRing A B
  have h_inj : Function.Injective f := by
    -- Simplicity of the source forces the multiplication map to be injective.
    exact RingHom.injective μ.toRingHom
  have h_finrank : Module.finrank k (B ⊗[k] C) = Module.finrank k A := by
    -- The dimension comparison is exactly the centralizer dimension formula.
    exact centralizer_tensorProduct_finrank_eq A B
  -- Equal finite dimensions upgrade injectivity of the linear map to surjectivity.
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp h_inj

/- Domain sampling for Lemma 11.7.2.
- primary domain: tensor products of central simple algebras and centralizers of subalgebras;
- inspected owner declarations:
  `Subalgebra.finrank_mul_finrank_centralizer`,
  `Subalgebra.centralizer_centralizer_eq`,
  `Algebra.TensorProduct.lift`,
  `Algebra.TensorProduct.lift_tmul`;
- best owner abstraction: `Subalgebra.centralizer` on the subalgebra side, together with the
  canonical tensor-product multiplication map given directly by `Algebra.TensorProduct.lift`;
- primitive data: the subalgebra `B` and its centralizer `C_A(B)`;
- derived API: bijectivity of the canonical multiplication map and the resulting algebra
  equivalence;
- layer classification:
  `source-facing`: the algebra equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`;
  `core/canonical`: `Subalgebra.centralizer` and `Algebra.TensorProduct.lift`;
  `bridge/view`: the bijectivity theorem upgrading the canonical lift to an equivalence. -/

/- Lemma 11.7.2 is a `bridge/view` item: the source-facing statement is an explicit algebra
equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`, while the core owner map is the canonical tensor-product lift
`Algebra.TensorProduct.lift B.val C.val ...`. -/
-- Proof sketch: Theorem 11.7.1 gives the dimension identity
-- `[A : k] = [B : k] [C_A(B) : k]`, while Lemma 11.4.7 shows that `B ⊗[k] C_A(B)` is simple
-- because `B` is central simple over `k`. The canonical multiplication map is therefore injective,
-- and the dimension equality forces surjectivity.
/-- Lemma 11.7.2, owner form: the canonical multiplication map
`B ⊗[k] Subalgebra.centralizer k (B : Set A) →ₐ[k] A` is bijective. -/
@[stacks 074U]
theorem centralizerTensorProduct_bijective :
    Function.Bijective
      (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := by
  have h_inj :
      Function.Injective
        (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := by
    -- The domain is simple, so the canonical multiplication map has zero kernel.
    letI : IsSimpleRing (B ⊗[k] C) := centralizer_tensorProduct_isSimpleRing A B
    exact RingHom.injective _
  have h_surj :
      Function.Surjective
        (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := by
    -- Route correction: follow the source proof through equal dimensions, not a double-centralizer
    -- detour.
    exact centralizer_tensorProduct_surjective A B
  exact ⟨h_inj, h_surj⟩

/-- Lemma 11.7.2: if `A` is a finite central simple `k`-algebra and `B` is a simple central
`k`-subalgebra of `A`, then the canonical multiplication map identifies
`B ⊗[k] Subalgebra.centralizer k (B : Set A)` with `A`. -/
@[stacks 074U]
noncomputable def centralizerTensorProductAlgEquiv :
    B ⊗[k] C ≃ₐ[k] A :=
  AlgEquiv.ofBijective
    (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B))
    (centralizerTensorProduct_bijective A B)

@[simp]
theorem centralizerTensorProductAlgEquiv_tmul (b : B) (c : C) :
    centralizerTensorProductAlgEquiv A B (b ⊗ₜ[k] c) = (b : A) * c := by
  simp [centralizerTensorProductAlgEquiv]

end

end Subalgebra
