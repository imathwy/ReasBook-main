import Mathlib
import Serre.Chap06.Proposition_6_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {K : Type u} {ι : Type v} {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)] [IsAlgClosed K]
variable (π : ι → Rep K G)
variable [∀ i, FiniteDimensional K (π i)]

section CompleteFamily

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: on a finite index type, `finsum` agrees with the ordinary
`Finset.univ` sum. -/
lemma finsum_eq_sum_univ {α : Type*} [Fintype α] [DecidableEq α] (f : α → K) :
    (∑ᶠ a : α, f a) = Finset.univ.sum f := by
  classical
  let hf : Function.HasFiniteSupport f := Set.toFinite _
  rw [finsum_eq_sum f hf]
  -- Replace the support sum by a filtered univ sum, then drop the zero terms.
  change ∑ x ∈ (Function.support f).toFinite.toFinset, f x = Finset.univ.sum f
  have hs : (Function.support f).toFinite.toFinset = Finset.univ.filter (fun x : α => f x ≠ 0) := by
    ext x
    simp [Function.support]
  rw [hs, Finset.sum_filter_ne_zero]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: the trace of a block-diagonal map on a finite product is the
sum of the traces of its diagonal blocks. -/
lemma trace_piMap_eq_sum_trace {α : Type*} [Fintype α] [DecidableEq α]
    {M : α → Type*} [∀ a, AddCommGroup (M a)] [∀ a, Module K (M a)]
    [∀ a, Module.Free K (M a)] [∀ a, Module.Finite K (M a)]
    (f : ∀ a, M a →ₗ[K] M a) :
    LinearMap.trace K (∀ a, M a) (LinearMap.piMap f) = ∑ a, LinearMap.trace K (M a) (f a) := by
  let b : ∀ a, Module.Basis _ K (M a) := fun a ↦ Module.Free.chooseBasis K (M a)
  -- Compute the product trace in the sigma-indexed basis induced from the factor bases.
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis b)]
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sigma, LinearMap.piMap, LinearMap.toMatrix_apply]
  congr with a
  simpa [Matrix.trace, LinearMap.toMatrix_apply] using
    (LinearMap.trace_eq_matrix_trace K (b a) (f a)).symm

omit [Invertible (Nat.card G : K)] [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: left multiplication on the group algebra has trace `|G|`
times the coefficient at `1`. -/
lemma trace_lmul_groupAlgebra_eq_card_mul_coeff_one (v : K[G]) :
    LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) = (Nat.card G : K) * v 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : K) = (Fintype.card G : K) := by
    simp [Nat.card_eq_fintype_card]
  -- Evaluate the regular trace in the delta-function basis of `K[G]`.
  rw [show LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) =
      (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (Algebra.lmul K (K[G]) v)).trace by
    exact LinearMap.trace_eq_matrix_trace K Finsupp.basisSingleOne (Algebra.lmul K (K[G]) v)]
  rw [Matrix.trace, hcard]
  simp [LinearMap.toMatrix_apply]
  calc
    Finset.univ.sum (fun x : G => (((LinearMap.mul K K[G]) v) fun₀ | x => 1) x)
        = Finset.univ.sum (fun _ : G => v 1) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simpa using (MonoidAlgebra.mul_single_apply v (1 : K) x x)
    _ = (Fintype.card G : K) * v 1 := by
          simp

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: on a matrix algebra, the trace of left multiplication by `A`
is the matrix size times `trace A`. -/
lemma trace_lmul_matrix_eq_card_mul_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    LinearMap.trace K (Matrix n n K) (Algebra.lmul K (Matrix n n K) A) =
      (Fintype.card n : K) * A.trace := by
  let swapArgs : (n → n → K) ≃ₗ[K] n → n → K :=
    { toFun := fun f j i => f i j
      invFun := fun f j i => f i j
      left_inv := by intro f; funext i j; rfl
      right_inv := by intro f; funext i j; rfl
      map_add' := by intro f g; funext i j; rfl
      map_smul' := by intro c f; funext i j; rfl }
  let e : Matrix n n K ≃ₗ[K] n → n → K := (Matrix.ofLinearEquiv K).symm.trans swapArgs
  have hconj :
      e.conj (Algebra.lmul K (Matrix n n K) A) = LinearMap.piMap (fun _ : n => Matrix.toLin' A) := by
    -- View a matrix as its family of columns so left multiplication becomes block diagonal.
    ext M i j
    simp [e, swapArgs, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc
    LinearMap.trace K (Matrix n n K) (Algebra.lmul K (Matrix n n K) A)
        = LinearMap.trace K (n → n → K) (e.conj (Algebra.lmul K (Matrix n n K) A)) := by
            symm
            exact LinearMap.trace_conj' (Algebra.lmul K (Matrix n n K) A) e
    _ = LinearMap.trace K (n → n → K) (LinearMap.piMap (fun _ : n => Matrix.toLin' A)) := by
          rw [hconj]
    _ = ∑ _ : n, LinearMap.trace K (n → K) (Matrix.toLin' A) := by
          exact trace_piMap_eq_sum_trace (K := K) (f := fun _ : n => Matrix.toLin' A)
    _ = (Fintype.card n : K) * A.trace := by
          simp [Matrix.trace_toLin'_eq]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: after choosing a basis of `V`, the matrix of an endomorphism
has the same trace as the original linear map. -/
lemma trace_matrix_of_end {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) :
    let b := Module.Free.chooseBasis K V
    let e := LinearMap.toMatrixAlgEquiv b
    (e A).trace = LinearMap.trace K V A := by
  let b := Module.Free.chooseBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  -- Convert the matrix trace back to the original endomorphism through `toLin`.
  calc
    (e A).trace = LinearMap.trace K V ((Matrix.toLin b b) (e A)) := by
      exact (Matrix.trace_toLin_eq (A := e A) (b := b)).symm
    _ = LinearMap.trace K V A := by
      change LinearMap.trace K V (Matrix.toLinAlgEquiv b (e A)) = LinearMap.trace K V A
      rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

omit [IsAlgClosed K] in
/-- Helper for Proposition 6-6.2-2: for an endomorphism algebra, the trace of left multiplication
by `A` is `dim(V)` times `trace A`. -/
lemma trace_lmul_end_eq_finrank_mul_trace {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Module.End K V) :
    LinearMap.trace K (Module.End K V) (Algebra.lmul K (Module.End K V) A) =
      (Module.finrank K V : K) * LinearMap.trace K V A := by
  let b := Module.Free.chooseBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  have hconj :
      e.toLinearEquiv.conj (Algebra.lmul K (Module.End K V) A) =
        Algebra.lmul K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K) (e A) := by
    -- Transport left multiplication from endomorphisms to matrices through the basis algebra equivalence.
    ext f i j
    simpa using congrArg (fun g => g i j) (e.map_mul A (e.symm f))
  calc
    LinearMap.trace K (Module.End K V) (Algebra.lmul K (Module.End K V) A)
        = LinearMap.trace K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K)
            (e.toLinearEquiv.conj (Algebra.lmul K (Module.End K V) A)) := by
              symm
              exact LinearMap.trace_conj' (Algebra.lmul K (Module.End K V) A) e.toLinearEquiv
    _ = LinearMap.trace K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K)
          (Algebra.lmul K (Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K) (e A)) := by
          rw [hconj]
    _ = (Module.finrank K V : K) * (e A).trace := by
          simpa [Module.finrank_eq_card_chooseBasisIndex] using
            trace_lmul_matrix_eq_card_mul_trace (K := K) (A := e A)
    _ = (Module.finrank K V : K) * LinearMap.trace K V A := by
          simpa using congrArg (fun t => (Module.finrank K V : K) * t) (trace_matrix_of_end (K := K) A)

/-- Helper for Proposition 6-6.2-2: the product-side trace is the degree-weighted sum of the
factor traces. -/
lemma trace_lmul_familyEnd_eq_sum_finrank_mul_trace [Fintype ι] [DecidableEq ι]
    (f : Π i, Module.End K (π i)) :
    LinearMap.trace K (Π i, Module.End K (π i))
        (Algebra.lmul K (Π i, Module.End K (π i)) f) =
      ∑ i, (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (f i) := by
  have hlmul :
      Algebra.lmul K (Π i, Module.End K (π i)) f =
        LinearMap.piMap (fun i => Algebra.lmul K (Module.End K (π i)) (f i)) := by
    -- Left multiplication in the product algebra is coordinatewise.
    ext g i x
    rfl
  rw [hlmul, trace_piMap_eq_sum_trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact trace_lmul_end_eq_finrank_mul_trace (K := K) (A := f i)

/-- Helper for Proposition 6-6.2-2: the canonical Wedderburn equivalence conjugates left
multiplication by `v` on `K[G]` to left multiplication by `ρ̃[π] v` on the product endomorphism
algebra. -/
lemma familyEndAlgEquiv_conj_lmul
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (v : K[G]) :
    (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv.conj
        (Algebra.lmul K (K[G]) v) =
      Algebra.lmul K (Π i, Module.End K (π i)) ((ρ̃[π]) v) := by
  let e := irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete
  -- Transport multiplication through the algebra equivalence pointwise on the product.
  ext f i x
  change e (v * e.symm f) i x = (((ρ̃[π]) v * f) i) x
  rw [map_mul, AlgEquiv.apply_symm_apply]
  rfl

-- Proof sketch: apply the regular trace on `K[G]` to the shifted element `s⁻¹ * u`,
-- transport that trace across the Wedderburn equivalence from Proposition `6-6.2-1`,
-- and evaluate the target trace factorwise.
/-- Proposition 6-6.2-2: for a complete pairwise nonisomorphic family of irreducible
finite-dimensional representations over an algebraically closed field in which `|G|` is
invertible, the coefficient of `s` in the group-algebra element `u` is the normalized sum of the
traces of `ρ_i(s⁻¹)` composed with the `i`-th factor of the canonical Wedderburn image
`ρ̃[π] u`, weighted by the degrees `dim(π i)`. -/
theorem groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u : K[G]) (s : G) :
    u s =
      (Nat.card G : K)⁻¹ *
        ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
          LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i) := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype G := Fintype.ofFinite G
  let v : K[G] := MonoidAlgebra.of K G s⁻¹ * u
  let term : ι → K := fun i ↦
    (Module.finrank K (π i) : K) * LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i)
  have hcard : (Nat.card G : K) ≠ 0 := by
    exact (isUnit_iff_ne_zero).mp (isUnit_of_invertible (Nat.card G : K))
  have hv_coeff : v 1 = u s := by
    -- Shifting by `s⁻¹` moves the `s`-coefficient of `u` to the `1`-coefficient of `v`.
    simp [v, MonoidAlgebra.of_apply]
  have hv_image (i : ι) : ((ρ̃[π]) v) i = (π i).ρ s⁻¹ * (ρ̃[π]) u i := by
    -- Push the shifted group-algebra element through the product algebra hom.
    simp [v, familyEndAlgHom, MonoidAlgebra.of_apply]
  have htrace_term (i : ι) :
      (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (((ρ̃[π]) v) i) = term i := by
    -- After rewriting the image of `v`, the trace term matches the statement exactly.
    simp [term, hv_image i]
  have htrace : (Nat.card G : K) * u s = Finset.univ.sum term := by
    -- Compare the regular trace on `K[G]` with the factorwise trace on the product side.
    calc
      (Nat.card G : K) * u s = (Nat.card G : K) * v 1 := by rw [hv_coeff]
      _ = LinearMap.trace K (K[G]) (Algebra.lmul K (K[G]) v) := by
            symm
            exact trace_lmul_groupAlgebra_eq_card_mul_coeff_one (K := K) (G := G) v
      _ = LinearMap.trace K (Π i, Module.End K (π i))
            ((irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv.conj
              (Algebra.lmul K (K[G]) v)) := by
              symm
              exact LinearMap.trace_conj' (Algebra.lmul K (K[G]) v)
                (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv
      _ = LinearMap.trace K (Π i, Module.End K (π i))
            (Algebra.lmul K (Π i, Module.End K (π i)) ((ρ̃[π]) v)) := by
              rw [familyEndAlgEquiv_conj_lmul (π := π) hπ_pairwise hπ_complete v]
      _ = ∑ i, (Module.finrank K (π i) : K) * LinearMap.trace K (π i) (((ρ̃[π]) v) i) := by
              exact trace_lmul_familyEnd_eq_sum_finrank_mul_trace (π := π) ((ρ̃[π]) v)
      _ = Finset.univ.sum term := by
              refine Finset.sum_congr rfl fun i _ => htrace_term i
  have hfinsum : (∑ᶠ i : ι, term i) = Finset.univ.sum term :=
    finsum_eq_sum_univ (K := K) term
  -- Multiply the trace identity by `|G|⁻¹` to isolate the coefficient `u s`.
  calc
    u s = (1 : K) * u s := by
      simp
    _ = (Nat.card G : K)⁻¹ * ((Nat.card G : K) * u s) := by
      rw [show (1 : K) = (Nat.card G : K)⁻¹ * (Nat.card G : K) by
        rw [inv_mul_cancel₀ hcard]]
      rw [mul_assoc]
    _ = (Nat.card G : K)⁻¹ * Finset.univ.sum term := by
      rw [htrace]
    _ = (Nat.card G : K)⁻¹ * ∑ᶠ i : ι, term i := by
      rw [hfinsum]
    _ = (Nat.card G : K)⁻¹ *
          ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
            LinearMap.trace K (π i) ((π i).ρ s⁻¹ * (ρ̃[π]) u i) := by
      rfl

-- Proof sketch: apply Proposition `groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace` to the
-- element of `K[G]` obtained from `f` via the canonical inverse Wedderburn isomorphism, then use
-- `apply_symm_apply` to identify its canonical Wedderburn image with `f`.
/-- The inverse of the canonical Wedderburn isomorphism recovers the coefficient of `s` by the
normalized degree-weighted trace sum over the irreducible factors. -/
theorem irreducibleFamilyEndAlgEquiv_symm_apply
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (f : Π i, Module.End K (π i)) (s : G) :
    (irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete).symm f s =
      (Nat.card G : K)⁻¹ *
        ∑ᶠ i : ι, (Module.finrank K (π i) : K) *
          LinearMap.trace K (π i) ((π i).ρ s⁻¹ * f i) := by
  let e := irreducibleFamilyEndAlgEquiv π hπ_pairwise hπ_complete
  have hi : ∀ i, (ρ̃[π]) (e.symm f) i = f i := fun i ↦
    congrFun (e.apply_symm_apply f) i
  simpa [hi] using
    groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace π hπ_pairwise hπ_complete (e.symm f) s

end CompleteFamily

end

end Representation
