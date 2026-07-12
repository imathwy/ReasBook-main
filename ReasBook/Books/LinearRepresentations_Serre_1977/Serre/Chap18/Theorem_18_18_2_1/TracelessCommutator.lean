import Mathlib

/-!
# Traceless endomorphisms are sums of commutators

We prove that a trace-zero square matrix over a field (and hence a trace-zero endomorphism
of a finite-dimensional vector space) is a finite sum of additive commutators `A * B - B * A`.

The proof of the matrix statement goes by decomposing a traceless matrix `M` into:
* its off-diagonal part: each single-entry matrix `single i j c` with `i ≠ j` is a
  commutator, namely `single i i 1 * single i j c - single i j c * single i i 1`;
* its diagonal part: fixing `i₀`, each difference `single i i c - single i₀ i₀ c` is the
  commutator `single i i₀ c * single i₀ i 1 - single i₀ i 1 * single i i₀ c`, and the trace
  zero hypothesis lets us write the diagonal as a sum of such differences.
-/

noncomputable section

universe u x

namespace Representation

variable {k : Type u} [Field k] {n : Type x} [Fintype n] [DecidableEq n]

/-- The set of matrices expressible as a finite sum of additive commutators, bundled as an
additive subgroup of `Matrix n n k`. -/
private def commutatorSums (k : Type u) [Field k] (n : Type x) [Fintype n] [DecidableEq n] :
    AddSubgroup (Matrix n n k) where
  carrier := {M | ∃ L : List (Matrix n n k × Matrix n n k),
    M = (L.map fun ab ↦ ab.1 * ab.2 - ab.2 * ab.1).sum}
  zero_mem' := ⟨[], rfl⟩
  add_mem' := by
    rintro a b ⟨L₁, rfl⟩ ⟨L₂, rfl⟩
    exact ⟨L₁ ++ L₂, by simp⟩
  neg_mem' := by
    rintro a ⟨L, rfl⟩
    refine ⟨L.map Prod.swap, ?_⟩
    induction L with
    | nil => simp
    | cons p t ih =>
      simp only [List.map_cons, List.sum_cons, Prod.fst_swap, Prod.snd_swap]
      rw [← ih]
      abel

/-- An off-diagonal single-entry matrix is a sum of commutators. -/
private lemma single_mem_of_ne {i j : n} (hij : i ≠ j) (c : k) :
    Matrix.single i j c ∈ commutatorSums k n := by
  refine ⟨[(Matrix.single i i 1, Matrix.single i j c)], ?_⟩
  simp [Ne.symm hij]

/-- A difference of two diagonal single-entry matrices (with the same entry) is a sum of
commutators. -/
private lemma single_sub_single_mem (i j : n) (c : k) :
    Matrix.single i i c - Matrix.single j j c ∈ commutatorSums k n := by
  refine ⟨[(Matrix.single i j c, Matrix.single j i 1)], ?_⟩
  simp

/-- A traceless square matrix over a field is a sum of additive commutators. -/
theorem matrix_trace_zero_eq_sum_commutators {k : Type u} [Field k] {n : Type x} [Fintype n]
    [DecidableEq n] (M : Matrix n n k) (hM : Matrix.trace M = 0) :
    ∃ L : List (Matrix n n k × Matrix n n k),
      M = (L.map fun ab ↦ ab.1 * ab.2 - ab.2 * ab.1).sum := by
  suffices h : M ∈ commutatorSums k n from h
  cases isEmpty_or_nonempty n with
  | inl h =>
    have hM0 : M = 0 := by ext i j; exact h.elim i
    rw [hM0]
    exact zero_mem _
  | inr h =>
    obtain ⟨i₀⟩ := h
    have htr : ∑ i, M i i = 0 := hM
    -- the sum of the diagonal entries except `i₀` is the negative of the `i₀` entry
    have h1 : ∑ i ∈ Finset.univ.erase i₀, M i i = -M i₀ i₀ :=
      eq_neg_of_add_eq_zero_right <| by
        rw [Finset.add_sum_erase Finset.univ (fun i ↦ M i i) (Finset.mem_univ i₀), htr]
    -- pull a sum inside `Matrix.single i₀ i₀`
    have hsum : ∑ i ∈ Finset.univ.erase i₀, Matrix.single i₀ i₀ (M i i)
        = Matrix.single i₀ i₀ (∑ i ∈ Finset.univ.erase i₀, M i i) := by
      simp only [← Matrix.singleAddMonoidHom_apply]
      exact (map_sum _ _ _).symm
    -- rewrite the diagonal part as a sum of diagonal differences
    have hdiag : ∑ i, Matrix.single i i (M i i)
        = ∑ i ∈ Finset.univ.erase i₀,
            (Matrix.single i i (M i i) - Matrix.single i₀ i₀ (M i i)) := by
      rw [Finset.sum_sub_distrib, hsum, h1, ← Matrix.singleAddMonoidHom_apply, map_neg,
        sub_neg_eq_add, Matrix.singleAddMonoidHom_apply,
        Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀)]
    -- decompose `M` into off-diagonal singles and diagonal differences
    have hdecomp : M = (∑ p ∈ Finset.univ.offDiag, Matrix.single p.1 p.2 (M p.1 p.2))
        + ∑ i ∈ Finset.univ.erase i₀,
            (Matrix.single i i (M i i) - Matrix.single i₀ i₀ (M i i)) := by
      rw [← hdiag]
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      rw [← Finset.sum_product', ← Finset.diag_union_offDiag Finset.univ,
        Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, add_comm]
    rw [hdecomp]
    exact add_mem
      (sum_mem fun p hp ↦ single_mem_of_ne (Finset.mem_offDiag.mp hp).2.2 _)
      (sum_mem fun i _ ↦ single_sub_single_mem i i₀ _)

/-- A traceless endomorphism of a finite-dimensional vector space is a sum of commutators. -/
theorem end_trace_zero_eq_sum_commutators {k : Type u} [Field k] {V : Type x} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : Module.End k V)
    (hf : LinearMap.trace k V f = 0) :
    ∃ L : List (Module.End k V × Module.End k V),
      f = (L.map fun ab ↦ ab.1 * ab.2 - ab.2 * ab.1).sum := by
  let b := Module.finBasis k V
  let e : Module.End k V ≃ₐ[k] Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k :=
    LinearMap.toMatrixAlgEquiv b
  have htr : Matrix.trace (e f) = 0 := by
    have : e f = LinearMap.toMatrix b b f := rfl
    rw [this, ← LinearMap.trace_eq_matrix_trace k b f]
    exact hf
  obtain ⟨L, hL⟩ := matrix_trace_zero_eq_sum_commutators (e f) htr
  refine ⟨L.map fun ab ↦ (e.symm ab.1, e.symm ab.2), ?_⟩
  have hf' : f = e.symm (e f) := (e.symm_apply_apply f).symm
  rw [hf', hL, map_list_sum, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun ab _ ↦ by simp

end Representation

end
