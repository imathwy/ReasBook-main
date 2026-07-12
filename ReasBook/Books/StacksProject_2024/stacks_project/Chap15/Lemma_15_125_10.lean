import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Bezout

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling:
- primary domain: unimodular rows over Bézout domains and their completion to invertible matrices;
- sampled owner declarations:
  `IsBezout`,
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`,
  `Matrix.GL`;
- best owner abstraction: `Matrix.GL (Fin (n + 1)) R` for the completion object, with
  `Fintype.linearCombination R f` as the canonical core map behind the unit-ideal hypothesis;
- primitive data: a finite row `f : Fin (n + 1) → R`;
- derived API: the condition that `f` generates the unit ideal and the resulting invertible
  completion with first row `f`, indexed canonically by `0`, together with the operational
  surjective-`linearCombination` bridge;
- source/core/bridge triage:
  `source-facing`: completion of a unimodular row to an invertible square matrix;
  `core/canonical`: `Matrix.GL (Fin (n + 1)) R` and `Fintype.linearCombination R f`;
  `bridge/view`: `Ideal.span (Set.range f) = ⊤`, via
  `span_range_eq_top_iff_surjective_fintypeLinearCombination`. -/

section

open Matrix

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.125.10: if a finite family generates a nonzero ideal, then that ideal has
a nonzero generator and the family factors through a unimodular normalized row. -/
lemma exists_nonzero_generator_factorization_of_span_range_ne_bot [IsDomain R] [IsBezout R] {m : ℕ}
    (g : Fin (m + 1) → R) (hbot : Ideal.span (Set.range g) ≠ ⊥) :
    ∃ d : R, ∃ u : Fin (m + 1) → R,
      (∀ i, g i = d * u i) ∧
      Ideal.span (Set.range g) = Ideal.span ({d} : Set R) ∧
      d ≠ 0 ∧
      Ideal.span (Set.range u) = ⊤ := by
  let I : Ideal R := Ideal.span (Set.range g)
  have hIfg : I.FG := by
    simpa [I] using (Submodule.fg_span (Set.finite_range g) : (Ideal.span (Set.range g)).FG)
  letI : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hIfg
  let d : R := Submodule.IsPrincipal.generator I
  have hIspan : I = Ideal.span ({d} : Set R) := by
    -- The principal-generator owner rewrites the span to a singleton ideal.
    simpa [I, d] using (Ideal.span_singleton_generator I).symm
  have hd_ne_zero : d ≠ 0 := by
    intro hd
    have hIbot : I = ⊥ := by
      rw [hIspan, hd]
      simp
    exact hbot (by simpa [I] using hIbot)
  have hdiv : ∀ i, d ∣ g i := by
    intro i
    have hgi : g i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [hIspan] at hgi
    simpa [Ideal.mem_span_singleton] using hgi
  choose u hu using hdiv
  have hfactor : ∀ i, g i = d * u i := by
    intro i
    exact hu i
  have hd_mem : d ∈ I := by
    -- The chosen generator lies in its own principal ideal.
    simpa [I, d] using (Submodule.IsPrincipal.generator_mem I)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R) (v := g) (x := d)).mp hd_mem
  have hu_one :
      ∑ i, c i * u i = 1 := by
    -- Cancel the nonzero generator after rewriting the combination through the factorization.
    apply mul_left_cancel₀ hd_ne_zero
    calc
      d * (∑ i, c i * u i) = ∑ i, d * (c i * u i) := by
        rw [Finset.mul_sum]
      _ = ∑ i, c i * (d * u i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = ∑ i, c i * g i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hfactor i]
      _ = d := by
        simpa [smul_eq_mul] using hc
      _ = d * 1 := by ring
  have hu_top : Ideal.span (Set.range u) = ⊤ := by
    -- The normalized row is unimodular because the generator itself is a combination of the row.
    exact (Ideal.eq_top_iff_one _).2 <|
      (Submodule.mem_span_range_iff_exists_fun (R := R) (v := u) (x := (1 : R))).2
        ⟨c, by simpa [smul_eq_mul] using hu_one⟩
  exact ⟨d, u, hfactor, hIspan, hd_ne_zero, hu_top⟩

/-- Helper for Lemma 15.125.10: replacing the initial part of a `snoc` row by a generator of its
span only changes the ambient span to the corresponding two-generated ideal. -/
lemma span_range_snoc_eq_span_pair_of_init_span_eq {m : ℕ}
    (g : Fin (m + 1) → R) (a d : R)
    (hspan : Ideal.span (Set.range g) = Ideal.span ({d} : Set R)) :
    Ideal.span (Set.range (Fin.snoc g a)) = Ideal.span ({d, a} : Set R) := by
  -- We compare the two ideals by inclusion, using the canonical embedding of the prefix into the
  -- `snoc` row and the fact that `a` appears at the final index.
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last =>
        -- The new last entry is exactly `a`.
        exact Ideal.subset_span (by simp)
    | cast i =>
        -- Prefix entries already lie in the span of `d`, hence in the larger two-generated ideal.
        have hgi : g i ∈ Ideal.span ({d} : Set R) := by
          rw [← hspan]
          exact Ideal.subset_span ⟨i, rfl⟩
        have hpair_le : Ideal.span ({d} : Set R) ≤ Ideal.span ({d, a} : Set R) := by
          refine Ideal.span_mono ?_
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hx]
        simpa [Fin.snoc_castSucc] using hpair_le hgi
  ·
    have hprefix_subset : Set.range g ⊆ Set.range (Fin.snoc g a) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castSucc i, by simp [Fin.snoc_castSucc]⟩
    have hd : d ∈ Ideal.span (Set.range (Fin.snoc g a)) := by
      -- Transport the generator `d` through the prefix inclusion into the larger span.
      have hd_prefix : d ∈ Ideal.span (Set.range g) := by
        rw [hspan]
        exact Ideal.subset_span (by simp)
      exact (Ideal.span_mono hprefix_subset) hd_prefix
    refine Ideal.span_le.2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hd
    · exact Ideal.subset_span ⟨Fin.last (m + 1), by simp [Fin.snoc_last]⟩

/-- Helper for Lemma 15.125.10: pad an invertible matrix by a final basis vector without changing
its first row. -/
lemma exists_padded_gl_fixing_last_basis {m : ℕ}
    (A : GL (Fin (m + 1)) R) :
    ∃ B : GL (Fin (m + 2)) R,
      B 0 = Fin.snoc (A 0) 0 ∧
      B (Fin.last (m + 1)) = Fin.snoc (fun _ : Fin (m + 1) ↦ 0) 1 := by
  let e : Fin (m + 1) ⊕ Fin 1 ≃ Fin (m + 2) := finSumFinEquiv
  let M : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin 1) R :=
    Matrix.fromBlocks (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 0 1
  have hAdet : IsUnit ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) R).det) := by
    -- The existing completion `A` is already a unit matrix, so its determinant is a unit.
    exact (Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R)).1 ⟨A, rfl⟩
  have hMdet : IsUnit M.det := by
    -- The block diagonal determinant is the determinant of `A` times `1`.
    dsimp [M]
    rw [Matrix.det_fromBlocks_zero₁₂]
    simpa using IsUnit.mul hAdet (isUnit_one : IsUnit (1 : R))
  rcases (Matrix.isUnit_iff_isUnit_det M).2 hMdet with ⟨U, hU⟩
  let B : GL (Fin (m + 2)) R :=
    Units.map (Matrix.reindexAlgEquiv R R e).toMonoidHom U
  refine ⟨B, ?_, ?_⟩
  · -- Reading the first row of the reindexed block matrix gives the padded original first row.
    ext j
    cases j using Fin.lastCases with
    | last =>
        have hzero : e.symm 0 = Sum.inl (0 : Fin (m + 1)) := by
          apply e.injective
          simpa [e, Fin.castAdd]
        have hlast : e.symm (Fin.last (m + 1)) = Sum.inr (0 : Fin 1) := by
          apply e.injective
          simpa [e, Fin.natAdd, Fin.last]
        rw [show ((B : Matrix (Fin (m + 2)) (Fin (m + 2)) R) 0 (Fin.last (m + 1))) =
            Matrix.reindex e e (↑U) 0 (Fin.last (m + 1)) by rfl]
        rw [hU]
        simp [e, M, Matrix.reindex_apply, hzero, hlast]
    | cast j =>
        have hzero : e.symm 0 = Sum.inl (0 : Fin (m + 1)) := by
          apply e.injective
          simpa [e, Fin.castAdd]
        have hcast : e.symm (Fin.castSucc j) = Sum.inl j := by
          apply e.injective
          simpa [e, Fin.castAdd]
        rw [show ((B : Matrix (Fin (m + 2)) (Fin (m + 2)) R) 0 (Fin.castSucc j)) =
            Matrix.reindex e e (↑U) 0 (Fin.castSucc j) by rfl]
        rw [hU]
        simp [e, M, Matrix.reindex_apply, hzero, hcast]
  · -- The last row is the final basis vector because the lower-right block is `1`.
    ext j
    cases j using Fin.lastCases with
    | last =>
        have hlast : e.symm (Fin.last (m + 1)) = Sum.inr (0 : Fin 1) := by
          apply e.injective
          simpa [e, Fin.natAdd, Fin.last]
        rw [show ((B : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
            (Fin.last (m + 1)) (Fin.last (m + 1))) =
            Matrix.reindex e e (↑U) (Fin.last (m + 1)) (Fin.last (m + 1)) by rfl]
        rw [hU]
        simp [e, M, Matrix.reindex_apply, hlast]
    | cast j =>
        have hlast : e.symm (Fin.last (m + 1)) = Sum.inr (0 : Fin 1) := by
          apply e.injective
          simpa [e, Fin.natAdd, Fin.last]
        have hcast : e.symm (Fin.castSucc j) = Sum.inl j := by
          apply e.injective
          simpa [e, Fin.castAdd]
        rw [show ((B : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
            (Fin.last (m + 1)) (Fin.castSucc j)) =
            Matrix.reindex e e (↑U) (Fin.last (m + 1)) (Fin.castSucc j) by rfl]
        rw [hU]
        simp [e, M, Matrix.reindex_apply, hlast, hcast, Fin.snoc_castSucc]

/-- Helper for Lemma 15.125.10: multiplying the endpoint Bézout row by the padded inductive
completion yields the expected scaled prefix together with the unchanged last entry. -/
lemma first_row_mul_endpoint_padded {m : ℕ}
    (L B : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (d t : R) (u : Fin (m + 1) → R)
    (hL : L 0 = Fin.snoc (Fin.cons d (fun _ : Fin m ↦ 0)) t)
    (hB0 : B 0 = Fin.snoc u 0)
    (hBlast : B (Fin.last (m + 1)) = Fin.snoc (fun _ : Fin (m + 1) ↦ 0) 1) :
    (L * B) 0 = Fin.snoc (fun i ↦ d * u i) t := by
  -- Expand the product row once and split the sum into the `0`, middle, and `last` indices.
  ext j
  cases j using Fin.lastCases with
  | last =>
      -- At the last column, only the `0` and `last` summands can survive.
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
      have hmiddle :
          ∑ x : Fin m,
              L 0 x.succ.castSucc * B x.succ.castSucc (Fin.last (m + 1)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxzero :
            ((Fin.snoc (Fin.cons d (fun _ : Fin m ↦ 0)) t : Fin (m + 2) → R) x.succ.castSucc) = 0 := by
          rw [Fin.snoc_castSucc]
          simp [Fin.cons_succ]
        rw [hL, hxzero, zero_mul]
      have hLzero : L 0 (Fin.castSucc 0) = d := by
        rw [hL, Fin.snoc_castSucc, Fin.cons_zero]
      have hLlast : L 0 (Fin.last (m + 1)) = t := by
        rw [hL, Fin.snoc_last]
      have hB0last : B (Fin.castSucc 0) (Fin.last (m + 1)) = 0 := by
        have hrow := congrArg (fun r ↦ r (Fin.last (m + 1))) hB0
        simpa [Fin.snoc_last] using hrow
      have hBlastlast : B (Fin.last (m + 1)) (Fin.last (m + 1)) = 1 := by
        have hrow := congrArg (fun r ↦ r (Fin.last (m + 1))) hBlast
        simpa [Fin.snoc_last] using hrow
      rw [hmiddle]
      calc
        L 0 (Fin.castSucc 0) * B (Fin.castSucc 0) (Fin.last (m + 1)) + 0 +
            L 0 (Fin.last (m + 1)) * B (Fin.last (m + 1)) (Fin.last (m + 1))
            = d * 0 + 0 + t * 1 := by rw [hLzero, hB0last, hLlast, hBlastlast]
        _ = t := by simp
        _ = (Fin.snoc (fun i ↦ d * u i) t : Fin (m + 2) → R) (Fin.last (m + 1)) := by
          simp [Fin.snoc_last]
  | cast j =>
      -- On a prefix column, the last basis row vanishes and only the `0` summand remains.
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
      have hmiddle :
          ∑ x : Fin m,
              L 0 x.succ.castSucc * B x.succ.castSucc j.castSucc = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxzero :
            ((Fin.snoc (Fin.cons d (fun _ : Fin m ↦ 0)) t : Fin (m + 2) → R) x.succ.castSucc) = 0 := by
          rw [Fin.snoc_castSucc]
          simp [Fin.cons_succ]
        rw [hL, hxzero, zero_mul]
      have hLzero : L 0 (Fin.castSucc 0) = d := by
        rw [hL, Fin.snoc_castSucc, Fin.cons_zero]
      have hLlast : L 0 (Fin.last (m + 1)) = t := by
        rw [hL, Fin.snoc_last]
      have hB0cast : B (Fin.castSucc 0) j.castSucc = u j := by
        have hrow := congrArg (fun r ↦ r j.castSucc) hB0
        simpa [Fin.snoc_castSucc] using hrow
      have hBlastcast : B (Fin.last (m + 1)) j.castSucc = 0 := by
        have hrow := congrArg (fun r ↦ r j.castSucc) hBlast
        simpa [Fin.snoc_castSucc] using hrow
      rw [hmiddle]
      calc
        L 0 (Fin.castSucc 0) * B (Fin.castSucc 0) j.castSucc + 0 +
            L 0 (Fin.last (m + 1)) * B (Fin.last (m + 1)) j.castSucc
            = d * u j + 0 + t * 0 := by rw [hLzero, hB0cast, hLlast, hBlastcast]
        _ = d * u j := by simp
        _ = (Fin.snoc (fun i ↦ d * u i) t : Fin (m + 2) → R) j.castSucc := by
          simp [Fin.snoc_castSucc]

/-- Helper for Lemma 15.125.10: the forward endpoint map inserts the two endpoint coordinates at
the beginning and end of `Fin (m + 2)`. -/
def endpoint_bezout_forward (m : ℕ) : Fin 2 ⊕ Fin m → Fin (m + 2) := fun s ↦
  match s with
  | Sum.inl j => Fin.cases 0 (fun _ : Fin 1 ↦ Fin.last (m + 1)) j
  | Sum.inr i => Fin.castSucc i.succ

/-- Helper for Lemma 15.125.10: the backward endpoint map extracts the initial endpoint, terminal
endpoint, and middle coordinates from `Fin (m + 2)`. -/
def endpoint_bezout_backward (m : ℕ) : Fin (m + 2) → Fin 2 ⊕ Fin m := fun i ↦
  Fin.lastCases
    (Sum.inl (1 : Fin 2))
    (fun j ↦ Fin.cases (Sum.inl 0) (fun k ↦ Sum.inr k) j)
    i

/-- Helper for Lemma 15.125.10: the backward endpoint map sends a cast-successor index to the
corresponding initial or middle summand. -/
lemma endpoint_bezout_backward_castSucc {m : ℕ} (i : Fin (m + 1)) :
    endpoint_bezout_backward m (Fin.castSucc i) =
      Fin.cases (Sum.inl 0) (fun k ↦ Sum.inr k) i := by
  simpa [endpoint_bezout_backward] using
    (Fin.lastCases_castSucc
      (motive := fun _ : Fin (m + 2) ↦ Fin 2 ⊕ Fin m)
      (last := Sum.inl (1 : Fin 2))
      (cast := fun j : Fin (m + 1) ↦ Fin.cases (Sum.inl 0) (fun k ↦ Sum.inr k) j)
      (i := i))

/-- Helper for Lemma 15.125.10: the backward endpoint map sends the last index to the second
endpoint summand. -/
lemma endpoint_bezout_backward_last {m : ℕ} :
    endpoint_bezout_backward m (Fin.last (m + 1)) = Sum.inl 1 := by
  simpa [endpoint_bezout_backward] using
    (Fin.lastCases_last
      (motive := fun _ : Fin (m + 2) ↦ Fin 2 ⊕ Fin m)
      (last := Sum.inl (1 : Fin 2))
      (cast := fun j : Fin (m + 1) ↦ Fin.cases (Sum.inl 0) (fun k ↦ Sum.inr k) j))

/-- Helper for Lemma 15.125.10: the forward endpoint map is left inverse to the backward one. -/
lemma endpoint_bezout_forward_left_inv (m : ℕ) :
    Function.LeftInverse (endpoint_bezout_backward m) (endpoint_bezout_forward m) := by
  intro s
  cases s with
  | inl j =>
      fin_cases j
      · simpa [endpoint_bezout_forward] using
          (endpoint_bezout_backward_castSucc (m := m) (i := (0 : Fin (m + 1))))
      · simpa [endpoint_bezout_forward] using (endpoint_bezout_backward_last (m := m))
  | inr i =>
      simpa [endpoint_bezout_forward] using
        (endpoint_bezout_backward_castSucc (m := m) (i := i.succ))

/-- Helper for Lemma 15.125.10: the backward endpoint map is right inverse to the forward one. -/
lemma endpoint_bezout_backward_right_inv (m : ℕ) :
    Function.RightInverse (endpoint_bezout_backward m) (endpoint_bezout_forward m) := by
  intro i
  cases i using Fin.lastCases with
  | last =>
      rw [endpoint_bezout_backward_last]
      rfl
  | cast j =>
      cases j using Fin.cases with
      | zero =>
          rw [endpoint_bezout_backward_castSucc]
          rfl
      | succ k =>
          rw [endpoint_bezout_backward_castSucc]
          rfl

/-- Helper for Lemma 15.125.10: split `Fin (m + 2)` into the first coordinate, the final
coordinate, and the middle `m` coordinates so that the source `2 × 2` endpoint block can be
reindexed onto `Fin (m + 2)`. -/
def endpoint_bezout_reindex (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m + 2) :=
  { toFun := endpoint_bezout_forward m
    invFun := endpoint_bezout_backward m
    left_inv := endpoint_bezout_forward_left_inv m
    right_inv := endpoint_bezout_backward_right_inv m }

/-- Helper for Lemma 15.125.10: the reindexing sends the initial coordinate to the first slot of
the endpoint `2 × 2` block. -/
lemma endpoint_bezout_reindex_zero {m : ℕ} :
    (endpoint_bezout_reindex m).symm 0 = Sum.inl 0 := by
  simpa [endpoint_bezout_reindex] using
    (endpoint_bezout_backward_castSucc (m := m) (i := (0 : Fin (m + 1))))

/-- Helper for Lemma 15.125.10: the reindexing sends the final coordinate to the second slot of
the endpoint `2 × 2` block. -/
lemma endpoint_bezout_reindex_last {m : ℕ} :
    (endpoint_bezout_reindex m).symm (Fin.last (m + 1)) = Sum.inl 1 := by
  simpa [endpoint_bezout_reindex] using (endpoint_bezout_backward_last (m := m))

/-- Helper for Lemma 15.125.10: the reindexing sends the middle coordinates to the identity block.
-/
lemma endpoint_bezout_reindex_middle {m : ℕ} (i : Fin m) :
    (endpoint_bezout_reindex m).symm (Fin.castSucc i.succ) = Sum.inr i := by
  simpa [endpoint_bezout_reindex] using
    (endpoint_bezout_backward_castSucc (m := m) (i := i.succ))

/-- Helper for Lemma 15.125.10: this is the source endpoint matrix with a `2 × 2` corner block
and an identity middle block, reindexed onto `Fin (m + 2)`. -/
def endpoint_bezout_matrix {m : ℕ} (d t b a : R) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  Matrix.reindex (endpoint_bezout_reindex m) (endpoint_bezout_reindex m)
    (Matrix.fromBlocks (!![d, t; b, a]) 0 0 (1 : Matrix (Fin m) (Fin m) R))

/-- Helper for Lemma 15.125.10: the determinant of the source endpoint block is the Bézout
combination from the textbook proof. -/
lemma endpoint_bezout_matrix_det {m : ℕ} (d t b a : R) :
    Matrix.det (endpoint_bezout_matrix (m := m) d t b a) = a * d - b * t := by
  -- Route correction: compute the determinant on the concrete `2 × 2` source block first and
  -- only then reindex, instead of trying to build an explicit inverse on `Fin (m + 2)`.
  calc
    Matrix.det (endpoint_bezout_matrix (m := m) d t b a) =
        Matrix.det (Matrix.fromBlocks (!![d, t; b, a]) 0 0 (1 : Matrix (Fin m) (Fin m) R)) := by
      simpa [endpoint_bezout_matrix] using
        (Matrix.det_reindex_self
          (e := endpoint_bezout_reindex m)
          (M := Matrix.fromBlocks (!![d, t; b, a]) 0 0 (1 : Matrix (Fin m) (Fin m) R))).symm
    _ = Matrix.det (!![d, t; b, a] : Matrix (Fin 2) (Fin 2) R) *
        Matrix.det (1 : Matrix (Fin m) (Fin m) R) := by
      rw [Matrix.det_fromBlocks_zero₁₂]
    _ = (a * d - b * t) * 1 := by
      rw [Matrix.det_fin_two]
      simp
      ring
    _ = a * d - b * t := by simp

/-- Helper for Lemma 15.125.10: the first row of the endpoint block has the source shape
`[d, 0, ..., 0, t]`. -/
lemma endpoint_bezout_matrix_row_zero {m : ℕ} (d t b a : R) :
    endpoint_bezout_matrix (m := m) d t b a 0 = Fin.snoc (Fin.cons d (fun _ : Fin m ↦ 0)) t := by
  -- Read the reindexed source block row coordinatewise, separating the first, middle, and final
  -- positions of `Fin (m + 2)`.
  ext j
  cases j using Fin.lastCases with
  | last =>
      simp [endpoint_bezout_matrix, Matrix.reindex_apply, endpoint_bezout_reindex_zero,
        endpoint_bezout_reindex_last, Fin.snoc_last]
  | cast j =>
      cases j using Fin.cases with
      | zero =>
          simp [endpoint_bezout_matrix, Matrix.reindex_apply, endpoint_bezout_reindex_zero,
            Fin.cons_zero]
      | succ i =>
          have hzero := endpoint_bezout_reindex_zero (m := m)
          have hmiddle := endpoint_bezout_reindex_middle (m := m) i
          have hmiddle' : (endpoint_bezout_reindex m).symm i.castSucc.succ = Sum.inr i := by
            rw [Fin.succ_castSucc]
            exact hmiddle
          dsimp [endpoint_bezout_matrix, Matrix.reindex]
          rw [hzero, hmiddle']
          rw [Fin.succ_castSucc, Fin.snoc_castSucc]
          simp [Fin.cons_succ]

/-- Helper for Lemma 15.125.10: if the pair `(d, t)` generates the unit ideal, then a Bézout
relation `a * d - b * t = 1` exists. -/
lemma bezout_relation_of_span_pair_eq_top (d t : R)
    (hspan : Ideal.span ({d, t} : Set R) = ⊤) :
    ∃ a b : R, a * d - b * t = 1 := by
  -- The unit-ideal hypothesis puts `1` in the two-generated ideal, and `Ideal.mem_span_pair`
  -- rewrites that membership as a concrete Bézout combination.
  have hone : (1 : R) ∈ Ideal.span ({d, t} : Set R) := by
    simpa [hspan] using (Ideal.mem_top : (1 : R) ∈ (⊤ : Ideal R))
  rcases Ideal.mem_span_pair.mp hone with ⟨a, b, hab⟩
  refine ⟨a, -b, ?_⟩
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using hab

/-- Helper for Lemma 15.125.10: a Bézout relation with value `1` produces the source endpoint
completion matrix as an element of `GL`. -/
lemma exists_endpoint_unimodular_gl {m : ℕ} (d t a b : R)
    (hbezout : a * d - b * t = 1) :
    ∃ L : GL (Fin (m + 2)) R, L 0 = Fin.snoc (Fin.cons d (fun _ : Fin m ↦ 0)) t := by
  let M : Matrix (Fin (m + 2)) (Fin (m + 2)) R := endpoint_bezout_matrix (m := m) d t b a
  have hMdet : IsUnit M.det := by
    rw [show M.det = a * d - b * t by
      simp [M, endpoint_bezout_matrix_det]]
    rw [hbezout]
    simpa using (isUnit_one : IsUnit (1 : R))
  let L : GL (Fin (m + 2)) R := Matrix.GeneralLinearGroup.mk'' M hMdet
  refine ⟨L, ?_⟩
  -- The packaged unit matrix has the same first row as the concrete endpoint block.
  simpa [L, M] using endpoint_bezout_matrix_row_zero (m := m) d t b a

-- Proof sketch: argue by induction on `n`. For `n = 1`, the hypothesis that `f 0` generates the
-- unit ideal says `f 0` is a unit, so the `1 × 1` matrix `[f 0]` is invertible. For `n > 1`,
-- replace the first `n - 1` entries by a single generator of their ideal using the Bézout
-- property, apply the induction hypothesis to complete that shorter row, and then compose with a
-- `2 × 2` unimodular block sending `(f, fₙ)` to a row generating `1`.
/-- Lemma 15.125.10: over a Bézout domain, any finite row generating the unit ideal is the first
row of an invertible square matrix. -/
theorem exists_invertible_matrix_first_row_eq_of_span_range_eq_top
    [IsDomain R] [IsBezout R]
    {n : ℕ} (f : Fin (n + 1) → R) (hunit : Ideal.span (Set.range f) = ⊤) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := by
  induction n with
  | zero =>
      -- In size `1`, the unit-ideal hypothesis says the single entry is a unit.
      have hf0_unit : IsUnit (f 0) := by
        have hsingle : Ideal.span ({f 0} : Set R) = ⊤ := by
          have hrange : Set.range f = ({f 0} : Set R) := by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨i, rfl⟩
              fin_cases i
              simp
            · intro hx
              simp only [Set.mem_singleton_iff] at hx
              rcases hx with rfl
              exact ⟨0, rfl⟩
          simpa [hrange] using hunit
        simpa using (Ideal.span_singleton_eq_top.1 hsingle)
      let M : Matrix (Fin 1) (Fin 1) R := !![f 0]
      have hMdet : IsUnit M.det := by
        simpa [M, Matrix.det_fin_one] using hf0_unit
      let A : GL (Fin 1) R := Matrix.GeneralLinearGroup.mk'' M hMdet
      refine ⟨A, ?_⟩
      ext i
      fin_cases i
      simp [A, M]
  | succ n ih =>
      -- The source proof splits on whether the prefix ideal vanishes.
      let g : Fin (n + 1) → R := Fin.init f
      let t : R := f (Fin.last (n + 1))
      have hf_snoc : f = Fin.snoc g t := by
        -- Splitting a row into its `init` part and final coordinate is the canonical source
        -- decomposition for the induction step.
        ext i
        cases i using Fin.lastCases with
        | last =>
            simp [g, t, Fin.snoc_last]
        | cast i =>
            rw [Fin.snoc_castSucc]
            rfl
      by_cases hprefix : Ideal.span (Set.range g) = ⊥
      · -- A zero prefix means the row is concentrated in the final entry, so the source endpoint
        -- block with `d = 0` already gives the required completion.
        have hg_zero : g = fun _ : Fin (n + 1) ↦ 0 := by
          ext i
          have hgi : g i ∈ Ideal.span (Set.range g) := Ideal.subset_span ⟨i, rfl⟩
          rw [hprefix] at hgi
          simpa using hgi
        have hpair_top : Ideal.span ({(0 : R), t} : Set R) = ⊤ := by
          calc
            Ideal.span ({(0 : R), t} : Set R) =
                Ideal.span (Set.range (Fin.snoc g t)) := by
              symm
              have hspan_zero :
                  Ideal.span (Set.range g) = Ideal.span ({(0 : R)} : Set R) := by
                simpa [hprefix]
              exact span_range_snoc_eq_span_pair_of_init_span_eq (g := g) (a := t) (d := 0)
                hspan_zero
            _ = ⊤ := by simpa [hf_snoc] using hunit
        obtain ⟨a, b, hab⟩ := bezout_relation_of_span_pair_eq_top (d := (0 : R)) (t := t)
          hpair_top
        obtain ⟨L, hLrow⟩ := exists_endpoint_unimodular_gl (m := n) (d := (0 : R)) (t := t)
          (a := a) (b := b) hab
        refine ⟨L, ?_⟩
        calc
          L 0 = Fin.snoc (Fin.cons (0 : R) (fun _ : Fin n ↦ 0)) t := hLrow
          _ = Fin.snoc (fun _ : Fin (n + 1) ↦ 0) t := by
            ext i
            cases i using Fin.cases with
            | zero => rfl
            | succ i => rfl
          _ = Fin.snoc g t := by rw [hg_zero]
          _ = f := hf_snoc.symm
      · -- Compress the nonzero prefix to a single generator, complete the normalized shorter row,
        -- pad it, and finish with the source endpoint Bézout block.
        obtain ⟨d, u, hfactor, hgspan, hd_ne_zero, hu_top⟩ :=
          exists_nonzero_generator_factorization_of_span_range_ne_bot (g := g) hprefix
        obtain ⟨A, hArow⟩ := ih u hu_top
        obtain ⟨B, hB0, hBlast⟩ := exists_padded_gl_fixing_last_basis A
        have hB0u : B 0 = Fin.snoc u 0 := by
          simpa [hArow] using hB0
        have hpair_top : Ideal.span ({d, t} : Set R) = ⊤ := by
          calc
            Ideal.span ({d, t} : Set R) = Ideal.span (Set.range (Fin.snoc g t)) := by
              symm
              exact span_range_snoc_eq_span_pair_of_init_span_eq (g := g) (a := t) (d := d) hgspan
            _ = ⊤ := by simpa [hf_snoc] using hunit
        obtain ⟨a, b, hab⟩ := bezout_relation_of_span_pair_eq_top (d := d) (t := t) hpair_top
        obtain ⟨L, hLrow⟩ := exists_endpoint_unimodular_gl (m := n) (d := d) (t := t)
          (a := a) (b := b) hab
        refine ⟨L * B, ?_⟩
        have hLBrow :
            (((L : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *
                (B : Matrix (Fin (n + 2)) (Fin (n + 2)) R)) 0) =
              Fin.snoc (fun i ↦ d * u i) t := by
          exact first_row_mul_endpoint_padded
            (L := (L : Matrix (Fin (n + 2)) (Fin (n + 2)) R))
            (B := (B : Matrix (Fin (n + 2)) (Fin (n + 2)) R))
            (d := d) (t := t) (u := u) hLrow hB0u hBlast
        have hprefix_row :
            (Fin.snoc (fun i ↦ d * u i) t : Fin (n + 2) → R) = Fin.snoc g t := by
          ext i
          cases i using Fin.lastCases with
          | last =>
              simp [Fin.snoc_last]
          | cast i =>
              simp [Fin.snoc_castSucc, hfactor i]
        calc
          (L * B) 0 =
              (((L : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *
                (B : Matrix (Fin (n + 2)) (Fin (n + 2)) R)) 0) := by
            rfl
          _ = Fin.snoc (fun i ↦ d * u i) t := hLBrow
          _ = Fin.snoc g t := hprefix_row
          _ = f := hf_snoc.symm

/-- Canonical `Fintype.linearCombination` bridge view of
`exists_invertible_matrix_first_row_eq_of_span_range_eq_top`. -/
theorem exists_invertible_matrix_first_row_eq_of_surjective_fintypeLinearCombination
    [IsDomain R] [IsBezout R]
    {n : ℕ} (f : Fin (n + 1) → R)
    (hsurj : Function.Surjective (Fintype.linearCombination R f)) :
    ∃ A : GL (Fin (n + 1)) R, A 0 = f := by
  apply exists_invertible_matrix_first_row_eq_of_span_range_eq_top
  simpa using (span_range_eq_top_iff_surjective_fintypeLinearCombination R f).2 hsurj

end
