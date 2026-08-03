import Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22
import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open Function
open scoped LovaszSchrijverNotation
open scoped CoordinateLiftProjectNotation

section Theorem1010

variable {n : ℕ}

private theorem homogenized_cone_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q) :
    homogenized_cone P ⊆ homogenized_cone Q := by
  intro y hy
  rw [mem_homogenized_cone_iff] at hy ⊢
  rcases hy with ⟨t, ht, x, hx, rfl⟩
  exact ⟨t, ht, x, convexHull_mono hPQ hx, rfl⟩

private theorem isLovaszSchrijverMatrix_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q)
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsLovaszSchrijverMatrix P Y) :
    IsLovaszSchrijverMatrix Q Y := by
  rw [isLovaszSchrijverMatrix_iff] at hY ⊢
  rcases hY with ⟨h_symm, h0, hrest, hdiag⟩
  refine ⟨h_symm, homogenized_cone_mono hPQ h0, ?_, hdiag⟩
  intro i
  rcases hrest i with ⟨hi, hdiff⟩
  exact ⟨homogenized_cone_mono hPQ hi, homogenized_cone_mono hPQ hdiff⟩

/-- The Lovász-Schrijver operator is monotone with respect to set inclusion. -/
theorem lovasz_schrijver_N_mono :
    Monotone (fun P : Set (Fin n → ℝ) ↦ lovasz_schrijver_N P) := by
  intro P Q hPQ x hx
  change x ∈ N(P) at hx
  change x ∈ N(Q)
  rw [mem_lovasz_schrijver_N_iff] at hx ⊢
  rcases hx with ⟨Y, hY, hcol⟩
  exact ⟨Y, isLovaszSchrijverMatrix_mono hPQ hY, hcol⟩

/-- Under the unit-box assumption on `P`, the one-step Lovász-Schrijver relaxation is contained
in each coordinate lift-and-project hull `(P)_{j}`. -/
theorem lovasz_schrijver_N_subset_coordinate_lift_project_hull
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n))
    (j : Fin n) :
    N(P) ⊆ (P)_{j} := by
  sorry

private theorem coordinate_lift_project_hull_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q)
    (j : Fin n) :
    (P)_{j} ⊆ (Q)_{j} := by
  rw [coordinate_lift_project_hull_def, coordinate_lift_project_hull_def]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hPQ hx.1, hx.2⟩
    · exact Or.inr ⟨hPQ hx.1, hx.2⟩

private theorem lovasz_schrijver_iterate_subset_self
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P) :
    ∀ t : ℕ, (lovasz_schrijver_N^[t]) P ⊆ P
  | 0 => by simp
  | t + 1 => by
      refine Set.Subset.trans ?_ <|
        lovasz_schrijver_N_subset P hP_convex
      simpa [Function.iterate_succ_apply'] using
        lovasz_schrijver_N_mono (lovasz_schrijver_iterate_subset_self P hP_convex t)

/-- For a convex set `P`, the Lovász-Schrijver iterates form a descending chain
`P ⊇ N(P) ⊇ N(N(P)) ⊇ ⋯`; equivalently,
`(lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P` for every `t`. -/
theorem lovasz_schrijver_iterates_descend
    (P : Set (Fin n → ℝ))
    (hP_convex : Convex ℝ P)
    (t : ℕ) :
    (lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P := by
  induction t with
  | zero =>
      simpa [Function.iterate_succ_apply'] using
        lovasz_schrijver_N_subset P hP_convex
  | succ t ih =>
      simpa [Function.iterate_succ_apply', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        lovasz_schrijver_N_mono ih

/-- Theorem 10.10 (1). For a polyhedron `P`, the Lovász-Schrijver iterates form a descending
chain `P ⊇ N(P) ⊇ N(N(P)) ⊇ ⋯`; equivalently,
`(lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P` for every `t`. -/
theorem lovasz_schrijver_iterates_descend_of_is_polyhedron
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (t : ℕ) :
    (lovasz_schrijver_N^[t + 1]) P ⊆ (lovasz_schrijver_N^[t]) P :=
  lovasz_schrijver_iterates_descend P (convex_of_is_polyhedron hP_polyhedron) t

private theorem convexHull_zero_one_points_subset_lovasz_schrijver_iterate
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    ∀ t : ℕ,
      convexHull ℝ (zero_one_points (Nat.le_refl n) P) ⊆ (lovasz_schrijver_N^[t]) P
  | 0 => by
      have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
      refine convexHull_min ?_ hP_convex
      intro x hx
      exact (mem_zero_one_points_iff (Nat.le_refl n) P x).1 hx |>.1
  | t + 1 => by
      let S := zero_one_points (Nat.le_refl n) P
      calc
        convexHull ℝ S ⊆
            convexHull ℝ (zero_one_points (Nat.le_refl n) ((lovasz_schrijver_N^[t]) P)) := by
              refine convexHull_mono ?_
              intro x hx
              rw [mem_zero_one_points_iff (Nat.le_refl n) ((lovasz_schrijver_N^[t]) P) x]
              refine ⟨?_, ?_⟩
              · exact convexHull_zero_one_points_subset_lovasz_schrijver_iterate P
                  hP_polyhedron t (subset_convexHull ℝ S hx)
              · exact (mem_zero_one_points_iff (Nat.le_refl n) P x).1 hx |>.2
        _ ⊆ N₊((lovasz_schrijver_N^[t]) P) :=
          convexHull_zero_one_points_subset_lovasz_schrijver_N_plus ((lovasz_schrijver_N^[t]) P)
        _ ⊆ N((lovasz_schrijver_N^[t]) P) :=
          lovasz_schrijver_N_plus_subset_N ((lovasz_schrijver_N^[t]) P)
        _ = (lovasz_schrijver_N^[t + 1]) P := by
          simp [Function.iterate_succ_apply']

private theorem lovasz_schrijver_iterate_subset_sequential_convexification
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n)) :
    ∀ {t : ℕ}, (ht : t ≤ n) →
      (lovasz_schrijver_N^[t]) P ⊆ sequential_convexification_iter (Nat.le_refl n) P ht
  | 0, ht => by
      simp [sequential_convexification_iter_zero (Nat.le_refl n) P]
  | t + 1, ht => by
      have ht_prev : t ≤ n := Nat.le_of_succ_le ht
      calc
        (lovasz_schrijver_N^[t + 1]) P
            = N((lovasz_schrijver_N^[t]) P) := by
                simp [Function.iterate_succ_apply']
        _ ⊆ ((lovasz_schrijver_N^[t]) P)_{
              Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩} :=
            lovasz_schrijver_N_subset_coordinate_lift_project_hull ((lovasz_schrijver_N^[t]) P)
              (by
                intro x hx
                exact hP_subset <|
                  lovasz_schrijver_iterate_subset_self P
                    (convex_of_is_polyhedron hP_polyhedron) t hx)
              (Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩)
        _ ⊆ (sequential_convexification_iter (Nat.le_refl n) P ht_prev)_{
              Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩} :=
            coordinate_lift_project_hull_mono
              (lovasz_schrijver_iterate_subset_sequential_convexification P hP_polyhedron
                hP_subset ht_prev)
              (Fin.castLE (Nat.le_refl n) ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩)
        _ = sequential_convexification_iter (Nat.le_refl n) P ht := by
            rw [sequential_convexification_iter_succ (Nat.le_refl n) P ht]

/-- Theorem 10.10 (2). Let `P ⊆ [0,1]^n`, let
`S = {x ∈ P : x_j ∈ {0,1} for j = 1, …, n}`, and let `N` denote the Lovász-Schrijver iterate
operator. Then `Nⁿ(P) = conv(S)`. Here `S` is formalized as
`zero_one_points (Nat.le_refl n) P`. -/
theorem lovasz_schrijver_nth_iterate_eq_convexHull_zero_one_points
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box (Nat.le_refl n)) :
    (lovasz_schrijver_N^[n]) P = convexHull ℝ (zero_one_points (Nat.le_refl n) P) := by
  refine Set.Subset.antisymm ?_ ?_
  · calc
      (lovasz_schrijver_N^[n]) P ⊆
          sequential_convexification_iter (Nat.le_refl n) P (Nat.le_refl n) :=
        lovasz_schrijver_iterate_subset_sequential_convexification P hP_polyhedron hP_subset
          (Nat.le_refl n)
      _ = convexHull ℝ (zero_one_points (Nat.le_refl n) P) :=
        sequential_convexification_iter_eq_convexHull_zero_one_points
          (Nat.le_refl n) P hP_polyhedron hP_subset
  · exact convexHull_zero_one_points_subset_lovasz_schrijver_iterate P hP_polyhedron n

end Theorem1010
