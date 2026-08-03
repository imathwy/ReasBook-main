import Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: rational polyhedra and stage-indexed feasibility algorithms
-- * core/canonical owners inspected: `rational_matrix_polyhedron`,
--   `mem_rational_matrix_polyhedron`, `is_rational_polyhedron`, and the Chapter 5
--   algorithm-owner `StopsAt` pattern
-- * semantic recall: `lean_leansearch` produced no relevant upstream ellipsoid-method owner,
--   so the local `EllipsoidFeasibilityMethod` / `CutoffCertificate` surface is retained
-- * source-facing owner kept here: `EllipsoidFeasibilityMethod`
-- * bridge/view layer: none; no upstream ellipsoid-method owner exists in the project
-- * derived API kept minimal: `StopsAt`, coercion/apply and nonterminal-step companion lemmas,
--   the source-facing theorem `stopsAt_iff`, and `polyhedron_subset`

section Theorem722

variable {m n : ℕ}

/-- An abstract stage-indexed execution of the ellipsoid feasibility method for the rational
polyhedron `P = {x ∈ ℝ^n | A x ≤ b}`. The ellipsoid `ellipsoids t` has center `centers t`; when
`separatingIndex t = some i`, the center violates the `i`th inequality and the next ellipsoid
contains the cut intersection `E_t ∩ {x | aᵢ x ≤ bᵢ}`. When `separatingIndex t = none`, the
current center is already feasible for `P`. -/
structure EllipsoidFeasibilityMethod
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) where
  ellipsoids : ℕ → Set (Fin n → ℝ)
  centers : ℕ → Fin n → ℝ
  separatingIndex : ℕ → Option (Fin m)
  center_mem_ellipsoid : ∀ t : ℕ, centers t ∈ ellipsoids t
  polyhedron_subset_initial : rational_matrix_polyhedron A b ⊆ ellipsoids 0
  separatingIndex_none_iff :
    ∀ t : ℕ,
      separatingIndex t = none ↔ centers t ∈ rational_matrix_polyhedron A b
  separatingIndex_spec :
    ∀ ⦃t : ℕ⦄ ⦃i : Fin m⦄, separatingIndex t = some i →
      (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ centers t
  next_contains_cut_intersection :
    ∀ ⦃t : ℕ⦄ ⦃i : Fin m⦄, separatingIndex t = some i →
      ellipsoids t ∩
          {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)} ⊆
        ellipsoids (t + 1)

/-- An ellipsoid feasibility method coerces to its stage-indexed family of ellipsoids. -/
instance {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} :
    CoeFun (EllipsoidFeasibilityMethod A b) (fun _ ↦ ℕ → Set (Fin n → ℝ)) where
  coe M := M.ellipsoids

namespace EllipsoidFeasibilityMethod

variable {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}

/-- Evaluating an ellipsoid feasibility method by coercion returns its current ellipsoid. -/
@[simp] theorem coe_apply (M : EllipsoidFeasibilityMethod A b) (t : ℕ) :
    M t = M.ellipsoids t :=
  rfl

/-- An ellipsoid run stops at stage `t` when its current center already lies in the target
polyhedron and hence no violated inequality is returned. -/
def StopsAt
    (M : EllipsoidFeasibilityMethod A b)
    (t : ℕ) : Prop :=
  M.separatingIndex t = none

/-- An ellipsoid feasibility run stops at stage `t` exactly when its current center is feasible
for the input polyhedron `P = {x ∈ ℝ^n | A x ≤ b}`. -/
@[simp] theorem stopsAt_iff (M : EllipsoidFeasibilityMethod A b) (t : ℕ) :
    M.StopsAt t ↔ M.centers t ∈ rational_matrix_polyhedron A b :=
  M.separatingIndex_none_iff t

/-- At every nonterminal stage, the method records a violated inequality index. -/
theorem exists_separatingIndex_of_not_stopsAt
    (M : EllipsoidFeasibilityMethod A b) {t : ℕ} (ht : ¬ M.StopsAt t) :
    ∃ i : Fin m, M.separatingIndex t = some i := by
  cases h_sep : M.separatingIndex t with
  | none =>
      exact False.elim (ht h_sep)
  | some i =>
      exact ⟨i, rfl⟩

/-- At every nonterminal stage, the recorded separating index certifies that the current center
violates one defining inequality of the target polyhedron. -/
theorem exists_separatingIndex_spec_of_not_stopsAt
    (M : EllipsoidFeasibilityMethod A b) {t : ℕ} (ht : ¬ M.StopsAt t) :
    ∃ i : Fin m,
      M.separatingIndex t = some i ∧
        (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ M.centers t := by
  obtain ⟨i, hi⟩ := M.exists_separatingIndex_of_not_stopsAt ht
  exact ⟨i, hi, M.separatingIndex_spec hi⟩

/-- If an ellipsoid feasibility run has not stopped before stage `t`, then the target polyhedron
is still contained in the current ellipsoid `E_t`. -/
theorem polyhedron_subset (M : EllipsoidFeasibilityMethod A b) (t : ℕ)
    (h_no_stop : ∀ s < t, ¬ M.StopsAt s) :
    rational_matrix_polyhedron A b ⊆ M t := by
  induction t with
  | zero =>
      simpa using M.polyhedron_subset_initial
  | succ t ih =>
      intro x hx
      have hx_mem : x ∈ M t := by
        apply ih
        · intro s hs
          exact h_no_stop s (Nat.lt_trans hs (Nat.lt_succ_self t))
        · exact hx
      have ht_not_stop : ¬ M.StopsAt t := h_no_stop t (Nat.lt_succ_self t)
      obtain ⟨i, h_sep, -⟩ := M.exists_separatingIndex_spec_of_not_stopsAt ht_not_stop
      exact M.next_contains_cut_intersection h_sep
        ⟨hx_mem, (mem_rational_matrix_polyhedron A b x).mp hx i⟩

/-- A cutoff certificate at stage `tStar` with threshold `ε` packages the shared small-volume
hypotheses: every full-dimensional target polyhedron has volume at least `ε`, while the current
ellipsoid `E_{tStar}` already has volume strictly smaller than `ε`. -/
structure CutoffCertificate
    (M : EllipsoidFeasibilityMethod A b)
    (ε : ENNReal)
    (tStar : ℕ) : Prop where
  polyhedron_volume_lower_bound :
    (interior (rational_matrix_polyhedron A b)).Nonempty →
      ε ≤ MeasureTheory.volume (rational_matrix_polyhedron A b)
  ellipsoid_volume_lt : MeasureTheory.volume (M tStar) < ε

/-- A polynomial `π` is a cutoff bound for `M` when one can choose cutoff data `(ε, tStar)`
for this run so that `tStar` is bounded by `π` evaluated at the encoding size of the input
system `(A, b)`. -/
def PolynomialCutoffBound
    (M : EllipsoidFeasibilityMethod A b)
    (π : Polynomial ℕ) : Prop :=
  ∃ ε : ENNReal, ∃ tStar : ℕ,
    M.CutoffCertificate ε tStar ∧
      tStar ≤ π.eval (n + rational_linear_system_encoding_size A b)

/-- A polynomial cutoff bound provides a concrete cutoff certificate whose stage is bounded by the
corresponding polynomial. -/
theorem cutoff_le_encoding_bound
    {M : EllipsoidFeasibilityMethod A b}
    {π : Polynomial ℕ}
    (hπ : M.PolynomialCutoffBound π) :
    ∃ ε : ENNReal, ∃ tStar : ℕ,
      M.CutoffCertificate ε tStar ∧
        tStar ≤ π.eval (n + rational_linear_system_encoding_size A b) :=
  hπ

end EllipsoidFeasibilityMethod

variable
  (A : Matrix (Fin m) (Fin n) ℚ)
  (b : Fin m → ℚ)
  (M : EllipsoidFeasibilityMethod A b)

/-- If `tStar` is a small-volume cutoff stage for the run `M`, then every full-dimensional target
polyhedron is detected by some terminal stage at or before `tStar`. -/
theorem ellipsoid_feasibility_method_finds_feasible_point_by_cutoff
    (ε : ENNReal)
    (tStar : ℕ)
    (h_cutoff : M.CutoffCertificate ε tStar)
    (h_nonempty : (interior (rational_matrix_polyhedron A b)).Nonempty) :
    ∃ t : ℕ, t ≤ tStar ∧ M.StopsAt t := by
  by_contra h_no_stage
  have h_no_stop : ∀ t ≤ tStar, ¬ M.StopsAt t := by
    intro t ht h_stop
    exact h_no_stage ⟨t, ht, h_stop⟩
  have h_subset :
      rational_matrix_polyhedron A b ⊆ M tStar :=
    M.polyhedron_subset tStar (fun s hs ↦ h_no_stop s (Nat.le_of_lt hs))
  have h_lt :
      MeasureTheory.volume (rational_matrix_polyhedron A b) < ε :=
    lt_of_le_of_lt (MeasureTheory.volume.mono h_subset) h_cutoff.ellipsoid_volume_lt
  exact (not_le_of_gt h_lt) (h_cutoff.polyhedron_volume_lower_bound h_nonempty)

/-- If a small-volume cutoff stage `tStar` is reached without termination, then the target
polyhedron has empty interior. -/
theorem ellipsoid_feasibility_method_empty_interior_of_no_stop_by_cutoff
    (ε : ENNReal)
    (tStar : ℕ)
    (h_cutoff : M.CutoffCertificate ε tStar)
    (h_no_stop : ∀ t ≤ tStar, ¬ M.StopsAt t) :
    interior (rational_matrix_polyhedron A b) = ∅ := by
  by_contra h_nonempty
  have h_nonempty' : (interior (rational_matrix_polyhedron A b)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h_nonempty
  obtain ⟨t, ht, h_stop⟩ :=
    ellipsoid_feasibility_method_finds_feasible_point_by_cutoff
      A b M ε tStar h_cutoff h_nonempty'
  exact h_no_stop t ht h_stop

/-- For a chosen ellipsoid feasibility run `M` and polynomial `π`, this property packages the
three source-facing clauses of Theorem 7.22: a polynomial cutoff certificate exists for `M`, the
run finds a feasible point within the resulting polynomial bound whenever the target polyhedron has
nonempty interior, and failure to stop by that bound forces the target polyhedron to have empty
interior. -/
class HasCorrectOutputAndPolynomialIterationBound
    (M : EllipsoidFeasibilityMethod A b)
    (π : Polynomial ℕ) : Prop where
  cutoff_bound : M.PolynomialCutoffBound π
  finds_feasible_point :
    (interior (rational_matrix_polyhedron A b)).Nonempty →
      ∃ t : ℕ,
        t ≤ π.eval (n + rational_linear_system_encoding_size A b) ∧ M.StopsAt t
  empty_interior_of_no_stop :
    (∀ t ≤ π.eval (n + rational_linear_system_encoding_size A b), ¬ M.StopsAt t) →
      interior (rational_matrix_polyhedron A b) = ∅

/-- Theorem 7.22. The ellipsoid algorithm terminates with a correct output if `E₀` and `t*` are
chosen large enough. Furthermore this choice can be made so that the number of iterations is
polynomial. In this source-facing formalization, the chosen quantitative data are represented by
an ellipsoid feasibility run `M` together with a polynomial cutoff property for
`P = {x ∈ ℝ^n | A x ≤ b}`. -/
theorem ellipsoid_feasibility_method_has_correct_output_and_polynomial_iteration_bound :
    ∃ (M : EllipsoidFeasibilityMethod A b) (π : Polynomial ℕ),
      HasCorrectOutputAndPolynomialIterationBound A b M π := sorry

end Theorem722
