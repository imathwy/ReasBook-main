import Mathlib
import Serre.Chap01.Definition_1_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Representation

section

variable {G : Type u} [Monoid G]

/-- Helper for Remark 1-1.4-3: the span of any vector is stable for the trivial action. -/
lemma trivial_span_singleton_apply_mem (v : ℂ × ℂ) :
    ∀ g x, x ∈ (ℂ ∙ v : Submodule ℂ (ℂ × ℂ)) →
      (Representation.trivial ℂ G (ℂ × ℂ)) g x ∈ (ℂ ∙ v : Submodule ℂ (ℂ × ℂ)) := by
  intro g x hx
  -- The trivial representation acts by the identity, so stability is immediate.
  simpa [Representation.trivial] using hx

/-- Helper for Remark 1-1.4-3: the line spanned by a vector in `ℂ × ℂ`, viewed as a
subrepresentation of the trivial representation. -/
abbrev trivial_line_subrepresentation (v : ℂ × ℂ) :
    Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ)) :=
  { toSubmodule := ℂ ∙ v
    apply_mem_toSubmodule := trivial_span_singleton_apply_mem (G := G) v }

/-- Helper for Remark 1-1.4-3: the two coordinate-axis lines in `ℂ × ℂ`. -/
abbrev coordinate_lines : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ))
  | 0 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))
  | 1 => trivial_line_subrepresentation (G := G) ((0 : ℂ), (1 : ℂ))

/-- Helper for Remark 1-1.4-3: the diagonal and anti-diagonal lines in `ℂ × ℂ`. -/
abbrev diagonal_lines : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ))
  | 0 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (1 : ℂ))
  | 1 => trivial_line_subrepresentation (G := G) ((1 : ℂ), (-1 : ℂ))

/-- Helper for Remark 1-1.4-3: a nonzero line in the trivial two-dimensional
representation has dimension one. -/
lemma trivial_line_finrank_eq_one {v : ℂ × ℂ} (hv : v ≠ 0) :
    Module.finrank ℂ (trivial_line_subrepresentation (G := G) v).toSubmodule = 1 := by
  -- The underlying submodule is literally the span of a single nonzero vector.
  simpa [trivial_line_subrepresentation] using finrank_span_singleton hv

/-- Helper for Remark 1-1.4-3: every nonzero line in the trivial two-dimensional
representation is irreducible. -/
lemma trivial_line_is_irreducible {v : ℂ × ℂ} (hv : v ≠ 0) :
    (trivial_line_subrepresentation (G := G) v).toRepresentation.IsIrreducible := by
  -- We pass from the one-dimensionality of the line to irreducibility.
  exact
    isIrreducible_of_finrank_eq_one
      (trivial_line_subrepresentation (G := G) v).toRepresentation
      (trivial_line_finrank_eq_one (G := G) hv)

/-- Helper for Remark 1-1.4-3: the coordinate-axis lines form a complementary pair. -/
lemma coordinate_axes_are_compl :
    IsCompl
      (coordinate_lines (G := G) 0).toSubmodule
      (coordinate_lines (G := G) 1).toSubmodule := by
  have h10 : ((1 : ℂ), (0 : ℂ)) ≠ 0 := by
    simp
  have h01 : ((0 : ℂ), (1 : ℂ)) ≠ 0 := by
    simp
  have hfin0 :
      Module.finrank ℂ (coordinate_lines (G := G) 0).toSubmodule = 1 := by
    simpa [coordinate_lines] using trivial_line_finrank_eq_one (G := G) h10
  have hfin1 :
      Module.finrank ℂ (coordinate_lines (G := G) 1).toSubmodule = 1 := by
    simpa [coordinate_lines] using trivial_line_finrank_eq_one (G := G) h01
  -- The geometric content is that two distinct one-dimensional axes in `ℂ²`
  -- are disjoint and have dimensions summing to the ambient dimension.
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
  · simp [hfin0, hfin1]
  · apply Submodule.disjoint_span_singleton_of_notMem
    simp [Submodule.mem_span_singleton]

/-- Helper for Remark 1-1.4-3: the diagonal and anti-diagonal lines form a complementary pair. -/
lemma diagonal_lines_are_compl :
    IsCompl
      (diagonal_lines (G := G) 0).toSubmodule
      (diagonal_lines (G := G) 1).toSubmodule := by
  have h11 : ((1 : ℂ), (1 : ℂ)) ≠ 0 := by
    simp
  have h1m1 : ((1 : ℂ), (-1 : ℂ)) ≠ 0 := by
    simp
  have hfin0 :
      Module.finrank ℂ (diagonal_lines (G := G) 0).toSubmodule = 1 := by
    simpa [diagonal_lines] using trivial_line_finrank_eq_one (G := G) h11
  have hfin1 :
      Module.finrank ℂ (diagonal_lines (G := G) 1).toSubmodule = 1 := by
    simpa [diagonal_lines] using trivial_line_finrank_eq_one (G := G) h1m1
  -- The same dimension-and-disjointness argument works for the diagonal pair.
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
  · simp [hfin0, hfin1]
  · apply Submodule.disjoint_span_singleton_of_notMem
    simp [Submodule.mem_span_singleton]
    norm_num

/-- Helper for Remark 1-1.4-3: for a `Fin 2`-indexed family, a complementary pair gives an
internal direct sum decomposition. -/
lemma fin2_is_internal_of_is_compl
    {σ : Fin 2 → Submodule ℂ (ℂ × ℂ)} (hσ : IsCompl (σ 0) (σ 1)) :
    DirectSum.IsInternal σ := by
  have h01 : (0 : Fin 2) ≠ 1 := by
    decide
  have hfin2 : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i
    · simp
    · simp
  -- For two summands, `IsInternal` is exactly the `IsCompl` condition.
  exact (DirectSum.isInternal_submodule_iff_isCompl σ h01 hfin2).2 hσ

/-- Helper for Remark 1-1.4-3: each coordinate-axis summand is irreducible. -/
lemma coordinate_lines_are_irreducible :
    ∀ i, (coordinate_lines (G := G) i).toRepresentation.IsIrreducible := by
  intro i
  fin_cases i
  · have h10 : ((1 : ℂ), (0 : ℂ)) ≠ 0 := by
      simp
    simpa [coordinate_lines] using trivial_line_is_irreducible (G := G) h10
  · have h01 : ((0 : ℂ), (1 : ℂ)) ≠ 0 := by
      simp
    simpa [coordinate_lines] using trivial_line_is_irreducible (G := G) h01

/-- Helper for Remark 1-1.4-3: each diagonal summand is irreducible. -/
lemma diagonal_lines_are_irreducible :
    ∀ i, (diagonal_lines (G := G) i).toRepresentation.IsIrreducible := by
  intro i
  fin_cases i
  · have h11 : ((1 : ℂ), (1 : ℂ)) ≠ 0 := by
      simp
    simpa [diagonal_lines] using trivial_line_is_irreducible (G := G) h11
  · have h1m1 : ((1 : ℂ), (-1 : ℂ)) ≠ 0 := by
      simp
    simpa [diagonal_lines] using trivial_line_is_irreducible (G := G) h1m1

/-- Helper for Remark 1-1.4-3: the coordinate-axis pair and the diagonal pair are distinct
families of summands. -/
lemma coordinate_and_diagonal_ranges_ne :
    Set.range (coordinate_lines (G := G)) ≠ Set.range (diagonal_lines (G := G)) := by
  intro hEq
  have hcoord_mem :
      trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ)) ∈
        Set.range (coordinate_lines (G := G)) := by
    exact ⟨0, by simp [coordinate_lines]⟩
  rw [hEq] at hcoord_mem
  rcases hcoord_mem with ⟨i, hi⟩
  fin_cases i
  · have hdiag_mem :
        ((1 : ℂ), (1 : ℂ)) ∈ (diagonal_lines (G := G) 0).toSubmodule := by
      simp
    have haxis_mem :
        ((1 : ℂ), (1 : ℂ)) ∈
          (trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))).toSubmodule := by
      exact hi ▸ hdiag_mem
    -- `(1,1)` lies on the diagonal but not on the first coordinate axis.
    simp [Submodule.mem_span_singleton] at haxis_mem
  · have hdiag_mem :
        ((1 : ℂ), (-1 : ℂ)) ∈ (diagonal_lines (G := G) 1).toSubmodule := by
      simp
    have haxis_mem :
        ((1 : ℂ), (-1 : ℂ)) ∈
          (trivial_line_subrepresentation (G := G) ((1 : ℂ), (0 : ℂ))).toSubmodule := by
      exact hi ▸ hdiag_mem
    -- `(1,-1)` lies on the anti-diagonal but not on the first coordinate axis.
    simp [Submodule.mem_span_singleton] at haxis_mem

/-- Remark 1-1.4-3: the decomposition of a representation into irreducible summands is not unique
in general. The trivial representation on `ℂ × ℂ` admits two distinct decompositions into
irreducible lines: the coordinate axes and the diagonal/anti-diagonal lines. -/
theorem exists_distinct_irreducible_line_decompositions_trivial :
    ∃ σ τ : Fin 2 → Subrepresentation (Representation.trivial ℂ G (ℂ × ℂ)),
      Set.range σ ≠ Set.range τ ∧
        DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
        DirectSum.IsInternal (fun i ↦ (τ i).toSubmodule) ∧
        (∀ i, (σ i).toRepresentation.IsIrreducible) ∧
        ∀ i, (τ i).toRepresentation.IsIrreducible := by
  have hcoord_internal :
      DirectSum.IsInternal (fun i ↦ (coordinate_lines (G := G) i).toSubmodule) := by
    -- The coordinate axes give the first internal direct sum decomposition.
    exact
      fin2_is_internal_of_is_compl
        (σ := fun i ↦ (coordinate_lines (G := G) i).toSubmodule)
        (coordinate_axes_are_compl (G := G))
  have hdiag_internal :
      DirectSum.IsInternal (fun i ↦ (diagonal_lines (G := G) i).toSubmodule) := by
    -- The diagonal lines give the second internal direct sum decomposition.
    exact
      fin2_is_internal_of_is_compl
        (σ := fun i ↦ (diagonal_lines (G := G) i).toSubmodule)
        (diagonal_lines_are_compl (G := G))
  -- We witness non-uniqueness by these two concrete decompositions.
  exact
    ⟨coordinate_lines (G := G), diagonal_lines (G := G),
      coordinate_and_diagonal_ranges_ne (G := G),
      hcoord_internal, hdiag_internal,
      coordinate_lines_are_irreducible (G := G),
      diagonal_lines_are_irreducible (G := G)⟩

/- The second sentence of Remark 1-1.4-3 is a forward reference to §2.3:
the multiplicity of a fixed irreducible summand is decomposition-independent.
That later theorem is intentionally not anticipated in this source-facing file. -/

end
