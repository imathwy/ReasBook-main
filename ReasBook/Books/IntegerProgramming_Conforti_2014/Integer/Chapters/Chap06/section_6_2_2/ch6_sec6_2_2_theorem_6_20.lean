import Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open scoped BigOperators Matrix

noncomputable section

section Theorem620

variable {p : ℕ}

/-- The normalized facet functional centered at `xbar` with normal `d`. -/
def centered_facet_functional
    (xbar d x : Fin p → ℝ) : ℝ :=
  d ⬝ᵥ (x - xbar)

/-- `centered_facet_functional xbar d x` is the displayed sum
`∑ h, d_h * (x_h - xbar_h)`. -/
theorem centered_facet_functional_def
    (xbar d x : Fin p → ℝ) :
    centered_facet_functional xbar d x =
      ∑ h : Fin p, d h * (x h - xbar h) := by
  simp [centered_facet_functional, dotProduct]

/-- The polyhedron cut out by the normalized centered inequalities with normals `normals`. -/
def centered_polyhedron_of_normals
    {t : ℕ}
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ) : Set (Fin p → ℝ) :=
  {x | ∀ i : Fin t, centered_facet_functional xbar (normals i) x ≤ 1}

/-- Membership in `centered_polyhedron_of_normals xbar normals` means satisfying each normalized
facet inequality. -/
theorem mem_centered_polyhedron_of_normals_iff
    {t : ℕ}
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ)
    (x : Fin p → ℝ) :
    x ∈ centered_polyhedron_of_normals xbar normals ↔
      ∀ i : Fin t, centered_facet_functional xbar (normals i) x ≤ 1 :=
  Iff.rfl

/-- The facet of `K` cut out by the normalized centered inequality with normal `d`. -/
def centered_facet_face
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d : Fin p → ℝ) : Set (Fin p → ℝ) :=
  face_set K d (1 + d ⬝ᵥ xbar)

/-- `centered_facet_face xbar K d` is the canonical equality face `face_set K d (1 + d ⬝ᵥ xbar)`
coming from the centered inequality `d ⬝ᵥ (x - xbar) ≤ 1`. -/
theorem centered_facet_face_eq_face_set
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d : Fin p → ℝ) :
    centered_facet_face xbar K d = face_set K d (1 + d ⬝ᵥ xbar) :=
  rfl

/-- Membership in `centered_facet_face xbar K d` means belonging to `K` and saturating the
corresponding normalized facet inequality. -/
theorem mem_centered_facet_face_iff
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d x : Fin p → ℝ) :
    x ∈ centered_facet_face xbar K d ↔
      x ∈ K ∧ centered_facet_functional xbar d x = 1 := by
  rw [centered_facet_face_eq_face_set, mem_face_set_iff]
  constructor
  · rintro ⟨hxK, hxface⟩
    refine ⟨hxK, ?_⟩
    rw [centered_facet_functional, dotProduct_sub]
    linarith
  · rintro ⟨hxK, hxface⟩
    refine ⟨hxK, ?_⟩
    rw [centered_facet_functional, dotProduct_sub] at hxface
    linarith

/-- A centered facet presentation of `K` at `xbar` is a normalized finite family of facet
inequalities whose associated equality sets are exactly the facets of `K`. -/
def IsCenteredFacetPresentation
    {t : ℕ}
    (K : Set (Fin p → ℝ))
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ) : Prop :=
  K = centered_polyhedron_of_normals xbar normals ∧
    (∀ i : Fin t, IsFacetOf K (centered_facet_face xbar K (normals i))) ∧
    ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
      ∃! i : Fin t, F = centered_facet_face xbar K (normals i)

/-- `IsCenteredFacetPresentation K xbar normals` unfolds to a normalized facet presentation whose
equality faces are exactly the facets of `K`. -/
theorem isCenteredFacetPresentation_iff
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ} :
    IsCenteredFacetPresentation K xbar normals ↔
      K = centered_polyhedron_of_normals xbar normals ∧
        (∀ i : Fin t, IsFacetOf K (centered_facet_face xbar K (normals i))) ∧
        ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
          ∃! i : Fin t, F = centered_facet_face xbar K (normals i) :=
  Iff.rfl

namespace IsCenteredFacetPresentation

/-- A centered facet presentation identifies `K` with the normalized centered inequality system
cut out by its indexed facet normals. -/
theorem eq_centered_polyhedron_of_normals
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals) :
    K = centered_polyhedron_of_normals xbar normals :=
  h.1

/-- Every indexed equality face in a centered facet presentation is a facet of `K`. -/
theorem isFacetOf
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals)
    (i : Fin t) :
    IsFacetOf K (centered_facet_face xbar K (normals i)) :=
  h.2.1 i

/-- Every facet of `K` appears exactly once among the indexed centered equality faces. -/
theorem existsUnique_index
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals)
    (F : Set (Fin p → ℝ))
    (hF : IsFacetOf K F) :
    ∃! i : Fin t, F = centered_facet_face xbar K (normals i) :=
  h.2.2 F hF

end IsCenteredFacetPresentation

/-- Theorem 6.20 (1). Let `K ⊆ ℝ^p` be a `ℤ^p`-free polyhedron containing `xbar` in its
interior. Then `K` admits a normalized centered facet presentation
`K = {x | ∑ h, d_h^i * (x_h - xbar_h) ≤ 1 for all i}`, and this presentation is unique up to a
reindexing of the facet normals. -/
theorem exists_unique_centered_facet_presentation_up_to_reindexing
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    (hK_polyhedron : is_polyhedron K)
    (hK_lattice_free : is_lattice_free K)
    (hxbar_mem : xbar ∈ interior K) :
    ∃ t : ℕ, ∃ _ : NeZero t, ∃ normals : Fin t → Fin p → ℝ,
      IsCenteredFacetPresentation K xbar normals ∧
        ∀ t' : ℕ, ∀ _ : NeZero t', ∀ normals' : Fin t' → Fin p → ℝ,
          IsCenteredFacetPresentation K xbar normals' →
            ∃ e : Fin t ≃ Fin t', ∀ i : Fin t, normals' (e i) = normals i := sorry

/-- Theorem 6.20 (2). If `K` is written by a normalized centered facet presentation, then the
single-ray Section 6.2 intersection-cut coefficient
`IntersectionCut.intersection_cut_coeff K xbar (fun _ : Fin 1 ↦ r) 0` is the maximum of the dot
products of the facet normals with the ray direction `r`. -/
theorem intersection_cut_coeff_eq_sup_facet_normal_dotProduct
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    [NeZero t]
    (normals : Fin t → Fin p → ℝ)
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    (r : Fin p → ℝ) :
    IntersectionCut.intersection_cut_coeff K xbar (fun _ : Fin 1 ↦ r) 0 =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin t ↦ normals i ⬝ᵥ r) := sorry

end Theorem620
