import Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18

noncomputable section

open SimpleGraph
open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

-- This file keeps the source-facing subtour-elimination cut objects, but reuses the Chapter 3
-- complete-graph cut owner `cutIncidenceVector`, the Chapter 7 traveling-salesman owner
-- `travelingSalesmanPolytope`, and the Chapter 3 facet owner `IsFacetOf`.

section Theorem719

/-- The boundary edge set `δ(S)` of a vertex subset `S` in the complete graph on `Fin n`. -/
abbrev edge_boundary_finset {n : ℕ} (S : Finset (Fin n)) : Finset (complete_graph_edges n) :=
  Finset.univ.filter
    fun e ↦ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n))

notation "δ(" S ")" => edge_boundary_finset S

/-- The complete-graph cut notation `δ(S)` is the Chapter 4 cut-edge finset specialized to
`completeGraph (Fin n)` and reindexed along `completeGraphEdge`. -/
theorem mem_edge_boundary_finset_iff_mem_cutEdgeFinset
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) := by
  simp [edge_boundary_finset]

/-- Membership in `δ(S)` means that the edge admits one endpoint in `S` and the other outside
`S`. -/
theorem mem_edge_boundary_finset_iff_mixed_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = e.1 := by
  simpa [completeGraphEdge] using
    (mem_cutEdgeFinset_iff (completeGraph (Fin n)) :
      completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) ↔
        ∃ u ∈ (S : Set (Fin n)), ∃ v ∉ (S : Set (Fin n)), s(u, v) = completeGraphEdge e)

/-- Membership in `δ(S)` is equivalent to saying that the two canonical `Sym2.out` endpoints of
`e` lie on opposite sides of the cut. -/
theorem mem_edge_boundary_finset_iff_out_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_edge_boundary_finset_iff_mixed_endpoints S e).1 he with ⟨u, hu, v, hv, huv⟩
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Membership in `δ(S)` means that the canonical cut-incidence vector of `S` takes value `1` on
that edge coordinate. -/
theorem mem_edge_boundary_finset_iff
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ cutIncidenceVector S e = 1 := by
  rw [mem_edge_boundary_finset_iff_out_endpoints]
  have hpair :
      cutIncidenceVector S e =
        if (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) then 0 else 1 := by
    simpa [e.1.out_eq] using
      (cutIncidenceVector_apply_pair S e.1.out.1 e.1.out.2 (by simpa [e.1.out_eq] using e.2))
  rw [hpair]
  by_cases h₁ : e.1.out.1 ∈ S
  · by_cases h₂ : e.1.out.2 ∈ S
    · have hsame :
          (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) := by
        exact propext (by simp [h₁, h₂])
      simp [h₁, h₂]
    · have hdiff :
          (e.1.out.1 ∈ S) ≠ (e.1.out.2 ∈ S) := by
        intro hsame
        exact h₂ (hsame ▸ h₁)
      simp [h₁, h₂]
  · by_cases h₂ : e.1.out.2 ∈ S
    · have hdiff :
          (e.1.out.1 ∈ S) ≠ (e.1.out.2 ∈ S) := by
        intro hsame
        exact h₁ (hsame ▸ h₂)
      simp [h₁, h₂]
    · have hsame :
          (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) := by
        exact propext (by simp [h₁, h₂])
      simp [h₁, h₂]

/-- The left-hand side `∑_{e ∈ δ(S)} x_e` of the subtour-elimination constraint associated with
`S`. -/
def subtour_elimination_value
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) : ℝ :=
  Finset.sum (δ(S)) x

/-- Every coordinate of the canonical cut-incidence vector is either `0` or `1`. -/
theorem cutIncidenceVector_eq_zero_or_one
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rw [cutIncidenceVector_apply_pair S u v he]
      by_cases huv : (u ∈ S) = (v ∈ S) <;> simp [huv]

/-- The canonical cut-incidence vector is the indicator of the boundary-edge finset `δ(S)`. -/
theorem cutIncidenceVector_eq_indicator_edge_boundary
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = if e ∈ δ(S) then 1 else 0 := by
  by_cases he : e ∈ δ(S)
  · simpa [he] using (mem_edge_boundary_finset_iff S e).mp he
  · rcases cutIncidenceVector_eq_zero_or_one S e with hzero | hone
    · simp [he, hzero]
    · exfalso
      exact he ((mem_edge_boundary_finset_iff S e).2 hone)

/-- `subtour_elimination_value S x` is the sum of the coordinates of `x` over the cut `δ(S)`. -/
theorem subtour_elimination_value_eq
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = Finset.sum (δ(S)) x :=
  rfl

/-- The source-facing subtour-elimination sum is the canonical dot product with the cut-incidence
vector of `S`. -/
theorem subtour_elimination_value_eq_dotProduct
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = cutIncidenceVector S ⬝ᵥ x := by
  symm
  calc
    cutIncidenceVector S ⬝ᵥ x
        = ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e := by
            simp [dotProduct, cutIncidenceVector_eq_indicator_edge_boundary]
    _ = Finset.sum (δ(S)) x := by
          calc
            ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e
                = ∑ e : complete_graph_edges n, if e ∈ δ(S) then x e else 0 := by
                    refine Finset.sum_congr rfl fun e _ ↦ ?_
                    by_cases he : e ∈ δ(S) <;> simp [he]
            _ = Finset.sum (δ(S)) x := by
                  have huniv :
                      Finset.univ.filter
                          (fun e : complete_graph_edges n ↦ e ∈ δ(S)) = δ(S) := by
                    ext e
                    simp
                  rw [← huniv, Finset.sum_filter]
                  simp
    _ = subtour_elimination_value S x := by
          rw [subtour_elimination_value]

/-- The equality face of the traveling salesman polytope cut out by the subtour-elimination
constraint for `S`. -/
def subtour_elimination_face (n : ℕ) (S : Finset (Fin n)) :
    Set (complete_graph_edges n → ℝ) :=
  {x | x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2}

/-- Membership in `subtour_elimination_face n S` means belonging to the traveling salesman
polytope and meeting the subtour-elimination inequality at equality. -/
theorem mem_subtour_elimination_face_iff
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2 :=
  Iff.rfl

/-- The source-facing equality face is equivalently the equality set of the canonical valid
inequality `(-cutIncidenceVector S) ⬝ᵥ x ≤ -2`. -/
theorem mem_subtour_elimination_face_iff_neg_cutIncidence
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ (-cutIncidenceVector S) ⬝ᵥ x = -2 := by
  rw [mem_subtour_elimination_face_iff, subtour_elimination_value_eq_dotProduct]
  constructor
  · rintro ⟨hx, hxeq⟩
    exact ⟨hx, by rw [neg_dotProduct, hxeq]⟩
  · rintro ⟨hx, hxeq⟩
    have hxeq' : cutIncidenceVector S ⬝ᵥ x = 2 := by
      simpa [neg_dotProduct] using congrArg Neg.neg hxeq
    exact ⟨hx, hxeq'⟩

/-- Theorem 7.19. For `S ⊆ V = Fin n` with `2 ≤ |S| ≤ n - 2`, the subtour-elimination
constraint `∑_{e ∈ δ(S)} x_e ≥ 2` is valid on the traveling salesman polytope on `n ≥ 4`
nodes. -/
theorem subtour_elimination_constraint_valid
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2)
    {x : complete_graph_edges n → ℝ}
    (hx : x ∈ travelingSalesmanPolytope n) :
    2 ≤ subtour_elimination_value S x := sorry

/-- The subtour-elimination inequality in the canonical Chapter 3 valid-inequality owner form. -/
theorem subtour_elimination_is_valid_inequality
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    is_valid_inequality (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2) := by
  rw [is_valid_inequality_iff]
  intro x hx
  have hvalid := subtour_elimination_constraint_valid hn S hS_lower hS_upper hx
  simpa [subtour_elimination_value_eq_dotProduct, dotProduct_neg] using neg_le_neg hvalid

/-- Theorem 7.19. For `S ⊆ V = Fin n` with `2 ≤ |S| ≤ n - 2`, the equality face cut out by
`∑_{e ∈ δ(S)} x_e = 2` is a facet of the traveling salesman polytope on `n ≥ 4` nodes. -/
theorem subtour_elimination_face_isFacetOf
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n S) := sorry

end Theorem719
