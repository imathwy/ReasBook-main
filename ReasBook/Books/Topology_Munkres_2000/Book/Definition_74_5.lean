module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting

public section

namespace OrientableSurfacePresentation

noncomputable section

/-- Helper for Definition 74.5: the signed boundary letter in position `i` of the
standard orientable word. -/
def boundaryLetter (i : ℕ) : (ℕ × Bool) × Bool :=
  match i % 4 with
  | 0 => ((i / 4 + 1, false), true)
  | 1 => ((i / 4 + 1, true), true)
  | 2 => ((i / 4 + 1, false), false)
  | _ => ((i / 4 + 1, true), false)

/-- Helper for Definition 74.5: the lifted arguments of the vertices of the standard
regular `4 * n`-gon. -/
def angles (n : ℕ) (i : Fin (4 * n + 1)) : ℝ :=
  2 * Real.pi * i / (4 * n)

/-- Helper for Definition 74.5: the standard orientable polygon has at least three
edges when `0 < n`. -/
theorem three_le_edgeCount (n : ℕ) (hn : 0 < n) : 3 ≤ 4 * n := by
  -- A positive number of four-edge blocks supplies at least four edges.
  omega

/-- Helper for Definition 74.5: the lifted vertex arguments of the standard polygon
are strictly increasing. -/
theorem angles_strictMono (n : ℕ) (hn : 0 < n) : StrictMono (angles n) := by
  -- Positive scaling and division preserve the strict order of vertex indices.
  intro i j hij
  rw [angles, angles]
  have denominator_pos : (0 : ℝ) < 4 * n := by
    positivity
  have coefficient_pos : (0 : ℝ) < 2 * Real.pi := by
    positivity
  rw [div_lt_div_iff_of_pos_right denominator_pos]
  exact mul_lt_mul_of_pos_left (Nat.cast_lt.2 hij) coefficient_pos

/-- Helper for Definition 74.5: the final lifted argument closes the standard polygon
after one full turn. -/
theorem angles_last (n : ℕ) (hn : 0 < n) :
    angles n (Fin.last (4 * n)) = angles n 0 + 2 * Real.pi := by
  -- The last index equals the denominator, so its angle is one full revolution.
  rw [angles, angles]
  have denominator_pos : (0 : ℝ) < 4 * n := by
    positivity
  field_simp
  norm_num [Fin.last]

/-- Helper for Definition 74.5: the standard regular cyclic `4 * n`-gon used to
present the `n`-fold torus. -/
def polygon (n : ℕ) (hn : 0 < n) : CyclicPolygon (4 * n) where
  three_le := three_le_edgeCount n hn
  center := 0
  radius := 1
  radius_pos := zero_lt_one
  angles := angles n
  angles_strictMono := angles_strictMono n hn
  angles_last := angles_last n hn

/-- Helper for Definition 74.5: the standard edge pasting with boundary word
`(a₁ b₁ a₁⁻¹ b₁⁻¹) ⋯ (aₙ bₙ aₙ⁻¹ bₙ⁻¹)`. -/
def pasting (n : ℕ) (hn : 0 < n) : (polygon n hn).EdgePasting (ℕ × Bool) :=
  .ofSigns (polygon n hn) (fun i ↦ (boundaryLetter i).1)
    (fun i ↦ (boundaryLetter i).2)

/-- Definition 74.5: The `n`-fold torus is the realization of the standard orientable
edge pasting with boundary word
`(a₁ b₁ a₁⁻¹ b₁⁻¹) ⋯ (aₙ bₙ aₙ⁻¹ bₙ⁻¹)`. -/
abbrev nFoldTorus (n : ℕ) (hn : 0 < n) :=
  (pasting n hn).Realization

/-- Helper for Definition 74.5: the canonical map from the standard polygon to the
`n`-fold torus. -/
abbrev quotientMap (n : ℕ) (hn : 0 < n) :
    (polygon n hn).region → nFoldTorus n hn :=
  (pasting n hn).quotientMap

/-- Helper for Definition 74.5: the standard polygon has a positive number of
vertices when `0 < n`. -/
theorem vertexCount_pos (n : ℕ) (hn : 0 < n) : 0 < 4 * n := by
  -- Multiplying the positive block count by four preserves positivity.
  omega

/-- Helper for Definition 74.5: the first vertex index of the standard polygon. -/
def firstIndex (n : ℕ) (hn : 0 < n) : Fin (4 * n) :=
  ⟨0, vertexCount_pos n hn⟩

/-- Helper for Definition 74.5: the canonical basepoint is the quotient image of the
first polygon vertex. -/
def basepoint (n : ℕ) (hn : 0 < n) : nFoldTorus n hn :=
  quotientMap n hn
    ⟨(polygon n hn).toPolygon.vertices (firstIndex n hn),
      (polygon n hn).vertex_mem_region (firstIndex n hn)⟩

/-- Helper for Definition 74.5: the canonical map to the `n`-fold torus is a quotient
map. -/
theorem isQuotientMap_quotientMap (n : ℕ) (hn : 0 < n) :
    Topology.IsQuotientMap (quotientMap n hn) :=
  (pasting n hn).isQuotientMap_quotientMap


end

end OrientableSurfacePresentation
