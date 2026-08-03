module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting
public import Topology_Munkres_2000.Book.Definition_74_4.Scheme

public section

namespace NonorientableSurfacePresentation

noncomputable section

/-- The signed boundary letter in position `i` of the standard nonorientable word. -/
def boundaryLetter (i : ℕ) : ℕ × Bool :=
  (i / 2 + 1, true)

/-- The explicit word `(a₁ a₁) ⋯ (aₘ aₘ)`. -/
def boundaryLetters (m : ℕ) : List (ℕ × Bool) :=
  List.ofFn (fun i : Fin (2 * m) ↦ boundaryLetter i)

/-- The standard nonorientable word has `2 * m` letters. -/
theorem boundaryLetters_length (m : ℕ) : (boundaryLetters m).length = 2 * m := by
  -- `List.ofFn` has one entry for each index of `Fin (2 * m)`.
  simp [boundaryLetters]

/-- The standard nonorientable word has at least three letters when `1 < m`. -/
theorem boundaryLetters_minLength (m : ℕ) (hm : 1 < m) :
    3 ≤ (boundaryLetters m).length := by
  -- Replace the word length by its edge count and use the lower bound on `m`.
  rw [boundaryLetters_length]
  omega

/-- The standard nonorientable boundary word, regarded as a polygon word. -/
def boundaryWord (m : ℕ) (hm : 1 < m) : PolygonWord ℕ :=
  ⟨boundaryLetters m, boundaryLetters_minLength m hm⟩

/-- The underlying list of the standard nonorientable boundary word. -/
theorem boundaryWord_val (m : ℕ) (hm : 1 < m) :
    (boundaryWord m hm).val = boundaryLetters m := by
  -- The polygon-word constructor stores `boundaryLetters m` as its value field.
  rfl

/-- The singleton labelling scheme for the standard nonorientable polygon. -/
def scheme (m : ℕ) (hm : 1 < m) : LabellingScheme ℕ :=
  {boundaryWord m hm}

/-- A polygon word belongs to the standard scheme exactly when it is the boundary word. -/
theorem mem_scheme_iff (m : ℕ) (hm : 1 < m) (word : PolygonWord ℕ) :
    word ∈ scheme m hm ↔ word = boundaryWord m hm := by
  -- Membership in the singleton scheme is equality with its unique word.
  simp only [scheme, Multiset.mem_singleton]

/-- The lifted arguments of the vertices of the standard regular `2 * m`-gon. -/
def angles (m : ℕ) (i : Fin (2 * m + 1)) : ℝ :=
  2 * Real.pi * i / (2 * m)

/-- The standard nonorientable polygon has at least three edges when `1 < m`. -/
theorem three_le_edgeCount (m : ℕ) (hm : 1 < m) : 3 ≤ 2 * m := by
  -- At least two two-edge blocks supply at least four edges.
  omega

/-- The lifted vertex arguments of the standard polygon are strictly increasing. -/
theorem angles_strictMono (m : ℕ) (hm : 1 < m) : StrictMono (angles m) := by
  -- Positive scaling and division preserve the strict order of vertex indices.
  intro i j hij
  rw [angles, angles]
  have denominator_pos : (0 : ℝ) < 2 * m := by
    positivity
  have coefficient_pos : (0 : ℝ) < 2 * Real.pi := by
    positivity
  rw [div_lt_div_iff_of_pos_right denominator_pos]
  exact mul_lt_mul_of_pos_left (Nat.cast_lt.2 hij) coefficient_pos

/-- The final lifted argument closes the standard polygon after one full turn. -/
theorem angles_last (m : ℕ) (hm : 1 < m) :
    angles m (Fin.last (2 * m)) = angles m 0 + 2 * Real.pi := by
  -- The final index equals the denominator, so its angle is one full revolution.
  rw [angles, angles]
  have denominator_pos : (0 : ℝ) < 2 * m := by
    positivity
  field_simp
  norm_num [Fin.last]

/-- The standard regular cyclic `2 * m`-gon used to present the `m`-fold projective plane. -/
def polygon (m : ℕ) (hm : 1 < m) : CyclicPolygon (2 * m) where
  three_le := three_le_edgeCount m hm
  center := 0
  radius := 1
  radius_pos := zero_lt_one
  angles := angles m
  angles_strictMono := angles_strictMono m hm
  angles_last := angles_last m hm

/-- The standard edge pasting with boundary word `(a₁ a₁) ⋯ (aₘ aₘ)`. -/
def pasting (m : ℕ) (hm : 1 < m) : (polygon m hm).EdgePasting ℕ :=
  -- Route correction: the imported `ofSigns` body is opaque here, so expose the same
  -- label and sign data directly to support the boundary-word projection theorem.
  { label := fun i ↦ (boundaryLetter i).1
    orientation := fun i ↦ (polygon m hm).signedOrientation i true
    sign := fun _ ↦ true
    orientation_eq := fun _ ↦ rfl }

/-- The label and orientation of each pasted edge are the corresponding boundary letter. -/
theorem pasting_boundaryLetter (m : ℕ) (hm : 1 < m) (i : Fin (2 * m)) :
    ((pasting m hm).label i, (pasting m hm).sign i) = boundaryLetter i := by
  -- The record projections recover the chosen label and the constant positive sign.
  simp only [pasting, boundaryLetter]

/-- The `m`-fold projective plane is the realization of the standard nonorientable edge pasting. -/
abbrev mFoldProjectivePlane (m : ℕ) (hm : 1 < m) :=
  (pasting m hm).Realization

/-- The canonical map from the standard polygon to the `m`-fold projective plane. -/
abbrev quotientMap (m : ℕ) (hm : 1 < m) :
    (polygon m hm).region → mFoldProjectivePlane m hm :=
  (pasting m hm).quotientMap

/-- The standard polygon has a positive number of vertices when `1 < m`. -/
theorem vertexCount_pos (m : ℕ) (hm : 1 < m) : 0 < 2 * m := by
  -- Multiplying the positive block count by two preserves positivity.
  omega

/-- The first vertex index of the standard polygon. -/
def firstIndex (m : ℕ) (hm : 1 < m) : Fin (2 * m) :=
  ⟨0, vertexCount_pos m hm⟩

/-- The canonical basepoint is the quotient image of the first polygon vertex. -/
def basepoint (m : ℕ) (hm : 1 < m) : mFoldProjectivePlane m hm :=
  quotientMap m hm
    ⟨(polygon m hm).toPolygon.vertices (firstIndex m hm),
      (polygon m hm).vertex_mem_region (firstIndex m hm)⟩

/-- The canonical map to the `m`-fold projective plane is a quotient map. -/
theorem isQuotientMap_quotientMap (m : ℕ) (hm : 1 < m) :
    Topology.IsQuotientMap (quotientMap m hm) :=
  (pasting m hm).isQuotientMap_quotientMap


end

end NonorientableSurfacePresentation
