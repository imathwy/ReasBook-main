module

public import Topology_Munkres_2000.Book.Example_22_2.Hyperbola
public import Mathlib.Topology.Constructions.SumProd
public section

/- Example 22.2 (1): The first-coordinate projection `Prod.fst : ℝ × ℝ → ℝ`
is continuous. -/
#check (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))

/- Example 22.2 (2): The first-coordinate projection `Prod.fst : ℝ × ℝ → ℝ`
is surjective. -/
#check (Prod.fst_surjective : Function.Surjective (Prod.fst : ℝ × ℝ → ℝ))

/- Example 22.2 (3): The first-coordinate projection `Prod.fst : ℝ × ℝ → ℝ`
is an open map. -/
#check (isOpenMap_fst : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ))

namespace ReciprocalHyperbola

/-- Helper for Example 22.2: a point on the reciprocal hyperbola has nonzero first
coordinate. -/
lemma fst_ne_zero_of_mem {point : ℝ × ℝ} (hpoint : point ∈ set) : point.1 ≠ 0 := by
  -- Convert membership to the product equation and rule out a zero first factor.
  have hproduct : point.1 * point.2 = 1 := (mem_set point).mp hpoint
  intro hzero
  rw [hzero, zero_mul] at hproduct
  exact zero_ne_one hproduct

/-- Helper for Example 22.2: a nonzero real and its reciprocal form a point of the
reciprocal hyperbola. -/
lemma reciprocalPair_mem {x : ℝ} (hx : x ≠ 0) : (x, x⁻¹) ∈ set := by
  -- Reduce membership to the standard inverse multiplication identity.
  apply (mem_set (x, x⁻¹)).mpr
  exact mul_inv_cancel₀ hx

/-- Helper for Example 22.2: the named reciprocal hyperbola is the level set where
the coordinate product equals one. -/
lemma set_eq_productOne : set = {point : ℝ × ℝ | point.1 * point.2 = 1} := by
  -- Identify the sets pointwise through the owner-level membership specification.
  ext point
  exact mem_set point

/-- Helper for Example 22.2: the reciprocal hyperbola is closed in `ℝ × ℝ`. -/
theorem isClosed : IsClosed set := by
  -- Present the hyperbola as the equality locus of two continuous functions.
  rw [set_eq_productOne]
  exact isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

/-- Helper for Example 22.2: the first-coordinate image of the reciprocal hyperbola is
the complement of `{0}`. -/
theorem fst_image :
    Prod.fst '' set = ({0}ᶜ : Set ℝ) := by
  -- Prove both inclusions using nonvanishing and the canonical reciprocal witness.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨point, hpoint, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fst_ne_zero_of_mem hpoint
  · intro hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    refine ⟨(x, x⁻¹), reciprocalPair_mem hx, ?_⟩
    rfl

/-- Helper for Example 22.2: the first-coordinate image of the reciprocal hyperbola is
not closed in `ℝ`. -/
theorem fst_image_not_isClosed : ¬ IsClosed (Prod.fst '' set) := by
  -- Rewrite the image as the punctured line, whose complement is the non-open singleton zero.
  rw [fst_image]
  intro hclosed
  have singleton_open : IsOpen ({0} : Set ℝ) := by
    simpa only [compl_compl] using hclosed.isOpen_compl
  exact not_isOpen_singleton 0 singleton_open

/-- Example 22.2 (7): The first-coordinate projection `Prod.fst : ℝ × ℝ → ℝ`
is not a closed map. -/
theorem fst_not_isClosedMap : ¬ IsClosedMap (Prod.fst : ℝ × ℝ → ℝ) := by
  -- Route correction: consume the exported hyperbola specification instead of duplicating it.
  intro hclosedMap
  -- A closed projection would send the named closed hyperbola to a closed image.
  have image_closed : IsClosed (Prod.fst '' set) := hclosedMap set isClosed
  exact fst_image_not_isClosed image_closed

end ReciprocalHyperbola

end
