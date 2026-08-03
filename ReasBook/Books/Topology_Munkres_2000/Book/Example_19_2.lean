module

import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct
public import Topology_Munkres_2000.Book.Proposition_19_1

public section

open scoped CartesianProduct Topology

/-- The box whose `n`th coordinate interval is `(-1 / (n + 1), 1 / (n + 1))`. -/
def shrinkingRealBox : Set (ℕ → ℝ) :=
  ∏ n, Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))

/-- The constant-sequence diagonal is continuous for the product topology. -/
theorem continuous_realSequenceDiagonal :
    Continuous (Function.const ℕ : ℝ → ℕ → ℝ) := by
  -- Continuity into the product is checked independently in every coordinate.
  apply continuous_pi
  intro n
  simpa only [Function.const_apply] using (continuous_id' : Continuous (fun t : ℝ ↦ t))

/-- The shrinking coordinate box is open for the box topology. -/
theorem isOpen_shrinkingRealBox :
    IsOpen[Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)] shrinkingRealBox := by
  -- Each coordinate interval is open, so their full box is box-open.
  exact Pi.isOpen_box (fun n : ℕ ↦
    Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) (fun _ ↦ isOpen_Ioo)

/-- The inverse image of the shrinking box under the diagonal is the singleton `{0}`. -/
theorem preimage_shrinkingRealBox :
    (Function.const ℕ : ℝ → ℕ → ℝ) ⁻¹' shrinkingRealBox = ({0} : Set ℝ) := by
  -- Membership in the preimage means lying in every shrinking coordinate interval.
  ext t
  constructor
  · intro ht
    simp only [Set.mem_singleton_iff]
    by_contra ht0
    -- A nonzero real has positive absolute value, eventually exceeding a box radius.
    have habsPos : 0 < |t| := abs_pos.mpr ht0
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt habsPos
    have hcoord := ht n (Set.mem_univ n)
    have habsLt : |t| < 1 / ((n : ℝ) + 1) := (abs_lt).mpr hcoord
    exact lt_asymm hn habsLt
  · intro ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    -- Zero lies strictly between the endpoints of every positive coordinate radius.
    intro n hn
    have hradius : 0 < 1 / ((n : ℝ) + 1) := by
      positivity
    constructor
    · exact neg_lt_zero.mpr hradius
    · exact hradius

/-- Example 19.2: the constant-sequence diagonal is not continuous for the box topology. -/
theorem notContinuous_realSequenceDiagonal_box :
    ¬ Continuous[_, Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)]
      (Function.const ℕ : ℝ → ℕ → ℝ) := by
  intro hcontinuous
  -- Continuity would make the singleton preimage of the open shrinking box open.
  have hopen : IsOpen ((Function.const ℕ : ℝ → ℕ → ℝ) ⁻¹' shrinkingRealBox) :=
    @Continuous.isOpen_preimage ℝ (ℕ → ℝ) inferInstance
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) _ hcontinuous shrinkingRealBox
      isOpen_shrinkingRealBox
  rw [preimage_shrinkingRealBox] at hopen
  exact not_isOpen_singleton 0 hopen
