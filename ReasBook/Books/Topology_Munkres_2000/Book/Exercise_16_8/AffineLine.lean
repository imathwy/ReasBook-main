module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.DiscreteSubset

public section

open Set

/- Affine lines in products involving the Sorgenfrey line. -/
namespace SorgenfreyAffineLine

/-- A vertical line in the product of the Sorgenfrey line and the usual real line. -/
def euclideanVertical (a : ℝ) : Set (SorgenfreyLine × ℝ) :=
  {point | SorgenfreyLine.toReal point.1 = a}

/-- A nonvertical affine line in the product of the Sorgenfrey line and the usual real line. -/
def euclideanGraph (m b : ℝ) : Set (SorgenfreyLine × ℝ) :=
  {point | point.2 = m * SorgenfreyLine.toReal point.1 + b}

/-- A vertical line in the Sorgenfrey plane. -/
def vertical (a : ℝ) : Set (SorgenfreyLine × SorgenfreyLine) :=
  {point | SorgenfreyLine.toReal point.1 = a}

/-- A nonvertical affine line in the Sorgenfrey plane. -/
def graph (m b : ℝ) : Set (SorgenfreyLine × SorgenfreyLine) :=
  {point | SorgenfreyLine.toReal point.2 = m * SorgenfreyLine.toReal point.1 + b}

/-- Membership in a nonvertical affine line in the Sorgenfrey plane. -/
theorem mem_graph_iff (m b : ℝ) (point : SorgenfreyLine × SorgenfreyLine) :
    point ∈ graph m b ↔
      SorgenfreyLine.toReal point.2 = m * SorgenfreyLine.toReal point.1 + b := Iff.rfl

/-- Helper for Exercise 16.8: a canonical half-open interval is open in the Sorgenfrey line. -/
private lemma isOpen_Ico_sorgenfrey (a b : ℝ) (hab : a < b) :
    IsOpen (Set.Ico a b : Set SorgenfreyLine) := by
  -- Recognize the interval as a member of the lower-limit basis.
  apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
  exact ⟨a, b, hab, rfl⟩

/-- Helper for Exercise 16.8: the carrier map from the Sorgenfrey line to `ℝ` is continuous. -/
private lemma continuousToReal : Continuous SorgenfreyLine.toReal := by
  -- Refine each usual open neighborhood to a lower-limit interval at the same point.
  rw [continuous_def]
  intro s hs
  refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hx
  obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
  refine ⟨Set.Ico (SorgenfreyLine.toReal x) b, ?_, ?_, ?_⟩
  · exact ⟨SorgenfreyLine.toReal x, b, hxab.2, rfl⟩
  · exact Set.left_mem_Ico.mpr hxab.2
  · intro y hy
    exact hab ⟨hxab.1.trans_le hy.1, hy.2⟩

/-- Helper for Exercise 16.8: a nonnegative affine self-map is continuous on the Sorgenfrey line. -/
private lemma continuousAffineToSorgenfreyOfNonneg (m b : ℝ) (hm : 0 ≤ m) :
    Continuous
      (fun x : SorgenfreyLine ↦
        SorgenfreyLine.toReal.symm (m * SorgenfreyLine.toReal x + b)) := by
  -- A zero slope gives a constant map; otherwise use lower-limit basis neighborhoods.
  rcases hm.eq_or_lt with rfl | hmpos
  · simpa only [zero_mul, zero_add] using
      (continuous_const : Continuous (fun _ : SorgenfreyLine ↦ SorgenfreyLine.toReal.symm b))
  · refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.continuous_iff.mpr ?_
    rintro _ ⟨c, d, hcd, rfl⟩
    refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
    intro x hx
    change c ≤ m * SorgenfreyLine.toReal x + b ∧
      m * SorgenfreyLine.toReal x + b < d at hx
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hendpoint : m * ((d - b) / m) = d - b := by
      field_simp
    have hxupper : SorgenfreyLine.toReal x < (d - b) / m := by
      nlinarith
    refine ⟨Set.Ico (SorgenfreyLine.toReal x) ((d - b) / m), ?_, ?_, ?_⟩
    · exact ⟨SorgenfreyLine.toReal x, (d - b) / m, hxupper, rfl⟩
    · exact Set.left_mem_Ico.mpr hxupper
    · intro y hy
      rcases hy with ⟨hylower, hyupper⟩
      change SorgenfreyLine.toReal x ≤ SorgenfreyLine.toReal y at hylower
      change SorgenfreyLine.toReal y < (d - b) / m at hyupper
      change c ≤ m * SorgenfreyLine.toReal y + b ∧
        m * SorgenfreyLine.toReal y + b < d
      constructor
      · nlinarith
      · nlinarith

/-- Helper for Exercise 16.8: the inverse parametrization lies on a Euclidean vertical line. -/
private lemma euclideanVerticalInvFun_mem (a y : ℝ) :
    (SorgenfreyLine.toReal.symm a, y) ∈ euclideanVertical a := by
  -- The carrier equivalence sends its inverse image back to `a`.
  simp only [euclideanVertical, Set.mem_setOf_eq, Equiv.apply_symm_apply]

/-- Helper for Exercise 16.8: the Euclidean vertical parametrization is a left inverse. -/
private lemma euclideanVerticalEquiv_leftInverse (a : ℝ) (point : euclideanVertical a) :
    (⟨(SorgenfreyLine.toReal.symm a, point.1.2),
      euclideanVerticalInvFun_mem a point.1.2⟩ : euclideanVertical a) = point := by
  -- Membership identifies the first coordinate, while the second coordinate is unchanged.
  apply Subtype.ext
  apply Prod.ext
  · apply SorgenfreyLine.toReal.injective
    simpa only [Equiv.apply_symm_apply] using point.property.symm
  · rfl

/-- Helper for Exercise 16.8: the Euclidean vertical parametrization is a right inverse. -/
private lemma euclideanVerticalEquiv_rightInverse (a y : ℝ) :
    (⟨(SorgenfreyLine.toReal.symm a, y), euclideanVerticalInvFun_mem a y⟩ :
      euclideanVertical a).1.2 = y := by
  -- Projection recovers the parameter definitionally.
  rfl

/-- Helper for Exercise 16.8: projection to the second coordinate is continuous. -/
private lemma continuousEuclideanVerticalToFun (a : ℝ) :
    Continuous (fun point : euclideanVertical a ↦ point.1.2) := by
  -- Restrict the continuous second projection to the subtype.
  exact continuous_snd.comp continuous_subtype_val

/-- Helper for Exercise 16.8: the inverse Euclidean vertical parametrization is continuous. -/
private lemma continuousEuclideanVerticalInvFun (a : ℝ) :
    Continuous (fun y : ℝ ↦
      (⟨(SorgenfreyLine.toReal.symm a, y), euclideanVerticalInvFun_mem a y⟩ :
        euclideanVertical a)) := by
  -- Pair a constant first coordinate with the identity, then restrict to the line.
  exact (continuous_const.prodMk continuous_id).subtype_mk _

/-- The second-coordinate parametrization of a vertical line in
`SorgenfreyLine × ℝ`. -/
def euclideanVerticalEquiv (a : ℝ) : euclideanVertical a ≃ ℝ where
  toFun point := point.1.2
  invFun y := ⟨(SorgenfreyLine.toReal.symm a, y), euclideanVerticalInvFun_mem a y⟩
  left_inv := euclideanVerticalEquiv_leftInverse a
  right_inv := euclideanVerticalEquiv_rightInverse a

/-- Helper for Exercise 16.8: the inverse parametrization lies on a Euclidean affine graph. -/
private lemma euclideanGraphInvFun_mem (m b : ℝ) (x : SorgenfreyLine) :
    (x, m * SorgenfreyLine.toReal x + b) ∈ euclideanGraph m b := by
  -- The second coordinate is the defining affine expression.
  rfl

/-- Helper for Exercise 16.8: the Euclidean graph parametrization is a left inverse. -/
private lemma euclideanGraphEquiv_leftInverse (m b : ℝ) (point : euclideanGraph m b) :
    (⟨(point.1.1, m * SorgenfreyLine.toReal point.1.1 + b),
      euclideanGraphInvFun_mem m b point.1.1⟩ : euclideanGraph m b) = point := by
  -- The first coordinate is fixed and membership supplies the second coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact point.property.symm

/-- Helper for Exercise 16.8: the Euclidean graph parametrization is a right inverse. -/
private lemma euclideanGraphEquiv_rightInverse (m b : ℝ) (x : SorgenfreyLine) :
    (⟨(x, m * SorgenfreyLine.toReal x + b), euclideanGraphInvFun_mem m b x⟩ :
      euclideanGraph m b).1.1 = x := by
  -- Projection recovers the parameter definitionally.
  rfl

/-- Helper for Exercise 16.8: projection to the first Sorgenfrey coordinate is continuous. -/
private lemma continuousEuclideanGraphToFun (m b : ℝ) :
    Continuous (fun point : euclideanGraph m b ↦ point.1.1) := by
  -- Restrict the continuous first projection to the subtype.
  exact continuous_fst.comp continuous_subtype_val

/-- Helper for Exercise 16.8: the inverse Euclidean graph parametrization is continuous. -/
private lemma continuousEuclideanGraphInvFun (m b : ℝ) :
    Continuous (fun x : SorgenfreyLine ↦
      (⟨(x, m * SorgenfreyLine.toReal x + b), euclideanGraphInvFun_mem m b x⟩ :
        euclideanGraph m b)) := by
  -- Pair the identity with the continuous real-valued affine coordinate.
  exact (continuous_id.prodMk
    ((continuous_const.mul continuousToReal).add continuous_const)).subtype_mk _

/-- The first-coordinate parametrization of a nonvertical line in
`SorgenfreyLine × ℝ`. -/
def euclideanGraphEquiv (m b : ℝ) : euclideanGraph m b ≃ SorgenfreyLine where
  toFun point := point.1.1
  invFun x := ⟨(x, m * SorgenfreyLine.toReal x + b), euclideanGraphInvFun_mem m b x⟩
  left_inv := euclideanGraphEquiv_leftInverse m b
  right_inv := euclideanGraphEquiv_rightInverse m b

/-- Helper for Exercise 16.8: the inverse parametrization lies on a Sorgenfrey vertical line. -/
private lemma verticalInvFun_mem (a : ℝ) (y : SorgenfreyLine) :
    (SorgenfreyLine.toReal.symm a, y) ∈ vertical a := by
  -- The carrier equivalence sends its inverse image back to `a`.
  simp only [vertical, Set.mem_setOf_eq, Equiv.apply_symm_apply]

/-- Helper for Exercise 16.8: the Sorgenfrey vertical parametrization is a left inverse. -/
private lemma verticalEquiv_leftInverse (a : ℝ) (point : vertical a) :
    (⟨(SorgenfreyLine.toReal.symm a, point.1.2), verticalInvFun_mem a point.1.2⟩ :
      vertical a) = point := by
  -- Membership identifies the first coordinate, while the second coordinate is unchanged.
  apply Subtype.ext
  apply Prod.ext
  · apply SorgenfreyLine.toReal.injective
    simpa only [Equiv.apply_symm_apply] using point.property.symm
  · rfl

/-- Helper for Exercise 16.8: the Sorgenfrey vertical parametrization is a right inverse. -/
private lemma verticalEquiv_rightInverse (a : ℝ) (y : SorgenfreyLine) :
    (⟨(SorgenfreyLine.toReal.symm a, y), verticalInvFun_mem a y⟩ : vertical a).1.2 = y := by
  -- Projection recovers the parameter definitionally.
  rfl

/-- Helper for Exercise 16.8: projection from a Sorgenfrey vertical line is continuous. -/
private lemma continuousVerticalToFun (a : ℝ) :
    Continuous (fun point : vertical a ↦ point.1.2) := by
  -- Restrict the continuous second projection to the subtype.
  exact continuous_snd.comp continuous_subtype_val

/-- Helper for Exercise 16.8: the inverse Sorgenfrey vertical parametrization is continuous. -/
private lemma continuousVerticalInvFun (a : ℝ) :
    Continuous (fun y : SorgenfreyLine ↦
      (⟨(SorgenfreyLine.toReal.symm a, y), verticalInvFun_mem a y⟩ : vertical a)) := by
  -- Pair a constant first coordinate with the identity, then restrict to the line.
  exact (continuous_const.prodMk continuous_id).subtype_mk _

/-- The second-coordinate parametrization of a vertical line in the Sorgenfrey plane. -/
def verticalEquiv (a : ℝ) : vertical a ≃ SorgenfreyLine where
  toFun point := point.1.2
  invFun y := ⟨(SorgenfreyLine.toReal.symm a, y), verticalInvFun_mem a y⟩
  left_inv := verticalEquiv_leftInverse a
  right_inv := verticalEquiv_rightInverse a

/-- Helper for Exercise 16.8: the inverse parametrization lies on a Sorgenfrey affine graph. -/
private lemma graphInvFun_mem (m b : ℝ) (x : SorgenfreyLine) :
    (x, SorgenfreyLine.toReal.symm (m * SorgenfreyLine.toReal x + b)) ∈ graph m b := by
  -- Applying the carrier equivalence recovers the defining affine expression.
  simp only [graph, Set.mem_setOf_eq, Equiv.apply_symm_apply]

/-- Helper for Exercise 16.8: the Sorgenfrey graph parametrization is a left inverse. -/
private lemma graphEquiv_leftInverse (m b : ℝ) (point : graph m b) :
    (⟨(point.1.1, SorgenfreyLine.toReal.symm
        (m * SorgenfreyLine.toReal point.1.1 + b)),
      graphInvFun_mem m b point.1.1⟩ : graph m b) = point := by
  -- The first coordinate is fixed and graph membership identifies the second coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply SorgenfreyLine.toReal.injective
    simpa only [Equiv.apply_symm_apply] using point.property.symm

/-- Helper for Exercise 16.8: the Sorgenfrey graph parametrization is a right inverse. -/
private lemma graphEquiv_rightInverse (m b : ℝ) (x : SorgenfreyLine) :
    (⟨(x, SorgenfreyLine.toReal.symm (m * SorgenfreyLine.toReal x + b)),
      graphInvFun_mem m b x⟩ : graph m b).1.1 = x := by
  -- Projection recovers the parameter definitionally.
  rfl

/-- Helper for Exercise 16.8: projection from a Sorgenfrey affine graph is continuous. -/
private lemma continuousGraphToFun (m b : ℝ) :
    Continuous (fun point : graph m b ↦ point.1.1) := by
  -- Restrict the continuous first projection to the subtype.
  exact continuous_fst.comp continuous_subtype_val

/-- Helper for Exercise 16.8: the inverse nonnegative-slope graph parametrization is continuous. -/
private lemma continuousGraphInvFun (m b : ℝ) (hm : 0 ≤ m) :
    Continuous (fun x : SorgenfreyLine ↦
      (⟨(x, SorgenfreyLine.toReal.symm (m * SorgenfreyLine.toReal x + b)),
        graphInvFun_mem m b x⟩ : graph m b)) := by
  -- Pair the identity with the continuous nonnegative affine coordinate.
  exact (continuous_id.prodMk (continuousAffineToSorgenfreyOfNonneg m b hm)).subtype_mk _

/-- The first-coordinate parametrization of a nonvertical line in the Sorgenfrey plane. -/
def graphEquiv (m b : ℝ) : graph m b ≃ SorgenfreyLine where
  toFun point := point.1.1
  invFun x :=
    ⟨(x, SorgenfreyLine.toReal.symm (m * SorgenfreyLine.toReal x + b)),
      graphInvFun_mem m b x⟩
  left_inv := graphEquiv_leftInverse m b
  right_inv := graphEquiv_rightInverse m b

/-- A vertical line in `SorgenfreyLine × ℝ` is homeomorphic to the usual real line. -/
def euclideanVerticalHomeomorph (a : ℝ) : euclideanVertical a ≃ₜ ℝ where
  toEquiv := euclideanVerticalEquiv a
  continuous_toFun := continuousEuclideanVerticalToFun a
  continuous_invFun := continuousEuclideanVerticalInvFun a

/-- A nonvertical line in `SorgenfreyLine × ℝ` is homeomorphic to the Sorgenfrey line. -/
def euclideanGraphHomeomorph (m b : ℝ) : euclideanGraph m b ≃ₜ SorgenfreyLine where
  toEquiv := euclideanGraphEquiv m b
  continuous_toFun := continuousEuclideanGraphToFun m b
  continuous_invFun := continuousEuclideanGraphInvFun m b

/-- A vertical line in the Sorgenfrey plane is homeomorphic to the Sorgenfrey line. -/
def verticalHomeomorph (a : ℝ) : vertical a ≃ₜ SorgenfreyLine where
  toEquiv := verticalEquiv a
  continuous_toFun := continuousVerticalToFun a
  continuous_invFun := continuousVerticalInvFun a

/-- A line of nonnegative slope in the Sorgenfrey plane is homeomorphic to the Sorgenfrey line. -/
def graphHomeomorphOfNonneg (m b : ℝ) (hm : 0 ≤ m) : graph m b ≃ₜ SorgenfreyLine where
  toEquiv := graphEquiv m b
  continuous_toFun := continuousGraphToFun m b
  continuous_invFun := continuousGraphInvFun m b hm

end SorgenfreyAffineLine
