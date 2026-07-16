import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_41

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the exercise
-- is matched directly against the local formalization of Proposition 5.41.

/-- Exercise 5.42: this exercise asks for the proof of Proposition 5.41. In this item-per-file
formalization, the first recalled atomic statement says that inward-pointing vectors are exactly
those with positive distinguished boundary coordinate. -/
recall inward_pointing_iff_boundary_coordinate_component_pos

/- Outward-pointing vectors are exactly those with negative distinguished boundary coordinate. -/
recall outward_pointing_iff_boundary_coordinate_component_neg

/- Boundary-tangent vectors are exactly those with zero distinguished boundary coordinate. -/
recall tangent_to_boundary_iff_boundary_coordinate_component_eq_zero

/- Every boundary tangent vector is tangent to the boundary, inward-pointing,
or outward-pointing. -/
recall boundary_vector_trichotomy

/- A boundary-tangent vector is not inward-pointing. -/
recall tangent_to_boundary_not_inward_pointing

/- A boundary-tangent vector is not outward-pointing. -/
recall tangent_to_boundary_not_outward_pointing

/- An inward-pointing tangent vector is not outward-pointing. -/
recall inward_pointing_not_outward_pointing

/- Negating a tangent vector exchanges inward- and outward-pointing. -/
recall inward_pointing_iff_neg_outward_pointing
