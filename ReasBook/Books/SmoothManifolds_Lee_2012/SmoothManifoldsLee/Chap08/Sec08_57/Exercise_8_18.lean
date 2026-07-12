import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Example_8_17
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Proposition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth vector fields and `F`-relatedness along smooth maps;
-- * source-facing owner: `VectorField.f_related`;
-- * derived API sampled before refinement: `f_related_iff_mfderiv_comp_eq`;
-- * exact upstream owner for part (1): `example_8_17_d_dt_related_rotation_field`.
-- Primitive data here is only the circle map and the two vector fields from Example 8.17; this
-- exercise should therefore reuse the existing owner theorem directly instead of keeping a
-- duplicate local wrapper.

/-
Exercise 8.18 (1): directly from the definition, the vector field `d/dt` on `ℝ` is
`example_8_17_circle_parametrization`-related to the rotation field
`Y = x ∂/∂y - y ∂/∂x` on `ℝ²`. This is exactly Example 8.17's existing owner theorem.
-/
recall example_8_17_d_dt_related_rotation_field

/-
Exercise 8.18 (2): Proposition 8.16 recovers the same `F`-relatedness statement from the
test-function characterization.
-/
example :
    VectorField.f_related
      example_8_17_circle_parametrization
      example_8_17_d_dt
      example_8_17_rotation_field := by
  exact
    (f_related_iff_mfderiv_comp_eq example_8_17_circle_parametrization_contMDiff).2 <|
      (f_related_iff_mfderiv_comp_eq example_8_17_circle_parametrization_contMDiff).1
        example_8_17_d_dt_related_rotation_field
