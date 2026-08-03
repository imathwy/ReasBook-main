import BauschkeLean.Chap06.Proposition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Example 27.10 observes that Proposition 27.8, specialized to the shifted
  half-squared norm `y ↦ ‖y - x‖^2 / 2`, recovers the standard metric-projection criterion.
- `core/canonical`: the project owner for that projection criterion is
  `eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex`.
- `bridge/view`: the Chapter 27 example adds no new public owner beyond identifying that the
  specialized Chapter 27 optimality system is exactly the existing Chapter 6 theorem.

The refined file therefore deletes the duplicate wrapper theorem and reuses the existing canonical
owner directly. -/

/- Example 27.10: after specializing Proposition 27.8 to the shifted half-squared norm, the
result is exactly the canonical projection/normal-cone criterion from Chapter 6. -/
#check eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
