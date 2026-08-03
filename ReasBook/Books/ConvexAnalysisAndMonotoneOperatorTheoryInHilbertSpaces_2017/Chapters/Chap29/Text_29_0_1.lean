import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap06.Proposition_6_47

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Text 29.0.1 recalls the classical characterization of the projection `P_C x`
  onto a nonempty closed convex set `C` by the variational inequality (29.1), and equivalently by
  membership of the residual `x - P_C x` in the normal cone at the projection point.
- `core/canonical`: the project owners are
  `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` from
  Chapter 3 and `eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex` from
  Chapter 6.
- `bridge/view`: this chapter-opening text adds no new theorem beyond those owner statements, so
  the item is a direct owner check rather than a second wrapper theorem.

Primitive data: none beyond the nonempty closed convex set and ambient Hilbert-space point already
owned by the recalled theorems.
Derived API: none; later Chapter 29 files can reuse the existing owner theorems directly. -/

/- Text 29.0.1: the chapter-opening characterization of `P_C x` is exactly the existing
projection-point variational-inequality theorem and its equivalent normal-cone reformulation, so
this item is a direct owner check. -/
#check eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
#check eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
