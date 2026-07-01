import Nesterov.Chap05.Definition_5_4_7_6
import Nesterov.Chap05.Definition_5_4_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpaceLp

/- Theorem 5.4.7.5 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-cone domain.

Sampled owner declarations:
* `EuclideanSpace.LpExponent` from `Definition_3_7`, the project owner for admissible
  finite-dimensional `ℓ_p` exponents `1 ≤ p < ∞`;
* `EuclideanSpace.lpSeminorm` and `EuclideanSpace.lpNorm_eq_sum` from `Definition_3_7`, the
  intrinsic finite-dimensional `ℓ_p` owner and its textbook notation surface `‖z‖_[p]`;
* `lpNormEpigraphCone` and `mem_lpNormEpigraphCone_iff` from `Definition_5_4_7_6`, the
  coordinate-model epigraph bridge sitting underneath the intrinsic norm inequality;
* `lpEpigraphConeLiftDomain` and `mem_lpEpigraphConeLiftDomain_iff` from
  `Definition_5_4_7_7`, the chapter owner for the lifted-domain witness data;
* `WithLp.toLp`, the canonical coordinate norm owner used internally by
  `lpNormEpigraphCone`.

Source/core/bridge triage:
* source-facing: membership of `(τ, z)` in the epigraph owner `lpNormEpigraphCone n p`;
* core/canonical: the owner seminorm `EuclideanSpace.lpSeminorm n p`;
* bridge/view: the coordinate epigraph owner `lpNormEpigraphCone n (p : ENNReal)` and the
  lifted witness
  domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`.

Primitive data:
* the admissible exponent `p : EuclideanSpace.LpExponent`;
* the epigraph point `(τ, z) : ℝ × EuclideanSpace ℝ (Fin n)`.

Derived API:
* the source-facing epigraph membership `(τ, z) ∈ lpNormEpigraphCone n p`;
* the intrinsic inequality bridge `mem_lpNormEpigraphCone_iff`;
* the lifted witness domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`;
* the coordinatewise witness inequalities, recovered from
  `mem_lpEpigraphConeLiftDomain_iff` when needed.

This theorem therefore lives on the Chapter 5 epigraph owner surface `lpNormEpigraphCone`, while
the intrinsic inequality `‖z‖_[p] ≤ τ` is kept only as the upstream bridge
`mem_lpNormEpigraphCone_iff`. The lifted witness set remains a genuine bridge layer rather than a
competing public owner. -/

-- Proof sketch: the main theorem is stated directly on the epigraph owner
-- `lpNormEpigraphCone n p`. For the forward direction, construct a lift `(τ, x, z)` in
-- `lpEpigraphConeLiftDomain n (1 / p.toReal)` by choosing the standard coordinate witness `x`
-- from the finite-dimensional `ℓ_p` norm formula. For the reverse direction, unpack the lift with
-- `mem_lpEpigraphConeLiftDomain_iff`, raise the coordinate inequalities to the power
-- `p.toReal`, sum over `i`, use `∑ i, x i = τ`, and finally read the result back through
-- `mem_lpNormEpigraphCone_iff` when needed.
/-- Theorem 5.4.7.5: a point `(τ, z)` lies in the finite-dimensional `ℓ_p` epigraph cone exactly
when it admits a lift to the chapter’s lifted domain with exponent `1 / p.toReal`. -/
theorem mem_lpNormEpigraphCone_iff_exists_lift
    {n : ℕ} (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    (τ, z) ∈ lpNormEpigraphCone n p ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) :=
  sorry

/-- The intrinsic inequality form of Theorem 5.4.7.5, read through the epigraph-owner bridge
`mem_lpNormEpigraphCone_iff`. -/
theorem lpSeminorm_le_iff_exists_lift
    {n : ℕ} (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    ‖z‖_[p] ≤ τ ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) := by
  rw [← mem_lpNormEpigraphCone_iff]
  exact mem_lpNormEpigraphCone_iff_exists_lift p
