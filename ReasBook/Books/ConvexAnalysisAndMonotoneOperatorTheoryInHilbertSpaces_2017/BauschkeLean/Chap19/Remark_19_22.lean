import BauschkeLean.Chap19.Proposition_19_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/- Source/core/bridge triage:
- `source-facing`: Remark 19.22 records two points about a saddle point for the
  equality-constraint perturbation: the terminology that `v̄` is a Lagrange multiplier for `x̄`,
  and the fact that `x̄` solves the unconstrained affine minimization problem (19.43).
- `core/canonical`: the owner theorem for the mathematical content is
  `mem_argmin_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation` in
  `Proposition_19_21`.
- `bridge/view`: this remark adds no new owner or wrapper API; it is a direct recall of those
  canonical consequences.

Primitive data: none beyond the saddle-point hypothesis already owned by the proposition file.
Derived API: none; the numbered remark is exactly these owner-level consequences. -/

/- Remark 19.22 recalls that a saddle point yields the affine-objective minimizer statement,
while the phrase "Lagrange multiplier" is terminology rather than new theorem content. -/
#check mem_argmin_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation

end ERealFunction
