import BauschkeLean.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/- Source/core/bridge triage:
- `source-facing`: Remark 19.26 extracts the unconstrained argmin consequence of a saddle point
  for the Lagrangian attached to the inequality-constraint perturbation.
- `core/canonical`: the owner theorem is
  `mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation`.
- `bridge/view`: the remark adds no new owner or companion wrapper; it is a direct recall of the
  Chapter 19 owner theorem.

Primitive data: none beyond the saddle-point hypothesis already owned by
`mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation`.
Derived API: none; the numbered remark is exactly that canonical consequence. -/

/- Remark 19.26 is exactly the companion theorem already established in
`Proposition_19_25`. -/
#check mem_argmin_of_isSaddlePointOn_lagrangian_inequalityConstraintPerturbation

end ERealFunction
