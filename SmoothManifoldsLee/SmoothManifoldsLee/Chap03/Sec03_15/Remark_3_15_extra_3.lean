import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 3.15-extra-3: for a smooth map between manifolds with corners, `MDifferentiableAt.mfderiv`
identifies the manifold derivative with the derivative in preferred coordinates of
`writtenInExtChartAt I I' p F`, taken as `fderivWithin` on the model range `range I` at
`extChartAt I p p`. This is the correct general coordinate statement: outside the model-space case
one should not read it as an unrestricted Fréchet derivative on the whole ambient model vector
space. The companion recall `mfderiv_eq_fderiv` is the specialization to the trivial/model-space
manifold structure, where the coordinate representative is just `F`, so one recovers the usual
total derivative and, in Euclidean coordinates, the Jacobian matrix. -/
recall MDifferentiableAt.mfderiv

recall mfderiv_eq_fderiv
