import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: LinearRepresentations_Serre_1977's continuous rotation group `C_infty`, written via angles modulo `2π`
  together with its invariant measure;
- `core/canonical`: the additive circle owner `Real.Angle = AddCircle (2 * π)`;
- `bridge/view`: `Real.Angle.toCircle` realizes an angle class as the corresponding unit complex
  rotation, while the measure statements are recalled from the generic `AddCircle` API specialized
  at period `2 * π`.

This file therefore introduces no primitive data or parallel wrapper API: it only recalls the
canonical owner and its standard bridge/measure declarations already present in mathlib. -/

/- Definition 5-5.2-1: the group `C_infty` of plane rotations is modeled by the canonical
additive circle `Real.Angle = ℝ / 2πℤ`, so composing rotations corresponds to adding angles
modulo `2π`. -/
recall Real.Angle

/- The rotation `r_α` through angle `α`, with `α` taken modulo `2π`, is represented by the
canonical map `Real.Angle.toCircle : Real.Angle → Circle` to the unit complex numbers. -/
recall Real.Angle.toCircle

/- The canonical normalized Haar measure on `Real.Angle = AddCircle (2 * π)` is
`AddCircle.haarAddCircle`. -/
recall AddCircle.haarAddCircle

/- The standard quotient measure on `Real.Angle = AddCircle (2 * π)` is `2π` times
`AddCircle.haarAddCircle`; equivalently, the normalized invariant measure on `C_infty` is
`(1 / (2 * π)) dα`. -/
recall AddCircle.volume_eq_smul_haarAddCircle
