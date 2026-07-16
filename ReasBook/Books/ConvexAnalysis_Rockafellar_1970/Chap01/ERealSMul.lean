import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul

/-!
Compatibility import for the canonical `WithBotTop` scalar-action owner.

The scalar action and its simp API now live in
`ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul`. This file remains only as a thin
re-export for older imports inside the project.
-/

noncomputable section

/-- Bridge instance: treat the chapter alias `EReal = WithBotTop ℝ` as carrying the canonical
scalar action from `WithBotTop`. This avoids per-file local instance glue when owner declarations
are written over `EReal` in theorem elaboration output. -/
instance instSMulRealEReal : SMul ℝ EReal := WithBotTop.instSMul
