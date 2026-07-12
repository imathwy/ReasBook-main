import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_9_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_9_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_9_3

/- Text 22.3.9 is split across the following source-facing components:
- `Text_22_3_9_1`: the owner abstraction `GeneralPrimalSystem` with intrinsic relation owner
  `GeneralPrimalSystem.relation`;
- `Text_22_3_9_2`: the specialization constructor `GeneralPrimalSystem.ofLe` encoding `Ax ≤ a`;
- `Text_22_3_9_3`: the specialization constructor `GeneralPrimalSystem.ofNonnegativeEq`
  encoding `x ≥ 0`, `Ax = a`.
-/
