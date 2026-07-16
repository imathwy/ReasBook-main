import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Finite
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Coe
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Div
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.AbsSign
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.CoeInvDiv
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.FiniteSurface
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Order
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Algebra
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Existence
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Monotonicity
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Intervals
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Continuity

/-!
Canonical umbrella module for the chapter-facing `WithBotTop α` infrastructure.

Owner layout:
- `EOrder/Basic`: coercions, recursion, order bridge, zero/one boundary lemmas
- `EOrder/Add`: canonical additive layer
- `EOrder/Finite`: statement-only finite-sum API over the canonical additive surface
- `EOrder/Mul`: canonical multiplicative and power layer
- `EOrder/Operations`: canonical negation/subtraction layer
- `EOrder/Coe`: interaction with genuine/coerced finite elements
- `EOrder/Div`: first higher boundary-facing division theorems
- `EOrder/AbsSign`: chapter-facing `abs/sign` layer over the canonical `WithBotTop` owner
- `EOrder/CoeInvDiv`: coercion-facing bridges for finite elements and `abs/sign/inv/div/pow`
- `EOrder/FiniteSurface`: finite-element statements specialized from the generic chapter-facing surface
- `EOrder/Order`: order-facing theorems whose primary owner is not `abs/sign`
- `EOrder/Algebra`: algebra-facing `mul/inv/div` consequences
- `EOrder/Existence`: existence and `∀ lt`-to-`≤` theorem surface
- `EOrder/Monotonicity`: monotonicity, positivity reflection, and `pow`-order interaction
- `EOrder/Intervals`: interval transport and the neighborhoods of `⊥` and `⊤`
- `EOrder/Continuity`: statement-only continuity surface for the chapter-facing operations
-/
