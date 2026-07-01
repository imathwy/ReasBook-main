import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_1_1

noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {L : Type z}
variable [HAdd L L L] [HSub L L L]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [CompleteLattice L]

-- Proposition 37.1.2 in textbook pointwise notation on the canonical Chapter 37 owners.
recall lowerConjugate_le_upperConjugate
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) ≤ K ^*(uStar, x)

end

end Bifunction
