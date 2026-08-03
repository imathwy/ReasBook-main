module

import Mathlib.Logic.Basic

/- Remark 1.2: `Or P Q` is inclusive disjunction, allowing both propositions to
hold, while `Xor P Q` is exclusive disjunction, requiring exactly one to hold. -/
#check Or
#check Xor
#check xor_iff_or_and_not_and
