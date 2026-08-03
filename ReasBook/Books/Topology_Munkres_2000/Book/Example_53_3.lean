module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

namespace Circle

/- Example 53.3. The squaring map on the complex unit circle is a covering map in
Munkres's surjective sense. -/
#check And.intro (isQuotientCoveringMap_npow 2).isCoveringMap
  (isQuotientCoveringMap_npow 2).surjective

/- More precisely, the squaring map is the quotient covering map by its kernel. -/
#check isQuotientCoveringMap_npow 2

end Circle
