module

import Mathlib.Topology.Compactness.Compact

/- Remark 37.1. The product `X × Y` of two compact spaces is compact. The recalled
open-cover proof first extracts finite covers of the slices `{x} × Y` by basis
rectangles and then combines them into a finite cover of the whole product. -/
#check instCompactSpaceProd
