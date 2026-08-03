module

import Mathlib.Data.Setoid.Partition

/- Notation 3.3: For a setoid `r` on `A`, the book's collection `𝓔` of all
equivalence classes is represented by `r.classes`. -/
#check Setoid.classes

/- The collection of equivalence classes of a setoid is a partition of its
carrier. -/
#check Setoid.isPartition_classes
