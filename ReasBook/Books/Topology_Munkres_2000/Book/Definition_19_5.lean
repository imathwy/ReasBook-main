module

import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology

/- Definition 19.5: For an indexed family of topological spaces `X`, the
collection of all full boxes `∏ α, U α`, where every `U α` is open in `X α`,
is `Pi.boxBasis X`. -/
#check Pi.boxBasis

/- A set belongs to `Pi.boxBasis X` exactly when it is a full box with every
coordinate set open. -/
#check Pi.mem_boxBasis
