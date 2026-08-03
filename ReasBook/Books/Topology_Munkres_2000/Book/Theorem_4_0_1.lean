module

import Mathlib.Topology.Metrizable.Urysohn

public section

/- Theorem 4.0.1 (Urysohn metrization theorem): A second-countable regular space,
expressed using mathlib's `T3Space` convention, embeds in a metric space and is
therefore metrizable. Mathlib gives the concrete target `ℕ →ᵇ ℝ`. -/
#check TopologicalSpace.exists_embedding_l_infty
#check TopologicalSpace.metrizableSpace_of_t3_secondCountable
