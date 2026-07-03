import Mathlib
import DifferentialForms_Cartan_1970.V.section21.«0001_Definition_V_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this scope note lies in the function-space interface for holomorphic
-- restrictions. Relevant owner declarations checked before refinement: the project bridge/view
-- `analyticFunctionSubring`, the core holomorphic owner `AnalyticOnNhd`, and the canonical
-- continuous-function space `C(D, ℂ)`.

variable {D : Set ℂ}

/- Remark V.4-extra-2: this source item is a scope note about the ambient function spaces rather
than a new theorem. In this section, the holomorphic-function space is the restriction-space owner
`analyticFunctionSubring ℂ D`, while the continuous function space `𝒞(D)` is represented by
`C(D, ℂ)`. The note says that the preceding Proposition 2.1 still makes sense on `𝒞(D)`, whereas
the converse announced next is intended only for subsets of `analyticFunctionSubring ℂ D`. -/
recall analyticFunctionSubring
#check C(D, ℂ)
