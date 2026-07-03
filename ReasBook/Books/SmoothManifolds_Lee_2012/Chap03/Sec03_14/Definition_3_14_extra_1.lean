import Mathlib
import Mathlib.Tactic.Recall

open scoped Manifold

section

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

/- Definition 3.14-extra-1: for a smooth map `F : M → N`, Lee's differential `dFₚ`
is represented in mathlib by the manifold derivative `mfderiv I I' F p`, a continuous
linear map from `TangentSpace I p` to `TangentSpace I' (F p)`. -/
recall mfderiv (F : M → N) (p : M) :
    TangentSpace I p →L[𝕜] TangentSpace I' (F p)

end
