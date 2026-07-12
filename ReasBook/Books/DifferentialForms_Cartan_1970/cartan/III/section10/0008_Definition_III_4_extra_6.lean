import Mathlib
import DifferentialForms_Cartan_1970.III.section10.«0007_Definition_III_4_extra_5»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/- Definition III.4-extra-6 (1): mathlib expresses "`o` is a pole of `f`" by the canonical
condition `meromorphicOrderAt f o < 0`, with asymptotic consequence
`tendsto_cobounded_of_meromorphicOrderAt_neg`. -/
#check (fun (f : 𝕜 → E) (o : 𝕜) ↦ meromorphicOrderAt f o < 0)

/-- Definition III.4-extra-6 (2): the point `o` is an essential singularity of `f` when `f` is
analytic on a punctured neighborhood of `o` but is not meromorphic at `o`. -/
def HasEssentialSingularityAt (f : 𝕜 → E) (o : 𝕜) : Prop :=
  HasIsolatedSingularityAt f o ∧ ¬ MeromorphicAt f o

namespace HasEssentialSingularityAt

/-- An essential singularity is, in particular, an isolated singularity. -/
theorem isolated {f : 𝕜 → E} {o : 𝕜} (hf : HasEssentialSingularityAt f o) :
    HasIsolatedSingularityAt f o :=
  hf.1

/-- An essential singularity is analytic at every nearby point away from the center. -/
theorem eventually_analyticAt {f : 𝕜 → E} {o : 𝕜} (hf : HasEssentialSingularityAt f o) :
    ∀ᶠ z in 𝓝[≠] o, AnalyticAt 𝕜 f z :=
  hf.isolated.eventually_analyticAt

/-- An essential singularity is, in particular, not a meromorphic singularity. -/
theorem not_meromorphicAt {f : 𝕜 → E} {o : 𝕜} (hf : HasEssentialSingularityAt f o) :
    ¬ MeromorphicAt f o :=
  hf.2

end HasEssentialSingularityAt

end
