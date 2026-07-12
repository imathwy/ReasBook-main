import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0010_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

variable {X E F : Type*} [TopologicalSpace X] [Norm E]

-- Domain sampling: this item lies in the compacta-boundedness / function-space interface.
-- Relevant declarations inspected before refinement: the upstream restriction-space owner
-- `analyticFunctionSubring`, the project's compact-subset owner pattern
-- `MeromorphicSeriesNormallyConvergentOnCompacta.on_compact`, and mathlib's function-space owner
-- style via `ContinuousMap`.
-- Source-facing layer: boundedness of a family of functions on compact subsets of `s`.
-- Core/canonical owner abstraction: a carrier coercing to functions `s → E`, where the source only
-- uses compactness on `s` and norms of values in `E`.
-- Primitive data: only evaluation on `s`. Derived specializations: holomorphic families through
-- `analyticFunctionSubring ℂ D`, and continuous families through `C(s, E)`.

/-- Definition V.4-extra-1: a family of `E`-valued functions on `s` is uniformly bounded on
compact subsets of `s` when each compact `K ⊆ s` admits one real bound for the values of all
members of the family on `K`. This notion depends only on evaluation on `s`, so the owner is any
carrier that coerces to functions `s → E`; in particular, `analyticFunctionSubring ℂ D` is a
specialization when `s = D` and `E = ℂ`, and continuous families are another specialization. -/
def UniformlyBoundedOnCompacta (s : Set X) [CoeFun F fun _ ↦ s → E]
    (A : Set F) : Prop :=
  ∀ ⦃K : Set X⦄ (_ : IsCompact K) (hKs : K ⊆ s),
    ∃ M : ℝ, ∀ f (_ : f ∈ A) z (hz : z ∈ K), ‖f ⟨z, hKs hz⟩‖ ≤ M

/-- On each fixed compact subset `K ⊆ s`, a uniformly bounded family admits one common real bound
for all of its members on `K`. -/
theorem UniformlyBoundedOnCompacta.exists_bound
    {s : Set X} [CoeFun F fun _ ↦ s → E] {A : Set F} {K : Set X}
    (hA : UniformlyBoundedOnCompacta s A) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ M : ℝ, ∀ f (_ : f ∈ A) z (hz : z ∈ K), ‖f ⟨z, hKs hz⟩‖ ≤ M :=
  hA hK hKs
