import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

variable (n m : ℕ)
variable (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
variable (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))

/- Definition 1.2-extra-1 (core/canonical): smoothness for maps between open subsets of Euclidean
spaces is formalized by `ContDiffOn ℝ ∞` on the open domain. Since open subsets `U ⊆ ℝⁿ` and
`V ⊆ ℝᵐ` inherit the canonical manifold structures, the public owner for diffeomorphisms between
them is the diffeomorphism type on the open-subset types themselves, `U ≃ₘ⟮𝓡 n, 𝓡 m⟯ V`. Its
underlying topological data is recovered by the standard forgetful bridge
`Diffeomorph.toHomeomorph`. The auxiliary `PartialDiffeomorph` API belongs to
local-diffeomorphism internals, not to the public surface for diffeomorphisms between open
subsets. -/
#check (ContDiffOn ℝ ∞)
#check (U ≃ₘ⟮𝓡 n, 𝓡 m⟯ V)
recall Diffeomorph.toHomeomorph
