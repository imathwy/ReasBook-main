import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain note: this item lies in graded commutative algebra and projective-spectrum topology.
It is a `core/canonical` recall: the owner abstraction is `ProjectiveSpectrum 𝒜`, while the
topology is derived canonically from that owner via `ProjectiveSpectrum.zariskiTopology`. No local
wrapper or parallel `Proj` point-space API is needed here. -/

/- Definition 10.57.1 (Stacks, Tag `00JN`) is recalled canonically by
`ProjectiveSpectrum 𝒜`: for an `ℕ`-graded commutative ring, its points are exactly the homogeneous
prime ideals that do not contain the irrelevant ideal. This is the source's `Proj(S)`. -/
recall ProjectiveSpectrum

/- Companion recall: the topological-space structure on `ProjectiveSpectrum 𝒜` is the canonical
Zariski topology used for `Proj(S)`. -/
recall ProjectiveSpectrum.zariskiTopology

end
