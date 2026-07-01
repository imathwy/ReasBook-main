import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.4.52: the textbook data of a norm on a `K`-vector space is an ambient function
`‖·‖ : V → ℝ` together with definiteness, absolute homogeneity, and the triangle inequality.
Mathlib packages exactly this minimal theorem-level core as `NormedSpace.Core K V`, taking the
norm itself as primitive `[Norm V]`; the usual `NormedAddCommGroup` and `NormedSpace` structures
are then derived from that owner. This uses the standard real-valued norm in place of the source's
`ℝ≥0`-valued presentation. -/
recall NormedSpace.Core (K : Type u) (V : Type v) [NormedField K] [AddCommGroup V] [Module K V]
  [Norm V] : Prop

section

variable {K : Type u} {V : Type v} [NormedField K] [AddCommGroup V] [Module K V] [Norm V]

/- The canonical bridge from the core norm axioms to the ambient normed additive-group structure
is `NormedAddCommGroup.ofCore`. -/
#check (NormedAddCommGroup.ofCore : NormedSpace.Core K V → NormedAddCommGroup V)

end
