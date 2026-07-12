import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- The canonical algebraic owners for the notation used here were verified directly against
-- `Mathlib.Algebra.Group.Defs`, and the chapter's smooth additive owner was checked against
-- `Mathlib.Geometry.Manifold.Algebra.LieGroup`: multiplicative notation is governed by `Group`,
-- additive notation is governed by `AddGroup`, and the additive Lie-group examples in this
-- chapter use `LieAddGroup` rather than the more specialized `AddCommGroup`.

open scoped Manifold ContDiff

section MultiplicativeNotation

universe u

/- Notation 7.46-extra-2: in a Lie group, the multiplicative notation comes from the ambient
`Group` structure. -/
recall Group (G : Type u) : Type u

variable {G : Type u} [Group G] (g h : G)

#check (g * h : G)
#check ((1 : G) : G)

end MultiplicativeNotation

section AdditiveNotation

universe u𝕜 uE uA

/- Additive notation in the chapter's additive Lie-group examples comes from the ambient
`AddGroup` structure carried by the canonical smooth owner `LieAddGroup`. -/
recall LieAddGroup

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {A : Type uA} [AddGroup A] [TopologicalSpace A] [ChartedSpace E A]
variable [LieAddGroup (𝓘(𝕜, E)) ∞ A] (x y : A)

#check (inferInstance : LieAddGroup (𝓘(𝕜, E)) ∞ A)
#check (x + y : A)
#check ((0 : A) : A)

end AdditiveNotation
