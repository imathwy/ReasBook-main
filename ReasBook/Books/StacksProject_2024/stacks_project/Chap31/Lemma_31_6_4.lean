import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (𝒢 : S.Modules) (x : X)

local notation:max f:max "^*" => Scheme.Modules.pullback f

-- Semantic recall: `lean_leansearch` surfaced the scheme-theoretic fiber owner
-- `Scheme.Hom.fiber`, the canonical fiber point `Scheme.Hom.asFiber`, and the module-pullback
-- notation `f^*`; Chapter 31 local precedent fixes the weak-assassin owner as
-- `Scheme.Modules.weakAss`, while Chapter 29 packages the pointwise flatness hypothesis through
-- the canonical owner `Scheme.Hom.flatAt`. The fiberwise generic-point hypothesis is exposed
-- through membership of the canonical fiber point `f.asFiber x` in the generic points of the
-- irreducible components of the scheme-theoretic fiber `f.fiber (f x)`.

/-- Lemma 31.6.4: let `f : X ⟶ S` be a morphism of schemes, let `\mathcal G` be an
`\mathcal O_S`-module, and let `x : X` with `s = f(x)`. If `f` is flat at `x`, the point `x` is a
generic point of the fiber `X_s`, and `s ∈ WeakAss_S(\mathcal G)`, then
`x ∈ WeakAss(f^*\mathcal G)`. The source states this for quasi-coherent `\mathcal G`, but the
Chapter 31 weak-assassin owner and pullback surface used here make the same statement for
arbitrary module sheaves. -/
theorem mem_weakAss_pullback_of_flatAt_of_isGenericPoint_fiber
    (hflat : flatAt f x)
    (hgeneric : f.asFiber x ∈ genericPointsOfIrreducibleComponents (f.fiber (f x)))
    (hs : f x ∈ 𝒢.weakAss) :
    x ∈ (((f^*).obj 𝒢).weakAss) := sorry

end AlgebraicGeometry.Scheme.Modules
