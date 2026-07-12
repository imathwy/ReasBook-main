import Mathlib
import StacksProject_2024.Chap25.Lemma_25_8_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` only recalled the generic upstream hypercover owners.
-- The source-facing statement in this section is the local Chapter 25 restriction morphism on
-- `simplicialHom`, using the single-simplex extension theorem from Lemma 25.8.1 and the finite
-- filtration owner from `SSet.exists_singleSimplexExtensionFiltration`.

/-- Lemma 25.8.2: let `K` be a hypercovering of `X` and let `U ⊆ V` be an inclusion of simplicial
sets whose terms are all finite nonempty and which has only finitely many nondegenerate simplices.
Then the induced restriction morphism `Hom(V, K)_0 ⟶ Hom(U, K)_0` in `SR(C, X)` is covering.

In Lean, the inclusion is formalized by a subcomplex `U : V.Subcomplex`, the finiteness hypotheses
are packaged by the canonical owner `V.Finite` together with explicit degreewise nonemptiness
assumptions, and the restriction morphism is the degree-`0` component of
`simplicialHomPrecomp U.ι K.toSimplicialObject`. -/
@[stacks 01GN]
theorem hypercoveringHomZeroPrecomp_isCovering_of_finiteInclusion
    {X : C} {V : SSet.{w}} [V.Finite]
    (U : V.Subcomplex)
    [Nonempty ((U : SSet) _⦋0⦌)]
    [Nonempty (V _⦋0⦌)]
    (hU_nonempty : ∀ n : ℕ, Nonempty ((U : SSet) _⦋n⦌))
    (hV_nonempty : ∀ n : ℕ, Nonempty (V _⦋n⦌))
    (K : @Hypercovering C _ J X) :
    Hom.IsCovering J
      ((simplicialHomPrecomp U.ι K.toSimplicialObject).app (op ⦋0⦌)) := sorry

end CategoryTheory
