import Mathlib
import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` recalled generic simplicial face-map and one-hypercover
-- API; the verified local owner/API for this item is the Chapter 25 `Hypercovering` structure from
-- `Lemma_25_3_7`, together with the simplicial face maps `K.toSimplicialObject.δ i`.

namespace Hypercovering

/-- Lemma 25.8.3 (1): if `K` is a hypercovering of `X`, then every simplicial degree family `K_n`
is a covering of `X`. In Lean this is formalized by the covering sieve condition on the fixed-target
family `K.toSimplicialObject.obj (op <| SimplexCategory.mk n)`. -/
@[stacks 0DEQ]
theorem degree_isCovering
    {X : C}
    (K : @Hypercovering C _ J X) (n : ℕ) :
    (K.toSimplicialObject.obj (op <| SimplexCategory.mk n)).toSieve ∈ J X := sorry

/-- Lemma 25.8.3 (2): if `K` is a hypercovering of `X`, then every face map is a covering
morphism. In the source notation this says `d^n_i : K_n ⟶ K_{n - 1}` is covering for all `n ≥ 1`
and `0 ≤ i ≤ n`; in Lean this is `Hom.IsCovering J (K.toSimplicialObject.δ i)` for
`i : Fin (n + 2)`, i.e. the face map `K_{n + 1} ⟶ K_n`. -/
@[stacks 0DEQ]
theorem faceMap_isCovering
    {X : C}
    (K : @Hypercovering C _ J X) (n : ℕ) (i : Fin (n + 2)) :
    Hom.IsCovering J (K.toSimplicialObject.δ i) := sorry

end Hypercovering

end CategoryTheory
