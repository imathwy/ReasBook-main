import StacksProject_2024.stacks_project.Chap25.Lemma_25_8_2

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

-- Semantic search note: `lean_leansearch` recalled generic one-hypercover and simplicial-set
-- relative-homotopy API. The source-facing statement here uses the local Chapter 25
-- `Hypercovering` owner and the Chapter 14/25 simplicial copower and internal-hom restriction
-- maps, which are the verified local API for `K × Δ[k]` and restriction to `K × ∂Δ[k]`.

namespace Hypercovering

/-- Remark 25.9.3: given hypercoverings `K` and `L` of `X` and a morphism
`a : K × ∂Δ[k] ⟶ L`, there exists a refinement `c : K' ⟶ K` and a morphism
`g : K' × Δ[k] ⟶ L` whose restriction to `K' × ∂Δ[k]` is
`a ∘ (c × id)`. In the project API the simplicial-set copower is written with the simplicial set
on the left, so the restriction is expressed by precomposing `g` with
`simplicialCopowerIndexHom` along `(∂Δ[k]).ι`, while `a ∘ (c × id)` is expressed by
`simplicialCopowerHom (∂Δ[k]) c ≫ a`. -/
@[stacks 01GT]
theorem existsRefinementBoundarySimplexExtension
    {X : C}
    (K L : @Hypercovering C _ J X)
    (k : ℕ)
    (a : (∂Δ[k] : SSet.{w}) × K.toSimplicialObject ⟶ L.toSimplicialObject) :
    ∃ (K' : @Hypercovering C _ J X)
      (c : K'.toSimplicialObject ⟶ K.toSimplicialObject)
      (g : (Δ[k] : SSet.{w}) × K'.toSimplicialObject ⟶ L.toSimplicialObject),
      simplicialCopowerIndexHom K'.toSimplicialObject (∂Δ[k]).ι ≫ g =
        simplicialCopowerHom (∂Δ[k] : SSet.{w}) c ≫ a := sorry

end Hypercovering

end CategoryTheory
