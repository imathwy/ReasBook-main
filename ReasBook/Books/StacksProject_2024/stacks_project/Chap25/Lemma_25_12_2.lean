import StacksProject_2024.stacks_project.Chap25.«25_12_2_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` recalled mathlib's `GrothendieckTopology.OneHypercover`
-- API, but this item is about full hypercoverings with degreewise families in a chosen subset of
-- objects, so the verified local Chapter 25 `Hypercovering` / `SR(C, X)` owner is the right
-- source-faithful surface here.

open SemiRepresentableFamily.Over

/-- Lemma 25.12.2: let `\mathcal{C}` be a site with fibre products, and let `B` be a subset of its
objects such that every object admits a covering family whose sources lie in `B`, and such that
adjoining any single arrow `U' \to U` with `U' ∈ B` to a `B`-covering family over `U` again gives
a covering family. Then every object `X` admits a hypercovering all of whose simplicial degree
families have sources in `B`. -/
@[stacks 0DAV]
theorem existsHypercoveringDegreewiseObjectsIn
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : SR(C, U), 𝒰.IsBasisCovering J.toPrecoverage B)
    (hadd : ∀ {U : C} (𝒰 : SR(C, U)), 𝒰.IsBasisCovering J.toPrecoverage B →
      ∀ {U' : C} (f : U' ⟶ U), U' ∈ B → (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C) :
    ∃ K : Hypercovering J X, K.degreewiseObjectsIn B := sorry

end CategoryTheory
