import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap25.Definition_25_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]

-- Semantic search note: `lean_leansearch` recalled mathlib's `GrothendieckTopology.OneHypercover`
-- API, but this source item is about the local Chapter 25 site-level hypercovering owner
-- `HypercoveringOf.Terminal J`, i.e. simplicial objects in `SR(C)` augmented to the terminal
-- presheaf.

namespace SemiRepresentableFamily

/-- A semi-representable family lies in `B` if every component object belongs to `B`. -/
def objectsIn (K : SR(C)) (B : Set C) : Prop :=
  ∀ i : K.index, K.obj i ∈ B

/-- Unfolding `objectsIn` says exactly that each component object of the family belongs to `B`. -/
theorem objectsIn_iff (K : SR(C)) (B : Set C) :
    K.objectsIn B ↔ ∀ i : K.index, K.obj i ∈ B := sorry

end SemiRepresentableFamily

namespace HypercoveringOf

open SemiRepresentableFamily

/-- A site-level hypercovering lies degreewise in `B` if every component object in every simplicial
degree belongs to `B`. -/
def degreewiseObjectsIn (K : HypercoveringOf.Terminal J) (B : Set C) : Prop :=
  ∀ n : ℕ, (K.simplicial.obj (op <| SimplexCategory.mk n)).objectsIn B

/-- Unfolding `degreewiseObjectsIn` says exactly that each simplicial degree family lies in `B`. -/
theorem degreewiseObjectsIn_iff (K : HypercoveringOf.Terminal J) (B : Set C) :
    K.degreewiseObjectsIn B ↔
      ∀ n : ℕ, (K.simplicial.obj (op <| SimplexCategory.mk n)).objectsIn B := sorry

end HypercoveringOf

open SemiRepresentableFamily
open HypercoveringOf

/-- Lemma 25.12.3: let `\mathcal{C}` be a site with equalizers and fibre products, and let `B` be
a subset of its objects. If every object of `\mathcal{C}` admits a covering family whose members
lie in `B`, then there exists a hypercovering of the terminal presheaf whose simplicial degree
families all have component objects in `B`. -/
theorem existsSiteHypercoveringDegreewiseObjectsIn
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : SR(C, U),
      (∀ i : 𝒰.index, (𝒰.obj i).left ∈ B) ∧ 𝒰.toSieve ∈ J U) :
    ∃ K : HypercoveringOf.Terminal J, K.degreewiseObjectsIn B := sorry

end CategoryTheory
