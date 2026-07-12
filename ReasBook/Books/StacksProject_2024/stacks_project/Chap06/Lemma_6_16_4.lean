import Mathlib
import StacksProject_2024.Chap06.Definition_6_15_1
import StacksProject_2024.Chap06.Lemma_6_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe w u

/- Domain-style sampling for Lemma 6.16.4:
- primary domain: sheaves of algebraic structures on a topological space, compared with their
  underlying sheaves of sets through stalk functors;
- inspected owner declarations:
  `IsAlgebraicStructure`,
  `sheafCompose`,
  `filteredStalk`,
  `stalkCompIso`,
  `existsUnique_pushforward_hom_of_underlying_sectionwise_structure_preserving`;
- best owner abstraction:
  the source-facing owner here is the underlying morphism of sheaves of sets
  `(sheafCompose (Opens.grothendieckTopology X) F).obj ℱ ⟶
    (sheafCompose (Opens.grothendieckTopology X) F).obj 𝒢`,
  with the `C`-valued sheaf morphism `Φ : ℱ ⟶ 𝒢` recovered uniquely from it;
- primitive data:
  the underlying morphism of set-valued sheaves `φ` and the stalkwise existence of lifts in `C`;
- derived API:
  the comparison isomorphisms `stalkCompIso` and the equality
  `(sheafCompose (Opens.grothendieckTopology X) F).map Φ = φ`.

Source/core/bridge triage:
- `source-facing`: the textbook stalkwise criterion for lifting an underlying morphism of sheaves
  of sets to a morphism of sheaves of algebraic structures;
- `core/canonical`: the underlying sheaf-of-sets owner `sheafCompose (Opens.grothendieckTopology X) F`,
  with the sectionwise lifting criterion later abstracted by
  `existsUnique_pushforward_hom_of_underlying_sectionwise_structure_preserving`;
- `bridge/view`: the stalkwise compatibility equation expressed via `stalkCompIso`.

The theorem is therefore not a duplicate owner declaration. The right refinement is to keep this
source-facing theorem while aligning its surface with the chapter’s canonical owner API.
-/

section

variable {C : Type u} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]
variable {X : TopCat.{w}}
variable {ℱ 𝒢 : X.Sheaf C}

local notation "J" => Opens.grothendieckTopology X
local notation "underlyingSheaf" =>
  @sheafCompose _ _ _ _ _ _ J F (hasSheafCompose_of_preservesLimitsOfSize J)

-- Proof sketch: for each open `U`, compare the underlying section map `φ.app (op U)` with the
-- product of the stalk maps over points of `U`. By the stalkwise hypothesis and the canonical
-- stalk/postcomposition comparison, the right vertical map in the Stacks proof is a morphism in
-- `C`; Lemma 6.11.1 gives injectivity of the bottom horizontal map on underlying sets. Apply
-- Lemma 6.15.4 and Example 6.15.5 to obtain a unique sectionwise morphism `ℱ(U) ⟶ 𝒢(U)` lifting
-- `φ.app (op U)`, then use faithfulness of `F` to deduce naturality and assemble these maps into
-- a morphism of `C`-valued sheaves.
/-- Lemma 6.16.4: if, for every point `x`, the induced map on stalks of the underlying sheaves of
sets of `C`-valued sheaves is the underlying map of a morphism in `C`, then the given underlying
morphism of sheaves of sets comes from a unique morphism of sheaves of algebraic structures. -/
theorem existsUnique_sheaf_hom_of_underlying_stalkwise_structure_preserving
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ x : X, ∃ ψx : filteredStalk x ℱ.presheaf ⟶ filteredStalk x 𝒢.presheaf,
      (stalkCompIso x F ℱ.presheaf).hom ≫
          (stalkFunctor (Type w) x).map (Sheaf.homEquiv φ) ≫
          (stalkCompIso x F 𝒢.presheaf).inv =
        F.map ψx) :
    ∃! Φ : ℱ ⟶ 𝒢,
      (underlyingSheaf).map Φ = φ := by
  sorry

end
