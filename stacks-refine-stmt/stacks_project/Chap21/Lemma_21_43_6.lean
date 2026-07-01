import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Lemma 21.43.6:
- primary domain: size bounds for cochain complexes of presheaves of modules and mono-presented
  subcomplex inclusions;
- sampled owner declarations:
  `CochainComplex`,
  `PresheafOfModules`,
  `Subobject`;
- best owner abstraction: the canonical subobject `G : Subobject F` of the ambient complex
  `F : CochainComplex (PresheafOfModules 𝒪) ℤ`, with the inclusion map recovered as `G.arrow`;
- primitive data: the ambient complex `F`, the chosen seed family `Ω`, the candidate subcomplex
  `G : Subobject F`, and the chosen seed family `Ω`;
- derived API: the section-cardinality measures and the property that `ι` contains the chosen
  seeds and satisfies the uniform cardinal bound.

Source/core/bridge triage:
- `source-facing`: a bounded subcomplex containing the designated seed sections;
- `core/canonical`: `Subobject F`;
- `bridge/view`: the cardinal-valued size functions
  `CochainComplex.sectionsCardinal` and `CochainComplex.seedSectionsCardinal`, together with the
  inclusion `G.arrow : (G : ModComplex) ⟶ F`. -/

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

local notation "ModComplex" => CochainComplex (PresheafOfModules 𝒪) ℤ

namespace CochainComplex

/-- The total cardinality of the sections occurring in a cochain complex of presheaves of
`\mathcal O`-modules. -/
def sectionsCardinal (F : ModComplex) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).obj (op U))

/-- The cardinality of a chosen family of seed sections in a cochain complex of presheaves of
`\mathcal O`-modules. -/
def seedSectionsCardinal
    (F : ModComplex)
    (Ω : ∀ i : ℤ, ∀ U : C, Set ((F.X i).obj (op U))) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, {x : (F.X i).obj (op U) // x ∈ Ω i U})

end CochainComplex

open CategoryTheory.ModulesOnCategory.CochainComplex

-- Proof sketch: choose a cardinal bound depending only on the category `C` and the presheaf of
-- rings `𝒪`. For each complex `F` and family of seed sections `Ω`, generate the smallest
-- objectwise `\mathcal O(U)`-submodules stable under restrictions and differentials that contain
-- all seeds, and assemble them into a subcomplex `H ⟶ F`. The standard closure construction gives
-- the required cardinal estimate.
/-- Lemma 21.43.6: for a category `C` with a presheaf of rings `\mathcal O`, there exists a
cardinal `κ` such that every cochain complex `\mathcal F^\bullet` of presheaves of
`\mathcal O`-modules, together with chosen subsets `Ω^i_U ⊆ \mathcal F^i(U)`, admits a subcomplex
`\mathcal H^\bullet ⊆ \mathcal F^\bullet` whose image contains each `Ω^i_U` and whose total
objectwise cardinality is bounded by `max(κ, |\bigcup Ω^i_U|)`. Here the subcomplex is encoded as
a canonical subobject `G : Subobject F` with inclusion `G.arrow : (G : ModComplex) ⟶ F`. -/
theorem exists_bounded_subcomplex_containing_section_subsets :
    ∃ κ : Cardinal,
      ∀ (F : ModComplex) (Ω : ∀ i : ℤ, ∀ U : C, Set ((F.X i).obj (op U))),
        ∃ G : Subobject F,
          (∀ i : ℤ, ∀ U : C, Ω i U ⊆ Set.range ((G.arrow.f i).app (op U))) ∧
            sectionsCardinal 𝒪 (G : ModComplex) ≤ max κ (seedSectionsCardinal 𝒪 F Ω) := sorry

end

end CategoryTheory.ModulesOnCategory
