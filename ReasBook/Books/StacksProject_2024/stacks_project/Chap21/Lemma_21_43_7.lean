import StacksProject_2024.stacks_project.Chap21.Lemma_21_43_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Subobject

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

/-
Domain-style sampling for Lemma 21.43.7:
- primary domain: size bounds for representatives in the derived category of presheaves of
  modules, together with quasi-isomorphic bounded subcomplex inclusions;
- sampled owner declarations:
  `Subobject`,
  `DerivedCategory.Q`,
  `CochainComplex.sectionsCardinal`,
  `exists_bounded_subcomplex_containing_section_subsets`;
- best owner abstraction: for a representing complex `F : ModComplex`, a bounded representative
  subcomplex should be a canonical `Subobject F`, with inclusion map
  `G.arrow : underlying.obj G ⟶ F`;
- primitive data: an object `K : DModO`, a representing complex `F`, and a canonical subobject
  `G : Subobject F`;
- derived API: the source-facing size notation `sizeD[𝒪](K)`, its representation bound, and the
  theorem
  that some `G : Subobject F` is quasi-isomorphic to `F` with the required cardinal bound.

Source/core/bridge triage:
- `source-facing`: the size invariant `derivedObjectCardinal 𝒪 K` and the bounded-representative
  existence theorem;
- `core/canonical`: `Subobject F` as the owner of subcomplex inclusions into `F`;
- `bridge/view`: the map `DerivedCategory.Q.map G.arrow` and the section-cardinality bounds. -/

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

local notation "ModComplex" => CochainComplex (PresheafOfModules 𝒪) ℤ
local notation "DModO" => DerivedCategory (PresheafOfModules 𝒪)

open CochainComplex
open scoped ModulesOnCategoryCardinal

/-- The size `sizeD[𝒪](K)` of an object `K ∈ D(𝒪)` is the least cardinal bound among all
cochain complexes of `𝒪`-modules representing `K`, measured by the total cardinality of their
objectwise sections. -/
def derivedObjectCardinal
    (K : DModO) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (F : ModComplex) (_ : DerivedCategory.Q.obj F ≅ K),
      sizeₛ(F) ≤ κ}

scoped[ModulesOnCategoryCardinal] notation:max "sizeD[" O "](" K ")" =>
  CategoryTheory.ModulesOnCategory.derivedObjectCardinal O K

-- Proof sketch: the complex `F` itself contributes an element of the set of admissible cardinal
-- bounds defining `derivedObjectCardinal 𝒪 K` through the chosen isomorphism `Q.obj F ≅ K`, so the
-- infimum is bounded above by the cardinal of sections of `F`.
/-- Any representative complex bounds the canonical cardinal `sizeD[𝒪](K)` from above by
`sizeₛ(F)`. -/
theorem derivedObjectCardinal_le_of_representation
    {K : DModO} (F : ModComplex) (e : DerivedCategory.Q.obj F ≅ K) :
    sizeD[𝒪](K) ≤ sizeₛ(F) := sorry

/-- Companion bridge for Lemma `21.43.7`: if the inclusion of `G : Subobject F` becomes an
isomorphism after applying `DerivedCategory.Q`, then `underlying.obj G` is itself a representative
of `K`. -/
def subobjectRepresentationIso
    {K : DModO} {F : ModComplex} (e : DerivedCategory.Q.obj F ≅ K)
    {G : Subobject F} (hG : IsIso (DerivedCategory.Q.map G.arrow)) :
    DerivedCategory.Q.obj (underlying.obj G) ≅ K :=
  let _ : IsIso (DerivedCategory.Q.map G.arrow) := hG
  asIso (DerivedCategory.Q.map G.arrow) ≪≫ e

-- Proof sketch: start from Lemma `21.43.6` to choose a small subcomplex surjecting onto every
-- cohomology sheaf of `F`. Then enlarge it inductively, still using Lemma `21.43.6`, so that at
-- each stage the kernel of the map on cohomology to `F` stabilizes. The union of this countable
-- chain is a subcomplex whose inclusion is a quasi-isomorphism, and cardinal arithmetic keeps its
-- total size bounded by `max(κ, sizeD[𝒪](K))`.
/-- Lemma 21.43.7: there exists a cardinal `κ` such that, whenever a cochain complex
`F : ModComplex` represents `K ∈ D(𝒪)`, there is a canonical subobject `G : Subobject F` whose
inclusion `G.arrow : underlying.obj G ⟶ F` becomes an isomorphism in `D(𝒪)` and whose total
section cardinality is bounded by `max(κ, sizeD[𝒪](K))`. Equivalently, `underlying.obj G` is a
bounded-size subcomplex still representing `K`. -/
@[stacks 0GYY]
theorem exists_cardinal_for_bounded_representative_subcomplexes :
    ∃ κ : Cardinal,
      ∀ (K : DModO) (F : ModComplex) (e : DerivedCategory.Q.obj F ≅ K),
        ∃ G : Subobject F,
          IsIso (DerivedCategory.Q.map G.arrow) ∧
            sizeₛ(underlying.obj G) ≤ max κ sizeD[𝒪](K) := sorry

/-- Companion bridge for Lemma `21.43.7`: if a subobject `G : Subobject F` still represents `K`
after applying `DerivedCategory.Q`, then its own total section cardinality already bounds
`sizeD[𝒪](K)`. -/
theorem derivedObjectCardinal_le_of_subobject_representation
    {K : DModO} {F : ModComplex} (e : DerivedCategory.Q.obj F ≅ K)
    {G : Subobject F} (hG : IsIso (DerivedCategory.Q.map G.arrow)) :
    sizeD[𝒪](K) ≤ sizeₛ(underlying.obj G) :=
  derivedObjectCardinal_le_of_representation 𝒪 (underlying.obj G)
    (subobjectRepresentationIso 𝒪 e hG)

end

end CategoryTheory.ModulesOnCategory
