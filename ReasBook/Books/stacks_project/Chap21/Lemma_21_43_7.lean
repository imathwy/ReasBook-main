import stacks_project.Chap21.Lemma_21_43_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

local notation "ModComplex" => CochainComplex (PresheafOfModules 𝒪) ℤ
local notation "DModO" => DerivedCategory (PresheafOfModules 𝒪)

open _root_.CategoryTheory.ModulesOnCategory.CochainComplex

/-- The size `|K|` of an object `K ∈ D(\mathcal O)` is the least cardinal bound among all
cochain complexes of `\mathcal O`-modules representing `K`, measured by the total cardinality of
their objectwise sections. -/
def derivedObjectCardinal
    (K : DModO) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (F : ModComplex) (_e : DerivedCategory.Q.obj F ≅ K),
      sectionsCardinal 𝒪 F ≤ κ}

-- Proof sketch: the representing complex `F` itself contributes an element of the set of
-- admissible cardinal bounds defining `derivedObjectCardinal 𝒪 K`, so the infimum is bounded
-- above by the cardinal of sections of `F`.
/-- Any chosen complex representing `K` bounds the canonical cardinal `|K|` from above. -/
theorem derivedObjectCardinal_le_of_representation
    (K : DModO)
    (F : ModComplex)
    (e : DerivedCategory.Q.obj F ≅ K) :
    derivedObjectCardinal 𝒪 K ≤ sectionsCardinal 𝒪 F := sorry

/-- A monomorphism `ι : \mathcal H^\bullet \to \mathcal F^\bullet` exhibits `\mathcal H^\bullet`
as a subcomplex of `\mathcal F^\bullet` that becomes isomorphic to `\mathcal F^\bullet` in
`D(\mathcal O)` and whose total section cardinality is bounded by `max(\kappa, |K|)`. When
`\mathcal F^\bullet` represents `K`, this says that `\mathcal H^\bullet` also represents `K`. -/
class IsBoundedRepresentativeSubcomplex
    (κ : Cardinal)
    (K : DModO)
    (F H : ModComplex)
    (ι : H ⟶ F) : Prop where
  mono : Mono ι
  quasiIso : IsIso (DerivedCategory.Q.map ι)
  cardinal_bound :
    sectionsCardinal 𝒪 H ≤ max κ (derivedObjectCardinal 𝒪 K)

-- Proof sketch: start from Lemma `21.43.6` to choose a small subcomplex surjecting onto every
-- cohomology sheaf of `F`. Then enlarge it inductively, still using Lemma `21.43.6`, so that at
-- each stage the kernel of the map on cohomology to `F` stabilizes. The union of this countable
-- chain is a subcomplex whose inclusion is a quasi-isomorphism, and cardinal arithmetic keeps its
-- total size bounded by `max(\kappa, |K|)`.
/-- Lemma 21.43.7: there exists a cardinal `\kappa` such that, whenever a cochain complex
`\mathcal F^\bullet` of `\mathcal O`-modules represents an object `K` of `D(\mathcal O)`, there
is a subcomplex `\mathcal H^\bullet \subset \mathcal F^\bullet` whose inclusion becomes an
isomorphism in `D(\mathcal O)` and whose total section cardinality is bounded by
`max(\kappa, |K|)`. Equivalently, `\mathcal H^\bullet` is a bounded-size subcomplex still
representing `K`. -/
theorem exists_cardinal_for_bounded_representative_subcomplexes :
    ∃ κ : Cardinal,
      ∀ (K : DModO)
        (F : ModComplex) (_e : DerivedCategory.Q.obj F ≅ K),
        ∃ (H : ModComplex) (ι : H ⟶ F),
          IsBoundedRepresentativeSubcomplex 𝒪 κ K F H ι := sorry

end

end CategoryTheory.ModulesOnCategory
