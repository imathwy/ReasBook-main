import stacks_project.Chap07.Lemma_7_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Coverage C}
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]

local notation "J" => K.toGrothendieck

/- Domain-style sampling for Lemma 7.17.10:
- primary domain: filtered colimits of `Type`-valued sheaves on a site presented by a coverage,
  specialized to ordinal-indexed diagrams and controlled by ordinal cofinality;
- sampled owner abstractions:
  `Coverage.toGrothendieck`,
  `sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject`,
  `Ordinal.iSup_lt_of_lt_cof`,
  `colimit.post`;
- source/core/bridge triage:
  `source-facing`: the ordinal parameter `β` and the cardinal bound
  `Cardinal.lift (Cardinal.mk R.uncurry) < β.cof` on `K`-covering presieves;
  `core/canonical`: the section-comparison morphism
  `colimit.post F ((sheafSections J (Type (max u v))).obj (op U))` together with
  the filtered comparison owner family already isolated in Lemma 7.17.7;
  `bridge/view`: passing from the chosen coverage `K` to the associated Grothendieck topology, and
  from a `< β.cof`-small family of local stages to one common stage of the ordinal diagram using
  cofinality.

Primitive data are only the ordinal diagram `F` and the source cardinal bound `hcover`. The
comparison morphism is derived API, and the ambient owner family in the chapter is still the
filtered-colimit comparison of Lemma 7.17.7. There is no upstream owner for the exact
small-cover cofinality condition, so that hypothesis should remain explicit rather than being
collapsed into the different quasi-compact-overlap owner from Lemma 7.17.7.
-/
-- Proof sketch: argue directly with the source small-cover hypothesis. Injectivity comes from the
-- filtered-colimit comparison for sheaf sections, while surjectivity is obtained by representing a
-- target section on a `K`-covering presieve of cardinality `< β.cof`, then using ordinal
-- cofinality to dominate all local stages by one stage of `F`. The empty-index case `β = 0`
-- remains a separate degenerate argument.

section

variable (β : Ordinal) (F : Set.Iio β ⥤ Sheaf J (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include hcover

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
injective. This is the injective half of the source-facing bijectivity statement for the canonical
owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := sorry

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
surjective. This is the surjective half of the source-facing bijectivity statement for the
canonical owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Surjective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := sorry

/-- Lemma 7.17.10: let `K` be a chosen coverage on `C`. If the cofinality of `β` dominates the
cardinality of every `K`-covering presieve of each object `U`, then for every `U` the canonical
map from the filtered colimit of the section sets `F i (U)` to the section set of the colimit
sheaf is bijective. -/
theorem sheafFilteredColimitSectionsComparison_bijective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Bijective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
  ⟨sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
      β F hcover U,
    sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
      β F hcover U⟩

end

end CategoryTheory
