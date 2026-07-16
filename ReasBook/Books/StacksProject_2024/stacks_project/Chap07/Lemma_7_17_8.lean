import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable {I : Type w} [Category I] [Small.{max u v} I]

/- Source/core/bridge triage for 7.17.8:
- primary domain: filtered colimits of set-valued sheaves, global sections, and quasi-compact
  test objects in the sheaf topos;
- sampled owner declarations:
  `Limits.colimit.post`,
  `Sheaf.Γ`,
  `Sheaf.IsQuasiCompactObject`,
  `Sheaf.IsLocallySurjective`;
- best owner abstraction for the comparison map:
  `Limits.colimit.post F (Γ J (Type (max u v)))`;
- primitive data: a filtered diagram `F : I ⥤ Sheaf J (Type (max u v))` and a source-facing
  test subset `S : Set (Sheaf J (Type (max u v)))`;
- derived API: the canonical terminal map `terminal.from`, the terminal sheaf
  `⊤_ (Sheaf J (Type (max u v)))`, and
  quasi-compactness of self-products via `Sheaf.IsQuasiCompactObject`.

Source/core/bridge triage:
- source-facing owner introduced in this file: `IsQuasiCompactTestSet`
- core/canonical owners: `Limits.colimit.post`, `Sheaf.Γ`, `terminal.from`,
  `Sheaf.IsQuasiCompactObject`, and `Sheaf.IsLocallySurjective`
- bridge/view role: the lemmas below specialize the sectionwise filtered-colimit comparison from
  Lemma 7.17.7 to global sections and are stated directly for
  `colimit.post F (Γ J (Type (max u v)))`; the class `IsQuasiCompactTestSet` packages the
  source-facing test-set hypothesis via the canonical terminal map
-/

variable [IsFiltered I]

-- Proof sketch: identify the presheaf colimit underlying the sheaf colimit, observe that
-- transition monomorphisms make the presheaf colimit separated, and apply injectivity of the map
-- from a separated presheaf to its sheafification on global sections.
/-- Lemma 7.17.8 (1): if every transition morphism in the filtered diagram is a monomorphism,
then the canonical map from the filtered colimit of global sections to the global sections of the
colimit sheaf is injective. -/
theorem globalSectionsColimitComparison_injective_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    Function.Injective (colimit.post F (Γ J (Type (max u v)))) := sorry

-- Proof sketch: compare equalizers of two global sections after passing to a tail of the
-- filtered diagram and use quasi-compactness of the terminal sheaf to force equality at a finite
-- stage.
/-- Lemma 7.17.8 (2): if the topos `Sh(C)` is quasi-compact, then the canonical map from the
filtered colimit of global sections to the global sections of the colimit sheaf is injective. -/
theorem globalSectionsColimitComparison_injective_of_quasiCompactTopos
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hJ : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject) :
    Function.Injective (colimit.post F (Γ J (Type (max u v)))) := sorry

-- Proof sketch: injectivity comes from the quasi-compactness of the terminal sheaf, while
-- surjectivity is obtained by lifting a global section through the union of the mono images of
-- the stages and using quasi-compactness to descend the lift to one stage.
/-- Lemma 7.17.8 (3): if `Sh(C)` is quasi-compact and every transition morphism is a
monomorphism, then the canonical map from the filtered colimit of global sections to the global
sections of the colimit sheaf is an isomorphism. -/
theorem globalSectionsColimitComparison_isIso_of_quasiCompactTopos_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hJ : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    IsIso (colimit.post F (Γ J (Type (max u v)))) := sorry

/-- A test set of sheaves detects locally surjective canonical maps to the terminal sheaf and has
quasi-compact self-products. -/
@[mk_iff isQuasiCompactTestSet_iff]
class IsQuasiCompactTestSet (S : Set (Sheaf J (Type (max u v)))) : Prop where
  lift_terminal
      {F : Sheaf J (Type (max u v))}
      (hF : IsLocallySurjective (terminal.from F)) :
      ∃ K : Sheaf J (Type (max u v)), K ∈ S ∧ ∃ κ : K ⟶ F,
        IsLocallySurjective (κ ≫ terminal.from F)
  quasiCompact_selfProduct
      {K : Sheaf J (Type (max u v))} (hK : K ∈ S) :
      (K ⨯ K).IsQuasiCompactObject

-- Proof sketch: use the testing set to lift a global section of the colimit along a surjection
-- `K ⟶ *`, reduce to finitely many stages by quasi-compactness of `K`, and then use
-- quasi-compactness of `K × K` to force compatibility on overlaps at one common stage.
/-- Lemma 7.17.8 (4): if there is a set of sheaves that tests surjections to the terminal sheaf
and whose self-products are quasi-compact, then the canonical map from the filtered colimit of
global sections to the global sections of the colimit sheaf is bijective. -/
theorem globalSectionsColimitComparison_bijective_of_quasiCompactTestSet
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hS : ∃ S : Set (Sheaf J (Type (max u v))), IsQuasiCompactTestSet J S) :
    Function.Bijective (colimit.post F (Γ J (Type (max u v)))) := sorry

end CategoryTheory.GrothendieckTopology
