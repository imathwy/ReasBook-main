import Mathlib
import StacksProject_2024.stacks_project.Chap06.ClosedSubsetInclusion
import StacksProject_2024.stacks_project.Chap06.Definition_6_15_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_13_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_15_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Presheaf.stalkPushforward

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u v w

section

variable {X : TopCat.{u}}
variable {Z : Set X}

local notation "sZ" => X.subsetInclusion Z
local notation "iZ" => X.closedSubsetInclusion Z

/- Domain-style sampling for Lemma 6.32.1:
- primary domain: sheaf pushforward/pullback and stalk comparison for the inclusion of a closed
  subset in `TopCat`;
- sampled owner declarations:
  `TopCat.subsetInclusion`,
  `TopCat.closedSubsetInclusion`,
  `IsAlgebraicStructure`,
  `stalkPushforward_iso_of_isInducing`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction: the ambient owner is the subset inclusion morphism
  `TopCat.subsetInclusion X Z`; the closed-subset inclusion
  `TopCat.closedSubsetInclusion X Z` is only the source-facing bridge for the clauses that use
  closedness to describe stalks outside `Z`; the coefficient-side owner is the chapter predicate
  `IsAlgebraicStructure C F` for algebraic-structure-valued clauses and the canonical stalk and
  adjunction APIs attached to a map of spaces;
- primitive data: only the subset `Z : Set X`, its inclusion into `X`, and the coefficient pair
  `(C, F)` when a clause is stated for algebraic structures;
- derived API: the stalk comparison, the counit isomorphisms, and the terminal/zero stalk
  consequences outside `Z`, obtained from those owners.

Source/core/bridge triage:
- `source-facing`: the Stacks-project assertions about pushforward from a closed subset and the
  resulting stalk/counit behavior;
- `core/canonical`: the mathlib stalk-pushforward and pullback-pushforward-adjunction owners for a
  map of spaces;
- `bridge/view`: the specialization of those owners to the closed-subset inclusion. -/

-- Proof sketch: because `Z` is closed, every point `x ∉ Z` has an open neighbourhood disjoint
-- from `Z`; on that neighbourhood the pushforward sheaf is evaluating the original sheaf on the
-- empty open, whose sections form a singleton.
/-- Lemma 6.32.1 (1): if `x ∉ Z`, then the stalk of the pushforward of a sheaf of sets on the
closed subset `Z` is canonically a singleton; equivalently, its map to the terminal set is an
isomorphism. -/
theorem closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (((Sheaf.pushforward (Type u)
            iZ).obj
          ℱ).presheaf.stalk x)) := sorry

-- Proof sketch: the subtype inclusion `Z ↪ X` is inducing, so the canonical map on stalks for
-- pushforward along the inclusion is an isomorphism by the standard `stalkPushforward` result.
section

variable {C : Type v} [Category.{u} C] [HasColimits.{u} C]
variable (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z)

/- Core/canonical recall: for the inclusion `Z ↪ X`, the stalk comparison is the direct
specialization of `stalkPushforward_iso_of_isInducing`. -/
#check
  (stalkPushforward_iso_of_isInducing
    C Topology.IsInducing.subtypeVal ℱ.presheaf z :
      IsIso (ℱ.presheaf.stalkPushforward C iZ z))

end

local instance : PreservesLimits (forget (Type u)) :=
  CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeHom

local instance : PreservesFilteredColimits (forget (Type u)) := by
  letI : PreservesColimits (forget (Type u)) :=
    CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeHom
  exact PreservesColimits.preservesFilteredColimits (forget (Type u))

local instance : (forget (Type u)).ReflectsIsomorphisms :=
  CategoryTheory.instReflectsIsomorphismsForgetTypeHom

local instance : (forget (Type u)).Faithful := inferInstance

local instance : IsAlgebraicStructure (Type u) (forget (Type u)) where

section

variable {C : Type v} [Category.{u} C]
variable {FC : C → C → Type u} {CC : C → Type u}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
variable [IsAlgebraicStructure C (forget C)] [HasColimits.{u} C]

-- Proof sketch: for a concrete algebraic-structure category `C`, the forgetful functor
-- `forget C : C ⥤ Type u` commutes with pullback and pushforward, so the counit map is detected
-- on underlying sets and reflected back to `C`.
/-- Owner theorem: for the subset inclusion `s : Z ↪ X`, the counit
`i^{-1} i_* ℱ ⟶ ℱ` is an isomorphism for any sheaf of algebraic structures on `Z`.
The set-valued and abelian-group clauses are specializations of this owner statement. -/
theorem subsetSheaf_pullback_pushforward_counit_isIso
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) :
    IsIso ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ) := sorry

/- Set-valued specialization: for sheaves of sets on `Z`, the counit `i^{-1} i_* ℱ ⟶ ℱ` is the
direct `Type` specialization of the owner theorem above. -/
section

variable (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z))

#check
  (show IsIso ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ) from
    subsetSheaf_pullback_pushforward_counit_isIso ℱ)

end

-- Proof sketch: the abelian-group version is the same counit map as in the set-valued case, now
-- taken in `AddCommGrpCat`; the stalk computation on points of `Z` identifies it with the
-- identity on every stalk.
/- Abelian-group specialization: on abelian sheaves over `Z`, the counit
`i^{-1} i_* ℱ ⟶ ℱ` is the `AddCommGrpCat` specialization of the same owner theorem. -/
section

variable (ℱ : TopCat.Sheaf AddCommGrpCat (TopCat.of Z))

#check
  (show IsIso ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat sZ).counit.app ℱ) from
    subsetSheaf_pullback_pushforward_counit_isIso ℱ)

end

-- Proof sketch: outside `Z`, the pushforward sheaf is already the zero object on a sufficiently
-- small neighbourhood disjoint from `Z`; taking the filtered colimit defining the stalk preserves
-- this zero object in `AddCommGrpCat`.
/-- Lemma 6.32.1 (2): if `x ∉ Z`, then the stalk of the pushforward of an abelian sheaf on the
closed subset `Z` is zero. -/
theorem closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf AddCommGrpCat (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsZero
      (((Sheaf.pushforward AddCommGrpCat
          iZ).obj
        ℱ).presheaf.stalk x) := sorry

end

section

variable {C : Type v} [Category.{u} C]
variable {FC : C → C → Type u} {CC : C → Type u}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
variable [IsAlgebraicStructure C (forget C)]

-- Proof sketch: as in the set-valued case, a point outside `Z` has a neighbourhood disjoint from
-- `Z`, so the pushforward sheaf evaluates on the empty open there; for sheaves of algebraic
-- structures, sections over the empty open form the final object, and the forgetful functor to
-- `Type` reduces the filtered-stalk claim to the corresponding statement for sets.
/-- Lemma 6.32.1 (3): if `x ∉ Z`, then the chapter filtered stalk of the pushforward of a sheaf
of algebraic structures on the closed subset `Z` is terminal; equivalently, its canonical map to
the terminal object is an isomorphism. -/
theorem closedSubsetSheaf_pushforward_stalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf C (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (filteredStalk x
          ((Sheaf.pushforward C
              iZ).obj
            ℱ).presheaf)) := sorry

end

end
