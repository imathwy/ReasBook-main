import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib owners
-- `Scheme.PartialMap` and `Scheme.RationalMap`; local Chapter 29 precedent supplies
-- `schemeTheoreticallyDense` and Lemma 29.7.6 as `schemeTheoreticallyDense_inf`.
-- The tag evidence is consistent: item tag `01RX` matches the source URL `/tag/01RX`.

/-- Remark 29.49.14 (1): the variant partial maps are those partial maps whose domains are
scheme theoretically dense open subschemes of the source. -/
@[stacks 01RX]
abbrev PseudoPartialMap (X Y : Scheme.{u}) : Type u :=
  { f : X.PartialMap Y // schemeTheoreticallyDense f.domain }

/-- A pseudo-partial map has scheme theoretically dense domain. -/
theorem PseudoPartialMap.schemeTheoreticallyDense_domain {X Y : Scheme.{u}}
    (f : PseudoPartialMap X Y) :
    schemeTheoreticallyDense f.1.domain := sorry

/-- Remark 29.49.14 (2): the usual equivalence relation on partial maps restricts to an
equivalence relation on partial maps defined on scheme theoretically dense open subschemes. -/
@[stacks 01RX]
theorem pseudoPartialMap_equivalence (X Y : Scheme.{u}) :
    Equivalence (fun f g : PseudoPartialMap X Y ↦ f.1.equiv g.1) := sorry

/-- A rational map is a pseudo-morphism representative if it comes from a partial map defined on a
scheme theoretically dense open subscheme. -/
def RationalMap.HasSchemeTheoreticallyDenseRepresentative {X Y : Scheme.{u}}
    (φ : X.RationalMap Y) : Prop :=
  ∃ f : PseudoPartialMap X Y, f.1.toRationalMap = φ

/-- Unfold the predicate that a rational map has a representative on a scheme theoretically dense
open subscheme. -/
theorem RationalMap.hasSchemeTheoreticallyDenseRepresentative_iff {X Y : Scheme.{u}}
    (φ : X.RationalMap Y) :
    φ.HasSchemeTheoreticallyDenseRepresentative ↔
      ∃ f : PseudoPartialMap X Y, f.1.toRationalMap = φ := sorry

/-- Remark 29.49.14 (3): a pseudo-morphism from `X` to `Y` is the equivalence class, represented
canonically as the corresponding rational map, of a partial map from a scheme theoretically dense
open subscheme of `X` to `Y`. -/
@[stacks 01RX]
abbrev PseudoMorphism (X Y : Scheme.{u}) : Type u :=
  { φ : X.RationalMap Y // φ.HasSchemeTheoreticallyDenseRepresentative }

/-- The rational map associated to a pseudo-morphism by forgetting that representatives were
required to have scheme theoretically dense domain. -/
abbrev PseudoMorphism.toRationalMap {X Y : Scheme.{u}} (φ : PseudoMorphism X Y) :
    X.RationalMap Y :=
  φ.1

/-- Every pseudo-morphism has a representative pseudo-partial map. -/
theorem PseudoMorphism.exists_pseudoPartialMap {X Y : Scheme.{u}} (φ : PseudoMorphism X Y) :
    ∃ f : PseudoPartialMap X Y, f.1.toRationalMap = φ.toRationalMap := sorry

/-- On a representative pseudo-partial map, `PseudoMorphism.toRationalMap` is the usual rational
map associated to that partial map. -/
theorem PseudoMorphism.toRationalMap_mk {X Y : Scheme.{u}} (f : PseudoPartialMap X Y) :
    PseudoMorphism.toRationalMap
        (⟨f.1.toRationalMap, ⟨f, rfl⟩⟩ : PseudoMorphism X Y) =
      f.1.toRationalMap := sorry

/-- Remark 29.49.14 (4): if the source scheme is reduced, pseudo-morphisms from `X` to `Y`
coincide with the usual rational maps from `X` to `Y`. -/
@[stacks 01RX]
theorem pseudoMorphism_toRationalMap_bijective_of_isReduced {X Y : Scheme.{u}} [IsReduced X] :
    Function.Bijective
      (PseudoMorphism.toRationalMap : PseudoMorphism X Y → X.RationalMap Y) := sorry

end AlgebraicGeometry.Scheme
