import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

/- Domain-style sampling for Lemma 14.27.1:
- primary domain: simplicial homotopy and the induced chain homotopies on the Dold-Kan chain
  complex functors;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `_root_.Homotopy.compLeft`,
  `_root_.Homotopy.compRight`,
  `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
- best owner abstraction: the source-facing owner is `SimplicialObject.Homotopic`, the canonical
  target owner is direct chain-homotopy data `_root_.Homotopy`, and the normalized-Moore
  comparison is the bridge/view supplied by the Dold-Kan homotopy equivalence;
- primitive-vs-derived split:
  primitive data are a zigzag simplicial homotopy witness `hab : Homotopic a b` and the canonical
  normalized-Moore comparison maps;
  derived API is the induced chain homotopy on alternating face map and normalized Moore
  complexes.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that zigzag-homotopic simplicial maps induce homotopic
  chain maps;
- `core/canonical`: direct chain homotopies between the induced chain maps;
- `bridge/view`: the normalized-Moore comparison between `normalizedMooreComplex` and
  `alternatingFaceMapComplex`. -/

section AlternatingFaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

-- Proof sketch: map each directed simplicial-homotopy step in the given zigzag to the induced
-- chain homotopy `H.toChainHomotopy` on alternating face map complexes; reverse steps using
-- `Homotopy.symm`, and concatenate the resulting chain homotopies using `Homotopy.trans`.
/-- Lemma 14.27.1 (1): if two morphisms of simplicial objects are homotopic in the zigzag sense,
then the induced morphisms on the alternating face map complexes `s(U) ⟶ s(V)` are homotopic as
chain maps. -/
@[stacks 019S]
theorem alternatingFaceMapComplex_map_homotopic
    (hab : Homotopic a b) :
    Nonempty
      (_root_.Homotopy
        ((alternatingFaceMapComplex A).map a)
        ((alternatingFaceMapComplex A).map b)) := by
  induction hab with
  | rel x y hxy =>
      exact ⟨hxy.some.toChainHomotopy⟩
  | refl x =>
      exact ⟨_root_.Homotopy.refl _⟩
  | symm x y _ ih =>
      rcases ih with ⟨h⟩
      exact ⟨h.symm⟩
  | trans x y z _ _ ihxy ihyz =>
      rcases ihxy with ⟨hxy⟩
      rcases ihyz with ⟨hyz⟩
      exact ⟨hxy.trans hyz⟩

end AlternatingFaceMapComplex

section NormalizedMooreComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

namespace Homotopy

-- Proof sketch: compare the normalized Moore complex with the alternating face map complex using
-- `inclusionOfMooreComplexMap` and `PInftyToNormalizedMooreComplex`, then transport the canonical
-- chain homotopy `H.toChainHomotopy` across these comparison maps by `compLeft`, `compRight`, and
-- `Homotopy.ofEq`.
/-- The normalized-Moore chain homotopy induced by a simplicial homotopy. This is the canonical
bridge from the simplicial owner `Homotopy a b` to a chain homotopy between `N(a)` and `N(b)`. -/
noncomputable def toNormalizedMooreComplexHomotopy (H : Homotopy a b) :
    _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b) :=
  let hNatA :
      (normalizedMooreComplex A).map a ≫ inclusionOfMooreComplexMap V =
        inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a := by
    simpa using (inclusionOfMooreComplex A).naturality a
  let hNatB :
      (normalizedMooreComplex A).map b ≫ inclusionOfMooreComplexMap V =
        inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map b := by
    simpa using (inclusionOfMooreComplex A).naturality b
  let hSplitV :
      inclusionOfMooreComplexMap V ≫ PInftyToNormalizedMooreComplex V = 𝟙 _ := by
    simpa [splitMonoInclusionOfMooreComplexMap] using (splitMonoInclusionOfMooreComplexMap V).id
  let h :
      _root_.Homotopy
        (inclusionOfMooreComplexMap U ≫
          ((alternatingFaceMapComplex A).map a ≫ PInftyToNormalizedMooreComplex V))
        (inclusionOfMooreComplexMap U ≫
          ((alternatingFaceMapComplex A).map b ≫ PInftyToNormalizedMooreComplex V)) :=
    ((H.toChainHomotopy.compRight (PInftyToNormalizedMooreComplex V)).compLeft
        (inclusionOfMooreComplexMap U))
  let ha :
      (normalizedMooreComplex A).map a =
        inclusionOfMooreComplexMap U ≫
          ((alternatingFaceMapComplex A).map a ≫ PInftyToNormalizedMooreComplex V) := by
    calc
      (normalizedMooreComplex A).map a =
          (normalizedMooreComplex A).map a ≫ 𝟙 _ := by simp
      _ =
          (normalizedMooreComplex A).map a ≫
            (inclusionOfMooreComplexMap V ≫ PInftyToNormalizedMooreComplex V) := by
              rw [← hSplitV]
              rfl
      _ =
          ((normalizedMooreComplex A).map a ≫ inclusionOfMooreComplexMap V) ≫
            PInftyToNormalizedMooreComplex V := by simp [Category.assoc]
      _ =
          (inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a) ≫
            PInftyToNormalizedMooreComplex V := by rw [hNatA]
      _ = inclusionOfMooreComplexMap U ≫
            ((alternatingFaceMapComplex A).map a ≫ PInftyToNormalizedMooreComplex V) := by
              simp [Category.assoc]
  let hb :
      (normalizedMooreComplex A).map b =
        inclusionOfMooreComplexMap U ≫
          ((alternatingFaceMapComplex A).map b ≫ PInftyToNormalizedMooreComplex V) := by
    calc
      (normalizedMooreComplex A).map b =
          (normalizedMooreComplex A).map b ≫ 𝟙 _ := by simp
      _ =
          (normalizedMooreComplex A).map b ≫
            (inclusionOfMooreComplexMap V ≫ PInftyToNormalizedMooreComplex V) := by
              rw [← hSplitV]
              rfl
      _ =
          ((normalizedMooreComplex A).map b ≫ inclusionOfMooreComplexMap V) ≫
            PInftyToNormalizedMooreComplex V := by simp [Category.assoc]
      _ =
          (inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map b) ≫
            PInftyToNormalizedMooreComplex V := by rw [hNatB]
      _ = inclusionOfMooreComplexMap U ≫
            ((alternatingFaceMapComplex A).map b ≫ PInftyToNormalizedMooreComplex V) := by
              simp [Category.assoc]
  (_root_.Homotopy.ofEq ha).trans (h.trans (_root_.Homotopy.ofEq hb.symm))

/-- Degreewise comparison formula for `Homotopy.toNormalizedMooreComplexHomotopy`. -/
theorem toNormalizedMooreComplexHomotopy_hom (H : Homotopy a b) (n : ℕ) :
    H.toNormalizedMooreComplexHomotopy.hom n (n + 1) =
      (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫
        (PInftyToNormalizedMooreComplex V).f (n + 1) := by
  simp only [Homotopy.toNormalizedMooreComplexHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compLeft_hom, _root_.Homotopy.compRight_hom,
    Pi.zero_apply, zero_add, add_zero]

end Homotopy

-- Proof sketch: apply part (1) to obtain a homotopy between `s(a)` and `s(b)`. Then identify
-- `N(a)` and `N(b)` as the composites
-- `N(U) ⟶ s(U) ⟶ s(V) ⟶ N(V)` via `inclusionOfMooreComplexMap` and
-- `PInftyToNormalizedMooreComplex`, and use the canonical operations
-- `(h.compLeft _).compRight _` to pre- and postcompose the chain homotopy. The required
-- comparison equalities are the naturality formulas from the normalized-Moore comparison.
/-- Lemma 14.27.1 (2): if `A` is abelian and two morphisms of simplicial objects are homotopic in
the zigzag sense, then the induced morphisms on the normalized Moore complexes `N(U) ⟶ N(V)` are
homotopic as chain maps. -/
@[stacks 019S]
theorem normalizedMooreComplex_map_homotopic
    (hab : Homotopic a b) :
    Nonempty
      (_root_.Homotopy
        ((normalizedMooreComplex A).map a)
        ((normalizedMooreComplex A).map b)) := by
  induction hab with
  | rel x y hxy =>
      exact ⟨hxy.some.toNormalizedMooreComplexHomotopy⟩
  | refl x =>
      exact ⟨_root_.Homotopy.refl _⟩
  | symm x y _ ih =>
      rcases ih with ⟨h⟩
      exact ⟨h.symm⟩
  | trans x y z _ _ ihxy ihyz =>
      rcases ihxy with ⟨hxy⟩
      rcases ihyz with ⟨hyz⟩
      exact ⟨hxy.trans hyz⟩

end NormalizedMooreComplex

end CategoryTheory.SimplicialObject
