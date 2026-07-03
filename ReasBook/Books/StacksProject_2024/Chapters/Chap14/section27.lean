import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_27_1 (from Chap14) -/
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

/-! ### Lemma_14_27_2 (from Chap14) -/
open CategoryTheory
open AlgebraicTopology

universe u v

noncomputable section

namespace CategoryTheory.SimplicialObject

/- Domain-style sampling for Lemma 14.27.2:
- primary domain: simplicial homotopy equivalences and the induced homotopy-equivalence property
  on the canonical chain-complex functors attached to a simplicial object;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `_root_.HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
- best owner abstraction: the source-side owner is
  `CategoryTheory.SimplicialObject.HomotopyEquiv U V`; the public target-side owner for this file
  is the morphism property `HomologicalComplex.homotopyEquivalences`, while chain-level
  `_root_.HomotopyEquiv` data remain internal proof witnesses only;
- primitive-vs-derived split:
  primitive data are the simplicial homotopy-equivalence witness `e : HomotopyEquiv U V` together
  with the existential chain homotopies furnished by Lemma 14.27.1;
  derived API is the pair of public morphism-property theorems for alternating face map complexes
  and normalized Moore complexes.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a simplicial homotopy equivalence induces a chain
  homotopy equivalence after applying `s` or `N`;
- `core/canonical`: `_root_.HomotopyEquiv` on chain complexes;
- `bridge/view`: the public morphism property
  `HomologicalComplex.homotopyEquivalences`, with any chain-level witness data constructed only
  inside the theorem proofs. -/

section AlternatingFaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

-- Proof sketch: apply Lemma 14.27.1 (1) to the two simplicial homotopies in `e`; these produce
-- the two chain homotopies needed to build an internal chain-level `HomotopyEquiv`, which is then
-- packaged into the canonical morphism-property owner.
/-- A simplicial homotopy equivalence induces a homotopy equivalence on alternating face map
complexes. -/
theorem alternatingFaceMapComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map e.hom) := by
  let h :
      _root_.HomotopyEquiv
        ((alternatingFaceMapComplex A).obj U)
        ((alternatingFaceMapComplex A).obj V) := {
      hom := (alternatingFaceMapComplex A).map e.hom
      inv := (alternatingFaceMapComplex A).map e.inv
      homotopyHomInvId := by
        classical
        simpa using
          Classical.choice
            (alternatingFaceMapComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        classical
        simpa using
          Classical.choice
            (alternatingFaceMapComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a simplicial homotopy equivalence `e` whose forward map is `a`. By
-- the previous theorem,
-- the induced map on alternating face map complexes is a chain-homotopy equivalence. The present
-- statement is the source-facing morphism-property corollary obtained by unpacking
-- `IsHomotopyEquivalence a`.
/-- Lemma 14.27.2: if a morphism of simplicial objects is a simplicial homotopy equivalence, then
the induced morphism on alternating face map complexes `s(a) : s(U) ⟶ s(V)` is a homotopy
equivalence of chain complexes. -/
theorem alternatingFaceMapComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.alternatingFaceMapComplex_map_isHomotopyEquivalence

end AlternatingFaceMapComplex

section NormalizedMooreComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

-- Proof sketch: apply Lemma 14.27.1 (2) to the two simplicial homotopies in `e`; this yields the
-- chain homotopies needed to build the internal chain-level witness for the morphism property.
/-- In an abelian category, a simplicial homotopy equivalence induces a homotopy equivalence on
normalized Moore complexes. -/
theorem normalizedMooreComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map e.hom) := by
  let h :
      _root_.HomotopyEquiv
        ((normalizedMooreComplex A).obj U)
        ((normalizedMooreComplex A).obj V) := {
      hom := (normalizedMooreComplex A).map e.hom
      inv := (normalizedMooreComplex A).map e.inv
      homotopyHomInvId := by
        classical
        rw [← Functor.map_comp, ← Functor.map_id]
        exact
          Classical.choice
            (normalizedMooreComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        classical
        rw [← Functor.map_comp, ← Functor.map_id]
        exact
          Classical.choice
            (normalizedMooreComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a simplicial homotopy equivalence `e` lifting `a`. By Lemma 14.27.1 (2),
-- the previous theorem yields the required chain-homotopy inverse for `N(a)`. The present
-- statement is the
-- source-facing morphism-property corollary obtained from `IsHomotopyEquivalence a`.
/-- In an abelian category, the normalized Moore complex also sends simplicial homotopy
equivalences to homotopy equivalences of chain complexes. -/
theorem normalizedMooreComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.normalizedMooreComplex_map_isHomotopyEquivalence

end NormalizedMooreComplex

end CategoryTheory.SimplicialObject
