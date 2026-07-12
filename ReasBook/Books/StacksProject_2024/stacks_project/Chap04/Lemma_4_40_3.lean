import Mathlib
import StacksProject_2024.Chap04.Definition_4_40_1
import StacksProject_2024.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ v₁

namespace CategoryTheory

open FibredInGroupoidsOver
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]

/- Domain-style sampling for Lemma 4.40.3:
- primary domain: morphisms between representable categories fibred in groupoids over a fixed base
  and their description through slice categories;
- sampled owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsMor`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence`;
- best owner abstraction: the bundled chapter owner `FibredInGroupoidsOver C`, with morphisms
  expressed by `FibredInGroupoidsMor`;
- primitive data: only the represented fibred-groupoid objects and the chosen equivalences over
  `C` to slice projections;
- derived API: the source-facing predicate `FibredInGroupoidsMor.InducesHom`, together with the
  quotient-level equivalence on `2`-isomorphism classes of morphisms and its slice
  specialization.

Source/core/bridge triage:
- `source-facing`: Lemma 4.40.3 for represented fibred groupoids and its slice specialization;
- `core/canonical`: `FibredInGroupoidsOver`, `FibredInGroupoidsMor`,
  `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the internal transport from a represented fibred groupoid to the slice model
  `Over.forget X`.

The refinement therefore keeps the slice transport machinery private, but moves the public API to
the owner-level morphism type `FibredInGroupoidsMor` instead of repeating raw
`BasedCategory.ofFunctor ... ⥤ᵇ ...` types.
-/

namespace FibredInGroupoidsOver

/-- The canonical morphism `C/X ⟶ C/Y` over `C` induced by postcomposition with
`φ : X ⟶ Y`. This is the owner-level bridge from `Over.map φ` to the chapter's morphism type
`FibredInGroupoidsMor`. -/
abbrev overMap {X Y : C} (φ : X ⟶ Y) :
    FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := Over.map φ
      w := Over.mapForget_eq φ }

end FibredInGroupoidsOver

-- Proof sketch: because a based functor `F : C/X ⟶ C/Y` commutes strictly with the forgetful
-- functors to `C`, the object `F.obj (Over.mk (𝟙 X))` lies over `X`.
/-- The image of `id_X : X/X` under a morphism `C/X ⟶ C/Y` over `C` has source object `X`. -/
private theorem sliceMor_obj_id_left_eq {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) :
    ((G F).obj (Over.mk (𝟙 X))).left = X := sorry

/-- The morphism `X ⟶ Y` obtained by evaluating `F : C/X ⟶ C/Y` over `C` at `id_X : X/X`. -/
private def sliceMorToHom {X Y : C}
    (F : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)) :
    X ⟶ Y :=
  eqToHom (sliceMor_obj_id_left_eq F).symm ≫ ((G F).obj (Over.mk (𝟙 X))).hom

-- Proof sketch: a vertical natural isomorphism between two morphisms `C/X ⟶ C/Y` over `C`
-- evaluates at `id_X` to a vertical isomorphism in `C/Y`, hence identifies the recovered arrows
-- `X ⟶ Y`.
private theorem sliceMorToHom_eq_of_isomorphic {X Y : C}
    {F G : ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y)}
    (hFG : IsIsomorphic F G) :
    sliceMorToHom F = sliceMorToHom G := sorry

private noncomputable def sliceMorIsoClassesToHom (X Y : C) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)))) →
      (X ⟶ Y) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)) ↦
        sliceMorToHom F)
      (fun _ _ hFG ↦ sliceMorToHom_eq_of_isomorphic hFG)

-- Proof sketch: specialize
-- `FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence` to
-- `(FibredInGroupoidsOver.ofFunctor (Over.forget Y) : FibredInGroupoidsOver C).toFibredCategoryOver`
-- at `X`, so evaluation at `id_X` induces a bijection on isomorphism classes; compose with the
-- canonical identification of the fiber of `Over.forget Y` over `X` with `Hom_C(X, Y)`.
private theorem sliceMorIsoClassesToHom_bijective (X Y : C) :
    Function.Bijective (sliceMorIsoClassesToHom X Y) := sorry

private theorem slice_id_isEquivalenceOverBase (X : C) :
    FibredInGroupoidsMor.IsEquivalenceOverBase
      (((𝟙 (ofFunctor (Over.forget X))) :
        FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget X)))) :=
  FibredInGroupoidsOver.hom_isEquivalenceOverBase (Bicategory.Equivalence.id _)

/-- Transport a morphism between represented fibred categories to a morphism between the
corresponding slice categories. -/
private noncomputable def representableFibredInGroupoidsMorToSliceMor
    {P Q : FibredInGroupoidsOver C}
    {X Y : C}
    (j : P ⟶ ofFunctor (Over.forget X))
    (j' : Q ⟶ ofFunctor (Over.forget Y))
    (hj : FibredInGroupoidsMor.IsEquivalenceOverBase j)
    (F : P ⟶ Q) :
    ofFunctor (Over.forget X) ⟶ ofFunctor (Over.forget Y) :=
  let i : ofFunctor (Over.forget X) ⟶ P :=
    Classical.choose (FibredInGroupoidsMor.exists_inverse j hj)
  (i ≫ F) ≫ j'

private theorem representableFibredInGroupoidsMorToHom_eq_of_isomorphic
    {P Q : FibredInGroupoidsOver C}
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase)
    {F G : FibredInGroupoidsMor P Q}
    (hFG : IsIsomorphic F G) :
    sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj F) =
      sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj G) := sorry

private noncomputable def representableFibredInGroupoidsMorIsoClassesToHom
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor P Q)) →
      (X ⟶ Y) :=
  fun qFG ↦
    Quotient.liftOn qFG
      (fun F : FibredInGroupoidsMor P Q ↦
        sliceMorToHom (representableFibredInGroupoidsMorToSliceMor j j' hj F))
      (fun _ _ hFG ↦ representableFibredInGroupoidsMorToHom_eq_of_isomorphic j j' hj hFG)

-- Proof sketch: transport the hom-category of morphisms `p ⟶ q` across the chosen slice
-- presentations, reduce to the slice statement proved above, and use the fact that changing the
-- quasi-inverse of `j` does not change the induced class in the slice hom-category.
private theorem representableFibredInGroupoidsMorIsoClassesToHom_bijective
    (P Q : FibredInGroupoidsOver C)
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    Function.Bijective
      (representableFibredInGroupoidsMorIsoClassesToHom P Q j j' hj) := sorry

namespace FibredInGroupoidsMor

variable {P Q : FibredInGroupoidsOver C}

/-- A morphism `F : P ⟶ Q` induces the morphism `φ : X ⟶ Y` on isomorphism classes of objects,
with respect to chosen presentations `j : P ⟶ C/X` and `j' : Q ⟶ C/Y`, when the two composites
`P ⟶ Q ⟶ C/Y` and `P ⟶ C/X ⟶ C/Y` are `2`-isomorphic over `C`. This is the source-facing
condition behind Lemma 4.40.3. -/
def InducesHom
    {X Y : C}
    (F : P ⟶ Q)
    (j : P ⟶ ofFunctor (Over.forget X))
    (j' : Q ⟶ ofFunctor (Over.forget Y))
    (φ : X ⟶ Y) : Prop :=
  Nonempty
    ((F ≫ j') ≅
      (j ≫ FibredInGroupoidsOver.overMap φ))

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

variable {P Q : FibredInGroupoidsOver C}

/-- Quotient-level reformulation of Lemma 4.40.3: if bundled categories fibred in groupoids `P`
and `Q` are represented by objects `X` and `Y` of `C` through presentation morphisms over `C`,
then the set of `2`-isomorphism classes of `1`-morphisms from `P` to `Q` is canonically
identified with `Hom_C(X, Y)`. The source-facing induced-map condition is exposed separately as
`FibredInGroupoidsMor.InducesHom`. -/
noncomputable def mor_isoClasses_equiv_hom
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) ≃ (X ⟶ Y) :=
  Equiv.ofBijective
    (representableFibredInGroupoidsMorIsoClassesToHom P Q j j' hj)
    (representableFibredInGroupoidsMorIsoClassesToHom_bijective P Q j j' hj hj')

/-- Companion bridge for Lemma 4.40.3: the same canonical equivalence expressed using chosen
bicategorical equivalences `P ≌ C/X` and `Q ≌ C/Y` in `FibredInGroupoidsOver C`. -/
noncomputable def mor_isoClasses_equiv_hom_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y)) :
    isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) ≃
      (X ⟶ Y) :=
  mor_isoClasses_equiv_hom
    eP.hom
    eQ.hom
    (FibredInGroupoidsOver.hom_isEquivalenceOverBase eP)
    (FibredInGroupoidsOver.hom_isEquivalenceOverBase eQ)

/-- Companion reformulation of Lemma 4.40.3: for chosen presentation morphisms of `P` and `Q`
by `X` and `Y`, the canonical map from `2`-isomorphism classes of `1`-morphisms `P ⟶ Q` to
`Hom_C(X, Y)` is bijective. -/
theorem mor_isoClasses_to_hom_bijective
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase) :
    Function.Bijective
      (mor_isoClasses_equiv_hom j j' hj hj' :
        isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) →
          (X ⟶ Y)) :=
  (mor_isoClasses_equiv_hom j j' hj hj').bijective

/-- Companion bridge reformulation of Lemma 4.40.3 using chosen bicategorical equivalences to the
slice presentations `C/X ⥤ C` and `C/Y ⥤ C`. -/
theorem mor_isoClasses_to_hom_bijective_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y)) :
    Function.Bijective
      (mor_isoClasses_equiv_hom_of_equivalences eP eQ :
        isomorphismClasses.obj (Cat.of (FibredInGroupoidsMor P Q)) →
          (X ⟶ Y)) :=
  (mor_isoClasses_equiv_hom_of_equivalences eP eQ).bijective

/-- Companion bridge for Lemma 4.40.3: the source-facing induced-map condition agrees with the
quotient-level equivalence `mor_isoClasses_equiv_hom`. -/
theorem inducesHom_iff_mor_isoClasses_equiv_hom_eq
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase)
    (F : FibredInGroupoidsMor P Q) (φ : X ⟶ Y) :
    FibredInGroupoidsMor.InducesHom F j j' φ ↔
      mor_isoClasses_equiv_hom j j' hj hj' (Quotient.mk'' F) = φ := sorry

/-- Lemma 4.40.3, more precisely: every morphism `φ : X ⟶ Y` is represented by a `1`-morphism
`F : P ⟶ Q` over `C` that induces `φ` on isomorphism classes of objects, and such an `F` is
unique up to a unique `2`-isomorphism. -/
theorem exists_unique_morphism_up_to_unique_iso_of_hom
    {X Y : C}
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor Q (ofFunctor (Over.forget Y)))
    (hj : j.IsEquivalenceOverBase) (hj' : j'.IsEquivalenceOverBase)
    (φ : X ⟶ Y) :
    ∃ F : FibredInGroupoidsMor P Q,
      FibredInGroupoidsMor.InducesHom F j j' φ ∧
        ∀ G : FibredInGroupoidsMor P Q,
          FibredInGroupoidsMor.InducesHom G j j' φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := sorry

/-- Companion bridge form of the existence-and-uniqueness statement in Lemma 4.40.3, using
chosen bicategorical equivalences to slice categories. -/
theorem exists_unique_morphism_up_to_unique_iso_of_hom_of_equivalences
    {X Y : C}
    (eP : P ≌ ofFunctor (Over.forget X))
    (eQ : Q ≌ ofFunctor (Over.forget Y))
    (φ : X ⟶ Y) :
    ∃ F : FibredInGroupoidsMor P Q,
      FibredInGroupoidsMor.InducesHom F eP.hom eQ.hom φ ∧
        ∀ G : FibredInGroupoidsMor P Q,
          FibredInGroupoidsMor.InducesHom G eP.hom eQ.hom φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := by
  simpa [FibredInGroupoidsMor.InducesHom, mor_isoClasses_equiv_hom_of_equivalences] using
    exists_unique_morphism_up_to_unique_iso_of_hom
      eP.hom
      eQ.hom
      (FibredInGroupoidsOver.hom_isEquivalenceOverBase eP)
      (FibredInGroupoidsOver.hom_isEquivalenceOverBase eQ)
      φ

end FibredInGroupoidsOver

/-- Quotient-level specialization of Lemma 4.40.3 to slice categories: the set of
`2`-isomorphism classes of morphisms `C/X ⟶ C/Y` over `C` is canonically identified with
`Hom_C(X, Y)`. -/
noncomputable def sliceMor_isoClasses_equiv_hom (X Y : C) :
    isomorphismClasses.obj
        (Cat.of (FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)))) ≃
      (X ⟶ Y) :=
  FibredInGroupoidsOver.mor_isoClasses_equiv_hom
    (𝟙 (ofFunctor (Over.forget X)))
    (𝟙 (ofFunctor (Over.forget Y)))
    (slice_id_isEquivalenceOverBase X)
    (slice_id_isEquivalenceOverBase Y)

/-- Companion reformulation of the slice specialization of Lemma 4.40.3: the canonical map to
`Hom_C(X, Y)` is bijective. -/
theorem sliceMor_isoClasses_to_hom_bijective (X Y : C) :
    Function.Bijective
      (sliceMor_isoClasses_equiv_hom X Y :
        isomorphismClasses.obj
            (Cat.of
              (FibredInGroupoidsMor (ofFunctor (Over.forget X))
                (ofFunctor (Over.forget Y)))) →
          (X ⟶ Y)) :=
  (sliceMor_isoClasses_equiv_hom X Y).bijective

/-- Companion specialization of the existence-and-uniqueness form of Lemma 4.40.3 to slice
categories. -/
theorem exists_unique_slice_morphism_up_to_unique_iso_of_hom {X Y : C} (φ : X ⟶ Y) :
    ∃ F :
        FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)),
      FibredInGroupoidsMor.InducesHom
          F (𝟙 (ofFunctor (Over.forget X))) (𝟙 (ofFunctor (Over.forget Y))) φ ∧
        ∀ G :
            FibredInGroupoidsMor (ofFunctor (Over.forget X)) (ofFunctor (Over.forget Y)),
          FibredInGroupoidsMor.InducesHom
            G (𝟙 (ofFunctor (Over.forget X))) (𝟙 (ofFunctor (Over.forget Y))) φ →
            Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G) := by
  simpa [sliceMor_isoClasses_equiv_hom, FibredInGroupoidsMor.InducesHom] using
    FibredInGroupoidsOver.exists_unique_morphism_up_to_unique_iso_of_hom
      (𝟙 (ofFunctor (Over.forget X)))
      (𝟙 (ofFunctor (Over.forget Y)))
      (slice_id_isEquivalenceOverBase X)
      (slice_id_isEquivalenceOverBase Y)
      φ

end CategoryTheory
