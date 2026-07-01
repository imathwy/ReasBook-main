import Mathlib
import stacks_project.Chap13.Definition_13_41_1
import stacks_project.Chap13.Lemma_13_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.41.5:
- primary domain: uniqueness of morphisms of Postnikov systems in a pretriangulated category under
  Hom-vanishing hypotheses;
- inspected owner declarations:
  `ShiftedHom`,
  `shifted_hom_vanishes_above_successor`,
  `PostnikovSystemMorphism`,
  `PostnikovSystemMorphism.triangleMorphism`,
  `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`;
- best owner abstraction:
  `source-facing`: the three global textbook Hom-vanishing alternatives for Postnikov systems,
  `core/canonical`: the triangle category owner together with the stagewise uniqueness theorem
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, the shifted-Hom owner `ShiftedHom`, and
    the chapter-level familywise vanishing owner `shifted_hom_vanishes_above_successor`,
  `bridge/view`: the stagewise triangle morphisms `ψ.triangleMorphism i` and the canonical
    translation between the source-facing index formulas and those owner-level shifted-Hom
    vanishing predicates;
- primitive-vs-derived split:
  primitive data: the two Postnikov systems and the source-facing global vanishing alternative,
  derived API: the induced triangle-level uniqueness statements obtained by applying
    `triangleMorphism_eq_of_outer_eq_of_hom_vanishing` to the stage triangles. The third
  alternative remains source-facing here, rather than being repackaged, because this file does
    not yet have an upstream owner predicate for the paired cross-vanishing hypothesis. -/

-- Proof sketch: argue by induction on the length of the Postnikov systems. In the first two
-- vanishing cases, the successive maps to or from the extreme auxiliary object are forced stage by
-- stage by the distinguished triangles of the Postnikov systems. In the third case, compare two
-- candidate morphisms on the top distinguished triangles and apply
-- `triangleMorphism_eq_of_outer_eq_of_hom_vanishing`, using the stated cross-vanishing together
-- with the inductive description of the auxiliary objects exactly as in Lemmas 13.41.4 and 13.4.8.
/-- Lemma 13.41.5: if any one of the three textbook Hom-vanishing hypotheses holds for two
Postnikov systems over a morphism `φ : X ⟶ X'`, then there exists at most one morphism of
Postnikov systems lying over `φ`. -/
theorem postnikovSystemMorphism_subsingleton_of_hom_vanishing
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (hvan :
      (∀ a : Fin n, Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))) ∨
        (∀ a : Fin n,
          Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))) ∨
          (∀ ⦃a b : Fin (n + 1)⦄, b < a →
            Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
              Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1)))) :
    Subsingleton (PostnikovSystemMorphism P P' φ) := sorry

end

end CategoryTheory
