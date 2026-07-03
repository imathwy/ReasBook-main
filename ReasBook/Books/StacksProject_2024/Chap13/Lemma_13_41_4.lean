import Mathlib
import StacksProject_2024.Chap13.Definition_13_41_1
import StacksProject_2024.Chap13.«13_41_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ZeroObject

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.4:
- primary domain: Postnikov systems in a pretriangulated category and stagewise Hom-vanishing;
- inspected owner declarations:
  `shifted_hom_vanishes_above_successor`,
  `ComposableArrows.intFamily`,
  `PostnikovSystem.intFamily`,
  `PostnikovSystem`,
  `PostnikovSystemMorphism`;
- best owner abstraction: the familywise vanishing condition is already owned by
  `shifted_hom_vanishes_above_successor` on ℤ-indexed object families, and the finite-row
  bookkeeping should be routed through the owner bridges `X.intFamily` and `P'.intFamily`;
- source/core/bridge triage:
  `source-facing`: the extension existence statement for morphisms of Postnikov systems,
  `core/canonical`: the owner vanishing predicate `shifted_hom_vanishes_above_successor`,
  `bridge/view`: the owner-level auxiliary-family view `P'.intFamily`;
- primitive-vs-derived split:
  primitive data: a Postnikov system `P'` and the owner vanishing hypothesis on `X` and `X'`,
  derived API: the entrywise zero-morphism conclusion for maps into the auxiliary objects of `P'`.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

-- Proof sketch: induct on the stage `b` of the Postnikov system `P'`. For the inductive step,
-- use the distinguished triangle `Y'_b ⟶ X'_b ⟶ Y'_{b-1} ⟶ Y'_b[1]` and the resulting exact
-- sequence of Hom groups; the outer terms vanish by the induction hypothesis and the assumed
-- vanishing into `X'_b`.
/-- Lemma 13.41.4 (1): if `P'` is a Postnikov system on `X'` and
`Hom(X_i[i - j - 1], X'_j) = 0` for `i > j + 1`, then also
`Hom(X_i[i - j - 1], Y'_j) = 0` for `i > j + 1`, where `Y'_j` is the `j`th auxiliary object of
`P'`. The main statement is kept at the owner level
`shifted_hom_vanishes_above_successor X.intFamily P'.intFamily`; the pointwise
zero-morphism
form is the companion theorem `postnikov_auxiliary_vanishing_apply`. -/
theorem postnikov_auxiliary_vanishing
    {n : ℕ} {X X' : ComposableArrows D n} (P' : PostnikovSystem X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily) :
    shifted_hom_vanishes_above_successor X.intFamily P'.intFamily := sorry

/-- The owner-level vanishing result of Lemma 13.41.4 (1), specialized back to the original
entrywise zero-morphism form for maps into the auxiliary objects of `P'`. -/
theorem postnikov_auxiliary_vanishing_apply
    {n : ℕ} {X X' : ComposableArrows D n} (P' : PostnikovSystem X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily)
    {a b : Fin (n + 1)} (hab : a.1 + 1 < b.1)
    (f : ShiftedHom (X.obj a) (P' b) ((a.1 : ℤ) + 1 - b.1)) :
    f = 0 := by
  have hsub :
      Subsingleton (ShiftedHom (X.obj a) (P' b) ((a.1 : ℤ) + 1 - b.1)) :=
    P'.subsingleton_hom_of_shifted_hom_vanishes_above_successor
      (postnikov_auxiliary_vanishing P' h) hab
  exact hsub.elim f 0

-- Proof sketch: induct on the length of the Postnikov system extension problem. After extending
-- the morphism on the shorter truncation, the obstruction to commutativity at the top stage
-- factors through `Y'_{j-1}[-1]`; part (1) makes that obstruction vanish, and then TR3 supplies
-- the missing morphism of distinguished triangles.
/-- Lemma 13.41.4 (2): if `P` and `P'` are Postnikov systems on two complexes and
`Hom(X_i[i - j - 1], X'_j) = 0` for `i > j + 1`, then any morphism of complexes `φ : X ⟶ X'`
extends to a morphism of Postnikov systems. The vanishing hypothesis is taken directly in the
owner form `shifted_hom_vanishes_above_successor X.intFamily X'.intFamily`. -/
theorem morphism_extends_to_postnikovSystemMorphism
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X')
    (h : shifted_hom_vanishes_above_successor X.intFamily X'.intFamily) :
    Nonempty (PostnikovSystemMorphism P P' φ) := sorry

end

end CategoryTheory
