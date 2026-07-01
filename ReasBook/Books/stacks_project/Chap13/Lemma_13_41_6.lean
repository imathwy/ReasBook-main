import Mathlib
import stacks_project.Chap13.Lemma_13_41_3
import stacks_project.Chap13.Lemma_13_41_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.41.6:
- primary domain: existence and uniqueness of finite Postnikov systems in a pretriangulated
  category under stagewise Hom-vanishing;
- inspected owner declarations:
  `PostnikovSystem`,
  `shifted_hom_vanishes_above_successor`,
  `morphism_extends_to_postnikovSystemMorphism`,
  `Pretriangulated.isIso₃_of_isIso₁₂`;
- best owner abstraction:
  `source-facing`: existence of `PostnikovSystem X` and isomorphism between two such systems;
  `core/canonical`: the extension owner `morphism_extends_to_postnikovSystemMorphism` and the
    stagewise distinguished-triangle two-out-of-three theorem
    `Pretriangulated.isIso₃_of_isIso₁₂`;
  `bridge/view`: the triangle-valued view `P.triangle i` of each Postnikov stage;
- primitive-vs-derived split:
  primitive data: the complex `X`, its complexness hypothesis, and the source-facing vanishing
  predicate `shifted_hom_vanishes_above_successor`;
  derived API: existence of an identity-over morphism of Postnikov systems and the resulting
    stagewise isomorphism statement. -/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
variable {n : ℕ}

open PostnikovSystemMorphism

namespace PostnikovSystemMorphism

-- Proof sketch: for the induced morphism between the stage triangles of `P` and `P'`, the middle
-- component is the identity on `X`, hence an isomorphism. Starting from the rightmost stage, where
-- `toX` is an isomorphism by definition, apply `Pretriangulated.isIso₃_of_isIso₁₂` inductively to
-- the stage triangle morphisms to show that each auxiliary component map `ψ.yMap i` is an
-- isomorphism.
/-- Under the vanishing hypothesis of Lemma 13.41.6 (2), any morphism of Postnikov systems over the
identity of `X` is stagewise an isomorphism on the auxiliary objects. This is the derived
stagewise-isomorphism API attached to the source-facing uniqueness statement. -/
theorem yMap_isIso_of_extension_vanishing
    {X : ComposableArrows D n} {P P' : PostnikovSystem X}
    (ψ : PostnikovSystemMorphism P P' (𝟙 X))
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily)
    (i : Fin (n + 1)) : IsIso (ψ.yMap i) := sorry

end PostnikovSystemMorphism

-- Proof sketch: induct on the length `n`. The cases `n = 0, 1, 2` are Lemma 13.41.3. For the
-- inductive step, choose a Postnikov system on the tail complex, use the long exact Hom sequence
-- of the last distinguished triangle to reduce extension to a vanishing statement for
-- `Hom(X_n, Y_{n - 3}[-1])`, and then deduce that vanishing from the stated hypothesis exactly as
-- in Lemma 13.41.4 (1).
/-- Lemma 13.41.6 (1): if `X` is a finite complex and `Hom(X_i[i - j - 2], X_j) = 0` for
`i > j + 2`, then `X` admits a Postnikov system. This is expressed via the owner hypothesis
`shifted_hom_vanishes_above_successor X.intFamily (fun i ↦ X.intFamily (i - 1))`. -/
theorem postnikovSystem_exists_of_existence_vanishing
    (X : ComposableArrows D n) (hX : X.IsComplex)
    (h : shifted_hom_vanishes_above_successor
      X.intFamily (fun i ↦ X.intFamily (i - 1))) :
    Nonempty (PostnikovSystem X) := sorry

-- Proof sketch: Lemma 13.41.4 (2) applied to the identity morphism of `X` gives a morphism
-- `P ⟶ P'`. Applying `Pretriangulated.isIso₃_of_isIso₁₂` to the induced morphism between the
-- stage triangles of `P` and `P'`, and inducting from the rightmost stage where `toX` is an
-- isomorphism by definition, shows that every component map on the auxiliary objects is an
-- isomorphism.
/-- Lemma 13.41.6 (2): if `Hom(X_i[i - j - 1], X_j) = 0` for `i > j + 1`, then any two
Postnikov systems on `X` are isomorphic. The vanishing hypothesis is taken directly in the owner
form `shifted_hom_vanishes_above_successor X.intFamily X.intFamily`. -/
theorem postnikovSystem_isomorphic_of_extension_vanishing
    {X : ComposableArrows D n} (P P' : PostnikovSystem X)
    (h : shifted_hom_vanishes_above_successor X.intFamily X.intFamily) :
    ∃ ψ : PostnikovSystemMorphism P P' (𝟙 X), ∀ i, IsIso (ψ.yMap i) := by
  rcases morphism_extends_to_postnikovSystemMorphism P P' (𝟙 X) h with ⟨ψ⟩
  exact ⟨ψ, yMap_isIso_of_extension_vanishing ψ h⟩

end

end CategoryTheory
