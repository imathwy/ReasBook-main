import Mathlib
import StacksProject_2024.Chap12.Definition_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ShortComplex.ShortExact

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {A B C : 𝒜}

/- Domain-style sampling for Lemma 13.27.7:
- primary domain: short exact sequences in an abelian category, their Yoneda composition in
  `Ext²`, and the `3 × 3` pullback comparison between short exact sequences;
- inspected owner declarations:
  `Extension`,
  `Extension.Isomorphic`,
  `ExtensionClass.pullback`,
  `DistinguishedThreeByThreeExtension`;
- best owner abstraction:
  `source-facing`: a commutative exact `3 × 3` extension diagram over fixed rows
    `S : Extension A B` and `T : Extension B C`;
  `core/canonical`: the degree-`1` owner `ExtensionClass A T.E`;
  `bridge/view`: the pullback equation
    `ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧`.

Primitive data are the middle short exact row `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, a comparison morphism
`S.E ⟶ W`, and the pullback square over `T.f : B ⟶ T.E`. The extension-class pullback identity is
derived bridge API from that source-facing diagram data, not the main owner.
-/

-- Proof sketch: apply the contravariant long exact sequence in `Ext(-, A)` to the short exact
-- sequence `T : 0 ⟶ B ⟶ T.E ⟶ C ⟶ 0`. The vanishing of the Yoneda product means that the class of
-- `S : 0 ⟶ A ⟶ S.E ⟶ B ⟶ 0` lifts to an element of `Ext¹(T.E, A)`, and such a lift is represented
-- by a short exact sequence `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0` whose pullback along `B ⟶ T.E` recovers `S`,
-- equivalently giving the claimed exact `3 × 3` diagram.
namespace Extension

/-- Source-facing `3 × 3` extension data for Lemma 13.27.7. This is the exact diagrammatic owner:
the top row is `S`, the bottom row is `T`, the middle row is a short exact sequence
`0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, and the right-hand square is a pullback. In an abelian category this is an
exact canonical equivalent of the textbook commutative exact `3 × 3` diagram. -/
structure ThreeByThree (S : Extension A B) (T : Extension B C) where
  middleRow : Extension A T.E
  middleColumnMap : S.E ⟶ middleRow.E
  left_comm : S.f ≫ middleColumnMap = middleRow.f
  right_pullback : IsPullback S.g middleColumnMap T.f middleRow.g

namespace ThreeByThree

variable {S : Extension A B} {T : Extension B C}

@[simp]
theorem right_comm (D : ThreeByThree S T) :
    S.g ≫ T.f = D.middleColumnMap ≫ D.middleRow.g :=
  D.right_pullback.w

end ThreeByThree

end Extension

/-- The source-facing `3 × 3` extension data of `Extension.ThreeByThree` is equivalent to the
bridge/view statement that the middle row has pullback extension class `⟦S⟧`. -/
theorem nonempty_threeByThree_iff_exists_pullback_extClass_eq
    (S : Extension A B) (T : Extension B C) :
    Nonempty (Extension.ThreeByThree S T) ↔
      ∃ U : Extension A T.E,
        ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧ := sorry

variable [HasExt.{w} 𝒜]

/-- Lemma 13.27.7: for short exact sequences `S : 0 ⟶ A ⟶ E ⟶ B ⟶ 0` and
`T : 0 ⟶ B ⟶ E' ⟶ C ⟶ 0` in an abelian category, the Yoneda product of their classes in
`Ext²(C, A)` is zero if and only if there exists a commutative `3 × 3` diagram with exact
rows and columns whose middle row is `0 ⟶ A ⟶ W ⟶ E' ⟶ 0` and whose middle column is
`0 ⟶ E ⟶ W ⟶ C ⟶ 0`. -/
theorem comp_extClass_eq_zero_iff_exists_exact_three_by_three_diagram
    (S : Extension A B) (T : Extension B C) :
    (extClass T.shortExact).comp (extClass S.shortExact) rfl = 0 ↔
      Nonempty (Extension.ThreeByThree S T) := by
  rw [nonempty_threeByThree_iff_exists_pullback_extClass_eq]
  sorry

end

end CategoryTheory
