import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory
open unitInterval

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyWith` is the canonical owner for
-- homotopies through maps satisfying a predicate, and `Under A` is the canonical category of
-- spaces under a fixed space `A`.

/-- The predicate saying that a continuous map `X.right ⟶ Y.right` is a map under `A`. -/
def underMapCondition {A : TopCat} (X Y : Under A) : C(X.right, Y.right) → Prop :=
  fun f ↦ f.comp X.hom.hom = Y.hom.hom

/-- Definition 6.5.2 (1): for morphisms `f₀ f₁ : X ⟶ Y` in `Under A`, a homotopy under `A`,
written rel `A`, is a homotopy through maps under `A`. -/
abbrev UnderHomotopy {A : TopCat} {X Y : Under A} (f₀ f₁ : X ⟶ Y) : Type _ :=
  ContinuousMap.HomotopyWith f₀.right.hom f₁.right.hom (underMapCondition X Y)

namespace UnderHomotopy

/-- Every intermediate stage of a homotopy under `A` is again a map under `A`. -/
theorem w {A : TopCat} {X Y : Under A} {f₀ f₁ : X ⟶ Y} (H : UnderHomotopy f₀ f₁) (t : I) :
    (H.toHomotopy.curry t).comp X.hom.hom = Y.hom.hom :=
  H.prop t

end UnderHomotopy

/-- Two morphisms in `Under A` are homotopic under `A` if they are connected by a homotopy through
maps under `A`. -/
abbrev HomotopicUnder {A : TopCat} {X Y : Under A} (f₀ f₁ : X ⟶ Y) : Prop :=
  ContinuousMap.HomotopicWith f₀.right.hom f₁.right.hom (underMapCondition X Y)

namespace HomotopicUnder

/-- Every morphism in `Under A` is homotopic under `A` to itself. -/
theorem refl {A : TopCat} {X Y : Under A} (f : X ⟶ Y) : HomotopicUnder f f :=
  ContinuousMap.HomotopicWith.refl f.right.hom <| by
    simpa [underMapCondition] using congrArg TopCat.Hom.hom (Under.w f)

/-- Homotopy under `A` is symmetric. -/
@[symm] theorem symm {A : TopCat} {X Y : Under A} {f₀ f₁ : X ⟶ Y}
    (h : HomotopicUnder f₀ f₁) : HomotopicUnder f₁ f₀ :=
  ContinuousMap.HomotopicWith.symm h

/-- Homotopy under `A` is transitive. -/
@[trans] theorem trans {A : TopCat} {X Y : Under A} {f₀ f₁ f₂ : X ⟶ Y}
    (h₀ : HomotopicUnder f₀ f₁) (h₁ : HomotopicUnder f₁ f₂) : HomotopicUnder f₀ f₂ :=
  ContinuousMap.HomotopicWith.trans h₀ h₁

end HomotopicUnder

/-- Definition 6.5.2 (2): a homotopy equivalence under `A` is called a cofiber homotopy
equivalence. -/
class IsCofiberHomotopyEquivalence {A : TopCat} {X Y : Under A} (f : X ⟶ Y) : Prop where
  /-- A cofiber homotopy equivalence admits a two-sided homotopy inverse under `A`. -/
  exists_inverse :
    ∃ g : Y ⟶ X, HomotopicUnder (g ≫ f) (𝟙 Y) ∧ HomotopicUnder (f ≫ g) (𝟙 X)

/-- A cofiber homotopy equivalence is exactly a morphism in `Under A` that admits a two-sided
inverse up to homotopy under `A`. -/
theorem isCofiberHomotopyEquivalence_iff {A : TopCat} {X Y : Under A} {f : X ⟶ Y} :
    IsCofiberHomotopyEquivalence f ↔
      ∃ g : Y ⟶ X, HomotopicUnder (g ≫ f) (𝟙 Y) ∧ HomotopicUnder (f ≫ g) (𝟙 X) :=
  ⟨fun h ↦ h.exists_inverse, fun h ↦ ⟨h⟩⟩
