import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Equiv

open CategoryTheory
open TopCat
open unitInterval
open scoped ContinuousMap

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyWith` is the canonical owner for
-- homotopies through maps satisfying a predicate, and `Over B` is the canonical category of
-- spaces over a fixed base. Local precedent: `Definition_6_5_2.lean`.

universe u

/-- The predicate saying that a continuous map `X.left ⟶ Y.left` is a map over `B`. -/
def overMapCondition {B : TopCat.{u}} (X Y : Over B) : C(X.left, Y.left) → Prop :=
  fun f ↦ ofHom f ≫ Y.hom = X.hom

/-- Definition 7.5.2 (1): for morphisms `f₀ f₁ : X ⟶ Y` in `Over B`, a homotopy over `B` is a
homotopy through maps over `B`. -/
abbrev OverHomotopy {B : TopCat.{u}} {X Y : Over B} (f₀ f₁ : X ⟶ Y) : Type _ :=
  ContinuousMap.HomotopyWith f₀.left.hom f₁.left.hom (overMapCondition X Y)

namespace OverHomotopy

/-- Every intermediate stage of a homotopy over `B` is again a map over `B`. -/
theorem w {B : TopCat.{u}} {X Y : Over B} {f₀ f₁ : X ⟶ Y} (H : OverHomotopy f₀ f₁) (t : I) :
    ofHom (H.toHomotopy.curry t) ≫ Y.hom = X.hom :=
  H.prop t

end OverHomotopy

/-- Two morphisms in `Over B` are homotopic over `B` if they are connected by a homotopy through
maps over `B`. -/
abbrev HomotopicOver {B : TopCat.{u}} {X Y : Over B} (f₀ f₁ : X ⟶ Y) : Prop :=
  ContinuousMap.HomotopicWith f₀.left.hom f₁.left.hom (overMapCondition X Y)

namespace HomotopicOver

/-- Every morphism in `Over B` is homotopic over `B` to itself. -/
theorem refl {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) : HomotopicOver f f :=
  ContinuousMap.HomotopicWith.refl f.left.hom <| by
    simpa [overMapCondition] using Over.w f

/-- Homotopy over `B` is symmetric. -/
@[symm] theorem symm {B : TopCat.{u}} {X Y : Over B} {f₀ f₁ : X ⟶ Y}
    (h : HomotopicOver f₀ f₁) : HomotopicOver f₁ f₀ :=
  ContinuousMap.HomotopicWith.symm h

/-- Homotopy over `B` is transitive. -/
@[trans] theorem trans {B : TopCat.{u}} {X Y : Over B} {f₀ f₁ f₂ : X ⟶ Y}
    (h₀ : HomotopicOver f₀ f₁) (h₁ : HomotopicOver f₁ f₂) : HomotopicOver f₀ f₂ :=
  ContinuousMap.HomotopicWith.trans h₀ h₁

end HomotopicOver

/-- Definition 7.5.2 (2): a homotopy equivalence over `B` is called a fiber homotopy
equivalence. -/
class IsFiberHomotopyEquivalence {B : TopCat.{u}} {X Y : Over B} (f : X ⟶ Y) : Prop where
  /-- A fiber homotopy equivalence admits a two-sided homotopy inverse over `B`. -/
  exists_inverse :
    ∃ g : Y ⟶ X, HomotopicOver (g ≫ f) (𝟙 Y) ∧ HomotopicOver (f ≫ g) (𝟙 X)

/-- A fiber homotopy equivalence is exactly a morphism in `Over B` that admits a two-sided
inverse up to homotopy over `B`. -/
theorem isFiberHomotopyEquivalence_iff {B : TopCat.{u}} {X Y : Over B} {f : X ⟶ Y} :
    IsFiberHomotopyEquivalence f ↔
      ∃ g : Y ⟶ X, HomotopicOver (g ≫ f) (𝟙 Y) ∧ HomotopicOver (f ≫ g) (𝟙 X) :=
  ⟨fun h ↦ h.exists_inverse, fun h ↦ ⟨h⟩⟩
