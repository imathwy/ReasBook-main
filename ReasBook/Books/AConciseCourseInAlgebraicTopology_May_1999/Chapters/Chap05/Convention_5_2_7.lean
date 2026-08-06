import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.CompactlyGenerated

open CategoryTheory

universe u w

namespace CompactlyGenerated

/-- The one-point compactly generated space. -/
abbrev point : CompactlyGenerated.{u, w} where
  toTop := TopCat.of PUnit.{w + 1}

/-- The constant morphism from the one-point compactly generated space. -/
abbrev pointHom {X : CompactlyGenerated.{u, w}} (x : X) : point ⟶ X :=
  ConcreteCategory.ofHom (ContinuousMap.const PUnit.{w + 1} x)

end CompactlyGenerated

/-- Convention 5.2.7: `CompactlyGenerated.{u, w}` is the category `U` of compactly generated
spaces and continuous maps, and `PointedCompactlyGenerated.{u, w}` is the category `T` of based
compactly generated spaces and based maps. It is canonically the under category of the one-point
compactly generated space. -/
abbrev PointedCompactlyGenerated :=
  Under (CompactlyGenerated.point.{u, w})

namespace PointedCompactlyGenerated

/-- Construct a based compactly generated space from a compactly generated space and a point. -/
abbrev of (X : CompactlyGenerated.{u, w}) (x : X) : PointedCompactlyGenerated :=
  Under.mk (CompactlyGenerated.pointHom x)

/-- The underlying compactly generated space. -/
abbrev toCompactlyGenerated (X : PointedCompactlyGenerated) :=
  X.right

/-- The distinguished basepoint. -/
abbrev point (X : PointedCompactlyGenerated) :=
  X.hom PUnit.unit

@[simp] theorem toCompactlyGenerated_of (X : CompactlyGenerated.{u, w}) (x : X) :
    (of X x).toCompactlyGenerated = X :=
  rfl

@[simp] theorem point_of (X : CompactlyGenerated.{u, w}) (x : X) :
    (of X x).point = x := by
  change (ContinuousMap.const PUnit.{w + 1} x) PUnit.unit = x
  rfl

/-- A based compactly generated space, viewed as a based topological space. -/
noncomputable abbrev toBasedSpace
    (X : PointedCompactlyGenerated.{u, w}) : Under (⊤_ TopCat.{w}) :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} X.point))

namespace Hom

/-- The underlying morphism of compactly generated spaces. -/
abbrev hom {X Y : PointedCompactlyGenerated} (f : X ⟶ Y) :=
  f.right

@[simp] theorem id_hom (X : PointedCompactlyGenerated) :
    hom (𝟙 X : X ⟶ X) = 𝟙 X.toCompactlyGenerated :=
  rfl

@[simp] theorem comp_hom {X Y Z : PointedCompactlyGenerated}
    (f : X ⟶ Y) (g : Y ⟶ Z) : hom (f ≫ g) = hom f ≫ hom g :=
  rfl

/-- A morphism of based compactly generated spaces preserves the distinguished basepoints. -/
@[simp] theorem map_point {X Y : PointedCompactlyGenerated} (f : X ⟶ Y) :
    hom f X.point = Y.point := by
  change (X.hom ≫ f.right) PUnit.unit = Y.hom PUnit.unit
  exact congrArg (fun h ↦ h PUnit.unit) (congrArg ConcreteCategory.hom (Under.w f))

end Hom

/-- A based map of pointed compactly generated spaces induces a based map of topological spaces. -/
theorem toBasedSpaceMap_w {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    (toBasedSpace X).hom ≫ (Hom.hom f).hom = (toBasedSpace Y).hom := by
  ext x
  change (Hom.hom f)
      ((TopCat.terminalIsoPUnit.hom ≫
          TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} X.point)) x) =
    (TopCat.terminalIsoPUnit.hom ≫
        TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} Y.point)) x
  simpa only [ContinuousMap.const_apply] using
    (show ConcreteCategory.hom (Hom.hom f) X.point = Y.point from Hom.map_point f)

/-- The based topological map induced by a based map of compactly generated spaces. -/
noncomputable abbrev toBasedSpaceMap
    {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    toBasedSpace X ⟶ toBasedSpace Y :=
  Under.homMk (Hom.hom f).hom (toBasedSpaceMap_w f)

end PointedCompactlyGenerated
