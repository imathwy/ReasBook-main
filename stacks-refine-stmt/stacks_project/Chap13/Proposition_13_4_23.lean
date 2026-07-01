import Mathlib.CategoryTheory.Triangulated.Triangulated

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

set_option checkBinderAnnotations false in
section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/- Domain-style sampling for Proposition 13.4.23:
- primary domain: triangulated categories, commutative squares, distinguished triangles, and the
  octahedral formalism.
- inspected declarations: `CommSq`, `Triangle`, `TriangleMorphism`,
  `Pretriangulated.completeDistinguishedTriangleMorphism`, and `Triangulated.Octahedron`.
- best owner abstraction: the source-facing `3-by-3` extension should sit over the canonical input
  square `CommSq f u v f'`, while its row/column data should be read as `Triangle`s and the two
  comparison maps between the first two rows and the first two columns should be exposed through
  the canonical owner `TriangleMorphism`.
- primitive-vs-derived split:
  primitive data: the extra objects and arrows of the `3-by-3` diagram, the six
  distinguished-triangle witnesses, the four commutation rules needed to build the two comparison
  triangle morphisms, the three adjacent squares, and the lower-right anticommutativity;
  derived API: the six rows/columns as canonical `Triangle`s together with the two comparison
  `TriangleMorphism`s. -/

/- Source/core/bridge triage for Proposition 13.4.23:
- source-facing: `DistinguishedThreeByThreeExtension`, which records the textbook `3-by-3`
  diagram.
- core/canonical: `CommSq`, `Triangle`, `TriangleMorphism`, and `Octahedron`.
- bridge/view: the six row/column `Triangle` views together with the two comparison
  `TriangleMorphism`s assembled from the source-facing arrows and commutative squares. -/

/-- A `3-by-3` extension of a commutative square in a triangulated category.

The six distinguished triangles are the top, middle, and bottom rows together with the left,
middle, and right columns of the usual `3-by-3` diagram. The two comparison maps from the first
two rows and the first two columns are exposed below as canonical `TriangleMorphism`s, the
adjacent shift-compatible squares are part of the data, and the lower-right square is required to
anticommute. -/
structure DistinguishedThreeByThreeExtension
    {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') where
  Z : C
  Z' : C
  X'' : C
  Y'' : C
  Z'' : C
  top2 : Y ⟶ Z
  top3 : Z ⟶ X⟦(1 : ℤ)⟧
  middleRow2 : Y' ⟶ Z'
  middleRow3 : Z' ⟶ X'⟦(1 : ℤ)⟧
  left2 : X' ⟶ X''
  left3 : X'' ⟶ X⟦(1 : ℤ)⟧
  middleCol2 : Y' ⟶ Y''
  middleCol3 : Y'' ⟶ Y⟦(1 : ℤ)⟧
  right1 : Z ⟶ Z'
  right2 : Z' ⟶ Z''
  right3 : Z'' ⟶ Z⟦(1 : ℤ)⟧
  bottom1 : X'' ⟶ Y''
  bottom2 : Y'' ⟶ Z''
  bottom3 : Z'' ⟶ X''⟦(1 : ℤ)⟧
  topRow_distinguished : Triangle.mk f top2 top3 ∈ distTriang C
  middleRow_distinguished : Triangle.mk f' middleRow2 middleRow3 ∈ distTriang C
  leftColumn_distinguished : Triangle.mk u left2 left3 ∈ distTriang C
  middleColumn_distinguished : Triangle.mk v middleCol2 middleCol3 ∈ distTriang C
  topToMiddle_comm₂ : top2 ≫ right1 = v ≫ middleRow2
  topToMiddle_comm₃ : top3 ≫ u⟦(1 : ℤ)⟧' = right1 ≫ middleRow3
  leftToMiddle_comm₂ : left2 ≫ bottom1 = f' ≫ middleCol2
  leftToMiddle_comm₃ : left3 ≫ f⟦(1 : ℤ)⟧' = bottom1 ≫ middleCol3
  bottomRow_distinguished :
    Triangle.mk bottom1 bottom2 bottom3 ∈ distTriang C
  rightColumn_distinguished :
    Triangle.mk right1 right2 right3 ∈ distTriang C
  middle : CommSq middleRow2 middleCol2 right2 bottom2
  middleRight : CommSq middleRow3 right2 (left2⟦(1 : ℤ)⟧') bottom3
  lowerMiddle : CommSq bottom2 middleCol3 right3 (top2⟦(1 : ℤ)⟧')
  lowerRight_anticomm :
    bottom3 ≫ left3⟦(1 : ℤ)⟧' = -(right3 ≫ top3⟦(1 : ℤ)⟧')

namespace DistinguishedThreeByThreeExtension

variable {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
  {sq : CommSq f u v f'}

/-- The top distinguished triangle in a `3-by-3` extension. -/
abbrev topRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk f E.top2 E.top3

/-- The middle distinguished triangle in a `3-by-3` extension. -/
abbrev middleRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk f' E.middleRow2 E.middleRow3

/-- The left distinguished triangle in a `3-by-3` extension. -/
abbrev leftColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk u E.left2 E.left3

/-- The middle distinguished triangle in the column direction. -/
abbrev middleColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk v E.middleCol2 E.middleCol3

/-- The bottom distinguished triangle in a `3-by-3` extension. -/
abbrev bottomRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk E.bottom1 E.bottom2 E.bottom3

/-- The right distinguished triangle in a `3-by-3` extension. -/
abbrev rightColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk E.right1 E.right2 E.right3

/-- The comparison morphism from the top row to the middle row. -/
abbrev topRowToMiddleRow (E : DistinguishedThreeByThreeExtension sq) :
    E.topRow ⟶ E.middleRow :=
  Triangle.homMk _ _ u v E.right1 sq.w E.topToMiddle_comm₂ E.topToMiddle_comm₃

/-- The comparison morphism from the left column to the middle column. -/
abbrev leftColumnToMiddleColumn (E : DistinguishedThreeByThreeExtension sq) :
    E.leftColumn ⟶ E.middleColumn :=
  Triangle.homMk _ _ f f' E.bottom1 sq.w.symm E.leftToMiddle_comm₂ E.leftToMiddle_comm₃

@[simp]
theorem topRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.topRow ∈ distTriang C :=
  E.topRow_distinguished

@[simp]
theorem middleRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.middleRow ∈ distTriang C :=
  E.middleRow_distinguished

@[simp]
theorem leftColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.leftColumn ∈ distTriang C :=
  E.leftColumn_distinguished

@[simp]
theorem middleColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.middleColumn ∈ distTriang C :=
  E.middleColumn_distinguished

@[simp]
theorem bottomRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.bottomRow ∈ distTriang C :=
  E.bottomRow_distinguished

@[simp]
theorem rightColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.rightColumn ∈ distTriang C :=
  E.rightColumn_distinguished

end DistinguishedThreeByThreeExtension

-- Proof sketch: complete the top row and the left column to distinguished triangles, upgrade the
-- original square to morphisms of triangles, and then apply the octahedron axiom twice to obtain
-- the right column and the bottom row; the lower-right sign comes from the shifted triangle in the
-- final octahedral step.
/-- Proposition 13.4.23: any commutative square in a triangulated category extends to a
`3-by-3` diagram whose top, middle, and bottom rows and whose left, middle, and right columns are
distinguished triangles, with the adjacent shift-compatible squares and an anticommutative
lower-right square. -/
theorem commSq_has_distinguished_three_by_three_extension
    [IsTriangulated C] {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') :
    Nonempty (DistinguishedThreeByThreeExtension sq) := sorry

/-- Proposition 13.4.23 in equation form: a commuting square `f ≫ v = u ≫ f'` admits a
distinguished `3-by-3` extension. -/
theorem commutative_square_has_distinguished_three_by_three_extension
    [IsTriangulated C] {X Y X' Y' : C} (f : X ⟶ Y) (u : X ⟶ X') (v : Y ⟶ Y')
    (f' : X' ⟶ Y') (comm : f ≫ v = u ≫ f') :
    Nonempty (DistinguishedThreeByThreeExtension (CommSq.mk comm)) := by
  simpa using commSq_has_distinguished_three_by_three_extension (CommSq.mk comm)

end

end CategoryTheory
