import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/- Source/core/bridge triage:
- `source-facing`: a diagram `X ⟶ W` over `S ⟶ Sᵢ`;
- `core/canonical`: an object of the under category
  `Under (Over.mk (f ≫ π) : Over Si)` whose ambient object is `Over.mk toSi`;
- `bridge/view`: the companion accessors below recovering `W`, `X ⟶ W`, `W ⟶ Sᵢ`, and the
  commutative square as a `CommSq`.

The source item varies the upper-right corner `W`, so unlike a pure square recall it should not be
just `CommSq`. The canonical owner is the slice-category object encoding a factorization of
`f ≫ π : X ⟶ Sᵢ`. The abbreviation below keeps the source-facing name while deleting the bespoke
wrapper structure.
-/

/-- 32.22.2.1: a diagram `X ⟶ W` over `S ⟶ Sᵢ`, formalized by the canonical under-category owner
for factorizations of `f ≫ π : X ⟶ Sᵢ`. -/
abbrev FiniteTypeApproximationDiagram {X S Si : Scheme.{u}}
    (f : X ⟶ S) (π : S ⟶ Si) :=
  Under (Over.mk (f ≫ π) : Over Si)

namespace FiniteTypeApproximationDiagram

variable {X S Si : Scheme.{u}} {f : X ⟶ S} {π : S ⟶ Si}

/-- Construct the canonical owner from source-facing scheme data and a commuting square. -/
abbrev mk (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    FiniteTypeApproximationDiagram f π :=
  Under.mk
    (show (Over.mk (f ≫ π) : Over Si) ⟶ Over.mk toSi from
      Over.homMk toW comm.w)

/-- The upper-right corner scheme `W`. -/
abbrev W (D : FiniteTypeApproximationDiagram f π) : Scheme.{u} :=
  D.right.left

/-- The top horizontal morphism `X ⟶ W`. -/
abbrev toW (D : FiniteTypeApproximationDiagram f π) : X ⟶ D.W :=
  D.hom.left

/-- The right vertical morphism `W ⟶ Sᵢ`. -/
abbrev toSi (D : FiniteTypeApproximationDiagram f π) : D.W ⟶ Si :=
  D.right.hom

/-- The defining square commutes. -/
abbrev comm (D : FiniteTypeApproximationDiagram f π) :
    CommSq D.toW f D.toSi π :=
  CommSq.mk D.hom.w

@[simp] theorem mk_W (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).W = W :=
  rfl

@[simp] theorem mk_toW (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).toW = toW :=
  rfl

@[simp] theorem mk_toSi (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).toSi = toSi :=
  rfl

@[simp] theorem mk_comm (W : Scheme.{u}) (toW : X ⟶ W) (toSi : W ⟶ Si)
    (comm : CommSq toW f toSi π) :
    (mk W toW toSi comm).comm = comm := by
  cases comm
  rfl

@[simp] theorem w (D : FiniteTypeApproximationDiagram f π) :
    D.toW ≫ D.toSi = f ≫ π :=
  D.comm.w

end FiniteTypeApproximationDiagram

end AlgebraicGeometry
