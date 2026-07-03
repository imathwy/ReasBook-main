import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_3_1 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]
variable (F G : C ⥤ D)

/- Definition 2.3.1: a natural transformation from `F` to `G` is the canonical mathlib structure
`CategoryTheory.NatTrans F G`, written `F ⟶ G`, consisting of component morphisms
`α.app A : F.obj A ⟶ G.obj A` for each object `A`, subject to the naturality condition for
every morphism `f : A ⟶ B`. -/
#check (F ⟶ G)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/- A natural transformation has a component morphism at each object of the source category. -/
recall NatTrans.app (α : F ⟶ G) (A : C) :
    F.obj A ⟶ G.obj A

/- The components of a natural transformation commute with the functorial action on every
morphism. -/
recall NatTrans.naturality (α : F ⟶ G) {A B : C} (f : A ⟶ B) :
    F.map f ≫ α.app B = α.app A ≫ G.map f

/-! ### Example_2_3_2 (from Chap02) -/
universe u

open CategoryTheory

/- Example 2.3.2: the inclusion of a set `S` into the underlying set of its free abelian group
is the unit natural transformation of the free-forgetful adjunction, hence is natural in `S`. -/
#check (AddCommGrpCat.adj).unit

/- The naturality of this inclusion is the standard naturality of the unit of an adjunction. -/
#check (AddCommGrpCat.adj).unit_naturality

/-! ### Definition_2_3_3 (from Chap02) -/
/- Definition 2.3.3: the free abelian group functor is left adjoint to the forgetful functor
from abelian groups to sets, meaning that morphisms from the free abelian group on a set `S`
to an abelian group `A` are naturally identified with functions from `S` to the underlying set
of `A`. -/
#check AddCommGrpCat.adj

/-! ### Definition_2_3_4 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/- Definition 2.3.4: categories `C` and `D` are equivalent via the canonical mathlib notion
`C ≌ D`, which packages a forward functor, an inverse functor, and natural isomorphisms
identifying each composite with the corresponding identity functor. -/
#check (C ≌ D)

/- An equivalence of categories has a forward functor from `C` to `D`. -/
recall CategoryTheory.Equivalence.functor {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : C ⥤ D

/- An equivalence of categories has an inverse functor from `D` to `C`. -/
recall CategoryTheory.Equivalence.inverse {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : D ⥤ C

/- The unit of an equivalence is a natural isomorphism from the identity on `C` to the composite
of the forward and inverse functors. -/
recall CategoryTheory.Equivalence.unitIso {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : 𝟭 C ≅ e.functor ⋙ e.inverse

/- The counit of an equivalence is a natural isomorphism from the composite of the inverse and
forward functors to the identity on `D`. -/
recall CategoryTheory.Equivalence.counitIso {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (e : C ≌ D) : e.inverse ⋙ e.functor ≅ 𝟭 D
