import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_1_1 (from Chap02) -/
universe u v

open CategoryTheory

/- Definition 2.1.1: a category consists of objects, morphism sets `C(A, B)`, identity
morphisms `id_A`, and an associative composition law satisfying the left and right unit laws. -/
recall Category (C : Type u) : Type (max u (v + 1))

/-! ### Definition_2_1_2 (from Chap02) -/
universe u

open CategoryTheory

/- Definition 2.1.2: a category is small when its objects form a set; in mathlib this is
the canonical abbreviation `SmallCategory`, expressing that the objects and morphisms live in
the same universe level. -/
recall SmallCategory (C : Type u) : Type (u + 1)

/-! ### Example_2_1_3 (from Chap02) -/
universe u

open CategoryTheory

/- Example 2.1.3: standard examples of categories in mathlib include the category of types with
functions, the category of topological spaces with continuous maps, the category of groups with
homomorphisms, and the category of abelian groups with homomorphisms. For `Type u`, the canonical
owner is the large-category instance `CategoryTheory.types`. -/
#check (inferInstance : LargeCategory (Type u))

/- The bundled type `TopCat` carries the standard category of topological spaces and continuous
maps. -/
#check (inferInstance : Category TopCat)

/- The bundled type `GrpCat` carries the standard category of groups and group homomorphisms. -/
#check (inferInstance : Category GrpCat)

/- The bundled type `AddCommGrpCat` carries the standard category of abelian groups and
homomorphisms. -/
#check (inferInstance : Category AddCommGrpCat)
