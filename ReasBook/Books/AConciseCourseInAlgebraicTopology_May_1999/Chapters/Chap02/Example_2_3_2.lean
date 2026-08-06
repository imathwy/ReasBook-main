import Mathlib.Algebra.Category.Grp.Adjunctions

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 2.3.2: the inclusion of a set `S` into the underlying set of its free abelian group
is the unit natural transformation of the free-forgetful adjunction, hence is natural in `S`. -/
#check (AddCommGrpCat.adj).unit

/- The naturality of this inclusion is the standard naturality of the unit of an adjunction. -/
#check (AddCommGrpCat.adj).unit_naturality
