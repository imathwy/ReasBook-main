import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory Limits

/- Definition 2.6.7: a category is cocomplete when it has all colimits, expressed by the
canonical abbreviation `HasColimits`. -/
recall HasColimits (C : Type u) [Category.{v} C] : Prop

/- Completeness is the dual notion, expressed by the canonical abbreviation `HasLimits`. -/
recall HasLimits (C : Type u) [Category.{v} C] : Prop
