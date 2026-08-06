import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1

open AlgebraicTopology CategoryTheory
open scoped CapProduct singularCohomology

noncomputable section

universe u

-- Local Chapter 18/20 precedent already exposes the cup product, cap product, the comparison
-- `singularCohomologyClassToRSingularCohomology`, and the induced pullback/pushforward maps on
-- their owner files. This proposition reuses those owners directly.

section

variable (R : Type u) [CommRing R]
variable (M : ModuleCat.{u} R)
variable {X Y : TopCat.{u}}

/-- The target homology object of the iterated cap product agrees with the target homology object
of capping by a cup product. -/
private theorem singularCapProduct_cup_target_eq
    (X : TopCat.{u}) (p q r : ℕ) :
    singularHomologyWithCoefficients R X M ((r - q) - p) =
      singularHomologyWithCoefficients R X M (r - (p + q)) := sorry

/-- The underlying carrier types of the two target homology objects in the cup-cap compatibility
comparison agree. -/
private theorem singularCapProduct_cup_target_type_eq
    (X : TopCat.{u}) (p q r : ℕ) :
    (singularHomologyWithCoefficients R X M ((r - q) - p) : Type u) =
      singularHomologyWithCoefficients R X M (r - (p + q)) := sorry

/-- Proposition 20.2.3 (1). Cap product is natural with respect to maps of spaces: pushing
forward the cap product of `f^* α` with `z` agrees with capping `f_* z` with `α`. -/
theorem singularCapProduct_naturality
    (f : X ⟶ Y) (p q : ℕ) (α : rSingularCohomology R Y p)
    (z : singularHomologyWithCoefficients R X M q) :
    singularHomologyWithCoefficients.map R M f (q - p)
        (rSingularCohomology.map R f p α ∩ z) =
      α ∩ singularHomologyWithCoefficients.map R M f q z := sorry

/-- Proposition 20.2.3 (2). Cap product is compatible with cup products: after transporting the
Chapter 18 cup product to `rSingularCohomology`, capping with `α ⌣ β` agrees with first capping
with `β` and then capping with `α`, up to the standard grading cast
`r - (p + q) = (r - q) - p`. -/
theorem singularCapProduct_cup_compatibility
    (X : TopCat.{u}) (p q r : ℕ) (α : singularCohomologyClasses R X p)
    (β : singularCohomologyClasses R X q)
    (z : singularHomologyWithCoefficients R X M r) :
    singularCohomologyClassToRSingularCohomology R X (p + q)
        (α ⌣ β) ∩ z =
      cast
        (singularCapProduct_cup_target_type_eq R M X p q r)
        (singularCohomologyClassToRSingularCohomology R X p α ∩
          (singularCohomologyClassToRSingularCohomology R X q β ∩ z)) := sorry

end
