import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Corollary_2_8_2.WedgeOfCircles

/-- Corollary 2.8.2: the canonical map from the free group on one generator for each circle to the
fundamental group of the wedge of those circles is bijective. -/
-- Proof sketch: apply Proposition 2.8.1 to the constant family of based circles. Theorem 1.5.11
-- identifies the fundamental group of each summand with the infinite cyclic group, equivalently
-- with the free group on one generator, so the free product comparison becomes the free-group
-- comparison defined above.
theorem wedge_of_circles_fundamental_group_comparison_bijective (ι : Type) :
    Function.Bijective (wedge_of_circles_fundamental_group_comparison ι) := by
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso
    (GrpCat.ofHom (wedge_of_circles_fundamental_group_comparison ι))

/-- Corollary 2.8.2 companion: the canonical map from the free group on `ι` to the fundamental
group of the wedge of `ι` circles as a multiplicative equivalence. -/
noncomputable def wedge_of_circles_fundamental_group_mulEquiv (ι : Type) :
    FreeGroup ι ≃* FundamentalGroup (wedge_of_circles ι).right
      (underTopBasepoint (wedge_of_circles ι)) :=
  CategoryTheory.Iso.groupIsoToMulEquiv
    (CategoryTheory.asIso (GrpCat.ofHom (wedge_of_circles_fundamental_group_comparison ι)))

/-- The underlying homomorphism of `wedge_of_circles_fundamental_group_mulEquiv` is the canonical
comparison map. -/
@[simp] theorem wedge_of_circles_fundamental_group_mulEquiv_toMonoidHom (ι : Type) :
    (wedge_of_circles_fundamental_group_mulEquiv ι).toMonoidHom =
      wedge_of_circles_fundamental_group_comparison ι :=
  rfl

/-- The multiplicative equivalence `wedge_of_circles_fundamental_group_mulEquiv` evaluates to the
canonical comparison map. -/
@[simp] theorem wedge_of_circles_fundamental_group_mulEquiv_apply
    (ι : Type) (x : FreeGroup ι) :
    wedge_of_circles_fundamental_group_mulEquiv ι x =
      wedge_of_circles_fundamental_group_comparison ι x :=
  rfl
