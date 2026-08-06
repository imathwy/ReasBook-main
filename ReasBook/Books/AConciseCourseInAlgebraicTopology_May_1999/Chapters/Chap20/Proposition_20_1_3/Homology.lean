import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u

/-- Singular homology in degree `n` with coefficients in the constant module `R`. -/
abbrev rSingularHomology (R : Type u) [CommRing R] (n : ℕ) (X : TopCat.{u}) : ModuleCat.{u} R :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (constantCoefficientModule R)).obj X

/-- Unfolding `rSingularHomology` recovers the constant-coefficient singular homology object
provided by `singularHomologyFunctor`. -/
theorem rSingularHomology_def (R : Type u) [CommRing R] (n : ℕ) (X : TopCat.{u}) :
    rSingularHomology R n X =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (constantCoefficientModule R)).obj X :=
  rfl

/-- The localization map from global top singular homology to the local top homology group at
`x`, induced by the quotient map to the cokernel modeling `H_n(M, M \ {x}; R)`. -/
def localTopHomologyMap (R : Type u) [CommRing R] (n : ℕ) (M : Type u) [TopologicalSpace M]
    (x : M) :
    rSingularHomology R n (TopCat.of.{u} M) ⟶ localTopHomologyGroup R n M x :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map
    (cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (constantCoefficientModule R)).map (puncturedPointInclusion x)))

/-- `localTopHomologyMap` is the homology map induced by the cokernel projection defining the
local top homology group. -/
theorem localTopHomologyMap_def (R : Type u) [CommRing R] (n : ℕ) (M : Type u)
    [TopologicalSpace M] (x : M) :
    localTopHomologyMap R n M x =
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map
        (cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (constantCoefficientModule R)).map (puncturedPointInclusion x))) :=
  rfl

/-- A class `z ∈ H_n(M; R)` is an `R`-fundamental class when its image in every local top
homology group can be identified with the unit `1 : R`. -/
def IsRFundamentalClass (R : Type u) [CommRing R] (n : ℕ) (M : Type u) [TopologicalSpace M]
    (z : rSingularHomology R n (TopCat.of.{u} M)) : Prop :=
  ∀ x : M, ∃ e : localTopHomologyGroup R n M x ≅ constantCoefficientModule R,
    e.hom ((localTopHomologyMap R n M x) z) = 1

/-- Unfolding `IsRFundamentalClass` says that every local image of `z` becomes `1 : R` under some
pointwise identification of the local top homology group with `R`. -/
theorem isRFundamentalClass_iff (R : Type u) [CommRing R] (n : ℕ) (M : Type u)
    [TopologicalSpace M] (z : rSingularHomology R n (TopCat.of.{u} M)) :
    IsRFundamentalClass R n M z ↔
      ∀ x : M, ∃ e : localTopHomologyGroup R n M x ≅ constantCoefficientModule R,
        e.hom ((localTopHomologyMap R n M x) z) = 1 :=
  Iff.rfl

section

variable {R : Type u} [CommRing R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The local trivializations determined by `z` are those whose chosen identifications send the
local image of `z` to `1 : R` at every point of their domain. -/
def inducedROrientationAtlas (z : rSingularHomology R n (TopCat.of.{u} M)) :
    Set (LocalTopHomologyTrivialization R n M) :=
  { U | ∀ x : U.domain, (U.identify x).hom ((localTopHomologyMap R n M x.1) z) = 1 }

/-- Membership in `inducedROrientationAtlas z` means that the chosen local identifications of the
trivialization send the local image of `z` to `1 : R` everywhere on the domain. -/
@[simp] theorem mem_inducedROrientationAtlas_iff {z : rSingularHomology R n (TopCat.of.{u} M)}
    {U : LocalTopHomologyTrivialization R n M} :
    U ∈ inducedROrientationAtlas z ↔
      ∀ x : U.domain, (U.identify x).hom ((localTopHomologyMap R n M x.1) z) = 1 :=
  Iff.rfl

/-- Helper for Proposition 20.1.3: an element of `constantCoefficientModule R` is the scalar
multiple of `1` given by its underlying coefficient. -/
theorem constantCoefficientModule_eq_down_smul_one
    (y : constantCoefficientModule R) :
    y = y.down • (1 : constantCoefficientModule R) := by
  cases y
  exact congrArg ULift.up (mul_one _).symm

/-- Helper for Proposition 20.1.3: an isomorphism to `constantCoefficientModule R` is determined
by any element that it sends to `1`. -/
theorem isoToConstantCoefficient_eq_of_hom_eq_one
    {A : ModuleCat.{u} R} (e₁ e₂ : A ≅ constantCoefficientModule R) {a : A}
    (h₁ : e₁.hom a = 1) (h₂ : e₂.hom a = 1) :
    e₁ = e₂ := by
  sorry

/-- An `R`-fundamental class is compatible with an `R`-orientation when every point lies in some
atlas chart whose chosen identifications send the local image of the class to `1 : R` everywhere
on that chart. -/
def IsRFundamentalClassFor (o : ROrientedManifold R I n M)
    (z : rSingularHomology R n (TopCat.of.{u} M)) : Prop :=
  ∀ x : M, ∃ U : LocalTopHomologyTrivialization R n M,
    U ∈ o.atlas ∧ x ∈ U.domain ∧ U ∈ inducedROrientationAtlas z

/-- Compatibility with a chosen `R`-orientation implies the usual pointwise local characterization
of an `R`-fundamental class. -/
theorem IsRFundamentalClassFor.isRFundamentalClass {o : ROrientedManifold R I n M}
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClassFor o z) :
    IsRFundamentalClass R n M z := by
  sorry

/-- A global `R`-orientation is compatible with `z` when one of its representing oriented atlases
is compatible with `z`. This removes dependence on a specific atlas presentation. -/
def IsRFundamentalClassForGlobalOrientation
    (o : ROrientedManifold.GlobalOrientation R I n M)
    (z : rSingularHomology R n (TopCat.of.{u} M)) : Prop :=
  ∃ o' : ROrientedManifold R I n M,
    ROrientedManifold.toGlobalOrientation o' = o ∧ IsRFundamentalClassFor o' z

/-- Unfolding class-level compatibility says exactly that some representative oriented atlas of
the global orientation class is compatible with `z`. -/
theorem isRFundamentalClassForGlobalOrientation_iff
    (o : ROrientedManifold.GlobalOrientation R I n M)
    (z : rSingularHomology R n (TopCat.of.{u} M)) :
    IsRFundamentalClassForGlobalOrientation o z ↔
      ∃ o' : ROrientedManifold R I n M,
        ROrientedManifold.toGlobalOrientation o' = o ∧ IsRFundamentalClassFor o' z :=
  Iff.rfl

/-- Atlas-level compatibility produces compatibility with the induced global orientation class. -/
theorem IsRFundamentalClassFor.toGlobalOrientation
    {o : ROrientedManifold R I n M} {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassFor o z) :
    IsRFundamentalClassForGlobalOrientation (ROrientedManifold.toGlobalOrientation o) z :=
  ⟨o, rfl, hz⟩

/-- Class-level compatibility still implies the intrinsic `R`-fundamental-class condition. -/
theorem IsRFundamentalClassForGlobalOrientation.isRFundamentalClass
    {o : ROrientedManifold.GlobalOrientation R I n M}
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassForGlobalOrientation o z) :
    IsRFundamentalClass R n M z := by
  sorry

end
