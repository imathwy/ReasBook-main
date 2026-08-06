import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Path
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Calculation_13_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Remark_13_5_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Problem_20_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_1_2

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open Simplicial
open scoped Manifold TopCat Topology

noncomputable section

-- Chapter 13 already fixes `integralSingularHomology`, and Chapter 20 records orientability by
-- `ROrientedManifold`.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [CompactSpace M]
  [ConnectedSpace M] [Fact (Module.finrank ℝ E = 3)]

private abbrev problem21_6_4SingularSSetSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X) _⦋n⦌

local notation "singularSSetSimplex" => problem21_6_4SingularSSetSimplex

private noncomputable def problem21_6_4SingularChainDegreeIsoCoproduct
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).obj X).X n) ≅
      ∐ fun _ : singularSimplex n X ↦ constantCoefficientModule R :=
  (eqToIso rfl) ≪≫
    show (∐ fun _ : problem21_6_4SingularSSetSimplex X n ↦ constantCoefficientModule R) ≅
        ∐ fun _ : singularSimplex n X ↦ constantCoefficientModule R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv n X)
        (fun _ ↦ Iso.refl (constantCoefficientModule R))

local notation "singularChainDegreeIsoCoproduct" =>
  problem21_6_4SingularChainDegreeIsoCoproduct

/-- Helper for Problem 21.6.4: a path-connected space has a unique path component. -/
theorem pathConnected_uniqueZerothHomotopy
    (X : Type _) [TopologicalSpace X] [PathConnectedSpace X] :
    Nonempty (Unique (ZerothHomotopy X)) := by
  -- Convert path connectedness into the standard nonempty-plus-subsingleton description of `π₀`.
  rcases (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp inferInstance with
    ⟨hne, hsub⟩
  rcases hne with ⟨x⟩
  -- Then package the unique path component into the target `Unique` witness.
  exact ⟨{ default := x, uniq := fun y ↦ hsub.elim y x }⟩

/-- Helper for Problem 21.6.4: a connected closed orientable `3`-manifold is path connected. -/
theorem closedOrientableThreeManifold_pathConnectedSpace
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M)) :
    PathConnectedSpace M := by
  rcases h_orientable with ⟨o⟩
  -- Use the orientation witness to recover the manifold structure required by the standard local
  -- path connectedness bridge.
  let _ : ROrientedManifold ℤ I 3 M := o
  -- Charts modeled on Euclidean space make the manifold locally path connected.
  let _ : LocPathConnectedSpace H :=
    (ModelWithCorners.toHomeomorph I).isOpenEmbedding.locPathConnectedSpace
  let _ : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace H M
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- Helper for Problem 21.6.4: the `3`-sphere is path connected. -/
theorem sphereThree_pathConnectedSpace :
    PathConnectedSpace (TopCat.sphere.{0} 3) := by
  -- Reuse the earlier sphere connectivity theorem at the concrete degree `3`.
  exact sphere_pathConnectedSpace_of_two_le (n := 3) (by decide)

/-- Helper for Problem 21.6.4: the `3`-sphere is connected. -/
theorem sphereThree_connectedSpace :
    ConnectedSpace (TopCat.sphere.{0} 3) := by
  -- Path connectedness is stronger than connectedness, so the sphere inherits the latter.
  let _ : PathConnectedSpace (TopCat.sphere.{0} 3) := sphereThree_pathConnectedSpace
  infer_instance

/-- Helper for Problem 21.6.4: the `3`-sphere is simply connected. -/
theorem sphereThree_simplyConnectedSpace :
    SimplyConnectedSpace (TopCat.sphere.{0} 3) := by
  -- Reuse the standard simply-connectedness of spheres in dimensions at least `2`.
  simpa using sphere_simplyConnectedSpace_of_two_le (n := 3) (by decide)

/-- Helper for Problem 21.6.4: the `3`-sphere has a unique path component. -/
theorem sphereThree_uniqueZerothHomotopy :
    Nonempty (Unique (ZerothHomotopy (TopCat.sphere.{0} 3))) := by
  -- Reduce uniqueness of path components to the already established path connectedness of `S^3`.
  let _ : PathConnectedSpace (TopCat.sphere.{0} 3) := sphereThree_pathConnectedSpace
  exact pathConnected_uniqueZerothHomotopy (TopCat.sphere.{0} 3)

/-- Helper for Problem 21.6.4: a connected closed orientable `3`-manifold has a unique path
component. -/
theorem closedOrientableThreeManifold_uniqueZerothHomotopy
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M)) :
    Nonempty (Unique (ZerothHomotopy M)) := by
  -- First recover path connectedness from the manifold structure.
  let _ : PathConnectedSpace M :=
    closedOrientableThreeManifold_pathConnectedSpace (I := I) (M := M) h_orientable
  -- Then apply the generic `π₀` uniqueness bridge.
  exact pathConnected_uniqueZerothHomotopy M

/-- Helper for Problem 21.6.4: orientability identifies the top integral homology of a connected
closed `3`-manifold with `ℤ`. -/
theorem closedOrientableThreeManifoldTopIntegralHomology
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M)) :
    Nonempty (integralSingularHomology 3 (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  rcases h_orientable with ⟨o⟩
  -- Local instance justification (manifold structure): the Chapter 13 top-homology theorem is
  -- formulated with a typeclass-oriented manifold witness, and `o` is the canonical source of
  -- that instance in this proof.
  let _ : ROrientedManifold ℤ I 3 M := o
  -- Apply the connected closed-manifold top-homology characterization in dimension `3`.
  exact
    (orientability_iff_topIntegralHomologyIso_of_connectedClosedManifold
      (I := I) (M := M) (n := 3)).1 ⟨o⟩

/-- Helper for Problem 21.6.4: the Chapter 20 constant coefficient owner `constantCoefficientModule
ℤ` is canonically the ordinary unit `ℤ`-module. -/
private noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- Helper for Problem 21.6.4: ordinary integral singular homology agrees with Chapter 20's
constant-coefficient owner `rSingularHomology ℤ` in every degree. -/
theorem integralSingularHomologyIsoRSingularHomology
    (X : TopCat) (k : ℕ) :
    Nonempty (integralSingularHomology k X ≅ rSingularHomology ℤ k X) := by
  -- Compare both owners by changing the coefficient module from `ULift ℤ` to the standard `ℤ`.
  refine ⟨?_⟩
  simpa [integralSingularHomology, rSingularHomology] using
    (((singularHomologyFunctor (ModuleCat ℤ) k).mapIso
      constantCoefficientModuleIsoInt).app X).symm

/-- Helper for Problem 21.6.4: the zeroth constant-coefficient singular homology of a point is
the coefficient module itself. -/
theorem pointRSingularHomologyZeroIsoConstantCoefficient
    (R : Type) [CommRing R] :
    Nonempty (rSingularHomology R 0 (TopCat.of Unit) ≅ constantCoefficientModule R) := by
  -- Compute `H₀` of the point by the totally disconnected-space calculation.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat R) (R := constantCoefficientModule R) (X := TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)

/-- Helper for Problem 21.6.4: a singular `0`-simplex is determined by its unique vertex, so
degree-zero simplices are canonically the points of `X`. -/
private noncomputable def standardZeroSimplexPoint : Δ^0 :=
  ⟨fun _ ↦ 1, by
    constructor
    · intro i
      norm_num
    · simp⟩

/-- Helper for Problem 21.6.4: the standard `0`-simplex `Δ^0` is a subsingleton. -/
private theorem standardZeroSimplex_subsingleton : Subsingleton (Δ^0) := by
  refine ⟨fun a b ↦ ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i
  have ha : a.1 0 = 1 := by
    simpa using a.2.2
  have hb : b.1 0 = 1 := by
    simpa using b.2.2
  exact ha.trans hb.symm

/-- Helper for Problem 21.6.4: a singular `0`-simplex is determined by its unique vertex, so
degree-zero simplices are canonically the points of `X`. -/
noncomputable def singularSimplexZeroEquiv
    (X : Type _) [TopologicalSpace X] :
    singularSimplex 0 X ≃ X where
  toFun σ := σ standardZeroSimplexPoint
  invFun x := ContinuousMap.const _ x
  left_inv := by
    intro σ
    -- A `0`-simplex is constant because the standard `0`-simplex is subsingleton.
    ext t
    exact congrArg σ (standardZeroSimplex_subsingleton.elim standardZeroSimplexPoint t)
  right_inv := by
    intro x
    rfl

/-- Helper for Problem 21.6.4: the inverse of `singularSimplexZeroEquiv` sends a point to the
constant singular `0`-simplex at that point. -/
@[simp] theorem singularSimplexZeroEquiv_symm_apply
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexZeroEquiv X).symm x = ContinuousMap.const _ x :=
  rfl

/-- Helper for Problem 21.6.4: the constant singular `0`-simplex at `x` maps to `x` under the
degree-zero simplex/point equivalence. -/
@[simp] theorem singularSimplexZeroEquiv_apply_const
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexZeroEquiv X (ContinuousMap.const _ x) = x :=
  rfl

/-- Helper for Problem 21.6.4: degree-zero singular chains are the coproduct of one copy of `R`
for each point of `X`. -/
noncomputable def singularChainDegreeZeroIsoPointCoproduct
    (R : Type) [CommRing R] (X : TopCat) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).obj X).X 0) ≅
      ∐ fun _ : X ↦ constantCoefficientModule R :=
  singularChainDegreeIsoCoproduct R X 0 ≪≫
    show (∐ fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) ≅
        ∐ fun _ : X ↦ constantCoefficientModule R from
      Limits.Sigma.whiskerEquiv (singularSimplexZeroEquiv X)
        (fun _ ↦ Iso.refl (constantCoefficientModule R))

/-- Helper for Problem 21.6.4: in degree `n`, the singular-chain map induced by `f` is the
coproduct map on singular-set `n`-simplices. -/
theorem singularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).map f).f n) =
      Sigma.map'
        (fun σ : singularSSetSimplex X n ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ)
        (fun _ ↦ 𝟙 (constantCoefficientModule R)) :=
  rfl

/-- Helper for Problem 21.6.4: the chosen point inclusion `Unit ⟶ X` is the canonical constant
map at `x`. -/
@[simp] theorem pointInclusion_eq_const
    (X : TopCat) (x : X) :
    TopCat.ofHom (ContinuousMap.const Unit x) = TopCat.const (X := TopCat.of Unit) x :=
  rfl

/-- Helper for Problem 21.6.4: the inverse singular-simplex equivalence in degree `0` sends the
constant singular simplex at `x` to the corresponding singular-set `0`-simplex. -/
@[simp] theorem singularSimplexEquiv_symm_apply_const_zero
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x) =
      TopCat.toSSetObj₀Equiv.symm x :=
  rfl

/-- Helper for Problem 21.6.4: the forward singular-simplex equivalence in degree `0` sends the
singular-set `0`-simplex at `x` to the constant singular simplex at `x`. -/
@[simp] theorem singularSimplexEquiv_apply_toSSetObjZero
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexEquiv 0 (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) =
      ContinuousMap.const _ x :=
  rfl

/-- Helper for Problem 21.6.4: the inverse of the unique-index coproduct is the unique coproduct
leg. -/
@[simp] theorem coproductUniqueIso_inv_eq_unitLeg
    (R : Type) [CommRing R] :
    (coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)).inv =
      Sigma.ι (fun _ : Unit ↦ constantCoefficientModule R) () := by
  -- The `simps` formula for `coproductUniqueIso` already identifies the inverse with the unique
  -- colimit injection.
  simp [coproductUniqueIso_inv]

/-- Helper for Problem 21.6.4: under `singularSimplexEquiv`, the simplicial map induced by the
constant map at `x` is the constant singular simplex at `x`. -/
@[simp] theorem singularSimplexEquiv_map_const
    (n : ℕ) (X : Type _) [TopologicalSpace X] (x : X) (σ : singularSimplex n Unit) :
    singularSimplexEquiv n (TopCat.of X)
        (((TopCat.toSSet.map (TopCat.const (X := TopCat.of Unit) x)).app
          (Opposite.op (SimplexCategory.mk n))
          ((singularSimplexEquiv n (TopCat.of Unit)).symm σ))) =
      ContinuousMap.const _ x := by
  -- The singular-set map of a constant map is postcomposition with that constant map.
  rfl

/-- Helper for Problem 21.6.4: for `TopCat.of Unit`, the inverse of the degree-zero point chart
sends the unique point generator to the unique simplex leg. -/
theorem unitZeroChainLeg_eq_constantSimplexLeg
    (R : Type) [CommRing R] :
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
    let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
    uIso.inv ≫ eUnit.inv =
      Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
        (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv := by
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  let ePointUnit :
      (∐ fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R) ≅
        ∐ fun _ : Unit ↦ constantCoefficientModule R :=
    Limits.Sigma.whiskerEquiv (singularSimplexZeroEquiv Unit)
      (fun _ ↦ Iso.refl (constantCoefficientModule R))
  change uIso.inv ≫ eUnit.inv =
      Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
        (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv
  calc
    uIso.inv ≫ eUnit.inv = uIso.inv ≫ ePointUnit.inv ≫ eSimplexUnit.inv := by
      -- First expand the degree-zero point chart into the simplex chart followed by reindexing.
      simp [eUnit, eSimplexUnit, ePointUnit, singularChainDegreeZeroIsoPointCoproduct,
        Category.assoc]
    _ = Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          ((singularSimplexZeroEquiv Unit).symm ()) ≫ eSimplexUnit.inv := by
      have h :
          uIso.inv ≫ ePointUnit.inv =
            Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
              ((singularSimplexZeroEquiv Unit).symm ()) := by
        rw [coproductUniqueIso_inv_eq_unitLeg (R := R)]
        -- Then compute the inverse reindexing map on the unique `Unit` generator.
        simpa [ePointUnit, Limits.Sigma.whiskerEquiv] using
          (Sigma.ι_comp_map'
            (f := fun _ : Unit ↦ constantCoefficientModule R)
            (g := fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
            ((singularSimplexZeroEquiv Unit).symm)
            (fun _ ↦ 𝟙 (constantCoefficientModule R))
            ())
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ eSimplexUnit.inv) h
    _ = Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv := by
      -- Finally identify the inverse point/simplex equivalence on `Unit`.
      simp

/-- Helper for Problem 21.6.4: precomposing the simplex coproduct chart inverse with a simplex
leg recovers the corresponding singular-set leg. -/
theorem singularChainDegreeIsoCoproduct_inv_simplexLeg
    (R : Type) [CommRing R] (X : TopCat) (σ : singularSimplex 0 X) :
    Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) σ ≫
        (singularChainDegreeIsoCoproduct (R := R) X 0).inv =
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
        ((singularSimplexEquiv 0 X).symm σ) := by
  -- Expand the inverse coproduct reindexing and evaluate it on the chosen simplex leg.
  change
    Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) σ ≫
        (show (∐ fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) ≅
            ∐ fun _ : singularSimplex 0 X ↦ constantCoefficientModule R from
          Limits.Sigma.whiskerEquiv (singularSimplexEquiv 0 X)
            (fun _ ↦ Iso.refl (constantCoefficientModule R))).inv =
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
        ((singularSimplexEquiv 0 X).symm σ)
  simpa [Limits.Sigma.whiskerEquiv] using
    (Sigma.ι_comp_map'
      (f := fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
      (g := fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
      ((singularSimplexEquiv 0 X).symm)
      (fun _ ↦ 𝟙 (constantCoefficientModule R))
      σ)

/-- Helper for Problem 21.6.4: postcomposing a singular-set leg with the simplex coproduct chart
recovers the corresponding simplex leg. -/
theorem singularChainDegreeIsoCoproduct_hom_sSetLeg
    (R : Type) [CommRing R] (X : TopCat) (σ : singularSSetSimplex X 0) :
    Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) σ ≫
        (singularChainDegreeIsoCoproduct (R := R) X 0).hom =
      Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
        (singularSimplexEquiv 0 X σ) := by
  -- Expand the coproduct reindexing and evaluate it on the chosen singular-set simplex.
  change
    Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) σ ≫
        (show (∐ fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) ≅
            ∐ fun _ : singularSimplex 0 X ↦ constantCoefficientModule R from
          Limits.Sigma.whiskerEquiv (singularSimplexEquiv 0 X)
            (fun _ ↦ Iso.refl (constantCoefficientModule R))).hom =
      Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
        (singularSimplexEquiv 0 X σ)
  simpa [Limits.Sigma.whiskerEquiv] using
    (Sigma.ι_comp_map'
      (f := fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
      (g := fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
      (singularSimplexEquiv 0 X)
      (fun _ ↦ 𝟙 (constantCoefficientModule R))
      σ)

/-- Helper for Problem 21.6.4: before reindexing degree-zero simplices by points, the point
inclusion `Unit ⟶ X` sends the unique source generator to the simplex leg indexed by the
constant simplex at `x`. -/
theorem pointInclusion_zeroChainSimplexLeg
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
    let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
      Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
        (ContinuousMap.const _ x) := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  let σUnit : singularSSetSimplex (TopCat.of Unit) 0 :=
    (singularSimplexEquiv 0 (TopCat.of Unit)).symm (ContinuousMap.const _ ())
  let σX : singularSSetSimplex X 0 :=
    ((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σUnit)
  have hUnit :
      uIso.inv ≫ eUnit.inv =
        Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv := by
    -- Normalize the unique source generator before applying the degree-zero chain map.
    simpa [eUnit, eSimplexUnit, uIso] using
      unitZeroChainLeg_eq_constantSimplexLeg (R := R)
  calc
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
        Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom := by
      -- Replace the source chart by the normalized simplex leg.
      simpa [Category.assoc] using
        congrArg (fun f ↦ f ≫ (F.map ix).f 0 ≫ eSimplexX.hom) hUnit
    _ = Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ constantCoefficientModule R)
          σUnit ≫ (F.map ix).f 0 ≫ eSimplexX.hom := by
      -- Move from simplex-indexed coproducts to the singular-set degree-zero indexing.
      simpa [σUnit, Category.assoc] using
        congrArg (fun f ↦ f ≫ (F.map ix).f 0 ≫ eSimplexX.hom)
          (singularChainDegreeIsoCoproduct_inv_simplexLeg
            (R := R) (X := TopCat.of Unit) (σ := ContinuousMap.const _ ()))
    _ = Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
          σX ≫ eSimplexX.hom := by
      -- The degree-zero chain map is the coproduct map on singular-set simplices.
      rw [singularChainDegreeMap_eq_sigmaMap' (R := R) (f := ix) (n := 0)]
      have hMap :
          Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ constantCoefficientModule R)
              σUnit ≫
                Sigma.map'
                  (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
                    (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
                  (fun _ ↦ 𝟙 (constantCoefficientModule R)) =
            𝟙 (constantCoefficientModule R) ≫
              Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) σX := by
        simpa [σX] using
          (Sigma.ι_comp_map'
            (f := fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ constantCoefficientModule R)
            (g := fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
            (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
              (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
            (fun _ ↦ 𝟙 (constantCoefficientModule R))
            σUnit)
      calc
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ constantCoefficientModule R)
            σUnit ≫
              Sigma.map'
                (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
                  (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
                (fun _ ↦ 𝟙 (constantCoefficientModule R)) ≫
                eSimplexX.hom =
            (𝟙 (constantCoefficientModule R) ≫
              Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R) σX) ≫
                eSimplexX.hom := by
          exact congrArg (fun f ↦ f ≫ eSimplexX.hom) hMap
        _ = Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
              σX ≫ eSimplexX.hom := by
          simp [Category.assoc]
    _ = Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (singularSimplexEquiv 0 X σX) := by
      -- Finally reindex the target coproduct back to ordinary singular simplices.
      simpa [σX, Category.assoc] using
        singularChainDegreeIsoCoproduct_hom_sSetLeg (R := R) (X := X) (σ := σX)
    _ = Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (ContinuousMap.const _ x) := by
      -- The constant map on `Unit` carries the unique degree-zero simplex to the constant simplex
      -- at `x`.
      have hConst : singularSimplexEquiv 0 X σX = ContinuousMap.const _ x := by
        simpa [pointInclusion_eq_const, σUnit, σX] using
          (singularSimplexEquiv_map_const 0 X x (ContinuousMap.const _ ()))
      rw [hConst]

/-- Helper for Problem 21.6.4: reindexing the degree-zero simplex coproduct by points sends the
constant simplex leg at `x` to the point leg at `x`. -/
theorem constZeroSimplexLeg_comp_pointCoproductReindex
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) (ContinuousMap.const _ x) ≫
        (Limits.Sigma.whiskerEquiv (singularSimplexZeroEquiv X)
          (fun _ ↦ Iso.refl (constantCoefficientModule R))).hom =
      Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x := by
  -- Expand the coproduct reindexing and evaluate it on the constant `0`-simplex indexed by `x`.
  simpa [Limits.Sigma.whiskerEquiv] using
    (Sigma.ι_comp_map'
      (f := fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
      (g := fun _ : X ↦ constantCoefficientModule R)
      (singularSimplexZeroEquiv X)
      (fun _ ↦ 𝟙 (constantCoefficientModule R))
      (ContinuousMap.const _ x))

/-- Helper for Problem 21.6.4: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
unique point generator to the chain generator indexed by `x`. -/
theorem pointInclusion_zeroChainLeg
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
    let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eX.hom =
      Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  let ePointX :
      (∐ fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) ≅
        ∐ fun _ : X ↦ constantCoefficientModule R :=
    Limits.Sigma.whiskerEquiv (singularSimplexZeroEquiv X)
      (fun _ ↦ Iso.refl (constantCoefficientModule R))
  change uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eX.hom =
      Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x
  -- First expose the simplex-indexed coproduct leg, then reindex degree-zero simplices by
  -- points using the canonical `singularSimplex 0 X ≃ X`.
  calc
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eX.hom =
        uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom ≫ ePointX.hom := by
      simp [eX, eSimplexX, ePointX, singularChainDegreeZeroIsoPointCoproduct]
    _ = Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (ContinuousMap.const _ x) ≫ ePointX.hom := by
      simpa [Category.assoc] using
        congrArg (fun f ↦ f ≫ ePointX.hom)
          (pointInclusion_zeroChainSimplexLeg (R := R) (X := X) x)
    _ = Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x := by
      simpa [ePointX] using
        constZeroSimplexLeg_comp_pointCoproductReindex (R := R) (X := X) x

/-- Helper for Problem 21.6.4: the canonical map from degree-zero chains onto `H₀(X; R)` is
surjective. -/
theorem degreeZeroChains_surjective_to_rSingularHomologyZero
    (R : Type) [CommRing R] (X : TopCat) :
    Function.Surjective
      ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).obj X).pOpcycles
          0 ≫
        (ChainComplex.isoHomologyι₀
          (((singularChainComplexFunctor (ModuleCat R)).obj
            (constantCoefficientModule R)).obj X)).inv) := by
  -- The projection to opcycles is epi, and in degree `0` opcycles identify with homology.
  exact
    (ModuleCat.epi_iff_surjective _).mp
      (by
        change Epi
          ((((singularChainComplexFunctor (ModuleCat R)).obj
              (constantCoefficientModule R)).obj X).pOpcycles 0 ≫
            (ChainComplex.isoHomologyι₀
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (constantCoefficientModule R)).obj X)).inv)
        infer_instance)

/-- Helper for Problem 21.6.4: the degree-zero class of the `x`-indexed chain generator agrees
with the image of the unique point generator under the inclusion `Unit ⟶ X` at `x`. -/
theorem pointGenerator_homology_eq_pointInclusion_image
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
    let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R))
    let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
    let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
    let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
    (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ eX.inv ≫ πX =
      uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
  let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
  change (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ eX.inv ≫ πX =
      uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix
  have hchains :
      uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 =
        (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ eX.inv := by
    -- Compare the degree-zero chain maps after postcomposing with the coproduct chart.
    apply (cancel_mono eX.hom).1
    simpa [Category.assoc] using
      pointInclusion_zeroChainLeg (R := R) (X := X) x
  -- Naturality of the passage from chains to `H₀` carries the generator identity to homology.
  calc
    (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ eX.inv ≫ πX =
        uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ πX := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ πX) hchains.symm
    _ = uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
      have hπ : (F.map ix).f 0 ≫ πX = πUnit ≫ FH.map ix := by
        calc
          (F.map ix).f 0 ≫ πX =
              (F.map ix).f 0 ≫ (F.obj X).pOpcycles 0 ≫ (F.obj X).isoHomologyι₀.inv := by
            rfl
          _ =
              (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                HomologicalComplex.opcyclesMap (F.map ix) 0 ≫
                  (F.obj X).isoHomologyι₀.inv := by
            rw [← Category.assoc, ← Category.assoc, HomologicalComplex.p_opcyclesMap]
          _ =
              πUnit ≫ FH.map ix := by
            dsimp [FH, πUnit, singularHomologyFunctor]
            rw [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality]
      calc
        uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ πX =
            uIso.inv ≫ eUnit.inv ≫ ((F.map ix).f 0 ≫ πX) := by
          simp [Category.assoc]
        _ = uIso.inv ≫ eUnit.inv ≫ (πUnit ≫ FH.map ix) := by
          change uIso.inv ≫ eUnit.inv ≫ ((F.map ix).f 0 ≫ πX) =
            uIso.inv ≫ eUnit.inv ≫ (πUnit ≫ FH.map ix)
          exact congrArg (fun f ↦ uIso.inv ≫ eUnit.inv ≫ f) hπ
        _ = uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
          simp [Category.assoc]

/-- Helper for Problem 21.6.4: a path between `x` and `y` identifies the two induced maps on
`H₀(-; R)` coming from the point inclusions `Unit ⟶ X`. -/
theorem pointInclusionHom_eq_of_path
    (R : Type) [CommRing R] (X : TopCat) {x y : X} (γ : Path x y) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map iy := by
  -- Homotopy invariance identifies homotopic point inclusions on singular homology.
  dsimp
  simpa using TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat R) (R := constantCoefficientModule R) (n := 0)
    (H := (Path.toHomotopyConst (Y := Unit) γ))

/-- Helper for Problem 21.6.4: in a path-connected space, every point inclusion `Unit ⟶ X`
induces the same map on zeroth constant-coefficient singular homology. -/
theorem pointInclusionHom_eq_of_pathConnected
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x y : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map iy := by
  -- Reduce the path-connected case to the explicit path comparison.
  simpa using
    pointInclusionHom_eq_of_path (R := R) (X := X) (γ := PathConnectedSpace.somePath x y)

/-- Helper for Problem 21.6.4: in a path-connected space, the degree-zero class of any point
agrees with the degree-zero class of a chosen basepoint. -/
theorem pointClass_eq_basepointClass_of_pathConnected
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x₀ x : X) :
    let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let hUnit : rSingularHomology R 0 (TopCat.of Unit) ≅ constantCoefficientModule R :=
      Classical.choice (pointRSingularHomologyZeroIsoConstantCoefficient (R := R))
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map i₀
        (hUnit.inv.hom (1 : constantCoefficientModule R)) =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map ix
        (hUnit.inv.hom (1 : constantCoefficientModule R)) := by
  classical
  let hUnit : rSingularHomology R 0 (TopCat.of Unit) ≅ constantCoefficientModule R :=
    Classical.choice (pointRSingularHomologyZeroIsoConstantCoefficient (R := R))
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  have hMaps :
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map i₀ =
        ((singularHomologyFunctor (ModuleCat R) 0).obj
          (constantCoefficientModule R)).map ix := by
    -- Path connectedness identifies the two point-inclusion maps on `H₀(-; R)`.
    simpa [i₀, ix] using pointInclusionHom_eq_of_pathConnected (R := R) (X := X) x₀ x
  -- Evaluate the common map on the preferred degree-zero point generator.
  exact congrArg (fun f ↦ f (hUnit.inv.hom (1 : constantCoefficientModule R))) hMaps

/-- Helper for Problem 21.6.4: the inclusion of a chosen basepoint splits after applying zeroth
constant-coefficient singular homology. -/
theorem pointInclusion_retraction_homology_split
    (R : Type) [CommRing R] (X : TopCat) (x₀ : X) :
    let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
    let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map i₀ ≫
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map g =
        𝟙 (rSingularHomology R 0 (TopCat.of Unit)) := by
  let F := ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R))
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  have hgi : i₀ ≫ g = 𝟙 (TopCat.of Unit) := by
    -- The composite `Unit ⟶ X ⟶ Unit` is the identity map of the point.
    ext u
  -- Functoriality transports the point retraction to the induced map on `H₀(-; R)`.
  simpa [F, i₀, g, Functor.map_comp] using congrArg F.map hgi

/-- Helper for Problem 21.6.4: in a path-connected space, the chosen basepoint inclusion
`Unit ⟶ X` should be surjective on zeroth constant-coefficient singular homology. -/
theorem pathConnectedH0BasepointInclusion_surjective
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x₀ : X) :
    let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
    Function.Surjective
      (((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map i₀) := by
  classical
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
  let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
  let β : constantCoefficientModule R ⟶ rSingularHomology R 0 (TopCat.of Unit) :=
    uIso.inv ≫ eUnit.inv ≫ πUnit
  let δ : (∐ fun _ : X ↦ constantCoefficientModule R) ⟶
      rSingularHomology R 0 (TopCat.of Unit) :=
    Sigma.desc (fun _ : X ↦ β)
  let α : (∐ fun _ : X ↦ constantCoefficientModule R) ⟶ rSingularHomology R 0 X :=
    eX.inv ≫ πX
  have hFactor : α = δ ≫ FH.map i₀ := by
    -- Check the factorization on each point generator of `C₀(X; R)`.
    refine Sigma.hom_ext _ _ fun x ↦ ?_
    calc
      (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ α =
          β ≫ FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) := by
        simpa [α, β, Category.assoc] using
          pointGenerator_homology_eq_pointInclusion_image (R := R) (X := X) x
      _ = β ≫ FH.map i₀ := by
        rw [show FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) = FH.map i₀ by
              symm
              simpa [i₀] using
                pointInclusionHom_eq_of_pathConnected (R := R) (X := X) x₀ x]
      _ = (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x ≫ δ) ≫ FH.map i₀ := by
        have hι :
            Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x ≫ δ = β := by
          simpa [δ] using (Sigma.ι_desc (fun _ : X ↦ β) x)
        rw [hι]
  -- Every `H₀(X; R)` class has a degree-zero chain representative, and `hFactor` rewrites that
  -- representative through the basepoint inclusion.
  dsimp
  intro z
  rcases degreeZeroChains_surjective_to_rSingularHomologyZero (R := R) (X := X) z with ⟨c, hc⟩
  refine ⟨δ (eX.hom c), ?_⟩
  change ((δ ≫ FH.map i₀) (eX.hom c)) = z
  rw [← hFactor]
  simpa [α] using hc

/-- Helper for Problem 21.6.4: a path-connected space has zeroth constant-coefficient singular
homology equal to the coefficient module. -/
theorem pathConnectedRSingularHomologyZeroIsoConstantCoefficient
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] :
    Nonempty (rSingularHomology R 0 X ≅ constantCoefficientModule R) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R))
  have hsplit :
      FH.map i₀ ≫ FH.map g =
        𝟙 (rSingularHomology R 0 (TopCat.of Unit)) := by
    -- The constant map to the point is a retraction of the chosen basepoint inclusion.
    simpa [i₀, g] using
      pointInclusion_retraction_homology_split (R := R) (X := X) x₀
  have hsurj : Function.Surjective (FH.map i₀) := by
    -- The remaining frontier is now isolated in the basepoint-surjectivity helper.
    simpa [i₀] using pathConnectedH0BasepointInclusion_surjective (R := R) (X := X) x₀
  have hinj : Function.Injective (FH.map i₀) := by
    -- The retraction gives an explicit left inverse on the underlying module map.
    have hleft : Function.LeftInverse (FH.map g) (FH.map i₀) := by
      intro z
      have h := congrArg (fun f ↦ f z) hsplit
      simpa [Category.assoc] using h
    exact hleft.injective
  let f : rSingularHomology R 0 (TopCat.of Unit) →ₗ[R] rSingularHomology R 0 X :=
    (FH.map i₀).hom
  have hsurj_f : Function.Surjective f := hsurj
  have hinj_f : Function.Injective f := hinj
  let hBasepoint : rSingularHomology R 0 (TopCat.of Unit) ≅ rSingularHomology R 0 X :=
    LinearEquiv.toModuleIso <| LinearEquiv.ofBijective f ⟨hinj_f, hsurj_f⟩
  -- Finish by comparing with the already computed point homology.
  exact
    ⟨hBasepoint.symm ≪≫
      Classical.choice (pointRSingularHomologyZeroIsoConstantCoefficient (R := R))⟩

/-- Helper for Problem 21.6.4: a connected closed orientable `3`-manifold has zeroth integral
singular homology `ℤ`. -/
theorem closedOrientableThreeManifoldZeroIntegralHomologyIsoInt
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M)) :
    Nonempty (integralSingularHomology 0 (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  -- First replace connectedness by the path-connected `H₀` owner from Chapter 20.
  let _ : PathConnectedSpace M :=
    closedOrientableThreeManifold_pathConnectedSpace (I := I) (M := M) h_orientable
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.of M) 0 with ⟨hInt⟩
  rcases
      pathConnectedRSingularHomologyZeroIsoConstantCoefficient
        (R := ℤ) (X := TopCat.of M) with ⟨hZero⟩
  -- Then transport back to the ordinary integral homology owner.
  exact ⟨hInt ≪≫ hZero ≪≫ constantCoefficientModuleIsoInt⟩

/-- Helper for Problem 21.6.4: the `3`-sphere has zeroth integral singular homology `ℤ`. -/
theorem sphereThreeZeroIntegralHomologyIsoInt :
    Nonempty (integralSingularHomology 0 (TopCat.sphere.{0} 3) ≅ ModuleCat.of ℤ ℤ) := by
  -- Reuse the same path-connected `H₀` package for the sphere.
  let _ : PathConnectedSpace (TopCat.sphere.{0} 3) := sphereThree_pathConnectedSpace
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere.{0} 3) 0 with ⟨hInt⟩
  rcases
      pathConnectedRSingularHomologyZeroIsoConstantCoefficient
        (R := ℤ) (X := TopCat.sphere.{0} 3) with ⟨hZero⟩
  -- The constant coefficient module is again the ordinary `ℤ`-module.
  exact ⟨hInt ≪≫ hZero ≪≫ constantCoefficientModuleIsoInt⟩

/-- Helper for Problem 21.6.4: for any integer-coefficient pair homology theory on based spaces,
the reduced homology of `S^3` is `ℤ` in degree `3` and vanishes in every other natural degree. -/
theorem sphereThreeReducedHomologyPattern
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    (H : PairHomologyTheory ℤ) :
    Nonempty (ModuleCat.of ℤ (basedReducedHomology H (3 : ℤ) (basedSphere 3)) ≅
      ModuleCat.of ℤ ℤ) ∧
      ∀ {q : ℕ}, q ≠ 3 →
        IsZero (ModuleCat.of ℤ (basedReducedHomology H (q : ℤ) (basedSphere 3))) := by
  -- Package the degree-`3` and off-degree sphere calculations together so later proof steps can
  -- consume one stable owner-level interface instead of repeating the Chapter 13 rewrites.
  refine ⟨?_, ?_⟩
  · -- The generic reduced sphere calculation already identifies `H̃₃(S³)` with `ℤ`.
    simpa using sphereReducedHomologyWithCoefficients_self (H := H) 3
  · intro q hq
    -- Every natural degree different from `3` is an off-top degree for `S³`, so the generic
    -- reduced sphere vanishing theorem applies directly after coercing the degree to `ℤ`.
    have hq' : (q : ℤ) ≠ (3 : ℤ) := by
      exact_mod_cast hq
    simpa using sphereReducedHomologyWithCoefficients_isZero_of_ne (H := H) 3 (q : ℤ) hq'

/-- Helper for Problem 21.6.4: `S^3` has ordinary integral homology `ℤ` in degrees `0` and `3`
and vanishes in all other natural degrees. -/
theorem sphereThreeIntegralHomologyPattern :
    Nonempty (integralSingularHomology 0 (TopCat.sphere 3) ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (integralSingularHomology 3 (TopCat.sphere 3) ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, k ≠ 0 → k ≠ 3 → IsZero (integralSingularHomology k (TopCat.sphere 3)) := by
  rcases CompactManifold.sphereIntegralHomologyPattern_of_pos (n := 3) (by decide) with
    ⟨hTop, hMiddle, hAbove⟩
  refine ⟨?_, hTop, ?_⟩
  · -- The degree-zero branch was already computed directly from path connectedness.
    exact sphereThreeZeroIntegralHomologyIsoInt
  · intro k hk0 hk3
    -- Split the off-top degrees into the middle range `0 < k < 3` and the above-dimension range.
    by_cases hlt : k < 3
    · exact hMiddle (Nat.pos_of_ne_zero hk0) hlt
    · have hgt : 3 < k := by omega
      exact hAbove hgt

/-- Helper for Problem 21.6.4: two zero homology objects are canonically isomorphic. -/
theorem isoOfIsZero {C : Type _} [Category C] [HasZeroObject C]
    {A B : C} (hA : IsZero A) (hB : IsZero B) :
    Nonempty (A ≅ B) := by
  -- Compare both objects with the zero object and compose the resulting isomorphisms.
  exact ⟨hA.isoZero ≪≫ hB.isoZero.symm⟩

/-- Helper for Problem 21.6.4: Chapter 18's ordinary integral singular cohomology owner agrees
with the Chapter 20 owner `rSingularCohomology ℤ`. -/
noncomputable def singularCohomologyIsoRSingularCohomology
    (X : TopCat) (p : ℕ) :
    singularCohomology X p ≅ rSingularCohomology ℤ X p := by
  -- Both sides are definitional abbreviations for the homology of the same singular cochain
  -- complex, so the comparison is the identity isomorphism.
  exact eqToIso (by rfl)

/-- Helper for Problem 21.6.4: after normalizing the Chapter 20 cohomology owner to ordinary
integral singular cohomology, the remaining degree-`1` vanishing target is exactly the source's
`H^1(M; ℤ) = 0` step. -/
theorem closedOrientableThreeManifoldDegreeOneSingularCohomologyIsZero
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M))
    (h_H1 : IsZero (integralSingularHomology 1 (TopCat.of M))) :
    IsZero (singularCohomology (TopCat.of M) 1) := by
  -- Route correction: the owner mismatch is now isolated, so the only remaining work is the
  -- degree-`1` UCT argument on the ordinary singular cohomology owner.
  -- TODO for Problem 21.6.4: apply the Chapter 17 universal coefficient sequence to a
  -- `ℤ`-indexed extension of the integral singular chain complex, kill the `Hom(H₁, ℤ)` term
  -- with `h_H1`, kill the `Ext¹(H₀, ℤ)` term using
  -- `closedOrientableThreeManifoldZeroIntegralHomologyIsoInt`, and conclude `H^1(M; ℤ) = 0`.
  sorry

/-- Helper for Problem 21.6.4: on a closed orientable `3`-manifold with `H₁(M; ℤ) = 0`, the
degree-`1` constant-coefficient cohomology owner vanishes. -/
theorem closedOrientableThreeManifoldDegreeOneConstantCoefficientCohomologyIsZero
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M))
    (h_H1 : IsZero (integralSingularHomology 1 (TopCat.of M))) :
    IsZero (rSingularCohomology ℤ (TopCat.of M) 1) := by
  have hSing :
      IsZero (singularCohomology (TopCat.of M) 1) :=
    closedOrientableThreeManifoldDegreeOneSingularCohomologyIsZero
      (I := I) (M := M) h_orientable h_H1
  -- Transport the ordinary singular cohomology vanishing back to the Chapter 20 owner.
  exact
    IsZero.of_iso hSing
      (singularCohomologyIsoRSingularCohomology (TopCat.of M) 1)

/-- Helper for Problem 21.6.4: packaging the constant local-system universal-cover model reduces
the cap-duality witness to a single constructor application. -/
theorem constantIntegralLocalSystemDualityData
    (o : ROrientedManifold ℤ I 3 M)
    {z : rSingularHomology ℤ 3 (TopCat.of M)}
    (hz : IsRFundamentalClassFor o z) :
    ∃ x : M,
      ∃ C :
        ChosenUniversalCoverChainModel
          ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ ℤ)) x,
        ∃ cohomologyIso :
          C.ComputesCohomology (fun p ↦ rSingularCohomology ℤ (TopCat.of M) p),
          ∃ homologyIso :
            C.ComputesHomology
              (fun q ↦
                singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ ℤ) q),
            ∃ capWithZ : C.CapWithFundamentalClass 3 z,
              ∀ p : ℕ,
                ModuleCat.ofHom (capWithFundamentalClass z p) =
                  localCoefficientPoincareDualityMap C 3
                    (fun q ↦ rSingularCohomology ℤ (TopCat.of M) q)
                    (fun q ↦
                      singularHomologyWithCoefficients ℤ (TopCat.of M)
                        (ModuleCat.of ℤ ℤ) q)
                    cohomologyIso homologyIso capWithZ p := by
  -- Route correction: all remaining based-model bookkeeping is concentrated here, so later uses
  -- only have to unpack the chosen model and apply the Chapter 20 constructor.
  -- TODO for Problem 21.6.4: choose a basepoint using path connectedness, choose the
  -- universal-cover chain model for the trivial local system, provide the cohomology and
  -- homology comparison data to the source-facing owners, and identify the transported local
  -- coefficient duality map with `ModuleCat.ofHom (capWithFundamentalClass z p)`.
  sorry

/-- Helper for Problem 21.6.4: a compatible integral fundamental class gives the source-facing
constant-system Poincare duality witness needed for the concrete cap-product family. -/
theorem capWithFundamentalClass_isLocalCoefficientPoincareDualityMap_of_isRFundamentalClassFor
    (o : ROrientedManifold ℤ I 3 M)
    {z : rSingularHomology ℤ 3 (TopCat.of M)}
    (hz : IsRFundamentalClassFor o z) :
    IsLocalCoefficientPoincareDualityMap o
      ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ ℤ))
      z
      (fun p ↦ rSingularCohomology ℤ (TopCat.of M) p)
      (fun q ↦ singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ ℤ) q)
      (fun p ↦ ModuleCat.ofHom (capWithFundamentalClass z p)) := by
  rcases constantIntegralLocalSystemDualityData (I := I) (M := M) o hz with
    ⟨x, C, cohomologyIso, homologyIso, capWithZ, hcapWithZ⟩
  -- The packaged chosen-model data matches the Chapter 20 specification term-for-term.
  refine ⟨hz, x, C, cohomologyIso, homologyIso, capWithZ, ?_⟩
  intro p
  -- The remaining comparison is exactly the packaged cap-map identification.
  exact hcapWithZ p

/-- Helper for Problem 21.6.4: once the source-facing constant-system duality witness is in
place, each concrete cap-product map `capWithFundamentalClass z p` is an isomorphism. -/
theorem capWithFundamentalClass_isIso_of_isRFundamentalClassFor
    (o : ROrientedManifold ℤ I 3 M)
    {z : rSingularHomology ℤ 3 (TopCat.of M)}
    (hz : IsRFundamentalClassFor o z) (p : ℕ) :
    IsIso (ModuleCat.ofHom (capWithFundamentalClass z p)) := by
  -- Apply the abstract Chapter 20 duality theorem to the concrete cap-product family.
  exact
    isIso_of_isLocalCoefficientPoincareDualityMap
      o
      ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ ℤ))
      z
      (fun q ↦ rSingularCohomology ℤ (TopCat.of M) q)
      (fun q ↦ singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ ℤ) q)
      (fun q ↦ ModuleCat.ofHom (capWithFundamentalClass z q))
      (capWithFundamentalClass_isLocalCoefficientPoincareDualityMap_of_isRFundamentalClassFor
        (I := I) (M := M) o hz)
      p

/-- Helper for Problem 21.6.4: on a closed orientable `3`-manifold with `H₁(M; ℤ) = 0`, the
second integral homology group vanishes. -/
theorem closedOrientableThreeManifoldIntegralHomologyTwoIsZero
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M))
    (h_H1 : IsZero (integralSingularHomology 1 (TopCat.of M))) :
    IsZero (integralSingularHomology 2 (TopCat.of M)) := by
  -- TODO: orient the concrete cap-product comparison in the direction required by the
  -- `integralSingularHomology` owner, then transport the degree-one cohomology vanishing.
  sorry

/-- Helper for Problem 21.6.4: on a closed orientable `3`-manifold, integral homology vanishes
in every degree above `3`. -/
theorem closedOrientableThreeManifoldIntegralHomologyAboveThreeIsZero
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M))
    {k : ℕ} (hk : 3 < k) :
    IsZero (integralSingularHomology k (TopCat.of M)) := by
  rcases h_orientable with ⟨o⟩
  -- Use the orientation witness to recover the manifold instance required by the Chapter 20
  -- above-dimension vanishing theorem.
  let _ : ROrientedManifold ℤ I 3 M := o
  exact
    CompactManifold.isZeroIntegralHomology_of_gt_dimension
      (E := E) (M := M) (n := 3) Fact.out hk

/-- Problem 21.6.4: a closed orientable `3`-manifold with trivial first integral homology has the
same integral homology groups as `S^3`. Here "closed" is made explicit by `[CompactSpace M]`,
the connectedness convention is made explicit by `[ConnectedSpace M]`, orientability is recorded
as `Nonempty (ROrientedManifold ℤ I 3 M)`, which already packages the `I`-manifold structure, the
dimension-`3` condition is recorded by `[Fact (Module.finrank ℝ E = 3)]`, and the conclusion is
stated degreewise as an isomorphism with the integral singular homology of the canonical sphere
object `TopCat.sphere 3`.
-/
theorem integralSingularHomologyIsoSphereOfClosedOrientableThreeManifold
    (h_orientable : Nonempty (ROrientedManifold ℤ I 3 M))
    (h_H1 : IsZero (integralSingularHomology 1 (TopCat.of M))) (k : ℕ) :
    Nonempty ((integralSingularHomology k (TopCat.of M)) ≅
      (integralSingularHomology k (TopCat.sphere 3))) := by
  -- Route correction: normalize the manifold side degreewise first, so the remaining blockers are
  -- explicit sphere-side and duality-side comparisons rather than one monolithic `sorry`.
  rcases k with _ | k
  · -- The degree-zero branch is now delegated to the path-connected-space `H₀` owner package.
    rcases closedOrientableThreeManifoldZeroIntegralHomologyIsoInt
        (I := I) (M := M) h_orientable with ⟨hM⟩
    rcases sphereThreeZeroIntegralHomologyIsoInt with ⟨hSphere⟩
    exact ⟨hM ≪≫ hSphere.symm⟩
  rcases k with _ | k
  · -- Both degree-`1` homology groups vanish, so compare them through the zero object.
    have hSphere :
        IsZero (integralSingularHomology 1 (TopCat.sphere 3)) :=
      (sphereThreeIntegralHomologyPattern.2.2) 1 (by decide) (by decide)
    exact isoOfIsZero h_H1 hSphere
  rcases k with _ | k
  · -- The manifold-side degree-`2` vanishing is isolated in a dedicated duality/UCT helper.
    have hM :
        IsZero (integralSingularHomology 2 (TopCat.of M)) :=
      closedOrientableThreeManifoldIntegralHomologyTwoIsZero
        (I := I) (M := M) h_orientable h_H1
    have hSphere :
        IsZero (integralSingularHomology 2 (TopCat.sphere 3)) :=
      (sphereThreeIntegralHomologyPattern.2.2) 2 (by decide) (by decide)
    exact isoOfIsZero hM hSphere
  rcases k with _ | k
  · -- The manifold side of the top-degree comparison is already reduced to the standard owner.
    rcases closedOrientableThreeManifoldTopIntegralHomology
        (I := I) (M := M) h_orientable with
      ⟨hM⟩
    rcases sphereThreeIntegralHomologyPattern.2.1 with ⟨hSphere⟩
    -- Compare both top homology groups through the common `ℤ` owner.
    exact ⟨hM ≪≫ hSphere.symm⟩
  · -- TODO: use the Chapter 20 dimension-vanishing theorem once its exact exported owner is found.
    have hk : 3 < k + 4 := by omega
    have hM :
        IsZero (integralSingularHomology (k + 4) (TopCat.of M)) :=
      closedOrientableThreeManifoldIntegralHomologyAboveThreeIsZero
        (I := I) (M := M) h_orientable hk
    have hSphere :
        IsZero (integralSingularHomology (k + 4) (TopCat.sphere 3)) :=
      (sphereThreeIntegralHomologyPattern.2.2) (k + 4) (by omega) (by omega)
    exact isoOfIsZero hM hSphere

end
