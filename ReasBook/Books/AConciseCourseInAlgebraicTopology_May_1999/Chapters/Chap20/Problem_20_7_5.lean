import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.PrimeField
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Connected.LocPathConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Remark_13_5_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

noncomputable section

open AlgebraicTopology CategoryTheory MonoidalCategory
open CategoryTheory.Limits
open Simplicial
open scoped TensorProduct

-- Chapter 13 already fixes `integralSingularHomology` as the owner for ordinary integral
-- singular homology, and Chapter 20 fixes `rSingularHomology` for constant-coefficient homology.
-- The source hypothesis `f_*(i_n) = q z` is kept below by explicit map-and-generator data rather
-- than by a file-local wrapper predicate.

private abbrev problem20_7_5SingularSSetSimplex (X : TopCat) (k : ℕ) : Type _ :=
  (TopCat.toSSet.obj X) _⦋k⦌

local notation "singularSSetSimplex" => problem20_7_5SingularSSetSimplex

private noncomputable def problem20_7_5SingularChainDegreeIsoCoproduct
    (R : Type) [CommRing R] (X : TopCat) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).obj X).X k) ≅
      ∐ fun _ : singularSimplex k X ↦ constantCoefficientModule R :=
  (eqToIso rfl) ≪≫
    show (∐ fun _ : problem20_7_5SingularSSetSimplex X k ↦ constantCoefficientModule R) ≅
        ∐ fun _ : singularSimplex k X ↦ constantCoefficientModule R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv k X)
        (fun _ ↦ Iso.refl (constantCoefficientModule R))

local notation "singularChainDegreeIsoCoproduct" =>
  problem20_7_5SingularChainDegreeIsoCoproduct

/-- Helper for Problem 20.7.5: in degree `k`, the singular-chain map induced by `f` is the
coproduct map on singular `k`-simplices. -/
theorem singularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).map f).f k) =
      Sigma.map'
        (fun σ : singularSSetSimplex X k ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk k)) σ)
        (fun _ ↦ 𝟙 (constantCoefficientModule R)) :=
  rfl

/-- Helper for Problem 20.7.5: the direct unit-coefficient singular chain group in degree `k` is
the coproduct of one copy of `R` for each singular `k`-simplex. This keeps the later integral
projective/flatness arguments on the ordinary unit-coefficient owner. -/
private noncomputable def unitSingularChainDegreeIsoCoproduct
    (R : Type) [CommRing R] (X : TopCat) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X).X k) ≅
      ∐ fun _ : singularSimplex k X ↦ ModuleCat.of R R :=
  (eqToIso rfl) ≪≫
    show (∐ fun _ : singularSSetSimplex X k ↦ ModuleCat.of R R) ≅
        ∐ fun _ : singularSimplex k X ↦ ModuleCat.of R R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv k X)
        (fun _ ↦ Iso.refl (ModuleCat.of R R))

/-- Helper for Problem 20.7.5: in degree `k`, the unit-owner singular-chain map induced by `f`
is the coproduct map on singular `k`-simplices. -/
theorem unitSingularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f).f k) =
      Sigma.map'
        (fun σ : singularSSetSimplex X k ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk k)) σ)
        (fun _ ↦ 𝟙 (ModuleCat.of R R)) :=
  -- The unit-owner chain map is definitionally the simplex-indexed coproduct map.
  rfl

section

variable {n p : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [hBoundaryless : I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [hT2 : T2Space M] [hCharted : ChartedSpace H M]
  [hCompact : CompactSpace M] [hConnected : ConnectedSpace M] [hManifold : IsManifold I ⊤ M]
variable [hDim : Fact (Module.finrank ℝ E = n)]

include hBoundaryless hT2 hCharted hCompact hConnected hManifold hDim

/-- Helper for Problem 20.7.5: a top integral homology generator on `M` determines an integral
orientation together with a compatible integral fundamental class. -/
theorem existsIntegralOrientationAndFundamentalClass
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) :
    ∃ o : ROrientedManifold ℤ I n M,
      ∃ z : rSingularHomology ℤ n (TopCat.of M), IsRFundamentalClassFor o z := by
  -- Convert the chosen top integral homology generator into an integral orientation.
  have hOrientable : Nonempty (ROrientedManifold ℤ I n M) :=
    (orientability_iff_topIntegralHomologyIso_of_connectedClosedManifold).2 ⟨targetTopIso⟩
  rcases hOrientable with ⟨o⟩
  -- Then choose the unique compatible integral fundamental class for that orientation.
  rcases
      existsUnique_rFundamentalClassFor_of_rOrientedManifold
        (ROrientedManifold.toGlobalOrientation o) with ⟨z, hz, _⟩
  rcases (isRFundamentalClassForGlobalOrientation_iff _ _).mp hz with ⟨o', -, hz'⟩
  exact ⟨o', z, hz'⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: if the prime `p` does not divide `q`, then `q` is nonzero in
`ZMod p`. -/
theorem zmodIntCast_ne_zero_of_not_dvd
    {q : ℤ} (hpq : ¬ (p : ℤ) ∣ q) :
    (q : ZMod p) ≠ 0 := by
  -- Rewrite vanishing in `ZMod p` as divisibility in `ℤ`.
  intro hq
  exact hpq ((ZMod.intCast_zmod_eq_zero_iff_dvd q p).mp hq)

/-- Helper for Problem 20.7.5: the coefficient module `ZMod p`, viewed as a `ℤ`-module object. -/
private abbrev intZModModule (p : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (ZMod p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: when `p` is prime and `q` is nonzero in `ZMod p`, multiplication
by `q` is surjective on the underlying `ℤ`-module `ZMod p`. -/
theorem zmodIntScalar_surjective_of_ne_zero
    (hp : p.Prime) {q : ℤ} (hq : (q : ZMod p) ≠ 0) :
    Function.Surjective (fun y : intZModModule p ↦ q • y) := by
  -- Install the field structure on `ZMod p` so the inverse of the nonzero scalar is available.
  let _ : Fact p.Prime := ⟨hp⟩
  intro y
  refine ⟨(((q : ZMod p)⁻¹) * y : intZModModule p), ?_⟩
  -- Then evaluate the scalar action using the inverse of `(q : ZMod p)`.
  simpa [smul_eq_mul, mul_assoc] using
    congrArg (fun t : ZMod p ↦ t * y) (mul_inv_cancel₀ hq)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: if `p` does not divide `q`, then multiplication by `q` is
surjective on the underlying `ℤ`-module `ZMod p`. -/
theorem zmodIntScalar_surjective_of_not_dvd
    (hp : p.Prime) {q : ℤ} (hpq : ¬ (p : ℤ) ∣ q) :
    Function.Surjective (fun y : intZModModule p ↦ q • y) := by
  -- Reduce to the nonzero-scalar case already proved above.
  exact
    zmodIntScalar_surjective_of_ne_zero (p := p) hp
      (zmodIntCast_ne_zero_of_not_dvd (p := p) hpq)

/-- Helper for Problem 20.7.5: a connected closed manifold is path connected. -/
theorem connectedClosedManifold_pathConnectedSpace :
    PathConnectedSpace M := by
  -- Install the manifold local path connectedness needed for the standard bridge.
  let _ : LocPathConnectedSpace H :=
    (ModelWithCorners.toHomeomorph I).isOpenEmbedding.locPathConnectedSpace
  let _ : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace H M
  exact PathConnectedSpace.of_locPathConnectedSpace

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: a path-connected space has a unique path component. -/
theorem pathConnected_uniqueZerothHomotopy
    (X : Type _) [TopologicalSpace X] [PathConnectedSpace X] :
    Nonempty (Unique (ZerothHomotopy X)) := by
  -- Convert path connectedness into the standard nonempty-plus-subsingleton description of `π₀`.
  rcases (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp inferInstance with
    ⟨hne, hsub⟩
  rcases hne with ⟨x⟩
  -- Then package the unique path component into the target `Unique` witness.
  exact ⟨{ default := x, uniq := fun y ↦ hsub.elim y x }⟩

/-- Helper for Problem 20.7.5: a connected closed manifold has a unique path component. -/
theorem connectedClosedManifold_uniqueZerothHomotopy :
    Nonempty (Unique (ZerothHomotopy M)) := by
  let _ : PathConnectedSpace M :=
    connectedClosedManifold_pathConnectedSpace
      (E := E) (H := H) (I := I) (M := M) (n := n)
  -- Reduce the manifold-specific statement to the generic path-connected-space lemma.
  exact pathConnected_uniqueZerothHomotopy (X := M)

/-- Helper for Problem 20.7.5: the Chapter 20 constant coefficient owner `constantCoefficientModule
ℤ` is canonically the ordinary unit `ℤ`-module. -/
private noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- Helper for Problem 20.7.5: the Chapter 20 constant coefficient owner
`constantCoefficientModule (ZMod p)` is canonically the ordinary unit `ZMod p`-module. -/
private noncomputable def constantCoefficientModuleIsoZMod :
    constantCoefficientModule (ZMod p) ≅ ModuleCat.of (ZMod p) (ZMod p) :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift (ZMod p) ≃ₗ[ZMod p] ZMod p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the Chapter 20 constant-coefficient `ZMod p` homology owner agrees
with the ordinary unit-coefficient singular homology owner. -/
theorem zmodConstantCoefficientHomologyIsoUnitOwner
    (X : TopCat) (k : ℕ) :
    Nonempty
      (rSingularHomology (ZMod p) k X ≅
        (((singularHomologyFunctor (ModuleCat (ZMod p)) k).obj
          (ModuleCat.of (ZMod p) (ZMod p))).obj X)) := by
  -- Compare the Chapter 20 constant coefficient owner with the ordinary unit-module owner once.
  refine ⟨?_⟩
  simpa [rSingularHomology] using
    (((singularHomologyFunctor (ModuleCat (ZMod p)) k).mapIso
      constantCoefficientModuleIsoZMod).app X)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: after restricting scalars along `ℤ → ZMod p`, the degree-`k`
term of the unit-owner `ZMod p` singular chain complex is identified with the restricted-scalar
image of the simplex-indexed coproduct owner. -/
noncomputable def restrictedUnitSingularChainDegreeIsoCoproduct
    (X : TopCat) (k : ℕ) :
    ((((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (((singularChainComplexFunctor (ModuleCat (ZMod p))).obj
          (ModuleCat.of (ZMod p) (ZMod p))).obj X)).X k) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
        (∐ fun _ : singularSimplex k X ↦ ModuleCat.of (ZMod p) (ZMod p))) := by
  -- First normalize the `ZMod p`-linear chain group to the simplex coproduct owner.
  let eUnit := unitSingularChainDegreeIsoCoproduct (R := ZMod p) X k
  -- Then restrict scalars degreewise so both sides live in `ModuleCat ℤ`.
  simpa [Functor.mapHomologicalComplex_obj_X] using
    (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).mapIso eUnit

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: restricting scalars along `ℤ → ZMod p` reflects zero objects,
because the underlying carrier type is unchanged. -/
theorem zmodModule_isZero_of_restrictScalars
    (A : ModuleCat (ZMod p))
    (hA : IsZero ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj A)) :
    IsZero A := by
  -- A zero restricted module is subsingleton on the unchanged underlying carrier.
  have hsub : Subsingleton A := by
    simpa using (ModuleCat.isZero_iff_subsingleton.mp hA)
  let _ : Subsingleton A := hsub
  -- Then the original `ZMod p`-module object is zero as well.
  exact ModuleCat.isZero_of_subsingleton A

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: after restricting scalars to `ℤ`, the Chapter 20 constant-
coefficient `ZMod p` homology owner agrees with the unit-coefficient owner. -/
theorem zmodRestrictedCoefficientHomologyIsoUnitOwner
    (X : TopCat) (k : ℕ) :
    Nonempty
      (((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
          (rSingularHomology (ZMod p) k X)) ≅
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
          ((((singularHomologyFunctor (ModuleCat (ZMod p)) k).obj
              (ModuleCat.of (ZMod p) (ZMod p))).obj X)))) := by
  rcases zmodConstantCoefficientHomologyIsoUnitOwner (p := p) X k with ⟨hUnit⟩
  -- Restrict scalars so both homology owners live in the common category `ModuleCat ℤ`.
  refine ⟨?_⟩
  simpa using
    ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).mapIso hUnit)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the zeroth constant-coefficient singular homology of a point is the
coefficient module itself. -/
theorem pointRSingularHomologyZeroIsoConstantCoefficient
    (R : Type) [CommRing R] :
    Nonempty (rSingularHomology R 0 (TopCat.of Unit) ≅ constantCoefficientModule R) := by
  -- Compute `H₀` of the point via the totally disconnected-space calculation.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat R) (R := constantCoefficientModule R) (X := TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: ordinary integral singular homology agrees with the Chapter 20
owner `rSingularHomology ℤ` in every degree. -/
theorem integralSingularHomologyIsoRSingularHomology
    (X : TopCat) (k : ℕ) :
    Nonempty (integralSingularHomology k X ≅ rSingularHomology ℤ k X) := by
  -- Compare both homology owners with the same singular-chain homology object.
  refine ⟨?_⟩
  simpa [integralSingularHomology, rSingularHomology] using
    (((singularHomologyFunctor (ModuleCat ℤ) k).mapIso
      constantCoefficientModuleIsoInt).app X).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: a path between `x` and `y` identifies the maps on `H₀(-; R)`
induced by the two point inclusions `Unit ⟶ X`. -/
theorem pointInclusionHom_eq_of_path
    (R : Type) [CommRing R] (X : TopCat) {x y : X} (γ : Path x y) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map iy := by
  -- Homotopy invariance identifies the induced maps of homotopic point inclusions.
  dsimp
  simpa using TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat R) (R := constantCoefficientModule R) (n := 0)
    (H := (Path.toHomotopyConst (Y := Unit) γ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: in a path-connected space, every point inclusion `Unit ⟶ X`
induces the same map on `H₀(-; R)`. -/
theorem pointInclusionHom_eq_of_pathConnected
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x y : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (constantCoefficientModule R)).map iy := by
  -- Reduce the path-connected case to the explicit path-based comparison.
  simpa using
    pointInclusionHom_eq_of_path (R := R) (X := X) (γ := PathConnectedSpace.somePath x y)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: in a path-connected space, the degree-zero class of any point
agrees with the class of a chosen basepoint. -/
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
  -- Evaluate the common map on the preferred generator of `H₀(Unit; R)`.
  exact congrArg (fun f ↦ f (hUnit.inv.hom (1 : constantCoefficientModule R))) hMaps

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the inclusion of a chosen basepoint into a space splits after
applying zeroth constant-coefficient singular homology. -/
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
  -- Functoriality transports the point retraction to the induced maps on `H₀(-; R)`.
  simpa [F, i₀, g, Functor.map_comp] using congrArg F.map hgi

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: a singular `0`-simplex is determined by its unique vertex, so
degree-zero simplices are canonically the points of `X`. -/
noncomputable def singularSimplexZeroEquiv
    (X : Type _) [TopologicalSpace X] :
    singularSimplex 0 X ≃ X :=
  { toFun := fun σ ↦ TopCat.toSSetObj₀Equiv ((singularSimplexEquiv 0 (TopCat.of X)).symm σ)
    invFun := fun x ↦ singularSimplexEquiv 0 (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x)
    left_inv := by
      intro σ
      -- The canonical singular-set degree-zero equivalences are inverse to each other.
      simp
    right_inv := by
      intro x
      -- The same canonical degree-zero equivalences recover the original point.
      simp }

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the inverse of `singularSimplexZeroEquiv` sends a point to the
constant singular `0`-simplex at that point. -/
@[simp] theorem singularSimplexZeroEquiv_symm_apply
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexZeroEquiv X).symm x = ContinuousMap.const _ x := by
  -- Apply injectivity of the degree-zero simplex/point equivalence.
  apply (singularSimplexZeroEquiv X).injective
  change TopCat.toSSetObj₀Equiv
      ((singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x)) = x
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the constant singular `0`-simplex at `x` maps to `x` under the
degree-zero simplex/point equivalence. -/
@[simp] theorem singularSimplexZeroEquiv_apply_const
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexZeroEquiv X (ContinuousMap.const _ x) = x := by
  -- Evaluate the canonical degree-zero equivalence on the constant singular simplex.
  change TopCat.toSSetObj₀Equiv
      ((singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x)) = x
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the inverse singular-simplex equivalence in degree `0` sends the
constant singular simplex at `x` to the corresponding singular-set `0`-simplex. -/
@[simp] theorem singularSimplexEquiv_symm_apply_const_zero
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x) =
      TopCat.toSSetObj₀Equiv.symm x :=
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the forward singular-simplex equivalence in degree `0` sends the
singular-set `0`-simplex at `x` to the constant singular simplex at `x`. -/
@[simp] theorem singularSimplexEquiv_apply_toSSetObjZero
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexEquiv 0 (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) =
      ContinuousMap.const _ x := by
  -- Unfold the degree-zero point/simplex equivalence once and read off the constant simplex.
  simpa [singularSimplexZeroEquiv] using singularSimplexZeroEquiv_symm_apply (X := X) x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: under `singularSimplexEquiv`, the simplicial map induced by the
constant map at `x` is the constant singular simplex at `x`. -/
@[simp] theorem singularSimplexEquiv_map_const
    (k : ℕ) (X : Type _) [TopologicalSpace X] (x : X) (σ : singularSimplex k Unit) :
    singularSimplexEquiv k (TopCat.of X)
        (((TopCat.toSSet.map (TopCat.const (X := TopCat.of Unit) x)).app
          (Opposite.op (SimplexCategory.mk k))
          ((singularSimplexEquiv k (TopCat.of Unit)).symm σ))) =
      ContinuousMap.const _ x := by
  -- The singular-set map of a constant map is postcomposition with that constant map.
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: degree-zero singular chains are the coproduct of one copy of `R`
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: reindexing the degree-zero simplex coproduct by points sends the
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the chosen point inclusion `Unit ⟶ X` is the canonical constant
map at `x`. -/
@[simp] theorem pointInclusion_eq_const
    (X : TopCat) (x : X) :
    TopCat.ofHom (ContinuousMap.const Unit x) = TopCat.const (X := TopCat.of Unit) x :=
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the inverse of the unique-index coproduct is the unique coproduct
leg. -/
@[simp] theorem coproductUniqueIso_inv_eq_unitLeg
    (R : Type) [CommRing R] :
    (coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)).inv =
      Sigma.ι (fun _ : Unit ↦ constantCoefficientModule R) () := by
  -- The `simps` formula for `coproductUniqueIso` already identifies the inverse with the unique
  -- colimit injection.
  simp [coproductUniqueIso_inv]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: for `TopCat.of Unit`, the inverse of the degree-zero point chart
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: after conjugating the degree-zero chain map of the point inclusion
by the simplex coproduct charts, one obtains the explicit simplex-indexed coproduct map. -/
theorem pointInclusionZeroChainMapInSimplexCoordinates
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
    let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
    let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
    eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
      Sigma.map'
        (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
          singularSimplexEquiv 0 X
            (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))))
        (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
  let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
  have hmap :
      (F.map ix).f 0 =
        Sigma.map'
          (fun τ : singularSSetSimplex (TopCat.of Unit) 0 ↦
            (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) τ)
          (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
    -- Re-express the degree-zero chain map as the coproduct map on singular `0`-simplices.
    simpa [F] using singularChainDegreeMap_eq_sigmaMap' (R := R) ix 0
  change eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
      Sigma.map'
        (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
          singularSimplexEquiv 0 X
            (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))))
        (fun _ ↦ 𝟙 (constantCoefficientModule R))
  have hcomp1 :
      eSimplexUnit.inv ≫ (F.map ix).f 0 =
        Sigma.map'
          (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
            (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))
          (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
    rw [hmap]
    -- First compose the inverse simplex chart on `Unit` with the simplicial coproduct map.
    simpa [eSimplexUnit, problem20_7_5SingularChainDegreeIsoCoproduct] using
      (Sigma.map'_comp_map'
        (f := fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
        (g := fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ constantCoefficientModule R)
        (h := fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
        (p := (singularSimplexEquiv 0 (TopCat.of Unit)).symm)
        (p' := fun τ : singularSSetSimplex (TopCat.of Unit) 0 ↦
          (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) τ)
        (q := fun _ ↦ 𝟙 (constantCoefficientModule R))
        (q' := fun _ ↦ 𝟙 (constantCoefficientModule R)))
  -- Then compose with the target simplex chart to return to continuous singular simplices.
  calc
    eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
        (eSimplexUnit.inv ≫ (F.map ix).f 0) ≫ eSimplexX.hom := by
      simp [Category.assoc]
    _ =
        Sigma.map'
          (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
            (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))
          (fun _ ↦ 𝟙 (constantCoefficientModule R)) ≫ eSimplexX.hom := by
      simpa using congrArg (fun f ↦ f ≫ eSimplexX.hom) hcomp1
    _ =
        Sigma.map'
          (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
            singularSimplexEquiv 0 X
              ((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
                ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ)))
          (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
      simpa [eSimplexX, problem20_7_5SingularChainDegreeIsoCoproduct] using
        (Sigma.map'_comp_map'
          (f := fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (g := fun _ : singularSSetSimplex X 0 ↦ constantCoefficientModule R)
          (h := fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (p := fun σ : singularSimplex 0 (TopCat.of Unit) ↦
            (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))
          (p' := singularSimplexEquiv 0 X)
          (q := fun _ ↦ 𝟙 (constantCoefficientModule R))
          (q' := fun _ ↦ 𝟙 (constantCoefficientModule R)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
unique source generator to the simplex leg indexed by the constant simplex at `x`. -/
theorem pointInclusion_zeroChainSimplexLeg
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
    let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
      Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) (ContinuousMap.const _ x) := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R))
  let eSimplexUnit := singularChainDegreeIsoCoproduct (R := R) (TopCat.of Unit) 0
  let eSimplexX := singularChainDegreeIsoCoproduct (R := R) X 0
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)
  have hunit :
      uIso.inv ≫ eUnit.inv =
        Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv := by
    -- Replace the unique point generator by the unique singular `0`-simplex generator.
    simpa [uIso, eUnit, eSimplexUnit] using unitZeroChainLeg_eq_constantSimplexLeg (R := R)
  have hcoords :
      eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
        Sigma.map'
          (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
            singularSimplexEquiv 0 X
              (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
                ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))))
          (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
    -- The conjugated degree-zero chain map is exactly the simplex-indexed coproduct map.
    simpa [ix, F, eSimplexUnit, eSimplexX] using
      pointInclusionZeroChainMapInSimplexCoordinates (R := R) (X := X) x
  -- Route correction: isolate the conjugated degree-zero chain map first, then evaluate it on
  -- the unique source simplex leg and simplify the resulting constant simplex.
  calc
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom =
        (uIso.inv ≫ eUnit.inv) ≫ (F.map ix).f 0 ≫ eSimplexX.hom := by
      simp [Category.assoc]
    _ =
        (Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv) ≫
            (F.map ix).f 0 ≫ eSimplexX.hom := by
      rw [hunit]
    _ =
        Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫ eSimplexUnit.inv ≫ (F.map ix).f 0 ≫ eSimplexX.hom := by
      simp [Category.assoc]
    _ =
        Sigma.ι (fun _ : singularSimplex 0 (TopCat.of Unit) ↦ constantCoefficientModule R)
          (ContinuousMap.const _ ()) ≫
            Sigma.map'
              (fun σ : singularSimplex 0 (TopCat.of Unit) ↦
                singularSimplexEquiv 0 X
                  (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
                    ((singularSimplexEquiv 0 (TopCat.of Unit)).symm σ))))
              (fun _ ↦ 𝟙 (constantCoefficientModule R)) := by
      rw [hcoords]
    _ = Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (singularSimplexEquiv 0 X
            (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
              ((singularSimplexEquiv 0 (TopCat.of Unit)).symm (ContinuousMap.const _ ()))))) := by
      simp
    _ = Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R)
          (ContinuousMap.const _ x) := by
      -- The singular-set map of the point inclusion is postcomposition with the constant map.
      have hconst :
          singularSimplexEquiv 0 X
              (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0))
                ((singularSimplexEquiv 0 (TopCat.of Unit)).symm (ContinuousMap.const _ ())))) =
            ContinuousMap.const _ x := by
        simpa [ix, pointInclusion_eq_const] using
          (singularSimplexEquiv_map_const 0 X x (ContinuousMap.const _ ()))
      rw [hconst]

/-
  `pointInclusion_zeroChainLeg` is independent of the ambient manifold parameters, so keep the
  owner theorem free of the section-wide Chapter 20 hypotheses.
-/
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
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
  -- First expose the simplex-indexed coproduct leg, then reindex degree-zero simplices by points.
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the canonical map from degree-zero chains onto `H₀(X; R)` is
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: the degree-zero class of the `x`-indexed chain generator agrees
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
    -- Compare the two degree-zero chain maps after postcomposing with the coproduct chart.
    apply (cancel_mono eX.hom).1
    simpa [Category.assoc] using
      pointInclusion_zeroChainLeg (R := R) (X := X) x
  -- Naturality of the passage from chains to `H₀` transports the chain-level generator identity.
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
          rw [hπ]
          rfl
        _ = uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
          simp [Category.assoc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: in a path-connected space, the chosen basepoint inclusion
`Unit ⟶ X` is surjective on zeroth constant-coefficient singular homology. -/
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
  change Function.Surjective (FH.map i₀)
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
      _ = (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ δ ≫ FH.map i₀ := by
        have hβ : (Sigma.ι (fun _ : X ↦ constantCoefficientModule R) x) ≫ δ = β := by
          simpa [δ] using (Sigma.ι_desc (fun _ : X ↦ β) x)
        rw [← hβ, Category.assoc]
  -- Every `H₀(X; R)` class has a degree-zero chain representative, and `hFactor` rewrites that
  -- representative through the chosen basepoint inclusion.
  intro z
  rcases degreeZeroChains_surjective_to_rSingularHomologyZero (R := R) (X := X) z with ⟨c, hc⟩
  refine ⟨δ (eX.hom c), ?_⟩
  change ((δ ≫ FH.map i₀) (eX.hom c)) = z
  rw [← hFactor]
  simpa [α] using hc

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: a path-connected space has zeroth constant-coefficient singular
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
    -- The chosen basepoint inclusion is split by the constant retraction to the point.
    simpa [i₀, g] using
      pointInclusion_retraction_homology_split (R := R) (X := X) x₀
  have hsurj : Function.Surjective (FH.map i₀) := by
    -- Surjectivity is exactly the basepoint factorization established above.
    simpa [i₀] using pathConnectedH0BasepointInclusion_surjective (R := R) (X := X) x₀
  have hinj : Function.Injective (FH.map i₀) := by
    -- The constant retraction gives a left inverse on the underlying module map.
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
  -- Finish by comparing `H₀(X; R)` with `H₀(Unit; R)` and then using the point computation.
  exact
    ⟨hBasepoint.symm ≪≫
      Classical.choice (pointRSingularHomologyZeroIsoConstantCoefficient (R := R))⟩

/-- Problem 20.7.5 (1): under the standing compact connected boundaryless `n`-manifold
hypotheses, the zeroth `ZMod p`-homology of `M` is `ZMod p`. -/
theorem zmodSingularHomology_zero_of_connected :
    Nonempty
      (rSingularHomology (ZMod p) 0 (TopCat.of M) ≅ constantCoefficientModule (ZMod p)) := by
  -- First convert the manifold hypotheses into path connectedness.
  let _ : PathConnectedSpace M :=
    connectedClosedManifold_pathConnectedSpace
      (E := E) (H := H) (I := I) (M := M) (n := n)
  -- Then apply the generic path-connected `H₀` comparison.
  exact
    pathConnectedRSingularHomologyZeroIsoConstantCoefficient
      (R := ZMod p) (X := TopCat.of M)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: every degree of the integral singular chain complex is projective,
because it is a coproduct of copies of `ℤ` indexed by singular simplices. -/
theorem integralSingularChainDegree_projective
    (X : TopCat) (k : ℕ) :
    Projective ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X k) := by
  -- First identify degree `k` with the simplex-indexed coproduct of copies of `ℤ`.
  let e := unitSingularChainDegreeIsoCoproduct ℤ X k
  have hInt : Projective (ModuleCat.of ℤ ℤ) := by
    -- The coefficient object `ℤ` is free of rank one, hence projective.
    simpa using (ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ ℤ))
  have hCoproduct : Projective (∐ fun _ : singularSimplex k X ↦ ModuleCat.of ℤ ℤ) := by
    -- Local instance justification (typeclass bridge): the coproduct-projective instance needs
    -- projectivity for each constant `ℤ` summand.
    letI : ∀ σ : singularSimplex k X, Projective (ModuleCat.of ℤ ℤ) := fun _ ↦ hInt
    infer_instance
  -- Transport projectivity back across the canonical simplexwise coproduct comparison.
  simpa using Projective.of_iso e.symm hCoproduct

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: every degree of the integral singular chain complex is flat over
`ℤ`, so the Chapter 17 universal coefficient sequence applies to singular chains. -/
theorem integralSingularChainDegree_flat
    (X : TopCat) (k : ℕ) :
    Module.Flat ℤ ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X k) := by
  -- First promote the degree-`k` chain group to a projective object of `ModuleCat ℤ`.
  -- Local instance justification (typeclass bridge): the standard `projective => flat`
  -- instance needs the projective structure in the local instance context.
  letI :
      Projective ((((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X).X k) :=
    integralSingularChainDegree_projective (X := X) k
  -- Then the usual projective-implies-flat instance discharges the UCT side condition.
  infer_instance

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: `Tor(ℤ, N)` vanishes because `ℤ` is projective as a left
`ℤ`-module. -/
theorem torOfProjectiveLeft_isZero
    (N : ModuleCat ℤ) :
    IsZero (ModuleCat.tor ℤ (ModuleCat.of ℤ ℤ) N) := by
  let F : ModuleCat ℤ ⥤ ModuleCat ℤ :=
    (MonoidalCategory.tensoringLeft (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  letI : Module.Flat ℤ (ModuleCat.of ℤ ℤ) := by
    -- The unit module `ℤ` is free of rank one, hence projective and therefore flat.
    letI : Projective (ModuleCat.of ℤ ℤ) := by
      simpa using (ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ ℤ))
    infer_instance
  let hzero :
      IsZero
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution N).complex).homology 1) := by
    -- Exactness of `ℤ ⊗ P•` at degree `1` kills the corresponding homology object.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    simpa using
      Module.Flat.lTensor_shortComplex_exact (ModuleCat.of ℤ ℤ)
        (ShortComplex.mk
          ((CategoryTheory.projectiveResolution N).complex.d 2 1)
          ((CategoryTheory.projectiveResolution N).complex.d 1 0)
          ((CategoryTheory.projectiveResolution N).complex.d_comp_d 2 1 0))
        ((CategoryTheory.projectiveResolution N).exact_succ 0)
  -- The Chapter 17 Tor owner is exactly this first homology object.
  exact
    IsZero.of_iso hzero <|
      by
        simpa [ModuleCat.tor_def, ModuleCat.torFunctor_def, F] using
          ((CategoryTheory.projectiveResolution N).isoLeftDerivedObj F 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: if `p` does not divide `q`, then multiplication by `q` on `ZMod p`
is bijective as a `ℤ`-linear endomorphism. -/
theorem zmodIntScalar_bijective_of_not_dvd
    (hp : p.Prime) {q : ℤ} (hpq : ¬ (p : ℤ) ∣ q) :
    Function.Bijective (fun y : intZModModule p ↦ q • y) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hq : (q : ZMod p) ≠ 0 :=
    zmodIntCast_ne_zero_of_not_dvd (p := p) hpq
  have hsurj :
      Function.Surjective (fun y : ZMod p ↦ q • y) := by
    intro y
    rcases zmodIntScalar_surjective_of_not_dvd (p := p) hp hpq (y : intZModModule p) with
      ⟨y', hy'⟩
    exact ⟨(y' : ZMod p), hy'⟩
  refine ⟨?_ , hsurj⟩
  intro y₁ y₂ hy
  -- Multiply the equality by the inverse scalar in `ZMod p` to cancel `q`.
  have hy' : y₁ = y₂ ∨ (q : ZMod p) = 0 := by
    simpa [smul_smul] using
      congrArg (fun t : intZModModule p ↦ ((q : ZMod p)⁻¹ : ZMod p) • t) hy
  exact hy'.resolve_right hq

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] hBoundaryless [TopologicalSpace M] hT2 hCharted hCompact
  hConnected hManifold hDim in
/-- Helper for Problem 20.7.5: if `p ∤ q`, then multiplication by `q` is a `ℤ`-linear
automorphism of the coefficient module `ZMod p`. This is the coefficient-side unit needed in the
later UCT cleanup. -/
noncomputable def zmodIntScalarLinearEquiv_of_not_dvd
    (hp : p.Prime) {q : ℤ} (hpq : ¬ (p : ℤ) ∣ q) :
    intZModModule p ≃ₗ[ℤ] intZModModule p :=
  LinearEquiv.ofBijective
    (q • (LinearMap.id : intZModModule p →ₗ[ℤ] intZModModule p))
    (zmodIntScalar_bijective_of_not_dvd (p := p) hp hpq)

/-- Helper for Problem 20.7.5: the coefficient automorphism from
`zmodIntScalarLinearEquiv_of_not_dvd` acts by the expected scalar multiplication formula. -/
@[simp] theorem zmodIntScalarLinearEquiv_of_not_dvd_apply
    (hp : p.Prime) {q : ℤ} (hpq : ¬ (p : ℤ) ∣ q) (x : intZModModule p) :
    zmodIntScalarLinearEquiv_of_not_dvd (p := p) hp hpq x = q • x :=
  rfl

/-- Problem 20.7.5 (2): if `f : S^n → M` carries a chosen generator of `H_n(S^n; ℤ)` to `q`
times a chosen generator of `H_n(M; ℤ)` and the prime `p` does not divide `q`, then the top
`ZMod p`-homology of `M` is `ZMod p`. -/
theorem zmodSingularHomology_top_of_sphereDegree_coprime
    (hn : 0 < n) {q : ℤ}
    (f : TopCat.sphere n ⟶ TopCat.of M)
    (sphereTopIso : integralSingularHomology n (TopCat.sphere n) ≅ ModuleCat.of ℤ ℤ)
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ)
    (hfq :
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f ≫
          targetTopIso.hom =
        sphereTopIso.hom ≫ ModuleCat.ofHom (q • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
    (hp : p.Prime) (hpq : ¬ (p : ℤ) ∣ q) :
    Nonempty
      (rSingularHomology (ZMod p) n (TopCat.of M) ≅ constantCoefficientModule (ZMod p)) := by
  -- Route correction: directly importing the Chapter 20 cap-product and local-duality owners into
  -- this file still triggers the known `Books.AConciseCourseInAlgebraicTopology_May_1999/Chap09/Lemma_9_4_10.lean` frontier
  -- failure, so the remaining top-degree gap is still the local coefficient-owner comparison from
  -- `singularHomologyWithCoefficients ℤ _ (ModuleCat.of ℤ (ZMod p))`
  -- to the restricted `rSingularHomology (ZMod p)` owner.
  -- TODO for Problem 20.7.5: prove that coefficient-owner bridge, transport `hfq` through the
  -- top-degree UCT short exact sequence, and identify the induced endomorphism with
  -- multiplication by the unit `(q : ZMod p)`.
  sorry

/-- Problem 20.7.5 (3): if `f : S^n → M` carries a chosen generator of `H_n(S^n; ℤ)` to `q`
times a chosen generator of `H_n(M; ℤ)` and the prime `p` does not divide `q`, then every other
`ZMod p`-homology group of `M` vanishes. -/
theorem zmodSingularHomology_isZero_of_sphereDegree_coprime
    (hn : 0 < n) {q : ℤ}
    (f : TopCat.sphere n ⟶ TopCat.of M)
    (sphereTopIso : integralSingularHomology n (TopCat.sphere n) ≅ ModuleCat.of ℤ ℤ)
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ)
    (hfq :
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f ≫
          targetTopIso.hom =
        sphereTopIso.hom ≫ ModuleCat.ofHom (q • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
    (hp : p.Prime) (hpq : ¬ (p : ℤ) ∣ q) {k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n) :
    IsZero (rSingularHomology (ZMod p) k (TopCat.of M)) := by
  -- Route correction: the verified import frontier still blocks the direct Chapter 20 duality
  -- owners here, so the remaining obstruction is the same explicit coefficient-owner bridge as in
  -- the top-degree case, together with the above-dimension vanishing branch needed by the
  -- middle-degree integral annihilation theorem.
  -- TODO for Problem 20.7.5: combine the integral `q`-annihilation theorem with the UCT outer
  -- term cleanup, then reflect the restricted-scalar vanishing back to `rSingularHomology
  -- (ZMod p)` using `zmodModule_isZero_of_restrictScalars`.
  sorry

/-- Helper for Problem 20.7.5: the chosen top-degree integral homology identification with `ℤ`
forces every torsion class in degree `n` to vanish. -/
theorem integralSingularHomology_top_eq_zero_of_isOfFinAddOrder
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ)
    (x : integralSingularHomology n (TopCat.of M)) (hx : IsOfFinAddOrder x) :
    x = 0 := by
  -- Transport the torsion class across the chosen top-degree identification.
  have hx' : IsOfFinAddOrder (targetTopIso.hom x) := by
    rw [isOfFinAddOrder_iff_zsmul_eq_zero] at hx ⊢
    rcases hx with ⟨m, hmpos, hmx⟩
    refine ⟨m, hmpos, ?_⟩
    simpa using congrArg targetTopIso.hom hmx
  -- The additive group underlying `ℤ` is torsion-free, so the transported class is zero.
  have hzero : targetTopIso.hom x = 0 := by
    by_contra hx0
    exact not_isOfFinAddOrder_of_isAddTorsionFree hx0 hx'
  -- Cancel the chosen isomorphism to return to the original homology group.
  calc
    x = targetTopIso.inv.hom (targetTopIso.hom x) := by
      simp
    _ = 0 := by
      rw [hzero]
      simp

/-- Helper for Problem 20.7.5: a connected closed manifold has zeroth integral singular homology
`ℤ`. -/
theorem integralSingularHomologyZeroIsoInt_of_connectedClosedManifold :
    Nonempty (integralSingularHomology 0 (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  -- First replace connectedness by the path-connected `H₀` comparison from Chapter 20.
  let _ : PathConnectedSpace M :=
    connectedClosedManifold_pathConnectedSpace
      (E := E) (H := H) (I := I) (M := M) (n := n)
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.of M) 0 with ⟨hInt⟩
  rcases
      pathConnectedRSingularHomologyZeroIsoConstantCoefficient
        (R := ℤ) (X := TopCat.of M) with ⟨hZero⟩
  -- Then transport the Chapter 20 constant coefficient owner back to the ordinary `ℤ`-module.
  exact ⟨hInt ≪≫ hZero ≪≫ constantCoefficientModuleIsoInt⟩

/-- Helper for Problem 20.7.5: the `Tor(H₀(M; ℤ), ZMod p)` term vanishes because connected closed
manifolds have `H₀(M; ℤ) ≅ ℤ`. -/
theorem torIntegralHomologyZeroZMod_isZero
    (p : ℕ) :
    IsZero
      (ModuleCat.tor ℤ (integralSingularHomology 0 (TopCat.of M)) (ModuleCat.of ℤ (ZMod p))) := by
  rcases integralSingularHomologyZeroIsoInt_of_connectedClosedManifold
      (E := E) (H := H) (I := I) (M := M) (n := n) with ⟨e₀⟩
  -- Transport the left Tor input across the canonical `H₀(M; ℤ) ≅ ℤ` comparison.
  exact
    IsZero.of_iso
      (torOfProjectiveLeft_isZero (N := ModuleCat.of ℤ (ZMod p)))
      (((ModuleCat.torFunctor ℤ).mapIso e₀).app (ModuleCat.of ℤ (ZMod p)))

/-- Helper for Problem 20.7.5: every torsion class in `H₀(M; ℤ)` vanishes once the generic
path-connected-space identification `H₀(X; ℤ) ≅ ℤ` is available. -/
theorem integralSingularHomology_zero_eq_zero_of_isOfFinAddOrder
    (x : integralSingularHomology 0 (TopCat.of M)) (hx : IsOfFinAddOrder x) :
    x = 0 := by
  -- First identify `H₀(M; ℤ)` with the standard torsion-free module `ℤ`.
  rcases integralSingularHomologyZeroIsoInt_of_connectedClosedManifold
      (E := E) (H := H) (I := I) (M := M) (n := n) with ⟨hIso⟩
  -- Transport the torsion class across that isomorphism.
  have hx' : IsOfFinAddOrder (hIso.hom x) := by
    rw [isOfFinAddOrder_iff_zsmul_eq_zero] at hx ⊢
    rcases hx with ⟨m, hmpos, hmx⟩
    refine ⟨m, hmpos, ?_⟩
    simpa using congrArg hIso.hom hmx
  -- Torsion-freeness of `ℤ` forces the transported class to vanish.
  have hzero : hIso.hom x = 0 := by
    by_contra hx0
    exact not_isOfFinAddOrder_of_isAddTorsionFree hx0 hx'
  -- Cancel the chosen isomorphism to conclude in `H₀(M; ℤ)`.
  calc
    x = hIso.inv.hom (hIso.hom x) := by
      simp
    _ = 0 := by
      rw [hzero]
      simp

/-- Helper for Problem 20.7.5: in every middle degree `0 < k < n`, the sphere-degree `q`
annihilates integral homology classes of `M`. -/
theorem zsmul_eq_zero_middle_integralHomology_of_sphereDegree
    (hn : 0 < n) {q : ℤ}
    (f : TopCat.sphere n ⟶ TopCat.of M)
    (sphereTopIso : integralSingularHomology n (TopCat.sphere n) ≅ ModuleCat.of ℤ ℤ)
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ)
    (hfq :
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f ≫
          targetTopIso.hom =
        sphereTopIso.hom ≫ ModuleCat.ofHom (q • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
    {k : ℕ} (hk0 : k ≠ 0) (hkn : k ≠ n)
    (x : integralSingularHomology k (TopCat.of M)) :
    q • x = 0 := by
  -- Route correction: the middle-degree proof still has the same fixed skeleton, but the direct
  -- Chapter 20 imports needed for the constant-coefficient cap-product adapter are blocked by the
  -- verified `Lemma_9_4_10` frontier failure. The unresolved parts are therefore the comparison
  -- from those chosen-model duality maps to `capWithFundamentalClass`, and the independent
  -- above-dimension vanishing branch for `k > n`.
  -- TODO for Problem 20.7.5: surface the constant-coefficient `capWithFundamentalClass` adapter
  -- without crossing the broken import frontier, then split the proof into the `n < k` branch
  -- (dimension vanishing) and the `k < n` branch (surjectivity of cap with the chosen
  -- fundamental class plus sphere off-top vanishing).
  sorry

/-- Problem 20.7.5 (4): if `f : S^n → M` carries a chosen generator of `H_n(S^n; ℤ)` to `q`
times a chosen generator of `H_n(M; ℤ)` and `x` is torsion in an integral singular homology group
of `M`, then the same degree `q` annihilates `x`. -/
theorem zsmul_eq_zero_of_isOfFinAddOrder_of_sphereDegree
    (hn : 0 < n) {q : ℤ}
    (f : TopCat.sphere n ⟶ TopCat.of M)
    (sphereTopIso : integralSingularHomology n (TopCat.sphere n) ≅ ModuleCat.of ℤ ℤ)
    (targetTopIso : integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ)
    (hfq :
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f ≫
          targetTopIso.hom =
        sphereTopIso.hom ≫ ModuleCat.ofHom (q • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
    {k : ℕ}
    (x : integralSingularHomology k (TopCat.of M)) (hx : IsOfFinAddOrder x) :
    q • x = 0 := by
  -- Split off the top degree, where the chosen `ℤ`-generator already forces torsion to vanish.
  by_cases hkn : k = n
  · subst hkn
    have hx0 : x = 0 :=
      integralSingularHomology_top_eq_zero_of_isOfFinAddOrder
        (E := E) (H := H) (I := I) (M := M) (n := k) targetTopIso x hx
    rw [hx0]
    exact zsmul_zero q
  -- Then isolate the degree-zero case, whose only remaining input is the generic `H₀` bridge.
  by_cases hk0 : k = 0
  · subst hk0
    have hx0 : x = 0 :=
      integralSingularHomology_zero_eq_zero_of_isOfFinAddOrder
        (E := E) (H := H) (I := I) (M := M) (n := n) x hx
    rw [hx0]
    exact zsmul_zero q
  -- Every remaining degree is middle-dimensional, so the stronger annihilation helper applies.
  exact
    zsmul_eq_zero_middle_integralHomology_of_sphereDegree
      (E := E) (H := H) (I := I) (M := M) (n := n)
      hn f sphereTopIso targetTopIso hfq hk0 hkn x

end
