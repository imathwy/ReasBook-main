import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Subpath
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Homology

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped ContinuousMap Manifold Topology

noncomputable section

-- Chapter 13 already fixes `integralSingularHomology` as the canonical owner for ordinary
-- singular homology, mathlib uses `ContinuousMap.HomotopyEquiv` for homotopy equivalence, and
-- the local project models the suspension hypothesis through `reducedSuspension`.

section

variable {n : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I 0 M]

namespace CompactManifold

/-- Helper for Problem 20.7.6: the singular simplicial set of `X` in degree `n`. This keeps the
degree-zero chain calculations independent of the heavier Chapter 18 cochain file. -/
private abbrev singularSSetSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X) _⦋n⦌

/-- Helper for Problem 20.7.6: degree-`n` singular chains are the coproduct of one copy of `R`
for each singular `n`-simplex. This is the only Chapter 18 API needed below, so we keep the
owner-local version here to avoid the broken broader import chain. -/
noncomputable def singularChainDegreeIsoCoproduct
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).obj X).X n) ≅
      ∐ fun _ : singularSimplex n X ↦ constantCoefficientModule R :=
  (eqToIso rfl) ≪≫
    show (∐ fun _ : singularSSetSimplex X n ↦ constantCoefficientModule R) ≅
        ∐ fun _ : singularSimplex n X ↦ constantCoefficientModule R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv n X)
        (fun _ ↦ Iso.refl (constantCoefficientModule R))

/-- Helper for Problem 20.7.6: in degree `n`, the singular-chain map induced by `f` is the
coproduct map on singular `n`-simplices. -/
theorem singularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (constantCoefficientModule R)).map f).f n) =
      Sigma.map'
        (fun σ : singularSSetSimplex X n ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ)
        (fun _ ↦ 𝟙 (constantCoefficientModule R)) :=
  rfl

/-- Helper for Problem 20.7.6: the direct unit-coefficient singular chain group in degree `n` is
the coproduct of one copy of `R` for each singular `n`-simplex. This keeps the projective/flat
chain arguments on the ordinary unit-coefficient owner needed by later UCT steps. -/
private noncomputable def unitSingularChainDegreeIsoCoproduct
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X).X n) ≅
      ∐ fun _ : singularSimplex n X ↦ ModuleCat.of R R :=
  (eqToIso rfl) ≪≫
    show (∐ fun _ : singularSSetSimplex X n ↦ ModuleCat.of R R) ≅
        ∐ fun _ : singularSimplex n X ↦ ModuleCat.of R R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv n X)
        (fun _ ↦ Iso.refl (ModuleCat.of R R))

/-- Helper for Problem 20.7.6: every point of `Σ X` is joined to the suspension basepoint by a
subpath of its meridian. -/
theorem suspensionJoinedToBasepoint
    (X : PointedCompactlyGenerated) (y : (Σ X).toCompactlyGenerated) :
    Joined (reducedSuspensionPoint X) y := by
  rcases Quotient.exists_rep y with ⟨p, rfl⟩
  let scaledHeight : unitInterval → unitInterval :=
    fun t ↦ ⟨t * p.2, unitInterval.mul_mem t.2 p.2.2⟩
  have hscaled : Continuous scaledHeight := by
    exact Continuous.subtype_mk (continuous_subtype_val.mul continuous_const)
      (fun t ↦ unitInterval.mul_mem t.2 p.2.2)
  -- Follow the meridian only up to the representative height `p.2`.
  refine ⟨?_⟩
  refine
    { toFun := fun t ↦ (reducedSuspensionMk X (p.1, scaledHeight t) :
        (Σ X).toCompactlyGenerated)
      continuous_toFun := (continuous_reducedSuspensionMk_meridian X p.1).comp hscaled
      source' := ?_
      target' := ?_ }
  · simp [scaledHeight]
  · have h1 : scaledHeight 1 = p.2 := by
      simp [scaledHeight]
    rw [h1]
    rfl

/-- Helper for Problem 20.7.6: every reduced suspension is path connected. -/
theorem suspensionPathConnectedSpace
    (X : PointedCompactlyGenerated) :
    PathConnectedSpace ((Σ X).toCompactlyGenerated) := by
  refine ⟨⟨reducedSuspensionPoint X⟩, ?_⟩
  intro y z
  -- Join both endpoints to the distinguished suspension basepoint and concatenate the paths.
  exact (suspensionJoinedToBasepoint X y).symm.trans (suspensionJoinedToBasepoint X z)

/-- Helper for Problem 20.7.6: a compact manifold homotopy equivalent to a reduced suspension is
path connected. -/
theorem manifoldPathConnectedSpace_of_homotopyEquivSuspension
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated)) :
    PathConnectedSpace M := by
  rcases h_susp with ⟨X, ⟨e⟩⟩
  let _ : PathConnectedSpace ((Σ X).toCompactlyGenerated) := suspensionPathConnectedSpace X
  let hleft : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id M) :=
    Classical.choice e.left_inv
  refine ⟨⟨e.symm (reducedSuspensionPoint X)⟩, ?_⟩
  intro x x'
  have hx : Joined x (e.symm (e x)) := by
    -- The left homotopy inverse gives a path from `x` to the comparison point `e.symm (e x)`.
    exact (show Joined (e.symm (e x)) x from ⟨hleft.evalAt x⟩).symm
  have hcore : Joined (e.symm (e x)) (e.symm (e x')) := by
    -- Transport a path in the suspension back along the chosen homotopy inverse.
    exact ⟨(PathConnectedSpace.somePath (e x) (e x')).map e.symm.continuous⟩
  have hx' : Joined (e.symm (e x')) x' := by
    -- The same homotopy inverse closes the path at the second endpoint.
    exact ⟨hleft.evalAt x'⟩
  exact hx.trans (hcore.trans hx')

/-- Helper for Problem 20.7.6: positive-dimensional spheres are path connected. -/
theorem spherePathConnectedSpace_of_pos
    (hn : 0 < n) :
    PathConnectedSpace (TopCat.sphere n) := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n + 1 := by
      simpa using Nat.succ_le_succ hn
    have hcard : 1 < (n + 1 : Cardinal) := by
      exact_mod_cast hnat
    simpa using hcard
  change PathConnectedSpace (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
    -- The ordinary Euclidean sphere is path connected in positive dimension.
    exact isPathConnected_iff_pathConnectedSpace.mp <| by
      simpa using
        (isPathConnected_sphere
          hdim
          (0 : EuclideanSpace ℝ (Fin (n + 1)))
          (by norm_num : 0 ≤ (1 : ℝ)))
  -- `TopCat.sphere n` is the `ULift` of the ordinary Euclidean sphere.
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

/-- Helper for Problem 20.7.6: a path-connected space has a unique path component. -/
theorem pathConnected_uniqueZerothHomotopy
    (X : Type _) [TopologicalSpace X] [PathConnectedSpace X] :
    Nonempty (Unique (ZerothHomotopy X)) := by
  -- Convert path connectedness into the standard nonempty-plus-subsingleton description of `π₀`.
  rcases (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp inferInstance with
    ⟨hne, hsub⟩
  rcases hne with ⟨x⟩
  -- Then package the unique path component into the target `Unique` witness.
  exact ⟨{ default := x, uniq := fun y ↦ hsub.elim y x }⟩

/-- Helper for Problem 20.7.6: a compact manifold homotopy equivalent to a reduced suspension has
exactly one path component. -/
theorem manifoldUniqueZerothHomotopy_of_homotopyEquivSuspension
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated)) :
    Nonempty (Unique (ZerothHomotopy M)) := by
  let _ : PathConnectedSpace M :=
    manifoldPathConnectedSpace_of_homotopyEquivSuspension (M := M) h_susp
  -- Reduce the manifold statement to the generic path-connected-space owner.
  exact pathConnected_uniqueZerothHomotopy (X := M)

/-- Helper for Problem 20.7.6: a positive-dimensional sphere has exactly one path component. -/
theorem sphereUniqueZerothHomotopy_of_pos
    (hn : 0 < n) :
    Nonempty (Unique (ZerothHomotopy (TopCat.sphere n))) := by
  let _ : PathConnectedSpace (TopCat.sphere n) := spherePathConnectedSpace_of_pos hn
  -- Reduce the sphere statement to the generic path-connected-space owner.
  exact pathConnected_uniqueZerothHomotopy (X := TopCat.sphere n)

/-- Helper for Problem 20.7.6: two zero objects in a pointed category are canonically
isomorphic. -/
theorem isoOfIsZero
    {C : Type _} [Category C] [Limits.HasZeroObject C] {A B : C}
    (hA : IsZero A) (hB : IsZero B) :
    Nonempty (A ≅ B) := by
  -- Compare both objects with the distinguished zero object and compose the resulting
  -- isomorphisms.
  exact ⟨hA.isoZero ≪≫ hB.isoZero.symm⟩

/-- Helper for Problem 20.7.6: the Chapter 20 coefficient owner `constantCoefficientModule ℤ` is
canonically the ordinary unit `ℤ`-module. -/
noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- Helper for Problem 20.7.6: ordinary integral singular homology agrees with the Chapter 20
owner `rSingularHomology ℤ` in every degree. -/
theorem integralSingularHomologyIsoRSingularHomology
    (X : TopCat) (k : ℕ) :
    Nonempty (integralSingularHomology k X ≅ rSingularHomology ℤ k X) := by
  -- Compare both degree-`k` owners with the same singular-chain homology object.
  refine ⟨?_⟩
  simpa [integralSingularHomology, rSingularHomology] using
    (((singularHomologyFunctor (ModuleCat ℤ) k).mapIso
      constantCoefficientModuleIsoInt).app X).symm

/-- Helper for Problem 20.7.6: a unique path component gives path connectedness. -/
theorem pathConnectedSpace_of_uniqueZerothHomotopy
    (X : Type _) [TopologicalSpace X]
    (hπ0 : Nonempty (Unique (ZerothHomotopy X))) :
    PathConnectedSpace X := by
  rcases hπ0 with ⟨hUnique⟩
  let _ : Unique (ZerothHomotopy X) := hUnique
  -- Repackage the unique path component into the standard path-connectedness criterion.
  exact (pathConnectedSpace_iff_zerothHomotopy (X := X)).2 ⟨⟨default⟩, inferInstance⟩

/-- Helper for Problem 20.7.6: the zeroth constant-coefficient singular homology of a point is the
coefficient module itself. -/
theorem pointRSingularHomologyZeroIsoConstantCoefficient
    (R : Type) [CommRing R] :
    Nonempty (rSingularHomology R 0 (TopCat.of Unit) ≅ constantCoefficientModule R) := by
  -- Compute `H₀` of the point by the totally disconnected-space calculation.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat R) (R := constantCoefficientModule R) (X := TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)

/-- Helper for Problem 20.7.6: a singular `0`-simplex is determined by its unique vertex, so
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

/-- Helper for Problem 20.7.6: the constant singular `0`-simplex at `x` maps to `x` under the
degree-zero simplex/point equivalence. -/
@[simp] theorem singularSimplexZeroEquiv_apply_const
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexZeroEquiv X (ContinuousMap.const _ x) = x :=
  by
    -- Evaluate the canonical degree-zero equivalence on the constant singular simplex.
    change TopCat.toSSetObj₀Equiv
        ((singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x)) = x
    rfl

/-- Helper for Problem 20.7.6: the inverse of the degree-zero simplex/point equivalence is the
constant singular simplex. -/
@[simp] theorem singularSimplexZeroEquiv_symm_apply
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexZeroEquiv X).symm x = ContinuousMap.const _ x := by
  apply (singularSimplexZeroEquiv X).injective
  simp

/-- Helper for Problem 20.7.6: the inverse singular-simplex equivalence in degree `0` sends the
constant singular simplex at `x` to the corresponding singular-set `0`-simplex. -/
@[simp] theorem singularSimplexEquiv_symm_apply_const_zero
    (X : Type _) [TopologicalSpace X] (x : X) :
    (singularSimplexEquiv 0 (TopCat.of X)).symm (ContinuousMap.const _ x) =
      TopCat.toSSetObj₀Equiv.symm x :=
  rfl

/-- Helper for Problem 20.7.6: the forward singular-simplex equivalence in degree `0` sends the
singular-set `0`-simplex at `x` to the constant singular simplex at `x`. -/
@[simp] theorem singularSimplexEquiv_apply_toSSetObjZero
    (X : Type _) [TopologicalSpace X] (x : X) :
    singularSimplexEquiv 0 (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) =
      ContinuousMap.const _ x := by
  simpa [singularSimplexZeroEquiv] using singularSimplexZeroEquiv_symm_apply (X := X) x

/-- Helper for Problem 20.7.6: under `singularSimplexEquiv`, the simplicial map induced by the
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

/-- Helper for Problem 20.7.6: degree-zero singular chains are the coproduct of one copy of `R`
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

/-- Helper for Problem 20.7.6: reindexing the degree-zero simplex coproduct by points sends the
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

/-- Helper for Problem 20.7.6: the chosen point inclusion `Unit ⟶ X` is the canonical constant
map at `x`. -/
@[simp] theorem pointInclusion_eq_const
    (X : TopCat) (x : X) :
    TopCat.ofHom (ContinuousMap.const Unit x) = TopCat.const (X := TopCat.of Unit) x :=
  rfl

/-- Helper for Problem 20.7.6: the inverse of the unique-index coproduct is the unique coproduct
leg. -/
@[simp] theorem coproductUniqueIso_inv_eq_unitLeg
    (R : Type) [CommRing R] :
    (coproductUniqueIso (fun _ : Unit ↦ constantCoefficientModule R)).inv =
      Sigma.ι (fun _ : Unit ↦ constantCoefficientModule R) () := by
  -- The `simps` formula for `coproductUniqueIso` already identifies the inverse with the unique
  -- colimit injection.
  simp [coproductUniqueIso_inv]

/-- Helper for Problem 20.7.6: for `TopCat.of Unit`, the inverse of the degree-zero point chart
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

/-- Helper for Problem 20.7.6: precomposing the simplex coproduct chart inverse with a simplex
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

/-- Helper for Problem 20.7.6: postcomposing a singular-set leg with the simplex coproduct chart
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

/-- Helper for Problem 20.7.6: before reindexing degree-zero simplices by points, the point
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
      Sigma.ι (fun _ : singularSimplex 0 X ↦ constantCoefficientModule R) (ContinuousMap.const _ x) := by
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
        simpa [σUnit, σX] using
          (singularSimplexEquiv_map_const 0 X x (ContinuousMap.const _ ()))
      rw [hConst]

/-- Helper for Problem 20.7.6: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
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
  -- First normalize the chain map to the simplex-indexed coproduct, then reindex simplices by
  -- points using the canonical degree-zero equivalence.
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

/-- Helper for Problem 20.7.6: the canonical map from degree-zero chains onto `H₀(X; R)` is
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

/-- Helper for Problem 20.7.6: the degree-zero class of the `x`-indexed chain generator agrees
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
          change uIso.inv ≫ eUnit.inv ≫ ((F.map ix).f 0 ≫ πX) =
            uIso.inv ≫ eUnit.inv ≫ (πUnit ≫ FH.map ix)
          exact congrArg (fun f ↦ uIso.inv ≫ eUnit.inv ≫ f) hπ
        _ = uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
          simp [Category.assoc]

/-- Helper for Problem 20.7.6: a path between `x` and `y` identifies the two induced maps on
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

/-- Helper for Problem 20.7.6: in a path-connected space, every point inclusion `Unit ⟶ X`
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

/-- Helper for Problem 20.7.6: the inclusion of a chosen basepoint splits after applying zeroth
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

/-- Helper for Problem 20.7.6: in a path-connected space, the chosen basepoint inclusion
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

/-- Helper for Problem 20.7.6: once the chain-level degree-zero surjectivity package is surfaced,
a path-connected space has zeroth constant-coefficient singular homology equal to the coefficient
module. -/
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
  -- Finish by comparing with the already computed point homology.
  exact
    ⟨hBasepoint.symm ≪≫
      Classical.choice (pointRSingularHomologyZeroIsoConstantCoefficient (R := R))⟩

/-- Helper for Problem 20.7.6: a unique path component identifies integral `H₀` with `ℤ`. -/
theorem zeroIntegralSingularHomologyIsoInt_of_uniqueZerothHomotopy
    (X : TopCat) (hπ0 : Nonempty (Unique (ZerothHomotopy X))) :
    Nonempty (integralSingularHomology 0 X ≅ ModuleCat.of ℤ ℤ) := by
  let _ : PathConnectedSpace X := pathConnectedSpace_of_uniqueZerothHomotopy X hπ0
  -- First replace ordinary integral homology by `rSingularHomology ℤ`, then apply the generic
  -- path-connected-space `H₀` package and collapse the coefficient owner to `ℤ`.
  rcases integralSingularHomologyIsoRSingularHomology X 0 with ⟨hInt⟩
  rcases pathConnectedRSingularHomologyZeroIsoConstantCoefficient
      (R := ℤ) (X := X) with ⟨hZero⟩
  exact ⟨hInt ≪≫ hZero ≪≫ constantCoefficientModuleIsoInt⟩

/-- Helper for Problem 20.7.6: every degree of the unit-coefficient integral singular chain
complex is projective, because it is a coproduct of copies of `ℤ` indexed by singular simplices. -/
theorem integralSingularChainDegreeProjective
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

/-- Helper for Problem 20.7.6: every degree of the unit-coefficient integral singular chain
complex is flat over `ℤ`, so the Chapter 17 universal coefficient sequence applies once the
remaining owner bridges are available. -/
theorem integralSingularChainDegreeFlat
    (X : TopCat) (k : ℕ) :
    Module.Flat ℤ ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X k) := by
  -- First promote the degree-`k` chain group to a projective object of `ModuleCat ℤ`.
  -- Local instance justification (typeclass bridge): the standard `projective => flat`
  -- instance needs the projective structure in the local instance context.
  letI :
      Projective ((((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X).X k) :=
    integralSingularChainDegreeProjective (X := X) k
  -- Then the usual projective-implies-flat instance discharges the UCT side condition.
  infer_instance

/-- Helper for Problem 20.7.6: the remaining manifold-side closing package should bundle middle
integral homology vanishing and the top-degree `ℤ` computation. -/
theorem middleIntegralHomologyIsZero_of_homotopyEquivSuspension
    (h_dim : Module.finrank ℝ E = n) (hn : 0 < n)
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated))
    {k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    IsZero (integralSingularHomology k (TopCat.of M)) := by
  -- Route correction: the old smooth-orientation route mismatched the theorem surface
  -- `[IsManifold I 0 M]`. The next proof must instead use an intrinsic `IsRFundamentalClass`
  -- witness, then combine the Chapter 20 pairing with the suspension cup-product vanishing.
  -- TODO for Problem 20.7.6: obtain a field-valued intrinsic fundamental class on the actual
  -- `C⁰` manifold surface, use it to force middle field cohomology to vanish, and finish by the
  -- Chapter 17 UCT cleanup on integral chains.
  admit

/-- Helper for Problem 20.7.6: the top integral homology of the manifold is `ℤ` once the
middle-degree vanishing and intrinsic topological fundamental class are surfaced. -/
theorem topIntegralHomologyIsoInt_of_homotopyEquivSuspension
    (h_dim : Module.finrank ℝ E = n) (hn : 0 < n)
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated)) :
    Nonempty (integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  -- Route correction: the top-degree branch should be finished on the intrinsic Chapter 20
  -- `IsRFundamentalClass` owner rather than by importing the smooth-orientation package.
  -- TODO for Problem 20.7.6: once the intrinsic `C⁰` fundamental class exists, use the
  -- top-degree Poincare comparison and UCT torsion-freeness to identify `H_n(M; ℤ)` with `ℤ`.
  admit

/-- Helper for Problem 20.7.6: the remaining manifold-side closing package is the conjunction of
the middle-degree vanishing and the top-degree `ℤ` computation. -/
theorem integralMiddleZero_and_topIsoInt_of_homotopyEquivSuspension
    (h_dim : Module.finrank ℝ E = n) (hn : 0 < n)
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated)) :
    (∀ {k : ℕ}, 0 < k → k < n → IsZero (integralSingularHomology k (TopCat.of M))) ∧
      Nonempty (integralSingularHomology n (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨?_, ?_⟩
  · intro k hk0 hkn
    -- The middle-degree branch is now isolated as its own intrinsic `C⁰` duality/UCT helper.
    exact
      middleIntegralHomologyIsZero_of_homotopyEquivSuspension
        (M := M) h_dim hn h_susp hk0 hkn
  · -- The top-degree branch is packaged separately so the remaining blocker is no longer hidden
    -- inside the middle-degree vanishing proof.
    exact topIntegralHomologyIsoInt_of_homotopyEquivSuspension (M := M) h_dim hn h_susp

/-- Helper for Problem 20.7.6: above the manifold dimension, integral singular homology should
vanish once the topological Chapter 20 owner is surfaced. -/
theorem isZeroRSingularHomology_of_gt_dimension_c0
    (h_dim : Module.finrank ℝ E = n) {k : ℕ} (hkn : n < k) :
    IsZero (rSingularHomology ℤ k (TopCat.of M)) := by
  -- Route correction: this branch should be proved directly on the Chapter 20 owner
  -- `rSingularHomology ℤ` by the local compact-support plus Mayer-Vietoris argument from 20.4.x,
  -- and only then transported back to `integralSingularHomology`.
  -- TODO for Problem 20.7.6: reduce an arbitrary class to compact support, cover it by finitely
  -- many chart domains, use the Euclidean vanishing theorem on each chart, and run the
  -- Mayer-Vietoris induction on that finite cover.
  admit

/-- Helper for Problem 20.7.6: above the manifold dimension, the ordinary integral owner vanishes
after transporting the Chapter 20 `rSingularHomology` vanishing statement. -/
theorem isZeroIntegralHomology_of_gt_dimension
    (h_dim : Module.finrank ℝ E = n) {k : ℕ} (hkn : n < k) :
    IsZero (integralSingularHomology k (TopCat.of M)) := by
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.of M) k with ⟨hCompare⟩
  -- First prove the above-dimension vanishing on the Chapter 20 owner `rSingularHomology ℤ`.
  let hZeroR : IsZero (rSingularHomology ℤ k (TopCat.of M)) :=
    isZeroRSingularHomology_of_gt_dimension_c0 (M := M) h_dim hkn
  -- Then transport the vanishing result back to the ordinary integral singular homology owner.
  exact IsZero.of_iso hZeroR hCompare

/-- Helper for Problem 20.7.6: a positive-dimensional sphere has integral homology concentrated in
degrees `0` and `n`, with top degree `ℤ`. -/
theorem sphereIntegralHomologyPattern_of_pos
    (hn : 0 < n) :
    Nonempty (integralSingularHomology n (TopCat.sphere n) ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ {k : ℕ}, 0 < k → k < n → IsZero (integralSingularHomology k (TopCat.sphere n))) ∧
      (∀ {k : ℕ}, n < k → IsZero (integralSingularHomology k (TopCat.sphere n))) := by
  -- The sphere-side comparison is kept as a single frontier package so this item no longer
  -- depends on the broken Chapter 14/15 Moore-space import chain during local checking.
  admit

/-- Problem 20.7.6: if a compact positive-dimensional `n`-manifold is homotopy equivalent to a
suspension, then its integral singular homology groups are those of `S^n`. In the current
project the suspension is formalized by the canonical reduced-suspension notation `Σ X`, and the
sphere is the canonical object `TopCat.sphere n`. -/
theorem integralSingularHomologyIsoSphere_of_homotopyEquivSuspension
    (h_dim : Module.finrank ℝ E = n) (hn : 0 < n)
    (h_susp : ∃ X : PointedCompactlyGenerated,
      Nonempty (M ≃ₕ (Σ X).toCompactlyGenerated)) (k : ℕ) :
    Nonempty (integralSingularHomology k (TopCat.of M) ≅
      integralSingularHomology k (TopCat.sphere n)) := by
  let _ : PathConnectedSpace M := manifoldPathConnectedSpace_of_homotopyEquivSuspension
    (M := M) h_susp
  -- Route correction: the proof is now split by degree so the remaining missing API is explicit.
  by_cases hk0 : k = 0
  · subst hk0
    -- Compare both zeroth homology groups with the standard owner `ℤ`.
    rcases
        zeroIntegralSingularHomologyIsoInt_of_uniqueZerothHomotopy
          (X := TopCat.of M)
          (manifoldUniqueZerothHomotopy_of_homotopyEquivSuspension
            (M := M) h_susp) with ⟨hM⟩
    rcases
        zeroIntegralSingularHomologyIsoInt_of_uniqueZerothHomotopy
          (X := TopCat.sphere n)
          (sphereUniqueZerothHomotopy_of_pos (n := n) hn) with ⟨hS⟩
    exact ⟨hM ≪≫ hS.symm⟩
  by_cases hkn : k = n
  · subst hkn
    -- Route correction: the top-degree branch should come from the intrinsic manifold-side
    -- closing package, together with the sphere-side top-degree computation.
    rcases integralMiddleZero_and_topIsoInt_of_homotopyEquivSuspension
        (M := M) h_dim hn h_susp with ⟨_, hM⟩
    rcases sphereIntegralHomologyPattern_of_pos hn with ⟨hS, _, _⟩
    rcases hM with ⟨hM⟩
    rcases hS with ⟨hS⟩
    exact ⟨hM ≪≫ hS.symm⟩
  by_cases hlt : k < n
  · -- Route correction: the middle-degree branch should come from the intrinsic fundamental-class
    -- pairing route packaged in `integralMiddleZero_and_topIsoInt_of_homotopyEquivSuspension`.
    have hMiddle :
        ∀ {j : ℕ}, 0 < j → j < n → IsZero (integralSingularHomology j (TopCat.of M)) :=
      (integralMiddleZero_and_topIsoInt_of_homotopyEquivSuspension
        (M := M) h_dim hn h_susp).1
    let hMzero : IsZero (integralSingularHomology k (TopCat.of M)) :=
      hMiddle (show 0 < k from Nat.pos_of_ne_zero hk0) hlt
    let hSzero : IsZero (integralSingularHomology k (TopCat.sphere n)) :=
      (sphereIntegralHomologyPattern_of_pos (n := n) hn).2.1
        (show 0 < k from Nat.pos_of_ne_zero hk0) hlt
    exact isoOfIsZero hMzero hSzero
  · have hgt : n < k := by
      have hnk : n ≠ k := by
        intro hnk
        exact hkn hnk.symm
      exact lt_of_le_of_ne (Nat.le_of_not_gt hlt) hnk
    let hMzero : IsZero (integralSingularHomology k (TopCat.of M)) :=
      isZeroIntegralHomology_of_gt_dimension (M := M) h_dim hgt
    let hSzero : IsZero (integralSingularHomology k (TopCat.sphere n)) :=
      (sphereIntegralHomologyPattern_of_pos (n := n) hn).2.2 hgt
    exact isoOfIsZero hMzero hSzero

end CompactManifold

end
