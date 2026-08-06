import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_1_1

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Topology
open Simplicial

noncomputable section

private theorem isZero_finZeroModule : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
  letI : Subsingleton (Fin 0 → ℤ) := by infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Problem 13.6.4: every positive-dimensional topological sphere is path connected. -/
private theorem spherePathConnectedSpace_of_pos {n : ℕ} (hn : 0 < n) :
    PathConnectedSpace (TopCat.sphere n) := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n + 1 := by
      simpa using Nat.succ_le_succ hn
    have hcard : 1 < (n + 1 : Cardinal) := by
      exact_mod_cast hnat
    simpa using hcard
  -- Reduce `TopCat.sphere n` to the ordinary Euclidean sphere, where mathlib supplies the
  -- path-connectedness theorem in positive dimension.
  change PathConnectedSpace (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
    exact isPathConnected_iff_pathConnectedSpace.mp <| by
      simpa using
        (isPathConnected_sphere
          hdim
          (0 : EuclideanSpace ℝ (Fin (n + 1)))
          (by norm_num : 0 ≤ (1 : ℝ)))
  -- The topological sphere is just the `ULift` of that Euclidean sphere.
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

/-- Helper for Problem 13.6.4: the product of two positive-dimensional spheres is path
connected. -/
private theorem sphereProductPathConnectedSpace_of_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    PathConnectedSpace (TopCat.of (TopCat.sphere m × TopCat.sphere n)) := by
  -- Put the factorwise path-connectedness instances in scope and build the product path
  -- pointwise from the factorwise paths.
  let _ : PathConnectedSpace (TopCat.sphere m) := spherePathConnectedSpace_of_pos hm
  let _ : PathConnectedSpace (TopCat.sphere n) := spherePathConnectedSpace_of_pos hn
  rcases (PathConnectedSpace.nonempty : Nonempty (TopCat.sphere m)) with ⟨x₀⟩
  rcases (PathConnectedSpace.nonempty : Nonempty (TopCat.sphere n)) with ⟨y₀⟩
  refine ⟨⟨x₀, y₀⟩, ?_⟩
  intro x y
  exact ⟨(PathConnectedSpace.somePath x.1 y.1).prod (PathConnectedSpace.somePath x.2 y.2)⟩

/-- Helper for Problem 13.6.4: the degree-zero unit-coefficient singular chains of `X` are the
coproduct of one copy of `R` for each point of `X`. -/
private abbrev unitCoefficientSingularChainDegree
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) : ModuleCat R :=
  ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X).X n)

/-- Helper for Problem 13.6.4: the `n`-simplices of the singular simplicial set of `X`. -/
private abbrev singularSSetSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Helper for Problem 13.6.4: degree-zero singular chains are the coproduct of one copy of `R`
for each point of `X`. -/
private noncomputable def singularChainDegreeZeroIsoPointCoproduct
    (R : Type) [CommRing R] (X : TopCat) :
    unitCoefficientSingularChainDegree R X 0 ≅ ∐ fun _ : X ↦ ModuleCat.of R R :=
  -- First keep the definitional simplex-indexed coproduct owner, then reindex it by points.
  (eqToIso rfl : unitCoefficientSingularChainDegree R X 0 ≅
      ∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≪≫
    show (∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≅
        ∐ fun _ : X ↦ ModuleCat.of R R from
      Limits.Sigma.whiskerEquiv
        (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
        (fun _ ↦ Iso.refl (ModuleCat.of R R))

/-- Helper for Problem 13.6.4: in degree `k`, the unit-coefficient singular-chain map induced by
`f` is the coproduct map on singular `k`-simplices. -/
private theorem unitCoefficientSingularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f).f k) =
      Sigma.map'
        (fun σ : singularSSetSimplex X k ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk k)) σ)
        (fun _ ↦ 𝟙 (ModuleCat.of R R)) :=
  rfl

/-- Helper for Problem 13.6.4: the inverse of the unique-index coproduct is the unique coproduct
leg. -/
@[simp] private theorem coproductUniqueIso_inv_eq_unitLeg_unitCoefficients
    (R : Type) [CommRing R] :
    (coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv =
      Sigma.ι (fun _ : Unit ↦ ModuleCat.of R R) () := by
  -- The `simps` formula for `coproductUniqueIso` already identifies the inverse with the unique
  -- colimit injection.
  simp [coproductUniqueIso_inv]

/-- Helper for Problem 13.6.4: the unique `0`-simplex of `Unit` is sent to `x` by the constant
map `Unit ⟶ X` under the point/simplex equivalence. -/
private theorem toSSetObj₀Equiv_map_const_unit (X : TopCat) (x : X) :
    TopCat.toSSetObj₀Equiv
        (((TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const Unit x))).app
          (Opposite.op (SimplexCategory.mk 0)))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit))) = x := by
  -- Rewrite the simplicial map of the constant point inclusion as the constant `0`-simplex at
  -- `x`, then evaluate the point/simplex equivalence.
  change TopCat.toSSetObj₀Equiv
      ((SSet.const (TopCat.toSSetObj₀Equiv.symm x)).app
        (Opposite.op (SimplexCategory.mk 0))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit))) = x
  simp

/-- Helper for Problem 13.6.4: reindexing the degree-zero simplex coproduct by points sends the
simplex coming from the constant map `Unit ⟶ X` at `x` to the point leg at `x`. -/
private theorem constZeroSimplexLeg_comp_pointCoproductReindex_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R)
        (((TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const Unit x))).app
          (Opposite.op (SimplexCategory.mk 0)))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit))) ≫
      (show (∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≅
          ∐ fun _ : X ↦ ModuleCat.of R R from
        Limits.Sigma.whiskerEquiv
          (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
          (fun _ ↦ Iso.refl (ModuleCat.of R R))).hom =
      Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x := by
  -- Expand the point-reindexing map and evaluate it on the constant `0`-simplex at `x`.
  have h :
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R)
          (((TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const Unit x))).app
            (Opposite.op (SimplexCategory.mk 0)))
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit))) ≫
        (show (∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≅
            ∐ fun _ : X ↦ ModuleCat.of R R from
          Limits.Sigma.whiskerEquiv
            (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
            (fun _ ↦ Iso.refl (ModuleCat.of R R))).hom =
        Sigma.ι (fun _ : X ↦ ModuleCat.of R R)
          (TopCat.toSSetObj₀Equiv
            (((TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const Unit x))).app
              (Opposite.op (SimplexCategory.mk 0)))
              ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)))) := by
    simpa [Limits.Sigma.whiskerEquiv] using
      (Sigma.ι_comp_map'
        (f := fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R)
        (g := fun _ : X ↦ ModuleCat.of R R)
        (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
        (fun _ ↦ 𝟙 (ModuleCat.of R R))
        (((TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const Unit x))).app
          (Opposite.op (SimplexCategory.mk 0)))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit))))
  rw [toSSetObj₀Equiv_map_const_unit] at h
  exact h

/-- Helper for Problem 13.6.4: postcomposing a degree-zero simplex leg with the point/simplex
reindexing chart yields the corresponding point leg. -/
private theorem singularChainDegreeZeroIsoPointCoproduct_hom_simplexLeg
    (R : Type) [CommRing R] (X : TopCat) (σ : singularSSetSimplex X 0) :
    Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σ ≫
      (singularChainDegreeZeroIsoPointCoproduct (R := R) X).hom =
        Sigma.ι (fun _ : X ↦ ModuleCat.of R R) (TopCat.toSSetObj₀Equiv σ) := by
  -- Route correction: compute the owner-level `hom` map on a single simplex leg once so later
  -- proofs can rewrite through the hidden definitional cast without reopening it.
  let c :
      unitCoefficientSingularChainDegree R X 0 ⟶
        ∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R := eqToHom (by rfl)
  have hRaw :
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σ ≫
          (show (∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≅
              ∐ fun _ : X ↦ ModuleCat.of R R from
            Limits.Sigma.whiskerEquiv
              (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
              (fun _ ↦ Iso.refl (ModuleCat.of R R))).hom =
        Sigma.ι (fun _ : X ↦ ModuleCat.of R R) (TopCat.toSSetObj₀Equiv σ) := by
    simpa [Limits.Sigma.whiskerEquiv] using
      (Sigma.ι_comp_map'
        (f := fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R)
        (g := fun _ : X ↦ ModuleCat.of R R)
        (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
        (fun _ ↦ 𝟙 (ModuleCat.of R R))
        σ)
  have hCast :
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σ ≫ c ≫
          (show (∐ fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) ≅
              ∐ fun _ : X ↦ ModuleCat.of R R from
            Limits.Sigma.whiskerEquiv
              (TopCat.toSSetObj₀Equiv : singularSSetSimplex X 0 ≃ X)
              (fun _ ↦ Iso.refl (ModuleCat.of R R))).hom =
        Sigma.ι (fun _ : X ↦ ModuleCat.of R R) (TopCat.toSSetObj₀Equiv σ) := by
    exact hRaw
  -- The remaining coercion is exactly the definitional identification of degree-zero chains with
  -- the simplex-indexed coproduct.
  simpa [c, singularChainDegreeZeroIsoPointCoproduct, unitCoefficientSingularChainDegree,
    Limits.Sigma.whiskerEquiv, Category.assoc] using hCast

/-- Helper for Problem 13.6.4: for `TopCat.of Unit`, the inverse of the degree-zero
point/simplex coproduct chart sends the unique point generator to the unique simplex leg. -/
private theorem singularChainDegreeZeroIsoPointCoproduct_inv_unitLeg
    (R : Type) [CommRing R] :
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
    uIso.inv ≫ eUnit.inv =
      Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) := by
  -- Route correction: normalize the inverse of the degree-zero reindexing map once at the owner
  -- level instead of repeatedly unfolding it inside the downstream point-inclusion proofs.
  let c :
      (∐ fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R) ⟶
        unitCoefficientSingularChainDegree R (TopCat.of Unit) 0 := eqToHom (by rfl)
  have hRaw :
      Sigma.ι (fun _ : Unit ↦ ModuleCat.of R R) default ≫
          Sigma.map'
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm)
            (fun _ ↦ 𝟙 (ModuleCat.of R R)) =
        𝟙 (ModuleCat.of R R) ≫
          Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) := by
    simpa using
      (Sigma.ι_comp_map'
        (f := fun _ : Unit ↦ ModuleCat.of R R)
        (g := fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm)
        (fun _ ↦ 𝟙 (ModuleCat.of R R))
        (default : Unit))
  have hCast :
      Sigma.ι (fun _ : Unit ↦ ModuleCat.of R R) default ≫
          Sigma.map'
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm)
            (fun _ ↦ 𝟙 (ModuleCat.of R R)) ≫ c =
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫ c := by
    simpa [c, Category.assoc] using congrArg (fun f ↦ f ≫ c) hRaw
  -- The only remaining cast is the definitional identification of degree-zero chains with the
  -- simplex-indexed coproduct.
  suffices
      Sigma.ι (fun _ : Unit ↦ ModuleCat.of R R) default ≫
          Sigma.map'
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm)
            (fun _ ↦ 𝟙 (ModuleCat.of R R)) ≫ c =
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫ c by
    simpa [c, singularChainDegreeZeroIsoPointCoproduct, unitCoefficientSingularChainDegree,
      Limits.Sigma.whiskerEquiv, Category.assoc]
  exact hCast

/-- Helper for Problem 13.6.4: before reindexing simplices by points, the point inclusion
`Unit ⟶ X` sends the unique source generator to the simplex leg indexed by the constant simplex
at `x`. -/
private theorem pointInclusion_zeroChainSimplexLeg_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let σx : singularSSetSimplex X 0 :=
      (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)))
    let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 =
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let σx : singularSSetSimplex X 0 :=
    (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)))
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)))
  let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
  -- First normalize the unique source generator before applying the point inclusion.
  have hUnit :
      uIso.inv ≫ eUnit.inv =
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) := by
    simpa [eUnit, uIso] using singularChainDegreeZeroIsoPointCoproduct_inv_unitLeg (R := R)
  have hUnitComp :
      uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 =
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫
            (F.map ix).f 0 := by
    simpa [Category.assoc] using congrArg (fun f ↦ f ≫ (F.map ix).f 0) hUnit
  -- Then identify the induced degree-zero chain map with the coproduct map on simplices.
  have hMap :
      Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫
            (F.map ix).f 0 =
        Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx := by
    rw [unitCoefficientSingularChainDegreeMap_eq_sigmaMap' (R := R) (f := ix) (k := 0)]
    have hRaw :
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫
            Sigma.map'
              (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
                (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
              (fun _ ↦ 𝟙 (ModuleCat.of R R)) =
          𝟙 (ModuleCat.of R R) ≫
            Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx := by
      simpa [σx] using
        (Sigma.ι_comp_map'
          (f := fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
          (g := fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R)
          (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
            (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
          (fun _ ↦ 𝟙 (ModuleCat.of R R))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)))
    suffices
        Sigma.ι (fun _ : singularSSetSimplex (TopCat.of Unit) 0 ↦ ModuleCat.of R R)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)) ≫
            Sigma.map'
              (fun σ : singularSSetSimplex (TopCat.of Unit) 0 ↦
                (TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)) σ)
              (fun _ ↦ 𝟙 (ModuleCat.of R R)) =
          𝟙 (ModuleCat.of R R) ≫
            Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx by
      simpa
    exact hRaw
  exact by
    -- Compose the owner-level normalization with the simplex-level chain-map computation.
    simpa [ix, F, eUnit, σx, uIso, Category.assoc] using hUnitComp.trans hMap

/-- Helper for Problem 13.6.4: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
unique point generator to the chain generator indexed by `x`. -/
private theorem pointInclusion_zeroChainLeg_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
    let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
    uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eX.hom =
      Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let σx : singularSSetSimplex X 0 :=
    (((TopCat.toSSet.map ix).app (Opposite.op (SimplexCategory.mk 0)))
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of Unit)).symm (default : Unit)))
  let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
  -- First rewrite the source generator at the simplex-indexed coproduct level.
  have hSimplex :
      uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 =
        Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx := by
    simpa [ix, F, eUnit, σx, uIso] using
      pointInclusion_zeroChainSimplexLeg_unitCoefficients (R := R) (X := X) (x := x)
  have hSimplexComp :
      uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 ≫ eX.hom =
        Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx ≫ eX.hom := by
    simpa [Category.assoc] using congrArg (fun f ↦ f ≫ eX.hom) hSimplex
  -- Then postcompose with the point/simplex reindexing chart to recover the point leg.
  have hReindex :
      Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx ≫ eX.hom =
        Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x := by
    -- Compute the owner-level reindexing map on the constant simplex `σx`, then identify its
    -- point image with `x`.
    have hLeg :
        Sigma.ι (fun _ : singularSSetSimplex X 0 ↦ ModuleCat.of R R) σx ≫ eX.hom =
          Sigma.ι (fun _ : X ↦ ModuleCat.of R R) (TopCat.toSSetObj₀Equiv σx) := by
      simpa [eX, σx] using
        singularChainDegreeZeroIsoPointCoproduct_hom_simplexLeg (R := R) (X := X) σx
    rw [toSSetObj₀Equiv_map_const_unit] at hLeg
    exact hLeg
  exact by
    -- The point-indexed coproduct formula is exactly the postcomposition of the simplex formula.
    simpa [ix, F, eX, eUnit, uIso, Category.assoc] using hSimplexComp.trans hReindex

/-- Helper for Problem 13.6.4: the canonical map from degree-zero chains onto `H₀(X; R)` is
surjective for the direct singular-homology owner used in this file. -/
private theorem degreeZeroChains_surjective_to_unitCoefficientHomologyZero
    (R : Type) [CommRing R] (X : TopCat) :
    Function.Surjective
      ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (((singularChainComplexFunctor (ModuleCat R)).obj
            (ModuleCat.of R R)).obj X)).inv) := by
  -- The projection to opcycles is epi, and in degree `0` opcycles identify with homology.
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Helper for Problem 13.6.4: the degree-zero class of the `x`-indexed chain generator agrees
with the image of the unique point generator under the inclusion `Unit ⟶ X` at `x`. -/
private theorem pointGenerator_homology_eq_pointInclusion_image_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) (x : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
    let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
    let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
    let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
    let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
    let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
    let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
    (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ eX.inv ≫ πX =
      uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix := by
  let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
  let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
  let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
  change (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ eX.inv ≫ πX =
      uIso.inv ≫ eUnit.inv ≫ πUnit ≫ FH.map ix
  have hchains :
      uIso.inv ≫ eUnit.inv ≫ (F.map ix).f 0 =
        (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ eX.inv := by
    -- Compare the two degree-zero chain maps after postcomposing with the coproduct chart.
    apply (cancel_mono eX.hom).1
    simpa [Category.assoc] using
      pointInclusion_zeroChainLeg_unitCoefficients (R := R) (X := X) x
  -- Naturality of the passage from chains to `H₀` carries the generator identity to homology.
  calc
    (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ eX.inv ≫ πX =
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

/-- Helper for Problem 13.6.4: a path between `x` and `y` identifies the two induced maps on
`H₀(-; R)` coming from the point inclusions `Unit ⟶ X`. -/
private theorem pointInclusionHom_eq_of_path_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) {x y : X} (γ : Path x y) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map iy := by
  -- Homotopy invariance identifies homotopic point inclusions on singular homology.
  dsimp
  simpa using TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat R) (R := ModuleCat.of R R) (n := 0)
    (H := (Path.toHomotopyConst (Y := Unit) γ))

/-- Helper for Problem 13.6.4: in a path-connected space, every point inclusion `Unit ⟶ X`
induces the same map on zeroth unit-coefficient singular homology. -/
private theorem pointInclusionHom_eq_of_pathConnected_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x y : X) :
    let ix : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x)
    let iy : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit y)
    ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map ix =
      ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map iy := by
  -- Reduce the path-connected case to the explicit path comparison.
  simpa using
    pointInclusionHom_eq_of_path_unitCoefficients (R := R) (X := X)
      (γ := PathConnectedSpace.somePath x y)

/-- Helper for Problem 13.6.4: the inclusion of a chosen basepoint splits after applying zeroth
unit-coefficient singular homology. -/
private theorem pointInclusion_retraction_homology_split_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) (x₀ : X) :
    let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
    let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
    ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map i₀ ≫
      ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map g =
        𝟙 ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
          (TopCat.of Unit))) := by
  let F := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  have hgi : i₀ ≫ g = 𝟙 (TopCat.of Unit) := by
    -- The composite `Unit ⟶ X ⟶ Unit` is the identity map of the point.
    ext u
  -- Functoriality transports the point retraction to the induced map on `H₀`.
  simpa [F, i₀, g, Functor.map_comp] using congrArg F.map hgi

/-- Helper for Problem 13.6.4: in a path-connected space, the chosen basepoint inclusion
`Unit ⟶ X` is surjective on zeroth unit-coefficient singular homology. -/
private theorem pathConnectedH0BasepointInclusion_surjective_unitCoefficients
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] (x₀ : X) :
    let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
    Function.Surjective
      (((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).map i₀) := by
  classical
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eUnit := singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)
  let uIso := coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)
  let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
  let πUnit := (F.obj (TopCat.of Unit)).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv
  let β : ModuleCat.of R R ⟶
      ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of Unit))) :=
    uIso.inv ≫ eUnit.inv ≫ πUnit
  let δ : (∐ fun _ : X ↦ ModuleCat.of R R) ⟶
      ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of Unit))) :=
    Sigma.desc (fun _ : X ↦ β)
  let α : (∐ fun _ : X ↦ ModuleCat.of R R) ⟶
      ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X)) :=
    eX.inv ≫ πX
  change Function.Surjective (FH.map i₀)
  have hFactor : α = δ ≫ FH.map i₀ := by
    -- Check the factorization on each point generator of `C₀(X; R)`.
    refine Sigma.hom_ext _ _ fun x ↦ ?_
    calc
      (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ α =
          β ≫ FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) := by
        simpa [α, β, Category.assoc] using
          pointGenerator_homology_eq_pointInclusion_image_unitCoefficients
            (R := R) (X := X) x
      _ = β ≫ FH.map i₀ := by
        rw [show FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) = FH.map i₀ by
              symm
              simpa [i₀] using
                pointInclusionHom_eq_of_pathConnected_unitCoefficients
                  (R := R) (X := X) x₀ x]
      _ = (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ δ ≫ FH.map i₀ := by
        have hβ : (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ δ = β := by
          simpa [δ] using (Sigma.ι_desc (fun _ : X ↦ β) x)
        rw [← hβ, Category.assoc]
  -- Every `H₀(X; R)` class has a degree-zero chain representative, and `hFactor` rewrites that
  -- representative through the chosen basepoint inclusion.
  intro z
  rcases degreeZeroChains_surjective_to_unitCoefficientHomologyZero
      (R := R) (X := X) z with ⟨c, hc⟩
  refine ⟨δ (eX.hom c), ?_⟩
  change ((δ ≫ FH.map i₀) (eX.hom c)) = z
  rw [← hFactor]
  simpa [α] using hc

/-- Helper for Problem 13.6.4: the degree-zero unit-coefficient singular homology of a point is
the coefficient module itself. -/
private theorem pointUnitCoefficientHomologyZeroIso
    (R : Type) [CommRing R] :
    Nonempty ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
      (TopCat.of Unit)) ≅ ModuleCat.of R R) := by
  -- Compute `H₀` of the point via the totally disconnected-space description.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat R) (R := ModuleCat.of R R) (X := TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)

/-- Helper for Problem 13.6.4: a path-connected space has degree-zero unit-coefficient singular
homology equal to the coefficient module. -/
private theorem unitCoefficientHomologyZeroIsoOfPathConnected
    (R : Type) [CommRing R] (X : TopCat) [PathConnectedSpace X] :
    Nonempty ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X) ≅
      ModuleCat.of R R) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  let i₀ : TopCat.of Unit ⟶ X := TopCat.ofHom (ContinuousMap.const Unit x₀)
  let g : X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  have hsplit :
      FH.map i₀ ≫ FH.map g =
        𝟙 ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
          (TopCat.of Unit))) := by
    -- The chosen basepoint inclusion is split by the constant retraction to the point.
    simpa [i₀, g] using
      pointInclusion_retraction_homology_split_unitCoefficients (R := R) (X := X) x₀
  have hsurj : Function.Surjective (FH.map i₀) := by
    -- Surjectivity is exactly the basepoint factorization established above.
    simpa [i₀] using
      pathConnectedH0BasepointInclusion_surjective_unitCoefficients (R := R) (X := X) x₀
  have hinj : Function.Injective (FH.map i₀) := by
    -- The constant retraction gives a left inverse on the underlying module map.
    have hleft : Function.LeftInverse (FH.map g) (FH.map i₀) := by
      intro z
      have h := congrArg (fun f ↦ f z) hsplit
      simpa [Category.assoc] using h
    exact hleft.injective
  let f :
      ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj (TopCat.of Unit)))
        →ₗ[R]
          ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X)) :=
    (FH.map i₀).hom
  have hsurj_f : Function.Surjective f := hsurj
  have hinj_f : Function.Injective f := hinj
  let hBasepoint :
      ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of Unit))) ≅
        ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X)) :=
    LinearEquiv.toModuleIso <| LinearEquiv.ofBijective f ⟨hinj_f, hsurj_f⟩
  -- Finish by comparing `H₀(X; R)` with `H₀(Unit; R)` and then using the point computation.
  exact
    ⟨hBasepoint.symm ≪≫
      Classical.choice (pointUnitCoefficientHomologyZeroIso (R := R))⟩

/-- Helper for Problem 13.6.4: a path-connected space has integral singular `H₀` equal to `ℤ`.
-/
private theorem pathConnectedIntegralHomologyZeroIso
    (X : TopCat) [PathConnectedSpace X] :
    Nonempty (integralSingularHomology 0 X ≅ ModuleCat.of ℤ ℤ) := by
  -- The chapter owner `integralSingularHomology` is definitionally the unit-coefficient singular
  -- homology owner, so the general path-connected `H₀` theorem applies directly.
  simpa [integralSingularHomology] using
    unitCoefficientHomologyZeroIsoOfPathConnected (R := ℤ) X

/-- Helper for Problem 13.6.4: the vector `(1)` lies on the concrete model of `TopCat.sphere 0`.
-/
private theorem sphereZeroPos_mem :
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ TopCat.SphereModel 0 := by
  -- Unfold the zero-sphere model to the one-coordinate norm equation.
  simp [TopCat.SphereModel]

/-- Helper for Problem 13.6.4: a chosen positive point of `TopCat.sphere 0`. -/
private def sphereZeroPos : TopCat.sphere.{0} 0 :=
  ULift.up <| ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), sphereZeroPos_mem⟩

/-- Helper for Problem 13.6.4: the two distinguished points of `TopCat.sphere 0` are distinct. -/
private theorem sphereZeroPos_ne_neg :
    (sphereZeroPos : TopCat.sphere.{0} 0) ≠ -sphereZeroPos := by
  -- Compare the unique coordinate of the two explicit points.
  intro h
  have h0 : (sphereZeroPos.down.1 : Fin 1 → ℝ) 0 =
      ((-sphereZeroPos).down.1 : Fin 1 → ℝ) 0 := by
    simpa using
      congrArg (fun z : TopCat.sphere.{0} 0 ↦ (z.down.1 : Fin 1 → ℝ) 0) h
  change (1 : ℝ) = -1 at h0
  norm_num at h0

/-- Helper for Problem 13.6.4: every point of `TopCat.sphere 0` is either `sphereZeroPos` or its
antipode. -/
private theorem sphereZero_eq_or_eq_neg (x : TopCat.sphere.{0} 0) :
    x = sphereZeroPos ∨ x = -sphereZeroPos := by
  -- Express `x` by its unique coordinate in `ℝ`.
  have hxsingle : x.down.1 = EuclideanSpace.single (0 : Fin 1) (x.down.1 0) := by
    ext i
    fin_cases i
    simp [EuclideanSpace.single]
  have hxmem : dist x.down.1 0 = 1 := by
    simpa [Metric.mem_sphere] using x.down.2
  have hxnorm : ‖x.down.1‖ = 1 := by
    simpa [dist_eq_norm] using hxmem
  have hnormeq : ‖x.down.1‖ = ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ :=
    congrArg norm hxsingle
  have hnormsingle : ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ = ‖x.down.1 0‖ := by
    simpa using (PiLp.norm_single (0 : Fin 1) (x.down.1 0 : ℝ))
  have hxcoordnorm : ‖x.down.1 0‖ = 1 := by
    calc
      ‖x.down.1 0‖ = ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ := hnormsingle.symm
      _ = ‖x.down.1‖ := hnormeq.symm
      _ = 1 := hxnorm
  have habs : |x.down.1 0| = 1 := by
    simpa [Real.norm_eq_abs] using hxcoordnorm
  have hsq : (x.down.1 0) ^ 2 = (1 : ℝ) ^ 2 := by
    nlinarith [abs_mul_abs_self (x.down.1 0), habs]
  have hcoord : x.down.1 0 = 1 ∨ x.down.1 0 = -1 :=
    eq_or_eq_neg_of_sq_eq_sq _ _ hsq
  -- Lift the coordinate classification back to the zero-sphere.
  cases hcoord with
  | inl h =>
      left
      apply ULift.ext
      apply Subtype.ext
      ext i
      fin_cases i
      simpa [sphereZeroPos, EuclideanSpace.single] using h
  | inr h =>
      right
      apply ULift.ext
      apply Subtype.ext
      ext i
      fin_cases i
      simpa [sphereZeroPos, EuclideanSpace.single] using h

/-- Helper for Problem 13.6.4: `TopCat.sphere 0` has decidable equality on its two points. -/
private noncomputable instance sphereZeroDecidableEq : DecidableEq (TopCat.sphere.{0} 0) :=
  Classical.decEq _

/-- Helper for Problem 13.6.4: the zero-sphere is finite with exactly the chosen point and its
antipode. -/
private noncomputable instance sphereZeroFintype : Fintype (TopCat.sphere.{0} 0) where
  elems := {sphereZeroPos, -sphereZeroPos}
  complete x := by
    -- The explicit two-point classification exhausts the zero-sphere.
    rcases sphereZero_eq_or_eq_neg x with h | h <;> simp [h]

/-- Helper for Problem 13.6.4: `TopCat.sphere 0` inherits the `T₁` topology of the metric
sphere. -/
private instance sphereZeroT1Space : T1Space (TopCat.sphere.{0} 0) := by
  constructor
  intro x
  have hclosed : IsClosed ({x.down} : Set (TopCat.SphereModel 0)) := by
    have hclosedBall : IsClosed (Metric.closedBall x.down 0) := Metric.isClosed_closedBall
    rwa [Metric.closedBall_zero] at hclosedBall
  have hpre := hclosed.preimage continuous_uliftDown
  have heq : ULift.down ⁻¹' ({x.down} : Set (TopCat.SphereModel 0)) = {x} := by
    ext y
    change y.down = x.down ↔ y = x
    constructor
    · exact fun h ↦ ULift.ext _ _ h
    · exact fun h ↦ congrArg ULift.down h
  rw [heq] at hpre
  exact hpre

/-- Helper for Problem 13.6.4: the zero-sphere has the discrete topology. -/
private instance sphereZeroDiscreteTopology : DiscreteTopology (TopCat.sphere.{0} 0) := by
  infer_instance

/-- Helper for Problem 13.6.4: the zero-sphere is totally disconnected. -/
private instance sphereZeroTotallyDisconnected :
    TotallyDisconnectedSpace (TopCat.sphere.{0} 0) := by
  infer_instance

/-- Helper for Problem 13.6.4: the chosen two-point model of `TopCat.sphere 0` is equivalent to
`Fin 2`. -/
private noncomputable def sphereZeroEquivFinTwo : TopCat.sphere.{0} 0 ≃ Fin 2 := by
  -- Send the positive point to `0` and its antipode to `1`.
  refine
    { toFun := fun x ↦ if x = sphereZeroPos then 0 else 1
      invFun := fun i ↦ if i = 0 then sphereZeroPos else -sphereZeroPos
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases sphereZero_eq_or_eq_neg x with rfl | rfl
    · simp
    · simp [sphereZeroPos_ne_neg, Ne.symm sphereZeroPos_ne_neg]
  · intro i
    fin_cases i <;> simp [sphereZeroPos_ne_neg, Ne.symm sphereZeroPos_ne_neg]

/-- Helper for Problem 13.6.4: a constant `ModuleCat` coproduct admits the concrete `Finsupp`
presentation used below to count point components. -/
private noncomputable def moduleCatConstantCoproductCofan
    (R : Type) [CommRing R] (ι : Type) (M : Type)
    [AddCommGroup M] [Module R M] :
    Limits.Cofan fun _ : ι ↦ ModuleCat.of R M :=
  Limits.Cofan.mk (ModuleCat.of R (ι →₀ M)) fun i ↦
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := M))

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Problem 13.6.4: the concrete `Finsupp` cofan is colimiting for a constant
`ModuleCat` diagram. -/
private noncomputable def moduleCatConstantCoproductIsColimit
    (R : Type) [CommRing R] (ι : Type) (M : Type)
    [AddCommGroup M] [Module R M] :
    Limits.IsColimit (moduleCatConstantCoproductCofan (R := R) ι M) where
  desc s := ModuleCat.ofHom <| Finsupp.lsum R (N := s.pt) (fun i ↦ (s.ι.app ⟨i⟩).hom)
  fac s j := by
    -- Each coproduct injection picks out exactly one summand of the `Finsupp` sum.
    ext x
    simp [moduleCatConstantCoproductCofan]
  uniq s f h := by
    -- Two maps out of a `Finsupp` module agree once they agree on every basis vector.
    ext : 1
    apply Finsupp.lhom_ext'
    intro i
    ext x
    have hi := congrArg ModuleCat.Hom.hom (h ⟨i⟩)
    simpa [moduleCatConstantCoproductCofan] using LinearMap.congr_fun hi x

/-- Helper for Problem 13.6.4: a constant coproduct in `ModuleCat` is canonically identified
with the corresponding finitely supported function module. -/
private noncomputable def moduleCatConstantCoproductIso
    (R : Type) [CommRing R] (ι : Type) (M : Type)
    [AddCommGroup M] [Module R M] :
    (∐ fun _ : ι ↦ ModuleCat.of R M) ≅ ModuleCat.of R (ι →₀ M) :=
  Limits.IsColimit.coconePointUniqueUpToIso
    (Limits.coproductIsCoproduct (fun _ : ι ↦ ModuleCat.of R M))
    (moduleCatConstantCoproductIsColimit (R := R) ι M)

/-- Helper for Problem 13.6.4: the point-indexed coproduct for `TopCat.sphere 0` is the free
rank-two `ℤ`-module. -/
private noncomputable def sphereZeroPointCoproductIso :
    (∐ fun _ : TopCat.sphere 0 ↦ ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (ℤ × ℤ) :=
  (show (∐ fun _ : TopCat.sphere 0 ↦ ModuleCat.of ℤ ℤ) ≅
      ∐ fun _ : Fin 2 ↦ ModuleCat.of ℤ ℤ from
    Limits.Sigma.whiskerEquiv sphereZeroEquivFinTwo (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))) ≪≫
    moduleCatConstantCoproductIso (R := ℤ) (ι := Fin 2) ℤ ≪≫
    LinearEquiv.toModuleIso (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 2)) ≪≫
    LinearEquiv.toModuleIso (LinearEquiv.finTwoArrow ℤ ℤ)

/-- Helper for Problem 13.6.4: the point-indexed coproduct for `TopCat.sphere 0 × TopCat.sphere
0` is the free rank-four `ℤ`-module. -/
private noncomputable def sphereZeroSquarePointCoproductIso :
    (∐ fun _ : TopCat.of (TopCat.sphere 0 × TopCat.sphere 0) ↦ ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ) := by
  let eProd : TopCat.of (TopCat.sphere 0 × TopCat.sphere 0) ≃ Fin 4 := by
    let e :=
      (sphereZeroEquivFinTwo.prodCongr sphereZeroEquivFinTwo).trans
        (show Fin 2 × Fin 2 ≃ Fin 4 by
          simpa using (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)))
    exact e
  -- Reindex the coproduct by the explicit four-point owner, then normalize to functions.
  refine
    (show (∐ fun _ : TopCat.of (TopCat.sphere 0 × TopCat.sphere 0) ↦ ModuleCat.of ℤ ℤ) ≅
        ∐ fun _ : Fin 4 ↦ ModuleCat.of ℤ ℤ from
      Limits.Sigma.whiskerEquiv eProd (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))) ≪≫
      moduleCatConstantCoproductIso (R := ℤ) (ι := Fin 4) ℤ ≪≫
      LinearEquiv.toModuleIso (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 4))

/-- Helper for Problem 13.6.4: the zeroth integral homology of `TopCat.sphere 0` is `ℤ × ℤ`,
and every positive-degree integral homology group vanishes. -/
private theorem sphereZeroIntegralHomologyPattern :
    Nonempty (integralSingularHomology 0 (TopCat.sphere 0) ≅ ModuleCat.of ℤ (ℤ × ℤ)) ∧
      ∀ q : ℕ, q ≠ 0 → IsZero (integralSingularHomology q (TopCat.sphere 0)) := by
  constructor
  · -- Compute `H₀(S⁰; ℤ)` from the totally disconnected-space formula and the two-point model.
    refine ⟨?_⟩
    exact
      singularHomologyFunctorZeroOfTotallyDisconnectedSpace
          (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ) (X := TopCat.sphere 0) ≪≫
        sphereZeroPointCoproductIso
  · intro q hq
    -- Positive-degree singular homology of a totally disconnected space vanishes.
    simpa [integralSingularHomology] using
      (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (C := ModuleCat ℤ) (n := q) (R := ModuleCat.of ℤ ℤ) (X := TopCat.sphere 0) hq)

/-- Helper for Problem 13.6.4: if `q : X ⟶ B` admits a section `s : B ⟶ X` and each point of `X`
is path-connected to the chosen section point in its fiber, then `H₀(X; R) ≅ H₀(B; R)`. -/
private theorem homologyZeroIsoOfSectionWithFiberPaths
    (R : Type) [CommRing R] {X B : TopCat}
    (q : X ⟶ B) (s : B ⟶ X) (hsq : s ≫ q = 𝟙 B)
    (hfiber : ∀ x : X, Path x (s (q x))) :
    Nonempty ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X) ≅
      (((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj B)) := by
  classical
  let F := ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))
  let FH := ((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  let eX := singularChainDegreeZeroIsoPointCoproduct (R := R) X
  let eB := singularChainDegreeZeroIsoPointCoproduct (R := R) B
  let πX := (F.obj X).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj X)).inv
  let πB := (F.obj B).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (F.obj B)).inv
  let αX : (∐ fun _ : X ↦ ModuleCat.of R R) ⟶ (FH.obj X) := eX.inv ≫ πX
  let αB : (∐ fun _ : B ↦ ModuleCat.of R R) ⟶ (FH.obj B) := eB.inv ≫ πB
  let δ : (∐ fun _ : X ↦ ModuleCat.of R R) ⟶ (FH.obj B) :=
    Sigma.desc (fun x : X ↦ Sigma.ι (fun _ : B ↦ ModuleCat.of R R) (q x) ≫ αB)
  have hFactor : αX = δ ≫ FH.map s := by
    -- Check the factorization on point generators, using the chosen fiberwise paths.
    refine Sigma.hom_ext _ _ fun x ↦ ?_
    have hBx :
        (Sigma.ι (fun _ : B ↦ ModuleCat.of R R) (q x)) ≫ αB =
          ((coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv) ≫
            (singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)).inv ≫
              ((F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv) ≫
                  FH.map (TopCat.ofHom (ContinuousMap.const Unit (q x))) := by
      simpa [αB] using
        pointGenerator_homology_eq_pointInclusion_image_unitCoefficients
          (R := R) (X := B) (q x)
    have hXx :
        (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ αX =
          ((coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv) ≫
            (singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)).inv ≫
              ((F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv) ≫
                  FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) := by
      simpa [αX] using
        pointGenerator_homology_eq_pointInclusion_image_unitCoefficients
          (R := R) (X := X) x
    have hPath :
        FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) =
          FH.map (TopCat.ofHom (ContinuousMap.const Unit (s (q x)))) := by
      simpa using
        pointInclusionHom_eq_of_path_unitCoefficients (R := R) (X := X) (γ := hfiber x)
    calc
      (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ αX =
          ((coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv) ≫
            (singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)).inv ≫
              ((F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv) ≫
                  FH.map (TopCat.ofHom (ContinuousMap.const Unit x)) := hXx
      _ =
          ((coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv) ≫
            (singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)).inv ≫
              ((F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv) ≫
                  FH.map (TopCat.ofHom (ContinuousMap.const Unit (s (q x)))) := by
            simp [hPath]
      _ =
          ((coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv) ≫
            (singularChainDegreeZeroIsoPointCoproduct (R := R) (TopCat.of Unit)).inv ≫
              ((F.obj (TopCat.of Unit)).pOpcycles 0 ≫
                (ChainComplex.isoHomologyι₀ (F.obj (TopCat.of Unit))).inv) ≫
                  (FH.map (TopCat.ofHom (ContinuousMap.const Unit (q x))) ≫ FH.map s) := by
            have hconst :
                TopCat.ofHom (ContinuousMap.const Unit (s (q x))) =
                  TopCat.ofHom (ContinuousMap.const Unit (q x)) ≫ s := by
              ext u
              rfl
            rw [hconst, Functor.map_comp]
            rfl
      _ = (Sigma.ι (fun _ : B ↦ ModuleCat.of R R) (q x)) ≫ αB ≫ FH.map s := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ FH.map s) hBx.symm
      _ = (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ δ ≫ FH.map s := by
            have hδ : (Sigma.ι (fun _ : X ↦ ModuleCat.of R R) x) ≫ δ =
                (Sigma.ι (fun _ : B ↦ ModuleCat.of R R) (q x)) ≫ αB := by
              simpa [δ] using
                (Sigma.ι_desc (fun x : X ↦ Sigma.ι (fun _ : B ↦ ModuleCat.of R R) (q x) ≫ αB) x)
            exact congrArg (fun f ↦ f ≫ FH.map s) hδ.symm
  have hsurj : Function.Surjective (FH.map s).hom := by
    -- Every `H₀(X; R)` class is represented by a point generator, and `hFactor` rewrites each
    -- such generator through the chosen section.
    intro z
    rcases degreeZeroChains_surjective_to_unitCoefficientHomologyZero (R := R) (X := X) z with
      ⟨c, hc⟩
    refine ⟨δ (eX.hom c), ?_⟩
    change ((δ ≫ FH.map s) (eX.hom c)) = z
    rw [← hFactor]
    simpa [αX] using hc
  have hinj : Function.Injective (FH.map s).hom := by
    -- The section equation gives a left inverse on `H₀`.
    have hleft : Function.LeftInverse (FH.map q).hom (FH.map s).hom := by
      intro z
      have h := congrArg (fun f ↦ f z) (congrArg FH.map hsq)
      simpa [Functor.map_comp] using h
    exact hleft.injective
  let f : (FH.obj B) →ₗ[R] (FH.obj X) := (FH.map s).hom
  have hsurj_f : Function.Surjective f := hsurj
  have hinj_f : Function.Injective f := hinj
  refine ⟨(LinearEquiv.toModuleIso <| LinearEquiv.ofBijective f ⟨hinj_f, hsurj_f⟩).symm⟩

/-- The integral singular homology object of `S^m × S^n` in degree `k`. -/
noncomputable abbrev sphereProductIntegralHomologyGroup (m n k : ℕ) : ModuleCat ℤ :=
  integralSingularHomology k (TopCat.of (TopCat.sphere m × TopCat.sphere n))

/-- Helper for Problem 13.6.4: if exactly one sphere factor is `S^0`, then the zeroth integral
homology of the product is `ℤ × ℤ`. -/
private theorem sphereProductSingleZeroFactorIntegralHomologyZeroIso
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hnotBoth : ¬ (m = 0 ∧ n = 0)) :
    Nonempty (sphereProductIntegralHomologyGroup m n 0 ≅ ModuleCat.of ℤ (ℤ × ℤ)) := by
  rcases hzero with hm | hn
  · subst hm
    have hnpos : 0 < n := by
      apply Nat.pos_of_ne_zero
      intro hn0
      exact hnotBoth ⟨rfl, hn0⟩
    let _ : PathConnectedSpace (TopCat.sphere n) := spherePathConnectedSpace_of_pos hnpos
    let y₀ : TopCat.sphere n := Classical.choice PathConnectedSpace.nonempty
    let q : TopCat.of (TopCat.sphere 0 × TopCat.sphere n) ⟶ TopCat.sphere 0 :=
      TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
    let s : TopCat.sphere 0 ⟶ TopCat.of (TopCat.sphere 0 × TopCat.sphere n) :=
      TopCat.ofHom ⟨fun x ↦ (x, y₀), continuous_id.prodMk continuous_const⟩
    have hsq : s ≫ q = 𝟙 (TopCat.sphere 0) := by
      ext x
      change x = x
      rfl
    have hfiber : ∀ x : TopCat.of (TopCat.sphere 0 × TopCat.sphere n), Path x (s (q x)) := by
      intro x
      simpa [q, s] using (Path.refl x.1).prod (PathConnectedSpace.somePath x.2 y₀)
    have hRetract :
        Nonempty (sphereProductIntegralHomologyGroup 0 n 0 ≅ integralSingularHomology 0 (TopCat.sphere 0)) := by
      simpa [sphereProductIntegralHomologyGroup, integralSingularHomology, q, s] using
        homologyZeroIsoOfSectionWithFiberPaths (R := ℤ) q s hsq hfiber
    rcases sphereZeroIntegralHomologyPattern with ⟨hZero, _hvanish⟩
    rcases hRetract with ⟨eRetract⟩
    rcases hZero with ⟨eZero⟩
    exact ⟨eRetract ≪≫ eZero⟩
  · subst hn
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      exact hnotBoth ⟨hm0, rfl⟩
    let _ : PathConnectedSpace (TopCat.sphere m) := spherePathConnectedSpace_of_pos hmpos
    let x₀ : TopCat.sphere m := Classical.choice PathConnectedSpace.nonempty
    let q : TopCat.of (TopCat.sphere m × TopCat.sphere 0) ⟶ TopCat.sphere 0 :=
      TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    let s : TopCat.sphere 0 ⟶ TopCat.of (TopCat.sphere m × TopCat.sphere 0) :=
      TopCat.ofHom ⟨fun y ↦ (x₀, y), continuous_const.prodMk continuous_id⟩
    have hsq : s ≫ q = 𝟙 (TopCat.sphere 0) := by
      ext x
      change x = x
      rfl
    have hfiber : ∀ x : TopCat.of (TopCat.sphere m × TopCat.sphere 0), Path x (s (q x)) := by
      intro x
      simpa [q, s] using (PathConnectedSpace.somePath x.1 x₀).prod (Path.refl x.2)
    have hRetract :
        Nonempty (sphereProductIntegralHomologyGroup m 0 0 ≅ integralSingularHomology 0 (TopCat.sphere 0)) := by
      simpa [sphereProductIntegralHomologyGroup, integralSingularHomology, q, s] using
        homologyZeroIsoOfSectionWithFiberPaths (R := ℤ) q s hsq hfiber
    rcases sphereZeroIntegralHomologyPattern with ⟨hZero, _hvanish⟩
    rcases hRetract with ⟨eRetract⟩
    rcases hZero with ⟨eZero⟩
    exact ⟨eRetract ≪≫ eZero⟩

/-- Helper for Problem 13.6.4: the zeroth integral homology of `S^0 × S^0` is free of rank
four. -/
private theorem sphereZeroSquareIntegralHomologyZeroIso :
    Nonempty (sphereProductIntegralHomologyGroup 0 0 0 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  -- Compute `H₀(S⁰ × S⁰; ℤ)` from the totally disconnected-space formula and the explicit
  -- four-point model of the product.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
        (X := TopCat.of (TopCat.sphere 0 × TopCat.sphere 0)) ≪≫
      sphereZeroSquarePointCoproductIso

/-- The graded integral homology groups expected for `S^m × S^n`. -/
noncomputable def sphereProductHomology (m n k : ℕ) : ModuleCat ℤ :=
  if _ : m = 0 then
    if _ : n = 0 then
      if k = 0 then
        ModuleCat.of ℤ (Fin 4 → ℤ)
      else
        ModuleCat.of ℤ (Fin 0 → ℤ)
    else if k = 0 then
      ModuleCat.of ℤ (ℤ × ℤ)
    else if k = n then
      ModuleCat.of ℤ (ℤ × ℤ)
    else
      ModuleCat.of ℤ (Fin 0 → ℤ)
  else if _ : n = 0 then
    if k = 0 then
      ModuleCat.of ℤ (ℤ × ℤ)
    else if k = m then
      ModuleCat.of ℤ (ℤ × ℤ)
    else
      ModuleCat.of ℤ (Fin 0 → ℤ)
  else if k = 0 then
    ModuleCat.of ℤ ℤ
  else if _ : m = n then
    if k = m then
      ModuleCat.of ℤ (ℤ × ℤ)
    else if k = m + n then
      ModuleCat.of ℤ ℤ
    else
      ModuleCat.of ℤ (Fin 0 → ℤ)
  else if k = m then
    ModuleCat.of ℤ ℤ
  else if k = n then
    ModuleCat.of ℤ ℤ
  else if k = m + n then
    ModuleCat.of ℤ ℤ
  else
    ModuleCat.of ℤ (Fin 0 → ℤ)

/-- If both sphere factors are positive-dimensional, then the degree-`0` model homology is `ℤ`. -/
theorem sphereProductHomology_positive_zero
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    sphereProductHomology m n 0 = ModuleCat.of ℤ ℤ := by
  simp [sphereProductHomology, hm.ne', hn.ne']

/-- If both sphere factors are positive-dimensional and distinct, then the degree-`m` model
homology is `ℤ`. -/
theorem sphereProductHomology_positive_left
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    sphereProductHomology m n m = ModuleCat.of ℤ ℤ := by
  simp [sphereProductHomology, hm.ne', hn.ne', hmn]

/-- If both sphere factors are positive-dimensional and distinct, then the degree-`n` model
homology is `ℤ`. -/
theorem sphereProductHomology_positive_right
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    sphereProductHomology m n n = ModuleCat.of ℤ ℤ := by
  simp [sphereProductHomology, hm.ne', hn.ne', hmn]

/-- If both sphere factors are the same positive dimension, then the middle model homology is
`ℤ × ℤ`. -/
theorem sphereProductHomology_positive_diagonal
    (m n : ℕ) (hm : 0 < m) (hmn : m = n) :
    sphereProductHomology m n m = ModuleCat.of ℤ (ℤ × ℤ) := by
  subst hmn
  simp [sphereProductHomology, hm.ne']

/-- If both sphere factors are positive-dimensional, then the top model homology is `ℤ`. -/
theorem sphereProductHomology_positive_top
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    sphereProductHomology m n (m + n) = ModuleCat.of ℤ ℤ := by
  simp [sphereProductHomology, hm.ne', hn.ne']

/-- If both sphere factors are positive-dimensional, then every other model homology group is
zero. -/
theorem sphereProductHomology_positive_isZero
    (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk0 : k ≠ 0) (hkm : k ≠ m) (hkn : k ≠ n) (hktop : k ≠ m + n) :
    IsZero (sphereProductHomology m n k) := by
  simpa [sphereProductHomology, hm.ne', hn.ne', hk0, hkm, hkn, hktop] using
    isZero_finZeroModule

/-- If exactly one factor is `S^0`, then the degree-`0` model homology is `ℤ × ℤ`. -/
theorem sphereProductHomology_singleZeroFactor_zero
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n) :
    sphereProductHomology m n 0 = ModuleCat.of ℤ (ℤ × ℤ) := by
  rcases hzero with rfl | rfl
  · have hn : 0 < n := by simpa using hpos
    simp [sphereProductHomology, hn.ne']
  · have hm : 0 < m := by simpa [Nat.add_comm] using hpos
    simp [sphereProductHomology, hm.ne']

/-- If exactly one factor is `S^0`, then the top model homology is `ℤ × ℤ`. -/
theorem sphereProductHomology_singleZeroFactor_top
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n) :
    sphereProductHomology m n (m + n) = ModuleCat.of ℤ (ℤ × ℤ) := by
  rcases hzero with rfl | rfl
  · have hn : 0 < n := by simpa using hpos
    simp [sphereProductHomology, hn.ne']
  · have hm : 0 < m := by simpa [Nat.add_comm] using hpos
    simp [sphereProductHomology, hm.ne']

/-- If exactly one factor is `S^0`, then all remaining model homology groups vanish. -/
theorem sphereProductHomology_singleZeroFactor_isZero
    (m n k : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n)
    (hk0 : k ≠ 0) (hktop : k ≠ m + n) :
    IsZero (sphereProductHomology m n k) := by
  rcases hzero with rfl | rfl
  · have hn : 0 < n := by simpa using hpos
    have hkn : k ≠ n := by simpa using hktop
    simpa [sphereProductHomology, hk0, hn.ne', hkn] using isZero_finZeroModule
  · have hm : 0 < m := by simpa [Nat.add_comm] using hpos
    have hkm : k ≠ m := by simpa [Nat.add_comm] using hktop
    simpa [sphereProductHomology, hk0, hm.ne', hkm] using isZero_finZeroModule

/-- For `S^0 × S^0`, the degree-`0` model homology is free of rank `4`. -/
theorem sphereProductHomology_doubleZeroFactor_zero :
    sphereProductHomology 0 0 0 = ModuleCat.of ℤ (Fin 4 → ℤ) := by
  simp [sphereProductHomology]

/-- For `S^0 × S^0`, every positive-degree model homology group is zero. -/
theorem sphereProductHomology_doubleZeroFactor_isZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero (sphereProductHomology 0 0 k) := by
  simpa [sphereProductHomology, hk] using isZero_finZeroModule

/-- Helper for Problem 13.6.4: in degree `0`, the explicit model depends only on whether each
sphere factor is `S^0`, matching the later path-component case split for `H₀`. -/
theorem sphereProductHomology_zeroDegree_cases (m n : ℕ) :
    sphereProductHomology m n 0 =
      if m = 0 then
        if n = 0 then ModuleCat.of ℤ (Fin 4 → ℤ)
        else ModuleCat.of ℤ (ℤ × ℤ)
      else if n = 0 then
        ModuleCat.of ℤ (ℤ × ℤ)
      else
        ModuleCat.of ℤ ℤ := by
  by_cases hm : m = 0
  · subst hm
    by_cases hn : n = 0
    · subst hn
      -- Both factors are `S^0`, so the degree-zero model has four components.
      simp [sphereProductHomology]
    · -- Exactly one factor is `S^0`, so the degree-zero model has two components.
      simp [sphereProductHomology, hn]
  · by_cases hn : n = 0
    · subst hn
      -- Symmetrically, one zero-dimensional factor gives the rank-two degree-zero model.
      simp [sphereProductHomology, hm]
    · -- If both factors are positive-dimensional, the degree-zero model is the usual `ℤ`.
      simp [sphereProductHomology, hm, hn]

/-- Helper for Problem 13.6.4: if neither sphere factor is `S^0`, then the degree-zero explicit
model is the connected-space answer `ℤ`. -/
theorem sphereProductHomology_zeroDegree_of_ne_zero
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    sphereProductHomology m n 0 = ModuleCat.of ℤ ℤ := by
  -- Convert the nonvanishing hypotheses into positivity and reuse the positive-dimensional case.
  exact sphereProductHomology_positive_zero m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- Helper for Problem 13.6.4: if exactly one factor is `S^0`, then the degree-zero explicit
model is `ℤ × ℤ`, matching the two path components of the product. -/
theorem sphereProductHomology_zeroDegree_of_singleZeroFactor
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hnotBoth : ¬ (m = 0 ∧ n = 0)) :
    sphereProductHomology m n 0 = ModuleCat.of ℤ (ℤ × ℤ) := by
  have hpos : 0 < m + n := by
    rcases hzero with rfl | rfl
    · have hn : n ≠ 0 := by
        intro hn
        exact hnotBoth ⟨rfl, hn⟩
      simpa using Nat.pos_of_ne_zero hn
    · have hm : m ≠ 0 := by
        intro hm
        exact hnotBoth ⟨hm, rfl⟩
      simpa [Nat.add_comm] using Nat.pos_of_ne_zero hm
  -- Reduce to the existing one-zero-factor computation after showing the remaining dimension is
  -- positive.
  exact sphereProductHomology_singleZeroFactor_zero m n hzero hpos

/-- Helper for Problem 13.6.4: every explicit model homology group of `S^m × S^n` is a
projective `ℤ`-module, so the future Kunneth route can discharge its `Tor`-vanishing side
conditions by instance search after reducing to this model. -/
theorem sphereProductHomology_projective (m n k : ℕ) :
    Projective (sphereProductHomology m n k) := by
  classical
  -- Unfold the explicit case split and let instance search recognize each branch as a free
  -- `ℤ`-module.
  unfold sphereProductHomology
  repeat' split_ifs
  all_goals infer_instance

/-- Helper for Problem 13.6.4: every explicit model homology group of `S^m × S^n` is flat over
`ℤ`, so the algebraic Kunneth package can use the explicit answer as a flat input whenever the
geometric comparison is available. -/
theorem sphereProductHomology_flat (m n k : ℕ) :
    Module.Flat ℤ (sphereProductHomology m n k) := by
  -- First reuse the already-proved projectivity of the explicit model.
  let _ : Projective (sphereProductHomology m n k) :=
    sphereProductHomology_projective m n k
  -- Then let the standard `projective => flat` instance over `ℤ` finish the algebraic side
  -- condition.
  infer_instance

/-- Helper for Problem 13.6.4: the degree-one `Tor` term with the explicit homology model of
`S^m × S^n` as the right input vanishes, because that model is projective over `ℤ`. -/
theorem sphereProductHomology_torIsZero_right
    (M : ModuleCat ℤ) (m n k : ℕ) :
    IsZero (ModuleCat.tor ℤ M (sphereProductHomology m n k)) := by
  -- First reuse the explicit projectivity of the computed model homology object.
  let _ : Projective (sphereProductHomology m n k) :=
    sphereProductHomology_projective m n k
  -- Then invoke the Chapter 17 source-facing Tor-vanishing theorem for projective right inputs.
  simpa using
    (ModuleCat.isZero_tor_of_projective_right
      (R := ℤ) M (sphereProductHomology m n k))

/-- Helper for Problem 13.6.4: each degree of a chosen cellular chain complex is a free
`ℤ`-module, because cellular chains are free abelian groups on the cells in that degree. -/
theorem cellularChainComplexDegree_free
    (X : Type*) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (i : ℕ) :
    Module.Free ℤ ((cellularChainComplex X data).X i) := by
  -- Identify the degree-`i` chain group with the free abelian group on the `i`-cells.
  simpa [cellularChainComplex, cellularChainGroup_def] using
    (inferInstance : Module.Free ℤ (FreeAbelianGroup (cellularCell X i)))

/-- Helper for Problem 13.6.4: each degree of a chosen cellular chain complex is projective,
because cellular chains are free abelian groups on the cells in that degree. -/
theorem cellularChainComplexDegree_projective
    (X : Type*) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (i : ℕ) :
    Projective ((cellularChainComplex X data).X i) := by
  -- First record the stronger free-module structure on the degree-`i` cellular chain group.
  let _ : Module.Free ℤ ((cellularChainComplex X data).X i) :=
    cellularChainComplexDegree_free X data i
  -- Then let the standard free-implies-projective instance on `ModuleCat ℤ` finish.
  infer_instance

/-- Helper for Problem 13.6.4: each degree of a chosen cellular chain complex is flat over `ℤ`,
so the product Kunneth sequence can use cellular chain groups without any extra algebraic work.
-/
theorem cellularChainComplexDegree_flat
    (X : Type*) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (data : CellularDifferentialFamily X) (i : ℕ) :
    Module.Flat ℤ ((cellularChainComplex X data).X i) := by
  -- First promote the free cellular chain group to a projective object of `ModuleCat ℤ`.
  let _ : Projective ((cellularChainComplex X data).X i) :=
    cellularChainComplexDegree_projective X data i
  -- Then the standard `projective => flat` instance over `ℤ` finishes the side condition.
  infer_instance

/-- Helper for Problem 13.6.4: once the actual integral homology is identified with any
intermediate model and that intermediate model is identified with the explicit answer, the desired
comparison follows by composition. -/
theorem sphereProductIntegralHomologyComparisonOfIntermediateModel
    {m n k : ℕ} {M : ModuleCat ℤ}
    (hToIntermediate : Nonempty (sphereProductIntegralHomologyGroup m n k ≅ M))
    (hIntermediateToModel : Nonempty (M ≅ sphereProductHomology m n k)) :
    Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k) := by
  -- Compose the singular-to-intermediate and intermediate-to-model isomorphisms.
  rcases hToIntermediate with ⟨e₁⟩
  rcases hIntermediateToModel with ⟨e₂⟩
  exact ⟨e₁ ≪≫ e₂⟩

/-- Helper for Problem 13.6.4: if an intermediate model is definitionally the explicit answer,
then the singular-to-intermediate comparison already yields the desired computation. -/
theorem sphereProductIntegralHomologyComparisonOfIntermediateModelEq
    {m n k : ℕ} {M : ModuleCat ℤ}
    (hToIntermediate : Nonempty (sphereProductIntegralHomologyGroup m n k ≅ M))
    (hIntermediateToModel : M = sphereProductHomology m n k) :
    Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k) := by
  -- Convert the model equality into an isomorphism and reuse the generic composition helper.
  exact sphereProductIntegralHomologyComparisonOfIntermediateModel
    hToIntermediate ⟨eqToIso hIntermediateToModel⟩

/-- Helper for Problem 13.6.4: vanishing of any intermediate model transports backward to the
actual integral homology of `S^m × S^n`. -/
theorem sphereProductIntegralHomologyIsZeroOfIntermediateModel
    {m n k : ℕ} {M : ModuleCat ℤ}
    (hToIntermediate : Nonempty (sphereProductIntegralHomologyGroup m n k ≅ M))
    (hzero : IsZero M) :
    IsZero (sphereProductIntegralHomologyGroup m n k) := by
  -- Move the zero-object statement back along the chosen comparison isomorphism.
  rcases hToIntermediate with ⟨e⟩
  exact IsZero.of_iso hzero e

/-- Helper for Problem 13.6.4: the zeroth integral homology of a product of positive-dimensional
spheres is the connected-space answer `ℤ`. -/
private theorem sphereProductZeroDegreeComparisonOfPositive
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nonempty (sphereProductIntegralHomologyGroup m n 0 ≅ sphereProductHomology m n 0) := by
  let _ : PathConnectedSpace (TopCat.of (TopCat.sphere m × TopCat.sphere n)) :=
    sphereProductPathConnectedSpace_of_pos hm hn
  -- First identify the actual zeroth homology with `ℤ`, then rewrite the explicit model branch.
  exact sphereProductIntegralHomologyComparisonOfIntermediateModelEq
    (m := m) (n := n) (k := 0)
    (M := ModuleCat.of ℤ ℤ)
    (by
      simpa [sphereProductIntegralHomologyGroup] using
        (pathConnectedIntegralHomologyZeroIso
          (TopCat.of (TopCat.sphere m × TopCat.sphere n))))
    (sphereProductHomology_positive_zero m n hm hn).symm

/-- Helper for Problem 13.6.4: compare the actual integral singular homology of `S^m × S^n`
with the explicit computation `sphereProductHomology m n k`. -/
theorem sphereProductSingularToExplicitComparison
    (m n k : ℕ) :
    Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k) := by
  -- Route correction: the degree-zero connected branch is now closed directly through the local
  -- path-connected `H₀ ≅ ℤ` bridge. The remaining frontier is genuinely the one-zero-factor
  -- component count and the positive-degree cellular/Kunneth comparison.
  by_cases hk : k = 0
  · subst hk
    by_cases hm : m = 0
    · subst m
      by_cases hn : n = 0
      · -- The double-zero product is a discrete four-point space, so `H₀` is free of rank `4`.
        subst n
        exact sphereProductIntegralHomologyComparisonOfIntermediateModelEq
          (m := 0) (n := 0) (k := 0)
          (M := ModuleCat.of ℤ (Fin 4 → ℤ))
          sphereZeroSquareIntegralHomologyZeroIso
          sphereProductHomology_doubleZeroFactor_zero.symm
      · -- If exactly one factor is `S⁰`, retract onto that factor and use the computed `H₀(S⁰)`.
        exact sphereProductIntegralHomologyComparisonOfIntermediateModelEq
          (m := 0) (n := n) (k := 0)
          (M := ModuleCat.of ℤ (ℤ × ℤ))
          (sphereProductSingleZeroFactorIntegralHomologyZeroIso
            0 n (Or.inl rfl) (by
              intro hBoth
              exact hn hBoth.2))
          (sphereProductHomology_zeroDegree_of_singleZeroFactor
            0 n (Or.inl rfl) (by
              intro hBoth
              exact hn hBoth.2)).symm
    · by_cases hn : n = 0
      · -- The symmetric one-zero-factor case uses the same retract argument onto `S⁰`.
        subst n
        exact sphereProductIntegralHomologyComparisonOfIntermediateModelEq
          (m := m) (n := 0) (k := 0)
          (M := ModuleCat.of ℤ (ℤ × ℤ))
          (sphereProductSingleZeroFactorIntegralHomologyZeroIso
            m 0 (Or.inr rfl) (by
              intro hBoth
              exact hm hBoth.1))
          (sphereProductHomology_zeroDegree_of_singleZeroFactor
            m 0 (Or.inr rfl) (by
              intro hBoth
              exact hm hBoth.1)).symm
      · -- Both factors are positive-dimensional, so the product is path connected and `H₀ = ℤ`.
        exact sphereProductZeroDegreeComparisonOfPositive m n
          (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  · -- TODO for Problem 13.6.4: in positive degree, import the product-cellular comparison from
    -- Theorem 13.4.1, compare the product with the tensor of the sphere cellular chain models,
    -- and collapse the resulting Chapter 17 Kunneth sequence to the explicit model.
    sorry

/-- The actual integral singular homology of `S^m × S^n` is compared to the explicit computation
`sphereProductHomology m n k` by reducing to the dedicated comparison helper. -/
theorem sphereProductIntegralHomologyComparison
    (m n k : ℕ) :
    Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k) := by
  -- Keep the public theorem short: the single remaining frontier is the dedicated comparison
  -- helper above.
  exact sphereProductSingularToExplicitComparison m n k

/-- Helper for Problem 13.6.4: compose the comparison isomorphism with a concrete model equality
to obtain the desired integral homology computation. -/
theorem sphereProductIntegralHomologyIsoOfModelEq
    {m n k : ℕ} {M : ModuleCat ℤ}
    (hcmp : Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k))
    (hModel : sphereProductHomology m n k = M) :
    Nonempty (sphereProductIntegralHomologyGroup m n k ≅ M) := by
  -- Compose the comparison isomorphism with the isomorphism induced by the explicit model
  -- equality.
  rcases hcmp with ⟨e⟩
  refine ⟨e ≪≫ eqToIso hModel⟩

/-- Helper for Problem 13.6.4: transport vanishing from the explicit model to the actual integral
homology object of `S^m × S^n`. -/
theorem sphereProductIntegralHomologyIsZeroOfModel
    {m n k : ℕ}
    (hcmp : Nonempty (sphereProductIntegralHomologyGroup m n k ≅ sphereProductHomology m n k))
    (hzero : IsZero (sphereProductHomology m n k)) :
    IsZero (sphereProductIntegralHomologyGroup m n k) := by
  -- Move the zero-object statement across the comparison isomorphism.
  rcases hcmp with ⟨e⟩
  exact IsZero.of_iso hzero e

/-- Problem 13.6.4 (1): if `m` and `n` are positive, then the degree-`0` integral homology group
of `S^m × S^n` is infinite cyclic. -/
theorem sphereProductIntegralHomologyPositiveZero
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nonempty (sphereProductIntegralHomologyGroup m n 0 ≅ ModuleCat.of ℤ ℤ) := by
  -- Transport the degree-`0` model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n 0)
    (sphereProductHomology_positive_zero m n hm hn)

/-- Problem 13.6.4 (2): if `m` and `n` are positive and distinct, then the degree-`m` integral
homology group of `S^m × S^n` is infinite cyclic. -/
theorem sphereProductIntegralHomologyPositiveLeft
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Nonempty (sphereProductIntegralHomologyGroup m n m ≅ ModuleCat.of ℤ ℤ) := by
  -- Transport the degree-`m` model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n m)
    (sphereProductHomology_positive_left m n hm hn hmn)

/-- Problem 13.6.4 (3): if `m` and `n` are positive and distinct, then the degree-`n` integral
homology group of `S^m × S^n` is infinite cyclic. -/
theorem sphereProductIntegralHomologyPositiveRight
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Nonempty (sphereProductIntegralHomologyGroup m n n ≅ ModuleCat.of ℤ ℤ) := by
  -- Transport the degree-`n` model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n n)
    (sphereProductHomology_positive_right m n hm hn hmn)

/-- Problem 13.6.4 (4): if `m` and `n` are equal and positive, then the middle integral homology
group of `S^m × S^m` is `ℤ × ℤ`. -/
theorem sphereProductIntegralHomologyPositiveDiagonal
    (m n : ℕ) (hm : 0 < m) (hmn : m = n) :
    Nonempty (sphereProductIntegralHomologyGroup m n m ≅ ModuleCat.of ℤ (ℤ × ℤ)) := by
  -- Transport the diagonal model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n m)
    (sphereProductHomology_positive_diagonal m n hm hmn)

/-- Problem 13.6.4 (5): if `m` and `n` are positive, then the top integral homology group of
`S^m × S^n` in degree `m + n` is infinite cyclic. -/
theorem sphereProductIntegralHomologyPositiveTop
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nonempty (sphereProductIntegralHomologyGroup m n (m + n) ≅ ModuleCat.of ℤ ℤ) := by
  -- Transport the top-degree model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n (m + n))
    (sphereProductHomology_positive_top m n hm hn)

/-- Problem 13.6.4 (6): if `m` and `n` are positive, then every other integral homology group of
`S^m × S^n` is zero. -/
theorem sphereProductIntegralHomologyPositiveIsZero
    (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk0 : k ≠ 0) (hkm : k ≠ m) (hkn : k ≠ n) (hktop : k ≠ m + n) :
    IsZero (sphereProductIntegralHomologyGroup m n k) := by
  -- Transport the vanishing model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsZeroOfModel
    (sphereProductIntegralHomologyComparison m n k)
    (sphereProductHomology_positive_isZero m n k hm hn hk0 hkm hkn hktop)

/-- Problem 13.6.4 (7): if exactly one factor is `S^0`, then the degree-`0` integral homology
group of the product is `ℤ × ℤ`. -/
theorem sphereProductIntegralHomologySingleZeroFactorZero
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n) :
    Nonempty (sphereProductIntegralHomologyGroup m n 0 ≅ ModuleCat.of ℤ (ℤ × ℤ)) := by
  -- Transport the degree-`0` one-zero-factor model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n 0)
    (sphereProductHomology_singleZeroFactor_zero m n hzero hpos)

/-- Problem 13.6.4 (8): if exactly one factor is `S^0`, then the top integral homology group of
the product in degree `m + n` is `ℤ × ℤ`. -/
theorem sphereProductIntegralHomologySingleZeroFactorTop
    (m n : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n) :
    Nonempty (sphereProductIntegralHomologyGroup m n (m + n) ≅
      ModuleCat.of ℤ (ℤ × ℤ)) := by
  -- Transport the top-degree one-zero-factor model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison m n (m + n))
    (sphereProductHomology_singleZeroFactor_top m n hzero hpos)

/-- Problem 13.6.4 (9): if exactly one factor is `S^0`, then the remaining integral homology
groups of the product are zero. -/
theorem sphereProductIntegralHomologySingleZeroFactorIsZero
    (m n k : ℕ) (hzero : m = 0 ∨ n = 0) (hpos : 0 < m + n)
    (hk0 : k ≠ 0) (hktop : k ≠ m + n) :
    IsZero (sphereProductIntegralHomologyGroup m n k) := by
  -- Transport the one-zero-factor vanishing computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsZeroOfModel
    (sphereProductIntegralHomologyComparison m n k)
    (sphereProductHomology_singleZeroFactor_isZero m n k hzero hpos hk0 hktop)

/-- Problem 13.6.4 (10): the degree-`0` integral homology group of `S^0 × S^0` is free of rank
`4`. -/
theorem sphereProductIntegralHomologyDoubleZeroFactorZero :
    Nonempty (sphereProductIntegralHomologyGroup 0 0 0 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  -- Transport the `S^0 × S^0` degree-`0` model computation across the comparison isomorphism.
  exact sphereProductIntegralHomologyIsoOfModelEq
    (sphereProductIntegralHomologyComparison 0 0 0)
    sphereProductHomology_doubleZeroFactor_zero

/-- Problem 13.6.4 (11): every positive-degree integral homology group of `S^0 × S^0` is zero. -/
theorem sphereProductIntegralHomologyDoubleZeroFactorIsZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero (sphereProductIntegralHomologyGroup 0 0 k) := by
  -- Transport the positive-degree `S^0 × S^0` vanishing computation across the comparison
  -- isomorphism.
  exact sphereProductIntegralHomologyIsZeroOfModel
    (sphereProductIntegralHomologyComparison 0 0 k)
    (sphereProductHomology_doubleZeroFactor_isZero k hk)
