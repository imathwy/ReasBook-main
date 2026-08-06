import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_8_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology

open AlgebraicTopology CategoryTheory Limits Metric Topology

noncomputable section

-- This file uses the chapter-level owner `integralSingularHomology` for integer coefficients and
-- `singularHomologyFunctor` for `ZMod p` coefficients, together with the canonical orbit-quotient
-- notation `X /[G]`.

/-- The unit sphere in `ℂ^n`, viewed as a concrete model of `S^{2n-1}`. -/
abbrev ComplexLensSphere (n : ℕ) := sphere (0 : EuclideanSpace ℂ (Fin n)) 1

/-- The monoid homomorphism sending a `p`th root of unity in `ℂ` to the corresponding point of
the complex unit circle. -/
noncomputable def rootsOfUnitySphereHom (p : ℕ) [NeZero p] :
    rootsOfUnity p ℂ →* sphere (0 : ℂ) 1 where
  toFun ζ := by
    refine ⟨((ζ : ℂˣ) : ℂ), ?_⟩
    exact mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity ζ.2)
  map_one' := by
    ext
    rfl
  map_mul' ζ ξ := by
    ext
    rfl

/-- The natural action of the `p`th roots of unity on the complex unit sphere `S^{2n-1}` by
scalar multiplication. -/
instance rootsOfUnityComplexLensSphereMulAction (p n : ℕ) [NeZero p] :
    MulAction (rootsOfUnity p ℂ) (ComplexLensSphere n) :=
  MulAction.compHom _ (rootsOfUnitySphereHom p)

/-- The standard quotient model of the lens space `L^n = S^{2n-1} / (ℤ / p)`, realized as the
orbit space of the scalar action of the `p`th roots of unity on the unit sphere in `ℂ^n`. -/
abbrev LensSpace (p n : ℕ) [NeZero p] :=
  ComplexLensSphere n /[rootsOfUnity p ℂ]

/-- The integral singular homology of the lens space `L^n`. -/
abbrev lensSpaceIntegralHomology (p n q : ℕ) [NeZero p] : ModuleCat ℤ :=
  integralSingularHomology q (TopCat.of (LensSpace p n))

/-- The `ZMod p`-valued singular homology of the lens space `L^n`. -/
abbrev lensSpaceModPHomology (p n q : ℕ) [NeZero p] : ModuleCat (ZMod p) :=
  ((singularHomologyFunctor (ModuleCat (ZMod p)) q).obj (ModuleCat.of (ZMod p) (ZMod p))).obj
    (TopCat.of (LensSpace p n))

/-- Unfolding `lensSpaceIntegralHomology` recovers the chapter-level integral singular homology
owner on `LensSpace p n`. -/
theorem lensSpaceIntegralHomology_def (p n q : ℕ) [NeZero p] :
    lensSpaceIntegralHomology p n q = integralSingularHomology q (TopCat.of (LensSpace p n)) :=
  rfl

/-- Unfolding `lensSpaceModPHomology` recovers the constant-coefficient singular homology owner on
`LensSpace p n` with coefficients in `ZMod p`. -/
theorem lensSpaceModPHomology_def (p n q : ℕ) [NeZero p] :
    lensSpaceModPHomology p n q =
      ((singularHomologyFunctor (ModuleCat (ZMod p)) q).obj
        (ModuleCat.of (ZMod p) (ZMod p))).obj (TopCat.of (LensSpace p n)) :=
  rfl

/-- Helper for Problem 13.6.5: the unit sphere in `ℂ^n` is path connected once `n > 0`. -/
private theorem complexLensSphere_pathConnectedSpace_of_pos {n : ℕ} (hn : 0 < n) :
    PathConnectedSpace (ComplexLensSphere n) := by
  -- Convert the positivity hypothesis into the real-rank condition used by
  -- `isPathConnected_sphere`.
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℂ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_real_of_complex, finrank_euclideanSpace_fin]
    have hnat : 1 < 2 * n := by
      omega
    exact_mod_cast hnat
  -- The sphere in a real vector space of dimension at least two is path connected.
  exact isPathConnected_iff_pathConnectedSpace.mp <| by
    simpa [ComplexLensSphere] using
      (isPathConnected_sphere
        hdim
        (0 : EuclideanSpace ℂ (Fin n))
        (by norm_num : 0 ≤ (1 : ℝ)))

/-- Helper for Problem 13.6.5: the orbit quotient `LensSpace p n` is path connected once `n > 0`.
-/
private theorem lensSpace_pathConnectedSpace_of_pos (p n : ℕ) [NeZero p] (hn : 0 < n) :
    PathConnectedSpace (LensSpace p n) := by
  -- Quotients preserve path connectedness, so it suffices to work on the sphere model.
  let _ : PathConnectedSpace (ComplexLensSphere n) := complexLensSphere_pathConnectedSpace_of_pos hn
  change PathConnectedSpace (Quotient (MulAction.orbitRel (rootsOfUnity p ℂ) (ComplexLensSphere n)))
  exact Quotient.mk''_surjective.pathConnectedSpace continuous_quotient_mk'

/-- Helper for Problem 13.6.5: a positive-dimensional lens space has a single path component. -/
private theorem lensSpace_zerothHomotopy_subsingleton (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Subsingleton (ZerothHomotopy (LensSpace p n)) := by
  let _ : PathConnectedSpace (LensSpace p n) := lensSpace_pathConnectedSpace_of_pos p n hn
  -- Path connectedness identifies every pair of points in the quotient.
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (PathConnectedSpace.joined x y)

/-- Helper for Problem 13.6.5: a positive-dimensional lens space has exactly one path component.
-/
private theorem lensSpace_zerothHomotopy_unique_of_pos (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (Unique (ZerothHomotopy (LensSpace p n))) := by
  -- Use the path-connectedness criterion phrased in terms of zeroth homotopy.
  let _ : PathConnectedSpace (LensSpace p n) := lensSpace_pathConnectedSpace_of_pos p n hn
  rcases
      (pathConnectedSpace_iff_zerothHomotopy (X := LensSpace p n)).mp inferInstance with
    ⟨hne, hsub⟩
  rcases hne with ⟨x⟩
  -- Package the unique path component explicitly for later `H₀`-comparison use.
  exact ⟨{ default := x, uniq := fun y ↦ hsub.elim y x }⟩

/-- Helper for Problem 13.6.5: the degree-zero unit-coefficient singular homology of a point is
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

/-- Helper for Problem 13.6.5: the degree-`n` singular chains of `X` with coefficients in `R`
are the degree-`n` term of the ordinary singular chain complex with constant coefficients
`ModuleCat.of R R`. -/
private abbrev unitCoefficientSingularChainDegree
    (R : Type) [CommRing R] (X : TopCat) (n : ℕ) : ModuleCat R :=
  ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X).X n)

/-- Helper for Problem 13.6.5: the `n`-simplices of the singular simplicial set of `X`. -/
private abbrev singularSSetSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Helper for Problem 13.6.5: degree-zero singular chains are the coproduct of one copy of `R`
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

/-- Helper for Problem 13.6.5: in degree `k`, the unit-coefficient singular-chain map induced by
`f` is the coproduct map on singular `k`-simplices. -/
private theorem unitCoefficientSingularChainDegreeMap_eq_sigmaMap'
    (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f).f k) =
      Sigma.map'
        (fun σ : singularSSetSimplex X k ↦
          (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk k)) σ)
        (fun _ ↦ 𝟙 (ModuleCat.of R R)) :=
  rfl

/-- Helper for Problem 13.6.5: the inverse of the unique-index coproduct is the unique coproduct
leg. -/
@[simp] private theorem coproductUniqueIso_inv_eq_unitLeg_unitCoefficients
    (R : Type) [CommRing R] :
    (coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of R R)).inv =
      Sigma.ι (fun _ : Unit ↦ ModuleCat.of R R) () := by
  -- The `simps` formula for `coproductUniqueIso` already identifies the inverse with the unique
  -- colimit injection.
  simp [coproductUniqueIso_inv]

/-- Helper for Problem 13.6.5: the unique `0`-simplex of `Unit` is sent to `x` by the constant
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

/-- Helper for Problem 13.6.5: reindexing the degree-zero simplex coproduct by points sends the
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

/-- Helper for Problem 13.6.5: postcomposing a degree-zero simplex leg with the point/simplex
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

/-- Helper for Problem 13.6.5: for `TopCat.of Unit`, the inverse of the degree-zero
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

/-- Helper for Problem 13.6.5: before reindexing simplices by points, the point inclusion
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

/-- Helper for Problem 13.6.5: on degree-zero chains, the point inclusion `Unit ⟶ X` sends the
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

/-- Helper for Problem 13.6.5: the canonical map from degree-zero chains onto `H₀(X; R)` is
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

/-- Helper for Problem 13.6.5: the degree-zero class of the `x`-indexed chain generator agrees
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

/-- Helper for Problem 13.6.5: a path between `x` and `y` identifies the two induced maps on
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

/-- Helper for Problem 13.6.5: in a path-connected space, every point inclusion `Unit ⟶ X`
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

/-- Helper for Problem 13.6.5: the inclusion of a chosen basepoint splits after applying zeroth
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

/-- Helper for Problem 13.6.5: in a path-connected space, the chosen basepoint inclusion
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

/-- Helper for Problem 13.6.5: a path-connected space has degree-zero unit-coefficient singular
homology equal to the coefficient module. -/
theorem unitCoefficientHomologyZeroIsoOfPathConnected
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

section PrimeLensSpace

variable (p n : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- Helper for Problem 13.6.5: the graded `ℤ`-modules underlying the parity-model chain complex
for `L^n`, with one copy of `ℤ` in each degree `q ≤ 2 * n - 1` and zero above that range. -/
def lensSpaceParityChainComplexObj (n : ℕ) : ℕ → ModuleCat ℤ
  | q => if q ≤ 2 * n - 1 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ (Fin 0 → ℤ)

/-- Helper for Problem 13.6.5: the parity-model boundary in degree `m + 1 → m`, given by `0` in
odd degree and multiplication by `p` in even degree, with zero differential above the top cell. -/
def lensSpaceParityChainComplexBoundary (p n : ℕ) (m : ℕ) :
    lensSpaceParityChainComplexObj n (m + 1) ⟶ lensSpaceParityChainComplexObj n m :=
  if hm : m + 1 ≤ 2 * n - 1 then
    (eqToHom (by
      simp [lensSpaceParityChainComplexObj, hm])) ≫
      (if Odd (m + 1) then
        0
      else
        ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
      (eqToHom (by
        simp [lensSpaceParityChainComplexObj, Nat.le_of_succ_le hm]))
  else
    0

/-- Helper for Problem 13.6.5: the parity-model boundary maps for `L^n` square to zero. -/
theorem lensSpaceParityChainComplexBoundary_sq (p n m : ℕ) :
    lensSpaceParityChainComplexBoundary p n (m + 1) ≫
      lensSpaceParityChainComplexBoundary p n m = 0 := by
  -- Consecutive differentials alternate between `0` and multiplication by `p`,
  -- so one of the two factors is always zero below the top degree.
  by_cases hm : m + 2 ≤ 2 * n - 1
  · have hm' : m + 1 ≤ 2 * n - 1 := Nat.le_trans (Nat.le_succ (m + 1)) hm
    by_cases hodd : Odd (m + 1)
    · simp [lensSpaceParityChainComplexBoundary, hm, hm', hodd]
    · have hmEven : Even (m + 1) := Nat.not_odd_iff_even.mp hodd
      have hodd' : Odd (m + 2) := by
        simpa [Nat.add_assoc] using hmEven.add_odd odd_one
      simp [lensSpaceParityChainComplexBoundary, hm, hm', hodd, hodd']
  · simp [lensSpaceParityChainComplexBoundary, hm]

/-- Helper for Problem 13.6.5: the explicit integral parity-model chain complex for `L^n`. -/
abbrev lensSpaceParityChainComplex (p n : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (lensSpaceParityChainComplexObj n)
    (lensSpaceParityChainComplexBoundary p n)
    (lensSpaceParityChainComplexBoundary_sq p n)

/-- Helper for Problem 13.6.5: in the integral parity model for `L^n`, degree `q ≤ 2 * n - 1`
has chain group `ℤ`. -/
@[simp] theorem lensSpaceParityChainComplex_X_of_le
    (p n q : ℕ) (hq : q ≤ 2 * n - 1) :
    (lensSpaceParityChainComplex p n).X q = ModuleCat.of ℤ ℤ := by
  -- Unfold the explicit chain-model object in the in-range case.
  rw [ChainComplex.of_x]
  simp [lensSpaceParityChainComplexObj, hq]

/-- Helper for Problem 13.6.5: in the integral parity model for `L^n`, degrees above `2 * n - 1`
have zero chain group. -/
@[simp] theorem lensSpaceParityChainComplex_X_of_gt
    (p n q : ℕ) (hq : 2 * n - 1 < q) :
    (lensSpaceParityChainComplex p n).X q = ModuleCat.of ℤ (Fin 0 → ℤ) := by
  -- Above the top cell degree, the model has no generators.
  rw [ChainComplex.of_x]
  simp [lensSpaceParityChainComplexObj, Nat.not_le.mpr hq]

/-- Helper for Problem 13.6.5: if `(k : ℕ) ≤ m`, then also `k.natPred ≤ m`. -/
private theorem lensSpaceNatPred_le (k : ℕ+) {m : ℕ} (hkm : (k : ℕ) ≤ m) :
    k.natPred ≤ m :=
  le_trans (by simpa [PNat.natPred_add_one] using Nat.le_succ k.natPred) hkm

/-- Helper for Problem 13.6.5: the degree-`k` differential of the integral parity model,
transported to the standard rank-one coordinates on source and target chain groups. -/
def lensSpaceParityDifferential
    (p n : ℕ) (k : ℕ+) (hkn : (k : ℕ) ≤ 2 * n - 1) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  (eqToIso (lensSpaceParityChainComplex_X_of_le p n (k : ℕ) hkn).symm).hom ≫
    (lensSpaceParityChainComplex p n).d (k : ℕ) k.natPred ≫
      (eqToIso
        (lensSpaceParityChainComplex_X_of_le p n k.natPred
          (lensSpaceNatPred_le k hkn))).hom

/-- Helper for Problem 13.6.5: in the integral parity model, the transported degree-`k`
differential is `0` for odd `k` and multiplication by `p` for even `k ≤ 2 * n - 1`. -/
@[simp] theorem lensSpaceParityDifferential_eq
    (p n : ℕ) (k : ℕ+) (hkn : (k : ℕ) ≤ 2 * n - 1) :
    lensSpaceParityDifferential p n k hkn =
      if Odd (k : ℕ) then
        0
      else
        ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  -- Reduce to the explicit boundary formula in the rank-one coordinates.
  rcases k with ⟨k, hkpos⟩
  cases k with
  | zero => cases hkpos
  | succ m =>
      have hm : m < 2 * n - 1 := Nat.lt_of_succ_le hkn
      simp [lensSpaceParityDifferential, lensSpaceParityChainComplexBoundary, hm]

/-- Helper for Problem 13.6.5: the graded `ZMod p`-modules underlying the mod-`p` parity-model
chain complex for `L^n`, with one copy of `ZMod p` in each degree `q ≤ 2 * n - 1`. -/
def lensSpaceParityModPChainComplexObj (p n : ℕ) : ℕ → ModuleCat (ZMod p)
  | q => if q ≤ 2 * n - 1 then ModuleCat.of (ZMod p) (ZMod p)
    else ModuleCat.of (ZMod p) (Fin 0 → ZMod p)

/-- Helper for Problem 13.6.5: after reducing coefficients mod `p`, every parity-model
differential vanishes. -/
def lensSpaceParityModPChainComplexBoundary (p n : ℕ) (m : ℕ) :
    lensSpaceParityModPChainComplexObj p n (m + 1) ⟶ lensSpaceParityModPChainComplexObj p n m :=
  0

/-- Helper for Problem 13.6.5: the mod-`p` parity-model boundary maps square to zero. -/
theorem lensSpaceParityModPChainComplexBoundary_sq (p n m : ℕ) :
    lensSpaceParityModPChainComplexBoundary p n (m + 1) ≫
      lensSpaceParityModPChainComplexBoundary p n m = 0 := by
  -- The reduced parity model has zero differential in every degree.
  simp [lensSpaceParityModPChainComplexBoundary]

/-- Helper for Problem 13.6.5: the explicit mod-`p` parity-model chain complex for `L^n`. -/
abbrev lensSpaceParityModPChainComplex (p n : ℕ) :
    ChainComplex (ModuleCat (ZMod p)) ℕ :=
  ChainComplex.of
    (lensSpaceParityModPChainComplexObj p n)
    (lensSpaceParityModPChainComplexBoundary p n)
    (lensSpaceParityModPChainComplexBoundary_sq p n)

/-- Helper for Problem 13.6.5: in the mod-`p` parity model for `L^n`, degree `q ≤ 2 * n - 1`
has chain group `ZMod p`. -/
@[simp] theorem lensSpaceParityModPChainComplex_X_of_le
    (p n q : ℕ) (hq : q ≤ 2 * n - 1) :
    (lensSpaceParityModPChainComplex p n).X q = ModuleCat.of (ZMod p) (ZMod p) := by
  -- Unfold the explicit mod-`p` chain-model object in the in-range case.
  rw [ChainComplex.of_x]
  simp [lensSpaceParityModPChainComplexObj, hq]

/-- Helper for Problem 13.6.5: in the mod-`p` parity model for `L^n`, degrees above `2 * n - 1`
have zero chain group. -/
@[simp] theorem lensSpaceParityModPChainComplex_X_of_gt
    (p n q : ℕ) (hq : 2 * n - 1 < q) :
    (lensSpaceParityModPChainComplex p n).X q = ModuleCat.of (ZMod p) (Fin 0 → ZMod p) := by
  -- Above the top cell degree, the reduced model also has no generators.
  rw [ChainComplex.of_x]
  simp [lensSpaceParityModPChainComplexObj, Nat.not_le.mpr hq]

/-- Helper for Problem 13.6.5: every differential in the mod-`p` parity model is zero. -/
@[simp] theorem lensSpaceParityModPChainComplex_d_eq_zero
    (p n m : ℕ) :
    (lensSpaceParityModPChainComplex p n).d (m + 1) m = 0 := by
  -- The chain complex was defined with zero differential in every degree.
  have hd :
      (lensSpaceParityModPChainComplex p n).d (m + 1) m =
        lensSpaceParityModPChainComplexBoundary p n m := by
    simpa [lensSpaceParityModPChainComplex] using
      (ChainComplex.of_d
        (lensSpaceParityModPChainComplexObj p n)
        (lensSpaceParityModPChainComplexBoundary p n)
        (lensSpaceParityModPChainComplexBoundary_sq p n)
        m)
  rw [hd]
  rfl

/-- Helper for Problem 13.6.5: the zero finite-function `ZMod p`-module is a zero object in
`ModuleCat (ZMod p)`. -/
private theorem isZero_finZeroModuleModP (p : ℕ) :
    IsZero (ModuleCat.of (ZMod p) (Fin 0 → ZMod p)) := by
  -- The carrier has a unique element, so the corresponding module object is zero.
  letI : Subsingleton (Fin 0 → ZMod p) := by infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Problem 13.6.5: the cokernel of multiplication by `p` on `ℤ` is `ZMod p`. -/
theorem cokernelMulIntIdIsoZMod (p : ℕ) [NeZero p] :
    Nonempty (cokernel (ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≅
      ModuleCat.of ℤ (ZMod p)) := by
  -- Identify the categorical cokernel with the quotient by the range of `p • id`.
  let f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
    ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
  let e₁ :
      cokernel f ≅
        ModuleCat.of ℤ (ℤ ⧸ LinearMap.range (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) :=
    ModuleCat.cokernelIsoRangeQuotient f
  -- The range is the principal ideal generated by `p`.
  have hRange :
      LinearMap.range (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) =
        Ideal.span {(p : ℤ)} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, rfl⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨y, ?_⟩
      simp [mul_comm]
    · intro hx
      rw [Ideal.mem_span_singleton] at hx
      rcases hx with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [mul_comm] using hy.symm
  let e₂ :
      ModuleCat.of ℤ (ℤ ⧸ LinearMap.range (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≅
        ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    (Submodule.quotEquivOfEq _ _ hRange).toModuleIso
  -- The standard quotient-ring model of `ZMod p` finishes the identification.
  let e₃ : ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(p : ℤ)}) ≅ ModuleCat.of ℤ (ZMod p) :=
    ((Int.quotientSpanNatEquivZMod p).toAddEquiv.toIntLinearEquiv).toModuleIso
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- Helper for Problem 13.6.5: the zero finite-function `ℤ`-module is a zero object in
`ModuleCat ℤ`. -/
private theorem isZero_finZeroModuleInt :
    IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
  -- The carrier has a unique element, so the corresponding module object is zero.
  letI : Subsingleton (Fin 0 → ℤ) := by infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Problem 13.6.5: multiplication by a nonzero natural number on `ℤ` is monic as a
module morphism. -/
private theorem mono_mulIntId (p : ℕ) [NeZero p] :
    Mono (ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) := by
  -- Reduce monomorphism to injectivity of scalar multiplication on the torsion-free module `ℤ`.
  rw [ModuleCat.mono_iff_injective]
  have hpz : ((p : ℤ) : ℤ) ≠ 0 := by
    exact_mod_cast (NeZero.ne p)
  simpa using (smul_right_injective ℤ hpz)

/-- Helper for Problem 13.6.5: once the source degree lies above the top cell, the corresponding
integral parity-model differential is zero. -/
private theorem lensSpaceParityChainComplex_d_eq_zero_of_gt
    (p n m : ℕ) (hm : 2 * n - 1 < m + 1) :
    (lensSpaceParityChainComplex p n).d (m + 1) m = 0 := by
  -- Rewrite the differential through the explicit boundary owner of the parity complex.
  have hd :
      (lensSpaceParityChainComplex p n).d (m + 1) m =
        lensSpaceParityChainComplexBoundary p n m := by
    simpa [lensSpaceParityChainComplex] using
      (ChainComplex.of_d
        (lensSpaceParityChainComplexObj n)
        (lensSpaceParityChainComplexBoundary p n)
        (lensSpaceParityChainComplexBoundary_sq p n)
        m)
  -- Above the top cell, the boundary definition is already in its zero branch.
  have hBoundary : lensSpaceParityChainComplexBoundary p n m = 0 := by
    simp [lensSpaceParityChainComplexBoundary, Nat.not_le.mpr hm]
  simpa [hd] using hBoundary

/-- Helper for Problem 13.6.5: below the top degree, the actual integral parity-model
differential is the transported form of the rank-one model differential. -/
private theorem lensSpaceParityChainComplex_d_eq_transport
    (p n : ℕ) (k : ℕ+) (hkn : (k : ℕ) ≤ 2 * n - 1) :
    (lensSpaceParityChainComplex p n).d (k : ℕ) k.natPred =
      (eqToIso (lensSpaceParityChainComplex_X_of_le p n (k : ℕ) hkn)).hom ≫
        (if Odd (k : ℕ) then
          0
        else
          ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
        (eqToIso
          (lensSpaceParityChainComplex_X_of_le p n k.natPred
            (lensSpaceNatPred_le k hkn))).inv := by
  -- Undo the coordinate-change isomorphisms built into `lensSpaceParityDifferential`.
  let eSrc : (lensSpaceParityChainComplex p n).X (k : ℕ) ≅ ModuleCat.of ℤ ℤ :=
    eqToIso (lensSpaceParityChainComplex_X_of_le p n (k : ℕ) hkn)
  let eTgt : (lensSpaceParityChainComplex p n).X k.natPred ≅ ModuleCat.of ℤ ℤ :=
    eqToIso
      (lensSpaceParityChainComplex_X_of_le p n k.natPred
        (lensSpaceNatPred_le k hkn))
  have h := lensSpaceParityDifferential_eq p n k hkn
  have h' := congrArg (fun f => eSrc.hom ≫ f ≫ eTgt.inv) h
  simpa [lensSpaceParityDifferential, eSrc, eTgt, Category.assoc] using h'

/-- Helper for Problem 13.6.5: the top homology of the integral parity model is `ℤ`. -/
theorem lensSpaceParityChainComplexHomology_top
    (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty ((lensSpaceParityChainComplex p n).homology (2 * n - 1) ≅ ModuleCat.of ℤ ℤ) := by
  -- First rewrite the top outgoing differential through the transported parity model.
  have htopPos : 0 < 2 * n - 1 := by
    omega
  let topDegree : ℕ+ := ⟨2 * n - 1, htopPos⟩
  have htopOdd : Odd (2 * n - 1) := by
    rw [odd_iff_exists_bit1]
    exact ⟨n - 1, by omega⟩
  have hOut :
      (lensSpaceParityChainComplex p n).d (2 * n - 1) (2 * n - 2) = 0 := by
    -- The top differential is the odd branch of the parity formula, hence zero.
    simpa [topDegree, htopOdd, Category.assoc] using
      lensSpaceParityChainComplex_d_eq_transport p n topDegree (by rfl)
  have hIn :
      (lensSpaceParityChainComplex p n).d (2 * n) (2 * n - 1) = 0 := by
    -- The next source degree already lies above the top cell, so the incoming map vanishes.
    have hEq : 2 * n = (2 * n - 1) + 1 := by
      omega
    rw [hEq]
    exact lensSpaceParityChainComplex_d_eq_zero_of_gt p n (2 * n - 1) (by omega)
  have hnextTop :
      (ComplexShape.down ℕ).next (2 * n - 1) = 2 * n - 2 := by
    have hsucc : 2 * n - 1 = (2 * n - 2) + 1 := by
      omega
    rw [hsucc]
    simpa using ChainComplex.next_nat_succ (2 * n - 2)
  have hprevTop :
      (ComplexShape.down ℕ).prev (2 * n - 1) = 2 * n := by
    simpa using (show (2 * n - 1) + 1 = 2 * n by omega)
  -- With both adjacent differentials zero, homology identifies with the top chain group `ℤ`.
  exact ⟨HomologicalComplex.isoHomologyι (lensSpaceParityChainComplex p n) (2 * n - 1)
      (2 * n - 2) hnextTop hOut ≪≫
      (HomologicalComplex.pOpcyclesIso (lensSpaceParityChainComplex p n) (2 * n)
        (2 * n - 1) hprevTop hIn).symm ≪≫
      eqToIso (lensSpaceParityChainComplex_X_of_le p n (2 * n - 1) le_rfl)⟩

/-- Helper for Problem 13.6.5: in degree `0`, the integral parity model has homology `ℤ` once
`n > 0`. -/
theorem lensSpaceParityChainComplexHomology_zero
    (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty ((lensSpaceParityChainComplex p n).homology 0 ≅ ModuleCat.of ℤ ℤ) := by
  -- Route correction: degree `0` should be computed from the explicit parity model, not from a
  -- separate generic connected-space `H₀` bridge.
  let degree : ℕ+ := ⟨1, Nat.succ_pos 0⟩
  have hOneLeTop : (1 : ℕ) ≤ 2 * n - 1 := by
    omega
  have h10 : (lensSpaceParityChainComplex p n).d 1 0 = 0 := by
    -- The first differential is the odd-degree branch of the parity formula, hence zero.
    have hodd : Odd (1 : ℕ) := by decide
    simpa [degree, hodd, Category.assoc] using
      lensSpaceParityChainComplex_d_eq_transport p n degree hOneLeTop
  -- With vanishing incoming differential, `H₀` identifies with the degree-zero chain group `ℤ`.
  exact ⟨ChainComplex.isoHomologyι₀ (lensSpaceParityChainComplex p n) ≪≫
      (HomologicalComplex.pOpcyclesIso (lensSpaceParityChainComplex p n) 1 0
        (by simp) h10).symm ≪≫
      eqToIso (lensSpaceParityChainComplex_X_of_le p n 0 (by omega))⟩

/-- Helper for Problem 13.6.5: in even positive degrees strictly below the top cell, the outgoing
integral parity differential is monic because it transports to multiplication by `p` on `ℤ`.
-/
private theorem lensSpaceParityChainComplex_d_mono_even_lt_top
    (p n q : ℕ) [NeZero p] (hq0 : q ≠ 0) (hqeven : ¬ Odd q) (hqtop : q < 2 * n - 1) :
    Mono ((lensSpaceParityChainComplex p n).d q (q - 1)) := by
  -- First rewrite the differential through the transported rank-one parity model.
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  let degree : ℕ+ := ⟨q, hqpos⟩
  let eSrc : (lensSpaceParityChainComplex p n).X q ≅ ModuleCat.of ℤ ℤ :=
    eqToIso (lensSpaceParityChainComplex_X_of_le p n q (Nat.le_of_lt hqtop))
  let eTgt : (lensSpaceParityChainComplex p n).X (q - 1) ≅ ModuleCat.of ℤ ℤ :=
    eqToIso (lensSpaceParityChainComplex_X_of_le p n (q - 1) (by omega))
  let mulP : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
    ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
  have hTransport :
      (lensSpaceParityChainComplex p n).d q (q - 1) =
        eSrc.hom ≫ mulP ≫ eTgt.inv := by
    simpa [degree, eSrc, eTgt, mulP, hqeven, Category.assoc] using
      lensSpaceParityChainComplex_d_eq_transport p n degree (Nat.le_of_lt hqtop)
  -- Local instance justification (transported monomorphism): after rewriting, the differential is
  -- a composite of two isomorphisms with multiplication by `p`, so the existing monomorphism
  -- theorem `mono_mulIntId` is the exact canonical input for instance search.
  letI : Mono mulP := mono_mulIntId p
  rw [hTransport]
  infer_instance

/-- Helper for Problem 13.6.5: in even positive degrees strictly below the top cell, the parity
short complex is exact. -/
private theorem lensSpaceParityChainComplexExactAt_even_lt_top
    (p n q : ℕ) [NeZero p] (hq0 : q ≠ 0) (hqeven : ¬ Odd q) (hqtop : q < 2 * n - 1) :
    (lensSpaceParityChainComplex p n).ExactAt q := by
  have hprev : (ComplexShape.down ℕ).prev q = q + 1 := by
    simp
  have hnext : (ComplexShape.down ℕ).next q = q - 1 := by
    have hsucc : q = (q - 1) + 1 := by
      omega
    rw [hsucc]
    simpa using ChainComplex.next_nat_succ (q - 1)
  rw [HomologicalComplex.exactAt_iff' (K := lensSpaceParityChainComplex p n)
    (i := q + 1) (j := q) (k := q - 1) hprev hnext]
  have hqEven : Even q := Nat.not_odd_iff_even.mp hqeven
  have hSuccOdd : Odd (q + 1) := by
    simpa [Nat.add_comm] using hqEven.add_odd odd_one
  let incomingDegree : ℕ+ := ⟨q + 1, Nat.succ_pos q⟩
  have hIncomingLe : q + 1 ≤ 2 * n - 1 := by
    omega
  have hIncomingZero : (lensSpaceParityChainComplex p n).d (q + 1) q = 0 := by
    -- The incoming differential is the odd-degree branch, so the short complex starts with zero.
    simpa [incomingDegree, hSuccOdd, Category.assoc] using
      lensSpaceParityChainComplex_d_eq_transport p n incomingDegree hIncomingLe
  -- Exactness now reduces to monicity of the outgoing multiplication-by-`p` map.
  exact (((lensSpaceParityChainComplex p n).sc' (q + 1) q (q - 1)).exact_iff_mono
    hIncomingZero).2 (by
      simpa using lensSpaceParityChainComplex_d_mono_even_lt_top p n q hq0 hqeven hqtop)

/-- Helper for Problem 13.6.5: in odd degrees strictly below the top, the integral parity-model
homology is `ZMod p`. -/
theorem lensSpaceParityChainComplexHomology_odd_lt_top
    (p n q : ℕ) [NeZero p] (hqodd : Odd q) (hqtop : q < 2 * n - 1) :
    Nonempty ((lensSpaceParityChainComplex p n).homology q ≅ ModuleCat.of ℤ (ZMod p)) := by
  -- First use the odd-degree differential formula to collapse homology onto the opcycles.
  have hqpos : 0 < q := Nat.pos_of_ne_zero (fun hq0 => by simpa [hq0] using hqodd)
  let degree : ℕ+ := ⟨q, hqpos⟩
  have hqle : q ≤ 2 * n - 1 := Nat.le_of_lt hqtop
  have hprev : (ComplexShape.down ℕ).prev q = q + 1 := by
    simp
  have hnext : (ComplexShape.down ℕ).next q = q - 1 := by
    have hsucc : q = (q - 1) + 1 := by
      omega
    rw [hsucc]
    simpa using ChainComplex.next_nat_succ (q - 1)
  have hOut : (lensSpaceParityChainComplex p n).d q (q - 1) = 0 := by
    simpa [degree, hqodd, Category.assoc] using
      lensSpaceParityChainComplex_d_eq_transport p n degree hqle
  -- Then identify the incoming differential with multiplication by `p` on `ℤ`.
  let incomingDegree : ℕ+ := ⟨q + 1, Nat.succ_pos q⟩
  have hIncomingLe : q + 1 ≤ 2 * n - 1 := by
    omega
  have hqSuccEven : Even (q + 1) := by
    simpa [Nat.add_comm] using hqodd.add_odd odd_one
  have hqSuccNotOdd : ¬ Odd (q + 1) := Nat.not_odd_iff_even.mpr hqSuccEven
  let eSrc : (lensSpaceParityChainComplex p n).X (q + 1) ≅ ModuleCat.of ℤ ℤ :=
    eqToIso (lensSpaceParityChainComplex_X_of_le p n (q + 1) (by omega))
  let eTgt : (lensSpaceParityChainComplex p n).X q ≅ ModuleCat.of ℤ ℤ :=
    eqToIso (lensSpaceParityChainComplex_X_of_le p n q hqle)
  let mulP : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
    ModuleCat.ofHom (((p : ℤ) : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
  have hCokernelSquare :
      (lensSpaceParityChainComplex p n).d (q + 1) q ≫ eTgt.hom =
        eSrc.hom ≫ mulP := by
    have hTransport :
        (lensSpaceParityChainComplex p n).d (q + 1) q =
          eSrc.hom ≫ mulP ≫ eTgt.inv := by
      simpa [incomingDegree, eSrc, eTgt, mulP, hqSuccNotOdd, Category.assoc] using
        lensSpaceParityChainComplex_d_eq_transport p n incomingDegree hIncomingLe
    calc
      (lensSpaceParityChainComplex p n).d (q + 1) q ≫ eTgt.hom =
          (eSrc.hom ≫ mulP ≫ eTgt.inv) ≫ eTgt.hom := by rw [hTransport]
      _ = eSrc.hom ≫ mulP := by simp [Category.assoc]
  rcases cokernelMulIntIdIsoZMod p with ⟨eMulP⟩
  -- The odd-degree homology is therefore the cokernel of multiplication by `p`.
  exact ⟨HomologicalComplex.isoHomologyι (lensSpaceParityChainComplex p n) q (q - 1) hnext hOut ≪≫
      (lensSpaceParityChainComplex p n).opcyclesIsoSc' (q + 1) q (q - 1) hprev hnext ≪≫
      ((lensSpaceParityChainComplex p n).sc' (q + 1) q (q - 1)).opcyclesIsoCokernel ≪≫
      cokernel.mapIso (f := (lensSpaceParityChainComplex p n).d (q + 1) q) mulP eSrc eTgt
        hCokernelSquare ≪≫
      eMulP⟩

/-- Helper for Problem 13.6.5: outside degree `0`, the top degree, and the odd degrees below the
top, the integral parity-model homology vanishes. -/
theorem lensSpaceParityChainComplexHomology_isZero
    (p n q : ℕ) [NeZero p]
    (hq0 : q ≠ 0) (hqtop : q ≠ 2 * n - 1) (hqrest : ¬ Odd q ∨ 2 * n - 1 < q) :
    IsZero ((lensSpaceParityChainComplex p n).homology q) := by
  by_cases hgt : 2 * n - 1 < q
  · have hX : IsZero ((lensSpaceParityChainComplex p n).X q) := by
      -- Above the top cell, the degree-`q` chain group is already the zero module.
      rw [lensSpaceParityChainComplex_X_of_gt p n q hgt]
      exact isZero_finZeroModuleInt
    have hSc : IsZero (((lensSpaceParityChainComplex p n).sc q).X₂) := by
      simpa [HomologicalComplex.sc] using hX
    -- The short-complex homology vanishes because its middle object is zero.
    simpa [HomologicalComplex.homology] using
      (ShortComplex.isZero_homology_of_isZero_X₂
        (S := (lensSpaceParityChainComplex p n).sc q) hSc)
  · have hlt : q < 2 * n - 1 := by
      omega
    have hqeven : ¬ Odd q := by
      cases hqrest with
      | inl h => exact h
      | inr h => exact False.elim (hgt h)
    -- Below the top in even degree, exactness of the parity short complex forces zero homology.
    exact
      (lensSpaceParityChainComplexExactAt_even_lt_top p n q hq0 hqeven hlt).isZero_homology

/-- Helper for Problem 13.6.5: once the actual zeroth integral homology of `LensSpace p n` is
identified with `ℤ`, the degree-zero comparison to the parity model is immediate. -/
private theorem lensSpaceZeroDegreeIntegralComparisonOfActualHomology
    (p n : ℕ) [NeZero p] (hn : 0 < n)
    (hActual : Nonempty (lensSpaceIntegralHomology p n 0 ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty (lensSpaceIntegralHomology p n 0 ≅ (lensSpaceParityChainComplex p n).homology 0) := by
  rcases hActual with ⟨eActual⟩
  rcases lensSpaceParityChainComplexHomology_zero p n hn with ⟨eParity⟩
  -- The degree-zero branch only needs the actual `H₀` computation and the already proved parity
  -- model computation.
  exact ⟨eActual ≪≫ eParity.symm⟩

/-- Helper for Problem 13.6.5: a positive-dimensional lens space has zeroth integral homology
`ℤ`. -/
private theorem lensSpaceIntegralHomologyZeroIsoInt
    (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (lensSpaceIntegralHomology p n 0 ≅ ModuleCat.of ℤ ℤ) := by
  -- Specialize the generic path-connected `H₀` computation to `LensSpace p n`.
  let _ : PathConnectedSpace (LensSpace p n) := lensSpace_pathConnectedSpace_of_pos p n hn
  simpa [lensSpaceIntegralHomology_def] using
    unitCoefficientHomologyZeroIsoOfPathConnected ℤ (TopCat.of (LensSpace p n))

/-- Helper for Problem 13.6.5: a positive-dimensional lens space has zeroth `ZMod p`-homology
equal to the coefficient module. -/
private theorem lensSpaceModPHomologyZeroIsoZMod
    (p n : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (lensSpaceModPHomology p n 0 ≅ ModuleCat.of (ZMod p) (ZMod p)) := by
  -- The same path-connected `H₀` argument works after changing coefficients to `ZMod p`.
  let _ : PathConnectedSpace (LensSpace p n) := lensSpace_pathConnectedSpace_of_pos p n hn
  simpa [lensSpaceModPHomology_def] using
    unitCoefficientHomologyZeroIsoOfPathConnected (ZMod p) (TopCat.of (LensSpace p n))

/-- Degree-zero mod-`p` comparison, placed before the bundled singular-to-parity comparison so
the latter does not depend on a declaration that appears later in the file. -/
private theorem lensSpaceZeroDegreeModPComparisonEarly
    (p n : ℕ) [NeZero p] (hn : 0 < n)
    (hActual : Nonempty (lensSpaceModPHomology p n 0 ≅ ModuleCat.of (ZMod p) (ZMod p))) :
    Nonempty (lensSpaceModPHomology p n 0 ≅
      (lensSpaceParityModPChainComplex p n).homology 0) := by
  rcases hActual with ⟨eActual⟩
  have h10 : (lensSpaceParityModPChainComplex p n).d 1 0 = 0 := by
    simpa using lensSpaceParityModPChainComplex_d_eq_zero p n 0
  let eParity : (lensSpaceParityModPChainComplex p n).homology 0 ≅
      ModuleCat.of (ZMod p) (ZMod p) :=
    ChainComplex.isoHomologyι₀ (lensSpaceParityModPChainComplex p n) ≪≫
      (HomologicalComplex.pOpcyclesIso (lensSpaceParityModPChainComplex p n) 1 0
        (by simp) h10).symm ≪≫
      eqToIso (lensSpaceParityModPChainComplex_X_of_le p n 0 (by omega))
  exact ⟨eActual ≪≫ eParity.symm⟩

/-- Helper for Problem 13.6.5: the unresolved absolute singular-to-cellular frontier for
`LensSpace p n` packages both the integral and mod-`p` comparisons to the explicit parity
models. -/
private theorem lensSpacePositiveDegreeSingularToParityComparison
    (p n q : ℕ) [NeZero p] (hn : 0 < n) (hq0 : q ≠ 0) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q) ∧
      Nonempty
        (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q) :=
by
  -- Route correction: keep the unresolved geometry as one bundled positive-degree frontier, rather
  -- than duplicating the same missing premise in separate integral and mod-`p` placeholders.
  -- TODO for Problem 13.6.5: build a dependency-closed standard CW owner for `LensSpace p n`,
  -- compare absolute singular homology to that actual cellular model in positive degree for `ℤ`
  -- and `ZMod p`, and then identify the transported cellular differential with the explicit parity
  -- differential already computed in this file.
  sorry

/-- Helper for Problem 13.6.5: the integral positive-degree comparison is the integral component
of the single bundled singular-to-parity blocker. -/
private theorem lensSpacePositiveDegreeIntegralComparison
    (p n q : ℕ) [NeZero p] (hn : 0 < n) (hq0 : q ≠ 0) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q) := by
  -- Extract the integral comparison from the single positive-degree frontier.
  exact (lensSpacePositiveDegreeSingularToParityComparison p n q hn hq0).1

/-- Helper for Problem 13.6.5: the mod-`p` positive-degree comparison is the coefficient-`ZMod p`
component of the single bundled singular-to-parity blocker. -/
private theorem lensSpacePositiveDegreeModPComparison
    (p n q : ℕ) [NeZero p] (hn : 0 < n) (hq0 : q ≠ 0) :
    Nonempty
      (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q) := by
  -- Extract the mod-`p` comparison from the same positive-degree frontier.
  exact (lensSpacePositiveDegreeSingularToParityComparison p n q hn hq0).2

/-- Helper for Problem 13.6.5: the positive-degree comparison frontier should return the two final
singular-to-parity isomorphisms directly, without packaging dead intermediate owners. -/
private theorem lensSpacePositiveDegreeComparisons
    (p n q : ℕ) [NeZero p] (hn : 0 < n) (hq0 : q ≠ 0) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q) ∧
      Nonempty
        (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q) := by
  -- Reuse the single bundled positive-degree comparison theorem directly.
  exact lensSpacePositiveDegreeSingularToParityComparison p n q hn hq0

/-- Helper for Problem 13.6.5: the only remaining absolute singular-to-cellular frontier for
`LensSpace p n` is the positive-degree comparison to the explicit parity models. -/
private theorem lensSpaceSingularToParityComparisonData
    (p n q : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q) ∧
      Nonempty
        (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q) :=
by
  by_cases hq0 : q = 0
  · subst hq0
    -- The degree-zero branch now closes by path connectedness plus the explicit parity `H₀`
    -- computations already proved in this file.
    constructor
    · exact lensSpaceZeroDegreeIntegralComparisonOfActualHomology p n hn
        (lensSpaceIntegralHomologyZeroIsoInt p n hn)
    · exact lensSpaceZeroDegreeModPComparisonEarly p n hn
        (lensSpaceModPHomologyZeroIsoZMod p n hn)
  · -- Route correction: only the positive-degree singular-to-parity comparison remains open.
    exact lensSpacePositiveDegreeSingularToParityComparison p n q hn hq0

/-- Helper for Problem 13.6.5: the remaining integral step is a comparison from actual singular
homology of `LensSpace p n` to the explicit parity-model chain complex. -/
theorem lensSpaceIntegralHomologyComparison
    (p n q : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q) := by
  -- Extract the integral component from the single bundled comparison blocker.
  exact (lensSpaceSingularToParityComparisonData p n q hn).1

/-- Helper for Problem 13.6.5: once the actual integral singular homology is compared to the
parity-model homology, any concrete model isomorphism can be composed in. -/
theorem lensSpaceIntegralHomologyComparisonOfIntermediateModel
    {p n q : ℕ} [NeZero p] {M : ModuleCat ℤ}
    (hToIntermediate :
      Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q))
    (hIntermediateToModel :
      Nonempty ((lensSpaceParityChainComplex p n).homology q ≅ M)) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ M) := by
  -- Compose the remaining geometric comparison with the chosen explicit parity-model computation.
  rcases hToIntermediate with ⟨e₁⟩
  rcases hIntermediateToModel with ⟨e₂⟩
  exact ⟨e₁ ≪≫ e₂⟩

/-- Helper for Problem 13.6.5: once the actual `ZMod p`-valued singular homology is compared to
the parity-model homology, any concrete model isomorphism can be composed in. -/
theorem lensSpaceModPHomologyComparisonOfIntermediateModel
    {p n q : ℕ} [NeZero p] {M : ModuleCat (ZMod p)}
    (hToIntermediate :
      Nonempty (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q))
    (hIntermediateToModel :
      Nonempty ((lensSpaceParityModPChainComplex p n).homology q ≅ M)) :
    Nonempty (lensSpaceModPHomology p n q ≅ M) := by
  -- Compose the missing geometric comparison with the explicit parity-model computation.
  rcases hToIntermediate with ⟨e₁⟩
  rcases hIntermediateToModel with ⟨e₂⟩
  exact ⟨e₁ ≪≫ e₂⟩

/-- Helper for Problem 13.6.5: vanishing of the integral parity-model homology transports across
any comparison from actual singular homology to that model. -/
theorem lensSpaceIntegralHomologyIsZeroOfIntermediateModel
    {p n q : ℕ} [NeZero p]
    (hToIntermediate :
      Nonempty (lensSpaceIntegralHomology p n q ≅ (lensSpaceParityChainComplex p n).homology q))
    (hzero : IsZero ((lensSpaceParityChainComplex p n).homology q)) :
    IsZero (lensSpaceIntegralHomology p n q) := by
  -- Move the zero-object statement backward along the comparison isomorphism.
  rcases hToIntermediate with ⟨e⟩
  exact IsZero.of_iso hzero e

/-- Helper for Problem 13.6.5: vanishing of the mod-`p` parity-model homology transports across
any comparison from actual singular homology to that model. -/
theorem lensSpaceModPHomologyIsZeroOfIntermediateModel
    {p n q : ℕ} [NeZero p]
    (hToIntermediate :
      Nonempty (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q))
    (hzero : IsZero ((lensSpaceParityModPChainComplex p n).homology q)) :
    IsZero (lensSpaceModPHomology p n q) := by
  -- Move the zero-object statement backward along the comparison isomorphism.
  rcases hToIntermediate with ⟨e⟩
  exact IsZero.of_iso hzero e

/-- Helper for Problem 13.6.5: in every degree `q ≤ 2 * n - 1`, the mod-`p` parity model has
homology `ZMod p`. -/
theorem lensSpaceParityModPChainComplexHomology_le_top
    (p n q : ℕ) (hq : q ≤ 2 * n - 1) :
    Nonempty ((lensSpaceParityModPChainComplex p n).homology q ≅
      ModuleCat.of (ZMod p) (ZMod p)) := by
  -- With zero differentials on both sides of degree `q`, homology identifies with the chain
  -- group in degree `q`.
  cases q with
  | zero =>
      have h10 : (lensSpaceParityModPChainComplex p n).d 1 0 = 0 := by
        simpa using lensSpaceParityModPChainComplex_d_eq_zero p n 0
      exact ⟨ChainComplex.isoHomologyι₀ (lensSpaceParityModPChainComplex p n) ≪≫
        (HomologicalComplex.pOpcyclesIso (lensSpaceParityModPChainComplex p n) 1 0
          (by simp) h10).symm ≪≫
        eqToIso (lensSpaceParityModPChainComplex_X_of_le p n 0 hq)⟩
  | succ m =>
      have hOut : (lensSpaceParityModPChainComplex p n).d (m + 1) m = 0 := by
        simpa using lensSpaceParityModPChainComplex_d_eq_zero p n m
      have hIn : (lensSpaceParityModPChainComplex p n).d (m + 2) (m + 1) = 0 := by
        simpa using lensSpaceParityModPChainComplex_d_eq_zero p n (m + 1)
      exact ⟨HomologicalComplex.isoHomologyι (lensSpaceParityModPChainComplex p n) (m + 1) m
        (by simp) hOut ≪≫
        (HomologicalComplex.pOpcyclesIso (lensSpaceParityModPChainComplex p n) (m + 2) (m + 1)
          (by simp) hIn).symm ≪≫
        eqToIso (lensSpaceParityModPChainComplex_X_of_le p n (m + 1) hq)⟩

/-- Helper for Problem 13.6.5: once the actual zeroth `ZMod p`-valued homology of `LensSpace p
n` is identified with the coefficient module, the degree-zero comparison to the parity model is
immediate. -/
private theorem lensSpaceZeroDegreeModPComparisonOfActualHomology
    (p n : ℕ) [NeZero p] (hn : 0 < n)
    (hActual : Nonempty (lensSpaceModPHomology p n 0 ≅ ModuleCat.of (ZMod p) (ZMod p))) :
    Nonempty (lensSpaceModPHomology p n 0 ≅ (lensSpaceParityModPChainComplex p n).homology 0) := by
  rcases hActual with ⟨eActual⟩
  rcases lensSpaceParityModPChainComplexHomology_le_top p n 0 (by omega) with ⟨eParity⟩
  -- The degree-zero mod-`p` branch is the same short composition as in the integral case.
  exact ⟨eActual ≪≫ eParity.symm⟩

/-- Helper for Problem 13.6.5: above degree `2 * n - 1`, the mod-`p` parity model has zero
homology because its chain group in that degree is already zero. -/
theorem lensSpaceParityModPChainComplexHomology_gt_top
    (p n q : ℕ) (hq : 2 * n - 1 < q) :
    IsZero ((lensSpaceParityModPChainComplex p n).homology q) := by
  -- The same zero-differential argument identifies homology with the zero chain group.
  cases q with
  | zero =>
      omega
  | succ m =>
      have hOut : (lensSpaceParityModPChainComplex p n).d (m + 1) m = 0 := by
        simpa using lensSpaceParityModPChainComplex_d_eq_zero p n m
      have hIn : (lensSpaceParityModPChainComplex p n).d (m + 2) (m + 1) = 0 := by
        simpa using lensSpaceParityModPChainComplex_d_eq_zero p n (m + 1)
      exact IsZero.of_iso (isZero_finZeroModuleModP p)
        (HomologicalComplex.isoHomologyι (lensSpaceParityModPChainComplex p n) (m + 1) m
          (by simp) hOut ≪≫
          (HomologicalComplex.pOpcyclesIso (lensSpaceParityModPChainComplex p n) (m + 2) (m + 1)
            (by simp) hIn).symm ≪≫
          eqToIso (lensSpaceParityModPChainComplex_X_of_gt p n (m + 1) hq))

/-- Helper for Problem 13.6.5: the missing mod-`p` step is a comparison from actual singular
homology of `LensSpace p n` to the explicit parity-model chain complex. -/
theorem lensSpaceModPHomologyComparison
    (p n q : ℕ) [NeZero p] (hn : 0 < n) :
    Nonempty (lensSpaceModPHomology p n q ≅ (lensSpaceParityModPChainComplex p n).homology q) := by
  -- Extract the mod-`p` component from the same bundled absolute comparison blocker.
  exact (lensSpaceSingularToParityComparisonData p n q hn).2

/-- Problem 13.6.5 (1): the source states this for odd prime `p`, and the same zeroth integral
homology computation holds for every prime `p`. -/
theorem lensSpace_integralHomology_zero
    (hn : 0 < n) :
    Nonempty (lensSpaceIntegralHomology p n 0 ≅ ModuleCat.of ℤ ℤ) := by
  -- Route correction: compose the remaining singular-to-cellular comparison with the completed
  -- parity-model `H₀` computation.
  exact lensSpaceIntegralHomologyComparisonOfIntermediateModel
    (lensSpaceIntegralHomologyComparison p n 0 hn)
    (lensSpaceParityChainComplexHomology_zero p n hn)

/-- Problem 13.6.5 (2): the source states this for odd prime `p`, and the same top integral
homology computation holds for every prime `p` in degree `2n - 1`. -/
theorem lensSpace_integralHomology_top
    (hn : 0 < n) :
    Nonempty (lensSpaceIntegralHomology p n (2 * n - 1) ≅ ModuleCat.of ℤ ℤ) := by
  -- Compose the missing geometric comparison with the completed top-degree parity-model
  -- computation.
  exact lensSpaceIntegralHomologyComparisonOfIntermediateModel
    (lensSpaceIntegralHomologyComparison p n (2 * n - 1) hn)
    (lensSpaceParityChainComplexHomology_top p n hn)

/-- Problem 13.6.5 (3): the source states this for odd prime `p`, and the same description of the
odd intermediate integral homology groups holds for every prime `p`. -/
theorem lensSpace_integralHomology_odd
    (q : ℕ) (hn : 0 < n)
    (hqodd : Odd q) (hqtop : q < 2 * n - 1) :
    Nonempty (lensSpaceIntegralHomology p n q ≅ ModuleCat.of ℤ (ZMod p)) := by
  -- Compose the missing geometric comparison with the completed odd-degree parity-model
  -- computation.
  exact lensSpaceIntegralHomologyComparisonOfIntermediateModel
    (lensSpaceIntegralHomologyComparison p n q hn)
    (lensSpaceParityChainComplexHomology_odd_lt_top p n q hqodd hqtop)

/-- Problem 13.6.5 (4): the source states this for odd prime `p`, and the same vanishing statement
for the remaining integral homology groups holds for every prime `p`. -/
theorem lensSpace_integralHomology_isZero
    (q : ℕ) (hn : 0 < n)
    (hq0 : q ≠ 0) (hqtop : q ≠ 2 * n - 1) (hqrest : ¬ Odd q ∨ 2 * n - 1 < q) :
    IsZero (lensSpaceIntegralHomology p n q) := by
  -- Transport the completed parity-model vanishing statement across the missing geometric
  -- comparison.
  exact lensSpaceIntegralHomologyIsZeroOfIntermediateModel
    (lensSpaceIntegralHomologyComparison p n q hn)
    (lensSpaceParityChainComplexHomology_isZero p n q hq0 hqtop hqrest)

/-- Problem 13.6.5 (5): the source states this for odd prime `p`, and the same `ZMod p`-valued
homology computation holds for every prime `p` in every degree at most `2n - 1`. -/
theorem lensSpace_modPHomology_le_top
    (q : ℕ) (hn : 0 < n) (hq : q ≤ 2 * n - 1) :
    Nonempty (lensSpaceModPHomology p n q ≅
      ModuleCat.of (ZMod p) (ZMod p)) := by
  -- Compose the remaining geometric comparison with the completed mod-`p` parity-model
  -- computation.
  exact lensSpaceModPHomologyComparisonOfIntermediateModel
    (lensSpaceModPHomologyComparison p n q hn)
    (lensSpaceParityModPChainComplexHomology_le_top p n q hq)

/-- Problem 13.6.5 (6): the source states this for odd prime `p`, and the same `ZMod p`-valued
homology vanishing statement holds for every prime `p` in every degree above `2n - 1`. -/
theorem lensSpace_modPHomology_gt_top
    (q : ℕ) (hn : 0 < n) (hq : 2 * n - 1 < q) :
    IsZero (lensSpaceModPHomology p n q) := by
  -- Transport the zero-object statement from the completed mod-`p` parity model.
  exact lensSpaceModPHomologyIsZeroOfIntermediateModel
    (lensSpaceModPHomologyComparison p n q hn)
    (lensSpaceParityModPChainComplexHomology_gt_top p n q hq)

end PrimeLensSpace
