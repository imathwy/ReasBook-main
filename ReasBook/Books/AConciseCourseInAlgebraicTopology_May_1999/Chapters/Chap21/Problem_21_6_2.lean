import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Proposition_12_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Problem_20_7_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3

open AlgebraicTopology CategoryTheory HomotopicalAlgebra Limits SpacePair ContinuousMap
open TopCat (SphereModel sphereModelHomeomorph)
open scoped Manifold Topology

noncomputable section

universe u

-- Chapter 13 already fixes `integralSingularHomology`, and mathlib exposes the canonical
-- manifold-boundary subtype `(𝓡∂ (m + 1)).boundary M`. This file states Problem 21.6.2 directly
-- against that boundary owner.

/-- Helper for Problem 21.6.2: a source-facing pair cohomology theory only needs the graded
contravariant functors, the point-space dimension axiom, and weak-equivalence invariance used
below. -/
structure PairCohomologyTheory (π : Type u) [AddCommGroup π] where
  /-- The graded contravariant functor `H^q(X, A; π)` on pairs. -/
  cohomology : ℤ → SpacePair.{u}ᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- The degree-zero cohomology of the one-point pair is the coefficient group `π`. -/
  dimensionZero :
    Nonempty ((cohomology 0).obj (Opposite.op SpacePair.point) ≅ AddCommGrpCat.of π)
  /-- The higher and lower cohomology of the one-point pair vanishes away from degree `0`. -/
  dimensionHigher (q : ℤ) (hq : q ≠ 0) :
    IsZero ((cohomology q).obj (Opposite.op SpacePair.point))
  /-- Weakly equivalent pairs induce isomorphisms in each cohomological degree. -/
  weakEquivalenceInvariant (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((cohomology q).map f.op)

/-- Helper for Problem 21.6.2: the absolute-pair functor `X ↦ (X, ∅)`. -/
private def absolutePairFunctor : TopCat.{u} ⥤ SpacePair.{u} where
  obj X := SpacePair.absolute X
  map f :=
    { hom := f
      map_subspace' := by
        intro x hx
        cases hx }
  map_id := by
    intro X
    apply SpacePair.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply SpacePair.hom_ext
    rfl

namespace PairCohomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- Helper for Problem 21.6.2: the absolute cohomology functor `X ↦ H^q(X, ∅; π)`. -/
abbrev absoluteCohomology (H : PairCohomologyTheory π) (q : ℤ) :
    TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  absolutePairFunctor.op ⋙ H.cohomology q

/-- Helper for Problem 21.6.2: weak equivalences of pairs induce cohomology isomorphisms. -/
instance map_isIso_of_weakEquivalence
    (H : PairCohomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((H.cohomology q).map f.op) :=
  H.weakEquivalenceInvariant q f

end PairCohomologyTheory

variable {m : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]

/-- Helper for Problem 21.6.2: the integral singular chain complex of a space with coefficients in
`ℤ`. This local copy avoids importing the heavier Chapter 20 cup-product file. -/
abbrev integralSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)

/-- Helper for Problem 21.6.2: the Chapter 20 owner `rSingularHomology ℤ` is the homology of the
integral singular chain complex. This is the only comparison API from Construction 20.1.4 used in
the current file. -/
noncomputable def rSingularHomologyIsoIntegralSingularHomology
    (X : TopCat) (p : ℕ) :
    rSingularHomology ℤ p X ≅ (integralSingularChainComplex X).homology p :=
  -- The standard singular-homology functor comparison already identifies constant coefficients
  -- with the ordinary integral chain complex.
  (((singularHomologyFunctor (ModuleCat ℤ) p).mapIso
      (LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ))).app X)

/-- Helper for Problem 21.6.2: ordinary integral singular homology agrees with the Chapter 20
owner `rSingularHomology ℤ` in every degree. -/
theorem integralSingularHomologyIsoRSingularHomology
    (X : TopCat) (k : ℕ) :
    Nonempty (integralSingularHomology k X ≅ rSingularHomology ℤ k X) := by
  -- Compare both homology owners with the same singular-chain homology object.
  refine ⟨?_⟩
  simpa [integralSingularHomology, integralSingularChainComplex] using
    (rSingularHomologyIsoIntegralSingularHomology X k).symm

/-- Helper for Problem 21.6.2: the Chapter 20 constant coefficient owner `constantCoefficientModule
ℤ` is canonically the ordinary unit `ℤ`-module. -/
private noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- Helper for Problem 21.6.2: a homotopy equivalence induces an isomorphism on
`rSingularHomology ℤ` in every degree. -/
theorem rSingularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (k : ℕ) :
    Nonempty (rSingularHomology ℤ k (TopCat.of X) ≅ rSingularHomology ℤ k (TopCat.of Y)) := by
  let F := (singularChainComplexFunctor (ModuleCat ℤ)).obj (constantCoefficientModule ℤ)
  let FH := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  -- The forward and inverse maps on homology are induced by the two directions of `e`.
  let f : rSingularHomology ℤ k (TopCat.of X) ⟶ rSingularHomology ℤ k (TopCat.of Y) :=
    FH.map (F.map (TopCat.ofHom e.toFun))
  let g : rSingularHomology ℤ k (TopCat.of Y) ⟶ rSingularHomology ℤ k (TopCat.of X) :=
    FH.map (F.map (TopCat.ofHom e.invFun))
  have hfg : f ≫ g = 𝟙 _ := by
    rcases e.left_inv with ⟨hLeft⟩
    have hcomp :
        HomologicalComplex.homologyMap
            (F.map (TopCat.ofHom e.toFun) ≫ F.map (TopCat.ofHom e.invFun)) k =
          𝟙 _ := by
      -- Homotopy invariance turns the left inverse homotopy into the identity on homology.
      simpa [F, rSingularHomology, Functor.map_comp] using
        TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          (C := ModuleCat ℤ) (R := constantCoefficientModule ℤ) (n := k)
          (H := (show TopCat.Homotopy
            (TopCat.ofHom (e.invFun.comp e.toFun)) (𝟙 (TopCat.of X)) from hLeft))
    calc
      f ≫ g =
          HomologicalComplex.homologyMap
            (F.map (TopCat.ofHom e.toFun) ≫ F.map (TopCat.ofHom e.invFun)) k := by
        rw [show f = HomologicalComplex.homologyMap (F.map (TopCat.ofHom e.toFun)) k by rfl]
        rw [show g = HomologicalComplex.homologyMap (F.map (TopCat.ofHom e.invFun)) k by rfl]
        simpa using
          (HomologicalComplex.homologyMap_comp
            (φ := F.map (TopCat.ofHom e.toFun))
            (ψ := F.map (TopCat.ofHom e.invFun))
            (i := k)).symm
      _ = 𝟙 _ := hcomp
  have hgf : g ≫ f = 𝟙 _ := by
    rcases e.right_inv with ⟨hRight⟩
    have hcomp :
        HomologicalComplex.homologyMap
            (F.map (TopCat.ofHom e.invFun) ≫ F.map (TopCat.ofHom e.toFun)) k =
          𝟙 _ := by
      -- The right inverse homotopy gives the second triangle identity on homology.
      simpa [F, rSingularHomology, Functor.map_comp] using
        TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          (C := ModuleCat ℤ) (R := constantCoefficientModule ℤ) (n := k)
          (H := (show TopCat.Homotopy
            (TopCat.ofHom (e.toFun.comp e.invFun)) (𝟙 (TopCat.of Y)) from hRight))
    calc
      g ≫ f =
          HomologicalComplex.homologyMap
            (F.map (TopCat.ofHom e.invFun) ≫ F.map (TopCat.ofHom e.toFun)) k := by
        rw [show g = HomologicalComplex.homologyMap (F.map (TopCat.ofHom e.invFun)) k by rfl]
        rw [show f = HomologicalComplex.homologyMap (F.map (TopCat.ofHom e.toFun)) k by rfl]
        simpa using
          (HomologicalComplex.homologyMap_comp
            (φ := F.map (TopCat.ofHom e.invFun))
            (ψ := F.map (TopCat.ofHom e.toFun))
            (i := k)).symm
      _ = 𝟙 _ := hcomp
  exact ⟨{ hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩

/-- Helper for Problem 21.6.2: the map of absolute pairs induced by a homotopy equivalence is a
weak equivalence of pairs. -/
private abbrev absolutePairMapOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    SpacePair.absolute (TopCat.of X) ⟶ SpacePair.absolute (TopCat.of Y) where
  hom := TopCat.ofHom e.toFun
  map_subspace' := by
    intro x hx
    cases hx

/-- Helper for Problem 21.6.2: absolute pairs preserve weak equivalences coming from ambient
homotopy equivalences. -/
private theorem absolutePairMapIsWeakEquivalenceOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    SpacePair.IsWeakEquivalence (absolutePairMapOfHomotopyEquiv e) := by
  -- The ambient homotopy equivalence already supplies the required inverse on the empty subspace.
  refine ⟨e, rfl, ?_⟩
  intro y hy
  cases hy

/-- Helper for Problem 21.6.2: a homotopy equivalence induces an isomorphism on the absolute
cohomology objects attached to any pair cohomology theory. -/
theorem absoluteCohomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (Hcoh : PairCohomologyTheory ℤ) (e : X ≃ₕ Y) (q : ℤ) :
    Nonempty
      (((Hcoh.absoluteCohomology q).obj (Opposite.op (TopCat.of X))) ≅
        ((Hcoh.absoluteCohomology q).obj (Opposite.op (TopCat.of Y)))) := by
  let f := absolutePairMapOfHomotopyEquiv e.symm
  let _ : WeakEquivalence f :=
    (spacePair_weakEquivalence_iff f).2
      (absolutePairMapIsWeakEquivalenceOfHomotopyEquiv e.symm)
  refine ⟨?_⟩
  simpa [PairCohomologyTheory.absoluteCohomology, absolutePairFunctor] using
    (asIso ((Hcoh.cohomology q).map f.op))

/-- Helper for Problem 21.6.2: the absolute cohomology of a contractible space agrees with the
point calculation for any pair cohomology theory. -/
theorem contractibleAbsoluteCohomologyPattern
    (Hcoh : PairCohomologyTheory ℤ) [ContractibleSpace M] :
    Nonempty
        (((Hcoh.absoluteCohomology 0).obj (Opposite.op (TopCat.of M))) ≅ AddCommGrpCat.of ℤ) ∧
      ∀ q : ℤ, q ≠ 0 →
        IsZero ((Hcoh.absoluteCohomology q).obj (Opposite.op (TopCat.of M))) := by
  rcases ContractibleSpace.hequiv_unit M with ⟨eUnit⟩
  let ePoint : Unit ≃ₕ PUnit :=
    (Homeomorph.homeomorphOfUnique Unit PUnit).toHomotopyEquiv
  let e : M ≃ₕ PUnit := eUnit.trans ePoint
  constructor
  · rcases absoluteCohomologyIsoOfHomotopyEquiv (X := M) (Y := PUnit) Hcoh e 0 with ⟨hM⟩
    rcases Hcoh.dimensionZero with ⟨hPoint⟩
    exact ⟨hM ≪≫ (by
      simpa [PairCohomologyTheory.absoluteCohomology, absolutePairFunctor, SpacePair.point] using
        hPoint)⟩
  · intro q hq
    rcases absoluteCohomologyIsoOfHomotopyEquiv (X := M) (Y := PUnit) Hcoh e q with ⟨hM⟩
    have hPoint :
        IsZero ((Hcoh.absoluteCohomology q).obj (Opposite.op (TopCat.of PUnit))) := by
      simpa [PairCohomologyTheory.absoluteCohomology, absolutePairFunctor, SpacePair.point] using
        Hcoh.dimensionHigher q hq
    exact IsZero.of_iso hPoint hM

/-- Helper for Problem 21.6.2: the zeroth `rSingularHomology ℤ` of the one-point space is `ℤ`.
-/
theorem rSingularHomologyUnitZero :
    Nonempty (rSingularHomology ℤ 0 (TopCat.of Unit) ≅ ModuleCat.of ℤ ℤ) := by
  -- Compute `H₀` of the point via the totally disconnected-space calculation and collapse the
  -- singleton coproduct.
  refine ⟨?_⟩
  exact
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat ℤ) (R := constantCoefficientModule ℤ) (X := TopCat.of Unit) ≪≫
      coproductUniqueIso (fun _ : Unit => constantCoefficientModule ℤ) ≪≫
    constantCoefficientModuleIsoInt

/-- Helper for Problem 21.6.2: the positive-degree `rSingularHomology ℤ` of the one-point space
vanishes. -/
theorem rSingularHomologyUnit_isZero_of_ne (k : ℕ) (hk : k ≠ 0) :
    IsZero (rSingularHomology ℤ k (TopCat.of Unit)) := by
  -- A point is totally disconnected, so all higher singular homology groups are zero.
  simpa [rSingularHomology] using
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (C := ModuleCat ℤ) (n := k) (R := constantCoefficientModule ℤ)
      (X := TopCat.of Unit) hk)

/-- Helper for Problem 21.6.2: a contractible space has the same `rSingularHomology ℤ` as a
point. -/
theorem rSingularHomologyIsoUnit_of_contractible
    (k : ℕ) [ContractibleSpace M] :
    Nonempty (rSingularHomology ℤ k (TopCat.of M) ≅ rSingularHomology ℤ k (TopCat.of Unit)) := by
  -- Reduce the comparison to the canonical homotopy equivalence from a contractible space to the
  -- one-point space.
  rcases ContractibleSpace.hequiv_unit M with ⟨e⟩
  exact rSingularHomologyIsoOfHomotopyEquiv e k

/-- Helper for Problem 21.6.2: the zeroth `rSingularHomology ℤ` of a contractible space is `ℤ`.
-/
theorem rSingularHomologyZeroIsoInt_of_contractible
    [ContractibleSpace M] :
    Nonempty (rSingularHomology ℤ 0 (TopCat.of M) ≅ ModuleCat.of ℤ ℤ) := by
  -- Compare first with the point and then use the explicit point computation.
  rcases rSingularHomologyIsoUnit_of_contractible (M := M) 0 with ⟨hM⟩
  rcases rSingularHomologyUnitZero with ⟨hUnit⟩
  exact ⟨hM ≪≫ hUnit⟩

/-- Helper for Problem 21.6.2: every positive-degree `rSingularHomology ℤ` group of a contractible
space vanishes. -/
theorem rSingularHomology_isZero_of_contractible
    (k : ℕ) [ContractibleSpace M] (hk : k ≠ 0) :
    IsZero (rSingularHomology ℤ k (TopCat.of M)) := by
  rcases rSingularHomologyIsoUnit_of_contractible (M := M) k with ⟨hM⟩
  -- Compare with the point and import the positive-degree vanishing there.
  exact IsZero.of_iso (rSingularHomologyUnit_isZero_of_ne k hk) hM

/-- Helper for Problem 21.6.2: transporting the sphere calculation from
`integralSingularHomology` gives the positive-dimensional sphere pattern on `rSingularHomology ℤ`.
-/
theorem sphereRSingularHomologyPattern_of_pos
    (hm : 0 < m) :
    Nonempty (rSingularHomology ℤ m (TopCat.sphere m) ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ {k : ℕ}, 0 < k → k < m → IsZero (rSingularHomology ℤ k (TopCat.sphere m))) ∧
      (∀ {k : ℕ}, m < k → IsZero (rSingularHomology ℤ k (TopCat.sphere m))) := by
  rcases CompactManifold.sphereIntegralHomologyPattern_of_pos (n := m) hm with
    ⟨hTop, hMiddle, hAbove⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hTop with ⟨hTop⟩
    rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere m) m with ⟨hCompare⟩
    exact ⟨hCompare.symm ≪≫ hTop⟩
  · intro k hk hkm
    rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere m) k with ⟨hCompare⟩
    exact IsZero.of_iso (hMiddle hk hkm) hCompare.symm
  · intro k hmk
    rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere m) k with ⟨hCompare⟩
    exact IsZero.of_iso (hAbove hmk) hCompare.symm

/-- Helper for Problem 21.6.2: a positive-dimensional sphere has zeroth `rSingularHomology ℤ`
equal to `ℤ`. -/
theorem sphereRSingularHomologyZeroIsoInt_of_pos
    (hm : 0 < m) :
    Nonempty (rSingularHomology ℤ 0 (TopCat.sphere m) ≅ ModuleCat.of ℤ ℤ) := by
  rcases CompactManifold.zeroIntegralSingularHomologyIsoInt_of_uniqueZerothHomotopy
      (X := TopCat.sphere m)
      (CompactManifold.sphereUniqueZerothHomotopy_of_pos (n := m) hm) with
    ⟨hSphere⟩
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere m) 0 with ⟨hCompare⟩
  exact ⟨hCompare.symm ≪≫ hSphere⟩

/-- Helper for Problem 21.6.2: the unique `R`-fundamental class compatible with the compact
oriented manifold `o`. -/
noncomputable def canonicalRFundamentalClass
    {R : Type} [CommRing R] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] {n : ℕ}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    [Fact (Module.finrank ℝ E = n)] (o : ROrientedManifold R I n M) :
    rSingularHomology R n (TopCat.of M) :=
  Classical.choose
    (ExistsUnique.exists
      (existsUnique_rFundamentalClassFor_of_representative_rOrientedManifold o))

/-- Helper for Problem 21.6.2: the canonical compatible `R`-fundamental class satisfies the
orientation compatibility predicate. -/
theorem canonicalRFundamentalClass_spec
    {R : Type} [CommRing R] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] {n : ℕ}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    [Fact (Module.finrank ℝ E = n)] (o : ROrientedManifold R I n M) :
    IsRFundamentalClassFor o (canonicalRFundamentalClass o) := by
  -- This is exactly the witness chosen when defining `canonicalRFundamentalClass`.
  exact
    Classical.choose_spec
      (ExistsUnique.exists
        (existsUnique_rFundamentalClassFor_of_representative_rOrientedManifold o))

/-- Helper for Problem 21.6.2: the pair `(M, ∂M)` carries the canonical connecting morphism
`H_(m + 1)(M, ∂M; ℤ) ⟶ H_m(∂M; ℤ)`. -/
theorem existsBoundaryRelativeBoundaryMorphism :
    ∃ δ : boundaryRelativeSingularHomology ℤ (m + 1) M ⟶
        rSingularHomology ℤ m (TopCat.of (manifoldBoundary (m + 1) M)),
      IsBoundaryRelativeSingularHomologyBoundary ℤ (m + 1) M δ := by
  -- The pair short exact sequence already packages the connecting morphism.
  let hS := boundaryRelativeSingularShortComplexShortExact (R := ℤ) (n := m + 1) (M := M)
  refine ⟨boundaryRelativeSingularHomologyBoundaryOfShortExact ℤ (m + 1) M hS, ?_⟩
  -- This morphism is canonical by construction from that short exact sequence.
  exact ⟨hS, rfl⟩

/-- Helper for Problem 21.6.2: an oriented compact manifold with boundary has a
boundary-relative fundamental class. -/
theorem existsBoundaryRelativeFundamentalClass_of_orientedWithBoundary
    [CompactSpace M] [ROrientedManifoldWithBoundary ℤ (m + 1) M] :
    ∃ z : boundaryRelativeSingularHomology ℤ (m + 1) M,
      IsBoundaryRelativeFundamentalClassFor z := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M) := by
    infer_instance
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m) := by
    exact ⟨@finrank_euclideanSpace_fin ℝ _ m⟩
  let _ :
      ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) - 1))) (manifoldBoundary (m + 1) M) := by
    change ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M)
    infer_instance
  let _ :
      Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) - 1))) = (m + 1) - 1) := by
    change Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)
    exact ⟨@finrank_euclideanSpace_fin ℝ _ m⟩
  -- First pick the canonical fundamental class on the oriented boundary.
  let zBoundary : rSingularHomology ℤ m (TopCat.of (manifoldBoundary (m + 1) M)) :=
    canonicalRFundamentalClass
      (ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc ℤ m M)
  have hzBoundary :
      IsRFundamentalClassFor
        (ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc ℤ m M) zBoundary := by
    simpa [zBoundary] using
      canonicalRFundamentalClass_spec
        (ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc ℤ m M)
  -- Then invoke the canonical boundary-relative existence-and-uniqueness theorem.
  rcases existsBoundaryRelativeBoundaryMorphism (m := m) (M := M) with ⟨δ, hδ⟩
  rcases existsUnique_boundaryRelativeFundamentalClass_of_rOrientedManifoldWithBoundary
      (R := ℤ) (n := m + 1) (M := M) δ hδ zBoundary hzBoundary with
    ⟨z, hz, _⟩
  exact ⟨z, hz.1⟩

/-- Helper for Problem 21.6.2: the complement of the interior in `M` is canonically homeomorphic
to the boundary `∂M`. -/
private abbrev boundaryComplementHomeomorph :
    subspaceComplement M ((𝓡∂ (m + 1)).interior M) ≃ₜ manifoldBoundary (m + 1) M := by
  -- This is the canonical Chapter 21 identification `M \ interior(M) = ∂M`.
  simpa [manifoldBoundary, subspaceComplement] using
    Homeomorph.setCongr ((𝓡∂ (m + 1)).compl_interior)

/-- Helper for Problem 21.6.2: singular homology transports the boundary-complement model to the
canonical boundary owner. -/
private abbrev boundaryComplementRSingularHomologyIso
    (k : ℕ) :
    rSingularHomology ℤ k (TopCat.of (subspaceComplement M ((𝓡∂ (m + 1)).interior M))) ≅
      rSingularHomology ℤ k (TopCat.of (manifoldBoundary (m + 1) M)) :=
  (((singularHomologyFunctor (ModuleCat ℤ) k).obj (constantCoefficientModule ℤ)).mapIso
    (TopCat.isoOfHomeo (boundaryComplementHomeomorph (m := m) (M := M))))

/-- Helper for Problem 21.6.2: the degree-`p` boundary-relative homology target, viewed in
`AddCommGrpCat`. -/
abbrev boundaryRelativeSingularHomologyGroup
    (R : Type) [CommRing R] (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (relativeTopHomologyGroup R (n - p) M ((𝓡∂ n).interior M))

/-- Helper for Problem 21.6.2: the codomain of the absolute-relative cap-product pairing in
degree `p`. -/
abbrev absoluteToRelativeCapTarget
    (R : Type) [CommRing R] (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of
    (H[n](M, ∂M; R) →+ boundaryRelativeSingularHomologyGroup R n M p)

/-- Helper for Problem 21.6.2: evaluation at `z ∈ H_n(M, ∂M; R)` turns a curried cap-product
pairing into the corresponding degree-`p` duality morphism. -/
abbrev evalAtBoundaryRelativeClass
    {R : Type} [CommRing R] {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R)) (A : AddCommGrpCat) :
    AddCommGrpCat.of (H[n](M, ∂M; R) →+ A) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ f z
      map_zero' := rfl
      map_add' := by
        intro f g
        rfl }

/-- Helper for Problem 21.6.2: a chosen source-facing realization of the absolute-relative
cap-product pairing used below. -/
structure BoundaryRelativeCapProduct
    {R : Type} [CommRing R] (Hcoh : PairCohomologyTheory R)
    (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] where
  /-- The absolute-relative cap-product pairing
  `H^p(M; R) ⟶ Hom(H_n(M, ∂M; R), H_(n - p)(M, ∂M; R))`. -/
  absolutePairing (p : ℕ) :
    (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ⟶
      absoluteToRelativeCapTarget R n M p

/-- Helper for Problem 21.6.2: the degree-`p` morphism obtained by evaluating the
absolute-relative cap-product pairing at `z ∈ H_n(M, ∂M; R)`. -/
abbrev boundaryRelativeAbsoluteToRelativeMap
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (p : ℕ) :
    (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ⟶
      boundaryRelativeSingularHomologyGroup R n M p :=
  capProduct.absolutePairing p ≫
    evalAtBoundaryRelativeClass z (boundaryRelativeSingularHomologyGroup R n M p)

/-- Helper for Problem 21.6.2: a source-facing cap-product pairing realizes the boundary-relative
duality package for `z` when `z` is boundary-relative fundamental and the induced absolute maps
are degreewise isomorphisms. -/
class IsBoundaryRelativePoincareDualityMap
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M) : Prop where
  /-- A boundary-relative duality family is only defined from a boundary-relative fundamental
  class. -/
  isBoundaryRelativeFundamentalClassFor : IsBoundaryRelativeFundamentalClassFor z
  /-- The absolute-relative cap-product maps induced by evaluating at `z` are degreewise
  isomorphisms. -/
  absoluteToRelative_isIso (p : ℕ) :
    IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p)

/-- Helper for Problem 21.6.2: the absolute-to-relative cap-with-`z` morphism is an isomorphism
in each degree. -/
instance boundaryRelativeAbsoluteToRelativeMap_isIso
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] {z : H[n](M, ∂M; R)}
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct)
    (p : ℕ) :
    IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p) :=
  hD.absoluteToRelative_isIso p

/-- Helper for Problem 21.6.2: a full boundary-relative Poincare duality package projects to the
degreewise absolute-relative duality family consumed by the later relative-homology comparison. -/
theorem boundaryRelativeAbsoluteDualityFamily_of_poincareDuality
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] {z : H[n](M, ∂M; R)}
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct) :
    ∃ D : ∀ p : ℕ,
        (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ⟶
          boundaryRelativeSingularHomologyGroup R n M p,
      ∀ p : ℕ, IsIso (D p) := by
  -- Package the degreewise absolute-relative cap-with-`z` maps as the family used downstream.
  refine ⟨fun p ↦ boundaryRelativeAbsoluteToRelativeMap z capProduct p, ?_⟩
  intro p
  -- Each component is one of the isomorphisms recorded in the full duality package.
  exact hD.absoluteToRelative_isIso p

/-- Helper for Problem 21.6.2: once a boundary-relative fundamental class is equipped with a
degreewise duality package, the contractible absolute cohomology pattern converts the pair
`(M, ∂M)` into the expected top-degree relative homology pattern. -/
theorem relativeTopHomologyPattern_of_contractibleDuality
    (Hcoh : PairCohomologyTheory ℤ)
    [ContractibleSpace M]
    {z : H[m + 1](M, ∂M; ℤ)}
    (capProduct : BoundaryRelativeCapProduct Hcoh (m + 1) M)
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct) :
    Nonempty
        (AddCommGrpCat.of
            (relativeTopHomologyGroup ℤ (m + 1) M ((𝓡∂ (m + 1)).interior M)) ≅
          AddCommGrpCat.of ℤ) ∧
      ∀ p : ℕ, p ≠ 0 →
        IsZero (relativeTopHomologyGroup ℤ ((m + 1) - p) M ((𝓡∂ (m + 1)).interior M)) := by
  rcases contractibleAbsoluteCohomologyPattern (M := M) Hcoh with ⟨⟨hZero⟩, hHigher⟩
  constructor
  · -- Degree `0` duality identifies the top relative homology group with `ℤ`.
    have hIso0 : IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct 0) :=
      hD.absoluteToRelative_isIso 0
    let _ : IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct 0) := hIso0
    refine ⟨(asIso (boundaryRelativeAbsoluteToRelativeMap z capProduct 0)).symm ≪≫ hZero⟩
  · intro p hp
    -- Positive-degree absolute cohomology vanishes on a contractible space.
    have hSourceZero :
        IsZero ((Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M))) := by
      exact hHigher (p : ℤ) (by exact_mod_cast hp)
    -- Transport that vanishing across the degree-`p` duality isomorphism.
    have hIso : IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p) :=
      hD.absoluteToRelative_isIso p
    let _ : IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p) := hIso
    let e :
        (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ≅
          boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p :=
      asIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p)
    have hTargetZero :
        IsZero (boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p) :=
      IsZero.of_iso hSourceZero e.symm
    have hSubsingleton :
        Subsingleton (relativeTopHomologyGroup ℤ ((m + 1) - p) M ((𝓡∂ (m + 1)).interior M)) := by
      simpa [boundaryRelativeSingularHomologyGroup] using
        (AddCommGrpCat.subsingleton_of_isZero hTargetZero)
    -- A subsingleton module object is zero in `ModuleCat`.
    exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Problem 21.6.2: the predecessor-spelled finrank fact on the boundary Euclidean
model is definitionally the usual `finrank_euclideanSpace_fin` statement. -/
private theorem boundaryFinrankFactPred :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) - 1))) = (m + 1) - 1) := by
  -- Reduce the predecessor index to `m`, then use the standard finite-dimensionality calculation.
  change Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)
  exact ⟨@finrank_euclideanSpace_fin ℝ _ m⟩

/-- Helper for Problem 21.6.2: the boundary-manifold field in
`ROrientedManifoldWithBoundary` can be discharged by the canonical Chapter 21 boundary owner under
its own canonical boundary charted-space owner. -/
private theorem canonicalBoundaryIsManifoldOnChapter21Owner
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)] :
    @IsManifold
      ℝ
      DenselyNormedField.toNontriviallyNormedField
      (EuclideanSpace ℝ (Fin m))
      (PiLp.normedAddCommGroup 2 fun _ ↦ ℝ)
      (PiLp.normedSpace 2 ℝ fun _ ↦ ℝ)
      (EuclideanSpace ℝ (Fin m))
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (𝓡 m)
      ⊤
      (manifoldBoundary (m + 1) M)
      instTopologicalSpaceSubtype
      (ManifoldBoundary.boundaryEuclideanChartedSpace (n := m) (W := M)) := by
  -- This is exactly the canonical Chapter 21 boundary manifold theorem.
  exact ManifoldBoundary.boundary_isManifold (n := m) (W := M)

/-- Helper for Problem 21.6.2: the remaining `boundary_isManifold` blocker is the owner-surface
transport from the canonical Chapter 21 boundary charted-space owner to the current arbitrary
boundary `ChartedSpace` binder. -/
private theorem boundaryIsManifold_ofCanonicalOwner
    [IsManifold (𝓡∂ (m + 1)) ⊤ M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)]
    (hCanonical :
      @IsManifold
        ℝ
        DenselyNormedField.toNontriviallyNormedField
        (EuclideanSpace ℝ (Fin m))
        (PiLp.normedAddCommGroup 2 fun _ ↦ ℝ)
        (PiLp.normedSpace 2 ℝ fun _ ↦ ℝ)
        (EuclideanSpace ℝ (Fin m))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (𝓡 m)
        ⊤
        (manifoldBoundary (m + 1) M)
        instTopologicalSpaceSubtype
        (ManifoldBoundary.boundaryEuclideanChartedSpace (n := m) (W := M))) :
    IsManifold (𝓡 m) ⊤ (manifoldBoundary (m + 1) M) := by
  -- Route correction: the geometric content is already available on the canonical Chapter 21
  -- owner, so the only missing step is a transport theorem from that owner to the current
  -- boundary `ChartedSpace` binder.
  -- TODO: prove that the current boundary charted-space structure is compatible with the canonical
  -- `ManifoldBoundary.boundaryEuclideanChartedSpace`, then transport `hCanonical` across that
  -- owner equality/compatibility bridge.
  sorry

/-- Helper for Problem 21.6.2: the remaining `boundary_isManifold` blocker is the owner-surface
transport from the canonical Chapter 21 boundary charted-space to the arbitrary boundary
`ChartedSpace` binder in `ROrientedManifoldWithBoundary`. -/
private theorem boundaryIsManifold_currentInstance
    [IsManifold (𝓡∂ (m + 1)) ⊤ M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)] :
    IsManifold (𝓡 m) ⊤ (manifoldBoundary (m + 1) M) := by
  have hCanonical :
      @IsManifold
        ℝ
        DenselyNormedField.toNontriviallyNormedField
        (EuclideanSpace ℝ (Fin m))
        (PiLp.normedAddCommGroup 2 fun _ ↦ ℝ)
        (PiLp.normedSpace 2 ℝ fun _ ↦ ℝ)
        (EuclideanSpace ℝ (Fin m))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (𝓡 m)
        ⊤
        (manifoldBoundary (m + 1) M)
        instTopologicalSpaceSubtype
        (ManifoldBoundary.boundaryEuclideanChartedSpace (n := m) (W := M)) :=
    canonicalBoundaryIsManifoldOnChapter21Owner (m := m) (M := M)
  -- The remaining work is now isolated to the owner-transport helper above.
  exact boundaryIsManifold_ofCanonicalOwner (m := m) (M := M) hCanonical

/-- Helper for Problem 21.6.2: the with-boundary orientation owner can be packaged from a chosen
covering family of compatible ambient trivializations once a compatible boundary-chart operator is
available on that family. -/
theorem nonemptyROrientedManifoldWithBoundary_of_coveringFamily
    [IsManifold (𝓡∂ (m + 1)) ⊤ M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m)]
    (atlasFamily : M → LocalTopHomologyTrivialization ℤ (m + 1) M)
    (hmem : ∀ x : M, x ∈ (atlasFamily x).domain)
    (hcompat : ∀ x y : M, (atlasFamily x).OrientationCompatible (atlasFamily y))
    (boundaryChart :
      LocalTopHomologyTrivialization ℤ (m + 1) M →
        LocalTopHomologyTrivialization ℤ m (manifoldBoundary (m + 1) M))
    (hboundary_domain :
      ∀ x : M, (boundaryChart (atlasFamily x)).domain = Subtype.val ⁻¹' (atlasFamily x).domain)
    (hboundary_compat :
      ∀ x y : M,
        (boundaryChart (atlasFamily x)).OrientationCompatible (boundaryChart (atlasFamily y))) :
    Nonempty (ROrientedManifoldWithBoundary ℤ (m + 1) M) := by
  -- Package the chosen ambient atlas as `Set.range atlasFamily`, exactly as in the boundaryless
  -- orientation owner, and record the induced boundary charts through the given operator.
  refine ⟨(show ROrientedManifoldWithBoundary ℤ (m + 1) M from {
    toIsManifold := inferInstance
    atlas := Set.range atlasFamily
    cover := ?_
    pairwise_compatible := ?_
    boundaryChart := boundaryChart
    boundaryChart_domain := ?_
    boundaryChart_compatible := ?_
    boundary_isManifold := ?_ })⟩
  · intro x
    -- The indexing point chooses an atlas chart that contains it.
    exact ⟨atlasFamily x, ⟨x, rfl⟩, hmem x⟩
  · intro U V hU hV
    -- Compatibility reduces to the supplied pairwise compatibility on the indexing family.
    rcases hU with ⟨x, rfl⟩
    rcases hV with ⟨y, rfl⟩
    exact hcompat x y
  · intro U hU
    -- The induced boundary chart domain was assumed to be the boundary slice of the ambient one.
    rcases hU with ⟨x, rfl⟩
    exact hboundary_domain x
  · intro U V hU hV
    -- Boundary-chart compatibility is inherited from the supplied family-level hypothesis.
    rcases hU with ⟨x, rfl⟩
    rcases hV with ⟨y, rfl⟩
    exact hboundary_compat x y
  · -- The canonical boundary manifold instance is already provided by `ManifoldBoundary`.
    intro instBoundaryCharted instBoundaryFinrank
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) (manifoldBoundary (m + 1) M) :=
      instBoundaryCharted
    let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m) :=
      instBoundaryFinrank
    -- Route correction: this field only needs the current boundary instances, so the canonical
    -- `ManifoldBoundary.boundary_isManifold` theorem closes it directly.
    exact boundaryIsManifold_currentInstance (m := m) (M := M)

/-- Helper for Problem 21.6.2: only the absolute-relative branch of the duality package is needed
to compute the relative homology pattern of a contractible manifold with boundary. -/
theorem relativeTopHomologyPattern_of_contractibleAbsoluteDuality
    (Hcoh : PairCohomologyTheory ℤ)
    [ContractibleSpace M]
    (D : ∀ p : ℕ,
      (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ⟶
        boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p)
    (hD : ∀ p : ℕ, IsIso (D p)) :
    Nonempty
        (AddCommGrpCat.of
            (relativeTopHomologyGroup ℤ (m + 1) M ((𝓡∂ (m + 1)).interior M)) ≅
          AddCommGrpCat.of ℤ) ∧
      ∀ p : ℕ, p ≠ 0 →
        IsZero (relativeTopHomologyGroup ℤ ((m + 1) - p) M ((𝓡∂ (m + 1)).interior M)) := by
  rcases contractibleAbsoluteCohomologyPattern (M := M) Hcoh with ⟨⟨hZero⟩, hHigher⟩
  constructor
  · -- Degree `0` identifies the top relative homology group with `ℤ`.
    have hIso0 : IsIso (D 0) :=
      hD 0
    let _ : IsIso (D 0) := hIso0
    refine ⟨(asIso (D 0)).symm ≪≫ hZero⟩
  · intro p hp
    -- Positive-degree absolute cohomology vanishes on a contractible space.
    have hSourceZero :
        IsZero ((Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M))) := by
      exact hHigher (p : ℤ) (by exact_mod_cast hp)
    -- Transport that vanishing across the degree-`p` absolute-relative duality isomorphism.
    have hIso : IsIso (D p) :=
      hD p
    let _ : IsIso (D p) := hIso
    let e :
        (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ≅
          boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p :=
      asIso (D p)
    have hTargetZero :
        IsZero (boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p) :=
      IsZero.of_iso hSourceZero e.symm
    have hSubsingleton :
        Subsingleton (relativeTopHomologyGroup ℤ ((m + 1) - p) M ((𝓡∂ (m + 1)).interior M)) := by
      simpa [boundaryRelativeSingularHomologyGroup] using
        (AddCommGrpCat.subsingleton_of_isZero hTargetZero)
    -- A subsingleton module object is zero in `ModuleCat`.
    exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Problem 21.6.2: a compact contractible manifold with boundary should supply the
ambient orientation package needed for the boundary-relative duality argument. -/
theorem contractibleOrientedWithBoundary
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] :
    Nonempty (ROrientedManifoldWithBoundary ℤ (m + 1) M) := by
  classical
  let atlasFamily : M → LocalTopHomologyTrivialization ℤ (m + 1) M := fun x ↦
    Classical.choose
      (OrientationCover.existsLocalTopHomologyTrivializationAt (n := m + 1) (M := M) x)
  have hmem : ∀ x : M, x ∈ (atlasFamily x).domain := by
    intro x
    exact
      Classical.choose_spec
        (OrientationCover.existsLocalTopHomologyTrivializationAt (n := m + 1) (M := M) x)
  have hcompat : ∀ x y : M, (atlasFamily x).Compatible (atlasFamily y) := by
    intro x y
    exact
      OrientationCover.compatible_of_isManifold (n := m + 1) (M := M)
        (atlasFamily x) (atlasFamily y)
  -- Route correction: the ambient atlas is now packaged abstractly by
  -- `nonemptyROrientedManifoldWithBoundary_of_coveringFamily`, so the remaining blocker is only
  -- the missing owner-level boundary-chart constructor on each ambient trivialization.
  -- TODO: expose a canonical `boundaryChart` operator on
  -- `LocalTopHomologyTrivialization ℤ (m + 1) M` whose domain is
  -- `Subtype.val ⁻¹' U.domain`, then feed its compatibility theorem into the generic packaging
  -- lemma above.
  sorry

/-- Helper for Problem 21.6.2: an oriented compact manifold with boundary should provide the
smallest boundary-relative absolute duality family consumed by the relative-homology computation
below. -/
theorem boundaryRelativeDualityData_of_orientedWithBoundary
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ROrientedManifoldWithBoundary ℤ (m + 1) M] :
    ∃ (Hcoh : PairCohomologyTheory ℤ)
      (D : ∀ p : ℕ,
        (Hcoh.absoluteCohomology (p : ℤ)).obj (Opposite.op (TopCat.of M)) ⟶
          boundaryRelativeSingularHomologyGroup ℤ (m + 1) M p),
      ∀ p : ℕ, IsIso (D p) := by
  -- Route correction: the previous frontier asked for a full `BoundaryRelativeCapProduct`, but
  -- the current file only consumes the absolute-relative branch of that package.
  -- TODO: obtain a boundary-relative fundamental class from
  -- `existsBoundaryRelativeFundamentalClass_of_orientedWithBoundary`, then construct a full
  -- `BoundaryRelativeCapProduct` and `IsBoundaryRelativePoincareDualityMap`, and finally project
  -- that package to the current theorem's interface via
  -- `boundaryRelativeAbsoluteDualityFamily_of_poincareDuality`.
  sorry

/-- Helper for Problem 21.6.2: once the oriented boundary-relative duality package exists, the
relative homology of `(M, ∂M)` has the expected top-degree `ℤ` and vanishes below top degree. -/
theorem boundaryRelativeLowDegreePattern_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] :
    Nonempty
        (AddCommGrpCat.of
            (relativeTopHomologyGroup ℤ (m + 1) M ((𝓡∂ (m + 1)).interior M)) ≅
          AddCommGrpCat.of ℤ) ∧
      ∀ j : ℕ, 0 < j → j ≤ m →
        IsZero (relativeTopHomologyGroup ℤ j M ((𝓡∂ (m + 1)).interior M)) := by
  classical
  -- First reduce to the two theorem-local duality inputs isolated above.
  rcases contractibleOrientedWithBoundary (m := m) (M := M) with ⟨hOrient⟩
  letI : ROrientedManifoldWithBoundary ℤ (m + 1) M := hOrient
  rcases boundaryRelativeDualityData_of_orientedWithBoundary (m := m) (M := M) with
    ⟨Hcoh, D, hD⟩
  have hRel :=
    relativeTopHomologyPattern_of_contractibleAbsoluteDuality
      (m := m) (M := M) Hcoh D hD
  constructor
  · exact hRel.1
  · intro j hjpos hj
    -- The duality pattern gives vanishing in the complementary positive degree `p = m + 1 - j`.
    have hp : m + 1 - j ≠ 0 := by
      omega
    have hindex : (m + 1) - (m + 1 - j) = j := by
      omega
    simpa [hindex] using
      hRel.2 (m + 1 - j) hp

/-- Helper for Problem 21.6.2: the top-degree relative group can be viewed on the canonical
`ModuleCat ℤ` owner once the additive-group pattern has been established. -/
theorem relativeTopHomologyTopIsoInt_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] :
    Nonempty
      (relativeTopHomologyGroup ℤ (m + 1) M ((𝓡∂ (m + 1)).interior M) ≅
        ModuleCat.of ℤ ℤ) := by
  rcases boundaryRelativeLowDegreePattern_of_contractible (m := m) (M := M) with
    ⟨⟨hTop⟩, _⟩
  refine ⟨?_⟩
  -- Convert the additive-group top-degree comparison into the `ℤ`-linear equivalence that
  -- `ModuleCat` expects.
  exact LinearEquiv.toModuleIso
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv hTop).toIntLinearEquiv

/-- Helper for Problem 21.6.2: in the strictly sub-top degrees `0 < k < m`, the boundary
homology vanishes. -/
theorem boundaryRSingularHomology_isZero_of_contractible_of_lt
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] {k : ℕ} (hk : 0 < k) (hkm : k < m) :
    IsZero (rSingularHomology ℤ k (TopCat.of (manifoldBoundary (m + 1) M))) := by
  -- TODO: use the degree-`k` five-term exact sequence for `(M, ∂M)` to show the connecting map
  -- `H_(k + 1)(M, ∂M; ℤ) ⟶ H_k(∂M; ℤ)` is epic, then combine
  -- `boundaryRelativeLowDegreePattern_of_contractible` with contractible ambient homology
  -- vanishing to force `H_k(∂M; ℤ) = 0`.
  sorry

/-- Helper for Problem 21.6.2: in top degree `m`, the boundary carries `rSingularHomology ℤ`
equal to `ℤ`. -/
theorem boundaryRSingularHomologyTopIsoInt_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] (hm : 0 < m) :
    Nonempty (rSingularHomology ℤ m (TopCat.of (manifoldBoundary (m + 1) M)) ≅
      ModuleCat.of ℤ ℤ) := by
  -- TODO: use the degree-`m` five-term exact sequence to show the connecting morphism
  -- `H_(m + 1)(M, ∂M; ℤ) ⟶ H_m(∂M; ℤ)` is an isomorphism, then combine it with
  -- `relativeTopHomologyTopIsoInt_of_contractible`.
  sorry

/-- Helper for Problem 21.6.2: for `m > 0`, exactness at the `H₀` end identifies the boundary's
zeroth homology with `ℤ`. -/
theorem boundaryRSingularHomologyZeroIsoInt_of_contractible_of_pos
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] (hm : 0 < m) :
    Nonempty (rSingularHomology ℤ 0 (TopCat.of (manifoldBoundary (m + 1) M)) ≅
      ModuleCat.of ℤ ℤ) := by
  -- TODO: use the degree-zero five-term exact sequence together with the vanishing
  -- `H₁(M, ∂M; ℤ) = 0 = H₀(M, ∂M; ℤ)` to identify `H₀(∂M; ℤ)` with the contractible ambient
  -- group `H₀(M; ℤ) ≅ ℤ`.
  sorry

/-- Helper for Problem 21.6.2: the positive-degree boundary homology should match the positive
degree sphere pattern once the boundary exact-sequence comparison is extracted. -/
theorem boundaryPositiveDegreeIsoSphere_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] {k : ℕ} (hk : 0 < k) :
    Nonempty
      (rSingularHomology ℤ k (TopCat.of (manifoldBoundary (m + 1) M)) ≅
        rSingularHomology ℤ k (TopCat.sphere m)) := by
  by_cases hkm : k ≤ m
  · by_cases hkTop : k = m
    · subst hkTop
      -- In top degree, both the boundary and the sphere carry `ℤ`.
      rcases boundaryRSingularHomologyTopIsoInt_of_contractible (M := M) hk with
        ⟨hBoundary⟩
      rcases sphereRSingularHomologyPattern_of_pos (m := k) hk with ⟨⟨hSphere⟩, _, _⟩
      exact ⟨hBoundary ≪≫ hSphere.symm⟩
    · have hklt : k < m := lt_of_le_of_ne hkm hkTop
      have hBoundaryZero :
          IsZero (rSingularHomology ℤ k (TopCat.of (manifoldBoundary (m + 1) M))) :=
        boundaryRSingularHomology_isZero_of_contractible_of_lt (m := m) (M := M) hk hklt
      have hmPos : 0 < m := lt_trans hk hklt
      have hSphereZero :
          IsZero (rSingularHomology ℤ k (TopCat.sphere m)) :=
        (sphereRSingularHomologyPattern_of_pos (m := m) hmPos).2.1 hk hklt
      exact CompactManifold.isoOfIsZero hBoundaryZero hSphereZero
  · have hmk : m < k := lt_of_not_ge hkm
    -- Route correction: the middle and top branches are now reduced to exact-sequence arguments.
    -- TODO: finish the above-dimension branch by surfacing a direct boundary-dimension vanishing
    -- theorem on the canonical boundary owner `manifoldBoundary (m + 1) M`.
    sorry

/-- Helper for Problem 21.6.2: the degree-zero boundary homology should match that of `S^m`,
with a separate `m = 0` branch for `S⁰`. -/
theorem boundaryZeroDegreeIsoSphere_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] :
    Nonempty
      (rSingularHomology ℤ 0 (TopCat.of (manifoldBoundary (m + 1) M)) ≅
        rSingularHomology ℤ 0 (TopCat.sphere m)) := by
  by_cases hm : m = 0
  · -- Route correction: the positive-dimensional branch is now isolated below.
    -- TODO: when `m = 0`, show that the boundary of a compact contractible `1`-manifold has two
    -- path components, so its zeroth homology agrees with `H₀(S⁰; ℤ)`.
    sorry
  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
    rcases boundaryRSingularHomologyZeroIsoInt_of_contractible_of_pos (m := m) (M := M) hmPos with
      ⟨hBoundary⟩
    rcases sphereRSingularHomologyZeroIsoInt_of_pos (m := m) hmPos with ⟨hSphere⟩
    exact ⟨hBoundary ≪≫ hSphere.symm⟩

/-- Helper for Problem 21.6.2: the remaining homological core is to compare the boundary of a
contractible manifold with `S^m` on the Chapter 20 owner `rSingularHomology ℤ`. -/
theorem rSingularHomology_boundary_isoSphere_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] (k : ℕ) :
    Nonempty
      (rSingularHomology ℤ k (TopCat.of (manifoldBoundary (m + 1) M)) ≅
        rSingularHomology ℤ k (TopCat.sphere m)) := by
  -- Route correction: the main theorem is now a short assembly over the isolated frontier
  -- lemmas, so the remaining blocker is no longer hidden inside this declaration.
  by_cases hk : k = 0
  · subst hk
    -- Degree zero is the exceptional branch because `S⁰` is disconnected.
    exact boundaryZeroDegreeIsoSphere_of_contractible (m := m) (M := M)
  · -- Every positive degree is delegated to the exact-sequence comparison helper.
    exact boundaryPositiveDegreeIsoSphere_of_contractible
      (m := m) (M := M) (Nat.pos_iff_ne_zero.mpr hk)

/-- Problem 21.6.2: if a compact contractible `(m + 1)`-manifold with boundary `M` is given, then
the boundary subtype has the integral singular homology of the sphere `S^m`. The statement is
expressed through the Chapter 13 owner `integralSingularHomology` and the canonical boundary
subtype `(𝓡∂ (m + 1)).boundary M`. -/
theorem integralSingularHomology_boundary_isoSphere_of_contractible
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (m + 1)) (m + 1) M]
    [ContractibleSpace M] (k : ℕ) :
    Nonempty
      (integralSingularHomology k (TopCat.of ((𝓡∂ (m + 1)).boundary M)) ≅
        integralSingularHomology k (TopCat.sphere m)) := by
  -- Route correction: once the boundary-sphere comparison is established on `rSingularHomology`,
  -- the Chapter 13 owner-level statement follows by transporting across the canonical comparison
  -- isomorphisms at the boundary and at the sphere.
  rcases integralSingularHomologyIsoRSingularHomology
      (TopCat.of (manifoldBoundary (m + 1) M)) k with ⟨hBoundaryComparison⟩
  rcases rSingularHomology_boundary_isoSphere_of_contractible (m := m) (M := M) k with
      ⟨hBoundarySphere⟩
  rcases integralSingularHomologyIsoRSingularHomology (TopCat.sphere m) k with
      ⟨hSphereComparison⟩
  exact ⟨hBoundaryComparison ≪≫ hBoundarySphere ≪≫ hSphereComparison.symm⟩
