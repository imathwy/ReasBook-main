module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Remark_60_1.ReducedHomologyZero
public import Topology_Munkres_2000.Book.Theorem_62_1.FiniteRelativeDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.CechDiagram
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Theorem_63_7.FiniteAlexanderStage
public import Topology_Munkres_2000.Book.Theorem_63_7.ModTwoAlexanderNonvanishing
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.LocallyContractible

public section

open Set
open CategoryTheory
open CategoryTheory.Limits

/-- Helper for Theorem 63.7: a subspace homeomorphic to a standard sphere is
compact. -/
private lemma isCompact_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) : IsCompact C := by
  -- Transport the compact-space instance from the standard sphere to the subtype.
  obtain ⟨e⟩ := hC
  letI : CompactSpace C := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Helper for Theorem 63.7: an embedded standard sphere is closed in the
ambient standard sphere. -/
private lemma isClosed_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) : IsClosed C := by
  -- A compact subset of the Hausdorff ambient sphere is closed.
  exact (isCompact_of_homeomorphic_standardSphere n C hC).isClosed

/-- Helper for Theorem 63.7: summing coefficients is the augmentation of finitely
supported integral component chains. -/
private noncomputable abbrev componentAugmentationIntegral (ι : Type*) :
    (ι →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ (fun _ : ι ↦ (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

/-- Helper for Theorem 63.7: integral component augmentation is injective exactly
when its indexing type has at most one element. -/
private lemma componentAugmentationIntegral_injective_iff_subsingleton (ι : Type*) :
    Function.Injective (componentAugmentationIntegral ι) ↔ Subsingleton ι := by
  constructor
  · intro h
    -- Equal augmentation values of two unit chains force their indices to agree.
    refine ⟨fun i j ↦ Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) ?_⟩
    apply h
    simp only [componentAugmentationIntegral, Finsupp.lsum_single, LinearMap.id_apply]
  · intro h
    -- On a subsingleton index type, augmentation is evaluation at the unique index.
    letI : Subsingleton ι := h
    intro x y hxy
    ext i
    have hsum (z : ι →₀ ℤ) : componentAugmentationIntegral ι z = z i := by
      classical
      rw [componentAugmentationIntegral, Finsupp.lsum_apply]
      exact Finsupp.sum_eq_single i (fun j _ hj ↦ (hj (Subsingleton.elim j i)).elim)
        fun _ ↦ LinearMap.map_zero _
    rw [← hsum x, ← hsum y, hxy]

/-- Helper for Theorem 63.7: integral singular `H₀` is the finitely supported
module on path components. -/
private noncomputable def singularHomologyZeroIsoFinsuppIntegral (X : TopCat) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj X ≅
      ModuleCat.of ℤ (ZerothHomotopy X →₀ ℤ) :=
  letI := Classical.decEq (ZerothHomotopy X)
  TopCat.singularHomology₀Iso X (ModuleCat.of ℤ ℤ) ≪≫
    ModuleCat.coprodIsoDirectSum
      (fun _ : ZerothHomotopy X ↦ ModuleCat.of ℤ ℤ) ≪≫
      (finsuppLEquivDirectSum ℤ ℤ (ZerothHomotopy X)).symm.toModuleIso

/-- Helper for Theorem 63.7: the coproduct-to-Finsupp comparison carries the fold
map to integral component augmentation. -/
private lemma coprodIsoDirectSum_hom_comp_componentAugmentationIntegral
    (ι : Type) [DecidableEq ι] :
    (ModuleCat.coprodIsoDirectSum (fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom ≫
        (finsuppLEquivDirectSum ℤ ℤ ι).symm.toModuleIso.hom ≫
          ModuleCat.ofHom (componentAugmentationIntegral ι) =
      Sigma.desc (fun _ : ι ↦ 𝟙 (ModuleCat.of ℤ ℤ)) := by
  -- Compare the maps on each coproduct generator.
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, Sigma.ι_desc]
  ext
  simp [finsuppLEquivDirectSum_symm_lof, componentAugmentationIntegral]

/-- Helper for Theorem 63.7: the normalized integral singular-`H₀` isomorphism
intertwines canonical augmentation with coefficient summation. -/
private lemma singularHomologyZeroIsoFinsuppIntegral_hom_comp_augmentation
    (X : TopCat) :
    (singularHomologyZeroIsoFinsuppIntegral X).hom ≫
        ModuleCat.ofHom (componentAugmentationIntegral (ZerothHomotopy X)) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
  -- Normalize through the coproduct and then identify its fold map.
  classical
  rw [singularHomologyZeroIsoFinsuppIntegral, Iso.trans_hom, Iso.trans_hom]
  rw [Category.assoc, Category.assoc,
    coprodIsoDirectSum_hom_comp_componentAugmentationIntegral]
  rw [TopCat.singularHomology₀Iso_sigma_desc_id]

/-- Helper for Theorem 63.7: reduced integral `H₀` is linearly equivalent to the
kernel of augmentation on component chains. -/
private lemma nonempty_reducedSingularHomologyZero_linearEquiv_componentKernel
    (X : TopCat) :
    Nonempty
      (AlgebraicTopology.ReducedSingularHomologyZero X ≃ₗ[ℤ]
        LinearMap.ker (componentAugmentationIntegral (ZerothHomotopy X))) := by
  -- Transport the categorical kernel across the normalized singular-`H₀` isomorphism.
  let ε := X.singularHomology₀ε (ModuleCat.of ℤ ℤ)
  let σ := ModuleCat.ofHom (componentAugmentationIntegral (ZerothHomotopy X))
  have hcompat : ε ≫ (Iso.refl _).hom =
      (singularHomologyZeroIsoFinsuppIntegral X).hom ≫ σ := by
    simpa [ε, σ] using
      (singularHomologyZeroIsoFinsuppIntegral_hom_comp_augmentation X).symm
  exact
    ⟨(kernel.mapIso ε σ (singularHomologyZeroIsoFinsuppIntegral X) (Iso.refl _) hcompat ≪≫
        ModuleCat.kernelIsoKer σ).toLinearEquiv⟩

/-- Helper for Theorem 63.7: on an open subset of a locally path-connected
space, preconnectedness is equivalent to vanishing reduced integral `H₀`. -/
private lemma isPreconnected_iff_isZero_reducedSingularHomologyZero
    {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X] (S : Set X)
    (hS : IsOpen S) :
    IsPreconnected S ↔
      IsZero (AlgebraicTopology.ReducedSingularHomologyZero (TopCat.of S)) := by
  -- Openness gives local path-connectedness on the subtype, after which both sides
  -- say that the path-component type is a subsingleton.
  letI : LocallyPathConnectedSpace S := hS.locallyPathConnectedSpace
  obtain ⟨e⟩ :=
    nonempty_reducedSingularHomologyZero_linearEquiv_componentKernel (TopCat.of S)
  calc
    IsPreconnected S ↔ PreconnectedSpace S := isPreconnected_iff_preconnectedSpace
    _ ↔ Subsingleton (ZerothHomotopy S) :=
      InvarianceOfDomainSupport.preconnectedSpace_iff_subsingleton_zerothHomotopy S
    _ ↔ Function.Injective (componentAugmentationIntegral (ZerothHomotopy S)) :=
      (componentAugmentationIntegral_injective_iff_subsingleton _).symm
    _ ↔ Subsingleton
        (LinearMap.ker (componentAugmentationIntegral (ZerothHomotopy S))) :=
      (InvarianceOfDomainSupport.subsingleton_ker_iff_injective _).symm
    _ ↔ Subsingleton (AlgebraicTopology.ReducedSingularHomologyZero (TopCat.of S)) :=
      e.toEquiv.subsingleton_congr.symm
    _ ↔ IsZero (AlgebraicTopology.ReducedSingularHomologyZero (TopCat.of S)) :=
      ModuleCat.isZero_iff_subsingleton.symm

/-- Helper for Theorem 63.7: every point of the standard zero-sphere is either a
chosen point or its antipode. -/
private lemma standardSphereZero_eq_or_eq_neg (x y : StandardSphere 0) :
    y = x ∨ y = -x := by
  -- The single coordinate of a point of `S⁰` has square one.
  have hx : x.1 0 ^ 2 = (1 : ℝ) := by
    have hx' :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) x.1).mp x.property
    simpa using hx'
  have hy : y.1 0 ^ 2 = (1 : ℝ) := by
    have hy' :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) y.1).mp y.property
    simpa using hy'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hx.symm) with hxy | hxy
  · left
    apply Subtype.ext
    ext i
    simpa only [Fin.eq_zero i] using hxy
  · right
    apply Subtype.ext
    ext i
    simpa [Fin.eq_zero i] using hxy

/-- Helper for Theorem 63.7: canonical complex coordinates preserve membership
in the Euclidean unit circle. -/
private lemma euclideanPlaneCoordinates_mem_unitSphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- The coordinate equivalence is a linear isometry, so it preserves norms.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 63.7: canonical Euclidean-complex coordinates identify
the standard one-sphere with the complex circle. -/
private noncomputable def standardSphereOneHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneCoordinates_mem_unitSphere

/-- Helper for Theorem 63.7: a subspace homeomorphic to the standard one-sphere
is a simple closed curve. -/
private lemma isSimpleClosedCurve_of_homeomorphic_standardSphereOne
    (C : Set (StandardSphere 2))
    (hC : Nonempty (C ≃ₜ StandardSphere 1)) :
    Topology.IsSimpleClosedCurve C := by
  -- Compose the given homeomorphism with the canonical identification of `S¹`
  -- and the complex circle.
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  exact hC.map (fun e ↦ e.trans standardSphereOneHomeomorphCircle)

/-- Helper for Theorem 63.7: deleting two distinct points disconnects the
standard one-sphere. -/
private lemma not_isPreconnected_standardSphereOne_compl_pair
    (a b : StandardSphere 1) (hab : a ≠ b) :
    ¬ IsPreconnected ({a, b}ᶜ : Set (StandardSphere 1)) := by
  -- Transfer the pair complement to the complex circle, where the path argument
  -- is already available.
  have habCircle : standardSphereOneHomeomorphCircle a ≠
      standardSphereOneHomeomorphCircle b :=
    standardSphereOneHomeomorphCircle.injective.ne hab
  intro hPreconnected
  apply Circle.not_isPreconnected_compl_pair habCircle
  apply (standardSphereOneHomeomorphCircle.isPreconnected_preimage).mp
  have hPreimage : standardSphereOneHomeomorphCircle ⁻¹'
      ({standardSphereOneHomeomorphCircle a,
        standardSphereOneHomeomorphCircle b}ᶜ : Set Circle) = {a, b}ᶜ := by
    ext z
    simp
  rw [hPreimage]
  exact hPreconnected


/-- Helper for Theorem 63.7: a real normed vector space has a neighborhood
basis of contractible metric balls. -/
private lemma stronglyLocallyContractibleSpace_normedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E := by
  -- Use the metric-ball neighborhood basis, whose positive-radius members are convex.
  exact StronglyLocallyContractibleSpace.of_bases
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ hr ↦ Metric.contractibleSpace_ball hr)

/-- Helper for Theorem 63.7: a charted space modeled on a strongly locally
contractible space is strongly locally contractible. -/
private lemma stronglyLocallyContractibleSpace_chartedSpace
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  -- Pull a contractible basis contained in each chart target back through the chart.
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun x s ↦
      s ∈ nhds (chartAt H x x) ∧ ContractibleSpace s ∧
        s ⊆ (chartAt H x).target)
    (s := fun x s ↦ (chartAt H x).symm '' s) ?_ ?_
  · intro x
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((contractible_basis (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  · rintro x s ⟨_, hsContractible, hsTarget⟩
    -- The restricted inverse chart identifies the pulled-back set with `s`.
    letI : ContractibleSpace s := hsContractible
    exact
      ((chartAt H x).symm.homeomorphOfImageSubsetSource hsTarget rfl).symm.contractibleSpace

/-- Helper for Theorem 63.7: every subspace homeomorphic to a standard sphere
is locally contractible. -/
private lemma locallyContractibleSpace_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    LocallyContractibleSpace C := by
  -- Standard spheres are charted by Euclidean space, which has contractible balls.
  letI : StronglyLocallyContractibleSpace (EuclideanSpace ℝ (Fin n)) :=
    stronglyLocallyContractibleSpace_normedSpace _
  have hSphereStrong : StronglyLocallyContractibleSpace (StandardSphere n) :=
    stronglyLocallyContractibleSpace_chartedSpace
      (EuclideanSpace ℝ (Fin n)) (StandardSphere n)
  obtain ⟨e⟩ := hC
  letI : StronglyLocallyContractibleSpace (StandardSphere n) := hSphereStrong
  have hCStrong : StronglyLocallyContractibleSpace C :=
    e.isOpenEmbedding.stronglyLocallyContractibleSpace
  letI : StronglyLocallyContractibleSpace C := hCStrong
  exact StronglyLocallyContractibleSpace.locallyContractible (X := C)

/-- Helper for Theorem 63.7: an integral module is nonzero when it is
isomorphic to the rank-one integral module. -/
private lemma not_isZero_of_nonempty_iso_moduleCatInt {M : ModuleCat ℤ}
    (hM : Nonempty (M ≅ ModuleCat.of ℤ ℤ)) : ¬ IsZero M := by
  obtain ⟨e⟩ := hM
  intro hZero
  -- Transport zero-ness across the isomorphism, then distinguish zero from one.
  have hIntZero : IsZero (ModuleCat.of ℤ ℤ) := IsZero.of_iso hZero e.symm
  have hIntSubsingleton : Subsingleton (ModuleCat.of ℤ ℤ) :=
    ModuleCat.isZero_iff_subsingleton.mp hIntZero
  exact zero_ne_one (@Subsingleton.elim (ModuleCat.of ℤ ℤ) hIntSubsingleton 0 1)

namespace InvarianceOfDomainSupport

universe u

/-- Helper for Theorem 63.7: the transposed graph incidence followed by the
transposed vertex augmentation is zero over `ZMod 2`. -/
lemma incMatrixTranspose_mul_vertexAugmentationTranspose
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (G.incMatrix (ZMod 2)).transpose *
        (vertexAugmentationMatrix V).transpose = 0 := by
  have hBoundary :
      vertexAugmentationMatrix V * G.incMatrix (ZMod 2) = 0 := by
    -- Compare linear maps, where the augmentation computation is part of the public API.
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul,
      Matrix.mulVecLin_zero]
    apply LinearMap.ext
    intro x
    ext u
    rw [LinearMap.comp_apply, LinearMap.zero_apply,
      vertexAugmentationMatrix_mulVecLin_apply]
    simp_rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    rw [← Finset.sum_mul]
    by_cases he : e ∈ G.edgeSet
    · -- An actual edge has two endpoints, whose mod-two coefficients add to zero.
      rw [G.sum_incMatrix_apply_of_mem_edgeSet he]
      have hTwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      rw [hTwo, zero_mul]
    · -- A non-edge has an identically zero incidence column.
      rw [G.sum_incMatrix_apply_of_notMem_edgeSet he, zero_mul]
  -- Transposition reverses the already-zero augmented incidence product.
  rw [← Matrix.transpose_mul, hBoundary, Matrix.transpose_zero]

/-- Helper for Theorem 63.7: dual incidence of a transpose, reindexed by
identity equivalences, recovers the original matrix. -/
lemma dualIncidenceMatrix_transpose_refl
    {R I J : Type*} (A : Matrix I J R) :
    dualIncidenceMatrix A.transpose (Equiv.refl J) (Equiv.refl I) = A := by
  -- Evaluate corresponding cells through the public dual-incidence formula.
  ext i j
  simpa only [Equiv.refl_apply, Matrix.transpose_apply] using
    (dualIncidenceMatrix_apply A.transpose (Equiv.refl J) (Equiv.refl I) i j)

namespace FiniteGraphDualCochainModel

/-- Helper for Theorem 63.7: every finite simple graph has the canonical primal
cochain model obtained by transposing incidence and augmentation. -/
def ofGraph {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] : FiniteGraphDualCochainModel G Unit V (Sym2 V) :=
  { lower := (vertexAugmentationMatrix V).transpose
    upper := (G.incMatrix (ZMod 2)).transpose
    lowDual := Equiv.refl Unit
    middleDual := Equiv.refl V
    highDual := Equiv.refl (Sym2 V)
    squareZero := incMatrixTranspose_mul_vertexAugmentationTranspose G
    dualUpper_eq_graphIncidence :=
      dualIncidenceMatrix_transpose_refl (G.incMatrix (ZMod 2))
    dualLower_eq_vertexAugmentation :=
      dualIncidenceMatrix_transpose_refl (vertexAugmentationMatrix V) }

end FiniteGraphDualCochainModel

/-- Helper for Theorem 63.7: a finite graph with at most one connected
component has trivial reduced mod-two graph homology. -/
lemma graphReducedHomologyZeroModTwo_subsingleton_of_components
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (hComponents : Subsingleton G.ConnectedComponent) :
    Subsingleton (graphReducedHomologyZeroModTwo G) := by
  -- Normalize graph homology to the augmentation kernel on components.
  obtain ⟨e⟩ := graphReducedHomologyZeroModTwo_linearEquiv_componentKernel G
  have hAugmentation :
      Function.Injective (componentAugmentationModTwo G.ConnectedComponent) :=
    (componentAugmentationModTwo_injective_iff_subsingleton _).mpr hComponents
  have hKernel :
      Subsingleton
        (LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent)) :=
    (subsingleton_ker_iff_injective _).mpr hAugmentation
  -- Transport kernel triviality back through the graph-homology equivalence.
  exact e.toEquiv.subsingleton_congr.mpr hKernel

namespace FiniteAlexanderStage

/-- Helper for Theorem 63.7: a finite Alexander stage with at most one graph
component has zero cover-stage cohomology. -/
lemma isZero_coverCohomology_of_subsingleton_components
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q)
    (hComponents : Subsingleton A.graph.ConnectedComponent) :
    IsZero (liftedFaceNerveCohomology A.cover q) := by
  -- First kill graph homology, then transport vanishing through finite duality
  -- and the single universe-lift bridge supplied by the stage.
  have hGraph :
      IsZero
        (ModuleCat.of (ZMod 2)
          (graphReducedHomologyZeroModTwo A.graph)) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (graphReducedHomologyZeroModTwo_subsingleton_of_components
        A.graph hComponents)
  have hLifted :
      IsZero
        ((ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj
          (ModuleCat.of (ZMod 2)
            (graphReducedHomologyZeroModTwo A.graph))) :=
    Functor.map_isZero (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)) hGraph
  exact IsZero.of_iso hLifted A.finiteDuality

end FiniteAlexanderStage

/-- Helper for Theorem 63.7: a nonzero homology class lifted through a cover
refinement makes the target's lifted face-nerve cohomology nonzero. -/
lemma not_isZero_liftedFaceNerveCohomology_of_homology_lift
    {X : Type} [TopologicalSpace X] {q : ℕ}
    {U V : CechFiniteOpenCover.{0, 0} X}
    [DecidableEq U.Index] (f : CechFiniteOpenCover.RefinementMap U V)
    (zU : CechFiniteOpenCover.faceNerveHomology U q) (hzU : zU ≠ 0)
    (zV : CechFiniteOpenCover.faceNerveHomology V q)
    (hLift : f.faceNerveHomologyMap q zV = zU) :
    ¬ IsZero (liftedFaceNerveCohomology V q) := by
  -- Separate the nonzero source class by a dual functional, then pull that
  -- functional to the target along the homology comparison.
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_ne_zero (ZMod 2) hzU
  let φV : CechFiniteOpenCover.faceNerveCohomology V q :=
    (f.faceNerveHomologyMap q).hom.dualMap φ
  have hφV : φV ≠ 0 := by
    intro hφVZero
    apply hφ
    calc
      φ zU = φ (f.faceNerveHomologyMap q zV) := congrArg φ hLift.symm
      _ = φV zV := by
        exact (LinearMap.dualMap_apply
          (f.faceNerveHomologyMap q).hom φ zV).symm
      _ = 0 := by
        rw [hφVZero, LinearMap.zero_apply]
  intro hLiftedZero
  -- Full faithfulness of universe lifting reflects the alleged zero object to
  -- the ordinary dual module, contradicting the pulled-back functional.
  have hRawZero :
      IsZero
        (ModuleCat.of (ZMod 2)
          (CechFiniteOpenCover.faceNerveCohomology V q)) :=
    IsZero.of_full_of_faithful_of_isZero
      (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)) _ hLiftedZero
  have hRawSubsingleton :
      Subsingleton (CechFiniteOpenCover.faceNerveCohomology V q) :=
    ModuleCat.isZero_iff_subsingleton.mp hRawZero
  exact hφV (hRawSubsingleton.elim _ _)

namespace FiniteGraphDualCochainModel

/-- Helper for Theorem 63.7: a graph-dual cochain model is exact when its
underlying graph has at most one connected component. -/
lemma exact_of_subsingleton_components
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    [DecidableRel G.Adj] {low middle high : Type u}
    [Fintype low] [Fintype middle] [Fintype high]
    (M : FiniteGraphDualCochainModel G low middle high)
    (hComponents : Subsingleton G.ConnectedComponent) :
    Function.Exact M.lower.mulVecLin M.upper.mulVecLin := by
  -- Apply finite dual incidence after reducing the target to graph homology.
  apply M.exact_iff_graphHomologySubsingleton.mpr
  exact graphReducedHomologyZeroModTwo_subsingleton_of_components G hComponents

end FiniteGraphDualCochainModel

/-- Helper for Theorem 63.7: the outside-face comparability graph carries its
canonical transposed-incidence cochain model. -/
noncomputable abbrev outsideFaceGraphDualCochainModel {n : ℕ}
    (K : SSet.Subcomplex.{0} (SSet.boundary (n + 1)).toSSet) :=
  letI : Finite K.N := finiteOutsideBoundarySubcomplexFaces K
  letI : Fintype K.N := Fintype.ofFinite K.N
  letI : DecidableEq K.N := Classical.decEq K.N
  letI : DecidableRel (outsideFaceComparabilityGraph K).Adj := Classical.decRel _
  FiniteGraphDualCochainModel.ofGraph (outsideFaceComparabilityGraph K)

/-- Helper for Theorem 63.7: exactness of the canonical outside-face graph
cochain model, with all finite data fixed internally. -/
noncomputable abbrev outsideFaceGraphDualCochainModelExact {n : ℕ}
    (K : SSet.Subcomplex.{0} (SSet.boundary (n + 1)).toSSet) : Prop :=
  letI : Finite K.N := finiteOutsideBoundarySubcomplexFaces K
  letI : Fintype K.N := Fintype.ofFinite K.N
  letI : DecidableEq K.N := Classical.decEq K.N
  letI : DecidableRel (outsideFaceComparabilityGraph K).Adj := Classical.decRel _
  Function.Exact
    (outsideFaceGraphDualCochainModel K).lower.mulVecLin
    (outsideFaceGraphDualCochainModel K).upper.mulVecLin

/-- Helper for Theorem 63.7: the canonical outside-face graph model is
nonexact exactly when the realized boundary complement has nonzero reduced
mod-two `H₀`. -/
lemma BoundaryComplementOpenStarModel.not_isZero_reducedHomologyZeroModTwo_iff_graphModel_notExact
    {n : ℕ} {K : SSet.Subcomplex.{0} (SSet.boundary (n + 1)).toSSet}
    (M : BoundaryComplementOpenStarModel n K) :
    ¬ IsZero
        (reducedHomologyZeroModTwo
          (TopCat.of (boundaryRealizationComplement n K))) ↔
      ¬ outsideFaceGraphDualCochainModelExact K := by
  -- Negate the geometric vanishing comparison, then use finite dual incidence.
  calc
    ¬ IsZero
        (reducedHomologyZeroModTwo
          (TopCat.of (boundaryRealizationComplement n K))) ↔
        ¬ Subsingleton (outsideFaceGraphReducedHomologyZeroModTwo K) :=
      not_congr M.isZero_reducedHomologyZeroModTwo_iff
    _ ↔ ¬ outsideFaceGraphDualCochainModelExact K := by
      letI : Finite K.N := finiteOutsideBoundarySubcomplexFaces K
      letI : Fintype K.N := Fintype.ofFinite K.N
      letI : DecidableEq K.N := Classical.decEq K.N
      letI : DecidableRel (outsideFaceComparabilityGraph K).Adj := Classical.decRel _
      simpa only [outsideFaceGraphReducedHomologyZeroModTwo,
        outsideFaceGraphDualCochainModelExact,
        outsideFaceGraphDualCochainModel] using
        (FiniteGraphDualCochainModel.ofGraph
          (outsideFaceComparabilityGraph K)).graphHomologyNontrivial_iff_not_exact

/- The coherent-cocone route below is retained only as route history.  It asked
for refinement compatibility that the separation argument does not need.

/-- Helper for Theorem 63.7: lift reduced mod-two `H₀` to the universe of the
reduced Čech colimit. -/
private noncomputable abbrev liftedReducedHomologyZeroModTwo (X : TopCat.{0}) :
    ModuleCat.{1} (ZMod 2) :=
  (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj (reducedHomologyZeroModTwo X)

-- Route correction: the imported named Čech colimit aliases have opaque bodies,
-- so this local interface uses their canonical explicit `colimit` normal form.
/-- Helper for Theorem 63.7: a colimiting finite-stage Alexander cocone
identifies reduced Čech cohomology with lifted reduced `H₀`. -/
private noncomputable def reducedCechAlexanderIsoOfIsColimit
    (K X : TopCat.{0}) (q : ℕ)
    (α : CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q ⟶
      (Functor.const _).obj (liftedReducedHomologyZeroModTwo X))
    (hα : IsColimit (Cocone.mk _ α)) :
    colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q) ≅
      liftedReducedHomologyZeroModTwo X :=
  -- Compare the canonical colimit cocone with the supplied colimiting cocone.
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hα

/-- Helper for Theorem 63.7: the colimit comparison restricts at each finite
cover to the supplied Alexander cocone leg. -/
private lemma reducedCechAlexanderIso_hom_comp_ι
    (K X : TopCat.{0}) (q : ℕ)
    (α : CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q ⟶
      (Functor.const _).obj (liftedReducedHomologyZeroModTwo X))
    (hα : IsColimit (Cocone.mk _ α))
    (U : CechFiniteOpenCover.{0, 0} K) :
    colimit.ι (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q) U ≫
        (reducedCechAlexanderIsoOfIsColimit K X q α hα).hom =
      α.app U := by
  -- Compute the unique comparison map on the canonical colimit generator.
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) hα U

/-- Helper for Theorem 63.7: a nonzero reduced Čech colimit and a colimiting
Alexander cocone force the unlifted reduced mod-two `H₀` target to be nonzero. -/
private lemma not_isZero_reducedHomologyZeroModTwo_of_reducedCechAlexanderCocone
    (K X : TopCat.{0}) (q : ℕ)
    (α : CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q ⟶
      (Functor.const _).obj (liftedReducedHomologyZeroModTwo X))
    (hα : IsColimit (Cocone.mk _ α))
    (hCech : ¬ IsZero
      (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q))) :
    ¬ IsZero (reducedHomologyZeroModTwo X) := by
  intro hHomologyZero
  -- Universe lifting preserves a zero target.
  have hLiftedZero : IsZero (liftedReducedHomologyZeroModTwo X) :=
    Functor.map_isZero (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)) hHomologyZero
  -- The colimit comparison then makes the nonzero Čech source zero as well.
  apply hCech
  exact IsZero.of_iso hLiftedZero
    (reducedCechAlexanderIsoOfIsColimit K X q α hα)

-- Route correction: the previous package stored colimitness and sphere
-- nonvanishing together, obscuring the missing geometric construction.  Keep
-- adapted-stage coherence in a final restricted diagram and extend it only once.
/-- Helper for Theorem 63.7: a compact subset has a final adapted-cover diagram
whose compatible Alexander comparison is colimiting. -/
private structure CoherentCompactAlexanderDiagram
    (n : ℕ) (K : Set (StandardSphere (n + 1))) where
  /-- The indices for the adapted finite stages. -/
  J : Type 1
  /-- Adapted stages form a category. -/
  [category : CategoryTheory.Category.{1} J]
  /-- The adapted stages define a final subsystem of finite covers. -/
  cover : J ⥤ CechFiniteOpenCover.{0, 0} K
  /-- The adapted-cover subsystem is final. -/
  [final : cover.Final]
  /-- The finite Alexander maps are compatible with refinement. -/
  comparison :
    cover ⋙ CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) n ⟶
      (Functor.const J).obj
        (liftedReducedHomologyZeroModTwo
          (TopCat.of (Kᶜ : Set (StandardSphere (n + 1)))))
  /-- The compatible comparison computes the complement invariant. -/
  comparisonIsColimit : IsColimit (Cocone.mk _ comparison)

/-- Helper for Theorem 63.7: compact subsets admit coherent adapted finite
Alexander diagrams. -/
private lemma nonempty_coherentCompactAlexanderDiagram
    (n : ℕ) (K : Set (StandardSphere (n + 1))) (hK : IsCompact K) :
    Nonempty (CoherentCompactAlexanderDiagram n K) := by
  -- TODO: construct ambient barycentric subdivisions subordinate to each cover,
  -- prove refinement compatibility by incidence/component squares, and prove
  -- that the finite complement models form a colimiting cocone.
  unresolved

/-- Helper for Theorem 63.7: a coherent adapted-cover comparison extends to a
colimiting Alexander cocone on the full finite-cover diagram. -/
private lemma existsColimitingReducedCechAlexanderCocone
    {n : ℕ} {K : Set (StandardSphere (n + 1))}
    (A : CoherentCompactAlexanderDiagram n K) :
    ∃ α : CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) n ⟶
          (Functor.const _).obj
            (liftedReducedHomologyZeroModTwo
              (TopCat.of (Kᶜ : Set (StandardSphere (n + 1))))),
      Nonempty (IsColimit (Cocone.mk _ α)) := by
  -- Extend the restricted cocone along the final adapted-cover functor.
  letI : CategoryTheory.Category A.J := A.category
  letI : A.cover.Final := A.final
  let restricted := Cocone.mk _ A.comparison
  let extended := Functor.Final.extendCocone.obj restricted
  refine ⟨extended.ι, ⟨?_⟩⟩
  -- Finality transfers the verified colimit property to the full diagram.
  exact
    (Functor.Final.isColimitExtendCoconeEquiv A.cover restricted).symm
      A.comparisonIsColimit

/-- Helper for Theorem 63.7: universe lifting preserves and reflects vanishing
of reduced mod-two `H₀`. -/
private lemma isZero_liftedReducedHomologyZeroModTwo_iff (X : TopCat.{0}) :
    IsZero (liftedReducedHomologyZeroModTwo X) ↔
      IsZero (reducedHomologyZeroModTwo X) := by
  -- Normalize both categorical assertions to subsingleton carriers.
  calc
    IsZero (liftedReducedHomologyZeroModTwo X) ↔
        Subsingleton (liftedReducedHomologyZeroModTwo X) :=
      ModuleCat.isZero_iff_subsingleton
    _ ↔ Subsingleton (reducedHomologyZeroModTwo X) :=
      Equiv.ulift.subsingleton_congr
    _ ↔ IsZero (reducedHomologyZeroModTwo X) :=
      ModuleCat.isZero_iff_subsingleton.symm

/-- Helper for Theorem 63.7: a coherent compact Alexander comparison reflects
nonvanishing of the complement invariant to the full Čech colimit. -/
private lemma not_isZero_reducedCechCohomology_of_coherentAlexanderDiagram
    {n : ℕ} {K : Set (StandardSphere (n + 1))}
    (A : CoherentCompactAlexanderDiagram n K)
    (hComplement :
      ¬ IsZero
        (reducedHomologyZeroModTwo
          (TopCat.of (Kᶜ : Set (StandardSphere (n + 1)))))) :
    ¬ IsZero
      (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) n)) := by
  -- Extend the coherent comparison and use its colimit isomorphism.
  obtain ⟨α, ⟨hα⟩⟩ := existsColimitingReducedCechAlexanderCocone A
  intro hCechZero
  have hLiftedZero :
      IsZero
        (liftedReducedHomologyZeroModTwo
          (TopCat.of (Kᶜ : Set (StandardSphere (n + 1))))) :=
    IsZero.of_iso hCechZero
      (reducedCechAlexanderIsoOfIsColimit
        (TopCat.of K)
        (TopCat.of (Kᶜ : Set (StandardSphere (n + 1)))) n α hα).symm
  -- Remove the universe lift to contradict complement nonvanishing.
  exact hComplement
    ((isZero_liftedReducedHomologyZeroModTwo_iff
      (TopCat.of (Kᶜ : Set (StandardSphere (n + 1))))).mp hLiftedZero)

/-- Helper for Theorem 63.7: the top reduced mod-two Čech class of an
embedded standard sphere is nonzero. -/
private lemma not_isZero_reducedCechCohomologyModTwo_of_homeomorphic_standardSphere
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ¬ IsZero
      (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := C) n)) := by
  -- TODO: transport covers through the supplied homeomorphism and compute the
  -- standard sphere's top class by applying the coherent comparison to the
  -- coordinate equator, whose complement has two sign components.
  unresolved

/-- Helper for Theorem 63.7: an embedded standard sphere admits a colimiting
Alexander cocone whose top reduced Čech source is nonzero. -/
private lemma existsColimitingAlexanderCoconeWithNonzeroSphereSource
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ∃ α : CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := C) n ⟶
          (Functor.const _).obj
            (liftedReducedHomologyZeroModTwo
              (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))),
      Nonempty (IsColimit (Cocone.mk _ α)) ∧
        ¬ IsZero
          (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
            (X := C) n)) := by
  -- Compactness supplies the coherent restricted diagram, and finality extends it.
  obtain ⟨A⟩ := nonempty_coherentCompactAlexanderDiagram n C
    (isCompact_of_homeomorphic_standardSphere n C hC)
  obtain ⟨α, ⟨hα⟩⟩ := existsColimitingReducedCechAlexanderCocone A
  -- The independently computed sphere class completes the shared package.
  exact
    ⟨α, ⟨hα⟩,
      not_isZero_reducedCechCohomologyModTwo_of_homeomorphic_standardSphere n C hC⟩

/-- Helper for Theorem 63.7: finite Alexander maps assemble to a monomorphism
from top reduced Čech cohomology into reduced homology of the complement. -/
private lemma exists_mono_reducedCechAlexanderMap_sphereEmbedding
    (n : ℕ) (hn : 0 < n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ∃ f :
        colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
          (X := C) n) ⟶
          liftedReducedHomologyZeroModTwo
            (TopCat.of (Cᶜ : Set (StandardSphere (n + 1)))),
      Mono f := by
  -- The colimiting cocone identifies its target with the canonical Čech
  -- colimit; the forward comparison of this isomorphism is monomorphic.
  clear hn
  obtain ⟨α, ⟨hα⟩, _⟩ :=
    existsColimitingAlexanderCoconeWithNonzeroSphereSource n C hC
  let f :=
    (reducedCechAlexanderIsoOfIsColimit
      (TopCat.of C)
      (TopCat.of (Cᶜ : Set (StandardSphere (n + 1)))) n α hα).hom
  have hf : Mono f := inferInstance
  exact ⟨f, hf⟩

/-- Helper for Theorem 63.7: a monomorphic Alexander comparison from a
nonzero reduced Čech colimit forces its unlifted homology target to be nonzero. -/
private lemma not_isZero_reducedHomologyZeroModTwo_of_mono_reducedCechAlexanderMap
    (K X : TopCat.{0}) (q : ℕ)
    (f : colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q) ⟶ liftedReducedHomologyZeroModTwo X)
    [Mono f]
    (hCech : ¬ IsZero
      (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := K) q))) :
    ¬ IsZero (reducedHomologyZeroModTwo X) := by
  intro hHomologyZero
  -- Lift target vanishing once, then reflect it across the monomorphism.
  have hLiftedZero : IsZero (liftedReducedHomologyZeroModTwo X) :=
    Functor.map_isZero (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)) hHomologyZero
  apply hCech
  exact IsZero.of_mono f hLiftedZero
-/

/-- Helper for Theorem 63.7: forgetting a universe-lifted filtered colimit of
mod-two modules preserves its chosen colimit. -/
lemma preservesColimit_forget₂_universeLiftedModule
    {J : Type 1} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{1} (ZMod 2)) :
    PreservesColimit F
      (forget₂ (ModuleCat.{1} (ZMod 2)) AddCommGrpCat.{1}) := by
  -- Use the explicit filtered-colimit cocones because the generic instance
  -- only applies when module and coefficient-ring universes coincide.
  exact
    preservesColimit_of_preserves_colimit_cocone
      (F := forget₂ (ModuleCat.{1} (ZMod 2)) AddCommGrpCat.{1})
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
        (F ⋙ forget₂ (ModuleCat.{1} (ZMod 2)) AddCommGrpCat.{1}))

/-- Helper for Theorem 63.7: the type-valued forgetful functor preserves a
universe-lifted filtered colimit of mod-two modules. -/
lemma preservesColimit_forget_universeLiftedModule
    {J : Type 1} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{1} (ZMod 2)) :
    PreservesColimit F (forget (ModuleCat.{1} (ZMod 2))) := by
  -- First forget scalar multiplication, then use preservation by the ordinary
  -- additive-group forgetful functor.
  -- Local instance justification (universe bridge): the standard instance does
  -- not cover modules lifted above the coefficient-ring universe.
  letI : PreservesColimit F
      (forget₂ (ModuleCat.{1} (ZMod 2)) AddCommGrpCat.{1}) :=
    preservesColimit_forget₂_universeLiftedModule F
  change PreservesColimit F
    (forget₂ (ModuleCat.{1} (ZMod 2)) AddCommGrpCat.{1} ⋙
      forget AddCommGrpCat.{1})
  infer_instance

/-- Helper for Theorem 63.7: a module colimit is zero if every stage maps to a
zero stage. -/
lemma isZero_colimit_of_eventually_isZero
    {J : Type 1} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{1} (ZMod 2)) [HasColimit F]
    (hEventually : ∀ j, ∃ (k : J) (_ : j ⟶ k), IsZero (F.obj k)) :
    IsZero (colimit F) := by
  -- Every colimit element is represented at one stage; move that representative
  -- to a supplied zero stage before comparing arbitrary elements.
  -- Local instance justification (universe bridge): concrete representatives
  -- require preservation by the type-valued forgetful functor.
  letI : PreservesColimit F (forget (ModuleCat.{1} (ZMod 2))) :=
    preservesColimit_forget_universeLiftedModule F
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  obtain ⟨i, xi, rfl⟩ := Concrete.colimit_exists_rep F x
  obtain ⟨j, yj, rfl⟩ := Concrete.colimit_exists_rep F y
  have representative_eq_zero (k : J) (z : F.obj k) :
      colimit.ι F k z = 0 := by
    obtain ⟨l, f, hl⟩ := hEventually k
    have hlSubsingleton : Subsingleton (F.obj l) :=
      ModuleCat.isZero_iff_subsingleton.mp hl
    have hMapZero : F.map f z = 0 := Subsingleton.elim _ _
    have hNaturality := ConcreteCategory.congr_hom (colimit.w F f) z
    calc
      colimit.ι F k z = (F.map f ≫ colimit.ι F l) z := hNaturality.symm
      _ = colimit.ι F l (F.map f z) := by
        rw [CategoryTheory.comp_apply]
      _ = 0 := by
        rw [hMapZero, map_zero]
  exact (representative_eq_zero i xi).trans
    (representative_eq_zero j yj).symm

/-- Helper for Theorem 63.7: a persistent Čech class is represented at one
finite cover and stays nonzero after every refinement. -/
def HasPersistentCechClass (X : Type) [TopologicalSpace X] (q : ℕ) : Prop :=
  ∃ (U : CechFiniteOpenCover.{0, 0} X)
      (z : (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0} q).obj U),
    z ≠ 0 ∧
      ∀ {V : CechFiniteOpenCover.{0, 0} X} (f : U ⟶ V),
        (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0} q).map f z ≠ 0

/-- Helper for Theorem 63.7: a persistent finite-cover class makes the reduced
Čech colimit nonzero. -/
lemma not_isZero_colimit_of_hasPersistentCechClass
    {X : Type} [TopologicalSpace X] {q : ℕ}
    (hPersistent : HasPersistentCechClass X q) :
    ¬ IsZero
      (colimit (CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0}
        (X := X) q)) := by
  -- If its colimit image vanished, filtered-colimit equality would kill it at
  -- one common refinement, contradicting persistence.
  let F : CechFiniteOpenCover.{0, 0} X ⥤ ModuleCat.{1} (ZMod 2) :=
    CechFiniteOpenCover.reducedCechCohomologyDiagram.{0, 0} (X := X) q
  -- Local instance justification (filtered cover index): the project exposes
  -- this fact as a named lemma rather than an instance.
  letI : IsFiltered (CechFiniteOpenCover.{0, 0} X) :=
    CechFiniteOpenCover.isFiltered
  -- Local instance justification (universe bridge): the equality criterion for
  -- concrete colimit representatives needs the forgetful preservation fact.
  letI : PreservesColimit F (forget (ModuleCat.{1} (ZMod 2))) :=
    preservesColimit_forget_universeLiftedModule F
  obtain ⟨U, z, hz, hRefinement⟩ := hPersistent
  intro hColimitZero
  have hColimitSubsingleton : Subsingleton ↑(colimit F) :=
    ModuleCat.isZero_iff_subsingleton.mp hColimitZero
  have hImageZero : colimit.ι F U z = colimit.ι F U 0 :=
    Subsingleton.elim _ _
  obtain ⟨V, f, g, hfg⟩ :=
    (Concrete.colimit_rep_eq_iff_exists F z 0).mp hImageZero
  apply hRefinement f
  calc
    F.map f z = F.map g 0 := hfg
    _ = 0 := map_zero _

/-- Helper for Theorem 63.7: the coordinate simplex-hemisphere indexed by a
vertex of an abstract `(n + 1)`-simplex. -/
private def simplexHemisphereSet (n : ℕ) :
    Fin (n + 2) → Set (StandardSphere n) :=
  Fin.lastCases
    {x | ∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j < 0}
    (fun i ↦ {x | 0 < (x : EuclideanSpace ℝ (Fin (n + 1))) i})

/-- Helper for Theorem 63.7: every coordinate simplex-hemisphere is open in
the standard sphere. -/
private lemma isOpen_simplexHemisphereSet (n : ℕ) (i : Fin (n + 2)) :
    IsOpen (simplexHemisphereSet n i) := by
  -- Separate the final negative-sum hemisphere from the coordinate hemispheres.
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hSum : Continuous (fun x : StandardSphere n ↦
        ∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j) :=
      continuous_finsetSum Finset.univ fun j _ ↦
        (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) j).comp
          continuous_subtype_val
    simpa only [simplexHemisphereSet, Fin.lastCases_last] using
      isOpen_lt hSum continuous_const
  · have hCoordinate : Continuous (fun x : StandardSphere n ↦
        (x : EuclideanSpace ℝ (Fin (n + 1))) j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) j).comp
        continuous_subtype_val
    simpa only [simplexHemisphereSet, Fin.lastCases_castSucc] using
      isOpen_lt continuous_const hCoordinate

/-- Helper for Theorem 63.7: the coordinate simplex-hemispheres cover the
standard sphere. -/
private lemma iUnion_simplexHemisphereSet (n : ℕ) :
    ⋃ i, simplexHemisphereSet n i = Set.univ := by
  -- A point with a positive coordinate lies in its coordinate hemisphere.
  apply Set.eq_univ_of_forall
  intro x
  by_cases hPositive : ∃ j : Fin (n + 1), 0 <
      (x : EuclideanSpace ℝ (Fin (n + 1))) j
  · obtain ⟨j, hj⟩ := hPositive
    apply Set.mem_iUnion.mpr
    refine ⟨j.castSucc, ?_⟩
    simpa only [simplexHemisphereSet, Fin.lastCases_castSucc,
      Set.mem_setOf_eq] using hj
  · -- Otherwise every coordinate is nonpositive; their sum is strictly negative,
    -- since a unit-sphere point cannot be the zero vector.
    have hNonpositive (j : Fin (n + 1)) :
        (x : EuclideanSpace ℝ (Fin (n + 1))) j ≤ 0 := by
      exact not_lt.mp (not_exists.mp hPositive j)
    have hSumNegative :
        ∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j < 0 := by
      have hSumNonpositive :
          ∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j ≤ 0 :=
        Finset.sum_nonpos fun j _ ↦ hNonpositive j
      refine lt_of_le_of_ne hSumNonpositive ?_
      intro hSumZero
      have hCoordinateZero (j : Fin (n + 1)) :
          (x : EuclideanSpace ℝ (Fin (n + 1))) j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos
          (fun k _ ↦ hNonpositive k)).mp hSumZero j (Finset.mem_univ j)
      have hxZero : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
        apply PiLp.ext
        intro j
        simpa only [PiLp.zero_apply] using hCoordinateZero j
      exact ne_zero_of_mem_unit_sphere x hxZero
    apply Set.mem_iUnion.mpr
    refine ⟨Fin.last (n + 1), ?_⟩
    simpa only [simplexHemisphereSet, Fin.lastCases_last,
      Set.mem_setOf_eq] using hSumNegative

/-- Helper for Theorem 63.7: the coordinate simplex-hemisphere family is an
indexed open cover of the standard sphere. -/
private lemma simplexHemisphereFamily_isCover (n : ℕ) :
    TopologicalSpace.IsOpenCover (fun i : Fin (n + 2) ↦
      (⟨simplexHemisphereSet n i, isOpen_simplexHemisphereSet n i⟩ :
        TopologicalSpace.Opens (StandardSphere n))) := by
  -- Forget the bundled openness and apply the proved union calculation.
  apply TopologicalSpace.IsOpenCover.of_sets
  exact iUnion_simplexHemisphereSet n

/-- Helper for Theorem 63.7: the explicit finite simplex-hemisphere cover of
the standard sphere. -/
private def simplexHemisphereCover (n : ℕ) :
    CechFiniteOpenCover.{0, 0} (StandardSphere n) :=
  { Index := Fin (n + 2)
    indexFintype := Fin.fintype (n + 2)
    opens := fun i ↦
      ⟨simplexHemisphereSet n i, isOpen_simplexHemisphereSet n i⟩
    isCover := simplexHemisphereFamily_isCover n }

/-- Helper for Theorem 63.7: pull a finite indexed open cover back along a
homeomorphism without changing its index type. -/
private abbrev CechFiniteOpenCover.comapHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : CechFiniteOpenCover.{0, 0} X) (e : Y ≃ₜ X) :
    CechFiniteOpenCover.{0, 0} Y :=
  { Index := U.Index
    indexFintype := U.indexFintype
    opens := fun i ↦ (U.opens i).comap (e : C(Y, X))
    isCover := U.isCover.comap (e : C(Y, X)) }

/-- Helper for Theorem 63.7: a surjection preserves nonemptiness of every
finite intersection after taking preimages. -/
private lemma iInter_preimage_nonempty_iff_of_surjective
    {ι X Y : Type} (f : Y → X) (hf : Function.Surjective f)
    (A : ι → Set X) (s : Finset ι) :
    (⋂ i ∈ s, f ⁻¹' A i).Nonempty ↔ (⋂ i ∈ s, A i).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    -- The image of a common preimage point lies in every original set.
    refine ⟨f y, ?_⟩
    simpa only [Set.mem_iInter, Set.mem_preimage] using hy
  · rintro ⟨x, hx⟩
    -- Lift a common point through surjectivity and reuse all its memberships.
    obtain ⟨y, rfl⟩ := hf x
    refine ⟨y, ?_⟩
    simpa only [Set.mem_iInter, Set.mem_preimage] using hx

/-- Helper for Theorem 63.7: pulling a finite open cover back through a
homeomorphism preserves every finite-intersection nonemptiness test. -/
private lemma iInter_comapHomeomorph_nonempty_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : CechFiniteOpenCover.{0, 0} X) (e : Y ≃ₜ X)
    (s : Finset U.Index) :
    (⋂ i ∈ s, ((U.comapHomeomorph e).opens i : Set Y)).Nonempty ↔
      (⋂ i ∈ s, (U.opens i : Set X)).Nonempty := by
  -- Reduce the bundled open sets to preimages, then use surjectivity.
  simpa only [CechFiniteOpenCover.comapHomeomorph,
    TopologicalSpace.Opens.coe_comap] using
    iInter_preimage_nonempty_iff_of_surjective
      ((e : C(Y, X)) : Y → X) e.surjective
      (fun i ↦ (U.opens i : Set X)) s

/-- Helper for Theorem 63.7: pulling a finite open cover back through a
homeomorphism preserves membership in its nerve faces. -/
private lemma mem_comapHomeomorph_nerveFaces_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : CechFiniteOpenCover.{0, 0} X) (e : Y ≃ₜ X)
    (s : Finset U.Index) :
    s ∈ (U.comapHomeomorph e).nerveFaces ↔ s ∈ U.nerveFaces := by
  -- Normalize both nerve predicates, then transport their common-intersection test.
  calc
    s ∈ (U.comapHomeomorph e).nerveFaces ↔
        s.Nonempty ∧
          (⋂ i ∈ s, ((U.comapHomeomorph e).opens i : Set Y)).Nonempty :=
      CechFiniteOpenCover.mem_nerveFaces_iff _ _
    _ ↔ s.Nonempty ∧ (⋂ i ∈ s, (U.opens i : Set X)).Nonempty :=
      and_congr_right (fun _ ↦ iInter_comapHomeomorph_nonempty_iff U e s)
    _ ↔ s ∈ U.nerveFaces :=
      (CechFiniteOpenCover.mem_nerveFaces_iff U s).symm

/-- Helper for Theorem 63.7: the raw vector opposite a chosen simplex
hemisphere lies strictly in every other hemisphere before normalization. -/
private def simplexHemisphereWitnessVector (n : ℕ) :
    Fin (n + 2) → EuclideanSpace ℝ (Fin (n + 1)) :=
  Fin.lastCases
    (WithLp.toLp 2 (fun _ ↦ 1))
    (fun k ↦ WithLp.toLp 2
      (fun j ↦ if j = k then -((n + 1 : ℕ) : ℝ) else 1))

/-- Helper for Theorem 63.7: the raw opposite-hemisphere witness is nonzero. -/
private lemma simplexHemisphereWitnessVector_ne_zero
    (n : ℕ) (i : Fin (n + 2)) :
    simplexHemisphereWitnessVector n i ≠ 0 := by
  -- Inspect a coordinate which is visibly nonzero in each `lastCases` branch.
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · intro hZero
    have hCoordinate := congrArg
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x 0) hZero
    norm_num [simplexHemisphereWitnessVector] at hCoordinate
  · intro hZero
    have hCoordinate := congrArg
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x k) hZero
    have hCast : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
      positivity
    exact hCast (neg_eq_zero.mp (by
      simpa [simplexHemisphereWitnessVector] using hCoordinate))

/-- Helper for Theorem 63.7: normalization of the raw witness lies on the
unit sphere. -/
private lemma normalize_simplexHemisphereWitnessVector_mem_sphere
    (n : ℕ) (i : Fin (n + 2)) :
    NormedSpace.normalize (simplexHemisphereWitnessVector n i) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- A nonzero vector has unit norm after normalization.
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize
    (simplexHemisphereWitnessVector_ne_zero n i)

/-- Helper for Theorem 63.7: the normalized point opposite a chosen simplex
hemisphere. -/
private noncomputable def simplexHemisphereWitness
    (n : ℕ) (i : Fin (n + 2)) : StandardSphere n :=
  ⟨NormedSpace.normalize (simplexHemisphereWitnessVector n i),
    normalize_simplexHemisphereWitnessVector_mem_sphere n i⟩

/-- Helper for Theorem 63.7: the coordinates of a coordinate-opposite raw
witness sum to minus one. -/
private lemma sum_simplexHemisphereWitnessVector_castSucc
    (n : ℕ) (k : Fin (n + 1)) :
    ∑ j : Fin (n + 1), simplexHemisphereWitnessVector n k.castSucc j = -1 := by
  -- Split off the exceptional coordinate; all remaining coordinates equal one.
  classical
  simp only [simplexHemisphereWitnessVector, Fin.lastCases_castSucc,
    PiLp.toLp_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have hOffDiagonal (j : Fin (n + 1))
      (hj : j ∈ Finset.univ.erase k) : j ≠ k :=
    (Finset.mem_erase.mp hj).1
  rw [Finset.sum_congr rfl
    (fun j hj ↦ if_neg (hOffDiagonal j hj))]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, if_pos,
    Finset.card_erase_of_mem, Finset.mem_univ, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  ring

/-- Helper for Theorem 63.7: the normalized point opposite one hemisphere
belongs to every other simplex hemisphere. -/
private lemma simplexHemisphereWitness_mem
    (n : ℕ) (i j : Fin (n + 2)) (hji : j ≠ i) :
    simplexHemisphereWitness n i ∈ simplexHemisphereSet n j := by
  -- Normalization multiplies every raw coordinate by one positive scalar.
  refine Fin.lastCases
    (motive := fun i ↦ ∀ j, j ≠ i →
      simplexHemisphereWitness n i ∈ simplexHemisphereSet n j)
    ?_ (fun k ↦ ?_) i j hji
  · intro j
    refine Fin.lastCases
      (motive := fun j ↦ j ≠ Fin.last (n + 1) →
        simplexHemisphereWitness n (Fin.last (n + 1)) ∈
          simplexHemisphereSet n j)
      (fun hj ↦ (hj rfl).elim) (fun l _ ↦ ?_) j
    have hInvPositive :
        0 < ‖simplexHemisphereWitnessVector n (Fin.last (n + 1))‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr
        (simplexHemisphereWitnessVector_ne_zero n (Fin.last (n + 1))))
    simpa only [simplexHemisphereWitness, simplexHemisphereSet,
      Fin.lastCases_castSucc, Fin.lastCases_last, Set.mem_setOf_eq,
      NormedSpace.normalize,
      PiLp.smul_apply, smul_eq_mul, simplexHemisphereWitnessVector,
      PiLp.toLp_apply, mul_one] using hInvPositive
  · intro j
    refine Fin.lastCases
      (motive := fun j ↦ j ≠ k.castSucc →
        simplexHemisphereWitness n k.castSucc ∈ simplexHemisphereSet n j)
      (fun _ ↦ ?_) (fun l hj ↦ ?_) j
    · have hInvPositive :
          0 < ‖simplexHemisphereWitnessVector n k.castSucc‖⁻¹ :=
        inv_pos.mpr (norm_pos_iff.mpr
          (simplexHemisphereWitnessVector_ne_zero n k.castSucc))
      have hSum :
          ∑ l : Fin (n + 1),
              (simplexHemisphereWitness n k.castSucc :
                EuclideanSpace ℝ (Fin (n + 1))) l =
            ‖simplexHemisphereWitnessVector n k.castSucc‖⁻¹ * (-1) := by
        simp only [simplexHemisphereWitness, NormedSpace.normalize,
          PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum,
          sum_simplexHemisphereWitnessVector_castSucc]
      simpa only [simplexHemisphereSet, Fin.lastCases_last, Set.mem_setOf_eq,
        hSum, mul_neg, mul_one, neg_lt_zero] using hInvPositive
    · have hlk : l ≠ k := by
        intro hlk
        subst l
        exact hj rfl
      have hInvPositive :
          0 < ‖simplexHemisphereWitnessVector n k.castSucc‖⁻¹ :=
        inv_pos.mpr (norm_pos_iff.mpr
          (simplexHemisphereWitnessVector_ne_zero n k.castSucc))
      simpa only [simplexHemisphereWitness, simplexHemisphereSet,
          Fin.lastCases_castSucc, Set.mem_setOf_eq, NormedSpace.normalize,
          PiLp.smul_apply, smul_eq_mul, simplexHemisphereWitnessVector,
          PiLp.toLp_apply, if_neg hlk, mul_one] using hInvPositive

/-- Helper for Theorem 63.7: a family of simplex hemispheres has nonempty
intersection exactly when it omits at least one hemisphere. -/
private lemma iInter_simplexHemisphereSet_nonempty_iff
    (n : ℕ) (s : Finset (Fin (n + 2))) :
    (⋂ i ∈ s, simplexHemisphereSet n i).Nonempty ↔
      s ≠ Finset.univ := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    -- Membership in all coordinate hemispheres makes the coordinate sum
    -- positive, contradicting membership in the final negative-sum hemisphere.
    have hCoordinate (j : Fin (n + 1)) :
        0 < (x : EuclideanSpace ℝ (Fin (n + 1))) j := by
      have hxj := Set.mem_iInter.mp (Set.mem_iInter.mp hx j.castSucc)
        (Finset.mem_univ j.castSucc)
      simpa only [simplexHemisphereSet, Fin.lastCases_castSucc,
        Set.mem_setOf_eq] using hxj
    have hSumPositive :
        0 < ∑ j : Fin (n + 1),
          (x : EuclideanSpace ℝ (Fin (n + 1))) j :=
      Finset.sum_pos (fun j _ ↦ hCoordinate j) (Finset.univ_nonempty)
    have hSumNegative :=
      Set.mem_iInter.mp
        (Set.mem_iInter.mp hx (Fin.last (n + 1)))
          (Finset.mem_univ (Fin.last (n + 1)))
    have hSumNegative' :
        ∑ j : Fin (n + 1),
            (x : EuclideanSpace ℝ (Fin (n + 1))) j < 0 := by
      simpa only [simplexHemisphereSet, Fin.lastCases_last,
        Set.mem_setOf_eq] using hSumNegative
    exact (lt_asymm hSumPositive hSumNegative')
  · intro hs
    -- Choose an omitted hemisphere and use its opposite normalized point.
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 2), i ∉ s := by
      by_contra hOmitted
      apply hs
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact hOmitted ⟨i, hi⟩
    refine ⟨simplexHemisphereWitness n i, ?_⟩
    simp only [Set.mem_iInter]
    intro j hjs
    exact simplexHemisphereWitness_mem n i j (fun hji ↦ hi (hji ▸ hjs))

/-- Helper for Theorem 63.7: the nerve of the simplex-hemisphere cover is the
poset of nonempty proper subsets of its vertex set. -/
private lemma mem_simplexHemisphereCover_nerveFaces_iff
    (n : ℕ) (s : Finset (Fin (n + 2))) :
    s ∈ (simplexHemisphereCover n).nerveFaces ↔
      s.Nonempty ∧ s ≠ Finset.univ := by
  -- Combine the general nerve computation with the explicit intersection test.
  have hNerve :=
    CechFiniteOpenCover.mem_nerveFaces_iff (simplexHemisphereCover n) s
  simpa only [simplexHemisphereCover] using
    hNerve.trans
      (and_congr_right (fun _ ↦ iInter_simplexHemisphereSet_nonempty_iff n s))

/-- Helper for Theorem 63.7: transport the explicit simplex-hemisphere cover
to an embedded copy of the standard sphere. -/
private noncomputable def embeddedSphereSimplexHemisphereCover
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    CechFiniteOpenCover.{0, 0} C :=
  (simplexHemisphereCover n).comapHomeomorph (Classical.choice hC)

-- Local instance justification (opaque cover index): the transported cover's
-- index is definitionally `Fin (n + 2)`, but the private definition is opaque
-- at later declarations that form refinement maps.
/-- Helper for Theorem 63.7: the embedded hemisphere cover has decidable
equality on its finite index type. -/
private noncomputable instance embeddedSphereSimplexHemisphereCoverIndexDecidableEq
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    DecidableEq (embeddedSphereSimplexHemisphereCover n C hC).Index :=
  Classical.decEq _

/-- Helper for Theorem 63.7: the transported simplex-hemisphere cover has the
same nonempty proper finite subsets as its nerve faces. -/
private lemma mem_embeddedSphereSimplexHemisphereCover_nerveFaces_iff
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n))
    (s : Finset (Fin (n + 2))) :
    s ∈ (embeddedSphereSimplexHemisphereCover n C hC).nerveFaces ↔
      s.Nonempty ∧ s ≠ Finset.univ := by
  -- First remove the homeomorphic pullback, then use the explicit face lattice.
  calc
    s ∈ (embeddedSphereSimplexHemisphereCover n C hC).nerveFaces ↔
        s ∈ (simplexHemisphereCover n).nerveFaces := by
      unfold embeddedSphereSimplexHemisphereCover
      exact mem_comapHomeomorph_nerveFaces_iff
        (simplexHemisphereCover n) (Classical.choice hC) s
    _ ↔ s.Nonempty ∧ s ≠ Finset.univ :=
      mem_simplexHemisphereCover_nerveFaces_iff n s

-- Route correction: the former adapted-stage wrapper duplicated the
-- finite-duality interface and asked for target homology itself to vanish.  The
-- selected geometric stage now returns the existing `FiniteAlexanderStage`, a
-- maximal-flag lift, and connectedness of its outside graph.
/-- Helper for Theorem 63.7: a preconnected complement supplies a finite
Alexander stage carrying the lifted maximal-flag class. -/
private lemma exists_complementAdaptedFiniteAlexanderStage
    (n : ℕ) (hn : 2 ≤ n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) (hCompact : IsCompact C)
    (hPreconnected : IsPreconnected Cᶜ) :
    ∃ (A : FiniteAlexanderStage (TopCat.of C)
          (TopCat.of (Cᶜ : Set (StandardSphere (n + 1)))) n)
        (f : CechFiniteOpenCover.RefinementMap
          (embeddedSphereSimplexHemisphereCover n C hC) A.cover)
        (sourceClass : CechFiniteOpenCover.faceNerveHomology
          (embeddedSphereSimplexHemisphereCover n C hC) n)
        (targetClass : CechFiniteOpenCover.faceNerveHomology A.cover n),
      sourceClass ≠ 0 ∧
        f.faceNerveHomologyMap n targetClass = sourceClass ∧
          Subsingleton A.graph.ConnectedComponent := by
  -- TODO: sum maximal flags in the normalized proper-face nerve, prove its
  -- coefficient nonzero, and choose one relative-star subdivision subordinate
  -- both to the hemisphere cover and finitely many complement paths.
  sorry

end InvarianceOfDomainSupport

/-- Helper for Theorem 63.7: in dimensions at least two, mod-two Alexander
duality makes reduced `H₀` of the complement of an embedded sphere nonzero. -/
private lemma not_isZero_reducedHomologyZeroModTwo_sphereComplement_of_two_le
    (n : ℕ) (hn : 2 ≤ n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ¬ IsZero
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
        (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) := by
  -- Route correction: under vanishing reduced `H₀`, the complement is
  -- preconnected. One adapted stage then maps a nonzero sphere class
  -- from a target whose homology is forced to be zero.
  -- Local instance justification (ambient topology): the reduced-`H₀` bridge
  -- needs local path-connectedness furnished by the sphere's manifold charts.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hComplementOpen : IsOpen Cᶜ :=
    (isClosed_of_homeomorphic_standardSphere n C hC).isOpen_compl
  intro hHomologyZero
  have hComplementPreconnected : IsPreconnected Cᶜ :=
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Cᶜ hComplementOpen).mpr hHomologyZero
  -- The selected stage carries a lifted nonzero sphere class while its connected
  -- outside graph forces the same finite cohomology object to vanish.
  obtain ⟨A, f, sourceClass, targetClass, hSourceClass,
      hTargetClass, hComponents⟩ :=
    InvarianceOfDomainSupport.exists_complementAdaptedFiniteAlexanderStage
      n hn C hC (isCompact_of_homeomorphic_standardSphere n C hC)
      hComplementPreconnected
  have hStageZero :
      IsZero (InvarianceOfDomainSupport.liftedFaceNerveCohomology A.cover n) :=
    InvarianceOfDomainSupport.FiniteAlexanderStage.isZero_coverCohomology_of_subsingleton_components
      A hComponents
  have hStageNonzero :
      ¬ IsZero
        (InvarianceOfDomainSupport.liftedFaceNerveCohomology A.cover n) :=
    InvarianceOfDomainSupport.not_isZero_liftedFaceNerveCohomology_of_homology_lift
      f sourceClass hSourceClass targetClass hTargetClass
  exact hStageNonzero hStageZero

/-- Helper for Theorem 63.7: in dimensions at least two, nonvanishing of reduced
mod-two `H₀` forces nonvanishing of reduced integral `H₀`. -/
private lemma not_isZero_reducedSingularHomologyZero_sphereComplement_of_two_le
    (n : ℕ) (hn : 2 ≤ n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ¬ IsZero
      (AlgebraicTopology.ReducedSingularHomologyZero
        (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) := by
  -- Both coefficient systems vanish precisely when the open complement is
  -- preconnected, so integral vanishing would contradict mod-two duality.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hComplementOpen : IsOpen Cᶜ :=
    (isClosed_of_homeomorphic_standardSphere n C hC).isOpen_compl
  intro hIntegralZero
  have hComplementPreconnected : IsPreconnected Cᶜ :=
    (isPreconnected_iff_isZero_reducedSingularHomologyZero
      Cᶜ hComplementOpen).mpr hIntegralZero
  have hModTwoZero :
      IsZero
        (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
          (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) :=
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Cᶜ hComplementOpen).mp hComplementPreconnected
  exact not_isZero_reducedHomologyZeroModTwo_sphereComplement_of_two_le
    n hn C hC hModTwoZero

-- Route correction: the preceding Čech route left every positive dimension open.
-- The Jordan curve theorem now discharges dimension one, so only the genuinely
-- higher-dimensional Alexander-duality comparison remains.
/-- Helper for Theorem 63.7: positive-dimensional Alexander duality makes reduced
integral `H₀` of the complement of an embedded sphere nonzero. -/
private lemma not_isZero_reducedSingularHomologyZero_positiveSphereComplement
    (n : ℕ) (hn : 0 < n) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ¬ IsZero
      (AlgebraicTopology.ReducedSingularHomologyZero
        (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) := by
  rcases eq_or_ne n 1 with rfl | hnOne
  · -- The earlier Jordan curve theorem completely settles the one-dimensional case.
    letI : Topology.IsSimpleClosedCurve C :=
      isSimpleClosedCurve_of_homeomorphic_standardSphereOne C hC
    letI : LocallyPathConnectedSpace (StandardSphere 2) :=
      ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
    have hComplementOpen : IsOpen Cᶜ :=
      (isClosed_of_homeomorphic_standardSphere 1 C hC).isOpen_compl
    intro hIntegralZero
    have hComplementPreconnected : IsPreconnected Cᶜ :=
      (isPreconnected_iff_isZero_reducedSingularHomologyZero
        Cᶜ hComplementOpen).mpr hIntegralZero
    letI : PreconnectedSpace (Cᶜ : Set (StandardSphere 2)) :=
      isPreconnected_iff_preconnectedSpace.mp hComplementPreconnected
    have hAtMostOne :
        Cardinal.mk (ConnectedComponents (Cᶜ : Set (StandardSphere 2))) ≤ 1 :=
      Cardinal.le_one_iff_subsingleton.mpr inferInstance
    have hExactlyTwo :=
      Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
    rw [hExactlyTwo] at hAtMostOne
    norm_num at hAtMostOne
  · -- Only dimensions at least two still require the missing duality comparison.
    have hnTwo : 2 ≤ n := by
      omega
    exact not_isZero_reducedSingularHomologyZero_sphereComplement_of_two_le
      n hnTwo C hC

-- Route correction: the exact linear equivalence used previously bundled compact-subset
-- duality, homeomorphism invariance, and the sphere computation, while separation needs
-- only nonvanishing of the complement invariant.
/-- Helper for Theorem 63.7: reduced mod-two `H₀` of the complement of an
embedded standard sphere is nonzero. -/
private lemma not_isZero_reducedHomologyZeroModTwo_sphereComplement
    (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    ¬ IsZero
      (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
        (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) := by
  -- Both coefficient systems detect preconnectedness of the open complement.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hComplementOpen : IsOpen Cᶜ :=
    (isClosed_of_homeomorphic_standardSphere n C hC).isOpen_compl
  rcases n.eq_zero_or_pos with rfl | hn
  · -- In degree zero, the embedded `S⁰` is a pair of distinct points in a circle.
    obtain ⟨e⟩ := hC
    obtain ⟨x⟩ : Nonempty (StandardSphere 0) :=
      (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
    let a : C := e.symm x
    let b : C := e.symm (-x)
    have hab : a ≠ b := by
      intro hab
      apply ne_neg_of_mem_unit_sphere ℝ x
      simpa only [a, b, e.apply_symm_apply] using congrArg e hab
    have hCpair : C = {(a : StandardSphere 1), (b : StandardSphere 1)} := by
      ext z
      constructor
      · intro hz
        let zC : C := ⟨z, hz⟩
        rcases standardSphereZero_eq_or_eq_neg x (e zC) with heq | heq
        · have hza : zC = a := e.injective (by simpa only [a, e.apply_symm_apply] using heq)
          exact Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val hza))
        · have hzb : zC = b := e.injective (by simpa only [b, e.apply_symm_apply] using heq)
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton_iff.mpr (congrArg Subtype.val hzb)))
      · intro hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact a.property
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact b.property
    have habVal : (a : StandardSphere 1) ≠ (b : StandardSphere 1) :=
      fun h ↦ hab (Subtype.ext h)
    have hNotPreconnected : ¬ IsPreconnected Cᶜ := by
      rw [hCpair]
      exact not_isPreconnected_standardSphereOne_compl_pair _ _ habVal
    intro hZero
    apply hNotPreconnected
    exact
      (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
        Cᶜ hComplementOpen).mpr hZero
  · -- In positive dimensions, singular Alexander duality gives integral nonvanishing;
    -- the two reduced-`H₀` bridges transfer it to mod-two coefficients.
    intro hModTwoZero
    have hPreconnected : IsPreconnected Cᶜ :=
      (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
        Cᶜ hComplementOpen).mpr hModTwoZero
    have hIntegralZero :
        IsZero
          (AlgebraicTopology.ReducedSingularHomologyZero
            (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) :=
      (isPreconnected_iff_isZero_reducedSingularHomologyZero
        Cᶜ hComplementOpen).mp hPreconnected
    exact not_isZero_reducedSingularHomologyZero_positiveSphereComplement
      n hn C hC hIntegralZero

/-- Theorem 63.7: A subspace of the standard `(n + 1)`-sphere homeomorphic to
the standard `n`-sphere separates the standard `(n + 1)`-sphere. -/
theorem jordanBrouwer_separates (n : ℕ) (C : Set (StandardSphere (n + 1)))
    (hC : Nonempty (C ≃ₜ StandardSphere n)) :
    C.Separates := by
  -- The closed embedded sphere has an open complement in a locally path-connected sphere.
  letI : LocallyPathConnectedSpace (StandardSphere (n + 1)) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) _
  have hComplementOpen : IsOpen Cᶜ :=
    (isClosed_of_homeomorphic_standardSphere n C hC).isOpen_compl
  rw [Set.separates_iff]
  intro hComplementPreconnected
  -- Preconnectedness would annihilate reduced `H₀`, contradicting duality.
  have hComplementIsPreconnected : IsPreconnected Cᶜ :=
    isPreconnected_iff_preconnectedSpace.mpr hComplementPreconnected
  have hHomologyZero :
      IsZero
        (InvarianceOfDomainSupport.reducedHomologyZeroModTwo
          (TopCat.of (Cᶜ : Set (StandardSphere (n + 1))))) :=
    (InvarianceOfDomainSupport.isPreconnected_iff_isZero_reducedHomologyZeroModTwo
      Cᶜ hComplementOpen).mp hComplementIsPreconnected
  exact not_isZero_reducedHomologyZeroModTwo_sphereComplement n C hC hHomologyZero
