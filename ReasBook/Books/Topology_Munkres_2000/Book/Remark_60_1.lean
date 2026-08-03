module

public import Topology_Munkres_2000.Book.Remark_60_1.AntipodalCover
public import Topology_Munkres_2000.Book.Remark_60_1.AntipodalParity
public import Topology_Munkres_2000.Book.Remark_60_1.CoverTransitionTriangle
public import Topology_Munkres_2000.Book.Remark_60_1.CoefficientBockstein
public import Topology_Munkres_2000.Book.Remark_60_1.DegreeOneCharacters
public import Topology_Munkres_2000.Book.Remark_60_1.IntegralSingularCohomology
public import Topology_Munkres_2000.Book.Remark_60_1.RelativeSingularHomology
public import Topology_Munkres_2000.Book.Remark_60_1.ReducedHomologyZero
public import Topology_Munkres_2000.Book.Remark_60_1.ProjectivePlaneCohomology
public import Topology_Munkres_2000.Book.Remark_60_1.SmallSingularChains
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Homotopy.LocallyContractible

public section

open scoped DirectSum

namespace stdSimplex

/-- Helper for Remark 60.1: the coordinates of the affine extension of a finite
family of vertices. -/
noncomputable def affineCoordinates
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) : J → ℝ :=
  fun j ↦ ∑ i, x i * v i j

/-- Helper for Remark 60.1: affine combinations of simplex vertices remain in the
target standard simplex. -/
lemma affineCoordinates_mem_stdSimplex
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) :
    affineCoordinates v x ∈ stdSimplex ℝ J := by
  -- Each coordinate is a sum of products of nonnegative simplex coordinates.
  constructor
  · intro j
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) j)
  · -- Interchange the finite sums and use that both the weights and vertices sum to one.
    simp only [affineCoordinates]
    calc
      ∑ j, ∑ i, x i * v i j = ∑ i, ∑ j, x i * v i j := Finset.sum_comm
      _ = ∑ i, x i * ∑ j, v i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, x i := by
        simp only [stdSimplex.sum_eq_one, mul_one]
      _ = 1 := stdSimplex.sum_eq_one x

/-- Helper for Remark 60.1: the coordinate function of a finite affine extension
is continuous. -/
lemma continuous_affineCoordinates
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) :
    Continuous (affineCoordinates v) := by
  -- Continuity is checked coordinatewise, where the formula is a finite sum.
  apply continuous_pi
  intro j
  exact continuous_finsetSum Finset.univ fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- Helper for Remark 60.1: the affine extension of a finite family of vertices
is a continuous map between standard simplices. -/
lemma continuous_affineMapOfVertices
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) :
    Continuous (fun x ↦
      (⟨affineCoordinates v x, affineCoordinates_mem_stdSimplex v x⟩ :
        stdSimplex ℝ J)) := by
  -- Bundle the continuous coordinate function with its simplex-membership proof.
  exact Continuous.subtype_mk (continuous_affineCoordinates v) _

/-- Helper for Remark 60.1: continuously extend a finite vertex family by affine
combinations over the standard simplex. -/
noncomputable def affineMapOfVertices
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) : C(stdSimplex ℝ I, stdSimplex ℝ J) :=
  ⟨fun x ↦ ⟨affineCoordinates v x, affineCoordinates_mem_stdSimplex v x⟩,
    continuous_affineMapOfVertices v⟩

/-- Helper for Remark 60.1: the affine extension has the expected coordinate
formula. -/
lemma affineMapOfVertices_apply
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) (j : J) :
    affineMapOfVertices v x j = ∑ i, x i * v i j := by
  -- Unfold only the stable coordinate interface of the affine extension.
  rfl

/-- Helper for Remark 60.1: the affine extension recovers the prescribed value at
each vertex. -/
lemma affineMapOfVertices_vertex
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (v : I → stdSimplex ℝ J) (i : I) :
    affineMapOfVertices v (stdSimplex.vertex i) = v i := by
  -- At a vertex all weights vanish except the selected coordinate.
  ext j
  simp [affineMapOfVertices_apply, Pi.single_apply]

/-- Helper for Remark 60.1: precomposing an affine extension with a standard
simplex map pulls its vertex family back along the index map. -/
lemma affineMapOfVertices_map
    {K I J : Type*} [Fintype K] [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (f : K → I) (x : stdSimplex ℝ K) :
    affineMapOfVertices v (stdSimplex.map f x) =
      affineMapOfVertices (v ∘ f) x := by
  -- Compare coordinates, then flatten the sum over the fibers of `f`.
  classical
  ext j
  simp only [affineMapOfVertices_apply, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply, Function.comp_apply]
  calc
    ∑ i, (∑ k ∈ Finset.univ.filter (fun k ↦ f k = i), x k) * v i j =
        ∑ i, ∑ k ∈ Finset.univ.filter (fun k ↦ f k = i), x k * v i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ k ∈ Finset.univ.filter (fun k ↦ f k = i), x k * v (f k) j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = ∑ k, x k * v (f k) j :=
      Finset.sum_fiberwise Finset.univ f (fun k ↦ x k * v (f k) j)

/-- Helper for Remark 60.1: an index map induces a continuous map between its
standard simplices. -/
noncomputable def mapContinuous
    {K I : Type*} [Fintype K] [Fintype I]
    (f : K → I) : C(stdSimplex ℝ K, stdSimplex ℝ I) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

/-- Helper for Remark 60.1: the bundled affine extension commutes with
precomposition by a standard-simplex index map. -/
lemma affineMapOfVertices_comp_mapContinuous
    {K I J : Type*} [Fintype K] [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (f : K → I) :
    (affineMapOfVertices v).comp (mapContinuous f) =
      affineMapOfVertices (v ∘ f) := by
  -- Extensionality reduces the bundled identity to the pointwise fiber-sum formula.
  apply ContinuousMap.ext
  intro x
  exact affineMapOfVertices_map v f x

/-- Helper for Remark 60.1: composing finite affine simplex maps amounts to
applying the outer affine map to the inner vertex family. -/
lemma affineMapOfVertices_comp_affineMapOfVertices
    {K I J : Type*} [Fintype K] [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (w : K → stdSimplex ℝ I) :
    (affineMapOfVertices v).comp (affineMapOfVertices w) =
      affineMapOfVertices (fun k ↦ affineMapOfVertices v (w k)) := by
  -- Compare coordinates and interchange the two finite affine sums.
  apply ContinuousMap.ext
  intro x
  ext j
  simp only [ContinuousMap.comp_apply, affineMapOfVertices_apply,
    Finset.sum_mul, Finset.mul_sum]
  calc
    ∑ i, ∑ k, x k * w k i * v i j =
        ∑ k, ∑ i, x k * w k i * v i j := Finset.sum_comm
    _ = ∑ k, ∑ i, x k * (w k i * v i j) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Helper for Remark 60.1: affine extension of the standard vertex family is
the identity map of the standard simplex. -/
lemma affineMapOfVertices_stdSimplex_vertex
    {I : Type*} [Fintype I] [DecidableEq I] :
    affineMapOfVertices (stdSimplex.vertex : I → stdSimplex ℝ I) =
      ContinuousMap.id _ := by
  -- The standard basis expansion reconstructs every simplex coordinate.
  apply ContinuousMap.ext
  intro x
  ext j
  simp [affineMapOfVertices_apply, Pi.single_apply]

/-- Helper for Remark 60.1: an affine image point lies in the convex hull of
the prescribed finite vertex family. -/
lemma coe_affineMapOfVertices_mem_convexHull
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) :
    ((affineMapOfVertices v x : stdSimplex ℝ J) : J → ℝ) ∈
      convexHull ℝ (Set.range fun i ↦ ((v i : stdSimplex ℝ J) : J → ℝ)) := by
  -- Use the simplex coordinates as the nonnegative affine-combination weights.
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨Finset.univ, fun i ↦ x i, ?_, ?_, ?_⟩
  · intro i _
    exact stdSimplex.zero_le x i
  · exact stdSimplex.sum_eq_one x
  · rw [Finset.affineCombination_eq_linear_combination _ _ _
        (stdSimplex.sum_eq_one x)]
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (affineMapOfVertices_apply v x j).symm

/-- Helper for Remark 60.1: taking all affine combinations of a finite vertex
family does not change its metric diameter. -/
lemma diam_range_affineMapOfVertices
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) :
    Metric.diam (Set.range (affineMapOfVertices v)) =
      Metric.diam (Set.range v) := by
  classical
  let coe : stdSimplex ℝ J → (J → ℝ) := fun x ↦ x
  let vertices : Set (J → ℝ) := Set.range (fun i ↦ coe (v i))
  let affineRange : Set (J → ℝ) :=
    Set.range (fun x ↦ coe (affineMapOfVertices v x))
  have haffine : affineRange ⊆ convexHull ℝ vertices := by
    -- Invoke the affine-combination membership interface at each image point.
    rintro _ ⟨x, rfl⟩
    exact coe_affineMapOfVertices_mem_convexHull v x
  have hvertices : vertices ⊆ affineRange := by
    -- Conversely, every prescribed vertex is attained at a standard vertex.
    rintro _ ⟨i, rfl⟩
    refine ⟨stdSimplex.vertex i, ?_⟩
    exact congrArg coe (affineMapOfVertices_vertex v i)
  have hverticesBounded : Bornology.IsBounded vertices :=
    (Set.finite_range fun i ↦ coe (v i)).isBounded
  have haffineBounded : Bornology.IsBounded affineRange :=
    (isBounded_convexHull.mpr hverticesBounded).subset haffine
  have hambient : Metric.diam affineRange = Metric.diam vertices := by
    -- Sandwich the two diameters, using that convex hull preserves diameter.
    apply le_antisymm
    · exact (Metric.diam_mono haffine (isBounded_convexHull.mpr hverticesBounded)).trans_eq
        (convexHull_diam vertices)
    · exact Metric.diam_mono hvertices haffineBounded
  -- Coercion from a metric subtype is an isometry, so the ambient equality descends.
  calc
    Metric.diam (Set.range (affineMapOfVertices v)) =
        Metric.diam (coe '' Set.range (affineMapOfVertices v)) :=
      (isometry_subtype_coe.diam_image _).symm
    _ = Metric.diam affineRange := by
      congr 1
      exact (Set.range_comp' coe (affineMapOfVertices v)).symm
    _ = Metric.diam vertices := hambient
    _ = Metric.diam (coe '' Set.range v) := by
      congr 1
      exact Set.range_comp' coe v
    _ = Metric.diam (Set.range v) := isometry_subtype_coe.diam_image _

/-- Helper for Remark 60.1: if the prescribed vertices have diameter below
`δ`, the entire affine image lies in the `δ`-ball about any one of its points. -/
lemma range_affineMapOfVertices_subset_ball
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x₀ : stdSimplex ℝ I) {δ : ℝ}
    (hdiam : Metric.diam (Set.range v) < δ) :
    Set.range (affineMapOfVertices v) ⊆
      Metric.ball (affineMapOfVertices v x₀) δ := by
  have haffineBounded :
      Bornology.IsBounded (Set.range (affineMapOfVertices v)) := by
    -- The affine image of the compact standard simplex is bounded.
    simpa only [Set.image_univ] using
      (isCompact_univ.image (affineMapOfVertices v).continuous).isBounded
  intro _ hy
  apply Metric.mem_ball.mpr
  -- Compare two affine-image points through the normalized image diameter.
  calc
    dist _ (affineMapOfVertices v x₀) ≤
        Metric.diam (Set.range (affineMapOfVertices v)) :=
      Metric.dist_le_diam_of_mem haffineBounded hy (Set.mem_range_self x₀)
    _ = Metric.diam (Set.range v) := diam_range_affineMapOfVertices v
    _ < δ := hdiam

/-- Helper for Remark 60.1: every finite family of points in a standard simplex
has diameter at most one. -/
lemma diam_range_le_one
    {I J : Type*} [Fintype J]
    (v : I → stdSimplex ℝ J) : Metric.diam (Set.range v) ≤ 1 := by
  -- Bound pairwise distances in the family by the ambient simplex diameter.
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  simpa only [Subtype.dist_eq] using
    (Metric.dist_le_diam_of_mem (bounded_stdSimplex J) (v i).property (v j).property).trans
      (diam_stdSimplex_le (ι := J))

end stdSimplex

namespace AlgebraicTopology.BarycentricSubdivision

open CategoryTheory Simplicial

/-- Helper for Remark 60.1: the identity map of the standard topological simplex,
regarded as its universal singular simplex. -/
noncomputable def identitySingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).symm
    (ContinuousMap.id _)

/-- Helper for Remark 60.1: the universal singular simplex represents the identity
continuous map. -/
lemma toSSetObjEquiv_identitySingularSimplex (n : ℕ) :
    (TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
        (Opposite.op (SimplexCategory.mk n)) (identitySingularSimplex n) =
      ContinuousMap.id _ := by
  -- Unpack the universal simplex through the defining equivalence.
  exact Equiv.apply_symm_apply _ _

/-- Helper for Remark 60.1: a singular simplex determines its represented
continuous map from the standard topological simplex. -/
noncomputable def singularMap (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ X :=
  TopCat.ofHom (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ)

/-- Helper for Remark 60.1: the underlying continuous map of a represented
singular simplex is the value of the singular-simplex equivalence. -/
lemma singularMap_hom (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (singularMap X n σ).hom =
      X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ := by
  -- Expose the projection once, so later composition proofs avoid unfolding the wrapper.
  rfl

/-- Helper for Remark 60.1: pushing the universal simplex along its represented
map recovers the original singular simplex. -/
lemma map_identitySingularSimplex (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.map (singularMap X n σ)).app
        (Opposite.op (SimplexCategory.mk n)) (identitySingularSimplex n) = σ := by
  -- Compare continuous representatives; postcomposition with the identity does nothing.
  apply (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))).injective
  rw [toSSetObjEquiv_map, toSSetObjEquiv_identitySingularSimplex]
  rfl

/-- Helper for Remark 60.1: representing a pushed-forward singular simplex
amounts to postcomposing its represented map. -/
lemma singularMap_map {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    singularMap Y n
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ) =
      singularMap X n σ ≫ f := by
  -- Test the two maps on the universal simplex and read the result through the equivalence.
  have hsimplex :
      (TopCat.toSSet.map
        (singularMap Y n
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ))).app
          (Opposite.op (SimplexCategory.mk n)) (identitySingularSimplex n) =
        (TopCat.toSSet.map (singularMap X n σ ≫ f)).app
          (Opposite.op (SimplexCategory.mk n)) (identitySingularSimplex n) := by
    rw [map_identitySingularSimplex, Functor.map_comp, NatTrans.comp_app,
      CategoryTheory.comp_apply, map_identitySingularSimplex]
  apply TopCat.hom_ext
  have hrepresented := congrArg
    (Y.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))) hsimplex
  rw [toSSetObjEquiv_map, toSSetObjEquiv_map,
    toSSetObjEquiv_identitySingularSimplex] at hrepresented
  simpa only [ContinuousMap.comp_id] using hrepresented

/-- Helper for Remark 60.1: the integral fundamental chain of a standard simplex
is its universal singular-simplex generator. -/
noncomputable def integralFundamentalChain (n : ℕ) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  (TopCat.toSSet.obj
    (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
      (identitySingularSimplex n)

/-- Helper for Remark 60.1: the boundary of the universal fundamental chain is
the alternating sum of its face generators. -/
lemma integralFundamentalChain_boundary (n : ℕ) :
    integralFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
            ((TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i
                (identitySingularSimplex (n + 1))) := by
  -- Apply the standard simplicial boundary formula to the universal generator.
  exact SSet.ιChainComplex_d
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2)))))
    (ModuleCat.of ℤ ℤ) (identitySingularSimplex (n + 1))

/-- Helper for Remark 60.1: every singular-simplex generator is the pushforward
of the universal fundamental chain. -/
lemma integralFundamentalChain_naturality (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    integralFundamentalChain n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularMap X n σ))
          (ModuleCat.of ℤ ℤ)).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  -- Naturality of generators reduces the claim to the universal-simplex computation.
  rw [integralFundamentalChain, SSet.ι_chainComplexMap_f,
    map_identitySingularSimplex]

/-- Helper for Remark 60.1: the `k`-th ordered barycentric vertex is the
barycenter of the first `k + 1` permuted vertices. -/
noncomputable def vertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : stdSimplex ℝ (Fin (n + 1)) :=
  stdSimplex.map
    (fun j : Fin (k.val + 1) ↦
      π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) j))
    (stdSimplex.barycenter : stdSimplex ℝ (Fin (k.val + 1)))

/-- Helper for Remark 60.1: the barycentric simplex indexed by a permutation is
the affine extension of its ordered barycentric vertices. -/
noncomputable def continuousMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  stdSimplex.affineMapOfVertices (vertex n π)

/-- Helper for Remark 60.1: the barycentric affine simplex has the prescribed
value on each standard vertex. -/
lemma continuousMap_vertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    continuousMap n π (stdSimplex.vertex k) = vertex n π k := by
  -- The previously proved affine-extension computation applies to this vertex family.
  classical
  exact stdSimplex.affineMapOfVertices_vertex (vertex n π) k

/-- Helper for Remark 60.1: a permutation determines the singular simplex
spanned by its chain of successive face barycenters. -/
noncomputable def singularSimplex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).symm (continuousMap n π)

/-- Helper for Remark 60.1: the universal barycentric subdivision chain is the
signed sum of its permutation-indexed simplices. -/
noncomputable def standardChain (n : ℕ) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (singularSimplex n π)

/-- Helper for Remark 60.1: subdivision of one singular simplex is obtained by
pushing the universal barycentric chain along its represented map. -/
noncomputable def simplexChain (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  standardChain n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularMap X n σ))
      (ModuleCat.of ℤ ℤ)).f n

/-- Helper for Remark 60.1: simplexwise subdivision expands as the signed sum
of its pushed-forward barycentric subsimplices. -/
lemma simplexChain_eq_sum (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    simplexChain X n σ =
      ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.map (singularMap X n σ)).app
            (Opposite.op (SimplexCategory.mk n)) (singularSimplex n π)) := by
  -- Distribute pushforward over the signed sum and compute it on each generator.
  unfold simplexChain standardChain
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]

/-- Helper for Remark 60.1: each barycentric subsimplex remains inside the
image of the original singular simplex. -/
lemma range_barycentricSubsimplex_subset_range (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (π : Equiv.Perm (Fin (n + 1))) :
    Set.range
        (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))
          ((TopCat.toSSet.map (singularMap X n σ)).app
            (Opposite.op (SimplexCategory.mk n)) (singularSimplex n π))) ⊆
      Set.range (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ) := by
  -- The representative factors through the original simplex, so its range is smaller.
  rw [toSSetObjEquiv_map]
  rintro y ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- Helper for Remark 60.1: simplexwise barycentric subdivision is natural under
continuous maps of ambient spaces. -/
lemma simplexChain_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    simplexChain X n σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n =
      simplexChain Y n
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ) := by
  -- Expand both sides and push each generator through the ambient map.
  rw [simplexChain_eq_sum, simplexChain_eq_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f, singularMap_map]
  simp only [Functor.map_comp, NatTrans.comp_app, CategoryTheory.comp_apply]

/-- Helper for Remark 60.1: a barycentric vertex has its constant nonzero
coordinate exactly on the corresponding permutation prefix. -/
private lemma vertex_apply (n : ℕ) (k : Fin (n + 2))
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    vertex (n + 1) π k j =
      if j ∈ Set.range (fun l : Fin (k.val + 1) ↦
          π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l))
        then ((k.val + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  -- Expand the simplex map as the sum over the fiber of the chosen coordinate.
  unfold vertex
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  split_ifs with hj
  · obtain ⟨l, hl⟩ := hj
    have hfilter : Finset.univ.filter (fun l' : Fin (k.val + 1) ↦
        π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l') = j) = {l} := by
      ext l'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hl'
        exact Fin.castLE_injective _ (π.injective (hl'.trans hl.symm))
      · rintro rfl
        exact hl
    -- Injectivity of the prefix enumeration leaves one barycenter coordinate.
    rw [hfilter, Finset.sum_singleton]
    unfold stdSimplex.barycenter
    simp only [Fintype.card_fin]
    rfl
  · have hfilter : Finset.univ.filter (fun l : Fin (k.val + 1) ↦
        π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l) = j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact hj ⟨l, hl⟩
    -- Outside the prefix the relevant fiber, hence its coordinate sum, is empty.
    rw [hfilter, Finset.sum_empty]

/-- Helper for Remark 60.1: swapping the two positions adjacent to a retained
face index preserves every prefix that occurs on that face. -/
private lemma adjacentSwap_le_succAbove (n : ℕ) (i k : Fin (n + 1))
    (x : Fin (n + 2)) (hx : x.val ≤ (i.castSucc.succAbove k).val) :
    (Equiv.swap i.castSucc i.succ x).val ≤ (i.castSucc.succAbove k).val := by
  by_cases hki : k < i
  · have hface : i.castSucc.succAbove k = k.castSucc :=
      Fin.succAbove_castSucc_of_lt i k hki
    have hfaceVal : (i.castSucc.succAbove k).val = k.val :=
      congrArg Fin.val hface
    have hxi : x ≠ i.castSucc := by
      intro h
      have hxVal : x.val = i.val := congrArg Fin.val h
      omega
    have hxsi : x ≠ i.succ := by
      intro h
      have hxVal : x.val = i.val + 1 := congrArg Fin.val h
      omega
    -- Below `i` the swap fixes every element of the prefix.
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxsi]
    exact hx
  · have hik : i ≤ k := le_of_not_gt hki
    have hface : i.castSucc.succAbove k = k.succ :=
      Fin.succAbove_castSucc_of_le i k hik
    have hfaceVal : (i.castSucc.succAbove k).val = k.val + 1 :=
      congrArg Fin.val hface
    have hcastVal : i.castSucc.val = i.val := rfl
    have hsuccVal : i.succ.val = i.val + 1 := rfl
    -- At or above `i`, the prefix contains both exchanged positions.
    rw [Equiv.swap_apply_def]
    split_ifs
    · omega
    · omega
    · exact hx

/-- Helper for Remark 60.1: right multiplication by an adjacent swap leaves
the image of each retained permutation prefix unchanged. -/
private lemma range_adjacentSwap_castLE_succAbove (n : ℕ)
    (i k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2))) :
    Set.range (fun l : Fin ((i.castSucc.succAbove k).val + 1) ↦
        (π * Equiv.swap i.castSucc i.succ)
          (Fin.castLE (Nat.succ_le_succ
            (Nat.le_of_lt_succ (i.castSucc.succAbove k).isLt)) l)) =
      Set.range (fun l : Fin ((i.castSucc.succAbove k).val + 1) ↦
        π (Fin.castLE (Nat.succ_le_succ
          (Nat.le_of_lt_succ (i.castSucc.succAbove k).isLt)) l)) := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨l, rfl⟩
    let x := Fin.castLE (Nat.succ_le_succ
      (Nat.le_of_lt_succ (i.castSucc.succAbove k).isLt)) l
    have hxle : (Equiv.swap i.castSucc i.succ x).val ≤
        (i.castSucc.succAbove k).val :=
      adjacentSwap_le_succAbove n i k x (Nat.le_of_lt_succ l.isLt)
    let l' : Fin ((i.castSucc.succAbove k).val + 1) :=
      ⟨(Equiv.swap i.castSucc i.succ x).val, Nat.lt_succ_of_le hxle⟩
    -- Reindex the prefix by the adjacent swap itself.
    refine ⟨l', ?_⟩
    simp only [Equiv.Perm.mul_apply]
    congr 2
  · rintro _ ⟨l, rfl⟩
    let x := Fin.castLE (Nat.succ_le_succ
      (Nat.le_of_lt_succ (i.castSucc.succAbove k).isLt)) l
    have hxle : (Equiv.swap i.castSucc i.succ x).val ≤
        (i.castSucc.succAbove k).val :=
      adjacentSwap_le_succAbove n i k x (Nat.le_of_lt_succ l.isLt)
    let l' : Fin ((i.castSucc.succAbove k).val + 1) :=
      ⟨(Equiv.swap i.castSucc i.succ x).val, Nat.lt_succ_of_le hxle⟩
    refine ⟨l', ?_⟩
    simp only [Equiv.Perm.mul_apply]
    congr 2
    have hcast : Fin.castLE (Nat.succ_le_succ
        (Nat.le_of_lt_succ (i.castSucc.succAbove k).isLt)) l' =
        Equiv.swap i.castSucc i.succ x := by
      apply Fin.ext
      rfl
    -- Applying the same transposition twice recovers the original index.
    rw [hcast, Equiv.swap_apply_self]

/-- Helper for Remark 60.1: corresponding retained barycentric vertices agree
after an adjacent transposition. -/
private lemma vertex_adjacentSwap (n : ℕ) (i k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 2))) :
    vertex (n + 1) (π * Equiv.swap i.castSucc i.succ) (i.castSucc.succAbove k) =
      vertex (n + 1) π (i.castSucc.succAbove k) := by
  classical
  apply stdSimplex.ext
  funext j
  -- Both coordinate formulas use the same prefix range.
  rw [vertex_apply, vertex_apply]
  simp only [range_adjacentSwap_castLE_succAbove]

/-- Helper for Remark 60.1: the two barycentric affine maps agree on the
nonfinal face paired by an adjacent transposition. -/
private lemma continuousMap_face_adjacentSwap (n : ℕ) (i : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 2))) (z : stdSimplex ℝ (Fin (n + 1))) :
    continuousMap (n + 1) (π * Equiv.swap i.castSucc i.succ)
        (stdSimplex.map i.castSucc.succAbove z) =
      continuousMap (n + 1) π (stdSimplex.map i.castSucc.succAbove z) := by
  classical
  -- Pull the face inclusion through both affine extensions and compare vertices.
  unfold continuousMap
  rw [stdSimplex.affineMapOfVertices_map, stdSimplex.affineMapOfVertices_map]
  congr 2
  funext k
  exact vertex_adjacentSwap n i k π

/-- Helper for Remark 60.1: deleting a nonfinal barycenter gives the same
singular face after swapping the adjacent permutation entries. -/
lemma singularSimplex_δ_adjacentSwap (n : ℕ) (i : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 2))) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
        (singularSimplex (n + 1) (π * Equiv.swap i.castSucc i.succ)) =
      (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
        (singularSimplex (n + 1) π) := by
  -- Compare the continuous representatives pointwise on the standard face.
  apply ((TopCat.of (stdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  simp only [singularSimplex, Equiv.apply_symm_apply]
  exact continuousMap_face_adjacentSwap n i π z

/-- Helper for Remark 60.1: for a fixed nonfinal face, the signed sum of all
barycentric singular faces cancels in adjacent-transposition pairs. -/
lemma interiorFaces_sum_eq_zero (n : ℕ) (i : Fin (n + 1)) :
    ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
      (TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
              (singularSimplex (n + 1) π)) = 0 := by
  classical
  let s : Equiv.Perm (Fin (n + 2)) := Equiv.swap i.castSucc i.succ
  have his : i.castSucc ≠ i.succ :=
    (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  -- Pair every permutation with right multiplication by the adjacent swap.
  apply Finset.sum_ninvolution (s := Finset.univ) (fun π ↦ π * s)
  · intro π
    have hsign : ((π * s).sign : ℤ) = -(π.sign : ℤ) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap his]
      simp only [Units.val_neg, mul_neg, mul_one]
    rw [hsign]
    have hface := singularSimplex_δ_adjacentSwap n i π
    rw [hface]
    simp only [neg_zsmul, add_neg_cancel]
  · intro π _ hfixed
    have happ := congrArg (fun τ : Equiv.Perm (Fin (n + 2)) ↦ τ i.castSucc) hfixed
    simp only [Equiv.Perm.mul_apply, s, Equiv.swap_apply_left] at happ
    exact his (π.injective happ).symm
  · intro π
    exact Finset.mem_univ _
  · intro π
    rw [mul_assoc]
    simp only [s, Equiv.swap_mul_self, mul_one]

/-- Helper for Remark 60.1: order the vertices of the face opposite `r` by
`τ`, then append `r` as the final vertex. -/
def lastPermutation (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Fin.cycleIcc r (Fin.last (n + 1)) *
    τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1)))

/-- Helper for Remark 60.1: the final value of the last-vertex permutation is
the omitted face vertex. -/
lemma lastPermutation_last (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    lastPermutation n r τ (Fin.last (n + 1)) = r := by
  classical
  unfold lastPermutation
  rw [Equiv.Perm.mul_apply]
  rw [Equiv.Perm.extendDomain_apply_not_subtype]
  · -- The interval cycle sends its upper endpoint back to `r`.
    exact Fin.cycleIcc_of_last (Fin.le_last r)
  · simp only [not_ne_iff]

/-- Helper for Remark 60.1: before the final value, the last-vertex permutation
follows the ordered face inclusion. -/
lemma lastPermutation_castSucc (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    lastPermutation n r τ k.castSucc = r.succAbove (τ k) := by
  classical
  unfold lastPermutation
  rw [Equiv.Perm.mul_apply]
  have hext : τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1))) k.castSucc =
      (τ k).castSucc := by
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last_apply] using
      Equiv.Perm.extendDomain_apply_image τ
        (finSuccAboveEquiv (Fin.last (n + 1))) k
  rw [hext]
  -- The interval cycle carries the standard last-face inclusion to `r.succAbove`.
  have hcycle := congrFun
    (Fin.cycleIcc_comp_succAbove r (Fin.last (n + 1)) (Fin.le_last r)) (τ k)
  simpa only [Function.comp_apply, Fin.succAbove_last_apply] using hcycle

/-- Helper for Remark 60.1: the sign of the last-vertex permutation splits into
the interval-cycle sign and the face-ordering sign. -/
lemma lastPermutation_sign (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (lastPermutation n r τ).sign =
      (-1) ^ (Fin.last (n + 1) - r : ℕ) * τ.sign := by
  classical
  -- Multiplicativity, the cycle sign, and extension invariance give the formula.
  unfold lastPermutation
  rw [Equiv.Perm.sign_mul, Fin.sign_cycleIcc_of_le (Fin.le_last r),
    Equiv.Perm.sign_extendDomain]
  rfl

/-- Helper for Remark 60.1: the omitted vertex and its face ordering parameterize
all top-dimensional permutations bijectively. -/
lemma lastPermutation_bijective (n : ℕ) :
    Function.Bijective
      (fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
        lastPermutation n p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have hr : r = r' := by
      have happ := congrArg
        (fun π : Equiv.Perm (Fin (n + 2)) ↦ π (Fin.last (n + 1))) h
      simpa only [lastPermutation_last] using happ
    subst r'
    have hτ : τ = τ' := by
      apply Equiv.ext
      intro k
      have happ := congrArg (fun π : Equiv.Perm (Fin (n + 2)) ↦ π k.castSucc) h
      rw [lastPermutation_castSucc, lastPermutation_castSucc] at happ
      exact Fin.succAbove_right_injective happ
    subst τ'
    rfl
  · -- The two finite parameter spaces both have cardinality `(n + 2)!`.
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_perm,
      Nat.factorial_succ]

/-- Helper for Remark 60.1: retained vertices of the last-vertex permutation
are the barycentric vertices of the ordered face, mapped by `r.succAbove`. -/
lemma lastPermutation_vertex (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    vertex (n + 1) (lastPermutation n r τ) k.castSucc =
      stdSimplex.map r.succAbove (vertex n τ k) := by
  unfold vertex
  simp only [Fin.val_castSucc]
  rw [stdSimplex.map_comp_apply]
  congr 2
  funext l
  have hcast :
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.castSucc.isLt)) l =
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l).castSucc := by
    apply Fin.ext
    rfl
  -- Normalize the two cast spellings, then use the permutation computation rule.
  calc
    lastPermutation n r τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.castSucc.isLt)) l) =
      lastPermutation n r τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l).castSucc :=
          congrArg (lastPermutation n r τ) hcast
    _ = r.succAbove (τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l)) :=
      lastPermutation_castSucc n r τ _
    _ = (r.succAbove ∘ fun j ↦ τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) j)) l := rfl

/-- Helper for Remark 60.1: a standard-simplex face inclusion preserves the
coordinate indexed by a vertex in its image. -/
private lemma map_succAbove_apply {n : ℕ} (r : Fin (n + 1))
    (z : stdSimplex ℝ (Fin n)) (k : Fin n) :
    stdSimplex.map r.succAbove z (r.succAbove k) = z k := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter : Finset.univ.filter
      (fun l : Fin n ↦ r.succAbove l = r.succAbove k) = {k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.succAbove_right_inj]
  -- The injective face map has a singleton fiber over an included vertex.
  rw [hfilter, Finset.sum_singleton]

/-- Helper for Remark 60.1: a standard-simplex face inclusion has zero coordinate
at its omitted vertex. -/
private lemma map_succAbove_self {n : ℕ} (r : Fin (n + 1))
    (z : stdSimplex ℝ (Fin n)) : stdSimplex.map r.succAbove z r = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter : Finset.univ.filter (fun l : Fin n ↦ r.succAbove l = r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact Fin.succAbove_ne r l hl
  -- The omitted vertex has an empty fiber under the face inclusion.
  rw [hfilter, Finset.sum_empty]

/-- Helper for Remark 60.1: restricting a last-vertex barycentric affine map to
its final face is barycentric subdivision inside the corresponding face. -/
lemma lastPermutation_map (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (z : stdSimplex ℝ (Fin (n + 1))) :
    continuousMap (n + 1) (lastPermutation n r τ)
        (stdSimplex.map (Fin.last (n + 1)).succAbove z) =
      stdSimplex.map r.succAbove (continuousMap n τ z) := by
  classical
  apply stdSimplex.ext
  funext q
  rcases Fin.eq_self_or_eq_succAbove r q with rfl | ⟨j, rfl⟩
  · rw [map_succAbove_self]
    simp only [continuousMap, stdSimplex.affineMapOfVertices_apply]
    rw [Fin.sum_univ_castSucc]
    have hlast : stdSimplex.map (Fin.last (n + 1)).succAbove z
        (Fin.last (n + 1)) = 0 := map_succAbove_self _ z
    rw [hlast, zero_mul, add_zero]
    apply Finset.sum_eq_zero
    intro k _
    -- Every retained vertex lies in the face, so its omitted coordinate is zero.
    rw [lastPermutation_vertex, map_succAbove_self, mul_zero]
  · rw [map_succAbove_apply]
    simp only [continuousMap, stdSimplex.affineMapOfVertices_apply]
    rw [Fin.sum_univ_castSucc]
    have hlast : stdSimplex.map (Fin.last (n + 1)).succAbove z
        (Fin.last (n + 1)) = 0 := map_succAbove_self _ z
    rw [hlast, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    -- On retained coordinates, both sides have the same coefficient and vertex.
    have hcoeff : stdSimplex.map (Fin.last (n + 1)).succAbove z k.castSucc = z k := by
      simpa only [Fin.succAbove_last_apply] using
        map_succAbove_apply (Fin.last (n + 1)) z k
    rw [hcoeff, lastPermutation_vertex, map_succAbove_apply]

/-- Helper for Remark 60.1: the singular map represented by a face of the
universal simplex is the corresponding standard face inclusion. -/
private lemma singularMap_face_identity_apply (n : ℕ) (r : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (singularMap
      (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ r
          (identitySingularSimplex (n + 1)))).hom z =
      stdSimplex.map r.succAbove z := by
  -- Evaluate the represented face through the singular-simplex equivalence.
  unfold singularMap
  rw [TopCat.hom_ofHom]
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_identitySingularSimplex]
  rfl

/-- Helper for Remark 60.1: the final face of a last-vertex barycentric simplex
is the corresponding barycentric simplex pushed into the original face. -/
lemma singularSimplex_δ_lastPermutation (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    (TopCat.toSSet.obj Δ).δ (Fin.last (n + 1))
          (singularSimplex (n + 1) (lastPermutation n r τ)) =
      (TopCat.toSSet.map
        (singularMap Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))))).app
        (Opposite.op (SimplexCategory.mk n)) (singularSimplex n τ) := by
  dsimp only
  apply ((TopCat.of (stdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  -- Normalize the final face and the pushforward to their continuous representatives.
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_map]
  simp only [singularSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rw [singularMap_face_identity_apply]
  exact lastPermutation_map n r τ z

/-- Helper for Remark 60.1: multiplying the last-face boundary sign by the
last-vertex permutation sign gives the usual sign of the omitted vertex. -/
lemma lastPermutation_boundarySign (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (-1 : ℤ) ^ (n + 1) * ((lastPermutation n r τ).sign : ℤ) =
      (-1 : ℤ) ^ r.val * (τ.sign : ℤ) := by
  have hsign : ((lastPermutation n r τ).sign : ℤ) =
      (-1 : ℤ) ^ (Fin.last (n + 1) - r : ℕ) * (τ.sign : ℤ) := by
    -- Pass the permutation-sign identity from units to its underlying integer.
    calc
      ((lastPermutation n r τ).sign : ℤ) =
          ((((-1 : ℤˣ) ^ (Fin.last (n + 1) - r : ℕ)) * τ.sign : ℤˣ) : ℤ) :=
        congrArg (fun u : ℤˣ ↦ (u : ℤ)) (lastPermutation_sign n r τ)
      _ = ((((-1 : ℤˣ) ^ (Fin.last (n + 1) - r : ℕ) : ℤˣ) : ℤ) *
          (τ.sign : ℤ)) := Units.val_mul _ _
      _ = (((-1 : ℤˣ) : ℤ) ^ (Fin.last (n + 1) - r : ℕ) *
          (τ.sign : ℤ)) := by
        exact congrArg (fun a : ℤ ↦ a * (τ.sign : ℤ))
          (Units.val_pow_eq_pow_val (-1 : ℤˣ) (Fin.last (n + 1) - r : ℕ))
      _ = (-1 : ℤ) ^ (Fin.last (n + 1) - r : ℕ) * (τ.sign : ℤ) := by
        rfl
  rw [hsign, ← mul_assoc, ← pow_add]
  have hr : r.val ≤ n + 1 := Nat.le_of_lt_succ r.isLt
  have hsub : (Fin.last (n + 1) - r : ℕ) = n + 1 - r.val := by
    rfl
  have hexp : (n + 1) + (Fin.last (n + 1) - r : ℕ) =
      r.val + 2 * (Fin.last (n + 1) - r : ℕ) := by
    rw [hsub]
    omega
  rw [hexp, pow_add, pow_mul]
  norm_num

/-- Helper for Remark 60.1: the signed sum of final barycentric faces is the
alternating sum of the subdivisions of the original codimension-one faces. -/
lemma lastFaces_sum (n : ℕ) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
      ((-1 : ℤ) ^ (n + 1) •
        (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj Δ).δ (Fin.last (n + 1))
            (singularSimplex (n + 1) π))) =
      ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))) := by
  dsimp only
  let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
  let e := fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
    lastPermutation n p.1 p.2
  let finalGenerator := fun π : Equiv.Perm (Fin (n + 2)) ↦
    (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      ((TopCat.toSSet.obj Δ).δ (Fin.last (n + 1)) (singularSimplex (n + 1) π))
  let faceGenerator := fun r : Fin (n + 2) ↦
      fun τ : Equiv.Perm (Fin (n + 1)) ↦
        (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map
            (singularMap Δ n
              ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))))).app
            (Opposite.op (SimplexCategory.mk n)) (singularSimplex n τ))
  have he : Function.Bijective e := lastPermutation_bijective n
  have hgenerator (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
      finalGenerator (e (r, τ)) = faceGenerator r τ := by
    -- The final-face computation identifies the two simplex generators.
    unfold finalGenerator faceGenerator e Δ
    rw [singularSimplex_δ_lastPermutation]
  have hterm (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
      ((e p).sign : ℤ) • ((-1 : ℤ) ^ (n + 1) • finalGenerator (e p)) =
        (-1 : ℤ) ^ p.1.val • ((p.2.sign : ℤ) • faceGenerator p.1 p.2) := by
    rw [hgenerator]
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_comm ((e p).sign : ℤ)]
    exact lastPermutation_boundarySign n p.1 p.2
  calc
    ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
        ((-1 : ℤ) ^ (n + 1) • finalGenerator π) =
      ∑ p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
        (-1 : ℤ) ^ p.1.val • ((p.2.sign : ℤ) • faceGenerator p.1 p.2) :=
      (Fintype.sum_bijective e he
        (fun p ↦ (-1 : ℤ) ^ p.1.val •
          ((p.2.sign : ℤ) • faceGenerator p.1 p.2))
        (fun π ↦ (π.sign : ℤ) •
          ((-1 : ℤ) ^ (n + 1) • finalGenerator π))
        (fun p ↦ (hterm p).symm)).symm
    _ = ∑ r : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        (-1 : ℤ) ^ r.val • ((τ.sign : ℤ) • faceGenerator r τ) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        ∑ τ : Equiv.Perm (Fin (n + 1)),
          (τ.sign : ℤ) • faceGenerator r τ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.smul_sum]
    _ = ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [simplexChain_eq_sum]

/-- Helper for Remark 60.1: the universal barycentric subdivision chain has
boundary equal to the alternating sum of the subdivided original faces. -/
lemma standardChain_boundary (n : ℕ) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    standardChain (n + 1) ≫
        ((TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))) := by
  dsimp only
  unfold standardChain
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  simp_rw [SSet.ιChainComplex_d]
  have hsplit (π : Equiv.Perm (Fin (n + 2))) :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i
                (singularSimplex (n + 1) π))) =
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.castSucc.val •
          (TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                  (singularSimplex (n + 1) π))) +
        (-1 : ℤ) ^ (Fin.last (n + 1)).val •
          (TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ (Fin.last (n + 1))
                  (singularSimplex (n + 1) π)) := by
    exact Fin.sum_univ_castSucc _
  simp_rw [hsplit, smul_add]
  rw [Finset.sum_add_distrib]
  have hinterior :
      (∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.castSucc.val •
          (TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                  (singularSimplex (n + 1) π))) = 0 := by
    -- Commute the permutation and face sums, then cancel each fixed nonfinal face.
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    calc
      ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
          ((-1 : ℤ) ^ i.castSucc.val •
            (TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj
                  (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                    (singularSimplex (n + 1) π))) =
        ∑ π : Equiv.Perm (Fin (n + 2)), (-1 : ℤ) ^ i.castSucc.val •
          ((π.sign : ℤ) •
            (TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj
                  (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                    (singularSimplex (n + 1) π))) := by
          apply Finset.sum_congr rfl
          intro π _
          exact smul_comm _ _ _
      _ = (-1 : ℤ) ^ i.castSucc.val •
          ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
            (TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj
                  (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                    (singularSimplex (n + 1) π)) := by
        rw [Finset.smul_sum]
      _ = 0 := by
        rw [interiorFaces_sum_eq_zero, smul_zero]
  rw [hinterior, zero_add]
  -- The surviving final faces are exactly the reindexed face subdivisions.
  simpa only [Fin.val_last] using lastFaces_sum n

/-- Helper for Remark 60.1: the boundary of a subdivided singular simplex is the
alternating sum of the subdivisions of its faces. -/
lemma simplexChain_boundary (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    simplexChain X (n + 1) σ ≫
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain X n ((TopCat.toSSet.obj X).δ r σ) := by
  let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
  let F := SSet.chainComplexMap (TopCat.toSSet.map (singularMap X (n + 1) σ))
    (ModuleCat.of ℤ ℤ)
  -- Push the universal boundary calculation through the map represented by `σ`.
  calc
    simplexChain X (n + 1) σ ≫
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      (standardChain (n + 1) ≫ F.f (n + 1)) ≫
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n := rfl
    _ = standardChain (n + 1) ≫
        (F.f (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n) :=
      Category.assoc _ _ _
    _ = standardChain (n + 1) ≫
        (((TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
          F.f n) := by
      rw [HomologicalComplex.Hom.comm]
    _ = (standardChain (n + 1) ≫
        ((TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n) ≫
          F.f n := (Category.assoc _ _ _).symm
    _ = (∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1)))) ≫
          F.f n := by
      rw [standardChain_boundary]
    _ = ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        (simplexChain Δ n
          ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1))) ≫
            F.f n) := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro r _
      rw [Preadditive.zsmul_comp]
    _ = ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain X n
          ((TopCat.toSSet.map (singularMap X (n + 1) σ)).app
            (Opposite.op (SimplexCategory.mk n))
              ((TopCat.toSSet.obj Δ).δ r (identitySingularSimplex (n + 1)))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [simplexChain_naturality]
    _ = ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        simplexChain X n ((TopCat.toSSet.obj X).δ r σ) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [SSet.δ_naturality_apply, map_identitySingularSimplex]

/-- Helper for Remark 60.1: degreewise barycentric subdivision extends the
simplexwise assignment to the full integral singular-chain module. -/
noncomputable def component (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  CategoryTheory.Limits.Cofan.IsColimit.desc
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun σ ↦ simplexChain X n σ)

/-- Helper for Remark 60.1: the degreewise subdivision map has the prescribed
value on every singular-simplex generator. -/
lemma ι_component (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ component X n =
      simplexChain X n σ := by
  -- This is the factorization rule of the coproduct colimit defining chains.
  exact CategoryTheory.Limits.Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun τ ↦ simplexChain X n τ) σ

/-- Helper for Remark 60.1: degreewise barycentric subdivision commutes with
the singular-chain differential. -/
lemma component_comp_d (X : TopCat) (n : ℕ) :
    component X (n + 1) ≫
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
        component X n := by
  -- Generator extensionality reduces the chain square to the boundary computation.
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_component, simplexChain_boundary]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [Preadditive.zsmul_comp, ι_component]

/-- Helper for Remark 60.1: barycentric subdivision defines an endomorphism of
the integral singular chain complex. -/
noncomputable def chainMap (X : TopCat) :
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) :=
  ChainComplex.ofHom (fun n ↦ component X n) (fun n ↦ component_comp_d X n)

/-- Helper for Remark 60.1: the global subdivision chain map sends a simplex
generator to its signed barycentric subdivision. -/
lemma ι_chainMap (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (chainMap X).f n =
      simplexChain X n σ := by
  -- The packaged chain map has the degreewise component computed above.
  exact ι_component X n σ

end AlgebraicTopology.BarycentricSubdivision


namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits ContinuousMap

/-- Helper for Remark 60.1: the forward and inverse maps of a topological homotopy
equivalence induce a composite singular-chain map homotopic to the identity. -/
noncomputable def integralSingularChainHomotopyHomInvId
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Homotopy
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom e.toFun) ≫
        ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom e.invFun))
      (𝟙 (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))) :=
  -- Transport the functorial image of the chosen homotopy across the functor laws.
  (Homotopy.ofEq
    (CategoryTheory.Functor.map_comp
      ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
        (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)).symm).trans
    ((TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)
      (g := 𝟙 (TopCat.of X)) e.left_inv.some (ModuleCat.of ℤ ℤ)).trans
      (Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
            (TopCat.of X))))

/-- Helper for Remark 60.1: the inverse and forward maps of a topological homotopy
equivalence induce the other singular-chain composite homotopic to the identity. -/
noncomputable def integralSingularChainHomotopyInvHomId
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    Homotopy
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom e.invFun) ≫
        ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom e.toFun))
      (𝟙 (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))) :=
  -- Transport the inverse-composite homotopy across the same two functor laws.
  (Homotopy.ofEq
    (CategoryTheory.Functor.map_comp
      ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
        (TopCat.ofHom e.invFun) (TopCat.ofHom e.toFun)).symm).trans
    ((TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)
      (g := 𝟙 (TopCat.of Y)) e.right_inv.some (ModuleCat.of ℤ ℤ)).trans
      (Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
            (TopCat.of Y))))

/-- Helper for Remark 60.1: a topological homotopy equivalence induces a homotopy
equivalence of integral singular chain complexes. -/
noncomputable def integralSingularChainHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of X))
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of Y)) :=
  -- Package the two induced chain maps with the homotopies proved above.
  { hom := ((singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.toFun)
    inv := ((singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.invFun)
    homotopyHomInvId := integralSingularChainHomotopyHomInvId e
    homotopyInvHomId := integralSingularChainHomotopyInvHomId e }

/-- Helper for Remark 60.1: integral singular chains of a contractible space are
exact in every positive degree. -/
lemma integralSingularChainComplex_exactAt_of_contractible
    (X : TopCat) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).ExactAt n := by
  -- Compare with the one-point space through a chosen topological homotopy equivalence.
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  -- Positive homology vanishes for `Unit`, and the induced homology isomorphism transfers it.
  exact IsZero.of_iso
    (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of Unit) hn).isZero_homology
    ((integralSingularChainHomotopyEquiv e).toHomologyIso n)

end AlgebraicTopology

namespace AlgebraicTopology.BarycentricSubdivision

open CategoryTheory

/-- Helper for Remark 60.1: the integral coefficient module is projective, via its
canonical one-element basis. -/
lemma integralCoefficientModuleProjective :
    CategoryTheory.Projective (ModuleCat.of ℤ ℤ) :=
  -- Exhibit the coefficient module as a free rank-one module.
  ModuleCat.projective_of_free (Module.Basis.singleton Unit ℤ)

/-- Helper for Remark 60.1: the integral singular chain complex of a standard
simplex is exact in every positive degree. -/
lemma integralStandardSimplexChainComplex_exactAt (m n : ℕ) (hn : n ≠ 0) :
    ((TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
        (ModuleCat.of ℤ ℤ)).ExactAt n := by
  -- Contract the nonempty convex simplex to its zeroth vertex.
  letI : ContractibleSpace (stdSimplex ℝ (Fin (m + 1))) :=
    (convex_stdSimplex ℝ (Fin (m + 1))).contractibleSpace
      ⟨stdSimplex.vertex 0, (stdSimplex.vertex 0).property⟩
  exact integralSingularChainComplex_exactAt_of_contractible _ n hn

/-- Helper for Remark 60.1: positive exactness of a standard simplex, presented as
the explicit adjacent-differential short complex used for cycle lifting. -/
lemma integralStandardSimplexChainComplex_exact (m n : ℕ) :
    (((TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
        (ModuleCat.of ℤ ℤ)).sc' (n + 2) (n + 1) n).Exact := by
  -- Replace abstract `ExactAt` by the concrete three consecutive chain groups.
  rw [← HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact integralStandardSimplexChainComplex_exactAt m (n + 1) (Nat.succ_ne_zero n)

/-- Helper for Remark 60.1: choose a filler for a positive-dimensional integral
cycle in a standard simplex, returning zero when the input is not a cycle. -/
noncomputable def fillStandardSimplexCycle (m n : ℕ)
    (z : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1)) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 2) :=
  -- Keep the rank-one projectivity bridge local to the exactness lift.
  letI := integralCoefficientModuleProjective
  @dite
    (ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 2))
    (z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n = 0)
    (Classical.propDecidable _)
    (fun hz ↦
      (integralStandardSimplexChainComplex_exact m n).liftFromProjective z hz)
    (fun _ ↦ 0)

/-- Helper for Remark 60.1: the chosen standard-simplex filler has the prescribed
boundary whenever its input is a cycle. -/
lemma fillStandardSimplexCycle_boundary (m n : ℕ)
    (z : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n = 0) :
    fillStandardSimplexCycle m n z ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) = z := by
  -- Select the cycle branch, then apply the defining equation of the projective lift.
  rw [fillStandardSimplexCycle, dif_pos hz]
  exact ShortComplex.Exact.liftFromProjective_comp _ _ _

/-- Helper for Remark 60.1: transport a candidate prism on the standard
`n`-simplex across all faces of the standard `(n + 1)`-simplex, with signs. -/
noncomputable def standardPrismBoundary (n : ℕ)
    (p : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1)) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1) :=
  -- Push the lower-dimensional prism through each represented face map and alternate.
  ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
    (p ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map
          (singularMap
            (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ r
                  (identitySingularSimplex (n + 1)))))
        (ModuleCat.of ℤ ℤ)).f (n + 1))

/-- Helper for Remark 60.1: the universal prism is obtained recursively by filling
the difference between subdivision, the identity simplex, and the face prisms. -/
noncomputable def standardPrismChain :
    (n : ℕ) → ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1) := fun n ↦
  -- Start with zero in degree zero; at each successor fill the recursive defect.
  match n with
  | 0 => 0
  | Nat.succ n =>
      fillStandardSimplexCycle (n + 1) n
        (standardChain (n + 1) - integralFundamentalChain (n + 1) -
          standardPrismBoundary n (standardPrismChain n))

/-- Helper for Remark 60.1: the universal prism starts with the zero one-chain. -/
lemma standardPrismChain_zero : standardPrismChain 0 = 0 := by
  -- Read off the initial branch of the recursive construction.
  rfl

/-- Helper for Remark 60.1: each successor universal prism is the chosen filler
of the subdivision-minus-identity defect after subtracting its face prisms. -/
lemma standardPrismChain_succ (n : ℕ) :
    standardPrismChain (n + 1) =
      fillStandardSimplexCycle (n + 1) n
        (standardChain (n + 1) - integralFundamentalChain (n + 1) -
          standardPrismBoundary n (standardPrismChain n)) := by
  -- Read off the successor branch without unfolding the filler itself.
  rfl

/-- Helper for Remark 60.1: push the universal standard-simplex prism along the
continuous map represented by an arbitrary singular simplex. -/
noncomputable def simplexPrism (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1) :=
  -- Transport the universal chain one degree above the simplex generator.
  standardPrismChain n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularMap X n σ))
      (ModuleCat.of ℤ ℤ)).f (n + 1)

/-- Helper for Remark 60.1: extend the simplexwise prism assignment linearly to
the full integral singular-chain module in degree `n`. -/
noncomputable def prismComponent (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1) :=
  -- Use the coproduct colimit presentation of the free singular-chain module.
  CategoryTheory.Limits.Cofan.IsColimit.desc
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun σ ↦ simplexPrism X n σ)

/-- Helper for Remark 60.1: the global prism component has its prescribed value
on every singular-simplex generator. -/
lemma ι_prismComponent (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ prismComponent X n =
      simplexPrism X n σ := by
  -- Apply the colimit factorization rule for the generator indexed by `σ`.
  exact CategoryTheory.Limits.Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun τ ↦ simplexPrism X n τ) σ

/-- Helper for Remark 60.1: the alternating face prism is the universal
fundamental boundary followed by the global lower-degree prism component. -/
lemma fundamentalBoundary_comp_prismComponent (n : ℕ) :
    (integralFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n) ≫
      prismComponent (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n =
        standardPrismBoundary n (standardPrismChain n) := by
  -- Expand the fundamental boundary and evaluate the component on each face generator.
  rw [integralFundamentalChain_boundary, Preadditive.sum_comp]
  unfold standardPrismBoundary
  apply Finset.sum_congr rfl
  intro r _
  rw [Preadditive.zsmul_comp, ι_prismComponent]
  rfl

/-- Helper for Remark 60.1: degreewise integral simplicial-chain maps preserve
composition of simplicial maps. -/
lemma integralChainComplexMap_f_comp {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n ≫
        (SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f n =
      (SSet.chainComplexMap (f ≫ g) (ModuleCat.of ℤ ℤ)).f n := by
  -- Compare the degree components after applying functoriality at chain-map level.
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]

/-- Helper for Remark 60.1: transporting the universal alternating face prism
along a represented simplex agrees with applying the global prism to its boundary. -/
lemma standardPrismBoundary_naturality (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    standardPrismBoundary n (standardPrismChain n) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularMap X (n + 1) σ))
          (ModuleCat.of ℤ ℤ)).f (n + 1) =
      ((TopCat.toSSet.obj X).ιChainComplex σ ≫
          ((TopCat.toSSet.obj X).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n) ≫
        prismComponent X n := by
  -- Expand both sides into the same signed sum of represented face prisms.
  rw [SSet.ιChainComplex_d, Preadditive.sum_comp]
  unfold standardPrismBoundary
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, ι_prismComponent]
  -- Naturality of faces identifies the two represented continuous composites.
  unfold simplexPrism
  rw [Category.assoc, integralChainComplexMap_f_comp, ← Functor.map_comp,
    ← singularMap_map, SSet.δ_naturality_apply,
    map_identitySingularSimplex]

/-- Helper for Remark 60.1: a universal prism boundary equation yields the
successor-degree chain-homotopy equation on every singular chain complex. -/
lemma prismComponent_homotopy_of_standardPrismBoundary (X : TopCat) (n : ℕ)
    (hboundary :
      standardPrismChain (n + 1) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) =
        standardChain (n + 1) - integralFundamentalChain (n + 1) -
          standardPrismBoundary n (standardPrismChain n)) :
    (chainMap X).f (n + 1) =
      ((TopCat.toSSet.obj X).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ prismComponent X n +
        prismComponent X (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) +
        ((𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)) :
          (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
            (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))).f (n + 1) := by
  -- It suffices to compare the two endomorphisms on every simplex generator.
  apply SSet.chainComplex_hom_ext
  intro σ
  let F := SSet.chainComplexMap
    (TopCat.toSSet.map (singularMap X (n + 1) σ)) (ModuleCat.of ℤ ℤ)
  have hface :
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (((TopCat.toSSet.obj X).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ prismComponent X n) =
        standardPrismBoundary n (standardPrismChain n) ≫ F.f (n + 1) := by
    -- Reassociate the already proved transport square into the homotopy normal form.
    rw [← Category.assoc, ← standardPrismBoundary_naturality]
  have hprism :
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (prismComponent X (n + 1) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1)) =
        (standardChain (n + 1) - integralFundamentalChain (n + 1) -
            standardPrismBoundary n (standardPrismChain n)) ≫ F.f (n + 1) := by
    -- Commute the represented-simplex map past the differential, then use the
    -- assumed universal boundary equation.
    rw [← Category.assoc, ι_prismComponent]
    unfold simplexPrism
    rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc,
      hboundary]
  have hidentity :
      (TopCat.toSSet.obj X).ιChainComplex σ =
        integralFundamentalChain (n + 1) ≫ F.f (n + 1) := by
    -- The represented simplex is the pushforward of the universal generator.
    exact (integralFundamentalChain_naturality X (n + 1) σ).symm
  -- Substitute the three generator computations and cancel the additive defect.
  rw [ι_chainMap]
  unfold simplexChain
  rw [Preadditive.comp_add, Preadditive.comp_add]
  rw [hface, hprism, HomologicalComplex.id_f, Category.comp_id, hidentity]
  rw [Preadditive.sub_comp, Preadditive.sub_comp]
  abel

/-- Helper for Remark 60.1: every barycentric zero-simplex is the universal
zero-simplex, since the standard zero-simplex is a singleton. -/
lemma singularSimplex_zero (π : Equiv.Perm (Fin 1)) :
    singularSimplex 0 π = identitySingularSimplex 0 := by
  -- Compare represented continuous maps, which agree by subsingleton elimination.
  apply ((TopCat.of (stdSimplex ℝ (Fin 1))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk 0))).injective
  rw [singularSimplex, Equiv.apply_symm_apply,
    toSSetObjEquiv_identitySingularSimplex]
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- Helper for Remark 60.1: barycentric subdivision is the identity on the
universal zero-simplex. -/
lemma standardChain_zero : standardChain 0 = integralFundamentalChain 0 := by
  -- The permutation type of one vertex is a singleton with positive sign.
  classical
  unfold standardChain integralFundamentalChain
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 1))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, one_smul,
      singularSimplex_zero]
  · intro π _ hπ
    exact (hπ (Subsingleton.elim _ _)).elim
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Helper for Remark 60.1: the degree-zero prism component vanishes on every
integral singular chain complex. -/
lemma prismComponent_zero (X : TopCat) : prismComponent X 0 = 0 := by
  -- Generator extensionality reduces the claim to the zero universal prism.
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_prismComponent, CategoryTheory.Limits.comp_zero]
  unfold simplexPrism
  rw [standardPrismChain_zero, CategoryTheory.Limits.zero_comp]

/-- Helper for Remark 60.1: barycentric subdivision acts as the identity on
degree-zero integral singular chains. -/
lemma chainMap_zero (X : TopCat) :
    (chainMap X).f 0 =
      ((𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)) :
        (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
          (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))).f 0 := by
  -- Both maps carry each zero-simplex generator to itself.
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_chainMap, HomologicalComplex.id_f, Category.comp_id]
  unfold simplexChain
  rw [standardChain_zero, integralFundamentalChain_naturality]

/-- Helper for Remark 60.1: the boundary of the universal subdivision is the
fundamental boundary followed by the subdivision chain map. -/
lemma standardChain_boundary_eq_fundamentalBoundary_comp_chainMap (n : ℕ) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    standardChain (n + 1) ≫
        ((TopCat.toSSet.obj Δ).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      (integralFundamentalChain (n + 1) ≫
          ((TopCat.toSSet.obj Δ).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n) ≫
        (chainMap Δ).f n := by
  -- Expand both boundaries and compare the subdivision on each face generator.
  dsimp only
  rw [standardChain_boundary, integralFundamentalChain_boundary,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [Preadditive.zsmul_comp, ι_chainMap]

/-- Helper for Remark 60.1: the initial recursive prism defect is a cycle. -/
lemma standardPrismDefect_zero_isCycle :
    (standardChain 1 - integralFundamentalChain 1 -
        standardPrismBoundary 0 (standardPrismChain 0)) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin 2)))).chainComplex
          (ModuleCat.of ℤ ℤ)).d 1 0 = 0 := by
  -- In degree zero subdivision is the identity and the lower prism vanishes.
  rw [← fundamentalBoundary_comp_prismComponent,
    prismComponent_zero, CategoryTheory.Limits.comp_zero]
  rw [Preadditive.sub_comp, Preadditive.sub_comp,
    standardChain_boundary_eq_fundamentalBoundary_comp_chainMap,
    chainMap_zero, HomologicalComplex.id_f, Category.comp_id]
  simp only [CategoryTheory.Limits.zero_comp]
  abel

/-- Helper for Remark 60.1: once the prism boundary equation is known in one
dimension, the next recursive prism defect is a cycle. -/
lemma standardPrismDefect_succ_isCycle (n : ℕ)
    (hboundary :
      standardPrismChain (n + 1) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) =
        standardChain (n + 1) - integralFundamentalChain (n + 1) -
          standardPrismBoundary n (standardPrismChain n)) :
    (standardChain (n + 2) - integralFundamentalChain (n + 2) -
        standardPrismBoundary (n + 1) (standardPrismChain (n + 1))) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 3))))).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) = 0 := by
  let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 3)))
  let b := integralFundamentalChain (n + 2) ≫
    ((TopCat.toSSet.obj Δ).chainComplex
      (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1)
  have hsubdivision :
      standardChain (n + 2) ≫
          ((TopCat.toSSet.obj Δ).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) =
        b ≫ (chainMap Δ).f (n + 1) := by
    -- Express the subdivided boundary through the degreewise subdivision map.
    simpa only [Δ, b] using
      standardChain_boundary_eq_fundamentalBoundary_comp_chainMap (n + 1)
  have hfacePrism :
      b ≫ prismComponent Δ (n + 1) =
        standardPrismBoundary (n + 1) (standardPrismChain (n + 1)) := by
    -- The alternating face-prism term is the fundamental boundary acting on the prism.
    simpa only [Δ, b] using fundamentalBoundary_comp_prismComponent (n + 1)
  have hhomotopy :=
    prismComponent_homotopy_of_standardPrismBoundary Δ n hboundary
  have hcycle :
      b ≫ ((TopCat.toSSet.obj Δ).chainComplex
        (ModuleCat.of ℤ ℤ)).d (n + 1) n = 0 := by
    -- The fundamental boundary is itself a cycle by `d ≫ d = 0`.
    dsimp only [b]
    rw [Category.assoc, HomologicalComplex.d_comp_d,
      CategoryTheory.Limits.comp_zero]
  have hkill :
      b ≫ (((TopCat.toSSet.obj Δ).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ prismComponent Δ n) = 0 := by
    -- Postcomposing the vanishing double boundary remains zero.
    rw [← Category.assoc, hcycle, CategoryTheory.Limits.zero_comp]
  have hassoc :
      b ≫ (prismComponent Δ (n + 1) ≫
          ((TopCat.toSSet.obj Δ).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1)) =
        (b ≫ prismComponent Δ (n + 1)) ≫
          ((TopCat.toSSet.obj Δ).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) := by
    -- Put the prism-boundary summand in the same association as the defect term.
    exact (Category.assoc _ _ _).symm
  have hid :
      b ≫ ((𝟙 ((TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ)) :
        (TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ) ⟶
          (TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ))).f (n + 1) = b := by
    -- The identity chain map contributes the unchanged fundamental boundary.
    rw [HomologicalComplex.id_f, Category.comp_id]
  -- Expand the next defect, substitute the homotopy equation, and cancel its terms.
  rw [Preadditive.sub_comp, Preadditive.sub_comp, hsubdivision,
    ← hfacePrism, hhomotopy, Preadditive.comp_add, Preadditive.comp_add,
    hkill, hassoc, hid]
  abel

/-- Helper for Remark 60.1: every recursively chosen universal prism has
boundary equal to subdivision minus the identity simplex and its face prisms. -/
lemma standardPrismChain_boundary (n : ℕ) :
    standardPrismChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) =
      standardChain (n + 1) - integralFundamentalChain (n + 1) -
        standardPrismBoundary n (standardPrismChain n) := by
  -- Induct on dimension, using the previous boundary equation to show that the
  -- next recursive defect lies in the kernel of the differential.
  induction n with
  | zero =>
      rw [standardPrismChain_succ]
      exact fillStandardSimplexCycle_boundary 1 0 _ standardPrismDefect_zero_isCycle
  | succ n ih =>
      rw [standardPrismChain_succ]
      exact fillStandardSimplexCycle_boundary (n + 2) (n + 1) _
        (standardPrismDefect_succ_isCycle n ih)

/-- Helper for Remark 60.1: place each degreewise prism map in its unique
adjacent target degree, and use zero in all other degrees. -/
noncomputable def prismHomotopyComponent (X : TopCat) :
    ∀ i j : ℕ,
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X i ⟶
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X j :=
  fun i ↦ Pi.single (i + 1) (prismComponent X i)

/-- Helper for Remark 60.1: the prism homotopy family vanishes outside the
adjacent degrees allowed by the chain-complex shape. -/
lemma prismHomotopyComponent_zero (X : TopCat) (i j : ℕ)
    (hij : ¬(ComplexShape.down ℕ).Rel j i) :
    prismHomotopyComponent X i j = 0 := by
  -- The shape hypothesis says that `j` is not the single supported index `i + 1`.
  exact Pi.single_eq_of_ne (Ne.symm hij) _

/-- Helper for Remark 60.1: the prism homotopy components satisfy the chain
homotopy commutation equation in every degree. -/
lemma prismHomotopyComponent_comm (X : TopCat) (i : ℕ) :
    (chainMap X).f i =
      _root_.dNext i (prismHomotopyComponent X) +
        _root_.prevD i (prismHomotopyComponent X) +
        ((𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)) :
          (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
            (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))).f i := by
  -- Degree zero uses the vanishing initial prism; positive degrees use the
  -- universal boundary equation transported to the ambient space.
  cases i with
  | zero =>
      rw [_root_.Homotopy.prevD_chainComplex,
        _root_.Homotopy.dNext_zero_chainComplex]
      simp only [prismHomotopyComponent, Pi.single_eq_same,
        prismComponent_zero, CategoryTheory.Limits.zero_comp, zero_add]
      exact chainMap_zero X
  | succ n =>
      rw [_root_.Homotopy.prevD_chainComplex,
        _root_.Homotopy.dNext_succ_chainComplex]
      simpa only [prismHomotopyComponent, Pi.single_eq_same] using
        prismComponent_homotopy_of_standardPrismBoundary X n
          (standardPrismChain_boundary n)

/-- Helper for Remark 60.1: barycentric subdivision of integral singular chains
is chain-homotopic to the identity. -/
noncomputable def chainMapHomotopyIdentity (X : TopCat) :
    _root_.Homotopy (chainMap X)
      (𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))) :=
  { hom := prismHomotopyComponent X
    zero := prismHomotopyComponent_zero X
    comm := prismHomotopyComponent_comm X }

/-- Helper for Remark 60.1: one barycentric refinement cannot increase the
diameter of a finite simplex vertex family. -/
lemma diam_barycentricVertexFamily_le_diam
    {J : Type*} [Fintype J] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (π : Equiv.Perm (Fin (n + 1))) :
    Metric.diam
        (Set.range (fun k ↦ stdSimplex.affineMapOfVertices v (vertex n π k))) ≤
      Metric.diam (Set.range v) := by
  let affineRange := Set.range (stdSimplex.affineMapOfVertices v)
  have hrefined :
      Set.range (fun k ↦ stdSimplex.affineMapOfVertices v (vertex n π k)) ⊆
        affineRange := by
    -- Every refined vertex is an affine image of a barycentric vertex.
    rintro _ ⟨k, rfl⟩
    exact ⟨vertex n π k, rfl⟩
  have haffineBounded : Bornology.IsBounded affineRange := by
    -- The affine image of the compact standard simplex is compact, hence bounded.
    simpa only [Set.image_univ] using
      (isCompact_univ.image (stdSimplex.affineMapOfVertices v).continuous).isBounded
  -- Compare with the full affine image, whose diameter is exactly the old mesh.
  exact (Metric.diam_mono hrefined haffineBounded).trans_eq
    (stdSimplex.diam_range_affineMapOfVertices v)

/-- Helper for Remark 60.1: a refined vertex is the uniform average over the
corresponding permuted prefix of the old vertex family. -/
lemma affineMapOfVertices_vertex_apply
    {J : Type*} [Fintype J] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) (j : J) :
    stdSimplex.affineMapOfVertices v (vertex n π k) j =
      ∑ l : Fin (k.val + 1), ((k.val + 1 : ℕ) : ℝ)⁻¹ *
        v (π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l)) j := by
  -- Pull the prefix map through the affine extension and evaluate the barycenter weights.
  unfold vertex
  rw [stdSimplex.affineMapOfVertices_map]
  simp only [stdSimplex.affineMapOfVertices_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro l _
  change
    (stdSimplex.barycenter : stdSimplex ℝ (Fin (k.val + 1))).val l *
        v (π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l)) j = _
  rw [stdSimplex.barycenter_apply, Fintype.card_fin]

/-- Helper for Remark 60.1: the ambient value of a refined vertex is the
centroid of the corresponding initial permutation interval. -/
lemma coe_affineMapOfVertices_vertex_eq_centroid
    {J : Type*} [Fintype J] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    ((stdSimplex.affineMapOfVertices v (vertex n π k) :
        stdSimplex ℝ J) : J → ℝ) =
      (Finset.Iic k).centroid ℝ
        (fun r ↦ ((v (π r) : stdSimplex ℝ J) : J → ℝ)) := by
  classical
  let hcast : k.val + 1 ≤ n + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)
  have hmap :
      Finset.univ.map (Fin.castLEEmb hcast) = Finset.Iic k := by
    -- Characterize the image directly by the bound on the underlying natural indices.
    ext r
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · rintro ⟨l, rfl⟩
      exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ l.isLt)
    · intro hr
      refine ⟨⟨r.val, Nat.lt_succ_iff.mpr (Fin.le_iff_val_le_val.mp hr)⟩, ?_⟩
      exact Fin.ext rfl
  have hnonempty : (Finset.Iic k).Nonempty :=
    ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  -- Expand both centroids as uniform sums and reindex by the initial-interval embedding.
  ext j
  rw [affineMapOfVertices_vertex_apply]
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      ((Finset.Iic k).sum_centroidWeights_eq_one_of_nonempty ℝ hnonempty)]
  simp only [Finset.centroidWeights_apply, Fin.card_Iic]
  rw [← hmap, Finset.sum_map]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  congr 3

/-- Helper for Remark 60.1: for nested initial intervals, the distance between
their centroids is bounded by the barycentric mesh contraction factor. -/
lemma dist_centroid_Iic_le_diam_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (v : Fin (n + 1) → E) (a b : Fin (n + 1)) (hab : a ≤ b) :
    dist ((Finset.Iic a).centroid ℝ v) ((Finset.Iic b).centroid ℝ v) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  classical
  have hcentroid (c : Fin (n + 1)) :
      (Finset.Iic c).centroid ℝ v =
        (((c.val + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.Iic c, v i) := by
    -- Write each centroid as the uniform average over its initial interval.
    rw [Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        ((Finset.Iic c).sum_centroidWeights_eq_one_of_nonempty ℝ
          ⟨c, Finset.mem_Iic.mpr le_rfl⟩)]
    simp only [Finset.centroidWeights_apply, Fin.card_Iic, Finset.smul_sum]
  have hsum :
      ∑ i ∈ Finset.Iic b, v i =
        (∑ i ∈ Finset.Iic a, v i) + ∑ i ∈ Finset.Ioc a b, v i := by
    -- Split the larger initial interval into the old interval and its new tail.
    rw [← Finset.sum_union (Finset.Iic_disjoint_Ioc le_rfl),
      Finset.Iic_union_Ioc_eq_Iic hab]
  have hidentity :
      (Finset.Iic a).centroid ℝ v - (Finset.Iic b).centroid ℝ v =
        (((b.val + 1 : ℕ) : ℝ)⁻¹ •
          ∑ i ∈ Finset.Ioc a b, ((Finset.Iic a).centroid ℝ v - v i)) := by
    -- Algebraically, the centroid difference is the average of the new displacements.
    rw [hcentroid a, hcentroid b, hsum, Finset.sum_sub_distrib,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
    simp only [Fin.card_Ioc]
    -- Compare the two vector coefficients separately; only the old-prefix
    -- coefficient needs the interval-cardinality identity.
    match_scalars
    · rw [Nat.cast_sub (Fin.le_iff_val_le_val.mp hab)]
      field_simp
      ring
    · ring
  have hcentroidMem :
      (Finset.Iic a).centroid ℝ v ∈ convexHull ℝ (Set.range v) := by
    -- The uniform centroid weights are nonnegative and sum to one.
    rw [Finset.centroid_def]
    apply affineCombination_mem_convexHull
    · intro i _
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact (Finset.Iic a).sum_centroidWeights_eq_one_of_nonempty ℝ
        ⟨a, Finset.mem_Iic.mpr le_rfl⟩
  have hconvexBounded : Bornology.IsBounded (convexHull ℝ (Set.range v)) :=
    (isBounded_convexHull.mpr (Set.finite_range v).isBounded)
  have hterm (i : Fin (n + 1)) :
      ‖(Finset.Iic a).centroid ℝ v - v i‖ ≤ Metric.diam (Set.range v) := by
    -- Both endpoints lie in the convex hull, whose diameter equals the old mesh.
    simpa only [dist_eq_norm, convexHull_diam] using
      Metric.dist_le_diam_of_mem hconvexBounded hcentroidMem
        (subset_convexHull ℝ (Set.range v) (Set.mem_range_self i))
  have hsumNorm :
      ‖∑ i ∈ Finset.Ioc a b, ((Finset.Iic a).centroid ℝ v - v i)‖ ≤
        ((Finset.Ioc a b).card : ℝ) * Metric.diam (Set.range v) := by
    -- Sum the diameter bound over precisely the newly added vertices.
    calc
      ‖∑ i ∈ Finset.Ioc a b, ((Finset.Iic a).centroid ℝ v - v i)‖ ≤
          ∑ i ∈ Finset.Ioc a b, ‖(Finset.Iic a).centroid ℝ v - v i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.Ioc a b, Metric.diam (Set.range v) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ((Finset.Ioc a b).card : ℝ) * Metric.diam (Set.range v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcardRatio :
      ((Finset.Ioc a b).card : ℝ) / (b.val + 1) ≤
        (n : ℝ) / (n + 1) := by
    have hcardLeB : ((Finset.Ioc a b).card : ℝ) ≤ b.val := by
      simp only [Fin.card_Ioc]
      norm_cast
      omega
    have hbLeN : (b.val : ℝ) ≤ n := by
      norm_cast
      exact Nat.le_of_lt_succ b.isLt
    calc
      ((Finset.Ioc a b).card : ℝ) / (b.val + 1) ≤
          (b.val : ℝ) / (b.val + 1) := by
        exact div_le_div_of_nonneg_right hcardLeB (by positivity)
      _ ≤ (n : ℝ) / (n + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  -- Take norms in the difference identity and use the scalar ratio estimate.
  rw [dist_eq_norm, hidentity, norm_smul, norm_inv, Real.norm_natCast]
  calc
    ((b.val + 1 : ℕ) : ℝ)⁻¹ *
          ‖∑ i ∈ Finset.Ioc a b, ((Finset.Iic a).centroid ℝ v - v i)‖ ≤
        ((b.val + 1 : ℕ) : ℝ)⁻¹ *
          (((Finset.Ioc a b).card : ℝ) * Metric.diam (Set.range v)) := by
      exact mul_le_mul_of_nonneg_left hsumNorm (by positivity)
    _ = (((Finset.Ioc a b).card : ℝ) / (b.val + 1)) *
          Metric.diam (Set.range v) := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) :=
      mul_le_mul_of_nonneg_right hcardRatio Metric.diam_nonneg

/-- Helper for Remark 60.1: any two centroids in a nested initial-interval
chain satisfy the barycentric mesh contraction estimate. -/
lemma dist_centroid_Iic_le_diam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (v : Fin (n + 1) → E) (a b : Fin (n + 1)) :
    dist ((Finset.Iic a).centroid ℝ v) ((Finset.Iic b).centroid ℝ v) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  -- The initial intervals are linearly ordered; reverse the distance if necessary.
  obtain hab | hba := le_total a b
  · exact dist_centroid_Iic_le_diam_of_le n v a b hab
  · rw [dist_comm]
    exact dist_centroid_Iic_le_diam_of_le n v b a hba

/-- Helper for Remark 60.1: one barycentric refinement contracts the diameter
of a finite simplex vertex family by at most `n / (n + 1)`. -/
lemma diam_barycentricVertexFamily_le
    {J : Type*} [Fintype J] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (π : Equiv.Perm (Fin (n + 1))) :
    Metric.diam
        (Set.range (fun k ↦ stdSimplex.affineMapOfVertices v (vertex n π k))) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  classical
  let coe : stdSimplex ℝ J → (J → ℝ) := fun x ↦ x
  let w : Fin (n + 1) → (J → ℝ) := fun r ↦ coe (v (π r))
  have hrangePerm : Set.range (v ∘ π) = Set.range v := by
    -- A permutation only reindexes the old vertex range.
    apply Set.Subset.antisymm
    · rintro _ ⟨r, rfl⟩
      exact Set.mem_range_self (π r)
    · rintro _ ⟨r, rfl⟩
      exact ⟨π⁻¹ r, by simp⟩
  have hwDiam : Metric.diam (Set.range w) = Metric.diam (Set.range v) := by
    -- Coercion is an isometry, while the preceding equality removes reindexing.
    calc
      Metric.diam (Set.range w) =
          Metric.diam (coe '' Set.range (v ∘ π)) := by
        congr 1
        exact Set.range_comp' coe (v ∘ π)
      _ = Metric.diam (Set.range (v ∘ π)) := isometry_subtype_coe.diam_image _
      _ = Metric.diam (Set.range v) := congrArg Metric.diam hrangePerm
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) Metric.diam_nonneg)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  -- Replace refined vertices by their centroid normal forms and apply the generic estimate.
  calc
    dist ((fun k ↦ stdSimplex.affineMapOfVertices v (vertex n π k)) a)
          ((fun k ↦ stdSimplex.affineMapOfVertices v (vertex n π k)) b) =
        dist
          (((stdSimplex.affineMapOfVertices v (vertex n π a) :
              stdSimplex ℝ J) : J → ℝ))
          (((stdSimplex.affineMapOfVertices v (vertex n π b) :
              stdSimplex ℝ J) : J → ℝ)) := Subtype.dist_eq _ _
    _ = dist ((Finset.Iic a).centroid ℝ w)
          ((Finset.Iic b).centroid ℝ w) := by
      exact congrArg₂ dist
        (coe_affineMapOfVertices_vertex_eq_centroid n v π a)
        (coe_affineMapOfVertices_vertex_eq_centroid n v π b)
    _ ≤ ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
      simpa only [hwDiam] using dist_centroid_Iic_le_diam n w a b

/-- Helper for Remark 60.1: the vertex family along a path of iterated
barycentric subsimplices. -/
noncomputable def iteratedVertexFamily (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) →
      Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))
  | 0, _ => stdSimplex.vertex
  | N + 1, p => fun k ↦
      stdSimplex.affineMapOfVertices
        (iteratedVertexFamily n N (Fin.tail p)) (vertex n (p 0) k)

/-- Helper for Remark 60.1: the singular simplex obtained by following a path
of iterated barycentric subsimplices. -/
noncomputable def iteratedSingularSimplex (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) →
      (TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
          (Opposite.op (SimplexCategory.mk n))
  | 0, _ => identitySingularSimplex n
  | N + 1, p =>
      (TopCat.toSSet.map
        (singularMap (TopCat.of (stdSimplex ℝ (Fin (n + 1)))) n
          (iteratedSingularSimplex n N (Fin.tail p)))).app
            (Opposite.op (SimplexCategory.mk n)) (singularSimplex n (p 0))

/-- Helper for Remark 60.1: at iteration rank zero the controlled family is
the standard vertex family. -/
lemma iteratedVertexFamily_zero (n : ℕ)
    (p : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    iteratedVertexFamily n 0 p = stdSimplex.vertex := by
  -- Unfold the base recursion equation without expanding simplex vertices.
  rfl

/-- Helper for Remark 60.1: one successor step refines the tail family using
the first permutation on the path. -/
lemma iteratedVertexFamily_succ (n N : ℕ)
    (p : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    iteratedVertexFamily n (N + 1) p = fun k ↦
      stdSimplex.affineMapOfVertices
        (iteratedVertexFamily n N (Fin.tail p)) (vertex n (p 0) k) := by
  -- Unfold exactly one successor recursion equation.
  rfl

/-- Helper for Remark 60.1: the representative of an iterated singular simplex
is the affine extension of its iterated vertex family. -/
lemma toSSetObjEquiv_iteratedSingularSimplex (n N : ℕ)
    (p : Fin N → Equiv.Perm (Fin (n + 1))) :
    (TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
        (Opposite.op (SimplexCategory.mk n))
          (iteratedSingularSimplex n N p) =
      stdSimplex.affineMapOfVertices (iteratedVertexFamily n N p) := by
  -- Induct in head-tail order, matching one subdivision with one affine composition.
  induction N with
  | zero =>
      rw [iteratedSingularSimplex, toSSetObjEquiv_identitySingularSimplex,
        iteratedVertexFamily_zero,
        stdSimplex.affineMapOfVertices_stdSimplex_vertex]
  | succ N ih =>
      rw [iteratedSingularSimplex, toSSetObjEquiv_map, singularSimplex,
        Equiv.apply_symm_apply, singularMap_hom, ih, continuousMap,
        iteratedVertexFamily_succ,
        stdSimplex.affineMapOfVertices_comp_affineMapOfVertices]

/-- Helper for Remark 60.1: iterated barycentric subdivision is the recursively
composed endomorphism of the integral singular chain complex. -/
noncomputable def chainMapIterate (X : TopCat) :
    ℕ → ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))
  | 0 => 𝟙 _
  | N + 1 => chainMapIterate X N ≫ chainMap X

/-- Helper for Remark 60.1: summing over a tuple of successor length is the
same as summing first over its tail and then over its head. -/
lemma sum_finCons {A M : Type*} [Fintype A] [AddCommMonoid M] (N : ℕ)
    (f : (Fin (N + 1) → A) → M) :
    (∑ p : Fin N → A, ∑ a : A, f (Fin.cons a p)) = ∑ q, f q := by
  classical
  -- Swap the nested sums, combine them into a product, and use `Fin.consEquiv`.
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) ↦ A)) _ _
    (fun _ ↦ rfl)

/-- Helper for Remark 60.1: pushing one new barycentric simplex after an
iterated simplex agrees with pushing their successor path in one step. -/
lemma map_iteratedSingularSimplex_succ (X : TopCat) (n N : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (π : Equiv.Perm (Fin (n + 1)))
    (p : Fin N → Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.map
      (singularMap X n
        ((TopCat.toSSet.map (singularMap X n σ)).app
          (Opposite.op (SimplexCategory.mk n))
            (iteratedSingularSimplex n N p)))).app
        (Opposite.op (SimplexCategory.mk n)) (singularSimplex n π) =
      (TopCat.toSSet.map (singularMap X n σ)).app
        (Opposite.op (SimplexCategory.mk n))
          (iteratedSingularSimplex n (N + 1) (Fin.cons π p)) := by
  -- Expand the successor path and use functoriality of singular-simplex pushforward.
  rw [iteratedSingularSimplex, Fin.tail_cons, Fin.cons_zero, singularMap_map,
    Functor.map_comp, NatTrans.comp_app, CategoryTheory.comp_apply]

/-- Helper for Remark 60.1: an iterated subdivision sends a simplex generator
to the signed sum indexed by its permutation paths. -/
lemma chainMapIterate_generatorExpansion (X : TopCat) (n N : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (chainMapIterate X N).f n =
      ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
        (∏ j : Fin N, ((p j).sign : ℤ)) •
          (TopCat.toSSet.obj X).ιChainComplex
            ((TopCat.toSSet.map (singularMap X n σ)).app
              (Opposite.op (SimplexCategory.mk n))
                (iteratedSingularSimplex n N p)) := by
  classical
  -- Induct on the global subdivision rank while preserving the head-tail indexing.
  induction N with
  | zero =>
      rw [chainMapIterate, HomologicalComplex.id_f, Category.comp_id]
      rw [Fintype.sum_unique]
      rw [Fintype.prod_empty, one_smul, iteratedSingularSimplex,
        map_identitySingularSimplex]
  | succ N ih =>
      let nextSummand :
          (Fin (N + 1) → Equiv.Perm (Fin (n + 1))) →
            (ModuleCat.of ℤ ℤ ⟶
              ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n) :=
        fun q ↦
          (∏ j : Fin (N + 1), ((q j).sign : ℤ)) •
            (TopCat.toSSet.obj X).ιChainComplex
              ((TopCat.toSSet.map (singularMap X n σ)).app
                (Opposite.op (SimplexCategory.mk n))
                  (iteratedSingularSimplex n (N + 1) q))
      calc
        (TopCat.toSSet.obj X).ιChainComplex σ ≫
              (chainMapIterate X (N + 1)).f n =
            (∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
                (∏ j : Fin N, ((p j).sign : ℤ)) •
                  (TopCat.toSSet.obj X).ιChainComplex
                    ((TopCat.toSSet.map (singularMap X n σ)).app
                      (Opposite.op (SimplexCategory.mk n))
                        (iteratedSingularSimplex n N p))) ≫
              (chainMap X).f n := by
          rw [chainMapIterate, HomologicalComplex.comp_f, ← Category.assoc, ih]
        _ = ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
              (∏ j : Fin N, ((p j).sign : ℤ)) •
                ((TopCat.toSSet.obj X).ιChainComplex
                    ((TopCat.toSSet.map (singularMap X n σ)).app
                      (Opposite.op (SimplexCategory.mk n))
                        (iteratedSingularSimplex n N p)) ≫
                  (chainMap X).f n) := by
          rw [Preadditive.sum_comp]
          apply Finset.sum_congr rfl
          intro p _
          rw [Preadditive.zsmul_comp]
        _ = ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
              (∏ j : Fin N, ((p j).sign : ℤ)) •
                simplexChain X n
                  ((TopCat.toSSet.map (singularMap X n σ)).app
                    (Opposite.op (SimplexCategory.mk n))
                      (iteratedSingularSimplex n N p)) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [ι_chainMap]
        _ = ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
              (∏ j : Fin N, ((p j).sign : ℤ)) •
                (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
                  (TopCat.toSSet.obj X).ιChainComplex
                    ((TopCat.toSSet.map
                      (singularMap X n
                        ((TopCat.toSSet.map (singularMap X n σ)).app
                          (Opposite.op (SimplexCategory.mk n))
                            (iteratedSingularSimplex n N p)))).app
                      (Opposite.op (SimplexCategory.mk n))
                        (singularSimplex n π))) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [simplexChain_eq_sum]
        _ = ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
              ∑ π : Equiv.Perm (Fin (n + 1)),
                (∏ j : Fin N, ((p j).sign : ℤ)) •
                  ((π.sign : ℤ) •
                    (TopCat.toSSet.obj X).ιChainComplex
                      ((TopCat.toSSet.map
                        (singularMap X n
                          ((TopCat.toSSet.map (singularMap X n σ)).app
                            (Opposite.op (SimplexCategory.mk n))
                              (iteratedSingularSimplex n N p)))).app
                        (Opposite.op (SimplexCategory.mk n))
                          (singularSimplex n π))) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.smul_sum]
        _ = ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
              ∑ π : Equiv.Perm (Fin (n + 1)), nextSummand (Fin.cons π p) := by
          dsimp only [nextSummand]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro π _
          rw [smul_smul, map_iteratedSingularSimplex_succ,
            Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm]
        _ = ∑ q : Fin (N + 1) → Equiv.Perm (Fin (n + 1)), nextSummand q :=
          sum_finCons N nextSummand

/-- Helper for Remark 60.1: the initial iterated vertex family has mesh at most
the diameter of the standard simplex. -/
lemma diam_iteratedVertexFamily_zero_le (n : ℕ)
    (p : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (iteratedVertexFamily n 0 p)) ≤ 1 := by
  -- Rewrite the recursion base and apply the uniform simplex-diameter bound.
  rw [iteratedVertexFamily_zero]
  exact stdSimplex.diam_range_le_one stdSimplex.vertex

/-- Helper for Remark 60.1: a successor iterated family has no larger mesh than
the family at the tail of its permutation path. -/
lemma diam_iteratedVertexFamily_succ_le (n N : ℕ)
    (p : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (iteratedVertexFamily n (N + 1) p)) ≤
      Metric.diam (Set.range (iteratedVertexFamily n N (Fin.tail p))) := by
  -- Expose one recursive refinement and apply the generator-independent mesh bound.
  rw [iteratedVertexFamily_succ]
  exact diam_barycentricVertexFamily_le_diam n
    (iteratedVertexFamily n N (Fin.tail p)) (p 0)

/-- Helper for Remark 60.1: one successor iteration multiplies the old mesh by
at most the barycentric contraction factor. -/
lemma diam_iteratedVertexFamily_succ_le_mul (n N : ℕ)
    (p : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (iteratedVertexFamily n (N + 1) p)) ≤
      ((n : ℝ) / (n + 1)) *
        Metric.diam (Set.range (iteratedVertexFamily n N (Fin.tail p))) := by
  -- Expose one recursive refinement and invoke the quantitative mesh estimate.
  rw [iteratedVertexFamily_succ]
  exact diam_barycentricVertexFamily_le n
    (iteratedVertexFamily n N (Fin.tail p)) (p 0)

/-- Helper for Remark 60.1: every iterated barycentric vertex family remains
inside the unit mesh bound of the original standard simplex. -/
lemma diam_iteratedVertexFamily_le_one (n N : ℕ)
    (p : Fin N → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (iteratedVertexFamily n N p)) ≤ 1 := by
  -- Induct on the rank, using mesh monotonicity at each successor step.
  induction N with
  | zero => exact diam_iteratedVertexFamily_zero_le n p
  | succ N ih =>
      exact (diam_iteratedVertexFamily_succ_le n N p).trans (ih (Fin.tail p))

/-- Helper for Remark 60.1: after `N` barycentric refinements, every indexed
subsimplex has mesh at most `(n / (n + 1)) ^ N`. -/
lemma diam_iteratedVertexFamily_le (n N : ℕ)
    (p : Fin N → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (iteratedVertexFamily n N p)) ≤
      ((n : ℝ) / (n + 1)) ^ N := by
  -- Induct on the global refinement rank, multiplying the one-step estimate.
  induction N with
  | zero =>
      simpa only [pow_zero] using diam_iteratedVertexFamily_zero_le n p
  | succ N ih =>
      calc
        Metric.diam (Set.range (iteratedVertexFamily n (N + 1) p)) ≤
            ((n : ℝ) / (n + 1)) *
              Metric.diam (Set.range (iteratedVertexFamily n N (Fin.tail p))) :=
          diam_iteratedVertexFamily_succ_le_mul n N p
        _ ≤ ((n : ℝ) / (n + 1)) * ((n : ℝ) / (n + 1)) ^ N := by
          exact mul_le_mul_of_nonneg_left (ih (Fin.tail p))
            (div_nonneg (Nat.cast_nonneg _) (by positivity))
        _ = ((n : ℝ) / (n + 1)) ^ (N + 1) := by
          rw [pow_succ']

/-- Helper for Remark 60.1: an open cover pulled back to a standard simplex has
a positive metric Lebesgue number. -/
lemma exists_lebesgueNumber_comap_stdSimplex
    {X ι : Type*} [TopologicalSpace X] (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ δ > 0, ∀ x, ∃ i,
      Metric.ball x δ ⊆
        ((𝒰 i).comap σ : Set (stdSimplex ℝ (Fin (n + 1)))) := by
  let pulledCover : ι →
      TopologicalSpace.Opens (stdSimplex ℝ (Fin (n + 1))) :=
    fun i ↦ (𝒰 i).comap σ
  have hpulled : TopologicalSpace.IsOpenCover pulledCover := by
    -- Pulling the cover back along the simplex representative still covers its domain.
    exact h𝒰.comap σ
  have hpulledUnion :
      Set.univ ⊆ ⋃ i, (pulledCover i : Set (stdSimplex ℝ (Fin (n + 1)))) := by
    -- Re-express the lattice-valued cover condition as pointwise set membership.
    intro x _
    obtain ⟨i, hi⟩ := hpulled.exists_mem x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- Apply the metric Lebesgue-number lemma to this open pulled-back cover.
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ
      (fun i ↦ (pulledCover i).2) hpulledUnion
  exact ⟨δ, hδ, fun x ↦ hball x (Set.mem_univ x)⟩

/-- Helper for Remark 60.1: the barycentric mesh contraction factor eventually
has any prescribed positive upper bound. -/
lemma exists_barycentricMeshPower_lt (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ((n : ℝ) / (n + 1)) ^ N < δ := by
  have hfactorLt : (n : ℝ) / (n + 1) < 1 := by
    -- The barycentric mesh factor is strictly below one in every dimension.
    rw [div_lt_one (by positivity)]
    norm_num
  exact exists_pow_lt_of_lt_one hδ hfactorLt

/-- Helper for Remark 60.1: after sufficiently many barycentric refinements,
every iterated affine subsimplex of a fixed simplex map lies in one member of
an open cover. -/
lemma exists_iteratedSubsimplex_range_subset
    {X ι : Type*} [TopologicalSpace X] (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N, ∀ p : Fin N → Equiv.Perm (Fin (n + 1)), ∃ i,
      Set.range
          (σ.comp
            (stdSimplex.affineMapOfVertices (iteratedVertexFamily n N p))) ⊆
        𝒰 i := by
  obtain ⟨δ, hδ, hball⟩ :=
    exists_lebesgueNumber_comap_stdSimplex n 𝒰 h𝒰 σ
  obtain ⟨N, hN⟩ := exists_barycentricMeshPower_lt n hδ
  refine ⟨N, fun p ↦ ?_⟩
  let v := iteratedVertexFamily n N p
  let a := stdSimplex.affineMapOfVertices v
  let x₀ := a (stdSimplex.vertex (0 : Fin (n + 1)))
  obtain ⟨i, hi⟩ := hball x₀
  refine ⟨i, ?_⟩
  have hvertexDiam : Metric.diam (Set.range v) < δ :=
    (diam_iteratedVertexFamily_le n N p).trans_lt hN
  have hsmall : Set.range a ⊆ Metric.ball x₀ δ :=
    stdSimplex.range_affineMapOfVertices_subset_ball v
      (stdSimplex.vertex (0 : Fin (n + 1))) hvertexDiam
  rintro _ ⟨x, rfl⟩
  -- The geometric ball containment is precisely what the Lebesgue number consumes.
  exact hi (hsmall (Set.mem_range_self x))

/-- Helper for Remark 60.1: beyond one global rank, every iterated affine
subsimplex of a fixed singular simplex lies in one member of an open cover. -/
lemma exists_forall_ge_iteratedSubsimplex_range_subset
    {X ι : Type*} [TopologicalSpace X] (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N, ∀ M, N ≤ M →
      ∀ p : Fin M → Equiv.Perm (Fin (n + 1)), ∃ i,
        Set.range
            (σ.comp
              (stdSimplex.affineMapOfVertices (iteratedVertexFamily n M p))) ⊆
          𝒰 i := by
  obtain ⟨δ, hδ, hball⟩ :=
    exists_lebesgueNumber_comap_stdSimplex n 𝒰 h𝒰 σ
  obtain ⟨N, hN⟩ := exists_barycentricMeshPower_lt n hδ
  have hfactorNonnegative : 0 ≤ (n : ℝ) / (n + 1) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hfactorLeOne : (n : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  refine ⟨N, fun M hNM p ↦ ?_⟩
  let v := iteratedVertexFamily n M p
  let a := stdSimplex.affineMapOfVertices v
  let x₀ := a (stdSimplex.vertex (0 : Fin (n + 1)))
  obtain ⟨i, hi⟩ := hball x₀
  refine ⟨i, ?_⟩
  have hpower : ((n : ℝ) / (n + 1)) ^ M ≤
      ((n : ℝ) / (n + 1)) ^ N :=
    pow_le_pow_of_le_one hfactorNonnegative hfactorLeOne hNM
  have hvertexDiam : Metric.diam (Set.range v) < δ :=
    (diam_iteratedVertexFamily_le n M p).trans_lt (hpower.trans_lt hN)
  have hsmall : Set.range a ⊆ Metric.ball x₀ δ :=
    stdSimplex.range_affineMapOfVertices_subset_ball v
      (stdSimplex.vertex (0 : Fin (n + 1))) hvertexDiam
  rintro _ ⟨x, rfl⟩
  -- The common Lebesgue ball works uniformly at every later subdivision rank.
  exact hi (hsmall (Set.mem_range_self x))

/-- Helper for Remark 60.1: after sufficiently many barycentric subdivisions,
the chain of a singular-simplex generator lifts through the cover-small chain
inclusion. -/
lemma exists_chainMapIterate_generator_smallLift
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ N, ∃ c : ModuleCat.of ℤ ℤ ⟶
        ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).X n,
      c ≫ (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (chainMapIterate X N).f n := by
  let represented :=
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ
  obtain ⟨N, hN⟩ :=
    exists_iteratedSubsimplex_range_subset n 𝒰 h𝒰 represented
  let τ (p : Fin N → Equiv.Perm (Fin (n + 1))) :=
    (TopCat.toSSet.map (singularMap X n σ)).app
      (Opposite.op (SimplexCategory.mk n))
        (iteratedSingularSimplex n N p)
  have hτ (p : Fin N → Equiv.Perm (Fin (n + 1))) :
      τ p ∈ (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) := by
    -- The geometric range estimate is exactly the small-subcomplex criterion.
    rw [AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset]
    obtain ⟨i, hi⟩ := hN p
    refine ⟨i, ?_⟩
    rw [AlgebraicTopology.toSSetObjEquiv_map, singularMap_hom,
      toSSetObjEquiv_iteratedSingularSimplex]
    simpa only [represented] using hi
  let τsmall (p : Fin N → Equiv.Perm (Fin (n + 1))) :
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) :=
    ⟨τ p, hτ p⟩
  let c : ModuleCat.of ℤ ℤ ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
    ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
      (∏ j : Fin N, ((p j).sign : ℤ)) •
        (AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).ιChainComplex (τsmall p)
  refine ⟨N, c, ?_⟩
  -- Expand both sides over the same permutation paths and compare generators.
  dsimp only [c]
  rw [chainMapIterate_generatorExpansion, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  rw [Preadditive.zsmul_comp,
    AlgebraicTopology.integralSmallSingularChainInclusion_ι]

/-- Helper for Remark 60.1: after one rank, every later subdivision of a
singular-simplex generator lifts through the cover-small chain inclusion. -/
lemma exists_forall_ge_chainMapIterate_generator_smallLift
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ N, ∀ M, N ≤ M →
      ∃ c : ModuleCat.of ℤ ℤ ⟶
          ((AlgebraicTopology.smallSingularSubcomplex X
            (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
              (ModuleCat.of ℤ ℤ)).X n,
        c ≫ (AlgebraicTopology.integralSmallSingularChainInclusion X
            (fun i ↦ (𝒰 i : Set X))).f n =
          (TopCat.toSSet.obj X).ιChainComplex σ ≫
            (chainMapIterate X M).f n := by
  let represented :=
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ
  obtain ⟨N, hN⟩ :=
    exists_forall_ge_iteratedSubsimplex_range_subset n 𝒰 h𝒰 represented
  refine ⟨N, fun M hNM ↦ ?_⟩
  let τ (p : Fin M → Equiv.Perm (Fin (n + 1))) :=
    (TopCat.toSSet.map (singularMap X n σ)).app
      (Opposite.op (SimplexCategory.mk n))
        (iteratedSingularSimplex n M p)
  have hτ (p : Fin M → Equiv.Perm (Fin (n + 1))) :
      τ p ∈ (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) := by
    -- Use the uniform range estimate at this later subdivision rank.
    rw [AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset]
    obtain ⟨i, hi⟩ := hN M hNM p
    refine ⟨i, ?_⟩
    rw [AlgebraicTopology.toSSetObjEquiv_map, singularMap_hom,
      toSSetObjEquiv_iteratedSingularSimplex]
    simpa only [represented] using hi
  let τsmall (p : Fin M → Equiv.Perm (Fin (n + 1))) :
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) :=
    ⟨τ p, hτ p⟩
  let c : ModuleCat.of ℤ ℤ ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
    ∑ p : Fin M → Equiv.Perm (Fin (n + 1)),
      (∏ j : Fin M, ((p j).sign : ℤ)) •
        (AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).ιChainComplex (τsmall p)
  refine ⟨c, ?_⟩
  -- Compare the lifted and ambient permutation-path expansions term by term.
  dsimp only [c]
  rw [chainMapIterate_generatorExpansion, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  rw [Preadditive.zsmul_comp,
    AlgebraicTopology.integralSmallSingularChainInclusion_ι]

/-- Helper for Remark 60.1: every iterated barycentric subsimplex has image
contained in the image of its original singular simplex. -/
lemma range_iteratedSubsimplex_subset_range
    (X : TopCat) (n N : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (p : Fin N → Equiv.Perm (Fin (n + 1))) :
    Set.range
        (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))
          ((TopCat.toSSet.map (singularMap X n σ)).app
            (Opposite.op (SimplexCategory.mk n))
              (iteratedSingularSimplex n N p))) ⊆
      Set.range
        (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ) := by
  -- The represented iterated simplex factors through the represented original simplex.
  rw [AlgebraicTopology.toSSetObjEquiv_map, singularMap_hom,
    toSSetObjEquiv_iteratedSingularSimplex]
  rintro _ ⟨x, rfl⟩
  exact ⟨stdSimplex.affineMapOfVertices (iteratedVertexFamily n N p) x, rfl⟩

/-- Helper for Remark 60.1: every iterate of barycentric subdivision of an
already cover-small simplex generator lifts through the cover-small chain
inclusion. -/
lemma chainMapIterate_generator_smallLift_of_mem
    {X : TopCat} {ι : Type} (n N : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hσ : σ ∈ (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X))).obj
        (Opposite.op (SimplexCategory.mk n))) :
    ∃ c : ModuleCat.of ℤ ℤ ⟶
        ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).X n,
      c ≫ (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (chainMapIterate X N).f n := by
  obtain ⟨i, hi⟩ :=
    (AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset
      X (fun i ↦ (𝒰 i : Set X)) _ σ).mp hσ
  let τ (p : Fin N → Equiv.Perm (Fin (n + 1))) :=
    (TopCat.toSSet.map (singularMap X n σ)).app
      (Opposite.op (SimplexCategory.mk n))
        (iteratedSingularSimplex n N p)
  have hτ (p : Fin N → Equiv.Perm (Fin (n + 1))) :
      τ p ∈ (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) := by
    -- Image containment preserves membership in the same cover element.
    rw [AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset]
    exact ⟨i, (range_iteratedSubsimplex_subset_range X n N σ p).trans hi⟩
  let τsmall (p : Fin N → Equiv.Perm (Fin (n + 1))) :
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X))).obj
          (Opposite.op (SimplexCategory.mk n)) :=
    ⟨τ p, hτ p⟩
  let c : ModuleCat.of ℤ ℤ ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
    ∑ p : Fin N → Equiv.Perm (Fin (n + 1)),
      (∏ j : Fin N, ((p j).sign : ℤ)) •
        (AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).ιChainComplex (τsmall p)
  refine ⟨c, ?_⟩
  -- The generator expansion and the lifted expansion have identical coefficients.
  dsimp only [c]
  rw [chainMapIterate_generatorExpansion, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  rw [Preadditive.zsmul_comp,
    AlgebraicTopology.integralSmallSingularChainInclusion_ι]

/-- Helper for Remark 60.1: barycentric subdivision induces the identity on
integral singular homology. -/
lemma homologyMap_chainMap_eq_id (X : TopCat) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap X) n =
      𝟙 (((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).homology n) := by
  -- The prism operator identifies subdivision with the identity chain map.
  simpa only [HomologicalComplex.homologyMap_id] using
    (chainMapHomotopyIdentity X).homologyMap_eq n

/-- Helper for Remark 60.1: every iterated barycentric subdivision induces the
identity on integral singular homology. -/
lemma homologyMap_chainMapIterate_eq_id (X : TopCat) (n N : ℕ) :
    HomologicalComplex.homologyMap (chainMapIterate X N) n =
      𝟙 (((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).homology n) := by
  -- Induct through the composite, using the one-step prism homotopy each time.
  induction N with
  | zero =>
      rw [chainMapIterate, HomologicalComplex.homologyMap_id]
  | succ N ih =>
      rw [chainMapIterate, HomologicalComplex.homologyMap_comp, ih,
        homologyMap_chainMap_eq_id, Category.comp_id]

/-- Helper for Remark 60.1: the singular simplices obtained by postcomposing
through a cover-small simplex remain in the cover-small subcomplex. -/
lemma range_singularMap_le_smallSingularSubcomplex
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hσ : σ ∈ (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X))).obj
        (Opposite.op (SimplexCategory.mk n))) :
    SSet.Subcomplex.range (TopCat.toSSet.map (singularMap X n σ)) ≤
      AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) := by
  -- Every simplex in the range factors through the represented map of `σ`.
  intro m τ hτ
  obtain ⟨ρ, rfl⟩ := hτ
  rw [AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset]
  obtain ⟨i, hi⟩ :=
    (AlgebraicTopology.mem_smallSingularSubcomplex_iff_range_subset
      X (fun i ↦ (𝒰 i : Set X)) _ σ).mp hσ
  refine ⟨i, ?_⟩
  rw [AlgebraicTopology.toSSetObjEquiv_map, singularMap_hom]
  rintro _ ⟨x, rfl⟩
  exact hi ⟨_, rfl⟩

/-- Helper for Remark 60.1: the represented map of a cover-small simplex,
factored through the cover-small singular subcomplex. -/
noncomputable def singularMapToSmallSingularSubcomplex
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1)))) ⟶
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularMap X n σ.1))
    (range_singularMap_le_smallSingularSubcomplex n 𝒰 σ.1 σ.2)

/-- Helper for Remark 60.1: forgetting the small-subcomplex factorization of a
represented simplex recovers its original singular map. -/
lemma singularMapToSmallSingularSubcomplex_comp_inclusion
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    singularMapToSmallSingularSubcomplex n 𝒰 σ ≫
        (AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X))).ι =
      TopCat.toSSet.map (singularMap X n σ.1) := by
  -- This is the defining factorization equation of `Subcomplex.lift`.
  exact SSet.Subcomplex.lift_ι _ _

/-- Helper for Remark 60.1: the universal prism of a cover-small simplex,
regarded as a chain in the cover-small subcomplex. -/
noncomputable def smallSimplexPrism
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1) :=
  standardPrismChain n ≫
    (SSet.chainComplexMap
      (singularMapToSmallSingularSubcomplex n 𝒰 σ)
      (ModuleCat.of ℤ ℤ)).f (n + 1)

/-- Helper for Remark 60.1: inclusion carries the cover-small simplex prism to
the ambient simplex prism. -/
lemma smallSimplexPrism_comp_inclusion
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    smallSimplexPrism n 𝒰 σ ≫
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f (n + 1) =
      simplexPrism X n σ.1 := by
  -- Functoriality of simplicial chains removes the intermediate subcomplex.
  unfold smallSimplexPrism simplexPrism
  rw [Category.assoc, integralChainComplexMap_f_comp,
    singularMapToSmallSingularSubcomplex_comp_inclusion]

/-- Helper for Remark 60.1: extend the cover-small simplex prisms linearly over
all cover-small chains in one degree. -/
noncomputable def smallPrismComponent
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).X n ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X (n + 1) :=
  CategoryTheory.Limits.Cofan.IsColimit.desc
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) n)
      (fun σ ↦ smallSimplexPrism n 𝒰 σ)

/-- Helper for Remark 60.1: the cover-small prism component has the prescribed
value on every cover-small simplex generator. -/
lemma ι_smallPrismComponent
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).ιChainComplex σ ≫
        smallPrismComponent 𝒰 n =
      smallSimplexPrism n 𝒰 σ := by
  -- Apply the coproduct factorization rule defining the component.
  exact CategoryTheory.Limits.Cofan.IsColimit.fac
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) n)
      (fun τ ↦ smallSimplexPrism n 𝒰 τ) σ

/-- Helper for Remark 60.1: the cover-small prism component commutes with
inclusion into ambient chains. -/
lemma smallPrismComponent_comp_inclusion
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    smallPrismComponent 𝒰 n ≫
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f (n + 1) =
      (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n ≫
        prismComponent X n := by
  -- Check the naturality square on the free generators of small chains.
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallPrismComponent,
    smallSimplexPrism_comp_inclusion]
  rw [← Category.assoc,
    AlgebraicTopology.integralSmallSingularChainInclusion_ι,
    ι_prismComponent]

/-- Helper for Remark 60.1: the barycentric subdivision of one cover-small
simplex, lifted to the cover-small chain complex. -/
noncomputable def smallSimplexSubdivision
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  (chainMapIterate_generator_smallLift_of_mem n 1 𝒰 σ.1 σ.2).choose

/-- Helper for Remark 60.1: inclusion sends the lifted small-simplex
subdivision to its ambient barycentric subdivision. -/
lemma smallSimplexSubdivision_comp_inclusion
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    smallSimplexSubdivision n 𝒰 σ ≫
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ.1 ≫ (chainMap X).f n := by
  -- Specialize the established iterated lift to one subdivision step.
  simpa only [smallSimplexSubdivision, chainMapIterate,
    HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.id_comp] using
      (chainMapIterate_generator_smallLift_of_mem n 1 𝒰 σ.1 σ.2).choose_spec

/-- Helper for Remark 60.1: barycentric subdivision on the cover-small chain
module in one degree. -/
noncomputable def smallSubdivisionComponent
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).X n ⟶
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  CategoryTheory.Limits.Cofan.IsColimit.desc
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) n)
      (fun σ ↦ smallSimplexSubdivision n 𝒰 σ)

/-- Helper for Remark 60.1: cover-small subdivision has its defining value on
each cover-small simplex generator. -/
lemma ι_smallSubdivisionComponent
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ)
    (σ : (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).obj
        (Opposite.op (SimplexCategory.mk n))) :
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).ιChainComplex σ ≫
        smallSubdivisionComponent 𝒰 n =
      smallSimplexSubdivision n 𝒰 σ := by
  -- Apply the coproduct factorization rule defining small subdivision.
  exact CategoryTheory.Limits.Cofan.IsColimit.fac
    ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).isColimitChainComplexXCofan
        (ModuleCat.of ℤ ℤ) n)
      (fun τ ↦ smallSimplexSubdivision n 𝒰 τ) σ

/-- Helper for Remark 60.1: cover-small subdivision commutes with inclusion
into the ambient singular chains. -/
lemma smallSubdivisionComponent_comp_inclusion
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    smallSubdivisionComponent 𝒰 n ≫
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n =
      (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))).f n ≫
        (chainMap X).f n := by
  -- Check the square on each free small-simplex generator.
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSubdivisionComponent,
    smallSimplexSubdivision_comp_inclusion]
  rw [← Category.assoc,
    AlgebraicTopology.integralSmallSingularChainInclusion_ι]

/-- Helper for Remark 60.1: cover-small subdivision commutes with the singular
boundary operator. -/
lemma smallSubdivisionComponent_comp_d
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    smallSubdivisionComponent 𝒰 (n + 1) ≫
        ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
        smallSubdivisionComponent 𝒰 n := by
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  letI : Mono (ιsmall.f n) :=
    (ModuleCat.mono_iff_injective _).mpr
      (AlgebraicTopology.integralSmallSingularChainInclusion_injective
        X (fun i ↦ (𝒰 i : Set X)) n)
  -- Cancel the injective inclusion and use the ambient chain-map square.
  rw [← cancel_mono (ιsmall.f n)]
  calc
    (smallSubdivisionComponent 𝒰 (n + 1) ≫ _ ) ≫ ιsmall.f n =
        smallSubdivisionComponent 𝒰 (n + 1) ≫
          (ιsmall.f (n + 1) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 1) n) := by
      rw [Category.assoc, ιsmall.comm]
    _ = (smallSubdivisionComponent 𝒰 (n + 1) ≫
          ιsmall.f (n + 1)) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 1) n :=
      (Category.assoc _ _ _).symm
    _ = (ιsmall.f (n + 1) ≫ (chainMap X).f (n + 1)) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n := by
      rw [smallSubdivisionComponent_comp_inclusion]
    _ = ιsmall.f (n + 1) ≫
          ((chainMap X).f (n + 1) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 1) n) :=
      Category.assoc _ _ _
    _ = ιsmall.f (n + 1) ≫
          (((TopCat.toSSet.obj X).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
            (chainMap X).f n) := by
      rw [(chainMap X).comm]
    _ = (ιsmall.f (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n) ≫
          (chainMap X).f n := (Category.assoc _ _ _).symm
    _ = (((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ ιsmall.f n) ≫
          (chainMap X).f n := by
      rw [ιsmall.comm]
    _ = ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
          (ιsmall.f n ≫ (chainMap X).f n) := Category.assoc _ _ _
    _ = ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
          (smallSubdivisionComponent 𝒰 n ≫ ιsmall.f n) := by
      rw [smallSubdivisionComponent_comp_inclusion]
    _ = (_ ≫ smallSubdivisionComponent 𝒰 n) ≫ ιsmall.f n :=
      (Category.assoc _ _ _).symm

/-- Helper for Remark 60.1: barycentric subdivision defines an endomorphism of
the cover-small singular chain complex. -/
noncomputable def smallSubdivisionChainMap
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
        (ModuleCat.of ℤ ℤ) ⟶
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ) :=
  ChainComplex.ofHom (fun n ↦ smallSubdivisionComponent 𝒰 n)
    (fun n ↦ smallSubdivisionComponent_comp_d 𝒰 n)

/-- Helper for Remark 60.1: the cover-small subdivision chain map followed by
inclusion equals inclusion followed by ambient subdivision. -/
lemma smallSubdivisionChainMap_comp_inclusion
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    smallSubdivisionChainMap 𝒰 ≫
        AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X)) =
      AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X)) ≫ chainMap X := by
  -- The degreewise comparison already proved determines the chain map.
  ext n x
  exact CategoryTheory.congr_fun
    (smallSubdivisionComponent_comp_inclusion 𝒰 n) x

/-- Helper for Remark 60.1: cover-small barycentric subdivision is the identity
in degree zero. -/
lemma smallSubdivisionComponent_zero
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    smallSubdivisionComponent 𝒰 0 = 𝟙 _ := by
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  letI : Mono (ιsmall.f 0) :=
    (ModuleCat.mono_iff_injective _).mpr
      (AlgebraicTopology.integralSmallSingularChainInclusion_injective
        X (fun i ↦ (𝒰 i : Set X)) 0)
  -- Cancel inclusion and use the ambient degree-zero subdivision computation.
  rw [← cancel_mono (ιsmall.f 0)]
  calc
    smallSubdivisionComponent 𝒰 0 ≫ ιsmall.f 0 =
        ιsmall.f 0 ≫ (chainMap X).f 0 :=
      smallSubdivisionComponent_comp_inclusion 𝒰 0
    _ = ιsmall.f 0 ≫
        ((𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)) :
          (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ) ⟶
            (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ))).f 0 := by
      rw [chainMap_zero]
    _ = ιsmall.f 0 := by
      rw [HomologicalComplex.id_f, Category.comp_id]
    _ = 𝟙 _ ≫ ιsmall.f 0 := by rw [Category.id_comp]

/-- Helper for Remark 60.1: the restricted degree-zero prism component
vanishes. -/
lemma smallPrismComponent_zero
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    smallPrismComponent 𝒰 0 = 0 := by
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  letI : Mono (ιsmall.f 1) :=
    (ModuleCat.mono_iff_injective _).mpr
      (AlgebraicTopology.integralSmallSingularChainInclusion_injective
        X (fun i ↦ (𝒰 i : Set X)) 1)
  -- Inclusion identifies this component with the vanishing ambient prism.
  rw [← cancel_mono (ιsmall.f 1)]
  rw [smallPrismComponent_comp_inclusion, prismComponent_zero,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

/-- Helper for Remark 60.1: the restricted prism gives the successor-degree
homotopy equation between cover-small subdivision and the identity. -/
lemma smallPrismComponent_homotopy
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    smallSubdivisionComponent 𝒰 (n + 1) =
      ((AlgebraicTopology.smallSingularSubcomplex X
          (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ smallPrismComponent 𝒰 n +
        smallPrismComponent 𝒰 (n + 1) ≫
          ((AlgebraicTopology.smallSingularSubcomplex X
            (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
              (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) + 𝟙 _ := by
  let Csmall :=
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex (ModuleCat.of ℤ ℤ)
  let Cambient :=
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  letI : Mono (ιsmall.f (n + 1)) :=
    (ModuleCat.mono_iff_injective _).mpr
      (AlgebraicTopology.integralSmallSingularChainInclusion_injective
        X (fun i ↦ (𝒰 i : Set X)) (n + 1))
  have hambient := prismComponent_homotopy_of_standardPrismBoundary X n
    (standardPrismChain_boundary n)
  -- Cancel inclusion, then transport the ambient prism equation term by term.
  rw [← cancel_mono (ιsmall.f (n + 1))]
  calc
    smallSubdivisionComponent 𝒰 (n + 1) ≫ ιsmall.f (n + 1) =
        ιsmall.f (n + 1) ≫ (chainMap X).f (n + 1) :=
      smallSubdivisionComponent_comp_inclusion 𝒰 (n + 1)
    _ = ιsmall.f (n + 1) ≫
        (Cambient.d (n + 1) n ≫ prismComponent X n +
          prismComponent X (n + 1) ≫ Cambient.d (n + 2) (n + 1) +
          ((𝟙 Cambient : Cambient ⟶ Cambient).f (n + 1))) :=
      congrArg (fun g ↦ ιsmall.f (n + 1) ≫ g) hambient
    _ = (Csmall.d (n + 1) n ≫ smallPrismComponent 𝒰 n +
          smallPrismComponent 𝒰 (n + 1) ≫ Csmall.d (n + 2) (n + 1) +
          𝟙 _) ≫ ιsmall.f (n + 1) := by
      have hfirst :
          ιsmall.f (n + 1) ≫
              (Cambient.d (n + 1) n ≫ prismComponent X n) =
            (Csmall.d (n + 1) n ≫ smallPrismComponent 𝒰 n) ≫
              ιsmall.f (n + 1) := by
        calc
          ιsmall.f (n + 1) ≫
              (Cambient.d (n + 1) n ≫ prismComponent X n) =
            (ιsmall.f (n + 1) ≫ Cambient.d (n + 1) n) ≫
              prismComponent X n := (Category.assoc _ _ _).symm
          _ = (Csmall.d (n + 1) n ≫ ιsmall.f n) ≫
              prismComponent X n :=
            congrArg (fun q ↦ q ≫ prismComponent X n)
              (ιsmall.comm (n + 1) n)
          _ = Csmall.d (n + 1) n ≫
              (ιsmall.f n ≫ prismComponent X n) := Category.assoc _ _ _
          _ = Csmall.d (n + 1) n ≫
              (smallPrismComponent 𝒰 n ≫ ιsmall.f (n + 1)) :=
            congrArg (fun q ↦ Csmall.d (n + 1) n ≫ q)
              (smallPrismComponent_comp_inclusion 𝒰 n).symm
          _ = (Csmall.d (n + 1) n ≫ smallPrismComponent 𝒰 n) ≫
              ιsmall.f (n + 1) := (Category.assoc _ _ _).symm
      have hsecond :
          ιsmall.f (n + 1) ≫
              (prismComponent X (n + 1) ≫
                Cambient.d (n + 2) (n + 1)) =
            (smallPrismComponent 𝒰 (n + 1) ≫
              Csmall.d (n + 2) (n + 1)) ≫ ιsmall.f (n + 1) := by
        calc
          ιsmall.f (n + 1) ≫
              (prismComponent X (n + 1) ≫
                Cambient.d (n + 2) (n + 1)) =
            (ιsmall.f (n + 1) ≫ prismComponent X (n + 1)) ≫
              Cambient.d (n + 2) (n + 1) := (Category.assoc _ _ _).symm
          _ = (smallPrismComponent 𝒰 (n + 1) ≫ ιsmall.f (n + 2)) ≫
              Cambient.d (n + 2) (n + 1) :=
            congrArg (fun q ↦ q ≫ Cambient.d (n + 2) (n + 1))
              (smallPrismComponent_comp_inclusion 𝒰 (n + 1)).symm
          _ = smallPrismComponent 𝒰 (n + 1) ≫
              (ιsmall.f (n + 2) ≫ Cambient.d (n + 2) (n + 1)) :=
            Category.assoc _ _ _
          _ = smallPrismComponent 𝒰 (n + 1) ≫
              (Csmall.d (n + 2) (n + 1) ≫ ιsmall.f (n + 1)) :=
            congrArg (fun q ↦ smallPrismComponent 𝒰 (n + 1) ≫ q)
              (ιsmall.comm (n + 2) (n + 1))
          _ = (smallPrismComponent 𝒰 (n + 1) ≫
              Csmall.d (n + 2) (n + 1)) ≫ ιsmall.f (n + 1) :=
            (Category.assoc _ _ _).symm
      have hid :
          ιsmall.f (n + 1) ≫
              ((𝟙 Cambient : Cambient ⟶ Cambient).f (n + 1)) =
            ((𝟙 Csmall : Csmall ⟶ Csmall).f (n + 1)) ≫
              ιsmall.f (n + 1) := by
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      rw [Preadditive.comp_add, Preadditive.comp_add,
        Preadditive.add_comp, Preadditive.add_comp]
      exact congrArg₂ (· + ·) (congrArg₂ (· + ·) hfirst hsecond) hid

/-- Helper for Remark 60.1: place each restricted prism map in its adjacent
target degree and use zero elsewhere. -/
noncomputable def smallPrismHomotopyComponent
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    ∀ i j : ℕ,
      ((AlgebraicTopology.smallSingularSubcomplex X
        (fun k ↦ (𝒰 k : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).X i ⟶
        ((AlgebraicTopology.smallSingularSubcomplex X
          (fun k ↦ (𝒰 k : Set X)) : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).X j :=
  fun i ↦ Pi.single (i + 1) (smallPrismComponent 𝒰 i)

/-- Helper for Remark 60.1: the restricted prism family vanishes outside the
adjacent degrees of the chain-complex shape. -/
lemma smallPrismHomotopyComponent_zero
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (i j : ℕ)
    (hij : ¬(ComplexShape.down ℕ).Rel j i) :
    smallPrismHomotopyComponent 𝒰 i j = 0 := by
  -- The family is supported only at the successor of its source degree.
  exact Pi.single_eq_of_ne (Ne.symm hij) _

/-- Helper for Remark 60.1: the restricted prism family satisfies the chain
homotopy commutation equation in every degree. -/
lemma smallPrismHomotopyComponent_comm
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (i : ℕ) :
    (smallSubdivisionChainMap 𝒰).f i =
      _root_.dNext i (smallPrismHomotopyComponent 𝒰) +
        _root_.prevD i (smallPrismHomotopyComponent 𝒰) +
        𝟙 _ := by
  -- Degree zero is immediate; successor degrees use the restricted prism equation.
  cases i with
  | zero =>
      rw [_root_.Homotopy.prevD_chainComplex,
        _root_.Homotopy.dNext_zero_chainComplex]
      simp only [smallPrismHomotopyComponent, Pi.single_eq_same,
        smallPrismComponent_zero, CategoryTheory.Limits.zero_comp, zero_add]
      exact smallSubdivisionComponent_zero 𝒰
  | succ n =>
      rw [_root_.Homotopy.prevD_chainComplex,
        _root_.Homotopy.dNext_succ_chainComplex]
      simpa only [smallSubdivisionChainMap, smallPrismHomotopyComponent,
        Pi.single_eq_same] using smallPrismComponent_homotopy 𝒰 n

/-- Helper for Remark 60.1: barycentric subdivision of cover-small singular
chains is chain-homotopic to the identity within the cover-small complex. -/
noncomputable def smallSubdivisionChainMapHomotopyIdentity
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    _root_.Homotopy (smallSubdivisionChainMap 𝒰)
      (𝟙 ((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ))) :=
  { hom := smallPrismHomotopyComponent 𝒰
    zero := smallPrismHomotopyComponent_zero 𝒰
    comm := smallPrismHomotopyComponent_comm 𝒰 }

/-- Helper for Remark 60.1: restricted barycentric subdivision induces the
identity on cover-small singular homology. -/
lemma homologyMap_smallSubdivisionChainMap_eq_id
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivisionChainMap 𝒰) n =
      𝟙 (((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).homology n) := by
  -- Homotopic chain maps induce the same homology morphism.
  simpa only [HomologicalComplex.homologyMap_id] using
    (smallSubdivisionChainMapHomotopyIdentity 𝒰).homologyMap_eq n

/-- Helper for Remark 60.1: iterated barycentric subdivision on the cover-small
singular chain complex. -/
noncomputable def smallSubdivisionChainMapIterate
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) :
    ℕ → ((AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
        (ModuleCat.of ℤ ℤ) ⟶
      (AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ))
  | 0 => 𝟙 _
  | N + 1 => smallSubdivisionChainMapIterate 𝒰 N ≫
      smallSubdivisionChainMap 𝒰

/-- Helper for Remark 60.1: iterated cover-small subdivision commutes with
inclusion into the corresponding ambient iterate. -/
lemma smallSubdivisionChainMapIterate_comp_inclusion
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (N : ℕ) :
    smallSubdivisionChainMapIterate 𝒰 N ≫
        AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X)) =
      AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X)) ≫ chainMapIterate X N := by
  -- Induct on the common subdivision rank and use the one-step naturality square.
  induction N with
  | zero =>
      rw [smallSubdivisionChainMapIterate, chainMapIterate,
        Category.id_comp, Category.comp_id]
  | succ N ih =>
      rw [smallSubdivisionChainMapIterate, chainMapIterate, Category.assoc,
        smallSubdivisionChainMap_comp_inclusion, ← Category.assoc, ih,
        Category.assoc]

/-- Helper for Remark 60.1: every iterate of restricted subdivision induces
the identity on cover-small singular homology. -/
lemma homologyMap_smallSubdivisionChainMapIterate_eq_id
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X) (n N : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivisionChainMapIterate 𝒰 N) n =
      𝟙 (((AlgebraicTopology.smallSingularSubcomplex X
        (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).homology n) := by
  -- Iterate functoriality of homology and the one-step prism homotopy.
  induction N with
  | zero =>
      rw [smallSubdivisionChainMapIterate, HomologicalComplex.homologyMap_id]
  | succ N ih =>
      rw [smallSubdivisionChainMapIterate, HomologicalComplex.homologyMap_comp,
        ih, homologyMap_smallSubdivisionChainMap_eq_id, Category.comp_id]

/-- Helper for Remark 60.1: turn a vector in the concrete direct sum of simplex
coefficients into the corresponding rank-one singular-chain morphism. -/
noncomputable def chainMorphismOfDirectSum
    (X : TopCat) (n : ℕ)
    (v : (⨁ _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)), ℤ)) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  letI := Classical.decEq ((TopCat.toSSet.obj X).obj
    (Opposite.op (SimplexCategory.mk n)))
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ v) ≫
    (ModuleCat.coprodIsoDirectSum
      (fun _ : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)).inv

/-- Helper for Remark 60.1: the rank-one chain morphism evaluates at one to
the direct-sum vector transported back to the categorical coproduct. -/
lemma chainMorphismOfDirectSum_apply_one
    (X : TopCat) (n : ℕ)
    [instDecidable : DecidableEq ((TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))]
    (v : (⨁ _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)), ℤ)) :
    chainMorphismOfDirectSum X n v 1 =
      (ModuleCat.coprodIsoDirectSum
        (fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)).inv v := by
  -- Evaluation at one is the computation rule for `toSpanSingleton`.
  have hdecidable : instDecidable = Classical.decEq _ := Subsingleton.elim _ _
  subst instDecidable
  letI := Classical.decEq ((TopCat.toSSet.obj X).obj
    (Opposite.op (SimplexCategory.mk n)))
  simp only [chainMorphismOfDirectSum, CategoryTheory.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]
  rfl

/-- Helper for Remark 60.1: the rank-one chain construction sends the zero
direct-sum vector to the zero morphism. -/
lemma chainMorphismOfDirectSum_zero (X : TopCat) (n : ℕ) :
    chainMorphismOfDirectSum X n 0 = 0 := by
  -- The inverse coproduct equivalence and the rank-one map both preserve zero.
  classical
  rw [chainMorphismOfDirectSum, LinearMap.toSpanSingleton_zero,
    ModuleCat.ofHom_zero, CategoryTheory.Limits.zero_comp]

/-- Helper for Remark 60.1: the rank-one chain construction preserves addition
of direct-sum vectors. -/
lemma chainMorphismOfDirectSum_add
    (X : TopCat) (n : ℕ)
    (v w : (⨁ _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)), ℤ)) :
    chainMorphismOfDirectSum X n (v + w) =
      chainMorphismOfDirectSum X n v + chainMorphismOfDirectSum X n w := by
  -- Transport addition through the coproduct isomorphism and distribute scalar action.
  classical
  unfold chainMorphismOfDirectSum
  rw [LinearMap.toSpanSingleton_add,
    ModuleCat.ofHom_add, Preadditive.add_comp]

/-- Helper for Remark 60.1: a vector supported at one simplex gives the
corresponding integer multiple of that simplex generator. -/
lemma chainMorphismOfDirectSum_of
    (X : TopCat) (n : ℕ)
    [instDecidable : DecidableEq ((TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))]
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) (a : ℤ) :
    chainMorphismOfDirectSum X n
        (DirectSum.of
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) =
      a • (TopCat.toSSet.obj X).ιChainComplex σ := by
  have hdecidable : instDecidable = Classical.decEq _ := Subsingleton.elim _ _
  subst instDecidable
  letI := Classical.decEq ((TopCat.toSSet.obj X).obj
    (Opposite.op (SimplexCategory.mk n)))
  let generator : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
    a • (TopCat.toSSet.obj X).ιChainComplex σ
  change chainMorphismOfDirectSum X n
      (DirectSum.of
        (fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) = generator
  have hof := ModuleCat.lof_coprodIsoDirectSum_inv
    (fun _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ) σ
  have hof_apply (t : ℤ) := CategoryTheory.congr_fun hof t
  have hone :
      chainMorphismOfDirectSum X n
          (DirectSum.of
            (fun _ : (TopCat.toSSet.obj X).obj
              (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) 1 =
        generator 1 := by
    -- At the generator, this is the coproduct inclusion computation rule.
    rw [chainMorphismOfDirectSum_apply_one]
    calc
      (ModuleCat.coprodIsoDirectSum
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)).inv
          (DirectSum.of
            (fun _ : (TopCat.toSSet.obj X).obj
              (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) =
        (ModuleCat.ofHom
            (DirectSum.lof ℤ
              ((TopCat.toSSet.obj X).obj
                (Opposite.op (SimplexCategory.mk n)))
              (fun _ ↦ ℤ) σ) ≫
          (ModuleCat.coprodIsoDirectSum
            (fun _ : (TopCat.toSSet.obj X).obj
              (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)).inv) a := by
          rw [CategoryTheory.comp_apply]
          congr 1
      _ = (Limits.Sigma.ι
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ) σ) a :=
        hof_apply a
      _ = (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) σ a := rfl
      _ = generator 1 := by
        let inclusion := (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) σ
        have hmap : inclusion a = a • inclusion 1 := by
          simpa only [smul_eq_mul, mul_one] using
            map_zsmul inclusion.hom a (1 : ℤ)
        have hsmul := DFunLike.congr_fun
          (ModuleCat.hom_zsmul a inclusion) (1 : ℤ)
        calc
          inclusion a = a • inclusion 1 := hmap
          _ = (a • inclusion.hom) 1 := rfl
          _ = (a • inclusion).hom 1 := hsmul.symm
          _ = generator 1 := rfl
  -- Module morphisms from `ℤ` are determined by their value at one.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  calc
    chainMorphismOfDirectSum X n
        (DirectSum.of
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) z =
      z • chainMorphismOfDirectSum X n
        (DirectSum.of
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a) 1 := by
        simpa only [smul_eq_mul, mul_one] using
          map_zsmul (chainMorphismOfDirectSum X n
            (DirectSum.of
              (fun _ : (TopCat.toSSet.obj X).obj
                (Opposite.op (SimplexCategory.mk n)) ↦ ℤ) σ a)).hom z (1 : ℤ)
    _ = z • generator 1 := by rw [hone]
    _ = generator z := by
      simpa only [smul_eq_mul, mul_one] using
        (map_zsmul generator.hom z (1 : ℤ)).symm

/-- Helper for Remark 60.1: every direct-sum singular chain becomes cover-small
after one uniform subdivision rank, and remains so at all later ranks. -/
lemma exists_forall_ge_chainMorphismOfDirectSum_smallLift
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (v : (⨁ _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)), ℤ)) :
    ∃ N, ∀ M, N ≤ M →
      ∃ c : ModuleCat.of ℤ ℤ ⟶
          ((AlgebraicTopology.smallSingularSubcomplex X
            (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
              (ModuleCat.of ℤ ℤ)).X n,
        c ≫ (AlgebraicTopology.integralSmallSingularChainInclusion X
            (fun i ↦ (𝒰 i : Set X))).f n =
          chainMorphismOfDirectSum X n v ≫ (chainMapIterate X M).f n := by
  -- Induct over the finite direct-sum support, taking maxima of subdivision ranks.
  classical
  induction v using DirectSum.induction_on with
  | zero =>
      refine ⟨0, fun M _ ↦ ⟨0, ?_⟩⟩
      rw [CategoryTheory.Limits.zero_comp, chainMorphismOfDirectSum_zero,
        CategoryTheory.Limits.zero_comp]
  | of σ a =>
      obtain ⟨N, hN⟩ :=
        exists_forall_ge_chainMapIterate_generator_smallLift n 𝒰 h𝒰 σ
      refine ⟨N, fun M hNM ↦ ?_⟩
      obtain ⟨c, hc⟩ := hN M hNM
      refine ⟨a • c, ?_⟩
      rw [Preadditive.zsmul_comp, hc, chainMorphismOfDirectSum_of,
        Preadditive.zsmul_comp]
  | add v w hv hw =>
      obtain ⟨Nv, hv⟩ := hv
      obtain ⟨Nw, hw⟩ := hw
      refine ⟨max Nv Nw, fun M hM ↦ ?_⟩
      obtain ⟨cv, hcv⟩ := hv M ((le_max_left _ _).trans hM)
      obtain ⟨cw, hcw⟩ := hw M ((le_max_right _ _).trans hM)
      refine ⟨cv + cw, ?_⟩
      rw [Preadditive.add_comp, hcv, hcw, chainMorphismOfDirectSum_add,
        Preadditive.add_comp]

/-- Helper for Remark 60.1: every finite integral singular chain becomes
cover-small after sufficiently many barycentric subdivisions. -/
lemma exists_forall_ge_chainMapIterate_smallLift
    {X : TopCat} {ι : Type} (n : ℕ)
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (c : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    ∃ N, ∀ M, N ≤ M →
      ∃ csmall : ModuleCat.of ℤ ℤ ⟶
          ((AlgebraicTopology.smallSingularSubcomplex X
            (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex
              (ModuleCat.of ℤ ℤ)).X n,
        csmall ≫ (AlgebraicTopology.integralSmallSingularChainInclusion X
            (fun i ↦ (𝒰 i : Set X))).f n =
          c ≫ (chainMapIterate X M).f n := by
  classical
  let e := ModuleCat.coprodIsoDirectSum
    (fun _ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) ↦ ModuleCat.of ℤ ℤ)
  let v := e.hom (c 1)
  have hc : chainMorphismOfDirectSum X n v = c := by
    -- A linear map from `ℤ` is determined by the image of one.
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    calc
      chainMorphismOfDirectSum X n v z =
          (z : ℤ) • chainMorphismOfDirectSum X n v 1 := by
        simpa only [smul_eq_mul, mul_one] using
          map_zsmul (chainMorphismOfDirectSum X n v).hom z (1 : ℤ)
      _ = (z : ℤ) • c 1 := by
        rw [chainMorphismOfDirectSum_apply_one]
        simp only [v, e, Iso.hom_inv_id_apply]
      _ = c ((z : ℤ) • (1 : ℤ)) := (map_zsmul c.hom z (1 : ℤ)).symm
      _ = c z := by
        simp only [smul_eq_mul, mul_one]
  obtain ⟨N, hN⟩ :=
    exists_forall_ge_chainMorphismOfDirectSum_smallLift n 𝒰 h𝒰 v
  refine ⟨N, fun M hNM ↦ ?_⟩
  obtain ⟨csmall, hcsmall⟩ := hN M hNM
  exact ⟨csmall, by simpa only [hc] using hcsmall⟩

/-- Helper for Remark 60.1: the cover-small chain inclusion is surjective on
integral singular homology for an open cover. -/
lemma homologyMap_integralSmallSingularChainInclusion_surjective
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰) (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))) n) := by
  let Csmall :=
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex (ModuleCat.of ℤ ℤ)
  let Cambient :=
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  let j := (ComplexShape.down ℕ).next n
  letI : CategoryTheory.Projective (ModuleCat.of ℤ ℤ) :=
    integralCoefficientModuleProjective
  intro y
  let γ : ModuleCat.of ℤ ℤ ⟶ Cambient.homology n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ y)
  let z : ModuleCat.of ℤ ℤ ⟶ Cambient.cycles n :=
    CategoryTheory.Projective.factorThru γ (Cambient.homologyπ n)
  have hz : z ≫ Cambient.homologyπ n = γ := by
    -- Projectivity of the coefficient module lifts the chosen homology class to cycles.
    exact CategoryTheory.Projective.factorThru_comp γ (Cambient.homologyπ n)
  let c : ModuleCat.of ℤ ℤ ⟶ Cambient.X n := z ≫ Cambient.iCycles n
  have hc : c ≫ Cambient.d n j = 0 := by
    -- The lifted representative lands in the kernel of the outgoing differential.
    dsimp only [c]
    rw [Category.assoc, HomologicalComplex.iCycles_d,
      CategoryTheory.Limits.comp_zero]
  obtain ⟨N, hN⟩ := exists_forall_ge_chainMapIterate_smallLift n 𝒰 h𝒰 c
  obtain ⟨csmall, hcsmall⟩ := hN N le_rfl
  have hcsmallCycle : csmall ≫ Csmall.d n j = 0 := by
    letI : Mono (ιsmall.f j) :=
      (ModuleCat.mono_iff_injective _).mpr
        (AlgebraicTopology.integralSmallSingularChainInclusion_injective
          X (fun i ↦ (𝒰 i : Set X)) j)
    -- Detect the cycle equation after the injective inclusion into ambient chains.
    rw [← cancel_mono (ιsmall.f j)]
    calc
      (csmall ≫ Csmall.d n j) ≫ ιsmall.f j =
          csmall ≫ (ιsmall.f n ≫ Cambient.d n j) := by
        rw [Category.assoc, ιsmall.comm]
      _ = (csmall ≫ ιsmall.f n) ≫ Cambient.d n j :=
        (Category.assoc _ _ _).symm
      _ = (c ≫ (chainMapIterate X N).f n) ≫ Cambient.d n j := by
        rw [hcsmall]
      _ = c ≫ ((chainMapIterate X N).f n ≫ Cambient.d n j) :=
        Category.assoc _ _ _
      _ = c ≫ (Cambient.d n j ≫ (chainMapIterate X N).f j) := by
        rw [(chainMapIterate X N).comm]
      _ = (c ≫ Cambient.d n j) ≫ (chainMapIterate X N).f j :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hc, CategoryTheory.Limits.zero_comp]
      _ = 0 ≫ ιsmall.f j := CategoryTheory.Limits.zero_comp.symm
  let xmap : ModuleCat.of ℤ ℤ ⟶ Csmall.homology n :=
    Csmall.liftCycles csmall j rfl hcsmallCycle ≫ Csmall.homologyπ n
  have hcIterate :
      (c ≫ (chainMapIterate X N).f n) ≫ Cambient.d n j = 0 := by
    -- A chain map carries the chosen ambient cycle to another cycle.
    rw [Category.assoc, (chainMapIterate X N).comm, ← Category.assoc,
      hc, CategoryTheory.Limits.zero_comp]
  have hsmallLiftAmbient :
      Csmall.liftCycles csmall j rfl hcsmallCycle ≫
          HomologicalComplex.cyclesMap ιsmall n =
        Cambient.liftCycles (c ≫ (chainMapIterate X N).f n)
          j rfl hcIterate := by
    -- The equality of chain representatives determines the equality of cycles.
    rw [← cancel_mono (Cambient.iCycles n)]
    rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, HomologicalComplex.liftCycles_i, hcsmall,
      HomologicalComplex.liftCycles_i]
  have hsubdivisionLift :
      Cambient.liftCycles c j rfl hc ≫
          HomologicalComplex.cyclesMap (chainMapIterate X N) n =
        Cambient.liftCycles (c ≫ (chainMapIterate X N).f n)
          j rfl hcIterate := by
    -- Functoriality of cycles identifies subdivision before and after lifting.
    exact HomologicalComplex.liftCycles_comp_cyclesMap
      c j rfl hc (chainMapIterate X N)
  have hzLift : Cambient.liftCycles c j rfl hc = z := by
    -- A cycle morphism is determined by its composite with the cycles inclusion.
    rw [← cancel_mono (Cambient.iCycles n),
      HomologicalComplex.liftCycles_i]
  have hxmap : xmap ≫ HomologicalComplex.homologyMap ιsmall n = γ := by
    -- Naturality moves the class to the subdivided ambient representative.
    dsimp only [xmap]
    calc
      (Csmall.liftCycles csmall j rfl hcsmallCycle ≫
          Csmall.homologyπ n) ≫
          HomologicalComplex.homologyMap ιsmall n =
        (Csmall.liftCycles csmall j rfl hcsmallCycle ≫
          HomologicalComplex.cyclesMap ιsmall n) ≫
            Cambient.homologyπ n := by
          simp only [Category.assoc,
            HomologicalComplex.homologyπ_naturality]
          dsimp only [Cambient]
      _ = Cambient.liftCycles (c ≫ (chainMapIterate X N).f n)
          j rfl hcIterate ≫ Cambient.homologyπ n :=
        congrArg (fun q ↦ q ≫ Cambient.homologyπ n) hsmallLiftAmbient
      _ = (Cambient.liftCycles c j rfl hc ≫
          HomologicalComplex.cyclesMap (chainMapIterate X N) n) ≫
            Cambient.homologyπ n :=
        congrArg (fun q ↦ q ≫ Cambient.homologyπ n)
          hsubdivisionLift.symm
      _ = (Cambient.liftCycles c j rfl hc ≫ Cambient.homologyπ n) ≫
          HomologicalComplex.homologyMap (chainMapIterate X N) n := by
        simp only [Category.assoc,
          HomologicalComplex.homologyπ_naturality]
        dsimp only [Cambient]
      _ = (z ≫ Cambient.homologyπ n) ≫
          HomologicalComplex.homologyMap (chainMapIterate X N) n := by
        rw [hzLift]
      _ = γ ≫ HomologicalComplex.homologyMap (chainMapIterate X N) n := by
        rw [hz]
      _ = γ := by
        rw [homologyMap_chainMapIterate_eq_id, Category.comp_id]
  refine ⟨xmap 1, ?_⟩
  have hvalue := CategoryTheory.congr_fun hxmap 1
  have hmapped :
      HomologicalComplex.homologyMap ιsmall n (xmap 1) = γ 1 := by
    simpa only [CategoryTheory.comp_apply] using hvalue
  calc
    HomologicalComplex.homologyMap ιsmall n (xmap 1) = γ 1 := hmapped
    _ = y := by
      exact LinearMap.toSpanSingleton_apply_one ℤ _ y

/-- Helper for Remark 60.1: the cover-small chain inclusion is injective on
integral singular homology for an open cover. -/
lemma homologyMap_integralSmallSingularChainInclusion_injective
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰) (n : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.integralSmallSingularChainInclusion X
          (fun i ↦ (𝒰 i : Set X))) n) := by
  let Csmall :=
    (AlgebraicTopology.smallSingularSubcomplex X
      (fun i ↦ (𝒰 i : Set X)) : SSet).chainComplex (ModuleCat.of ℤ ℤ)
  let Cambient :=
    (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
  let ιsmall := AlgebraicTopology.integralSmallSingularChainInclusion X
    (fun i ↦ (𝒰 i : Set X))
  let i := (ComplexShape.down ℕ).prev n
  let j := (ComplexShape.down ℕ).next n
  letI : CategoryTheory.Projective (ModuleCat.of ℤ ℤ) :=
    integralCoefficientModuleProjective
  intro x y hxy
  let γ : ModuleCat.of ℤ ℤ ⟶ Csmall.homology n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (x - y))
  let z : ModuleCat.of ℤ ℤ ⟶ Csmall.cycles n :=
    CategoryTheory.Projective.factorThru γ (Csmall.homologyπ n)
  have hz : z ≫ Csmall.homologyπ n = γ := by
    -- Lift the difference class through the epimorphism from cycles to homology.
    exact CategoryTheory.Projective.factorThru_comp γ (Csmall.homologyπ n)
  let c : ModuleCat.of ℤ ℤ ⟶ Csmall.X n := z ≫ Csmall.iCycles n
  have hc : c ≫ Csmall.d n j = 0 := by
    dsimp only [c]
    rw [Category.assoc, HomologicalComplex.iCycles_d,
      CategoryTheory.Limits.comp_zero]
  have hγmap : γ ≫ HomologicalComplex.homologyMap ιsmall n = 0 := by
    -- The assumed equality says exactly that the rank-one difference map vanishes.
    have hdiff : HomologicalComplex.homologyMap ιsmall n (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hγone : γ 1 = x - y := by
      exact LinearMap.toSpanSingleton_apply_one ℤ _ (x - y)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    calc
      (γ ≫ HomologicalComplex.homologyMap ιsmall n) q =
          (q : ℤ) • (γ ≫ HomologicalComplex.homologyMap ιsmall n) 1 := by
        simpa only [smul_eq_mul, mul_one] using
          map_zsmul (γ ≫
            HomologicalComplex.homologyMap ιsmall n).hom q (1 : ℤ)
      _ = (q : ℤ) • HomologicalComplex.homologyMap ιsmall n (γ 1) := by
        rw [CategoryTheory.comp_apply]
      _ = (q : ℤ) • HomologicalComplex.homologyMap ιsmall n (x - y) := by
        rw [hγone]
      _ = 0 := by rw [hdiff, zsmul_zero]
      _ = (0 : ModuleCat.of ℤ ℤ ⟶ Cambient.homology n) q := rfl
  have hzambient :
      (z ≫ HomologicalComplex.cyclesMap ιsmall n) ≫
        Cambient.homologyπ n = 0 := by
    calc
      (z ≫ HomologicalComplex.cyclesMap ιsmall n) ≫
          Cambient.homologyπ n =
        z ≫ (HomologicalComplex.cyclesMap ιsmall n ≫
          Cambient.homologyπ n) := Category.assoc _ _ _
      _ = z ≫ (Csmall.homologyπ n ≫
          HomologicalComplex.homologyMap ιsmall n) := by
        rw [HomologicalComplex.homologyπ_naturality]
      _ = (z ≫ Csmall.homologyπ n) ≫
          HomologicalComplex.homologyMap ιsmall n :=
        (Category.assoc _ _ _).symm
      _ = γ ≫ HomologicalComplex.homologyMap ιsmall n := by rw [hz]
      _ = 0 := hγmap
  obtain ⟨A, π, hπ, b, hb⟩ :=
    (Cambient.comp_homologyπ_eq_zero_iff_up_to_refinements i n rfl
      (z ≫ HomologicalComplex.cyclesMap ιsmall n)).mp hzambient
  letI : Epi π := hπ
  let s : ModuleCat.of ℤ ℤ ⟶ A :=
    CategoryTheory.Projective.factorThru (𝟙 (ModuleCat.of ℤ ℤ)) π
  have hs : s ≫ π = 𝟙 (ModuleCat.of ℤ ℤ) := by
    exact CategoryTheory.Projective.factorThru_comp
      (𝟙 (ModuleCat.of ℤ ℤ)) π
  have hbchains :
      π ≫ z ≫ Csmall.iCycles n ≫ ιsmall.f n =
        b ≫ Cambient.d i n := by
    -- Forget cycles in the refinement equation to obtain an ordinary boundary equation.
    calc
      π ≫ z ≫ Csmall.iCycles n ≫ ιsmall.f n =
          π ≫ z ≫ (HomologicalComplex.cyclesMap ιsmall n ≫
            Cambient.iCycles n) := by
        rw [HomologicalComplex.cyclesMap_i]
      _ = (π ≫ z ≫ HomologicalComplex.cyclesMap ιsmall n) ≫
          Cambient.iCycles n := by simp only [Category.assoc]
      _ = (b ≫ Cambient.toCycles i n) ≫ Cambient.iCycles n :=
        congrArg (fun q ↦ q ≫ Cambient.iCycles n) hb
      _ = b ≫ Cambient.d i n := by
        rw [Category.assoc, HomologicalComplex.toCycles_i]
  let b' : ModuleCat.of ℤ ℤ ⟶ Cambient.X i := s ≫ b
  have hboundary : c ≫ ιsmall.f n = b' ≫ Cambient.d i n := by
    -- Split the refinement epimorphism using projectivity of the coefficient module.
    calc
      c ≫ ιsmall.f n = z ≫ Csmall.iCycles n ≫ ιsmall.f n := rfl
      _ = (s ≫ π) ≫ z ≫ Csmall.iCycles n ≫ ιsmall.f n := by
        rw [hs, Category.id_comp]
      _ = s ≫ (π ≫ z ≫ Csmall.iCycles n ≫ ιsmall.f n) := by
        simp only [Category.assoc]
      _ = s ≫ (b ≫ Cambient.d i n) :=
        congrArg (fun q ↦ s ≫ q) hbchains
      _ = b' ≫ Cambient.d i n := by
        simp only [b', Category.assoc]
  obtain ⟨N, hN⟩ := exists_forall_ge_chainMapIterate_smallLift i 𝒰 h𝒰 b'
  obtain ⟨bsmall, hbsmall⟩ := hN N le_rfl
  have hsmallBoundary :
      c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n =
        bsmall ≫ Csmall.d i n := by
    letI : Mono (ιsmall.f n) :=
      (ModuleCat.mono_iff_injective _).mpr
        (AlgebraicTopology.integralSmallSingularChainInclusion_injective
          X (fun k ↦ (𝒰 k : Set X)) n)
    -- Compare both candidate boundaries after the injective ambient inclusion.
    rw [← cancel_mono (ιsmall.f n)]
    calc
      (c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n) ≫
          ιsmall.f n =
        c ≫ ((smallSubdivisionChainMapIterate 𝒰 N).f n ≫
          ιsmall.f n) := Category.assoc _ _ _
      _ = c ≫ (ιsmall.f n ≫ (chainMapIterate X N).f n) := by
        have hcomponent := congrArg
          (fun q ↦ q.f n)
          (smallSubdivisionChainMapIterate_comp_inclusion 𝒰 N)
        have hcomponent' :
            (smallSubdivisionChainMapIterate 𝒰 N).f n ≫ ιsmall.f n =
              ιsmall.f n ≫ (chainMapIterate X N).f n := by
          simpa only [HomologicalComplex.comp_f] using hcomponent
        exact congrArg (fun q ↦ c ≫ q) hcomponent'
      _ = (c ≫ ιsmall.f n) ≫ (chainMapIterate X N).f n :=
        (Category.assoc _ _ _).symm
      _ = (b' ≫ Cambient.d i n) ≫ (chainMapIterate X N).f n := by
        rw [hboundary]
      _ = b' ≫ (Cambient.d i n ≫ (chainMapIterate X N).f n) :=
        Category.assoc _ _ _
      _ = b' ≫ ((chainMapIterate X N).f i ≫ Cambient.d i n) := by
        rw [(chainMapIterate X N).comm]
      _ = (b' ≫ (chainMapIterate X N).f i) ≫ Cambient.d i n :=
        (Category.assoc _ _ _).symm
      _ = (bsmall ≫ ιsmall.f i) ≫ Cambient.d i n := by
        rw [hbsmall]
      _ = bsmall ≫ (ιsmall.f i ≫ Cambient.d i n) :=
        Category.assoc _ _ _
      _ = bsmall ≫ (Csmall.d i n ≫ ιsmall.f n) := by
        rw [ιsmall.comm]
      _ = (bsmall ≫ Csmall.d i n) ≫ ιsmall.f n :=
        (Category.assoc _ _ _).symm
  have zLift : z = Csmall.liftCycles c j rfl hc := by
    -- Both cycle morphisms have the same underlying chain representative.
    rw [← cancel_mono (Csmall.iCycles n),
      HomologicalComplex.liftCycles_i]
  have hiteratedClass :
      (z ≫ Csmall.homologyπ n) ≫
          HomologicalComplex.homologyMap
            (smallSubdivisionChainMapIterate 𝒰 N) n =
        Csmall.liftCycles
            (c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n)
            j rfl (by rw [Category.assoc,
              (smallSubdivisionChainMapIterate 𝒰 N).comm,
              reassoc_of% hc, CategoryTheory.Limits.zero_comp]) ≫
          Csmall.homologyπ n := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [zLift, HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  have hboundaryClass :
      Csmall.liftCycles
          (c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n)
          j rfl (by rw [Category.assoc,
            (smallSubdivisionChainMapIterate 𝒰 N).comm,
            reassoc_of% hc, CategoryTheory.Limits.zero_comp]) ≫
        Csmall.homologyπ n = 0 := by
    exact Csmall.liftCycles_homologyπ_eq_zero_of_boundary
      (c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n) j rfl
      bsmall hsmallBoundary
  have hγzero : γ = 0 := by
    calc
      γ = z ≫ Csmall.homologyπ n := hz.symm
      _ = (z ≫ Csmall.homologyπ n) ≫ 𝟙 _ := by rw [Category.comp_id]
      _ = (z ≫ Csmall.homologyπ n) ≫
          HomologicalComplex.homologyMap
            (smallSubdivisionChainMapIterate 𝒰 N) n := by
        rw [homologyMap_smallSubdivisionChainMapIterate_eq_id]
      _ = Csmall.liftCycles
            (c ≫ (smallSubdivisionChainMapIterate 𝒰 N).f n)
            j rfl (by rw [Category.assoc,
              (smallSubdivisionChainMapIterate 𝒰 N).comm,
              reassoc_of% hc, CategoryTheory.Limits.zero_comp]) ≫
          Csmall.homologyπ n := hiteratedClass
      _ = 0 := hboundaryClass
  have hsub : x - y = 0 := by
    calc
      x - y = γ 1 := by
        exact (LinearMap.toSpanSingleton_apply_one ℤ _ (x - y)).symm
      _ = (0 : ModuleCat.of ℤ ℤ ⟶ Csmall.homology n) 1 :=
        CategoryTheory.congr_fun hγzero 1
      _ = 0 := rfl
  exact sub_eq_zero.mp hsub

/-- Helper for Remark 60.1: inclusion of cover-small integral singular chains
is a quasi-isomorphism for every open cover. -/
lemma integralSmallSingularChainInclusion_quasiIso
    {X : TopCat} {ι : Type}
    (𝒰 : ι → TopologicalSpace.Opens X)
    (h𝒰 : TopologicalSpace.IsOpenCover 𝒰) :
    QuasiIso
      (AlgebraicTopology.integralSmallSingularChainInclusion X
        (fun i ↦ (𝒰 i : Set X))) := by
  -- Bijectivity of every induced module map supplies the quasi-isomorphism instance.
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  exact ⟨homologyMap_integralSmallSingularChainInclusion_injective 𝒰 h𝒰 n,
    homologyMap_integralSmallSingularChainInclusion_surjective 𝒰 h𝒰 n⟩

/-- Helper for Remark 60.1: an open cover proves the small-chain inclusion is a
quasi-isomorphism for any propositionally equal spelling of its underlying sets. -/
lemma integralSmallSingularChainInclusion_quasiIso_of_eq
    {X : TopCat} {ι : Type} (U : ι → Set X)
    (V : ι → TopologicalSpace.Opens X)
    (hUV : U = fun i ↦ (V i : Set X))
    (hV : TopologicalSpace.IsOpenCover V) :
    QuasiIso (AlgebraicTopology.integralSmallSingularChainInclusion X U) := by
  -- Substitute the set family once, then invoke the canonical open-cover theorem.
  subst U
  exact integralSmallSingularChainInclusion_quasiIso V hV

end AlgebraicTopology.BarycentricSubdivision

namespace TopPair

open CategoryTheory

/-- Helper for Remark 60.1: inside the open subspace `B`, the part lying in the
open subspace `A`. -/
@[expose]
def openExcisionIntersection {X : TopCat}
    (A B : TopologicalSpace.Opens X) : Set (B : Set X) :=
  {x | (x.1 : X) ∈ A}

/-- Helper for Remark 60.1: the intersection subspace includes continuously in
the left-hand open subspace. -/
lemma continuous_openExcisionIntersectionToLeft {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    Continuous (fun x : openExcisionIntersection A B ↦
      (⟨x.1.1, x.2⟩ : (A : Set X))) := by
  -- Forget the two nested subtypes, then bundle the resulting map into `A`.
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _

/-- Helper for Remark 60.1: the intersection subspace includes in `A`. -/
def openExcisionIntersectionToLeft {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopCat.of (openExcisionIntersection A B) ⟶ TopCat.of (A : Set X) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1.1, x.2⟩, continuous_openExcisionIntersectionToLeft A B⟩

/-- Helper for Remark 60.1: the two nested subspace inclusions from `A ∩ B`
to `X` agree. -/
lemma openExcisionIntersection_square {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    openExcisionIntersectionToLeft A B ≫
        (TopPair.ofSubset (A : Set X)).map =
      (TopPair.ofSubset (openExcisionIntersection A B)).map ≫
        (TopPair.ofSubset (B : Set X)).map := by
  -- Both composites forget the same two subtype layers.
  ext x
  rfl

/-- Helper for Remark 60.1: the excision source is the pair `(B, A ∩ B)`. -/
abbrev openExcisionSource {X : TopCat}
    (A B : TopologicalSpace.Opens X) : TopPair :=
  @TopPair.ofSubset (TopCat.of (B : Set X)) (openExcisionIntersection A B)

/-- Helper for Remark 60.1: the canonical map of pairs `(B, A ∩ B) ⟶ (X, A)`. -/
def openExcisionHom {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    openExcisionSource A B ⟶ TopPair.ofSubset (A : Set X) :=
  TopPair.ofHom
    (TopPair.ofSubset (B : Set X)).map
    (openExcisionIntersectionToLeft A B)
    (openExcisionIntersection_square A B)

/-- Helper for Remark 60.1: the ambient component of the open-excision map is
the inclusion of `B` into `X`. -/
lemma openExcisionHom_fst {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopPair.Hom.fst (openExcisionHom A B) =
      (TopPair.ofSubset (B : Set X)).map := by
  -- This is the first component specified by `TopPair.ofHom`.
  rfl

/-- Helper for Remark 60.1: the subspace component of the open-excision map is
the inclusion of `A ∩ B` into `A`. -/
lemma openExcisionHom_snd {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopPair.Hom.snd (openExcisionHom A B) =
      openExcisionIntersectionToLeft A B := by
  -- This is the second component specified by `TopPair.ofHom`.
  rfl

end TopPair

namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits

/-- Helper for Remark 60.1: singular simplices in `A` land in the small
subcomplex subordinate to the two-member family `(A, B)`. -/
lemma range_leftInclusion_le_twoOpenSmall {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) ≤
      smallSingularSubcomplex X (fun b : Bool ↦ (Bool.rec A B b : Set X)) := by
  -- A simplex in the range factors through the `false` member, namely `A`.
  intro n σ hσ
  rw [mem_smallSingularSubcomplex_iff_exists]
  obtain ⟨τ, hτ⟩ := hσ
  exact ⟨false, τ, hτ⟩

/-- Helper for Remark 60.1: the inclusion of `A` factored through the
two-open small singular subcomplex. -/
@[expose]
noncomputable def twoOpenSmallLeftSSetMap {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopCat.toSSet.obj (TopCat.of (A : Set X)) ⟶
      (smallSingularSubcomplex X
        (fun b : Bool ↦ (Bool.rec A B b : Set X)) : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)))
    (range_leftInclusion_le_twoOpenSmall A B)

/-- Helper for Remark 60.1: forgetting the small factorization recovers the
ordinary simplicial inclusion of `A`. -/
lemma twoOpenSmallLeftSSetMap_comp_inclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    twoOpenSmallLeftSSetMap A B ≫
        (smallSingularSubcomplex X
          (fun b : Bool ↦ (Bool.rec A B b : Set X))).ι =
      TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)) := by
  -- Use the computation rule of the subcomplex lift.
  exact SSet.Subcomplex.lift_ι _ _

/-- Helper for Remark 60.1: singular simplices in `B` land in the small
subcomplex subordinate to the two-member family `(A, B)`. -/
lemma range_rightInclusion_le_twoOpenSmall {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) ≤
      smallSingularSubcomplex X (fun b : Bool ↦ (Bool.rec A B b : Set X)) := by
  -- A simplex in the range factors through the `true` member, namely `B`.
  intro n σ hσ
  rw [mem_smallSingularSubcomplex_iff_exists]
  obtain ⟨τ, hτ⟩ := hσ
  exact ⟨true, τ, hτ⟩

/-- Helper for Remark 60.1: the inclusion of `B` factored through the
two-open small singular subcomplex. -/
@[expose]
noncomputable def twoOpenSmallRightSSetMap {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopCat.toSSet.obj (TopCat.of (B : Set X)) ⟶
      (smallSingularSubcomplex X
        (fun b : Bool ↦ (Bool.rec A B b : Set X)) : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))
    (range_rightInclusion_le_twoOpenSmall A B)

/-- Helper for Remark 60.1: forgetting the right small factorization recovers
the ordinary simplicial inclusion of `B`. -/
lemma twoOpenSmallRightSSetMap_comp_inclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    twoOpenSmallRightSSetMap A B ≫
        (smallSingularSubcomplex X
          (fun b : Bool ↦ (Bool.rec A B b : Set X))).ι =
      TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)) := by
  -- Use the computation rule of the subcomplex lift.
  exact SSet.Subcomplex.lift_ι _ _

/-- Helper for Remark 60.1: the integral chain map from chains on `B` into the
two-open small chain complex. -/
noncomputable abbrev integralTwoOpenSmallRightInclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :=
  SSet.chainComplexMap (twoOpenSmallRightSSetMap A B) (ModuleCat.of ℤ ℤ)

/-- Helper for Remark 60.1: membership in the range of a singular subspace
inclusion is exactly containment of the represented simplex in that subspace. -/
lemma mem_range_singularSubspaceInclusion_iff {X : TopCat} (A : Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range
      (TopCat.toSSet.map (singularSubspaceInclusion X A))).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ A := by
  -- Translate range membership into a factorization through the subtype.
  simp only [Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨τ, hτ⟩
    have hfactor :
        (singularSubspaceInclusion X A).hom.comp
            ((TopCat.of A).toSSetObjEquiv n τ) =
          X.toSSetObjEquiv n σ := by
      rw [← hτ, toSSetObjEquiv_map]
    apply (continuousMap_factorsThrough_subtype_iff A
      (X.toSSetObjEquiv n σ)).mp
    have hforget :
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp
            ((TopCat.of A).toSSetObjEquiv n τ) =
          X.toSSetObjEquiv n σ := by
      simpa only [singularSubspaceInclusion_hom] using hfactor
    exact ⟨(TopCat.of A).toSSetObjEquiv n τ, hforget⟩
  · intro hσ
    obtain ⟨τ, hτ⟩ :=
      (continuousMap_factorsThrough_subtype_iff A
        (X.toSSetObjEquiv n σ)).mpr hσ
    refine ⟨((TopCat.of A).toSSetObjEquiv n).symm τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply]
    simpa only [singularSubspaceInclusion_hom] using hτ

/-- Helper for Remark 60.1: the nested-intersection inclusion followed by the
ambient subspace inclusion forgets both subtype layers. -/
lemma openExcisionComposite_hom {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    ((TopPair.openExcisionSource A B).map ≫
        singularSubspaceInclusion X (B : Set X)).hom =
      (⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
        (TopPair.openExcisionSource A B).map.hom := by
  -- Specialize the owner computation lemma at the nested intersection map.
  exact hom_comp_singularSubspaceInclusion X (B : Set X)
    (TopPair.openExcisionSource A B).map

/-- Helper for Remark 60.1: a singular simplex factors through the nested
intersection inside `B` exactly when its ambient range lies in both opens. -/
lemma mem_range_openExcisionIntersection_iff {X : TopCat}
    (A B : TopologicalSpace.Opens X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range
      (TopCat.toSSet.map
        ((TopPair.openExcisionSource A B).map ≫
          singularSubspaceInclusion X (B : Set X)))).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ A ∧
        Set.range (X.toSSetObjEquiv n σ) ⊆ B := by
  -- Use the pinned composite computation to avoid unfolding the stored
  -- `TopPair.fst` endpoint into the explicit subtype `TopCat.of B`.
  simp only [Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨τ, hτ⟩
    have hfactor := congrArg (X.toSSetObjEquiv n) hτ
    rw [toSSetObjEquiv_map] at hfactor
    have hfactor' :
        ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
          (TopPair.openExcisionSource A B).map.hom).comp
            ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) =
          X.toSSetObjEquiv n σ :=
      (congrArg
        (fun k ↦ k.comp
          ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ))
        (openExcisionComposite_hom A B)).symm.trans hfactor
    constructor
    · rintro _ ⟨y, rfl⟩
      have hy := DFunLike.congr_fun hfactor' y
      rw [← hy]
      exact (((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) y).2
    · rintro _ ⟨y, rfl⟩
      have hy := DFunLike.congr_fun hfactor' y
      rw [← hy]
      exact (((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) y).1.2
  · rintro ⟨hA, hB⟩
    let cX := X.toSSetObjEquiv n σ
    let cB : C(stdSimplex ℝ (Fin (n.unop.len + 1)), (B : Set X)) :=
      ⟨fun y ↦ ⟨cX y, hB (Set.mem_range_self y)⟩,
        cX.continuous.subtype_mk _⟩
    let cI : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
        TopPair.openExcisionIntersection A B) :=
      ⟨fun y ↦ ⟨cB y, hA (Set.mem_range_self y)⟩,
        cB.continuous.subtype_mk _⟩
    let τ := ((TopCat.of
      (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n).symm cI
    refine ⟨τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map]
    calc
      ((TopPair.openExcisionSource A B).map ≫
            singularSubspaceInclusion X (B : Set X)).hom.comp
          ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) =
        ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
          (TopPair.openExcisionSource A B).map.hom).comp
            ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) :=
        congrArg
          (fun k ↦ k.comp
            ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ))
          (openExcisionComposite_hom A B)
      _ = ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
          (TopPair.openExcisionSource A B).map.hom).comp cI := by
        exact congrArg
          (fun k ↦ ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
            (TopPair.openExcisionSource A B).map.hom).comp k)
          (Equiv.apply_symm_apply
            ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n) cI)
      _ = X.toSSetObjEquiv n σ := by
        ext y
        rfl
  /-
  -- Normalize range membership to a represented continuous simplex.
  simp only [Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨τ, hτ⟩
    have hfactor := congrArg (X.toSSetObjEquiv n) hτ
    rw [toSSetObjEquiv_map] at hfactor
    have hfactor' :
        ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
          (TopPair.openExcisionSource A B).map.hom).comp
            ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) =
          X.toSSetObjEquiv n σ := by
      -- Transport the represented simplex across the pinned composite computation.
      exact (congrArg
        (fun k ↦ k.comp
          ((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ))
        (openExcisionComposite_hom A B)).symm.trans hfactor
    constructor
    · rintro _ ⟨y, rfl⟩
      have hy := DFunLike.congr_fun hfactor' y
      rw [← hy]
      exact (((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) y).2
    · rintro _ ⟨y, rfl⟩
      have hy := DFunLike.congr_fun hfactor' y
      rw [← hy]
      exact (((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n τ) y).1.2
  · rintro ⟨hA, hB⟩
    let cX := X.toSSetObjEquiv n σ
    let cB : C(stdSimplex ℝ (Fin (n.unop.len + 1)), (B : Set X)) :=
      ⟨fun y ↦ ⟨cX y, hB (Set.mem_range_self y)⟩,
        cX.continuous.subtype_mk _⟩
    let cI : C(stdSimplex ℝ (Fin (n.unop.len + 1)),
        TopPair.openExcisionIntersection A B) :=
      ⟨fun y ↦ ⟨cB y, hA (Set.mem_range_self y)⟩,
        cB.continuous.subtype_mk _⟩
    refine ⟨((TopCat.of (TopPair.openExcisionIntersection A B)).toSSetObjEquiv n).symm cI,
      ?_⟩
    apply (X.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply]
    -- Replace the composite by its pinned continuous-map normal form.
    calc
      ((TopPair.openExcisionSource A B).map ≫
            singularSubspaceInclusion X (B : Set X)).hom.comp cI =
          ((⟨Subtype.val, continuous_subtype_val⟩ : C((B : Set X), X)).comp
            (TopPair.openExcisionSource A B).map.hom).comp cI :=
        congrArg (fun k ↦ k.comp cI) (openExcisionComposite_hom A B)
      _ = X.toSSetObjEquiv n σ := by
        ext y
        rfl
  -/

/-- Helper for Remark 60.1: the nested open intersection realizes the
intersection of the two ambient singular-subcomplex ranges. -/
lemma range_openExcisionIntersection_eq_inf {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map
          ((TopPair.openExcisionSource A B).map ≫
            singularSubspaceInclusion X (B : Set X))) =
      SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) := by
  -- Evaluate both subcomplexes and use their common range-containment normal form.
  ext n σ
  simp only [Subfunctor.min_obj, Set.mem_inter_iff]
  rw [mem_range_openExcisionIntersection_iff,
    mem_range_singularSubspaceInclusion_iff,
    mem_range_singularSubspaceInclusion_iff]

/-- Helper for Remark 60.1: the nested-intersection singular set is canonically
identified with the intersection of the two ambient ranges. -/
noncomputable def openExcisionIntersectionRangeIso {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map
      ((TopPair.openExcisionSource A B).map ≫
        singularSubspaceInclusion X (B : Set X)))] :
    TopCat.toSSet.obj (TopPair.openExcisionSource A B).snd ≅
      ((SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) :
            (TopCat.toSSet.obj X).Subcomplex) : SSet) :=
  asIso (SSet.Subcomplex.toRange
    (TopCat.toSSet.map
      ((TopPair.openExcisionSource A B).map ≫
        singularSubspaceInclusion X (B : Set X)))) ≪≫
    SSet.Subcomplex.eqToIso (range_openExcisionIntersection_eq_inf A B)

/-- Helper for Remark 60.1: after inclusion into the ambient singular set, the
intersection range isomorphism is the original nested inclusion. -/
lemma openExcisionIntersectionRangeIso_hom_comp_inclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map
      ((TopPair.openExcisionSource A B).map ≫
        singularSubspaceInclusion X (B : Set X)))] :
    (openExcisionIntersectionRangeIso A B).hom ≫
        (SSet.Subcomplex.range
            (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) ⊓
          SSet.Subcomplex.range
            (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))).ι =
      TopCat.toSSet.map
        ((TopPair.openExcisionSource A B).map ≫
          singularSubspaceInclusion X (B : Set X)) := by
  -- All three maps retain the same underlying simplex; compare them componentwise
  -- to avoid matching category instances through the stored pair projections.
  ext n x
  rfl

/-- Helper for Remark 60.1: the stored ambient component of the open-excision
map is the ordinary singular-subspace inclusion of `B`. -/
lemma openExcisionHom_fst_eq_singularSubspaceInclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    TopPair.Hom.fst (TopPair.openExcisionHom A B) =
      singularSubspaceInclusion X (B : Set X) := by
  -- Both names denote the canonical inclusion of the subtype `B` into `X`.
  exact (TopPair.openExcisionHom_fst A B).trans
    (singularSubspaceInclusion_eq_ofSubset_map X (B : Set X)).symm

/-- Helper for Remark 60.1: the range of the stored right inclusion is the
range subcomplex named by the explicit inclusion of `B`. -/
lemma range_openExcisionHom_fst_eq_range_rightInclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B))) =
      SSet.Subcomplex.range
        (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) := by
  -- Apply the range construction to the pinned equality of ambient maps.
  exact congrArg SSet.Subcomplex.range
    (TopCat.toSSet.congr_map
      (openExcisionHom_fst_eq_singularSubspaceInclusion A B))

/-- Helper for Remark 60.1: transporting between equal singular subcomplexes
and then including into the ambient simplicial set recovers the original inclusion. -/
lemma subcomplexEqToIso_hom_comp_inclusion {X : SSet}
    {S T : X.Subcomplex} (h : S = T) :
    (eqToIso (congrArg (fun U : X.Subcomplex ↦ (U : SSet)) h)).hom ≫ T.ι = S.ι := by
  -- After identifying the subcomplexes, both sides are the same subtype inclusion.
  subst T
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- Helper for Remark 60.1: the source `B` of the stored open-excision ambient
map is canonically identified with its named singular range. -/
noncomputable def openExcisionRightRangeIso {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map
      (TopPair.Hom.fst (TopPair.openExcisionHom A B)))] :
    TopCat.toSSet.obj (TopPair.openExcisionSource A B).fst ≅
      (SSet.Subcomplex.range
        (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) : SSet) :=
  asIso (SSet.Subcomplex.toRange
    (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B)))) ≪≫
    eqToIso (congrArg
      (fun U : (TopCat.toSSet.obj X).Subcomplex ↦ (U : SSet))
      (range_openExcisionHom_fst_eq_range_rightInclusion A B))

/-- Helper for Remark 60.1: including the right range isomorphism into the
ambient singular set recovers the stored ambient component. -/
lemma openExcisionRightRangeIso_hom_comp_inclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map
      (TopPair.Hom.fst (TopPair.openExcisionHom A B)))] :
    (openExcisionRightRangeIso A B).hom ≫
        (SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))).ι =
      TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B)) := by
  -- First pass through the equality of ranges, then apply the `toRange` rule.
  rw [openExcisionRightRangeIso, Iso.trans_hom]
  calc
    (asIso (SSet.Subcomplex.toRange
        (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B))))).hom ≫
        (eqToIso (congrArg
          (fun U : (TopCat.toSSet.obj X).Subcomplex ↦ (U : SSet))
          (range_openExcisionHom_fst_eq_range_rightInclusion A B))).hom ≫
          (SSet.Subcomplex.range
            (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))).ι =
      (asIso (SSet.Subcomplex.toRange
        (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B))))).hom ≫
        ((eqToIso (congrArg
          (fun U : (TopCat.toSSet.obj X).Subcomplex ↦ (U : SSet))
          (range_openExcisionHom_fst_eq_range_rightInclusion A B))).hom ≫
          (SSet.Subcomplex.range
            (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))).ι) :=
      rfl
    _ = (asIso (SSet.Subcomplex.toRange
        (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B))))).hom ≫
          (SSet.Subcomplex.range
            (TopCat.toSSet.map
              (TopPair.Hom.fst (TopPair.openExcisionHom A B)))).ι :=
      congrArg
        (fun k ↦ (asIso (SSet.Subcomplex.toRange
          (TopCat.toSSet.map (TopPair.Hom.fst
            (TopPair.openExcisionHom A B))))).hom ≫ k)
        (subcomplexEqToIso_hom_comp_inclusion
          (range_openExcisionHom_fst_eq_range_rightInclusion A B))
    _ = TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B)) :=
      SSet.Subcomplex.toRange_ι _

/-- Helper for Remark 60.1: after passing through the right range isomorphism,
the intersection inclusion agrees with the direct composite into `B`'s range. -/
lemma openExcisionSource_map_comp_rightRangeIso_hom_comp_inclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map
      (TopPair.Hom.fst (TopPair.openExcisionHom A B)))] :
    TopCat.toSSet.map
        ((TopPair.openExcisionSource A B).map ≫
          singularSubspaceInclusion X (B : Set X)) =
      (TopCat.toSSet.map (TopPair.openExcisionSource A B).map ≫
        (openExcisionRightRangeIso A B).hom) ≫
          (SSet.Subcomplex.range
            (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))).ι := by
  -- Normalize the direct composite and the range composite to the stored ambient map.
  exact (TopCat.toSSet.map_comp _ _).trans
    ((congrArg
      (fun k ↦ TopCat.toSSet.map (TopPair.openExcisionSource A B).map ≫
        TopCat.toSSet.map k)
      (openExcisionHom_fst_eq_singularSubspaceInclusion A B).symm).trans
        ((congrArg
          (fun k ↦ TopCat.toSSet.map (TopPair.openExcisionSource A B).map ≫ k)
          (openExcisionRightRangeIso_hom_comp_inclusion A B)).symm.trans
            (Category.assoc _ _ _).symm))

/-- Helper for Remark 60.1: the open subspace `A` is canonically identified
with the range of its singular-subspace inclusion. -/
noncomputable def openExcisionLeftRangeIso {X : TopCat}
    (A : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)))] :
    TopCat.toSSet.obj (TopCat.of (A : Set X)) ≅
      (SSet.Subcomplex.range
        (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) : SSet) :=
  asIso (SSet.Subcomplex.toRange
    (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))))

/-- Helper for Remark 60.1: including the left range isomorphism into the
ambient singular set recovers the inclusion of `A`. -/
lemma openExcisionLeftRangeIso_hom_comp_inclusion {X : TopCat}
    (A : TopologicalSpace.Opens X)
    [Mono (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)))] :
    (openExcisionLeftRangeIso A).hom ≫
        (SSet.Subcomplex.range
          (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)))).ι =
      TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)) := by
  -- This is the defining computation rule for the map to a morphism's range.
  exact SSet.Subcomplex.toRange_ι _

/-- Helper for Remark 60.1: the singular square formed by the two opens and
their nested intersection is a pushout onto the two-open small subcomplex. -/
lemma twoOpenSmallSSet_isPushout {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    IsPushout
      (TopCat.toSSet.map (TopPair.openExcisionSource A B).map)
      (TopCat.toSSet.map (TopPair.openExcisionIntersectionToLeft A B))
      (twoOpenSmallRightSSetMap A B)
      (twoOpenSmallLeftSSetMap A B) := by
  -- The three subtype inclusions are monic, so their maps to their ranges are isomorphisms.
  letI : Mono (TopPair.openExcisionSource A B).map :=
    (TopCat.mono_iff_injective _).mpr
      (TopPair.openExcisionSource A B).isEmbedding_map.injective
  letI : Mono (singularSubspaceInclusion X (A : Set X)) := by
    rw [singularSubspaceInclusion_eq_ofSubset_map]
    exact (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (A : Set X)).isEmbedding_map.injective
  letI : Mono (singularSubspaceInclusion X (B : Set X)) := by
    rw [singularSubspaceInclusion_eq_ofSubset_map]
    exact (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (B : Set X)).isEmbedding_map.injective
  letI : Mono (TopPair.ofSubset (B : Set X)).map :=
    (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (B : Set X)).isEmbedding_map.injective
  letI : Mono
      ((TopPair.openExcisionSource A B).map ≫
        singularSubspaceInclusion X (B : Set X)) :=
    by
      -- The composite is injective because both nested subtype inclusions are.
      apply (TopCat.mono_iff_injective _).mpr
      rw [singularSubspaceInclusion_eq_ofSubset_map]
      exact (TopPair.ofSubset (B : Set X)).isEmbedding_map.injective.comp
        (TopPair.openExcisionSource A B).isEmbedding_map.injective
  letI : Mono
      (TopCat.toSSet.map
        ((TopPair.openExcisionSource A B).map ≫
          singularSubspaceInclusion X (B : Set X))) := inferInstance
  letI : Mono
      (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) :=
    inferInstance
  letI : Mono
      (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X))) :=
    inferInstance
  letI : Mono (TopPair.Hom.fst (TopPair.openExcisionHom A B)) := by
    rw [TopPair.openExcisionHom_fst]
    exact (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (B : Set X)).isEmbedding_map.injective
  letI : Mono
      (TopCat.toSSet.map (TopPair.Hom.fst (TopPair.openExcisionHom A B))) :=
    inferInstance
  let rangeA := SSet.Subcomplex.range
    (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)))
  let rangeB := SSet.Subcomplex.range
    (TopCat.toSSet.map (singularSubspaceInclusion X (B : Set X)))
  let small := smallSingularSubcomplex X
    (fun b : Bool ↦ (Bool.rec A B b : Set X))
  have hsup : rangeB ⊔ rangeA = small := by
    -- The supremum over `Bool` lists `B` and then `A`.
    dsimp only [small, rangeA, rangeB]
    exact (smallSingularSubcomplex_opens_bool X A B).symm
  -- Route correction: use the global union/intersection pushout instead of
  -- constructing an inverse on degreewise quotient representatives.
  let sq : SSet.Subcomplex.BicartSq (rangeA ⊓ rangeB) rangeB rangeA small :=
    { sup_eq := hsup, inf_eq := inf_comm _ _ }
  have hpush := sq.isPushout
  -- Transport the lattice pushout across the three canonical range isomorphisms.
  refine hpush.of_iso' (openExcisionIntersectionRangeIso A B)
    (openExcisionRightRangeIso A B) (openExcisionLeftRangeIso A)
      (Iso.refl _) ?_ ?_ ?_ ?_
  · -- Compare both intersection-to-`B` maps after ambient inclusion.
    apply (cancel_mono rangeB.ι).mp
    calc
      ((openExcisionIntersectionRangeIso A B).hom ≫
          SSet.Subcomplex.homOfLE inf_le_right) ≫ rangeB.ι =
        (openExcisionIntersectionRangeIso A B).hom ≫
          (rangeA ⊓ rangeB).ι := by
        rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
      _ = TopCat.toSSet.map
          ((TopPair.openExcisionSource A B).map ≫
            singularSubspaceInclusion X (B : Set X)) :=
        openExcisionIntersectionRangeIso_hom_comp_inclusion A B
      _ = (TopCat.toSSet.map (TopPair.openExcisionSource A B).map ≫
          (openExcisionRightRangeIso A B).hom) ≫ rangeB.ι :=
        openExcisionSource_map_comp_rightRangeIso_hom_comp_inclusion A B
  · -- Compare both intersection-to-`A` maps after ambient inclusion.
    apply (cancel_mono rangeA.ι).mp
    calc
      ((openExcisionIntersectionRangeIso A B).hom ≫
          SSet.Subcomplex.homOfLE inf_le_left) ≫ rangeA.ι =
        (openExcisionIntersectionRangeIso A B).hom ≫
          (rangeA ⊓ rangeB).ι := by
        rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
      _ = TopCat.toSSet.map
          ((TopPair.openExcisionSource A B).map ≫
            singularSubspaceInclusion X (B : Set X)) :=
        openExcisionIntersectionRangeIso_hom_comp_inclusion A B
      _ = TopCat.toSSet.map
          (TopPair.openExcisionIntersectionToLeft A B ≫
            singularSubspaceInclusion X (A : Set X)) := by
        apply TopCat.toSSet.congr_map
        rw [singularSubspaceInclusion_eq_ofSubset_map,
          singularSubspaceInclusion_eq_ofSubset_map]
        exact (TopPair.openExcisionIntersection_square A B).symm
      _ = TopCat.toSSet.map (TopPair.openExcisionIntersectionToLeft A B) ≫
          TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X)) :=
        TopCat.toSSet.map_comp _ _
      _ = (TopCat.toSSet.map (TopPair.openExcisionIntersectionToLeft A B) ≫
          (openExcisionLeftRangeIso A).hom) ≫ rangeA.ι := by
        exact (congrArg
          (fun k ↦ TopCat.toSSet.map
            (TopPair.openExcisionIntersectionToLeft A B) ≫ k)
          (openExcisionLeftRangeIso_hom_comp_inclusion A)).symm.trans
            (Category.assoc _ _ _).symm
  · -- Compare the right legs after inclusion into the ambient singular set.
    apply (cancel_mono small.ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      Iso.refl_hom, Category.comp_id]
    exact (openExcisionRightRangeIso_hom_comp_inclusion A B).trans
      ((TopCat.toSSet.congr_map
        (openExcisionHom_fst_eq_singularSubspaceInclusion A B)).trans
          (twoOpenSmallRightSSetMap_comp_inclusion A B).symm)
  · -- Compare the left legs after inclusion into the ambient singular set.
    apply (cancel_mono small.ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      Iso.refl_hom, Category.comp_id]
    exact (openExcisionLeftRangeIso_hom_comp_inclusion A).trans
      (twoOpenSmallLeftSSetMap_comp_inclusion A B).symm

/-- Helper for Remark 60.1: the integral chain map from chains on `A` into the
two-open small chain complex. -/
noncomputable abbrev integralTwoOpenSmallLeftInclusion {X : TopCat}
    (A B : TopologicalSpace.Opens X) :=
  SSet.chainComplexMap (twoOpenSmallLeftSSetMap A B) (ModuleCat.of ℤ ℤ)

/-- Helper for Remark 60.1: applying integral simplicial chains to the
two-open singular pushout again gives a pushout square. -/
lemma integralTwoOpenSmallChain_isPushout {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    IsPushout
      (integralSingularChainComplexFunctor.map
        (TopPair.openExcisionSource A B).map)
      (integralSingularChainComplexFunctor.map
        (TopPair.openExcisionIntersectionToLeft A B))
      (integralTwoOpenSmallRightInclusion A B)
      (integralTwoOpenSmallLeftInclusion A B) := by
  let chainFunctor : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
    (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  -- Colimits of chain complexes are detected degreewise; each degree is free
  -- module formation after evaluating the simplicial set.
  letI : PreservesColimitsOfShape WalkingSpan chainFunctor :=
    HomologicalComplex.preservesColimitsOfShape_of_eval chainFunctor fun n ↦
      preservesColimitsOfShape_of_natIso
        (Iso.refl
          (((evaluation SimplexCategoryᵒᵖ Type).obj
              (Opposite.op (SimplexCategory.mk n))) ⋙
            sigmaConst.obj (ModuleCat.of ℤ ℤ)))
  -- Functoriality identifies the mapped square with the four named chain maps.
  exact (twoOpenSmallSSet_isPushout A B).map chainFunctor

/-- Helper for Remark 60.1: integral singular chains identify the explicit
subspace inclusion with the map of its canonical topological pair. -/
lemma integralSingularChainMap_subspace_eq_pairMap (X : TopCat) (A : Set X) :
    integralSingularChainComplexFunctor.map (singularSubspaceInclusion X A) =
      integralSingularChainComplexFunctor.map (TopPair.ofSubset A).map := by
  -- Functoriality transports the owner-level equality of the two inclusion maps.
  exact integralSingularChainComplexFunctor.congr_map
    (singularSubspaceInclusion_eq_ofSubset_map X A)

/-- Helper for Remark 60.1: the small inclusion followed by the ambient
inclusion is the ordinary chain map induced by `A ⊆ X`. -/
lemma integralTwoOpenSmallLeftInclusion_comp {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallLeftInclusion A B ≫
        integralSmallSingularChainInclusion X
          (fun b : Bool ↦ (Bool.rec A B b : Set X)) =
      integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map := by
  -- First compute the simplicial composite, then cross to the pair-map spelling once.
  rw [← integralSingularChainMap_subspace_eq_pairMap X (A : Set X)]
  rw [← Functor.map_comp, twoOpenSmallLeftSSetMap_comp_inclusion]
  rfl

/-- Helper for Remark 60.1: the small inclusion from `B`, followed by the
ambient inclusion, is the ordinary chain map induced by `B ⊆ X`. -/
lemma integralTwoOpenSmallRightInclusion_comp {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallRightInclusion A B ≫
        integralSmallSingularChainInclusion X
          (fun b : Bool ↦ (Bool.rec A B b : Set X)) =
      integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (B : Set X)).map := by
  -- First compute the simplicial composite, then cross to the pair-map spelling once.
  rw [← integralSingularChainMap_subspace_eq_pairMap X (B : Set X)]
  rw [← Functor.map_comp, twoOpenSmallRightSSetMap_comp_inclusion]
  rfl

/-- Helper for Remark 60.1: the right small-chain inclusion followed by the
ambient inclusion is the ambient component of the open-excision pair map. -/
lemma integralTwoOpenSmallRightInclusion_comp_openExcisionHom_fst {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallRightInclusion A B ≫
        integralSmallSingularChainInclusion X
          (fun b : Bool ↦ (Bool.rec A B b : Set X)) =
      integralSingularChainComplexFunctor.map
        (TopPair.Hom.fst (TopPair.openExcisionHom A B)) := by
  -- Cross from the explicit `B` inclusion to the stored pair projection once.
  calc
    _ = integralSingularChainComplexFunctor.map
          (TopPair.ofSubset (B : Set X)).map :=
      integralTwoOpenSmallRightInclusion_comp A B
    _ = integralSingularChainComplexFunctor.map
          (TopPair.Hom.fst (TopPair.openExcisionHom A B)) :=
      integralSingularChainComplexFunctor.congr_map
        (TopPair.openExcisionHom_fst A B).symm

/-- Helper for Remark 60.1: after the target relative quotient, the right
small-chain factorization is the defining open-excision relative-chain map. -/
lemma integralTwoOpenSmallRightInclusion_comp_relativeQuotient {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    (integralTwoOpenSmallRightInclusion A B ≫
        integralSmallSingularChainInclusion X
          (fun b : Bool ↦ (Bool.rec A B b : Set X))) ≫
      cokernel.π (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map) =
    cokernel.π (integralSingularChainComplexFunctor.map
        (TopPair.openExcisionSource A B).map) ≫
      relativeIntegralSingularChainMapExplicit
        (TopPair.openExcisionHom A B) := by
  -- First identify the ambient map, then use the cokernel-map computation rule.
  exact (congrArg
    (fun k ↦ k ≫ cokernel.π (integralSingularChainComplexFunctor.map
      (TopPair.ofSubset (A : Set X)).map))
    (integralTwoOpenSmallRightInclusion_comp_openExcisionHom_fst A B)).trans
      (relativeIntegralSingularChainMapExplicit_π
        (TopPair.openExcisionHom A B)).symm

/-- Helper for Remark 60.1: the right-associated small-chain factorization has
the same relative-quotient comparison as its left-associated form. -/
lemma integralTwoOpenSmallRightInclusion_comp_relativeQuotient_assoc {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallRightInclusion A B ≫
        (integralSmallSingularChainInclusion X
            (fun b : Bool ↦ (Bool.rec A B b : Set X)) ≫
          cokernel.π (integralSingularChainComplexFunctor.map
            (TopPair.ofSubset (A : Set X)).map)) =
      cokernel.π (integralSingularChainComplexFunctor.map
          (TopPair.openExcisionSource A B).map) ≫
        relativeIntegralSingularChainMapExplicit
          (TopPair.openExcisionHom A B) := by
  -- Reassociate once, then apply the pinned relative-quotient comparison.
  exact (Category.assoc _ _ _).symm.trans
    (integralTwoOpenSmallRightInclusion_comp_relativeQuotient A B)

/-- Helper for Remark 60.1: the two-open chain factorization also has the
identity-normalized form required by `cokernel.map`. -/
lemma integralTwoOpenSmallLeftInclusion_comp_id {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallLeftInclusion A B ≫
        integralSmallSingularChainInclusion X
          (fun b : Bool ↦ (Bool.rec A B b : Set X)) =
      𝟙 _ ≫ integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map := by
  -- Insert the identity on chains of `A` into the established factorization.
  rw [Category.id_comp]
  exact integralTwoOpenSmallLeftInclusion_comp A B

/-- Helper for Remark 60.1: chains on the left open set inject into the
two-open small singular chain complex. -/
lemma integralTwoOpenSmallLeftInclusion_mono {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    Mono (integralTwoOpenSmallLeftInclusion A B) := by
  -- Normalize the ambient inclusion to the canonical embedded-pair map.
  letI : Mono (singularSubspaceInclusion X (A : Set X)) := by
    rw [singularSubspaceInclusion_eq_ofSubset_map]
    exact (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (A : Set X)).isEmbedding_map.injective
  -- The singular-set functor carries this injective inclusion to a monomorphism.
  letI : Mono
      (TopCat.toSSet.map (singularSubspaceInclusion X (A : Set X))) :=
    inferInstance
  -- Cancel the monic ambient inclusion from the established simplicial factorization.
  letI : Mono (twoOpenSmallLeftSSetMap A B) :=
    mono_of_mono_fac (twoOpenSmallLeftSSetMap_comp_inclusion A B)
  -- Integral simplicial chains preserve the resulting simplicial monomorphism.
  letI := integralSimplicialChainComplex_preservesMonomorphisms
  infer_instance


/-- Helper for Remark 60.1: the two-open small relative chain complex is the
quotient of small chains by chains supported in `A`. -/
@[expose]
noncomputable def twoOpenSmallRelativeChainComplex {X : TopCat}
    (A B : TopologicalSpace.Opens X) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (integralTwoOpenSmallLeftInclusion A B)

/-- Helper for Remark 60.1: the pushout square induces the canonical map from
relative chains on `(B, A ∩ B)` to the two-open small relative quotient. -/
noncomputable def openExcisionSourceRelativeChainComparison {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    cokernel (integralSingularChainComplexFunctor.map
      (TopPair.openExcisionSource A B).map) ⟶
      twoOpenSmallRelativeChainComplex A B :=
  cokernel.map
    (integralSingularChainComplexFunctor.map
      (TopPair.openExcisionSource A B).map)
    (integralTwoOpenSmallLeftInclusion A B)
    (integralSingularChainComplexFunctor.map
      (TopPair.openExcisionIntersectionToLeft A B))
    (integralTwoOpenSmallRightInclusion A B)
    (integralTwoOpenSmallChain_isPushout A B).w

/-- Helper for Remark 60.1: the source-relative comparison has the expected
formula after the source cokernel projection. -/
lemma openExcisionSourceRelativeChainComparison_π {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    cokernel.π (integralSingularChainComplexFunctor.map
        (TopPair.openExcisionSource A B).map) ≫
      openExcisionSourceRelativeChainComparison A B =
    integralTwoOpenSmallRightInclusion A B ≫
      cokernel.π (integralTwoOpenSmallLeftInclusion A B) := by
  -- This is the projection computation rule for the cokernel map induced by the pushout.
  dsimp only [openExcisionSourceRelativeChainComparison,
    twoOpenSmallRelativeChainComplex, cokernel.map]
  rw [cokernel.π_desc]
  rfl

/-- Helper for Remark 60.1: the canonical source-relative comparison induced
by the two-open chain pushout is an isomorphism. -/
lemma openExcisionSourceRelativeChainComparison_isIso {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    IsIso (openExcisionSourceRelativeChainComparison A B) := by
  -- A pushout induces an isomorphism between the corresponding cokernels.
  exact isIso_cokernel_map_of_isPushout
    (integralTwoOpenSmallChain_isPushout A B)

/-- Helper for Remark 60.1: chains on `A`, two-open small chains, and their
quotient form the canonical short complex. -/
@[expose]
noncomputable def twoOpenSmallRelativeChainShortComplex {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (integralTwoOpenSmallLeftInclusion A B)
    (cokernel.π (integralTwoOpenSmallLeftInclusion A B))
    (cokernel.condition (integralTwoOpenSmallLeftInclusion A B))

/-- Helper for Remark 60.1: the first map of the named small-relative row is
the left small-chain inclusion. -/
lemma twoOpenSmallRelativeChainShortComplex_f {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    (twoOpenSmallRelativeChainShortComplex A B).f =
      integralTwoOpenSmallLeftInclusion A B := by
  -- Read the first projection from the canonical cokernel short complex.
  rfl

/-- Helper for Remark 60.1: the two-open small quotient maps to the explicit
ordinary quotient `C(X) / C(A)`. -/
noncomputable def twoOpenSmallRelativeChainComparisonExplicit {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    twoOpenSmallRelativeChainComplex A B ⟶
      cokernel (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map) :=
  cokernel.map
    (integralTwoOpenSmallLeftInclusion A B)
    (integralSingularChainComplexFunctor.map
      (TopPair.ofSubset (A : Set X)).map)
    (𝟙 _)
    (integralSmallSingularChainInclusion X
      (fun b : Bool ↦ (Bool.rec A B b : Set X)))
    (integralTwoOpenSmallLeftInclusion_comp_id A B)

/-- Helper for Remark 60.1: the explicit small-relative comparison commutes
with the two quotient projections. -/
lemma twoOpenSmallRelativeChainComparisonExplicit_π {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralSmallSingularChainInclusion X
        (fun b : Bool ↦ (Bool.rec A B b : Set X)) ≫
      cokernel.π (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map) =
    cokernel.π (integralTwoOpenSmallLeftInclusion A B) ≫
      twoOpenSmallRelativeChainComparisonExplicit A B := by
  -- This is the defining projection equation for the induced cokernel map.
  dsimp only [twoOpenSmallRelativeChainComparisonExplicit,
    twoOpenSmallRelativeChainComplex, cokernel.map]
  rw [cokernel.π_desc]
  rfl

/-- Helper for Remark 60.1: the right small-chain map followed by the two
relative comparison stages is the explicit open-excision relative map. -/
lemma integralTwoOpenSmallRightInclusion_comp_twoOpenRelativeComparison {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    integralTwoOpenSmallRightInclusion A B ≫
        (cokernel.π (integralTwoOpenSmallLeftInclusion A B) ≫
          twoOpenSmallRelativeChainComparisonExplicit A B) =
      cokernel.π (integralSingularChainComplexFunctor.map
          (TopPair.openExcisionSource A B).map) ≫
        relativeIntegralSingularChainMapExplicit
          (TopPair.openExcisionHom A B) := by
  -- Replace the small quotient comparison, then use the right-associated bridge.
  exact (congrArg
    (fun k ↦ integralTwoOpenSmallRightInclusion A B ≫ k)
    (twoOpenSmallRelativeChainComparisonExplicit_π A B).symm).trans
      (integralTwoOpenSmallRightInclusion_comp_relativeQuotient_assoc A B)

/-- Helper for Remark 60.1: the left-associated source comparison has the same
explicit open-excision relative-chain normal form. -/
lemma openExcisionSourceComparison_comp_twoOpenRelativeComparison {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    (integralTwoOpenSmallRightInclusion A B ≫
        cokernel.π (integralTwoOpenSmallLeftInclusion A B)) ≫
          twoOpenSmallRelativeChainComparisonExplicit A B =
      cokernel.π (integralSingularChainComplexFunctor.map
          (TopPair.openExcisionSource A B).map) ≫
        relativeIntegralSingularChainMapExplicit
          (TopPair.openExcisionHom A B) := by
  -- Reassociate to the already normalized two-stage comparison.
  exact (Category.assoc _ _ _).trans
    (integralTwoOpenSmallRightInclusion_comp_twoOpenRelativeComparison A B)

/-- Helper for Remark 60.1: for a two-open cover, the small relative quotient
maps quasi-isomorphically to the explicit ambient relative quotient. -/
lemma twoOpenSmallRelativeChainComparisonExplicit_quasiIso {X : TopCat}
    (A B : TopologicalSpace.Opens X)
    (hAB : TopologicalSpace.IsOpenCover (Bool.rec A B)) :
    QuasiIso
      (twoOpenSmallRelativeChainComparisonExplicit A B) := by
  -- Route correction: do not mix the evaluated relative-chain functor with the
  -- explicit cokernel here; compare two explicit cokernel rows first.
  -- Keep the target in the explicit objectwise-cokernel normal form.
  let ordinaryRow : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk
      (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map)
      (cokernel.π (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map))
      (cokernel.condition (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map))
  let ambientInclusion := integralSmallSingularChainInclusion X
    (fun b : Bool ↦ (Bool.rec A B b : Set X))
  -- The identity, small-chain inclusion, and cokernel comparison form a map of rows.
  let comparison : twoOpenSmallRelativeChainShortComplex A B ⟶ ordinaryRow :=
    ShortComplex.homMk
      (𝟙 _)
      ambientInclusion
      (twoOpenSmallRelativeChainComparisonExplicit A B)
      (integralTwoOpenSmallLeftInclusion_comp_id A B).symm
      (twoOpenSmallRelativeChainComparisonExplicit_π A B)
  -- Monicity of each first map makes both canonical cokernel rows short exact.
  letI : Mono (integralTwoOpenSmallLeftInclusion A B) :=
    integralTwoOpenSmallLeftInclusion_mono A B
  letI : Mono (TopPair.ofSubset (A : Set X)).map :=
    (TopCat.mono_iff_injective _).mpr
      (TopPair.ofSubset (A : Set X)).isEmbedding_map.injective
  letI : Mono
      (integralSingularChainComplexFunctor.map
        (TopPair.ofSubset (A : Set X)).map) := inferInstance
  have hsmallRow : (twoOpenSmallRelativeChainShortComplex A B).ShortExact := by
    -- Unfold this row once so the installed monomorphism matches its first map.
    dsimp only [twoOpenSmallRelativeChainShortComplex]
    exact { exact := ShortComplex.exact_cokernel _ }
  have hordinaryRow : ordinaryRow.ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hcomparisonOne : QuasiIso comparison.τ₁ := by
    -- The first component of the row comparison is the identity.
    have hcomparisonOneId : comparison.τ₁ = 𝟙 _ := by
      rfl
    -- Local instance justification (comparison): the component is propositionally
    -- the identity, so expose that canonical isomorphism to the quasi-isomorphism API.
    letI : IsIso comparison.τ₁ := by
      rw [hcomparisonOneId]
      exact IsIso.id _
    infer_instance
  have hcomparisonTwo : QuasiIso comparison.τ₂ := by
    -- Unfold only the comparison projection, then use the compiled small-chain theorem.
    have hcomparisonTwoComponent : comparison.τ₂ = ambientInclusion := by
      rfl
    have hcoverSets :
        (fun b : Bool ↦ (Bool.rec (A : Set X) (B : Set X) b)) =
          (fun b : Bool ↦
            ((Bool.rec A B b : TopologicalSpace.Opens X) : Set X)) := by
      funext b
      cases b <;> rfl
    have hambient : QuasiIso ambientInclusion := by
      dsimp only [ambientInclusion]
      exact BarycentricSubdivision.integralSmallSingularChainInclusion_quasiIso_of_eq
        (fun b : Bool ↦ Bool.rec (A : Set X) (B : Set X) b)
        (fun b ↦ Bool.rec A B b) hcoverSets hAB
    exact hcomparisonTwoComponent.symm ▸ hambient
  -- The first component is an identity and the second is the small-chain quasi-isomorphism.
  have hcomparison : QuasiIso comparison.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃
      comparison hsmallRow hordinaryRow hcomparisonOne hcomparisonTwo
  exact hcomparison

/-- Helper for Remark 60.1: the two compiled open-excision comparison stages
are the explicit objectwise relative-chain map of the pair morphism. -/
lemma openExcisionRelativeChainComparisonExplicit_eq {X : TopCat}
    (A B : TopologicalSpace.Opens X) :
    openExcisionSourceRelativeChainComparison A B ≫
        twoOpenSmallRelativeChainComparisonExplicit A B =
      relativeIntegralSingularChainMapExplicit (TopPair.openExcisionHom A B) := by
  -- Cancel the source quotient and compare the induced maps on ambient chains.
  apply (cancel_epi (cokernel.π (integralSingularChainComplexFunctor.map
    (TopPair.openExcisionSource A B).map))).mp
  rw [← Category.assoc, openExcisionSourceRelativeChainComparison_π]
  exact openExcisionSourceComparison_comp_twoOpenRelativeComparison A B

/-- Helper for Remark 60.1: relative integral singular chains satisfy excision
for a cover by two open subspaces. -/
lemma relativeIntegralSingularChainExcision_quasiIso_of_isOpenCover
    {X : TopCat} (A B : TopologicalSpace.Opens X)
    (hAB : TopologicalSpace.IsOpenCover (Bool.rec A B)) :
    QuasiIso
      (relativeIntegralSingularChainComplexFunctor.map
        (TopPair.openExcisionHom A B)) := by
  -- The pushout comparison is an isomorphism and the small-chain comparison is a quasi-isomorphism.
  letI : IsIso (openExcisionSourceRelativeChainComparison A B) :=
    openExcisionSourceRelativeChainComparison_isIso A B
  letI : QuasiIso
      (twoOpenSmallRelativeChainComparisonExplicit A B) :=
    twoOpenSmallRelativeChainComparisonExplicit_quasiIso A B hAB
  have hexplicit : QuasiIso
      (relativeIntegralSingularChainMapExplicit
        (TopPair.openExcisionHom A B)) := by
    rw [← openExcisionRelativeChainComparisonExplicit_eq]
    infer_instance
  letI : QuasiIso
      (relativeIntegralSingularChainMapExplicit
        (TopPair.openExcisionHom A B)) := hexplicit
  letI : QuasiIso
      (relativeIntegralSingularChainComplexObjIso
        (TopPair.openExcisionSource A B)).hom := inferInstance
  -- Transport the explicit quasi-isomorphism through the objectwise cokernel comparisons.
  have htransported : QuasiIso
      (relativeIntegralSingularChainComplexFunctor.map
          (TopPair.openExcisionHom A B) ≫
        (relativeIntegralSingularChainComplexObjIso
          (TopPair.ofSubset (A : Set X))).hom) := by
    rw [← relativeIntegralSingularChainComplexObjIso_naturality]
    exact quasiIso_comp
      (relativeIntegralSingularChainComplexObjIso
        (TopPair.openExcisionSource A B)).hom
      (relativeIntegralSingularChainMapExplicit
        (TopPair.openExcisionHom A B))
  letI : QuasiIso
      (relativeIntegralSingularChainComplexFunctor.map
          (TopPair.openExcisionHom A B) ≫
        (relativeIntegralSingularChainComplexObjIso
          (TopPair.ofSubset (A : Set X))).hom) := htransported
  letI : QuasiIso
      (relativeIntegralSingularChainComplexObjIso
        (TopPair.ofSubset (A : Set X))).hom := inferInstance
  -- Cancel the target object isomorphism from the transported composite.
  exact quasiIso_of_comp_right
    (relativeIntegralSingularChainComplexFunctor.map
      (TopPair.openExcisionHom A B))
    (relativeIntegralSingularChainComplexObjIso
      (TopPair.ofSubset (A : Set X))).hom

end AlgebraicTopology

namespace RealProjectivePlane

open CategoryTheory CategoryTheory.Limits

open AlgebraicTopology

/-- Helper for Remark 60.1: a point of the unit sphere is distinct from its antipode. -/
lemma spherePoint_ne_antipode
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : x ≠ -x := by
  -- The nonzero radius prevents a sphere point from being fixed by negation.
  intro hx
  have hxval : (x : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3)) :=
    congrArg Subtype.val hx
  have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hxval
  have hzero : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [Metric.mem_sphere] using x.2
  simpa [hzero] using hnorm

/-- Helper for Remark 60.1: every fiber of the projective-plane quotient consists of a
sphere point and its antipode. -/
lemma quotientMap_fiber_eq_pair
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    quotientMap ⁻¹' {quotientMap x} = {x, -x} := by
  -- Rewrite membership in the fiber using the quotient's equal-or-antipodal criterion.
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, quotientMap_eq_iff,
    Set.mem_insert_iff]
  constructor
  · rintro (rfl | hy)
    · exact Or.inl rfl
    · exact Or.inr (by simpa using (congrArg Neg.neg hy).symm)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (by simp)

/-- Helper for Remark 60.1: every fiber of the projective-plane quotient is finite. -/
lemma quotientMap_fiber_finite (p : RealProjectivePlane) :
    (quotientMap ⁻¹' {p}).Finite := by
  -- Choose a sphere representative and use the explicit two-point fiber description.
  obtain ⟨x, rfl⟩ := quotientMap_isQuotientMap.surjective p
  rw [quotientMap_fiber_eq_pair]
  exact Set.toFinite {x, -x}

/-- Helper for Remark 60.1: every fiber of the projective-plane quotient has exactly
two points. -/
lemma quotientMap_fiber_ncard (p : RealProjectivePlane) :
    (quotientMap ⁻¹' {p}).ncard = 2 := by
  -- Represent the base point by a sphere point and count the antipodal pair.
  obtain ⟨x, rfl⟩ := quotientMap_isQuotientMap.surjective p
  rw [quotientMap_fiber_eq_pair, Set.ncard_pair (spherePoint_ne_antipode x)]

/-- Helper for Remark 60.1: an element of an additive torsion-free commutative monoid
annihilated by two is zero. -/
lemma eq_zero_of_two_nsmul_eq_zero
    {A : Type*} [AddCommMonoid A] [IsAddTorsionFree A]
    {x : A} (hx : 2 • x = 0) : x = 0 := by
  -- Cancel the nonzero natural scalar `2` from the given equality.
  have htwo : (2 : ℕ) ≠ 0 := by
    norm_num
  exact nsmul_right_injective htwo (by simpa using hx)

/-- Helper for Remark 60.1: two-torsion vanishes after transport to an additive
torsion-free commutative monoid. -/
lemma eq_zero_of_two_nsmul_eq_zero_after_addEquiv
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] [IsAddTorsionFree B]
    (e : A ≃+ B) {x : A} (hx : 2 • x = 0) : x = 0 := by
  -- Map the torsion equation across the equivalence and cancel two in the target.
  have hmap : 2 • e x = 0 := by
    simpa using congrArg e hx
  apply e.injective
  simpa using eq_zero_of_two_nsmul_eq_zero hmap

/-- Helper for Remark 60.1: reduced integral zero-chains on the connected components
of the complement of `K`, represented by the kernel of augmentation. -/
noncomputable abbrev ReducedComplementComponentChains
    (K : Set (EuclideanSpace ℝ (Fin 3))) :=
  -- Summing coefficients gives the augmentation whose kernel models reduced `H₀`.
  LinearMap.ker
    (Finsupp.lsum ℤ
      (fun _ : ZerothHomotopy (Kᶜ : Set (EuclideanSpace ℝ (Fin 3))) =>
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))

/-- Helper for Remark 60.1: singular homology in degree zero is the free integral
module on the path components represented by `ZerothHomotopy`. -/
noncomputable def singularHomologyZeroIsoFinsupp (X : TopCat) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj X ≅
      ModuleCat.of ℤ (ZerothHomotopy X →₀ ℤ) :=
  letI := Classical.decEq (ZerothHomotopy X)
  TopCat.singularHomology₀Iso X (ModuleCat.of ℤ ℤ) ≪≫
    ModuleCat.coprodIsoDirectSum (fun _ : ZerothHomotopy X ↦ ModuleCat.of ℤ ℤ) ≪≫
      (finsuppLEquivDirectSum ℤ ℤ (ZerothHomotopy X)).symm.toModuleIso

/-- Helper for Remark 60.1: the standard coproduct-to-Finsupp isomorphism identifies
the coproduct fold with the Finsupp coefficient sum. -/
lemma coprodIsoDirectSum_hom_comp_finsuppAugmentation (ι : Type) [DecidableEq ι] :
    (ModuleCat.coprodIsoDirectSum (fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom ≫
        (finsuppLEquivDirectSum ℤ ℤ ι).symm.toModuleIso.hom ≫
          ModuleCat.ofHom
            (Finsupp.lsum ℤ (fun _ : ι ↦ (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) =
      Sigma.desc (fun _ : ι ↦ 𝟙 (ModuleCat.of ℤ ℤ)) := by
  -- It suffices to compare both maps on every coproduct generator.
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, Sigma.ι_desc]
  ext
  simp [finsuppLEquivDirectSum_symm_lof]

/-- Helper for Remark 60.1: the coproduct-to-Finsupp identification carries the
coproduct fold map to summation of finitely supported coefficients. -/
lemma singularHomologyZeroIsoFinsupp_hom_comp_augmentation (X : TopCat) :
    (singularHomologyZeroIsoFinsupp X).hom ≫
        ModuleCat.ofHom
          (Finsupp.lsum ℤ
            (fun _ : ZerothHomotopy X ↦ (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
  -- First identify the Finsupp sum with the fold map out of the categorical coproduct.
  classical
  rw [singularHomologyZeroIsoFinsupp, Iso.trans_hom, Iso.trans_hom]
  rw [Category.assoc, Category.assoc,
    coprodIsoDirectSum_hom_comp_finsuppAugmentation]
  rw [TopCat.singularHomology₀Iso_sigma_desc_id]

/-- Helper for Remark 60.1: canonical reduced singular `H₀` is linearly equivalent
to the augmentation kernel on finitely supported path-component chains. -/
lemma nonempty_reducedSingularHomologyZero_linearEquiv_componentChains
    (K : Set (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
      (ReducedSingularHomologyZero (TopCat.of (Kᶜ : Set (EuclideanSpace ℝ (Fin 3)))) ≃ₗ[ℤ]
        ReducedComplementComponentChains K) := by
  -- Transport the augmentation kernel across the normalized singular-H₀ isomorphism.
  let X := TopCat.of (Kᶜ : Set (EuclideanSpace ℝ (Fin 3)))
  let ε := X.singularHomology₀ε (ModuleCat.of ℤ ℤ)
  let σ := ModuleCat.ofHom
    (Finsupp.lsum ℤ
      (fun _ : ZerothHomotopy X ↦ (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
  have hcompat : ε ≫ (Iso.refl _).hom = (singularHomologyZeroIsoFinsupp X).hom ≫ σ := by
    simpa [ε, σ] using (singularHomologyZeroIsoFinsupp_hom_comp_augmentation X).symm
  -- The categorical kernel in the target is the ordinary linear-map kernel.
  exact
    ⟨(kernel.mapIso ε σ (singularHomologyZeroIsoFinsupp X) (Iso.refl _) hcompat ≪≫
        ModuleCat.kernelIsoKer σ).toLinearEquiv⟩

/-- Helper for Remark 60.1: reduced integral component chains of a complement are
additively torsion-free. -/
lemma reducedComplementComponentChains_isAddTorsionFree
    (K : Set (EuclideanSpace ℝ (Fin 3))) :
    IsAddTorsionFree (ReducedComplementComponentChains K) := by
  -- The augmentation kernel embeds in the torsion-free group of integral component chains.
  constructor
  intro n hn x y hxy
  apply Subtype.ext
  exact nsmul_right_injective hn (congrArg Subtype.val hxy)

/-- Helper for Remark 60.1: the integral dual of a chain group, placed in the
same degree of a cochain complex. -/
private abbrev integralDualCochainGroup
    (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (Module.Dual ℤ (K.X n))

/-- Helper for Remark 60.1: dualizing a chain differential gives the
corresponding integral coboundary. -/
private def integralDualCoboundary
    (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    integralDualCochainGroup K n ⟶ integralDualCochainGroup K (n + 1) :=
  ModuleCat.ofHom ((K.d (n + 1) n).hom.dualMap)

/-- Helper for Remark 60.1: consecutive integral-dual coboundaries compose to
zero. -/
private lemma integralDualCoboundary_comp
    (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    integralDualCoboundary K n ≫ integralDualCoboundary K (n + 1) = 0 := by
  -- Evaluate the dual composite and invoke square-zero for the original chains.
  ext φ x
  simpa only [integralDualCoboundary, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.dualMap_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] using
    congrArg (fun d ↦ φ (d.hom x)) (K.d_comp_d (n + 2) (n + 1) n)

/-- Helper for Remark 60.1: the cochain complex obtained by degreewise
integral duality from a chain complex. -/
private abbrev integralDualCochainComplex
    (K : ChainComplex (ModuleCat ℤ) ℕ) : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (integralDualCochainGroup K)
    (integralDualCoboundary K) (integralDualCoboundary_comp K)

/-- Helper for Remark 60.1: the adjacent differential of the integral-dual
cochain complex is its named coboundary. -/
private lemma integralDualCochainComplex_d_succ
    (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (integralDualCochainComplex K).d n (n + 1) =
      integralDualCoboundary K n := by
  -- Use the computation rule for a cochain complex built with `of`.
  exact CochainComplex.of_d _ _ n

/-- Helper for Remark 60.1: a chain map acts contravariantly on each
integral-dual cochain group. -/
private def integralDualCochainMapComponent
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    integralDualCochainGroup L n ⟶ integralDualCochainGroup K n :=
  ModuleCat.ofHom ((f.f n).hom.dualMap)

/-- Helper for Remark 60.1: the dual components of a chain map commute with
the integral-dual coboundaries. -/
private lemma integralDualCochainMapComponent_comm
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    integralDualCochainMapComponent f n ≫ integralDualCoboundary K n =
      integralDualCoboundary L n ≫ integralDualCochainMapComponent f (n + 1) := by
  -- Evaluate both dual composites on a chain and use the chain-map square.
  ext φ x
  simpa only [integralDualCochainMapComponent, integralDualCoboundary,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.dualMap_apply] using
    congrArg (fun d ↦ φ (d.hom x)) ((f.comm (n + 1) n).symm)

/-- Helper for Remark 60.1: the dual chain-map square in the packaged
cochain-complex spelling. -/
private lemma integralDualCochainMap_comm
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    integralDualCochainMapComponent f n ≫
        (integralDualCochainComplex K).d n (n + 1) =
      (integralDualCochainComplex L).d n (n + 1) ≫
        integralDualCochainMapComponent f (n + 1) := by
  -- Expose only the adjacent differential computation of `CochainComplex.of`.
  simpa only [integralDualCochainComplex, CochainComplex.of_d] using
    integralDualCochainMapComponent_comm f n

/-- Helper for Remark 60.1: integral duality sends a chain map to a cochain
map in the reverse direction. -/
private def integralDualCochainMap
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) :
    integralDualCochainComplex L ⟶ integralDualCochainComplex K :=
  CochainComplex.ofHom (fun n ↦ integralDualCochainMapComponent f n)
    (integralDualCochainMap_comm f)

/-- Helper for Remark 60.1: integral-dual cochain maps reverse composition. -/
private lemma integralDualCochainMap_comp
    {K L M : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    integralDualCochainMap (f ≫ g) =
      integralDualCochainMap g ≫ integralDualCochainMap f := by
  -- Compare degreewise and evaluate the two dual composites on each chain.
  ext n φ x
  rfl

/-- Helper for Remark 60.1: dualizing an identity chain map gives the identity
cochain map. -/
private lemma integralDualCochainMap_id
    (K : ChainComplex (ModuleCat ℤ) ℕ) :
    integralDualCochainMap (𝟙 K) = 𝟙 (integralDualCochainComplex K) := by
  -- Compare degreewise; `LinearMap.dualMap_id` gives the component identity.
  ext n φ x
  rfl

/-- Helper for Remark 60.1: dualize one component of a chain homotopy, reversing
its source and target degrees. -/
private def integralDualHomotopyComponent
    {K L : ChainComplex (ModuleCat ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) (i j : ℕ) :
    (integralDualCochainComplex L).X i ⟶
      (integralDualCochainComplex K).X j :=
  ModuleCat.ofHom ((h.hom j i).hom.dualMap)

/-- Helper for Remark 60.1: the dual homotopy component vanishes away from
adjacent cochain degrees. -/
private lemma integralDualHomotopyComponent_zero
    {K L : ChainComplex (ModuleCat ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) (i j : ℕ)
    (hij : ¬(ComplexShape.up ℕ).Rel j i) :
    integralDualHomotopyComponent h i j = 0 := by
  -- The reversed cochain relation is exactly the original chain relation.
  have hchain : ¬(ComplexShape.down ℕ).Rel i j := by
    simpa only [ComplexShape.up_Rel, ComplexShape.down_Rel] using hij
  rw [integralDualHomotopyComponent, h.zero j i hchain]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp

/-- Helper for Remark 60.1: dualized homotopy components satisfy the cochain
homotopy identity. -/
private lemma integralDualHomotopyComponent_comm
    {K L : ChainComplex (ModuleCat ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) (n : ℕ) :
    (integralDualCochainMap f).f n =
      dNext n (integralDualHomotopyComponent h) +
        prevD n (integralDualHomotopyComponent h) +
          (integralDualCochainMap g).f n := by
  cases n with
  | zero =>
      -- At degree zero the incoming cochain-homotopy summand vanishes.
      rw [dNext_eq _ (ComplexShape.up_mk 0 1 rfl), prevD_nat]
      rw [integralDualCochainComplex_d_succ L 0,
        (integralDualCochainComplex K).shape 0 0 (by simp)]
      have hchainComm := h.comm 0
      rw [dNext_nat K L 0 h.hom,
        prevD_eq h.hom
          (show (ComplexShape.down ℕ).Rel 1 0 by simp)] at hchainComm
      rw [K.shape 0 0 (by simp), zero_comp, zero_add] at hchainComm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      have hpoint := congrArg (fun q ↦
        (φ : Module.Dual ℤ (L.X 0)) (q.hom x)) hchainComm
      simp only [integralDualCochainMap, integralDualCochainMapComponent,
        integralDualCochainComplex, integralDualCoboundary,
        integralDualHomotopyComponent, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_ofHom, LinearMap.dualMap_apply, ModuleCat.hom_add,
        LinearMap.add_apply, map_add] at hpoint ⊢
      rw [hpoint]
      abel
  | succ n =>
      -- In positive degree both dualized adjacent chain-homotopy terms occur.
      rw [dNext_eq _ (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl),
        prevD_nat]
      rw [Nat.add_sub_cancel_right,
        integralDualCochainComplex_d_succ L (n + 1),
        integralDualCochainComplex_d_succ K n]
      have hchainComm := h.comm (n + 1)
      rw [dNext_nat K L (n + 1) h.hom,
        prevD_eq h.hom
          (show (ComplexShape.down ℕ).Rel (n + 1 + 1) (n + 1) by simp)]
        at hchainComm
      rw [Nat.add_sub_cancel_right] at hchainComm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      have hpoint := congrArg (fun q ↦
        (φ : Module.Dual ℤ (L.X (n + 1))) (q.hom x)) hchainComm
      simp only [integralDualCochainMap, integralDualCochainMapComponent,
        integralDualCochainComplex, integralDualCoboundary,
        integralDualHomotopyComponent, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_ofHom, LinearMap.dualMap_apply, ModuleCat.hom_add,
        LinearMap.add_apply, map_add]
        at hpoint ⊢
      rw [hpoint]
      abel

/-- Helper for Remark 60.1: integral duality carries a chain homotopy to a
cochain homotopy between the contravariant maps. -/
private def integralDualHomotopy
    {K L : ChainComplex (ModuleCat ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy (integralDualCochainMap f) (integralDualCochainMap g) :=
  { hom := integralDualHomotopyComponent h
    zero := integralDualHomotopyComponent_zero h
    comm := integralDualHomotopyComponent_comm h }

/-- Helper for Remark 60.1: the dual maps of the two sides of a chain homotopy
equivalence cancel on the dual of its target. -/
private def integralDualHomotopyHomInvId
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv K L) :
    Homotopy
      (integralDualCochainMap e.hom ≫ integralDualCochainMap e.inv)
      (𝟙 (integralDualCochainComplex L)) :=
  (Homotopy.ofEq (integralDualCochainMap_comp e.inv e.hom).symm).trans
    ((integralDualHomotopy e.homotopyInvHomId).trans
      (Homotopy.ofEq (integralDualCochainMap_id L)))

/-- Helper for Remark 60.1: the dual maps of the two sides of a chain homotopy
equivalence cancel on the dual of its source. -/
private def integralDualHomotopyInvHomId
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv K L) :
    Homotopy
      (integralDualCochainMap e.inv ≫ integralDualCochainMap e.hom)
      (𝟙 (integralDualCochainComplex K)) :=
  (Homotopy.ofEq (integralDualCochainMap_comp e.hom e.inv).symm).trans
    ((integralDualHomotopy e.homotopyHomInvId).trans
      (Homotopy.ofEq (integralDualCochainMap_id K)))

/-- Helper for Remark 60.1: integral duality reverses a chain homotopy
equivalence into a cochain homotopy equivalence. -/
private def integralDualHomotopyEquiv
    {K L : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (integralDualCochainComplex L)
      (integralDualCochainComplex K) :=
  { hom := integralDualCochainMap e.hom
    inv := integralDualCochainMap e.inv
    homotopyHomInvId := integralDualHomotopyHomInvId e
    homotopyInvHomId := integralDualHomotopyInvHomId e }

/-- Helper for Remark 60.1: dualizing a quasi-isomorphism between degreewise
projective integral chain complexes yields a cochain quasi-isomorphism. -/
private lemma integralDualCochainMap_quasiIso_of_projective
    {K L : ChainComplex (ModuleCat ℤ) ℕ}
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (integralDualCochainMap f) := by
  -- Projectivity promotes the chain quasi-isomorphism to a homotopy equivalence.
  obtain ⟨e, rfl⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  -- The dual homotopy equivalence supplies quasi-isomorphisms in every degree.
  exact (integralDualHomotopyEquiv e).quasiIso_hom

/-- Helper for Remark 60.1: the `k`-skeleton of the projective plane consists of
antipodal classes represented by sphere points whose coordinates above `k` vanish. -/
private def projectivePlaneSkeleton (k : ℕ) : Set RealProjectivePlane :=
  quotientMap ''
    {x : UnitSphereThree | ∀ i : Fin 3, k < i.1 → x.1 i = 0}

/-- Helper for Remark 60.1: the sphere-level coordinate locus whose antipodal
quotient is the `k`-skeleton of the projective plane. -/
private def projectivePlaneSkeletonSource (k : ℕ) : Set UnitSphereThree :=
  {x | ∀ i : Fin 3, k < i.1 → x.1 i = 0}

/-- Helper for Remark 60.1: membership in the sphere-level coordinate locus is
exactly vanishing of every coordinate above the cutoff. -/
private lemma mem_projectivePlaneSkeletonSource_iff (k : ℕ) (x : UnitSphereThree) :
    x ∈ projectivePlaneSkeletonSource k ↔
      ∀ i : Fin 3, k < i.1 → x.1 i = 0 := by
  -- Expose the coordinate-locus predicate through its stable membership interface.
  rfl

/-- Helper for Remark 60.1: the sphere-level coordinate locus is an intersection
of coordinate hyperplanes. -/
private lemma projectivePlaneSkeletonSource_eq_iInter (k : ℕ) :
    projectivePlaneSkeletonSource k =
      ⋂ i : Fin 3, ⋂ (_ : k < i.1), {x : UnitSphereThree | x.1 i = 0} := by
  -- Compare membership in the locus and in each required coordinate hyperplane.
  ext x
  simp only [mem_projectivePlaneSkeletonSource_iff, Set.mem_iInter,
    Set.mem_setOf_eq]

/-- Helper for Remark 60.1: the projective `k`-skeleton is the quotient image of
its sphere-level coordinate locus. -/
private lemma projectivePlaneSkeleton_eq_image_source (k : ℕ) :
    projectivePlaneSkeleton k =
      quotientMap '' projectivePlaneSkeletonSource k := by
  -- The named source only packages the predicate in the original skeleton definition.
  rfl

/-- Helper for Remark 60.1: every sphere-level coordinate skeleton is closed. -/
private lemma projectivePlaneSkeletonSource_isClosed (k : ℕ) :
    IsClosed (projectivePlaneSkeletonSource k) := by
  -- Reduce to closedness of the individual coordinate hyperplanes.
  rw [projectivePlaneSkeletonSource_eq_iInter]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    isClosed_eq
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp
        continuous_subtype_val)
      continuous_const

/-- Helper for Remark 60.1: every sphere-level coordinate skeleton is compact. -/
private lemma projectivePlaneSkeletonSource_isCompact (k : ℕ) :
    IsCompact (projectivePlaneSkeletonSource k) := by
  -- A closed coordinate locus in the compact unit sphere is compact.
  exact (projectivePlaneSkeletonSource_isClosed k).isCompact

/-- Helper for Remark 60.1: the equal-or-antipodal fiber relation of the sphere
quotient is closed. -/
private lemma quotientMapFiberRelation_isClosed :
    IsClosed {q : UnitSphereThree × UnitSphereThree |
      quotientMap q.1 = quotientMap q.2} := by
  -- The relation is the union of the diagonal and the graph of antipodal negation.
  simpa only [quotientMap_eq_iff, Set.setOf_or, Function.comp_apply] using
    (isClosed_eq continuous_snd continuous_fst).union
      (isClosed_eq continuous_snd (continuous_neg.comp continuous_fst))

/-- Helper for Remark 60.1: the antipodal sphere quotient is Hausdorff. -/
private instance realProjectivePlaneT2SpaceForSkeleton : T2Space RealProjectivePlane := by
  -- The open quotient criterion reduces Hausdorffness to the closed fiber relation.
  exact (t2Space_iff_of_isOpenQuotientMap
    quotientMap_isAddQuotientCoveringMap.isOpenQuotientMap).mpr
      quotientMapFiberRelation_isClosed

/-- Helper for Remark 60.1: every coordinate projective-plane skeleton is compact. -/
private lemma projectivePlaneSkeleton_isCompact (k : ℕ) :
    IsCompact (projectivePlaneSkeleton k) := by
  -- Pass compactness through the continuous antipodal quotient map.
  rw [projectivePlaneSkeleton_eq_image_source]
  exact (projectivePlaneSkeletonSource_isCompact k).image
    quotientMap_isCoveringMap.continuous

/-- Helper for Remark 60.1: every coordinate projective-plane skeleton is closed. -/
private lemma projectivePlaneSkeleton_isClosed (k : ℕ) :
    IsClosed (projectivePlaneSkeleton k) := by
  -- The compact skeleton is closed in the Hausdorff projective plane.
  exact (projectivePlaneSkeleton_isCompact k).isClosed

/-- Helper for Remark 60.1: the coordinate projective-plane skeleta increase with
the coordinate cutoff. -/
private lemma projectivePlaneSkeleton_mono {k l : ℕ} (hkl : k ≤ l) :
    projectivePlaneSkeleton k ⊆ projectivePlaneSkeleton l := by
  -- Retain the same sphere representative and discard fewer coordinate conditions.
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  intro i hli
  exact hx i (hkl.trans_lt hli)

/-- Helper for Remark 60.1: a vector supported only in coordinate zero is the
corresponding coordinate vector. -/
private lemma euclideanSpace_eq_single_zero_of_coordinates_vanish
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ i : Fin 3, 0 < i.1 → x i = 0) :
    x = PiLp.single 2 (0 : Fin 3) (x 0) := by
  -- Compare coordinates, separating the retained coordinate from the vanishing ones.
  ext i
  by_cases hi : i = 0
  · subst i
    simp
  · have hipos : 0 < i.1 := by
      omega
    rw [hx i hipos]
    simp [PiLp.single_apply, hi]

/-- Helper for Remark 60.1: a unit vector supported only in coordinate zero is
the positive or negative first coordinate vector. -/
private lemma unitSphereThree_eq_single_zero_or_neg
    (x : UnitSphereThree)
    (hx : ∀ i : Fin 3, 0 < i.1 → x.1 i = 0) :
    x.1 = PiLp.single 2 (0 : Fin 3) (1 : ℝ) ∨
      x.1 = -PiLp.single 2 (0 : Fin 3) (1 : ℝ) := by
  have hxsingle :=
    euclideanSpace_eq_single_zero_of_coordinates_vanish x.1 hx
  have hnorm : ‖x.1‖ = 1 := by
    -- Membership in the unit sphere supplies the norm equation.
    simpa only [UnitSphereThree, Metric.mem_sphere, dist_zero_right] using x.2
  rw [hxsingle, PiLp.norm_single, Real.norm_eq_abs] at hnorm
  have hsq : (x.1 0) ^ 2 = (1 : ℝ) ^ 2 :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mpr (by simpa only [abs_one] using hnorm)
  rcases (sq_eq_one_iff.mp (by simpa only [one_pow] using hsq)) with hcoord | hcoord
  · left
    rw [hxsingle, hcoord]
  · right
    rw [hxsingle, hcoord]
    exact PiLp.single_neg 2 (0 : Fin 3)

/-- Helper for Remark 60.1: the positive first coordinate vector lies on the
unit sphere. -/
private lemma projectivePlaneZeroCellRepresentative_mem_sphere :
    PiLp.single 2 (0 : Fin 3) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- Its norm is the absolute value of its sole nonzero coordinate.
  simp [Metric.mem_sphere, dist_zero_left]

/-- Helper for Remark 60.1: a fixed sphere representative of the unique
projective zero-cell. -/
private def projectivePlaneZeroCellRepresentative : UnitSphereThree :=
  ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ),
    projectivePlaneZeroCellRepresentative_mem_sphere⟩

/-- Helper for Remark 60.1: coercing the antipode of a sphere point gives the
negation of its ambient Euclidean vector. -/
private lemma unitSphereThree_coe_neg (x : UnitSphereThree) :
    ((-x : UnitSphereThree) : EuclideanSpace ℝ (Fin 3)) = -x.1 := by
  -- Negation on the sphere is inherited from the ambient normed space.
  rfl

/-- Helper for Remark 60.1: the coordinate zero-skeleton consists of exactly one
projective point. -/
private lemma projectivePlaneSkeleton_zero :
    projectivePlaneSkeleton 0 =
      {quotientMap projectivePlaneZeroCellRepresentative} := by
  -- Every supported sphere representative is one of the antipodal coordinate vectors.
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_singleton_iff]
    apply (quotientMap_eq_iff x projectivePlaneZeroCellRepresentative).mpr
    rcases unitSphereThree_eq_single_zero_or_neg x hx with hpositive | hnegative
    · exact Or.inl (Subtype.ext hpositive.symm)
    · apply Or.inr
      apply Subtype.ext
      rw [unitSphereThree_coe_neg]
      simpa only [projectivePlaneZeroCellRepresentative, neg_neg] using
        (congrArg Neg.neg hnegative).symm
  · rw [Set.mem_singleton_iff]
    rintro rfl
    refine ⟨projectivePlaneZeroCellRepresentative, ?_, rfl⟩
    intro i hi
    have hine : i ≠ 0 := by
      intro hieq
      subst i
      omega
    simp [projectivePlaneZeroCellRepresentative, PiLp.single_apply, hine]

/-- Helper for Remark 60.1: the coordinate `2`-skeleton is the whole real
projective plane. -/
private lemma projectivePlaneSkeleton_two :
    projectivePlaneSkeleton 2 = Set.univ := by
  -- Choose a sphere representative; `Fin 3` has no coordinate strictly above two.
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨x, rfl⟩ := quotientMap_isQuotientMap.surjective p
  refine ⟨x, ?_, rfl⟩
  intro i hi
  omega

/-- Helper for Remark 60.1: the cellular cochain group of the standard
three-cell filtration of `RealProjectivePlane`. -/
private abbrev projectivePlaneCellularCochainGroup : ℕ → ModuleCat ℤ
  | 0 => ModuleCat.of ℤ ℤ
  | 1 => ModuleCat.of ℤ ℤ
  | 2 => ModuleCat.of ℤ ℤ
  | _ => ModuleCat.of ℤ (Fin 0 → ℤ)

/-- Helper for Remark 60.1: the cellular coboundary is zero in degree zero,
multiplication by two in degree one, and zero thereafter. -/
private def projectivePlaneCellularCoboundary :
    (n : ℕ) → projectivePlaneCellularCochainGroup n ⟶
      projectivePlaneCellularCochainGroup (n + 1)
  | 0 => 0
  | 1 => ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2)
  | 2 => ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ))
  | _ + 3 => 0

/-- Helper for Remark 60.1: consecutive cellular coboundaries in the standard
projective-plane model compose to zero. -/
private lemma projectivePlaneCellularCoboundary_comp (n : ℕ) :
    projectivePlaneCellularCoboundary n ≫
      projectivePlaneCellularCoboundary (n + 1) = 0 := by
  -- The only nonzero coboundary is bracketed by zero maps.
  rcases n with _ | _ | n
  · simp [projectivePlaneCellularCoboundary]
  · simp [projectivePlaneCellularCoboundary]
  · rcases n with _ | n
    · simp [projectivePlaneCellularCoboundary]
    · simp [projectivePlaneCellularCoboundary]

/-- Helper for Remark 60.1: the full integral cellular cochain complex of the
standard filtration of the real projective plane. -/
private abbrev projectivePlaneCellularCochainComplex :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of projectivePlaneCellularCochainGroup
    projectivePlaneCellularCoboundary
    projectivePlaneCellularCoboundary_comp

/-- Helper for Remark 60.1: the degree-one differential of the full cellular
cochain complex is multiplication by two. -/
private lemma projectivePlaneCellularCochainComplex_d_one :
    projectivePlaneCellularCochainComplex.d 1 2 =
      ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2) := by
  -- Apply the adjacent-differential computation rule of `CochainComplex.of`.
  simpa [projectivePlaneCellularCochainComplex,
    projectivePlaneCellularCoboundary] using
    (CochainComplex.of_d projectivePlaneCellularCochainGroup
      projectivePlaneCellularCoboundary 1)

/-- Helper for Remark 60.1: the degree-two differential of the full cellular
cochain complex is zero. -/
private lemma projectivePlaneCellularCochainComplex_d_two :
    projectivePlaneCellularCochainComplex.d 2 3 =
      ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ)) := by
  -- Apply the adjacent-differential computation rule of `CochainComplex.of`.
  simpa [projectivePlaneCellularCochainComplex,
    projectivePlaneCellularCoboundary] using
    (CochainComplex.of_d projectivePlaneCellularCochainGroup
      projectivePlaneCellularCoboundary 2)

/-- Helper for Remark 60.1: the raw `CochainComplex.of` differential at
degrees one and two is multiplication by two. -/
private lemma projectivePlaneCellularCochainRaw_d_one :
    CochainComplex.of.d projectivePlaneCellularCochainGroup
        projectivePlaneCellularCoboundary 1 2 =
      ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2) := by
  -- Normalize the numeral successor and then apply `CochainComplex.of_d`.
  simpa [projectivePlaneCellularCoboundary] using
    (CochainComplex.of_d projectivePlaneCellularCochainGroup
      projectivePlaneCellularCoboundary 1)

/-- Helper for Remark 60.1: the raw `CochainComplex.of` differential at
degrees two and three is zero. -/
private lemma projectivePlaneCellularCochainRaw_d_two :
    CochainComplex.of.d projectivePlaneCellularCochainGroup
        projectivePlaneCellularCoboundary 2 3 =
      ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ)) := by
  -- Normalize the numeral successor and then apply `CochainComplex.of_d`.
  simpa [projectivePlaneCellularCoboundary] using
    (CochainComplex.of_d projectivePlaneCellularCochainGroup
      projectivePlaneCellularCoboundary 2)

/-- Helper for Remark 60.1: multiplication by two followed by the zero map is
zero in the explicit degree-two cellular cochain model. -/
private lemma projectivePlaneDegreeTwoCoboundary_comp_zero :
    (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ)).comp (LinearMap.lsmul ℤ ℤ 2) = 0 := by
  -- The second cellular coboundary has zero target, so the composite vanishes pointwise.
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- Helper for Remark 60.1: the degree-two cellular cochain short complex is
`ℤ --2→ ℤ --0→ 0`. -/
private abbrev projectivePlaneCellularDegreeTwoShortComplex :
    ShortComplex (ModuleCat ℤ) :=
  { f := ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2)
    g := ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ))
    zero := ModuleCat.hom_ext projectivePlaneDegreeTwoCoboundary_comp_zero }

/-- Helper for Remark 60.1: the first arrow of the degree-two projection of
the full cellular complex is multiplication by two. -/
private lemma projectivePlaneCellularCochainComplex_scTwo_f :
    (projectivePlaneCellularCochainComplex.sc' 1 2 3).f =
      ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2) := by
  -- The projection retains the full complex's differential from degree one.
  exact projectivePlaneCellularCochainComplex_d_one

/-- Helper for Remark 60.1: the second arrow of the degree-two projection of
the full cellular complex is zero. -/
private lemma projectivePlaneCellularCochainComplex_scTwo_g :
    (projectivePlaneCellularCochainComplex.sc' 1 2 3).g =
      ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ)) := by
  -- The projection retains the full complex's differential out of degree two.
  exact projectivePlaneCellularCochainComplex_d_two

/-- Helper for Remark 60.1: the identity comparison intertwines the first
arrows of the full and degree-two cellular complexes. -/
private lemma projectivePlaneCellularScTwo_comm_f :
    (𝟙 (ModuleCat.of ℤ ℤ)) ≫
        projectivePlaneCellularDegreeTwoShortComplex.f =
      (projectivePlaneCellularCochainComplex.sc' 1 2 3).f ≫
        𝟙 (ModuleCat.of ℤ ℤ) := by
  -- Both first arrows are the named multiplication-by-two coboundary.
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    projectivePlaneCellularCochainComplex,
    projectivePlaneCellularCochainGroup]
  rw [Category.id_comp, projectivePlaneCellularCochainRaw_d_one]
  exact (Category.comp_id
    (ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2))).symm

/-- Helper for Remark 60.1: the identity comparison intertwines the second
arrows of the full and degree-two cellular complexes. -/
private lemma projectivePlaneCellularScTwo_comm_g :
    (𝟙 (ModuleCat.of ℤ ℤ)) ≫
        projectivePlaneCellularDegreeTwoShortComplex.g =
      (projectivePlaneCellularCochainComplex.sc' 1 2 3).g ≫
        𝟙 (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
  -- Both second arrows are the named zero coboundary out of degree two.
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    projectivePlaneCellularCochainComplex,
    projectivePlaneCellularCochainGroup]
  rw [Category.id_comp, projectivePlaneCellularCochainRaw_d_two]
  exact (Category.comp_id
    (ModuleCat.ofHom (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ)))).symm

/-- Helper for Remark 60.1: the degree-two short-complex projection of the
full cellular cochain complex is the explicit `ℤ --2→ ℤ --0→ 0` model. -/
private def projectivePlaneCellularCochainComplexScTwoIso :
    projectivePlaneCellularCochainComplex.sc' 1 2 3 ≅
      projectivePlaneCellularDegreeTwoShortComplex :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    projectivePlaneCellularScTwo_comm_f
    projectivePlaneCellularScTwo_comm_g

/-- Helper for Remark 60.1: degree one is the predecessor of degree two in
the cochain-complex shape. -/
private lemma projectivePlaneCellularCochainComplex_prev_two :
    (ComplexShape.up ℕ).prev 2 = 1 := by
  -- Compute the predecessor in the standard natural-number cochain shape.
  simp

/-- Helper for Remark 60.1: degree three is the successor of degree two in
the cochain-complex shape. -/
private lemma projectivePlaneCellularCochainComplex_next_two :
    (ComplexShape.up ℕ).next 2 = 3 := by
  -- Compute the successor in the standard natural-number cochain shape.
  simp

/-- Helper for Remark 60.1: degree-two homology of the full cellular cochain
complex agrees with homology of its explicit short-complex projection. -/
private noncomputable def projectivePlaneCellularCochainHomologyIsoScTwo :
    projectivePlaneCellularCochainComplex.homology 2 ≅
      projectivePlaneCellularDegreeTwoShortComplex.homology :=
  projectivePlaneCellularCochainComplex.homologyIsoSc' 1 2 3
      projectivePlaneCellularCochainComplex_prev_two
      projectivePlaneCellularCochainComplex_next_two ≪≫
    ShortComplex.homologyMapIso projectivePlaneCellularCochainComplexScTwoIso

/-- Helper for Remark 60.1: the first arrow of the explicit degree-two cellular
cochain complex is multiplication by two. -/
private lemma projectivePlaneCellularDegreeTwoShortComplex_f_apply (x : ℤ) :
    projectivePlaneCellularDegreeTwoShortComplex.f x = (2 : ℤ) • x := by
  -- Expose the defining linear map without unfolding the short-complex structure elsewhere.
  rfl

/-- Helper for Remark 60.1: the second arrow of the explicit degree-two cellular
cochain complex vanishes. -/
private lemma projectivePlaneCellularDegreeTwoShortComplex_g_apply (x : ℤ) :
    projectivePlaneCellularDegreeTwoShortComplex.g x = 0 := by
  -- Expose the zero-coboundary computation used by the homology normalization.
  rfl

/-- Helper for Remark 60.1: every integer is a cycle for the zero outgoing
coboundary in the degree-two cellular short complex. -/
private lemma integer_mem_projectivePlaneCellularCycles (x : ℤ) :
    x ∈ LinearMap.ker projectivePlaneCellularDegreeTwoShortComplex.g.hom := by
  -- The outgoing cellular coboundary is identically zero.
  exact projectivePlaneCellularDegreeTwoShortComplex_g_apply x

/-- Helper for Remark 60.1: forgetting the proof that an integer is a cellular
cycle is a bijection because the outgoing coboundary is zero. -/
private lemma projectivePlaneCellularCycles_subtype_bijective :
    Function.Bijective
      (LinearMap.ker projectivePlaneCellularDegreeTwoShortComplex.g.hom).subtype := by
  -- Subtype inclusion is injective, and the preceding cycle lemma supplies every preimage.
  constructor
  · exact Submodule.subtype_injective _
  · intro x
    exact ⟨⟨x, integer_mem_projectivePlaneCellularCycles x⟩, rfl⟩

/-- Helper for Remark 60.1: cellular degree-two cycles are canonically identified
with the integers. -/
private noncomputable def projectivePlaneCellularCyclesLinearEquivInt :
    LinearMap.ker projectivePlaneCellularDegreeTwoShortComplex.g.hom ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective
    (LinearMap.ker projectivePlaneCellularDegreeTwoShortComplex.g.hom).subtype
    projectivePlaneCellularCycles_subtype_bijective

/-- Helper for Remark 60.1: the cycle equivalence forgets only the proof of the
zero outgoing coboundary. -/
private lemma projectivePlaneCellularCyclesLinearEquivInt_apply
    (x : LinearMap.ker projectivePlaneCellularDegreeTwoShortComplex.g.hom) :
    projectivePlaneCellularCyclesLinearEquivInt x = x.1 := by
  -- The equivalence was constructed directly from the kernel subtype map.
  rfl

/-- Helper for Remark 60.1: a cellular coboundary maps to twice its integer
coefficient under the cycle equivalence. -/
private lemma projectivePlaneCellularCyclesLinearEquivInt_toCycles (x : ℤ) :
    projectivePlaneCellularCyclesLinearEquivInt
        (projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles x) =
      (2 : ℤ) * x := by
  -- Both the cycle inclusion and the equivalence forget only proof fields.
  rfl

/-- Helper for Remark 60.1: an integer belongs to the module associated to an
additive subgroup exactly when it belongs to that additive subgroup. -/
private lemma mem_toIntSubmodule_iff (S : AddSubgroup ℤ) (x : ℤ) :
    x ∈ S.toIntSubmodule ↔ x ∈ S := by
  -- The integer-module structure retains the same underlying carrier set.
  rfl

/-- Helper for Remark 60.1: under the identification of cellular cycles with
`ℤ`, cellular boundaries are exactly the multiples of two. -/
private lemma projectivePlaneCellularBoundaryRange_map :
    (LinearMap.range projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles).map
        projectivePlaneCellularCyclesLinearEquivInt.toLinearMap =
      (AddSubgroup.zmultiples (2 : ℤ)).toIntSubmodule := by
  -- Both sides consist precisely of integers divisible by two.
  ext x
  constructor
  · -- A mapped boundary is the image of an integer under multiplication by two.
    rw [Submodule.mem_map]
    rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    have hmultiple : (2 : ℤ) * z ∈ AddSubgroup.zmultiples (2 : ℤ) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨z, by simp only [smul_eq_mul, mul_comm]⟩
    have hvalue :
        (projectivePlaneCellularCyclesLinearEquivInt
          (projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles z) : ℤ) =
            (2 : ℤ) * z :=
      projectivePlaneCellularCyclesLinearEquivInt_toCycles z
    exact hvalue.symm ▸ (mem_toIntSubmodule_iff _ _).mpr hmultiple
  · -- Conversely, write a multiple of two as the image of its coefficient.
    intro hx
    have hmultiple : x ∈ AddSubgroup.zmultiples (2 : ℤ) := by
      exact (mem_toIntSubmodule_iff _ _).mp hx
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmultiple
    rw [Submodule.mem_map]
    refine ⟨projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles z,
      ⟨z, rfl⟩, ?_⟩
    have hvalue :
        (projectivePlaneCellularCyclesLinearEquivInt
          (projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles z) : ℤ) =
            (2 : ℤ) * z :=
      projectivePlaneCellularCyclesLinearEquivInt_toCycles z
    exact hvalue.trans <| calc
      (2 : ℤ) * z = z * 2 := mul_comm _ _
      _ = x := by simpa only [smul_eq_mul] using hz

/-- Helper for Remark 60.1: homology of the explicit degree-two cellular short
complex is canonically `ZMod 2`. -/
private noncomputable def projectivePlaneCellularDegreeTwoHomologyLinearEquiv :
    projectivePlaneCellularDegreeTwoShortComplex.homology ≃ₗ[ℤ]
      DegreeTwoCellularCohomology :=
  projectivePlaneCellularDegreeTwoShortComplex.moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.Quotient.equiv
      (LinearMap.range projectivePlaneCellularDegreeTwoShortComplex.moduleCatToCycles)
      (AddSubgroup.zmultiples (2 : ℤ)).toIntSubmodule
      projectivePlaneCellularCyclesLinearEquivInt
      projectivePlaneCellularBoundaryRange_map).trans
        (Int.quotientZMultiplesNatEquivZMod 2).toIntLinearEquiv)

/-- Helper for Remark 60.1: normed real vector spaces have contractible metric
balls as a neighborhood basis. -/
private lemma stronglyLocallyContractibleSpace_normedRealModel
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E := by
  -- Positive-radius balls give the required neighborhood basis and are contractible.
  exact StronglyLocallyContractibleSpace.of_bases
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ hr ↦ Metric.contractibleSpace_ball hr)

/-- Helper for Remark 60.1: a charted space inherits strong local
contractibility from its model space. -/
private lemma stronglyLocallyContractibleSpace_of_chartedModel
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (hH : StronglyLocallyContractibleSpace H) :
    StronglyLocallyContractibleSpace M := by
  -- Local instance justification (regularity): `hH` is the explicit model-space
  -- structure whose basis is transported through the chosen chart.
  letI : StronglyLocallyContractibleSpace H := hH
  -- Pull a contractible basis inside each chart target back through the chart inverse.
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
    -- The chart restriction is a homeomorphism from `s` onto its image.
    exact (Homeomorph.contractibleSpace_iff
      ((chartAt H x).symm.homeomorphOfImageSubsetSource hsTarget rfl)).mp
        hsContractible

/-- Helper for Remark 60.1: a surjective local homeomorphism transfers strong
local contractibility from its source to its target. -/
private lemma stronglyLocallyContractibleSpace_of_surjective_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (hE : StronglyLocallyContractibleSpace E) (f : E → X)
    (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f) :
    StronglyLocallyContractibleSpace X := by
  -- Local instance justification (regularity): the explicit source structure
  -- `hE` supplies the basis transported by the local homeomorphism charts.
  letI : StronglyLocallyContractibleSpace E := hE
  classical
  choose e he using hsurj
  choose φ hφsource hφeq using fun x ↦ hf (e x)
  -- Images of source-side contractible basis members form a basis at each target point.
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun x s ↦ s ∈ nhds (e x) ∧ ContractibleSpace s ∧ s ⊆ (φ x).source)
    (s := fun x s ↦ φ x '' s) ?_ ?_
  · intro x
    have hcenter : φ x (e x) = x := by
      rw [← hφeq x, he x]
    have hfilter : nhds x = Filter.map (φ x) (nhds (e x)) := by
      calc
        nhds x = nhds (φ x (e x)) := congrArg nhds hcenter.symm
        _ = Filter.map (φ x) (nhds (e x)) :=
          ((φ x).map_nhds_eq (hφsource x)).symm
    rw [hfilter]
    exact ((contractible_basis (e x)).hasBasis_self_subset
      ((φ x).open_source.mem_nhds (hφsource x))).map _
  · rintro x s ⟨_, hsContractible, hsSource⟩
    -- Restricting the local homeomorphism identifies `s` with its image.
    exact (Homeomorph.contractibleSpace_iff
      ((φ x).homeomorphOfImageSubsetSource hsSource rfl)).mp hsContractible

/-- Helper for Remark 60.1: the real projective plane is strongly locally
contractible. -/
private lemma realProjectivePlane_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace RealProjectivePlane := by
  -- Sphere charts transfer the contractible-ball basis from the Euclidean model.
  have hModel :
      StronglyLocallyContractibleSpace (EuclideanSpace ℝ (Fin 2)) :=
    stronglyLocallyContractibleSpace_normedRealModel _
  have hSphere : StronglyLocallyContractibleSpace UnitSphereThree :=
    stronglyLocallyContractibleSpace_of_chartedModel
      (EuclideanSpace ℝ (Fin 2)) UnitSphereThree hModel
  -- The antipodal quotient is a surjective local homeomorphism.
  exact stronglyLocallyContractibleSpace_of_surjective_isLocalHomeomorph
    hSphere quotientMap quotientMap_isCoveringMap.isLocalHomeomorph
      quotientMap_isQuotientMap.surjective

/-- Helper for Remark 60.1: the antipodal cover's parity cochain is a
degree-one mod-two singular cocycle. -/
private lemma antipodalParityCochain_isCocycle :
    ((singularCochainComplexWithCoefficients
      (TopCat.of RealProjectivePlane) (ModuleCat.of ℤ (ZMod 2))).d 1 2).hom
        antipodalParityCochain = 0 := by
  -- Rewrite the specialized cochain to the generic Boolean-cover construction,
  -- then supply the compiled transition triangle law for every two-simplex.
  rw [antipodalParityCochain_eq_boolCoverParityCochain]
  apply boolCoverParityCochain_isCocycle_of_triangle
  intro simplex
  exact boolCoverEdgeTransition_triangle quotientMap
    quotientMap_isAddQuotientCoveringMap antipodalFiberChoice simplex

/-- Helper for Remark 60.1: the antipodal double cover supplies a mod-two
degree-one class which has no integral lift. -/
private lemma antipodalParityClass_not_liftable :
    ∃ a : SingularCohomologyWithCoefficients
        (TopCat.of RealProjectivePlane) (ModuleCat.of ℤ (ZMod 2)) 1,
      ¬ ∃ b : SingularCohomologyWithCoefficients
          (TopCat.of RealProjectivePlane) (ModuleCat.of ℤ ℤ) 1,
        HomologicalComplex.homologyMap
          (singularCoefficientCochainMap (TopCat.of RealProjectivePlane)
            integralModTwoCoefficientShortComplex.g) 1 b = a := by
  -- Route correction: the cellular comparison repeatedly required unavailable
  -- relative-cell excision, so use the antipodal cover's monodromy class instead.
  -- The transition cochain, generator rule, and triangle cocycle law are now
  -- available. TODO: construct one detected order-two cycle (twice a singular
  -- boundary); its evaluation then contradicts torsion-freeness of `ℤ`.
  let a := cohomologyOneClassOfCocycle (TopCat.of RealProjectivePlane)
    (ModuleCat.of ℤ (ZMod 2)) antipodalParityCochain
      antipodalParityCochain_isCocycle
  refine ⟨a, ?_⟩
  -- TODO: evaluate an assumed integral lift and `a` on an explicit singular
  -- one-cycle detecting antipodal monodromy; twice that cycle must be a
  -- boundary, forcing its integral evaluation to vanish while `a` evaluates to one.
  sorry

/-- Helper for Remark 60.1: integral degree-two singular cohomology of the real
projective plane contains a nonzero class annihilated by two. -/
private lemma exists_nonzero_twoTorsion_integralSingularCohomologyTwo :
    ∃ c : IntegralSingularCohomology (TopCat.of RealProjectivePlane) 2,
      c ≠ 0 ∧ 2 • c = 0 := by
  -- The Bockstein of a non-liftable parity class is nonzero and killed by two.
  obtain ⟨a, ha⟩ := antipodalParityClass_not_liftable
  let c := integralBockstein (TopCat.of RealProjectivePlane) a
  have hc : c ≠ 0 := by
    intro hzero
    exact ha ((integralBockstein_eq_zero_iff_lifts
      (TopCat.of RealProjectivePlane) a).mp hzero)
  have htwo : 2 • c = 0 :=
    two_nsmul_integralBockstein (TopCat.of RealProjectivePlane) a
  let e := (singularIntegralCoefficientCohomologyIso
    (TopCat.of RealProjectivePlane) 2).toLinearEquiv
  refine ⟨e c, ?_, ?_⟩
  · -- The cohomology comparison is injective, so it preserves nonvanishing.
    intro hzero
    apply hc
    exact e.injective (by simpa using hzero)
  · -- Transport the two-torsion equation across the additive equivalence.
    calc
      2 • e c = e (2 • c) := (e.toAddMonoidHom.map_nsmul 2 c).symm
      _ = e 0 := congrArg e htwo
      _ = 0 := e.map_zero

/-- Helper for Remark 60.1: integral Alexander duality in degree two for a
compact locally contractible subset of Euclidean three-space. -/
private lemma integralAlexanderDualityTwoZero
    (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hcompact : IsCompact K) (hclosed : IsClosed K)
    (hLocallyContractible : LocallyContractibleSpace K) :
    Nonempty
      (IntegralSingularCohomology (TopCat.of K) 2 ≅
        ReducedSingularHomologyZero
          (TopCat.of (Kᶜ : Set (EuclideanSpace ℝ (Fin 3))))) := by
  -- TODO: construct the finite-cover Alexander comparison and identify the
  -- one-point-compactification complement; this is the remaining duality frontier.
  sorry

/-- Helper for Remark 60.1: degree-two integral singular cohomology of an
embedded real projective plane is reduced integral `H₀` of its complement. -/
lemma integralSingularCohomologyIsoReducedSingularHomologyZero_of_embedding
    (f : RealProjectivePlane → EuclideanSpace ℝ (Fin 3))
    (hf : Topology.IsEmbedding f)
    (hcompact : IsCompact (Set.range f))
    (hclosed : IsClosed (Set.range f)) :
    Nonempty
      (IntegralSingularCohomology (TopCat.of RealProjectivePlane) 2 ≅
        ReducedSingularHomologyZero
          (TopCat.of ((Set.range f)ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) :=
  by
    -- Transport strong local contractibility from the projective plane to the embedded image.
    letI : StronglyLocallyContractibleSpace RealProjectivePlane :=
      realProjectivePlane_stronglyLocallyContractible
    have hRangeStrong : StronglyLocallyContractibleSpace (Set.range f) :=
      hf.toHomeomorph.symm.isOpenEmbedding.stronglyLocallyContractibleSpace
    -- Local instance justification (regularity): `hRangeStrong` depends on the
    -- particular embedding and is needed only to invoke the duality side condition.
    letI : StronglyLocallyContractibleSpace (Set.range f) := hRangeStrong
    have hRangeLocally : LocallyContractibleSpace (Set.range f) :=
      StronglyLocallyContractibleSpace.locallyContractible
    obtain ⟨eDuality⟩ :=
      integralAlexanderDualityTwoZero (Set.range f) hcompact hclosed hRangeLocally
    -- Cohomology invariance under the embedding homeomorphism supplies the first stage.
    let eImage : TopCat.of RealProjectivePlane ≅ TopCat.of (Set.range f) :=
      TopCat.isoOfHomeo hf.toHomeomorph
    exact ⟨integralSingularCohomologyMapIso eImage 2 ≪≫ eDuality⟩

/-- Helper for Remark 60.1: an embedded copy of the real projective plane with compact,
closed range in `ℝ³` yields a contradiction. -/
lemma compactClosedRangeEmbedding_false
    (f : RealProjectivePlane → EuclideanSpace ℝ (Fin 3))
    (hf : Topology.IsEmbedding f)
    (hcompact : IsCompact (Set.range f))
    (hclosed : IsClosed (Set.range f)) : False := by
  -- Route correction: arbitrary surface embeddings in three-space need not provide
  -- the ambient local product neighborhoods required by the former section argument.
  letI : IsAddTorsionFree
      (ReducedComplementComponentChains (Set.range f)) :=
    reducedComplementComponentChains_isAddTorsionFree (Set.range f)
  -- Alexander duality and the reduced-H₀ model send the Bockstein class into
  -- the torsion-free group of integral component chains.
  obtain ⟨c, hc, htwo⟩ :=
    exists_nonzero_twoTorsion_integralSingularCohomologyTwo
  obtain ⟨eduality⟩ :=
    integralSingularCohomologyIsoReducedSingularHomologyZero_of_embedding
      f hf hcompact hclosed
  obtain ⟨enormalize⟩ :=
    nonempty_reducedSingularHomologyZero_linearEquiv_componentChains (Set.range f)
  let e := eduality.toLinearEquiv.toAddEquiv.trans enormalize.toAddEquiv
  exact hc (eq_zero_of_two_nsmul_eq_zero_after_addEquiv e htwo)

/-- Remark 60.1: The real projective plane cannot be topologically embedded in `ℝ³`. -/
theorem notEmbeddableInThreeSpace :
    ¬ ∃ f : RealProjectivePlane → EuclideanSpace ℝ (Fin 3), Topology.IsEmbedding f := by
  -- Reduce an assumed embedding to its compact image in Euclidean three-space.
  rintro ⟨f, hf⟩
  have hcompact : IsCompact (Set.range f) := isCompact_range hf.continuous
  -- The Hausdorff Euclidean codomain makes the compact image closed.
  have hclosed : IsClosed (Set.range f) := hcompact.isClosed
  exact compactClosedRangeEmbedding_false f hf hcompact hclosed

end RealProjectivePlane
