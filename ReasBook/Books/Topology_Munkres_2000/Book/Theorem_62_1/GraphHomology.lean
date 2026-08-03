module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic

public section

namespace InvarianceOfDomainSupport

/-- Helper for Theorem 62.1: summing coefficients is the augmentation of finitely
supported mod-two chains. -/
noncomputable abbrev componentAugmentationModTwo (ι : Type*) :
    (ι →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2)
    (fun _ : ι ↦ (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))

/-- Helper for Theorem 62.1: the mod-two boundary of a finite simple graph is its
incidence matrix transported from finite functions to finitely supported functions. -/
noncomputable def graphBoundaryModTwo {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] :
    (Sym2 V →₀ ZMod 2) →ₗ[ZMod 2] (V →₀ ZMod 2) :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) V).symm.toLinearMap.comp
    ((G.incMatrix (ZMod 2)).mulVecLin.comp
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Sym2 V)).toLinearMap)

/-- Helper for Theorem 62.1: graph boundary coefficients are the usual finite
incidence-matrix sums. -/
lemma graphBoundaryModTwo_apply {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (x : Sym2 V →₀ ZMod 2) (v : V) :
    graphBoundaryModTwo G x v = ∑ e, G.incMatrix (ZMod 2) v e * x e := by
  -- Name the matrix product so the inverse finite-function equivalence is crossed once.
  let y : V → ZMod 2 :=
    (G.incMatrix (ZMod 2)).mulVec
      ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Sym2 V)) x)
  have hFiniteCoe :
      ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) V).symm y) v = y v :=
    congrFun
      ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) V).apply_symm_apply y) v
  calc
    graphBoundaryModTwo G x v =
        ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) V).symm y) v := rfl
    _ = y v := hFiniteCoe
    _ = ∑ e, G.incMatrix (ZMod 2) v e * x e := rfl

/-- Helper for Theorem 62.1: the graph boundary of a single edge coefficient is
the corresponding incidence column scaled by that coefficient. -/
lemma graphBoundaryModTwo_single_apply {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : ZMod 2) (v : V) :
    graphBoundaryModTwo G (Finsupp.single e a) v =
      G.incMatrix (ZMod 2) v e * a := by
  -- Reduce the matrix sum to its one supported edge coefficient.
  rw [graphBoundaryModTwo_apply]
  calc
    (∑ e', G.incMatrix (ZMod 2) v e' * Finsupp.single e a e') =
        G.incMatrix (ZMod 2) v e * Finsupp.single e a e :=
      Finset.sum_eq_single e
        (fun e' _ he' ↦ by
          simp only [Finsupp.single_apply, if_neg he'.symm, mul_zero])
        (fun he ↦ (he (Finset.mem_univ e)).elim)
    _ = G.incMatrix (ZMod 2) v e * a := by simp only [Finsupp.single_eq_same]

/-- Helper for Theorem 62.1: component augmentation on a finite type is the
ordinary sum of all coefficients. -/
lemma componentAugmentationModTwo_eq_sum {V : Type*} [Fintype V]
    (x : V →₀ ZMod 2) :
    componentAugmentationModTwo V x = ∑ v, x v := by
  -- Replace the support-indexed sum by the equal sum over the finite ambient type.
  classical
  simp only [componentAugmentationModTwo, Finsupp.lsum_apply]
  exact Finsupp.sum_fintype _ _ (fun _ ↦ rfl)

/-- Helper for Theorem 62.1: the one-row matrix whose linear map is vertex
augmentation on finite mod-two coefficient functions. -/
def vertexAugmentationMatrix (V : Type*) : Matrix Unit V (ZMod 2) :=
  fun _ _ ↦ 1

/-- Helper for Theorem 62.1: the vertex-augmentation matrix sums all finite
function coefficients. -/
lemma vertexAugmentationMatrix_mulVecLin_apply {V : Type*} [Fintype V]
    (x : V → ZMod 2) (u : Unit) :
    (vertexAugmentationMatrix V).mulVecLin x u = ∑ v, x v := by
  -- Every entry of the unique row is one.
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    vertexAugmentationMatrix, one_mul]

/-- Helper for Theorem 62.1: over `ZMod 2`, every finite graph boundary has zero
total component augmentation. -/
lemma componentAugmentationModTwo_comp_graphBoundaryModTwo
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (componentAugmentationModTwo V).comp (graphBoundaryModTwo G) = 0 := by
  -- It suffices to sum the matrix formula, then group the result by edge columns.
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.zero_apply,
    componentAugmentationModTwo_eq_sum]
  simp_rw [graphBoundaryModTwo_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.sum_mul]
  by_cases he : e ∈ G.edgeSet
  · rw [G.sum_incMatrix_apply_of_mem_edgeSet he]
    have hTwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    rw [hTwo, zero_mul]
  · rw [G.sum_incMatrix_apply_of_notMem_edgeSet he, zero_mul]

/-- Helper for Theorem 62.1: every mod-two graph boundary belongs to the kernel
of component augmentation. -/
lemma graphBoundaryModTwo_mem_componentKernel
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (x : Sym2 V →₀ ZMod 2) :
    graphBoundaryModTwo G x ∈
      LinearMap.ker (componentAugmentationModTwo V) := by
  -- Evaluate the already proved zero composite on the given edge chain.
  rw [LinearMap.mem_ker]
  have hComposite := LinearMap.congr_fun
    (componentAugmentationModTwo_comp_graphBoundaryModTwo G) x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hComposite

/-- Helper for Theorem 62.1: the graph boundary regarded as a map into the
augmentation kernel. -/
noncomputable def graphBoundaryModTwoToComponentKernel
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (Sym2 V →₀ ZMod 2) →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo V) :=
  (graphBoundaryModTwo G).codRestrict _
    (fun x ↦ graphBoundaryModTwo_mem_componentKernel G x)

/-- Helper for Theorem 62.1: coercing the kernel-valued graph boundary recovers
the original incidence boundary. -/
lemma graphBoundaryModTwoToComponentKernel_apply
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (x : Sym2 V →₀ ZMod 2) :
    ((graphBoundaryModTwoToComponentKernel G x :
      LinearMap.ker (componentAugmentationModTwo V)) : V →₀ ZMod 2) =
        graphBoundaryModTwo G x := by
  -- Use the named codomain-restriction computation rule rather than subtype reduction.
  exact LinearMap.codRestrict_apply _ _ _

/-- Helper for Theorem 62.1: reduced mod-two graph homology in degree zero is
the augmentation kernel modulo the range of the incidence boundary. -/
noncomputable abbrev graphReducedHomologyZeroModTwo
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :=
  LinearMap.ker (componentAugmentationModTwo V) ⧸
    LinearMap.range (graphBoundaryModTwoToComponentKernel G)

/-- Helper for Theorem 62.1: the reduced graph-homology quotient is trivial
exactly when incidence boundaries fill the augmentation kernel. -/
lemma graphReducedHomologyZeroModTwo_subsingleton_iff_exactFinsupp
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    Subsingleton (graphReducedHomologyZeroModTwo G) ↔
      Function.Exact (graphBoundaryModTwo G) (componentAugmentationModTwo V) := by
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro hRange
    -- Surjectivity onto the restricted kernel gives the missing exactness inclusion.
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      let z : LinearMap.ker (componentAugmentationModTwo V) := ⟨x, hx⟩
      have hz : z ∈ LinearMap.range (graphBoundaryModTwoToComponentKernel G) := by
        rw [hRange]
        exact Submodule.mem_top
      obtain ⟨y, hy⟩ := hz
      refine ⟨y, ?_⟩
      have hValues := congrArg
        (fun w : LinearMap.ker (componentAugmentationModTwo V) ↦
          (w : V →₀ ZMod 2)) hy
      simpa only [graphBoundaryModTwoToComponentKernel_apply] using hValues
    · exact LinearMap.range_le_ker_iff.mpr
        (componentAugmentationModTwo_comp_graphBoundaryModTwo G)
  · intro hExact
    -- Exactness makes the kernel-valued boundary map surjective.
    rw [LinearMap.range_eq_top]
    intro z
    rw [LinearMap.exact_iff] at hExact
    have hz : (z : V →₀ ZMod 2) ∈ LinearMap.range (graphBoundaryModTwo G) := by
      rw [← hExact]
      exact z.property
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, Subtype.ext ?_⟩
    rw [graphBoundaryModTwoToComponentKernel_apply]
    exact hy

/-- Helper for Theorem 62.1: reduced graph homology vanishes exactly when the
finite incidence matrix followed by vertex augmentation is exact. -/
lemma graphReducedHomologyZeroModTwo_subsingleton_iff_exact
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    Subsingleton (graphReducedHomologyZeroModTwo G) ↔
      Function.Exact (G.incMatrix (ZMod 2)).mulVecLin
        (vertexAugmentationMatrix V).mulVecLin := by
  let edgeCoefficients :=
    Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Sym2 V)
  let vertexCoefficients :=
    Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) V
  let totalCoefficient : ZMod 2 ≃ₗ[ZMod 2] Unit → ZMod 2 :=
    (LinearEquiv.funUnique Unit (ZMod 2) (ZMod 2)).symm
  have hBoundary :
      (G.incMatrix (ZMod 2)).mulVecLin ∘ₗ edgeCoefficients.toLinearMap =
        vertexCoefficients.toLinearMap ∘ₗ graphBoundaryModTwo G := by
    -- The definition of graph boundary is precisely this conjugation.
    apply LinearMap.ext
    intro x
    simp only [edgeCoefficients, vertexCoefficients, graphBoundaryModTwo,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hAugmentation :
      (vertexAugmentationMatrix V).mulVecLin ∘ₗ vertexCoefficients.toLinearMap =
        totalCoefficient.toLinearMap ∘ₗ componentAugmentationModTwo V := by
    -- Both sides are the same total coefficient, represented on `Unit` differently.
    apply LinearMap.ext
    intro x
    ext u
    simp only [LinearMap.comp_apply, vertexAugmentationMatrix_mulVecLin_apply,
      vertexCoefficients, Finsupp.linearEquivFunOnFinite_apply,
      componentAugmentationModTwo_eq_sum, totalCoefficient,
      LinearEquiv.coe_coe, LinearEquiv.funUnique_symm_apply]
    rfl
  -- Transport exactness through the three canonical coefficient equivalences.
  rw [graphReducedHomologyZeroModTwo_subsingleton_iff_exactFinsupp]
  exact (Function.Exact.iff_of_ladder_linearEquiv hBoundary hAugmentation).symm

/-- Helper for Theorem 62.1: summing coefficients commutes with pushing a
finitely supported chain forward along any function. -/
lemma componentAugmentationModTwo_comp_lmapDomain
    {V W : Type*} (q : V → W) :
    (componentAugmentationModTwo W).comp
        (Finsupp.lmapDomain (ZMod 2) (ZMod 2) q) =
      componentAugmentationModTwo V := by
  -- Compare the maps on the canonical one-vertex chains.
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, componentAugmentationModTwo,
    Finsupp.lsum_single, LinearMap.id_apply]

/-- Helper for Theorem 62.1: reindexing a finitely supported mod-two chain by an
equivalence preserves its total augmentation. -/
lemma componentAugmentationModTwo_domLCongr {V W : Type*} (e : V ≃ W)
    (x : V →₀ ZMod 2) :
    componentAugmentationModTwo W (Finsupp.domLCongr (R := ZMod 2) e x) =
      componentAugmentationModTwo V x := by
  -- Identify the equivalence reindexing with the injective map-domain operation.
  have hAugmentation := LinearMap.congr_fun
    (componentAugmentationModTwo_comp_lmapDomain e) x
  simpa only [LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain] using hAugmentation

/-- Helper for Theorem 62.1: reindexing by an equivalence sends augmentation-zero
chains to augmentation-zero chains. -/
lemma domLCongr_mem_componentAugmentationKernel {V W : Type*} (e : V ≃ W)
    (x : V →₀ ZMod 2) (hx : x ∈ LinearMap.ker (componentAugmentationModTwo V)) :
    Finsupp.domLCongr (R := ZMod 2) e x ∈
      LinearMap.ker (componentAugmentationModTwo W) := by
  -- Rewrite both kernel memberships as augmentation equations and use invariance.
  rw [LinearMap.mem_ker] at hx ⊢
  exact (componentAugmentationModTwo_domLCongr e x).trans hx

/-- Helper for Theorem 62.1: the linear reindexing map between two component
augmentation kernels. -/
noncomputable def componentAugmentationKernelMap {V W : Type*} (e : V ≃ W) :
    LinearMap.ker (componentAugmentationModTwo V) →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo W) :=
  ((Finsupp.domLCongr (R := ZMod 2) e).toLinearMap.domRestrict
      (LinearMap.ker (componentAugmentationModTwo V))).codRestrict _
    (fun x ↦ domLCongr_mem_componentAugmentationKernel e x x.property)

/-- Helper for Theorem 62.1: coercing the kernel reindexing map gives the
ordinary Finsupp domain reindexing. -/
lemma componentAugmentationKernelMap_apply {V W : Type*} (e : V ≃ W)
    (x : LinearMap.ker (componentAugmentationModTwo V)) :
    ((componentAugmentationKernelMap e x :
      LinearMap.ker (componentAugmentationModTwo W)) : W →₀ ZMod 2) =
        Finsupp.domLCongr (R := ZMod 2) e x := by
  -- Cross the codomain restriction with its named computation rule.
  exact LinearMap.codRestrict_apply _ _ _

/-- Helper for Theorem 62.1: reindexing by a type equivalence is bijective on
the corresponding component augmentation kernels. -/
lemma componentAugmentationKernelMap_bijective {V W : Type*} (e : V ≃ W) :
    Function.Bijective (componentAugmentationKernelMap e) := by
  constructor
  · intro x y hxy
    -- Injectivity follows after coercing to chains and using ambient reindexing.
    apply Subtype.ext
    apply (Finsupp.domLCongr (R := ZMod 2) e).injective
    have hCoe := congrArg
      (fun z : LinearMap.ker (componentAugmentationModTwo W) ↦ (z : W →₀ ZMod 2)) hxy
    simpa only [componentAugmentationKernelMap_apply] using hCoe
  · intro y
    -- Pull a target chain back along the inverse equivalence and retain its kernel proof.
    let xAmbient : V →₀ ZMod 2 := (Finsupp.domLCongr (R := ZMod 2) e).symm y
    have hx : xAmbient ∈ LinearMap.ker (componentAugmentationModTwo V) := by
      rw [LinearMap.mem_ker]
      have hAugmentation :=
        componentAugmentationModTwo_domLCongr e.symm (y : W →₀ ZMod 2)
      exact hAugmentation.trans y.property
    let x : LinearMap.ker (componentAugmentationModTwo V) := ⟨xAmbient, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [componentAugmentationKernelMap_apply]
    exact (Finsupp.domLCongr (R := ZMod 2) e).apply_symm_apply (y : W →₀ ZMod 2)

/-- Helper for Theorem 62.1: equivalent component-index types have linearly
equivalent mod-two augmentation kernels. -/
noncomputable def componentAugmentationKernelLinearEquiv {V W : Type*} (e : V ≃ W) :
    LinearMap.ker (componentAugmentationModTwo V) ≃ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo W) :=
  LinearEquiv.ofBijective (componentAugmentationKernelMap e)
    (componentAugmentationKernelMap_bijective e)

/-- Helper for Theorem 62.1: push a mod-two vertex chain forward to the graph's
connected-component chain module. -/
noncomputable def graphComponentChainsModTwo {V : Type*} (G : SimpleGraph V) :
    (V →₀ ZMod 2) →ₗ[ZMod 2] (G.ConnectedComponent →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) G.connectedComponentMk

/-- Helper for Theorem 62.1: the graph component-chain map preserves total
augmentation. -/
lemma componentAugmentationModTwo_comp_graphComponentChainsModTwo
    {V : Type*} (G : SimpleGraph V) :
    (componentAugmentationModTwo G.ConnectedComponent).comp
        (graphComponentChainsModTwo G) =
      componentAugmentationModTwo V := by
  -- Specialize functoriality of coefficient summation to the component projection.
  exact componentAugmentationModTwo_comp_lmapDomain G.connectedComponentMk

/-- Helper for Theorem 62.1: an actual graph edge has boundary equal to the sum
of its two endpoint chains over `ZMod 2`. -/
lemma graphBoundaryModTwo_single_of_adj_eq
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] {v w : V} (h : G.Adj v w) (a : ZMod 2) :
    graphBoundaryModTwo G (Finsupp.single s(v, w) a) =
      Finsupp.single v a + Finsupp.single w a := by
  -- Compare endpoint coefficients, separating the two endpoints from all other vertices.
  ext u
  rw [graphBoundaryModTwo_single_apply, SimpleGraph.incMatrix_apply']
  by_cases huv : u = v
  · subst u
    simp [G.mk'_mem_incidenceSet_iff, h, h.ne]
  · by_cases huw : u = w
    · subst u
      simp [G.mk'_mem_incidenceSet_iff, h, h.ne]
    · simp [G.mk'_mem_incidenceSet_iff, h, huv, huw]

/-- Helper for Theorem 62.1: a nonedge column of the graph incidence boundary
is zero. -/
lemma graphBoundaryModTwo_single_of_not_adj_eq_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] {v w : V} (h : ¬ G.Adj v w) (a : ZMod 2) :
    graphBoundaryModTwo G (Finsupp.single s(v, w) a) = 0 := by
  -- Every coefficient vanishes because the unordered pair is absent from all incidence sets.
  ext u
  rw [graphBoundaryModTwo_single_apply, SimpleGraph.incMatrix_apply']
  simp only [G.mk'_mem_incidenceSet_iff, h, false_and, if_false, zero_mul,
    Finsupp.zero_apply]

/-- Helper for Theorem 62.1: the sum of two adjacent endpoint chains lies in
the graph-boundary range. -/
lemma endpointChains_mem_graphBoundaryModTwoRange_of_adj
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] {v w : V} (h : G.Adj v w) (a : ZMod 2) :
    Finsupp.single v a + Finsupp.single w a ∈
      LinearMap.range (graphBoundaryModTwo G) := by
  -- The unordered edge generator maps to the required endpoint sum.
  exact ⟨Finsupp.single s(v, w) a,
    graphBoundaryModTwo_single_of_adj_eq G h a⟩

/-- Helper for Theorem 62.1: endpoints of any graph walk differ by a graph
boundary over `ZMod 2`. -/
lemma endpointChains_mem_graphBoundaryModTwoRange_of_walk
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] {v w : V} (p : G.Walk v w) (a : ZMod 2) :
    Finsupp.single v a + Finsupp.single w a ∈
      LinearMap.range (graphBoundaryModTwo G) := by
  -- Add the edge relations along the walk; each intermediate vertex occurs twice.
  induction p with
  | nil =>
      rename_i x
      have hZero : Finsupp.single x a + Finsupp.single x a = 0 := by
        apply Finsupp.ext
        intro u
        simp only [Finsupp.add_apply, Finsupp.zero_apply]
        exact CharTwo.add_self_eq_zero _
      rw [hZero]
      exact Submodule.zero_mem _
  | @cons u v w h p ih =>
      have hEdge := endpointChains_mem_graphBoundaryModTwoRange_of_adj G h a
      have hAdded := Submodule.add_mem _ hEdge ih
      have hNormalize :
          (Finsupp.single u a + Finsupp.single v a) +
              (Finsupp.single v a + Finsupp.single w a) =
            Finsupp.single u a + Finsupp.single w a := by
        apply Finsupp.ext
        intro z
        simp only [Finsupp.add_apply]
        calc
          (Finsupp.single u a z + Finsupp.single v a z) +
              (Finsupp.single v a z + Finsupp.single w a z) =
            Finsupp.single u a z +
                (Finsupp.single v a z + Finsupp.single v a z) +
              Finsupp.single w a z := by
                ac_rfl
          _ = Finsupp.single u a z + 0 + Finsupp.single w a z := by
                rw [CharTwo.add_self_eq_zero]
          _ = Finsupp.single u a z + Finsupp.single w a z := by
                rw [add_zero]
      rw [hNormalize] at hAdded
      exact hAdded

/-- Helper for Theorem 62.1: reachable vertices differ by a graph boundary over
`ZMod 2`. -/
lemma endpointChains_mem_graphBoundaryModTwoRange_of_reachable
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] {v w : V} (h : G.Reachable v w) (a : ZMod 2) :
    Finsupp.single v a + Finsupp.single w a ∈
      LinearMap.range (graphBoundaryModTwo G) := by
  -- Choose a witnessing walk and apply the endpoint calculation.
  exact h.elim (fun p ↦ endpointChains_mem_graphBoundaryModTwoRange_of_walk G p a)

/-- Helper for Theorem 62.1: graph incidence boundaries vanish after vertex
chains are pushed to graph connected components. -/
lemma graphComponentChainsModTwo_comp_graphBoundaryModTwo
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (graphComponentChainsModTwo G).comp (graphBoundaryModTwo G) = 0 := by
  -- Check the relation on one unordered-pair generator and split on whether it is an edge.
  apply Finsupp.lhom_ext
  intro e a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  refine e.ind ?_
  intro v w
  by_cases h : G.Adj v w
  · rw [graphBoundaryModTwo_single_of_adj_eq G h]
    simp only [map_add, graphComponentChainsModTwo, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h]
    apply Finsupp.ext
    intro C
    simp only [Finsupp.add_apply, Finsupp.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · rw [graphBoundaryModTwo_single_of_not_adj_eq_zero G h, map_zero]

/-- Helper for Theorem 62.1: pushing vertex chains to graph components sends
the augmentation kernel into the component augmentation kernel. -/
lemma graphComponentChainsModTwo_mem_componentKernel
    {V : Type*} (G : SimpleGraph V) (x : V →₀ ZMod 2)
    (hx : x ∈ LinearMap.ker (componentAugmentationModTwo V)) :
    graphComponentChainsModTwo G x ∈
      LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent) := by
  -- The component projection preserves augmentation, so it preserves its kernel.
  rw [LinearMap.mem_ker] at hx ⊢
  have hAugmentation := LinearMap.congr_fun
    (componentAugmentationModTwo_comp_graphComponentChainsModTwo G) x
  calc
    componentAugmentationModTwo G.ConnectedComponent
        (graphComponentChainsModTwo G x) =
      componentAugmentationModTwo V x := by
        simpa only [LinearMap.comp_apply] using hAugmentation
    _ = 0 := hx

/-- Helper for Theorem 62.1: the component-chain map restricted to the two
augmentation kernels. -/
noncomputable def graphComponentKernelMap
    {V : Type*} (G : SimpleGraph V) :
    LinearMap.ker (componentAugmentationModTwo V) →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent) :=
  ((graphComponentChainsModTwo G).domRestrict
      (LinearMap.ker (componentAugmentationModTwo V))).codRestrict _
    (fun x ↦ graphComponentChainsModTwo_mem_componentKernel G x x.property)

/-- Helper for Theorem 62.1: coercing the kernel-restricted component map gives
the original pushforward on vertex chains. -/
lemma graphComponentKernelMap_apply
    {V : Type*} (G : SimpleGraph V)
    (x : LinearMap.ker (componentAugmentationModTwo V)) :
    ((graphComponentKernelMap G x :
      LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent)) :
        G.ConnectedComponent →₀ ZMod 2) =
      graphComponentChainsModTwo G x := by
  -- Use the codomain-restriction computation rule at the ambient chain level.
  exact LinearMap.codRestrict_apply _ _ _

/-- Helper for Theorem 62.1: the augmentation-kernel component map annihilates
the kernel-valued graph boundary. -/
lemma graphComponentKernelMap_comp_graphBoundaryModTwoToComponentKernel
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (graphComponentKernelMap G).comp
        (graphBoundaryModTwoToComponentKernel G) = 0 := by
  -- Push the equality to ambient component chains and reuse the proved zero composite.
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hComposite := LinearMap.congr_fun
    (graphComponentChainsModTwo_comp_graphBoundaryModTwo G) x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
    graphComponentKernelMap_apply,
    graphBoundaryModTwoToComponentKernel_apply,
    ZeroMemClass.coe_zero] using hComposite

/-- Helper for Theorem 62.1: the incidence-boundary range is contained in the
kernel of the component map. -/
lemma graphBoundaryModTwoRange_le_graphComponentKernelMap_ker
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    LinearMap.range (graphBoundaryModTwoToComponentKernel G) ≤
      LinearMap.ker (graphComponentKernelMap G) := by
  -- Range-to-kernel containment is exactly the zero-composite relation.
  exact LinearMap.range_le_ker_iff.mpr
    (graphComponentKernelMap_comp_graphBoundaryModTwoToComponentKernel G)

/-- Helper for Theorem 62.1: the graph component map descends from reduced
mod-two graph homology to the component augmentation kernel. -/
noncomputable def graphReducedHomologyZeroModTwoToComponentKernel
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    graphReducedHomologyZeroModTwo G →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent) :=
  (LinearMap.range (graphBoundaryModTwoToComponentKernel G)).liftQ
    (graphComponentKernelMap G)
    (graphBoundaryModTwoRange_le_graphComponentKernelMap_ker G)

/-- Helper for Theorem 62.1: choose the canonical quotient representative of a
graph connected component. -/
noncomputable def graphComponentRepresentative
    {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) : V :=
  Quot.out C

/-- Helper for Theorem 62.1: the chosen representative belongs to its original
graph connected component. -/
lemma connectedComponentMk_graphComponentRepresentative
    {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) :
    G.connectedComponentMk (graphComponentRepresentative G C) = C := by
  -- This is the computation rule for the quotient representative.
  exact Quot.out_eq C

/-- Helper for Theorem 62.1: lift component chains back to chosen representative
vertex chains. -/
noncomputable def graphComponentChainSection
    {V : Type*} (G : SimpleGraph V) :
    (G.ConnectedComponent →₀ ZMod 2) →ₗ[ZMod 2] (V →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (graphComponentRepresentative G)

/-- Helper for Theorem 62.1: pushing a chosen representative-chain back to
components is the identity. -/
lemma graphComponentChainsModTwo_comp_graphComponentChainSection
    {V : Type*} (G : SimpleGraph V) :
    (graphComponentChainsModTwo G).comp (graphComponentChainSection G) =
      LinearMap.id := by
  -- Check the section equation on one component-chain generator.
  apply Finsupp.lhom_ext
  intro C a
  simp only [LinearMap.comp_apply, graphComponentChainSection,
    graphComponentChainsModTwo, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single,
    connectedComponentMk_graphComponentRepresentative, LinearMap.id_apply]

/-- Helper for Theorem 62.1: lifting along chosen component representatives
preserves the augmentation kernel. -/
lemma graphComponentChainSection_mem_componentKernel
    {V : Type*} (G : SimpleGraph V) (x : G.ConnectedComponent →₀ ZMod 2)
    (hx : x ∈ LinearMap.ker
      (componentAugmentationModTwo G.ConnectedComponent)) :
    graphComponentChainSection G x ∈
      LinearMap.ker (componentAugmentationModTwo V) := by
  -- Coefficient summation is unchanged by choosing one representative per component.
  rw [LinearMap.mem_ker] at hx ⊢
  have hAugmentation := LinearMap.congr_fun
    (componentAugmentationModTwo_comp_lmapDomain
      (graphComponentRepresentative G)) x
  calc
    componentAugmentationModTwo V (graphComponentChainSection G x) =
      componentAugmentationModTwo G.ConnectedComponent x := by
        simpa only [graphComponentChainSection, LinearMap.comp_apply] using hAugmentation
    _ = 0 := hx

/-- Helper for Theorem 62.1: the representative-chain section restricted to
component augmentation kernels. -/
noncomputable def graphComponentKernelSection
    {V : Type*} (G : SimpleGraph V) :
    LinearMap.ker (componentAugmentationModTwo G.ConnectedComponent) →ₗ[ZMod 2]
      LinearMap.ker (componentAugmentationModTwo V) :=
  ((graphComponentChainSection G).domRestrict
      (LinearMap.ker
        (componentAugmentationModTwo G.ConnectedComponent))).codRestrict _
    (fun x ↦ graphComponentChainSection_mem_componentKernel G x x.property)

/-- Helper for Theorem 62.1: coercing the restricted representative-chain map
recovers the ambient representative chain. -/
lemma graphComponentKernelSection_apply
    {V : Type*} (G : SimpleGraph V)
    (x : LinearMap.ker
      (componentAugmentationModTwo G.ConnectedComponent)) :
    ((graphComponentKernelSection G x :
      LinearMap.ker (componentAugmentationModTwo V)) : V →₀ ZMod 2) =
        graphComponentChainSection G x := by
  -- Use the codomain-restriction computation rule at the ambient vertex-chain level.
  exact LinearMap.codRestrict_apply _ _ _

/-- Helper for Theorem 62.1: the restricted representative-chain map is a
right inverse to the restricted component map. -/
lemma graphComponentKernelMap_comp_graphComponentKernelSection
    {V : Type*} (G : SimpleGraph V) :
    (graphComponentKernelMap G).comp (graphComponentKernelSection G) =
      LinearMap.id := by
  -- Compare ambient component chains and use the previously proved section equation.
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hSection := LinearMap.congr_fun
    (graphComponentChainsModTwo_comp_graphComponentChainSection G) x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    graphComponentKernelMap_apply,
    graphComponentKernelSection_apply] using hSection

/-- Helper for Theorem 62.1: the descended graph-homology map onto the component
augmentation kernel is surjective. -/
lemma graphReducedHomologyZeroModTwoToComponentKernel_surjective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    Function.Surjective (graphReducedHomologyZeroModTwoToComponentKernel G) := by
  -- Lift a target kernel chain to representatives, then take its quotient class.
  intro y
  let x := graphComponentKernelSection G y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [graphReducedHomologyZeroModTwoToComponentKernel,
    Submodule.liftQ_apply]
  have hSection := LinearMap.congr_fun
    (graphComponentKernelMap_comp_graphComponentKernelSection G) y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, x] using hSection

/-- Helper for Theorem 62.1: the kernel of the vertex-to-component chain map is
exactly the graph incidence-boundary range. -/
lemma graphComponentChainsModTwo_ker_eq_graphBoundaryModTwo_range
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    LinearMap.ker (graphComponentChainsModTwo G) =
      LinearMap.range (graphBoundaryModTwo G) := by
  -- One inclusion reconstructs a boundary by joining each supported vertex to
  -- the chosen representative of its component; the other is the zero composite.
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hReachable (v : V) :
        G.Reachable v
          (graphComponentRepresentative G (G.connectedComponentMk v)) :=
      SimpleGraph.ConnectedComponent.eq.mp
        (connectedComponentMk_graphComponentRepresentative G
          (G.connectedComponentMk v)).symm
    have hRangeSum :
        (∑ v ∈ x.support,
            (Finsupp.single v (x v) +
              Finsupp.single
                (graphComponentRepresentative G (G.connectedComponentMk v)) (x v))) ∈
          LinearMap.range (graphBoundaryModTwo G) := by
      apply Submodule.sum_mem
      intro v _
      exact endpointChains_mem_graphBoundaryModTwoRange_of_reachable G
        (hReachable v) (x v)
    have hSumEq :
        (∑ v ∈ x.support,
            (Finsupp.single v (x v) +
              Finsupp.single
                (graphComponentRepresentative G (G.connectedComponentMk v)) (x v))) =
          x + graphComponentChainSection G (graphComponentChainsModTwo G x) := by
      calc
        (∑ v ∈ x.support,
            (Finsupp.single v (x v) +
              Finsupp.single
                (graphComponentRepresentative G (G.connectedComponentMk v)) (x v))) =
            (∑ v ∈ x.support, Finsupp.single v (x v)) +
              ∑ v ∈ x.support,
                Finsupp.single
                  (graphComponentRepresentative G (G.connectedComponentMk v)) (x v) :=
          Finset.sum_add_distrib
        _ = x + Finsupp.mapDomain
              (graphComponentRepresentative G ∘ G.connectedComponentMk) x := by
          have hFirst :
              (∑ v ∈ x.support, Finsupp.single v (x v)) = x :=
            x.sum_single
          have hSecond :
              (∑ v ∈ x.support,
                  Finsupp.single
                    (graphComponentRepresentative G (G.connectedComponentMk v)) (x v)) =
                Finsupp.mapDomain
                  (graphComponentRepresentative G ∘ G.connectedComponentMk) x :=
            rfl
          exact congrArg₂ (fun y z ↦ y + z) hFirst hSecond
        _ = x + Finsupp.mapDomain (graphComponentRepresentative G)
              (Finsupp.mapDomain G.connectedComponentMk x) := by
          rw [Finsupp.mapDomain_comp]
        _ = x + graphComponentChainSection G
              (graphComponentChainsModTwo G x) := rfl
    rw [hx, map_zero, add_zero] at hSumEq
    rw [hSumEq] at hRangeSum
    exact hRangeSum
  · exact LinearMap.range_le_ker_iff.mpr
      (graphComponentChainsModTwo_comp_graphBoundaryModTwo G)

/-- Helper for Theorem 62.1: after restricting to augmentation kernels, the
component-map kernel is still exactly the incidence-boundary range. -/
lemma graphComponentKernelMap_ker_eq_graphBoundaryModTwoToComponentKernel_range
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    LinearMap.ker (graphComponentKernelMap G) =
      LinearMap.range (graphBoundaryModTwoToComponentKernel G) := by
  -- Compare both memberships after coercion to ambient vertex chains.
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hAmbientZero : graphComponentChainsModTwo G (x : V →₀ ZMod 2) = 0 := by
      have hCoe := congrArg
        (fun y : LinearMap.ker
          (componentAugmentationModTwo G.ConnectedComponent) ↦
            (y : G.ConnectedComponent →₀ ZMod 2)) hx
      simpa only [graphComponentKernelMap_apply,
        ZeroMemClass.coe_zero] using hCoe
    have hAmbientMem : (x : V →₀ ZMod 2) ∈
        LinearMap.ker (graphComponentChainsModTwo G) := by
      rw [LinearMap.mem_ker]
      exact hAmbientZero
    rw [graphComponentChainsModTwo_ker_eq_graphBoundaryModTwo_range G] at hAmbientMem
    rcases hAmbientMem with ⟨e, he⟩
    refine ⟨e, ?_⟩
    apply Subtype.ext
    simpa only [graphBoundaryModTwoToComponentKernel_apply] using he
  · intro x hx
    rcases hx with ⟨e, rfl⟩
    rw [LinearMap.mem_ker]
    have hComposite := LinearMap.congr_fun
      (graphComponentKernelMap_comp_graphBoundaryModTwoToComponentKernel G) e
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hComposite

/-- Helper for Theorem 62.1: the descended graph-homology map to the component
augmentation kernel is injective. -/
lemma graphReducedHomologyZeroModTwoToComponentKernel_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    Function.Injective (graphReducedHomologyZeroModTwoToComponentKernel G) := by
  -- Its quotient submodule is exactly the kernel of the map being descended.
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot'
    (LinearMap.range (graphBoundaryModTwoToComponentKernel G))
    (graphComponentKernelMap G)
    (graphComponentKernelMap_ker_eq_graphBoundaryModTwoToComponentKernel_range G).symm

/-- Helper for Theorem 62.1: reduced mod-two `H₀` of a finite graph is linearly
equivalent to the augmentation kernel on its connected components. -/
lemma graphReducedHomologyZeroModTwo_linearEquiv_componentKernel
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    Nonempty
      (graphReducedHomologyZeroModTwo G ≃ₗ[ZMod 2]
        LinearMap.ker
          (componentAugmentationModTwo G.ConnectedComponent)) := by
  -- Bundle the proved injectivity and surjectivity of the descended map.
  exact ⟨LinearEquiv.ofBijective
    (graphReducedHomologyZeroModTwoToComponentKernel G)
    ⟨graphReducedHomologyZeroModTwoToComponentKernel_injective G,
      graphReducedHomologyZeroModTwoToComponentKernel_surjective G⟩⟩

end InvarianceOfDomainSupport

end
