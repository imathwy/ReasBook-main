module

public import Topology_Munkres_2000.Book.Remark_60_1.SmallSingularChains
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Simplicial

/-- Helper for Theorem 63.7: the identity map of the standard topological
`n`-simplex, regarded as its universal singular `n`-simplex. -/
def standardSimplexIdentitySingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).symm
    (ContinuousMap.id _)

/-- Helper for Theorem 63.7: under the singular-simplex equivalence, the
universal singular simplex is the identity continuous map. -/
lemma toSSetObjEquiv_standardSimplexIdentitySingularSimplex (n : ℕ) :
    (TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
        (Opposite.op (SimplexCategory.mk n))
        (standardSimplexIdentitySingularSimplex n) =
      ContinuousMap.id _ := by
  -- Unpack the universal simplex through the defining equivalence.
  exact Equiv.apply_symm_apply _ _

/-- Helper for Theorem 63.7: a singular simplex determines the continuous map
from its standard topological simplex into the ambient space. -/
def standardSimplexSingularMap (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ X :=
  TopCat.ofHom (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) sigma)

/-- Helper for Theorem 63.7: pushing the universal identity simplex along the
map represented by a singular simplex recovers that simplex. -/
lemma map_standardSimplexIdentitySingularSimplex (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.map (standardSimplexSingularMap X n sigma)).app
        (Opposite.op (SimplexCategory.mk n))
        (standardSimplexIdentitySingularSimplex n) = sigma := by
  -- Compare continuous representatives: postcomposition with the identity does nothing.
  apply (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))).injective
  rw [toSSetObjEquiv_map,
    toSSetObjEquiv_standardSimplexIdentitySingularSimplex]
  rfl

/-- Helper for Theorem 63.7: the integral fundamental chain of the standard
topological `n`-simplex is its universal singular-simplex generator. -/
def integralStandardSimplexFundamentalChain (n : ℕ) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  (TopCat.toSSet.obj
    (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
      (standardSimplexIdentitySingularSimplex n)

/-- Helper for Theorem 63.7: the boundary of the universal integral
fundamental chain is the alternating sum of its face generators. -/
lemma integralStandardSimplexFundamentalChain_boundary (n : ℕ) :
    integralStandardSimplexFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
            ((TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i
                (standardSimplexIdentitySingularSimplex (n + 1))) := by
  -- Apply the standard boundary computation to the universal generator.
  exact SSet.ιChainComplex_d
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2)))))
    (ModuleCat.of ℤ ℤ) (standardSimplexIdentitySingularSimplex (n + 1))

/-- Helper for Theorem 63.7: every integral singular-simplex generator is the
pushforward of the universal fundamental chain of its standard simplex. -/
lemma integralStandardSimplexFundamentalChain_naturality (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    integralStandardSimplexFundamentalChain n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (standardSimplexSingularMap X n sigma))
          (ModuleCat.of ℤ ℤ)).f n =
      (TopCat.toSSet.obj X).ιChainComplex sigma := by
  -- Naturality of simplex generators reduces the claim to the preceding map computation.
  rw [integralStandardSimplexFundamentalChain, SSet.ι_chainComplexMap_f,
    map_standardSimplexIdentitySingularSimplex]

/-- Helper for Theorem 63.7: the `k`-th vertex in the barycentric simplex
indexed by a permutation is the barycenter of its first `k + 1` vertices. -/
def standardSimplexBarycentricVertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : stdSimplex ℝ (Fin (n + 1)) :=
  stdSimplex.map
    (fun j : Fin (k.val + 1) ↦
      π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) j))
    (stdSimplex.barycenter : stdSimplex ℝ (Fin (k.val + 1)))

/-- Helper for Theorem 63.7: the coordinate formula for the affine simplex
whose ordered vertices are successive face barycenters. -/
def standardSimplexBarycentricMapFunction (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (x : stdSimplex ℝ (Fin (n + 1))) :
    Fin (n + 1) → ℝ :=
  fun j ↦ ∑ k, x k * standardSimplexBarycentricVertex n π k j

/-- Helper for Theorem 63.7: the affine combination of successive face
barycenters lies in the standard simplex. -/
lemma standardSimplexBarycentricMapFunction_mem (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (x : stdSimplex ℝ (Fin (n + 1))) :
    standardSimplexBarycentricMapFunction n π x ∈
      stdSimplex ℝ (Fin (n + 1)) := by
  constructor
  · intro j
    -- Every coordinate is a sum of products of nonnegative barycentric coordinates.
    exact Finset.sum_nonneg fun k _ ↦
      mul_nonneg (stdSimplex.zero_le x k)
        (stdSimplex.zero_le (standardSimplexBarycentricVertex n π k) j)
  · -- Interchange the finite sums; each barycentric vertex has coordinate sum one.
    unfold standardSimplexBarycentricMapFunction
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]

/-- Helper for Theorem 63.7: the affine simplex associated to a permutation of
the original vertices and its chain of successive barycenters. -/
def standardSimplexBarycentricMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)) :=
  fun x ↦ ⟨standardSimplexBarycentricMapFunction n π x,
    standardSimplexBarycentricMapFunction_mem n π x⟩

/-- Helper for Theorem 63.7: the underlying coordinates of a barycentric
affine simplex map are its defining finite affine combination. -/
lemma coe_standardSimplexBarycentricMap (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (x : stdSimplex ℝ (Fin (n + 1))) :
    (standardSimplexBarycentricMap n π x : Fin (n + 1) → ℝ) =
      standardSimplexBarycentricMapFunction n π x := by
  -- Forgetting the subtype witness exposes the coordinate definition.
  rfl

/-- Helper for Theorem 63.7: the barycentric affine map sends its `k`-th
standard vertex to the barycenter of the first `k + 1` permuted vertices. -/
lemma standardSimplexBarycentricMap_vertex (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    standardSimplexBarycentricMap n π (stdSimplex.vertex k) =
      standardSimplexBarycentricVertex n π k := by
  -- Evaluate the affine combination at a standard basis vector.
  classical
  apply stdSimplex.ext
  rw [coe_standardSimplexBarycentricMap]
  funext j
  unfold standardSimplexBarycentricMapFunction
  simp only [stdSimplex.vertex_coe, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Helper for Theorem 63.7: each barycentric affine simplex map is continuous. -/
lemma continuous_standardSimplexBarycentricMap (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) :
    Continuous (standardSimplexBarycentricMap n π) := by
  -- Continuity is coordinatewise, and every coordinate is a finite linear combination.
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  apply continuous_finsetSum Finset.univ
  intro k _
  exact ((continuous_apply k).comp continuous_subtype_val).mul continuous_const

/-- Helper for Theorem 63.7: the barycentric affine simplex map bundled as a
continuous self-map of the standard topological simplex. -/
def standardSimplexBarycentricContinuousMap (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  ⟨standardSimplexBarycentricMap n π,
    continuous_standardSimplexBarycentricMap n π⟩

/-- Helper for Theorem 63.7: a permutation determines the singular simplex
spanned by its chain of successive face barycenters. -/
def standardSimplexBarycentricSingularSimplex (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).symm
      (standardSimplexBarycentricContinuousMap n π)

/-- Helper for Theorem 63.7: the universal barycentric subdivision chain is
the signed sum of the simplices indexed by vertex permutations. -/
def integralStandardSimplexBarycentricSubdivisionChain (n : ℕ) :
    ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (ModuleCat.of ℤ ℤ)).X n :=
  ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (standardSimplexBarycentricSingularSimplex n π)

/-- Helper for Theorem 63.7: barycentric subdivision of one singular simplex is
the pushforward of the universal barycentric subdivision chain. -/
def integralSingularSimplexBarycentricSubdivision (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶ ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  integralStandardSimplexBarycentricSubdivisionChain n ≫
    (SSet.chainComplexMap
      (TopCat.toSSet.map (standardSimplexSingularMap X n sigma))
      (ModuleCat.of ℤ ℤ)).f n

/-- Helper for Theorem 63.7: simplexwise barycentric subdivision is the
universal subdivision chain followed by the represented simplex map. -/
lemma integralSingularSimplexBarycentricSubdivision_eq_universal_comp
    (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    integralSingularSimplexBarycentricSubdivision X n sigma =
      integralStandardSimplexBarycentricSubdivisionChain n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (standardSimplexSingularMap X n sigma))
          (ModuleCat.of ℤ ℤ)).f n := by
  -- Expose the construction once at its owner so clients need no cross-module unfolding.
  rfl

/-- Helper for Theorem 63.7: subdivision of a singular-simplex generator is the
signed sum of its barycentric subsimplices. -/
lemma integralSingularSimplexBarycentricSubdivision_eq_sum (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    integralSingularSimplexBarycentricSubdivision X n sigma =
      ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.map (standardSimplexSingularMap X n sigma)).app
            (Opposite.op (SimplexCategory.mk n))
              (standardSimplexBarycentricSingularSimplex n π)) := by
  -- Distribute pushforward over the signed sum and compute it on each generator.
  unfold integralSingularSimplexBarycentricSubdivision
  rw [integralStandardSimplexBarycentricSubdivisionChain, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]

/-- Helper for Theorem 63.7: every barycentric subsimplex of a singular simplex
has image contained in the image of the original simplex. -/
lemma range_barycentricSubsimplex_subset_range (X : TopCat) (n : ℕ)
    (sigma : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (π : Equiv.Perm (Fin (n + 1))) :
    Set.range
        (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))
          ((TopCat.toSSet.map (standardSimplexSingularMap X n sigma)).app
            (Opposite.op (SimplexCategory.mk n))
              (standardSimplexBarycentricSingularSimplex n π))) ⊆
      Set.range
        (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) sigma) := by
  -- The continuous representative is a composite through the original simplex.
  rw [toSSetObjEquiv_map]
  rintro y ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- Helper for Theorem 63.7: a barycentric vertex has its constant nonzero
coordinate exactly on the corresponding permutation prefix. -/
private lemma standardSimplexBarycentricVertex_apply (n : ℕ)
    (k : Fin (n + 2)) (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    standardSimplexBarycentricVertex (n + 1) π k j =
      if j ∈ Set.range (fun l : Fin (k.val + 1) ↦
          π (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l))
        then ((k.val + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  -- Expand the simplex map as the sum over the fiber of the chosen coordinate.
  unfold standardSimplexBarycentricVertex
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

/-- Helper for Theorem 63.7: swapping the two positions adjacent to a retained
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

/-- Helper for Theorem 63.7: right multiplication by an adjacent swap leaves
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

/-- Helper for Theorem 63.7: corresponding retained barycentric vertices agree
after an adjacent transposition. -/
private lemma standardSimplexBarycentricVertex_adjacentSwap (n : ℕ)
    (i k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2))) :
    standardSimplexBarycentricVertex (n + 1)
        (π * Equiv.swap i.castSucc i.succ) (i.castSucc.succAbove k) =
      standardSimplexBarycentricVertex (n + 1) π (i.castSucc.succAbove k) := by
  classical
  apply stdSimplex.ext
  funext j
  -- Both coordinate formulas use the same prefix range.
  rw [standardSimplexBarycentricVertex_apply,
    standardSimplexBarycentricVertex_apply]
  simp only [range_adjacentSwap_castLE_succAbove]

/-- Helper for Theorem 63.7: the two barycentric affine maps agree on the
nonfinal face paired by an adjacent transposition. -/
private lemma standardSimplexBarycentricMap_face_adjacentSwap (n : ℕ)
    (i : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2)))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    standardSimplexBarycentricMap (n + 1)
        (π * Equiv.swap i.castSucc i.succ) (stdSimplex.map i.castSucc.succAbove z) =
      standardSimplexBarycentricMap (n + 1) π
        (stdSimplex.map i.castSucc.succAbove z) := by
  classical
  apply stdSimplex.ext
  rw [coe_standardSimplexBarycentricMap, coe_standardSimplexBarycentricMap]
  funext j
  unfold standardSimplexBarycentricMapFunction
  apply Finset.sum_congr rfl
  intro k _
  rcases Fin.eq_self_or_eq_succAbove i.castSucc k with rfl | ⟨k, rfl⟩
  · have hzero : stdSimplex.map i.castSucc.succAbove z i.castSucc = 0 := by
      rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      simp only [Finset.filter_false_of_mem (fun x _ ↦ Fin.succAbove_ne i.castSucc x),
        Finset.sum_empty]
    -- The omitted coordinate contributes zero to both affine combinations.
    rw [hzero, zero_mul, zero_mul]
  · -- Every retained coordinate uses the paired vertex equality.
    rw [standardSimplexBarycentricVertex_adjacentSwap]

/-- Helper for Theorem 63.7: deleting a nonfinal barycenter gives the same
singular face after swapping the adjacent permutation entries. -/
lemma standardSimplexBarycentricSingularSimplex_δ_adjacentSwap (n : ℕ)
    (i : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2))) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
        (standardSimplexBarycentricSingularSimplex (n + 1)
          (π * Equiv.swap i.castSucc i.succ)) =
      (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
        (standardSimplexBarycentricSingularSimplex (n + 1) π) := by
  -- Compare the continuous representatives pointwise on the standard face.
  apply ((TopCat.of (stdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  simp only [standardSimplexBarycentricSingularSimplex, Equiv.apply_symm_apply,
    standardSimplexBarycentricContinuousMap]
  exact standardSimplexBarycentricMap_face_adjacentSwap n i π z

/-- Helper for Theorem 63.7: for a fixed nonfinal face, the signed sum of all
barycentric singular faces cancels in adjacent-transposition pairs. -/
lemma integralStandardSimplexBarycentricInteriorFaces_sum_eq_zero (n : ℕ)
    (i : Fin (n + 1)) :
    ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
      (TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
              (standardSimplexBarycentricSingularSimplex (n + 1) π)) = 0 := by
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
    have hface := standardSimplexBarycentricSingularSimplex_δ_adjacentSwap n i π
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

/-- Helper for Theorem 63.7: order the vertices of the face opposite `r` by
`τ`, then append `r` as the final vertex. -/
def standardSimplexBarycentricLastPermutation (n : ℕ) (r : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Fin.cycleIcc r (Fin.last (n + 1)) *
    τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1)))

/-- Helper for Theorem 63.7: the final value of the last-vertex permutation is
the omitted face vertex. -/
lemma standardSimplexBarycentricLastPermutation_last (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    standardSimplexBarycentricLastPermutation n r τ (Fin.last (n + 1)) = r := by
  classical
  unfold standardSimplexBarycentricLastPermutation
  rw [Equiv.Perm.mul_apply]
  rw [Equiv.Perm.extendDomain_apply_not_subtype]
  · -- The interval cycle sends its upper endpoint back to `r`.
    exact Fin.cycleIcc_of_last (Fin.le_last r)
  · simp only [not_ne_iff]

/-- Helper for Theorem 63.7: before the final value, the last-vertex
permutation follows the ordered face inclusion. -/
lemma standardSimplexBarycentricLastPermutation_castSucc (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    standardSimplexBarycentricLastPermutation n r τ k.castSucc =
      r.succAbove (τ k) := by
  classical
  unfold standardSimplexBarycentricLastPermutation
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

/-- Helper for Theorem 63.7: the sign of the last-vertex permutation splits
into the interval-cycle sign and the face-ordering sign. -/
lemma standardSimplexBarycentricLastPermutation_sign (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (standardSimplexBarycentricLastPermutation n r τ).sign =
      (-1) ^ (Fin.last (n + 1) - r : ℕ) * τ.sign := by
  classical
  -- Multiplicativity, the cycle sign, and extension invariance give the formula.
  unfold standardSimplexBarycentricLastPermutation
  rw [Equiv.Perm.sign_mul, Fin.sign_cycleIcc_of_le (Fin.le_last r),
    Equiv.Perm.sign_extendDomain]

/-- Helper for Theorem 63.7: the omitted vertex and its face ordering
parameterize all top-dimensional permutations bijectively. -/
lemma standardSimplexBarycentricLastPermutation_bijective (n : ℕ) :
    Function.Bijective
      (fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
        standardSimplexBarycentricLastPermutation n p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have hr : r = r' := by
      have happ := congrArg
        (fun π : Equiv.Perm (Fin (n + 2)) ↦ π (Fin.last (n + 1))) h
      simpa only [standardSimplexBarycentricLastPermutation_last] using happ
    subst r'
    have hτ : τ = τ' := by
      apply Equiv.ext
      intro k
      have happ := congrArg
        (fun π : Equiv.Perm (Fin (n + 2)) ↦ π k.castSucc) h
      rw [standardSimplexBarycentricLastPermutation_castSucc,
        standardSimplexBarycentricLastPermutation_castSucc] at happ
      exact Fin.succAbove_right_injective happ
    subst τ'
    rfl
  · -- The two finite parameter spaces both have cardinality `(n + 2)!`.
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_perm,
      Nat.factorial_succ]

/-- Helper for Theorem 63.7: retained vertices of the last-vertex permutation
are the barycentric vertices of the ordered face, mapped by `r.succAbove`. -/
lemma standardSimplexBarycentricLastPermutation_vertex (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    standardSimplexBarycentricVertex (n + 1)
        (standardSimplexBarycentricLastPermutation n r τ) k.castSucc =
      stdSimplex.map r.succAbove (standardSimplexBarycentricVertex n τ k) := by
  unfold standardSimplexBarycentricVertex
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
    standardSimplexBarycentricLastPermutation n r τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.castSucc.isLt)) l) =
      standardSimplexBarycentricLastPermutation n r τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l).castSucc :=
          congrArg (standardSimplexBarycentricLastPermutation n r τ) hcast
    _ = r.succAbove (τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) l)) :=
      standardSimplexBarycentricLastPermutation_castSucc n r τ _
    _ = (r.succAbove ∘ fun j ↦ τ
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) j)) l := rfl

/-- Helper for Theorem 63.7: a standard-simplex face inclusion preserves the
coordinate indexed by a vertex in its image. -/
private lemma standardSimplex_map_succAbove_apply {n : ℕ} (r : Fin (n + 1))
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

/-- Helper for Theorem 63.7: a standard-simplex face inclusion has zero
coordinate at its omitted vertex. -/
private lemma standardSimplex_map_succAbove_self {n : ℕ} (r : Fin (n + 1))
    (z : stdSimplex ℝ (Fin n)) :
    stdSimplex.map r.succAbove z r = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfilter : Finset.univ.filter (fun l : Fin n ↦ r.succAbove l = r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact Fin.succAbove_ne r l hl
  -- The omitted vertex has an empty fiber under the face inclusion.
  rw [hfilter, Finset.sum_empty]

/-- Helper for Theorem 63.7: restricting a last-vertex barycentric affine map
to its final face is barycentric subdivision inside the corresponding face. -/
lemma standardSimplexBarycentricLastPermutation_map (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    standardSimplexBarycentricMap (n + 1)
        (standardSimplexBarycentricLastPermutation n r τ)
        (stdSimplex.map (Fin.last (n + 1)).succAbove z) =
      stdSimplex.map r.succAbove (standardSimplexBarycentricMap n τ z) := by
  classical
  apply stdSimplex.ext
  rw [coe_standardSimplexBarycentricMap]
  funext q
  rcases Fin.eq_self_or_eq_succAbove r q with rfl | ⟨j, rfl⟩
  · rw [standardSimplex_map_succAbove_self]
    unfold standardSimplexBarycentricMapFunction
    rw [Fin.sum_univ_castSucc]
    have hlast : stdSimplex.map (Fin.last (n + 1)).succAbove z
        (Fin.last (n + 1)) = 0 := standardSimplex_map_succAbove_self _ z
    rw [hlast, zero_mul, add_zero]
    apply Finset.sum_eq_zero
    intro k _
    -- Every retained vertex lies in the face, so its omitted coordinate is zero.
    rw [standardSimplexBarycentricLastPermutation_vertex,
      standardSimplex_map_succAbove_self, mul_zero]
  · rw [standardSimplex_map_succAbove_apply]
    rw [coe_standardSimplexBarycentricMap]
    unfold standardSimplexBarycentricMapFunction
    rw [Fin.sum_univ_castSucc]
    have hlast : stdSimplex.map (Fin.last (n + 1)).succAbove z
        (Fin.last (n + 1)) = 0 := standardSimplex_map_succAbove_self _ z
    rw [hlast, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    -- On retained coordinates, both sides have the same affine coefficient and vertex.
    have hcoeff : stdSimplex.map (Fin.last (n + 1)).succAbove z k.castSucc = z k := by
      simpa only [Fin.succAbove_last_apply] using
        standardSimplex_map_succAbove_apply (Fin.last (n + 1)) z k
    rw [hcoeff, standardSimplexBarycentricLastPermutation_vertex,
      standardSimplex_map_succAbove_apply]

/-- Helper for Theorem 63.7: the singular map represented by a face of the
universal simplex is the corresponding standard face inclusion. -/
private lemma standardSimplexSingularMap_face_identity_apply (n : ℕ)
    (r : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    (standardSimplexSingularMap
      (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ r
          (standardSimplexIdentitySingularSimplex (n + 1)))).hom z =
      stdSimplex.map r.succAbove z := by
  -- Evaluate the represented face through the singular-simplex equivalence.
  unfold standardSimplexSingularMap
  rw [TopCat.hom_ofHom]
  rw [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_standardSimplexIdentitySingularSimplex]
  rfl

/-- Helper for Theorem 63.7: the final face of a last-vertex barycentric
simplex is the corresponding barycentric simplex pushed into the original face. -/
lemma standardSimplexBarycentricSingularSimplex_δ_lastPermutation (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    (TopCat.toSSet.obj Δ).δ
        (Fin.last (n + 1))
          (standardSimplexBarycentricSingularSimplex (n + 1)
            (standardSimplexBarycentricLastPermutation n r τ)) =
      (TopCat.toSSet.map
        (standardSimplexSingularMap Δ n
          ((TopCat.toSSet.obj Δ).δ r
            (standardSimplexIdentitySingularSimplex (n + 1))))).app
        (Opposite.op (SimplexCategory.mk n))
          (standardSimplexBarycentricSingularSimplex n τ) := by
  dsimp only
  apply ((TopCat.of (stdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  -- Normalize the final face and the pushforward to their continuous representatives.
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_map]
  simp only [standardSimplexBarycentricSingularSimplex, Equiv.apply_symm_apply,
    standardSimplexBarycentricContinuousMap, ContinuousMap.comp_apply]
  rw [standardSimplexSingularMap_face_identity_apply]
  exact standardSimplexBarycentricLastPermutation_map n r τ z

/-- Helper for Theorem 63.7: multiplying the last-face boundary sign by the
last-vertex permutation sign gives the usual sign of the omitted vertex. -/
lemma standardSimplexBarycentricLastPermutation_boundarySign (n : ℕ)
    (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (-1 : ℤ) ^ (n + 1) *
        ((standardSimplexBarycentricLastPermutation n r τ).sign : ℤ) =
      (-1 : ℤ) ^ r.val * (τ.sign : ℤ) := by
  rw [standardSimplexBarycentricLastPermutation_sign]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [← mul_assoc, ← pow_add]
  have hr : r.val ≤ n + 1 := Nat.le_of_lt_succ r.isLt
  have hsub : (Fin.last (n + 1) - r : ℕ) = n + 1 - r.val := by
    rfl
  have hexp : (n + 1) + (Fin.last (n + 1) - r : ℕ) =
      r.val + 2 * (Fin.last (n + 1) - r : ℕ) := by
    rw [hsub]
    omega
  rw [hexp, pow_add, pow_mul]
  norm_num

/-- Helper for Theorem 63.7: the signed sum of final barycentric faces is the
alternating sum of the subdivisions of the original codimension-one faces. -/
lemma integralStandardSimplexBarycentricLastFaces_sum (n : ℕ) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    ∑ π : Equiv.Perm (Fin (n + 2)), (π.sign : ℤ) •
      ((-1 : ℤ) ^ (n + 1) •
        (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj Δ).δ (Fin.last (n + 1))
            (standardSimplexBarycentricSingularSimplex (n + 1) π))) =
      ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        integralSingularSimplexBarycentricSubdivision Δ n
          ((TopCat.toSSet.obj Δ).δ r
            (standardSimplexIdentitySingularSimplex (n + 1))) := by
  dsimp only
  let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
  let e := fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ↦
    standardSimplexBarycentricLastPermutation n p.1 p.2
  let finalGenerator := fun π : Equiv.Perm (Fin (n + 2)) ↦
    (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      ((TopCat.toSSet.obj Δ).δ (Fin.last (n + 1))
        (standardSimplexBarycentricSingularSimplex (n + 1) π))
  let faceGenerator := fun r : Fin (n + 2) ↦
      fun τ : Equiv.Perm (Fin (n + 1)) ↦
        (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map
            (standardSimplexSingularMap Δ n
              ((TopCat.toSSet.obj Δ).δ r
                (standardSimplexIdentitySingularSimplex (n + 1))))).app
            (Opposite.op (SimplexCategory.mk n))
              (standardSimplexBarycentricSingularSimplex n τ))
  have he : Function.Bijective e :=
    standardSimplexBarycentricLastPermutation_bijective n
  have hgenerator (r : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
      finalGenerator (e (r, τ)) = faceGenerator r τ := by
    -- The final-face computation identifies the two simplex generators.
    unfold finalGenerator faceGenerator e Δ
    rw [standardSimplexBarycentricSingularSimplex_δ_lastPermutation]
  have hterm (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
      ((e p).sign : ℤ) • ((-1 : ℤ) ^ (n + 1) • finalGenerator (e p)) =
        (-1 : ℤ) ^ p.1.val • ((p.2.sign : ℤ) • faceGenerator p.1 p.2) := by
    rw [hgenerator]
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_comm ((e p).sign : ℤ)]
    exact standardSimplexBarycentricLastPermutation_boundarySign n p.1 p.2
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
        integralSingularSimplexBarycentricSubdivision Δ n
          ((TopCat.toSSet.obj Δ).δ r
            (standardSimplexIdentitySingularSimplex (n + 1))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integralSingularSimplexBarycentricSubdivision_eq_sum]

/-- Helper for Theorem 63.7: the universal barycentric subdivision chain has
boundary equal to the alternating sum of the subdivided original faces. -/
lemma integralStandardSimplexBarycentricSubdivisionChain_boundary (n : ℕ) :
    let Δ := TopCat.of (stdSimplex ℝ (Fin (n + 2)))
    integralStandardSimplexBarycentricSubdivisionChain (n + 1) ≫
        ((TopCat.toSSet.obj Δ).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
      ∑ r : Fin (n + 2), (-1 : ℤ) ^ r.val •
        integralSingularSimplexBarycentricSubdivision Δ n
          ((TopCat.toSSet.obj Δ).δ r
            (standardSimplexIdentitySingularSimplex (n + 1))) := by
  dsimp only
  unfold integralStandardSimplexBarycentricSubdivisionChain
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
                (standardSimplexBarycentricSingularSimplex (n + 1) π))) =
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.castSucc.val •
          (TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                  (standardSimplexBarycentricSingularSimplex (n + 1) π))) +
        (-1 : ℤ) ^ (Fin.last (n + 1)).val •
          (TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ (Fin.last (n + 1))
                  (standardSimplexBarycentricSingularSimplex (n + 1) π)) := by
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
                  (standardSimplexBarycentricSingularSimplex (n + 1) π))) = 0 := by
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
                    (standardSimplexBarycentricSingularSimplex (n + 1) π))) =
        ∑ π : Equiv.Perm (Fin (n + 2)), (-1 : ℤ) ^ i.castSucc.val •
          ((π.sign : ℤ) •
            (TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj
                  (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ i.castSucc
                    (standardSimplexBarycentricSingularSimplex (n + 1) π))) := by
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
                    (standardSimplexBarycentricSingularSimplex (n + 1) π)) := by
        rw [Finset.smul_sum]
      _ = 0 := by
        rw [integralStandardSimplexBarycentricInteriorFaces_sum_eq_zero, smul_zero]
  rw [hinterior, zero_add]
  simpa only [Fin.val_last] using integralStandardSimplexBarycentricLastFaces_sum n

end AlgebraicTopology
