import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Manifold ContDiff Topology

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the API
-- choice was checked against local manifold declarations and mathlib's `IsManifold` interface.

noncomputable section

/-- Helper for Example 1.32: in ambient dimension `0`, a regular level set is empty because every
continuous linear map out of `ℝ^0` is zero. -/
lemma regular_level_set_isEmpty_of_zero_dim
    (U : Set (EuclideanSpace ℝ (Fin 0))) (Φ : EuclideanSpace ℝ (Fin 0) → ℝ) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0) :
    IsEmpty ↥(U ∩ Φ ⁻¹' {c}) := by
  refine ⟨fun a ↦ ?_⟩
  rcases a.2 with ⟨haU, haLevel⟩
  have hzero : fderiv ℝ Φ a.1 = 0 := Subsingleton.elim _ _
  exact (hreg a.1 haU (by simpa using haLevel) hzero).elim

/-- Helper for Example 1.32: a nonzero linear functional on `ℝ^(k+1)` is nonzero on some standard
basis vector. -/
lemma exists_nonzero_coordinate_of_nonzero_fderiv {k : ℕ}
    (L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i : Fin (k + 1), L (EuclideanSpace.single i (1 : ℝ)) ≠ 0 := by
  by_contra hcoord
  apply hL
  apply ContinuousLinearMap.ext
  intro x
  have hzero_basis : ∀ i : Fin (k + 1), L (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    intro i
    by_contra hi
    exact hcoord ⟨i, hi⟩
  -- Expand `x` in the standard basis and use the vanishing of each basis-vector image.
  calc
    L x = L (∑ i, x i • EuclideanSpace.single i (1 : ℝ)) := by
      congr 1
      simpa [EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin (k + 1)) ℝ).sum_repr x).symm
    _ = ∑ i, x i * L (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i) := by
      simp [smul_eq_mul]
    _ = 0 := by
      simp [EuclideanSpace.basisFun_apply, hzero_basis]

/-- Helper for Example 1.32: a nonzero continuous linear self-map of `ℝ` is invertible. -/
lemma real_line_map_isInvertible_of_ne_zero (L : ℝ →L[ℝ] ℝ) (hL : L ≠ 0) :
    L.IsInvertible := by
  have hL1 : L 1 ≠ 0 := by
    intro h1
    apply hL
    apply ContinuousLinearMap.ext
    intro x
    -- Every continuous linear endomorphism of `ℝ` is multiplication by its value at `1`.
    calc
      L x = L (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = x • L 1 := by rw [map_smul]
      _ = x * L 1 := by simp [smul_eq_mul]
      _ = 0 := by simp [h1]
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L 1) hL1), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  -- The automorphism corresponding to the unit `L 1` is exactly the map `L`.
  change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L 1)) x = L x
  calc
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L 1)) x = x • L 1 := by
      simp [ContinuousLinearMap.smulRight_apply]
    _ = L (x • (1 : ℝ)) := by rw [map_smul]
    _ = L x := by rw [smul_eq_mul, mul_one]

/-- Helper for Example 1.32: splitting off the `i`-th coordinate identifies `ℝ^(k+1)` with
`ℝ^k × ℝ`. -/
def split_at_coordinate {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ EuclideanSpace ℝ (Fin k) × ℝ where
  toFun x :=
    ((EuclideanSpace.equiv (Fin k) ℝ).symm fun j ↦ x (i.succAbove j), x i)
  invFun y :=
    (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm
      (i.insertNth y.2 ((EuclideanSpace.equiv (Fin k) ℝ) y.1))
  left_inv x := by
    -- Check the distinguished coordinate and the complementary coordinates separately.
    apply (EuclideanSpace.equiv (Fin (k + 1)) ℝ).injective
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      simp
  right_inv y := by
    -- The inverse reinserts the omitted coordinate and then drops it again.
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
      ext j
      simp
    · simp

/-- Helper for Example 1.32: after splitting off coordinate `i`, the second component is exactly
that coordinate. -/
lemma split_at_coordinate_snd_apply {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    (split_at_coordinate i x).2 = x i := by
  rfl

/-- Helper for Example 1.32: after splitting off coordinate `i`, the first component records the
remaining coordinates indexed by `succAbove i`. -/
lemma split_at_coordinate_fst_apply {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin k) :
    ((split_at_coordinate i x).1 : Fin k → ℝ) j = x (i.succAbove j) := by
  rfl

/-- Helper for Example 1.32: the inverse of the coordinate split restores the distinguished
coordinate in slot `i`. -/
lemma split_at_coordinate_symm_apply_self {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) :
    (split_at_coordinate i).symm y i = y.2 := by
  simp [split_at_coordinate]

/-- Helper for Example 1.32: the inverse of the coordinate split restores the complementary
coordinates in the `succAbove i` slots. -/
lemma split_at_coordinate_symm_apply_succAbove {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) (j : Fin k) :
    (split_at_coordinate i).symm y (i.succAbove j) = y.1 j := by
  simp [split_at_coordinate]

/-- Helper for Example 1.32: the coordinate split is continuous, so open neighborhoods can be
transported from the ambient Euclidean space to split coordinates. -/
lemma split_at_coordinate_continuous {k : ℕ} (i : Fin (k + 1)) :
    Continuous (split_at_coordinate i) := by
  let e := (EuclideanSpace.equiv (Fin (k + 1)) ℝ).toHomeomorph
  have hfun :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          (EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) :=
    e.continuous_toFun
  have hcoords :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          fun j : Fin k ↦ ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) (i.succAbove j)) := by
    -- First forget the `i`-th coordinate at the function-space level.
    exact continuous_pi fun j ↦ (continuous_apply (i.succAbove j)).comp hfun
  have hfst :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          (EuclideanSpace.equiv (Fin k) ℝ).symm
            (fun j : Fin k ↦ ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) (i.succAbove j))) := by
    -- Then transport the remaining coordinates back to `EuclideanSpace ℝ (Fin k)`.
    exact ((EuclideanSpace.equiv (Fin k) ℝ).symm.toHomeomorph.continuous_toFun).comp hcoords
  have hsnd :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin (k + 1)) ↦
          ((EuclideanSpace.equiv (Fin (k + 1)) ℝ) x) i) := by
    -- The distinguished coordinate is just one scalar projection.
    exact (continuous_apply i).comp hfun
  -- Reassemble the dropped coordinates and the distinguished coordinate into the product model.
  simpa [split_at_coordinate] using Continuous.prodMk hfst hsnd

/-- Helper for Example 1.32: the inverse coordinate split is continuous, so neighborhoods and
charts can be pulled back from split coordinates to the ambient level-set subtype. -/
lemma split_at_coordinate_symm_continuous {k : ℕ} (i : Fin (k + 1)) :
    Continuous (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm y) := by
  have hremove :
      Continuous
        (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦
          ((EuclideanSpace.equiv (Fin k) ℝ) y.1)) := by
    -- View the split-space first component as an honest `Fin k → ℝ` tuple.
    exact ((EuclideanSpace.equiv (Fin k) ℝ).toHomeomorph.continuous_toFun).comp continuous_fst
  have hinsert :
      Continuous
        (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦
          Fin.insertNth (α := fun _ : Fin (k + 1) ↦ ℝ) i y.2
            (((EuclideanSpace.equiv (Fin k) ℝ) y.1))) := by
    -- Reinsert the distinguished coordinate and keep the complementary coordinates unchanged.
    refine continuous_pi fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using continuous_snd
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      simpa using (continuous_apply j').comp hremove
  -- Finally transport the reinserted tuple back to Euclidean space.
  simpa [split_at_coordinate] using
    ((EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.toHomeomorph.continuous_toFun).comp hinsert

/-- Helper for Example 1.32: the coordinate split is a linear equivalence, so the fixed-coordinate
chart change can be handled by continuous linear algebra rather than repeated tuple unfolding. -/
noncomputable def split_at_coordinate_continuousLinearEquiv {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
  let e : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) × ℝ :=
    { toFun := split_at_coordinate i
      invFun := (split_at_coordinate i).symm
      left_inv := (split_at_coordinate i).left_inv
      right_inv := (split_at_coordinate i).right_inv
      map_add' := by
        intro x y
        -- The split map is linear coordinatewise on the retained coordinates and on the
        -- distinguished scalar coordinate.
        apply Prod.ext
        · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
          ext j
          simp [split_at_coordinate_fst_apply, add_comm, add_left_comm, add_assoc]
        · simp [split_at_coordinate_snd_apply]
      map_smul' := by
        intro t x
        -- Scalar multiplication is likewise checked separately on the retained coordinates and on
        -- the distinguished scalar coordinate.
        apply Prod.ext
        · apply (EuclideanSpace.equiv (Fin k) ℝ).injective
          ext j
          simp [split_at_coordinate_fst_apply]
        · simp [split_at_coordinate_snd_apply] }
  e.toContinuousLinearEquivOfContinuous (split_at_coordinate_continuous i)

/-- Helper for Example 1.32: the inverse coordinate split is smooth, so composing with it preserves
the regularity class needed for the inverse/implicit-function argument. -/
lemma split_at_coordinate_symm_contDiff {k : ℕ} (i : Fin (k + 1)) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm y) := by
  -- Route correction: once the inverse split is packaged as a continuous linear equivalence, its
  -- smoothness is immediate and we avoid repeated unfolding through `Fin.insertNth`.
  simpa [split_at_coordinate_continuousLinearEquiv,
    LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm] using
    (split_at_coordinate_continuousLinearEquiv i).symm.contDiff

/-- Helper for Example 1.32: the forward coordinate split is smooth for the same linear-algebra
reason as its inverse. -/
lemma split_at_coordinate_contDiff {k : ℕ} (i : Fin (k + 1)) :
    ContDiff ℝ ∞ (split_at_coordinate i) := by
  -- The forward split is a continuous linear equivalence, so its smoothness is global.
  simpa [split_at_coordinate_continuousLinearEquiv,
    LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous] using
    (split_at_coordinate_continuousLinearEquiv i).contDiff

/-- Helper for Example 1.32: `split_at_coordinate` upgrades to a homeomorphism between the ambient
Euclidean space and the split model `ℝ^k × ℝ`. -/
def split_at_coordinate_homeomorph {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ₜ EuclideanSpace ℝ (Fin k) × ℝ where
  toEquiv := split_at_coordinate i
  continuous_toFun := split_at_coordinate_continuous i
  continuous_invFun := split_at_coordinate_symm_continuous i

/-- Helper for Example 1.32: the homeomorphism wrapper has the same forward formula as the
underlying coordinate split. -/
@[simp] theorem split_at_coordinate_homeomorph_apply {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    split_at_coordinate_homeomorph i x = split_at_coordinate i x :=
  rfl

/-- Helper for Example 1.32: the inverse of the homeomorphism wrapper has the same formula as the
inverse of the underlying coordinate split. -/
@[simp] theorem split_at_coordinate_homeomorph_symm_apply {k : ℕ} (i : Fin (k + 1))
    (y : EuclideanSpace ℝ (Fin k) × ℝ) :
    (split_at_coordinate_homeomorph i).symm y = (split_at_coordinate i).symm y :=
  rfl

/-- Helper for Example 1.32: an eventual graph equation near `u` can be shrunk to explicit open
source and ambient neighborhoods on which graph membership is exact and the graph parametrization
stays inside the ambient patch. -/
lemma exists_open_graph_patch_of_eventually_eq {k : ℕ}
    {u : EuclideanSpace ℝ (Fin k) × ℝ}
    {P : Set (EuclideanSpace ℝ (Fin k) × ℝ)}
    {ψ : EuclideanSpace ℝ (Fin k) → ℝ}
    (hgraph : ∀ᶠ v in 𝓝 u, v ∈ P ↔ ψ v.1 = v.2)
    (hψ : Tendsto ψ (𝓝 u.1) (𝓝 u.2)) :
    ∃ V : Set (EuclideanSpace ℝ (Fin k)),
      ∃ N : Set (EuclideanSpace ℝ (Fin k) × ℝ),
      IsOpen V ∧ IsOpen N ∧
      u.1 ∈ V ∧ u ∈ N ∧
      (∀ v ∈ N,
        v ∈ P ↔ v ∈ V.graphOn ψ) ∧
      (∀ x ∈ V, (x, ψ x) ∈ N) := by
  let Q : Set (EuclideanSpace ℝ (Fin k) × ℝ) := {v | v ∈ P ↔ ψ v.1 = v.2}
  obtain ⟨N', hN'sub, hN'open, huN'⟩ := mem_nhds_iff.mp hgraph
  let g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) × ℝ := fun x ↦ (x, ψ x)
  have hg : Tendsto g (𝓝 u.1) (𝓝 u) := by
    rw [nhds_prod_eq]
    exact Tendsto.prodMk tendsto_id hψ
  have hpreN' : g ⁻¹' N' ∈ 𝓝 u.1 := hg (hN'open.mem_nhds huN')
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_nhds_iff.mp hpreN'
  let N : Set (EuclideanSpace ℝ (Fin k) × ℝ) := N' ∩ Prod.fst ⁻¹' V
  refine ⟨V, N, hVopen, ?_, huV, ?_, ?_, ?_⟩
  · -- Intersect the equation neighborhood with the first-coordinate strip over `V`.
    exact hN'open.inter (hVopen.preimage continuous_fst)
  · -- The base point belongs to both pieces of the chosen ambient patch.
    exact ⟨huN', huV⟩
  · intro v hvN
    have hvN' : v ∈ N' := hvN.1
    have hvV : v.1 ∈ V := hvN.2
    have hEq : v ∈ P ↔ ψ v.1 = v.2 := by
      apply hN'sub
      exact hvN'
    -- On the chosen patch, the local equation is exactly membership in `V.graphOn ψ`.
    constructor
    · intro hvP
      simpa [Set.mem_graphOn] using And.intro hvV (hEq.mp hvP)
    · intro hvGraph
      have hmemGraph : v.1 ∈ V ∧ ψ v.1 = v.2 := by
        simpa [Set.mem_graphOn] using hvGraph
      exact hEq.mpr hmemGraph.2
  · intro x hxV
    -- The graph parametrization stays in the chosen source neighborhood by construction.
    exact ⟨hVsub hxV, hxV⟩

/-- Helper for Example 1.32: on a neighborhood where the level set is given by a graph equation,
membership in the level set is exactly membership in the corresponding `graphOn`. -/
lemma regular_level_set_mem_graphOn_iff_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    {y : EuclideanSpace ℝ (Fin (k + 1))} (hyN : y ∈ N) :
    y ∈ U ∩ Φ ⁻¹' {c} ↔ split_at_coordinate i y ∈ V.graphOn ψ := by
  -- Rewrite the source-level graph equation into graph-membership language.
  simpa [Set.mem_graphOn, eq_comm] using hgraph y hyN

/-- Helper for Example 1.32: a point of the local level-set patch maps to the graph under the
split coordinates. -/
lemma regular_level_set_point_mem_graph_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    {p : ↥(U ∩ Φ ⁻¹' {c})} (hpN : p.1 ∈ N) :
    split_at_coordinate i p.1 ∈ V.graphOn ψ := by
  -- Apply the graph-on reformulation at the ambient point underlying `p`.
  exact (regular_level_set_mem_graphOn_iff_of_local_graph i V N ψ hgraph hpN).1 p.2

/-- Helper for Example 1.32: if the graph parametrization stays inside the ambient neighborhood,
then it lands back in the level set. -/
lemma regular_level_set_graph_point_mem_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    {x : EuclideanSpace ℝ (Fin k)} (hxV : x ∈ V) :
    (split_at_coordinate i).symm (x, ψ x) ∈ U ∩ Φ ⁻¹' {c} := by
  -- First place the graph point in the neighborhood where the local graph equation is valid.
  have hN : (split_at_coordinate i).symm (x, ψ x) ∈ N := hparamN x hxV
  -- Then rewrite its split coordinates back to `(x, ψ x)` and use the converse direction.
  refine (regular_level_set_mem_graphOn_iff_of_local_graph i V N ψ hgraph hN).2 ?_
  simpa [Set.mem_graphOn, eq_comm]

/-- Helper for Example 1.32: any point of the graph patch pulls back along the split coordinates
to a point of the ambient level set. -/
lemma regular_level_set_graph_mem_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    {q : EuclideanSpace ℝ (Fin k) × ℝ} (hq : q ∈ V.graphOn ψ) :
    (split_at_coordinate i).symm q ∈ U ∩ Φ ⁻¹' {c} := by
  -- Rewrite the graph point in the explicit `(x, ψ x)` form used by the local graph equation.
  have hxV : q.1 ∈ V := (Set.mem_graphOn.1 hq).1
  have hqEq : q.2 = ψ q.1 := (Set.mem_graphOn.1 hq).2.symm
  have hqPair : (q.1, ψ q.1) = q := by
    ext <;> simp [hqEq]
  have hmem :
      (split_at_coordinate i).symm (q.1, ψ q.1) ∈ U ∩ Φ ⁻¹' {c} :=
    regular_level_set_graph_point_mem_of_local_graph i V N ψ hgraph hparamN hxV
  simpa [hqPair] using hmem

/-- Helper for Example 1.32: once the ambient level-set patch is identified with a graph, the
corresponding subtype patch is homeomorphic to that graph. -/
noncomputable def regular_level_set_patch_homeomorph_to_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N) :
    {p : ↥(U ∩ Φ ⁻¹' {c}) // p.1 ∈ N} ≃ₜ V.graphOn ψ where
  toEquiv :=
    { toFun := fun p ↦
        ⟨split_at_coordinate i p.1.1,
          regular_level_set_point_mem_graph_of_local_graph i V N ψ hgraph p.2⟩
      invFun := fun q ↦
        ⟨⟨(split_at_coordinate i).symm q.1,
            regular_level_set_graph_mem_of_local_graph i V N ψ hgraph hparamN q.2⟩,
          by
            -- The graph parametrization stays inside the chosen ambient patch by hypothesis.
            have hxV : q.1.1 ∈ V := (Set.mem_graphOn.1 q.2).1
            have hN : (split_at_coordinate i).symm (q.1.1, ψ q.1.1) ∈ N := hparamN q.1.1 hxV
            have hqEq : q.1.2 = ψ q.1.1 := (Set.mem_graphOn.1 q.2).2.symm
            have hqPair : (q.1.1, ψ q.1.1) = q.1 := by
              ext <;> simp [hqEq]
            simpa [hqPair] using hN⟩
      left_inv := by
        intro p
        -- The forward map records the split coordinates, and the inverse reinserts them.
        apply Subtype.ext
        apply Subtype.ext
        have hpgraph :
            split_at_coordinate i p.1.1 ∈ V.graphOn ψ :=
          regular_level_set_point_mem_graph_of_local_graph i V N ψ hgraph p.2
        have _hpEq :
            (split_at_coordinate i p.1.1).2 = ψ ((split_at_coordinate i p.1.1).1) :=
          (Set.mem_graphOn.1 hpgraph).2.symm
        dsimp
        simpa using (split_at_coordinate i).left_inv p.1.1
      right_inv := by
        intro q
        -- A graph point is unchanged after splitting and reinserting its coordinates.
        apply Subtype.ext
        change split_at_coordinate i ((split_at_coordinate i).symm q.1) = q.1
        exact (split_at_coordinate i).apply_symm_apply q.1
      }
  continuous_toFun := by
    -- The forward map is just the split-coordinate map, restricted to the subtype patch.
    exact Continuous.subtype_mk
      ((split_at_coordinate_continuous i).comp
        (continuous_subtype_val.comp continuous_subtype_val))
      (fun p ↦ regular_level_set_point_mem_graph_of_local_graph i V N ψ hgraph p.2)
  continuous_invFun := by
    -- The inverse is the ambient inverse split map, again restricted to the graph patch.
    have hToLevelSet :
        Continuous fun q : V.graphOn ψ ↦
          (⟨(split_at_coordinate i).symm q.1,
            regular_level_set_graph_mem_of_local_graph i V N ψ hgraph hparamN q.2⟩ :
              ↥(U ∩ Φ ⁻¹' {c})) :=
      Continuous.subtype_mk
        ((split_at_coordinate_symm_continuous i).comp continuous_subtype_val)
        (fun q ↦ regular_level_set_graph_mem_of_local_graph i V N ψ hgraph hparamN q.2)
    exact Continuous.subtype_mk hToLevelSet (fun q ↦ by
      -- The graph equation keeps the inverse image inside the ambient neighborhood `N`.
      have hxV : q.1.1 ∈ V := (Set.mem_graphOn.1 q.2).1
      have hN : (split_at_coordinate i).symm (q.1.1, ψ q.1.1) ∈ N := hparamN q.1.1 hxV
      have hqEq : q.1.2 = ψ q.1.1 := (Set.mem_graphOn.1 q.2).2.symm
      have hqPair : (q.1.1, ψ q.1.1) = q.1 := by
        ext <;> simp [hqEq]
      simpa [hqPair] using hN)

/-- Helper for Example 1.32: the patch-to-graph homeomorphism simply records the split
coordinates of a point in the ambient patch. -/
@[simp] theorem regular_level_set_patch_homeomorph_to_graph_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (q : {p : ↥(U ∩ Φ ⁻¹' {c}) // p.1 ∈ N}) :
    ((regular_level_set_patch_homeomorph_to_graph i V N ψ hgraph hparamN q :
      V.graphOn ψ) : EuclideanSpace ℝ (Fin k) × ℝ) = split_at_coordinate i q.1.1 := by
  rfl

/-- Helper for Example 1.32: the inverse patch-to-graph homeomorphism reinserts the distinguished
coordinate by the explicit graph formula. -/
@[simp] theorem regular_level_set_patch_homeomorph_to_graph_symm_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (q : V.graphOn ψ) :
    (((regular_level_set_patch_homeomorph_to_graph i V N ψ hgraph hparamN).symm q :
      {p : ↥(U ∩ Φ ⁻¹' {c}) // p.1 ∈ N}).1 : ↥(U ∩ Φ ⁻¹' {c})).1 =
      (split_at_coordinate i).symm q.1 := by
  rfl

/-- Helper for Example 1.32: the canonical subtype patch cut out by an ambient set `T` is
homeomorphic to the corresponding ambient intersection `S ∩ T`. -/
private noncomputable def subtype_patch_intersection_homeomorph
    {X : Type*} [TopologicalSpace X] (S T : Set X) :
    {y : S | y.1 ∈ T} ≃ₜ (S ∩ T : Set X) where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter (fun x : X ↦ x ∈ S) (fun x : X ↦ x ∈ T)
  -- The forward map just forgets the nested subtype structure and remembers the intersection data.
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun y ↦ by exact ⟨y.1.2, y.2⟩)
  -- The inverse repackages an intersection point as a point of `S` lying in `T`.
  continuous_invFun := by
    have hToS : Continuous fun y : (S ∩ T : Set X) ↦ (⟨y.1, y.2.1⟩ : S) :=
      Continuous.subtype_mk continuous_subtype_val (fun y ↦ y.2.1)
    exact Continuous.subtype_mk hToS (fun y ↦ y.2.2)

/-- Helper for Example 1.32: inserting a scalar into the distinguished coordinate defines the
ambient coordinate-line direction used in the implicit-function argument. -/
def coordinate_insertion {k : ℕ} (i : Fin (k + 1)) :
    ℝ →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))

/-- Helper for Example 1.32: the coordinate-insertion map really is the standard basis-vector
inclusion `t ↦ single i t`. -/
lemma coordinate_insertion_apply {k : ℕ} (i : Fin (k + 1)) (t : ℝ) :
    coordinate_insertion i t = EuclideanSpace.single i t := by
  -- Compare coordinates: only the distinguished `i`-th coordinate survives.
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [coordinate_insertion, ContinuousLinearMap.smulRight_apply]
  · simp [coordinate_insertion, ContinuousLinearMap.smulRight_apply, hj]

/-- Helper for Example 1.32: composing the inverse split map with the right inclusion of
`ℝ^k × ℝ` recovers the distinguished ambient coordinate-line direction. -/
lemma split_at_coordinate_symm_comp_inr_eq_coordinate_insertion {k : ℕ} (i : Fin (k + 1)) :
    (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ =
        coordinate_insertion i := by
  -- The right inclusion fixes the retained coordinates at `0` and varies only the distinguished
  -- scalar coordinate, exactly matching the coordinate-insertion map.
  apply ContinuousLinearMap.ext
  intro t
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      split_at_coordinate_continuousLinearEquiv, coordinate_insertion_apply,
      split_at_coordinate_symm_apply_self]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      split_at_coordinate_continuousLinearEquiv, coordinate_insertion_apply,
      split_at_coordinate_symm_apply_succAbove, EuclideanSpace.single_apply]

/-- Helper for Example 1.32: varying only the distinguished split coordinate traces an affine line
in the ambient Euclidean space. -/
lemma split_at_coordinate_symm_line_eq {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin k)) :
    ∃ base : EuclideanSpace ℝ (Fin (k + 1)),
      (fun t : ℝ ↦ (split_at_coordinate i).symm (x, t)) =
        fun t : ℝ ↦ base + coordinate_insertion i t := by
  refine ⟨(split_at_coordinate i).symm (x, 0), ?_⟩
  -- Away from coordinate `i` the line is constant, while the `i`-th coordinate varies by `t`.
  funext t
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [coordinate_insertion_apply, split_at_coordinate_symm_apply_self]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    simp [coordinate_insertion_apply, split_at_coordinate_symm_apply_succAbove,
      EuclideanSpace.single_apply]

/-- Helper for Example 1.32: the affine line obtained by varying one split coordinate has
derivative equal to the corresponding coordinate-insertion map. -/
lemma split_at_coordinate_symm_line_hasFDerivAt {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin k)) (t₀ : ℝ) :
    HasFDerivAt (fun t : ℝ ↦ (split_at_coordinate i).symm (x, t))
      (coordinate_insertion i) t₀ := by
  have hpair :
      HasFDerivAt (fun t : ℝ ↦ (x, t))
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ) t₀ := by
    -- Only the second component varies along the coordinate line.
    simpa using hasFDerivAt_prodMk_right x t₀
  have hsymm :
      HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm y)
        (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap (x, t₀) := by
    -- The inverse split map is linear, so its derivative is itself.
    simpa [split_at_coordinate_continuousLinearEquiv,
      LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm] using
      ((split_at_coordinate_continuousLinearEquiv i).symm.hasFDerivAt :
        HasFDerivAt
          (split_at_coordinate_continuousLinearEquiv i).symm
          (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap (x, t₀))
  -- Compose the inverse split with the right-coordinate line and rewrite the linear derivative.
  simpa [Function.comp, split_at_coordinate_symm_comp_inr_eq_coordinate_insertion] using
    hsymm.comp t₀ hpair

/-- Helper for Example 1.32: restricting an ambient map to the affine line that varies only the
distinguished split coordinate differentiates by composing with `coordinate_insertion i`. -/
lemma hasFDerivAt_comp_split_at_coordinate_symm_line {k : ℕ}
    {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {Φ' : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ}
    (i : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin k)) (t₀ : ℝ)
    (hΦ : HasFDerivAt Φ Φ' ((split_at_coordinate i).symm (x, t₀))) :
    HasFDerivAt (fun t : ℝ ↦ Φ ((split_at_coordinate i).symm (x, t)))
      (Φ' ∘L coordinate_insertion i) t₀ := by
  -- The source route needs the `∂/∂xᶦ` derivative.  Differentiate `Φ` after restricting it to the
  -- affine line that changes only the `i`-th split coordinate.
  exact hΦ.comp t₀ (split_at_coordinate_symm_line_hasFDerivAt i x t₀)

/-- Helper for Example 1.32: the derivative of the split-coordinate affine-line restriction is the
ambient derivative composed with the distinguished coordinate insertion. -/
lemma fderiv_comp_split_at_coordinate_symm_line {k : ℕ}
    {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {Φ' : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ}
    (i : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin k)) (t₀ : ℝ)
    (hΦ : HasFDerivAt Φ Φ' ((split_at_coordinate i).symm (x, t₀))) :
    fderiv ℝ (fun t : ℝ ↦ Φ ((split_at_coordinate i).symm (x, t))) t₀ =
      Φ' ∘L coordinate_insertion i := by
  -- Once the derivative along the affine line is identified, `fderiv` recovers exactly that map.
  simpa using (hasFDerivAt_comp_split_at_coordinate_symm_line i x t₀ hΦ).fderiv

/-- Helper for Example 1.32: the ambient open neighborhood `N` determines the corresponding open
patch of the level-set subtype. -/
def regular_level_set_subtype_patch {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (c : ℝ)
    (N : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hN : IsOpen N) :
    TopologicalSpace.Opens ↥(U ∩ Φ ⁻¹' {c}) where
  carrier := {p : ↥(U ∩ Φ ⁻¹' {c}) | p.1 ∈ N}
  is_open' := hN.preimage continuous_subtype_val

/-- Helper for Example 1.32: the graph coordinates from Example 1.3 upgrade to an
`OpenPartialHomeomorph` defined on all of the graph of a continuous map. -/
noncomputable def graph_coordinate_chart_of_continuous
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set X) (hV : IsOpen V) (ψ : X → Y)
    (hψ : ContinuousOn ψ V) (hVne : Nonempty V) :
    OpenPartialHomeomorph (V.graphOn ψ) X :=
  let _ : Nonempty V := hVne
  (graph_coordinates V ψ hψ).toOpenPartialHomeomorph ≫ₕ
    show OpenPartialHomeomorph V X from
      @TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe X _ ⟨V, hV⟩ hVne

/-- Helper for Example 1.32: the continuous graph coordinate chart is defined on all of the graph
patch. -/
theorem graph_coordinate_chart_of_continuous_source
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set X) (hV : IsOpen V) (ψ : X → Y)
    (hψ : ContinuousOn ψ V) (hVne : Nonempty V) :
    (graph_coordinate_chart_of_continuous V hV ψ hψ hVne).source = (Set.univ : Set (V.graphOn ψ)) := by
  -- Both factors in the chart construction are defined on all of their domains.
  let _ : Nonempty V := hVne
  change Set.univ ∩ Set.univ = (Set.univ : Set (V.graphOn ψ))
  simp [graph_coordinate_chart_of_continuous, Homeomorph.toOpenPartialHomeomorph_source]

/-- Helper for Example 1.32: the graph-coordinate chart lands exactly in the base open set `V`. -/
theorem graph_coordinate_chart_of_continuous_target
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set X) (hV : IsOpen V) (ψ : X → Y)
    (hψ : ContinuousOn ψ V) (hVne : Nonempty V) :
    (graph_coordinate_chart_of_continuous V hV ψ hψ hVne).target = V := by
  let _ : Nonempty V := hVne
  -- The graph homeomorphism is global on the graph and the final subtype inclusion targets `V`.
  rw [graph_coordinate_chart_of_continuous, OpenPartialHomeomorph.trans_target]
  ext x
  simp [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

/-- Helper for Example 1.32: the continuous graph chart is still projection to the first
coordinate after forgetting the final subtype wrapper. -/
theorem graph_coordinate_chart_of_continuous_apply
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set X) (hV : IsOpen V) (ψ : X → Y)
    (hψ : ContinuousOn ψ V) (hVne : Nonempty V) (p : V.graphOn ψ) :
    graph_coordinate_chart_of_continuous V hV ψ hψ hVne p = p.1.1 := by
  -- The extra subtype inclusion just forgets the proof that the first coordinate lies in `V`.
  rw [graph_coordinate_chart_of_continuous, OpenPartialHomeomorph.trans_apply]
  simpa using graph_coordinates_apply V ψ hψ p

/-- Helper for Example 1.32: the inverse continuous graph chart sends `x ∈ V` to `(x, ψ x)`. -/
theorem graph_coordinate_chart_of_continuous_symm_apply
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set X) (hV : IsOpen V) (ψ : X → Y)
    (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    {x : X} (hx : x ∈ V) :
    (((graph_coordinate_chart_of_continuous V hV ψ hψ hVne).symm x : V.graphOn ψ) :
      X × Y) = (x, ψ x) := by
  let q : V.graphOn ψ := (graph_coordinate_chart_of_continuous V hV ψ hψ hVne).symm x
  have hxTarget : x ∈ (graph_coordinate_chart_of_continuous V hV ψ hψ hVne).target := by
    simpa [graph_coordinate_chart_of_continuous_target V hV ψ hψ hVne] using hx
  have hchart :
      graph_coordinate_chart_of_continuous V hV ψ hψ hVne q = x := by
    simpa [q] using
      (graph_coordinate_chart_of_continuous V hV ψ hψ hVne).right_inv hxTarget
  have hfst : q.1.1 = x := by
    -- The graph chart forgets everything except the retained base point.
    simpa [q] using
      (graph_coordinate_chart_of_continuous_apply V hV ψ hψ hVne q).trans hchart
  have hsnd : q.1.2 = ψ x := by
    -- The second coordinate is forced by the graph equation once the first coordinate is known.
    simpa [hfst] using (Set.mem_graphOn.1 q.2).2.symm
  ext <;> simp [q, hfst, hsnd]

/-- Helper for Example 1.32: once the level-set patch is written as a graph over an open
`V ⊆ ℝ^k`, the corresponding subtype patch carries a canonical chart to `ℝ^k`. -/
noncomputable def regular_level_set_patch_chart_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N) :
    OpenPartialHomeomorph (regular_level_set_subtype_patch U Φ c N hN)
      (EuclideanSpace ℝ (Fin k)) :=
  (regular_level_set_patch_homeomorph_to_graph i V N ψ hgraph hparamN).toOpenPartialHomeomorph ≫ₕ
    graph_coordinate_chart_of_continuous V hV ψ hψ hVne

/-- Helper for Example 1.32: the patch chart induced from the local graph picture is defined on
all of the chosen subtype patch. -/
theorem regular_level_set_patch_chart_of_local_graph_source {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N) :
    (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN).source =
      (Set.univ : Set ↥(regular_level_set_subtype_patch U Φ c N hN)) := by
  -- The subtype-to-graph homeomorphism and the graph-coordinate chart are both global on the
  -- chosen patch, so their composition has full source as well.
  rw [regular_level_set_patch_chart_of_local_graph, OpenPartialHomeomorph.trans_source]
  rw [graph_coordinate_chart_of_continuous_source V hV ψ hψ hVne]
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    exact ⟨trivial, trivial⟩

/-- Helper for Example 1.32: the patch chart built from a graph model lands exactly in the base
open set `V`. -/
theorem regular_level_set_patch_chart_of_local_graph_target {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N) :
    (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN).target = V := by
  -- The subtype-to-graph homeomorphism contributes no target restriction beyond the graph chart.
  rw [regular_level_set_patch_chart_of_local_graph, OpenPartialHomeomorph.trans_target,
    graph_coordinate_chart_of_continuous_target V hV ψ hψ hVne]
  ext x
  simp

/-- Helper for Example 1.32: the patch chart associated with a local graph still reads off the
retained split coordinates. -/
theorem regular_level_set_patch_chart_of_local_graph_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (q : ↥(regular_level_set_subtype_patch U Φ c N hN)) :
    regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN q =
      (split_at_coordinate i q.1.1).1 := by
  -- After identifying the patch with the graph, the chart is just `graph_coordinate_chart`.
  rw [regular_level_set_patch_chart_of_local_graph, OpenPartialHomeomorph.trans_apply]
  simpa using graph_coordinate_chart_of_continuous_apply V hV ψ hψ hVne
    ((regular_level_set_patch_homeomorph_to_graph i V N ψ hgraph hparamN) q)

/-- Helper for Example 1.32: the inverse patch chart reinserts the fixed branch value as the
distinguished split coordinate. -/
theorem regular_level_set_patch_chart_of_local_graph_symm_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (i : Fin (k + 1)) (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    {x : EuclideanSpace ℝ (Fin k)}
    (hx :
      x ∈ (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN).target) :
    ((regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN).symm x :
      ↥(regular_level_set_subtype_patch U Φ c N hN)).1.1 =
      (split_at_coordinate i).symm (x, ψ x) := by
  let q : ↥(regular_level_set_subtype_patch U Φ c N hN) :=
    (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN).symm x
  have hxTarget :
      x ∈
        (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph
          hparamN).target := hx
  have hchart :
      regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN q = x := by
    simpa [q] using
      (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph
        hparamN).right_inv hxTarget
  have hfst :
      (split_at_coordinate i q.1.1).1 = x := by
    -- The patch chart still reads off the retained split coordinates.
    simpa [q] using
      (regular_level_set_patch_chart_of_local_graph_apply i V N ψ hN hV hψ hVne hgraph
        hparamN q).trans hchart
  have hsplit :
      (split_at_coordinate i q.1.1).1 ∈ V ∧
        (split_at_coordinate i q.1.1).2 = ψ ((split_at_coordinate i q.1.1).1) :=
    (hgraph q.1.1 q.2).1 q.1.2
  have hsnd :
      (split_at_coordinate i q.1.1).2 = ψ x := by
    -- The level-set condition identifies the distinguished split coordinate with `ψ x`.
    simpa [hfst] using hsplit.2
  have hfst' :
      (split_at_coordinate i q.1.1).1 =
        ((split_at_coordinate i) ((split_at_coordinate i).symm (x, ψ x))).1 := by
    simpa using hfst
  have hsnd' :
      (split_at_coordinate i q.1.1).2 =
        ((split_at_coordinate i) ((split_at_coordinate i).symm (x, ψ x))).2 := by
    simpa using hsnd
  -- The split map is injective, so matching both split coordinates determines the ambient point.
  apply (split_at_coordinate i).injective
  exact Prod.ext hfst' hsnd'

/-- Helper for Example 1.32: a local graph patch determines an explicit chart on the whole level
set subtype by first restricting to the ambient patch and then applying graph coordinates. -/
noncomputable def regular_level_set_local_chart_of_local_graph {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (p : ↥(U ∩ Φ ⁻¹' {c})) (i : Fin (k + 1))
    (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (hpN : p.1 ∈ N) :
    OpenPartialHomeomorph ↥(U ∩ Φ ⁻¹' {c}) (EuclideanSpace ℝ (Fin k)) :=
  let P : TopologicalSpace.Opens ↥(U ∩ Φ ⁻¹' {c}) := regular_level_set_subtype_patch U Φ c N hN
  ((P.openPartialHomeomorphSubtypeCoe ⟨p, hpN⟩).symm).trans
    (regular_level_set_patch_chart_of_local_graph i V N ψ hN hV hψ hVne hgraph hparamN)

/-- Helper for Example 1.32: the explicit local chart coming from a graph patch is defined exactly
at the points whose ambient representatives lie in the chosen neighborhood `N`. -/
theorem regular_level_set_local_chart_of_local_graph_source {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (p : ↥(U ∩ Φ ⁻¹' {c})) (i : Fin (k + 1))
    (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (hpN : p.1 ∈ N) :
    (regular_level_set_local_chart_of_local_graph p i V N ψ hN hV hψ hVne hgraph hparamN hpN).source =
      {q : ↥(U ∩ Φ ⁻¹' {c}) | q.1 ∈ N} := by
  let P : TopologicalSpace.Opens ↥(U ∩ Φ ⁻¹' {c}) := regular_level_set_subtype_patch U Φ c N hN
  -- The graph chart is global on the patch, so the only source condition is membership in `N`.
  ext q
  simp [regular_level_set_local_chart_of_local_graph, P, regular_level_set_subtype_patch,
    OpenPartialHomeomorph.trans_source,
    regular_level_set_patch_chart_of_local_graph_source]

/-- Helper for Example 1.32: the explicit local chart obtained from a graph patch has target `V`. -/
theorem regular_level_set_local_chart_of_local_graph_target {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} (p : ↥(U ∩ Φ ⁻¹' {c})) (i : Fin (k + 1))
    (V : Set (EuclideanSpace ℝ (Fin k)))
    (N : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : IsOpen N) (hV : IsOpen V) (hψ : ContinuousOn ψ V) (hVne : Nonempty V)
    (hgraph : ∀ y ∈ N,
      y ∈ U ∩ Φ ⁻¹' {c} ↔
        (split_at_coordinate i y).1 ∈ V ∧
          (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1))
    (hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N)
    (hpN : p.1 ∈ N) :
    (regular_level_set_local_chart_of_local_graph p i V N ψ hN hV hψ hVne hgraph hparamN hpN).target = V := by
  let P : TopologicalSpace.Opens ↥(U ∩ Φ ⁻¹' {c}) := regular_level_set_subtype_patch U Φ c N hN
  -- The initial restriction-to-patch map has full target, so the target is inherited from the
  -- underlying patch chart.
  rw [regular_level_set_local_chart_of_local_graph, OpenPartialHomeomorph.trans_target,
    regular_level_set_patch_chart_of_local_graph_target i V N ψ hN hV hψ hVne hgraph hparamN]
  ext x
  simp [P]

/-- Helper for Example 1.32: on an open set where `Φ` is `C^1`, the chosen coordinate derivative
`y ↦ DΦ(y)(eᵢ)` varies continuously. -/
lemma regular_level_set_coordinate_derivative_continuousOn {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U)
    (i : Fin (k + 1)) :
    ContinuousOn (fun y ↦ (fderiv ℝ Φ y) (EuclideanSpace.single i (1 : ℝ))) U := by
  -- First use `C^1` regularity to make the bundled derivative continuous, then evaluate it at the
  -- fixed basis vector selecting the `i`-th coordinate derivative.
  simpa using
    (hΦ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

/-- Helper for Example 1.32: if one coordinate derivative is nonzero at `p`, then after shrinking
to a small open neighborhood inside `U` the same coordinate derivative stays nonzero everywhere on
that neighborhood. -/
lemma regular_level_set_exists_open_nonzero_coordinate_derivative {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U)
    (i : Fin (k + 1)) {p : EuclideanSpace ℝ (Fin (k + 1))} (hpU : p ∈ U)
    (hpi : (fderiv ℝ Φ p) (EuclideanSpace.single i (1 : ℝ)) ≠ 0) :
    ∃ N : Set (EuclideanSpace ℝ (Fin (k + 1))),
      IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧
      ∀ y ∈ N, (fderiv ℝ Φ y) (EuclideanSpace.single i (1 : ℝ)) ≠ 0 := by
  let g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ :=
    fun y ↦ (fderiv ℝ Φ y) (EuclideanSpace.single i (1 : ℝ))
  have hg : ContinuousOn g U := regular_level_set_coordinate_derivative_continuousOn U hU Φ hΦ i
  have hpre : g ⁻¹' ({0} : Set ℝ)ᶜ ∈ 𝓝 p := by
    -- Continuity at `p` lets us pull back the open set of nonzero scalars.
    have hne : ({0} : Set ℝ)ᶜ ∈ 𝓝 (g p) :=
      IsOpen.mem_nhds isClosed_singleton.isOpen_compl hpi
    exact ((hg p hpU).continuousAt (hU.mem_nhds hpU)).preimage_mem_nhds hne
  obtain ⟨N', hN'sub, hN'open, hpN'⟩ := mem_nhds_iff.mp hpre
  refine ⟨N' ∩ U, hN'open.inter hU, ⟨hpN', hpU⟩, Set.inter_subset_right, ?_⟩
  intro y hyN
  -- Every point of the shrunken neighborhood stays inside the pulled-back nonzero set.
  show g y ≠ 0
  exact hN'sub hyN.1

/-- Helper for Example 1.32: at each regular point of the level set, one coordinate derivative can
be fixed on a whole open ambient patch, matching Lee's fixed-coordinate implicit-function route. -/
lemma regular_level_set_exists_local_nonzero_coordinate {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0)
    (p : ↥(U ∩ Φ ⁻¹' {c})) :
    ∃ i : Fin (k + 1), ∃ N : Set (EuclideanSpace ℝ (Fin (k + 1))),
      IsOpen N ∧ p.1 ∈ N ∧ N ⊆ U ∧
      ∀ y ∈ N, (fderiv ℝ Φ y) (EuclideanSpace.single i (1 : ℝ)) ≠ 0 := by
  have hfp : fderiv ℝ Φ p.1 ≠ 0 := hreg p.1 p.2.1 (by simpa using p.2.2)
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate_of_nonzero_fderiv (fderiv ℝ Φ p.1) hfp
  obtain ⟨N, hN, hpN, hNU, hderivN⟩ :=
    regular_level_set_exists_open_nonzero_coordinate_derivative U hU Φ hΦ i p.2.1 hi
  -- This packages the fixed-coordinate nonvanishing invariant needed before invoking the IFT.
  exact ⟨i, N, hN, hpN, hNU, hderivN⟩

/-- Helper for Example 1.32: after splitting off the `i`-th coordinate, the product-domain
right derivative required by the implicit-function theorem is exactly the chosen `i`-th partial
derivative, hence invertible whenever that coordinate derivative is nonzero. -/
lemma regular_level_set_split_pullback_right_fderiv_eq {k : ℕ}
    {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (i : Fin (k + 1)) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hΦy : ContDiffAt ℝ 1 Φ y) :
    fderiv ℝ
        (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
        (split_at_coordinate i y) ∘L
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ =
        fderiv ℝ Φ y ∘L coordinate_insertion i := by
  have hcomp :
      HasFDerivAt
        (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
        (fderiv ℝ Φ y ∘L (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap)
        (split_at_coordinate i y) := by
    have hsymm_apply :
        (split_at_coordinate_continuousLinearEquiv i).symm (split_at_coordinate i y) = y := by
      simpa [split_at_coordinate_continuousLinearEquiv] using (split_at_coordinate i).left_inv y
    have hΦsplit :
        HasFDerivAt Φ (fderiv ℝ Φ y)
          ((split_at_coordinate_continuousLinearEquiv i).symm (split_at_coordinate i y)) := by
      simpa [hsymm_apply] using (hΦy.differentiableAt one_ne_zero).hasFDerivAt
    -- Differentiate `Φ` after transporting product coordinates back to the ambient space by the
    -- inverse split linear equivalence.
    simpa [hsymm_apply] using
      (hΦsplit.comp (split_at_coordinate i y)
        ((split_at_coordinate_continuousLinearEquiv i).symm.hasFDerivAt :
          HasFDerivAt
            (split_at_coordinate_continuousLinearEquiv i).symm
            (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap
            (split_at_coordinate i y)))
  calc
    fderiv ℝ
        (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
        (split_at_coordinate i y) ∘L
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ
      =
        (fderiv ℝ Φ y ∘L (split_at_coordinate_continuousLinearEquiv i).symm.toContinuousLinearMap) ∘L
          ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ := by
            rw [hcomp.fderiv]
    _ = fderiv ℝ Φ y ∘L coordinate_insertion i := by
      rw [ContinuousLinearMap.comp_assoc, split_at_coordinate_symm_comp_inr_eq_coordinate_insertion]

/-- Helper for Example 1.32: after splitting off the `i`-th coordinate, the product-domain
right derivative required by the implicit-function theorem is exactly the chosen `i`-th partial
derivative, hence invertible whenever that coordinate derivative is nonzero. -/
lemma regular_level_set_split_pullback_right_derivative_isInvertible {k : ℕ}
    {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (i : Fin (k + 1)) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hΦy : ContDiffAt ℝ 1 Φ y)
    (hi : (fderiv ℝ Φ y) (EuclideanSpace.single i (1 : ℝ)) ≠ 0) :
    (fderiv ℝ
        (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
        (split_at_coordinate i y) ∘L
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible := by
  have hrewrite := regular_level_set_split_pullback_right_fderiv_eq i hΦy
  have hnonzero :
      fderiv ℝ Φ y ∘L coordinate_insertion i ≠ 0 := by
    -- A continuous linear map `ℝ →L[ℝ] ℝ` is nonzero as soon as its value at `1` is nonzero.
    intro hzero
    apply hi
    have hval :
        (fderiv ℝ Φ y ∘L coordinate_insertion i) 1 = 0 := by
      exact congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hzero
    simpa [coordinate_insertion_apply] using hval
  -- Rewrite the product-domain right derivative to the ambient `i`-th coordinate derivative.
  rw [hrewrite]
  exact real_line_map_isInvertible_of_ne_zero _ hnonzero

/-- Helper for Example 1.32: if the derivative of `F` in the distinguished scalar direction is
invertible at `q`, then the derivative of `v ↦ (F v, v.1)` is a continuous linear equivalence. -/
noncomputable def prod_fst_fderiv_equiv_of_right_invertible {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) × ℝ → ℝ)
    (q : EuclideanSpace ℝ (Fin k) × ℝ)
    (hq :
      (fderiv ℝ F q ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible) :
    (EuclideanSpace ℝ (Fin k) × ℝ) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin k) :=
  ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl
    (fderiv ℝ F q) (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) ℝ)
    (by
      have :
          (fderiv ℝ F q ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).range ≤
            (fderiv ℝ F q).range := LinearMap.range_comp_le_range ..
      rwa [LinearMap.range_eq_top.mpr hq.surjective, top_le_iff] at this)
    Submodule.range_fst
    (by
      constructor
      · rw [LinearMap.disjoint_ker]
        intro (_, y) hy rfl
        simpa using (injective_iff_map_eq_zero _).mp hq.injective y hy
      · rw [Submodule.codisjoint_iff_exists_add_eq]
        intro v
        have ⟨y, hy⟩ := hq.surjective ((fderiv ℝ F q) v)
        use v - (0, y), (0, y)
        aesop)

/-- Helper for Example 1.32: with the same invertibility hypothesis, the explicit map
`v ↦ (F v, v.1)` differentiates to the packaged continuous linear equivalence above. -/
lemma hasFDerivAt_prod_fst_of_right_invertible {k : ℕ}
    {F : EuclideanSpace ℝ (Fin k) × ℝ → ℝ}
    {q : EuclideanSpace ℝ (Fin k) × ℝ}
    (hFq : ContDiffAt ℝ ∞ F q)
    (hq :
      (fderiv ℝ F q ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible) :
    HasFDerivAt (fun v ↦ (F v, v.1))
      ((prod_fst_fderiv_equiv_of_right_invertible F q hq : _ →L[ℝ] _)) q := by
  have hFderiv : HasFDerivAt F (fderiv ℝ F q) q :=
    ((hFq.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).differentiableAt one_ne_zero).hasFDerivAt
  -- Pair the derivative of `F` with the fixed first projection and rewrite it as the chosen
  -- continuous linear equivalence.
  simpa [prod_fst_fderiv_equiv_of_right_invertible] using hFderiv.prodMk hasFDerivAt_fst

/-- Helper for Example 1.32: the implicit-function step should produce an explicit local graph
description of the level set near `p`. -/
lemma regular_level_set_exists_local_graph_data {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0)
    (p : ↥(U ∩ Φ ⁻¹' {c})) :
    ∃ i : Fin (k + 1),
      ∃ V : Set (EuclideanSpace ℝ (Fin k)),
      ∃ N : Set (EuclideanSpace ℝ (Fin (k + 1))),
      ∃ ψ : EuclideanSpace ℝ (Fin k) → ℝ,
        IsOpen V ∧ IsOpen N ∧ p.1 ∈ N ∧ ContinuousOn ψ V ∧
        (∀ y ∈ N,
          y ∈ U ∩ Φ ⁻¹' {c} ↔
            (split_at_coordinate i y).1 ∈ V ∧
              (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1)) ∧
        (∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N) := by
  obtain ⟨i, N₀, hN₀, hpN₀, hN₀U, hderivN₀⟩ :=
    regular_level_set_exists_local_nonzero_coordinate U hU Φ hΦ c hreg p
  -- Route correction: the chart-packaging step has been separated from the IFT step.  The
  -- fixed-coordinate nonvanishing patch is now established; the remaining blocker is to apply the
  -- implicit function theorem on that patch and shrink the resulting eventual graph equation.
  have hif :
      (fderiv ℝ
          (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
          (split_at_coordinate i p.1) ∘L
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible :=
    regular_level_set_split_pullback_right_derivative_isInvertible i
      (hΦ.contDiffAt (hU.mem_nhds (hN₀U hpN₀))) (hderivN₀ p.1 hpN₀)
  let u : EuclideanSpace ℝ (Fin k) × ℝ := split_at_coordinate i p.1
  let F : EuclideanSpace ℝ (Fin k) × ℝ → ℝ := fun v ↦ Φ ((split_at_coordinate i).symm v)
  have hpLevelEq : Φ p.1 = c := by
    simpa using p.2.2
  have hFu : ContDiffAt ℝ 1 F u := by
    -- Differentiate the pulled-back equation in split coordinates at the base point `u`.
    have hΦp : ContDiffAt ℝ 1 Φ ((split_at_coordinate i).symm u) := by
      simpa [u] using hΦ.contDiffAt (hU.mem_nhds (hN₀U hpN₀))
    have hsplit : ContDiffAt ℝ 1 (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦
        (split_at_coordinate i).symm v) u := by
      exact ((split_at_coordinate_symm_contDiff i).contDiffAt).of_le (by simp)
    simpa [F, u] using hΦp.comp u hsplit
  let φu := (hFu.hasStrictFDerivAt one_ne_zero).implicitFunctionDataOfProdDomain hif
  let eu := φu.toOpenPartialHomeomorph
  let W : Set (EuclideanSpace ℝ (Fin k) × ℝ) := split_at_coordinate i '' N₀
  have hW : IsOpen W := by
    -- Transport the fixed-coordinate ambient patch into split coordinates.
    simpa [W] using (split_at_coordinate_homeomorph i).isOpenMap N₀ hN₀
  have huW : u ∈ W := by
    exact ⟨p.1, hpN₀, by simp [u]⟩
  have huSource : u ∈ eu.source := by
    simpa [eu, φu, u] using φu.pt_mem_toOpenPartialHomeomorph_source
  have huMap : eu u = (c, u.1) := by
    ext <;> simp [eu, φu, F, u, hpLevelEq]
  have huTarget : (c, u.1) ∈ eu.target := by
    -- At the base point, the implicit-function chart records the level value `c` and the
    -- retained coordinates `u.1`.
    simpa [huMap] using eu.map_source huSource
  have hpre :
      eu.symm ⁻¹' W ∈ 𝓝 (c, u.1) := by
    -- Shrink the target so that the inverse branch stays inside the fixed-coordinate patch `W`.
    have hcontSymm : ContinuousAt eu.symm (eu u) := eu.continuousAt_symm (eu.map_source huSource)
    have hWnhds : W ∈ 𝓝 (eu.symm (eu u)) := by
      simpa [eu.left_inv huSource] using hW.mem_nhds huW
    simpa [huMap] using hcontSymm.preimage_mem_nhds hWnhds
  obtain ⟨T₀, hT₀sub, hT₀open, huT₀⟩ := mem_nhds_iff.mp hpre
  let T : Set (ℝ × EuclideanSpace ℝ (Fin k)) := T₀ ∩ eu.target
  have hT : IsOpen T := hT₀open.inter eu.open_target
  have huT : (c, u.1) ∈ T := ⟨huT₀, huTarget⟩
  have hTsubW : ∀ z ∈ T, eu.symm z ∈ W := by
    intro z hz
    exact hT₀sub hz.1
  let σ : EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k) := fun x ↦ (c, x)
  let V : Set (EuclideanSpace ℝ (Fin k)) := σ ⁻¹' T
  let ψ : EuclideanSpace ℝ (Fin k) → ℝ := fun x ↦ (eu.symm (c, x)).2
  let N : Set (EuclideanSpace ℝ (Fin (k + 1))) :=
    (split_at_coordinate i) ⁻¹' (eu.source ∩ eu ⁻¹' T)
  have hV : IsOpen V := by
    -- The source slice `V` is the preimage of the shrunken target under `x ↦ (c, x)`.
    simpa [V, σ] using hT.preimage (continuous_const.prodMk continuous_id)
  have hN : IsOpen N := by
    -- Pull back the split-space graph patch to the ambient Euclidean space.
    simpa [N] using
      (eu.isOpen_inter_preimage hT).preimage (split_at_coordinate_continuous i)
  have hpN : p.1 ∈ N := by
    -- The base point lies in the chosen ambient patch because its split coordinates lie in the
    -- source and target pieces defining `N`.
    simpa [N, u, huMap] using ⟨huSource, huT⟩
  have hσ_maps : Set.MapsTo σ V T := by
    intro x hx
    exact hx
  have hψ : ContinuousOn ψ V := by
    -- The fixed branch is continuous on `V` because it is the inverse branch of `eu` on `T`.
    have hsymmOn : ContinuousOn (fun x : EuclideanSpace ℝ (Fin k) ↦ eu.symm (σ x)) V :=
      (eu.continuousOn_invFun.mono fun z hz ↦ hz.2).comp (continuous_const.prodMk continuous_id).continuousOn
        hσ_maps
    simpa [ψ, σ, Function.comp] using continuous_snd.comp_continuousOn hsymmOn
  refine ⟨i, V, N, ψ, hV, hN, hpN, hψ, ?_, ?_⟩
  · intro y hyN
    -- On the ambient patch `N`, the level set equation is equivalent to the fixed-branch graph
    -- equation because `eu` is locally invertible on `T`.
    let q : EuclideanSpace ℝ (Fin k) × ℝ := split_at_coordinate i y
    have hq : q ∈ eu.source ∩ eu ⁻¹' T := by
      simpa [N, q] using hyN
    have hqSource : q ∈ eu.source := hq.1
    have hqT : eu q ∈ T := hq.2
    have hqW : q ∈ W := by
      have hqSymm : eu.symm (eu q) = q := eu.left_inv hqSource
      simpa [hqSymm] using hTsubW (eu q) hqT
    have hyN₀ : y ∈ N₀ := by
      rcases hqW with ⟨y₀, hy₀N₀, hy₀eq⟩
      have hy₀ : y₀ = y := by
        apply (split_at_coordinate i).injective
        simpa [q] using hy₀eq
      simpa [hy₀] using hy₀N₀
    have hyU : y ∈ U := hN₀U hyN₀
    have hqBack : (split_at_coordinate i).symm q = y := by
      simpa [q] using (split_at_coordinate i).left_inv y
    constructor
    · intro hyLevel
      have hyLevelEq : Φ y = c := by simpa using hyLevel.2
      have hEq : eu q = (c, q.1) := by
        ext <;> simp [eu, φu, F, q, hqBack, hyLevelEq]
      have hqV : q.1 ∈ V := by
        simpa [V, σ, hEq] using hqT
      have hqGraph : q.2 = ψ q.1 := by
        have hqSymm : eu.symm (c, q.1) = q := by
          simpa [hEq] using eu.left_inv hqSource
        simpa [ψ, hqSymm]
      exact ⟨hqV, hqGraph⟩
    · rintro ⟨hqV, hqGraph⟩
      have hzT : (c, q.1) ∈ T := hqV
      have hqFst : (eu.symm (c, q.1)).1 = q.1 := by
        exact congrArg Prod.snd (eu.right_inv hzT.2)
      have hqEq : eu.symm (c, q.1) = q := by
        exact Prod.ext hqFst (by simpa [ψ] using hqGraph.symm)
      have hqW' : q ∈ W := by
        simpa [hqEq] using hTsubW (c, q.1) hzT
      have hyN₀' : y ∈ N₀ := by
        rcases hqW' with ⟨y₀, hy₀N₀, hy₀eq⟩
        have hy₀ : y₀ = y := by
          apply (split_at_coordinate i).injective
          simpa [q] using hy₀eq
        simpa [hy₀] using hy₀N₀
      have hyLevelEq : Φ y = c := by
        have hEq : eu q = (c, q.1) := by
          simpa [hqEq] using eu.right_inv hzT.2
        have hFirst : F q = c := congrArg Prod.fst hEq
        simpa [F, q, hqBack] using hFirst
      exact ⟨hN₀U hyN₀', by simpa [hyLevelEq]⟩
  · intro x hxV
    -- Points on the graph parametrized by `ψ` lie in the ambient patch by construction.
    have hzT : (c, x) ∈ T := hxV
    have hfstEq : (eu.symm (c, x)).1 = x := by
      exact congrArg Prod.snd (eu.right_inv hzT.2)
    have hpair : eu.symm (c, x) = (x, ψ x) := by
      exact Prod.ext hfstEq (by simp [ψ])
    have hmem : (x, ψ x) ∈ eu.source ∩ eu ⁻¹' T := by
      have hmap : eu (x, ψ x) = (c, x) := by
        calc
          eu (x, ψ x) = eu (eu.symm (c, x)) := by simpa [hpair]
          _ = (c, x) := eu.right_inv hzT.2
      refine ⟨?_, ?_⟩
      · simpa [hpair] using eu.map_target hzT.2
      · simpa [hmap] using hzT
    simpa [N] using hmem

/-- Helper for Example 1.32: after splitting off a coordinate with nonzero derivative, each point
of the regular level set should admit a local chart to `ℝ^k`. -/
lemma regular_level_set_has_local_chart {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0) :
    ∀ p : ↥(U ∩ Φ ⁻¹' {c}),
      ∃ e : OpenPartialHomeomorph ↥(U ∩ Φ ⁻¹' {c}) (EuclideanSpace ℝ (Fin k)),
        p ∈ e.source := by
  intro p
  obtain ⟨i, V, N, ψ, hV, hN, hpN, hψ, hgraph, hparamN⟩ :=
    regular_level_set_exists_local_graph_data U hU Φ hΦ c hreg p
  have hpGraph : split_at_coordinate i p.1 ∈ V.graphOn ψ :=
    regular_level_set_point_mem_graph_of_local_graph i V N ψ hgraph hpN
  have hVne : Nonempty V := ⟨⟨(split_at_coordinate i p.1).1, (Set.mem_graphOn.1 hpGraph).1⟩⟩
  let e : OpenPartialHomeomorph ↥(U ∩ Φ ⁻¹' {c}) (EuclideanSpace ℝ (Fin k)) :=
    regular_level_set_local_chart_of_local_graph p i V N ψ hN hV hψ hVne hgraph hparamN hpN
  refine ⟨e, ?_⟩
  -- The explicit chart source is exactly the ambient patch membership condition.
  have hpSource :
      p ∈ (regular_level_set_local_chart_of_local_graph p i V N ψ hN hV hψ hVne hgraph hparamN hpN).source := by
    rw [regular_level_set_local_chart_of_local_graph_source]
    exact hpN
  simpa [e] using hpSource

/-- Helper for Example 1.32: package the explicit smooth local graph data used to define one chart
in the smooth atlas of a regular level set. -/
structure RegularLevelSetSmoothLocalGraphData {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (c : ℝ)
    (p : ↥(U ∩ Φ ⁻¹' {c})) where
  i : Fin (k + 1)
  V : Set (EuclideanSpace ℝ (Fin k))
  N : Set (EuclideanSpace ℝ (Fin (k + 1)))
  ψ : EuclideanSpace ℝ (Fin k) → ℝ
  hV : IsOpen V
  hN : IsOpen N
  hpN : p.1 ∈ N
  hψ : ContinuousOn ψ V
  hψsmooth : ContDiffOn ℝ ∞ ψ V
  hgraph : ∀ y ∈ N,
    y ∈ U ∩ Φ ⁻¹' {c} ↔
      (split_at_coordinate i y).1 ∈ V ∧
        (split_at_coordinate i y).2 = ψ ((split_at_coordinate i y).1)
  hparamN : ∀ x ∈ V, (split_at_coordinate i).symm (x, ψ x) ∈ N

/-- Helper for Example 1.32: the fixed-coordinate implicit-function construction can be refined so
that the chosen branch `ψ` is smooth on the same open set `V` used for the local graph chart. -/
lemma regular_level_set_exists_local_smooth_graph_data {k : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0)
    (p : ↥(U ∩ Φ ⁻¹' {c})) :
    Nonempty (RegularLevelSetSmoothLocalGraphData U Φ c p) := by
  obtain ⟨i, N₀, hN₀, hpN₀, hN₀U, hderivN₀⟩ :=
    regular_level_set_exists_local_nonzero_coordinate U hU Φ (hΦ.of_le (by simp)) c hreg p
  have hif :
      (fderiv ℝ
          (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ Φ ((split_at_coordinate i).symm v))
          (split_at_coordinate i p.1) ∘L
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible :=
    regular_level_set_split_pullback_right_derivative_isInvertible i
      ((hΦ.contDiffAt (hU.mem_nhds (hN₀U hpN₀))).of_le (by simp)) (hderivN₀ p.1 hpN₀)
  let u : EuclideanSpace ℝ (Fin k) × ℝ := split_at_coordinate i p.1
  let F : EuclideanSpace ℝ (Fin k) × ℝ → ℝ := fun v ↦ Φ ((split_at_coordinate i).symm v)
  have hpLevelEq : Φ p.1 = c := by
    simpa using p.2.2
  have hFu : ContDiffAt ℝ ∞ F u := by
    -- Pull back the ambient smooth function `Φ` to split coordinates at the base point `u`.
    have hΦp : ContDiffAt ℝ ∞ Φ ((split_at_coordinate i).symm u) := by
      simpa [u] using hΦ.contDiffAt (hU.mem_nhds (hN₀U hpN₀))
    have hsplit :
        ContDiffAt ℝ ∞ (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ (split_at_coordinate i).symm v) u :=
      (split_at_coordinate_symm_contDiff i).contDiffAt
    simpa [F, u] using hΦp.comp u hsplit
  have hFu1 : ContDiffAt ℝ 1 F u := hFu.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  let φu := (hFu1.hasStrictFDerivAt one_ne_zero).implicitFunctionDataOfProdDomain hif
  let eu := φu.toOpenPartialHomeomorph
  let W : Set (EuclideanSpace ℝ (Fin k) × ℝ) := split_at_coordinate i '' N₀
  have hW : IsOpen W := by
    -- Transport the fixed-coordinate ambient patch into split coordinates.
    simpa [W] using (split_at_coordinate_homeomorph i).isOpenMap N₀ hN₀
  have huW : u ∈ W := by
    exact ⟨p.1, hpN₀, by simp [u]⟩
  have huSource : u ∈ eu.source := by
    simpa [eu, φu, u] using φu.pt_mem_toOpenPartialHomeomorph_source
  have huMap : eu u = (c, u.1) := by
    -- At the base point the inverse-function chart records the level value and retained
    -- coordinates.
    ext <;> simp [eu, φu, F, u, hpLevelEq]
  have huTarget : (c, u.1) ∈ eu.target := by
    simpa [huMap] using eu.map_source huSource
  have hpre :
      eu.symm ⁻¹' W ∈ 𝓝 (c, u.1) := by
    -- Shrink the target so the inverse branch stays inside the chosen split-coordinate patch.
    have hcontSymm : ContinuousAt eu.symm (eu u) := eu.continuousAt_symm (eu.map_source huSource)
    have hWnhds : W ∈ 𝓝 (eu.symm (eu u)) := by
      simpa [eu.left_inv huSource] using hW.mem_nhds huW
    simpa [huMap] using hcontSymm.preimage_mem_nhds hWnhds
  obtain ⟨T₀, hT₀sub, hT₀open, huT₀⟩ := mem_nhds_iff.mp hpre
  let T : Set (ℝ × EuclideanSpace ℝ (Fin k)) := T₀ ∩ eu.target
  have hT : IsOpen T := hT₀open.inter eu.open_target
  have huT : (c, u.1) ∈ T := ⟨huT₀, huTarget⟩
  have hTsubW : ∀ z ∈ T, eu.symm z ∈ W := by
    intro z hz
    exact hT₀sub hz.1
  let σ : EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k) := fun x ↦ (c, x)
  let V : Set (EuclideanSpace ℝ (Fin k)) := σ ⁻¹' T
  let ψ : EuclideanSpace ℝ (Fin k) → ℝ := fun x ↦ (eu.symm (c, x)).2
  let N : Set (EuclideanSpace ℝ (Fin (k + 1))) :=
    (split_at_coordinate i) ⁻¹' (eu.source ∩ eu ⁻¹' T)
  have hV : IsOpen V := by
    -- The source slice `V` is the preimage of the shrunken target under `x ↦ (c, x)`.
    simpa [V, σ] using hT.preimage (continuous_const.prodMk continuous_id)
  have hN : IsOpen N := by
    -- Pull back the split-space graph patch to the ambient Euclidean space.
    simpa [N] using
      (eu.isOpen_inter_preimage hT).preimage (split_at_coordinate_continuous i)
  have hpN : p.1 ∈ N := by
    -- The base point lies in the pulled-back patch because its split coordinates lie in both the
    -- source and target pieces defining `N`.
    simpa [N, u, huMap] using ⟨huSource, huT⟩
  have hσ_maps : Set.MapsTo σ V T := by
    intro x hx
    exact hx
  have hψ : ContinuousOn ψ V := by
    -- The chosen implicit branch is continuous on `V` because it is the inverse branch of `eu`
    -- followed by the second projection.
    have hsymmOn : ContinuousOn (fun x : EuclideanSpace ℝ (Fin k) ↦ eu.symm (σ x)) V :=
      (eu.continuousOn_invFun.mono fun z hz ↦ hz.2).comp (continuous_const.prodMk continuous_id).continuousOn
        hσ_maps
    simpa [ψ, σ, Function.comp] using continuous_snd.comp_continuousOn hsymmOn
  have hψsmooth : ContDiffOn ℝ ∞ ψ V := by
    rw [contDiffOn_infty]
    intro m x hxV
    -- For each `x ∈ V`, the branch value `ψ x` is the second coordinate of `eu.symm (c, x)`.
    have hzT : (c, x) ∈ T := hxV
    let q : EuclideanSpace ℝ (Fin k) × ℝ := eu.symm (c, x)
    have hqW : q ∈ W := by
      simpa [q] using hTsubW (c, x) hzT
    rcases hqW with ⟨y, hyN₀, hyq⟩
    have hsymm_q : (split_at_coordinate i).symm q = y := by
      simpa [q] using (congrArg (split_at_coordinate i).symm hyq).symm
    have hΦy : ContDiffAt ℝ ∞ Φ y := hΦ.contDiffAt (hU.mem_nhds (hN₀U hyN₀))
    have hFq : ContDiffAt ℝ ∞ F q := by
      -- Rewrite `F` at `q` back to the ambient point `y` where `Φ` is already smooth.
      have hΦq : ContDiffAt ℝ ∞ Φ ((split_at_coordinate i).symm q) := by
        simpa [hsymm_q] using hΦy
      simpa [F, hsymm_q] using
        hΦq.comp q ((split_at_coordinate_symm_contDiff i).contDiffAt)
    have hInvertible :
        (fderiv ℝ F q ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) ℝ).IsInvertible := by
      -- The distinguished scalar derivative is nonzero on the whole ambient patch `N₀`.
      simpa [F, hyq] using
        regular_level_set_split_pullback_right_derivative_isInvertible i
          (hΦy.of_le (by simp)) (hderivN₀ y hyN₀)
    have heu_deriv :
        HasFDerivAt eu ((prod_fst_fderiv_equiv_of_right_invertible F q hInvertible : _ →L[ℝ] _)) q := by
      -- The forward chart is exactly `v ↦ (F v, v.1)` at the derivative level.
      simpa [eu, φu, F, ImplicitFunctionData.toOpenPartialHomeomorph_apply] using
        hasFDerivAt_prod_fst_of_right_invertible hFq hInvertible
    have heu : ContDiffAt ℝ m eu q := by
      -- The same explicit formula gives finite-order smoothness of the forward chart.
      have hpair : ContDiffAt ℝ ∞ (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ (F v, v.1)) q :=
        hFq.prodMk contDiffAt_fst
      have hm : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        exact WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) (m : ℕ∞))
      have hpairm : ContDiffAt ℝ m (fun v : EuclideanSpace ℝ (Fin k) × ℝ ↦ (F v, v.1)) q :=
        hpair.of_le hm
      simpa [eu, φu, F, ImplicitFunctionData.toOpenPartialHomeomorph_apply] using hpairm
    have hsymm :
        ContDiffAt ℝ m (fun x' : EuclideanSpace ℝ (Fin k) ↦ eu.symm (σ x')) x := by
      -- Compose `eu.symm` with the slice map `x' ↦ (c, x')`.
      have hσ :
          ContDiffAt ℝ m (fun x' : EuclideanSpace ℝ (Fin k) ↦ (c, x')) x := by
        simpa [σ] using
          (contDiff_const.prodMk
            (contDiff_id : ContDiff ℝ m (fun x' : EuclideanSpace ℝ (Fin k) ↦ x'))).contDiffAt
      exact (eu.contDiffAt_symm hzT.2 heu_deriv heu).comp x hσ
    have hψAt : ContDiffAt ℝ m ψ x := by
      simpa [ψ, σ, Function.comp] using (contDiffAt_snd.comp x hsymm)
    exact hψAt.contDiffWithinAt
  refine ⟨⟨i, V, N, ψ, hV, hN, hpN, hψ, hψsmooth, ?_, ?_⟩⟩
  · intro y hyN
    -- On the ambient patch `N`, the level-set equation is equivalent to the fixed-branch graph
    -- equation because `eu` is locally invertible on `T`.
    let q : EuclideanSpace ℝ (Fin k) × ℝ := split_at_coordinate i y
    have hq : q ∈ eu.source ∩ eu ⁻¹' T := by
      simpa [N, q] using hyN
    have hqSource : q ∈ eu.source := hq.1
    have hqT : eu q ∈ T := hq.2
    have hqW : q ∈ W := by
      have hqSymm : eu.symm (eu q) = q := eu.left_inv hqSource
      simpa [hqSymm] using hTsubW (eu q) hqT
    have hyN₀ : y ∈ N₀ := by
      rcases hqW with ⟨y₀, hy₀N₀, hy₀eq⟩
      have hy₀ : y₀ = y := by
        apply (split_at_coordinate i).injective
        simpa [q] using hy₀eq
      simpa [hy₀] using hy₀N₀
    have hyU : y ∈ U := hN₀U hyN₀
    have hqBack : (split_at_coordinate i).symm q = y := by
      simpa [q] using (split_at_coordinate i).left_inv y
    constructor
    · intro hyLevel
      have hyLevelEq : Φ y = c := by simpa using hyLevel.2
      have hEq : eu q = (c, q.1) := by
        ext <;> simp [eu, φu, F, q, hqBack, hyLevelEq]
      have hqV : q.1 ∈ V := by
        simpa [V, σ, hEq] using hqT
      have hqGraph : q.2 = ψ q.1 := by
        have hqSymm : eu.symm (c, q.1) = q := by
          simpa [hEq] using eu.left_inv hqSource
        simpa [ψ, hqSymm]
      exact ⟨hqV, hqGraph⟩
    · rintro ⟨hqV, hqGraph⟩
      have hzT : (c, q.1) ∈ T := hqV
      have hqFst : (eu.symm (c, q.1)).1 = q.1 := by
        exact congrArg Prod.snd (eu.right_inv hzT.2)
      have hqEq : eu.symm (c, q.1) = q := by
        exact Prod.ext hqFst (by simpa [ψ] using hqGraph.symm)
      have hqW' : q ∈ W := by
        simpa [hqEq] using hTsubW (c, q.1) hzT
      have hyN₀' : y ∈ N₀ := by
        rcases hqW' with ⟨y₀, hy₀N₀, hy₀eq⟩
        have hy₀ : y₀ = y := by
          apply (split_at_coordinate i).injective
          simpa [q] using hy₀eq
        simpa [hy₀] using hy₀N₀
      have hyLevelEq : Φ y = c := by
        have hEq : eu q = (c, q.1) := by
          simpa [hqEq] using eu.right_inv hzT.2
        have hFirst : F q = c := congrArg Prod.fst hEq
        simpa [F, q, hqBack] using hFirst
      exact ⟨hN₀U hyN₀', by simpa [hyLevelEq]⟩
  · intro x hxV
    -- Points on the graph parametrized by `ψ` lie in the ambient patch by construction.
    have hzT : (c, x) ∈ T := hxV
    have hfstEq : (eu.symm (c, x)).1 = x := by
      exact congrArg Prod.snd (eu.right_inv hzT.2)
    have hpair : eu.symm (c, x) = (x, ψ x) := by
      exact Prod.ext hfstEq (by simp [ψ])
    have hmem : (x, ψ x) ∈ eu.source ∩ eu ⁻¹' T := by
      have hmap : eu (x, ψ x) = (c, x) := by
        calc
          eu (x, ψ x) = eu (eu.symm (c, x)) := by simpa [hpair]
          _ = (c, x) := eu.right_inv hzT.2
      refine ⟨?_, ?_⟩
      · simpa [hpair] using eu.map_target hzT.2
      · simpa [hmap] using hzT
    simpa [N] using hmem

namespace RegularLevelSetSmoothLocalGraphData

/-- Helper for Example 1.32: the chosen base point supplies a point of `V`, so the chart domain is
nonempty. -/
lemma nonempty_V {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p) :
    Nonempty d.V := by
  have hpGraph : split_at_coordinate d.i p.1 ∈ d.V.graphOn d.ψ :=
    regular_level_set_point_mem_graph_of_local_graph d.i d.V d.N d.ψ d.hgraph d.hpN
  exact ⟨⟨(split_at_coordinate d.i p.1).1, (Set.mem_graphOn.1 hpGraph).1⟩⟩

/-- Helper for Example 1.32: the smooth local graph data determines the explicit chart used in the
smooth atlas. -/
noncomputable def chart {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p) :
    OpenPartialHomeomorph ↥(U ∩ Φ ⁻¹' {c}) (EuclideanSpace ℝ (Fin k)) :=
  regular_level_set_local_chart_of_local_graph p d.i d.V d.N d.ψ
    d.hN d.hV d.hψ d.nonempty_V d.hgraph d.hparamN d.hpN

/-- Helper for Example 1.32: the chosen chart is defined at the base point. -/
lemma mem_chart_source {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p) :
    p ∈ d.chart.source := by
  rw [RegularLevelSetSmoothLocalGraphData.chart, regular_level_set_local_chart_of_local_graph_source]
  exact d.hpN

/-- Helper for Example 1.32: the chart target is exactly the base open set `V` from the local
graph model. -/
lemma chart_target {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p) :
    d.chart.target = d.V := by
  rw [RegularLevelSetSmoothLocalGraphData.chart,
    regular_level_set_local_chart_of_local_graph_target]

/-- Helper for Example 1.32: the forward explicit local chart records the retained split
coordinates. -/
lemma chart_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p)
    {q : ↥(U ∩ Φ ⁻¹' {c})} (hq : q ∈ d.chart.source) :
    d.chart q = (split_at_coordinate d.i q.1).1 := by
  have hqN : q.1 ∈ d.N := by
    rw [RegularLevelSetSmoothLocalGraphData.chart,
      regular_level_set_local_chart_of_local_graph_source] at hq
    exact hq
  let P : TopologicalSpace.Opens ↥(U ∩ Φ ⁻¹' {c}) :=
    regular_level_set_subtype_patch U Φ c d.N d.hN
  let q' : ↥(regular_level_set_subtype_patch U Φ c d.N d.hN) :=
    (P.openPartialHomeomorphSubtypeCoe ⟨p, d.hpN⟩).symm q
  have hqTarget : q ∈ (P.openPartialHomeomorphSubtypeCoe ⟨p, d.hpN⟩).target := by
    simpa [P, regular_level_set_subtype_patch] using hqN
  have hq' : (q' : ↥(U ∩ Φ ⁻¹' {c})) = q := by
    -- The inverse of the open-subtype inclusion just reattaches the proof that `q.1 ∈ d.N`.
    simpa [P, q', TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using
      (P.openPartialHomeomorphSubtypeCoe ⟨p, d.hpN⟩).right_inv hqTarget
  -- After moving to the explicit patch subtype, the chart is exactly the patch graph chart.
  rw [RegularLevelSetSmoothLocalGraphData.chart, regular_level_set_local_chart_of_local_graph,
    OpenPartialHomeomorph.trans_apply]
  simpa [P, q', hq'] using
    regular_level_set_patch_chart_of_local_graph_apply d.i d.V d.N d.ψ d.hN d.hV d.hψ d.nonempty_V
      d.hgraph d.hparamN q'

/-- Helper for Example 1.32: the inverse of the explicit local chart reinserts the fixed branch
value as the distinguished split coordinate. -/
lemma chart_symm_apply {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ d.chart.target) :
    (d.chart.symm x : ↥(U ∩ Φ ⁻¹' {c})).1 = (split_at_coordinate d.i).symm (x, d.ψ x) := by
  have hxV : x ∈ d.V := by
    simpa [d.chart_target] using hx
  let q : ↥(U ∩ Φ ⁻¹' {c}) := d.chart.symm x
  have hqSource : q ∈ d.chart.source := d.chart.map_target hx
  have hqN : q.1 ∈ d.N := by
    rw [RegularLevelSetSmoothLocalGraphData.chart,
      regular_level_set_local_chart_of_local_graph_source] at hqSource
    exact hqSource
  have hchart : d.chart q = x := by
    simpa [q] using d.chart.right_inv hx
  have hfst : (split_at_coordinate d.i q.1).1 = x := by
    -- The inverse chart returns the unique level-set point whose retained coordinates are `x`.
    simpa [q] using (d.chart_apply hqSource).symm.trans hchart
  have hsplit :
      (split_at_coordinate d.i q.1).1 ∈ d.V ∧
        (split_at_coordinate d.i q.1).2 = d.ψ ((split_at_coordinate d.i q.1).1) :=
    (d.hgraph q.1 hqN).1 q.2
  have hsnd : (split_at_coordinate d.i q.1).2 = d.ψ x := by
    -- The graph equation now identifies the distinguished split coordinate with `d.ψ x`.
    simpa [hfst] using hsplit.2
  have hfst' :
      (split_at_coordinate d.i q.1).1 =
        ((split_at_coordinate d.i) ((split_at_coordinate d.i).symm (x, d.ψ x))).1 := by
    simpa using hfst
  have hsnd' :
      (split_at_coordinate d.i q.1).2 =
        ((split_at_coordinate d.i) ((split_at_coordinate d.i).symm (x, d.ψ x))).2 := by
    simpa using hsnd
  -- Matching both split coordinates determines the ambient point.
  apply (split_at_coordinate d.i).injective
  exact Prod.ext hfst' hsnd'

end RegularLevelSetSmoothLocalGraphData

/-- Helper for Example 1.32: on the overlap of two explicit local graph charts, the transition map
is exactly the split-coordinate expression from Lee's proof. -/
lemma regular_level_set_local_chart_of_local_graph_transition_formula {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p p' : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p)
    (d' : RegularLevelSetSmoothLocalGraphData U Φ c p') :
    Set.EqOn (d.chart.symm.trans d'.chart)
      (fun x ↦ (split_at_coordinate d'.i ((split_at_coordinate d.i).symm (x, d.ψ x))).1)
      (d.chart.symm.trans d'.chart).source := by
  intro x hx
  rw [OpenPartialHomeomorph.trans_apply]
  have hxTarget : x ∈ d.chart.target := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.1
  have hqSource : d.chart.symm x ∈ d'.chart.source := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx.2
  have hsymm :
      (d.chart.symm x : ↥(U ∩ Φ ⁻¹' {c})).1 = (split_at_coordinate d.i).symm (x, d.ψ x) :=
    d.chart_symm_apply hxTarget
  -- The overlap map is the second chart evaluated at the explicit inverse-image point.
  simpa [hsymm] using d'.chart_apply hqSource

/-- Helper for Example 1.32: after rewriting chart overlaps to the explicit split-coordinate
formula, the normalized transition is smooth because it is obtained by composing the graph map
`x ↦ (x, d.ψ x)` with globally smooth split-coordinate changes. -/
lemma regular_level_set_normalized_transition_contDiffOn {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p p' : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p)
    (d' : RegularLevelSetSmoothLocalGraphData U Φ c p') :
    ContDiffOn ℝ ∞
      (fun x ↦ (split_at_coordinate d'.i ((split_at_coordinate d.i).symm (x, d.ψ x))).1)
      (d.chart.symm.trans d'.chart).source := by
  let S : Set (EuclideanSpace ℝ (Fin k)) := (d.chart.symm.trans d'.chart).source
  have hSV : S ⊆ d.V := by
    intro x hx
    have hx' : x ∈ d.chart.target ∧ d.chart.symm x ∈ d'.chart.source := by
      simpa [S, OpenPartialHomeomorph.trans_source] using hx
    simpa [d.chart_target] using hx'.1
  have hgraphMap : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin k) ↦ (x, d.ψ x)) S := by
    -- On the overlap source, both the identity and the branch `d.ψ` are smooth.
    exact contDiff_id.contDiffOn.prodMk (d.hψsmooth.mono hSV)
  have hsplitBack :
      ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin k) ↦ (split_at_coordinate d.i).symm (x, d.ψ x)) S := by
    -- Reinsert the distinguished coordinate by the smooth inverse split map.
    simpa [Function.comp] using (split_at_coordinate_symm_contDiff d.i).comp_contDiffOn hgraphMap
  have hsplitForward :
      ContDiffOn ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin k) ↦
          split_at_coordinate d'.i ((split_at_coordinate d.i).symm (x, d.ψ x))) S := by
    -- Then change from `d.i`-split coordinates to `d'.i`-split coordinates.
    simpa [Function.comp] using (split_at_coordinate_contDiff d'.i).comp_contDiffOn hsplitBack
  -- Finally project to the retained coordinates of the target chart.
  simpa [S, Function.comp] using contDiff_fst.comp_contDiffOn hsplitForward

/-- Helper for Example 1.32: the transition between two explicit local graph charts is smooth on
its whole source because it is a composition of the graph map, the split inverse, the split map,
and the first projection. -/
lemma regular_level_set_local_chart_transition_contDiffOn {k : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (k + 1)))} {Φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {c : ℝ} {p p' : ↥(U ∩ Φ ⁻¹' {c})}
    (d : RegularLevelSetSmoothLocalGraphData U Φ c p)
    (d' : RegularLevelSetSmoothLocalGraphData U Φ c p') :
    ContDiffOn ℝ ∞ (d.chart.symm.trans d'.chart) (d.chart.symm.trans d'.chart).source := by
  -- First prove smoothness for the normalized overlap formula from Lee's split-coordinate
  -- description, then transfer it back to the raw chart transition by pointwise equality.
  exact (regular_level_set_normalized_transition_contDiffOn d d').congr
    (regular_level_set_local_chart_of_local_graph_transition_formula d d')

/-- Example 1.32 (1): if `U ⊆ ℝ^n` is open, `Φ : U → ℝ` is `C^1`, and the total derivative of
`Φ` is nonzero at every point of the level set `Φ⁻¹({c}) ∩ U`, then that level set admits a
charted-space structure making it a topological manifold of dimension `n - 1`. -/
theorem regular_level_set_topologicalManifold (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΦ : ContDiffOn ℝ 1 Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0) :
    let S := ↥(U ∩ Φ ⁻¹' {c})
    ∃ _ : TopologicalManifold (n - 1) S, IsManifold (𝓡 (n - 1)) 0 S := by
  classical
  by_cases hn : n = 0
  · subst hn
    -- In ambient dimension `0`, the regular level set is empty, so the empty atlas suffices.
    let S := ↥(U ∩ Φ ⁻¹' {c})
    let _ : IsEmpty S := regular_level_set_isEmpty_of_zero_dim U Φ c hreg
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) S := ChartedSpace.empty _ S
    let tm : TopologicalManifold 0 S := topologicalManifoldOfChartedSpace 0 S
    exact ⟨tm, inferInstance⟩
  · -- Route correction: reduce immediately to `n = k + 1`, then build the charted space from the
    -- pointwise local charts supplied by the inverse-function theorem.
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
    let S := ↥(U ∩ Φ ⁻¹' {c})
    change ∃ _ : TopologicalManifold k S, IsManifold (𝓡 k) 0 S
    have hcharts :
        ∀ p : S,
          ∃ e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)),
            p ∈ e.source :=
      regular_level_set_has_local_chart U hU Φ hΦ c hreg
    let chartAtLocal : S → OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
      fun p ↦ Classical.choose (hcharts p)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      { atlas := Set.range chartAtLocal
        chartAt := chartAtLocal
        mem_chart_source := fun p ↦ Classical.choose_spec (hcharts p)
        chart_mem_atlas := fun p ↦ ⟨p, rfl⟩ }
    -- Once the chosen local charts are installed, Hausdorff and second-countable properties come
    -- from the ambient Euclidean subtype topology.
    let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    exact ⟨tm, inferInstance⟩

/-- Example 1.32 (2): under the same regularity and nonvanishing-derivative hypotheses, the level
set `Φ⁻¹({c}) ∩ U` admits a smooth manifold structure modelled on `ℝ^(n - 1)`. -/
theorem regular_level_set_smooth_structure (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ U) (c : ℝ)
    (hreg : ∀ a ∈ U, Φ a = c → fderiv ℝ Φ a ≠ 0) :
    let S := ↥(U ∩ Φ ⁻¹' {c})
    ∃ _ : TopologicalManifold (n - 1) S, IsManifold (𝓡 (n - 1)) ∞ S := by
  classical
  by_cases hn : n = 0
  · subst hn
    -- In ambient dimension `0`, the regular level set is empty, so the empty smooth atlas suffices.
    let S := ↥(U ∩ Φ ⁻¹' {c})
    let _ : IsEmpty S := regular_level_set_isEmpty_of_zero_dim U Φ c hreg
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) S := ChartedSpace.empty _ S
    let tm : TopologicalManifold 0 S := topologicalManifoldOfChartedSpace 0 S
    exact ⟨tm, inferInstance⟩
  · -- Route correction: keep the topological chart-selection skeleton from the preceding theorem
    -- but choose the charts directly from the smooth local graph data so the overlap formulas are
    -- available in exactly the atlas used for the smooth structure.
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
    let S := ↥(U ∩ Φ ⁻¹' {c})
    change ∃ _ : TopologicalManifold k S, IsManifold (𝓡 k) ∞ S
    let chartData : ∀ p : S, RegularLevelSetSmoothLocalGraphData U Φ c p :=
      fun p ↦ Classical.choice (regular_level_set_exists_local_smooth_graph_data U hU Φ hΦ c hreg p)
    let chartAtLocal : S → OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
      fun p ↦ (chartData p).chart
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      { atlas := Set.range chartAtLocal
        chartAt := chartAtLocal
        mem_chart_source := fun p ↦ (chartData p).mem_chart_source
        chart_mem_atlas := fun p ↦ ⟨p, rfl⟩ }
    let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    have hs : IsManifold (𝓡 k) ∞ S := by
      -- The remaining smooth step is Lee's overlap computation for the explicit graph charts.
      refine isManifold_of_contDiffOn (I := 𝓡 k) (n := (∞ : ℕ∞ω)) (M := S) ?_
      intro e e' he he'
      rcases he with ⟨p, rfl⟩
      rcases he' with ⟨p', rfl⟩
      let dp := chartData p
      let dp' := chartData p'
      simpa [chartAtLocal, dp, dp'] using
        regular_level_set_local_chart_transition_contDiffOn dp dp'
    exact ⟨tm, hs⟩
