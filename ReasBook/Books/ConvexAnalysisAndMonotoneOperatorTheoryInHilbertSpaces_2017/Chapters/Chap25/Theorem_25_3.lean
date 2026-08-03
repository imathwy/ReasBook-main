import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap20.Proposition_20_23
import BauschkeLean.Chap20.Proposition_20_57
import BauschkeLean.Chap25.Theorem_25_3.ProjectedSriSum
import BauschkeLean.Chap21.Corollary_21_20
import BauschkeLean.Chap21.Proposition_21_12
import BauschkeLean.Chap21.Example_21_13

open Set
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator
universe u v

namespace SetValuedOperator

noncomputable section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Theorem 25.3 is the composite-sum maximality theorem for `A + L^* B L`
  under the domain regularity condition `(25.7)`.
- `core/canonical`: the reusable owner is maximal monotonicity, written
  `Maximal IsMonotone`.
- `bridge/view`: the composite operator `L^* B L` is represented by the local canonical bridge
  `ContinuousLinearMap.adjointImage`. -/

/-- Helper for Theorem 25.3: maximal monotonicity forces the graph to be nonempty. -/
private theorem graph_nonempty_of_maximal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : SetValuedOperator E E} (hT : Maximal IsMonotone T) :
    (gra T).Nonempty := by
  by_contra hT_graph
  let Z : SetValuedOperator E E := fun _ ↦ ({0} : Set E)
  have hZ_mono : Z.IsMonotone := by
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    simp [Z] at hu hv
    subst u
    subst v
    simp
  have hTZ : T ≤ Z := by
    intro x u hu
    have hmem : (x, u) ∈ gra T := by
      simpa [SetValuedOperator.mem_graph] using hu
    exact (hT_graph ⟨(x, u), hmem⟩).elim
  have hzero_mem : 0 ∈ T 0 := (hT.2 hZ_mono hTZ 0) (by simp [Z])
  have hmem_zero : (0, 0) ∈ gra T := by
    simpa [SetValuedOperator.mem_graph] using hzero_mem
  exact hT_graph ⟨(0, 0), hmem_zero⟩

/-- Helper for Theorem 25.3: the canonical orthogonal vector to `gra M` is `(M† v, -v)`. -/
private theorem pairAdjointNeg_mem_orthogonalGraph
    (M : H →L[ℝ] K) (v : K) :
    (M.adjoint v, -v) ∈
      ((((M.toLinearMap.graph : Submodule ℝ (H × K))ᗮ :
        Submodule ℝ (H × K)) : Set (H × K))) := by
  simpa using pair_adjoint_neg_mem_orthogonal_graph (M := M) (v := v)

/-- Helper for Theorem 25.3: every vector orthogonal to `gra M` has the form `(M† v, -v)`. -/
private theorem orthogonalGraph_point_eq_pairAdjointNeg
    (M : H →L[ℝ] K) {u : H × K}
    (hu : u ∈ ((((M.toLinearMap.graph : Submodule ℝ (H × K))ᗮ :
      Submodule ℝ (H × K)) : Set (H × K)))) :
    ∃ v : K, u = (M.adjoint v, -v) := by
  simpa using orthogonal_graph_point_eq_pair_adjoint_neg (M := M) hu

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 25.3: the `ℓ²` product inner product splits into its two coordinates. -/
private theorem prodInner_eq_sum {p q : H × K} :
    ⟪p, q⟫_ℝ = ⟪p.1, q.1⟫_ℝ + ⟪p.2, q.2⟫_ℝ := by
  rfl

/-- Helper for Theorem 25.3: `fstImageDomFitzpatrick` is convex for a maximally monotone
operator. -/
private theorem convexFstImageDomFitzpatrickOfMaximal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : SetValuedOperator E E) (hT : Maximal IsMonotone T) :
    Convex ℝ T.fstImageDomFitzpatrick := by
  have hT_graph : (gra T).Nonempty := graph_nonempty_of_maximal hT
  have hT_mono : T.IsMonotone := Maximal.isMonotone hT
  let FT : E × E → Set.Ioi (⊥ : EReal) :=
    properIoi (F[T])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        T hT_graph hT_mono)
  have hFT : FT ∈ Γ₀(E × E) := by
    -- Package the Fitzpatrick owner into the canonical `Γ₀` API before projecting its domain.
    simpa [FT] using fitzpatrickFunction_mem_gammaZero T hT_graph hT_mono
  -- The first-coordinate image of a convex effective domain is convex.
  simpa [fstImageDomFitzpatrick, FT, ERealFunction.effectiveDomain, ERealFunction.dom] using
    hFT.2.convex_effectiveDomain.linear_image (ContinuousLinearMap.fst ℝ E E).toLinearMap

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 25.3: at a graph point, the normal cone to `gra L` is the orthogonal
graph subspace. -/
private theorem normalConeGraph_eq_orthogonalGraph
    (L : H →L[ℝ] K) {p : H × K}
    (hp : p ∈ (L.toLinearMap.graph : Set (H × K))) :
    N[(L.toLinearMap.graph : Set (H × K))] p =
      ((((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ :
        Submodule ℝ (H × K)) : Set (H × K))) := by
  let A : AffineSubspace ℝ (H × K) :=
    (L.toLinearMap.graph : Submodule ℝ (H × K)).toAffineSubspace
  have hAset : (L.toLinearMap.graph : Set (H × K)) = (A : Set (H × K)) := by
    -- The affine subspace attached to the graph submodule has the same carrier.
    ext z
    simp [A, Submodule.mem_toAffineSubspace]
  rw [hAset]
  have hpA : p ∈ (A : Set (H × K)) := by
    simpa [A, Submodule.mem_toAffineSubspace] using hp
  -- Example 6.43 identifies the normal cone of an affine subspace with the orthogonal direction.
  simpa [A, Submodule.toAffineSubspace_direction] using
    normalCone_affineSubspace_eq_direction_orthogonal_of_mem A hpA

omit [InnerProductSpace ℝ H] [CompleteSpace H] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Theorem 25.3: the first projection carries set subtraction in `H × K` to set
subtraction in `H × K`. -/
private theorem fst_image_sub_eq_sub_fst_image
    {S T : Set (H × K)} :
    Prod.fst '' (S - T) = (Prod.fst '' S) - (Prod.fst '' T) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases Set.mem_sub.mp hp with ⟨s, hs, t, ht, hst⟩
    refine Set.mem_sub.mpr ?_
    refine ⟨s.1, ?_, t.1, ?_, ?_⟩
    · exact ⟨s, hs, rfl⟩
    · exact ⟨t, ht, rfl⟩
    · simpa using congrArg Prod.fst hst
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨s, hs, t, ht, hst⟩
    rcases hs with ⟨p, hp, hp1⟩
    rcases ht with ⟨q, hq, hq1⟩
    subst s
    subst t
    refine ⟨p - q, ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨p, hp, q, hq, rfl⟩
    · simp [hst]

/-- Helper for Theorem 25.3: membership in the lifted product-space sum on `gra L` is exactly
membership in `A + L.adjointImage B`. -/
private theorem memProdAddNormalConeGraph_iff_mem_addAdjointImage
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (L : H →L[ℝ] K) {x u : H} {v : K} :
    (u, v) ∈
        ((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) (x, L x) ↔
      u + L.adjoint v ∈ (A + L.adjointImage B) x := by
  have hxGraph : (x, L x) ∈ (L.toLinearMap.graph : Set (H × K)) := by
    simp [LinearMap.mem_graph_iff]
  constructor
  · intro huv
    change (u, v) ∈
      (A × B) (x, L x) + N[(L.toLinearMap.graph : Set (H × K))] (x, L x) at huv
    rw [Set.mem_add] at huv
    rcases huv with ⟨a, ha, n, hn, hsum⟩
    rcases a with ⟨a₁, a₂⟩
    rcases n with ⟨n₁, n₂⟩
    have ha' : a₁ ∈ A x ∧ a₂ ∈ B (L x) := by
      simpa using ha
    have hnOrth :
        (n₁, n₂) ∈
          ((((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ :
            Submodule ℝ (H × K)) : Set (H × K))) := by
      simpa [normalConeGraph_eq_orthogonalGraph (L := L) hxGraph] using hn
    rcases orthogonalGraph_point_eq_pairAdjointNeg (M := L) hnOrth with ⟨w, hw⟩
    change u + L.adjoint v ∈ A x + L.adjointImage B x
    refine Set.mem_add.mpr ?_
    refine ⟨a₁, ha'.1, L.adjoint a₂, ?_, ?_⟩
    · -- Repackage the `B (L x)` witness into the Chapter 16 adjoint-image owner.
      rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]
      exact ⟨a₂, ha'.2, rfl⟩
    · -- The orthogonal-graph witness collapses the lifted sum back to the source operator.
      have huEq : a₁ + n₁ = u := by
        simpa using congrArg Prod.fst hsum
      have hvEq : a₂ + n₂ = v := by
        simpa using congrArg Prod.snd hsum
      have hn₁Eq : n₁ = L.adjoint w := by
        simpa using congrArg Prod.fst hw
      have hn₂Eq : n₂ = -w := by
        simpa using congrArg Prod.snd hw
      subst n₁
      subst n₂
      have huEq' : u = a₁ + L.adjoint w := by
        simpa using huEq.symm
      have hvEq' : v = a₂ - w := by
        simpa [sub_eq_add_neg] using hvEq.symm
      calc
        a₁ + L.adjoint a₂
            = (a₁ + L.adjoint w) + L.adjoint (a₂ - w) := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = u + L.adjoint v := by
              rw [huEq', hvEq']
  · intro hu
    change u + L.adjoint v ∈ A x + L.adjointImage B x at hu
    change (u, v) ∈
      (A × B) (x, L x) + N[(L.toLinearMap.graph : Set (H × K))] (x, L x)
    rw [Set.mem_add] at hu ⊢
    rcases hu with ⟨a, ha, y, hy, huEq⟩
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hy
    rcases hy with ⟨b, hb, hyEq⟩
    subst hyEq
    have hnOrth :
        (L.adjoint (b - v), -(b - v)) ∈
          ((((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ :
            Submodule ℝ (H × K)) : Set (H × K))) := by
      exact pairAdjointNeg_mem_orthogonalGraph (M := L) (b - v)
    have hn :
        (L.adjoint (b - v), -(b - v)) ∈
          N[(L.toLinearMap.graph : Set (H × K))] (x, L x) := by
      simpa [normalConeGraph_eq_orthogonalGraph (L := L) hxGraph] using hnOrth
    refine ⟨(a, b), ?_, (L.adjoint (b - v), -(b - v)), hn, ?_⟩
    · have hab : a ∈ A x ∧ b ∈ B (L x) := ⟨ha, hb⟩
      simpa using hab
    · ext
      · calc
          a + L.adjoint (b - v)
              = (a + L.adjoint b) - L.adjoint v := by
                  simp [sub_eq_add_neg, add_assoc]
          _ = (u + L.adjoint v) - L.adjoint v := by rw [huEq]
          _ = u := by abel_nf
      · simp [sub_eq_add_neg, add_left_comm]

/-- Helper for Theorem 25.3: the normal cone to `gra L` is maximally monotone because the graph
is a nonempty closed convex set. -/
private theorem maximalNormalConeGraph
    (L : H →L[ℝ] K) :
    Maximal IsMonotone (N[(L.toLinearMap.graph : Set (H × K))]) := by
  have hGraph_nonempty : ((L.toLinearMap.graph : Set (H × K))).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [LinearMap.mem_graph_iff]
  have hGraph_closed : IsClosed (L.toLinearMap.graph : Set (H × K)) := by
    simpa [eq_comm, LinearMap.mem_graph_iff] using
      isClosed_eq continuous_snd (L.continuous.comp continuous_fst)
  have hGraph_convex : Convex ℝ (L.toLinearMap.graph : Set (H × K)) := by
    simpa using L.toLinearMap.graph.convex
  simpa using
    (Set.normalCone_isMaximallyMonotone hGraph_nonempty hGraph_closed hGraph_convex)

/-- Helper for Theorem 25.3: a Minty witness for `A + L.adjointImage B` lifts to the product
operator `(A × B) + N[gra L]`. -/
private theorem prodAddNormalConeGraph_mintyWitness_of_addAdjointImageWitness
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (L : H →L[ℝ] K) {z w : H}
    (hrel :
      ∀ ⦃x u : H⦄, u ∈ (A + L.adjointImage B) x → 0 ≤ ⟪z - x, w - u⟫_ℝ) :
    ∀ ⦃p q : H × K⦄,
      q ∈
          (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
            SetValuedOperator (H × K) (H × K)) p →
        0 ≤ ⟪(z, L z) - p, (w, 0) - q⟫_ℝ := by
  intro p q hq
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  have hpGraph : (x, y) ∈ (L.toLinearMap.graph : Set (H × K)) := by
    by_contra hpGraph
    change (u, v) ∈
      (A × B) (x, y) + N[(L.toLinearMap.graph : Set (H × K))] (x, y) at hq
    rw [Set.normalCone_of_not_mem hpGraph] at hq
    rw [Set.mem_add] at hq
    rcases hq with ⟨a, ha, n, hn, hsum⟩
    simp at hn
  have hyEq : y = L x := by
    simpa [LinearMap.mem_graph_iff] using hpGraph
  subst y
  have huTarget : u + L.adjoint v ∈ (A + L.adjointImage B) x := by
    exact
      (memProdAddNormalConeGraph_iff_mem_addAdjointImage
        (A := A) (B := B) L).1 hq
  have hnonneg : 0 ≤ ⟪z - x, w - (u + L.adjoint v)⟫_ℝ := hrel huTarget
  have hinner :
      ⟪(z, L z) - (x, L x), (w, 0) - (u, v)⟫_ℝ =
        ⟪z - x, w - (u + L.adjoint v)⟫_ℝ := by
    calc
      ⟪(z, L z) - (x, L x), (w, 0) - (u, v)⟫_ℝ
          = ⟪z - x, w - u⟫_ℝ + ⟪L z - L x, -v⟫_ℝ := by
              simpa using
                (prodInner_eq_sum
                  (p := (z, L z) - (x, L x))
                  (q := (w, (0 : K)) - (u, v)))
      _ = ⟪z - x, w - u⟫_ℝ - ⟪L (z - x), v⟫_ℝ := by
            simp [sub_eq_add_neg]
      _ = ⟪z - x, w - u⟫_ℝ - ⟪z - x, L.adjoint v⟫_ℝ := by
            rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪z - x, w - (u + L.adjoint v)⟫_ℝ := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (inner_sub_right (z - x) (w - u) (L.adjoint v)).symm
  rwa [hinner]

/-- Helper for Theorem 25.3: maximality of the lifted product-space operator projects to maximality
of `A + L.adjointImage B`. -/
private theorem isMonotone_addAdjointImage_of_maximal
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K) :
    (A + L.adjointImage B).IsMonotone := by
  -- The composite operator inherits monotonicity from the two maximally monotone factors.
  exact
    SetValuedOperator.IsMonotone.add_adjointImage (Maximal.isMonotone hA) L
      (Maximal.isMonotone hB)

/-- Helper for Theorem 25.3: maximality of the lifted product-space operator projects to maximality
of `A + L.adjointImage B`. -/
private theorem maximalAddAdjointImage_ofMaximalProdNormalConeGraph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hProd :
      Maximal IsMonotone (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
        SetValuedOperator (H × K) (H × K))) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  have hMono :
      (A + L.adjointImage B).IsMonotone :=
    isMonotone_addAdjointImage_of_maximal (A := A) (B := B) hA hB L
  rw [SetValuedOperator.maximal_iff_mem_iff]
  intro z w
  constructor
  · intro hw y v hv
    -- The easy direction is just monotonicity of the target composite operator.
    exact (SetValuedOperator.isMonotone_iff _).1 hMono hw hv
  · intro hrel
    have hrelProd :
        ∀ ⦃p q : H × K⦄,
          q ∈
              (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
                SetValuedOperator (H × K) (H × K)) p →
            0 ≤ ⟪(z, L z) - p, (w, 0) - q⟫_ℝ := by
      intro p q hq
      exact
        prodAddNormalConeGraph_mintyWitness_of_addAdjointImageWitness
          (A := A) (B := B) (L := L) hrel hq
    have hmemProd :
        (w, 0) ∈
          (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
            SetValuedOperator (H × K) (H × K)) (z, L z) := by
      exact (SetValuedOperator.Maximal.mem_iff hProd (z, L z) (w, 0)).2 hrelProd
    -- Evaluate the already-proved graph reduction at the zero second component.
    simpa using
      (memProdAddNormalConeGraph_iff_mem_addAdjointImage
        (A := A) (B := B) L).1 hmemProd

/-- Helper for Theorem 25.3: the source regularity hypothesis gives the exact projected `sri`
surface for the product operator `A × B` and the normal cone to `gra L`. -/
private theorem zeroMemSri_fstImageDomFitzpatrickProd_sub_graph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hcone :
      cone (B.dom - L '' A.dom) =
        ((Submodule.span ℝ (B.dom - L '' A.dom)).topologicalClosure : Set K)) :
    let C : Set (H × K) := A.fstImageDomFitzpatrick ×ˢ B.fstImageDomFitzpatrick
    let D : Set (H × K) := (L.toLinearMap.graph : Set (H × K))
    (0 : H × K) ∈ sri (C - D) := by
  dsimp
  have hA_dom_nonempty : A.dom.Nonempty := dom_nonempty_of_maximal A hA
  have hB_dom_nonempty : B.dom.Nonempty := dom_nonempty_of_maximal B hB
  have hA_fitz_nonempty : A.fstImageDomFitzpatrick.Nonempty := by
    rcases hA_dom_nonempty with ⟨x, hx⟩
    exact ⟨x, dom_subset_fst_image_dom_fitzpatrick (A := A) hA hx⟩
  have hB_fitz_nonempty : B.fstImageDomFitzpatrick.Nonempty := by
    rcases hB_dom_nonempty with ⟨x, hx⟩
    exact ⟨x, dom_subset_fst_image_dom_fitzpatrick (A := B) hB hx⟩
  have hclosureA :
      closure A.dom ⊆ closure (convexHull ℝ A.dom) :=
    closure_mono (subset_convexHull ℝ A.dom)
  have hclosureB :
      closure B.dom ⊆ closure (convexHull ℝ B.dom) :=
    closure_mono (subset_convexHull ℝ B.dom)
  have hA_dom_subset :
      A.dom ⊆ A.fstImageDomFitzpatrick := by
    intro x hx
    exact dom_subset_fst_image_dom_fitzpatrick (A := A) hA hx
  have hA_closure :
      A.fstImageDomFitzpatrick ⊆ closure (convexHull ℝ A.dom) := by
    intro x hx
    exact hclosureA (fst_image_dom_fitzpatrick_subset_closure_dom (A := A) hA hx)
  have hB_dom_subset :
      B.dom ⊆ B.fstImageDomFitzpatrick := by
    intro y hy
    exact dom_subset_fst_image_dom_fitzpatrick (A := B) hB hy
  have hB_closure :
      B.fstImageDomFitzpatrick ⊆ closure (convexHull ℝ B.dom) := by
    intro y hy
    exact hclosureB (fst_image_dom_fitzpatrick_subset_closure_dom (A := B) hB hy)
  -- Upgrade from `dom A × dom B` to the larger projected Fitzpatrick domains using the closure
  -- containments supplied by Proposition 21.12.
  exact
    zero_mem_strongRelativeInterior_prod_sub_graph_of_subset_closure_convexHull
      (C := A.fstImageDomFitzpatrick) (D := B.fstImageDomFitzpatrick)
      (A := A.dom) (B := B.dom) (L := L)
      hA_fitz_nonempty hB_fitz_nonempty
      (convexFstImageDomFitzpatrickOfMaximal (T := A) hA)
      (convexFstImageDomFitzpatrickOfMaximal (T := B) hB)
      hA_dom_subset hA_closure hB_dom_subset hB_closure hcone

/-- Helper for Theorem 25.3: the source regularity hypothesis gives the exact projected `sri`
surface for the product operator `A × B` and the normal cone to `gra L`. -/
private theorem zeroMemSriProjectedDifference_prodNormalConeGraph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hcone :
      cone (B.dom - L '' A.dom) =
        ((Submodule.span ℝ (B.dom - L '' A.dom)).topologicalClosure : Set K)) :
    let P : SetValuedOperator (H × K) (H × K) := A × B
    let G : SetValuedOperator (H × K) (H × K) := N[(L.toLinearMap.graph : Set (H × K))]
    (0 : H × K) ∈ sri (Prod.fst '' (ERealFunction.dom (F[P]) - ERealFunction.dom (F[G]))) := by
  dsimp
  let C : Set (H × K) := A.fstImageDomFitzpatrick ×ˢ B.fstImageDomFitzpatrick
  let D : Set (H × K) := (L.toLinearMap.graph : Set (H × K))
  have hProjectedSri :
      (0 : H × K) ∈ sri (C - D) :=
    zeroMemSri_fstImageDomFitzpatrickProd_sub_graph
      (A := A) (B := B) hA hB L hcone
  have hD_nonempty : D.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [D, LinearMap.mem_graph_iff]
  have hD_convex : Convex ℝ D := by
    simpa [D] using L.toLinearMap.graph.convex
  have hD_closed : IsClosed D := by
    simpa [D, eq_comm, LinearMap.mem_graph_iff] using
      isClosed_eq continuous_snd (L.continuous.comp continuous_fst)
  have hP_dom :
      Prod.fst '' ERealFunction.dom (F[(A × B)]) = C := by
    -- Proposition 20.57 identifies the first-coordinate Fitzpatrick domain of the product
    -- operator with the product of the coordinate projections.
    simpa [C, SetValuedOperator.fstImageDomFitzpatrick] using
      fst_image_dom_fitzpatrickFunction_prod A B
        (graph_nonempty_of_maximal hA) (graph_nonempty_of_maximal hB)
  have hG_dom :
      Prod.fst '' ERealFunction.dom (F[N[D]]) = D := by
    -- Example 21.13 rewrites the first-coordinate Fitzpatrick domain of the graph normal cone
    -- back to the graph itself.
    simpa [D, SetValuedOperator.fstImageDomFitzpatrick] using
      Set.fst_image_dom_fitzpatrick_normalCone_eq hD_nonempty hD_closed hD_convex
  rw [fst_image_sub_eq_sub_fst_image, hP_dom, hG_dom]
  exact hProjectedSri

/-- Helper for Theorem 25.3: the projected `sri` regularity for the product operator and the
graph normal cone isolates the remaining same-space maximality step for the lifted operator. -/
private theorem maximalityData_prodNormalConeGraph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K) :
    Maximal IsMonotone ((A × B) : SetValuedOperator (H × K) (H × K)) ∧
      Maximal IsMonotone
        (N[(L.toLinearMap.graph : Set (H × K))] :
          SetValuedOperator (H × K) (H × K)) := by
  -- Package the two maximality inputs once so the later lifted-regularity proof can reuse the
  -- product-space same-space data without rederiving it.
  refine ⟨Maximal.prod hA hB, ?_⟩
  exact maximalNormalConeGraph (H := H) (K := K) L

/-- Helper for Theorem 25.3: the projected `sri` regularity for the product operator and the
graph normal cone isolates the remaining same-space maximality step for the lifted operator. -/
private theorem maximalAdd_of_zeroMemSri_projectedDifference_compiled
    {P G : SetValuedOperator (H × K) (H × K)}
    (hP : Maximal IsMonotone P) (hG : Maximal IsMonotone G)
    (hsri :
      (0 : H × K) ∈
        sri (P.fstImageDomFitzpatrick - G.fstImageDomFitzpatrick)) :
    Maximal IsMonotone (P + G) := by
  -- Route correction: use the canonical same-space support theorem directly instead of the old
  -- private-name bridge back into `Corollary_25_4`.
  exact Maximal.add_of_zero_mem_sri_projectedFitzpatrickDifference hP hG hsri

/-- Helper for Theorem 25.3: the projected `sri` regularity for the product operator and the
graph normal cone isolates the remaining same-space maximality step for the lifted operator. -/
private theorem maximalProdAddNormalConeGraph_ofZeroMemSriProjectedDifference
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H × K) ∈
        sri
          (Prod.fst '' (ERealFunction.dom (F[(A × B)]) -
            ERealFunction.dom (F[N[(L.toLinearMap.graph : Set (H × K))]])))) :
    Maximal IsMonotone
      (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
        SetValuedOperator (H × K) (H × K)) := by
  -- Route correction: the correct proof is to specialize the Chapter 25 same-space `sri`
  -- maximal-sum theorem to `A × B` and `N[gra L]`, not to keep rebuilding local transport API.
  rcases maximalityData_prodNormalConeGraph (A := A) (B := B) hA hB L with ⟨hProd, hGraph⟩
  let P : SetValuedOperator (H × K) (H × K) := A × B
  let G : SetValuedOperator (H × K) (H × K) := N[(L.toLinearMap.graph : Set (H × K))]
  -- Apply the already compiled same-space projected-Fitzpatrick sum theorem directly to the
  -- lifted pair, bypassing the broken `Theorem_25_2` import surface.
  have hsriFitz :
      (0 : H × K) ∈
        sri (P.fstImageDomFitzpatrick - G.fstImageDomFitzpatrick) := by
    simpa
      [P, G, SetValuedOperator.fstImageDomFitzpatrick, fst_image_sub_eq_sub_fst_image] using hsri
  exact
    maximalAdd_of_zeroMemSri_projectedDifference_compiled
      (P := P) (G := G)
      hProd hGraph hsriFitz

/-- Theorem 25.3: let `A : H → 2^H` and `B : K → 2^K` be maximally monotone on real Hilbert
spaces, let `L : H →L[ℝ] K`, and suppose
`cone (dom B - L '' dom A) = closure (span (dom B - L '' dom A))`; then
`A + L^* B L`, realized as `A + L.adjointImage B`, is maximally monotone. -/
theorem Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hcone :
      cone (B.dom - L '' A.dom) =
        ((Submodule.span ℝ (B.dom - L '' A.dom)).topologicalClosure : Set K)) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  have hsri :
      (0 : H × K) ∈
        sri
          (Prod.fst '' (ERealFunction.dom (F[(A × B)]) -
            ERealFunction.dom (F[N[(L.toLinearMap.graph : Set (H × K))]]))) := by
    -- The source geometry produces the exact projected `sri` statement.
    exact zeroMemSriProjectedDifference_prodNormalConeGraph
      (A := A) (B := B) hA hB L hcone
  have hProd :
      Maximal IsMonotone
        (((A × B) + N[(L.toLinearMap.graph : Set (H × K))]) :
          SetValuedOperator (H × K) (H × K)) := by
    -- Apply the remaining same-space maximality step for the lifted product operator.
    exact maximalProdAddNormalConeGraph_ofZeroMemSriProjectedDifference
      (A := A) (B := B) hA hB L hsri
  -- Project the product-space maximality statement back to the source composite operator.
  exact maximalAddAdjointImage_ofMaximalProdNormalConeGraph
    (A := A) (B := B) hA hB L hProd

end

end SetValuedOperator
