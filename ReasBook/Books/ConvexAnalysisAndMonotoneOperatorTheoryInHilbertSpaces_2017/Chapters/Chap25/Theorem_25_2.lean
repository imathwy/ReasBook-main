import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap10.Proposition_10_3
import BauschkeLean.Chap12.Proposition_12_36
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Corollary_15_8
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap15.Theorem_15_27
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap20.Theorem_20_46
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap20.Proposition_20_58
import BauschkeLean.Chap20.Proposition_20_61

open Set
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Helper for Theorem 25.2: maximal monotonicity forces the graph to be nonempty. -/
private theorem graph_nonempty_of_maximal
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    (gra A).Nonempty := by
  by_contra hA_graph
  let B : SetValuedOperator H H := fun _ ↦ ({0} : Set H)
  have hB_mono : B.IsMonotone := by
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    simp [B] at hu hv
    subst u
    subst v
    simp
  have hAB : A ≤ B := by
    intro x u hu
    exfalso
    exact hA_graph ⟨(x, u), by simpa [SetValuedOperator.mem_graph] using hu⟩
  have hzero_mem : 0 ∈ A 0 := (hA.2 hB_mono hAB 0) (by simp [B])
  exact hA_graph ⟨(0, 0), by simpa [SetValuedOperator.mem_graph] using hzero_mem⟩

/-- Helper for Theorem 25.2: the projected Fitzpatrick-domain difference is convex. This freezes
the first-coordinate support surface before later `ri -> sri` transports. -/
private theorem projectedFitzpatrickDifference_convex
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Convex ℝ (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))) := by
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  have hFA :
      properIoi (F[A])
          (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
            A hA_graph (Maximal.isMonotone hA)) ∈
        Γ₀(H × H) :=
    fitzpatrickFunction_mem_gammaZero A hA_graph (Maximal.isMonotone hA)
  have hFB :
      properIoi (F[B])
          (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
            B hB_graph (Maximal.isMonotone hB)) ∈
        Γ₀(H × H) :=
    fitzpatrickFunction_mem_gammaZero B hB_graph (Maximal.isMonotone hB)
  have hdiff_convex :
      Convex ℝ (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])) := by
    -- The ambient Fitzpatrick-domain difference is convex because both effective domains come
    -- from `Γ₀` owners.
    simpa [ERealFunction.dom] using
      hFA.2.convex_effectiveDomain.sub hFB.2.convex_effectiveDomain
  -- Project convexity to the first coordinate once before the lifted product-space rewrite.
  simpa using hdiff_convex.linear_image (ContinuousLinearMap.fst ℝ H H).toLinearMap

/-- Helper for Theorem 25.2: the projected Fitzpatrick-domain `ri` hypothesis already yields an
algebraic-core witness on the raw span subtype. This isolates the part of the source route that
depends only on the Chapter 6 `ri` criterion. -/
private theorem zero_mem_core_projectedFitzpatrickDifference_onSpan
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    let S : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let V : Submodule ℝ H := Submodule.span ℝ (S - ({(0 : H)} : Set H))
    let T : Set V := ((↑) ⁻¹' S)
    (0 : V) ∈ Set.core T := by
  let S : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let V : Submodule ℝ H := Submodule.span ℝ (S - ({(0 : H)} : Set H))
  let T : Set V := ((↑) ⁻¹' S)
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  have hFA :
      properIoi (F[A])
          (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
            A hA_graph (Maximal.isMonotone hA)) ∈
        Γ₀(H × H) :=
    fitzpatrickFunction_mem_gammaZero A hA_graph (Maximal.isMonotone hA)
  have hFB :
      properIoi (F[B])
          (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
            B hB_graph (Maximal.isMonotone hB)) ∈
        Γ₀(H × H) :=
    fitzpatrickFunction_mem_gammaZero B hB_graph (Maximal.isMonotone hB)
  have hS_convex : Convex ℝ S := by
    -- Reuse the frozen convexity of the projected first-coordinate support surface.
    simpa [S] using projectedFitzpatrickDifference_convex hA hB
  have h0S : (0 : H) ∈ S := (Set.mem_relativeInterior_iff.mp hri).1
  have hsub_zero : S - ({(0 : H)} : Set H) = S := by
    -- Subtracting the origin does not change the projected difference set.
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, hyz⟩
      rcases Set.mem_singleton_iff.mp hz with rfl
      have hyx : y = x := by
        simpa using hyz
      simpa [hyx] using hy
    · intro hx
      exact Set.mem_sub.mpr ⟨x, hx, 0, by simp, by simp⟩
  have hcone_span_raw :
      cone (S - ({(0 : H)} : Set H)) =
        (Submodule.span ℝ (S - ({(0 : H)} : Set H)) : Set H) := by
    -- Rewrite the source `ri` statement into the canonical span-subtype form from Chapter 6.
    simpa [S] using (Set.mem_relativeInterior_iff.mp hri).2
  -- The Chapter 6 span-subtype bridge converts the `ri` cone identity into a core witness.
  simpa [S, V, T, hsub_zero] using
    (zero_mem_core_subtype_preimage_iff_cone_eq_span_translate
      (H := H) (C := S) hS_convex h0S).2 hcone_span_raw

/-- Helper for Theorem 25.2: once the translated first-coordinate set contains the origin, taking
the product with a full factor preserves the generated cone. -/
private theorem cone_prod_univ_eq_prod_cone_of_zero_mem
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {S : Set E} (h0 : (0 : E) ∈ S) :
    cone (S ×ˢ (Set.univ : Set K)) = cone S ×ˢ (Set.univ : Set K) := by
  let Cpair : ConvexCone ℝ (E × K) := ConvexCone.hull ℝ (S ×ˢ (Set.univ : Set K))
  let Cprod : ConvexCone ℝ (E × K) :=
    { carrier := cone S ×ˢ (Set.univ : Set K)
      smul_mem' := by
        intro a ha p hp
        exact ⟨(ConvexCone.hull ℝ S).smul_mem ha hp.1, by simp⟩
      add_mem' := by
        intro p hp q hq
        exact ⟨(ConvexCone.hull ℝ S).add_mem hp.1 hq.1, by simp⟩ }
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    -- Any convex cone containing `S × univ` contains the first-coordinate cone as well.
    have hp' : (x, y) ∈ (Cprod : Set (E × K)) := by
      exact
        ConvexCone.hull_min
          (C := Cprod)
          (by
            intro q hq
            exact ⟨ConvexCone.subset_hull hq.1, by simp⟩)
          hp
    simpa [Cprod, Set.mem_prod] using hp'
  · intro hp
    -- Recover some lifted point with first coordinate `x`, then shift its free coordinate.
    have hx : x ∈ cone S := by
      simpa [Set.mem_prod] using hp
    have hsubset :
        S ⊆ (Cpair.map (LinearMap.fst ℝ E K) : Set E) := by
      intro s hs
      exact
        ConvexCone.mem_map.2
          ⟨(s, (0 : K)), ConvexCone.subset_hull ⟨hs, by simp⟩, by simp⟩
    have hxproj : x ∈ Cpair.map (LinearMap.fst ℝ E K) := by
      exact ConvexCone.hull_min (C := Cpair.map (LinearMap.fst ℝ E K)) hsubset hx
    rcases ConvexCone.mem_map.1 hxproj with ⟨q, hq, hqfst⟩
    rcases q with ⟨x', k⟩
    have hx' : x' = x := by
      simpa using hqfst
    subst x'
    have hzero_shift : ((0 : E), y - k) ∈ (Cpair : Set (E × K)) := by
      exact ConvexCone.subset_hull ⟨h0, by simp⟩
    have hsum : (x, k) + ((0 : E), y - k) ∈ (Cpair : Set (E × K)) := add_mem hq hzero_shift
    simpa [Cpair] using hsum

/-- Helper for Theorem 25.2: translating a product with a full factor is the product of the
translated first-coordinate set with that same full factor. -/
private theorem sub_prod_univ_singleton_eq
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (S : Set E) (x : E) (y : K) :
    (S ×ˢ (Set.univ : Set K)) - ({(x, y)} : Set (E × K)) =
      (S - ({x} : Set E)) ×ˢ (Set.univ : Set K) := by
  ext p
  rcases p with ⟨z, t⟩
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases Set.mem_singleton_iff.mp hv with rfl
    refine ⟨?_, by simp⟩
    exact
      Set.mem_sub.mpr
        ⟨u.1, hu.1, x, by simp, by simpa using congrArg Prod.fst huv⟩
  · rintro ⟨hz, -⟩
    rcases Set.mem_sub.mp hz with ⟨u, hu, w, hw, huw⟩
    rcases Set.mem_singleton_iff.mp hw with hwx
    subst w
    refine Set.mem_sub.mpr ⟨(u, t + y), ⟨hu, by simp⟩, (x, y), by simp, ?_⟩
    ext <;> simp [huw]

/-- Helper for Theorem 25.2: taking the product with a full factor preserves algebraic core in the
first coordinate. This is the core analogue of the product-space regularity rewrites used later in
the lifted Chapter 15 bridge. -/
private theorem core_prod_univ_eq_prod_core
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (S : Set E) :
    Set.core (S ×ˢ (Set.univ : Set K)) = Set.core S ×ˢ (Set.univ : Set K) := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    rw [Set.mem_core_iff] at hp
    rcases hp with ⟨hxy, hcone⟩
    have hx : x ∈ S := hxy.1
    have hzero : (0 : E) ∈ S - ({x} : Set E) := by
      exact Set.mem_sub.mpr ⟨x, hx, x, by simp, by simp⟩
    have hprod :
        cone (S - ({x} : Set E)) ×ˢ (Set.univ : Set K) = (Set.univ : Set (E × K)) := by
      calc
        cone (S - ({x} : Set E)) ×ˢ (Set.univ : Set K) =
            cone ((S - ({x} : Set E)) ×ˢ (Set.univ : Set K)) := by
              symm
              exact cone_prod_univ_eq_prod_cone_of_zero_mem (K := K) hzero
        _ = (Set.univ : Set (E × K)) := by
              rw [sub_prod_univ_singleton_eq] at hcone
              exact hcone
    change x ∈ Set.core S ∧ y ∈ (Set.univ : Set K)
    refine ⟨?_, by simp⟩
    rw [Set.mem_core_iff]
    refine ⟨hx, ?_⟩
    ext z
    constructor
    · intro _
      simp
    · intro _
      have hzpair :
          (z, (0 : K)) ∈ cone (S - ({x} : Set E)) ×ˢ (Set.univ : Set K) := by
        have : (z, (0 : K)) ∈ (Set.univ : Set (E × K)) := by simp
        rwa [← hprod] at this
      exact hzpair.1
  · intro hp
    rcases hp with ⟨hxcore, -⟩
    rw [Set.mem_core_iff] at hxcore
    rcases hxcore with ⟨hx, hcone⟩
    have hzero : (0 : E) ∈ S - ({x} : Set E) := by
      exact Set.mem_sub.mpr ⟨x, hx, x, by simp, by simp⟩
    have hprod :
        cone ((S - ({x} : Set E)) ×ˢ (Set.univ : Set K)) = (Set.univ : Set (E × K)) := by
      calc
        cone ((S - ({x} : Set E)) ×ˢ (Set.univ : Set K)) =
            cone (S - ({x} : Set E)) ×ˢ (Set.univ : Set K) := by
              exact cone_prod_univ_eq_prod_cone_of_zero_mem (K := K) hzero
        _ = (Set.univ : Set (E × K)) := by
              ext q
              rcases q with ⟨u, v⟩
              constructor
              · intro _
                simp
              · intro _
                refine ⟨?_, by simp⟩
                rw [hcone]
                simp
    rw [Set.mem_core_iff]
    refine ⟨⟨hx, by simp⟩, ?_⟩
    rw [sub_prod_univ_singleton_eq]
    exact hprod

/-- Helper for Theorem 25.2: if the source set contains the origin, then the closed linear span of
`S × univ` is exactly the product of the closed linear span of `S` with the full second factor. -/
private theorem closure_span_prod_univ_eq_prod_closure_span_of_zero_mem
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {S : Set E} (h0 : (0 : E) ∈ S) :
    ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (E × K)) =
      (((Submodule.span ℝ S).topologicalClosure : Set E) ×ˢ (Set.univ : Set K)) := by
  have hspan_le :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) ≤
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    -- The lifted generators already lie in the obvious product span.
    simpa [Submodule.span_univ] using
      (Submodule.span_prod_le (R := ℝ) S (Set.univ : Set K))
  have hspan_ge :
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) ≤
        Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := by
    have hsubset :
        LinearMap.inl ℝ E K '' S ∪ LinearMap.inr ℝ E K '' (Set.univ : Set K) ⊆
          S ×ˢ (Set.univ : Set K) := by
      intro p hp
      rcases hp with hp | hp
      · rcases hp with ⟨x, hx, rfl⟩
        exact ⟨hx, by simp⟩
      · rcases hp with ⟨y, -, rfl⟩
        exact ⟨h0, by simp⟩
    -- The free factor is generated by the `inr` image because the first coordinate can be fixed at
    -- the origin.
    calc
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) =
          Submodule.span ℝ
            (LinearMap.inl ℝ E K '' S ∪ LinearMap.inr ℝ E K '' (Set.univ : Set K)) := by
              symm
              simpa [Submodule.span_univ] using
                (LinearMap.span_inl_union_inr (R := ℝ) (M := E) (M₂ := K)
                  (s := S) (t := (Set.univ : Set K)))
      _ ≤ Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := Submodule.span_mono hsubset
  have hspan_eq :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) =
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    exact le_antisymm hspan_le hspan_ge
  -- Normalize the product closure after freezing the span equality.
  rw [hspan_eq]
  change closure (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (E × K))) =
    (((Submodule.span ℝ S).topologicalClosure : Set E) ×ˢ (Set.univ : Set K))
  have hprod_set :
      (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (E × K))) =
        ((Submodule.span ℝ S : Set E) ×ˢ (Set.univ : Set K)) := by
    rfl
  rw [hprod_set, closure_prod_eq]
  simp

/-- Helper for Theorem 25.2: the conical hull commutes with a continuous linear equivalence. This
packages the first-coordinate sign change used later on the raw span-level support carrier. -/
private abbrev fitzpatrickFiberwiseInfimalConvolution
    {A B : SetValuedOperator H H} : H × H → EReal :=
  fun p ↦
    ((fun v : H ↦ F[A] (p.1, v)) □
      fun v ↦ F[B] (p.1, v)) p.2

/-- Helper for Theorem 25.2: package the Fitzpatrick owner of a maximal monotone operator into the
canonical `Γ₀` interface used by the Chapter 15 duality API. -/
private abbrev fitzpatrickIoi
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    H × H → Set.Ioi (⊥ : EReal) :=
  properIoi (F[A])
    (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
      A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA))

/-- Helper for Theorem 25.2: the packaged Fitzpatrick owner belongs to `Γ₀(H × H)`. -/
private theorem fitzpatrickIoi_mem_gammaZero
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    fitzpatrickIoi hA ∈ Γ₀(H × H) := by
  -- Re-express the standard Fitzpatrick `Γ₀` statement through the packaged owner spelling.
  simpa [fitzpatrickIoi] using
    fitzpatrickFunction_mem_gammaZero
      A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA)

/-- Helper for Theorem 25.2: the first-last lifted Fitzpatrick pullback used in the zero-slice
exactness package. -/
private abbrev liftedFirstLastFitzpatrickIoi
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
  fitzpatrickIoi hA ∘ ERealFunction.firstLastPullbackMap (H := H) (K := H)

/-- Helper for Theorem 25.2: the first-difference lifted Fitzpatrick pullback used in the
zero-slice exactness package. -/
private abbrev liftedFirstDifferenceFitzpatrickIoi
    {B : SetValuedOperator H H} (hB : Maximal IsMonotone B) :
    ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
  fitzpatrickIoi hB ∘ ERealFunction.firstDifferencePullbackMap (H := H) (K := H)

/-- Helper for Theorem 25.2: the lifted separable sum whose zero-second conjugate slice controls
the dual owner of the Fitzpatrick infimal convolution. -/
private abbrev liftedFitzpatrickPullbackSum
    {A B : SetValuedOperator H H}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    ((H × H) × H) → EReal :=
  fun q ↦
    (liftedFirstLastFitzpatrickIoi hA q : EReal) +
      (liftedFirstDifferenceFitzpatrickIoi hB q : EReal)

/-- Helper for Theorem 25.2: the first-last lifted Fitzpatrick pullback stays in `Γ₀`. -/
private theorem liftedFirstLastFitzpatrickIoi_mem_gammaZero
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    liftedFirstLastFitzpatrickIoi hA ∈ Γ₀(((H × H) × H)) := by
  -- Pull back the packaged Fitzpatrick owner along the canonical first-last map.
  simpa [liftedFirstLastFitzpatrickIoi, Function.comp] using
    ERealFunction.firstLastPullback_mem_gammaZero
      (H := H) (K := H) (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA)

/-- Helper for Theorem 25.2: the first-difference lifted Fitzpatrick pullback stays in `Γ₀`. -/
private theorem liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero
    {B : SetValuedOperator H H} (hB : Maximal IsMonotone B) :
    liftedFirstDifferenceFitzpatrickIoi hB ∈ Γ₀(((H × H) × H)) := by
  -- Pull back the packaged Fitzpatrick owner along the canonical first-difference map.
  simpa [liftedFirstDifferenceFitzpatrickIoi, Function.comp] using
    ERealFunction.firstDifferencePullback_mem_gammaZero
      (H := H) (K := H) (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB)

/-- Helper for Theorem 25.2: the literal lifted effective-domain difference is exactly the
`S × univ × univ` surface coming from the projected Fitzpatrick-domain difference. -/
private theorem liftedFitzpatrickDifference_eq_firstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
        effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
      ((((Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))) ×ˢ
          (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
  -- Freeze the exact lifted surface once so later closed-span transport no longer switches
  -- between two equivalent spellings.
  simpa [liftedFirstLastFitzpatrickIoi, liftedFirstDifferenceFitzpatrickIoi, fitzpatrickIoi,
    Function.comp, ERealFunction.dom] using
    ERealFunction.lifted_difference_eq_firstProjection_product_univ
      (φ := fitzpatrickIoi hA) (ψ := fitzpatrickIoi hB)

/-- Helper for Theorem 25.2: the literal lifted effective-domain difference surface is convex.
This freezes the ambient support set before the remaining closed-span transport is attempted. -/
private theorem liftedFitzpatrickDifference_convex
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Convex ℝ
      (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
        effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)) := by
  -- The lifted surface is the difference of two convex effective domains coming from `Γ₀`
  -- Fitzpatrick pullbacks.
  exact
    (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA).2.convex_effectiveDomain.sub
      (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB).2.convex_effectiveDomain

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the closed linear span of the
literal lifted support surface is exactly the projected closed span in the first coordinate times
two free factors. -/
private theorem liftedProjectedClosedSpan_eq_firstProjectionClosedSpanProduct_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let S : Set (((H × H) × H)) :=
      effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
        effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)
    ((Submodule.span ℝ S).topologicalClosure : Set (((H × H) × H))) =
      (((((Submodule.span ℝ S0).topologicalClosure : Set H) ×ˢ
          (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let P : Set (H × H) := ((S0 ×ˢ (Set.univ : Set H)) : Set (H × H))
  let S : Set (((H × H) × H)) :=
    effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
      effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)
  have h0S0 : (0 : H) ∈ S0 := (Set.mem_relativeInterior_iff.mp hri).1
  have h0P : (0 : H × H) ∈ P := by
    exact ⟨h0S0, by simp⟩
  have hsurface :
      S = (P ×ˢ (Set.univ : Set H)) := by
    -- Rewrite the literal lifted difference once into the product spelling used for the closure
    -- computation.
    simpa [S, S0, P] using liftedFitzpatrickDifference_eq_firstProjectionProduct hA hB
  have hclosureP :
      ((Submodule.span ℝ P).topologicalClosure : Set (H × H)) =
        (((Submodule.span ℝ S0).topologicalClosure : Set H) ×ˢ (Set.univ : Set H)) := by
    -- First normalize the one-step product `S0 × univ`.
    simpa [P] using
      closure_span_prod_univ_eq_prod_closure_span_of_zero_mem
        (E := H) (K := H) h0S0
  -- Then add the second free factor to reach the literal lifted surface.
  calc
    ((Submodule.span ℝ S).topologicalClosure : Set (((H × H) × H))) =
        ((Submodule.span ℝ (P ×ˢ (Set.univ : Set H))).topologicalClosure :
          Set (((H × H) × H))) := by
            rw [hsurface]
    _ = (((Submodule.span ℝ P).topologicalClosure : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
          exact
            closure_span_prod_univ_eq_prod_closure_span_of_zero_mem
              (E := H × H) (K := H) h0P
    _ = (((((Submodule.span ℝ S0).topologicalClosure : Set H) ×ˢ
            (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
          rw [hclosureP]

/-- Helper for Theorem 25.2: the Chapter 25 owner is exactly the first-projection infimal
postcomposition of the lifted Fitzpatrick pullback sum. -/
private theorem
    fitzpatrickFiberwiseInfimalConvolution_eq_infimalPostcomposition_liftedFitzpatrickPullbackSum
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B) =
      Prod.fst ▷ liftedFitzpatrickPullbackSum hA hB := by
  -- Rewrite the textbook fiberwise infimal convolution into the canonical lifted Chapter 15 form.
  simpa [fitzpatrickFiberwiseInfimalConvolution, liftedFitzpatrickPullbackSum,
    liftedFirstLastFitzpatrickIoi, liftedFirstDifferenceFitzpatrickIoi, fitzpatrickIoi,
    Function.comp] using
    (ERealFunction.secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
      (H := H) (K := H) (fitzpatrickIoi hA) (fitzpatrickIoi hB))

/-- Helper for Theorem 25.2: the pairing splits across addition in the second coordinate. -/
private theorem pairing_add_right (x u₁ u₂ : H) :
    pairing (x, u₁ + u₂) = pairing (x, u₁) + pairing (x, u₂) := by
  -- Expand the right pairing once so later infimal-convolution estimates can reuse this identity.
  change (((⟪x, u₁ + u₂⟫_ℝ : ℝ) : EReal)) =
    (((⟪x, u₁⟫_ℝ : ℝ) : EReal)) + (((⟪x, u₂⟫_ℝ : ℝ) : EReal))
  rw [inner_add_right, EReal.coe_add]

/-- Helper for Theorem 25.2: Jensen convexity of an `EReal`-valued function is equivalent to
convexity of its real-height epigraph. -/
private theorem convex_epigraph_of_isConvex_ereal
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {g : E → EReal} (hg_conv : IsConvex g) :
    Convex ℝ (epigraph g) := by
  -- Rewrite epigraph convexity through the Jensen inequality already packaged in `IsConvex`.
  refine (convex_epigraph_iff_jensen_on_dom g).2 ?_
  intro x y hx hy a ha₀ ha₁
  exact hg_conv ha₀.le ha₁.le

/-- Helper for Theorem 25.2: a proper `EReal`-valued function with convex epigraph is convex. -/
private theorem isConvex_of_convex_epigraph_of_isProper
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {g : E → EReal} (hconv : Convex ℝ (epigraph g)) (hproper : IsProper g) :
    IsConvex g := by
  -- Convert epigraph convexity back to Jensen convexity by splitting domain and endpoint cases.
  intro x y a ha₀ ha₁
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    rw [hcoef_eq]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha₀ (Ne.symm ha_zero)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha₁ ha_one
  by_cases hx : x ∈ ERealFunction.dom g
  · by_cases hy : y ∈ ERealFunction.dom g
    · -- On the domain, convexity of the epigraph is exactly Jensen convexity.
      simpa only [hcoef_eq] using
        (convex_epigraph_iff_jensen_on_dom g).1 hconv hx hy ha_pos ha_lt_one
    · -- Outside the domain the second term is `⊤`, so the right-hand side is automatically `⊤`.
      have hy_top : g y = ⊤ := by
        simpa [mem_dom_iff_ne_top] using hy
      have hx_term_ne_bot : (a : EReal) * g x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), ?_, Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha₀)⟩
        exact Or.inr (hproper.1 x)
      rw [hcoef_eq, hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
      rw [EReal.add_top_of_ne_bot hx_term_ne_bot]
      exact le_top
  · -- Outside the domain the first term is `⊤`, so the right-hand side is again `⊤`.
    have hx_top : g x = ⊤ := by
      simpa [mem_dom_iff_ne_top] using hx
    have hy_term_ne_bot : ((1 - a : ℝ) : EReal) * g y ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (EReal.coe_ne_bot (1 - a)), ?_, Or.inl (EReal.coe_ne_top (1 - a)),
        Or.inl (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha₁))⟩
      exact Or.inr (hproper.1 y)
    rw [hx_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos), hcoef_eq]
    rw [EReal.top_add_of_ne_bot hy_term_ne_bot]
    exact le_top

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, Corollary 15.8
rewrites the conjugate of the fiberwise Fitzpatrick owner as the infimal convolution of the
conjugate slices. This isolates the exact dual normal form that later contact arguments need. -/
private theorem conjugate_fitzpatrickFiberwiseInfimalConvolution_apply_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (u x : H) :
    (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗ (u, x) =
      ((fun u₁ : H ↦ (F[A])∗ (u₁, x)) □
        fun u₁ ↦ (F[B])∗ (u₁, x)) u := by
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  let FA : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        A hA_graph (Maximal.isMonotone hA))
  let FB : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[B])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        B hB_graph (Maximal.isMonotone hB))
  have hFA : FA ∈ Γ₀(H × H) := by
    -- Package the Fitzpatrick owners into the `Γ₀` form required by Corollary 15.8.
    simpa [FA] using
      fitzpatrickFunction_mem_gammaZero A hA_graph (Maximal.isMonotone hA)
  have hFB : FB ∈ Γ₀(H × H) := by
    -- The same packaging applies to the second operator.
    simpa [FB] using
      fitzpatrickFunction_mem_gammaZero B hB_graph (Maximal.isMonotone hB)
  have hsri' :
      (0 : H) ∈ sri (Prod.fst '' (ERealFunction.effectiveDomain FA - ERealFunction.effectiveDomain FB)) := by
    -- Re-express the source `sri` hypothesis through the canonical `Γ₀` effective domains.
    simpa [FA, FB, ERealFunction.dom] using hsri
  -- Corollary 15.8 gives the desired exact dual normal form.
  simpa [fitzpatrickFiberwiseInfimalConvolution, FA, FB] using
    ERealFunction.conjugate_secondVariableFiberwiseInfimalConvolution_eq_infimalConvolution_conjugateSlices_apply
      FA FB hFA hFB hsri' u x

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, the transpose-conjugate
of the fiberwise Fitzpatrick owner dominates the pairing. This is the dual inequality `(25.5)`
once Corollary 15.8 has normalized the owner. -/
private theorem pairing_le_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (x u : H) :
    pairing (x, u) ≤ ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) := by
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  -- Rewrite the dual owner through the slice formula from Corollary 15.8.
  rw [transpose_apply]
  rw [conjugate_fitzpatrickFiberwiseInfimalConvolution_apply_of_zero_mem_sri hA hB hsri u x]
  rw [ERealFunction.infimalConvolution_apply]
  refine le_iInf fun u₁ ↦ ?_
  -- Compare the pairing with each infimal-convolution summand using Proposition 20.61(iii).
  calc
    pairing (x, u) = pairing (x, u₁) + pairing (x, u - u₁) := by
      simpa [sub_eq_add_neg, add_assoc] using pairing_add_right x u₁ (u - u₁)
    _ ≤ (F[A])∗ (u₁, x) + (F[B])∗ (u - u₁, x) := by
      exact add_le_add
        (by
          simpa [transpose_apply] using
            inner_le_conjugateTranspose_fitzpatrickFunction
              A hA_graph (Maximal.isMonotone hA) x u₁)
        (by
          simpa [transpose_apply] using
            inner_le_conjugateTranspose_fitzpatrickFunction
              B hB_graph (Maximal.isMonotone hB) x (u - u₁))

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, the lifted
Fitzpatrick pullbacks already satisfy the exact product-space `sri` regularity used by the
Chapter 15 owner theorems. This isolates the lifted normalization from the later closed-span/core
transport. -/
private theorem zero_mem_sri_liftedFitzpatrickDifference_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    let FA : H × H → Set.Ioi (⊥ : EReal) :=
      properIoi (F[A])
        (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
          A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA))
    let FB : H × H → Set.Ioi (⊥ : EReal) :=
      properIoi (F[B])
        (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
          B (graph_nonempty_of_maximal hB) (Maximal.isMonotone hB))
    (0 : ((H × H) × H)) ∈
      sri
        (effectiveDomain
            (FA ∘ ERealFunction.firstLastPullbackMap (H := H) (K := H)) -
          effectiveDomain
            (FB ∘ ERealFunction.firstDifferencePullbackMap (H := H) (K := H))) := by
  let FA : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA))
  let FB : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[B])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        B (graph_nonempty_of_maximal hB) (Maximal.isMonotone hB))
  have hFA : FA ∈ Γ₀(H × H) := by
    -- Package the first Fitzpatrick owner into the `Γ₀` surface expected by the lifted Chapter 15
    -- regularity theorem.
    simpa [FA] using
      fitzpatrickFunction_mem_gammaZero A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA)
  have hFB : FB ∈ Γ₀(H × H) := by
    -- The second Fitzpatrick owner admits the same packaging.
    simpa [FB] using
      fitzpatrickFunction_mem_gammaZero B (graph_nonempty_of_maximal hB) (Maximal.isMonotone hB)
  -- The theorem-local lifted-difference file transports the projected `sri` hypothesis directly
  -- to the product-space pullbacks behind the owner `Fsum`.
  simpa [FA, FB, Function.comp] using
    ERealFunction.zero_mem_sri_lifted_difference_of_zero_mem_sri_firstProjection_difference
      FA FB hFA hFB hsri

/-- Helper for Theorem 25.2: the fiberwise Fitzpatrick infimal convolution dominates the pairing.
This is the source inequality `F ≥ ⟨·, ·⟩` for the Chapter 25 owner `F`. -/
private theorem pairing_le_fitzpatrickFiberwiseInfimalConvolution
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (x u : H) :
    pairing (x, u) ≤ fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B) (x, u) := by
  -- Estimate the infimal convolution termwise using the Fitzpatrick lower bounds of `A` and `B`.
  rw [fitzpatrickFiberwiseInfimalConvolution, ERealFunction.infimalConvolution_apply]
  refine le_iInf fun u₁ ↦ ?_
  calc
    pairing (x, u) = pairing (x, u₁) + pairing (x, u - u₁) := by
      simpa [sub_eq_add_neg, add_assoc] using pairing_add_right x u₁ (u - u₁)
    _ ≤ F[A] (x, u₁) + F[B] (x, u - u₁) := by
      exact add_le_add
        (Maximal.inner_le_fitzpatrickFunction hA x u₁)
        (Maximal.inner_le_fitzpatrickFunction hB x (u - u₁))

/-- Helper for Theorem 25.2: every graph point of `A + B` is a primal contact point of the
fiberwise Fitzpatrick infimal convolution owner. -/
private theorem fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_mem_graph_add
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u : H} (hu : (x, u) ∈ (A + B).graph) :
    fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B) (x, u) = pairing (x, u) := by
  rw [SetValuedOperator.mem_graph] at hu
  rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
  refine le_antisymm ?_ (pairing_le_fitzpatrickFiberwiseInfimalConvolution hA hB x (u₁ + u₂))
  -- Evaluate the infimal convolution at the concrete graph splitting `u₁ + u₂ = u₁ + u₂`.
  rw [fitzpatrickFiberwiseInfimalConvolution, ERealFunction.infimalConvolution_apply]
  have hsub : (u₁ + u₂) - u₁ = u₂ := by
    abel_nf
  calc
    (⨅ v : H, F[A] (x, v) + F[B] (x, (u₁ + u₂) - v)) ≤
        F[A] (x, u₁) + F[B] (x, (u₁ + u₂) - u₁) := by
          exact iInf_le (fun v : H ↦ F[A] (x, v) + F[B] (x, (u₁ + u₂) - v)) u₁
    _ = pairing (x, u₁) + pairing (x, u₂) := by
          rw [SetValuedOperator.fitzpatrickFunction_eq_inner_of_mem_graph
              (A := A) (Maximal.isMonotone hA) hu₁]
          rw [hsub]
          rw [SetValuedOperator.fitzpatrickFunction_eq_inner_of_mem_graph
              (A := B) (Maximal.isMonotone hB) hu₂]
    _ = pairing (x, u₁ + u₂) := by
          simpa using (pairing_add_right x u₁ u₂).symm

/-- Helper for Theorem 25.2: once a contact point of the fiberwise dual owner splits into two
Fitzpatrick contact points, the corresponding pair belongs to `gra (A + B)`. -/
private theorem mem_graph_add_of_fitzpatrickSplitContact
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u u₁ : H}
    (hAu₁ : ((F[A])∗)ᵀ (x, u₁) = pairing (x, u₁))
    (hBu₂ : ((F[B])∗)ᵀ (x, u - u₁) = pairing (x, u - u₁)) :
    (x, u) ∈ (A + B).graph := by
  -- Convert the two summand contact equalities into graph membership of `A` and `B`, then add.
  have hu₁_graph : (x, u₁) ∈ A.graph := by
    exact (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hA x u₁).2 hAu₁
  have hu₂_graph : (x, u - u₁) ∈ B.graph := by
    exact
      (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hB x (u - u₁)).2
        hBu₂
  rw [SetValuedOperator.mem_graph] at hu₁_graph hu₂_graph ⊢
  exact Set.mem_add.mpr ⟨u₁, hu₁_graph, u - u₁, hu₂_graph, by simp⟩

/-- Helper for Theorem 25.2: a split formula for the transpose-conjugate of the fiberwise owner
immediately yields the dual pairing lower bound needed by Theorem 20.46. -/
private theorem pairing_le_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_of_split
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u u₁ : H}
    (hsplit :
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
        ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁)) :
    pairing (x, u) ≤
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) := by
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  -- Compare each split term with the pairing and then rewrite by the supplied split identity.
  calc
    pairing (x, u) = pairing (x, u₁) + pairing (x, u - u₁) := by
      simpa [sub_eq_add_neg, add_assoc] using pairing_add_right x u₁ (u - u₁)
    _ ≤ ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) := by
      exact add_le_add
        (inner_le_conjugateTranspose_fitzpatrickFunction
          A hA_graph (Maximal.isMonotone hA) x u₁)
        (inner_le_conjugateTranspose_fitzpatrickFunction
          B hB_graph (Maximal.isMonotone hB) x (u - u₁))
    _ = ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) := hsplit.symm

/-- Helper for Theorem 25.2: every concrete split `u = u₁ + (u - u₁)` gives an upper bound for
the transpose-conjugate of the fiberwise Fitzpatrick owner. This is the easy half of the source
duality route, before any exactness or attainment input is used. -/
private theorem conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_le_split
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (x u u₁ : H) :
    ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) ≤
      ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) := by
  let FA : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA))
  let FB : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[B])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        B (graph_nonempty_of_maximal hB) (Maximal.isMonotone hB))
  have hFA : FA ∈ Γ₀(H × H) := by
    -- Package the first Fitzpatrick owner into `Γ₀` so the local lifted duality API applies.
    simpa [FA] using
      fitzpatrickFunction_mem_gammaZero A (graph_nonempty_of_maximal hA) (Maximal.isMonotone hA)
  have hFB : FB ∈ Γ₀(H × H) := by
    -- The second Fitzpatrick owner admits the same `Γ₀` packaging.
    simpa [FB] using
      fitzpatrickFunction_mem_gammaZero B (graph_nonempty_of_maximal hB) (Maximal.isMonotone hB)
  let LiftA : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun q ↦ FA (q.1.1, q.2)
  let LiftB : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun q ↦ FB (q.1.1, q.1.2 - q.2)
  let Lift : ((H × H) × H) → EReal := fun q ↦ (LiftA q : EReal) + (LiftB q : EReal)
  have hrepr :
      fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B) = Prod.fst ▷ Lift := by
    -- Normalize the Chapter 25 owner to the lifted first-projection infimal postcomposition.
    simpa [fitzpatrickFiberwiseInfimalConvolution, Lift, LiftA, LiftB, FA, FB] using
      (ERealFunction.secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
        (H := H) (K := H) FA FB)
  have hsum_le :
      Lift∗ (((u, x), (0 : H))) ≤
        (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((u, x), (0 : H))) := by
    -- The conjugate of a pointwise sum is always bounded above by the infimal convolution of the
    -- two conjugates.
    simpa [Lift, LiftA, LiftB] using
      (ERealFunction.conjugate_add_le_infimalConvolution_conjugate LiftA LiftB
        (((u, x), (0 : H))))
  have hzeroSlice :
      (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((u, x), (0 : H))) =
        ((fun v : H ↦ (F[A])∗ (v, x)) □ fun v ↦ (F[B])∗ (v, x)) u := by
    -- Collapse the lifted dual infimal convolution to the first-variable split formula.
    simpa [LiftA, LiftB, FA, FB] using
      (ERealFunction.zeroSecond_lifted_dualInfimalConvolution_eq_firstVariableInfimalConvolution
        (φ := FA) (ψ := FB) hFA hFB (u, x))
  -- Evaluate the dual upper bound at the chosen split point `u₁`.
  rw [transpose_apply, hrepr,
    ERealFunction.conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local Lift]
  calc
    Lift∗ (((u, x), (0 : H))) ≤
        (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((u, x), (0 : H))) := hsum_le
    _ = ((fun v : H ↦ (F[A])∗ (v, x)) □ fun v ↦ (F[B])∗ (v, x)) u := hzeroSlice
    _ ≤ (F[A])∗ (u₁, x) + (F[B])∗ (u - u₁, x) := by
        rw [ERealFunction.infimalConvolution_apply]
        exact iInf_le (fun v : H ↦ (F[A])∗ (v, x) + (F[B])∗ (u - v, x)) u₁

/-- Helper for Theorem 25.2: if a dual split already realizes the total pairing, then each
Fitzpatrick summand is itself at contact. This isolates the componentwise equality needed to
recover graph membership of `A + B` from an attained split. -/
private theorem splitConjugateContact_of_sum_eq_pairing
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u u₁ : H}
    (hsum :
      ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) = pairing (x, u)) :
    ((F[A])∗)ᵀ (x, u₁) = pairing (x, u₁) ∧
      ((F[B])∗)ᵀ (x, u - u₁) = pairing (x, u - u₁) := by
  let a : EReal := ((F[A])∗)ᵀ (x, u₁)
  let b : EReal := ((F[B])∗)ᵀ (x, u - u₁)
  let pa : EReal := pairing (x, u₁)
  let pb : EReal := pairing (x, u - u₁)
  have hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal hA
  have hB_graph : (gra B).Nonempty := graph_nonempty_of_maximal hB
  have hpa_le : pa ≤ a := by
    -- Proposition 20.61(iii) supplies the lower bound for the first split summand.
    simpa [a, pa] using
      inner_le_conjugateTranspose_fitzpatrickFunction
        A hA_graph (Maximal.isMonotone hA) x u₁
  have hpb_le : pb ≤ b := by
    -- The same lower bound applies to the second split summand.
    simpa [b, pb] using
      inner_le_conjugateTranspose_fitzpatrickFunction
        B hB_graph (Maximal.isMonotone hB) x (u - u₁)
  have hpair_sum : pa + pb = pairing (x, u) := by
    -- Normalize the total pairing into the same split coordinates.
    simpa [pa, pb, sub_eq_add_neg, add_assoc] using
      (pairing_add_right x u₁ (u - u₁)).symm
  have hab_sum : a + b = pa + pb := by
    calc
      a + b = pairing (x, u) := by simpa [a, b] using hsum
      _ = pa + pb := hpair_sum.symm
  have hpa_ne_bot : pa ≠ ⊥ := by
    simpa [pa, pairing_apply] using (EReal.coe_ne_bot (⟪x, u₁⟫_ℝ))
  have hpb_ne_bot : pb ≠ ⊥ := by
    simpa [pb, pairing_apply] using (EReal.coe_ne_bot (⟪x, u - u₁⟫_ℝ))
  have ha_ne_bot : a ≠ ⊥ := by
    intro ha_bot
    rw [ha_bot] at hpa_le
    exact not_le_of_gt (by simpa [pa, pairing_apply] using (EReal.bot_lt_coe (⟪x, u₁⟫_ℝ))) hpa_le
  have hb_ne_bot : b ≠ ⊥ := by
    intro hb_bot
    rw [hb_bot] at hpb_le
    exact not_le_of_gt
      (by simpa [pb, pairing_apply] using (EReal.bot_lt_coe (⟪x, u - u₁⟫_ℝ))) hpb_le
  have ha_ne_top : a ≠ ⊤ := by
    intro ha_top
    have hab_top : a + b = ⊤ := by
      rw [ha_top]
      exact EReal.top_add_of_ne_bot hb_ne_bot
    have hpair_ne_top : pa + pb ≠ ⊤ := by
      simpa [pa, pb, pairing_apply] using
        (EReal.coe_ne_top (⟪x, u₁⟫_ℝ + ⟪x, u - u₁⟫_ℝ))
    exact hpair_ne_top (hab_sum.symm.trans hab_top)
  have hb_ne_top : b ≠ ⊤ := by
    intro hb_top
    have hab_top : a + b = ⊤ := by
      rw [hb_top]
      exact EReal.add_top_of_ne_bot ha_ne_bot
    have hpair_ne_top : pa + pb ≠ ⊤ := by
      simpa [pa, pb, pairing_apply] using
        (EReal.coe_ne_top (⟪x, u₁⟫_ℝ + ⟪x, u - u₁⟫_ℝ))
    exact hpair_ne_top (hab_sum.symm.trans hab_top)
  have ha_coe : (((a.toReal : ℝ) : EReal)) = a :=
    EReal.coe_toReal ha_ne_top ha_ne_bot
  have hb_coe : (((b.toReal : ℝ) : EReal)) = b :=
    EReal.coe_toReal hb_ne_top hb_ne_bot
  have hab_real :
      a.toReal + b.toReal = ⟪x, u₁⟫_ℝ + ⟪x, u - u₁⟫_ℝ := by
    have hcoee :
        (((a.toReal + b.toReal : ℝ) : EReal)) =
          (((⟪x, u₁⟫_ℝ + ⟪x, u - u₁⟫_ℝ : ℝ) : EReal)) := by
      calc
        (((a.toReal + b.toReal : ℝ) : EReal)) =
            (((a.toReal : ℝ) : EReal)) + (((b.toReal : ℝ) : EReal)) := by
              simpa using (EReal.coe_add a.toReal b.toReal)
        _ = a + b := by
              simpa [ha_coe, hb_coe]
        _ = pa + pb := hab_sum
        _ = (((⟪x, u₁⟫_ℝ : ℝ) : EReal)) + (((⟪x, u - u₁⟫_ℝ : ℝ) : EReal)) := by
              simp [pa, pb, pairing_apply]
        _ = (((⟪x, u₁⟫_ℝ + ⟪x, u - u₁⟫_ℝ : ℝ) : EReal)) := by
              simpa using (EReal.coe_add ⟪x, u₁⟫_ℝ ⟪x, u - u₁⟫_ℝ).symm
    exact EReal.coe_eq_coe_iff.mp hcoee
  have hpa_real_le : ⟪x, u₁⟫_ℝ ≤ a.toReal := by
    have hcoe :
        (((⟪x, u₁⟫_ℝ : ℝ) : EReal)) ≤ (((a.toReal : ℝ) : EReal)) := by
      calc
        pa ≤ a := hpa_le
        _ = (((a.toReal : ℝ) : EReal)) := (EReal.coe_toReal ha_ne_top ha_ne_bot).symm
    simpa [pa, pairing_apply] using hcoe
  have hpb_real_le : ⟪x, u - u₁⟫_ℝ ≤ b.toReal := by
    have hcoe :
        (((⟪x, u - u₁⟫_ℝ : ℝ) : EReal)) ≤ (((b.toReal : ℝ) : EReal)) := by
      calc
        pb ≤ b := hpb_le
        _ = (((b.toReal : ℝ) : EReal)) := (EReal.coe_toReal hb_ne_top hb_ne_bot).symm
    simpa [pb, pairing_apply] using hcoe
  have ha_real_eq : a.toReal = ⟪x, u₁⟫_ℝ := by
    linarith
  have hb_real_eq : b.toReal = ⟪x, u - u₁⟫_ℝ := by
    linarith
  constructor
  · -- Convert the first real equality back to the `EReal` contact identity.
    calc
      a = (((a.toReal : ℝ) : EReal)) := ha_coe.symm
      _ = (((⟪x, u₁⟫_ℝ : ℝ) : EReal)) := by rw [ha_real_eq]
      _ = pa := by simp [pa, pairing_apply]
  · -- The same conversion closes the second contact identity.
    calc
      b = (((b.toReal : ℝ) : EReal)) := hb_coe.symm
      _ = (((⟪x, u - u₁⟫_ℝ : ℝ) : EReal)) := by rw [hb_real_eq]
      _ = pb := by simp [pb, pairing_apply]

/-- Helper for Theorem 25.2: once every dual point admits an attained split, the global dual
pairing lower bound follows from the split lower-bound reduction already proved above. -/
private theorem mem_cone_subtypePreimage_onClosedSpan_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Set E} (hS_convex : Convex ℝ S) :
    let B : ClosedSubmodule ℝ E :=
      ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ E) := ((↑) ⁻¹' S)
    ∀ {v : (B : Submodule ℝ E)}, v ∈ cone T ↔ ((v : E) ∈ cone S) := by
  let B : ClosedSubmodule ℝ E :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ E) := ((↑) ⁻¹' S)
  let B0 : Submodule ℝ E := (B : Submodule ℝ E)
  change ∀ {v : B0}, v ∈ cone T ↔ ((v : E) ∈ cone S)
  have hT_convex : Convex ℝ T := by
    -- Pull convexity back along the subtype inclusion of the closed span carrier.
    simpa [T, B0] using hS_convex.affine_preimage B0.subtype.toAffineMap
  intro v
  -- Compare both cone predicates using the positive-multiple description of convex cones.
  constructor
  · intro hv
    rw [cone_eq_toCone_of_convex_aux hT_convex] at hv
    rcases (Convex.mem_toCone hT_convex).1 hv with ⟨c, hc, y, hy, rfl⟩
    rw [cone_eq_toCone_of_convex_aux hS_convex]
    exact (Convex.mem_toCone hS_convex).2 ⟨c, hc, (y : E), hy, rfl⟩
  · intro hv
    rw [cone_eq_toCone_of_convex_aux hS_convex] at hv
    rcases (Convex.mem_toCone hS_convex).1 hv with ⟨c, hc, y, hy, hyv⟩
    have hyB : y ∈ (B : Set E) := by
      -- The closed span contains every generator of the ambient set.
      change y ∈ (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ E) : Set E)
      exact (Submodule.span ℝ S).le_topologicalClosure (Submodule.subset_span hy)
    rw [cone_eq_toCone_of_convex_aux hT_convex]
    refine (Convex.mem_toCone hT_convex).2 ⟨c, hc, ⟨y, hyB⟩, hy, ?_⟩
    apply Subtype.ext
    simpa using hyv

/-- Helper for Theorem 25.2: a closed-span subtype core witness on a convex surface upgrades to
ambient strong-relative-interior regularity on that same surface. This is the ambient/restricted
bridge needed after the lifted zero-slice geometry has been frozen. -/
private theorem zero_mem_sri_of_zero_mem_core_subtypePreimage_onClosedSpan
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Set E} (hS_convex : Convex ℝ S)
    (hcore_support :
      let B : ClosedSubmodule ℝ E :=
        ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
      let T : Set (B : Submodule ℝ E) := ((↑) ⁻¹' S)
      (0 : (B : Submodule ℝ E)) ∈ Set.core T) :
    (0 : E) ∈ sri S := by
  let B : ClosedSubmodule ℝ E :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ E) := ((↑) ⁻¹' S)
  let B0 : Submodule ℝ E := (B : Submodule ℝ E)
  have h0T : (0 : B0) ∈ T := (Set.mem_core_iff.mp hcore_support).1
  have h0S : (0 : E) ∈ S := by
    -- Unpack the subtype origin witness back to the ambient support surface.
    simpa [T, B0] using h0T
  have hS_nonempty : S.Nonempty := ⟨0, h0S⟩
  have hTsub : T - ({(0 : B0)} : Set B0) = T := by
    -- Subtracting the subtype origin does not change the closed-span preimage.
    ext v
    constructor
    · rintro ⟨u, hu, w, hw, huw⟩
      rcases Set.mem_singleton_iff.mp hw with rfl
      have huv : u = v := by simpa using huw
      simpa [huv] using hu
    · intro hv
      exact Set.mem_sub.mpr ⟨v, hv, 0, by simp, by simp⟩
  have hconeT : cone T = (univ : Set B0) := by
    -- Read the core predicate through the Chapter 6 cone criterion on the subtype carrier.
    simpa [hTsub] using (Set.mem_core_iff.mp hcore_support).2
  have hconeS :
      cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ E) : Set E) := by
    apply Set.Subset.antisymm
    · -- Every ambient cone point lies in the closed span generated by the surface.
      intro x hx
      exact cone_subset_topologicalClosure_span S hx
    · intro x hx
      let xB : B0 := ⟨x, hx⟩
      have hxConeT : xB ∈ cone T := by
        -- The subtype cone fills the entire closed span.
        simpa [hconeT]
      -- Route correction: move from the closed-span subtype back to the literal ambient surface
      -- before applying the Chapter 6 `sri` criterion.
      exact
        (mem_cone_subtypePreimage_onClosedSpan_iff (E := E) (S := S) hS_convex).1 hxConeT
  -- The ambient surface now satisfies the same cone-equals-closed-span criterion.
  exact
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hS_nonempty hS_convex).2 hconeS

/-- Helper for Theorem 25.2: under ambient strong-relative-interior regularity on the literal
lifted difference surface, every zero-second dual slice is either infeasible or attained by a
concrete split of the two lifted pullback conjugates. -/
private theorem liftedZeroSliceTopOrSplit_of_zero_mem_sri_lifted
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsriLifted : (0 : ((H × H) × H)) ∈
      sri
        (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))) :
    ∀ q : H × H,
      (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = ⊤ ∨
        ∃ r : ((H × H) × H),
          (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) =
            (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (((q, (0 : H))) - r)) := by
  let φ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstLastFitzpatrickIoi hA
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  have hφ : φ ∈ Γ₀(((H × H) × H)) := by
    -- Freeze the first lifted Fitzpatrick pullback in the canonical `Γ₀` owner interface.
    simpa [φ] using liftedFirstLastFitzpatrickIoi_mem_gammaZero hA
  have hψ : ψ ∈ Γ₀(((H × H) × H)) := by
    -- The second lifted pullback admits the same Chapter 15 packaging.
    simpa [ψ] using liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB
  let χ : ((H × H) × H) → EReal :=
    ERealFunction.infimalConvolution (gammaZeroConjugate φ hφ) (gammaZeroConjugate ψ hψ)
  have hconj :
      (liftedFitzpatrickPullbackSum hA hB)∗ =
        χ := by
    -- Theorem 15.3 identifies the conjugate of the lifted pointwise sum with the dual infimal
    -- convolution of the two lifted pullback conjugates.
    simpa [χ, liftedFitzpatrickPullbackSum, φ, ψ] using
      ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        φ ψ hφ hψ hsriLifted
  have hexact :
      infimalConvolution.Exact (gammaZeroConjugate φ hφ) (gammaZeroConjugate ψ hψ) := by
    -- The same lifted `sri` witness gives exactness of that dual infimal convolution.
    simpa [φ, ψ] using
      ERealFunction.InfimalConvolutionRegularity.infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
        φ ψ hφ hψ hsriLifted
  intro q
  by_cases htop : (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = ⊤
  · -- Outside the dual domain, the desired dichotomy is immediate.
    exact Or.inl htop
  · -- On the finite branch, exactness provides a minimizing split of the lifted dual infimal
    -- convolution at the zero-second slice.
    have hdom :
        (q, (0 : H)) ∈ ERealFunction.dom χ := by
      rw [mem_dom_iff_ne_top]
      intro htopInf
      have hvalue :
          (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = χ (q, (0 : H)) := by
        simpa using congrFun hconj (q, (0 : H))
      exact htop (hvalue.trans htopInf)
    obtain ⟨r, hr⟩ := hexact hdom
    refine Or.inr ⟨r, ?_⟩
    calc
      (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = χ (q, (0 : H)) := by
            simpa using congrFun hconj (q, (0 : H))
      _ = (gammaZeroConjugate φ hφ r : EReal) +
            (gammaZeroConjugate ψ hψ (((q, (0 : H))) - r) : EReal) := hr
      _ = (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
              (((q, (0 : H))) - r)) := by
            simp [gammaZeroConjugate, φ, ψ]

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, every lifted
zero-second dual slice is either infeasible or attained by a concrete split of the two lifted
Fitzpatrick pullback conjugates. This isolates the pure Chapter 15 exactness step before the
weaker `ri` hypothesis is transported to a closed-span ambient. -/
private theorem liftedZeroSliceTopOrSplit_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    ∀ q : H × H,
      (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = ⊤ ∨
        ∃ r : ((H × H) × H),
          (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) =
            (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (((q, (0 : H))) - r)) := by
  let φ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstLastFitzpatrickIoi hA
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  have hsriLifted :
      (0 : ((H × H) × H)) ∈ sri (effectiveDomain φ - effectiveDomain ψ) := by
    -- Lift the projected `sri` witness to the exact product-space pullback regularity condition.
    simpa [φ, ψ] using
      zero_mem_sri_liftedFitzpatrickDifference_of_zero_mem_sri hA hB hsri
  -- The projected `sri` route is now just a normalization step down to the literal lifted
  -- surface, where the Chapter 15 exactness theorem is applied once.
  exact liftedZeroSliceTopOrSplit_of_zero_mem_sri_lifted hA hB hsriLifted

/-- Helper for Theorem 25.2: the projected `ri` hypothesis already gives a common effective-domain
point for the two lifted pullback owners. This packages the easy geometric part of the source
argument before the remaining dual exactness transport. -/
private theorem liftedPullbackOwners_effectiveDomain_inter_nonempty_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) ∩
      effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)).Nonempty := by
  let S : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  have h0S : (0 : H) ∈ S := (Set.mem_relativeInterior_iff.mp hri).1
  rcases h0S with ⟨d, hd, hd0⟩
  rcases Set.mem_sub.mp hd with ⟨a, ha, b, hb, hab⟩
  have hab_fst : a.1 = b.1 := by
    have hfst : a.1 - b.1 = (0 : H) := by
      calc
        a.1 - b.1 = Prod.fst (a - b) := by rfl
        _ = 0 := by simpa [hd0] using congrArg Prod.fst hab
    exact sub_eq_zero.mp hfst
  let q : ((H × H) × H) := ((a.1, a.2 + b.2), a.2)
  refine ⟨q, ?_, ?_⟩
  · -- The first-last pullback sees exactly the ambient domain witness `a`.
    simpa [q, liftedFirstLastFitzpatrickIoi, fitzpatrickIoi, Function.comp] using ha
  · -- The first-difference pullback rewrites to the ambient domain witness `b`.
    have hq :
        ERealFunction.firstDifferencePullbackMap (H := H) (K := H) q = b := by
      ext <;> simp [q, hab_fst]
    change ERealFunction.firstDifferencePullbackMap (H := H) (K := H) q ∈
      effectiveDomain (fitzpatrickIoi hB)
    rw [hq]
    simpa [fitzpatrickIoi] using hb

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the two lifted pullback owners
share a finite point, so their pointwise sum is again a `Γ₀` owner on the lifted space. -/
private theorem liftedPullbackSum_mem_gammaZero_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    liftedFirstLastFitzpatrickIoi hA + liftedFirstDifferenceFitzpatrickIoi hB ∈
      Γ₀(((H × H) × H)) := by
  -- The lifted summands are individually in `Γ₀`, and the projected-domain witness gives one
  -- common lifted point where both are finite.
  refine
    pointwiseAdd_mem_gammaZero
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstDifferenceFitzpatrickIoi hB)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA)
      (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB)
      ?_
  exact
    liftedPullbackOwners_effectiveDomain_inter_nonempty_of_zero_mem_ri
      hA hB hri

/-- Helper for Theorem 25.2: the lifted pullback sum already has some finite conjugate value under
the projected `ri` hypothesis. This separates general dual properness from the remaining
zero-second slice transport problem. -/
private theorem secondVariableSlice_mem_gammaZero_of_nonemptyEffectiveDomain
    {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (F : E × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(E × K)) (x : E)
    (hx : (effectiveDomain (fun y : K ↦ F (x, y))).Nonempty) :
    (fun y : K ↦ F (x, y)) ∈ Γ₀(K) := by
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · -- Lower semicontinuity survives restriction to the continuous slice embedding `y ↦ (x, y)`.
    simpa [Function.comp] using hF.1.comp (Continuous.prodMk_right x)
  · refine ⟨hx, subset_rfl, ?_⟩
    intro y₁ hy₁ y₂ hy₂ α hα0 hα1
    -- Jensen convexity on the ambient owner specializes directly to the two fixed-`x` slice points.
    simpa [Prod.smul_mk, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using
      hF.2.ineq
        (x := (x, y₁))
        (hx := by simpa [mem_effectiveDomain_iff] using hy₁)
        (y := (x, y₂))
        (hy := by simpa [mem_effectiveDomain_iff] using hy₂)
        (α := α) hα0 hα1

/-- Helper for Theorem 25.2: the common lifted effective-domain point from the projected `ri`
hypothesis yields one common first coordinate where both Fitzpatrick slices are themselves `Γ₀`
owners on `H`. This isolates the already-verified slice-level part of the pending dual witness. -/
private theorem commonFirstCoordinate_fitzpatrickSlices_mem_gammaZero_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    ∃ x : H,
      (fun u : H ↦ fitzpatrickIoi hA (x, u)) ∈ Γ₀(H) ∧
        (fun u : H ↦ fitzpatrickIoi hB (x, u)) ∈ Γ₀(H) := by
  rcases liftedPullbackOwners_effectiveDomain_inter_nonempty_of_zero_mem_ri hA hB hri with
    ⟨q, hqA, hqB⟩
  refine ⟨q.1.1, ?_, ?_⟩
  · -- The first lifted-domain witness gives a finite point in the fixed-`x` Fitzpatrick slice of
    -- `A`, so the slice inherits the ambient `Γ₀` structure.
    refine
      secondVariableSlice_mem_gammaZero_of_nonemptyEffectiveDomain
        (F := fitzpatrickIoi hA)
        (hF := fitzpatrickIoi_mem_gammaZero hA)
        (x := q.1.1)
        ?_
    refine ⟨q.2, ?_⟩
    simpa [liftedFirstLastFitzpatrickIoi, Function.comp] using hqA
  · -- The second lifted-domain witness does the same for the fixed-`x` Fitzpatrick slice of `B`.
    refine
      secondVariableSlice_mem_gammaZero_of_nonemptyEffectiveDomain
        (F := fitzpatrickIoi hB)
        (hF := fitzpatrickIoi_mem_gammaZero hB)
        (x := q.1.1)
        ?_
    refine ⟨q.1.2 - q.2, ?_⟩
    simpa [liftedFirstDifferenceFitzpatrickIoi, Function.comp] using hqB

/-- Helper for Theorem 25.2: the same common first coordinate can be chosen so that both fixed
`x` Fitzpatrick slices have finite Fenchel conjugate at some points. This isolates the slice-level
dual finiteness that the remaining lifted zero-slice bridge still has to package. -/
private theorem commonFirstCoordinate_sliceConjugateFinite_of_zeroMemRi
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    ∃ x uA uB,
      (((fun u : H ↦ fitzpatrickIoi hA (x, u)).asEReal∗) uA) < ⊤ ∧
        (((fun u : H ↦ fitzpatrickIoi hB (x, u)).asEReal∗) uB) < ⊤ := by
  rcases commonFirstCoordinate_fitzpatrickSlices_mem_gammaZero_of_zero_mem_ri hA hB hri with
    ⟨x, hxA, hxB⟩
  rcases ERealFunction.dom_conjugate_nonempty_of_mem_gammaZero hxA with ⟨uA, huA⟩
  rcases ERealFunction.dom_conjugate_nonempty_of_mem_gammaZero hxB with ⟨uB, huB⟩
  refine ⟨x, uA, uB, ?_, ?_⟩
  · -- A point in the conjugate domain is exactly a point where the conjugate is finite above.
    simpa using (ERealFunction.mem_dom_iff _ _).mp huA
  · -- The same domain-to-finiteness rewrite applies to the second fixed-`x` slice.
    simpa using (ERealFunction.mem_dom_iff _ _).mp huB

/-- Helper for Theorem 25.2: zero-second membership in the closed span of the literal lifted
support surface is equivalent to first-coordinate membership in the projected closed span. This
freezes the support test used by the remaining pointwise `⊤ ∨ split` branch argument. -/
private theorem zeroSecond_mem_liftedProjectedClosedSpan_iff_fst_mem_projectedClosedSpan
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    {q : H × H} :
    (((q, (0 : H)) : ((H × H) × H)) ∈
      ((Submodule.span ℝ
        (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
            Set (((H × H) × H)))) ↔
      q.1 ∈
        ((Submodule.span ℝ
          (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
            Set H) := by
  -- Read zero-second closed-span membership on the literal lifted surface entirely through the
  -- first-coordinate closed span.
  rw [liftedProjectedClosedSpan_eq_firstProjectionClosedSpanProduct_of_zero_mem_ri hA hB hri]
  simp

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, evaluating the lifted
zero-second conjugate at the explicit split point is bounded above by the corresponding ambient
Fitzpatrick conjugate split. This isolates the exact owner-form estimate available from Corollary
15.8 before any slice/ambient variance conversion is attempted. -/
private theorem liftedZeroSlice_le_explicitAmbientConjugateSplit
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (x uA uB : H) :
    (liftedFitzpatrickPullbackSum hA hB)∗ (((uA + uB, x), (0 : H))) ≤
      ((fitzpatrickIoi hA).asEReal∗ (uA, x)) + ((fitzpatrickIoi hB).asEReal∗ (uB, x)) := by
  let φ : H × H → Set.Ioi (⊥ : EReal) := fitzpatrickIoi hA
  let ψ : H × H → Set.Ioi (⊥ : EReal) := fitzpatrickIoi hB
  have hφ : φ ∈ Γ₀(H × H) := by
    -- Freeze the first Fitzpatrick owner in the packaged `Γ₀` interface.
    simpa [φ] using fitzpatrickIoi_mem_gammaZero hA
  have hψ : ψ ∈ Γ₀(H × H) := by
    -- The second Fitzpatrick owner admits the same packaging.
    simpa [ψ] using fitzpatrickIoi_mem_gammaZero hB
  let LiftA : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun q ↦ φ (q.1.1, q.2)
  let LiftB : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun q ↦ ψ (q.1.1, q.1.2 - q.2)
  let Lift : ((H × H) × H) → EReal := fun q ↦ (LiftA q : EReal) + (LiftB q : EReal)
  have hsum_le :
      Lift∗ (((uA + uB, x), (0 : H))) ≤
        (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((uA + uB, x), (0 : H))) := by
    -- The conjugate of a pointwise sum is always bounded above by the dual infimal convolution.
    simpa [Lift, LiftA, LiftB] using
      (ERealFunction.conjugate_add_le_infimalConvolution_conjugate LiftA LiftB
        (((uA + uB, x), (0 : H))))
  have hzeroSlice :
      (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((uA + uB, x), (0 : H))) =
        ((fun v : H ↦ φ.asEReal∗ (v, x)) □
          fun v ↦ ψ.asEReal∗ (v, x)) (uA + uB) := by
    -- Collapse the lifted zero-second dual infimal convolution to the first-variable split.
    simpa [LiftA, LiftB] using
      (ERealFunction.zeroSecond_lifted_dualInfimalConvolution_eq_firstVariableInfimalConvolution
        (φ := φ) (ψ := ψ) hφ hψ (uA + uB, x))
  -- Evaluate the first-variable infimal convolution at the explicit split `uA`.
  calc
    (liftedFitzpatrickPullbackSum hA hB)∗ (((uA + uB, x), (0 : H))) =
        Lift∗ (((uA + uB, x), (0 : H))) := by
          rfl
    _ ≤ (((LiftA.asEReal)∗) □ ((LiftB.asEReal)∗)) (((uA + uB, x), (0 : H))) := hsum_le
    _ = ((fun v : H ↦ φ.asEReal∗ (v, x)) □
          fun v ↦ ψ.asEReal∗ (v, x)) (uA + uB) := hzeroSlice
    _ ≤ φ.asEReal∗ (uA, x) + ψ.asEReal∗ ((uA + uB) - uA, x) := by
          rw [ERealFunction.infimalConvolution_apply]
          exact
            iInf_le
              (fun v : H ↦ φ.asEReal∗ (v, x) + ψ.asEReal∗ ((uA + uB) - v, x))
              uA
    _ = ((fitzpatrickIoi hA).asEReal∗ (uA, x)) + ((fitzpatrickIoi hB).asEReal∗ (uB, x)) := by
          simp [φ, ψ]

/-- Helper for Theorem 25.2: finiteness of the two ambient Fitzpatrick conjugate summands at a
common second coordinate already forces a finite zero-second dual value for the lifted pullback
sum at the corresponding split point. -/
private theorem liftedZeroSliceFiniteAtExplicitSplit_of_ambientConjugateFinite
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x uA uB : H}
    (hAuA : ((fitzpatrickIoi hA).asEReal∗ (uA, x)) < ⊤)
    (hBuB : ((fitzpatrickIoi hB).asEReal∗ (uB, x)) < ⊤) :
    (liftedFitzpatrickPullbackSum hA hB)∗ (((uA + uB, x), (0 : H))) < ⊤ := by
  -- Bound the zero-second value by the explicit split, then use finiteness of each summand.
  refine lt_of_le_of_lt
    (liftedZeroSlice_le_explicitAmbientConjugateSplit hA hB x uA uB) ?_
  exact EReal.add_lt_top (ne_of_lt hAuA) (ne_of_lt hBuB)

/-- Helper for Theorem 25.2: finiteness of the two ambient Fitzpatrick conjugate summands at a
common second coordinate already forces a finite ambient conjugate value for the fiberwise
Fitzpatrick infimal convolution at the summed first coordinate. -/
private theorem
    fitzpatrickFiberwiseInfimalConvolution_conjugateFinite_of_explicitAmbientSplit
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x uA uB : H}
    (hAuA : ((fitzpatrickIoi hA).asEReal∗ (uA, x)) < ⊤)
    (hBuB : ((fitzpatrickIoi hB).asEReal∗ (uB, x)) < ⊤) :
    ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗) (uA + uB, x) < ⊤ := by
  have hle :=
    conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_le_split hA hB x (uA + uB) uA
  -- Rewrite the transpose spelling back to the ambient conjugate before using the explicit split.
  rw [transpose_apply, transpose_apply, transpose_apply] at hle
  refine lt_of_le_of_lt hle ?_
  simpa using EReal.add_lt_top (ne_of_lt hAuA) (ne_of_lt hBuB)

/-- Helper for Theorem 25.2: under the stronger projected `sri` hypothesis, evaluating the lifted
zero-second conjugate at the explicit split point is bounded above by the corresponding ambient
Fitzpatrick conjugate split. This keeps the original `sri`-named interface while delegating the
actual estimate to the unconditional conjugate-of-sum upper bound above. -/
private def affineTiltERealLocal
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → EReal) (u : E) : E → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

/-- Helper for Theorem 25.2: evaluating the local affine tilt exposes the added linear term. -/
@[simp] private theorem affineTiltERealLocal_apply
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → EReal) (u x : E) :
    affineTiltERealLocal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

/-- Helper for Theorem 25.2: affine tilting a `Γ₀(E)` owner preserves properness. -/
private theorem affineTiltERealLocal_isProper
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (u : E) :
    IsProper (affineTiltERealLocal f.asEReal u) := by
  have htilt_eq_coe :
      ∀ ⦃x : E⦄, x ∈ effectiveDomain f →
        affineTiltERealLocal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
    intro x hx
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [affineTiltERealLocal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  constructor
  · intro x
    by_cases hx : x ∈ effectiveDomain f
    · rw [htilt_eq_coe hx]
      exact EReal.coe_ne_bot _
    · have hx_top : f.asEReal x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
      rw [affineTiltERealLocal, hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
      simp
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [ERealFunction.mem_dom_iff, htilt_eq_coe hx]
    simpa using (EReal.coe_lt_top (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ)))

/-- Helper for Theorem 25.2: package the local affine tilt back into `]-∞,+∞]`. -/
private abbrev affineTiltIoiLocal
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (u : E) :
    E → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltERealLocal f.asEReal u) (affineTiltERealLocal_isProper f hf u)

/-- Helper for Theorem 25.2: coercing the packaged local affine tilt recovers the raw tilt. -/
@[simp] private theorem affineTiltIoiLocal_apply
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (u x : E) :
    (affineTiltIoiLocal f hf u x : EReal) = affineTiltERealLocal f.asEReal u x := by
  rfl

/-- Helper for Theorem 25.2: the packaged local affine tilt belongs to `Γ₀(E)`. -/
private theorem affineTiltLocal_memGammaZero
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (u : E) :
    affineTiltIoiLocal f hf u ∈ Γ₀(E) := by
  have hlinear_gamma :
      (fun x : E ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) ∈ Γ(E) := by
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      change (((-(⟪a • x + (1 - a) • y, u⟫_ℝ) : ℝ) : EReal)) ≤
        (a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
          (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))
      have hreal :
          -(⟪a • x + (1 - a) • y, u⟫_ℝ) =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      rw [hreal, hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    · simpa using
        (continuous_coe_real_ereal.comp
          ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
  have htilt_gamma : affineTiltERealLocal f.asEReal u ∈ Γ(E) := by
    have hf_gamma : f.asEReal ∈ Γ(E) := asEReal_mem_gamma_of_mem_gammaZero hf
    rw [mem_gamma_iff] at hf_gamma hlinear_gamma ⊢
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by exact_mod_cast ha0
      have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
        exact_mod_cast sub_nonneg.mpr ha1
      have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
      calc
        affineTiltERealLocal f.asEReal u (a • x + (1 - a) • y)
            ≤ ((a : EReal) * f.asEReal x + (1 - a : EReal) * f.asEReal y) +
                ((a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
                  (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))) := by
              simpa [affineTiltERealLocal] using
                add_le_add (hf_gamma.1 ha0 ha1) (hlinear_gamma.1 ha0 ha1)
        _ = (a : EReal) * affineTiltERealLocal f.asEReal u x +
              (1 - a : EReal) * affineTiltERealLocal f.asEReal u y := by
              simp [affineTiltERealLocal,
                EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top,
                add_assoc, add_left_comm]
    · rw [lowerSemicontinuous_iff_le_liminf]
      intro x
      calc
        affineTiltERealLocal f.asEReal u x
            ≤ Filter.liminf f.asEReal (nhds x) +
                Filter.liminf (fun y : E ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal))) (nhds x) := by
              simpa [affineTiltERealLocal] using
                add_le_add (hf_gamma.2.le_liminf x) (hlinear_gamma.2.le_liminf x)
        _ ≤ Filter.liminf (affineTiltERealLocal f.asEReal u) (nhds x) := by
              simpa [affineTiltERealLocal] using
                (EReal.le_liminf_add :
                  Filter.liminf f.asEReal (nhds x) +
                      Filter.liminf
                        (fun y : E ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                        (nhds x) ≤
                    Filter.liminf
                      (fun y : E ↦
                        f.asEReal y + (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                      (nhds x))
  exact properIoi_mem_gammaZero_of_mem_gamma (affineTiltERealLocal_isProper f hf u) htilt_gamma

/-- Helper for Theorem 25.2: affine tilting does not change the effective domain. -/
private theorem effectiveDomain_affineTiltIoiLocal
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (u : E) :
    effectiveDomain (affineTiltIoiLocal f hf u) = effectiveDomain f := by
  ext x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hvalue :
        affineTiltERealLocal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
      rw [affineTiltERealLocal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
      simp [sub_eq_add_neg]
    rw [affineTiltIoiLocal_apply, hvalue]
    constructor
    · intro _
      exact mem_effectiveDomain_iff.mp hx
    · intro _
      exact EReal.coe_lt_top _
  · rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hx_top : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [affineTiltIoiLocal_apply, affineTiltERealLocal, hx_top,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
    simp [hx_top]

/-- Helper for Theorem 25.2: the fixed-`q` lifted dual value is the zero-value conjugate of the
corresponding affine tilt of the full lifted sum. This isolates the normalization part of the new
route without yet solving the remaining closed-span exactness transport. -/
private theorem liftedZeroSlice_eq_zeroConjugate_tiltedLiftedSum
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    (affineTiltERealLocal (liftedFitzpatrickPullbackSum hA hB) q0)∗ (0 : ((H × H) × H)) =
      (liftedFitzpatrickPullbackSum hA hB)∗ q0 := by
  -- Route correction: convert the fixed-`q` evaluation to a zero-slice conjugate before trying to
  -- apply any closed-span exactness theorem.
  have hconj :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := (liftedFitzpatrickPullbackSum hA hB))
        (y := (0 : ((H × H) × H))) (v := -q0) (β := 0))
      0
  simpa [affineTiltERealLocal, Pi.add_apply, add_assoc, add_left_comm, add_comm] using hconj

/-- Helper for Theorem 25.2: the affine-tilted lifted sum is exactly the identity-map composite
primal objective for the tilted first pullback and the unchanged second pullback. This freezes the
same-space owner spelling that the remaining exact-support attainment step must use. -/
private theorem tiltedLiftedSum_eq_compositePrimalObjective
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    affineTiltERealLocal (liftedFitzpatrickPullbackSum hA hB) q0 =
      ERealFunction.compositePrimalObjective
        (liftedFirstDifferenceFitzpatrickIoi hB)
        (affineTiltIoiLocal
          (liftedFirstLastFitzpatrickIoi hA)
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0)
        (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
  -- Expand the identity-map composite problem once so the affine-tilted first summand and the
  -- unchanged second summand appear in the same owner notation.
  funext x
  simp [ERealFunction.compositePrimalObjective, ERealFunction.primalObjective,
    affineTiltERealLocal, liftedFitzpatrickPullbackSum, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 25.2: the fixed zero-second lifted dual value is the negative composite
primal optimal value of the affine-tilted first pullback paired with the unchanged second
pullback. This isolates the remaining blocker to one exact-support attainment theorem for that
same-space composite owner. -/
private theorem tiltedZeroSlice_eq_neg_compositePrimalOptimalValue
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
      -ERealFunction.compositePrimalOptimalValue
        (liftedFirstDifferenceFitzpatrickIoi hB)
        (affineTiltIoiLocal
          (liftedFirstLastFitzpatrickIoi hA)
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0)
        (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
  -- First rewrite the fixed-`q` conjugate as the zero-slice conjugate of the affine tilt.
  calc
    (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
        (affineTiltERealLocal (liftedFitzpatrickPullbackSum hA hB) q0)∗
          (0 : ((H × H) × H)) := by
            symm
            exact liftedZeroSlice_eq_zeroConjugate_tiltedLiftedSum hA hB q0
    _ =
        -ERealFunction.compositePrimalOptimalValue
          (liftedFirstDifferenceFitzpatrickIoi hB)
          (affineTiltIoiLocal
            (liftedFirstLastFitzpatrickIoi hA)
            (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0)
          (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
            -- Then identify that zero-slice conjugate with the negative infimum of the tilted
            -- same-space primal objective.
            rw [conjugate_zero_eq_neg_iInf, ERealFunction.compositePrimalOptimalValue_def,
              sInf_range]
            simpa using
              congrArg
                (fun f : (((H × H) × H) → EReal) ↦ -sInf (Set.range f))
                (tiltedLiftedSum_eq_compositePrimalObjective hA hB q0)

/-- Helper for Theorem 25.2: packaging the affine tilt of the first lifted Fitzpatrick pullback
preserves the `Γ₀` structure and does not change the effective domain. This freezes the tilted
owner used by the fixed-`q` dual normalization. -/
private theorem affineTiltedLiftedFirstLast_memGammaZero_eqDom
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (q0 : ((H × H) × H)) :
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    φtilt ∈ Γ₀(((H × H) × H)) ∧
      effectiveDomain φtilt = effectiveDomain (liftedFirstLastFitzpatrickIoi hA) := by
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  constructor
  · -- The global affine-tilt API already packages the tilted lifted owner back into `Γ₀`.
    simpa [φtilt] using
      affineTiltLocal_memGammaZero
        (f := liftedFirstLastFitzpatrickIoi hA)
        (hf := liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  · -- Affine tilting only adds a finite linear term, so the effective domain is unchanged.
    simpa [φtilt] using
      effectiveDomain_affineTiltIoiLocal
        (f := liftedFirstLastFitzpatrickIoi hA)
        (hf := liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0

/-- Helper for Theorem 25.2: affine tilting the first lifted pullback does not change the literal
support surface used by the zero-second slice argument. This keeps the remaining frontier in one
stable spelling of the closed-span support set. -/
private theorem tiltedLiftedDifference_eq_untiltedDifference
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
      effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
        effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  -- Rewrite the affine-tilted first effective domain back to the original pulled-back domain.
  simpa [φtilt] using
    congrArg
      (fun S : Set (((H × H) × H)) ↦
        S - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))
      (affineTiltedLiftedFirstLast_memGammaZero_eqDom hA q0).2

/-- Helper for Theorem 25.2: the fixed zero-second slice sees the same closed-span support test
after affine tilting the first lifted owner. This is the exact transport needed before invoking
the Chapter 15 dual package on the tilted pair. -/
private theorem tiltedZeroSecond_mem_tiltedProjectedClosedSpan_iff_fst_mem_projectedClosedSpan
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    (q0 ∈
      ((Submodule.span ℝ
        (effectiveDomain φtilt -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
            Set (((H × H) × H)))) ↔
      q.1 ∈
        ((Submodule.span ℝ
          (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
            Set H) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  have hdiff :
      effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
        effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
    -- Affine tilting keeps the literal lifted support surface unchanged.
    simpa [q0, φtilt] using tiltedLiftedDifference_eq_untiltedDifference hA hB q0
  dsimp [q0, φtilt]
  -- First collapse the tilted support surface to the untilted lifted one.
  rw [hdiff]
  -- The zero-second support test on the untilted lifted surface already reads through `q.1`.
  change
    (((q, (0 : H)) : ((H × H) × H)) ∈
        ((Submodule.span ℝ
          (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
            effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
              Set (((H × H) × H)))) ↔
      q.1 ∈
        ((Submodule.span ℝ
          (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
            Set H)
  rw [liftedProjectedClosedSpan_eq_firstProjectionClosedSpanProduct_of_zero_mem_ri hA hB hri]
  simp

/-- Helper for Theorem 25.2: the tilted support surface is convex because affine tilting preserves
the first lifted effective domain. This keeps the remaining closed-span argument in the same
surface spelling as the support-membership transport above. -/
private theorem tiltedLiftedDifference_eq_firstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
      ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
        Set (((H × H) × H))) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  dsimp [S0, φtilt]
  -- Replace the tilted first summand by the untilted one, then reuse the already-frozen product
  -- spelling of the lifted Fitzpatrick difference.
  calc
    effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
        effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
            simpa [φtilt] using tiltedLiftedDifference_eq_untiltedDifference hA hB q0
    _ =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
            simpa [S0] using liftedFitzpatrickDifference_eq_firstProjectionProduct hA hB

/-- Helper for Theorem 25.2: reading the same tilted lifted surface in the Chapter 15 order
`effectiveDomain ψ - id '' effectiveDomain φtilt` only negates the first-coordinate support set.
This isolates the remaining blocker to the closed-span core promotion, not to any `φ - ψ` versus
`ψ - φ` carrier rewrite. -/
private theorem reversedTiltedLiftedDifference_eq_negFirstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 : ((H × H) × H)) :
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) -
        (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt =
      (((((-S0) ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
        Set (((H × H) × H))) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  have hforward :
      effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    -- Normalize the forward same-space surface first, then swap witnesses explicitly.
    simpa [S0, φtilt] using tiltedLiftedDifference_eq_firstProjectionProduct hA hB q0
  ext p
  constructor
  · intro hp
    rcases Set.mem_sub.mp hp with ⟨u, hu, w, hw, huw⟩
    rcases hw with ⟨v, hv, rfl⟩
    have hneg :
        -p ∈ effectiveDomain φtilt -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
      refine Set.mem_sub.mpr ⟨v, hv, u, hu, ?_⟩
      -- Negating the reversed difference equality recovers the forward witness.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using congrArg Neg.neg huw
    have hneg_mem :
        -p ∈
          ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
            Set (((H × H) × H))) := by
      rwa [hforward] at hneg
    -- Only the first coordinate changes sign; the two free factors stay unrestricted.
    have hp_first : p.1.1 ∈ (-S0 : Set H) := by
      simpa [Set.mem_neg] using hneg_mem.1.1
    exact ⟨⟨hp_first, by simp⟩, by simp⟩
  · intro hp
    have hneg_mem :
        -p ∈
          ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
            Set (((H × H) × H))) := by
      -- Read the negated first-coordinate carrier back through the forward product spelling.
      have hp_first : p.1.1 ∈ (-S0 : Set H) := hp.1.1
      have hneg_first : (-p).1.1 ∈ S0 := by
        simpa [Set.mem_neg] using hp_first
      exact ⟨⟨hneg_first, by simp⟩, by simp⟩
    have hforward_mem :
        -p ∈ effectiveDomain φtilt -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
      simpa [← hforward] using hneg_mem
    rcases Set.mem_sub.mp hforward_mem with ⟨u, hu, v, hv, huv⟩
    refine Set.mem_sub.mpr ⟨v, hv, u, ⟨u, hu, rfl⟩, ?_⟩
    -- Swapping the forward witnesses produces the reversed same-space difference equality.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using congrArg Neg.neg huv

/-- Helper for Theorem 25.2: after translating the tilted same-space pair by a common
effective-domain point, the closed-span subtype support set is already the subtype preimage of the
explicit `(-S₀) × univ × univ` carrier. This freezes the transport seam before the remaining
closed-span core argument. -/
private theorem translatedTiltedForwardSupportSubtypePreimage_eq_firstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
      let S : Set (((H × H) × H)) :=
        effectiveDomain φz -
          (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain ψz
      let Bc : ClosedSubmodule ℝ (((H × H) × H)) :=
        ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
      let T : Set (Bc : Submodule ℝ (((H × H) × H))) := ((↑) ⁻¹' S)
      T =
        ((↑) ⁻¹'
          ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
            Set (((H × H) × H)))) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  dsimp
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let S : Set (((H × H) × H)) :=
    effectiveDomain φz -
      (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain ψz
  let Bc : ClosedSubmodule ℝ (((H × H) × H)) :=
    ⟨(Submodule.span ℝ S).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (Bc : Submodule ℝ (((H × H) × H))) := ((↑) ⁻¹' S)
  have htranslated :
      effectiveDomain φz -
          (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain ψz =
        effectiveDomain φtilt -
          (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain ψ := by
    -- Forget the compensating translation in the ambient same-space support surface once.
    simpa [φz, ψz, φtilt, ψ, ContinuousLinearMap.id_apply] using
      (ERealFunction.translated_composite_data_preserves_regular_set
        (f := ψ) (g := φtilt)
        (L := ContinuousLinearMap.id ℝ (((H × H) × H)))
        (a := z) hzψ (b := z) hzφ rfl).1
  have hsurface :
      effectiveDomain φtilt -
          (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain ψ =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    -- Normalize the frozen tilted same-space surface to the explicit `S₀ ×ˢ univ ×ˢ univ`
    -- carrier before introducing the closed-span subtype.
    simpa [q0, φtilt, ψ, S0] using
      tiltedLiftedDifference_eq_firstProjectionProduct hA hB q0
  -- The restricted forward support test is now exactly the subtype preimage of the explicit
  -- product carrier.
  simpa [T, S, S0, φz, ψz, φtilt, ψ] using
    congrArg
      (fun U : Set (((H × H) × H)) ↦
        (Subtype.val ⁻¹' U : Set (Bc : Submodule ℝ (((H × H) × H)))))
      (htranslated.trans hsurface)

/-- Helper for Theorem 25.2: negating the first-coordinate support set does not change its closed
linear span. This keeps the reversed support carrier in the same first-coordinate closed-span
normal form as the forward carrier. -/
private theorem closure_span_neg_eq_closure_span
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) :
    ((Submodule.span ℝ (-S : Set E)).topologicalClosure : Set E) =
      ((Submodule.span ℝ S).topologicalClosure : Set E) := by
  have hspan :
      Submodule.span ℝ (-S : Set E) = Submodule.span ℝ S := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      intro x hx
      have hnegx : -x ∈ S := by
        simpa [Set.mem_neg] using hx
      simpa using Submodule.neg_mem (Submodule.span ℝ S) (Submodule.subset_span hnegx)
    · refine Submodule.span_le.mpr ?_
      intro x hx
      have hnegx : -x ∈ (-S : Set E) := by
        simpa [Set.mem_neg] using hx
      simpa using Submodule.neg_mem (Submodule.span ℝ (-S : Set E)) (Submodule.subset_span hnegx)
  simpa [hspan]

/-- Helper for Theorem 25.2: after translating the affine-tilted same-space pair by a common
effective-domain point, the reversed closed support span is exactly the projected first-coordinate
closed span times the two free factors. This freezes the carrier normalization for the reversed
core route. -/
private theorem tiltedLiftedClosedSpan_eq_firstProjectionClosedSpanProduct_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q0 : ((H × H) × H)) :
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    ((Submodule.span ℝ
      (effectiveDomain φtilt -
        effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
          Set (((H × H) × H))) =
      (((((Submodule.span ℝ S0).topologicalClosure : Set H) ×ˢ
          (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  have hsurface :
      effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) =
        effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
    -- Affine tilting leaves the literal lifted support surface unchanged.
    simpa [φtilt] using tiltedLiftedDifference_eq_untiltedDifference hA hB q0
  -- After collapsing the tilted surface to the untilted one, reuse the closed-span product
  -- normalization already proved for the literal lifted difference.
  calc
    (((Submodule.span ℝ
        (effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
          Submodule ℝ (((H × H) × H))) : Set (((H × H) × H))) =
      (((Submodule.span ℝ
        (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB))).topologicalClosure :
            Submodule ℝ (((H × H) × H))) : Set (((H × H) × H))) := by
          -- Freeze the closed-span transport before the final product normalization.
          rw [hsurface]
    _ =
      (((((Submodule.span ℝ S0).topologicalClosure : Set H) ×ˢ
          (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) := by
        exact
          liftedProjectedClosedSpan_eq_firstProjectionClosedSpanProduct_of_zero_mem_ri
            hA hB hri

/-- Helper for Theorem 25.2: membership in the affine-tilted closed support span is read
entirely through the first coordinate, because the other two factors remain unrestricted. -/
private theorem zero_mem_tiltedLiftedDifference_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q0 : ((H × H) × H)) :
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    (0 : ((H × H) × H)) ∈
      effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  have h0S0 : (0 : H) ∈ S0 := by
    exact (Set.mem_relativeInterior_iff.mp hri).1
  dsimp
  -- Rewrite the tilted support surface to the explicit product spelling and read off the origin.
  rw [tiltedLiftedDifference_eq_firstProjectionProduct hA hB q0]
  have hzero :
      (0 : ((H × H) × H)) ∈
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    simp [h0S0]
  simpa [S0] using hzero

/-- Helper for Theorem 25.2: the exact tilted support surface contains a common domain witness for
the two lifted pullbacks. This is the zero-domain datum that any later translated closed-span
argument will need. -/
private theorem exists_common_mem_effectiveDomain_tiltedLiftedPair_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q0 : ((H × H) × H)) :
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    ∃ z : ((H × H) × H),
      z ∈ effectiveDomain φtilt ∧
        z ∈ effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  have hzero_mem :
      (0 : ((H × H) × H)) ∈
        effectiveDomain φtilt - effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB) := by
    simpa [φtilt] using zero_mem_tiltedLiftedDifference_of_zero_mem_ri hA hB hri q0
  rcases Set.mem_sub.mp hzero_mem with ⟨y, hy, z, hz, hyz⟩
  have hy_eq_z : y = z := by
    exact sub_eq_zero.mp hyz
  refine ⟨y, hy, ?_⟩
  simpa [hy_eq_z] using hz

/-- Helper for Theorem 25.2: the identity-map composite dual objective for the affine-tilted
first lifted pullback is exactly the concrete split kernel used by the later fixed-`q` support
argument. This records the normalization once, so the remaining blocker is only the closed-span
attainment input. -/
private theorem tiltedCompositeDualObjective_eq_splitApply
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q0 r : ((H × H) × H)) :
    compositeDualObjective
        (affineTiltIoiLocal
          (liftedFirstLastFitzpatrickIoi hA)
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0)
        (liftedFirstDifferenceFitzpatrickIoi hB)
        (ContinuousLinearMap.id ℝ (((H × H) × H)))
        (q0 - r) =
      (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
        (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - r)) := by
  have htilt :
      (affineTiltIoiLocal
          (liftedFirstLastFitzpatrickIoi hA)
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0).asEReal∗ =
        fun v ↦ ((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (v + q0) := by
    funext v
    -- The affine tilt only translates the first conjugate by `-q0`.
    have hconj :=
      congrFun
        (conjugate_translate_add_inner_add_const
          (f := (liftedFirstLastFitzpatrickIoi hA).asEReal)
          (y := (0 : ((H × H) × H))) (v := -q0) (β := 0))
        v
    simpa [Function.asEReal_apply, affineTiltERealLocal, Pi.add_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hconj
  -- Expand the identity-map dual objective and collapse the translated first conjugate at
  -- `-(q0 - r) = r - q0` back to the original conjugate at `r`.
  rw [compositeDualObjective_apply, htilt]
  simp [neg_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 25.2: on an identity-map composite problem, swapping the two primal
summands does not change the primal optimal value. This keeps the final lifted rewrite compatible
with the translated same-space owner order. -/
private theorem compositePrimalOptimalValue_id_comm
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) :
    ERealFunction.compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ E) =
      ERealFunction.compositePrimalOptimalValue g f (ContinuousLinearMap.id ℝ E) := by
  -- Freeze the pointwise identity-map objective once; the two summands commute pointwise.
  have hobj :
      ERealFunction.compositePrimalObjective f g (ContinuousLinearMap.id ℝ E) =
        ERealFunction.compositePrimalObjective g f (ContinuousLinearMap.id ℝ E) := by
    funext x
    simp [ERealFunction.compositePrimalObjective_apply, add_comm]
  -- The ranges of the two identical pointwise objectives have the same infimum.
  simpa [ERealFunction.compositePrimalOptimalValue_def] using
    congrArg (fun h : E → EReal ↦ sInf (Set.range h)) hobj

/-- Helper for Theorem 25.2: an attained composite-dual equality already identifies the witness as
an `Argmin` point of the identity-map dual owner. -/
private theorem mem_argmin_compositeDualObjective_of_attainedPrimalOptimalValue
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) {v : E}
    (hv :
      ERealFunction.compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ E) =
        -ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) v) :
    v ∈ Argmin (ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E)) := by
  -- The attained value saturates weak duality, so the chosen dual point is globally minimizing.
  refine
    ERealFunction.mem_argmin_of_valueEq_and_weakDuality
      (h := ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E))
      (w := v)
      (a := ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) v)
      rfl ?_
  intro w
  have hweak :=
    ERealFunction.compositePrimalOptimalValue_ge_neg_compositeDualObjective
      f g (ContinuousLinearMap.id ℝ E) w
  rw [hv] at hweak
  exact EReal.neg_le_neg_iff.mp hweak

/-- Helper for Theorem 25.2: once one dual candidate has value different from `⊤`, every attained
dual minimizer has value different from `⊤` as well. -/
private theorem argminDualValue_neTop_of_nonTopCandidate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) {v0 : E}
    (hv0 :
      v0 ∈ Argmin (ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E)))
    (hcandidate :
      ∃ vCand : E,
        ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) vCand ≠ ⊤) :
    ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) v0 ≠ ⊤ := by
  let D : E → EReal := ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E)
  have hv0_eq : D v0 = sInf (Set.range D) := by
    simpa [D] using (mem_argmin_iff_eq_sInf.mp hv0)
  rcases hcandidate with ⟨vCand, hvCand_neTop⟩
  have hsInf_neTop : sInf (Set.range D) ≠ ⊤ := by
    intro hsInf_top
    have hCand_top : D vCand = ⊤ := by
      apply le_antisymm le_top
      simpa [hsInf_top] using (sInf_le (s := Set.range D) ⟨vCand, rfl⟩)
    exact hvCand_neTop hCand_top
  -- Replace the attained value by the range infimum and use the finite comparison point.
  simpa [D, hv0_eq] using hsInf_neTop

/-- Helper for Theorem 25.2: any non-`⊤` composite-dual candidate rules out the exceptional primal
value `⊥` by weak duality. -/
private theorem compositePrimalOptimalValue_neBot_of_exists_nonTopDualCandidate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal))
    (hcandidate :
      ∃ vCand : E,
        ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) vCand ≠ ⊤) :
    ERealFunction.compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ E) ≠ ⊥ := by
  rcases hcandidate with ⟨vCand, hvCand_neTop⟩
  intro hprimal_bot
  have hweak :=
    ERealFunction.compositePrimalOptimalValue_ge_neg_compositeDualObjective
      f g (ContinuousLinearMap.id ℝ E) vCand
  have hdual_neBot :
      -ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) vCand ≠ ⊥ := by
    -- Negating a non-`⊤` dual value never lands at the exceptional primal value `⊥`.
    simpa using hvCand_neTop
  have hdual_le_bot :
      -ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) vCand ≤ ⊥ := by
    -- Specialize weak duality at the explicit candidate and rewrite the exceptional primal branch.
    simpa [hprimal_bot] using hweak
  exact hdual_neBot (le_bot_iff.mp hdual_le_bot)

/-- Helper for Theorem 25.2: after translating the affine-tilted same-space pair by a common
effective-domain point, the literal support surface `effectiveDomain φz - effectiveDomain ψz`
is still the explicit first-coordinate product carrier. This records the ambient normalization
before the remaining support-attainment bridge. -/
private theorem translatedTiltedDifference_eq_firstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      effectiveDomain φz - effectiveDomain ψz =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  have hsurface :
      effectiveDomain φz - effectiveDomain ψz =
        effectiveDomain φtilt - effectiveDomain ψ := by
    -- Read the common translation through the generic identity-map regularity preservation once.
    simpa [φz, ψz, φtilt, ψ] using
      (ERealFunction.translated_composite_data_preserves_regular_set
        (f := ψ) (g := φtilt)
        (L := ContinuousLinearMap.id ℝ (((H × H) × H)))
        (a := z) hzψ (b := z) hzφ rfl).1
  -- Collapse the untilted support surface to the explicit first-coordinate product spelling.
  calc
    effectiveDomain φz - effectiveDomain ψz =
        effectiveDomain φtilt - effectiveDomain ψ := hsurface
    _ =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
            simpa [S0, φtilt, ψ] using tiltedLiftedDifference_eq_firstProjectionProduct hA hB q0

/-- Helper for Theorem 25.2: the translated same-space support surface in the Chapter 15 order
`effectiveDomain ψz - id '' effectiveDomain φz` is still the explicit product carrier with the
first coordinate negated. This isolates the remaining blocker to the exact off-support dual
alternative, not to another transport rewrite. -/
private theorem translatedReversedTiltedDifference_eq_negFirstProjectionProduct
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        (((((-S0) ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  have hsurface :
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        effectiveDomain ψ - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt := by
    -- Keep the translated support surface in the reversed Chapter 15 order for the off-support
    -- branch, where the dual owner is written with `ψz - φz`.
    simpa [φz, ψz, φtilt, ψ] using
      (ERealFunction.translated_composite_data_preserves_regular_set
        (f := φtilt) (g := ψ)
        (L := ContinuousLinearMap.id ℝ (((H × H) × H)))
        (a := z) hzφ (b := z) hzψ rfl).1
  -- Collapse the untilted reversed surface to the explicit negated first-coordinate carrier.
  calc
    effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        effectiveDomain ψ - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt :=
          hsurface
    _ =
        (((((-S0) ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
            simpa [S0, φtilt, ψ] using
              reversedTiltedLiftedDifference_eq_negFirstProjectionProduct hA hB q0

/-- Helper for Theorem 25.2: once the frozen translated support point is known to lie in the
projected closed span and the primal value is nonexceptional, the remaining task is the owner-level
attained-value transport from the closed support carrier back to the ambient translated pair. -/
private theorem translatedPrimalBot_of_not_closedSpanPoint
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      q.1 ∉ Sclosed →
      ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) = ⊥ := by
  -- Route correction: the off-support branch should be proved directly on the frozen translated
  -- owner instead of being recovered indirectly from a larger support theorem.
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  have _hsurface :
      effectiveDomain φz - effectiveDomain ψz =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    -- The remaining blocker is no longer the ambient support-surface spelling.
    exact translatedTiltedDifference_eq_firstProjectionProduct hA hB q (z := z) hzφ hzψ
  have _hrevSurface :
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        (((((-S0) ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    -- The remaining blocker is the owner-level all-`⊤` dual alternative, not another reverse
    -- support-surface transport.
    exact
      translatedReversedTiltedDifference_eq_negFirstProjectionProduct hA hB q
        (z := z) hzφ hzψ
  -- TODO: use the frozen translated support surface and the product-graph dual alternative to show
  -- that every dual value is `⊤` off support, then rewrite the primal branch to `⊥`.
  sorry

/-- Helper for Theorem 25.2: the closed-span support branch should supply both the attained
translated dual value and one finite dual witness, so the ambient wrappers no longer duplicate the
same closed-carrier transport seam. -/
private theorem translatedSupportWitness_of_closedSpanPoint
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      q.1 ∈ Sclosed →
      ∃ v : ((H × H) × H),
        ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) =
          -ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v ∧
        ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v ≠ ⊤ := by
  -- Route correction: this is the single remaining on-support theorem. The attained-value and
  -- non-`⊤` wrappers below should only project its two outputs.
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  have hq0_mem :
      q0 ∈
        ((Submodule.span ℝ (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
          Set (((H × H) × H))) :=
    hq0_closed.mpr hq
  have _hsurface :
      effectiveDomain φz - effectiveDomain ψz =
        ((((S0 ×ˢ (Set.univ : Set H)) : Set (H × H)) ×ˢ (Set.univ : Set H)) :
          Set (((H × H) × H))) := by
    -- The support branch is already normalized to the explicit product carrier before the closed
    -- support witness is requested.
    exact translatedTiltedDifference_eq_firstProjectionProduct hA hB q (z := z) hzφ hzψ
  let _qB :
      (⟨(Submodule.span ℝ (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure,
        Submodule.isClosed_topologicalClosure _⟩ : ClosedSubmodule ℝ (((H × H) × H))) :=
    ⟨(Submodule.span ℝ (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure,
      Submodule.isClosed_topologicalClosure _⟩
  have _hqB : q0 ∈ (_qB : Set (((H × H) × H))) := hq0_mem
  -- TODO: restrict the translated same-space problem to the closed support carrier at `q0`,
  -- obtain the shifted support witness there, and transport the attained value and finite dual
  -- value back to the ambient translated owner in one step.
  sorry

/-- Helper for Theorem 25.2: once the frozen translated support point is known to lie in the
projected closed span and the primal value is nonexceptional, the remaining task is the owner-level
attained-value transport from the closed support carrier back to the ambient translated pair. -/
private theorem translatedAttainedDualValue_of_closedSpanPoint_of_primalNeBot
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      q.1 ∈ Sclosed →
      ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) ≠ ⊥ →
      ∃ v : ((H × H) × H),
        ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) =
          -ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v := by
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq _hμ_neBot
  -- Project the attained-value component from the single on-support witness package.
  obtain ⟨v, hvEq, _hvNeTop⟩ :=
    translatedSupportWitness_of_closedSpanPoint hA hB hri q
      (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  exact ⟨v, hvEq⟩

/-- Helper for Theorem 25.2: if the frozen translated primal optimal value is nonexceptional,
then the support point must lie in the projected closed span. -/
private theorem translatedClosedSpanMembership_of_primalNeBot
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) ≠ ⊥ →
      q.1 ∈ Sclosed := by
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hμ_neBot
  by_contra hq
  -- The new direct off-support theorem closes the contraposition without reopening the support
  -- transport seam here.
  have hμ_bot :=
    translatedPrimalBot_of_not_closedSpanPoint hA hB hri q
      (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  exact hμ_neBot hμ_bot

/-- Helper for Theorem 25.2: on the projected closed span, the frozen translated dual owner
already has at least one non-`⊤` value. -/
private theorem translatedNonTopDualCandidate_of_closedSpanPoint
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      q.1 ∈ Sclosed →
      ∃ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v ≠ ⊤ := by
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  -- Project the finite-value component from the single on-support witness package.
  obtain ⟨v, _hvEq, hvNeTop⟩ :=
    translatedSupportWitness_of_closedSpanPoint hA hB hri q
      (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
  exact ⟨v, hvNeTop⟩

/-- Helper for Theorem 25.2: once the translated zero-domain pair has been frozen, the remaining
support dichotomy is purely an owner-level statement for the translated same-space composite
problem. This isolates the exact closed-span support theorem still needed for the final lifted
zero-second branch split. -/
private theorem translatedFrozenSupportDichotomy_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) →
      ψz ∈ Γ₀(((H × H) × H)) →
      (0 : ((H × H) × H)) ∈ effectiveDomain φz →
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz →
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) →
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) →
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈ Sclosed) →
      (q.1 ∉ Sclosed →
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) = ⊥) ∧
      (q.1 ∈ Sclosed →
        ∃ v : ((H × H) × H),
          ERealFunction.compositePrimalOptimalValue φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) =
            -ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v ∧
          ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v ≠ ⊤) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  intro hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed
  -- Route correction: the old monolithic support proof mixed attainment, support membership, and
  -- value transport. Keep those three seams separate so the remaining blocker is owner-level.
  constructor
  · intro hq
    by_contra hμ
    -- Any nonexceptional primal value would force the support point back into the frozen closed
    -- span, contradicting the off-support hypothesis.
    exact
      hq <|
        translatedClosedSpanMembership_of_primalNeBot hA hB hri q
          (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hμ
  · intro hq
    obtain ⟨vCand, hvCand_neTop⟩ :=
      translatedNonTopDualCandidate_of_closedSpanPoint hA hB hri q
        (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
    have hμ_neBot :
        ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) ≠ ⊥ := by
      -- A single non-`⊤` dual point already rules out the exceptional primal branch.
      exact
        compositePrimalOptimalValue_neBot_of_exists_nonTopDualCandidate φtilt ψ
          ⟨vCand, hvCand_neTop⟩
    obtain ⟨v0, hv0Eq⟩ :=
      translatedAttainedDualValue_of_closedSpanPoint_of_primalNeBot hA hB hri q
        (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed hq
        hμ_neBot
    let D : ((H × H) × H) → EReal :=
      ERealFunction.compositeDualObjective φtilt ψ
        (ContinuousLinearMap.id ℝ (((H × H) × H)))
    have hv0_neTop : D v0 ≠ ⊤ := by
      intro hv0_top
      -- If the attained dual value were `⊤`, the attained primal value would collapse to `⊥`.
      apply hμ_neBot
      calc
        ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) =
            -D v0 := hv0Eq
        _ = ⊥ := by simp [D, hv0_top]
    exact ⟨v0, hv0Eq, by simpa [D] using hv0_neTop⟩

/-- Helper for Theorem 25.2: under the stronger lifted `sri` hypothesis, the full lifted
conjugate is either `⊤` or it is attained by a concrete split of the two pullback conjugates, and
the attained branch is automatically finite above. This records the exact same-space conclusion
before the weaker projected-`ri` hypothesis is transported to the lifted support test. -/
private theorem liftedConjugate_topOrSplitFinite_of_zero_mem_sri_lifted
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsriLifted : (0 : ((H × H) × H)) ∈
      sri
        (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)))
    (q0 : ((H × H) × H)) :
    (liftedFitzpatrickPullbackSum hA hB)∗ q0 = ⊤ ∨
      ∃ r : ((H × H) × H),
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - r)) ∧
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 < ⊤ := by
  let φ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstLastFitzpatrickIoi hA
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  have hφ : φ ∈ Γ₀(((H × H) × H)) := by
    -- Freeze the first pulled-back Fitzpatrick owner in the canonical `Γ₀` interface.
    simpa [φ] using liftedFirstLastFitzpatrickIoi_mem_gammaZero hA
  have hψ : ψ ∈ Γ₀(((H × H) × H)) := by
    -- The second pullback uses the same `Γ₀` packaging.
    simpa [ψ] using liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB
  let χ : ((H × H) × H) → EReal :=
    ERealFunction.infimalConvolution (gammaZeroConjugate φ hφ) (gammaZeroConjugate ψ hψ)
  have hconj :
      (liftedFitzpatrickPullbackSum hA hB)∗ =
        χ := by
    -- Under lifted `sri`, the full lifted sum conjugate is exactly the dual infimal convolution.
    simpa [χ, liftedFitzpatrickPullbackSum, φ, ψ] using
      ERealFunction.InfimalConvolutionRegularity.conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        φ ψ hφ hψ hsriLifted
  have hExact :
      infimalConvolution.Exact (gammaZeroConjugate φ hφ) (gammaZeroConjugate ψ hψ) := by
    -- The same lifted `sri` hypothesis gives exactness of that infimal convolution.
    simpa [φ, ψ] using
      ERealFunction.InfimalConvolutionRegularity.infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
        φ ψ hφ hψ hsriLifted
  by_cases htop : (liftedFitzpatrickPullbackSum hA hB)∗ q0 = ⊤
  · -- Outside the lifted conjugate domain, the desired dichotomy is immediate.
    exact Or.inl htop
  · -- On the finite branch, exactness produces a concrete split at `q0`.
    have hdom :
        q0 ∈ ERealFunction.dom χ := by
      rw [mem_dom_iff_ne_top]
      intro htopInf
      exact htop ((congrFun hconj q0).trans htopInf)
    rcases hExact hdom with ⟨r, hr⟩
    refine Or.inr ⟨r, ?_, lt_top_iff_ne_top.mpr htop⟩
    calc
      (liftedFitzpatrickPullbackSum hA hB)∗ q0 = χ q0 := by
            simpa using congrFun hconj q0
      _ = (gammaZeroConjugate φ hφ r : EReal) +
            (gammaZeroConjugate ψ hψ (q0 - r) : EReal) := hr
      _ = (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - r)) := by
            simp [gammaZeroConjugate, φ, ψ]

/-- Helper for Theorem 25.2: if the first coordinate of the zero-second slice lies outside the
projected closed span, then that zero-second point also lies outside the closed span of the
literal lifted support surface. This freezes the off-support branch in ambient lifted coordinates.
-/
private theorem translatedTiltedCompositeZeroDomainData_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q0 : ((H × H) × H)) :
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    ∃ z : ((H × H) × H),
      z ∈ effectiveDomain φtilt ∧
      z ∈ effectiveDomain ψ ∧
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) ∧
      ψz ∈ Γ₀(((H × H) × H)) ∧
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        effectiveDomain ψ - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain φz ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz ∧
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) ∧
      ∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v := by
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  rcases exists_common_mem_effectiveDomain_tiltedLiftedPair_of_zero_mem_ri hA hB hri q0 with
    ⟨z, hzφ, hzψ⟩
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  have hφz_gamma : φz ∈ Γ₀(((H × H) × H)) := by
    -- Translate the affine-tilted first owner so the common domain witness becomes the origin.
    simpa [φz, φtilt] using
      translate_mem_gammaZero
        (f := φtilt)
        (affineTiltedLiftedFirstLast_memGammaZero_eqDom hA q0).1 z
  have hψz_gamma : ψz ∈ Γ₀(((H × H) × H)) := by
    -- The second lifted pullback admits the same translation packaging.
    simpa [ψz, ψ] using
      translate_mem_gammaZero (f := ψ) (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB) z
  have hregular :
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        effectiveDomain ψ - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain φz ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz ∧
      ∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v := by
    -- Freeze the exact same-space regularity surface and dual objective before the closed-span
    -- restriction is introduced.
    simpa [φz, ψz, φtilt, ψ] using
      ERealFunction.translated_composite_data_preserves_regular_set
        (f := φtilt) (g := ψ)
        (L := ContinuousLinearMap.id ℝ (((H × H) × H)))
        (a := z) hzφ (b := z) hzψ rfl
  have hprimal :
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
    -- The same compensating translation preserves the identity-map primal infimum.
    simpa [φz, ψz, φtilt, ψ] using
      ERealFunction.translated_compositePrimalOptimalValue_eq_original_of_image_domain_witness
        (f := φtilt) (g := ψ)
        (L := ContinuousLinearMap.id ℝ (((H × H) × H)))
        (a := z) (b := z) rfl
  rcases hregular with ⟨hregular, hzeroφz, hzeroψz, hdual⟩
  refine ⟨z, hzφ, hzψ, hφz_gamma, hψz_gamma, hregular, hzeroφz, hzeroψz, hprimal, hdual⟩

/-- Helper for Theorem 25.2: in the same-space identity-map case, translating both owners by a
common effective-domain point preserves the regularity surface in the literal owner order
`effectiveDomain f - effectiveDomain g`. This removes the repeated `ψ - φ` versus `φ - ψ`
transport churn from the remaining closed-span argument. -/
private theorem translatedSameSpaceDifference_eq_original
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) {z : E}
    (hzf : z ∈ effectiveDomain f) (hzg : z ∈ effectiveDomain g) :
    let fz : E → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + z)
    let gz : E → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + z)
    effectiveDomain fz - effectiveDomain gz = effectiveDomain f - effectiveDomain g := by
  -- Route correction: invoke the generic translation theorem with the two owners swapped so the
  -- resulting support equality is already in the literal `f - g` order used downstream.
  simpa using
    (ERealFunction.translated_composite_data_preserves_regular_set
      (f := g) (g := f)
      (L := ContinuousLinearMap.id ℝ E)
      (a := z) hzg (b := z) hzf rfl).1

/-- Helper for Theorem 25.2: the closed span of the same-space regularity surface is unchanged by
translating both owners by a common effective-domain point. This packages the ambient carrier
normalization once before the remaining closed-span core argument. -/
private theorem translatedSameSpaceDifferenceClosedSpan_eq_original
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) {z : E}
    (hzf : z ∈ effectiveDomain f) (hzg : z ∈ effectiveDomain g) :
    let fz : E → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + z)
    let gz : E → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + z)
    ((Submodule.span ℝ (effectiveDomain fz - effectiveDomain gz)).topologicalClosure : Set E) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set E) := by
  let fz : E → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + z)
  let gz : E → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + z)
  -- Freeze the translated support equality first, then transport it through `span` and closure.
  simpa [fz, gz] using
    congrArg
      (fun S : Set E ↦ ((Submodule.span ℝ S).topologicalClosure : Set E))
      (translatedSameSpaceDifference_eq_original (f := f) (g := g) hzf hzg)

/-- Helper for Theorem 25.2: translating the affine-tilted same-space pair by a common
effective-domain point does not change the closed-span support test for the zero-second slice.
This packages the remaining ambient/translated carrier comparison in the exact spelling needed by
the projected closed-span branch split. -/
private theorem
    translatedTiltedZeroSecond_mem_translatedSupportClosedSpan_iff_fst_mem_projectedClosedSpan
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    ∀ {z : ((H × H) × H)},
      z ∈ effectiveDomain φtilt →
      z ∈ effectiveDomain ψ →
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      q0 ∈
        ((Submodule.span ℝ
          (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
            Set (((H × H) × H))) ↔
        q.1 ∈
          (((Submodule.span ℝ
            (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
              Set H)) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  dsimp [q0, φtilt, ψ]
  intro z hzφ hzψ
  let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
  let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
  have hclosed :
      ((Submodule.span ℝ (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
          Set (((H × H) × H))) =
        ((Submodule.span ℝ (effectiveDomain φtilt - effectiveDomain ψ)).topologicalClosure :
          Set (((H × H) × H))) := by
    -- Discard the compensating translation in the same-space closed-span carrier once.
    have hsurface :
        effectiveDomain φz - effectiveDomain ψz =
          effectiveDomain φtilt - effectiveDomain ψ := by
      simpa [φz, ψz] using
        translatedSameSpaceDifference_eq_original
          (f := φtilt) (g := ψ) (hzf := hzφ) (hzg := hzψ)
    rw [hsurface]
  -- Compare translated support membership to the frozen tilted support test in two small steps.
  calc
    q0 ∈
        ((Submodule.span ℝ (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
          Set (((H × H) × H))) ↔
      q0 ∈
        ((Submodule.span ℝ (effectiveDomain φtilt - effectiveDomain ψ)).topologicalClosure :
          Set (((H × H) × H))) := by
            rw [hclosed]
    _ ↔
      q.1 ∈
        ((Submodule.span ℝ
          (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
            Set H) := by
              -- Avoid reopening the closed-span carrier normalization through `simpa`; the
              -- already-frozen theorem is exactly the required membership test.
              exact
                tiltedZeroSecond_mem_tiltedProjectedClosedSpan_iff_fst_mem_projectedClosedSpan
                  hA hB hri q

/-- Helper for Theorem 25.2: once two same-space owners both contain the origin, each effective
domain already lies in the closed span of their difference surface. This is the closed-span
carrier used by the later restricted support argument. -/
private theorem effectiveDomain_subset_sameSpaceDifferenceClosedSpan_of_zero_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal))
    (hzero_f : (0 : E) ∈ effectiveDomain f)
    (hzero_g : (0 : E) ∈ effectiveDomain g) :
    effectiveDomain f ⊆
        (((((Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).topologicalClosure :
            Submodule ℝ E) : Set E))) ∧
      effectiveDomain g ⊆
        (((((Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).topologicalClosure :
            Submodule ℝ E) : Set E))) := by
  constructor
  · intro x hx
    have hnegx :
        -x ∈ effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f := by
      refine Set.mem_sub.mpr ⟨0, hzero_g, x, ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · simp
    have hx_span :
        x ∈ Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f) := by
      -- The generator `-x = 0 - x` lies in the support surface, so negating it puts `x` in the
      -- span as well.
      simpa using
        Submodule.neg_mem
          (Submodule.span ℝ
            (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f))
          (Submodule.subset_span hnegx)
    exact (Submodule.span ℝ
      (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).le_topologicalClosure
        hx_span
  · intro y hy
    have hy_diff :
        y ∈ effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f := by
      refine Set.mem_sub.mpr ⟨y, hy, 0, ?_, ?_⟩
      · exact ⟨0, hzero_f, by simp⟩
      · simp
    have hy_span :
        y ∈ Submodule.span ℝ
          (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f) :=
      Submodule.subset_span hy_diff
    exact (Submodule.span ℝ
      (effectiveDomain g - (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)).le_topologicalClosure
        hy_span

/-- Helper for Theorem 25.2: if two same-space effective domains already lie in a closed
subspace `B`, then the restricted identity-map support surface is exactly the subtype preimage of
the ambient support surface. This isolates the remaining closed-span work from ambient/subtype
set-transport noise. -/
private theorem sameSpaceDifference_subtypePreimage_eq_of_effectiveDomain_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : ClosedSubmodule ℝ E}
    (f g : E → Set.Ioi (⊥ : EReal))
    (hfB : effectiveDomain f ⊆ (B : Set E))
    (hgB : effectiveDomain g ⊆ (B : Set E)) :
    effectiveDomain (fun y : (B : Submodule ℝ E) ↦ g y) -
        (ContinuousLinearMap.id ℝ (B : Submodule ℝ E)) ''
          effectiveDomain (fun x : (B : Submodule ℝ E) ↦ f x) =
      ((↑) ⁻¹' (effectiveDomain g -
        (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)) := by
  ext y
  constructor
  · rintro ⟨u, hu, w, hw, huw⟩
    rcases hw with ⟨v, hv, rfl⟩
    -- Forget the subtype carrier once; the restricted witnesses are already ambient witnesses.
    refine Set.mem_sub.mpr ⟨(u : E), ?_, (v : E), ?_, ?_⟩
    · simpa using hu
    · exact ⟨(v : E), by simpa using hv, rfl⟩
    · exact congrArg (fun t : (B : Submodule ℝ E) ↦ (t : E)) huw
  · intro hy
    rcases Set.mem_sub.mp hy with ⟨u, hu, w, hw, huw⟩
    rcases hw with ⟨v, hv, rfl⟩
    let uB : (B : Submodule ℝ E) := ⟨u, hgB hu⟩
    let vB : (B : Submodule ℝ E) := ⟨v, hfB hv⟩
    -- Repackage the ambient witnesses inside the closed subspace that contains both domains.
    refine Set.mem_sub.mpr ⟨uB, ?_, vB, ?_, ?_⟩
    · simpa [uB] using hu
    · exact ⟨vB, by simpa [vB] using hv, rfl⟩
    · apply Subtype.ext
      simpa [uB, vB] using huw

/-- Helper for Theorem 25.2: in the same-space zero-domain situation, restricting both owners to
the closed span of their literal difference surface rewrites the restricted support set to the
subtype preimage of the ambient one. This packages the exact closed-span surface normalization
used by the translated support branch. -/
private theorem translatedTiltedClosedSpanData_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let q0 : ((H × H) × H) := (q, (0 : H))
    let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
      affineTiltIoiLocal
        (liftedFirstLastFitzpatrickIoi hA)
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
    let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
    ∃ z : ((H × H) × H),
      z ∈ effectiveDomain φtilt ∧
      z ∈ effectiveDomain ψ ∧
      let φz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun x ↦ φtilt (x + z)
      let ψz : ((H × H) × H) → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (y + z)
      φz ∈ Γ₀(((H × H) × H)) ∧
      ψz ∈ Γ₀(((H × H) × H)) ∧
      effectiveDomain ψz - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φz =
        effectiveDomain ψ - (ContinuousLinearMap.id ℝ (((H × H) × H))) '' effectiveDomain φtilt ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain φz ∧
      (0 : ((H × H) × H)) ∈ effectiveDomain ψz ∧
      ERealFunction.compositePrimalOptimalValue φz ψz
          (ContinuousLinearMap.id ℝ (((H × H) × H))) =
        ERealFunction.compositePrimalOptimalValue φtilt ψ
          (ContinuousLinearMap.id ℝ (((H × H) × H))) ∧
      (∀ v : ((H × H) × H),
        ERealFunction.compositeDualObjective φz ψz
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v) ∧
      (q0 ∈
          ((Submodule.span ℝ
            (effectiveDomain φz - effectiveDomain ψz)).topologicalClosure :
              Set (((H × H) × H))) ↔
        q.1 ∈
          (((Submodule.span ℝ
            (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))).topologicalClosure :
              Set H))) := by
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  obtain ⟨z, hzφ, hzψ, hφz_gamma, hψz_gamma, hregular, hzeroφz, hzeroψz, hprimal, hdual⟩ :=
    translatedTiltedCompositeZeroDomainData_of_zero_mem_ri hA hB hri q0
  refine ⟨z, hzφ, hzψ, hφz_gamma, hψz_gamma, hregular, hzeroφz, hzeroψz, hprimal, hdual, ?_⟩
  -- Read the translated closed-span support test through the first coordinate once, after the
  -- common effective-domain translation has been frozen.
  exact
    translatedTiltedZeroSecond_mem_translatedSupportClosedSpan_iff_fst_mem_projectedClosedSpan
      hA hB hri q (z := z) hzφ hzψ

/-- Helper for Theorem 25.2: in the same-space identity-map setting, Proposition 15.22 already
turns a `core` hypothesis into an attained dual value. This is the safe owner-level attainment
theorem that the remaining translated closed-span bridge should feed. -/
private theorem exists_attainedCompositeDualValue_of_zero_mem_core_sameSpace
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(E)) (hg : g ∈ Γ₀(E))
    (hcore : (0 : E) ∈
      Set.core
        (effectiveDomain g -
          (ContinuousLinearMap.id ℝ E) '' effectiveDomain f)) :
    ∃ v : E,
      ERealFunction.compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ E) =
        -ERealFunction.compositeDualObjective f g (ContinuousLinearMap.id ℝ E) v := by
  -- Route correction: use the safe composite-duality owner from Proposition 15.22 rather than
  -- the unfinished shared same-space attainment file.
  rcases
      ERealFunction.exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain_support
        f hf g hg (ContinuousLinearMap.id ℝ E) hcore with
    ⟨v, -, hv⟩
  exact ⟨v, hv⟩

/-- Helper for Theorem 25.2: strong relative interior at the origin already implies ordinary
relative interior there. This is the only generic downgrade needed in the completed `sri` branch.
-/
private theorem zero_mem_ri_of_zero_mem_sri
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Set E} (hsri : (0 : E) ∈ sri S) :
    (0 : E) ∈ ri S := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨h0S, hcone⟩
  refine Set.mem_relativeInterior_iff.mpr ⟨h0S, ?_⟩
  have hcone_subset_span :
      cone (S - ({(0 : E)} : Set E)) ⊆
        (Submodule.span ℝ (S - ({(0 : E)} : Set E)) : Set E) := by
    -- The conical hull always lies in the linear span of the generating translate.
    exact
      ConvexCone.hull_min
        (C := (Submodule.span ℝ (S - ({(0 : E)} : Set E))).toConvexCone)
        (fun z hz ↦ Submodule.subset_span hz)
  apply Set.Subset.antisymm
  · exact hcone_subset_span
  · intro x hx
    -- The `sri` identity upgrades every span point to the same cone point.
    have hxClosed :
        x ∈
          ((Submodule.span ℝ (S - ({(0 : E)} : Set E))).topologicalClosure : Set E) := by
      exact (Submodule.span ℝ (S - ({(0 : E)} : Set E))).le_topologicalClosure hx
    rw [← hcone] at hxClosed
    exact hxClosed

/-- Helper for Theorem 25.2: under the projected `sri` hypothesis, every dual point of the
fiberwise Fitzpatrick owner is either infeasible or realized by a concrete split of the two
Fitzpatrick conjugates. This is the owner-level `⊤ ∨ split` alternative used in the completed
`sri` branch. -/
private theorem
    conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_topOrSplit_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (x u : H) :
    ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) = ⊤ ∨
      ∃ u₁ : H,
        ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
          ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) ∧
        ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) < ⊤ := by
  classical
  let q0 : ((H × H) × H) := (((u, x), (0 : H)))
  have hsriLifted :
      (0 : ((H × H) × H)) ∈
        sri
          (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
            effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)) := by
    -- Lift the projected `sri` witness once to the literal lifted support surface.
    simpa using zero_mem_sri_liftedFitzpatrickDifference_of_zero_mem_sri hA hB hsri
  have hrepr :
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 := by
    -- Rewrite the transpose-conjugate owner to the lifted zero-second conjugate slice.
    rw [transpose_apply,
      fitzpatrickFiberwiseInfimalConvolution_eq_infimalPostcomposition_liftedFitzpatrickPullbackSum
        hA hB]
    simpa [q0] using
      congrFun
        (ERealFunction.conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local
          (liftedFitzpatrickPullbackSum hA hB))
        (u, x)
  rcases liftedConjugate_topOrSplitFinite_of_zero_mem_sri_lifted hA hB hsriLifted q0 with
    htop | ⟨r, hr, hfin⟩
  · -- The infeasible lifted branch is exactly the `⊤` branch downstairs.
    exact Or.inl (hrepr.trans htop)
  · rcases r with ⟨⟨u₁, b⟩, v⟩
    have hleft_ne_bot :
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) ≠ ⊥ := by
      -- Fenchel conjugates of proper owners are never `⊥`.
      exact
        conjugate_ne_bot_of_effectiveDomain_nonempty
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA).2.nonempty
          (((u₁, b), v))
    have hright_ne_bot :
        (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - (((u₁, b), v)))) ≠ ⊥ := by
      -- The same non-`⊥` statement holds for the second lifted pullback conjugate.
      exact
        conjugate_ne_bot_of_effectiveDomain_nonempty
          (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB).2.nonempty
          (q0 - (((u₁, b), v)))
    have hb : b = 0 := by
      by_contra hb
      have hleft_top :
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) = ⊤ := by
        -- Any nonzero middle coordinate forces the first lifted conjugate to `⊤`.
        simpa [liftedFirstLastFitzpatrickIoi, Function.comp, hb] using
          (ERealFunction.conjugate_firstLastPullback_apply
            (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) u₁ b v)
      have hsum_top :
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (q0 - (((u₁, b), v))) : EReal) = ⊤ := by
        rw [hleft_top]
        exact EReal.top_add_of_ne_bot hright_ne_bot
      exact hfin.ne (hr.trans hsum_top)
    subst b
    have hv : v = x := by
      by_contra hv
      have hsub :
          q0 - (((u₁, (0 : H)), v)) =
            ((((u - u₁), x), -v) : ((H × H) × H)) := by
        -- Freeze the zero-second subtraction once before normalizing the second conjugate.
        ext <;> simp [q0, sub_eq_add_neg]
      have hright_top :
          (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
            (q0 - (((u₁, (0 : H)), v))) : EReal) = ⊤ := by
        have hneg : (-v : H) ≠ -x := by
          intro hnegEq
          apply hv
          simpa using congrArg Neg.neg hnegEq
        -- Off the branch `-v = -x`, the second lifted conjugate is forced to `⊤`.
        rw [hsub]
        simpa [liftedFirstDifferenceFitzpatrickIoi, Function.comp, hneg] using
          (ERealFunction.conjugate_firstDifferencePullback_apply
            (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB)
            (u - u₁) x (-v))
      have hsum_top :
          ((((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, (0 : H)), v))) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (q0 - (((u₁, (0 : H)), v)))) : EReal) = ⊤ := by
        rw [hright_top]
        exact EReal.add_top_of_ne_bot hleft_ne_bot
      exact hfin.ne (hr.trans hsum_top)
    subst v
    refine Or.inr ⟨u₁, ?_, ?_⟩
    · have hsub :
          q0 - (((u₁, (0 : H)), x)) =
            ((((u - u₁), x), -x) : ((H × H) × H)) := by
        -- Normalize the residual lifted split once before collapsing both pullback conjugates.
        ext <;> simp [q0, sub_eq_add_neg]
      calc
        ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
            (liftedFitzpatrickPullbackSum hA hB)∗ q0 := hrepr
        _ =
            (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, (0 : H)), x))) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (q0 - (((u₁, (0 : H)), x)))) := by
                  simpa [q0] using hr
        _ = ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) := by
              rw [ERealFunction.conjugate_firstLastPullback_apply
                (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) u₁ 0 x]
              rw [hsub]
              rw [ERealFunction.conjugate_firstDifferencePullback_apply
                (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB) (u - u₁) x (-x)]
              simp [fitzpatrickIoi, transpose_apply]
    · -- Transport the lifted finiteness statement back through the zero-second normalization.
      exact hrepr ▸ hfin

/-- Helper for Theorem 25.2: under the projected `sri` hypothesis, the contact set of the
transpose-conjugate owner is exactly `gra (A + B)`. This is the textbook identity `(25.6)` in the
completed `sri` branch. -/
private theorem
    mem_graph_add_iff_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_inner_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (x u : H) :
    (x, u) ∈ (A + B).graph ↔
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) = pairing (x, u) := by
  constructor
  · intro hu
    rw [SetValuedOperator.mem_graph] at hu
    rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    have hAu₁ :
        ((F[A])∗)ᵀ (x, u₁) = pairing (x, u₁) := by
      exact (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hA x u₁).1 hu₁
    have hBu₂ :
        ((F[B])∗)ᵀ (x, u₂) = pairing (x, u₂) := by
      exact (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hB x u₂).1 hu₂
    have hBuSplit :
        ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) = pairing (x, u₂) := by
      -- Freeze the concrete split coordinate before rewriting by the `B`-contact identity.
      calc
        ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) = ((F[B])∗)ᵀ (x, u₂) := by simp
        _ = pairing (x, u₂) := hBu₂
    refine le_antisymm ?_ (pairing_le_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_of_zero_mem_sri hA hB hsri x (u₁ + u₂))
    calc
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u₁ + u₂) ≤
          ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) := by
            exact
              conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_le_split
                hA hB x (u₁ + u₂) u₁
      _ = pairing (x, u₁) + pairing (x, u₂) := by
            rw [hAu₁, hBuSplit]
      _ = pairing (x, u₁ + u₂) := by
            simpa using (pairing_add_right x u₁ u₂).symm
  · intro hcontact
    rcases
        conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_topOrSplit_of_zero_mem_sri
          hA hB hsri x u with
      htop | ⟨u₁, hsplit, _⟩
    · exfalso
      have hpair_ne_top : pairing (x, u) ≠ ⊤ := by
        simpa [pairing_apply] using (EReal.coe_ne_top (⟪x, u⟫_ℝ))
      exact hpair_ne_top (hcontact.symm.trans htop)
    · have hsum :
          ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) = pairing (x, u) := by
        rw [← hsplit, hcontact]
      rcases splitConjugateContact_of_sum_eq_pairing hA hB hsum with ⟨hAu₁, hBu₂⟩
      exact mem_graph_add_of_fitzpatrickSplitContact hA hB hAu₁ hBu₂

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the Chapter 20 owner data for
the fiberwise Fitzpatrick infimal convolution are now fully available. This keeps the final
maximality proof flat. -/
private theorem conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_liftedZeroSecond
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (x u : H) :
    ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
      (liftedFitzpatrickPullbackSum hA hB)∗ (((u, x), (0 : H))) := by
  -- Rewrite the transpose-conjugate owner to the lifted zero-second conjugate slice once.
  rw [transpose_apply,
    fitzpatrickFiberwiseInfimalConvolution_eq_infimalPostcomposition_liftedFitzpatrickPullbackSum
      hA hB]
  simpa using
    congrFun
      (ERealFunction.conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local
        (liftedFitzpatrickPullbackSum hA hB))
      (u, x)

/-- Helper for Theorem 25.2: any finite lifted zero-second split already normalizes to the
ambient split formula for the transpose-conjugate Chapter 25 owner. This isolates the purely
algebraic zero-slice cleanup from the remaining projected closed-span branch theorem. -/
private theorem
    conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_split_of_liftedZeroSecond
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    {x u : H} {r : ((H × H) × H)}
    (hr :
      (liftedFitzpatrickPullbackSum hA hB)∗ (((u, x), (0 : H))) =
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
          (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
            ((((u, x), (0 : H))) - r)))
    (hfin : (liftedFitzpatrickPullbackSum hA hB)∗ (((u, x), (0 : H))) < ⊤) :
    ∃ u₁ : H,
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
        ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) ∧
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) < ⊤ := by
  classical
  let q0 : ((H × H) × H) := (((u, x), (0 : H)))
  have hrepr :
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 := by
    -- Freeze the ambient-to-lifted zero-second normalization before unpacking the split witness.
    simpa [q0] using
      conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_liftedZeroSecond hA hB x u
  rcases r with ⟨⟨u₁, b⟩, v⟩
  have hleft_ne_bot :
      (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) ≠ ⊥ := by
    -- Fenchel conjugates of proper owners are never `⊥`.
    exact
      conjugate_ne_bot_of_effectiveDomain_nonempty
        (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA).2.nonempty
        (((u₁, b), v))
  have hright_ne_bot :
      (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - (((u₁, b), v)))) ≠ ⊥ := by
    -- The same non-`⊥` statement holds for the second lifted pullback conjugate.
    exact
      conjugate_ne_bot_of_effectiveDomain_nonempty
        (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB).2.nonempty
        (q0 - (((u₁, b), v)))
  have hb : b = 0 := by
    by_contra hb
    have hleft_top :
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) = ⊤ := by
      -- Any nonzero middle coordinate forces the first lifted conjugate to `⊤`.
      simpa [liftedFirstLastFitzpatrickIoi, Function.comp, hb] using
        (ERealFunction.conjugate_firstLastPullback_apply
          (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) u₁ b v)
    have hsum_top :
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, b), v))) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
              (q0 - (((u₁, b), v))) : EReal) = ⊤ := by
      rw [hleft_top]
      exact EReal.top_add_of_ne_bot hright_ne_bot
    exact hfin.ne (hr.trans hsum_top)
  subst b
  have hv : v = x := by
    by_contra hv
    have hsub :
        q0 - (((u₁, (0 : H)), v)) =
          ((((u - u₁), x), -v) : ((H × H) × H)) := by
      -- Normalize the residual lifted split before collapsing the second conjugate.
      ext <;> simp [q0, sub_eq_add_neg]
    have hright_top :
        (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
          (q0 - (((u₁, (0 : H)), v))) : EReal) = ⊤ := by
      have hneg : (-v : H) ≠ -x := by
        intro hnegEq
        apply hv
        simpa using congrArg Neg.neg hnegEq
      -- Off the branch `-v = -x`, the second lifted conjugate is forced to `⊤`.
      rw [hsub]
      simpa [liftedFirstDifferenceFitzpatrickIoi, Function.comp, hneg] using
        (ERealFunction.conjugate_firstDifferencePullback_apply
          (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB)
          (u - u₁) x (-v))
    have hsum_top :
        ((((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, (0 : H)), v))) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
              (q0 - (((u₁, (0 : H)), v)))) : EReal) = ⊤ := by
      rw [hright_top]
      exact EReal.add_top_of_ne_bot hleft_ne_bot
    exact hfin.ne (hr.trans hsum_top)
  subst v
  refine ⟨u₁, ?_, ?_⟩
  · have hsub :
        q0 - (((u₁, (0 : H)), x)) =
          ((((u - u₁), x), -x) : ((H × H) × H)) := by
      -- Freeze the residual lifted split before collapsing both pullback conjugates.
      ext <;> simp [q0, sub_eq_add_neg]
    calc
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
          (liftedFitzpatrickPullbackSum hA hB)∗ q0 := hrepr
      _ =
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((u₁, (0 : H)), x))) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
              (q0 - (((u₁, (0 : H)), x)))) := by
                simpa [q0] using hr
      _ = ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) := by
            rw [ERealFunction.conjugate_firstLastPullback_apply
              (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) u₁ 0 x]
            rw [hsub]
            rw [ERealFunction.conjugate_firstDifferencePullback_apply
              (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB) (u - u₁) x (-x)]
            simp [fitzpatrickIoi, transpose_apply]
  · -- Transport the lifted finiteness statement back through the zero-second normalization.
    simpa [hrepr] using hfin

/-- Helper for Theorem 25.2: projected closed-span membership splits the zero-second lifted dual
problem into an infeasible off-support branch and a finite split branch on support. This is the
single remaining owner-level blocker for the direct `ri` route. -/
private theorem liftedZeroSliceTopOrSplitByProjectedClosedSpan_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))))
    (q : H × H) :
    let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
    let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
    (q.1 ∉ Sclosed →
      (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) = ⊤) ∧
    (q.1 ∈ Sclosed →
      ∃ r : ((H × H) × H),
        (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) =
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
            (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
              (((q, (0 : H))) - r)) ∧
        (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) < ⊤) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
  let q0 : ((H × H) × H) := (q, (0 : H))
  let φtilt : ((H × H) × H) → Set.Ioi (⊥ : EReal) :=
    affineTiltIoiLocal
      (liftedFirstLastFitzpatrickIoi hA)
      (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA) q0
  let ψ : ((H × H) × H) → Set.Ioi (⊥ : EReal) := liftedFirstDifferenceFitzpatrickIoi hB
  obtain ⟨z, hzφ, hzψ, hφz_gamma, hψz_gamma, _hregular, hzeroφz, hzeroψz, hprimal, hdual,
      hq0_closed⟩ :=
    translatedTiltedClosedSpanData_of_zero_mem_ri hA hB hri q
  have hsupport :=
    translatedFrozenSupportDichotomy_of_zero_mem_ri hA hB hri q
      (z := z) hzφ hzψ hφz_gamma hψz_gamma hzeroφz hzeroψz hprimal hdual hq0_closed
  constructor
  · intro hq
    have hprimal_bot := hsupport.1 hq
    have hswap :
        ERealFunction.compositePrimalOptimalValue ψ φtilt
            (ContinuousLinearMap.id ℝ (((H × H) × H))) =
          ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
      exact compositePrimalOptimalValue_id_comm ψ φtilt
    -- Rewrite the lifted zero-second value to the translated primal owner and discharge the
    -- off-support branch from the exceptional value `⊥`.
    calc
      (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) =
          -ERealFunction.compositePrimalOptimalValue ψ φtilt
            (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
              simpa [q0, φtilt, ψ] using
                tiltedZeroSlice_eq_neg_compositePrimalOptimalValue hA hB q0
      _ =
          -ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
              rw [hswap]
      _ = ⊤ := by simpa [hprimal_bot]
  · intro hq
    obtain ⟨v, hvEq, hvneTop⟩ := hsupport.2 hq
    let r : ((H × H) × H) := q0 - v
    have hzeroSlice :
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
          -ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
      calc
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
            -ERealFunction.compositePrimalOptimalValue ψ φtilt
              (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
                simpa [q0, φtilt, ψ] using
                  tiltedZeroSlice_eq_neg_compositePrimalOptimalValue hA hB q0
        _ =
            -ERealFunction.compositePrimalOptimalValue φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) := by
                rw [compositePrimalOptimalValue_id_comm ψ φtilt]
    have hvalue :
        -ERealFunction.compositePrimalOptimalValue φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) =
          ERealFunction.compositeDualObjective φtilt ψ
            (ContinuousLinearMap.id ℝ (((H × H) × H))) v := by
      -- Negate the attained translated-dual identity once before returning to the lifted split.
      simpa using congrArg Neg.neg hvEq
    refine ⟨r, ?_, ?_⟩
    · -- Normalize the translated attained dual value back to the literal lifted split formula.
      calc
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
            -ERealFunction.compositePrimalOptimalValue φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) := hzeroSlice
        _ =
            ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v := hvalue
        _ =
            (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) r) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (q0 - r)) := by
                simpa [r, q0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  tiltedCompositeDualObjective_eq_splitApply hA hB q0 r
    · -- The attained translated dual value is finite above, so the lifted zero-second value is too.
      calc
        (liftedFitzpatrickPullbackSum hA hB)∗ q0 =
            -ERealFunction.compositePrimalOptimalValue φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) := hzeroSlice
        _ =
            ERealFunction.compositeDualObjective φtilt ψ
              (ContinuousLinearMap.id ℝ (((H × H) × H))) v := hvalue
        _ < ⊤ := lt_top_iff_ne_top.mpr hvneTop

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the Chapter 20 owner data for
the fiberwise Fitzpatrick infimal convolution are now fully available. This keeps the final
maximality proof flat. -/
private theorem ambientConjugateFiniteShiftedSecondCoordinates_of_finiteLiftedConjugate
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsriLifted : (0 : ((H × H) × H)) ∈
      sri
        (effectiveDomain (liftedFirstLastFitzpatrickIoi hA) -
          effectiveDomain (liftedFirstDifferenceFitzpatrickIoi hB)))
    {p : ((H × H) × H)}
    (hp : (liftedFitzpatrickPullbackSum hA hB)∗ p < ⊤) :
    ∃ uA : H,
      ((fitzpatrickIoi hA).asEReal∗ (uA, p.1.2 + p.2)) < ⊤ ∧
        ((fitzpatrickIoi hB).asEReal∗ (p.1.1 - uA, p.1.2)) < ⊤ := by
  classical
  rcases liftedConjugate_topOrSplitFinite_of_zero_mem_sri_lifted hA hB hsriLifted p with
    htop | ⟨r, hr, hfin⟩
  · exfalso
    exact hp.ne htop
  · rcases r with ⟨⟨uA, b⟩, v⟩
    have hleft_ne_bot :
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((uA, b), v))) ≠ ⊥ := by
      -- Fenchel conjugates of proper owners are never `⊥`.
      exact
        conjugate_ne_bot_of_effectiveDomain_nonempty
          (liftedFirstLastFitzpatrickIoi_mem_gammaZero hA).2.nonempty
          (((uA, b), v))
    have hright_ne_bot :
        (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗) (p - (((uA, b), v)))) ≠ ⊥ := by
      -- The same non-`⊥` statement holds for the second lifted pullback conjugate.
      exact
        conjugate_ne_bot_of_effectiveDomain_nonempty
          (liftedFirstDifferenceFitzpatrickIoi_mem_gammaZero hB).2.nonempty
          (p - (((uA, b), v)))
    have hleft_lt_top :
        (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((uA, b), v))) < ⊤ := by
      -- The attained split stays finite above because the whole lifted conjugate value is finite.
      refine lt_top_iff_ne_top.mpr fun hleft_top ↦ ?_
      have hsum_top :
          ((((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((uA, b), v))) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (p - (((uA, b), v)))) : EReal) = ⊤ := by
        rw [hleft_top]
        exact EReal.top_add_of_ne_bot hright_ne_bot
      exact hfin.ne (hr.trans hsum_top)
    have hb : b = 0 := by
      by_contra hb
      have hleft_top :
          (((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((uA, b), v))) = ⊤ := by
        -- The first pulled-back conjugate is finite only on the zero middle slice.
        simpa [liftedFirstLastFitzpatrickIoi, Function.comp, hb] using
          (ERealFunction.conjugate_firstLastPullback_apply
            (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) uA b v)
      exact (ne_of_lt hleft_lt_top) hleft_top
    subst b
    have hright_lt_top :
        (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
          (p - (((uA, (0 : H)), v)))) < ⊤ := by
      -- The second split summand is finite for the same reason.
      refine lt_top_iff_ne_top.mpr fun hright_top ↦ ?_
      have hsum_top :
          ((((liftedFirstLastFitzpatrickIoi hA).asEReal∗) (((uA, (0 : H)), v))) +
              (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
                (p - (((uA, (0 : H)), v)))) : EReal) = ⊤ := by
        rw [hright_top]
        exact EReal.add_top_of_ne_bot hleft_ne_bot
      exact hfin.ne (hr.trans hsum_top)
    have hsub :
        p - (((uA, (0 : H)), v)) =
          ((((p.1.1 - uA), p.1.2), p.2 - v) : ((H × H) × H)) := by
      -- Freeze the residual lifted split before normalizing the second conjugate.
      ext <;> simp [sub_eq_add_neg]
    have hslice : p.2 - v = -p.1.2 := by
      by_contra hslice
      have hright_top :
          (((liftedFirstDifferenceFitzpatrickIoi hB).asEReal∗)
            (p - (((uA, (0 : H)), v))) : EReal) = ⊤ := by
        -- Off the branch `p.2 - v = -p.1.2`, the second pulled-back conjugate is `⊤`.
        rw [hsub]
        simpa [liftedFirstDifferenceFitzpatrickIoi, Function.comp, hslice] using
          (ERealFunction.conjugate_firstDifferencePullback_apply
            (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB)
            (p.1.1 - uA) p.1.2 (p.2 - v))
      exact (ne_of_lt hright_lt_top) hright_top
    have hv : v = p.1.2 + p.2 := by
      -- Solve the residual slice equation once before reading the first ambient conjugate value.
      have hv' : p.2 = -p.1.2 + v := (sub_eq_iff_eq_add).mp hslice
      calc
        v = p.1.2 + (-p.1.2 + v) := by simp [add_assoc]
        _ = p.1.2 + p.2 := by rw [hv'.symm]
    have hAuA :
        ((fitzpatrickIoi hA).asEReal∗ (uA, p.1.2 + p.2)) < ⊤ := by
      -- Collapse the first pulled-back conjugate to the ambient one on its forced slice.
      rw [← hv]
      rw [ERealFunction.conjugate_firstLastPullback_apply
        (φ := fitzpatrickIoi hA) (hφ := fitzpatrickIoi_mem_gammaZero hA) uA 0 v] at hleft_lt_top
      simpa using hleft_lt_top
    have hBuB :
        ((fitzpatrickIoi hB).asEReal∗ (p.1.1 - uA, p.1.2)) < ⊤ := by
      -- Collapse the second pulled-back conjugate on the forced negative slice.
      rw [hsub] at hright_lt_top
      rw [ERealFunction.conjugate_firstDifferencePullback_apply
        (ψ := fitzpatrickIoi hB) (hψ := fitzpatrickIoi_mem_gammaZero hB)
        (p.1.1 - uA) p.1.2 (p.2 - v)] at hright_lt_top
      simpa [hslice] using hright_lt_top
    exact ⟨uA, hAuA, hBuB⟩

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the Chapter 20 owner data for
the fiberwise Fitzpatrick infimal convolution are now fully available. This keeps the final
maximality proof flat. -/
private theorem existsFiniteZeroSecondLiftedConjugate_of_zeroMemRI
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    ∃ q : H × H, (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) < ⊤ := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
  have hzero_closed : (0 : H) ∈ Sclosed := by
    -- The closed linear span always contains the origin, so the zero-second slice is on support.
    exact (Submodule.span ℝ S0).le_topologicalClosure (Submodule.zero_mem _)
  rcases
      (liftedZeroSliceTopOrSplitByProjectedClosedSpan_of_zero_mem_ri
        hA hB hri (0, 0)).2 hzero_closed with
    ⟨r, hr, hfin⟩
  -- The support branch at `q = 0` already gives the required finite zero-second witness.
  exact ⟨(0, 0), hfin⟩

/-- Helper for Theorem 25.2: one finite zero-second value of the lifted pullback conjugate
already gives a point in the conjugate domain of the ambient fiberwise Fitzpatrick owner. -/
private theorem fiberwiseConjugateDomNonempty_of_finiteLiftedZeroSecond
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hfinite :
      ∃ q : H × H, (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) < ⊤) :
    (ERealFunction.dom
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)).Nonempty := by
  rcases hfinite with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [ERealFunction.mem_dom_iff]
  -- Rewrite the ambient conjugate to the lifted zero-second conjugate slice before using the
  -- supplied finite witness.
  rw [fitzpatrickFiberwiseInfimalConvolution_eq_infimalPostcomposition_liftedFitzpatrickPullbackSum
    hA hB]
  have hzeroSlice :
      (Prod.fst ▷ liftedFitzpatrickPullbackSum hA hB)∗ q =
        (liftedFitzpatrickPullbackSum hA hB)∗ (q, (0 : H)) := by
    simpa using
      congrFun
        (ERealFunction.conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_local
          (liftedFitzpatrickPullbackSum hA hB))
        q
  rwa [hzeroSlice]

/-- Helper for Theorem 25.2: under the projected `ri` hypothesis, the Chapter 20 owner data for
the fiberwise Fitzpatrick infimal convolution are now fully available. This keeps the final
maximality proof flat. -/
private theorem
    fitzpatrickFiberwiseInfimalConvolution_conjugate_dom_nonempty_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    (ERealFunction.dom
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)).Nonempty := by
  -- Reuse the literal lifted zero-second finiteness witness once it has been proved.
  exact
    fiberwiseConjugateDomNonempty_of_finiteLiftedZeroSecond
      hA hB (existsFiniteZeroSecondLiftedConjugate_of_zeroMemRI hA hB hri)

/-- Helper for Theorem 25.2: the projected `ri` hypothesis already gives the ambient Chapter 25
fiberwise owner as a proper convex function. This isolates the primal-side regularity that does
not depend on the remaining zero-second dual witness. -/
private theorem fitzpatrickFiberwiseInfimalConvolution_ownerRegularity_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    IsProper (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)) ∧
      IsConvex (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)) := by
  have hF_dom_nonempty :
      (ERealFunction.dom
        (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))).Nonempty := by
    rcases liftedPullbackOwners_effectiveDomain_inter_nonempty_of_zero_mem_ri hA hB hri with
      ⟨q, hqA, hqB⟩
    refine ⟨q.1, ?_⟩
    -- Evaluate the infimal convolution at the common lifted-domain witness.
    rw [ERealFunction.mem_dom_iff, fitzpatrickFiberwiseInfimalConvolution,
      ERealFunction.infimalConvolution_apply]
    refine lt_of_le_of_lt (iInf_le _ q.2) ?_
    have hqA_lt : (liftedFirstLastFitzpatrickIoi hA q : EReal) < ⊤ :=
      mem_effectiveDomain_iff.mp hqA
    have hqB_lt : (liftedFirstDifferenceFitzpatrickIoi hB q : EReal) < ⊤ :=
      mem_effectiveDomain_iff.mp hqB
    exact EReal.add_lt_top (ne_of_lt hqA_lt) (ne_of_lt hqB_lt)
  have hF_proper :
      IsProper (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)) := by
    constructor
    · intro p
      by_contra hpbot
      have hpair_bot :
          (⊥ : EReal) < pairing p := by
        -- The Hilbert pairing is always a finite real value, hence strictly above `⊥`.
        change (⊥ : EReal) < (((⟪p.1, p.2⟫_ℝ : ℝ) : EReal))
        exact EReal.bot_lt_coe (⟪p.1, p.2⟫_ℝ)
      have hle := pairing_le_fitzpatrickFiberwiseInfimalConvolution hA hB p.1 p.2
      rw [hpbot] at hle
      exact not_le_of_gt hpair_bot hle
    · exact hF_dom_nonempty
  have hLift_gamma :
      liftedFirstLastFitzpatrickIoi hA + liftedFirstDifferenceFitzpatrickIoi hB ∈
        Γ₀(((H × H) × H)) :=
    liftedPullbackSum_mem_gammaZero_of_zero_mem_ri hA hB hri
  have hLift_conv :
      IsConvex (liftedFitzpatrickPullbackSum hA hB) := by
    -- Read convexity of the lifted owner through its packaged `Γ₀` datum once.
    simpa [liftedFitzpatrickPullbackSum] using
      ((mem_gamma_iff _).1 (asEReal_mem_gamma_of_mem_gammaZero hLift_gamma)).1
  have hF_epi :
      Convex ℝ
        (epigraph (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))) := by
    -- Convexity survives the first-projection infimal postcomposition of the lifted owner.
    rw [fitzpatrickFiberwiseInfimalConvolution_eq_infimalPostcomposition_liftedFitzpatrickPullbackSum
      hA hB]
    simpa [liftedFitzpatrickPullbackSum] using
      convex_epigraph_infimalPostcomposition
        (liftedFirstLastFitzpatrickIoi hA + liftedFirstDifferenceFitzpatrickIoi hB)
        ((ContinuousLinearMap.fst ℝ (H × H) H).toAffineMap)
        (convex_epigraph_of_isConvex_ereal hLift_conv)
  have hF_conv :
      IsConvex (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)) := by
    -- Convert epigraph convexity back to Jensen convexity for the Chapter 25 owner.
    exact isConvex_of_convex_epigraph_of_isProper hF_epi hF_proper
  exact ⟨hF_proper, hF_conv⟩

/-- Helper for Theorem 25.2: under the projected `sri` hypothesis, the Chapter 20 owner data for
the fiberwise Fitzpatrick infimal convolution are now fully available. This keeps the final
maximality proof flat. -/
private theorem fitzpatrickFiberwiseInfimalConvolution_dualOwnerData_of_zero_mem_sri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    (∀ x u : H,
        pairing (x, u) ≤
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u)) ∧
      IsConvex (fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)) ∧
      IsProper ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗) := by
  have hri :
      (0 : H) ∈ ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))) :=
    zero_mem_ri_of_zero_mem_sri hsri
  have hdualLower :
      ∀ x u : H,
        pairing (x, u) ≤
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) := by
    intro x u
    exact
      pairing_le_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_of_zero_mem_sri
        hA hB hsri x u
  obtain ⟨hF_proper, hF_conv⟩ :=
    fitzpatrickFiberwiseInfimalConvolution_ownerRegularity_of_zero_mem_ri hA hB hri
  have hFstar_dom_nonempty :
      (ERealFunction.dom
        ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)).Nonempty := by
    -- Reuse the projected-`ri` ambient dual-domain witness; the stronger `sri` hypothesis is only
    -- needed for the pointwise contact identity, not for nonemptiness of the conjugate domain.
    exact
      fitzpatrickFiberwiseInfimalConvolution_conjugate_dom_nonempty_of_zero_mem_ri
        hA hB hri
  have hFstar_proper :
      IsProper ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗) := by
    constructor
    · intro z
      exact conjugate_ne_bot_of_isProper hF_proper z
    · exact hFstar_dom_nonempty
  exact ⟨hdualLower, hF_conv, hFstar_proper⟩

/-- Helper for Theorem 25.2: the direct `ri` route should provide both the dual lower bound and
the contact-set characterization without passing through a global projected `sri` upgrade. -/
private theorem fitzpatrickFiberwiseInfimalConvolution_dualContactData_of_zero_mem_ri
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    (∀ x u : H,
        pairing (x, u) ≤
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u)) ∧
      (∀ x u : H,
        (x, u) ∈ (A + B).graph ↔
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
            pairing (x, u)) := by
  let S0 : Set H := Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B]))
  let Sclosed : Set H := ((Submodule.span ℝ S0).topologicalClosure : Set H)
  have htopOrSplit :
      ∀ x u : H,
        ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) = ⊤ ∨
          ∃ u₁ : H,
            ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
              ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) ∧
            ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) < ⊤ := by
    intro x u
    by_cases hq : u ∈ Sclosed
    · rcases
        (liftedZeroSliceTopOrSplitByProjectedClosedSpan_of_zero_mem_ri
          hA hB hri (u, x)).2 hq with
        ⟨r, hr, hfin⟩
      rcases
          conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_split_of_liftedZeroSecond
            hA hB (x := x) (u := u) hr hfin with
        ⟨u₁, hsplit, hfin'⟩
      exact Or.inr ⟨u₁, hsplit, hfin'⟩
    · have htopLift :
          (liftedFitzpatrickPullbackSum hA hB)∗ (((u, x), (0 : H))) = ⊤ := by
        exact
          (liftedZeroSliceTopOrSplitByProjectedClosedSpan_of_zero_mem_ri
            hA hB hri (u, x)).1 hq
      have hrepr :
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) =
            (liftedFitzpatrickPullbackSum hA hB)∗ (((u, x), (0 : H))) := by
        exact
          conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_liftedZeroSecond
            hA hB x u
      exact Or.inl (hrepr.trans htopLift)
  have hdualLower :
      ∀ x u : H,
        pairing (x, u) ≤
          ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u) := by
    intro x u
    rcases htopOrSplit x u with htop | ⟨u₁, hsplit, _⟩
    · simpa [htop] using (le_top : pairing (x, u) ≤ (⊤ : EReal))
    · exact
        pairing_le_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_of_split
          hA hB hsplit
  refine ⟨hdualLower, ?_⟩
  intro x u
  constructor
  · intro hu
    rw [SetValuedOperator.mem_graph] at hu
    rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    have hAu₁ :
        ((F[A])∗)ᵀ (x, u₁) = pairing (x, u₁) := by
      exact (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hA x u₁).1 hu₁
    have hBu₂ :
        ((F[B])∗)ᵀ (x, u₂) = pairing (x, u₂) := by
      exact (Maximal.mem_graph_iff_conjugateTranspose_fitzpatrickFunction_eq_inner hB x u₂).1 hu₂
    have hBuSplit :
        ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) = pairing (x, u₂) := by
      -- Freeze the concrete split coordinate before rewriting by the `B`-contact identity.
      calc
        ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) = ((F[B])∗)ᵀ (x, u₂) := by simp
        _ = pairing (x, u₂) := hBu₂
    refine le_antisymm ?_ (hdualLower x (u₁ + u₂))
    calc
      ((fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B))∗)ᵀ (x, u₁ + u₂) ≤
          ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, (u₁ + u₂) - u₁) := by
            exact
              conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_le_split
                hA hB x (u₁ + u₂) u₁
      _ = pairing (x, u₁) + pairing (x, u₂) := by
            rw [hAu₁, hBuSplit]
      _ = pairing (x, u₁ + u₂) := by
            simpa using (pairing_add_right x u₁ u₂).symm
  · intro hcontact
    rcases htopOrSplit x u with htop | ⟨u₁, hsplit, _⟩
    · exfalso
      have hpair_ne_top : pairing (x, u) ≠ ⊤ := by
        simpa [pairing_apply] using (EReal.coe_ne_top (⟪x, u⟫_ℝ))
      exact hpair_ne_top (hcontact.symm.trans htop)
    · have hsum :
          ((F[A])∗)ᵀ (x, u₁) + ((F[B])∗)ᵀ (x, u - u₁) = pairing (x, u) := by
        rw [← hsplit, hcontact]
      rcases splitConjugateContact_of_sum_eq_pairing hA hB hsum with ⟨hAu₁, hBu₂⟩
      exact mem_graph_add_of_fitzpatrickSplitContact hA hB hAu₁ hBu₂

/-- Theorem 25.2: if `A` and `B` are maximally monotone and
`0 ∈ ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))`, then `A + B` is
maximally monotone. -/
theorem Maximal.add_of_zero_mem_ri_fst_image_dom_fitzpatrick_sub
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hri : (0 : H) ∈
      ri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    Maximal IsMonotone (A + B) := by
  let Fsum : H × H → EReal := fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)
  obtain ⟨hdualLower, hcontact⟩ :=
    fitzpatrickFiberwiseInfimalConvolution_dualContactData_of_zero_mem_ri hA hB hri
  obtain ⟨hFsum_proper, hFsum_conv⟩ :=
    fitzpatrickFiberwiseInfimalConvolution_ownerRegularity_of_zero_mem_ri hA hB hri
  have hFsum_star_proper : IsProper (Fsum∗) := by
    constructor
    · intro z
      exact conjugate_ne_bot_of_isProper hFsum_proper z
    · exact fitzpatrickFiberwiseInfimalConvolution_conjugate_dom_nonempty_of_zero_mem_ri hA hB hri
  have hFsum_ge : ∀ x u : H, pairing (x, u) ≤ Fsum (x, u) := by
    -- This is the primal inequality `F ≥ ⟪·, ·⟫`, unchanged from the completed `sri` branch.
    intro x u
    exact pairing_le_fitzpatrickFiberwiseInfimalConvolution hA hB x u
  have hmax_contact :
      Maximal IsMonotone (pairingEqualityOperator ((Fsum∗)ᵀ)) := by
    -- Theorem 20.46 applies once the direct `ri` dual lower bound and conjugate properness are in
    -- place.
    exact
      pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
        (F := Fsum) hdualLower hFsum_conv hFsum_star_proper hFsum_ge
  have hsum_eq :
      A + B = pairingEqualityOperator ((Fsum∗)ᵀ) := by
    -- Repackage the direct `ri` contact-set characterization through the canonical pairing-contact
    -- operator spelling.
    funext x
    ext u
    rw [mem_pairingEqualityOperator_iff]
    exact hcontact x u
  -- Replace the contact operator by the actual sum operator.
  simpa [hsum_eq] using hmax_contact

/-- Theorem 25.2 (`sri` companion): if `A` and `B` are maximally monotone and
`0 ∈ sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))`, then `A + B` is
maximally monotone. -/
theorem Maximal.add_of_zero_mem_sri_fst_image_dom_fitzpatrick_sub
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsri : (0 : H) ∈
      sri (Prod.fst '' (ERealFunction.dom (F[A]) - ERealFunction.dom (F[B])))) :
    Maximal IsMonotone (A + B) := by
  let Fsum : H × H → EReal := fitzpatrickFiberwiseInfimalConvolution (A := A) (B := B)
  obtain ⟨hdualLower, hFsum_conv, hFsum_star_proper⟩ :=
    fitzpatrickFiberwiseInfimalConvolution_dualOwnerData_of_zero_mem_sri hA hB hsri
  have hFsum_ge : ∀ x u : H, pairing (x, u) ≤ Fsum (x, u) := by
    -- This is the primal inequality `F ≥ ⟪·, ·⟫` from the source proof.
    intro x u
    exact pairing_le_fitzpatrickFiberwiseInfimalConvolution hA hB x u
  have hmax_contact :
      Maximal IsMonotone (pairingEqualityOperator ((Fsum∗)ᵀ)) := by
    -- The Chapter 20 maximality criterion now applies directly to the canonical owner `Fsum`.
    exact
      pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
        (F := Fsum) hdualLower hFsum_conv hFsum_star_proper hFsum_ge
  have hsum_eq :
      A + B = pairingEqualityOperator ((Fsum∗)ᵀ) := by
    -- Identify the Chapter 20 contact operator with `A + B` through the exact contact-set
    -- characterization proved just above.
    funext x
    ext u
    rw [mem_pairingEqualityOperator_iff]
    constructor
    · intro hu
      -- Forget the pointwise membership spelling once, then apply the graph/contact theorem.
      exact
        (mem_graph_add_iff_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_inner_of_zero_mem_sri
          hA hB hsri x u).1 (by simpa [SetValuedOperator.mem_graph] using hu)
    · intro hcontact
      -- Repackage the contact equality back as graph membership and then as pointwise membership.
      exact
        (by
          have hgraph :
              (x, u) ∈ (A + B).graph :=
            (mem_graph_add_iff_conjugateTranspose_fitzpatrickFiberwiseInfimalConvolution_eq_inner_of_zero_mem_sri
              hA hB hsri x u).2 hcontact
          simpa [SetValuedOperator.mem_graph] using hgraph)
  -- Replace the contact operator by the actual sum operator.
  simpa [hsum_eq] using hmax_contact

end

end SetValuedOperator
