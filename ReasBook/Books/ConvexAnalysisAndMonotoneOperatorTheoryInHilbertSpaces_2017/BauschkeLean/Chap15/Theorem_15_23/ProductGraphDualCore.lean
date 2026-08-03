import Mathlib
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap15.FenchelSameSpaceAttainment
import BauschkeLean.Chap15.Definition_15_10

open Set
open scoped Pointwise

noncomputable section

universe u v

namespace ERealFunction

namespace Theorem_15_23

section FenchelRockafellarDuality

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

local instance prod_seminormedAddCommGroup_l2_graph : SeminormedAddCommGroup (X × Y) :=
  prod_seminormedAddCommGroup_l2 (H := X) (K := Y)

local instance prod_normedAddCommGroup_l2_graph : NormedAddCommGroup (X × Y) :=
  prod_normedAddCommGroup_l2 (H := X) (K := Y)

local instance prod_normedSpace_l2_graph : NormedSpace ℝ (X × Y) :=
  prod_normedSpace_l2 (H := X) (K := Y)

local instance prod_completeSpace_l2_graph : CompleteSpace (X × Y) :=
  prod_completeSpace_l2 (H := X) (K := Y)

local instance prod_innerProductSpace_l2_graph : InnerProductSpace ℝ (X × Y) :=
  prod_innerProductSpace_l2 (H := X) (K := Y)

/-- Helper for Theorem 15 23: the pullback of a `Γ₀` function along the first product projection
again belongs to `Γ₀` on the product space. -/
lemma fst_projection_mem_gammaZero
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X)) :
    (fun p : X × Y ↦ F p.1) ∈ Γ₀(X × Y) := by
  rw [mem_gammaZero_iff] at hF ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous first projection.
    simpa using hF.1.comp continuous_fst
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- A domain witness for `F` lifts to the product space by adjoining a zero second
      -- coordinate.
      obtain ⟨x, hx⟩ := hF.2.nonempty
      refine ⟨(x, 0), ?_⟩
      simpa [mem_effectiveDomain_iff] using hx
    · -- Convexity is inherited pointwise on the first coordinate.
      intro p hp q hq a ha0 ha1
      have hp' : p.1 ∈ effectiveDomain F := by
        simpa [mem_effectiveDomain_iff] using hp
      have hq' : q.1 ∈ effectiveDomain F := by
        simpa [mem_effectiveDomain_iff] using hq
      simpa using hF.2.ineq hp' hq' ha0 ha1

/-- Helper for Theorem 15 23: the pullback of a `Γ₀` function along the second product projection
again belongs to `Γ₀` on the product space. -/
lemma snd_projection_mem_gammaZero
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y)) :
    (fun p : X × Y ↦ G p.2) ∈ Γ₀(X × Y) := by
  rw [mem_gammaZero_iff] at hG ⊢
  constructor
  · -- Lower semicontinuity is preserved by the continuous second projection.
    simpa using hG.1.comp continuous_snd
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- A domain witness for `G` lifts to the product space by adjoining a zero first
      -- coordinate.
      obtain ⟨y, hy⟩ := hG.2.nonempty
      refine ⟨(0, y), ?_⟩
      simpa [mem_effectiveDomain_iff] using hy
    · -- Convexity is inherited pointwise on the second coordinate.
      intro p hp q hq a ha0 ha1
      have hp' : p.2 ∈ effectiveDomain G := by
        simpa [mem_effectiveDomain_iff] using hp
      have hq' : q.2 ∈ effectiveDomain G := by
        simpa [mem_effectiveDomain_iff] using hq
      simpa using hG.2.ineq hp' hq' ha0 ha1

/-- Helper for Theorem 15 23: the separable product objective `(x, y) ↦ F x + G y` belongs to
`Γ₀(X × Y)`. -/
lemma separable_sum_mem_gammaZero
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y)) :
    ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2) ∈ Γ₀(X × Y) := by
  have hfst : (fun p : X × Y ↦ F p.1) ∈ Γ₀(X × Y) :=
    fst_projection_mem_gammaZero (F := F) hF
  have hsnd : (fun p : X × Y ↦ G p.2) ∈ Γ₀(X × Y) :=
    snd_projection_mem_gammaZero (G := G) hG
  obtain ⟨x, hx⟩ := hF.2.nonempty
  obtain ⟨y, hy⟩ := hG.2.nonempty
  -- The lifted effective domains intersect at a product of ambient domain witnesses.
  refine pointwiseAdd_mem_gammaZero (fun p : X × Y ↦ F p.1) (fun p ↦ G p.2) hfst hsnd ?_
  refine ⟨(x, y), ?_, ?_⟩
  · simpa [mem_effectiveDomain_iff] using hx
  · simpa [mem_effectiveDomain_iff] using hy

/-- Helper for Theorem 15 23: the graph indicator of a continuous linear map belongs to `Γ₀` on
the product space. -/
lemma graphIndicator_mem_gammaZero
    (M : X →L[ℝ] Y) :
    (ι[(M.toLinearMap.graph : Set (X × Y))]) ∈ Γ₀(X × Y) := by
  -- The graph is nonempty, closed, and convex, so the generic indicator theorem applies.
  refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ ?_ ?_
  · refine ⟨(0, 0), ?_⟩
    simp [LinearMap.mem_graph_iff]
  · simpa [eq_comm, LinearMap.mem_graph_iff] using
      isClosed_eq continuous_snd (M.continuous.comp continuous_fst)
  · simpa using M.toLinearMap.graph.convex

/-- Helper for Theorem 15 23: for a nonempty convex set, algebraic-core membership at the origin
implies strong-relative-interior membership at the origin. -/
lemma zero_mem_sri_of_zero_mem_core_of_nonempty_convex
    {S : Set Y}
    (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (hcore : (0 : Y) ∈ Set.core S) :
    (0 : Y) ∈ sri S := by
  rcases Set.mem_core_iff.mp hcore with ⟨hzeroS, hcone_univ⟩
  have hsub_zero : S - ({0} : Set Y) = S := by
    -- Subtracting the origin does not change the regularity set at the source origin.
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, hyz⟩
      rcases Set.mem_singleton_iff.mp hz with rfl
      have hyx : y = x := by simpa using hyz
      simpa [hyx] using hy
    · intro hx
      exact Set.mem_sub.mpr ⟨x, hx, 0, by simp, by simp⟩
  have hconeS : cone S = (univ : Set Y) := by
    simpa [hsub_zero] using hcone_univ
  have hclosure_span :
      ((Submodule.span ℝ S).topologicalClosure : Set Y) = univ := by
    apply Set.Subset.antisymm
    · simp
    · intro y hy
      have hyCone : y ∈ cone S := by simpa [hconeS]
      exact cone_subset_topologicalClosure_span S hyCone
  -- Rewrite the core criterion into the cone-equals-closed-span criterion from Proposition 6.21.
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hS_nonempty hS_convex).2 ?_
  calc
    cone S = (univ : Set Y) := hconeS
    _ = ((Submodule.span ℝ S).topologicalClosure : Set Y) := hclosure_span.symm

/-- Helper for Theorem 15 23: the textbook `sri` hypothesis on
`effectiveDomain G - M '' effectiveDomain F` is equivalent to the product-space graph hypothesis
from Proposition 6.21. -/
lemma zero_mem_sri_prod_sub_graph_of_zero_mem_sri_sub_image_effectiveDomain
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hsri : (0 : Y) ∈ sri (effectiveDomain G - M '' effectiveDomain F)) :
    (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - (M.toLinearMap.graph : Set (X × Y))) := by
  obtain ⟨x, hx⟩ := hF.2.nonempty
  obtain ⟨y, hy⟩ := hG.2.nonempty
  -- Proposition 6.21 is the exact source bridge from the image-difference hypothesis to the
  -- product-space graph model.
  exact
    (zero_mem_strongRelativeInterior_sub_image_iff_zero_mem_strongRelativeInterior_prod_sub_graph
      (C := effectiveDomain F) (D := effectiveDomain G)
      ⟨x, hx⟩ ⟨y, hy⟩
      hF.2.convex_effectiveDomain
      hG.2.convex_effectiveDomain
      M).1 hsri

/-- Helper for Theorem 15 23: algebraic-core regularity on
`effectiveDomain G - M '' effectiveDomain F` upgrades to the corresponding product-space
strong-relative-interior hypothesis. -/
lemma productGraphZeroMemSRI_of_zeroMemCoreSubImage
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - (M.toLinearMap.graph : Set (X × Y))) := by
  let S : Set Y := effectiveDomain G - M '' effectiveDomain F
  have hS_nonempty : S.Nonempty := by
    -- Core membership at the origin gives an explicit point of the source difference set.
    rcases Set.mem_core_iff.mp hcore with ⟨hzero, _⟩
    exact ⟨0, hzero⟩
  have hS_convex : Convex ℝ S := by
    -- The source difference set is convex because both effective domains are convex.
    dsimp [S]
    exact
      hG.2.convex_effectiveDomain.sub
        (hF.2.convex_effectiveDomain.linear_image M.toLinearMap)
  have hsri : (0 : Y) ∈ sri S := by
    -- Convert the source `core` hypothesis to the Chapter 6 strong-relative-interior owner.
    exact zero_mem_sri_of_zero_mem_core_of_nonempty_convex hS_nonempty hS_convex hcore
  -- Transport the source regularity statement to the product graph model.
  simpa [S] using
    zero_mem_sri_prod_sub_graph_of_zero_mem_sri_sub_image_effectiveDomain
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hsri

/-- Helper for Theorem 15 23: the product-space pair already satisfies the `Γ₀/Γ₀/sri`
hypotheses of the canonical same-space Fenchel theorem, up to the final effective-domain
rewriting. -/
lemma product_pair_regularized_data
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2) ∈ Γ₀(X × Y) ∧
      (ι[(M.toLinearMap.graph : Set (X × Y))]) ∈ Γ₀(X × Y) ∧
      (0 : X × Y) ∈
        sri (effectiveDomain F ×ˢ effectiveDomain G - (M.toLinearMap.graph : Set (X × Y))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The separable product objective is proper convex on the product space.
    exact separable_sum_mem_gammaZero (F := F) hF (G := G) hG
  · -- The graph indicator is proper convex because the graph is nonempty, closed, and convex.
    exact graphIndicator_mem_gammaZero (M := M)
  · -- The source regularity hypothesis upgrades to the product-space graph hypothesis.
    exact productGraphZeroMemSRI_of_zeroMemCoreSubImage
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore

/-- Helper for Theorem 15 23: the effective domain of the separable product objective is the
product of the coordinatewise effective domains. -/
lemma effectiveDomain_separable_sum_eq_prod
    (F : X → Set.Ioi (⊥ : EReal))
    (G : Y → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)) =
      effectiveDomain F ×ˢ effectiveDomain G := by
  ext p
  rw [mem_effectiveDomain_pointwiseAdd_iff]
  constructor
  · intro hp
    constructor
    · simpa [mem_effectiveDomain_iff] using hp.1
    · simpa [mem_effectiveDomain_iff] using hp.2
  · rintro ⟨hpF, hpG⟩
    constructor
    · simpa [mem_effectiveDomain_iff] using hpF
    · simpa [mem_effectiveDomain_iff] using hpG

/-- Helper for Theorem 15 23: the effective domain of the graph indicator is exactly the graph. -/
lemma effectiveDomain_graphIndicator_eq_graph
    (M : X →L[ℝ] Y) :
    effectiveDomain (ι[(M.toLinearMap.graph : Set (X × Y))]) =
      (M.toLinearMap.graph : Set (X × Y)) := by
  -- The generic indicator-domain identity already gives the exact graph set.
  simpa using effectiveDomain_indicator (M.toLinearMap.graph : Set (X × Y))

/-- Helper for Theorem 15 23: after normalizing the product pair to `P := (x, y) ↦ F x + G y`
and `I := ι[graph M]`, the product-space regularity hypothesis is already in the exact
same-space owner form `0 ∈ sri (effectiveDomain P - effectiveDomain I)`. -/
lemma zero_mem_sri_sub_effectiveDomain_product_pair
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    (0 : X × Y) ∈
      sri
        (effectiveDomain (((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)) -
          effectiveDomain (ι[(M.toLinearMap.graph : Set (X × Y))])) := by
  -- First transport the source core hypothesis to the product graph model.
  have hsri_prod :
      (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - (M.toLinearMap.graph : Set (X × Y))) := by
    exact productGraphZeroMemSRI_of_zeroMemCoreSubImage
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
  -- Then rewrite both effective domains to the normalized same-space owner pair `(P, I)`.
  simpa [effectiveDomain_separable_sum_eq_prod, effectiveDomain_graphIndicator_eq_graph] using hsri_prod

/-- Helper for Theorem 15 23: away from the orthogonal complement of `graph(M)`, the graph
indicator conjugate is `⊤`, so the product-graph Fenchel dual objective is infeasible. -/
lemma fenchelDualObjective_separable_graph_eq_top_off_orthogonal
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (hu : u ∉ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y)))) :
    fenchelDualObjective
        ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
        (ι[(M.toLinearMap.graph : Set (X × Y))])
        u = ⊤ := by
  let P : X × Y → Set.Ioi (⊥ : EReal) := (fun p : X × Y ↦ F p.1) + fun p ↦ G p.2
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[(M.toLinearMap.graph : Set (X × Y))]
  have hP_gamma : P ∈ Γ₀(X × Y) := by
    -- The separable product objective is proper, so its reflected conjugate is never `⊥`.
    simpa [P] using separable_sum_mem_gammaZero (F := F) hF (G := G) hG
  have hP_reverse_ne_bot : P.asEReal∗ᵛ u ≠ ⊥ := by
    -- Properness rules out the exceptional `⊥` branch for the reflected conjugate term.
    simpa [P, ERealFunction.reverse_apply] using
      conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hP_gamma) (-u)
  have hindicator_top :
      (I.asEReal∗) u = ⊤ := by
    -- Off `graph(M)ᗮ`, the graph-indicator conjugate is exactly `⊤`.
    simpa [I, ERealFunction.indicator, hu] using
      congrFun (conjugate_indicator_submodule_eq_indicator_orthogonal
        (V := M.toLinearMap.graph)) u
  -- The `⊤` indicator-conjugate term forces the whole dual objective to be `⊤`.
  rw [fenchelDualObjective_apply, hindicator_top]
  exact EReal.add_top_of_ne_bot hP_reverse_ne_bot

/-- Helper for Theorem 15 23: any product-graph dual point with non-`⊤` value already lies in
the orthogonal complement of `graph(M)`. -/
lemma mem_orthogonal_graph_of_product_graph_dual_ne_top
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (huTop :
      fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))])
          u ≠ ⊤) :
    u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
      Submodule ℝ (X × Y)) : Set (X × Y))) := by
  -- Off the orthogonal slice the graph-indicator conjugate is definitionally `⊤`, so any
  -- non-`⊤` point must already lie in `graph(M)ᗮ`.
  by_contra hu_not
  exact huTop <|
    fenchelDualObjective_separable_graph_eq_top_off_orthogonal
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hu_not

/-- Helper for Theorem 15 23: once an attained product-graph dual minimizer is fixed, either the
dual objective is everywhere `⊤`, or that minimizer already lies in `graph(M)ᗮ`. -/
lemma product_graph_dual_all_top_or_mem_orthogonal_of_mem_argmin
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    {u : X × Y}
    (huArg :
      u ∈ Argmin
        (fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))])))
    (huValue :
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))]) =
        -(fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))])
            u)) :
    ((∀ z : X × Y,
        fenchelDualObjective
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))])
            z = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))]) = ⊥) ∨
      u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y))) := by
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[(M.toLinearMap.graph : Set (X × Y))]
  let D : X × Y → EReal := fenchelDualObjective ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2) I
  by_cases huOrth :
      u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
        Submodule ℝ (X × Y)) : Set (X × Y)))
  · -- On the orthogonal slice, the attained minimizer already has the required graph-side shape.
    exact Or.inr huOrth
  · have huTop :
        D u = ⊤ := by
      simpa [D, I] using
        fenchelDualObjective_separable_graph_eq_top_off_orthogonal
          (F := F) (hF := hF) (G := G) (hG := hG) (M := M) huOrth
    have hu_sInf :
        D u = sInf (Set.range D) := by
      simpa [D, I] using (mem_argmin_iff_eq_sInf.mp huArg)
    have hsInf_top :
        sInf (Set.range D) = ⊤ := by
      -- The minimizing value is `⊤`, so the infimum of the whole range is already `⊤`.
      calc
        sInf (Set.range D) = D u := hu_sInf.symm
        _ = ⊤ := huTop
    have hall :
        ∀ z : X × Y, D z = ⊤ := by
      intro z
      have hz_ge :
          sInf (Set.range D) ≤ D z :=
        (isGLB_sInf (Set.range D)).1 (Set.mem_range_self z)
      -- Since `⊤` is the infimum, every value of the dual objective must equal `⊤`.
      exact le_antisymm le_top <| by simpa [hsInf_top] using hz_ge
    have hprimal_bot :
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))]) = ⊥ := by
      -- Rewriting the attained equality at a `⊤` minimizer gives the degenerate primal value.
      calc
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))]) =
          -(D u) := by simpa [D, I] using huValue
        _ = ⊥ := by simp [huTop]
    exact Or.inl ⟨by simpa [D, I] using hall, hprimal_bot⟩

/-- Helper for Theorem 15 23: once the same-space Fenchel theorem supplies an attained
product-graph dual minimizer, the remaining work is only the graph-side orthogonal localization. -/
lemma orthogonal_or_all_top_of_product_graph_dual_attainment
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hattain :
      ∃ u ∈ Argmin
        (fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))])),
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[(M.toLinearMap.graph : Set (X × Y))])
              u)) :
    ((∀ u : X × Y,
        fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))])
          u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))]) = ⊥) ∨
      ∃ u : X × Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[(M.toLinearMap.graph : Set (X × Y))])
              u) ∧
        u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) := by
  rcases hattain with ⟨u, huArg, huValue⟩
  -- The graph adapter either detects the degenerate `⊤/⊥` branch or localizes the minimizer.
  rcases
      product_graph_dual_all_top_or_mem_orthogonal_of_mem_argmin
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M)
        huArg huValue
    with htop | huOrth
  · exact Or.inl htop
  · exact Or.inr ⟨u, huValue, huOrth⟩

/-- Helper for Theorem 15 23: this theorem-local owner packages the remaining product-graph
zero-slice exactness step. It is kept outside the main theorem file so the source proof in
`Theorem_15_23.lean` can remain focused on the closed-span restriction and translation route. -/
theorem product_graph_dual_all_top_or_orthogonal_value_of_zero_mem_core_sub_image_effectiveDomain
    (F : X → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(X))
    (G : Y → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(Y))
    (M : X →L[ℝ] Y)
    (hcore : (0 : Y) ∈ Set.core (effectiveDomain G - M '' effectiveDomain F)) :
    ((∀ u : X × Y,
        fenchelDualObjective
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))])
          u = ⊤) ∧
      primalOptimalValue
          ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
          (ι[(M.toLinearMap.graph : Set (X × Y))]) = ⊥) ∨
      ∃ u : X × Y,
        primalOptimalValue
            ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
            (ι[(M.toLinearMap.graph : Set (X × Y))]) =
          -(fenchelDualObjective
              ((fun p : X × Y ↦ F p.1) + fun p ↦ G p.2)
              (ι[(M.toLinearMap.graph : Set (X × Y))])
              u) ∧
        u ∈ ((((M.toLinearMap.graph : Submodule ℝ (X × Y))ᗮ :
          Submodule ℝ (X × Y)) : Set (X × Y))) := by
  let P : X × Y → Set.Ioi (⊥ : EReal) := (fun p : X × Y ↦ F p.1) + fun p ↦ G p.2
  let I : X × Y → Set.Ioi (⊥ : EReal) := ι[(M.toLinearMap.graph : Set (X × Y))]
  have hP_gamma : P ∈ Γ₀(X × Y) := by
    -- First normalize the separable product objective into the canonical `Γ₀` owner.
    simpa [P] using separable_sum_mem_gammaZero (F := F) hF (G := G) hG
  have hI_gamma : I ∈ Γ₀(X × Y) := by
    -- The graph indicator is the canonical `Γ₀` constraint term on the product space.
    simpa [I] using graphIndicator_mem_gammaZero (M := M)
  have hsri_prod :
      (0 : X × Y) ∈ sri (effectiveDomain F ×ˢ effectiveDomain G - (M.toLinearMap.graph : Set (X × Y))) := by
    -- The source core hypothesis has now been transported to the product-space graph model.
    exact productGraphZeroMemSRI_of_zeroMemCoreSubImage
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
  have hsri_owner :
      (0 : X × Y) ∈ sri (effectiveDomain P - effectiveDomain I) := by
    -- Freeze the effective-domain normalization once so the remaining blocker is only upstream
    -- same-space Fenchel attainment for `(P, I)`.
    simpa [P, I] using
      zero_mem_sri_sub_effectiveDomain_product_pair
        (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hcore
  have hattain_owner :
      ∃ u ∈ Argmin (fenchelDualObjective P I),
        primalOptimalValue P I = -(fenchelDualObjective P I u) := by
    -- The product pair now matches the shared same-space Fenchel owner exactly.
    simpa [P, I] using
      exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain_shared
        P I hP_gamma hI_gamma hsri_owner
  -- The graph-side transport is now fully separated from the remaining same-space attainment input.
  simpa [P, I] using
    orthogonal_or_all_top_of_product_graph_dual_attainment
      (F := F) (hF := hF) (G := G) (hG := hG) (M := M) hattain_owner

end FenchelRockafellarDuality

end Theorem_15_23

end ERealFunction
