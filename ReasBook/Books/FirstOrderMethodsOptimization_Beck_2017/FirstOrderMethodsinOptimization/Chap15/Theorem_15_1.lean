import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Lemma_2_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Proposition_2_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Proposition_4_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Theorem_4_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Definition_15_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap15.Definition_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Pointwise

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]
variable {h₁ : X → EReal} {h₂ : Z → EReal}
variable {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 4 and Chapter 15 duality files. This item is `source-facing`: its mathematical content is
the strong-duality equality for the ADMM primal/dual value pair together with dual attainment.
The `core/canonical` owners are already upstream:
- `admm_problem_value`, `admm_dual_problem_value`, and `admm_dual_objective` in Chapter 15;
- `fenchel_duality_value_eq` and
  `exists_isGreatest_fenchel_dual_objective_of_finite_value` in Chapter 4.

Accordingly, this file keeps only the ADMM-specialized statements. The primitive data for those
specializations are the properness and convexity hypotheses actually consumed by the Chapter 4
owners, together with the source-facing relative-interior feasibility clause from Assumption
15.2(E). On the codomain side, the owner declarations already live over the weaker ambient layer
`[AddCommGroup Y] [Module ℝ Y]`, so this file does not retain extra normed or finite-dimensional
structure on `Y` as theorem-level input. The larger Chapter 15 bundle
`IsADMMConvexObjectivePair` remains upstream auxiliary API, but it is not the owner-level input
for these theorem statements. -/

recall admm_problem_value
recall admm_dual_problem_value
recall admm_dual_objective
recall fenchel_dual_objective
recall fenchel_dual_problem_value
recall fenchel_dual_problem_value_eq_sSup
recall fenchel_duality_value_eq
recall exists_isGreatest_fenchel_dual_objective_of_finite_value

variable (h₁_proper : IsProperExtendedRealFunction h₁)
variable (h₂_proper : IsProperExtendedRealFunction h₂)
variable (h₁_convex : is_convex_function h₁)
variable (h₂_convex : is_convex_function h₂)
variable (hqual :
  ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
    ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
      A xHat + B zHat = c)

/-- Helper for Theorem 15.1: negating an affine perturbation turns its infimum into the negative
Fenchel conjugate. -/
private theorem ereal_sInf_range_sub_pairing_eq_neg_conjugate
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) (η : Module.Dual ℝ E) :
    sInf (Set.range fun x : E ↦ f x - (η x : EReal)) = -conjugate_function f η := by
  -- Rewrite the affine-perturbation range as the negation of the conjugate-defining range.
  have hrange :
      Set.range (fun x : E ↦ f x - (η x : EReal)) =
        -Set.range (fun x : E ↦ (η x : EReal) - f x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hneg : -(f x - (η x : EReal)) = ((η x : EReal) - f x) := by
        have hraw : -(f x - (η x : EReal)) = -f x + (η x : EReal) := by
          exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hneg : -(f x - (η x : EReal)) = -r := by
        calc
          -(f x - (η x : EReal)) = ((η x : EReal) - f x) := by
            have hraw : -(f x - (η x : EReal)) = -f x + (η x : EReal) := by
              exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
            simpa [sub_eq_add_neg, add_comm] using hraw
          _ = -r := by simpa using hx
      have hr : -(-(f x - (η x : EReal))) = -(-r) := congrArg Neg.neg hneg
      simpa using hr
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange]
  have hsInf_neg : sInf (-Set.range (fun x : E ↦ (η x : EReal) - f x)) =
      -sSup (Set.range fun x : E ↦ (η x : EReal) - f x) := by
    refine le_antisymm ?_ ?_
    · have hsSup :
        sSup (Set.range fun x : E ↦ (η x : EReal) - f x) ≤
          -sInf (-Set.range fun x : E ↦ (η x : EReal) - f x) := by
        refine sSup_le ?_
        intro x hx
        have hsInf :
            sInf (-Set.range fun x : E ↦ (η x : EReal) - f x) ≤ -x := by
          exact sInf_le
            (by
              simpa [Set.mem_neg] using hx :
                -x ∈ -Set.range fun x : E ↦ (η x : EReal) - f x)
        exact EReal.le_neg.mp hsInf
      exact EReal.le_neg.mpr hsSup
    · refine le_sInf ?_
      intro z hz
      exact EReal.neg_le.mpr
        (le_sSup
          (by
            simpa [Set.mem_neg] using hz :
              -z ∈ Set.range fun x : E ↦ (η x : EReal) - f x))
  rw [hsInf_neg, conjugate_function_apply]

/-- Helper for Theorem 15.1: every point of an affine subspace lies in the intrinsic interior of
its carrier set. -/
private theorem mem_intrinsicInterior_affineSubspace
    {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (s : AffineSubspace ℝ P) {x : P} (hx : x ∈ (s : Set P)) :
    x ∈ intrinsicInterior ℝ (s : Set P) := by
  -- Unfold the intrinsic interior inside the affine span, which is the affine subspace itself.
  rw [intrinsicInterior]
  refine ⟨⟨x, ?_⟩, ?_, rfl⟩
  · simpa [AffineSubspace.affineSpan_coe] using hx
  · have hpre :
        ((↑) : affineSpan ℝ (s : Set P) → P) ⁻¹' (s : Set P) = Set.univ := by
      ext y
      change (↑y ∈ (s : Set P)) ↔ True
      constructor
      · intro _
        trivial
      · intro _
        simpa [AffineSubspace.affineSpan_coe] using y.property
    rw [hpre]
    simp

/-- Helper for Theorem 15.1: the relative interiors of the block domains combine to the product
relative interior. -/
private theorem mem_intrinsicInterior_prod
    {S : Set X} {T : Set Z} {x : X} {z : Z}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Route correction: use the closed-ball characterization from Definition 3.7, then project the
  -- ambient affine-span condition to each coordinate before applying the original witnesses.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ X Z).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ X Z).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ X Z).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ X Z).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ X Z).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ X Z).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 15.1: the ADMM objective is finite exactly on the product of the two block
effective domains. -/
private theorem effective_domain_admm_objective
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    effective_domain (H[h₁, h₂]) = effective_domain h₁ ×ˢ effective_domain h₂ := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Turn finiteness of the sum into coordinatewise finiteness using the properness `ne_bot` facts.
  simp [effective_domain, lt_top_iff_ne_top,
    EReal.add_ne_top_iff_ne_top₂, h₁_proper.ne_bot x, h₂_proper.ne_bot z]

/-- Helper for Theorem 15.1: the ADMM objective never takes the value `-∞`. -/
private theorem admm_objective_ne_bot
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (xz : X × Z) :
    H[h₁, h₂] xz ≠ ⊥ := by
  rcases xz with ⟨x, z⟩
  -- Each block objective avoids `⊥`, so their sum avoids `⊥` as well.
  simpa [admm_objective_apply, EReal.add_ne_bot_iff] using
    And.intro (h₁_proper.ne_bot x) (h₂_proper.ne_bot z)

/-- Helper for Theorem 15.1: the ADMM product objective is proper. -/
private theorem admm_objective_proper
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    IsProperExtendedRealFunction (H[h₁, h₂]) := by
  rcases h₁_proper.effective_domain_nonempty with ⟨x₀, hx₀⟩
  rcases h₂_proper.effective_domain_nonempty with ⟨z₀, hz₀⟩
  refine
    { ne_bot := admm_objective_ne_bot (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper
      effective_domain_nonempty := ?_ }
  -- Combine the coordinatewise effective-domain witnesses into a product witness.
  refine ⟨(x₀, z₀), ?_⟩
  simpa [effective_domain_admm_objective (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper] using
    And.intro hx₀ hz₀

/-- Helper for Theorem 15.1: the pointwise sum of two convex extended-real-valued functions is
convex. -/
private theorem is_convex_function_add
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f g : E → EReal) (hf : is_convex_function f) (hg : is_convex_function g) :
    is_convex_function (f + g) := by
  let F : Fin 2 → E → EReal := fun i ↦ if i = 0 then f else g
  let α : Fin 2 → NNReal := fun _ ↦ 1
  have hconv :
      is_convex_function (fun x ↦ ∑ i : Fin 2, (((α i : ℝ) : EReal) * F i x)) := by
    refine is_convex_function_finset_nonneg_weighted_sum ?_ α
    intro i
    fin_cases i
    · simpa [F] using hf
    · simpa [F] using hg
  -- Evaluate the two-term weighted sum explicitly.
  simpa [F, α, Fin.sum_univ_two] using hconv

/-- Helper for Theorem 15.1: the ADMM product objective is convex on `X × Z`. -/
private theorem admm_objective_convex
    (h₁_convex : is_convex_function h₁)
    (h₂_convex : is_convex_function h₂) :
    is_convex_function (H[h₁, h₂]) := by
  have hfst : is_convex_function (fun xz : X × Z ↦ h₁ xz.1) := by
    -- Pull back `h₁` along the first coordinate projection.
    simpa using
      is_convex_function_precompose_affineMap (f := h₁) h₁_convex
        (LinearMap.fst ℝ X Z).toAffineMap
  have hsnd : is_convex_function (fun xz : X × Z ↦ h₂ xz.2) := by
    -- Pull back `h₂` along the second coordinate projection.
    simpa using
      is_convex_function_precompose_affineMap (f := h₂) h₂_convex
        (LinearMap.snd ℝ X Z).toAffineMap
  -- The ADMM objective is the sum of the two pulled-back block objectives.
  simpa [admm_objective] using
    is_convex_function_add (fun xz : X × Z ↦ h₁ xz.1) (fun xz : X × Z ↦ h₂ xz.2) hfst hsnd

/-- Helper for Theorem 15.1: a linear fiber is a translate of the kernel through any feasible
base point. -/
private theorem linear_fiber_eq_singleton_add_ker
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x0 : E) (c : F) (hx0 : L x0 = c) :
    {x : E | L x = c} = ({x0} : Set E) + (LinearMap.ker L : Set E) := by
  ext x
  constructor
  · intro hx
    -- Split a feasible point into the chosen base point plus a kernel displacement.
    refine ⟨x0, by simp, x - x0, ?_, by abel⟩
    change L (x - x0) = 0
    rw [LinearMap.map_sub, hx, hx0, sub_self]
  · rintro ⟨u, hu, v, hv, hsum⟩
    have hu0 : u = x0 := Set.mem_singleton_iff.1 hu
    -- Conversely, adding a kernel displacement preserves the linear constraint value.
    rw [← hsum, hu0]
    change L (x0 + v) = c
    rw [LinearMap.map_add, LinearMap.mem_ker.1 hv, hx0, add_zero]

/-- Helper for Theorem 15.1: the polar cone of a submodule carrier is its dual annihilator. -/
private theorem polar_cone_submodule_eq_dualAnnihilator
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (W : Submodule ℝ E) :
    polar_cone (W : Set E) = W.dualAnnihilator := by
  ext φ
  rw [mem_polar_cone]
  constructor
  · intro h
    change φ ∈ W.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    -- Test the polar inequality on `w` and `-w` to upgrade nonpositivity to vanishing.
    have hle : φ w ≤ 0 := h w hw
    have hneg : φ (-w) ≤ 0 := h (-w) (by simpa using W.neg_mem hw)
    have hge : 0 ≤ φ w := by
      have hneg' : -φ w ≤ 0 := by simpa using hneg
      exact neg_nonpos.mp hneg'
    exact le_antisymm hle hge
  · intro h
    change φ ∈ W.dualAnnihilator at h
    rw [Submodule.mem_dualAnnihilator] at h
    intro w hw
    -- Vanishing on the submodule is the stronger condition required by the polar cone.
    simpa [h w hw]

/-- Helper for Theorem 15.1: the set-theoretic range of `dualMap` matches its linear-map range. -/
private theorem set_range_dualMap_eq_linearMap_range
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) :
    Set.range L.dualMap = (LinearMap.range L.dualMap : Set (Module.Dual ℝ E)) := by
  ext ξ
  rw [Set.mem_range]
  exact LinearMap.mem_range

/-- Helper for Theorem 15.1: the support function of a singleton is evaluation at its unique
point. -/
private theorem support_function_singleton
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x0 : E) (ξ : Module.Dual ℝ E) :
    support_function ({x0} : Set E) ξ = (ξ x0 : EReal) := by
  -- The pairing image of a singleton has greatest element given by the unique point.
  refine support_function_eq_of_isGreatest_image ({x0} : Set E) ξ ?_
  refine ⟨?_, ?_⟩
  · exact ⟨x0, by simp, rfl⟩
  · intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    rcases Set.mem_singleton_iff.1 hx with rfl
    exact le_rfl

/-- Helper for Theorem 15.1: the support function of an affine linear fiber is evaluation at the
base point plus the indicator of the transpose range. -/
private theorem support_function_linear_fiber_eq_eval_add_indicator_dual_range
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x0 : E) (c : F) (hx0 : L x0 = c) (ξ : Module.Dual ℝ E) :
    support_function ({x : E | L x = c}) ξ =
      (ξ x0 : EReal) + extendedIndicator (Set.range L.dualMap) ξ := by
  have hcone : IsCone ((LinearMap.ker L : Submodule ℝ E) : Set E) := by
    intro a x hx
    -- The kernel is closed under nonnegative scaling because it is a submodule.
    change (a : ℝ) • x ∈ LinearMap.ker L
    rw [LinearMap.mem_ker, LinearMap.map_smul, LinearMap.mem_ker.1 hx]
    simp
  have hzero : (0 : E) ∈ ((LinearMap.ker L : Submodule ℝ E) : Set E) := by
    simp
  have hker :
      support_function ((LinearMap.ker L : Submodule ℝ E) : Set E) =
        extendedIndicator (Set.range L.dualMap) := by
    ext ψ
    -- Rewrite the homogeneous support function through the polar cone and then through the
    -- dual-annihilator/range identification.
    calc
      support_function ((LinearMap.ker L : Submodule ℝ E) : Set E) ψ
          = extendedIndicator (polar_cone ((LinearMap.ker L : Set E))) ψ := by
              simpa using congrArg (fun f : Module.Dual ℝ E → EReal ↦ f ψ)
                (support_function_eq_indicatorFunction_polarCone
                  ((LinearMap.ker L : Set E)) hcone hzero)
      _ = extendedIndicator ((LinearMap.ker L).dualAnnihilator : Set (Module.Dual ℝ E)) ψ := by
            rw [polar_cone_submodule_eq_dualAnnihilator]
      _ = extendedIndicator (LinearMap.range L.dualMap : Set (Module.Dual ℝ E)) ψ := by
            rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      _ = extendedIndicator (Set.range L.dualMap) ψ := by
            rw [set_range_dualMap_eq_linearMap_range]
  -- Rewrite the affine fiber as a translate of the kernel, then split the support function across
  -- the singleton and homogeneous pieces.
  calc
    support_function ({x : E | L x = c}) ξ
        = support_function (({x0} : Set E) + (LinearMap.ker L : Set E)) ξ := by
            rw [linear_fiber_eq_singleton_add_ker L x0 c hx0]
    _ = support_function ({x0} : Set E) ξ +
          support_function ((LinearMap.ker L : Submodule ℝ E) : Set E) ξ := by
            rw [support_function_minkowski_sum]
    _ = (ξ x0 : EReal) + support_function ((LinearMap.ker L : Submodule ℝ E) : Set E) ξ := by
            rw [support_function_singleton]
    _ = (ξ x0 : EReal) + extendedIndicator (Set.range L.dualMap) ξ := by
            rw [hker]

/-- Helper for Theorem 15.1: once a feasible base point is fixed, the ADMM constraint set is the
affine subspace obtained by translating `ker (A.coprod B)` through that point. -/
private theorem admm_feasible_set_eq_affineSubspace_of_mem
    {xz0 : X × Z} (hxz0 : xz0 ∈ admm_feasible_set A B c) :
    admm_feasible_set A B c =
      ((AffineSubspace.mk' xz0 (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z)) := by
  ext xz
  constructor
  · intro hxz
    -- Compare any other feasible point to the base point by taking their difference in the kernel.
    change xz - xz0 ∈ (A.coprod B).ker
    rw [LinearMap.mem_ker]
    rw [LinearMap.map_sub]
    have hxz_eq : (A.coprod B) xz = c := by
      simpa using hxz
    have hxz0_eq : (A.coprod B) xz0 = c := by
      simpa using hxz0
    calc
      (A.coprod B) xz - (A.coprod B) xz0 = c - c := by rw [hxz_eq, hxz0_eq]
      _ = 0 := sub_self c
  · intro hxz
    -- Conversely, a kernel displacement keeps the affine constraint value unchanged.
    change xz - xz0 ∈ (A.coprod B).ker at hxz
    rw [LinearMap.mem_ker] at hxz
    rw [LinearMap.map_sub] at hxz
    have hxz0_eq : (A.coprod B) xz0 = c := by
      simpa using hxz0
    have heq : (A.coprod B) xz = (A.coprod B) xz0 := sub_eq_zero.mp hxz
    simpa using heq.trans hxz0_eq

/-- Helper for Theorem 15.1: the ADMM feasible set is convex. -/
private theorem admm_feasible_set_convex :
    Convex ℝ (admm_feasible_set A B c) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  have hx_eq : A x₁ + B z₁ = c := by
    simpa using hx
  have hy_eq : A x₂ + B z₂ = c := by
    simpa using hy
  -- The affine constraint is preserved by convex combinations because `a + b = 1`.
  change A (a • x₁ + b • x₂) + B (a • z₁ + b • z₂) = c
  calc
    A (a • x₁ + b • x₂) + B (a • z₁ + b • z₂)
        = a • (A x₁ + B z₁) + b • (A x₂ + B z₂) := by
            simp [map_add, map_smul, smul_add, add_assoc, add_left_comm]
    _ = a • c + b • c := by rw [hx_eq, hy_eq]
    _ = (a + b) • c := by rw [← add_smul]
    _ = c := by simpa [hab] using (one_smul ℝ c)

/-- Helper for Theorem 15.1: every feasible ADMM point lies in the intrinsic interior of the
affine feasible set. -/
private theorem mem_intrinsicInterior_admm_feasible_set
    {xz : X × Z} (hxz : xz ∈ admm_feasible_set A B c) :
    xz ∈ intrinsicInterior ℝ (admm_feasible_set A B c) := by
  have hmem :
      xz ∈
        ((AffineSubspace.mk' xz (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z)) := by
    -- The base point of the affine translate belongs to it via the zero kernel displacement.
    change xz - xz ∈ (A.coprod B).ker
    rw [LinearMap.mem_ker]
    simp
  have hri :
      xz ∈ intrinsicInterior ℝ
        (((AffineSubspace.mk' xz (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z))) := by
    -- Every point of an affine subspace lies in its intrinsic interior.
    exact mem_intrinsicInterior_affineSubspace
      (AffineSubspace.mk' xz (A.coprod B).ker) hmem
  -- Rewrite the feasible set as that affine translate through the chosen feasible point.
  simpa [admm_feasible_set_eq_affineSubspace_of_mem (A := A) (B := B) (c := c) hxz] using hri

/-- Helper for Theorem 15.1: the ADMM primal value is the Fenchel primal infimum for the product
objective plus the feasible-set indicator. -/
private theorem admm_problem_value_eq_fenchel_primal_infimum
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    H_opt[h₁, h₂; A, B, c] =
      sInf (Set.range (composite_model_objective (H[h₁, h₂])
        (extendedIndicator (admm_feasible_set A B c)))) := by
  -- Rewrite the constrained objective as `H + δ_C` using the global no-`⊥` property of `H`.
  have hrewrite :
      constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c) =
        composite_model_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) := by
    -- Route correction: supply the non-`⊥` side condition explicitly, then rewrite `f + δ_C`
    -- back to the canonical pointwise-sum owner `composite_model_objective`.
    simpa [composite_model_objective_eq_add] using
      (constrained_problem_objective_eq_add_extendedIndicator
        (f := H[h₁, h₂]) (C := admm_feasible_set A B c)
        (fun yz _ ↦ admm_objective_ne_bot (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper yz))
  have hrange :
      Set.range (constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c)) =
        Set.range (composite_model_objective (H[h₁, h₂])
          (extendedIndicator (admm_feasible_set A B c))) := by
    simpa using congrArg Set.range hrewrite
  rw [admm_problem_value_eq_sInf]
  rw [hrange]

/-- Helper for Theorem 15.1: the ADMM qualification matches the Chapter 4 Fenchel qualification
on the product space. -/
private theorem admm_fenchel_qualification
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    (intrinsicInterior ℝ (effective_domain (H[h₁, h₂])) ∩
      intrinsicInterior ℝ (admm_feasible_set A B c)).Nonempty := by
  rcases hqual with ⟨xHat, hxHat, zHat, hzHat, hfeas⟩
  refine ⟨(xHat, zHat), ?_, ?_⟩
  · -- The product relative-interior witness transfers through the product-domain identity.
    simpa [effective_domain_admm_objective (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper] using
      mem_intrinsicInterior_prod (X := X) (Z := Z) hxHat hzHat
  · -- The feasible witness lies in the intrinsic interior of the affine constraint fiber.
    exact mem_intrinsicInterior_admm_feasible_set (A := A) (B := B) (c := c)
      (xz := (xHat, zHat)) (by simpa using hfeas)

/-- Helper for Theorem 15.1: the support function of the ADMM feasible affine fiber is constant on
the transpose range. -/
private theorem support_function_admm_feasible_set_on_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (y : Module.Dual ℝ Y) :
    support_function (admm_feasible_set A B c) ((A.coprod B).dualMap y) = (y c : EReal) := by
  rcases hqual with ⟨xHat, hxHat, zHat, hzHat, hfeas⟩
  have hxz_feas : (xHat, zHat) ∈ admm_feasible_set A B c := by
    simpa using hfeas
  -- The transpose pairing is constant on the feasible fiber, so its image has greatest element
  -- `y c`.
  refine support_function_eq_of_isGreatest_image _ _ ?_
  refine ⟨?_, ?_⟩
  · refine ⟨(xHat, zHat), hxz_feas, ?_⟩
    simp [LinearMap.dualMap_apply, hfeas]
  · intro r hr
    rcases hr with ⟨xz, hxz, rfl⟩
    have hxz_eq : (A.coprod B) xz = c := by
      simpa using hxz
    simp [LinearMap.dualMap_apply, hxz_eq]

/-- Helper for Theorem 15.1: outside the transpose range, the support function of the ADMM
feasible affine fiber is infinite. -/
private theorem support_function_admm_feasible_set_eq_top_of_not_mem_dual_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (ξ : Module.Dual ℝ (X × Z))
    (hξ : ξ ∉ Set.range (A.coprod B).dualMap) :
    support_function (admm_feasible_set A B c) (-ξ) = ⊤ := by
  rcases hqual with ⟨xHat, hxHat, zHat, hzHat, hfeas⟩
  have hxz0 : (A.coprod B) (xHat, zHat) = c := by
    simpa using hfeas
  have hnegξ : -ξ ∉ Set.range (A.coprod B).dualMap := by
    intro hnegξ
    apply hξ
    rcases hnegξ with ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    simpa [hy]
  -- Route correction: compute the affine-fiber support function through the kernel-translation
  -- formula, then the off-range indicator term forces the value to `⊤`.
  calc
    support_function (admm_feasible_set A B c) (-ξ)
        = ((-ξ) (xHat, zHat) : EReal) +
            extendedIndicator (Set.range (A.coprod B).dualMap) (-ξ) := by
              simpa [admm_feasible_set, LinearMap.coprod_apply] using
                support_function_linear_fiber_eq_eval_add_indicator_dual_range
                  (L := A.coprod B) (x0 := (xHat, zHat)) (c := c) hxz0 (-ξ)
    _ = ⊤ := by
          simp [extendedIndicator, hnegξ]

/-- Helper for Theorem 15.1: subtracting the pulled-back dual pairing from the block objective
repackages the integrand as the ADMM Lagrangian plus the constant term `⟨y, c⟩`. -/
private theorem admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
    (y : Module.Dual ℝ Y) (xz : X × Z) :
    H[h₁, h₂] xz - (((A.coprod B).dualMap (-y)) xz : EReal) =
      admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y + (y c : EReal) := by
  rcases xz with ⟨x, z⟩
  have hpair :
      (((A.coprod B).dualMap (-y)) (x, z) : EReal) = -((y (A x + B z) : ℝ) : EReal) := by
    -- The transpose of `(-y)` evaluates to the negative primal pairing.
    let t : Y := (A.coprod B) (x, z)
    calc
      (((A.coprod B).dualMap (-y)) (x, z) : EReal)
          = ((((-y) t : ℝ)) : EReal) := by
              simp [LinearMap.dualMap_apply, t]
      _ = -(((y t : ℝ) : EReal)) := by
            simp
      _ = -((y (A x + B z) : ℝ) : EReal) := by
            simp [t, LinearMap.coprod_apply]
  have hsplit :
      ((y (A x + B z) : ℝ) : EReal) =
        (y (A x + B z - c) : EReal) + (y c : EReal) := by
    -- Split the affine pairing into the constraint residual and the constant term `⟨y, c⟩`.
    have hsplit_real : y (A x + B z - c) + y c = y (A x + B z) := by
      calc
        y (A x + B z - c) + y c = (y (A x + B z) - y c) + y c := by
          simp [sub_eq_add_neg, map_add, add_assoc]
        _ = y (A x + B z) := by
          abel
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hsplit_real.symm
  -- Rewrite the pulled-back pairing, then fold the residual term back into the Lagrangian owner.
  calc
    H[h₁, h₂] (x, z) - (((A.coprod B).dualMap (-y)) (x, z) : EReal)
        = h₁ x + h₂ z + ((y (A x + B z) : ℝ) : EReal) := by
            rw [admm_objective_apply, hpair]
            simp [sub_eq_add_neg]
    _ = h₁ x + h₂ z + (y (A x + B z - c) : EReal) + (y c : EReal) := by
          simpa [add_assoc] using congrArg (fun t : EReal ↦ h₁ x + h₂ z + t) hsplit
    _ = admm_lagrangian h₁ h₂ A B c x z y + (y c : EReal) := by
          rw [admm_lagrangian_apply]

/-- Helper for Theorem 15.1: translating an `EReal` range by a finite scalar translates its
infimum by the same scalar. -/
private theorem ereal_sInf_range_add_finite
    {α : Type*} (φ : α → EReal) (r : ℝ) :
    sInf (Set.range fun a : α ↦ φ a + (r : EReal)) = sInf (Set.range φ) + (r : EReal) := by
  refine le_antisymm ?_ ?_
  · -- Shift the translated infimum back by `-r` to recover a lower bound for the original range.
    have hshift :
        sInf (Set.range fun a : α ↦ φ a + (r : EReal)) + ((-r : ℝ) : EReal) ≤
          sInf (Set.range φ) := by
      refine le_sInf ?_
      intro x hx
      rcases hx with ⟨a, rfl⟩
      have hsInf :
          sInf (Set.range fun a : α ↦ φ a + (r : EReal)) ≤ φ a + (r : EReal) := by
        exact sInf_le (show φ a + (r : EReal) ∈ Set.range (fun a : α ↦ φ a + (r : EReal)) from
          ⟨a, rfl⟩)
      have hsInf' :
          sInf (Set.range fun a : α ↦ φ a + (r : EReal)) + ((-r : ℝ) : EReal) ≤
            φ a + (r : EReal) + ((-r : ℝ) : EReal) := by
        exact (EReal.addLECancellable_coe (-r)).add_le_add_iff_right.mpr hsInf
      calc
        sInf (Set.range fun a : α ↦ φ a + (r : EReal)) + ((-r : ℝ) : EReal) ≤
            φ a + (r : EReal) + ((-r : ℝ) : EReal) := hsInf'
        _ = φ a := by
              simpa [sub_eq_add_neg, add_assoc] using
                (EReal.add_sub_cancel_right (a := φ a) (b := r))
    have hshift' :
        sInf (Set.range fun a : α ↦ φ a + (r : EReal)) + ((-r : ℝ) : EReal) + (r : EReal) ≤
          sInf (Set.range φ) + (r : EReal) := by
      exact (EReal.addLECancellable_coe r).add_le_add_iff_right.mpr hshift
    calc
      sInf (Set.range fun a : α ↦ φ a + (r : EReal))
          = sInf (Set.range fun a : α ↦ φ a + (r : EReal)) + ((-r : ℝ) : EReal) + (r : EReal) := by
              simpa [sub_eq_add_neg, add_assoc] using
                (EReal.sub_add_cancel
                  (a := sInf (Set.range fun a : α ↦ φ a + (r : EReal))) (b := r)).symm
      _ ≤ sInf (Set.range φ) + (r : EReal) := hshift'
  · -- Conversely, `sInf (range φ) + r` is a lower bound for the translated range.
    refine le_sInf ?_
    intro x hx
    rcases hx with ⟨a, rfl⟩
    have hsInf : sInf (Set.range φ) ≤ φ a := by
      exact sInf_le (show φ a ∈ Set.range φ from ⟨a, rfl⟩)
    exact (EReal.addLECancellable_coe r).add_le_add_iff_right.mpr hsInf

/-- Helper for Theorem 15.1: on the transpose range, the first Fenchel term is the ADMM dual
objective plus the constant evaluation `⟨y, c⟩`. -/
private theorem neg_conjugate_admm_objective_coprodDual_neg_eq_dual_objective_add_eval
    (y : Module.Dual ℝ Y) :
    -conjugate_function (H[h₁, h₂]) ((A.coprod B).dualMap (-y)) =
      admm_dual_objective h₁ h₂ A B c y + (y c : EReal) := by
  -- Route correction: rewrite the negative conjugate through the ADMM Lagrangian owner instead
  -- of a raw product-conjugate splitting argument.
  rw [← ereal_sInf_range_sub_pairing_eq_neg_conjugate]
  have hrange :
      Set.range
          (fun xz : X × Z ↦ H[h₁, h₂] xz - (((A.coprod B).dualMap (-y)) xz : EReal)) =
        Set.range
          (fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y + (y c : EReal)) := by
    ext r
    constructor
    · rintro ⟨xz, rfl⟩
      exact ⟨xz,
        (admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
          (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) y xz).symm⟩
    · rintro ⟨xz, rfl⟩
      exact ⟨xz,
        admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
          (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) y xz⟩
  -- Pull the finite scalar `⟨y, c⟩` outside the infimum and use the Definition 15.2 owner.
  rw [hrange, ereal_sInf_range_add_finite]
  rw [← admm_dual_objective_eq_sInf_lagrangian (h₁ := h₁) (h₂ := h₂)
    (A := A) (B := B) (c := c) (y := y)]

/-- Helper for Theorem 15.1: on the transpose range, the unrestricted Fenchel dual objective
agrees with the ADMM dual objective. -/
private theorem fenchel_dual_objective_on_admm_constraint_dual_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (y : Module.Dual ℝ Y) :
    fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
      ((A.coprod B).dualMap (-y)) =
        admm_dual_objective h₁ h₂ A B c y := by
  have hneg :
      -((A.coprod B).dualMap (-y)) = (A.coprod B).dualMap y := by
    -- Negating the pulled-back `-y` recovers the ordinary transpose evaluation at `y`.
    simpa using congrArg Neg.neg ((A.coprod B).dualMap.map_neg y)
  -- Expand the Fenchel dual objective, rewrite both terms on the transpose range, and cancel
  -- the finite scalar `⟨y, c⟩`.
  calc
    fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
        ((A.coprod B).dualMap (-y))
        = -conjugate_function (H[h₁, h₂]) ((A.coprod B).dualMap (-y)) -
            support_function (admm_feasible_set A B c) ((A.coprod B).dualMap y) := by
              rw [fenchel_dual_objective_apply,
                conjugate_function_extendedIndicator_apply_eq_support_function, hneg]
    _ = (admm_dual_objective h₁ h₂ A B c y + (y c : EReal)) - (y c : EReal) := by
          rw [neg_conjugate_admm_objective_coprodDual_neg_eq_dual_objective_add_eval
            (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) y,
            support_function_admm_feasible_set_on_range
              (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual y]
    _ = admm_dual_objective h₁ h₂ A B c y := by
          simpa using
            (EReal.add_sub_cancel_right (a := admm_dual_objective h₁ h₂ A B c y) (b := y c))

/-- Helper for Theorem 15.1: outside the transpose range, the unrestricted Fenchel dual objective
collapses to `-∞`. -/
private theorem fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (ξ : Module.Dual ℝ (X × Z))
    (hξ : ξ ∉ Set.range (A.coprod B).dualMap) :
    fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ = ⊥ := by
  -- Expand the Fenchel dual objective and force the indicator-conjugate term to `⊤`.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function]
  rw [support_function_admm_feasible_set_eq_top_of_not_mem_dual_range
    (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual ξ hξ]
  simp

/-- Helper for Theorem 15.1: the unrestricted Fenchel dual value of the ADMM product formulation
is exactly the ADMM dual problem value. -/
private theorem fenchel_dual_problem_value_eq_admm_dual_problem_value
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
      admm_dual_problem_value h₁ h₂ A B c := by
  -- Compare the two dual suprema pointwise, using the on-range identification and the off-range
  -- `⊥` collapse.
  rw [fenchel_dual_problem_value_eq_sSup, admm_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨ξ, rfl⟩
    by_cases hξ : ξ ∈ Set.range (A.coprod B).dualMap
    · rcases hξ with ⟨y₀, rfl⟩
      rw [show (A.coprod B).dualMap y₀ = (A.coprod B).dualMap (-(-y₀)) by simp]
      rw [fenchel_dual_objective_on_admm_constraint_dual_range
        (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual (-y₀)]
      exact le_sSup ⟨-y₀, rfl⟩
    · rw [fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
      (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual ξ hξ]
      exact bot_le
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [← fenchel_dual_objective_on_admm_constraint_dual_range
      (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual y]
    exact le_sSup ⟨(A.coprod B).dualMap (-y), rfl⟩

/-- Helper for Theorem 15.1: the indicator of the nonempty ADMM feasible set is proper. -/
private theorem admm_feasible_set_indicator_proper
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    IsProperExtendedRealFunction (extendedIndicator (admm_feasible_set A B c)) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro xz
    by_cases hxz : xz ∈ admm_feasible_set A B c <;> simp [extendedIndicator, hxz]
  · rcases hqual with ⟨xHat, hxHat, zHat, hzHat, hfeas⟩
    exact ⟨(xHat, zHat), by simpa using hfeas⟩

/-- Helper for Theorem 15.1: the indicator of the ADMM feasible affine set is convex. -/
private theorem admm_feasible_set_indicator_convex :
    is_convex_function (extendedIndicator (admm_feasible_set A B c)) := by
  have h_zero_convex : is_convex_function (0 : X × Z → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (X × Z))))
  have h_constrained_convex :
      is_convex_function
        (constrained_problem_objective (0 : X × Z → EReal) (admm_feasible_set A B c)) :=
    is_convex_function_constrained_problem_objective h_zero_convex admm_feasible_set_convex
  -- Rewrite the constrained owner as the indicator because the zero function contributes nothing.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (0 : X × Z → EReal) (admm_feasible_set A B c) (fun _ _ ↦ by simp)] at h_constrained_convex
  simpa [composite_model_objective] using h_constrained_convex

-- Proof sketch: rewrite the affine-constrained ADMM primal problem as a Fenchel problem on the
-- product space `X × Z`, with the equality constraint encoded by the indicator of the affine set
-- `{(x, z) | A x + B z = c}`. The relative-interior feasibility assumption is exactly the
-- qualification needed to apply Fenchel--Rockafellar duality, and the resulting dual value is
-- `admm_dual_problem_value h₁ h₂ A B c`.
include h₁_proper h₂_proper h₁_convex h₂_convex hqual

omit h₁_proper h₂_proper h₁_convex h₂_convex in
/-- Helper for Theorem 15.1: a Fenchel dual maximizer for the ADMM product formulation must lie in
the transpose range, because off-range dual values collapse to `⊥` while the attained dual value
is finite. -/
private theorem fenchel_maximizer_mem_admm_constraint_dual_range
    (ξ : Module.Dual ℝ (X × Z))
    (hgreat :
      IsGreatest
        (Set.range
          (fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))))
        (fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ))
    (hfiniteF :
      ∃ r : ℝ,
        fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
          (r : EReal)) :
    ξ ∈ Set.range (A.coprod B).dualMap := by
  by_contra hξ
  have hfinite_ne_bot :
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ≠ ⊥ := by
    rcases hfiniteF with ⟨r, hr⟩
    rw [hr]
    exact EReal.coe_ne_bot r
  have hξ_value :
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
        fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ := by
    -- Rewrite the Fenchel dual value as the supremum of its objective range and evaluate it at
    -- the greatest point supplied by Chapter 4 dual attainment.
    rw [fenchel_dual_problem_value_eq_sSup]
    exact hgreat.csSup_eq
  rw [fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
    (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual ξ hξ] at hξ_value
  exact hfinite_ne_bot hξ_value

/-- Theorem 15.1 (1): under the relative-interior feasibility condition from Assumption 15.2(E),
the optimal values of the ADMM primal problem `(15.1)` and dual problem `(15.2)` coincide. -/
theorem admm_problem_value_eq_admm_dual_problem_value :
    H_opt[h₁, h₂; A, B, c] = admm_dual_problem_value h₁ h₂ A B c := by
  -- Route correction: after including the standing assumption package into the declaration
  -- abstraction, the source proof closes by a direct Fenchel-duality instantiation.
  calc
    H_opt[h₁, h₂; A, B, c]
        =
          sInf (Set.range (composite_model_objective (H[h₁, h₂])
            (extendedIndicator (admm_feasible_set A B c)))) :=
      admm_problem_value_eq_fenchel_primal_infimum
        (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) h₁_proper h₂_proper
    _ =
        fenchel_dual_problem_value (H[h₁, h₂])
          (extendedIndicator (admm_feasible_set A B c)) :=
      fenchel_duality_value_eq
        (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
        (admm_objective_proper (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper)
        (admm_feasible_set_indicator_proper
          (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual)
        (admm_objective_convex (h₁ := h₁) (h₂ := h₂) h₁_convex h₂_convex)
        (admm_feasible_set_indicator_convex (A := A) (B := B) (c := c))
        (by
          -- The ADMM relative-interior feasibility hypothesis is exactly the Fenchel
          -- qualification for the feasible-set indicator.
          simpa [effective_domain_extendedIndicator] using
            admm_fenchel_qualification
              (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c)
              h₁_proper h₂_proper hqual)
    _ = admm_dual_problem_value h₁ h₂ A B c :=
      fenchel_dual_problem_value_eq_admm_dual_problem_value
        (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual

-- Proof sketch: after the value equality above, the ADMM dual problem is a Fenchel dual problem
-- with the same qualification hypothesis. If the primal optimal value is finite, then the common
-- primal/dual value is finite, so the Chapter 4 dual-attainment theorem yields a dual maximizer,
-- which is rephrased as an `IsGreatest` point of the range of `admm_dual_objective`.
/-- Theorem 15.1 (2): under the same qualification, if the ADMM primal optimal value is finite,
then the dual problem `(15.2)` possesses an optimal solution. -/
theorem exists_isGreatest_admm_dual_objective_of_finite_admm_problem_value
    (hfinite : ∃ r : ℝ, H_opt[h₁, h₂; A, B, c] = (r : EReal)) :
    ∃ y : Module.Dual ℝ Y,
      IsGreatest (Set.range (admm_dual_objective h₁ h₂ A B c))
        (admm_dual_objective h₁ h₂ A B c y) := by
  have hfiniteF :
      ∃ r : ℝ,
        fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
          (r : EReal) := by
    rcases hfinite with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    -- First identify the unrestricted Fenchel dual value with the ADMM dual value, then use the
    -- already-established primal/dual equality to transport the finiteness witness.
    calc
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
          = admm_dual_problem_value h₁ h₂ A B c :=
        fenchel_dual_problem_value_eq_admm_dual_problem_value
          (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual
      _ = H_opt[h₁, h₂; A, B, c] := by
        -- Re-run the value equality locally to avoid ambiguity from the included declaration
        -- parameters in the public theorem constant.
        symm
        calc
          H_opt[h₁, h₂; A, B, c]
              =
                sInf (Set.range (composite_model_objective (H[h₁, h₂])
                  (extendedIndicator (admm_feasible_set A B c)))) :=
            admm_problem_value_eq_fenchel_primal_infimum
              (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) h₁_proper h₂_proper
          _ =
              fenchel_dual_problem_value (H[h₁, h₂])
                (extendedIndicator (admm_feasible_set A B c)) :=
            fenchel_duality_value_eq
              (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
              (admm_objective_proper (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper)
              (admm_feasible_set_indicator_proper
                (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual)
              (admm_objective_convex (h₁ := h₁) (h₂ := h₂) h₁_convex h₂_convex)
              (admm_feasible_set_indicator_convex (A := A) (B := B) (c := c))
              (by
                simpa [effective_domain_extendedIndicator] using
                  admm_fenchel_qualification
                    (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c)
                    h₁_proper h₂_proper hqual)
          _ = admm_dual_problem_value h₁ h₂ A B c :=
            fenchel_dual_problem_value_eq_admm_dual_problem_value
              (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual
      _ = (r : EReal) := hr
  rcases exists_isGreatest_fenchel_dual_objective_of_finite_value
      (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
      (admm_objective_proper (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper)
      (admm_feasible_set_indicator_proper
        (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual)
      (admm_objective_convex (h₁ := h₁) (h₂ := h₂) h₁_convex h₂_convex)
      (admm_feasible_set_indicator_convex (A := A) (B := B) (c := c))
      (by
        -- Reuse the same qualification rewrite as in the value theorem.
        simpa [effective_domain_extendedIndicator] using
          admm_fenchel_qualification
            (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c)
            h₁_proper h₂_proper hqual)
      hfiniteF with
    ⟨ξ, hξ_greatest⟩
  have hξ_mem :
      ξ ∈ Set.range (A.coprod B).dualMap :=
    fenchel_maximizer_mem_admm_constraint_dual_range
      (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) (hqual := hqual)
      ξ hξ_greatest hfiniteF
  rcases hξ_mem with ⟨η, hη⟩
  refine ⟨-η, ?_⟩
  refine ⟨⟨-η, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨y, rfl⟩
  have hle :
      fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
          ((A.coprod B).dualMap (-y)) ≤
        fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ :=
    hξ_greatest.2
      (show
          fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
              ((A.coprod B).dualMap (-y)) ∈
            Set.range
              (fenchel_dual_objective (H[h₁, h₂])
                (extendedIndicator (admm_feasible_set A B c))) from
        ⟨(A.coprod B).dualMap (-y), rfl⟩)
  have hξ_rewrite :
      fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ =
        admm_dual_objective h₁ h₂ A B c (-η) := by
    -- Rewrite the maximizing Fenchel dual point through its transpose-range representation.
    rw [← hη]
    simpa using
      (fenchel_dual_objective_on_admm_constraint_dual_range
        (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual (-η))
  -- Restrict the global Fenchel maximizer to the transpose range and rewrite both endpoints back
  -- to the ADMM dual objective.
  rw [fenchel_dual_objective_on_admm_constraint_dual_range
    (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (c := c) hqual y,
    hξ_rewrite] at hle
  exact hle

omit h₁_proper h₂_proper h₁_convex h₂_convex hqual

end
