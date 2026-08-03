import Mathlib
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap07.Proposition_7_16
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Example_12_21
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap16.Proposition_16_24
import BauschkeLean.Chap19.Proposition_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/- Source/core/bridge triage:
- `source-facing`: Example 19.8 is the cone-constrained proximal problem `(19.13)` with a
  positively homogeneous `Γ₀` penalty and the dual problem `(19.14)` over `D = (∂ ψ) 0`.
- `core/canonical`: the owner theorem is
  `argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator`.
- `bridge/view`: specialize that theorem to `φ = ι[K]`, use
  `proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex` to rewrite the
  indicator proximity operator as the metric projection `P[K, hK_cheb]`, use Example 13.3(ii) for
  the conjugate of the cone indicator, and use Proposition 16.24 to rewrite `ψ` as the support
  function of `(∂ ψ) 0`.
-/

variable (K : Set H) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
variable (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
variable {ψ : G → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(G))
variable (hψ_ph : PositivelyHomogeneous ψ.asEReal)
variable (z : H) (r : G) (L : H →L[ℝ] G)
variable (hsri : r ∈ sri (L '' K - effectiveDomain ψ))

local notation "hK_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex

local notation "D" => (∂ ψ) 0
local notation "dualObj" =>
  fun v : G ↦
    (1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) Kᵒ⊖ ^ 2 + ⟪v, r⟫_ℝ
local notation "primalObj" =>
  fun x : H ↦
    (ψ (L x - r) : EReal) + (((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)
local notation "ownerDualObj" =>
  fun v : G ↦
    ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
      ({}^[(1 : PosReal)] ι[K]) (z - L.adjoint v)) +
        (ψ∗[hψ] v : EReal) +
          ((⟪v, r⟫_ℝ : ℝ) : EReal)
local notation "ownerPrimalObj" =>
  fun x : H ↦
    (ι[K] x : EReal) + (ψ (L x - r) : EReal) +
      ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))

/-- Helper for Example 19.8: positive homogeneity identifies `ψ` with the support function of its
subdifferential at the origin, and this subdifferential is nonempty, closed, and convex. -/
lemma supportFunction_subdifferential_zero_data_of_positivelyHomogeneous_mem_gammaZero :
    ψ.asEReal = σ[D] ∧ D.Nonempty ∧ IsClosed D ∧ Convex ℝ D := by
  -- Start from the Chapter 14 support-function description of the linear minorant set.
  obtain ⟨hsupport, hminorant_nonempty, hminorant_closed, hminorant_convex⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hψ_ph hψ
  -- The support-function formula forces `ψ 0 = 0`, so the linear minorant set is `(∂ ψ) 0`.
  have hzero : (ψ 0 : EReal) = 0 :=
    value_zero_eq_zero_of_eq_supportFunction_nonempty hsupport hminorant_nonempty
  have hminorant_eq : linearMinorantSet ψ = D :=
    linearMinorantSet_eq_subdifferential_zero hzero
  -- Rewrite the Chapter 14 data into the Chapter 16 subdifferential-at-zero package.
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hminorant_eq] using hsupport
  · simpa [hminorant_eq] using hminorant_nonempty
  · simpa [hminorant_eq] using hminorant_closed
  · simpa [hminorant_eq] using hminorant_convex

/-- Helper for Example 19.8: the indicator of a closed convex set agrees with its Fenchel
biconjugate. -/
lemma biconjugate_indicator_eq_indicator_of_isClosed_convex
    (C : Set G) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ((ι[C]).asEReal)∗∗ = (ι[C]).asEReal := by
  by_cases hC_nonempty : C.Nonempty
  · have hC_gamma : ι[C] ∈ Γ₀(G) :=
      indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
    simpa using biconjugate_eq_of_mem_gammaZero hC_gamma
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    have hσ_empty : σ[(∅ : Set G)] = (fun _ : G ↦ (⊥ : EReal)) := by
      ext x
      simp [innerSupremumOn_eq_sSup_image]
    ext x
    rw [conjugate_indicator_eq_supportFunction]
    simp [hC_empty, hσ_empty, ERealFunction.conjugate]

/-- Helper for Example 19.8: the Fenchel conjugate of `ψ` is the indicator of
`(∂ ψ) 0` when `ψ` is positively homogeneous and belongs to `Γ₀(G)`. -/
lemma gammaZeroConjugate_eq_indicator_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero :
    (fun v : G ↦ (ψ∗[hψ] v : EReal)) = (ι[D]).asEReal := by
  obtain ⟨hsupport, hD_nonempty, hD_closed, hD_convex⟩ :=
    supportFunction_subdifferential_zero_data_of_positivelyHomogeneous_mem_gammaZero
      (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
      (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
      (z := z) (r := r) (L := L) (hsri := hsri)
  -- Rewrite `ψ` as a support function and then use the biconjugate formula for closed convex
  -- indicators.
  funext v
  calc
    (ψ∗[hψ] v : EReal) = ψ.asEReal∗ v := by
      rw [gammaZeroConjugate_apply]
    _ = (σ[D])∗ v := by
      rw [hsupport]
    _ = ((ι[D]).asEReal)∗∗ v := by
      rw [← conjugate_indicator_eq_supportFunction D]
    _ = ((ι[D]).asEReal) v := by
      simpa using congrFun
        (biconjugate_indicator_eq_indicator_of_isClosed_convex D hD_closed hD_convex) v
    _ = (ι[D] v : EReal) := rfl

/-- Helper for Example 19.8: the unit Moreau envelope of the indicator of the polar cone is the
half squared distance to that polar cone. -/
lemma unit_moreauEnvelope_indicator_polarCone_eq_half_sq_infDist (x : H) :
    ({}^[(1 : PosReal)] ι[Kᵒ⊖]) x =
      ((((1 / 2 : ℝ) * Metric.infDist x Kᵒ⊖ ^ 2 : ℝ) : EReal)) := by
  have hmoreau :=
    congrFun (indicator_moreauEnvelope_eq_scaled_sq_infEDist (Kᵒ⊖) (1 : PosReal)) x
  have hpolar_nonempty : (Kᵒ⊖ : Set H).Nonempty := by
    refine ⟨0, ?_⟩
    simpa using Set.zero_mem_polarCone K
  have hdist_top : (Metric.infEDist x Kᵒ⊖ : EReal) ≠ ⊤ := by
    intro htop
    rcases hpolar_nonempty with ⟨y, hy⟩
    exact ne_top_of_le_ne_top (edist_ne_top x y) (Metric.infEDist_le_edist_of_mem hy)
      (by simpa using htop)
  have hsq :
      (Metric.infEDist x Kᵒ⊖ : EReal) ^ 2 / (2 : EReal) =
        (((Metric.infDist x Kᵒ⊖ ^ 2) / 2 : ℝ) : EReal) := by
    have hdist_ne_bot : (Metric.infEDist x Kᵒ⊖ : EReal) ≠ ⊥ := by
      simp
    have htwo : (2 : EReal) = ((2 : ℝ) : EReal) := rfl
    rw [pow_two, ← EReal.coe_toReal hdist_top hdist_ne_bot,
      ← EReal.coe_toReal hdist_top hdist_ne_bot, htwo, ← EReal.coe_mul, ← EReal.coe_div]
    simp [Metric.infDist, pow_two]
  calc
    ({}^[(1 : PosReal)] ι[Kᵒ⊖]) x
        = (Metric.infEDist x Kᵒ⊖ : EReal) ^ 2 / (2 * ((1 : PosReal) : ℝ) : EReal) := hmoreau
    _ = (Metric.infEDist x Kᵒ⊖ : EReal) ^ 2 / (2 : EReal) := by
      norm_num
    _ = (((Metric.infDist x Kᵒ⊖ ^ 2) / 2 : ℝ) : EReal) := hsq
    _ = ((((1 / 2 : ℝ) * Metric.infDist x Kᵒ⊖ ^ 2 : ℝ) : EReal)) := by
      congr 1
      ring

/-- Helper for Example 19.8: after specializing Proposition 19.5 to `φ = ι[K]`, the owner dual
objective is the textbook dual objective plus the indicator of `(∂ ψ) 0`. -/
lemma specialized_dual_owner_eq_dualObj_add_indicator_subdifferential_zero
    (hindicator : ι[K] ∈ Γ₀(H)) :
    ownerDualObj = fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal) := by
  -- Route correction: instead of reconstructing Proposition 19.5's hidden perturbation object,
  -- move through the two public dual-objective bridge theorems that share that hidden left-hand
  -- side and then normalize the visible terms.
  funext v
  have hindicator_conj :
      ((ι[K])∗[hindicator]) = ι[Kᵒ⊖] := by
    -- Rewrite the packaged conjugate of `ι[K]` using the cone-indicator conjugacy from
    -- Example 13.3(ii).
    ext x
    apply Subtype.ext
    change (((ι[K])∗[hindicator] x : EReal)) = (ι[Kᵒ⊖] x : EReal)
    calc
      (((ι[K])∗[hindicator] x : EReal)) = ((ι[K]).asEReal∗ x) := by
        rw [gammaZeroConjugate_apply]
      _ = (ι[Kᵒ⊖] x : EReal) := by
        simpa using congrFun
          (conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
            K hK_nonempty hK_cone) x
  have hψ_conj : ψ∗[hψ] = ι[D] := by
    -- Positive homogeneity identifies the packaged conjugate of `ψ` with the indicator of
    -- `(∂ ψ) 0`.
    ext x
    apply Subtype.ext
    change ((ψ∗[hψ] x : EReal)) = (ι[D] x : EReal)
    simpa using congrFun
      (gammaZeroConjugate_eq_indicator_subdifferential_zero_of_positivelyHomogeneous_mem_gammaZero
        (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
        (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
        (z := z) (r := r) (L := L) (hsri := hsri)) x
  -- Follow Proposition 19.5 from the owner quadratic-minus-Moreau surface to the textbook
  -- `(19.9)` surface, then rewrite the cone and positively homogeneous pieces.
  have howner_quad :=
    perturbationDualObjective_compositePerturbationFunction_proximalObjective_translate_eq_quadratic_sub_moreauEnvelope
      (φ := ι[K]) (hφ := hindicator) (hψ := hψ) (z := z) (r := r) (L := L) v
  calc
    ownerDualObj v = _ := by
      simpa [ownerDualObj] using howner_quad.symm
    _ = ({}^[(1 : PosReal)] ((ι[K])∗[hindicator])) (z - L.adjoint v) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
      simpa using
        congrFun
          (perturbationDualObjective_compositePerturbationFunction_proximalObjective_translate
            (φ := ι[K]) (hφ := hindicator) (hψ := hψ) (z := z) (r := r) (L := L)) v
    _ = ({}^[(1 : PosReal)] ι[Kᵒ⊖]) (z - L.adjoint v) +
          (ι[D] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
      rw [hindicator_conj, hψ_conj]
    _ = ((((1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) Kᵒ⊖ ^ 2 : ℝ) : EReal)) +
          (ι[D] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
      rw [unit_moreauEnvelope_indicator_polarCone_eq_half_sq_infDist
        (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
        (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
        (z := z) (r := r) (L := L) (hsri := hsri) (x := z - L.adjoint v)]
    _ = (dualObj v : EReal) + (ι[D] v : EReal) := by
      -- The remaining terms are finite real scalars, so `simp` can fold them back into the
      -- textbook real-valued objective.
      simpa [dualObj, add_assoc, add_left_comm, add_comm]

/-- Example 19.8 (1): let `D = (∂ ψ) 0`. If `K` is a nonempty closed convex cone,
`ψ ∈ Γ₀(G)` is positively homogeneous, and `r ∈ sri (L(K) - dom ψ)`, then the dual problem
`(19.14)`,
`min { (1 / 2) d_{Kᵒ⊖}(z - L^* v)^2 + ⟪v, r⟫ | v ∈ D }`,
has at least one solution. -/
theorem argminOn_dual_subdifferential_zero_nonempty_for_cone_positivelyHomogeneous_problem :
    (Argmin[D] dualObj).Nonempty := by
  have hindicator : ι[K] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
  have hsri_owner : r ∈ sri (L '' effectiveDomain (ι[K]) - effectiveDomain ψ) := by
    -- The indicator domain is exactly `K`, so the owner's regularity condition is the given one.
    simpa [effectiveDomain_indicator] using hsri
  obtain ⟨howner_nonempty, _⟩ :=
    argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
      (φ := ι[K]) (hφ := hindicator) (hψ := hψ) (z := z) (r := r) (L := L) hsri_owner
  obtain ⟨w, hw⟩ := howner_nonempty
  have hdual_rewrite :
      ownerDualObj = fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal) :=
    specialized_dual_owner_eq_dualObj_add_indicator_subdifferential_zero
      (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
      (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
      (z := z) (r := r) (L := L) (hsri := hsri) hindicator
  have hw_global :
      w ∈ Argmin (fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) := by
    -- Rewrite the owner argmin statement into the textbook global dual objective.
    rw [mem_argmin_iff] at hw ⊢
    simpa [hdual_rewrite] using hw
  obtain ⟨_, hD_nonempty, _, _⟩ :=
    supportFunction_subdifferential_zero_data_of_positivelyHomogeneous_mem_gammaZero
      (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
      (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
      (z := z) (r := r) (L := L) (hsri := hsri)
  have hw_mem_D : w ∈ D := by
    -- Compare against a feasible point in `D`; outside `D` the indicator term makes the objective
    -- equal `⊤`, so a global minimizer cannot lie there.
    rw [mem_argmin_iff, isMinOn_univ_iff] at hw_global
    obtain ⟨d0, hd0⟩ := hD_nonempty
    by_contra hw_not_mem
    have hw_top :
        ((fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) w) = ⊤ := by
      simp [hw_not_mem]
    have hd0_not_top :
        ((fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) d0) ≠ ⊤ := by
      simp [dualObj, hd0]
    have hmin : ((fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) w) ≤
        ((fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) d0) :=
      hw_global d0
    rw [hw_top] at hmin
    exact hd0_not_top (top_le_iff.mp hmin)
  have hdual_not_bot : ∀ v ∉ D, (dualObj v : EReal) ≠ ⊥ := by
    -- The quadratic-distance-plus-linear term is real-valued, hence never `⊥`.
    intro v _
    simp [dualObj]
  have hargminOn :
      Argmin[D] (fun v : G ↦ (dualObj v : EReal)) =
        D ∩ Argmin (fun v : G ↦ (dualObj v : EReal) + (ι[D] v : EReal)) :=
    argminOn_eq_inter_argmin_add_indicator (f := fun v : G ↦ (dualObj v : EReal)) D hdual_not_bot
  have hw_on :
      w ∈ Argmin[D] (fun v : G ↦ (dualObj v : EReal)) := by
    rw [hargminOn]
    exact ⟨hw_mem_D, hw_global⟩
  exact ⟨w, by simpa using hw_on⟩

/-- Example 19.8 (2): let `D = (∂ ψ) 0`. If `v` solves the dual problem `(19.14)`, then the
unique solution of the cone-constrained primal problem `(19.13)`,
`min { ψ(Lx - r) + (1 / 2) ‖x - z‖^2 | x ∈ K }`, is the metric projection of
`z - L^* v` onto `K`. -/
theorem
    argminOn_cone_positivelyHomogeneous_plus_half_sqDist_eq_singleton_projection_of_mem_dualArgmin
    {v : G} (hv : v ∈ Argmin[D] dualObj) :
    Argmin[K] primalObj = {P[K, hK_cheb] (z - L.adjoint v)} := by
  have hindicator : ι[K] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
  have hsri_owner : r ∈ sri (L '' effectiveDomain (ι[K]) - effectiveDomain ψ) := by
    -- The indicator domain is `K`, so Proposition 19.5 applies with the same regularity input.
    simpa [effectiveDomain_indicator] using hsri
  have hdual_not_bot : ∀ u ∉ D, (dualObj u : EReal) ≠ ⊥ := by
    -- The dual objective is real-valued before the indicator is added.
    intro u _
    simp [dualObj]
  have hdual_argminOn :
      Argmin[D] (fun u : G ↦ (dualObj u : EReal)) =
        D ∩ Argmin (fun u : G ↦ (dualObj u : EReal) + (ι[D] u : EReal)) :=
    argminOn_eq_inter_argmin_add_indicator (f := fun u : G ↦ (dualObj u : EReal)) D hdual_not_bot
  have hv_on : v ∈ Argmin[D] (fun u : G ↦ (dualObj u : EReal)) := by
    simpa using hv
  have hv_global :
      v ∈ Argmin (fun u : G ↦ (dualObj u : EReal) + (ι[D] u : EReal)) := by
    -- Drop the explicit constraint now that the indicator term encodes it.
    rw [hdual_argminOn] at hv_on
    exact hv_on.2
  have hdual_rewrite :
      ownerDualObj = fun u : G ↦ (dualObj u : EReal) + (ι[D] u : EReal) :=
    specialized_dual_owner_eq_dualObj_add_indicator_subdifferential_zero
      (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
      (hK_convex := hK_convex) (hK_cone := hK_cone) (hψ := hψ) (hψ_ph := hψ_ph)
      (z := z) (r := r) (L := L) (hsri := hsri) hindicator
  have hv_owner : v ∈ Argmin ownerDualObj := by
    -- Translate the textbook dual argmin back to the owner objective from Proposition 19.5.
    rw [mem_argmin_iff] at hv_global ⊢
    simpa [hdual_rewrite] using hv_global
  obtain ⟨_, hprimal_singleton⟩ :=
    argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
      (φ := ι[K]) (hφ := hindicator) (hψ := hψ) (z := z) (r := r) (L := L) hsri_owner
  have hprox :
      Prox[ι[K], hindicator] = P[K, hK_cheb] := by
    simpa using
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hK_nonempty hK_closed hK_convex
  have howner_primal :
      Argmin (fun x : H ↦ primalObj x + (ι[K] x : EReal)) =
        ({P[K, hK_cheb] (z - L.adjoint v)} : Set H) := by
    -- Rewrite the owner's primal surface as the constrained objective plus the indicator of `K`.
    simpa [ownerPrimalObj, primalObj, hprox, add_assoc, add_left_comm, add_comm] using
      hprimal_singleton hv_owner
  have hprimal_not_bot : ∀ x ∉ K, primalObj x ≠ ⊥ := by
    -- The penalty lies in `]-∞, +∞]`, and the quadratic term is finite.
    intro x _
    simp [primalObj]
  have hprimal_argminOn :
      Argmin[K] primalObj = K ∩ Argmin (fun x : H ↦ primalObj x + (ι[K] x : EReal)) :=
    argminOn_eq_inter_argmin_add_indicator (f := primalObj) K hprimal_not_bot
  -- Intersect the owner singleton with `K`; the projection point already belongs to `K`.
  rw [hprimal_argminOn, howner_primal]
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨projectionPoint_mem K hK_cheb (z - L.adjoint v), Set.mem_singleton _⟩

end PrimalSolutionsViaDualSolutions

end ERealFunction
