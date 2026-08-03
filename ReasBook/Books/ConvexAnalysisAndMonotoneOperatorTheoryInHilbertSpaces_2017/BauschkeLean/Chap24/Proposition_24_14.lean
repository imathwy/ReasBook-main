import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Remark_16_28

namespace ERealFunction

open ContinuousLinearMap
open scoped Pointwise

universe u v

section CompAdjointEqSmulId

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 24.14: the scalar-adjoint identity `L ∘L L* = μ • Id` makes `L`
surjective. -/
private theorem surjective_of_comp_adjoint_eq_smul_id
    (L : H →L[ℝ] K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    Function.Surjective L := by
  intro y
  refine ⟨(μ : ℝ)⁻¹ • L.adjoint y, ?_⟩
  -- Evaluate the operator identity at `y` and solve for a preimage explicitly.
  have happly := congrArg (fun T : K →L[ℝ] K ↦ T y) hscalar
  have hLLstar : L (L.adjoint y) = (μ : ℝ) • y := by
    simpa using happly
  calc
    L ((μ : ℝ)⁻¹ • L.adjoint y) = (μ : ℝ)⁻¹ • L (L.adjoint y) := by
      rw [ContinuousLinearMap.map_smul]
    _ = (μ : ℝ)⁻¹ • ((μ : ℝ) • y) := by
      rw [hLLstar]
    _ = y := by
      rw [smul_smul]
      simp [inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]

-- Source/core/bridge triage:
-- `source-facing`: Proposition 24.14 states `Γ₀`-stability and the proximal formula for the
--   precomposition `f ∘ L` under the scalar-adjoint hypothesis `L ∘L L* = μ • Id`.
-- `core/canonical`: the Chapter 16 owner for the chain rule is `adjointImageSubdifferential`,
--   and the Chapter 23 owner for the prox formula is the adjoint-image resolvent identity.
-- `bridge/view`: the companion theorem below records the subdifferential bridge under the same
--   source hypothesis, while the proposition itself stays on the source-facing `Γ₀` and `Prox`
--   surfaces.

variable (f : K → Set.Ioi (⊥ : EReal))
variable (L : H →L[ℝ] K) (μ : PosReal)

/-- The `Γ₀`-stability part of Proposition 24.14: let `L : H →L[ℝ] K` satisfy
`L ∘L L* = μ • Id` for some `μ ∈ ℝ_{++}`. If `f ∈ Γ₀(K)`, then the precomposition
`f ∘ L` belongs to `Γ₀(H)`.

This is the source-facing specialization of the earlier precomposition owner to the full-range
condition induced by `L ∘L L* = μ • Id`. -/
theorem comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id
    (hf : f ∈ Γ₀(K))
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    f ∘ L ∈ Γ₀(H) := by
  -- Use the Chapter 16 composition owner once surjectivity gives a range-domain witness.
  refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty f hf L ?_
  rcases hf.2.nonempty with ⟨y, hy⟩
  rcases surjective_of_comp_adjoint_eq_smul_id L μ hscalar y with ⟨x, rfl⟩
  exact ⟨L x, ⟨⟨x, rfl⟩, hy⟩⟩

/-- Helper for Proposition 24.14: every element of `L^*(∂ f)(L x)` is already a subgradient of
`f ∘ L` at `x`. -/
private theorem memSubdifferentialCompOfMemAdjointImage
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    {x u : H} (hu : u ∈ ContinuousLinearMap.adjointImageSubdifferential L g x) :
    u ∈ (∂ (g ∘ L)) x := by
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image] at hu
  rcases hu with ⟨v, hv, rfl⟩
  -- Unpack the witness-level adjoint image membership and rewrite the subgradient inequality
  -- through the adjoint identity.
  rw [mem_subdifferential_iff] at hv ⊢
  intro y
  simpa [Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_sub_eq (L := L) (x := x) (y := y) (v := v)] using hv (L y)

/-- Helper for Proposition 24.14: under the scalar-adjoint hypothesis, every subgradient of
`g ∘ L` already lies in `L^*(∂ g)(L x)`. -/
private theorem memAdjointImageOfMemSubdifferentialCompOfCompAdjointEqSmulId
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    {x u : H} (hu : u ∈ (∂ (g ∘ L)) x) :
    u ∈ ContinuousLinearMap.adjointImageSubdifferential L g x := by
  have hsurj : Function.Surjective L :=
    surjective_of_comp_adjoint_eq_smul_id L μ hscalar
  rcases hg.2.nonempty with ⟨y, hy⟩
  rcases hsurj y with ⟨x0, hx0⟩
  have hcomp_nonempty : (effectiveDomain (g ∘ L)).Nonempty := by
    refine ⟨x0, ?_⟩
    exact mem_effectiveDomain_iff.mpr <| by
      simpa [Function.comp_apply, hx0] using (mem_effectiveDomain_iff.mp hy)
  have hx_dom : x ∈ SetValuedOperator.dom (∂ (g ∘ L)) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hx_eff : x ∈ effectiveDomain (g ∘ L) :=
    subdifferential_domain_subset_effectiveDomain (g ∘ L) hcomp_nonempty hx_dom
  have hgLx_top : (g (L x) : EReal) ≠ ⊤ := by
    simpa [Function.comp_apply] using ne_of_lt (mem_effectiveDomain_iff.mp hx_eff)
  have hu_sub := (mem_subdifferential_iff (f := g ∘ L) (x := x) (u := u)).1 hu
  have hu_orth : ∀ k : H, k ∈ L.ker → inner ℝ k u = 0 := by
    intro k hk
    have hk0 : L k = 0 := LinearMap.mem_ker.mp hk
    have hgLx_bot : (g (L x) : EReal) ≠ ⊥ := ne_of_gt (g (L x)).2
    have real_le_zero_of_add_le {r : ℝ}
        (h : ((r : EReal) + (g (L x) : EReal)) ≤ (g (L x) : EReal)) :
        r ≤ 0 := by
      rw [← EReal.coe_toReal hgLx_top hgLx_bot] at h
      have h' :
          (((r + (g (L x) : EReal).toReal : ℝ) : EReal)) ≤
            (((g (L x) : EReal).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_add] using h
      have hreal : r + (g (L x) : EReal).toReal ≤ (g (L x) : EReal).toReal := by
        exact_mod_cast h'
      linarith
    have hplus := by
      simpa [ContinuousLinearMap.map_add, hk0] using hu_sub (x + k)
    have hplus_real : inner ℝ k u ≤ 0 :=
      real_le_zero_of_add_le hplus
    have hneg_bound : inner ℝ (-k) u ≤ 0 := by
      have hplus_neg := by
        simpa [ContinuousLinearMap.map_add, hk0] using hu_sub (x + (-k))
      simpa using real_le_zero_of_add_le (r := -inner ℝ k u) hplus_neg
    have hminus_real : -inner ℝ k u ≤ 0 := by
      simpa using hneg_bound
    linarith
  let v : K := (μ : ℝ)⁻¹ • L u
  have hw_ker : u - L.adjoint v ∈ L.ker := by
    rw [LinearMap.mem_ker]
    have hLLstar_apply :
        L (L.adjoint v) = (μ : ℝ) • v := by
      simpa using congrArg (fun T : K →L[ℝ] K ↦ T v) hscalar
    calc
      L (u - L.adjoint v) = L u - L (L.adjoint v) := by
        simp
      _ = L u - (μ : ℝ) • v := by
        rw [hLLstar_apply]
      _ = 0 := by
        dsimp [v]
        rw [smul_smul]
        rw [mul_inv_cancel₀ μ.2.ne', one_smul, sub_self]
  have hLv : L.adjoint v = u := by
    set w : H := u - L.adjoint v with hw
    have hw_ker' : w ∈ L.ker := by
      simpa [hw] using hw_ker
    have hw_self : inner ℝ w w = 0 := by
      calc
        inner ℝ w w = inner ℝ w u - inner ℝ w (L.adjoint v) := by
          rw [hw, inner_sub_right]
        _ = 0 - inner ℝ (L w) v := by
          rw [hu_orth w hw_ker', (ContinuousLinearMap.adjoint_inner_right L w v).symm]
        _ = 0 := by
          have hw0 : L w = 0 := LinearMap.mem_ker.mp hw_ker'
          simp [hw0]
    have hw_zero : w = 0 := by
      simpa using inner_self_eq_zero.mp hw_self
    have huv_zero : u - L.adjoint v = 0 := by
      simpa [hw] using hw_zero
    exact (sub_eq_zero.mp huv_zero).symm
  have hu_eq :=
    -- Start from the Fenchel--Young characterization of the composite subgradient.
    (mem_subdifferential_iff_fenchel_young_eq (f := g ∘ L) hcomp_nonempty x u).1 hu
  have hinner_real : inner ℝ x u = inner ℝ (L x) v := by
    -- Transport the inner product through the adjoint identity and the exact witness
    -- `L.adjoint v = u`.
    simpa [hLv] using (ContinuousLinearMap.adjoint_inner_right L x v)
  have huvalue' : (g ∘ L).asEReal∗ u = g.asEReal∗ v := by
    -- Surjectivity turns the composite conjugate into the ordinary conjugate at the unique
    -- adjoint witness `v`.
    have huvalue_left : (g ∘ L).asEReal∗ u ≤ g.asEReal∗ v := by
      rw [conjugate_apply, conjugate_apply]
      refine iSup_le fun z ↦ ?_
      calc
        (((inner ℝ z u : ℝ) : EReal) - (g ∘ L) z)
            = (((inner ℝ (L z) v : ℝ) : EReal) - g (L z)) := by
                simpa [Function.asEReal_apply, Function.comp_apply, hLv] using
                  congrArg (fun r : ℝ ↦ ((r : EReal) - g (L z)))
                    (ContinuousLinearMap.adjoint_inner_right L z v)
        _ ≤ ⨆ y : K, (((inner ℝ y v : ℝ) : EReal) - g y) := by
              exact le_iSup (fun y : K ↦ (((inner ℝ y v : ℝ) : EReal) - g y)) (L z)
    have huvalue_right : g.asEReal∗ v ≤ (g ∘ L).asEReal∗ u := by
      rw [conjugate_apply, conjugate_apply]
      refine iSup_le fun y ↦ ?_
      rcases hsurj y with ⟨z, rfl⟩
      calc
        (((inner ℝ (L z) v : ℝ) : EReal) - g (L z))
            = (((inner ℝ z u : ℝ) : EReal) - (g ∘ L) z) := by
                simpa [Function.asEReal_apply, Function.comp_apply, hLv] using
                  congrArg (fun r : ℝ ↦ ((r : EReal) - g (L z)))
                    (ContinuousLinearMap.adjoint_inner_right L z v).symm
        _ ≤ ⨆ z' : H, (((inner ℝ z' u : ℝ) : EReal) - (g ∘ L) z') := by
              exact le_iSup (fun z' : H ↦ (((inner ℝ z' u : ℝ) : EReal) - (g ∘ L) z')) z
    exact le_antisymm huvalue_left huvalue_right
  -- Finally package the witness as membership in the adjoint-image operator.
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
  refine ⟨v, ?_, hLv⟩
  have hgy := calc
    (g (L x) : EReal) + g.asEReal∗ v = (g (L x) : EReal) + (g ∘ L).asEReal∗ u := by
      rw [← huvalue']
    _ = ((inner ℝ x u : ℝ) : EReal) := hu_eq
    _ = ((inner ℝ (L x) v : ℝ) : EReal) := congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  -- One more Fenchel--Young rewrite identifies `v` as a subgradient of `g` at `L x`.
  exact (mem_subdifferential_iff_fenchel_young_eq (f := g) hg.2.nonempty (L x) v).2 hgy

/-- Companion to Proposition 24.14: under the same scalar-adjoint hypothesis, the subdifferential
chain rule for `f ∘ L` takes the canonical Chapter 16 form
`∂ (f ∘ L) = L^* ∘ (∂ f) ∘ L`, realized as `adjointImageSubdifferential L f`. -/
theorem
    subdifferential_comp_eq_adjointImageSubdifferential_of_comp_adjoint_eq_smul_id
    (hf : f ∈ Γ₀(K))
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    ∂ (f ∘ L) = adjointImageSubdifferential L f := by
  -- Route correction: avoid the broken Chapter 15/16 chain-rule imports and prove both
  -- inclusions directly from the subgradient inequality plus the scalar-adjoint identity.
  ext x u
  constructor
  · intro hu
    exact memAdjointImageOfMemSubdifferentialCompOfCompAdjointEqSmulId
      (g := f) (hg := hf) (L := L) (μ := μ) hscalar
      hu
  · intro hu
    exact memSubdifferentialCompOfMemAdjointImage (g := f) (L := L) hu

/-- Helper for Proposition 24.14: the canonical candidate
`p = x + μ⁻¹ • L* (Prox_{μ f}(L x) - L x)` satisfies the residual inclusion
`x - p ∈ ∂ (f ∘ L) p`. -/
private theorem candidateResidualMemSubdifferentialCompOfCompAdjointEqSmulId
    (hf : f ∈ Γ₀(K))
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (x : H) :
    let q := Prox[μ, f, hf] (L x)
    let p := x + (μ : ℝ)⁻¹ • L.adjoint (q - L x)
    x - p ∈ (∂ (f ∘ L)) p := by
  let q := Prox[μ, f, hf] (L x)
  let p := x + (μ : ℝ)⁻¹ • L.adjoint (q - L x)
  have hscaledResidual :
      L x - q ∈ (∂ ((μ • f : K → Set.Ioi (⊥ : EReal)))) q := by
    -- Read the scaled proximal point as a scaled subgradient inclusion.
    simpa [q, scaledProximityOperator] using
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (f := (μ • f : K → Set.Ioi (⊥ : EReal)))
        (hf := smul_mem_gammaZero f hf μ)
        (x := L x)
        (p := q)).1 rfl
  have hbaseResidual :
      ((μ : ℝ)⁻¹ • (L x - q)) ∈ (∂ f) q := by
    -- Undo the positive scalar on the subdifferential side.
    rw [subdifferential_posReal_smul_eq_smul (f := f) (γ := μ)] at hscaledResidual
    change L x - q ∈ (μ : ℝ) • ((∂ f) q) at hscaledResidual
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ μ.2.ne'] at hscaledResidual
    simpa [smul_smul, mul_inv_cancel₀ μ.2.ne'] using hscaledResidual
  have hLLstar_apply :
      L (L.adjoint (q - L x)) = (μ : ℝ) • (q - L x) := by
    -- Evaluate the scalar-adjoint identity on the candidate residual.
    simpa using congrArg (fun T : K →L[ℝ] K ↦ T (q - L x)) hscalar
  have hLp : L p = q := by
    -- Push `L` through the candidate formula and simplify the scalar cancellation.
    calc
      L p = L x + (μ : ℝ)⁻¹ • L (L.adjoint (q - L x)) := by
        simp [p, ContinuousLinearMap.map_add]
      _ = L x + (μ : ℝ)⁻¹ • ((μ : ℝ) • (q - L x)) := by
        rw [hLLstar_apply]
      _ = L x + (q - L x) := by
        rw [smul_smul]
        simp [inv_mul_cancel₀ μ.2.ne']
      _ = q := by
        abel_nf
  have hxSubEq :
      x - p = L.adjoint (((μ : ℝ)⁻¹) • (L x - q)) := by
    have hsub : q - L x = -(L x - q) := by
      abel_nf
    -- Normalize the residual so it matches the adjoint-image witness exactly.
    calc
      x - p = -((μ : ℝ)⁻¹ • L.adjoint (q - L x)) := by
        simp [p]
      _ = -((μ : ℝ)⁻¹ • L.adjoint (-(L x - q))) := by
        rw [hsub]
      _ = -(-((μ : ℝ)⁻¹ • L.adjoint (L x - q))) := by
        rw [ContinuousLinearMap.map_neg, smul_neg]
      _ = (μ : ℝ)⁻¹ • L.adjoint (L x - q) := by
        simp
      _ = L.adjoint (((μ : ℝ)⁻¹) • (L x - q)) := by
        rw [ContinuousLinearMap.map_smul]
  have hadjoint :
      x - p ∈ adjointImageSubdifferential L f p := by
    -- Package the residual as an adjoint-image witness at the candidate point.
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
    refine ⟨((μ : ℝ)⁻¹ • (L x - q)), ?_, hxSubEq.symm⟩
    simpa [hLp] using hbaseResidual
  -- Replace the composite subdifferential by the adjoint-image bridge and close the goal.
  rw [subdifferential_comp_eq_adjointImageSubdifferential_of_comp_adjoint_eq_smul_id
    (f := f) (L := L) (μ := μ) hf hscalar]
  exact hadjoint

/-- Proposition 24.14 (2): under the hypotheses of Proposition 24.14, the proximal point of the
precomposition `f ∘ L` is
`x + μ⁻¹ • L* (Prox_{μ f}(L x) - L x)`, written on the local Chapter 24 owner
`Prox[μ, f, hf]`. -/
theorem prox_comp_continuousLinearMap_eq_add_inv_smul_adjoint_sub_of_comp_adjoint_eq_smul_id
    (hf : f ∈ Γ₀(K))
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (x : H) :
    Prox[
      f ∘ L,
      comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id f L μ hf hscalar
    ] x =
      x + (μ : ℝ)⁻¹ • L.adjoint (Prox[μ, f, hf] (L x) - L x) := by
  let q := Prox[μ, f, hf] (L x)
  let p := x + (μ : ℝ)⁻¹ • L.adjoint (q - L x)
  have hp :
      p = Prox[
        f ∘ L,
        comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id f L μ hf hscalar
      ] x := by
    -- Characterize the candidate point through the residual inclusion proved above.
    apply (eq_proximityOperator_iff_sub_mem_subdifferential
      (f := f ∘ L)
      (hf := comp_continuousLinearMap_mem_gammaZero_of_comp_adjoint_eq_smul_id
        f L μ hf hscalar)
      (x := x)
      (p := p)).2
    simpa [p, q] using
      candidateResidualMemSubdifferentialCompOfCompAdjointEqSmulId
        (f := f) (L := L) (μ := μ) hf hscalar x
  simpa [p, q] using hp.symm

end CompAdjointEqSmulId

end ERealFunction
