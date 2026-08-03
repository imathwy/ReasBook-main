import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap23.Corollary_23_11

-- Semantic recall note: `lean_leansearch` surfaced only the unrelated algebra-spectrum
-- resolvent API, so this item follows the verified local Chapter 23 owners `J[...]`,
-- `resolventMap`, `toSetValuedOperator`, and `Maximal IsMonotone`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 23.29 studies the scaled resolvent operator
  `μ⁻¹ J[((μ : ℝ) • A)]`.
- `core/canonical`: the Chapter 23 owner is the resolvent `J[...]` itself together with ordinary
  scalar multiplication of set-valued operators.
- `bridge/view`: the single-valued realizer `fun x ↦ (μ : ℝ)⁻¹ • resolventMap A hA μ x` is only a
  pointwise view of that operator and should not be kept as a parallel public owner. -/

/-- For maximally monotone `A`, the singleton-valued realizer
`x ↦ (μ : ℝ)⁻¹ • resolventMap A hA μ x` induces the scaled resolvent
`((μ : ℝ)⁻¹) • J[((μ : ℝ) • A)]`. -/
theorem inv_smul_resolventMap_toSetValuedOperator_eq_inv_smul_resolvent
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (μ : PosReal) :
    (fun x : H ↦ (μ : ℝ)⁻¹ • resolventMap A hA μ x).toSetValuedOperator =
      ((μ : ℝ)⁻¹) • J[((μ : ℝ) • A)] := by
  ext x y
  constructor
  · intro hy
    -- Unpack the singleton-valued realizer and reinsert the inverse scalar on the operator side.
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hy
    rw [Pi.smul_apply, resolvent_smul_eq_singleton_resolventMap_of_maximal A hA μ]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero μ.2.ne')]
    simp [hy, smul_smul, μ.2.ne']
  · intro hy
    -- Cancel the positive scalar to recover the singleton-valued realizer.
    rw [Pi.smul_apply, resolvent_smul_eq_singleton_resolventMap_of_maximal A hA μ] at hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero μ.2.ne')] at hy
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    apply smul_right_injective H μ.2.ne'
    simpa [smul_smul, μ.2.ne'] using hy

/-- For maximally monotone `A`, the scaled resolvent realizer agrees pointwise with the
source-facing formula `x ↦ (μ : ℝ)⁻¹ • x - yosidaApproximationMap A hA μ x`. -/
theorem inv_smul_resolventMap_eq_inv_smul_id_sub_yosidaApproximationMap
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (μ : PosReal) :
    (fun x : H ↦ (μ : ℝ)⁻¹ • resolventMap A hA μ x) =
      fun x : H ↦ (μ : ℝ)⁻¹ • x - yosidaApproximationMap A hA μ x := by
  funext x
  -- Expand the Yosida realizer and regroup the residual term.
  rw [yosidaApproximationMap_apply]
  have hrewrite :
      (μ : ℝ)⁻¹ • x - (μ : ℝ)⁻¹ • (x - resolventMap A hA μ x) =
        (μ : ℝ)⁻¹ • resolventMap A hA μ x := by
    rw [smul_sub]
    abel_nf
  exact hrewrite.symm

/-- Helper for Proposition 23.29: if `A : H → 2^H` is maximally monotone and `μ ∈ ℝ_{++}`, then
the scaled resolvent `μ⁻¹ J[((μ : ℝ) • A)]` is maximally monotone. -/
theorem inv_smul_resolvent_isMaximallyMonotone
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (μ : PosReal) :
    Maximal IsMonotone (((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)]) := by
  let μinv : PosReal := ⟨((μ : ℝ)⁻¹ : ℝ), inv_pos.mpr μ.2⟩
  -- Transport maximal monotonicity from the resolvent to its positive scalar multiple.
  simpa [μinv] using
    maximal_isMonotone_smul (resolvent_smul_isMaximallyMonotone A hA μ) μinv

omit [CompleteSpace H] in
/-- Helper for Proposition 23.29: membership in the inverse-scaled resolvent is equivalent to
membership of the rescaled point in the original resolvent. -/
private theorem mem_inv_smul_resolvent_iff
    {A : SetValuedOperator H H} (μ : PosReal) (p q : H) :
    q ∈ (((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)]) p ↔
      (μ : ℝ) • q ∈ J[((μ : ℝ) • A)] p := by
  constructor
  · intro hq
    -- Cancel the inverse scalar on the set-valued side.
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero μ.2.ne')] at hq
    simpa using hq
  · intro hq
    -- Reinsert the inverse scalar to recover the scaled resolvent surface.
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero μ.2.ne')]
    simpa using hq

omit [CompleteSpace H] in
/-- Helper for Proposition 23.29: after clearing denominators, the `μ`-resolvent residual at
`x - (γ / μ) • q` matches the normalized `δ`-resolvent residual at `((μ / (μ + γ)) • x)`, where
`δ = μ * μ * (μ + γ)⁻¹`. -/
private theorem scaledResolventResidual_eq_normalizedResidual
    (μ γ : PosReal) (x q : H) :
    let δ : PosReal := μ * μ * (μ + γ)⁻¹
    ((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q) =
      ((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q) := by
  let δ : PosReal := μ * μ * (μ + γ)⁻¹
  have hμsq : ((μ : ℝ) * (μ : ℝ)) ≠ 0 := mul_ne_zero μ.2.ne' μ.2.ne'
  have hleftCoeff : ((μ : ℝ) * (μ : ℝ)) * ((μ : ℝ)⁻¹ : ℝ) = (μ : ℝ) := by
    field_simp [μ.2.ne']
  have hleftDivCoeff :
      ((μ : ℝ) * (μ : ℝ)) * (((μ : ℝ)⁻¹ : ℝ) * ((γ : ℝ) / (μ : ℝ))) = (γ : ℝ) := by
    field_simp [μ.2.ne']
  have hrightCoeff :
      ((μ : ℝ) * (μ : ℝ)) * ((δ : ℝ)⁻¹ : ℝ) = ((μ + γ : PosReal) : ℝ) := by
    dsimp [δ]
    field_simp [μ.2.ne', (μ + γ).2.ne']
  have hrightXCoeff :
      ((μ : ℝ) * (μ : ℝ)) *
          (((δ : ℝ)⁻¹ : ℝ) * ((μ : ℝ) / ((μ + γ : PosReal) : ℝ))) = (μ : ℝ) := by
    calc
      ((μ : ℝ) * (μ : ℝ)) *
          (((δ : ℝ)⁻¹ : ℝ) * ((μ : ℝ) / ((μ + γ : PosReal) : ℝ)))
          = (((μ : ℝ) * (μ : ℝ)) * ((δ : ℝ)⁻¹ : ℝ)) *
              ((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) := by ring
      _ = ((μ + γ : PosReal) : ℝ) * ((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) := by
            rw [hrightCoeff]
      _ = (μ : ℝ) := by
            calc
              ((μ + γ : PosReal) : ℝ) * ((μ : ℝ) / ((μ + γ : PosReal) : ℝ))
                  = (μ : ℝ) *
                      ((((μ + γ : PosReal) : ℝ) / ((μ + γ : PosReal) : ℝ))) := by
                        ring
              _ = (μ : ℝ) := by
                    rw [div_self (μ + γ).2.ne', mul_one]
  apply smul_right_injective H hμsq
  -- Multiply both sides by `μ²` to clear every scalar denominator at once.
  have hleft :
      (((μ : ℝ) * (μ : ℝ)) : ℝ) • (((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q))
        = (μ : ℝ) • x - (γ : ℝ) • q - (μ : ℝ) • q := by
    calc
      (((μ : ℝ) * (μ : ℝ)) : ℝ) • (((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q))
          = (((μ : ℝ) * (μ : ℝ)) * ((μ : ℝ)⁻¹ : ℝ)) • x -
              (((μ : ℝ) * (μ : ℝ)) * (((μ : ℝ)⁻¹ : ℝ) * ((γ : ℝ) / (μ : ℝ))) ) • q -
              (((μ : ℝ) * (μ : ℝ)) * ((μ : ℝ)⁻¹ : ℝ)) • q := by
                simp [smul_sub, smul_smul, mul_assoc]
      _ = (μ : ℝ) • x - (γ : ℝ) • q - (μ : ℝ) • q := by
            simp [hleftCoeff, hleftDivCoeff]
  have hmiddle :
      (μ : ℝ) • x - (γ : ℝ) • q - (μ : ℝ) • q =
        (μ : ℝ) • x - ((μ + γ : PosReal) : ℝ) • q := by
    have hsum : ((μ + γ : PosReal) : ℝ) • q = (μ : ℝ) • q + (γ : ℝ) • q := by
      simpa using (add_smul (μ : ℝ) (γ : ℝ) q)
    calc
      (μ : ℝ) • x - (γ : ℝ) • q - (μ : ℝ) • q
          = (μ : ℝ) • x - ((μ : ℝ) • q + (γ : ℝ) • q) := by
              abel_nf
      _ = (μ : ℝ) • x - ((μ + γ : PosReal) : ℝ) • q := by
            rw [hsum]
  have hright :
      (((μ : ℝ) * (μ : ℝ)) : ℝ) •
          (((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q))
        = (μ : ℝ) • x - ((μ + γ : PosReal) : ℝ) • q := by
    calc
      (((μ : ℝ) * (μ : ℝ)) : ℝ) •
          (((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q))
          = (((μ : ℝ) * (μ : ℝ)) *
              (((δ : ℝ)⁻¹ : ℝ) * ((μ : ℝ) / ((μ + γ : PosReal) : ℝ)))) • x -
              (((μ : ℝ) * (μ : ℝ)) * ((δ : ℝ)⁻¹ : ℝ)) • q := by
                simp [smul_sub, smul_smul, mul_assoc]
      _ = (μ : ℝ) • x - ((μ + γ : PosReal) : ℝ) • q := by
            rw [hrightXCoeff, hrightCoeff]
  calc
    (((μ : ℝ) * (μ : ℝ)) : ℝ) • (((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q))
        = (μ : ℝ) • x - (γ : ℝ) • q - (μ : ℝ) • q := hleft
    _ = (μ : ℝ) • x - ((μ + γ : PosReal) : ℝ) • q := hmiddle
    _ = (((μ : ℝ) * (μ : ℝ)) : ℝ) •
          (((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q)) := hright.symm

/-- Proposition 23.29 (2): if `A : H → 2^H` is maximally monotone and `μ, γ ∈ ℝ_{++}`, then the
resolvent of `γ` times the scaled resolvent `μ⁻¹ J[((μ : ℝ) • A)]` is the singleton-valued map
`x ↦ x - (γ / μ) • resolventMap A hA (μ * μ * (μ + γ)⁻¹)
  ((μ / (μ + γ)) • x)`. -/
theorem resolvent_smul_inv_smul_resolvent_eq_id_sub_smul_resolventMap_comp_smul
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (μ γ : PosReal) :
    let δ : PosReal := μ * μ * (μ + γ)⁻¹
    J[((γ : ℝ) • (((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)]))] =
      (fun x : H ↦
        x - ((γ : ℝ) / (μ : ℝ)) •
          resolventMap A hA δ
            (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x)).toSetValuedOperator := by
  let δ : PosReal := μ * μ * (μ + γ)⁻¹
  ext x p
  rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  constructor
  · intro hp
    let q : H := ((μ : ℝ) / (γ : ℝ)) • (x - p)
    -- Convert the outer resolvent membership into a resolvent membership for `μ • A`.
    have hsub :
        x - p ∈ (γ : ℝ) • ((((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)]) p) :=
      (mem_resolvent_smul_iff_sub_mem_smul
        ((((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)])) γ x p).1 hp
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hsub
    have hqμ : q ∈ J[((μ : ℝ) • A)] p := by
      have hscaled :
          (μ : ℝ) • (((γ : ℝ)⁻¹ : ℝ) • (x - p)) ∈ J[((μ : ℝ) • A)] p :=
        (mem_inv_smul_resolvent_iff (A := A) μ p (((γ : ℝ)⁻¹ : ℝ) • (x - p))).1 hsub
      simpa [q, div_eq_mul_inv, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hp_eq : p = x - ((γ : ℝ) / (μ : ℝ)) • q := by
      have hscaled : ((γ : ℝ) / (μ : ℝ)) • q = x - p := by
        dsimp [q]
        rw [smul_smul]
        have hcoeff : ((γ : ℝ) / (μ : ℝ)) * ((μ : ℝ) / (γ : ℝ)) = 1 := by
          field_simp [μ.2.ne', γ.2.ne']
        simp [hcoeff]
      calc
        p = x - (x - p) := by abel_nf
        _ = x - ((γ : ℝ) / (μ : ℝ)) • q := by rw [hscaled]
    have hqμ' : q ∈ J[((μ : ℝ) • A)] (x - ((γ : ℝ) / (μ : ℝ)) • q) := by
      simpa [hp_eq] using hqμ
    have hqgraph :
        (q, ((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q)) ∈ gra A :=
      (mem_resolvent_smul_iff_mem_graph A μ
        (x - ((γ : ℝ) / (μ : ℝ)) • q) q).1 hqμ'
    have hresidual :
        ((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q) =
          ((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q) := by
      simpa [δ] using
        scaledResolventResidual_eq_normalizedResidual (μ := μ) (γ := γ) (x := x) (q := q)
    have hqδ : q ∈ J[((δ : ℝ) • A)] (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) := by
      rw [mem_resolvent_smul_iff_mem_graph]
      rw [mem_graph] at hqgraph ⊢
      simpa [hresidual] using hqgraph
    have hqeq :
        q =
          resolventMap A hA δ (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) := by
      rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA δ
        (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x)] at hqδ
      simpa using hqδ
    -- Replace the intermediate resolvent point `q` by the canonical singleton realizer.
    calc
      p = x - ((γ : ℝ) / (μ : ℝ)) • q := hp_eq
      _ =
          x - ((γ : ℝ) / (μ : ℝ)) •
            resolventMap A hA δ (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) := by
              rw [hqeq]
  · intro hp
    let q : H := resolventMap A hA δ (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x)
    -- Route correction: start from the canonical singleton realizer for `J[δ • A]`,
    -- then transport that membership back to the outer scaled resolvent.
    have hqδ : q ∈ J[((δ : ℝ) • A)] (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) := by
      rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA δ
        (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x)]
      simp [q]
    have hqgraph :
        (q, ((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q)) ∈ gra A :=
      (mem_resolvent_smul_iff_mem_graph A δ
        (((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) q).1 hqδ
    have hresidual :
        ((μ : ℝ)⁻¹ : ℝ) • ((x - ((γ : ℝ) / (μ : ℝ)) • q) - q) =
          ((δ : ℝ)⁻¹ : ℝ) • ((((μ : ℝ) / ((μ + γ : PosReal) : ℝ)) • x) - q) := by
      simpa [δ] using
        scaledResolventResidual_eq_normalizedResidual (μ := μ) (γ := γ) (x := x) (q := q)
    have hqμ :
        q ∈ J[((μ : ℝ) • A)] (x - ((γ : ℝ) / (μ : ℝ)) • q) := by
      rw [mem_resolvent_smul_iff_mem_graph]
      rw [mem_graph] at hqgraph ⊢
      simpa [hresidual] using hqgraph
    rw [hp]
    refine (mem_resolvent_smul_iff_sub_mem_smul
      ((((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)])) γ x
      (x - ((γ : ℝ) / (μ : ℝ)) • q)).2 ?_
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
    have hqscaled :
        (((μ : ℝ)⁻¹ : ℝ) • q) ∈
          (((μ : ℝ)⁻¹ : ℝ) • J[((μ : ℝ) • A)]) (x - ((γ : ℝ) / (μ : ℝ)) • q) := by
      have hqμscaled :
          (μ : ℝ) • (((μ : ℝ)⁻¹ : ℝ) • q) ∈
            J[((μ : ℝ) • A)] (x - ((γ : ℝ) / (μ : ℝ)) • q) := by
        simpa [smul_smul, μ.2.ne'] using hqμ
      exact
        (mem_inv_smul_resolvent_iff (A := A) μ
          (x - ((γ : ℝ) / (μ : ℝ)) • q) (((μ : ℝ)⁻¹ : ℝ) • q)).2 hqμscaled
    have hsub : x - (x - ((γ : ℝ) / (μ : ℝ)) • q) = ((γ : ℝ) / (μ : ℝ)) • q := by
      abel_nf
    have hcoeff :
        (((γ : ℝ)⁻¹ : ℝ) * ((γ : ℝ) / (μ : ℝ)) : ℝ) = ((μ : ℝ)⁻¹ : ℝ) := by
      field_simp [μ.2.ne', γ.2.ne']
    rw [hsub, smul_smul]
    simpa [hcoeff] using hqscaled

end SetValuedOperator
