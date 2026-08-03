import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall note: `lean_leansearch` did not surface these Chapter 23 resolvent/Yosida
-- identities, so the owner choice follows the local `J[...]`, `yosidaApproximation`, `gra`,
-- postfix `⁻¹`, and `comp` surfaces already established in Chapter 1 and Proposition 23.2.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 23.7: membership in `(((γ : ℝ) • id.toSetValuedOperator) + A⁻¹) u`
is equivalent to the canonical Yosida normal form `u ∈ A (x - (γ : ℝ) • u)`. -/
private theorem mem_smul_id_add_inverse_iff_mem
    (A : SetValuedOperator H H) (γ : PosReal) {x u : H} :
    x ∈ ((((γ : ℝ) • (id : H → H).toSetValuedOperator) + A⁻¹) u) ↔
      u ∈ A (x - (γ : ℝ) • u) := by
  -- Expand the pointwise sum and isolate the singleton contribution from the identity operator.
  rw [Pi.add_apply, Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, hEq⟩
    rw [Pi.smul_apply, Function.toSetValuedOperator_apply, Set.mem_smul_set] at hy
    rcases hy with ⟨v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hv
    subst v
    rw [mem_inverse_iff] at hz
    have hEq' : (γ : ℝ) • u + z = x := by
      simpa using hEq
    have hz_eq : z = x - (γ : ℝ) • u := by
      calc
        z = ((γ : ℝ) • u + z) - (γ : ℝ) • u := by
          abel_nf
        _ = x - (γ : ℝ) • u := by
          rw [hEq']
    simpa [hz_eq] using hz
  · intro hu
    refine ⟨(γ : ℝ) • u, ?_, x - (γ : ℝ) • u, ?_, ?_⟩
    · rw [Pi.smul_apply, Function.toSetValuedOperator_apply, Set.mem_smul_set]
      exact ⟨u, by simp, rfl⟩
    · rw [mem_inverse_iff]
      simpa using hu
    · abel_nf

/-- Helper for Proposition 23.7: iterating the Yosida approximation with parameters `γ` and `μ`
reduces pointwise to the single membership test `p ∈ A (x - ((γ + μ : ℝ) • p))`. -/
private theorem mem_iterated_yosidaApproximation_iff_mem_add_parameter
    (A : SetValuedOperator H H) (γ μ : PosReal) {x p : H} :
    p ∈ ({}^[γ] ({}^[μ] A)) x ↔ p ∈ A (x - ((γ + μ : ℝ) • p)) := by
  -- Normalize both Yosida layers to the same translated graph condition.
  rw [mem_yosidaApproximation_iff_mem, mem_yosidaApproximation_iff_mem]
  have hnorm :
      (x - (γ : ℝ) • p) - (μ : ℝ) • p = x - ((γ + μ : ℝ) • p) := by
    change (x - (γ : ℝ) • p) - (μ : ℝ) • p = x - (((γ : ℝ) + (μ : ℝ)) • p)
    simp [sub_eq_add_neg, add_smul, add_assoc, add_comm]
  constructor
  · intro hp
    simpa [hnorm] using hp
  · intro hp
    simpa [hnorm] using hp

/-- Helper for Proposition 23.7: membership in the affine operator
`id.toSetValuedOperator + c • (J[B] - id.toSetValuedOperator)` is equivalent to an explicit
resolvent witness `r ∈ J[B] x` with `u = x + c • (r - x)`. -/
private theorem mem_id_add_smul_resolvent_sub_id_iff
    (B : SetValuedOperator H H) (c : ℝ) {x u : H} :
    u ∈ (((id : H → H).toSetValuedOperator + c • (J[B] - (id : H → H).toSetValuedOperator)) x) ↔
      ∃ r ∈ J[B] x, u = x + c • (r - x) := by
  -- Expand the affine combination and package the subtraction witness into the resolvent point.
  rw [Pi.add_apply, Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, hEq⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hy
    subst y
    rw [Pi.smul_apply, Set.mem_smul_set] at hz
    rcases hz with ⟨w, hw, rfl⟩
    rw [Pi.sub_apply, Set.mem_sub] at hw
    rcases hw with ⟨r, hr, s, hs, hws⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hs
    subst s
    have hws' : r - x = w := by
      simpa using hws
    refine ⟨r, hr, ?_⟩
    calc
      u = x + c • w := by
            simpa using hEq.symm
      _ = x + c • (r - x) := by
            rw [← hws']
  · rintro ⟨r, hr, rfl⟩
    refine ⟨x, by simp [Function.toSetValuedOperator_apply], c • (r - x), ?_, rfl⟩
    rw [Pi.smul_apply, Set.mem_smul_set]
    refine ⟨r - x, ?_, rfl⟩
    rw [Pi.sub_apply, Set.mem_sub]
    exact ⟨r, hr, x, by simp [Function.toSetValuedOperator_apply], rfl⟩

/-- Part (i) of Proposition 23.7: the graph of `{}^[γ] A` is contained in the graph of
`A.comp J[(γ : ℝ) • A]`. -/
theorem graph_yosidaApproximation_subset_graph_comp_resolvent
    (A : SetValuedOperator H H) (γ : PosReal) :
    gra ({}^[γ] A) ⊆ gra (A.comp J[((γ : ℝ) • A)]) := by
  rintro ⟨x, u⟩ hxu
  rw [mem_graph] at hxu
  rw [mem_graph, mem_comp]
  -- The Yosida graph condition already provides the canonical resolvent witness `x - γ • u`.
  have huA : u ∈ A (x - (γ : ℝ) • u) :=
    (mem_yosidaApproximation_iff_mem A γ x u).mp hxu
  refine ⟨x - (γ : ℝ) • u, ?_, huA⟩
  -- Repackage the same witness through the resolvent characterization from Proposition 23.2.
  refine (mem_resolvent_smul_iff_sub_mem_smul A γ x (x - (γ : ℝ) • u)).2 ?_
  have hscaled : (γ : ℝ) • u ∈ (γ : ℝ) • A (x - (γ : ℝ) • u) :=
    Set.smul_mem_smul_set huA
  simpa using hscaled

/-- First equality in Proposition 23.7 (ii): `{}^[γ] A = (γ • Id + A⁻¹)⁻¹`, where `γ • Id` is the
singleton-valued operator induced by the homothety `x ↦ (γ : ℝ) • x`. -/
theorem yosidaApproximation_eq_inverse_smul_id_add_inverse
    (A : SetValuedOperator H H) (γ : PosReal) :
    {}^[γ] A =
      (((γ : ℝ) • (id : H → H).toSetValuedOperator) + A⁻¹)⁻¹ := by
  ext x u
  -- Both operators reduce to the same pointwise criterion `u ∈ A (x - γ • u)`.
  rw [mem_yosidaApproximation_iff_mem, mem_inverse_iff, mem_smul_id_add_inverse_iff_mem]

/-- Second equality in Proposition 23.7 (ii): `{}^[γ] A` is the composition of
`J[((γ : ℝ)⁻¹ • A⁻¹)]` with the singleton-valued inverse homothety
`x ↦ (γ : ℝ)⁻¹ • x`. -/
theorem yosidaApproximation_eq_resolvent_inverse_comp_inv_smul_id
    (A : SetValuedOperator H H) (γ : PosReal) :
    {}^[γ] A =
      (J[(((γ : ℝ)⁻¹) • A⁻¹)]).comp (((γ : ℝ)⁻¹) • id.toSetValuedOperator) := by
  let γinv : PosReal := ⟨(γ : ℝ)⁻¹, inv_pos.mpr γ.2⟩
  ext x u
  rw [mem_yosidaApproximation_iff_mem, mem_comp]
  constructor
  · intro hu
    -- Use the scaled source point `(γ : ℝ)⁻¹ • x` as the unique witness for the singleton-valued
    -- inverse homothety.
    refine ⟨(γ : ℝ)⁻¹ • x, ?_, ?_⟩
    · rw [Pi.smul_apply, Function.toSetValuedOperator_apply, Set.mem_smul_set]
      exact ⟨x, by simp, rfl⟩
    · -- Proposition 23.2 for `A⁻¹` with parameter `γ⁻¹` turns the target into the same normal
      -- form `u ∈ A (x - γ • u)`.
      refine (mem_resolvent_smul_iff_mem_graph A⁻¹ γinv ((γ : ℝ)⁻¹ • x) u).2 ?_
      rw [mem_graph, mem_inverse_iff]
      simpa [γinv, smul_sub, smul_smul, inv_inv, mul_inv_cancel₀ γ.2.ne', one_smul] using hu
  · rintro ⟨y, hy, hu⟩
    -- The singleton-valued witness must equal `(γ : ℝ)⁻¹ • x`, so the resolvent condition on
    -- `A⁻¹` converts back to the Yosida normal form on `A`.
    rw [Pi.smul_apply, Function.toSetValuedOperator_apply, Set.mem_smul_set] at hy
    rcases hy with ⟨x', hx', rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    have huA :
        u ∈ A (x - (γ : ℝ) • u) := by
      have huGraph :
          ((γinv : ℝ)⁻¹) • (((γ : ℝ)⁻¹) • x - u) ∈ A⁻¹ u :=
        by
          rw [← mem_graph]
          exact (mem_resolvent_smul_iff_mem_graph A⁻¹ γinv ((γ : ℝ)⁻¹ • x) u).mp hu
      rw [mem_inverse_iff] at huGraph
      simpa [γinv, smul_sub, smul_smul, inv_inv, mul_inv_cancel₀ γ.2.ne', one_smul] using huGraph
    exact huA

/-- Part (iii) of Proposition 23.7: taking the Yosida approximation with
parameter `γ + μ` agrees with first taking the `μ`-Yosida approximation and
then the `γ`-Yosida approximation. -/
theorem yosidaApproximation_add_eq_iterated_yosidaApproximation
    (A : SetValuedOperator H H) (γ μ : PosReal) :
    {}^[(γ + μ)] A = {}^[γ] ({}^[μ] A) := by
  ext x p
  -- Normalize both sides to the same translated membership condition in `A`.
  rw [mem_yosidaApproximation_iff_mem,
    mem_iterated_yosidaApproximation_iff_mem_add_parameter]
  change p ∈ A (x - (((γ : ℝ) + (μ : ℝ)) • p)) ↔
      p ∈ A (x - (((γ : ℝ) + (μ : ℝ)) • p))
  rfl

/-- Proposition 23.7 (iv): the resolvent of `γ • {}^[μ] A` is the affine
combination of `Id` and `J[((γ + μ : ℝ) • A)]` with coefficient
`(γ : ℝ) / (γ + μ : ℝ)`. -/
theorem resolvent_smul_yosidaApproximation_eq_affine_resolvent
    (A : SetValuedOperator H H) (γ μ : PosReal) :
    J[((γ : ℝ) • {}^[μ] A)] =
      id.toSetValuedOperator +
        (((γ : ℝ) / (γ + μ : ℝ)) •
          (J[((γ + μ : ℝ) • A)] - id.toSetValuedOperator)) := by
  have hκne : (γ + μ : ℝ) ≠ 0 := (γ + μ).2.ne'
  have hratio : ((γ : ℝ) / (γ + μ : ℝ)) * (γ + μ : ℝ) = (γ : ℝ) := by
    field_simp [hκne]
  ext x u
  rw [mem_id_add_smul_resolvent_sub_id_iff (B := ((γ + μ : ℝ) • A))
    (c := (γ : ℝ) / (γ + μ : ℝ))]
  constructor
  · intro hu
    -- Extract the canonical Yosida witness `p = γ⁻¹ • (x - u)` from the resolvent condition.
    have hscaled :
        (γ : ℝ)⁻¹ • (x - u) ∈ ({}^[μ] A) u := by
      have hxu : x - u ∈ (γ : ℝ) • ({}^[μ] A) u :=
        (mem_resolvent_smul_iff_sub_mem_smul ({}^[μ] A) γ x u).mp hu
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hxu
      simpa using hxu
    let p : H := (γ : ℝ)⁻¹ • (x - u)
    have hpY : p ∈ ({}^[μ] A) u := by
      simpa [p] using hscaled
    have hpA : p ∈ A (u - (μ : ℝ) • p) :=
      (mem_yosidaApproximation_iff_mem A μ u p).mp hpY
    have hxu : x - u = (γ : ℝ) • p := by
      calc
        x - u = (γ : ℝ) • ((γ : ℝ)⁻¹ • (x - u)) := by
          rw [smul_smul, mul_inv_cancel₀ γ.2.ne', one_smul]
        _ = (γ : ℝ) • p := by
          rfl
    have hu_eq : u = x - (γ : ℝ) • p := by
      calc
        u = x - (x - u) := by
              abel_nf
        _ = x - (γ : ℝ) • p := by
              rw [hxu]
    let r : H := x - ((γ + μ : ℝ) • p)
    have hr_eq : r = u - (μ : ℝ) • p := by
      calc
        r = x - ((γ + μ : ℝ) • p) := by
              rfl
        _ = x - ((γ : ℝ) • p + (μ : ℝ) • p) := by
              simp [add_smul]
        _ = (x - (γ : ℝ) • p) - (μ : ℝ) • p := by
              abel_nf
        _ = u - (μ : ℝ) • p := by
              rw [hu_eq]
    have hr : r ∈ J[((γ + μ : ℝ) • A)] x := by
      -- The same witness `p` proves that `r = x - (γ + μ) • p` lies in the resolvent of
      -- `(γ + μ) • A`.
      have hpAr : p ∈ A r := by
        simpa [hr_eq] using hpA
      refine (mem_resolvent_smul_iff_sub_mem_smul A (γ + μ) x r).2 ?_
      have hscaled' : ((γ + μ : ℝ) • p) ∈ (γ + μ : ℝ) • A r :=
        Set.smul_mem_smul_set hpAr
      simpa [r] using hscaled'
    have hscale :
        ((γ : ℝ) / (γ + μ : ℝ)) • ((γ + μ : ℝ) • p) = (γ : ℝ) • p := by
      calc
        ((γ : ℝ) / (γ + μ : ℝ)) • ((γ + μ : ℝ) • p)
            = (((γ : ℝ) / (γ + μ : ℝ)) * (γ + μ : ℝ)) • p := by
                rw [smul_smul]
        _ = (γ : ℝ) • p := by
              rw [hratio]
    refine ⟨r, hr, ?_⟩
    -- Rewrite the affine resolvent formula back to `u = x - γ • p`.
    calc
      u = x - (γ : ℝ) • p := hu_eq
      _ = x + ((γ : ℝ) / (γ + μ : ℝ)) • (r - x) := by
            calc
              x - (γ : ℝ) • p
                  = x + (-((γ : ℝ) • p)) := by
                        simp [sub_eq_add_neg]
              _ = x + ((γ : ℝ) / (γ + μ : ℝ)) •
                    (-((γ + μ : ℝ) • p)) := by
                        rw [smul_neg, hscale]
              _ = x + ((γ : ℝ) / (γ + μ : ℝ)) • (r - x) := by
                        congr 2
                        simp [r]
  · rintro ⟨r, hr, huEq⟩
    -- Recover the canonical witness `p = (γ + μ)⁻¹ • (x - r)` from the resolvent point `r`.
    let p : H := (γ + μ : ℝ)⁻¹ • (x - r)
    have hpA : p ∈ A r := by
      have hxr : x - r ∈ (γ + μ : ℝ) • A r :=
        (mem_resolvent_smul_iff_sub_mem_smul A (γ + μ) x r).mp hr
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hκne] at hxr
      simpa [p] using hxr
    have hxr : x - r = (γ + μ : ℝ) • p := by
      calc
        x - r = (γ + μ : ℝ) • ((γ + μ : ℝ)⁻¹ • (x - r)) := by
              rw [smul_smul, mul_inv_cancel₀ hκne, one_smul]
        _ = (γ + μ : ℝ) • p := by
              rfl
    have hscale :
        ((γ : ℝ) / (γ + μ : ℝ)) • ((γ + μ : ℝ) • p) = (γ : ℝ) • p := by
      calc
        ((γ : ℝ) / (γ + μ : ℝ)) • ((γ + μ : ℝ) • p)
            = (((γ : ℝ) / (γ + μ : ℝ)) * (γ + μ : ℝ)) • p := by
                rw [smul_smul]
        _ = (γ : ℝ) • p := by
              rw [hratio]
    have hu_eq : u = x - (γ : ℝ) • p := by
      calc
        u = x + ((γ : ℝ) / (γ + μ : ℝ)) • (r - x) := huEq
        _ = x + ((γ : ℝ) / (γ + μ : ℝ)) • (-(x - r)) := by
              congr 2
              abel_nf
        _ = x + ((γ : ℝ) / (γ + μ : ℝ)) • (-((γ + μ : ℝ) • p)) := by
              rw [hxr]
        _ = x - (γ : ℝ) • p := by
              rw [smul_neg, hscale]
              simp [sub_eq_add_neg]
    have hr_eq : r = u - (μ : ℝ) • p := by
      calc
        r = x - (x - r) := by
              abel_nf
        _ = x - ((γ + μ : ℝ) • p) := by
              rw [hxr]
        _ = x - ((γ : ℝ) • p + (μ : ℝ) • p) := by
              simp [add_smul]
        _ = (x - (γ : ℝ) • p) - (μ : ℝ) • p := by
              abel_nf
        _ = u - (μ : ℝ) • p := by
              rw [hu_eq]
    have hpY : p ∈ ({}^[μ] A) u := by
      refine (mem_yosidaApproximation_iff_mem A μ u p).2 ?_
      simpa [hr_eq] using hpA
    refine (mem_resolvent_smul_iff_sub_mem_smul ({}^[μ] A) γ x u).2 ?_
    have hscaled : (γ : ℝ) • p ∈ (γ : ℝ) • ({}^[μ] A) u :=
      Set.smul_mem_smul_set hpY
    have hxu : x - u = (γ : ℝ) • p := by
      calc
        x - u = x - (x - (γ : ℝ) • p) := by
              rw [hu_eq]
        _ = (γ : ℝ) • p := by
              abel_nf
    simpa [hxu] using hscaled

end SetValuedOperator
