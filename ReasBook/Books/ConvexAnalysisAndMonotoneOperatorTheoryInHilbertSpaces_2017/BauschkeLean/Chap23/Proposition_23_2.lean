import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap01.Text_1_0_17

-- Semantic recall note: `lean_leansearch` did not surface the Chapter 23 set-valued resolvent or
-- Yosida API, so the owner choice here follows the local `J[...]`, `yosidaApproximation`, `dom`,
-- `range`, and `gra` surfaces from Chapter 1 and Definition 23.1.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

private theorem dom_smul (a : ℝ) (A : SetValuedOperator H H) :
    dom (a • A) = dom A := by
  ext x
  rw [mem_dom_iff, mem_dom_iff, Pi.smul_apply, Set.smul_set_nonempty]

omit [AddCommGroup H] [Module ℝ H] in
private theorem dom_toSetValuedOperator (T : H → H) :
    dom T.toSetValuedOperator = Set.univ := by
  ext x
  rw [mem_dom_iff, Function.toSetValuedOperator_apply]
  simp

omit [Module ℝ H] in
private theorem dom_sub (A B : SetValuedOperator H H) :
    dom (A - B) = dom A ∩ dom B := by
  ext x
  rw [Set.mem_inter_iff, mem_dom_iff, mem_dom_iff, mem_dom_iff, Pi.sub_apply, sub_eq_add_neg,
    Set.add_nonempty]
  constructor
  · rintro ⟨hA, hnegB⟩
    rcases hnegB with ⟨y, hy⟩
    exact ⟨hA, ⟨-y, by simpa using hy⟩⟩
  · rintro ⟨hA, hB⟩
    rcases hB with ⟨y, hy⟩
    exact ⟨hA, ⟨-y, by simpa using hy⟩⟩

/-- Proposition 23.2 (1): the domain of the resolvent of `γ • A` agrees with the domain of the
Yosida approximation of `A` with index `γ`. -/
theorem dom_resolvent_smul_eq_dom_yosidaApproximation
    (A : SetValuedOperator H H) (γ : PosReal) :
    dom (J[((γ : ℝ) • A)]) = dom ({}^[γ] A) := by
  calc
    dom (J[((γ : ℝ) • A)]) = range ((id : H → H).toSetValuedOperator + (γ : ℝ) • A) := by
      simp [resolvent_def]
    _ = dom ({}^[γ] A) := by
      symm
      calc
        dom ({}^[γ] A) = dom ((id : H → H).toSetValuedOperator - J[((γ : ℝ) • A)]) := by
          rw [yosidaApproximation, dom_smul]
        _ = dom (J[((γ : ℝ) • A)]) := by
          rw [dom_sub, dom_toSetValuedOperator, Set.univ_inter]
        _ = range ((id : H → H).toSetValuedOperator + (γ : ℝ) • A) := by
          simp [resolvent_def]

/-- Proposition 23.2 (2): the common domain of `J[γ • A]` and `{}^[γ] A` is the
range of `Id + γ • A`, realized as `(id.toSetValuedOperator + (γ : ℝ) • A).range`. -/
theorem dom_yosidaApproximation_eq_range_id_add_smul
    (A : SetValuedOperator H H) (γ : PosReal) :
    dom ({}^[γ] A) =
      range (id.toSetValuedOperator + (γ : ℝ) • A) := by
  calc
    dom ({}^[γ] A) = dom ((id : H → H).toSetValuedOperator - J[((γ : ℝ) • A)]) := by
      rw [yosidaApproximation, dom_smul]
    _ = dom (J[((γ : ℝ) • A)]) := by
      rw [dom_sub, dom_toSetValuedOperator, Set.univ_inter]
    _ = range ((id : H → H).toSetValuedOperator + (γ : ℝ) • A) := by
      simp [resolvent_def]

/-- Proposition 23.2 (3): the range of the resolvent of `γ • A` is the domain of `A`. -/
theorem range_resolvent_smul_eq_dom
    (A : SetValuedOperator H H) (γ : PosReal) :
    range (J[((γ : ℝ) • A)]) = dom A := by
  calc
    range (J[((γ : ℝ) • A)]) = dom ((id : H → H).toSetValuedOperator + (γ : ℝ) • A) := by
      simp [resolvent_def]
    _ = dom (id.toSetValuedOperator : SetValuedOperator H H) ∩ dom A := by
      exact dom_add_smul (id.toSetValuedOperator : SetValuedOperator H H) A (γ : ℝ)
    _ = dom A := by
      rw [dom_toSetValuedOperator, Set.univ_inter]

/-- Proposition 23.2 (4): a point `p` belongs to the resolvent value `J[γ • A] x` exactly when
`x` belongs to the translated value set `p + γ • A p`. -/
theorem mem_resolvent_smul_iff_mem_singleton_add_smul
    (A : SetValuedOperator H H) (γ : PosReal) (x p : H) :
    p ∈ J[((γ : ℝ) • A)] x ↔ x ∈ ({p} : Set H) + (γ : ℝ) • A p := by
  rw [resolvent_def, mem_inverse_iff]
  change x ∈ ((id : H → H).toSetValuedOperator p + (γ : ℝ) • A p) ↔
      x ∈ ({p} : Set H) + (γ : ℝ) • A p
  simp [Function.toSetValuedOperator_apply]

/-- Proposition 23.2 (5): a point `p` belongs to `J[γ • A] x` exactly when the residual
`x - p` belongs to `γ • A p`. -/
theorem mem_resolvent_smul_iff_sub_mem_smul
    (A : SetValuedOperator H H) (γ : PosReal) (x p : H) :
    p ∈ J[((γ : ℝ) • A)] x ↔ x - p ∈ (γ : ℝ) • A p := by
  rw [mem_resolvent_smul_iff_mem_singleton_add_smul, Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hxz : x - p = z := by
      calc
        x - p = (p + z) - p := by rw [← hyz]
        _ = z := by abel_nf
    simpa [hxz] using hz
  · intro hx
    refine ⟨p, by simp, x - p, hx, ?_⟩
    abel_nf

/-- Proposition 23.2 (6): a point `p` belongs to `J[γ • A] x` exactly when the pair
`(p, (γ : ℝ)⁻¹ • (x - p))` lies in `gra A`. -/
theorem mem_resolvent_smul_iff_mem_graph
    (A : SetValuedOperator H H) (γ : PosReal) (x p : H) :
    p ∈ J[((γ : ℝ) • A)] x ↔ (p, (γ : ℝ)⁻¹ • (x - p)) ∈ gra A := by
  rw [mem_resolvent_smul_iff_sub_mem_smul, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne',
    mem_graph]

/-- Proposition 23.2 (7): a point `p` belongs to the Yosida value `({}^[γ] A) x`
exactly when `p ∈ A (x - γ • p)`. -/
theorem mem_yosidaApproximation_iff_mem
    (A : SetValuedOperator H H) (γ : PosReal) (x p : H) :
    p ∈ ({}^[γ] A) x ↔ p ∈ A (x - (γ : ℝ) • p) := by
  rw [yosidaApproximation_apply,
    Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero γ.2.ne')]
  rw [inv_inv]
  change (γ : ℝ) • p ∈ ({x} : Set H) - J[((γ : ℝ) • A)] x ↔
      p ∈ A (x - (γ : ℝ) • p)
  rw [Set.mem_sub]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hz_eq : z = x - (γ : ℝ) • p := by
      calc
        z = x - (x - z) := by abel_nf
        _ = x - (γ : ℝ) • p := by rw [hyz]
    have hz_res : x - (γ : ℝ) • p ∈ J[((γ : ℝ) • A)] x := by
      simpa [hz_eq] using hz
    have hscaled :
        x - (x - (γ : ℝ) • p) ∈ (γ : ℝ) • A (x - (γ : ℝ) • p) :=
      (mem_resolvent_smul_iff_sub_mem_smul A γ x (x - (γ : ℝ) • p)).mp hz_res
    have hscaled' : (γ : ℝ) • p ∈ (γ : ℝ) • A (x - (γ : ℝ) • p) := by
      simpa using hscaled
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hscaled'
    simpa [smul_smul, inv_mul_cancel₀ γ.2.ne'] using hscaled'
  · intro hp
    have hscaled : (γ : ℝ) • p ∈ (γ : ℝ) • A (x - (γ : ℝ) • p) :=
      Set.smul_mem_smul_set hp
    have hz_res : x - (γ : ℝ) • p ∈ J[((γ : ℝ) • A)] x := by
      refine (mem_resolvent_smul_iff_sub_mem_smul A γ x (x - (γ : ℝ) • p)).2 ?_
      simpa using hscaled
    refine ⟨x, by simp, x - (γ : ℝ) • p, hz_res, ?_⟩
    abel_nf

/-- Proposition 23.2 (8): a point `p` belongs to `({}^[γ] A) x` exactly when the
pair `(x - γ • p, p)` lies in `gra A`. -/
theorem mem_yosidaApproximation_iff_mem_graph
    (A : SetValuedOperator H H) (γ : PosReal) (x p : H) :
    p ∈ ({}^[γ] A) x ↔ (x - (γ : ℝ) • p, p) ∈ gra A := by
  rw [mem_yosidaApproximation_iff_mem, mem_graph]

end SetValuedOperator
