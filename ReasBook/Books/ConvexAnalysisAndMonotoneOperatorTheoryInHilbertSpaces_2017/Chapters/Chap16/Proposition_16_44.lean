import Mathlib
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 16 44: membership in `Id + ∂ f` at `p` is exactly the residual
subgradient inclusion `x - p ∈ ∂ f(p)`. -/
private theorem mem_id_add_subdifferential_iff_sub_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (x p : H) :
    x ∈ ((id : H → H).toSetValuedOperator + ∂ f) p ↔ x - p ∈ (∂ f) p := by
  constructor
  · intro hx
    rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
    subst u
    have hsub : x - p = v := by
      rw [sub_eq_iff_eq_add]
      simpa [add_comm] using huv.symm
    simpa [hsub] using hv
  · intro hx
    have hid_mem : p ∈ (id : H → H).toSetValuedOperator p := by
      simp [Function.toSetValuedOperator_apply]
    have hdecomp : p + (x - p) = x := by
      abel_nf
    exact Set.mem_add.2 ⟨p, hid_mem, x - p, hx, hdecomp⟩

-- Proof sketch: rewrite `p = Prox_f x` as `IsProxPoint f x p` via the Chapter 12 owner theorem
-- `eq_proximityOperator_of_isProxPoint`, then apply Proposition 12.26 and Definition 16.1.
/-- Proposition 16 44: for `f ∈ Γ₀(H)` and `x, p ∈ H`, the point `p` equals `Prox_f x` exactly
when the residual `x - p` belongs to the subdifferential of `f` at `p`. -/
theorem eq_proximityOperator_iff_sub_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x p : H) :
    p = Prox[f, hf] x ↔
      x - p ∈ (∂ f) p := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  constructor
  · intro hp
    have hp_prox : IsProxPoint f x p := by
      rw [hp]
      simpa using
        proximityOperator_isProxPoint f
          (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) x
    rw [mem_subdifferential_iff]
    exact (isProxPoint_iff_forall_inner_add_le f hconv x p).mp hp_prox
  · intro hp
    rw [mem_subdifferential_iff] at hp
    have hp_prox : IsProxPoint f x p :=
      (isProxPoint_iff_forall_inner_add_le f hconv x p).mpr hp
    simpa using
      eq_proximityOperator_of_isProxPoint f
        (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) hp_prox

-- Proof sketch: extensionality on `x` and set extensionality on `p` reduce the operator identity
-- to the pointwise equivalence above and the singleton description of `id.toSetValuedOperator`.
/-- The proximity operator of a `Γ₀(H)` function is the inverse of the set-valued operator
`id.toSetValuedOperator + ∂ f`, which is the textbook formula `Prox_f = (Id + ∂ f)⁻¹`
written through the canonical singleton-valued operator owner. -/
theorem singleton_proximityOperator_eq_inverse_add_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Prox[f, hf].toSetValuedOperator = ((id : H → H).toSetValuedOperator + ∂ f).inverse := by
  funext x
  ext p
  constructor
  · intro hp
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hp
    rw [SetValuedOperator.mem_inverse_iff]
    exact (mem_id_add_subdifferential_iff_sub_mem_subdifferential (f := f) x p).2 <|
      (eq_proximityOperator_iff_sub_mem_subdifferential hf x p).1 hp
  · intro hp
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    rw [SetValuedOperator.mem_inverse_iff] at hp
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hf x p).2 <|
      (mem_id_add_subdifferential_iff_sub_mem_subdifferential (f := f) x p).1 hp

end SubdifferentialCalculus

end ERealFunction
