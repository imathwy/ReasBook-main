import Mathlib
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap26.Definition_26_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Example 26.20 is the Chapter 26 owner
  `variationalInequalityProblem f (fun x ↦ ({x - z} : Set H))`.
- `core/canonical`: the Chapter 12 proximal-point owners are `IsProxPoint f z x` and
  `Prox[f, hf] z`.
- `bridge/view`: membership in this singleton-valued variational-inequality problem is equivalent
  to equality with the proximal point.

Domain-style sampling:
- `variationalInequalityProblem` and `mem_variationalInequalityProblem_iff` from
  `Definition_26_19` own the Chapter 26 variational-inequality surface.
- `isProxPoint_iff_forall_inner_add_le` from `Proposition_12_26` owns the canonical proximal
  variational inequality.
- `proximityOperator_isProxPoint` and `eq_proximityOperator_of_isProxPoint` from Chapter 12 own
  the canonical `Prox` witness and uniqueness API.

Primitive data: `f`, `z`, and the singleton-valued operator `x ↦ ({x - z} : Set H)`.
Derived API: the inner-product inequality bridge and the singleton/equality reformulations below.
-/

omit [CompleteSpace H] in
private theorem inner_sub_rev_eq_inner_sub
    (x y z : H) :
    ⟪y - x, z - x⟫_ℝ = ⟪x - y, x - z⟫_ℝ := by
  have hyx : y - x = -(x - y) := by
    abel_nf
  have hzx : z - x = -(x - z) := by
    abel_nf
  calc
    ⟪y - x, z - x⟫_ℝ = ⟪-(x - y), -(x - z)⟫_ℝ := by rw [hyx, hzx]
    _ = ⟪x - y, x - z⟫_ℝ := by
      simpa using inner_neg_neg (x - y) (x - z)

/-- Internal bridge from Proposition 12.26 to the Chapter 26 singleton-valued operator
`x ↦ ({x - z} : Set H)`. -/
private theorem eq_proximityOperator_iff_forall_inner_sub_add_le
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z x : H} :
    x = Prox[f, hf] z ↔
      ∀ y : H, (⟪x - y, x - z⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  have hunique : HasUniqueProxPoint f := hasUniqueProxPoint_of_mem_gammaZero f hf
  constructor
  · intro hx
    rw [hx]
    have hprox :=
      (isProxPoint_iff_forall_inner_add_le f hconv z (Prox[f, hf] z)).mp <|
        proximityOperator_isProxPoint f hunique z
    intro y
    simpa [inner_sub_rev_eq_inner_sub (Prox[f, hf] z) y z] using hprox y
  · intro h
    have hx_prox : IsProxPoint f z x := by
      refine (isProxPoint_iff_forall_inner_add_le f hconv z x).mpr ?_
      intro y
      simpa [inner_sub_rev_eq_inner_sub x y z] using h y
    simpa using eq_proximityOperator_of_isProxPoint f hunique hx_prox

/-- Membership in the Example 26.20 specialization of `variationalInequalityProblem` is exactly
the statement that the point equals the proximal point `Prox_f z`. -/
@[simp] theorem mem_variationalInequalityProblem_proximalPoint_iff
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {z x : H} :
    x ∈ variationalInequalityProblem f (fun y ↦ ({y - z} : Set H)) ↔
      x = Prox[f, hf] z := by
  rw [mem_variationalInequalityProblem_iff]
  constructor
  · rintro ⟨u, hu, hvar⟩
    have hu' : u = x - z := Set.mem_singleton_iff.mp hu
    have hx : ∀ y : H, (⟪x - y, x - z⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
      intro y
      simpa [hu'] using hvar y
    exact (eq_proximityOperator_iff_forall_inner_sub_add_le hf).2 hx
  · intro hx
    refine ⟨x - z, by simp, ?_⟩
    exact (eq_proximityOperator_iff_forall_inner_sub_add_le hf).1 hx

/-- Example 26.20: for `z ∈ H`, the variational inequality associated with
`B x = ({x - z} : Set H)` is the singleton consisting of the proximal point `Prox_f z`. -/
theorem variationalInequalityProblem_eq_singleton_proximityOperator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (z : H) :
    variationalInequalityProblem f (fun y ↦ ({y - z} : Set H)) =
      ({Prox[f, hf] z} : Set H) := by
  ext x
  rw [mem_variationalInequalityProblem_proximalPoint_iff hf]
  simp

end ERealFunction
