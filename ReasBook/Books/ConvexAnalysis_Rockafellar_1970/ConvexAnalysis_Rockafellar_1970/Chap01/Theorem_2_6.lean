import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 2.6 characterizes convex cones by closure under addition together with
  closure under positive scalar multiplication. The primitive source-facing owner is the cone
  predicate `Set.IsCone R K`; once that is fixed, convexity is exactly additive closure.
- `core/canonical`: convexity itself is read through the canonical criterion
  `convex_iff_add_mem`; no module-only convexity criterion is needed for this item.
  no bundled-cone wrapper is needed in this item.
- `bridge/view`: the reverse direction is the direct cone-plus-convex-combination argument:
  positive-scalar closure from `Set.IsCone` plus pointwise additive closure yields convexity; the
  set-level bridge `K + K ⊆ K` is then a derived restatement.
- Primitive data vs derived API: the primitive source data are `Set.IsCone R K` and pointwise
  additive closure; `K + K ⊆ K` and convexity are derived API.
- Domain-style sampling used here: `Set.IsCone`, `Set.IsCone.smul_mem`, `Set.add_mem_add`,
  `convex_iff_add_mem`, and `add_halves`.
- Layer target: `source-facing`.
-/

/- Definition 2.5.9: the source-facing cone predicate used in Theorem 2.6 is the chapter owner
`Set.IsCone R`. -/
section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

#check (Set.IsCone R : Set E → Prop)

end

namespace Set.IsCone

section WeakLayer

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

/-- Weak-layer constructor: in a cone, pointwise additive closure implies convexity. -/
theorem convex_of_add_mem {K : Set E} (hcone : Set.IsCone R K)
    (hadd : ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K) :
    Convex R K := by
  refine convex_iff_add_mem.2 ?_
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by simpa [ha0] using hab
    simpa [ha0, hb1] using hy
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      simpa [hb0, ha1] using hx
    · have ha_pos : (0 : R) < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : (0 : R) < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact hadd (hcone.smul_mem ha_pos hx) (hcone.smul_mem hb_pos hy)

/-- Weak-layer set form: in a cone, closure under pointwise set addition implies convexity. -/
theorem convex_of_add_subset {K : Set E} (hcone : Set.IsCone R K)
    (hadd : K + K ⊆ K) :
    Convex R K := by
  refine hcone.convex_of_add_mem ?_
  intro x y hx hy
  exact hadd (Set.add_mem_add hx hy)

end WeakLayer

section DivisionWeakLayer

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R]
variable [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [DistribMulAction R E]

/-- Division-layer constructor: in a cone, convexity implies closure under pointwise addition. -/
theorem add_mem_of_convex {K : Set E} (hcone : Set.IsCone R K)
    (hconv : Convex R K) :
    ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K := by
  intro x y hx hy
  have htwo_pos : (0 : R) < 2 := by
    exact (zero_lt_two : (0 : R) < 2)
  have htwo_ne : (2 : R) ≠ 0 := htwo_pos.ne'
  letI : NeZero (2 : R) := ⟨htwo_ne⟩
  have hhalf_nonneg : (0 : R) ≤ (1 / 2 : R) := by
    exact one_div_nonneg.2 (le_of_lt htwo_pos)
  have hxy : (1 / 2 : R) • x + (1 / 2 : R) • y ∈ K :=
    (convex_iff_add_mem.mp hconv) hx hy hhalf_nonneg hhalf_nonneg (add_halves 1)
  have hsum : (2 : R) • ((1 / 2 : R) • x + (1 / 2 : R) • y) ∈ K :=
    hcone.smul_mem htwo_pos hxy
  have htwo_inv : (2 : R) * (2 : R)⁻¹ = 1 := mul_inv_cancel₀ htwo_ne
  simpa [one_div, smul_add, smul_smul, htwo_inv] using hsum

/-- Division-layer set form: in a cone, convexity implies closure under pointwise set addition. -/
theorem add_subset_of_convex {K : Set E} (hcone : Set.IsCone R K)
    (hconv : Convex R K) :
    K + K ⊆ K := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact hcone.add_mem_of_convex hconv hx hy

end DivisionWeakLayer

section DivisionModuleLayer

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R]
variable [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Theorem 2.6: a cone in a module over a partially ordered division semiring is convex if and
only if it is closed under addition. -/
theorem convex_iff_add_mem {K : Set E} (hcone : Set.IsCone R K) :
    Convex R K ↔ ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K := by
  constructor
  · intro hconv
    exact hcone.add_mem_of_convex hconv
  · intro hadd
    exact hcone.convex_of_add_mem hadd

/-- Set-level bridge for Theorem 2.6: in a cone, convexity is equivalent to closure of `K` under
pointwise set addition. -/
theorem convex_iff_add_subset {K : Set E} (hcone : Set.IsCone R K) :
    Convex R K ↔ K + K ⊆ K := by
  constructor
  · intro hconv
    exact hcone.add_subset_of_convex hconv
  · intro hadd
    exact hcone.convex_of_add_subset hadd

end DivisionModuleLayer

end Set.IsCone
