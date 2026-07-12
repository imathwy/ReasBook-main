import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.9 introduces the cone predicate on subsets of `R^n` by closure
  under multiplication by positive real scalars.
- `core/canonical`: the chapter owner predicate for that notion is
  `Set.IsCone`, exposed canonically as pointwise positive-scalar closure
  `∀ c > 0, ∀ x ∈ K, c • x ∈ K`; on the bundled side, mathlib's owner object is
  `ConvexCone R E`.
- `bridge/view`: `ConvexCone.isCone` forgets the additive closure of a bundled convex cone and
  recovers the weaker source-facing predicate on its underlying set over the same scalar semiring.
- Primitive data vs derived API: pointwise positive-scalar closure is the primitive source-level
  content; the setwise positive-ray inclusion `({c : R | 0 < c}) • K ⊆ K` and the bundled
  `ConvexCone` view are derived bridges. There is no upstream unbundled owner in mathlib to
  replace `Set.IsCone`.
  This file should therefore keep the source predicate and only use the bundled cone as a bridge.
  Domain-style sampling used here: `Set.IsCone`, `Set.smul_set_subset_iff`, `Set.mem_smul`,
  `HasLinearPairing.pairingLinear`, `Set.mem_finset_sum` / `Set.mem_fintype_sum`, and the bundled
  bridge `ConvexCone.smul_mem`. These confirm that the source-facing cone owner remains primitive,
  while pairing-based dual-evaluation lemmas and bundled cone bridges stay derived.
- Layer target: `source-facing`; this file owns the unbundled textbook predicate, while the only
  retained derived API is the setwise positive-scalar bridge, the primitive finite-sum closure
  theorem on `Finset`s together with its `Fintype` specialization, and the bundled-to-set bridge
  theorem below.
-/

namespace Set

variable {𝕜 : Type v} {E : Type u}

section

variable (𝕜 : Type v) [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- Definition 2.5.9: a subset is a cone if it is closed under multiplication by positive
scalars. This owner is primitive in pointwise form. -/
def IsCone (K : Set E) : Prop :=
  ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ K → c • x ∈ K

end

section

variable {𝕜 : Type v} [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- Definition 2.5.9 in canonical setwise form as a bridge theorem. -/
theorem isCone_iff_pos_smul_subset (K : Set E) :
    IsCone 𝕜 K ↔ ({c : 𝕜 | 0 < c}) • K ⊆ K := by
  constructor
  · intro hK x hx
    rcases Set.mem_smul.mp hx with ⟨c, hc, y, hy, rfl⟩
    exact hK hc hy
  · intro hK c hc x hx
    exact hK (Set.mem_smul.mpr ⟨c, hc, x, hx, rfl⟩)

/-- Setwise action bridge form of Definition 2.5.9:
`K` is a cone iff each positive scalar acts invariantly on `K` as a whole set. -/
theorem isCone_iff_forall_pos_smul_subset (K : Set E) :
    IsCone 𝕜 K ↔ ∀ c : 𝕜, 0 < c → c • K ⊆ K := by
  constructor
  · intro hK c hc
    exact smul_set_subset_iff.2 (fun x hx ↦ hK hc hx)
  · intro hK c hc x hx
    exact smul_set_subset_iff.mp (hK c hc) hx

end

namespace IsCone

variable [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- A cone is closed under multiplication by each positive scalar. -/
theorem smul_mem {K : Set E} (hK : IsCone 𝕜 K) {c : 𝕜}
    (hc : 0 < c) {x : E} (hx : x ∈ K) : c • x ∈ K :=
  hK hc hx

/-- A cone is stable under each positive scalar action on its whole carrier set. -/
theorem smul_set_subset {K : Set E} (hK : IsCone 𝕜 K) {c : 𝕜}
    (hc : 0 < c) : c • K ⊆ K :=
  smul_set_subset_iff.2 (hK hc)

/-- An arbitrary intersection of cones is again a cone. -/
theorem sInter {S : Set (Set E)} (hS : ∀ s ∈ S, IsCone 𝕜 s) :
    IsCone 𝕜 (⋂₀ S) := by
  intro c hc x hx
  rw [Set.mem_sInter] at hx ⊢
  intro s hs
  exact (hS s hs) hc (hx s hs)

/-- Indexed-family form of cone intersection closure. -/
theorem iInter {ι : Sort*} {s : ι → Set E} (hs : ∀ i, IsCone 𝕜 (s i)) :
    IsCone 𝕜 (⋂ i, s i) := by
  intro c hc x hx
  rw [Set.mem_iInter] at hx ⊢
  intro i
  exact (hs i) hc (hx i)

end IsCone

section PairingLinearOrderedSemifield

open scoped Rockafellar

namespace IsCone

variable {𝕜 : Type v} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- If the pairing with `b` is bounded above on a cone by an explicit scalar bound `β`, then every
pairing value on that cone is nonpositive. This primitive owner-level theorem underlies the
`BddAbove` bridge below. -/
theorem pairing_nonpos_of_upperBound
    {K : Set X} (hK : IsCone 𝕜 K) {b : Y} {β : 𝕜}
    (hβ : ∀ x ∈ K, ⟪x, b⟫ₚ ≤ β) (x : X) (hx : x ∈ K) :
    ⟪x, b⟫ₚ ≤ (0 : 𝕜) := by
  by_contra hx_nonpos
  have hx_pos : (0 : 𝕜) < ⟪x, b⟫ₚ := lt_of_not_ge hx_nonpos
  let c : 𝕜 := max β 0 / ⟪x, b⟫ₚ + 1
  have hc : 0 < c := by
    dsimp [c]
    have h_nonneg : 0 ≤ max β 0 / ⟪x, b⟫ₚ := by
      exact div_nonneg (le_max_right β 0) (le_of_lt hx_pos)
    exact lt_of_lt_of_le (show (0 : 𝕜) < 1 by exact zero_lt_one) (le_add_of_nonneg_left h_nonneg)
  have hcx : ⟪c • x, b⟫ₚ ≤ β := hβ _ (hK.smul_mem hc hx)
  have hmul : c * ⟪x, b⟫ₚ ≤ β := by
    simpa [c] using hcx
  have hcalc : c * ⟪x, b⟫ₚ = max β 0 + ⟪x, b⟫ₚ := by
    calc
      c * ⟪x, b⟫ₚ = (max β 0 / ⟪x, b⟫ₚ + 1) * ⟪x, b⟫ₚ := by rfl
      _ = (max β 0 / ⟪x, b⟫ₚ) * ⟪x, b⟫ₚ + ⟪x, b⟫ₚ := by ring
      _ = max β 0 + ⟪x, b⟫ₚ := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hx_pos.ne', mul_one]
  have hsum_le : max β 0 + ⟪x, b⟫ₚ ≤ β := hcalc ▸ hmul
  have hβ_lt : β < max β 0 + ⟪x, b⟫ₚ :=
    lt_of_le_of_lt (le_max_left β 0) (lt_add_of_pos_right (max β 0) hx_pos)
  exact (not_le_of_gt hβ_lt) hsum_le

/-- If the pairing with `b` is bounded above on a cone, then it is nonpositive on that cone. -/
theorem pairing_nonpos_of_bddAbove {K : Set X} (hK : IsCone 𝕜 K) {b : Y}
    (hbdd : BddAbove ((fun x : X ↦ (⟪x, b⟫ₚ : 𝕜)) '' K)) (x : X) (hx : x ∈ K) :
    ⟪x, b⟫ₚ ≤ (0 : 𝕜) := by
  rcases hbdd with ⟨β, hβ⟩
  exact pairing_nonpos_of_upperBound hK (fun y hy ↦ hβ ⟨y, hy, rfl⟩) x hx

end IsCone

end PairingLinearOrderedSemifield

section PairingLinearOrderedField

open scoped Rockafellar

namespace IsCone

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any common upper bound for the pairing with `b` on a nonempty cone is nonnegative. -/
theorem pairing_upperBound_nonneg_of_nonempty {K : Set X} (hK : IsCone 𝕜 K)
    (hK_nonempty : K.Nonempty) {b : Y} {β : 𝕜} (hβ : ∀ x ∈ K, ⟪x, b⟫ₚ ≤ β) :
    (0 : 𝕜) ≤ β := by
  rcases hK_nonempty with ⟨y, hy⟩
  have hy_le : ⟪y, b⟫ₚ ≤ β := hβ y hy
  by_contra hβ_nonneg
  have hβ_neg : β < (0 : 𝕜) := lt_of_not_ge hβ_nonneg
  have hy_neg : ⟪y, b⟫ₚ < (0 : 𝕜) := lt_of_le_of_lt hy_le hβ_neg
  let c : 𝕜 := β / ((2 : 𝕜) * ⟪y, b⟫ₚ)
  have hc : 0 < c := by
    dsimp [c]
    refine div_pos_of_neg_of_neg hβ_neg ?_
    exact mul_neg_of_pos_of_neg (show (0 : 𝕜) < 2 by norm_num) hy_neg
  have hcy : ⟪c • y, b⟫ₚ ≤ β := hβ _ (hK.smul_mem hc hy)
  have hmul : c * ⟪y, b⟫ₚ ≤ β := by
    simpa using hcy
  have hcalc : (2 : 𝕜) * (c * ⟪y, b⟫ₚ) = β := by
    have htwo_ne : (2 : 𝕜) ≠ 0 := by norm_num
    have hy_ne : ⟪y, b⟫ₚ ≠ (0 : 𝕜) := hy_neg.ne
    have hden_ne : (2 : 𝕜) * ⟪y, b⟫ₚ ≠ 0 := mul_ne_zero htwo_ne hy_ne
    calc
      (2 : 𝕜) * (c * ⟪y, b⟫ₚ) = (β / ((2 : 𝕜) * ⟪y, b⟫ₚ) * ((2 : 𝕜) * ⟪y, b⟫ₚ)) := by
        dsimp [c]
        ring
      _ = β * (((2 : 𝕜) * ⟪y, b⟫ₚ)⁻¹ * ((2 : 𝕜) * ⟪y, b⟫ₚ)) := by
        rw [div_eq_mul_inv]
        ring
      _ = β := by rw [inv_mul_cancel₀ hden_ne, mul_one]
  have hβ_le_twoβ : β ≤ (2 : 𝕜) * β := by
    nlinarith [hmul, hcalc]
  have hβ_nonneg' : (0 : 𝕜) ≤ β := by nlinarith [hβ_le_twoβ]
  exact (not_le_of_gt hβ_neg) hβ_nonneg'

end IsCone

end PairingLinearOrderedField

namespace IsCone

variable [LT 𝕜] [Zero 𝕜] [AddCommMonoid E] [DistribSMul 𝕜 E]
variable {ι : Type*}

/-- A finite Minkowski sum of cones is again a cone. This is the primitive operational finite-sum
API; the `Fintype`-indexed theorem below is its `Finset.univ` specialization. -/
theorem finset_sum {s : Finset ι} {K : ι → Set E} (hK : ∀ i, i ∈ s → IsCone 𝕜 (K i)) :
    IsCone 𝕜 (∑ i ∈ s, K i) := by
  intro c hc x hx
  rw [Set.mem_finset_sum] at hx ⊢
  rcases hx with ⟨g, hg, rfl⟩
  exact ⟨fun i ↦ c • g i, fun {i} hi ↦ (hK i hi) hc (hg hi), by
    simpa using
      (show ∑ i ∈ s, c • g i = c • ∑ i ∈ s, g i from Finset.smul_sum.symm)⟩

variable [Fintype ι]

/-- A finite Minkowski sum of cones is again a cone. -/
theorem fintype_sum {K : ι → Set E} (hK : ∀ i, IsCone 𝕜 (K i)) :
    IsCone 𝕜 (∑ i, K i) := by
  simpa using
    (finset_sum (fun i _ ↦ hK i) : IsCone 𝕜 (∑ i ∈ (Finset.univ : Finset ι), K i))

end IsCone

end Set

namespace ConvexCone

variable {R : Type v} {E : Type u} [Semiring R] [PartialOrder R] [AddCommMonoid E] [SMul R E]

/-- Every bundled convex cone is a cone in the sense of Definition 2.5.9 after forgetting additive
closure. -/
theorem isCone (C : ConvexCone R E) : Set.IsCone R (C : Set E) := by
  intro c hc x hx
  exact C.smul_mem hc hx

end ConvexCone
