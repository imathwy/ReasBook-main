import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-- Theorem 3.2 at mathlib's canonical owner layer (stronger ambient assumptions). -/
recall Convex.add_smul

section

variable {𝕜 E : Type*} [Semifield 𝕜] [PartialOrder 𝕜]
  [AddLeftMono 𝕜] [PosMulReflectLT 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.2 states that for a convex set `C` and nonnegative scalars
  `λ₁, λ₂`, the scaled set by the sum equals the Minkowski sum of the separately scaled sets:
  `(λ₁ + λ₂) C = λ₁ C + λ₂ C`.
- `core/canonical`: the owner abstraction is the predicate `Convex 𝕜 C`; at the primitive chapter
  layer, the right owner theorem is a set-level scaling identity that only needs ordered-semifield
  scalars and additive-monoid structure on the ambient space.
- `bridge/view`: the textbook notations `λ C` and `A + B` are exactly mathlib's pointwise set
  scalar action `λ • C` and pointwise set addition `A + B`.
- Primitive data vs derived API: the convex set `C` and the scalars `λ₁`, `λ₂` are primitive.
  The proof uses `Set.add_smul_subset` for one inclusion and normalized convex-combination data
  for the reverse inclusion.
- Domain-style sampling: the chapter already fixes the owner notion in `Definition_2_0_1` by
  recalling `Convex`, and the neighboring Chapter 1 items `Theorem_3_1` and `Text_3_1_3`
  separately recall the derived owners `Convex.add` and `Convex.smul`. This item then serves as
  their canonical combination at the weaker ambient layer used by the chapter's follow-up
  specializations.
- Layer target: `core/canonical`; expose the theorem directly at this weaker owner layer.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: this is set-valued and codomain-free.
- Scalar/ambient structure stronger than needed? `No`: equality needs division by `a + b`, so the
  primitive layer is an ordered semifield action.
- Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`.
- Owner/name/notation surface canonical? `Yes`: use pointwise `•`/`+` notation and a short
  set-level owner name that distinguishes this weak-layer theorem from mathlib's stronger
  `Convex.add_smul`.
-/

/-- Theorem 3.2 at the chapter's primitive owner layer: for a convex set `C` and nonnegative
scalars `a, b`, scaling by `a + b` equals the Minkowski sum of the separately scaled sets. This
is the weak additive-monoid bridge version of `Convex.add_smul`, keeping the source-facing
identity while avoiding unnecessary additive-group assumptions on the ambient space. -/
theorem Convex.add_smul_set {C : Set E} (hC : Convex 𝕜 C) (a b : 𝕜)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) • C = a • C + b • C := by
  refine (Set.add_smul_subset _ _ _).antisymm ?_
  rintro x ⟨u, hu, v, hv, rfl⟩
  rcases Set.mem_smul_set.1 hu with ⟨x₁, hx₁, rfl⟩
  rcases Set.mem_smul_set.1 hv with ⟨x₂, hx₂, rfl⟩
  by_cases hab : a + b = 0
  · have ha_le_zero : a ≤ 0 := by
      have : a ≤ a + b := le_add_of_nonneg_right hb
      simpa [hab] using this
    have hb_le_zero : b ≤ 0 := by
      have : b ≤ b + a := le_add_of_nonneg_right ha
      simpa [add_comm, hab] using this
    have ha0 : a = 0 := le_antisymm ha_le_zero ha
    have hb0 : b = 0 := le_antisymm hb_le_zero hb
    refine Set.mem_smul_set.2 ⟨x₁, hx₁, ?_⟩
    subst ha0
    subst hb0
    simp
  · have hab_pos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    let z : E := (a / (a + b)) • x₁ + (b / (a + b)) • x₂
    have hzC : z ∈ C := by
      refine hC hx₁ hx₂ ?_ ?_ ?_
      · exact div_nonneg ha (le_of_lt hab_pos)
      · exact div_nonneg hb (le_of_lt hab_pos)
      · field_simp [hab]
    refine Set.mem_smul_set.2 ⟨z, hzC, ?_⟩
    change (a + b) • ((a / (a + b)) • x₁ + (b / (a + b)) • x₂) = a • x₁ + b • x₂
    calc
      (a + b) • ((a / (a + b)) • x₁ + (b / (a + b)) • x₂)
          = ((a + b) * (a / (a + b))) • x₁ + ((a + b) * (b / (a + b))) • x₂ := by
              simp [smul_add, mul_smul]
      _ = a • x₁ + b • x₂ := by
            field_simp [hab]

section

variable [ZeroLEOneClass 𝕜]

/-- Finite operational owner theorem derived from Theorem 3.2: for a convex set `C`, the
`(n + 1)`-fold pointwise additive sum of `C` agrees with scalar dilation by
`((n + 1 : ℕ) : 𝕜)`.

The `+ 1` indexing is intentional: at `n = 0`, both sides are exactly `C`, while a raw
`n`-indexed statement would fail at `n = 0` for empty sets because pointwise `0`-multiplication
by `𝕜` and `0`-fold additive summation of sets have different neutral elements. -/
theorem Convex.succ_nsmul_eq_natCast_smul {C : Set E} (hC : Convex 𝕜 C) (n : ℕ) :
    (n + 1 : ℕ) • C = ((n + 1 : ℕ) : 𝕜) • C := by
  have hNatNonneg : ∀ m : ℕ, (0 : 𝕜) ≤ (m : 𝕜) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        simpa [Nat.cast_add, Nat.cast_one] using
          add_nonneg hm (show (0 : 𝕜) ≤ 1 from zero_le_one)
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ((n + 1) + 1 : ℕ) • C = (n + 1 : ℕ) • C + C := by
          simp [succ_nsmul]
        _ = ((n + 1 : ℕ) : 𝕜) • C + (1 : 𝕜) • C := by
          simpa [one_smul] using congrArg (fun s : Set E => s + C) ih
        _ = (((n + 1 : ℕ) : 𝕜) + (1 : 𝕜)) • C := by
          simpa using
            (hC.add_smul_set
              ((n + 1 : ℕ) : 𝕜)
              (1 : 𝕜)
              (hNatNonneg (n + 1))
              (show (0 : 𝕜) ≤ 1 from zero_le_one)).symm
        _ = ((n + 1 + 1 : ℕ) : 𝕜) • C := by
          simp

end

end
