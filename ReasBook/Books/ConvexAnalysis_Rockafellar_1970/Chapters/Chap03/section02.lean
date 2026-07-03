import Mathlib.Algebra.Ring.Action.Pointwise.Set
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_3_2_1 (from Chap01) -/
open scoped Pointwise

section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.2.1 states that a convex set is unchanged by writing it as the
  Minkowski sum `t C + (1 - t) C` for any weight `t` with `0 ≤ t ≤ 1`.
- `core/canonical`: the primitive owner-side statement only needs nonnegative coefficients
  `a, b` with `a + b = 1`; it is exactly the equality obtained from `Set.add_smul_subset`
  and `Convex.set_combo_subset`.
- `bridge/view`: the textbook expression uses the specialization `a = t`, `b = 1 - t`.
- Primitive data vs derived API: the canonical primitive inputs are the convex set `C` and the
  coefficient pair `(a, b)` with `a + b = 1`; the `1 - t` form is a derived bridge surface.
- Domain-style sampling: this item aligns with `Convex.set_combo_subset`, `Set.add_smul_subset`,
  and `one_smul`.
- Ambient minimization: the primitive owner theorem needs only
  `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]`; subtraction appears only in the
  textbook bridge specialization.
- Layer target: keep a primitive owner theorem at the semiring layer, and expose Text 3.2.1 as a
  thin bridge corollary.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: the owner is `Convex 𝕜 C` with pointwise `•` and `+` on
  `Set E`, with no concrete codomain specialization.
- Scalar/ambient structure too strong? `No`: the primitive owner theorem is kept at
  `[Semiring 𝕜] [PartialOrder 𝕜]` and does not use subtraction.
- Concrete-model owner leak? `No`: the owner is intrinsic (`Convex`) rather than model-specific.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is algebraic/convex, not
  a closure/interior statement.
- Owner-name and parameter surface canonical? `Yes`: use a short primitive owner name aligned with
  convex-combination data, and keep the `1 - t` text form as a bridge layer.
-/

/-- Primitive owner form behind Text 3.2.1: for a convex set `C`, nonnegative coefficients adding
up to `1` give the exact pointwise-set decomposition `C = a • C + b • C`. This is the equality
counterpart of the canonical owner `Convex.set_combo_subset`. -/
theorem Convex.set_combo_eq {C : Set E} (hC : Convex 𝕜 C) (a b : 𝕜)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    C = a • C + b • C := by
  refine Set.Subset.antisymm ?_ (hC.set_combo_subset ha hb hab)
  calc
    C = (1 : 𝕜) • C := by simp
    _ = (a + b) • C := by simp [hab]
    _ ⊆ a • C + b • C := Set.add_smul_subset a b C

end

section

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-- Text 3.2.1: if `C` is convex and `t ∈ [0, 1]`, then `C` equals the Minkowski sum
`t • C + (1 - t) • C`. This is the specialization of `Convex.set_combo_eq` at
`a = t`, `b = 1 - t`, and only needs additive order monotonicity to convert `t ≤ 1`
into `0 ≤ 1 - t`. -/
theorem Convex.eq_smul_add_one_sub {C : Set E} (hC : Convex 𝕜 C) (t : 𝕜)
    (ht : t ∈ Set.Icc (0 : 𝕜) 1) :
    C = t • C + (1 - t) • C := by
  have hsum : t + (1 - t) = (1 : 𝕜) := by
    simp
  exact hC.set_combo_eq t (1 - t) ht.1 (sub_nonneg.mpr ht.2) hsum

end

/-! ### Text_3_2_2 (from Chap01) -/
open scoped Pointwise

section

variable {𝕜 E : Type*} [Semifield 𝕜] [PartialOrder 𝕜]
  [AddLeftMono 𝕜] [PosMulReflectLT 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.2.2 states that for a convex set `C`, the Minkowski sum `C + C` equals
  the dilation `2C`.
- `core/canonical`: the owner abstraction is `Convex 𝕜 C`; the primitive upstream owner theorem is
  `Convex.add_smul_set`, specialized at `a = b = 1`.
- `bridge/view`: the textbook notation `2C` is Lean's pointwise scalar action `(2 : 𝕜) • C`, and
  `C + C` is the pointwise set sum.
- Primitive data vs derived API: the primitive data are convexity of `C` plus `0 ≤ (1 : 𝕜)`.
  `ZeroLEOneClass` is then a bridge-layer packaging of that primitive scalar fact.
- Domain-style sampling: this item aligns with `Convex.add_smul_set`, the convex-set owner
  `Convex`, and standard pointwise scalar-action notation.
- Ambient minimization: no additive inverses are used in `E`, so `[AddCommMonoid E]` is enough.
- Layer target: expose a primitive theorem at the explicit `0 ≤ 1` layer, then keep Text 3.2.2 as
  a thin typeclass bridge theorem.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: this is set-valued and codomain-free.
- Scalar/ambient structure stronger than needed? `Improved`: the primitive theorem now requires
  only explicit `0 ≤ (1 : 𝕜)` instead of bundling that fact into a typeclass.
- Concrete-model owner leak? `No`: owner is intrinsic (`Convex`) and model-independent.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topological operator appears.
- Owner/name/notation surface canonical? `Yes`: the public theorem surface remains
  `C + C = (2 : 𝕜) • C` with standard pointwise notation.
-/

/-- Primitive owner form behind Text 3.2.2: convexity plus the scalar fact `0 ≤ 1` gives the
Minkowski-sum identity `C + C = (2 : 𝕜) • C`. -/
theorem Convex.add_self_eq_two_smul {C : Set E} (hC : Convex 𝕜 C)
    (h01 : (0 : 𝕜) ≤ 1) :
    C + C = (2 : 𝕜) • C := by
  simpa [one_add_one_eq_two] using
    (hC.add_smul_set (1 : 𝕜) (1 : 𝕜) h01 h01).symm

section

variable [ZeroLEOneClass 𝕜]

/-- Text 3.2.2 bridge form: for a convex set `C`, the Minkowski sum `C + C` equals `(2 : 𝕜) • C`.
This packages the primitive scalar side-condition `0 ≤ (1 : 𝕜)` via `ZeroLEOneClass`. -/
theorem Convex.add_self_eq_two_smul_of_zeroLEOneClass {C : Set E} (hC : Convex 𝕜 C) :
    C + C = (2 : 𝕜) • C := by
  exact hC.add_self_eq_two_smul (h01 := (show (0 : 𝕜) ≤ 1 from zero_le_one))

end

end

/-! ### Theorem_3_2 (from Chap01) -/
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

/-! ### Text_3_2_3 (from Chap01) -/
open scoped Pointwise

section

variable {𝕜 E : Type*} [Semifield 𝕜] [PartialOrder 𝕜]
  [AddLeftMono 𝕜] [PosMulReflectLT 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.2.3 states that for a convex set `C`, the threefold Minkowski sum
  `C + C + C` equals the dilation `3C`.
- `core/canonical`: the owner abstraction is `Convex 𝕜 C`; the primitive bridge used here is
  `Convex.add_smul_set` (specialized first at `a = b = 1`, then at `a = 2`, `b = 1`).
- `bridge/view`: the textbook notation `3C` is Lean's pointwise scalar action `(3 : 𝕜) • C`.
- Primitive data vs derived API: the primitive data are convexity of `C` and the scalar fact
  `0 ≤ (1 : 𝕜)` (from which `0 ≤ (2 : 𝕜)` is derived).
- Ambient minimization: no additive inverses are needed in `E`, and the scalar side-condition is the
  primitive fact `0 ≤ (1 : 𝕜)` rather than a bundled class assumption.
- Layer target: keep the source-facing theorem surface as a thin restatement of the canonical
  owner already exported upstream, with an explicit primitive scalar side-condition.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: this item is set-valued and codomain-free.
- Scalar/ambient structure stronger than needed? `Improved`: this file now states the primitive
  scalar hypothesis `0 ≤ (1 : 𝕜)` explicitly and provides a thin `ZeroLEOneClass` bridge theorem.
- Concrete-model owner leak? `No`: the owner remains intrinsic (`Convex`) rather than model-tied.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topological operators appear.
- Owner/name/notation surface canonical? `Yes`: use canonical pointwise `+`/`•` notation and keep a
  short owner-level theorem name.
-/

/-- Helper for Text 3.2.3: the scalar `2` is nonnegative once `0 ≤ (1 : 𝕜)`. -/
lemma zero_le_two_of_zero_le_one (h01 : (0 : 𝕜) ≤ (1 : 𝕜)) : (0 : 𝕜) ≤ (2 : 𝕜) := by
  -- Rewrite `2` as `1 + 1` so the given nonnegativity can be used twice.
  simpa [one_add_one_eq_two] using add_nonneg h01 h01

/-- Primitive owner form behind Text 3.2.3: convexity plus the scalar fact `0 ≤ (1 : 𝕜)` gives
`C + C + C = (3 : 𝕜) • C`. -/
theorem Convex.add_triple_eq_three_smul {C : Set E} (hC : Convex 𝕜 C)
    (h01 : (0 : 𝕜) ≤ 1) :
    C + C + C = (3 : 𝕜) • C := by
  -- First derive the nonnegativity needed to apply Theorem 3.2 at coefficients `2` and `1`.
  have h02 : (0 : 𝕜) ≤ (2 : 𝕜) := zero_le_two_of_zero_le_one (𝕜 := 𝕜) h01
  calc
    C + C + C = (C + C) + C := by simp [add_assoc]
    _ = (2 : 𝕜) • C + (1 : 𝕜) • C := by
      -- Collapse the first two copies of `C` by reusing Text 3.2.2.
      rw [hC.add_self_eq_two_smul h01]
      simp
    _ = ((2 : 𝕜) + (1 : 𝕜)) • C := by
      -- Apply Theorem 3.2 once more to combine `2 • C` and `1 • C`.
      simpa using (hC.add_smul_set (2 : 𝕜) (1 : 𝕜) h02 h01).symm
    _ = (((2 + 1 : ℕ) : 𝕜)) • C := by
      -- Re-express the scalar sum in numeral form before simplifying to `3`.
      simpa using congrArg (fun t : 𝕜 => t • C) (Nat.cast_add (R := 𝕜) 2 1).symm
    _ = (3 : 𝕜) • C := by simp

section

variable [ZeroLEOneClass 𝕜]

/-- Text 3.2.3 bridge form: for a convex set `C`, `C + C + C = (3 : 𝕜) • C`.
This packages the primitive scalar side-condition `0 ≤ (1 : 𝕜)` via `ZeroLEOneClass`. -/
theorem Convex.add_triple_eq_three_smul_of_zeroLEOneClass {C : Set E} (hC : Convex 𝕜 C) :
    C + C + C = (3 : 𝕜) • C := by
  -- Package the primitive theorem through the typeclass-supplied inequality `0 ≤ 1`.
  simpa using hC.add_triple_eq_three_smul (h01 := (zero_le_one : (0 : 𝕜) ≤ 1))

end

end
