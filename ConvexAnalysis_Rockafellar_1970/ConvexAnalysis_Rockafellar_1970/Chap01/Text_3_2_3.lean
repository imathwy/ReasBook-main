import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_2_2

-- Declarations for this item will be appended below by the statement pipeline.

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
