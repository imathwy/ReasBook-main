import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_5
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_7

open scoped Rockafellar SetRel

universe u v w

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Sub X] [Sub Y] [HasPairing X Y 𝕜]
variable [AddCommGroup 𝕜] [LE 𝕜] [AddRightMono 𝕜]
variable [HasPairingSubLeft X Y 𝕜] [HasPairingSubRight X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.4 says that cyclic monotonicity implies ordinary
  monotonicity for a multivalued mapping.
- `core/canonical`: this chapter already owns cyclic monotonicity and monotonicity as the relation
  predicates `SetRel.CyclicallyMonotone` and `SetRel.Monotone` on `ρ : SetRel X Y`, with the
  pairing codomain explicit in the owner parameter and surfaced via the chapter notation
  `CMon[𝕜](ρ)` and `Mon[𝕜](ρ)`.
- `bridge/view`: Proposition 5.24.4 is the owner-level implication from the stronger cyclic
  relation predicate to the weaker monotone one; strong-dual relation views are just later
  specialization of this canonical statement.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_5.lean`;
- `SetRel.Monotone` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_7.lean`;
- subtraction-compatible pairing owners `HasPairingSubLeft` and `HasPairingSubRight` from
  `ConvexAnalysis_Rockafellar_1970/Chap01/HasPairing.lean`, the primitive algebraic layer
  for the source cycle-to-monotonicity rewrite.

Primitive data vs derived API:
- primitive hypothesis: `CMon[𝕜](ρ)`;
- primitive ambient owner data used by the core theorem: subtraction-compatible pairing owners in
  the left and right arguments;
- derived conclusion: `Mon[𝕜](ρ)`.

Layer target: `core/canonical`. This item is the direct canonical implication between the chapter's
two owner predicates on relations.
-/

namespace SetRel.CyclicallyMonotone

-- Proof sketch: specialize cyclic monotonicity to a cycle of length `2`, obtaining
-- `⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ ≤ 0`. Rewriting with subtraction-compatible pairing identities
-- gives `-(⟪x₁ - x₀, y₁ - y₀⟫ₚ) ≤ 0`, hence monotonicity.
/-- Proposition 5.24.4 at the canonical owner layer: cyclic monotonicity implies monotonicity
whenever the pairing is subtraction-compatible in each argument. -/
theorem monotone {ρ : SetRel X Y} (hρ : CMon[𝕜](ρ)) :
    Mon[𝕜](ρ) := by
  refine ⟨?_⟩
  intro x₀ x₁ y₀ y₁ hx₀ hx₁
  have hsum : (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜) ≤ 0 := by
    simpa [Fin.sum_univ_two] using
      hρ.sum_nonpos 1 ![x₀, x₁] ![y₀, y₁] (by
        intro i
        fin_cases i
        · simpa using hx₀
        · simpa using hx₁)
  have hrewrite :
      (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜) =
        -(⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) := by
    calc
      (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜)
          = (⟪x₁, y₀⟫ₚ - ⟪x₀, y₀⟫ₚ) + (⟪x₀, y₁⟫ₚ - ⟪x₁, y₁⟫ₚ) := by
              rw [HasPairingSubLeft.pairing_sub_left x₁ x₀ y₀,
                HasPairingSubLeft.pairing_sub_left x₀ x₁ y₁]
      _ = -((⟪x₁, y₁⟫ₚ - ⟪x₀, y₁⟫ₚ) - (⟪x₁, y₀⟫ₚ - ⟪x₀, y₀⟫ₚ)) := by
            abel
      _ = -((⟪x₁ - x₀, y₁⟫ₚ : 𝕜) - ⟪x₁ - x₀, y₀⟫ₚ) := by
            rw [HasPairingSubLeft.pairing_sub_left x₁ x₀ y₁,
              HasPairingSubLeft.pairing_sub_left x₁ x₀ y₀]
      _ = -(⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) := by
            rw [← HasPairingSubRight.pairing_sub_right (x₁ - x₀) y₁ y₀]
  have hsub : (0 : 𝕜) - (⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) ≤ 0 := by
    simpa [hrewrite] using hsum
  exact sub_nonpos.mp hsub

/-- Canonical owner bridge: cyclic monotonicity implies monotonicity. This instance lets
downstream declarations use `Mon[𝕜](ρ)` via typeclass inference whenever
`[CMon[𝕜](ρ)]` is available. -/
instance toMonotone (ρ : SetRel X Y) [hρ : CMon[𝕜](ρ)] : Mon[𝕜](ρ) :=
  monotone hρ

end SetRel.CyclicallyMonotone

end
