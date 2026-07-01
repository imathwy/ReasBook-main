import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.3 states Rockafellar's concave biconjugacy identity
  `g** = cl g` for a concave function.
- `core/canonical`: the relevant owners already present in the project are `concaveConjugate` for
  the concave conjugate and `concaveClosure` for the closure from Definition 6.30.2.
- `bridge/view`: the theorem is the sign-dual transport of convex biconjugacy for `-g`; it should
  therefore be stated directly as an equality between those two existing owners, not through a new
  wrapper.

Primary mathematical domain:
- convex/concave duality on `WithBotTop 𝕜`-valued functions over finite-dimensional paired spaces.

Domain-style sampling used here:
- `concaveConjugate`;
- `concaveClosure`;
- `Function.IsConcave.convex_neg`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.

Primitive data vs derived API:
- primitive input: a concave function `g : E → WithBotTop 𝕜`;
- primitive owners already available: `concaveConjugate g` and `concaveClosure g`;
- derived API added here: the biconjugacy bridge identifying the concave biconjugate with the
  concave closure.

Layer target: `bridge/view`. The source theorem is not introducing a new owner; it relates the
existing Chapter 6 conjugate and closure owners. The source statement is lifted to the canonical
finite-dimensional scalar-parametric self-pairing layer already used by the convex-side
biconjugacy theorem.
-/

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

local notation:max g "∗∗" => (concaveConjugate (Y := E) g)∗

namespace Function.IsConcave

-- Proof sketch: apply the sign-duality formula from Theorem 6.30.4 twice to rewrite the concave
-- biconjugate of `g` as the negative of the convex biconjugate of `-g`. Since `hg` gives convexity
-- of `-g`, Theorem 12.2 identifies that convex biconjugate with `cl(-g)`, and unfolding
-- `concaveClosure` turns the result into the desired equality.
/-- Theorem 6.30.3: on a finite-dimensional space with a continuous linear self-pairing, the
concave biconjugate of a concave function equals its concave closure, at the finite-dimensional
scalar-parametric self-pairing layer. Here `concaveClosure g` is the closure from Definition 6.30.2,
namely the pointwise infimum of the affine majorants of `g`. -/
theorem biconjugate_eq_concaveClosure
    {g : E → WithBotTop 𝕜} (hg : g.IsConcave 𝕜) :
    g∗∗ = concaveClosure g := by
  ext x
  rw [concaveConjugate_eq_neg_convexConjugate_neg_apply
        (g := concaveConjugate (Y := E) g) (y := x)]
  have hneg_gStar :
      (-g∗) = fun y : E ↦ ((-g)⋆ : E → WithBotTop 𝕜) (-y) := by
    funext y
    simpa using
      congrArg Neg.neg (concaveConjugate_eq_neg_convexConjugate_neg_apply (g := g) (y := y))
  rw [hneg_gStar]
  have hpair_neg_left : ∀ y z : E, (⟪-y, z⟫ₚ : 𝕜) = -⟪y, z⟫ₚ := by
    intro y z
    change (HasLinearPairing.pairingLinear (-y)) z = -((HasLinearPairing.pairingLinear y) z)
    exact congrArg (fun φ : Module.Dual 𝕜 E => φ z)
      (LinearMap.map_neg (HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E) y)
  have hbiconj_neg :
      (((fun y : E ↦ ((-g)⋆ : E → WithBotTop 𝕜) (-y))⋆ : E → WithBotTop 𝕜) (-x)) =
        ((-g)⋆⋆ : E → WithBotTop 𝕜) x := by
    rw [convexConjugate_eq_iSup_pairing_sub, convexBiconjugate_eq_iSup_pairing_sub]
    calc
      (⨆ y : E, (⟪y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) (-y)))
          = ⨆ y : E, (⟪-y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y) := by
              simpa using
                (Equiv.iSup_comp (e := Equiv.neg E)
                  (g := fun y : E ↦
                    (⟪-y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y)))
      _ = ⨆ y : E, (⟪y, x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y) := by
            refine iSup_congr ?_
            intro y
            have hpair : (⟪-y, -x⟫ₚ : 𝕜) = ⟪y, x⟫ₚ := by
              calc
                (⟪-y, -x⟫ₚ : 𝕜) = -⟪-y, x⟫ₚ := HasPairingNegRight.pairing_neg_right (-y) x
                _ = -(-⟪y, x⟫ₚ) := by rw [hpair_neg_left y x]
                _ = ⟪y, x⟫ₚ := by simp
            change (((⟪-y, -x⟫ₚ : 𝕜) : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y)) =
              (((⟪y, x⟫ₚ : 𝕜) : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y))
            rw [hpair]
  rw [hbiconj_neg]
  rw [hg.convex_neg.biconjugate_eq_lowerSemicontinuousHull]
  rfl

end Function.IsConcave

end
