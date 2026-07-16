import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_14
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.5 identifies the biconjugate of the indicator of a convex set with
  the closure of that indicator, and then identifies that closure with the indicator of the set
  closure.
- `core/canonical`: the owner declarations already present in the project are
  `indicatorFunction`, `supportFunction`, `convexConjugate`, and
  `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `δ^*(· | C)` is the support function `supportFunction C`, while the
  closure `cl δ(· | C)` is represented by `lowerSemicontinuousHull (indicatorFunction C)`.
- `primitive data`: a set `C : Set E`; the convexity hypothesis `Convex 𝕜 C` is needed only for
  the biconjugacy clause, not for the closure-of-indicator clause.
- `derived API`: the owner-level closure theorem
  `lowerSemicontinuousHull (indicatorFunction C) = indicatorFunction (closure C)` (reused from
  Text 7.0.14 as `lowerSemicontinuousHull_indicator_eq_indicator_closure`) and its
  source-facing biconjugacy owner
  `convexConjugate (supportFunction C) = lowerSemicontinuousHull (indicatorFunction C)`, with
  the indicator-of-closure statement kept as a bridge corollary.

Domain-style sampling used here:
- `indicatorFunction`;
- `le_lowerSemicontinuousHull`;
- `LowerSemicontinuous.isClosed_preimage`;
- `convexConjugate_indicatorFunction_eq_supportFunction`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- `lowerSemicontinuousHull`.

Layer target:
- `bridge/view` for the closure theorem from Text 7.0.14
  `lowerSemicontinuousHull (indicatorFunction C) = indicatorFunction (closure C)`, which belongs
  at the generic lower-semicontinuity owner level of a topological space;
- `source-facing` for the support-function biconjugacy clauses, which reuse the chapter Fenchel
  owners on the finite-dimensional scalar-field pairing ambient where Theorem 12.2 lives.
-/

section

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
  [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
  [HasPairingSwap E E 𝕜]

-- Proof sketch: combine the chapter indicator/support bridge with biconjugacy at the pairing
-- level. The pairing-swap owner identifies the support-function conjugate with the indicator
-- biconjugate, and then Theorem 12.2 identifies that biconjugate with the closure owner
-- `cl(δ(· | C))`.
/-- Pairing-swap owner form of Text 13.1.5: on a finite-dimensional scalar-field space with a
continuous linear self-pairing, the conjugate of the support function of a convex set is the
closure `cl(δ(· | C))` of its indicator. -/
theorem convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator
    (C : Set E) (hC : Convex 𝕜 C) :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = cl((δ[𝕜](· | C))) := by
  change convexConjugate (supportFunction C : E → WithBotTop 𝕜) = cl((δ[𝕜](· | C)))
  have hsupport :
      convexConjugate (supportFunction C : E → WithBotTop 𝕜) =
        convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) := by
    simpa [convexBiconjugate] using
      congrArg (convexConjugate (X := E) (Y := E) (L := WithBotTop 𝕜))
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := E) (EStar := E) (α := 𝕜) C).symm
  have hbiconj :
      convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) =
        lowerSemicontinuousHull (δ[𝕜](· | C)) := by
    simpa using
      (((indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) C).2 hC).biconjugate_eq_lowerSemicontinuousHull)
  calc
    convexConjugate (supportFunction C : E → WithBotTop 𝕜) =
        convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) := hsupport
    _ = lowerSemicontinuousHull (δ[𝕜](· | C)) := hbiconj

-- Proof sketch: apply the owner-level biconjugacy identity above and rewrite `cl(δ(· | C))` as
-- `δ(· | closure C)` using the generic closure-of-indicator theorem.
/-- Pairing-swap owner form of Text 13.1.5: the conjugate of the support function of a convex set
is the indicator of the set closure. -/
theorem convexConjugate_supportFunction_eq_indicatorFunction_closure
    (C : Set E) (hC : Convex 𝕜 C) [ClosedIciTopology 𝕜] :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = (δ[𝕜](· | closure C)) := by
  change convexConjugate (supportFunction C : E → WithBotTop 𝕜) = (δ[𝕜](· | closure C))
  calc
    convexConjugate (supportFunction C : E → WithBotTop 𝕜) = cl((δ[𝕜](· | C))) :=
      convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator C hC
    _ = (δ[𝕜](· | closure C)) := by
      simpa using
        (lowerSemicontinuousHull_indicator_eq_indicator_closure (X := E) (𝕜 := 𝕜) C)

end

section

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
  [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: this is the pairing-symmetric bridge for the pairing-swap owner theorem above.
theorem convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : 𝕜) = ⟪y, x⟫ₚ)
    (C : Set E) (hC : Convex 𝕜 C) :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = cl((δ[𝕜](· | C))) := by
  letI : HasPairingSwap E E 𝕜 := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator
      (E := E) C hC)

-- Proof sketch: this is the pairing-symmetric bridge for the pairing-swap owner theorem above.
/-- Pairing-layer bridge form of Text 13.1.5: if the pairing is symmetric, then the conjugate of
the support function of a convex set is the indicator of the set closure. -/
theorem convexConjugate_supportFunction_eq_indicatorFunction_closure_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : 𝕜) = ⟪y, x⟫ₚ)
    (C : Set E) (hC : Convex 𝕜 C) [ClosedIciTopology 𝕜] :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = (δ[𝕜](· | closure C)) := by
  letI : HasPairingSwap E E 𝕜 := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_supportFunction_eq_indicatorFunction_closure (E := E) C hC)

end
