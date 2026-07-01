import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable {E : Type u} {F : Type v}
variable [HasPairing E E α] [HasPairing F F α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.2 identifies the conjugate of the precomposition
  `((cl g) A)^*` with the closure of the dual-side image `cl (A^* g^*)`.
- `core/canonical`: the owner layer is pairing-based. The primitive data are a primal map `A`,
  a dual map `Astar`, and the compatibility identity
  `⟪Astar y, x⟫ = ⟪y, A x⟫`.
- `bridge/view`: the inner-product adjoint form is a specialization with `Astar := A.adjoint`.

Domain-style sampling used here:
- `convexConjugate` from Defn 12.2;
- `lowerSemicontinuousHull` from Text 7.0.4;
- `Function.linearImage` and
  `convexConjugate_linearImage_eq_comp` from Theorem 16.3.1;
- the inner-product bridge `LinearMap.adjoint`.

Primitive data vs derived API:
- primitive inputs: maps `A : E → F` and `Astar : F → E`, the duality compatibility
  witness, and a function `g : F → WithTopBot α`;
- primitive owner identity: the biconjugate-layer equality
  `((g⋆⋆ ∘ A)⋆) = (Astar ◁ g⋆)⋆⋆`;
- derived API: the lower-semicontinuous-hull form and the convex-source form, recovered by
  supplying biconjugacy identities from Theorem 12.2.

Layer target: `source-facing`, expressed through the canonical owner declarations.
-/

-- Proof sketch: apply Theorem 16.3.1 to `Astar` and `g⋆`, using `A` as the dual-side map.
-- This identifies `(Astar ◁ g⋆)⋆` with `g⋆⋆ ∘ A`; conjugating both sides gives the displayed
-- biconjugate-layer identity.
theorem convexConjugate_comp_linearMap_eq_biconjugate_linearImage
    (A : E → F) (Astar : F → E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : α) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot α) :
    ((g⋆⋆ ∘ A)⋆ : E → WithTopBot α) =
      ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ := by
  have himage :
      (Astar ◁ g⋆)⋆ = g⋆⋆ ∘ A := by
    simpa using
      (convexConjugate_linearImage_eq_comp
        (A := Astar) (Astar := A) (hA := hAstar)
        (f := g⋆))
  exact congrArg (fun f : E → WithTopBot α ↦ (f⋆ : E → WithTopBot α)) himage.symm

section

variable [TopologicalSpace α] [TopologicalSpace E] [TopologicalSpace F]

-- Proof sketch: rewrite the primitive biconjugate identity above using the two supplied
-- biconjugacy equalities `g⋆⋆ = cl(g)` and `(Astar ◁ g⋆)⋆⋆ = cl(Astar ◁ g⋆)`.
/-- Lower-semicontinuous-hull form of Theorem 16.3.2: if the biconjugates of `g` and
`Astar ◁ g⋆` identify with their lower-semicontinuous hulls, then `((cl(g) ∘ A)⋆) =
cl(Astar ◁ g⋆)`. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_biconjugate
    (A : E → F) (Astar : F → E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : α) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot α)
    (hg_biconj : g⋆⋆ = cl(g))
    (hAg_biconj :
      ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ =
        cl(Astar ◁ g⋆)) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot α) = cl(Astar ◁ g⋆) := by
  calc
    ((cl(g) ∘ A)⋆ : E → WithTopBot α) = ((g⋆⋆ ∘ A)⋆ : E → WithTopBot α) := by
      simp [hg_biconj]
    _ = ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ := by
      simpa using
        convexConjugate_comp_linearMap_eq_biconjugate_linearImage
          (A := A) (Astar := Astar) (hAstar := hAstar) (g := g)
    _ = cl(Astar ◁ g⋆) := hAg_biconj

end

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]

-- Bridge note: the convex-source form relies on the Chapter 12 biconjugacy theorem
-- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.
-- The primitive theorem above is the canonical owner layer; this theorem supplies the
-- convex-source hypotheses that produce those biconjugacy identities.
-- Theorem 16.3.2 is recovered from the primitive biconjugacy-layer theorem by using
-- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` for `g` and `Astar ◁ g⋆`.
/-- Pairing-layer convex-source form of Theorem 16.3.2: for a primal map `A`, a dual map `Astar`,
and compatibility identity `⟪Astar y, x⟫ = ⟪y, A x⟫`, the conjugate of `cl(g) ∘ A` equals
`cl(Astar ◁ g⋆)` whenever `g` is convex. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot 𝕜) (hg : g.IsConvex 𝕜) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot 𝕜) = cl(Astar ◁ g⋆) := by
  have hgstar_conv : ((g⋆ : F → WithTopBot 𝕜)).IsConvex 𝕜 :=
    Function.isConvex_convexConjugate g
  have hconv : (Astar ◁ (g⋆ : F → WithTopBot 𝕜)).IsConvex 𝕜 := by
    simpa using
      Function.isConvex_linearImage (A := Astar) (h := (g⋆ : F → WithTopBot 𝕜)) hgstar_conv
  exact
    convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_biconjugate
      (A := A) (Astar := Astar) (hAstar := hAstar) (g := g)
      (hg_biconj := hg.biconjugate_eq_lowerSemicontinuousHull)
      (hAg_biconj := hconv.biconjugate_eq_lowerSemicontinuousHull)

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Inner-product-space bridge form of Theorem 16.3.2. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_adjoint_of_convex
    (A : E →ₗ[ℝ] F) (g : F → WithTopBot ℝ) (hg : g.IsConvex ℝ) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot ℝ) = cl(A.adjoint ◁ g⋆) := by
  simpa using
    (convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
      (A := A) (Astar := A.adjoint)
      (hAstar := fun y x => A.adjoint_inner_left x y) (g := g) hg)

end
