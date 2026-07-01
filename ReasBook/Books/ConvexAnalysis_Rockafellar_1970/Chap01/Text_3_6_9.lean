import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_6_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {R : Type*}
variable [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u}
variable [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.9 fixes convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁` and `K₂`, then forms the set of pairs `(λ, x)` for which the first coordinate decomposes as
  `λ = λ₁ + λ₂` with `(λ₁, x) ∈ K₁` and `(λ₂, x) ∈ K₂`.
- `core/canonical`: the owner abstractions are the first-coordinate fiberwise-sum operator `+ᶠ₁`
  from Text 3.6.2 and `Convex R` on subsets of `R × E`.
- `bridge/view`: Text 3.6.2 supplies the source-facing convexity theorem for this displayed
  first-coordinate existential set, proved there by bridging to `+ᶠ` after
  swapping the two product coordinates.
- Primitive data vs derived API: the theorem is a direct convexity statement about that explicit
  subset of `R × E`; the surface notation `+ᶠ₁` packages that subset without changing the
  mathematics.
- Domain-style sampling: this item reuses the owner `homogenizationSet`, the owner-side convexity
  theorem `Convex.homogenizationSet`, and the canonical bridge theorem
  `Convex.fiberwiseFirstSum`.
- Ambient minimization: the theorem uses only the ordered semifield module structure required by
  `homogenizationSet`, so the owner-level statement lives over an arbitrary module over `R`
  rather than the concrete coordinate model `EuclideanSpace ℝ (Fin n)`.
- Layer target: `source-facing`, implemented as a thin specialization of upstream owner bridges.
-/

/-- Text 3.6.9: for convex sets `C₁` and `C₂`, if `K₁` and `K₂` are their homogenization sets,
then the set of pairs `(λ, x)` for which there exist `λ₁` and `λ₂` with
`λ = λ₁ + λ₂`, `(λ₁, x) ∈ K₁`, and `(λ₂, x) ∈ K₂` is convex. Specializing `R = ℝ` recovers the
textbook statement. -/
-- Proof sketch: `Convex.homogenizationSet` gives convexity of each owner set
-- `homogenizationSet Cᵢ`, then the canonical owner theorem `Convex.fiberwiseFirstSum`
-- applies directly.
theorem Convex.homogenizationSet_fiberwiseFirstSum {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] +ᶠ₁ K[R | C₂]) := by
  exact (hC₁.homogenizationSet).fiberwiseFirstSum hC₂.homogenizationSet

end
