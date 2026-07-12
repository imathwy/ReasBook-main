import Mathlib

noncomputable section

open scoped LieGroup Manifold ContDiff

-- `lean_leansearch` is unavailable in this environment; the canonical mathlib owners used here
-- are `smoothLeftMul` / `smoothRightMul` and `Diffeomorph`.

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {H : Type*} [TopologicalSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]

/-- Definition 7.46-extra-3 (1). For `g ∈ G`, the left translation `L_g : G → G` is the map
`h ↦ g * h`. -/
abbrev leftTranslation (g : G) : G → G :=
  𝑳 I g

/-- `leftTranslation` evaluates by multiplication on the left. -/
theorem leftTranslation_apply (g h : G) :
    leftTranslation (I := I) g h = g * h := sorry

/-- Left translation by `g` as a global diffeomorphism of the Lie group `G`. -/
def leftTranslationDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G where
  toEquiv := Equiv.mulLeft g
  contMDiff_toFun :=
    show ContMDiff I I ∞ ((Equiv.mulLeft g : G ≃ G) : G → G) from
      contMDiff_mul_left (I := I) (n := ∞) (G := G) (a := g)
  contMDiff_invFun :=
    show ContMDiff I I ∞ (((Equiv.mulLeft g : G ≃ G).symm : G ≃ G) : G → G) from
      contMDiff_mul_left (I := I) (n := ∞) (G := G) (a := g⁻¹)

/-- `leftTranslationDiffeomorph` has the same underlying map as `leftTranslation`. -/
theorem leftTranslationDiffeomorph_apply (g h : G) :
    leftTranslationDiffeomorph (I := I) g h = leftTranslation (I := I) g h := sorry

/-- Definition 7.46-extra-3 (2). For `g ∈ G`, the right translation `R_g : G → G` is the map
`h ↦ h * g`. -/
abbrev rightTranslation (g : G) : G → G :=
  𝑹 I g

/-- `rightTranslation` evaluates by multiplication on the right. -/
theorem rightTranslation_apply (g h : G) :
    rightTranslation (I := I) g h = h * g := sorry

/-- Right translation by `g` as a global diffeomorphism of the Lie group `G`. -/
def rightTranslationDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G where
  toEquiv := Equiv.mulRight g
  contMDiff_toFun :=
    show ContMDiff I I ∞ ((Equiv.mulRight g : G ≃ G) : G → G) from
      contMDiff_mul_right (I := I) (n := ∞) (G := G) (a := g)
  contMDiff_invFun :=
    show ContMDiff I I ∞ (((Equiv.mulRight g : G ≃ G).symm : G ≃ G) : G → G) from
      contMDiff_mul_right (I := I) (n := ∞) (G := G) (a := g⁻¹)

/-- `rightTranslationDiffeomorph` has the same underlying map as `rightTranslation`. -/
theorem rightTranslationDiffeomorph_apply (g h : G) :
    rightTranslationDiffeomorph (I := I) g h = rightTranslation (I := I) g h := sorry
