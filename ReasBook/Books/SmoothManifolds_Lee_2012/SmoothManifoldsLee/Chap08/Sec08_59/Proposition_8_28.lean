import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SmoothManifolds_Lee_2012.Chap08.Sec08_59.Definition_8_59_extra_1

open scoped ContDiff Manifold
open VectorField

section

universe u𝕜 uE uH uM

-- Domain sampling pass:
-- * primary domain: Lie brackets of smooth vector fields on manifolds;
-- * source-facing layer: Lee's Proposition 8.28 identities for `⁅X, Y⁆`;
-- * core/canonical owner: `VectorField.mlieBracket`, already exposed here via `⁅X, Y⁆`;
-- * derived API reused below: `mlieBracket_add_left`, `mlieBracket_add_right`,
--   `mlieBracket_const_smul_left`, `mlieBracket_const_smul_right`, `mlieBracket_swap`,
--   `mlieBracket_smul_left`, `mlieBracket_smul_right`, and `leibniz_identity_mlieBracket`.
-- Primitive data is only the vector fields and scalar functions; all algebraic identities are
-- derived consequences of the canonical owner, so this file should stay a thin source-facing layer
-- over that upstream API.

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Proposition 8.28 (1): the Lie bracket is bilinear in its first argument:
`[aX + bY, Z] = a [X, Z] + b [Y, Z]`. This already holds under first-order
differentiability of `X` and `Y`, hence in particular for smooth vector fields. -/
theorem lie_bracket_bilinear_left
    [CompleteSpace E]
    [IsManifold I 2 M]
    (X Y Z : Π p : M, TangentSpace I p)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hY : ContMDiff I I.tangent 1 (T% Y))
    (a b : 𝕜) :
    ⁅a • X + b • Y, Z⁆ = a • ⁅X, Z⁆ + b • ⁅Y, Z⁆ := by
  ext x
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hAXx : MDiffAt (T% (a • X)) x := by
    exact ((hX x).const_smul_section).mdifferentiableAt (by simp)
  have hBYx : MDiffAt (T% (b • Y)) x := by
    exact ((hY x).const_smul_section).mdifferentiableAt (by simp)
  calc
    ⁅a • X + b • Y, Z⁆ x
      = mlieBracket I (a • X + b • Y) Z x := by simp
    _ = mlieBracket I (a • X) Z x + mlieBracket I (b • Y) Z x := by
      rw [mlieBracket_add_left hAXx hBYx]
    _ = a • mlieBracket I X Z x + b • mlieBracket I Y Z x := by
      rw [mlieBracket_const_smul_left hXx, mlieBracket_const_smul_left hYx]
    _ = (a • ⁅X, Z⁆ + b • ⁅Y, Z⁆) x := by
      simp [VectorField.bracket_eq_mlieBracket]

/-- Proposition 8.28 (2): the Lie bracket is bilinear in its second argument:
`[Z, aX + bY] = a [Z, X] + b [Z, Y]`. This already holds under first-order
differentiability of `X` and `Y`, hence in particular for smooth vector fields. -/
theorem lie_bracket_bilinear_right
    [CompleteSpace E]
    [IsManifold I 2 M]
    (X Y Z : Π p : M, TangentSpace I p)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hY : ContMDiff I I.tangent 1 (T% Y))
    (a b : 𝕜) :
    ⁅Z, a • X + b • Y⁆ = a • ⁅Z, X⁆ + b • ⁅Z, Y⁆ := by
  ext x
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hAXx : MDiffAt (T% (a • X)) x := by
    exact ((hX x).const_smul_section).mdifferentiableAt (by simp)
  have hBYx : MDiffAt (T% (b • Y)) x := by
    exact ((hY x).const_smul_section).mdifferentiableAt (by simp)
  calc
    ⁅Z, a • X + b • Y⁆ x
      = mlieBracket I Z (a • X + b • Y) x := by simp
    _ = mlieBracket I Z (a • X) x + mlieBracket I Z (b • Y) x := by
      rw [mlieBracket_add_right hAXx hBYx]
    _ = a • mlieBracket I Z X x + b • mlieBracket I Z Y x := by
      rw [mlieBracket_const_smul_right hXx, mlieBracket_const_smul_right hYx]
    _ = (a • ⁅Z, X⁆ + b • ⁅Z, Y⁆) x := by
      simp [VectorField.bracket_eq_mlieBracket]

/- Proposition 8.28 (3): the Lie bracket is antisymmetric:
`[X, Y] = -[Y, X]`. -/
recall VectorField.mlieBracket_swap

/- Proposition 8.28 (4): the Lie bracket satisfies the Jacobi identity.
We record it in the canonical Leibniz form supplied by `VectorField.leibniz_identity_mlieBracket`,
which already works under the sharper `minSmoothness 𝕜 2` hypotheses. -/
theorem lie_bracket_jacobi
    [CompleteSpace E]
    [IsManifold I (minSmoothness 𝕜 3) M]
    (X Y Z : Π p : M, TangentSpace I p)
    (hX : ContMDiff I I.tangent (minSmoothness 𝕜 2) (T% X))
    (hY : ContMDiff I I.tangent (minSmoothness 𝕜 2) (T% Y))
    (hZ : ContMDiff I I.tangent (minSmoothness 𝕜 2) (T% Z)) :
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ := by
  simpa [bracket_eq_mlieBracket] using
    leibniz_identity_mlieBracket hX hY hZ

/-- Proposition 8.28 (5): for smooth functions `f`, `g` and smooth vector fields `X`, `Y`,
the Lie bracket satisfies
`[fX, gY] = fg [X, Y] + (fXg) Y - (gYf) X`. This already holds under first-order
differentiability of `f`, `g`, `X`, and `Y`, hence in particular for smooth data. -/
theorem lie_bracket_smul_smul
    [CompleteSpace E]
    [IsManifold I 2 M]
    (f g : M → 𝕜)
    (X Y : Π p : M, TangentSpace I p)
    (hf : ContMDiff I 𝓘(𝕜) 1 f)
    (hg : ContMDiff I 𝓘(𝕜) 1 g)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hY : ContMDiff I I.tangent 1 (T% Y)) :
    ⁅f • X, g • Y⁆ =
      fun x ↦
        (f x * g x) • ⁅X, Y⁆ x +
          (d% g x ((f x) • X x)) • Y x -
          (d% f x ((g x) • Y x)) • X x := by
  ext x
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  have hgx : MDiffAt g x := (hg x).mdifferentiableAt (by simp)
  have hXx : MDiffAt (fun y ↦ (X y : TangentBundle I M)) x := by
    simpa using (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (fun y ↦ (Y y : TangentBundle I M)) x := by
    simpa using (hY x).mdifferentiableAt (by simp)
  have hsmul_left :
      mlieBracket I (f • X) (g • Y) x =
        -d% f x ((g • Y) x) • X x + f x • mlieBracket I X (g • Y) x := by
    exact mlieBracket_smul_left hfx hXx
  have hsmul_right :
      mlieBracket I X (g • Y) x = d% g x (X x) • Y x + g x • mlieBracket I X Y x := by
    exact mlieBracket_smul_right hgx hYx
  calc
    ⁅f • X, g • Y⁆ x
      = -d% f x ((g • Y) x) • X x + f x • ⁅X, g • Y⁆ x := by
          simpa [VectorField.bracket_eq_mlieBracket] using hsmul_left
    _ = -d% f x ((g x) • Y x) • X x + f x • (d% g x (X x) • Y x + g x • ⁅X, Y⁆ x) := by
          simp [VectorField.bracket_eq_mlieBracket, hsmul_right]
    _ = -d% f x ((g x) • Y x) • X x + (f x * d% g x (X x)) • Y x + (f x * g x) • ⁅X, Y⁆ x := by
          simpa [add_assoc] using
            show
              -(d% f x ((g x) • Y x)) • X x +
                  (f x • (d% g x (X x) • Y x) + f x • (g x • ⁅X, Y⁆ x)) =
                -(d% f x ((g x) • Y x)) • X x +
                  (f x * d% g x (X x)) • Y x +
                    (f x * g x) • ⁅X, Y⁆ x by
              simp [smul_smul, add_assoc]
    _ = -d% f x ((g x) • Y x) • X x + d% g x ((f x) • X x) • Y x + (f x * g x) • ⁅X, Y⁆ x := by
          have hsmul : d% g x ((f x) • X x) = f x * d% g x (X x) := by
            rw [(d% g x).map_smul]
            simp [smul_eq_mul]
          rw [← hsmul]
    _ = (f x * g x) • ⁅X, Y⁆ x + d% g x ((f x) • X x) • Y x - d% f x ((g x) • Y x) • X x := by
          simp [sub_eq_add_neg, add_assoc, add_comm]

end
