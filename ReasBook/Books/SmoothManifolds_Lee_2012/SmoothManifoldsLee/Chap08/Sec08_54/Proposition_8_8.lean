import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "SmoothFunction" => C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
local notation "SmoothVectorField" =>
  ContMDiffSection I E ∞ (fun p : M ↦ TangentSpace I p)

-- `lean_leansearch` was unavailable in this runner, so the canonical owners were checked directly
-- against mathlib's `ContMDiffSection` and `C^∞` smooth-function APIs.

/-- Proposition 8.8 (1): if `X` and `Y` are smooth vector fields on `M` and `f`, `g` are smooth
real-valued functions on `M`, then `f • X + g • Y` is a smooth vector field. -/
theorem contMDiff_add_smul_vectorField
    (X Y : (p : M) → TangentSpace I p)
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y))
    (f g : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    ContMDiff I I.tangent ∞ (T% (f • X + g • Y)) := by
  exact (hf.smul_section hX).add_section (hg.smul_section hY)

instance : SMul SmoothFunction SmoothVectorField where
  smul f X := ⟨fun x ↦ f x • X x, f.contMDiff.smul_section X.contMDiff⟩

/-- Pointwise formula for the action of smooth functions on bundled smooth vector fields. -/
theorem smoothVectorField_smul_apply
    (f : SmoothFunction) (X : SmoothVectorField) (x : M) :
    (f • X) x = f x • X x := rfl

/-- Proposition 8.8 (2): the bundled smooth vector fields on `M` form a module over the ring
`C^∞(M)` of smooth real-valued functions on `M`. -/
instance smoothVectorFieldModule : Module SmoothFunction SmoothVectorField where
  one_smul X := by
    ext x
    simp [smoothVectorField_smul_apply]
  mul_smul f g X := by
    ext x
    simp [smoothVectorField_smul_apply, mul_smul]
  smul_zero f := by
    ext x
    simp [smoothVectorField_smul_apply]
  smul_add f X Y := by
    ext x
    simp [smoothVectorField_smul_apply, smul_add]
  zero_smul X := by
    ext x
    simp [smoothVectorField_smul_apply]
  add_smul f g X := by
    ext x
    simp [smoothVectorField_smul_apply, add_smul]

end
