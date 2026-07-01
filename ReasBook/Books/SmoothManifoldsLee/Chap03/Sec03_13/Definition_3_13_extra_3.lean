import Mathlib.Geometry.Manifold.DerivationBundle

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Derivation Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/- Definition 3.13-extra-3: Lee's tangent space at `p`, defined as the real vector space of
derivations on smooth real-valued functions at `p`, is mathlib's `PointDerivation I p`. -/
#check (PointDerivation I : M → Type _)

-- Proof sketch: apply `Derivation.leibniz` to the pointed algebra of smooth functions at `p`, then
-- rewrite the scalar actions using `PointedContMDiffMap.smul_def`.
/-- A tangent vector viewed as a point derivation satisfies the textbook Leibniz rule at its base
point. -/
theorem point_derivation_leibniz {p : M} (v : PointDerivation I p) (f g : C^∞⟮I, M; ℝ⟯) :
    v (f * g) = f p * v g + g p * v f := by
  let fp : C^∞⟮I, M; ℝ⟯⟨p⟩ := f
  let gp : C^∞⟮I, M; ℝ⟯⟨p⟩ := g
  calc
    v (f * g) = v (fp * gp) := by rfl
    _ = fp • v gp + gp • v fp := v.leibniz fp gp
    _ = f p * v g + g p * v f := by rfl
