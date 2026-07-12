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

/- The textbook Leibniz rule for tangent vectors is the canonical derivation rule
`Derivation.leibniz`, applied in the pointed smooth-function algebra `C^∞⟮I, M; ℝ⟯⟨p⟩`. -/
#check
  (Derivation.leibniz :
    ∀ {p : M} (v : PointDerivation I p) (f g : C^∞⟮I, M; ℝ⟯⟨p⟩),
      v (f * g) = f • v g + g • v f)
