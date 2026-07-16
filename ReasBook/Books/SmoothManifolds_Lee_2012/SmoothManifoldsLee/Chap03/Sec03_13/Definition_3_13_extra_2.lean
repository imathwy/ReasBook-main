import Mathlib.Analysis.InnerProductSpace.PiL2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_13.Definition_3_13_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, R^n)
local notation "SmoothRn" => C^∞⟮I, R^n; ℝ⟯

/- Definition 3.13-extra-2: for a point `a ∈ ℝ^n`, the tangent space `T_a ℝ^n` viewed as the set
of derivations on smooth real-valued functions at `a` is mathlib's `PointDerivation` on the
Euclidean manifold `EuclideanSpace ℝ (Fin n)`. -/
#check (PointDerivation I : R^n → Type _)

/- A point derivation at `a` satisfies the canonical Leibniz rule in the pointed smooth-function
algebra at `a`; `PointedContMDiffMap.smul_def` rewrites the scalar actions to the textbook formula
`v (f * g) = f a * v g + g a * v f`. -/
#check
  (Derivation.leibniz :
    ∀ {a : R^n} (v : PointDerivation I a) (f g : PointedContMDiffMap ℝ I R^n ∞ a),
      v (f * g) = f • v g + g • v f)

/- Addition of point derivations is the canonical addition on `Derivation`, evaluated by
`Derivation.add_apply`. -/
#check Derivation.add_apply

/- Scalar multiplication of point derivations is the canonical scalar action on `Derivation`,
evaluated by `Derivation.smul_apply`. -/
#check Derivation.smul_apply
