import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.DerivationBundle

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_13_extra_1 (from Chap03/Sec03_13) -/
universe v

variable {V : Type v}

/-- Definition 3.13-extra-1: The geometric tangent space at `a` is the copy of the ambient vector
space whose elements are vectors with initial point fixed at `a`. -/
abbrev geometric_tangent_space : V → Type v := Bundle.Trivial V V

/-- The total space of geometric tangent vectors, with the base point remembered as part of the
data so that fibers over distinct points are disjoint. -/
abbrev geometric_tangent_vector : Type v :=
  Bundle.TotalSpace V (Bundle.Trivial V V)

-- A named owner for the textbook based-vector notation.
/-- The geometric tangent vector with displacement `v` and initial point `a`. -/
abbrev based_vector (a : V) (v : V) : geometric_tangent_space a := v

/- Textbook notation for a vector `v` based at the point `a`, written in Lean as `v ᵥ[a]`. -/
notation:max v "ᵥ[" a "]" => based_vector a v

namespace geometric_tangent_space

open Bundle

/-- The notation `v ᵥ[a]` realizes the textbook pair `(a, v)` under the canonical product-model
identification `Bundle.TotalSpace.toProd`. -/
theorem toProd_based_vector (a v : V) :
    TotalSpace.toProd V V (((v ᵥ[a]) : geometric_tangent_space a) : geometric_tangent_vector) =
      (a, v) := by
  rfl

/-- The canonical product-model image of the geometric tangent space at `a` is exactly the set
`{a} × V`. -/
theorem range_toProd (a : V) :
    Set.range (TotalSpace.toProd V V ∘
      ((↑) : geometric_tangent_space a → geometric_tangent_vector)) =
        {p : V × V | p.1 = a} := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · rintro hp
    refine ⟨p.2, ?_⟩
    rcases p with ⟨x, y⟩
    simp at hp
    simp [hp]

end geometric_tangent_space

/-! ### Definition_3_13_extra_2 (from Chap03/Sec03_13) -/
open scoped ContDiff Manifold

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, R^n)
local notation "SmoothRn" => C^∞⟮I, R^n; ℝ⟯

/- Definition 3.13-extra-2: for a point `a ∈ ℝ^n`, the tangent space `T_a ℝ^n` viewed as the set
of derivations on smooth real-valued functions at `a` is mathlib's `PointDerivation` on the
Euclidean manifold `EuclideanSpace ℝ (Fin n)`. -/
#check (PointDerivation I : R^n → Type _)

/- A point derivation at `a` satisfies the Leibniz rule on smooth real-valued functions on
`ℝ^n`. This is the Euclidean specialization of the chapter owner theorem from
`Definition_3_13_extra_3`. -/
#check
  (point_derivation_leibniz :
    ∀ {a : R^n} (v : PointDerivation I a) (f g : SmoothRn),
      v (f * g) = f a * v g + g a * v f)

/- Addition of point derivations is the canonical addition on `Derivation`, evaluated by
`Derivation.add_apply`. -/
#check Derivation.add_apply

/- Scalar multiplication of point derivations is the canonical scalar action on `Derivation`,
evaluated by `Derivation.smul_apply`. -/
#check Derivation.smul_apply

/-! ### Definition_3_13_extra_3 (from Chap03/Sec03_13) -/
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

/-! ### Proposition_3_13 (from Chap03/Sec03_14) -/
noncomputable section

open scoped Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so the
-- statement uses local mathlib inspection of `NormedSpace.fromTangentSpace`.

section

universe u v

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Proposition 3.13 (1): for a finite-dimensional real vector space `V` with its standard smooth
manifold structure and a point `a : V`, the map `v ↦ Dᵥ|ₐ` is the canonical linear isomorphism
from `V` to the tangent space `TangentSpace (𝓘(ℝ, V)) a`. -/
def vector_space_to_tangent_space (a : V) : V ≃L[ℝ] TangentSpace (𝓘(ℝ, V)) a :=
  (NormedSpace.fromTangentSpace a).symm

/-- Applying `vector_space_to_tangent_space` simply regards a vector of `V` as a tangent vector at
`a`. -/
theorem vector_space_to_tangent_space_apply (a : V) (v : V) :
    vector_space_to_tangent_space a v = v := sorry

/-- Proposition 3.13 (2): if `L : V → W` is linear, then the differential of `L` carries the
tangent vector at `a` corresponding to `v` to the tangent vector at `L a` corresponding to
`L v`. -/
theorem mfderiv_vector_space_to_tangent_space (a : V) (L : V →ₗ[ℝ] W) (v : V) :
    mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, W)) L a (vector_space_to_tangent_space a v) =
      vector_space_to_tangent_space (L a) (L v) := sorry

end
