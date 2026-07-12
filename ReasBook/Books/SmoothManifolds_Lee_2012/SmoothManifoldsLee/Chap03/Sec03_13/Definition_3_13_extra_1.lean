import Mathlib.Data.Bundle

-- Declarations for this item will be appended below by the statement pipeline.

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
