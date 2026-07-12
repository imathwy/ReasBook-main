import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField

universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L] [Normal K L]

/-- Every finite intermediate field of a normal extension lies in a finite normal
intermediate field. -/
-- Proof sketch: take the normal closure of `M` inside `L`; it contains `M`, is finite over `K`,
-- with normality over `K`.
theorem exists_finite_normal_intermediate_field
    (M : IntermediateField K L) [FiniteDimensional K M] :
    ∃ (N : IntermediateField K L) (_ : FiniteDimensional K N), M ≤ N ∧ Normal K N := sorry

/-- Lemma 9.16.5: if `M/K` is normal with `M'/M` finite inside `L`, then `M'` is contained
in an intermediate field `N/M` that is finite normal over `K`. -/
-- Proof sketch: first place the finitely generated `M`-subextension `M'` inside a finite
-- intermediate field over `K`; then take its normal closure inside `L`; view the result as an
-- intermediate field over `M`.
theorem exists_finite_extension_normal_over_base
    (M : IntermediateField K L) [Normal K M]
    (M' : IntermediateField M L) [FiniteDimensional M M'] :
    ∃ (N : IntermediateField M L) (_ : FiniteDimensional M N), M' ≤ N ∧ Normal K N := sorry

end
