import BauschkeLean.Chap22.Proposition_22_19
import BauschkeLean.Chap16.Proposition_16_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Characterizations

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

-- Domain-style sampling:
-- - `source-facing`: Corollary 24.7 is the uniqueness-up-to-constant statement for `Γ₀(H)`
--   functions with the same proximity operator.
-- - `core/canonical`: the actual owner of the constant-difference conclusion is
--   `exists_eq_add_const_of_subdifferential_eq_of_mem_gammaZero` in Chapter 22.
-- - `bridge/view`: the canonical prox-to-subdifferential bridge already appears upstream in
--   `Chap16/Proposition_16_44`, so this corollary should derive subdifferential equality from
--   pointwise equality of `Prox[f, hf]` and `Prox[g, hg]` rather than restating a parallel owner.

/-- Corollary 24.7: if `f, g ∈ Γ₀(ℋ)` have the same proximity operator, then they differ by a
finite real constant; equivalently, there exists `γ : ℝ` such that
`(f x : EReal) = (g x : EReal) + γ` for every `x`. -/
theorem exists_eq_add_const_of_eq_proximityOperator_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hprox : Prox[f, hf] = Prox[g, hg]) :
    ∃ γ : ℝ, ∀ x : H, (f x : EReal) = (g x : EReal) + γ := by
  have hsub : ∂ f = ∂ g := by
    funext x
    ext u
    have hf_sub : u ∈ (∂ f) x ↔ x = Prox[f, hf] (x + u) := by
      simpa using
        (eq_proximityOperator_iff_sub_mem_subdifferential hf (x + u) x).symm
    have hg_sub : u ∈ (∂ g) x ↔ x = Prox[g, hg] (x + u) := by
      simpa using
        (eq_proximityOperator_iff_sub_mem_subdifferential hg (x + u) x).symm
    rw [hf_sub, hg_sub]
    have hprox_apply : Prox[f, hf] (x + u) = Prox[g, hg] (x + u) :=
      congrArg (fun T : H → H ↦ T (x + u)) hprox
    simpa [hprox_apply]
  exact exists_eq_add_const_of_subdifferential_eq_of_mem_gammaZero hf hg hsub

end Characterizations

end ERealFunction
