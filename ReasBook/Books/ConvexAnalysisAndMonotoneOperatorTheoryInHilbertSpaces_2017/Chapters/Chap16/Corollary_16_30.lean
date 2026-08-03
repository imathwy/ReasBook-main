import Mathlib
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 16.30 is the `Γ₀(H)` reading of the inverse-subdifferential identity.
- `core/canonical`: Proposition 16.10 is the owner theorem at the primitive nonempty-domain layer.
- `bridge/view`: `f∗[hf]` is the canonical `Γ₀(H)` package
  `properConjugateIoi f hf.2.nonempty`.

Corollary 16.30 is therefore the source-facing `Γ₀(H)` specialization of Proposition 16.10,
obtained by rewriting the packaged conjugate through `gammaZeroConjugate`. -/
/-- Corollary 16.30: if `f ∈ Γ₀(H)`, then the inverse of the subdifferential of `f` is the
subdifferential of its Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
theorem inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ((∂ f).inverse : SetValuedOperator H H) = ∂ (f∗[hf]) := by
  ext u x
  constructor
  · intro hux
    rw [SetValuedOperator.mem_inverse_iff] at hux
    simpa [gammaZeroConjugate] using
      mem_subdifferential_properConjugateIoi_of_mem_subdifferential
        (f := f) hf.2.nonempty x u hux
  · intro hxu
    have hconj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
    have hu_sub :
        u ∈ (∂ ((f∗[hf])∗[hconj])) x := by
      simpa [gammaZeroConjugate] using
        mem_subdifferential_properConjugateIoi_of_mem_subdifferential
          (f := f∗[hf]) hconj.2.nonempty u x hxu
    have hbiconj :
        (f∗[hf])∗[hconj] = f := by
      funext z
      apply Subtype.ext
      calc
        (((f∗[hf])∗[hconj] z : Set.Ioi (⊥ : EReal)) : EReal) = (f∗[hf]).asEReal∗ z := by
          simp [gammaZeroConjugate]
        _ = f.asEReal∗∗ z := by
          have hpc :=
            properConjugateIoi_conjugate_eq_biconjugate
              (f := f) hf.2.nonempty z
          simpa [gammaZeroConjugate] using hpc
        _ = (f z : EReal) := by
          simpa [Function.asEReal] using
            congrArg (fun g : H → EReal ↦ g z) (biconjugate_eq_of_mem_gammaZero hf)
    rw [SetValuedOperator.mem_inverse_iff]
    have hu_f : u ∈ (∂ f) x := by
      simpa [hbiconj] using hu_sub
    exact hu_f

end SubdifferentialConjugation

end ERealFunction
