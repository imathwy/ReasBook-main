import Mathlib
import StacksProject_2024.Chap10.Definition_10_166_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

namespace Algebra

universe u v w

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

variable {ι : Type w}

/-- Lemma 10.166.5: if `k` is the directed colimit of subfields `kᵢ` and `A` is geometrically
regular over every `kᵢ`, then `A` is geometrically regular over `k`. -/
-- Proof sketch: to prove geometric regularity over `k`, test against a finite purely inseparable
-- extension `K/k`. The finitely many coefficients defining `K` descend to some stage `kᵢ`,
-- producing a finite purely inseparable extension `Kᵢ/kᵢ` with `K ≃ Kᵢ ⊗[kᵢ] k`; then
-- `K ⊗[k] A` identifies with `Kᵢ ⊗[kᵢ] A`, which is regular by the hypothesis on stage `i`.
theorem isGeometricallyRegular_of_directed_iSup_subfields
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (hA : ∀ i, IsGeometricallyRegular (kᵢ i) A) :
    IsGeometricallyRegular k A := sorry

end

end Algebra
