module

import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelIso.Basic

universe u

public section

variable {A : Type u} {n : ℕ} (f : A ≃ Fin n)

/- Remark 10.3: A bijection `f : A ≃ Fin n`, where `Fin n` is Lean's zero-based
model of the book's ordered set `{1, …, n}`, transports its strict order to the
relation `f ⁻¹'o (· < ·)` on `A`. This relation well-orders `A`, and `f` is an
order isomorphism from it to the strict order on `Fin n`. -/
#check (RelIso.preimage f ((· < ·) : Fin n → Fin n → Prop) :
  (f ⁻¹'o (· < ·)) ≃r ((· < ·) : Fin n → Fin n → Prop))
#synth IsWellOrder A (f ⁻¹'o ((· < ·) : Fin n → Fin n → Prop))

end
