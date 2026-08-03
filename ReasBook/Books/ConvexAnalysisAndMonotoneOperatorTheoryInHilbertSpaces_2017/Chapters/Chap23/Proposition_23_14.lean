import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap23.Proposition_23_7

-- Semantic recall note: `lean_leansearch` surfaced only unrelated generic resolvent/closure
-- results, so this item follows the canonical Chapter 23 owner `J[((γ : ℝ) • A)]` together with
-- an explicit realizer `T : H → H`.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 23.14: whole-space firm nonexpansiveness is the standard Hilbert-space
inequality `‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
private abbrev FirmlyNonexpansive (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

omit [CompleteSpace H] in
/-- Helper for Proposition 23.14: maximality of `A⁻¹ + ((β : ℝ) • Id)` transports to maximality
of the `β`-Yosida approximation `{}^[β] A`. -/
private theorem maximalYosidaApproximation_of_maximalInverseAddSmulId
    (A : SetValuedOperator H H) (β : PosReal)
    (hA :
      Maximal IsMonotone
        (A⁻¹ + ((β : ℝ) • id.toSetValuedOperator))) :
    Maximal IsMonotone ({}^[β] A) := by
  -- Rewrite the inverse-maximality hypothesis into the canonical Yosida approximation surface.
  simpa [yosidaApproximation_eq_inverse_smul_id_add_inverse, add_comm] using
    (Maximal.inverse hA)

omit [CompleteSpace H] in
/-- Helper for Proposition 23.14: the affine map built from a single-valued realizer `T` of
`J[((γ : ℝ) • A)]` realizes the resolvent of the scaled Yosida approximation
`((γ : ℝ) - (β : ℝ)) • {}^[β] A`. -/
private theorem
    id_add_smul_resolventRealizer_sub_id_toSetValuedOperator_eq_resolvent_smul_yosidaApproximation
    (A : SetValuedOperator H H) (β γ : PosReal) (hβγ : (β : ℝ) < (γ : ℝ))
    (T : H → H) (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    (fun x ↦ x + (1 - (β : ℝ) / (γ : ℝ)) • (T x - x)).toSetValuedOperator =
      J[(((γ : ℝ) - (β : ℝ)) • {}^[β] A)] := by
  let δ : PosReal := ⟨(γ : ℝ) - (β : ℝ), sub_pos.mpr hβγ⟩
  have hδaddβ : ((δ : ℝ) + (β : ℝ)) = (γ : ℝ) := by
    simp [δ]
  have hcoeff : 1 - (β : ℝ) / (γ : ℝ) = (δ : ℝ) / (γ : ℝ) := by
    dsimp [δ]
    field_simp [γ.2.ne']
  -- Compare the affine realizer with Proposition 23.7(iv) on the operator surface.
  rw [resolvent_smul_yosidaApproximation_eq_affine_resolvent A δ β]
  ext x y
  rw [hδaddβ]
  rw [← hT, Function.toSetValuedOperator_apply]
  -- Normalize the affine coefficient from `δ / γ` to `1 - β / γ`.
  simp [Function.toSetValuedOperator_apply, δ, hcoeff, sub_eq_add_neg]

omit [CompleteSpace H] in
/-- Proposition 23.14: let `β ∈ ℝ_{++}` and let `A : H → 2^H` be such that
`A⁻¹ + ((β : ℝ) • Id)` is maximally monotone, formalized as
`Maximal IsMonotone (A⁻¹ + ((β : ℝ) • id.toSetValuedOperator))`. If
`γ ∈ ]β, +∞[`, i.e. `(β : ℝ) < (γ : ℝ)`, then with `λ = 1 - β / γ` the affine map
`Id + λ (J_{γ A} - Id)` is firmly nonexpansive, formalized for every realizer
`T : H → H` of `J[((γ : ℝ) • A)]`. -/
theorem firmlyNonexpansive_id_add_resolventRealizer_sub_id_of_maximal_inverse_add_smul_id
    (A : SetValuedOperator H H) (β γ : PosReal)
    (hA :
      Maximal IsMonotone
        (A⁻¹ + ((β : ℝ) • id.toSetValuedOperator)))
    (hβγ : (β : ℝ) < (γ : ℝ)) (T : H → H)
    (hT : T.toSetValuedOperator = J[((γ : ℝ) • A)]) :
    FirmlyNonexpansive
      (fun x ↦
        x + (1 - (β : ℝ) / (γ : ℝ)) •
          (T x - x)) := by
  let δ : PosReal := ⟨(γ : ℝ) - (β : ℝ), sub_pos.mpr hβγ⟩
  -- Transport maximality from the hypothesis surface to the Yosida approximation.
  have hβA : Maximal IsMonotone ({}^[β] A) :=
    maximalYosidaApproximation_of_maximalInverseAddSmulId A β hA
  -- Identify the textbook affine map with the canonical resolvent surface.
  have hAffine :
      (fun x ↦ x + (1 - (β : ℝ) / (γ : ℝ)) • (T x - x)).toSetValuedOperator =
        J[((δ : ℝ) • {}^[β] A)] :=
    id_add_smul_resolventRealizer_sub_id_toSetValuedOperator_eq_resolvent_smul_yosidaApproximation
      A β γ hβγ T hT
  -- Apply Corollary 23.11 to that canonical resolvent representation.
  exact
    resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
      ({}^[β] A) hβA δ
      (fun x ↦ x + (1 - (β : ℝ) / (γ : ℝ)) • (T x - x)) hAffine

end SetValuedOperator
