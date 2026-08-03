import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap16.Proposition_16_9
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap24.Proposition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` did not surface a usable finite-family proximal theorem,
-- so this file follows the repo's finite direct-sum owner `directSumFunction` from
-- `Chap09/Remark_9_37.lean` together with the Chapter 12 `Prox` surface.
-- Domain-style sampling:
-- - primary domain: proximal calculus for finite direct sums of `Γ₀` functions on Hilbert spaces
-- - inspected owners:
--   `directSumFunction` and `directSumFunction_mem_gammaZero_of_forall_mem_gammaZero` from
--   `Chap09/Remark_9_37.lean`
--   `subdifferential_directSumFunction_eq_coordinatewise` from
--   `Chap16/Proposition_16_9.lean`
--   `Prox[_, _]` from `Chap12/ProximityOperator.lean`
--   `eq_proximityOperator_iff_sub_mem_subdifferential` from `Chap24/Proposition_24_1.lean`
-- Source/core/bridge triage:
-- - `source-facing`: the coordinatewise proximal vector for the finite direct sum
-- - `core/canonical`: the Chapter 9 owner `directSumFunction` and the Chapter 16 subdifferential
--   owner for that direct sum
-- - `bridge/view`: Proposition 24.11 identifies the Chapter 12 proximity operator of the direct
--   sum with the source-facing coordinatewise proximal vector

open scoped ERealFunction InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section Proposition2411

variable {I : Type v} [Fintype I]
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The coordinatewise proximal vector on the finite Hilbert direct sum `lp K 2` attached to a
family `fᵢ ∈ Γ₀(K i)`. -/
def directSumCoordinatewiseProx
    (f : ∀ i, K i → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(K i)) :
    lp K 2 → lp K 2 :=
  fun x ↦ ⟨fun i ↦ Prox[f i, hf i] (x i), Memℓp.all _⟩

/-- Evaluating the `i`th coordinate of `directSumCoordinatewiseProx f hf x` returns
`Prox[fᵢ, hfᵢ] (xᵢ)`. -/
@[simp] theorem directSumCoordinatewiseProx_apply
    (f : ∀ i, K i → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(K i))
    (x : lp K 2) (i : I) :
    directSumCoordinatewiseProx f hf x i = Prox[f i, hf i] (x i) :=
  rfl

/-- Proposition 24.11: for a finite family of real Hilbert spaces `K i`, if
`f = ⨁ i, fᵢ` is the finite direct sum of functions `fᵢ ∈ Γ₀(K i)`, then the proximity operator of
`f` acts coordinatewise:
`Prox_f x = (Prox_{fᵢ}(xᵢ))ᵢ`. -/
theorem prox_directSumFunction_eq_directSumCoordinatewiseProx
    (f : ∀ i, K i → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(K i))
    (x : lp K 2) :
    Prox[directSumFunction f, directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf] x =
      directSumCoordinatewiseProx f hf x := by
  let p := directSumCoordinatewiseProx f hf x
  have hdom : ∀ i, (effectiveDomain (f i)).Nonempty := fun i ↦ (hf i).2.nonempty
  symm
  apply (eq_proximityOperator_iff_sub_mem_subdifferential
    (directSumFunction f) (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)).2
  rw [subdifferential_directSumFunction_eq_coordinatewise f hdom p]
  intro i
  have hi :
      x i - Prox[f i, hf i] (x i) ∈ (∂ (f i)) (Prox[f i, hf i] (x i)) :=
    (eq_proximityOperator_iff_sub_mem_subdifferential (f i) (hf i)).1 rfl
  simpa [p] using hi

end Proposition2411

end ERealFunction
