import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {K : Type v} [CommRing K] [Algebra R K]

/- Canonical reference: for an `R`-algebra `K`, the predicate `IsAlmostIntegral R : K → Prop`
expresses that an element of `K` is almost integral over `R`, meaning that some nonzero element
of `R` sends all powers of that element back into the image of `R`. -/
#check (IsAlmostIntegral R : K → Prop)

/- Definition 10.37.3: the owner object for complete normality is the canonical subalgebra
`completeIntegralClosure R K`. In the intended fraction-ring case, complete normality is the
assertion that this subalgebra is `⊥`, i.e. that every almost integral element already lies in the
image of `algebraMap R K`. -/
#check (completeIntegralClosure R K = ⊥)

-- Proof sketch: use `mem_completeIntegralClosure` to rewrite almost integrality as membership in
-- `completeIntegralClosure R K`, then rewrite the defining equality to `⊥` and use
-- `Algebra.mem_bot` to identify membership in `⊥` with lying in the image of `algebraMap`.
/-
Bridge/view: in any `R`-algebra `K`, the condition `completeIntegralClosure R K = ⊥` says exactly
that every almost integral element of `K` comes from the algebra map `R → K`. Applied to a
fraction ring of a domain, this is the source-facing definition of complete normality.
-/
theorem isCompletelyNormal_iff :
    completeIntegralClosure R K = ⊥ ↔
      ∀ x : K, IsAlmostIntegral R x → ∃ y : R, algebraMap R K y = x := by
  rw [eq_bot_iff]
  constructor
  · intro h x hx
    have hx' : x ∈ (⊥ : Subalgebra R K) := h <| by
      simpa [mem_completeIntegralClosure] using hx
    simpa [Algebra.mem_bot, Set.mem_range] using hx'
  · intro h x hx
    simpa [Algebra.mem_bot, Set.mem_range] using
      h x (by simpa [mem_completeIntegralClosure] using hx)

section

variable [IsFractionRing R K]

/-- In the intended domain setting, a completely normal ring is integrally closed. -/
theorem isIntegrallyClosed_of_isCompletelyNormal
    (h : completeIntegralClosure R K = ⊥) : IsIntegrallyClosed R := by
  refine (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp ?_
  apply le_bot_iff.mp
  simpa [h] using
    (show integralClosure R K ≤ completeIntegralClosure R K from
      integralClosure_le_completeIntegralClosure)

end
end
