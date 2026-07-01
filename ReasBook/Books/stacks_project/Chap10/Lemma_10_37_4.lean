import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K]

/- Layering for this item:
* source-facing: closure of almost integral elements in the fraction field, together with the
  comparison between integral and almost integral elements;
* core/canonical owner: the subalgebra `completeIntegralClosure R K` and the predicates
  `IsAlmostIntegral R` and `IsIntegral R`;
* bridge/view: `mem_completeIntegralClosure`, which identifies the source-facing predicate with
  membership in the owner subalgebra.
-/

section

variable [IsDomain R] [IsFractionRing R K]

/- Lemma 10.37.4 (1): the sum of two almost integral elements is again almost integral. This is
the additive closure of the canonical owner object `completeIntegralClosure R K`. -/
#check
  (show ∀ u v : K, IsAlmostIntegral R u → IsAlmostIntegral R v → IsAlmostIntegral R (u + v) from
    fun _ _ ↦ (completeIntegralClosure R K).add_mem)

/- Lemma 10.37.4 (2): the product of two almost integral elements is again almost integral. This
is the multiplicative closure of the canonical owner object `completeIntegralClosure R K`. -/
#check
  (show ∀ u v : K, IsAlmostIntegral R u → IsAlmostIntegral R v → IsAlmostIntegral R (u * v) from
    fun _ _ ↦ (completeIntegralClosure R K).mul_mem)

end

/- Lemma 10.37.4 (3): an element of the fraction field that is integral over `R` is almost
integral over `R`. This is exactly the canonical mathlib theorem
`IsIntegral.isAlmostIntegral`, specialized to a domain `R` and its fraction field `K`. -/
recall IsIntegral.isAlmostIntegral

/- Lemma 10.37.4 (4): if `R` is Noetherian, then an element of the fraction field is almost
integral over `R` only if it is integral over `R`. This is exactly the canonical mathlib theorem
`IsAlmostIntegral.isIntegral`, specialized to a Noetherian domain `R` and its fraction field `K`.
-/
recall IsAlmostIntegral.isIntegral

end
