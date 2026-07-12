import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Etale R S]

-- Proof sketch: the owner abstraction for the conclusion is `Algebra.QuasiFinite R S`. Mathlib
-- already provides the canonical instance
-- `[Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] : Algebra.QuasiFinite R S`, and
-- an étale algebra supplies these hypotheses automatically.
/-- Lemma 10.143.6: an étale ring map `R → S` is quasi-finite. -/
theorem etale_ringHom_quasiFinite : (algebraMap R S).QuasiFinite := by
  rw [RingHom.quasiFinite_algebraMap]
  infer_instance

end
