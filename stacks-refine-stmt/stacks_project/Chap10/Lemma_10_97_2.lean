import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section flatness

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

-- The owner-level canonical fact is the instance
-- `AdicCompletion.flat_of_isNoetherian : Module.Flat R (AdicCompletion I R)`.
-- The textbook ring-hom statement is its standard bridge through
-- `RingHom.flat_algebraMap_iff`.
/-- Lemma 10.97.2 (1): if `R` is Noetherian, then the canonical ring map from `R` to its `I`-adic
completion is flat. -/
theorem adicCompletion_algebraMap_flat :
    (algebraMap R (AdicCompletion I R)).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

end flatness

section exactness

variable {R : Type u} [CommRing R] {I : Ideal R} [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable [Module.Finite R N]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
variable (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)

/- Lemma 10.97.2 (2): for finitely generated modules over a Noetherian ring, applying `I`-adic
completion to an exact pair of linear maps remains exact. This is exactly the canonical theorem
`AdicCompletion.map_exact`. -/
recall AdicCompletion.map_exact

end exactness
