import Mathlib
import stacks_project.Chap10.Lemma_10_66_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-
Domain triage:
* `source-facing`: the textbook item identifies the image of `WeakAss_S(M)` in `Spec R` under a
  finite ring map.
* `core/canonical`: the owner abstraction in this chapter is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: the only primitive module-theoretic datum needed pointwise is the annihilator
  ideal `Ideal.torsionOf _ _ m`; the set-level equality should be expressed directly in terms of
  the owner set rather than by a parallel wrapper declaration.
-/

namespace weaklyAssociatedPrimes

omit [Module.Finite R S] in
private theorem comap_torsionOf_eq (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- Lemma 10.66.13: let `f : Spec S → Spec R` be induced by `algebraMap R S`. If `R → S` is a
finite ring map, then the image of the weakly associated primes of `M` over `S` under `f` is
exactly the weakly associated primes of `M` over `R`. -/
-- Proof sketch: the inclusion `weaklyAssociatedPrimes R M ⊆ Ideal.comap (algebraMap R S) ''
-- weaklyAssociatedPrimes S M` is the restriction-of-scalars inclusion proved earlier. For the
-- reverse inclusion, start with `𝔮 ∈ weaklyAssociatedPrimes S M`, choose an element of `M` whose
-- annihilator has `𝔮` as a minimal prime, and use finiteness of `R → S`, prime avoidance, and the
-- semilocal structure of `S` over the contraction `𝔭` to produce an element whose annihilator over
-- `R` has `𝔭` as a minimal prime.
theorem restrictScalars_eq_image_comap_of_finite :
    Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M =
      weaklyAssociatedPrimes R M := by
  refine Set.Subset.antisymm ?_ subset_comap_image
  rintro 𝔭 ⟨𝔮, h𝔮, rfl⟩
  sorry

end weaklyAssociatedPrimes

end
