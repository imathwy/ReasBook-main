import StacksProject_2024.Chap10.Lemma_10_128_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped nonZeroDivisors

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

/- Domain-style sampling for Lemma 10.128.5:
- primary domain: the single-element form of the local flatness criterion for an essentially
  finitely presented flat local map, where regularity on the closed fiber is transported to
  regularity in the total ring together with flatness of the quotient;
- sampled owner declarations:
  `RingHom.EssFinitePresentation`,
  `injective_and_flat_quotient_of_mod_maximalIdeal_injective`,
  `Ideal.range_mul'`,
  `isRegular_iff_mem_nonZeroDivisors`;
- best owner abstraction: the core owner is the linear-map theorem
  `injective_and_flat_quotient_of_mod_maximalIdeal_injective`; the present lemma is its
  `source-facing` specialization to multiplication by a single element;
- primitive data: the local map `R → S`, the essential finite presentation hypothesis `hess`, the
  element `f : S`, and regularity of its image in the closed fiber;
- derived API: flatness of `S / fS` over `R` and regularity of `f` in `S`.

Source/core/bridge triage:
- `source-facing`: the Stacks single-element statement;
- `core/canonical`: `injective_and_flat_quotient_of_mod_maximalIdeal_injective`;
- `bridge/view`: the `S`-linear endomorphism `LinearMap.mul S S f` and the identification
  `LinearMap.range (LinearMap.mul S S f) = Ideal.span {f}`.
-/

-- Proof sketch: apply Lemma `10.128.4` to the `S`-linear map `S →ₗ[S] S` given by multiplication
-- by `f`. The hypothesis that `f` is a nonzerodivisor on the closed fiber gives injectivity of
-- the induced map modulo `maximalIdeal R`. Lemma `10.128.4` then yields injectivity of
-- multiplication by `f` on `S`, i.e. `f` is regular in `S`, and flatness of its cokernel, whose
-- range ideal is canonically `fS = Ideal.span {f}`.
/-- Lemma 10.128.5: for a flat essentially finitely presented local map `R → S`, if `f ∈ S` is a
nonzerodivisor on the closed fiber `S / 𝔪_R S`, then the quotient `S / fS` is flat over `R` and
`f` is a nonzerodivisor in `S`. -/
theorem flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation) (f : S)
    (hbar : IsRegular (Ideal.Quotient.mk 𝔪S f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := by
  let u : S →ₗ[S] S := LinearMap.mul S S f
  have hf : Ideal.Quotient.mk 𝔪S f ∈ nonZeroDivisors (S ⧸ 𝔪S) :=
    isRegular_iff_mem_nonZeroDivisors.mp hbar
  have hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
    intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    have hab' : (Submodule.Quotient.mk (f * a) : S ⧸ maximalIdeal R • (⊤ : Submodule R S)) =
        Submodule.Quotient.mk (f * b) := by
      simpa [LinearMap.quotientMapByIdeal, u] using hab
    have hab'' : f * a - f * b ∈ maximalIdeal R • (⊤ : Submodule R S) :=
      (Submodule.Quotient.eq _).1 hab'
    apply (Submodule.Quotient.eq _).2
    rw [Ideal.smul_top_eq_map] at hab'' ⊢
    change f * a - f * b ∈ 𝔪S at hab''
    change a - b ∈ 𝔪S
    have hmul : f * (a - b) ∈ 𝔪S := by
      simpa [mul_sub] using hab''
    have hzero : Ideal.Quotient.mk 𝔪S (a - b) = 0 := by
      rw [mem_nonZeroDivisors_iff_left] at hf
      exact hf (Ideal.Quotient.mk 𝔪S (a - b)) <| by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        simpa [mul_comm] using hmul
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hzero
  obtain ⟨hinj, hflat⟩ :=
    injective_and_flat_quotient_of_mod_maximalIdeal_injective hess u hmod
  have hrange : LinearMap.range u = Ideal.span ({f} : Set S) := by
    simp [u]
  rw [hrange] at hflat
  refine ⟨hflat, ?_⟩
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  intro x hx
  exact hinj <| by simpa [u] using hx

end
