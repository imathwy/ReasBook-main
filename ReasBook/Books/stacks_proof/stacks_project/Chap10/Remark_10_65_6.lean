import Mathlib.RingTheory.Localization.BaseChange
import stacks_proof.stacks_project.Chap10.Lemma_10_63_14
import stacks_proof.stacks_project.Chap10.Lemma_10_63_16
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal.Quotient (eq_zero_iff_mem)
open scoped TensorProduct nonZeroDivisors

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable [AddCommGroup N] [Module S N]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "Rbar" => R ⧸ p
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

-- Elements of `pS` vanish in `κ(p) ⊗[R] S`.
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S} (hx : x ∈ p.map (algebraMap R S)) :
    algebraMap S (p.Fiber S) x = 0 := by
  let φ : (R ⧸ p) ⊗[R] S →+* p.Fiber S :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (p.map (algebraMap R S)) x : S ⧸ p.map (algebraMap R S)) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p
    have : e (Ideal.Quotient.mk (p.map (algebraMap R S)) x) = (1 : R ⧸ p) ⊗ₜ[R] x := rfl
    rw [← this, hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

private noncomputable instance :
    Algebra Sbar (p.Fiber S) :=
  (Ideal.Quotient.liftₐ (p.map (algebraMap R S)) (Algebra.ofId S (p.Fiber S))
    fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map p hx).toRingHom.toAlgebra

/-- Helper for Remark 10.65.6: the underlying ring equivalence from the quotient-base-changed
fiber presentation to the standard fiber ring. -/
private noncomputable def fiber_tensor_over_quotient_ring_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃+* p.Fiber S :=
  (Algebra.TensorProduct.commRight Rbar Sbar p.ResidueField).toRingEquiv.trans
    ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p)).trans
      (Algebra.TensorProduct.cancelBaseChange R Rbar p.ResidueField p.ResidueField S)).toRingEquiv

/-- Helper for Remark 10.65.6: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s`, so the ring bridge respects the `S / pS`-algebra structures. -/
private theorem algebraMap_quotient_to_fiber_mk (s : S) :
    algebraMap Sbar (p.Fiber S) (Ideal.Quotient.mk (p.map (algebraMap R S)) s) = 1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Remark 10.65.6: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s`, so the ring bridge respects the `S / pS`-algebra structures. -/
private theorem fiber_tensor_over_quotient_ring_equiv_commutes (x : Sbar) :
    fiber_tensor_over_quotient_ring_equiv (R := R) (S := S) (p := p)
      (algebraMap Sbar (Sbar ⊗[Rbar] p.ResidueField) x) =
    algebraMap Sbar (p.Fiber S) x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [fiber_tensor_over_quotient_ring_equiv, algebraMap_quotient_to_fiber_mk,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Helper for Remark 10.65.6: the quotient presentation `S / pS` tensored with `κ(p)` over
`R / p` recovers the fiber ring `κ(p) ⊗[R] S` as an `S / pS`-algebra. -/
private noncomputable def fiber_tensor_over_quotient_alg_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃ₐ[Sbar] p.Fiber S :=
  { toRingEquiv := fiber_tensor_over_quotient_ring_equiv (R := R) (S := S) (p := p)
    commutes' := fiber_tensor_over_quotient_ring_equiv_commutes
      (R := R) (S := S) (p := p) }

/-- Helper for Remark 10.65.6: the fiber ring is the localization of `S / pS` at the image of
the nonzerodivisors of `R / p`. -/
private noncomputable def fiber_quotient_localization_alg_equiv :
    Localization T ≃ₐ[Sbar] p.Fiber S :=
  ((Localization.tensorLeftAlgEquiv Rbar⁰ Sbar).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sbar ≃ₐ[Sbar] Sbar)
        (IsLocalization.algEquiv Rbar⁰ (Localization Rbar⁰) p.ResidueField))).trans
    (fiber_tensor_over_quotient_alg_equiv (R := R) (S := S) (p := p))

/-- Helper for Remark 10.65.6: after viewing the fiber ring as a localization of `S / pS`, the
associated primes of the fiber module over `S / pS` are exactly the contractions of its associated
primes over the fiber ring. -/
private theorem associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber :
    Ideal.comap (algebraMap Sbar (p.Fiber S)) '' associatedPrimesOfModule (p.Fiber S) Nfiber =
      associatedPrimesOfModule Sbar Nfiber := by
  letI : IsLocalization T (Localization T) := Localization.isLocalization (M := T)
  letI : IsLocalization T (p.Fiber S) :=
    IsLocalization.isLocalization_of_algEquiv T
      (fiber_quotient_localization_alg_equiv (p := p))
  -- Route correction: once the fiber ring is recognized as a localization of `S / pS`, the
  -- reverse inclusion is the same annihilator-localization argument as in Lemma 10.63.16 (1).
  refine Set.Subset.antisymm associatedPrimesOfModule_image_comap_subset ?_
  intro p0 hp0
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp0
  rcases hp0 with ⟨hp0, m, hm⟩
  let q : Ideal (p.Fiber S) := Ideal.torsionOf (p.Fiber S) Nfiber m
  have hcomap : Ideal.comap (algebraMap Sbar (p.Fiber S)) q = p0 := by
    ext x
    rw [hm, Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    simp [algebraMap_smul]
  have hq_ne_top : q ≠ ⊤ := by
    intro hq_top
    apply hp0.ne_top
    simpa [hq_top] using hcomap.symm
  have hq : q.IsPrime := by
    refine (IsLocalization.isPrime_iff_isPrime_disjoint T (p.Fiber S) q).2 ?_
    refine ⟨by simpa [hcomap] using hp0, ?_⟩
    simpa [hcomap] using
      (IsLocalization.disjoint_comap_iff T (p.Fiber S) q).2 hq_ne_top
  refine ⟨q, ?_, hcomap⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
  exact ⟨hq, m, rfl⟩

/- Domain triage:
* `source-facing`: the two equalities in Remark 10.65.6 for associated primes of the fiber module.
* `core/canonical`: the owner theorem
  `associatedPrimesOfModule_quotient_image_comap_eq` for contraction along a quotient map.
* `bridge/view`: the local `Sbar`-algebra structure on `p.Fiber S`, used only to state the
  source-facing fiber comparison for the canonical tensor model `Nfiber`.
-/

/- Remark 10.65.6, first equality: for the canonical fiber module modeling
`N ⊗_R κ(p)`, the comparison between associated primes over `S` and over `S ⧸ pS` is exactly the
specialization of the owner theorem
`associatedPrimesOfModule_quotient_image_comap_eq` to the ideal `pS = p.map (algebraMap R S)` and
the `S`-module `Nfiber`. -/
#check
  (associatedPrimesOfModule_quotient_image_comap_eq (p.map (algebraMap R S)) :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      associatedPrimesOfModule S Nfiber)

/-- Remark 10.65.6, second equality: for the same fiber module, the textbook associated primes
over `S ⧸ pS` agree with those over the fiber ring `κ(p) ⊗[R] S` after transporting them back to
ideals of `S`. -/
@[stacks 05E0]
theorem associatedPrimesOfModule_fiberTensor_over_quotient_eq_over_fiber :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      Ideal.comap (algebraMap S (p.Fiber S)) ''
        associatedPrimesOfModule (p.Fiber S) Nfiber := by
  -- First rewrite the `S / pS`-level associated primes through the localization comparison.
  rw [← associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber
    (R := R) (S := S) (N := N) (p := p)]
  -- Then contract once more along `S → S / pS`, which composes to the original map `S → κ(p) ⊗ S`.
  ext I
  constructor
  · rintro ⟨K, ⟨J, hJ, rfl⟩, hKI⟩
    refine ⟨J, hJ, ?_⟩
    simpa [Ideal.comap_comap] using hKI
  · rintro ⟨J, hJ, hJmap⟩
    refine ⟨Ideal.comap (algebraMap Sbar (p.Fiber S)) J, ⟨J, hJ, rfl⟩, ?_⟩
    simpa using hJmap

end
