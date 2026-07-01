import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import stacks_project.Chap10.Definition_10_63_1
import stacks_project.Chap10.Definition_10_65_2
import stacks_project.Chap10.Lemma_10_62_1
import stacks_project.Chap10.Lemma_10_63_3
import stacks_project.Chap10.Lemma_10_63_4
import stacks_project.Chap10.Lemma_10_63_14
import stacks_project.Chap10.Lemma_10_63_16
import stacks_project.Chap10.Lemma_10_63_17

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal.Quotient (eq_zero_iff_mem)
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N]

/- Domain triage: this file lies in commutative algebra of associated primes under base change.
The owner abstraction is the chapter definition `relativeAssassin R S N` from Definition 10.65.2.
The only primitive extra data needed here is the quotient module `N / pN`; the sets `A'`, `A_fin`,
`A'_fin`, `B`, and `B_fin` are source-facing derived views used to compare that owner with
fiberwise and finite-generation presentations from the source. -/

/-- The quotient module `N / pN` appearing in Lemma 10.65.1. -/
abbrev relativeAssassinPrimeQuotient
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N]
    (p : Ideal R) : Type w :=
  N ⧸ (Ideal.map (algebraMap R S) p) • (⊤ : Submodule S N)

/-- The fiber-spectrum image `A'` from Lemma 10.65.1. -/
abbrev relativeAssassinAprime
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  ⋃ p : PrimeSpectrum R,
    PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
      { q : PrimeSpectrum (p.asIdeal.Fiber S) |
          q.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S) ((p.asIdeal.Fiber S) ⊗[S] N) }

/-- Membership in `A'` is by definition a fiber point mapping to the given prime of `S`. -/
@[simp] theorem mem_relativeAssassinAprime_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprime R S N ↔
      ∃ p : PrimeSpectrum R,
        q ∈ PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
          { q' : PrimeSpectrum (p.asIdeal.Fiber S) |
              q'.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
                ((p.asIdeal.Fiber S) ⊗[S] N) } := by
  constructor
  · intro hq
    exact Set.mem_iUnion.mp hq
  · rintro ⟨p, hp⟩
    exact Set.mem_iUnion.mpr ⟨p, hp⟩

/-- The finite-looking set `A_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinAfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S |
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) }

/-- Membership in `A_fin` is the associated-prime condition for the contracted prime quotient. -/
@[simp] theorem mem_relativeAssassinAfin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAfin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := by
  rfl

/-- The set `A'_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinAprimeFin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S |
      ∃ p : PrimeSpectrum R,
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) }

/-- Membership in `A'_fin` is by definition association to some prime-quotient `N / pN`. -/
@[simp] theorem mem_relativeAssassinAprimeFin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprimeFin R S N ↔
      ∃ p : PrimeSpectrum R,
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
  rfl

end

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N]
variable (p : Ideal R) [p.IsPrime]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "Rbar" => R ⧸ p
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

/-- Helper for Lemma 10.65.1: elements of `pS` vanish in the fiber ring `κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S} (hx : x ∈ p.map (algebraMap R S)) :
    algebraMap S (p.Fiber S) x = 0 := by
  let φ : (R ⧸ p) ⊗[R] S →+* p.Fiber S :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (p.map (algebraMap R S)) x : Sbar) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : Rbar) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p
    have he : e (Ideal.Quotient.mk (p.map (algebraMap R S)) x) = (1 : Rbar) ⊗ₜ[R] x :=
      rfl
    rw [← he, hquot]
    simp [e]
  have hφ : φ ((1 : Rbar) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

/-- Helper for Lemma 10.65.1: the fiber ring inherits the quotient-ring algebra structure. -/
private noncomputable instance fiberQuotientAlgebra :
    Algebra Sbar (p.Fiber S) :=
  (Ideal.Quotient.liftₐ (p.map (algebraMap R S)) (Algebra.ofId S (p.Fiber S))
    fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map (p := p) hx).toRingHom.toAlgebra

/-- Helper for Lemma 10.65.1: the quotient-base-changed fiber presentation recovers the usual
fiber ring at the level of rings. -/
private noncomputable def fiber_tensor_over_quotient_ring_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃+* p.Fiber S :=
  (Algebra.TensorProduct.commRight Rbar Sbar p.ResidueField).toRingEquiv.trans
    ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p)).trans
      (Algebra.TensorProduct.cancelBaseChange R Rbar p.ResidueField p.ResidueField S)).toRingEquiv

/-- Helper for Lemma 10.65.1: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s` in the fiber ring. -/
private theorem algebraMap_quotient_to_fiber_mk (s : S) :
    algebraMap Sbar (p.Fiber S) (Ideal.Quotient.mk (p.map (algebraMap R S)) s) = 1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Lemma 10.65.1: the ring equivalence from the quotient-base-changed fiber
presentation is compatible with the `S / pS`-algebra structures. -/
private theorem fiber_tensor_over_quotient_ring_equiv_commutes (x : Sbar) :
    fiber_tensor_over_quotient_ring_equiv (p := p)
      (algebraMap Sbar (Sbar ⊗[Rbar] p.ResidueField) x) =
    algebraMap Sbar (p.Fiber S) x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [fiber_tensor_over_quotient_ring_equiv, algebraMap_quotient_to_fiber_mk,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Helper for Lemma 10.65.1: the quotient-base-changed fiber presentation recovers the usual
fiber ring as an `S / pS`-algebra. -/
private noncomputable def fiber_tensor_over_quotient_alg_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃ₐ[Sbar] p.Fiber S :=
  { toRingEquiv := fiber_tensor_over_quotient_ring_equiv (p := p)
    commutes' := fiber_tensor_over_quotient_ring_equiv_commutes (p := p) }

/-- Helper for Lemma 10.65.1: the fiber ring is the localization of `S / pS` at the image of the
nonzerodivisors of `R / p`. -/
private noncomputable def fiber_quotient_localization_alg_equiv :
    Localization T ≃ₐ[Sbar] p.Fiber S :=
  ((Localization.tensorLeftAlgEquiv Rbar⁰ Sbar).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sbar ≃ₐ[Sbar] Sbar)
        (IsLocalization.algEquiv Rbar⁰ (Localization Rbar⁰) p.ResidueField))).trans
    (fiber_tensor_over_quotient_alg_equiv (p := p))

/-- Helper for Lemma 10.65.1: after identifying the fiber ring with a localization of `S / pS`,
associated primes over `S / pS` are exactly contractions of associated primes over the fiber ring. -/
private theorem associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber :
    Ideal.comap (algebraMap Sbar (p.Fiber S)) '' associatedPrimesOfModule (p.Fiber S) Nfiber =
      associatedPrimesOfModule Sbar Nfiber := by
  letI : IsLocalization T (Localization T) := Localization.isLocalization (M := T)
  letI : IsLocalization T (p.Fiber S) :=
    IsLocalization.isLocalization_of_algEquiv T
      (fiber_quotient_localization_alg_equiv (p := p))
  -- The owner theorem is Lemma 10.63.16 (1) for the localization `S / pS → κ(p) ⊗[R] S`.
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

/-- Helper for Lemma 10.65.1: the associated primes of the fiber module over `S` are exactly the
contractions of the associated primes over the fiber ring. -/
private theorem associatedPrimesOfModule_fiberTensor_eq_image_comap :
    associatedPrimesOfModule S Nfiber =
      Ideal.comap (algebraMap S (p.Fiber S)) '' associatedPrimesOfModule (p.Fiber S) Nfiber := by
  calc
    associatedPrimesOfModule S Nfiber =
        Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
          associatedPrimesOfModule Sbar Nfiber := by
          symm
          simpa using
            (associatedPrimesOfModule_quotient_image_comap_eq (R := S)
              (I := p.map (algebraMap R S)) (M := Nfiber))
    _ =
        Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
          (Ideal.comap (algebraMap Sbar (p.Fiber S)) ''
            associatedPrimesOfModule (p.Fiber S) Nfiber) := by
          rw [associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber (p := p).symm]
    _ =
        Ideal.comap (algebraMap S (p.Fiber S)) '' associatedPrimesOfModule (p.Fiber S) Nfiber := by
          ext I
          constructor
          · rintro ⟨K, ⟨J, hJ, rfl⟩, hKI⟩
            exact ⟨J, hJ, by simpa [Ideal.comap_comap] using hKI⟩
          · rintro ⟨J, hJ, hJI⟩
            refine ⟨Ideal.comap (algebraMap Sbar (p.Fiber S)) J, ?_, ?_⟩
            · exact ⟨J, hJ, rfl⟩
            · simpa using hJI

/-- Helper for Lemma 10.65.1: an associated prime of the fiber module over `S` is exactly the
image of an associated prime over the fiber ring. -/
private theorem mem_associatedPrimesOfModule_fiberTensor_iff
    (q : PrimeSpectrum S) :
    q.asIdeal ∈ associatedPrimesOfModule S Nfiber ↔
      q ∈ PrimeSpectrum.comap (algebraMap S (p.Fiber S)) ''
        { q' : PrimeSpectrum (p.Fiber S) |
            q'.asIdeal ∈ associatedPrimesOfModule (p.Fiber S) Nfiber } := by
  rw [associatedPrimesOfModule_fiberTensor_eq_image_comap (p := p)]
  constructor
  · rintro ⟨J, hJ, hJq⟩
    let q' : PrimeSpectrum (p.Fiber S) := ⟨J, hJ.1⟩
    refine ⟨q', hJ, ?_⟩
    apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal] using hJq
  · rintro ⟨q', hq', hqq'⟩
    refine ⟨q'.asIdeal, hq', ?_⟩
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqq'

end

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Helper for Lemma 10.65.1: reducing `N` modulo `pS` is the same `S`-module as tensoring `N`
with the quotient ring `R ⧸ p`. -/
private noncomputable def relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
    (p : Ideal R) :
    relativeAssassinPrimeQuotient R S N p ≃ₗ[S] N ⊗[R] (R ⧸ p) :=
  (TensorProduct.quotTensorEquivQuotSMul N (p.map (algebraMap R S))).symm.trans <|
    (TensorProduct.congr (Ideal.qoutMapEquivTensorQout (R := R) (S := S) (I := p))
      (LinearEquiv.refl S N)).trans <|
    (TensorProduct.comm S _ N).trans <|
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (R ⧸ p)

/-- Helper for Lemma 10.65.1: raising the universe of the right tensor factor does not change the
resulting `S`-module. -/
private noncomputable def tensor_right_ulift_linearEquiv
    {M : Type x} [AddCommGroup M] [Module R M] :
    N ⊗[R] ULift.{y, x} M ≃ₗ[S] N ⊗[R] M :=
  TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl S N) (ULift.moduleEquiv (R := R) (M := M))

section

variable (p : Ideal R) [p.IsPrime]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "Rbar" => R ⧸ p
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

/-- Helper for Lemma 10.65.1: the quotient module `N / pN` is the canonical base change
`(S / pS) ⊗[S] N`. -/
private noncomputable def relativeAssassinPrimeQuotient_quotientBaseChange_linearEquiv :
    relativeAssassinPrimeQuotient R S N p ≃ₗ[Sbar] Sbar ⊗[S] N := by
  let I : Ideal S := p.map (algebraMap R S)
  have hsurj : Function.Surjective (algebraMap S (S ⧸ I)) := by
    simpa [Ideal.Quotient.algebraMap_eq] using
      (show Function.Surjective (Ideal.Quotient.mk I) from Ideal.Quotient.mk_surjective)
  -- Route correction: normalize `N / pN` first as an `S / pS`-base change before localizing.
  exact (LinearEquiv.extendScalarsOfSurjective (R := S) (S := S ⧸ I) hsurj
    (TensorProduct.quotTensorEquivQuotSMul N I)).symm

/-- Helper for Lemma 10.65.1: localizing `N / pN` at the image of the nonzerodivisors of
`R / p` identifies it with the fiber module `κ(p) ⊗[R] N`. -/
private noncomputable def localized_relativeAssassinPrimeQuotient_linearEquiv_fiberTensor :
    LocalizedModule T (relativeAssassinPrimeQuotient R S N p) ≃ₗ[Sbar] Nfiber := by
  let e₀ :
      LocalizedModule T (relativeAssassinPrimeQuotient R S N p) ≃ₗ[Sbar]
        Localization T ⊗[Sbar] relativeAssassinPrimeQuotient R S N p :=
    (LocalizedModule.equivTensorProduct T (relativeAssassinPrimeQuotient R S N p)).restrictScalars Sbar
  let e₁ :
      Localization T ⊗[Sbar] relativeAssassinPrimeQuotient R S N p ≃ₗ[Sbar]
        Localization T ⊗[Sbar] (Sbar ⊗[S] N) :=
    TensorProduct.congr (LinearEquiv.refl Sbar (Localization T))
      (relativeAssassinPrimeQuotient_quotientBaseChange_linearEquiv
        (R := R) (S := S) (N := N) p)
  let e₂ :
      Localization T ⊗[Sbar] (Sbar ⊗[S] N) ≃ₗ[Sbar] Localization T ⊗[S] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      S Sbar (Localization T) (Localization T) N).restrictScalars Sbar
  let e₃ :
      Localization T ⊗[S] N ≃ₗ[Sbar] Nfiber :=
    TensorProduct.AlgebraTensorModule.congr
      (f := (fiber_quotient_localization_alg_equiv (R := R) (S := S) (p := p)).toLinearEquiv)
      (g := LinearEquiv.refl S N)
  -- The bridge is the source route: quotient base change, then localization, then fiber algebra.
  exact e₀.trans (e₁.trans (e₂.trans e₃))

/-- Helper for Lemma 10.65.1: if a prime of `S / pS` contracts to `p ⊂ R`, then its contraction
to `R / p` is the zero ideal. -/
private theorem quotient_prime_comap_eq_bot_of_under_eq
    {q : Ideal S} {qbar : Ideal Sbar}
    (hcomap : Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) qbar = q)
    (hunder : q.under R = p) :
    Ideal.comap (algebraMap Rbar Sbar) qbar = ⊥ := by
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  calc
    Ideal.comap (Ideal.Quotient.mk p) (Ideal.comap (algebraMap Rbar Sbar) qbar) =
        Ideal.comap (algebraMap R Sbar) qbar := by
          ext r
          rfl
    _ = Ideal.comap (algebraMap R S) q := by
          rw [← hcomap]
          ext r
          rfl
    _ = p := by
          simpa [Ideal.under_def] using hunder
    _ = Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal Rbar) := by
          symm
          ext r
          rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]

/-- Helper for Lemma 10.65.1: the contraction condition `q ∩ R = p` forces the corresponding
prime of `S / pS` to avoid the image of the nonzerodivisors of `R / p`. -/
private theorem quotient_prime_disjoint_localization_submonoid_of_under_eq
    {q : Ideal S} {qbar : Ideal Sbar}
    (hcomap : Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) qbar = q)
    (hunder : q.under R = p) :
    Disjoint (T : Set Sbar) (qbar : Set Sbar) := by
  have hbot :
      Ideal.comap (algebraMap Rbar Sbar) qbar = ⊥ :=
    quotient_prime_comap_eq_bot_of_under_eq (R := R) (S := S) (p := p) hcomap hunder
  rw [Set.disjoint_left]
  intro x hxT hxqbar
  rcases (show x ∈ Algebra.algebraMapSubmonoid Sbar Rbar⁰ from hxT) with ⟨s, hs, rfl⟩
  have hs_mem : (s : Rbar) ∈ Ideal.comap (algebraMap Rbar Sbar) qbar := by
    simpa using hxqbar
  have hs_zero : (s : Rbar) = 0 := by
    rw [hbot] at hs_mem
    have hs_bot : (s : Rbar) ∈ (⊥ : Ideal Rbar) := hs_mem
    exact hs_bot
  exact (nonZeroDivisors.ne_zero hs) hs_zero

/-- Helper for Lemma 10.65.1: associated primes of `N / pN` whose contraction to `R` is `p`
become associated primes of the fiber module after localization. -/
private theorem associatedPrimesOfModule_relativeAssassinPrimeQuotient_inter_under_eq_subset_fiberTensor :
    associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) ∩
      { q : Ideal S | q.under R = p } ⊆
        associatedPrimesOfModule S Nfiber := by
  intro q hq
  rcases hq with ⟨hq, hunder⟩
  let I : Ideal S := p.map (algebraMap R S)
  have hqbar_mem :
      q ∈ Ideal.comap (Ideal.Quotient.mk I) ''
        associatedPrimesOfModule Sbar (relativeAssassinPrimeQuotient R S N p) := by
    rw [associatedPrimesOfModule_quotient_image_comap_eq
      (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p)]
    exact hq
  rcases hqbar_mem with ⟨qbar, hqbar, hcomap⟩
  have hdisj :
      Disjoint (T : Set Sbar) (qbar : Set Sbar) :=
    quotient_prime_disjoint_localization_submonoid_of_under_eq
      (R := R) (S := S) (p := p) hcomap hunder
  have hloc :
      qbar ∈ associatedPrimesOfModule Sbar
        (LocalizedModule T (relativeAssassinPrimeQuotient R S N p)) :=
    associatedPrimesOfModule_inter_disjoint_subset_localizedModule T ⟨hqbar, hdisj⟩
  have hfiber_bar :
      qbar ∈ associatedPrimesOfModule Sbar Nfiber := by
    rw [LinearEquiv.associatedPrimesOfModule_eq Sbar
      (LocalizedModule T (relativeAssassinPrimeQuotient R S N p))
      (localized_relativeAssassinPrimeQuotient_linearEquiv_fiberTensor
        (R := R) (S := S) (N := N) (p := p))] at hloc
    exact hloc
  rw [associatedPrimesOfModule_fiberTensor_eq_image_comap (R := R) (S := S) (N := N) (p := p)]
  rw [← associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber
    (R := R) (S := S) (N := N) (p := p)] at hfiber_bar
  rcases hfiber_bar with ⟨J, hJ, hJqbar⟩
  refine ⟨J, hJ, ?_⟩
  calc
    Ideal.comap (algebraMap S (p.Fiber S)) J
        = Ideal.comap (Ideal.Quotient.mk I) (Ideal.comap (algebraMap Sbar (p.Fiber S)) J) := by
            ext s
            rfl
    _ = q := by simpa [hcomap] using congrArg (Ideal.comap (Ideal.Quotient.mk I)) hJqbar

end

/-- The set `B` from Lemma 10.65.1. -/
abbrev relativeAssassinB
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | ∃ (M : Type (max u v w x)) (_ : AddCommGroup M) (_ : Module R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) }

/-- The set `B_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinBfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | ∃ (M : Type (max u v w x)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.Finite R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) }

/-- Helper for Lemma 10.65.1: an injective map preserves the exact torsion ideal of a chosen
tensor witness. -/
private theorem torsionOf_map_eq_of_injective
    {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X] [Module A X]
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    {f : X →ₗ[A] Y} (hf : Function.Injective f) (x : X) :
    Ideal.torsionOf A Y (f x) = Ideal.torsionOf A X x := by
  -- Compare annihilator membership pointwise through injectivity of `f`.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply hf
    simpa using ha
  · intro ha
    simpa using congrArg f ha

/-- Helper for Lemma 10.65.1: every tensor lies in the image of tensoring with some finite
submodule of the right factor. -/
private theorem exists_finite_submodule_tensor_preimage
    {M : Type x} [AddCommGroup M] [Module R M] (z : N ⊗[R] M) :
    ∃ (M' : Submodule R M) (_ : Module.Finite R M') (z' : N ⊗[R] M'),
      TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype z' = z := by
  obtain ⟨M', hM'finite, hz_range⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite
      (R := R) (M := N) (N := M) ({z} : Set (N ⊗[R] M)) (Set.toFinite _)
  let inclusionTensor : N ⊗[R] M' →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype
  have hz_mem_range : z ∈ LinearMap.range inclusionTensor := by
    simpa [inclusionTensor] using hz_range (by simp : z ∈ ({z} : Set (N ⊗[R] M)))
  rcases hz_mem_range with ⟨z', rfl⟩
  -- Once the tensor lies in the image, the required finite-stage representative is exactly its
  -- chosen preimage.
  exact ⟨M', hM'finite, z', rfl⟩

/-- Lemma 10.65.1 (1): the relative assassin `A` agrees with the fiber-spectrum image `A'`. -/
-- Proof sketch: for each `p ∈ Spec(R)`, compare the associated primes of `N ⊗[R] κ(p)` over `S`,
-- over `S / pS`, and over the fiber ring using Lemma 10.63.14 and Lemma 10.63.16 (1).
theorem relativeAssassinA_eq_relativeAssassinAprime :
    relativeAssassin R S N = relativeAssassinAprime R S N := by
  ext q
  rw [mem_relativeAssassin_iff_fiber, mem_relativeAssassinAprime_iff]
  constructor
  · intro hq
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    -- Fix the contracted prime and rewrite the source membership through the fiber comparison.
    refine ⟨p, ?_⟩
    have hp :
        q.asIdeal ∈ associatedPrimesOfModule S ((p.asIdeal.Fiber S) ⊗[S] N) := by
      simpa [p, PrimeSpectrum.comap_asIdeal] using hq
    exact (mem_associatedPrimesOfModule_fiberTensor_iff (p := p.asIdeal) (q := q)).1 hp
  · rintro ⟨p, hp⟩
    -- The same fixed-prime comparison converts the fiber-spectrum witness back to `A`.
    rcases hp with ⟨q', hq', hqq'⟩
    have hqIdeal :
        q.asIdeal = Ideal.comap (algebraMap S (p.asIdeal.Fiber S)) q'.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hqq').symm
    have hqover : q'.asIdeal.LiesOver p.asIdeal := inferInstance
    have hunder' :
        Ideal.comap (algebraMap R (p.asIdeal.Fiber S)) q'.asIdeal = p.asIdeal := by
      simpa [Ideal.under_def] using hqover.over.symm
    have hunder : q.asIdeal.under R = p.asIdeal := by
      rw [Ideal.under_def, hqIdeal, Ideal.comap_comap]
      simpa [IsScalarTower.algebraMap_eq R S (p.asIdeal.Fiber S)] using hunder'
    have hmem :
        q.asIdeal ∈ associatedPrimesOfModule S ((p.asIdeal.Fiber S) ⊗[S] N) := by
      exact (mem_associatedPrimesOfModule_fiberTensor_iff (p := p.asIdeal) (q := q)).2
        ⟨q', hq', hqq'⟩
    have hpEq : p = PrimeSpectrum.comap (algebraMap R S) q := by
      apply PrimeSpectrum.ext
      simpa [PrimeSpectrum.comap_asIdeal] using hunder.symm
    subst p
    exact hmem

/-- Lemma 10.65.1 (2a): `A_fin` is contained in `A`. -/
-- Proof sketch: for `q ∈ A_fin`, use the contraction identity built into the definition of
-- `A_fin` and the localization comparison of associated primes from Lemma 10.63.16 to pass from
-- `N / (R ∩ q)N` to `N ⊗[R] κ(R ∩ q)`.
theorem relativeAssassinAfin_subset_relativeAssassinA :
    relativeAssassinAfin R S N ⊆ relativeAssassin R S N := by
  intro q hq
  let p : Ideal R := q.asIdeal.under R
  have hp : p.IsPrime := Ideal.IsPrime.under (A := R) q.asIdeal
  letI : p.IsPrime := hp
  -- Fix the contracted prime and use the localized quotient-to-fiber bridge from the source proof.
  have hfiber :
      q.asIdeal ∈ associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
    have hsubset :=
      associatedPrimesOfModule_relativeAssassinPrimeQuotient_inter_under_eq_subset_fiberTensor
        (R := R) (S := S) (N := N) (p := p)
    have hpair :
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) ∩
          { q : Ideal S | q.under R = p } := by
      refine ⟨?_, ?_⟩
      · simpa [mem_relativeAssassinAfin_iff, p] using hq
      · rfl
    exact hsubset hpair
  -- The fiber presentation is exactly the defining witness for membership in `A`.
  exact (mem_relativeAssassin_iff_fiber (R := R) (S := S) (N := N) q).2 <|
    by simpa [p] using hfiber

/-- Lemma 10.65.1 (2b): `B_fin` is contained in `B`. -/
-- Proof sketch: this is immediate from the definitions because every finite `R`-module is in
-- particular an `R`-module.
theorem relativeAssassinBfin_subset_relativeAssassinB :
    relativeAssassinBfin.{u, v, w, x} R S N ⊆ relativeAssassinB.{u, v, w, x} R S N := by
  rintro q ⟨M, instAdd, instModule, instFinite, hq⟩
  -- Forget only the finiteness hypothesis and keep the same tensor witness.
  exact ⟨M, instAdd, instModule, hq⟩

/-- Lemma 10.65.1 (2c): `A_fin` is contained in `A'_fin`. -/
-- Proof sketch: forget the contraction information encoded in the definition of `A_fin`.
theorem relativeAssassinAfin_subset_relativeAssassinAprimeFin :
    relativeAssassinAfin R S N ⊆ relativeAssassinAprimeFin R S N := by
  intro q hq
  -- Keep the same quotient witness and forget only that it was forced to be `q ∩ R`.
  refine ⟨PrimeSpectrum.comap (algebraMap R S) q, ?_⟩
  simpa [mem_relativeAssassinAfin_iff, PrimeSpectrum.comap_asIdeal] using hq

/-- Lemma 10.65.1 (2d): `A'_fin` is contained in `B_fin`. -/
-- Proof sketch: if `q` is associated to `N / pN`, then take the finite module `R ⧸ p`; the module
-- `N / pN` is the corresponding tensor product, so `q` lies in `B_fin`.
theorem relativeAssassinAprimeFin_subset_relativeAssassinBfin :
    relativeAssassinAprimeFin R S N ⊆ relativeAssassinBfin.{u, v, w, x} R S N := by
  intro q hq
  rcases hq with ⟨p, hp⟩
  refine ⟨ULift.{max v w x, u} (R ⧸ p.asIdeal), inferInstance, inferInstance, inferInstance, ?_⟩
  -- Rewrite the quotient-module witness through the canonical quotient/tensor comparison.
  have heq :
      associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) =
        associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) :=
    LinearEquiv.associatedPrimesOfModule_eq S
      (relativeAssassinPrimeQuotient R S N p.asIdeal)
      (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
        (R := R) (S := S) (N := N) p.asIdeal)
  rw [LinearEquiv.associatedPrimesOfModule_eq S
    (N ⊗[R] ULift.{max v w x, u} (R ⧸ p.asIdeal))
    (tensor_right_ulift_linearEquiv (R := R) (S := S) (N := N)
      (M := R ⧸ p.asIdeal))]
  exact heq ▸ hp

/-- Lemma 10.65.1 (2e): `A` is contained in `B`. -/
-- Proof sketch: each residue field `κ(p)` is an `R`-module, so any associated prime coming from
-- `N ⊗[R] κ(p)` contributes directly to the defining union for `B`.
theorem relativeAssassinA_subset_relativeAssassinB :
    relativeAssassin R S N ⊆ relativeAssassinB.{u, v, w, x} R S N := by
  intro q hq
  -- Reuse the same fiber module from the definition of `A` as the existential witness for `B`.
  refine ⟨ULift.{max v w x, u} ((q.asIdeal.under R).ResidueField), inferInstance, inferInstance, ?_⟩
  rw [LinearEquiv.associatedPrimesOfModule_eq S
    (N ⊗[R] ULift.{max v w x, u} ((q.asIdeal.under R).ResidueField))
    (tensor_right_ulift_linearEquiv (R := R) (S := S) (N := N)
      (M := (q.asIdeal.under R).ResidueField))]
  simpa [mem_relativeAssassin_iff] using hq

/-- Helper for Lemma 10.65.1: over a Noetherian `S`, the associated primes of `N / pN` whose
contraction to `R` is `p` are exactly the associated primes of the fiber module. -/
private theorem
    associatedPrimesOfModule_relativeAssassinPrimeQuotient_inter_under_eq_eq_fiberTensor_of_isNoetherian
    (p : Ideal R) [p.IsPrime] [IsNoetherianRing S] :
    associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) ∩
      { q : Ideal S | q.under R = p } =
        associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
  refine Set.Subset.antisymm
    (associatedPrimesOfModule_relativeAssassinPrimeQuotient_inter_under_eq_subset_fiberTensor
      (R := R) (S := S) (N := N) (p := p)) ?_
  intro q hq
  let qSpec : PrimeSpectrum S := ⟨q, hq.1⟩
  have hunder : q.under R = p := by
    have hqSpec :
        qSpec.asIdeal ∈ associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
      simpa [qSpec] using hq
    -- Read the contraction directly from the fiber-spectrum point lying over `p`.
    rcases (mem_associatedPrimesOfModule_fiberTensor_iff
      (R := R) (S := S) (N := N) (p := p) qSpec).1 hqSpec with ⟨q', hq', hqq'⟩
    have hqIdeal :
        q = Ideal.comap (algebraMap S (p.Fiber S)) q'.asIdeal := by
      simpa [qSpec, PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hqq').symm
    have hqover : q'.asIdeal.LiesOver p := inferInstance
    have hunder' :
        Ideal.comap (algebraMap R (p.Fiber S)) q'.asIdeal = p := by
      simpa [Ideal.under_def] using hqover.over.symm
    rw [Ideal.under_def, hqIdeal, Ideal.comap_comap]
    simpa [IsScalarTower.algebraMap_eq R S (p.Fiber S)] using hunder'
  let I : Ideal S := p.map (algebraMap R S)
  have hqbar_mem :
      q ∈ Ideal.comap (Ideal.Quotient.mk I) ''
        associatedPrimesOfModule (S ⧸ I) ((p.Fiber S) ⊗[S] N) := by
    rw [associatedPrimesOfModule_quotient_image_comap_eq
      (R := S) (I := I) (M := ((p.Fiber S) ⊗[S] N))]
    exact hq
  rcases hqbar_mem with ⟨qbar, hqbar, hcomap⟩
  have hloc :
      qbar ∈ associatedPrimesOfModule (S ⧸ I)
        (LocalizedModule (Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p)))
          (relativeAssassinPrimeQuotient R S N p)) := by
    -- Transport the fiber witness back through the fixed-prime localization equivalence.
    rw [← LinearEquiv.associatedPrimesOfModule_eq (S ⧸ I)
      (LocalizedModule (Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p)))
        (relativeAssassinPrimeQuotient R S N p))
      (localized_relativeAssassinPrimeQuotient_linearEquiv_fiberTensor
        (R := R) (S := S) (N := N) (p := p))] at hqbar
    exact hqbar
  have hpair :
      qbar ∈ associatedPrimesOfModule (S ⧸ I) (relativeAssassinPrimeQuotient R S N p) ∩
        { q : Ideal (S ⧸ I) |
            Disjoint
              ((Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p))) : Set (S ⧸ I))
              (q : Set (S ⧸ I)) } := by
    -- The Noetherian localization theorem identifies the localized module with the disjoint
    -- associated primes of the quotient module.
    rw [associatedPrimesOfModule_inter_disjoint_eq_localizedModule
      (R := S ⧸ I)
      (S := Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p)))
      (M := relativeAssassinPrimeQuotient R S N p)]
    exact hloc
  refine ⟨?_, hunder⟩
  -- Contract the quotient-level associated prime back to `S`.
  rw [← associatedPrimesOfModule_quotient_image_comap_eq
    (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p)]
  exact ⟨qbar, hpair.1, hcomap⟩

/-- Lemma 10.65.1 (3a): if `S` is Noetherian, then `A = A_fin`. -/
-- Proof sketch: apply the Noetherian form of the localization comparison for associated primes to
-- `N / (R ∩ q)N`, identifying the associated primes of `N ⊗[R] κ(R ∩ q)` with those associated
-- primes of the quotient module lying over the contracted prime.
theorem relativeAssassinA_eq_relativeAssassinAfin_of_isNoetherianRing [IsNoetherianRing S] :
    relativeAssassin R S N = relativeAssassinAfin R S N := by
  apply Set.Subset.antisymm
  · intro q hq
    let p : Ideal R := q.asIdeal.under R
    letI : p.IsPrime := Ideal.IsPrime.under (A := R) q.asIdeal
    have hfiber :
        q.asIdeal ∈ associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
      simpa [p] using (mem_relativeAssassin_iff_fiber (R := R) (S := S) (N := N) q).1 hq
    have hpair :
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) ∩
          { q : Ideal S | q.under R = p } := by
      -- Rewrite the fiber witness through the fixed-prime Noetherian equality.
      rw [associatedPrimesOfModule_relativeAssassinPrimeQuotient_inter_under_eq_eq_fiberTensor_of_isNoetherian
        (R := R) (S := S) (N := N) (p := p)]
      exact hfiber
    simpa [mem_relativeAssassinAfin_iff, p] using hpair.1
  · exact relativeAssassinAfin_subset_relativeAssassinA (R := R) (S := S) (N := N)

/-- Helper for Lemma 10.65.1: if a tensor in `N ⊗[R] M'` dies after mapping to `N ⊗[R] M` and
`M'` is finitely generated, then it already dies after enlarging `M'` to a finite submodule of
`M`. -/
private theorem tensor_zero_stabilizes_on_one_finite_stage
    {M : Type x} [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hM' : M'.FG) (z : N ⊗[R] M')
    (hz : TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype z = 0) :
    ∃ (M'' : Submodule R M) (hMM'' : M' ≤ M''), M''.FG ∧
      TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hMM'') z = 0 := by
  let zcomm : M' ⊗[R] N := TensorProduct.comm R N M' z
  have hzcomm :
      LinearMap.rTensor N M'.subtype zcomm = 0 := by
    -- Commute the tensor factors so the direct-limit theorem applies on the left factor.
    rw [show LinearMap.rTensor N M'.subtype zcomm =
      TensorProduct.comm R N M (TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype z) by
        simpa [zcomm] using LinearMap.rTensor_comm (N := N) (f := M'.subtype) z]
    simp [hz]
  obtain ⟨M'', hMM'', hM''fg, hzcomm''⟩ :=
    TensorProduct.eq_zero_of_fg_of_subtype_eq_zero
      (R := R) (M := M) (N := N) (P := M') hM' (t := zcomm) hzcomm
  refine ⟨M'', hMM'', hM''fg, ?_⟩
  have hz'' :
      TensorProduct.comm R N M''
        (TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hMM'') z) = 0 := by
    rw [show TensorProduct.comm R N M''
      (TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hMM'') z) =
        LinearMap.rTensor N (Submodule.inclusion hMM'') zcomm by
          symm
          simpa [zcomm] using LinearMap.rTensor_comm (N := N) (f := Submodule.inclusion hMM'') z]
    exact hzcomm''
  exact (TensorProduct.comm R N M'').injective hz''

/-- Helper for Lemma 10.65.1: finitely many zero relations in `N ⊗[R] M` already vanish after
passing to one finite submodule stage. -/
private theorem tensor_zero_stabilizes_on_finite_stage
    {ι : Type*} [Finite ι] {M : Type x} [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hM' : M'.FG) (z : ι → N ⊗[R] M')
    (hz : ∀ i, TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype (z i) = 0) :
    ∃ (M'' : Submodule R M) (hMM'' : M' ≤ M''), M''.FG ∧
      ∀ i, TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hMM'') (z i) = 0 := by
  classical
  choose Q hQle hQfg hQzero using
    fun i ↦ tensor_zero_stabilizes_on_one_finite_stage
      (R := R) (S := S) (N := N) (M := M) (M' := M') hM' (z i) (hz i)
  let M'' : Submodule R M := M' ⊔ iSup Q
  refine ⟨M'', le_sup_left, hM'.sup (Submodule.fg_iSup Q hQfg), ?_⟩
  intro i
  let hQi : Q i ≤ M'' := le_sup_of_le_right (le_iSup Q i)
  have hzero_i' :
      LinearMap.lTensor N (Submodule.inclusion hQi)
        ((LinearMap.lTensor N (Submodule.inclusion (hQle i))) (z i)) = 0 := by
    -- First kill the tensor in the chosen finite stage `Q i`, then map that zero relation forward
    -- to the common finite stage `M''`.
    simpa using congrArg (LinearMap.lTensor N (Submodule.inclusion hQi)) (hQzero i)
  have hzero_i :
      LinearMap.lTensor N (Submodule.inclusion (le_trans (hQle i) hQi)) (z i) = 0 := by
    have hcomp :
        LinearMap.lTensor N (Submodule.inclusion (le_trans (hQle i) hQi)) (z i) =
          LinearMap.lTensor N (Submodule.inclusion hQi)
            ((LinearMap.lTensor N (Submodule.inclusion (hQle i))) (z i)) := by
      simpa using
        (LinearMap.lTensor_comp_apply (M := N)
          (f := Submodule.inclusion (hQle i)) (g := Submodule.inclusion hQi) (x := z i))
    exact hcomp.trans hzero_i'
  simpa [M''] using hzero_i

/-- Helper for Lemma 10.65.1: over a Noetherian `S`, every associated-prime witness in
`N ⊗[R] M` descends to a finite `R`-submodule of `M`. -/
private theorem exists_finite_submodule_tensor_witness_same_annihilator_of_isNoetherian
    [IsNoetherianRing S] {M : Type x} [AddCommGroup M] [Module R M] {q : Ideal S}
    (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    ∃ (M' : Submodule R M) (_ : Module.Finite R M'),
      q ∈ associatedPrimesOfModule S (N ⊗[R] M') := by
  classical
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
  rcases hq with ⟨hqPrime, z, hz⟩
  obtain ⟨M₀, hM₀finite, z₀, hz₀⟩ :=
    exists_finite_submodule_tensor_preimage (R := R) (S := S) (N := N) z
  rcases q.fg_of_isNoetherianRing with ⟨gens, hgens⟩
  let rels : gens → N ⊗[R] M₀ := fun i ↦ i.1 • z₀
  have hrels_zero :
      ∀ i : gens,
        TensorProduct.AlgebraTensorModule.lTensor S N M₀.subtype (rels i) = 0 := by
    intro i
    -- Each chosen generator of `q` kills the original witness `z`, hence also the finite-stage
    -- representative after passing to a large enough finite stage.
    have hi_mem_q : i.1 ∈ q := by
      rw [← hgens]
      exact Ideal.subset_span i.2
    have hsmul_zero_z : i.1 • z = 0 := by
      simpa [hz, Ideal.mem_torsionOf_iff] using hi_mem_q
    simpa [rels, hz₀, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmul_zero_z
  obtain ⟨M₁, hM₀₁, hM₁fg, hrels₁⟩ :=
    tensor_zero_stabilizes_on_finite_stage
      (R := R) (S := S) (N := N) (M := M) (M' := M₀)
      (Module.Finite.iff_fg.mp hM₀finite) rels hrels_zero
  let z₁ : N ⊗[R] M₁ :=
    TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hM₀₁) z₀
  let inclusionTensor : N ⊗[R] M₁ →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N M₁.subtype
  have hz₁_image : inclusionTensor z₁ = z := by
    -- The descended tensor still maps to the original witness in `N ⊗[R] M`.
    rw [show inclusionTensor z₁ =
      LinearMap.lTensor N M₁.subtype ((LinearMap.lTensor N (Submodule.inclusion hM₀₁)) z₀) by rfl]
    rw [← LinearMap.lTensor_comp_apply]
    simpa [z₁, inclusionTensor, hz₀, Submodule.subtype_comp_inclusion]
  have hgens_le_torsion :
      Ideal.span (gens : Set S) ≤ Ideal.torsionOf S (N ⊗[R] M₁) z₁ := by
    refine Ideal.span_le.mpr ?_
    intro s hs
    let i : gens := ⟨s, hs⟩
    have hi_zero :
        TensorProduct.AlgebraTensorModule.lTensor S N (Submodule.inclusion hM₀₁) (rels i) = 0 :=
      hrels₁ i
    have hs_zero : s • z₁ = 0 := by
      simpa [rels, z₁, i] using hi_zero
    simpa [Ideal.mem_torsionOf_iff] using hs_zero
  have htorsion_le_q :
      Ideal.torsionOf S (N ⊗[R] M₁) z₁ ≤ q := by
    intro s hs
    have hs_zero : s • z₁ = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using hs
    have hs_zero_image : s • z = 0 := by
      simpa [hz₁_image] using congrArg inclusionTensor hs_zero
    simpa [hz, Ideal.mem_torsionOf_iff] using hs_zero_image
  refine ⟨M₁, Module.Finite.iff_fg.mpr hM₁fg, ?_⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
  refine ⟨hqPrime, z₁, le_antisymm ?_ htorsion_le_q⟩
  simpa [hgens] using hgens_le_torsion

/-- Lemma 10.65.1 (3b): if `S` is Noetherian, then `B = B_fin`. -/
-- Proof sketch: start from an associated prime of `N ⊗[R] M`, choose an element with that prime
-- annihilator, and then descend that witness to a finite `R`-submodule by stabilizing finitely
-- many generator relations of the annihilator ideal.
theorem relativeAssassinB_eq_relativeAssassinBfin_of_isNoetherianRing [IsNoetherianRing S] :
    relativeAssassinB.{u, v, w, x} R S N = relativeAssassinBfin.{u, v, w, x} R S N := by
  apply Set.Subset.antisymm
  · intro q hq
    rcases hq with ⟨M, instAdd, instModule, hq⟩
    obtain ⟨M', hM'finite, hq'⟩ :=
      exists_finite_submodule_tensor_witness_same_annihilator_of_isNoetherian
        (R := R) (S := S) (N := N) hq
    -- The descended finite submodule is exactly the finite witness required by `B_fin`.
    exact ⟨M', inferInstance, inferInstance, hM'finite, hq'⟩
  · exact relativeAssassinBfin_subset_relativeAssassinB (R := R) (S := S) (N := N)

/-- Helper for Lemma 10.65.1: if `r ∉ p`, then its image in `S / pS` is regular on `N / pN`
when `N` is flat over `R`. -/
private theorem isSMulRegular_relativeAssassinPrimeQuotient_quotientMap_of_not_mem
    [Module.Flat R N] {p : Ideal R} [p.IsPrime] {r : R} (hr : r ∉ p) :
    IsSMulRegular
      (relativeAssassinPrimeQuotient R S N p)
      (algebraMap R (S ⧸ p.map (algebraMap R S)) r) := by
  have hrbar_ne_zero : (Ideal.Quotient.mk p r : R ⧸ p) ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hr
  have hrbar_nz :
      (Ideal.Quotient.mk p r : R ⧸ p) ∈ nonZeroDivisors (R ⧸ p) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hrbar_ne_zero
  let _ : Module.Flat (R ⧸ p) ((R ⧸ p) ⊗[R] N) :=
    Module.Flat.baseChange (R := R) (S := R ⧸ p) (M := N)
  have hreg_left_bar :
      IsSMulRegular ((R ⧸ p) ⊗[R] N) (Ideal.Quotient.mk p r : R ⧸ p) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hrbar_nz
  have hreg_left :
      IsSMulRegular ((R ⧸ p) ⊗[R] N) r :=
    hreg_left_bar.of_map (Ideal.Quotient.mk p) fun _ ↦ rfl
  have hreg_tensor :
      IsSMulRegular (N ⊗[R] (R ⧸ p)) r := by
    -- Commute the two tensor factors before comparing with `N / pN`.
    exact ((TensorProduct.comm R (R ⧸ p) N).isSMulRegular_congr r).1 hreg_left
  have hreg_quot_R :
      IsSMulRegular (relativeAssassinPrimeQuotient R S N p) r := by
    -- Read regularity on `N / pN` through the canonical tensor model `N ⊗[R] (R / p)`.
    exact
      ((LinearEquiv.restrictScalars R
        (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
          (R := R) (S := S) (N := N) p)).isSMulRegular_congr r).2 hreg_tensor
  -- Convert the regular `R`-action to the corresponding scalar in the quotient ring `S / pS`.
  exact
    (isSMulRegular_algebraMap_iff
      (A := S ⧸ p.map (algebraMap R S))
      (M := relativeAssassinPrimeQuotient R S N p)
      (r := r)).2 hreg_quot_R

/-- Helper for Lemma 10.65.1: flatness identifies the associated primes of `N / pN` over
`S / pS` with those of its localization at the image of the nonzerodivisors of `R / p`. -/
private theorem associatedPrimesOfModule_relativeAssassinPrimeQuotient_over_quotient_eq_localized_of_flat
    [Module.Flat R N] (p : Ideal R) [p.IsPrime] :
    associatedPrimesOfModule (S ⧸ p.map (algebraMap R S))
        (relativeAssassinPrimeQuotient R S N p) =
      associatedPrimesOfModule (S ⧸ p.map (algebraMap R S))
        (LocalizedModule
          (Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S))
            (nonZeroDivisors (R ⧸ p)))
          (relativeAssassinPrimeQuotient R S N p)) := by
  refine associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule
    (Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S)) (nonZeroDivisors (R ⧸ p))) ?_
  intro t
  rcases t.2 with ⟨rbar, hrbar, ht⟩
  obtain ⟨r, hrfl⟩ := Ideal.Quotient.mk_surjective rbar
  have hr_not_mem : r ∉ p := by
    intro hr_mem
    exact nonZeroDivisors.ne_zero hrbar <| by
      rw [← hrfl, Ideal.Quotient.eq_zero_iff_mem]
      exact hr_mem
  -- Every element of the image submonoid comes from a numerator outside `p`, and the previous
  -- regularity lemma applies exactly to those numerators.
  have ht' : algebraMap R (S ⧸ p.map (algebraMap R S)) r = t := by
    calc
      algebraMap R (S ⧸ p.map (algebraMap R S)) r =
          algebraMap (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk p r) := by
            rfl
      _ = algebraMap (R ⧸ p) (S ⧸ p.map (algebraMap R S)) rbar := by
            simpa [hrfl]
      _ = t := ht
  simpa [ht'] using
    (isSMulRegular_relativeAssassinPrimeQuotient_quotientMap_of_not_mem
      (R := R) (S := S) (N := N) (p := p) hr_not_mem)

/-- Helper for Lemma 10.65.1: for a flat `R`-module `N`, the associated primes of `N / pN`
agree with those of the fiber module `N ⊗[R] κ(p)` over `S`. -/
private theorem associatedPrimesOfModule_relativeAssassinPrimeQuotient_eq_fiberTensor_of_flat
    [Module.Flat R N] (p : Ideal R) [p.IsPrime] :
    associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) =
      associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
  let I : Ideal S := p.map (algebraMap R S)
  -- Route correction: prove the equality first over `S / pS`, then transport it back to `S`.
  calc
    associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) =
        Ideal.comap (Ideal.Quotient.mk I) ''
          associatedPrimesOfModule (S ⧸ I) (relativeAssassinPrimeQuotient R S N p) := by
          symm
          simpa using
            (associatedPrimesOfModule_quotient_image_comap_eq
              (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p))
    _ =
        Ideal.comap (Ideal.Quotient.mk I) ''
          associatedPrimesOfModule (S ⧸ I)
            (LocalizedModule
              (Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p)))
              (relativeAssassinPrimeQuotient R S N p)) := by
          rw [associatedPrimesOfModule_relativeAssassinPrimeQuotient_over_quotient_eq_localized_of_flat
            (R := R) (S := S) (N := N) (p := p)]
    _ =
        Ideal.comap (Ideal.Quotient.mk I) '' associatedPrimesOfModule (S ⧸ I) ((p.Fiber S) ⊗[S] N) := by
          rw [LinearEquiv.associatedPrimesOfModule_eq (S ⧸ I)
            (LocalizedModule
              (Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p)))
              (relativeAssassinPrimeQuotient R S N p))
            (localized_relativeAssassinPrimeQuotient_linearEquiv_fiberTensor
              (R := R) (S := S) (N := N) (p := p))]
    _ =
        Ideal.comap (Ideal.Quotient.mk I) ''
          (Ideal.comap (algebraMap (S ⧸ I) (p.Fiber S)) ''
            associatedPrimesOfModule (p.Fiber S) ((p.Fiber S) ⊗[S] N)) := by
          rw [(associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber
            (R := R) (S := S) (N := N) (p := p)).symm]
    _ = associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
          rw [associatedPrimesOfModule_fiberTensor_eq_image_comap (R := R) (S := S) (N := N) (p := p)]
          ext q
          constructor
          · rintro ⟨qbar, ⟨q', hq', rfl⟩, hqbar⟩
            exact ⟨q', hq', by simpa [Ideal.comap_comap] using hqbar⟩
          · rintro ⟨q', hq_mem, hq_eq⟩
            refine ⟨Ideal.comap (algebraMap (S ⧸ I) (p.Fiber S)) q', ?_, ?_⟩
            · exact ⟨q', hq_mem, rfl⟩
            · simpa [Ideal.comap_comap] using hq_eq

/-- Lemma 10.65.1 (4a): if `N` is flat over `R`, then `A = A_fin`. -/
-- Proof sketch: flatness makes tensoring exact, so associated primes of `N ⊗[R] κ(p)` come from
-- associated primes of `N / pN`; combine this with the contraction equality from flatness.
theorem relativeAssassinA_eq_relativeAssassinAfin_of_flat [Module.Flat R N] :
    relativeAssassin R S N = relativeAssassinAfin R S N := by
  apply Set.Subset.antisymm
  · intro q hq
    let p : Ideal R := q.asIdeal.under R
    letI : p.IsPrime := Ideal.IsPrime.under (A := R) q.asIdeal
    have hfiber :
        q.asIdeal ∈ associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) := by
      simpa [p] using (mem_relativeAssassin_iff_fiber (R := R) (S := S) (N := N) q).1 hq
    have hquot :
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
      rw [associatedPrimesOfModule_relativeAssassinPrimeQuotient_eq_fiberTensor_of_flat
        (R := R) (S := S) (N := N) (p := p)]
      exact hfiber
    -- The fixed-prime equality rewrites the fiber witness into the defining witness for `A_fin`.
    simpa [mem_relativeAssassinAfin_iff, p] using hquot
  · exact relativeAssassinAfin_subset_relativeAssassinA (R := R) (S := S) (N := N)

/-- Helper for Lemma 10.65.1: for a flat `R`-module `N`, an associated prime of `N / pN` over `S`
contracts back to the fixed prime `p`. -/
private theorem under_eq_of_mem_associatedPrimes_relativeAssassinPrimeQuotient_of_flat
    [Module.Flat R N] {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hq : q.asIdeal ∈ associatedPrimesOfModule S
      (relativeAssassinPrimeQuotient R S N p.asIdeal)) :
    q.asIdeal.under R = p.asIdeal := by
  let I : Ideal S := p.asIdeal.map (algebraMap R S)
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
  rcases hq with ⟨hqPrime, m, hm⟩
  have hp_le : p.asIdeal ≤ q.asIdeal.under R := by
    have hqbar_mem :
        q.asIdeal ∈ Ideal.comap (Ideal.Quotient.mk I) ''
          associatedPrimesOfModule (S ⧸ I)
            (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
      -- The quotient presentation records that every associated prime of `N / pN` contains `pS`.
      rw [associatedPrimesOfModule_quotient_image_comap_eq
        (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p.asIdeal)]
      exact ⟨hqPrime, m, hm⟩
    rcases hqbar_mem with ⟨qbar, hqbar, hcomap⟩
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap]
    rw [← hcomap, Ideal.mem_comap]
    have hzero : Ideal.Quotient.mk I (algebraMap R S r) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    simpa [hzero] using (show (0 : S ⧸ I) ∈ qbar by simp)
  have hunder_le : q.asIdeal.under R ≤ p.asIdeal := by
    intro r hr
    by_contra hr_not_mem
    have hrbar_ne_zero : (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hr_not_mem
    have hrbar_nz :
        (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ∈ nonZeroDivisors (R ⧸ p.asIdeal) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hrbar_ne_zero
    let _ : Module.Flat (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] N) :=
      Module.Flat.baseChange (R := R) (S := R ⧸ p.asIdeal) (M := N)
    have hreg_left_bar :
        IsSMulRegular
          ((R ⧸ p.asIdeal) ⊗[R] N) (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hrbar_nz
    have hreg_left :
        IsSMulRegular ((R ⧸ p.asIdeal) ⊗[R] N) r :=
      hreg_left_bar.of_map (Ideal.Quotient.mk p.asIdeal) fun _ ↦ rfl
    have hreg_tensor :
        IsSMulRegular (N ⊗[R] (R ⧸ p.asIdeal)) r := by
      -- Move to the tensor model used elsewhere in the file before comparing with `N / pN`.
      exact ((TensorProduct.comm R (R ⧸ p.asIdeal) N).isSMulRegular_congr r).1 hreg_left
    have hreg_quot :
        IsSMulRegular (relativeAssassinPrimeQuotient R S N p.asIdeal) r := by
      -- Route correction: read regularity on `N / pN` through the textbook tensor model
      -- `N ⊗[R] (R ⧸ p)` before using the associated-prime witness.
      exact
        ((LinearEquiv.restrictScalars R
          (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
            (R := R) (S := S) (N := N) p.asIdeal)).isSMulRegular_congr r).2 hreg_tensor
    have hr_torsion :
        algebraMap R S r ∈ Ideal.torsionOf S
          (relativeAssassinPrimeQuotient R S N p.asIdeal) m := by
      simpa [Ideal.under_def, hm] using hr
    have hsmul_zero : (algebraMap R S r) • m = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using hr_torsion
    have hm_zero : m = 0 := hreg_quot <| by
      simpa using hsmul_zero
    have htop : q.asIdeal = ⊤ := by
      rw [hm, hm_zero, Ideal.torsionOf_zero]
    exact hqPrime.ne_top htop
  exact le_antisymm hunder_le hp_le

/-- Lemma 10.65.1 (4b): if `N` is flat over `R`, then `A_fin = A'_fin`. -/
-- Proof sketch: if `q` is associated to `N / pN`, flatness over the domain `R / p` shows that no
-- nonzero element of `R / p` can land in `q`, so the contraction of `q` to `R` is exactly `p`.
theorem relativeAssassinAfin_eq_relativeAssassinAprimeFin_of_flat [Module.Flat R N] :
    relativeAssassinAfin R S N = relativeAssassinAprimeFin R S N := by
  apply Set.Subset.antisymm
  · exact relativeAssassinAfin_subset_relativeAssassinAprimeFin (R := R) (S := S) (N := N)
  · intro q hq
    rcases hq with ⟨p, hp⟩
    have hunder :
        q.asIdeal.under R = p.asIdeal :=
      under_eq_of_mem_associatedPrimes_relativeAssassinPrimeQuotient_of_flat
        (R := R) (S := S) (N := N) hp
    -- The source proof closes here: once the contraction is forced to be `p`, the same witness
    -- is exactly the defining witness for `A_fin`.
    rw [mem_relativeAssassinAfin_iff, hunder]
    exact hp

/-- Lemma 10.65.1 (4c): if `N` is flat over `R`, then `B = B_fin`. -/
-- Proof sketch: exactness of `N ⊗[R] -` embeds `N ⊗[R] M'` into `N ⊗[R] M` for finite
-- submodules `M' ⊆ M`, so an element realizing an associated prime already lies in a finite
-- submodule without changing its annihilator.
theorem relativeAssassinB_eq_relativeAssassinBfin_of_flat [Module.Flat R N] :
    relativeAssassinB.{u, v, w, x} R S N = relativeAssassinBfin.{u, v, w, x} R S N := by
  apply Set.Subset.antisymm
  · intro q hq
    rcases hq with ⟨M, instAdd, instModule, hq⟩
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
    rcases hq with ⟨hqPrime, z, hz⟩
    obtain ⟨M', hM'finite, z', hz'⟩ :=
      exists_finite_submodule_tensor_preimage (R := R) (S := S) (N := N) z
    let inclusionTensor : N ⊗[R] M' →ₗ[S] N ⊗[R] M :=
      TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype
    have hinclusionTensor : Function.Injective inclusionTensor := by
      -- Flatness keeps the inclusion of the finite submodule injective after tensoring.
      simpa [inclusionTensor] using
        Module.Flat.lTensor_preserves_injective_linearMap (M := N) M'.subtype
          (Submodule.injective_subtype M')
    refine ⟨M', inferInstance, inferInstance, hM'finite, ?_⟩
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    refine ⟨hqPrime, z', ?_⟩
    -- The chosen witness already realizes the same annihilator inside the finite tensor stage.
    calc
      q.asIdeal = Ideal.torsionOf S (N ⊗[R] M) (inclusionTensor z') := by
        simpa [inclusionTensor, hz'] using hz
      _ = Ideal.torsionOf S (N ⊗[R] M') z' :=
        torsionOf_map_eq_of_injective (f := inclusionTensor) hinclusionTensor z'
  · exact relativeAssassinBfin_subset_relativeAssassinB (R := R) (S := S) (N := N)

/-- Helper for Lemma 10.65.1: after tensoring a prime-cyclic filtration with a flat module, every
associated prime of the final tensor stage comes from one prime-quotient factor. -/
private theorem associatedPrimesOfModule_tensorProduct_subset_primeFactorQuotients_of_filtration
    {M : Type x} [AddCommGroup M] [Module R M] [Module.Flat R N]
    (s : PrimeCyclicFiltration R M) (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule S (N ⊗[R] s.last) ⊆
      (⋃ p : PrimeSpectrum R, ⋃ _ : p ∈ PrimeCyclicFiltration.primeFactors (R := R) (M := M) s,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal)) := by
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton K =>
      intro hs₀ q hq
      have hK : K = ⊥ := hs₀
      subst hK
      -- The initial filtration stage is zero, so no associated-prime witness can live there.
      change q ∈ associatedPrimesOfModule S (N ⊗[R] (⊥ : Submodule R M)) at hq
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
      rcases hq with ⟨hqPrime, z, hz⟩
      letI : Subsingleton (N ⊗[R] (⊥ : Submodule R M)) := inferInstance
      have hz_zero : z = 0 := Subsingleton.elim _ _
      have htop : q = ⊤ := by
        rw [hz, hz_zero, Ideal.torsionOf_zero]
      exact (hqPrime.ne_top htop).elim
  | snoc s K hrel ih =>
      rcases hrel with ⟨hle, p, hp⟩
      have hp_nonempty := hp
      intro hs₀ q hq
      let f : N ⊗[R] (s.last.submoduleOf K) →ₗ[S] N ⊗[R] K :=
        TensorProduct.AlgebraTensorModule.lTensor S N (s.last.submoduleOf K).subtype
      let g : N ⊗[R] K →ₗ[S] N ⊗[R] (K ⧸ s.last.submoduleOf K) :=
        TensorProduct.AlgebraTensorModule.lTensor S N ((s.last.submoduleOf K).mkQ)
      have hf : Function.Injective f := by
        -- Flatness preserves injectivity of the previous filtration stage after tensoring.
        simpa [f] using
          Module.Flat.lTensor_preserves_injective_linearMap (M := N)
            (s.last.submoduleOf K).subtype
            (Submodule.injective_subtype (s.last.submoduleOf K))
      have hfg : Function.Exact f g := by
        -- The tensorized snoc step remains exact:
        -- `0 → N ⊗ s.last → N ⊗ K → N ⊗ (K / s.last)`.
        simpa [f, g] using
          (lTensor_exact N (LinearMap.exact_subtype_mkQ (s.last.submoduleOf K))
            (Submodule.mkQ_surjective (s.last.submoduleOf K)))
      have hsubset :
          associatedPrimesOfModule S (N ⊗[R] K) ⊆
            associatedPrimesOfModule S (N ⊗[R] (s.last.submoduleOf K)) ∪
              associatedPrimesOfModule S (N ⊗[R] (K ⧸ s.last.submoduleOf K)) :=
        associatedPrimesOfModule.subset_union_of_exact
          (R := S) (f := f) (g := g) hf hfg
      have hqK : q ∈ associatedPrimesOfModule S (N ⊗[R] K) := by
        rw [RelSeries.last_snoc] at hq
        exact hq
      rcases hsubset hqK with hq_prev | hq_last
      · have hq_prev_last : q ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
          simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := N ⊗[R] (s.last.submoduleOf K))
            (M' := N ⊗[R] s.last)
            (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N)
              (Submodule.submoduleOfEquivOfLe hle))] using hq_prev
        rcases Set.mem_iUnion.mp (ih hs₀ hq_prev_last) with ⟨p', hp'⟩
        rcases Set.mem_iUnion.mp hp' with ⟨hp'factor, hq'⟩
        exact Set.mem_iUnion.mpr ⟨p', Set.mem_iUnion.mpr
          ⟨PrimeCyclicFiltration.primeFactors_subset_snoc (s := s) ⟨hle, p, hp⟩ hp'factor, hq'⟩⟩
      · rcases hp with ⟨e⟩
        have hq_tensor_quotient :
            q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) := by
          -- Rewrite the final quotient stage through the prime-cyclic quotient isomorphism.
          simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := N ⊗[R] (K ⧸ s.last.submoduleOf K))
            (M' := N ⊗[R] (R ⧸ p.asIdeal))
            (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e)] using hq_last
        have hq_prime_quotient :
            q ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
          -- The source quotient factor is exactly the standard quotient module `N / pN`.
          rw [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := relativeAssassinPrimeQuotient R S N p.asIdeal)
            (M' := N ⊗[R] (R ⧸ p.asIdeal))
            (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
              (R := R) (S := S) (N := N) p.asIdeal)]
          exact hq_tensor_quotient
        exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
          ⟨PrimeCyclicFiltration.mem_primeFactors_snoc_last (s := s) hle hp_nonempty,
            hq_prime_quotient⟩⟩

/-- Helper for Lemma 10.65.1: in the Noetherian flat case, every finite witness in `B_fin`
already comes from some quotient module `N / pN`, hence lies in `A'_fin`. -/
private theorem relativeAssassinBfin_subset_relativeAssassinAprimeFin_of_isNoetherianRing_and_flat
    [IsNoetherianRing R] [Module.Flat R N] :
    relativeAssassinBfin.{u, v, w, x} R S N ⊆ relativeAssassinAprimeFin R S N := by
  intro q hq
  rcases hq with ⟨M, instAdd, instModule, hMfinite, hq⟩
  obtain ⟨s, hs₀, hs_top⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime (A := R) (M := M)
  let eTop : s.last ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ hs_top).trans Submodule.topEquiv
  have hq_last : q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
    -- Move the finite witness to the last stage of a prime-cyclic filtration of `M`.
    simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
      (M := N ⊗[R] s.last)
      (M' := N ⊗[R] M)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) eTop)] using hq
  rcases Set.mem_iUnion.mp
      (associatedPrimesOfModule_tensorProduct_subset_primeFactorQuotients_of_filtration
        (R := R) (S := S) (N := N) s hs₀ hq_last) with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨_hpFactor, hq'⟩
  exact ⟨p, hq'⟩

/-- Lemma 10.65.1 (5): if `R` is Noetherian and `N` is flat over `R`, then
`A = A' = A_fin = A'_fin = B = B_fin`. -/
-- Proof sketch: combine the flat equalities `A = A_fin = A'_fin` with the finite-filtration
-- inclusion `B_fin ⊆ A'_fin`, then rewrite `B` through the flat equality `B = B_fin`.
theorem relativeAssassin_all_eq_of_isNoetherianRing_and_flat
    [IsNoetherianRing R] [Module.Flat R N] :
    relativeAssassin R S N = relativeAssassinAprime R S N ∧
      relativeAssassin R S N = relativeAssassinAfin R S N ∧
      relativeAssassin R S N = relativeAssassinAprimeFin R S N ∧
      relativeAssassin R S N = relativeAssassinB.{u, v, w, x} R S N ∧
      relativeAssassin R S N = relativeAssassinBfin.{u, v, w, x} R S N := by
  have hAA' := relativeAssassinA_eq_relativeAssassinAprime (R := R) (S := S) (N := N)
  have hAAfin := relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)
  have hAfinA'fin :=
    relativeAssassinAfin_eq_relativeAssassinAprimeFin_of_flat (R := R) (S := S) (N := N)
  have hAA'fin : relativeAssassin R S N = relativeAssassinAprimeFin R S N := by
    calc
      relativeAssassin R S N = relativeAssassinAfin R S N := hAAfin
      _ = relativeAssassinAprimeFin R S N := hAfinA'fin
  refine ⟨hAA', ⟨hAAfin, ⟨hAA'fin, ?_, ?_⟩⟩⟩
  · ext q
    constructor
    · intro hq
      have hAprimeFin : q ∈ relativeAssassinAprimeFin R S N := by
        simpa [hAA'fin] using hq
      have hBfin : q ∈ relativeAssassinBfin R S N :=
        relativeAssassinAprimeFin_subset_relativeAssassinBfin (R := R) (S := S) (N := N) hAprimeFin
      rw [relativeAssassinB_eq_relativeAssassinBfin_of_flat (R := R) (S := S) (N := N)]
      exact hBfin
    · intro hq
      have hBfin : q ∈ relativeAssassinBfin R S N := by
        rw [← relativeAssassinB_eq_relativeAssassinBfin_of_flat (R := R) (S := S) (N := N)]
        exact hq
      have hAprimeFin : q ∈ relativeAssassinAprimeFin R S N :=
        relativeAssassinBfin_subset_relativeAssassinAprimeFin_of_isNoetherianRing_and_flat
          (R := R) (S := S) (N := N) hBfin
      simpa [hAA'fin] using hAprimeFin
  · ext q
    constructor
    · intro hq
      have hAprimeFin : q ∈ relativeAssassinAprimeFin R S N := by
        simpa [hAA'fin] using hq
      exact relativeAssassinAprimeFin_subset_relativeAssassinBfin (R := R) (S := S) (N := N) hAprimeFin
    · intro hq
      have hAprimeFin : q ∈ relativeAssassinAprimeFin R S N :=
        relativeAssassinBfin_subset_relativeAssassinAprimeFin_of_isNoetherianRing_and_flat
          (R := R) (S := S) (N := N) hq
      simpa [hAA'fin] using hAprimeFin

end
