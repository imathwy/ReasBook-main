import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_31_1 (from Chap10) -/
universe u v

/- Domain-style sampling for Lemma 10.31.1:
- primary domain: commutative algebra, specifically canonical Noetherianity transfer theorems for
  finite type algebras and localizations;
- inspected owner declarations:
  `Algebra.FiniteType.isNoetherianRing`,
  `IsLocalization.isNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`,
  `Ideal.fg_of_isNoetherianRing`;
- best owner abstraction: `IsNoetherianRing` as the ambient owner predicate, with the two transfer
  theorems above providing the canonical constructions used in the textbook clauses;
- primitive data: a finite type algebra structure or a localization structure over a Noetherian
  base ring;
- derived API: the induced `IsNoetherianRing` instance/property on the target ring.

Source/core/bridge triage:
- `source-facing`: the two textbook permanence statements for Noetherian rings;
- `core/canonical`: `Algebra.FiniteType.isNoetherianRing` and
  `IsLocalization.isNoetherianRing`;
- `bridge/view`: ideal-theoretic reformulations such as `isNoetherianRing_iff_ideal_fg` and
  `Ideal.fg_of_isNoetherianRing`. -/

section FiniteTypeCase

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A] [IsNoetherianRing R]

/- Lemma 10.31.1 (1) (Stacks tag `00FN`): any finite type algebra over a Noetherian ring is
Noetherian. This is the exact canonical theorem `Algebra.FiniteType.isNoetherianRing`. -/
#check (Algebra.FiniteType.isNoetherianRing R A : IsNoetherianRing A)

end FiniteTypeCase

section LocalizationCase

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Submonoid R} {S : Type v} [CommRing S] [Algebra R S] [IsLocalization M S]

/- Lemma 10.31.1 (2): any localization of a Noetherian ring is Noetherian. In mathlib this is the
canonical theorem `IsLocalization.isNoetherianRing`, stated more generally for localizations of
Noetherian commutative semirings. -/
recall IsLocalization.isNoetherianRing

end LocalizationCase

/-! ### Lemma_10_31_2 (from Chap10) -/
noncomputable section

universe u v

open Finset Finsupp
open scoped BigOperators PowerSeries

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

private noncomputable def mvPowerSeriesSumRingEquiv (R : Type u) [CommSemiring R] (σ τ : Type*) :
    MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun f := fun d e ↦ f (sumElim d e)
  invFun f := fun d ↦
    f
      (comapDomain Sum.inl d Sum.inl_injective.injOn)
      (comapDomain Sum.inr d Sum.inr_injective.injOn)
  left_inv f := by
    funext d
    simp [Finsupp.comapDomain_sumElim_comapDomain]
  right_inv f := by
    funext d
    funext e
    simp
  map_mul' f g := by
    classical
    funext d
    funext e
    let F : MvPowerSeries σ (MvPowerSeries τ R) := fun d e ↦ f (sumElim d e)
    let G : MvPowerSeries σ (MvPowerSeries τ R) := fun d e ↦ g (sumElim d e)
    have h :
        Finset.sum (antidiagonal (sumElim d e))
          (fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦ f p.1 * g p.2) =
        Finset.sum (antidiagonal d)
          (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
            Finset.sum (antidiagonal e)
              (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦ f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := by
      let split : ((σ →₀ ℕ) × (σ →₀ ℕ)) × ((τ →₀ ℕ) × (τ →₀ ℕ)) →
          (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) :=
        fun x ↦ (sumElim x.1.1 x.2.1, sumElim x.1.2 x.2.2)
      let unsplit : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) →
          ((σ →₀ ℕ) × (σ →₀ ℕ)) × ((τ →₀ ℕ) × (τ →₀ ℕ)) :=
        fun x ↦
          (( comapDomain Sum.inl x.1 Sum.inl_injective.injOn
           , comapDomain Sum.inl x.2 Sum.inl_injective.injOn)
          , ( comapDomain Sum.inr x.1 Sum.inr_injective.injOn
            , comapDomain Sum.inr x.2 Sum.inr_injective.injOn))
      have hleft : Function.LeftInverse unsplit split := by
        intro x
        rcases x with ⟨⟨x1, x2⟩, x3, x4⟩
        simp [split, unsplit, Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
      rw [← Finsupp.image_sumElim_product_antidiagonal]
      rw [Finset.sum_image hleft.injective.injOn]
      rw [Finset.sum_product]
    calc
      (f * g) (sumElim d e)
          = Finset.sum (antidiagonal (sumElim d e))
              (fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦ f p.1 * g p.2) := by
                simpa using MvPowerSeries.coeff_mul (sumElim d e) f g
      _ = Finset.sum (antidiagonal d)
            (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
              Finset.sum (antidiagonal e)
                (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦ f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := h
      _ = (F * G) d e := by
            calc
              Finset.sum (antidiagonal d)
                  (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
                    Finset.sum (antidiagonal e)
                      (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦ f (sumElim p.1 q.1) * g (sumElim p.2 q.2)))
                  = Finset.sum (antidiagonal d) (fun p ↦ (F p.1 * G p.2) e) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      simpa [F, G] using MvPowerSeries.coeff_mul e (F p.1) (G p.2)
              _ = (Finset.sum (antidiagonal d) (fun p ↦ F p.1 * G p.2)) e := by
                    exact (Finset.sum_apply e (antidiagonal d) fun p ↦ F p.1 * G p.2).symm
              _ = (F * G) d e := by
                    simpa using congrArg (fun s : MvPowerSeries τ R ↦ s e)
                      (MvPowerSeries.coeff_mul d F G)
  map_add' _ _ := by
    rfl

private noncomputable def optionToUnitSum (σ : Type*) : Option σ ≃ Unit ⊕ σ :=
  (Equiv.optionEquivSumPUnit σ).trans (Equiv.sumComm _ _)

private noncomputable def optionMvPowerSeriesRingEquiv (R : Type u) [CommSemiring R] (σ : Type*) :
    MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) :=
  (MvPowerSeries.renameEquiv R (optionToUnitSum σ)).toRingEquiv.trans
    (mvPowerSeriesSumRingEquiv R Unit σ)

private noncomputable def pemptyMvPowerSeriesRingEquiv (R : Type u) [CommSemiring R] :
    MvPowerSeries PEmpty R ≃+* R where
  toFun := MvPowerSeries.constantCoeff
  invFun := MvPowerSeries.C
  left_inv f := by
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    simp [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  right_inv r := by
    simp
  map_mul' _ _ := by simp
  map_add' _ _ := by simp

omit [IsNoetherianRing R] in
private theorem isNoetherianRing_mvPowerSeries_option (σ : Type*) [Fintype σ]
    [IsNoetherianRing (MvPowerSeries σ R)] :
    IsNoetherianRing (MvPowerSeries (Option σ) R) := by
  have : IsNoetherianRing (PowerSeries (MvPowerSeries σ R)) := by infer_instance
  exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries σ R))
    (optionMvPowerSeriesRingEquiv R σ).symm

private noncomputable def finZeroMvPowerSeriesRingEquiv (R : Type u) [CommSemiring R] :
    MvPowerSeries (Fin 0) R ≃+* R :=
  (MvPowerSeries.renameEquiv R (_root_.finZeroEquiv' : Fin 0 ≃ PEmpty.{1})).toRingEquiv.trans
    (pemptyMvPowerSeriesRingEquiv R)

private noncomputable def finSuccMvPowerSeriesRingEquiv (R : Type u) [CommSemiring R] (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  (MvPowerSeries.renameEquiv R (_root_.finSuccEquiv n)).toRingEquiv.trans
    (optionMvPowerSeriesRingEquiv R (Fin n))

private theorem isNoetherianRing_mvPowerSeries_fin :
    ∀ n : ℕ, IsNoetherianRing (MvPowerSeries (Fin n) R)
  | 0 =>
      isNoetherianRing_of_ringEquiv R (finZeroMvPowerSeriesRingEquiv R).symm
  | n + 1 =>
      @isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) R)) _ _ _
        (finSuccMvPowerSeriesRingEquiv R n).symm
        (by
          letI : IsNoetherianRing (MvPowerSeries (Fin n) R) :=
            isNoetherianRing_mvPowerSeries_fin n
          infer_instance)

/-- Lemma 10.31.2: if `R` is a Noetherian ring, then the formal power series ring
in finitely many variables over `R` is Noetherian. This is stated at the owner abstraction
`MvPowerSeries σ R` with `[Finite σ]`; the `Fin n` presentation is a specialization via
`MvPowerSeries.renameEquiv`. Internally, we follow the canonical finite-owner pattern from the
multivariate polynomial API: prove the `Fin n` case recursively and transport along
`Fintype.equivFin`. -/
instance mvPowerSeries_isNoetherianRing {σ : Type v} [Finite σ] :
    IsNoetherianRing (MvPowerSeries σ R) := by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) R) _ _ _
      (MvPowerSeries.renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv
      (isNoetherianRing_mvPowerSeries_fin _)

/-! ### Lemma_10_31_3 (from Chap10) -/
universe u v

section FieldCase

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/- Lemma 10.31.3 (field case; Stacks tag `00FO`): any finite type algebra over a field is
Noetherian. This is the field-specialized use of the owner theorem
`Algebra.FiniteType.isNoetherianRing`. -/
#check (Algebra.FiniteType.isNoetherianRing k A : IsNoetherianRing A)

end FieldCase

section IntCase

variable {A : Type u} [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]

/- Lemma 10.31.3 (`ℤ`-case): any finite type algebra over `ℤ` is Noetherian. This is the
`ℤ`-specialized use of the same owner theorem, with the base Noetherian hypothesis supplied by the
canonical instance on `ℤ`. -/
#check (Algebra.FiniteType.isNoetherianRing ℤ A : IsNoetherianRing A)

end IntCase

/-! ### Lemma_10_31_4 (from Chap10) -/
universe u v

section Modules

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

/- Lemma 10.31.4 (1): over a Noetherian ring, every finite `R`-module is finitely presented.
This is exactly the canonical theorem `Module.finitePresentation_of_finite`. -/
recall Module.finitePresentation_of_finite

variable (N : Submodule R M)

/- Lemma 10.31.4 (2): any submodule of a finite `R`-module is finite over a Noetherian ring.
The owner theorem is `isNoetherian_of_submodule_of_noetherian`; the source-facing finiteness
statement is its derived canonical instance consequence. -/
recall isNoetherian_of_submodule_of_noetherian
#check (inferInstance : Module.Finite R N)

end Modules

section Algebras

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [IsNoetherianRing R] [Algebra.FiniteType R A]

/- Lemma 10.31.4 (3): over a Noetherian ring, any finite type `R`-algebra is finitely presented
over `R`. This is the forward direction of the canonical theorem
`Algebra.FinitePresentation.of_finiteType`. -/
recall Algebra.FinitePresentation.of_finiteType

end Algebras

/-! ### Lemma_10_31_5 (from Chap10) -/
universe u

section

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/- Lemma 10.31.5: for the textbook case of a Noetherian ring, `Spec(R)` is a Noetherian
topological space in the sense of Topology, Definition 5.9.1. This is the canonical instance
`PrimeSpectrum.instNoetherianSpace`, which is available in mathlib under the weaker assumptions
`[CommSemiring R] [IsNoetherianRing R]`. -/
recall PrimeSpectrum.instNoetherianSpace

end

/-! ### Lemma_10_31_6 (from Chap10) -/
universe u

section

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/- Lemma 10.31.6: if `R` is a Noetherian ring, then `Spec(R)` has finitely many irreducible
components. Equivalently, `R` has finitely many minimal prime ideals by
`minimalPrimes.equivIrreducibleComponents` and `minimalPrimes.finite_of_isNoetherianRing`. This
is the canonical theorem `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` applied
to the canonical instance `PrimeSpectrum.instNoetherianSpace`, and both canonical ingredients are
already available under the weaker assumptions `[CommSemiring R] [IsNoetherianRing R]`. -/
recall TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

end

/-! ### Lemma_10_31_7 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [IsNoetherianRing S]
variable {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']
local notation "S'" => S ⊗[R] R'
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- Domain triage: this lemma lies in commutative algebra of finite-type base change and
-- Noetherianity. The owner abstraction is the `S`-algebra `S'`, obtained from
-- `Algebra.FiniteType.baseChange`; its Noetherianity is then a derived instance from
-- `Algebra.FiniteType.isNoetherianRing`. The displayed tensor order `R' ⊗[R] S` is only the
-- source-facing bridge/view, recovered from the owner object by `Algebra.TensorProduct.comm`.
/-- Lemma 10.31.7: if `R → R'` is of finite type and `S` is a Noetherian `R`-algebra, then the
base-changed ring `R' ⊗[R] S` is Noetherian. -/
theorem isNoetherianRing_baseChange :
    IsNoetherianRing (R' ⊗[R] S) := by
  let _ : Algebra.FiniteType S S' := inferInstance
  let _ : IsNoetherianRing S' := Algebra.FiniteType.isNoetherianRing S S'
  simpa using
    (isNoetherianRing_of_ringEquiv S' (Algebra.TensorProduct.comm R S R').toRingEquiv :
      IsNoetherianRing (R' ⊗[R] S))

end

/-! ### Lemma_10_31_8 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {R : Type w} [CommRing R] [Algebra k R] [IsNoetherianRing R]

-- Domain triage:
-- * source-facing: the textbook ring `K ⊗[k] R`
-- * core/canonical: `Algebra.EssFiniteType`, already fixed in Definition `9.6.6` as the owner
--   abstraction for finitely generated field extensions
-- * bridge/view: `Algebra.TensorProduct.comm k R K`
--
-- Proof sketch: base change makes `R ⊗[k] K` an essentially finite type `R`-algebra, so the
-- canonical theorem `Algebra.EssFiniteType.isNoetherianRing` makes the owner object Noetherian.
-- The textbook tensor order is then recovered by `TensorProduct.comm`.
/-- Lemma 10.31.8: if `k` is a field, `R` is a Noetherian `k`-algebra, and `K / k` is a finitely
generated field extension, then the textbook base change `K ⊗[k] R` is Noetherian. -/
theorem isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension :
    IsNoetherianRing (K ⊗[k] R) := by
  let _ : Algebra.EssFiniteType R (R ⊗[k] K) := inferInstance
  let _ : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  simpa using isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k R K).toRingEquiv

end

/-! ### Lemma_10_31_9 (from Chap10) -/
universe u

open Localization
open IsLocalRing
open scoped BigOperators

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p

private theorem awayElement_isUnit_atPrime (f : p.primeCompl) :
    IsUnit (algebraMap R Rₚ f.1) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff Rₚ p f.1).2 f.2

private theorem awayLift_injective_of_kernel_killed (f : p.primeCompl)
    (H : ∀ a, algebraMap R Rₚ a = 0 → ∃ n, f.1 ^ n * a = 0) :
    Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  letI : IsLocalization.Away (algebraMap R Rₚ f.1) Rₚ :=
    IsLocalization.away_of_isUnit_of_bijective Rₚ (awayElement_isUnit_atPrime p f)
      Function.bijective_id
  simpa [Localization.awayLift] using
    (show Function.Injective
        (IsLocalization.Away.map (Localization.Away f.1) Rₚ (algebraMap R Rₚ) f.1) by
      rw [IsLocalization.Away.map_injective_iff]
      exact H)

private theorem exists_injective_awayLift_atPrime_of_isNoetherianRing [IsNoetherianRing R] :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  classical
  have hfg : (RingHom.ker (algebraMap R Rₚ)).FG :=
    Ideal.FG.of_isNoetherianRing (RingHom.ker (algebraMap R Rₚ))
  rcases hfg with ⟨t, ht⟩
  have hx0 : ∀ x : t, ∃ s : p.primeCompl, s.1 * x.1 = 0 := by
    intro x
    have hxker : x.1 ∈ RingHom.ker (algebraMap R Rₚ) := by
      rw [← ht]
      exact Ideal.subset_span x.2
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rₚ x.1).mp <| by
      simpa [RingHom.mem_ker] using hxker
    exact ⟨s, hs⟩
  choose m hm using hx0
  let f : p.primeCompl := ⟨∏ x : t, (m x).1, by
    classical
    show (∏ x ∈ (Finset.univ : Finset t), (m x).1) ∈ p.primeCompl
    refine Finset.induction ?_ ?_ Finset.univ
    · simp
    · intro x s hx hs
      simpa [hx] using p.primeCompl.mul_mem (m x).2 hs⟩
  refine ⟨f, awayLift_injective_of_kernel_killed p f ?_⟩
  intro a ha
  have haK : a ∈ Ideal.span (t : Set R) := by
    rw [ht]
    exact ha
  have hf_mul : ∀ x : t, f.1 * x.1 = 0 := by
    intro x
    have hprod : f.1 = (m x).1 * ∏ y ∈ ({x}ᶜ : Set t), (m y).1 := by
      simpa [f] using Fintype.prod_eq_mul_prod_compl x (fun y : t ↦ (m y).1)
    calc
      f.1 * x.1 = ((m x).1 * ∏ y ∈ ({x}ᶜ : Set t), (m y).1) * x.1 := by rw [hprod]
      _ = (∏ y ∈ ({x}ᶜ : Set t), (m y).1) * ((m x).1 * x.1) := by ring
      _ = 0 := by simp [hm x]
  have hspan : ∀ b ∈ Ideal.span (t : Set R), f.1 * b = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | zero => simp
    | mem x hx => exact hf_mul ⟨x, hx⟩
    | add x y _ _ hx hy => simp [mul_add, hx, hy]
    | smul c x _ hx =>
        simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ c * z) hx
  exact ⟨1, by simpa using hspan a haK⟩

private theorem exists_injective_awayLift_atPrime_of_isReduced_finiteMinimalPrimes [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  classical
  let bad : Finset (Ideal R) := hfinite.toFinset.filter fun q ↦ ¬ q ≤ p
  let I : Ideal R := ∏ q ∈ bad, q
  have hI_not_le : ¬ I ≤ p := by
    intro hIp
    obtain ⟨q, hqbad, hqp⟩ :=
      (inferInstance : p.IsPrime).prod_le.mp (show (∏ q ∈ bad, q) ≤ p by simpa [I] using hIp)
    exact (Finset.mem_filter.mp hqbad).2 hqp
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp (show ¬ (I : Set R) ⊆ p by simpa using hI_not_le)
  let f' : p.primeCompl := ⟨f, hfp⟩
  refine ⟨f', awayLift_injective_of_kernel_killed p f' ?_⟩
  intro a ha
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rₚ a).mp ha
  have hfa : f * a ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    by_cases hqp : q ≤ p
    · have hsq : (s : R) ∉ q := fun hsq ↦ s.2 (hqp hsq)
      have hsa : s * a ∈ q := by simp [hs]
      have haq : a ∈ q := (Ideal.IsPrime.mem_or_mem inferInstance hsa).resolve_left hsq
      exact q.mul_mem_left f haq
    · have hqbad : q ∈ bad := Finset.mem_filter.mpr ⟨by simpa using hq, hqp⟩
      have hfq : f ∈ q := (Ideal.prod_le_inf.trans (Finset.inf_le hqbad)) hfI
      exact q.mul_mem_right a hfq
  have hsInf : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
    have hsInf' : sInf ((⊥ : Ideal R).minimalPrimes) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes
    have hrad : (⊥ : Ideal R).radical = (⊥ : Ideal R) := by
      simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R
    simpa [minimalPrimes] using hsInf'.trans hrad
  refine ⟨1, ?_⟩
  rw [pow_one, ← Ideal.mem_bot, ← hsInf]
  exact hfa

/-- Lemma 10.31.9: if `R` is Noetherian, or reduced with finitely many minimal primes, then there
exists `f ∉ p` such that the canonical map `R_f → R_𝔭` is injective. In mathlib, this map is the
canonical lift `Localization.awayLift` of `R → Localization.AtPrime p`, using that every `f ∉ p`
becomes a unit in `R_𝔭`. The domain case from the source is redundant here, since a domain is
reduced and has the unique minimal prime `(0)`. -/
-- Proof sketch: in the Noetherian case, kill the finitely generated kernel of `R → R_𝔭` after
-- localizing away from a suitable `f ∉ p`; the owner existence theorem for this step is
-- `Localization.exists_awayMap_injective_of_localRingHom_injective`. In the reduced case with
-- finitely many minimal primes, choose `f` in the product of the minimal primes not contained in
-- `p` but outside `p`; then any element of the kernel of `R → R_𝔭` is annihilated by `f`, since
-- it already vanishes at the minimal primes contained in `p` and `f` vanishes at the others.
theorem exists_injective_awayMap_atPrime_of_noetherian_or_reduced_finiteMinimalPrimes
    (h : IsNoetherianRing R ∨ (IsReduced R ∧ (minimalPrimes R).Finite)) :
    ∃ f : p.primeCompl,
      Function.Injective (awayLift (algebraMap R Rₚ) f.1 (awayElement_isUnit_atPrime p f)) := by
  rcases h with hnoeth | ⟨hred, hfinite⟩
  · letI := hnoeth
    exact exists_injective_awayLift_atPrime_of_isNoetherianRing p
  · classical
    letI := hred
    exact exists_injective_awayLift_atPrime_of_isReduced_finiteMinimalPrimes p hfinite

end

/-! ### Lemma_10_31_10 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Lemma 10.31.10 (Stacks tag `06RN`): any surjective endomorphism of a Noetherian ring is an
isomorphism. Mathlib organizes this under the owner theorem
`OrzechProperty.bijective_of_surjective_endomorphism`; the commutative Noetherian ring case is
recovered from `IsNoetherianRing.orzechProperty`, viewing a ring endomorphism `f : R →+* R` as the
linear endomorphism `f.toLinearMap` of the finite `R`-module `R`. -/
recall OrzechProperty.bijective_of_surjective_endomorphism

end
