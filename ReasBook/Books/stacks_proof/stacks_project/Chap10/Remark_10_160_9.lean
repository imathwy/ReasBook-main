import Mathlib
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.LocalRing.Quotient
import StacksProject_2024.Chap05.Lemma_5_20_2
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_160_4
import StacksProject_2024.Chap10.Definition_10_160_5
import StacksProject_2024.Chap10.Lemma_10_103_10
import StacksProject_2024.Chap10.Lemma_10_138_12
import StacksProject_2024.Chap10.Lemma_10_105_5
import StacksProject_2024.Chap10.Lemma_10_105_6
import StacksProject_2024.Chap10.Lemma_10_105_7
import StacksProject_2024.Chap10.Lemma_10_105_9
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_106_7
import StacksProject_2024.Chap10.Lemma_10_110_6
import StacksProject_2024.Chap10.Lemma_10_72_7
import StacksProject_2024.Chap10.Lemma_10_31_2
import StacksProject_2024.Chap10.Lemma_10_97_10
import StacksProject_2024.Chap10.Lemma_10_99_8
import StacksProject_2024.Chap10.Lemma_10_149_4
import StacksProject_2024.Chap10.Lemma_10_157_2
import StacksProject_2024.Chap10.Lemma_10_158_7
import StacksProject_2024.Chap10.Lemma_10_160_6
import StacksProject_2024.Chap10.Definition_10_103_12
import StacksProject_2024.Chap10.Remark_10_160_9.RegularSingleton

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Finset Finsupp Ideal RingTheory Sequence IsLocalRing TensorProduct
open scoped BigOperators PowerSeries TensorProduct nonZeroDivisors ENat

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- The source proof starts by reducing finite-variable power series to the zero-variable owner and
the one-variable successor step. The zero-variable case is already canonical, so we isolate it
here before facing the missing one-variable structural input. -/
/-- Helper for Remark 10.160.9: complete-local structure transports across ring equivalences. -/
theorem isCompleteLocalRing_of_ringEquiv (e : R ≃+* S) [IsCompleteLocalRing R] :
    IsCompleteLocalRing S := by
  let _ : IsLocalRing S := e.isLocalRing
  have hcomplete : IsAdicComplete (maximalIdeal S) S := by
    -- Transport adic completeness across the equivalence after identifying maximal ideals.
    simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using
      (IsAdicComplete.congr_ringEquiv (I := maximalIdeal R) e).2
        (inferInstance : IsAdicComplete (maximalIdeal R) R)
  exact
    { toIsLocalRing := e.isLocalRing
      toIsAdicComplete := hcomplete }

/-- Helper for Remark 10.160.9: zero formal variables recover the coefficient ring itself. -/
private noncomputable def mvPowerSeries_fin_zero_ringEquiv (R : Type u) [CommSemiring R] :
    MvPowerSeries (Fin 0) R ≃+* R where
  toFun := MvPowerSeries.constantCoeff
  invFun := MvPowerSeries.C
  left_inv f := by
    -- Every exponent vector in `Fin 0` is zero, so coefficient comparison reduces to constants.
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    simp [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  right_inv r := by
    -- Constant series are fixed by taking constant coefficient.
    simp
  map_mul' _ _ := by
    simp
  map_add' _ _ := by
    simp

/-- Helper for Remark 10.160.9: splitting variables indexed by `σ ⊕ τ` identifies multivariable
power series with `σ`-indexed power series whose coefficients are `τ`-indexed power series. -/
private theorem mvPowerSeries_sum_ringEquiv
    (A : Type u) [CommSemiring A] (σ τ : Type*) :
    Nonempty (MvPowerSeries (σ ⊕ τ) A ≃+* MvPowerSeries σ (MvPowerSeries τ A)) := by
  refine ⟨?_⟩
  refine
    { toFun := fun f d e ↦ f (sumElim d e)
      invFun := fun f d ↦
        f
          (comapDomain Sum.inl d Sum.inl_injective.injOn)
          (comapDomain Sum.inr d Sum.inr_injective.injOn)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · intro f
    funext d
    simp [Finsupp.comapDomain_sumElim_comapDomain]
  · intro f
    funext d
    funext e
    simp
  · intro f g
    classical
    funext d
    funext e
    let F : MvPowerSeries σ (MvPowerSeries τ A) := fun d e ↦ f (sumElim d e)
    let G : MvPowerSeries σ (MvPowerSeries τ A) := fun d e ↦ g (sumElim d e)
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
                    simpa using congrArg (fun s : MvPowerSeries τ A ↦ s e)
                      (MvPowerSeries.coeff_mul d F G)
  · intro f g
    rfl

/-- Helper for Remark 10.160.9: the distinguished `Option.none` variable identifies with the
univariate power-series variable. -/
private noncomputable def optionToUnitSum (σ : Type*) : Option σ ≃ Unit ⊕ σ :=
  (Equiv.optionEquivSumPUnit σ).trans (Equiv.sumComm _ _)

/-- Helper for Remark 10.160.9: one distinguished variable turns an `Option`-indexed
multivariable power series ring into a univariate power series ring over the remaining variables. -/
private theorem optionMvPowerSeries_ringEquiv
    (A : Type u) [CommSemiring A] (σ : Type*) :
    Nonempty (MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)) := by
  rcases mvPowerSeries_sum_ringEquiv A Unit σ with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (optionToUnitSum σ)).toRingEquiv.trans e⟩

/-- Helper for Remark 10.160.9: adjoining one more `Fin`-indexed variable is the same as passing
to a univariate power series ring over the previous finite-variable ring. -/
private theorem mvPowerSeries_fin_succ_ringEquiv
    (A : Type u) [CommSemiring A] (d : ℕ) :
    Nonempty (MvPowerSeries (Fin (d + 1)) A ≃+* PowerSeries (MvPowerSeries (Fin d) A)) := by
  rcases optionMvPowerSeries_ringEquiv A (Fin d) with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (_root_.finSuccEquiv d)).toRingEquiv.trans e⟩

/-- Helper for Remark 10.160.9: the kernel of the constant-coefficient map on `A⟦X⟧` is the
principal ideal generated by `X`. -/
private theorem powerSeries_constantCoeff_ker_eq_span_X
    (A : Type u) [CommRing A] :
    RingHom.ker (PowerSeries.constantCoeff (R := A)) =
      Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)) := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- Helper for Remark 10.160.9: quotienting `A⟦X⟧` by the ideal `(X)` recovers the coefficient
ring `A`. -/
private theorem powerSeries_quotient_span_X_ringEquiv
    (A : Type u) [CommRing A] :
    Nonempty (((PowerSeries A) ⧸
      Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ≃+* A) := by
  refine ⟨?_⟩
  exact
    (Ideal.quotEquivOfEq (powerSeries_constantCoeff_ker_eq_span_X A).symm).trans
      (RingHom.quotientKerEquivOfSurjective (PowerSeries.constantCoeff_surj (R := A)))

end

section

/- Domain-style sampling:
- primary domain: Cohen structure and universal catenarity for Noetherian complete local rings.
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `IsRegularLocalRing`,
  `exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg`,
  `universallyCatenaryRing_of_cohenMacaulayRing`.
- best owner abstraction: the ambient owners are `IsCompleteLocalRing R`,
  `IsRegularLocalRing R`, and `UniversallyCatenaryRing R`; the regular-local quotient statement is
  a `bridge/view` corollary of the Cohen-structure owner theorem, not a second source owner.
- primitive data: the complete-local and Noetherian owner hypotheses on `R`.
- derived API: finite-variable power-series support instances, the regular-local quotient
  presentation, and universal catenarity.

Source/core/bridge triage:
* `source-facing`: the remark-level corollary that a Noetherian complete local ring is a quotient
  of a regular local ring, and hence universally catenary;
* `core/canonical`: `IsCompleteLocalRing`, `IsRegularLocalRing`, and `UniversallyCatenaryRing`;
* `bridge/view`: the quotient presentation extracted from
  `exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg`.
-/

/-- Helper for Remark 10.160.9: the constant-coefficient map sends the maximal ideal of `A⟦X⟧`
onto the maximal ideal of `A`. -/
private theorem powerSeries_map_constantCoeff_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal (PowerSeries A)).map (PowerSeries.constantCoeff (R := A)) = maximalIdeal A := by
  -- The constant-coefficient map is a surjective local hom, so maximal ideals match under `map`.
  simpa using
    IsLocalRing.map_maximalIdeal_of_surjective
      (PowerSeries.constantCoeff (R := A))
      (PowerSeries.constantCoeff_surj (R := A))

/-- Helper for Remark 10.160.9: the maximal ideal of `A⟦X⟧` is generated by `X` together with the
constant series coming from the maximal ideal of `A`. -/
private theorem powerSeries_maximalIdeal_eq_span_insert_C_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    maximalIdeal (PowerSeries A) =
      Ideal.span
        (Set.insert (PowerSeries.X : PowerSeries A)
          (PowerSeries.C '' ((maximalIdeal A : Ideal A) : Set A))) := by
  have hX :
      (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) := by
    -- The constant coefficient of `X` is `0`, so `X` is not a unit.
    rw [IsLocalRing.mem_maximalIdeal]
    intro hX_unit
    have hconst_unit :
        IsUnit (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries A)) :=
      PowerSeries.isUnit_constantCoeff _ hX_unit
    simp at hconst_unit
  have hspan :
      Ideal.span (((maximalIdeal A : Ideal A) : Set A)) = maximalIdeal A := by
    -- The coefficient-side generators already span the maximal ideal of `A`.
    exact le_antisymm (Ideal.span_le.2 fun _ hx ↦ hx) Ideal.subset_span
  -- Apply the canonical `(m_A, X)` description of ideals in a power-series ring.
  simpa using
    (PowerSeries.eq_span_insert_X_of_X_mem_of_span_eq
      (I := maximalIdeal (PowerSeries A))
      (S := ((maximalIdeal A : Ideal A) : Set A))
      hX
      (hspan.trans (powerSeries_map_constantCoeff_maximalIdeal A).symm))

/-- Helper for Remark 10.160.9: membership in `(X)^n` is equivalent to vanishing of the first
`n` coefficients. -/
private theorem powerSeries_mem_span_X_pow_iff_coeff_eq_zero
    (A : Type u) [CommRing A] (n : ℕ) (f : PowerSeries A) :
    f ∈ (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ^ n ↔
      ∀ m, m < n → PowerSeries.coeff m f = 0 := by
  -- The ideal `(X)^n` is principal, generated by `X^n`, so the claim is exactly
  -- `PowerSeries.X_pow_dvd_iff`.
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

/-- Helper for Remark 10.160.9: congruence modulo `(X)^n` means equality of all coefficients in
degrees `< n`. -/
private theorem powerSeries_smodEq_span_X_pow_iff_coeff_eq
    (A : Type u) [CommRing A] (n : ℕ) (f g : PowerSeries A) :
    f ≡ g
      [SMOD ((Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ^ n •
        (⊤ : Submodule (PowerSeries A) (PowerSeries A)))] ↔
      ∀ m, m < n → PowerSeries.coeff m f = PowerSeries.coeff m g := by
  -- Rewrite modular equivalence as membership of the difference in `(X)^n`, then read that
  -- membership coefficientwise.
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
    powerSeries_mem_span_X_pow_iff_coeff_eq_zero (A := A) (n := n) (f := f - g)]
  constructor
  · intro h m hm
    simpa [sub_eq_zero] using h m hm
  · intro h m hm
    simp [h m hm]

/-- Helper for Remark 10.160.9: `A⟦X⟧` is complete for the `(X)`-adic topology. -/
private theorem powerSeries_isAdicComplete_span_X
    (A : Type u) [CommRing A] :
    IsAdicComplete
      (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))
      (PowerSeries A) := by
  refine
    { haus' := ?_, prec' := ?_ }
  · -- Vanishing modulo every power of `(X)` forces every coefficient to be zero.
    intro f h
    ext n
    have hmem :
        f ∈ (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ^ (n + 1) := by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using h (n + 1)
    exact
      (powerSeries_mem_span_X_pow_iff_coeff_eq_zero
        (A := A) (n := n + 1) (f := f)).1 hmem n (Nat.lt_succ_self n)
  · intro x h
    refine ⟨PowerSeries.mk (fun n ↦ PowerSeries.coeff n (x (n + 1))), ?_⟩
    intro n
    -- The Cauchy hypothesis says that the `i`-th coefficient stabilizes by stage `i + 1`.
    rw [powerSeries_smodEq_span_X_pow_iff_coeff_eq (A := A) (n := n)]
    intro i hi
    have hstable :
        PowerSeries.coeff i (x (i + 1)) = PowerSeries.coeff i (x n) := by
      have hmod :
          x (i + 1) ≡ x n
            [SMOD ((Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ^
              (i + 1) • (⊤ : Submodule (PowerSeries A) (PowerSeries A)))] :=
        h (Nat.succ_le_of_lt hi)
      exact
        (powerSeries_smodEq_span_X_pow_iff_coeff_eq
          (A := A) (n := i + 1) (f := x (i + 1)) (g := x n)).1
          hmod i (Nat.lt_succ_self i)
    simpa [PowerSeries.coeff_mk] using hstable.symm

/-- Helper for Remark 10.160.9: after quotienting by `(X)`, the image of the ambient maximal ideal
is adically complete because the quotient is canonically the complete local coefficient ring. -/
private theorem powerSeries_quotient_span_X_isAdicComplete_maximalIdeal_map
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    IsAdicComplete
      ((maximalIdeal (PowerSeries A)).map
        (Ideal.Quotient.mk
          (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))))
      ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) := by
  rcases powerSeries_quotient_span_X_ringEquiv (A := A) with ⟨e⟩
  let hquotCompleteLocal :
      IsCompleteLocalRing
        ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    isCompleteLocalRing_of_ringEquiv
      (R := A)
      (S := (PowerSeries A) ⧸
        Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))
      e.symm
  let _ :
      IsCompleteLocalRing
        ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    hquotCompleteLocal
  have hmap :
      (maximalIdeal (PowerSeries A)).map
          (Ideal.Quotient.mk
            (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))) =
        maximalIdeal
          ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk
        (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))))
      Ideal.Quotient.mk_surjective
  -- Once the quotient is recognized as a complete local ring, its maximal-ideal completion is
  -- already available as an instance.
  have hcompleteQuot :
      IsAdicComplete
        (maximalIdeal
          ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))))
        ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    hquotCompleteLocal.toIsAdicComplete
  simpa [hmap] using hcompleteQuot

/-- Helper for Remark 10.160.9: a power series ring over a Noetherian complete local ring is again
a complete local ring. -/
private theorem powerSeries_isCompleteLocalRing_of_isCompleteLocalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    IsCompleteLocalRing (PowerSeries A) := by
  let hXcomplete :
      IsAdicComplete
        (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))
        (PowerSeries A) :=
    powerSeries_isAdicComplete_span_X (A := A)
  have hquot :
      IsAdicComplete
        ((maximalIdeal (PowerSeries A)).map
          (Ideal.Quotient.mk
            (Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))))
        ((PowerSeries A) ⧸ Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    powerSeries_quotient_span_X_isAdicComplete_maximalIdeal_map (A := A)
  have hcomplete :
      IsAdicComplete (maximalIdeal (PowerSeries A)) (PowerSeries A) := by
    -- Lemma 10.97.10 upgrades the explicit `(X)`-adic completeness to maximal-ideal completeness
    -- using the quotient identification modulo `X`.
    exact
      isAdicComplete_of_quotient_isAdicComplete_of_isAdicComplete
        (A := PowerSeries A)
        (I := Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))
        (J := maximalIdeal (PowerSeries A))
        hXcomplete
        hquot
  exact
    { toIsLocalRing := inferInstance
      toIsAdicComplete := hcomplete }

/-- Formal power series in finitely many variables over a Noetherian complete local ring form a
complete local ring. -/
instance mvPowerSeries_fin_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] (d : ℕ) :
    IsCompleteLocalRing (MvPowerSeries (Fin d) R) := by
  induction d with
  | zero =>
      -- Route correction: isolate the zero-variable owner first; only the successor step still
      -- needs the missing one-variable completeness theorem for `PowerSeries`.
      exact
        isCompleteLocalRing_of_ringEquiv
          (R := R)
          (S := MvPowerSeries (Fin 0) R)
          (mvPowerSeries_fin_zero_ringEquiv R).symm
  | succ d ih =>
      rcases mvPowerSeries_fin_succ_ringEquiv (A := R) d with ⟨e⟩
      let _ : IsCompleteLocalRing (MvPowerSeries (Fin d) R) := ih
      let _ : IsNoetherianRing (MvPowerSeries (Fin d) R) := by
        infer_instance
      let _ : IsCompleteLocalRing (PowerSeries (MvPowerSeries (Fin d) R)) :=
        powerSeries_isCompleteLocalRing_of_isCompleteLocalRing
          (A := MvPowerSeries (Fin d) R)
      -- The successor step is the one-variable completion bridge over the already complete
      -- `d`-variable coefficient ring, followed by the standard reindexing equivalence.
      exact
        isCompleteLocalRing_of_ringEquiv
          (R := PowerSeries (MvPowerSeries (Fin d) R))
          (S := MvPowerSeries (Fin (d + 1)) R)
          e.symm

/-- Helper for Remark 10.160.9: quotienting `A⟦X⟧` by `(X)` inherits regular-locality from
`A`. -/
private theorem powerSeries_quotient_span_X_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing
      ((PowerSeries A) ⧸
        Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) := by
  rcases powerSeries_quotient_span_X_ringEquiv (A := A) with ⟨e⟩
  -- The quotient is canonically the coefficient ring, so regular-locality transports directly.
  exact IsRegularLocalRing.of_ringEquiv (R := A) e.symm

/-- Helper for Remark 10.160.9: the power-series variable `X` lies in the maximal ideal of
`A⟦X⟧`. -/
private theorem powerSeries_X_mem_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) := by
  -- The constant coefficient of `X` is zero, so `X` is not a unit.
  rw [IsLocalRing.mem_maximalIdeal]
  intro hX_unit
  have hconst_unit :
      IsUnit (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries A)) :=
    PowerSeries.isUnit_constantCoeff _ hX_unit
  simp at hconst_unit

/-- Helper for Remark 10.160.9: over a regular local coefficient ring, the power-series variable
`X` is a regular element of `A⟦X⟧`. -/
private theorem powerSeries_X_isRegular
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegular (PowerSeries.X : PowerSeries A) := by
  -- Multiplication by `X` is injective on either side in every power-series ring.
  exact ⟨PowerSeries.X_mul_injective, PowerSeries.mul_X_injective⟩

/-- Helper for Remark 10.160.9: the singleton sequence `[X]` is weakly regular in `A⟦X⟧`. -/
private theorem powerSeries_X_isWeaklyRegular_singleton
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsWeaklyRegular (PowerSeries A) [(PowerSeries.X : PowerSeries A)] := by
  -- The singleton-sequence API reduces weak regularity to ordinary regularity of `X`.
  exact
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff
      (PowerSeries A) (PowerSeries.X : PowerSeries A)).2
      ((powerSeries_X_isRegular (A := A)).isSMulRegular)

/-- Helper for Remark 10.160.9: the singleton sequence `[X]` is regular in `A⟦X⟧`. -/
private theorem powerSeries_X_regular_singleton
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegular (PowerSeries A) [(PowerSeries.X : PowerSeries A)] := by
  -- Route correction: the singleton upgrade now lives in a tiny helper module so this file only
  -- instantiates the canonical maximal-ideal-plus-regular-element pattern for `X`.
  let _ : Module.Finite (PowerSeries A) (PowerSeries A) := Module.Finite.self (PowerSeries A)
  have hX_mem :
      (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) :=
    powerSeries_X_mem_maximalIdeal (A := A)
  have hX_smulRegular :
      IsSMulRegular (PowerSeries A) (PowerSeries.X : PowerSeries A) :=
    (powerSeries_X_isRegular (A := A)).isSMulRegular
  exact
    regular_singleton_of_mem_maximalIdeal_of_isSMulRegular
      (R := PowerSeries A)
      (M := PowerSeries A)
      (x := (PowerSeries.X : PowerSeries A))
      hX_mem
      hX_smulRegular

/-- Helper for Remark 10.160.9: quotienting by `Ideal.ofList [X]` is the same regular-local
quotient as quotienting by `(X)`. -/
private theorem powerSeries_quotient_ofList_singleton_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing ((PowerSeries A) ⧸ Ideal.ofList [(PowerSeries.X : PowerSeries A)]) := by
  -- Normalize the singleton list ideal with an explicit quotient equivalence before transport.
  have hI :
      Ideal.ofList [(PowerSeries.X : PowerSeries A)] =
        Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)) := by
    rw [Ideal.ofList_singleton]
  let e :
      ((PowerSeries A) ⧸ Ideal.ofList [(PowerSeries.X : PowerSeries A)]) ≃+*
        ((PowerSeries A) ⧸
          Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    Ideal.quotEquivOfEq hI
  let _ :
      IsRegularLocalRing
        ((PowerSeries A) ⧸
          Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) :=
    powerSeries_quotient_span_X_isRegularLocalRing (A := A)
  exact
    IsRegularLocalRing.of_ringEquiv
      (R := (PowerSeries A) ⧸
        Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))
      e.symm

private theorem powerSeries_isRegularLocalRing_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing (PowerSeries A) := by
  -- Route correction: the verified prefix is the quotient identification
  -- `(A⟦X⟧)/(X) ≃ A`, already packaged as
  -- `powerSeries_quotient_span_X_isRegularLocalRing`; the easy side facts
  -- `powerSeries_X_mem_maximalIdeal` and `powerSeries_X_isRegular` are also now isolated. The
  -- remaining step is to show that `X` gives a singleton regular sequence in `A⟦X⟧` without
  -- triggering the current elaboration timeout around
  -- `IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`, and then apply
  -- `isRegularLocalRing_of_quotient_of_isRegular` with
  -- `rs := [(PowerSeries.X : PowerSeries A)]`.
  have hregX : IsRegular (PowerSeries A) [(PowerSeries.X : PowerSeries A)] := by
    -- Cache the singleton regular sequence before applying the quotient-lifting theorem.
    exact powerSeries_X_regular_singleton (A := A)
  have hquot :
      IsRegularLocalRing ((PowerSeries A) ⧸ Ideal.ofList [(PowerSeries.X : PowerSeries A)]) := by
    -- Normalize the quotient to the already verified `(X)`-quotient presentation.
    exact powerSeries_quotient_ofList_singleton_isRegularLocalRing (A := A)
  -- With the singleton regular sequence and regular-local quotient in hand, Lemma 10.106.7 lifts
  -- regular-locality back to the whole power-series ring.
  exact
    isRegularLocalRing_of_quotient_of_isRegular
      (R := PowerSeries A)
      (rs := [(PowerSeries.X : PowerSeries A)])
      hregX
      hquot

/-- Formal power series in finitely many variables over a regular local ring form a regular local
ring. -/
instance mvPowerSeries_fin_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin d) R) := by
  induction d with
  | zero =>
      -- Zero variables do not change the regular local owner.
      exact
        IsRegularLocalRing.of_ringEquiv
          (R := R)
          (mvPowerSeries_fin_zero_ringEquiv R).symm
  | succ d ih =>
      rcases mvPowerSeries_fin_succ_ringEquiv (A := R) d with ⟨e⟩
      let _ : IsRegularLocalRing (MvPowerSeries (Fin d) R) := ih
      let _ : IsRegularLocalRing (PowerSeries (MvPowerSeries (Fin d) R)) :=
        powerSeries_isRegularLocalRing_of_isRegularLocalRing
          (A := MvPowerSeries (Fin d) R)
      -- Reindex the successor variable into a single distinguished power-series variable.
      exact
        IsRegularLocalRing.of_ringEquiv
          (R := PowerSeries (MvPowerSeries (Fin d) R))
          e.symm

/-- Helper for Chap10 Remark 10 160 9: formal power series in variables indexed by any finite
type over a regular local ring form a regular local ring. -/
private theorem mvPowerSeries_finite_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (σ : Type u) [Finite σ] :
    IsRegularLocalRing (MvPowerSeries σ A) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let e : MvPowerSeries (Fin (Fintype.card σ)) A ≃+* MvPowerSeries σ A :=
    (MvPowerSeries.renameEquiv A (Fintype.equivFin σ).symm).toRingEquiv
  -- Reindex the finite variable set to the canonical `Fin` owner, where regularity is already
  -- available by induction on the number of variables.
  exact IsRegularLocalRing.of_ringEquiv (R := MvPowerSeries (Fin (Fintype.card σ)) A) e

/-- Helper for Remark 10.160.9: if `A` is a Noetherian local domain, then adjoining one formal
variable raises its Krull dimension by exactly one. -/
private theorem ringKrullDim_powerSeries_eq_succ
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ringKrullDim (PowerSeries A) = ringKrullDim A + 1 := by
  have hX_mem : (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) := by
    -- The variable `X` has zero constant coefficient, so it is not invertible.
    rw [IsLocalRing.mem_maximalIdeal]
    intro hX_unit
    have hconst_unit :
        IsUnit (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries A)) :=
      PowerSeries.isUnit_constantCoeff _ hX_unit
    simp at hconst_unit
  have hX_nonZeroDiv :
      (PowerSeries.X : PowerSeries A) ∈ nonZeroDivisors (PowerSeries A) := by
    -- In the domain `A⟦X⟧`, the distinguished variable is nonzero and hence a nonzerodivisor.
    exact mem_nonZeroDivisors_iff_ne_zero.mpr PowerSeries.X_ne_zero
  rcases powerSeries_quotient_span_X_ringEquiv (A := A) with ⟨e⟩
  calc
    ringKrullDim (PowerSeries A) =
        ringKrullDim
          (((PowerSeries A) ⧸
            Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))) + 1 := by
          -- The singleton nonzerodivisor quotient theorem is exactly the one-variable dimension
          -- step.
          symm
          simpa using
            (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
              (R := PowerSeries A) hX_nonZeroDiv hX_mem)
    _ = ringKrullDim A + 1 := by
          rw [ringKrullDim_eq_of_ringEquiv e]

-- Proof sketch: view the maximal ideal as generated by the coordinate variables and compute the
-- Krull dimension inductively, removing one power-series variable at a time.
/-- The Krull dimension of the `d`-variable formal power series ring over a field is `d`. -/
theorem ringKrullDim_mvPowerSeries_fin_field (k : Type u) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  induction d with
  | zero =>
      -- Zero variables reduce the dimension statement to the field case.
      simpa [ringKrullDim_eq_zero_of_field k] using
        (ringKrullDim_eq_of_ringEquiv (mvPowerSeries_fin_zero_ringEquiv k))
  | succ d ih =>
      rcases mvPowerSeries_fin_succ_ringEquiv (A := k) d with ⟨e⟩
      let _ : IsRegularLocalRing (MvPowerSeries (Fin d) k) := by
        infer_instance
      let _ : IsDomain (MvPowerSeries (Fin d) k) := NoZeroDivisors.to_isDomain _
      -- The same successor reindexing reduces the finite-variable dimension computation to the
      -- one-variable step.
      calc
        ringKrullDim (MvPowerSeries (Fin (d + 1)) k)
            = ringKrullDim (PowerSeries (MvPowerSeries (Fin d) k)) := by
                exact ringKrullDim_eq_of_ringEquiv e
        _ = ringKrullDim (MvPowerSeries (Fin d) k) + 1 := by
              exact ringKrullDim_powerSeries_eq_succ (A := MvPowerSeries (Fin d) k)
        _ = d + 1 := by
              rw [ih]

/-- Helper for Chap10 Remark 10 160 9: over a Noetherian local ring, the maximal ideal is
finitely generated. -/
private theorem maximalIdeal_fg_of_isNoetherianRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    (maximalIdeal A).FG := by
  -- This packages the Noetherian side condition needed by the Cohen-structure quotient theorem.
  exact IsNoetherian.noetherian (maximalIdeal A)

/-- Helper for Chap10 Remark 10 160 9: the maximal ideal of a coefficient ring is finitely
generated. -/
private theorem coefficientRing_maximalIdeal_fg
    (A : Type u) [CommRing A] [IsCompleteLocalRing A]
    (Λ : Subring A) [IsCoefficientRing A Λ] :
    (maximalIdeal Λ).FG := by
  -- A coefficient ring has principal maximal ideal, so finite generation follows from the
  -- standard principal-submodule finiteness lemma.
  exact Submodule.IsPrincipal.fg (inferInstance : (maximalIdeal Λ).IsPrincipal)

/-- Helper for Chap10 Remark 10 160 9: a field is complete local for its zero maximal ideal. -/
private theorem field_isCompleteLocalRing (k : Type u) [Field k] : IsCompleteLocalRing k := by
  let _ : IsLocalRing k := inferInstance
  have hcomplete : IsAdicComplete (maximalIdeal k) k := by
    -- The maximal ideal of a field is zero, and zero-adic completeness is canonical.
    simpa [IsLocalRing.maximalIdeal_eq_bot] using
      (inferInstance : IsAdicComplete (⊥ : Ideal k) k)
  exact
    { toIsLocalRing := inferInstance
      toIsAdicComplete := hcomplete }

/-- Helper for Chap10 Remark 10 160 9: a bijective ring homomorphism identifies ring
characteristics. -/
private theorem ringChar_eq_of_bijective_ringHom
    {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Bijective f) :
    ringChar R = ringChar S := by
  apply Nat.dvd_antisymm
  · -- Pull the vanishing of `ringChar S` back through injectivity of `f`.
    have hzeroS : ((ringChar S : ℕ) : S) = 0 :=
      (ringChar.spec S (ringChar S)).2 dvd_rfl
    have hmap : f ((ringChar S : ℕ) : R) = f 0 := by
      rw [map_natCast, hzeroS, map_zero]
    have hzeroR : ((ringChar S : ℕ) : R) = 0 := hf.1 hmap
    exact (ringChar.spec R (ringChar S)).mp hzeroR
  · -- Map the vanishing of `ringChar R` forward to `S`.
    have hzeroR : ((ringChar R : ℕ) : R) = 0 :=
      (ringChar.spec R (ringChar R)).2 dvd_rfl
    have hzeroS' : f ((ringChar R : ℕ) : R) = 0 := by
      rw [hzeroR]
      simp
    have hmapNat : f ((ringChar R : ℕ) : R) = ((ringChar R : ℕ) : S) := by
      rw [map_natCast]
    have hzeroS : ((ringChar R : ℕ) : S) = 0 := by
      rw [hmapNat] at hzeroS'
      exact hzeroS'
    exact (ringChar.spec S (ringChar R)).mp hzeroS

/-- Helper for Chap10 Remark 10 160 9: a proper quotient of a complete local ring is local. -/
private theorem quotientIsLocalRingOfProperIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  -- The quotient map is surjective, so the local-ring structure transports directly.
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Remark 10 160 9: for a proper quotient of a local ring, the maximal ideal of
the quotient is the image of the maximal ideal of the source. -/
private theorem quotientMaximalIdealEqMap
    {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) = maximalIdeal (A ⧸ I) := by
  -- Surjectivity identifies the quotient maximal ideal with the image of the source maximal ideal.
  exact
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Remark 10 160 9: the `maximalIdeal A`-adic completion of `A ⧸ I`, viewed as
an `A`-module, identifies canonically with `A ⧸ I`. -/
private noncomputable def quotientCompletionLinearEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] (I : Ideal A) :
    AdicCompletion (maximalIdeal A) (A ⧸ I) ≃ₗ[A] A ⧸ I :=
  let eCompletion :
      AdicCompletion (maximalIdeal A) (A ⧸ I) ≃ₗ[A]
        AdicCompletion (maximalIdeal A) A ⊗[A] (A ⧸ I) :=
    (LinearEquiv.restrictScalars A
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal A) (A ⧸ I))).symm
  let eTensor :
      (A ⧸ I) ≃ₐ[A] AdicCompletion (maximalIdeal A) A ⊗[A] (A ⧸ I) :=
    (Algebra.TensorProduct.lid A (A ⧸ I)).symm.trans
      (Algebra.TensorProduct.congr
        (AdicCompletion.ofAlgEquiv (maximalIdeal A))
        (show (A ⧸ I) ≃ₐ[A] (A ⧸ I) from AlgEquiv.refl))
  eCompletion.trans eTensor.symm.toLinearEquiv

/-- Helper for Chap10 Remark 10 160 9: the quotient-completion equivalence sends the canonical
completion class of `x` back to `x`. -/
private theorem quotientCompletionLinearEquiv_of
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    (I : Ideal A) (x : A ⧸ I) :
    quotientCompletionLinearEquiv A I
        (AdicCompletion.of (maximalIdeal A) (A ⧸ I) x) = x := by
  -- The tensor/completion comparison sends `of x` to `1 ⊗ x`, and `TensorProduct.lid` evaluates
  -- that tensor to `x`.
  simp [quotientCompletionLinearEquiv]

/-- Helper for Chap10 Remark 10 160 9: as an `A`-module, the quotient `A ⧸ I` is complete for the
`maximalIdeal A`-adic topology. -/
private theorem quotientIsAdicCompleteMaximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] (I : Ideal A) :
    IsAdicComplete (maximalIdeal A) (A ⧸ I) := by
  have hof_eq :
      (AdicCompletion.of (maximalIdeal A) (A ⧸ I) :
          (A ⧸ I) →ₗ[A] AdicCompletion (maximalIdeal A) (A ⧸ I)) =
        (quotientCompletionLinearEquiv A I).symm.toLinearMap := by
    -- Apply the constructed equivalence to both sides; both images are the source quotient class.
    apply LinearMap.ext
    intro x
    apply (quotientCompletionLinearEquiv A I).injective
    simp [quotientCompletionLinearEquiv_of]
  -- Once the completion map is an inverse equivalence, adic completeness follows immediately.
  exact (AdicCompletion.of_bijective_iff).mp <| by
    simpa [hof_eq] using (quotientCompletionLinearEquiv A I).symm.bijective

/-- Helper for Chap10 Remark 10 160 9: a proper quotient is adically complete for the image of the
source maximal ideal. -/
private theorem quotientIsAdicCompleteMappedMaximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    (I : Ideal A) :
    IsAdicComplete (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A)) (A ⧸ I) := by
  -- First regard the quotient as complete for the source maximal ideal, then transport
  -- completeness across the quotient algebra map.
  exact
    (IsAdicComplete.map_algebraMap_iff
      (R := A) (S := A ⧸ I) (I := maximalIdeal A) (M := A ⧸ I)).2 <|
      quotientIsAdicCompleteMaximalIdeal A I

/-- Helper for Chap10 Remark 10 160 9: a proper quotient of a Noetherian complete local ring is
again a complete local ring. -/
private theorem quotient_isCompleteLocalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (A ⧸ I) := by
  let _ : IsLocalRing (A ⧸ I) := quotientIsLocalRingOfProperIdeal A I hI
  have hcomplete : IsAdicComplete (maximalIdeal (A ⧸ I)) (A ⧸ I) := by
    -- Rewrite the quotient maximal ideal into the image of the source maximal ideal.
    rw [← quotientMaximalIdealEqMap I]
    exact quotientIsAdicCompleteMappedMaximalIdeal A I
  exact
    { toIsLocalRing := quotientIsLocalRingOfProperIdeal A I hI
      toIsAdicComplete := hcomplete }

/-- Helper for Chap10 Remark 10 160 9: the quotient map to a proper quotient induces a bijection on
residue fields. -/
private theorem residueField_map_quotient_mk_bijective
    {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (A ⧸ I) := quotientIsLocalRingOfProperIdeal A I hI
    let _ : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Function.Bijective (ResidueField.map (Ideal.Quotient.mk I)) := by
  let _ : IsLocalRing (A ⧸ I) := quotientIsLocalRingOfProperIdeal A I hI
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  constructor
  · -- Residue fields are fields, so a nontrivial map between them is injective.
    exact RingHom.injective (ResidueField.map q)
  · intro y
    -- Lift a residue class through the quotient and then through the source ring.
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue A a, rfl⟩

/-- Helper for Chap10 Remark 10 160 9: a complete local subring whose residue-field map is
bijective and whose maximal ideal is generated by the ambient residue characteristic is already a
coefficient ring. -/
private theorem isCoefficientRing_of_completeLocalSubring
    (A : Type u) [CommRing A] [IsCompleteLocalRing A]
    (Λ : Subring A) [IsCompleteLocalRing Λ] [IsLocalHom (Λ.subtype : Λ →+* A)]
    (hres : Function.Bijective (ResidueField.map (Λ.subtype : Λ →+* A)))
    (hmax : maximalIdeal Λ = Ideal.span ({(ringChar (ResidueField A) : Λ)} : Set Λ)) :
    IsCoefficientRing A Λ := by
  -- The complete-local and local-map owner fields are already available from the hypotheses; the
  -- remaining coefficient-ring data are the residue-field bijection and the generator identity.
  exact
    { residueField_bijective := hres
      maximalIdeal_eq_span_residueChar := hmax }

/-- Helper for Chap10 Remark 10 160 9: the range of a local field source with bijective
residue-field map is a coefficient ring. -/
private theorem isCoefficientRing_range_of_field_sourceMap
    (A k : Type u) [CommRing A] [IsCompleteLocalRing A] [Field k]
    (ι : k →+* A) [IsLocalHom ι]
    (hres : Function.Bijective (ResidueField.map ι)) :
    IsCoefficientRing A (RingHom.range ι) := by
  have hιrange_inj : Function.Injective ι.rangeRestrict := by
    intro x y hxy
    apply RingHom.injective ι
    exact Subtype.ext_iff.mp hxy
  let e : k ≃+* RingHom.range ι :=
    RingEquiv.ofBijective ι.rangeRestrict ⟨hιrange_inj, ι.rangeRestrict_surjective⟩
  let _ : IsCompleteLocalRing k := field_isCompleteLocalRing k
  let _ : IsCompleteLocalRing (RingHom.range ι) :=
    isCompleteLocalRing_of_ringEquiv (R := k) (S := RingHom.range ι) e
  have hloc : IsLocalHom ((RingHom.range ι).subtype : RingHom.range ι →+* A) := by
    -- The subtype reflects units because every range element has a field-source preimage.
    refine ⟨?_⟩
    intro x hx
    rcases x.2 with ⟨y, hy⟩
    have hunitι : IsUnit (ι y) := by
      simpa [hy] using hx
    have hunitPre : IsUnit y := IsUnit.of_map ι y hunitι
    have hx_eq : x = ι.rangeRestrict y := Subtype.ext hy.symm
    simpa [hx_eq] using IsUnit.map ι.rangeRestrict hunitPre
  let _ : IsLocalHom ((RingHom.range ι).subtype : RingHom.range ι →+* A) := hloc
  have hresRange :
      Function.Bijective
        (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)) := by
    -- Factor the original residue-field isomorphism through the range equivalence.
    have hcomp :
        ResidueField.map ι =
          (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)).comp
            (ResidueField.map (e : k →+* RingHom.range ι)) := by
      simpa [e] using
        (IsLocalRing.ResidueField.map_comp
          (f := (e : k →+* RingHom.range ι))
          (g := ((RingHom.range ι).subtype : RingHom.range ι →+* A)))
    have hequiv : Function.Bijective (ResidueField.map (e : k →+* RingHom.range ι)) :=
      (IsLocalRing.ResidueField.mapEquiv e).bijective
    constructor
    · intro x y hxy
      rcases hequiv.2 x with ⟨x0, rfl⟩
      rcases hequiv.2 y with ⟨y0, rfl⟩
      refine congrArg (ResidueField.map (e : k →+* RingHom.range ι)) ?_
      apply hres.1
      simpa [hcomp, RingHom.comp_apply] using hxy
    · intro y
      rcases hres.2 y with ⟨x, hx⟩
      refine ⟨ResidueField.map (e : k →+* RingHom.range ι) x, ?_⟩
      simpa [hcomp, RingHom.comp_apply] using hx
  refine
    { residueField_bijective := hresRange
      maximalIdeal_eq_span_residueChar := ?_ }
  letI : Field (RingHom.range ι) := (e.symm.toMulEquiv.isField (Field.toIsField k)).toField
  have hchar : ringChar (ResidueField (RingHom.range ι)) = ringChar (ResidueField A) :=
    ringChar_eq_of_bijective_ringHom
      (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)) hresRange
  have hzero : ((ringChar (ResidueField (RingHom.range ι)) : ℕ) : RingHom.range ι) = 0 := by
    -- In a field, the residue map is injective, so residue-characteristic vanishing descends.
    have hzeroRes :
        IsLocalRing.residue (RingHom.range ι)
          ((ringChar (ResidueField (RingHom.range ι)) : ℕ) : RingHom.range ι) = 0 := by
      change ((ringChar (ResidueField (RingHom.range ι)) : ℕ) :
        ResidueField (RingHom.range ι)) = 0
      exact (ringChar.spec (ResidueField (RingHom.range ι))
        (ringChar (ResidueField (RingHom.range ι)))).2 dvd_rfl
    rw [IsLocalRing.residue_eq_zero_iff] at hzeroRes
    simpa [IsLocalRing.maximalIdeal_eq_bot] using hzeroRes
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rw [← hchar]
  exact (Ideal.span_singleton_eq_bot.mpr hzero).symm

/-- Helper for Chap10 Remark 10 160 9: a Cohen subring with local inclusion, bijective residue
field map, and the induced residue-characteristic comparison is a coefficient ring. -/
private theorem isCoefficientRing_of_isCohenRing_subring
    (A : Type u) [CommRing A] [IsCompleteLocalRing A]
    (Λ : Subring A) [IsCohenRing Λ] [IsLocalHom (Λ.subtype : Λ →+* A)]
    (hres : Function.Bijective (ResidueField.map (Λ.subtype : Λ →+* A))) :
    IsCoefficientRing A Λ := by
  -- The complete-local and local-map parent fields are already available from the Cohen-ring and
  -- inclusion hypotheses; the remaining coefficient-ring data are residue-field bijectivity and
  -- the generator identity for the maximal ideal.
  refine
    { residueField_bijective := hres
      maximalIdeal_eq_span_residueChar := ?_ }
  -- Cohen rings generate the maximal ideal by their own residue characteristic; the bijective
  -- residue-field map identifies this characteristic with the ambient one.
  have hchar : ringChar (ResidueField Λ) = ringChar (ResidueField A) :=
    ringChar_eq_of_bijective_ringHom (ResidueField.map (Λ.subtype : Λ →+* A)) hres
  rw [← hchar]
  exact IsCohenRing.maximalIdeal_eq_span_residueChar

/-- Helper for Chap10 Remark 10 160 9: the kernel of a positive transition map
`A ⧸ K^(n + 1) → A ⧸ K^n` is nilpotent. -/
private theorem factorPowKernelIsNilpotent
    {B : Type u} [CommRing B] (K : Ideal B) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n))) := by
  -- Identify the kernel with the quotient image of `K^n`, whose square vanishes modulo `K^(n+1)`.
  refine ⟨2, ?_⟩
  rw [show
      RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n)) =
        Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) by
    simpa [Ideal.Quotient.factorPow] using
      (Ideal.Quotient.factor_ker (I := K ^ (n + 1)) (J := K ^ n)
        (Ideal.pow_le_pow_right (Nat.le_succ n)))]
  rw [pow_two, ← Ideal.map_mul, ← pow_add]
  have hle : n + 1 ≤ n + n := by
    omega
  exact eq_bot_mono
    (Ideal.map_mono (Ideal.pow_le_pow_right hle))
    (Ideal.map_quotient_self _)

/-- Helper for Chap10 Remark 10 160 9: compatibility on residue maps makes a local-ring map
local and forces its induced residue-field map to be bijective. -/
private theorem existsIsLocalHomAndResidueFieldMapBijectiveOfResidueCompat
    {C : Type u} [CommRing C] [IsLocalRing C]
    {S : Type u} [CommRing S] [IsLocalRing S]
    (ψ : C →+* S) (e : ResidueField C ≃+* ResidueField S)
    (hψ : (IsLocalRing.residue S).comp ψ = e.toRingHom.comp (IsLocalRing.residue C)) :
    ∃ (_ : IsLocalHom ψ), Function.Bijective (ResidueField.map ψ) := by
  -- The residue compatibility reflects unit information from `S` back to `C`.
  have hlocal : IsLocalHom ψ := by
    refine ⟨?_⟩
    intro a ha
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro ham
    have hresC : IsLocalRing.residue C a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ham
    have hresS : IsLocalRing.residue S (ψ a) = 0 := by
      calc
        IsLocalRing.residue S (ψ a) = ((IsLocalRing.residue S).comp ψ) a := rfl
        _ = (e.toRingHom.comp (IsLocalRing.residue C)) a := by rw [hψ]
        _ = 0 := by simp [hresC]
    have hresS_ne_zero : IsLocalRing.residue S (ψ a) ≠ 0 :=
      isUnit_iff_ne_zero.mp (IsUnit.map (IsLocalRing.residue S) ha)
    exact hresS_ne_zero hresS
  refine ⟨hlocal, ?_⟩
  letI : IsLocalHom ψ := hlocal
  -- Once `ψ` is known to be local, its residue-field map agrees with the chosen equivalence.
  have hmap : ResidueField.map ψ = e.toRingHom := by
    ext y
    rcases IsLocalRing.residue_surjective y with ⟨a, rfl⟩
    rw [IsLocalRing.ResidueField.map_residue]
    exact RingHom.congr_fun hψ a
  rw [hmap]
  exact e.bijective

/-- Helper for Chap10 Remark 10 160 9: residue-field characteristic zero forces a local ring to
have characteristic zero. -/
private theorem charZero_of_residueField_charZero
    (S : Type u) [CommRing S] [IsLocalRing S]
    (hchar0 : ringChar (ResidueField S) = 0) :
    CharZero S := by
  letI : CharZero (ResidueField S) :=
    (CharP.ringChar_zero_iff_CharZero (ResidueField S)).1 hchar0
  have hzero : ((ringChar S : ℕ) : ResidueField S) = 0 := by
    have hs : ((ringChar S : ℕ) : S) = 0 :=
      (ringChar.spec S (ringChar S)).2 dvd_rfl
    exact congrArg (IsLocalRing.residue S) hs
  have hring : ringChar S = 0 := by
    exact_mod_cast hzero
  exact (CharP.ringChar_zero_iff_CharZero S).1 hring

/-- Helper for Chap10 Remark 10 160 9: residue-field characteristic zero upgrades a local ring to
an equal-characteristic-zero `ℚ`-algebra. -/
private theorem nonemptyAlgebraRat_of_residueField_charZero
    (S : Type u) [CommRing S] [IsLocalRing S]
    (hchar0 : ringChar (ResidueField S) = 0) :
    Nonempty (Algebra ℚ S) := by
  rw [EqualCharZero.nonempty_algebraRat_iff]
  intro I hI
  let Q := S ⧸ I
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 hI
  letI : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : S →+* Q := Ideal.Quotient.mk I
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hres_bij : Function.Bijective (ResidueField.map q) := by
    -- Route correction: reuse the earlier canonical quotient-residue-field bijection directly in
    -- the `Ideal.Quotient.mk` spelling world.
    simpa [Q, q] using residueField_map_quotient_mk_bijective (A := S) I hI
  have hcharQ : ringChar (ResidueField Q) = 0 := by
    -- Transport the residue-field characteristic across the quotient residue-field bijection.
    rw [← ringChar_eq_of_bijective_ringHom (ResidueField.map q) hres_bij]
    exact hchar0
  exact charZero_of_residueField_charZero (S := Q) hcharQ

/-- Helper for Chap10 Remark 10 160 9: one formally-smooth lift step raises the residue-field map
from `A ⧸ m^(n+1)` to `A ⧸ m^(n+2)` in equal characteristic zero. -/
private theorem fieldLiftQuotientStep
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra ℚ A]
    (n : ℕ) (g : ResidueField A →+* A ⧸ (maximalIdeal A) ^ (n + 1)) :
    ∃ gnext : ResidueField A →+* A ⧸ (maximalIdeal A) ^ (n + 2),
      (Ideal.Quotient.factorPow (maximalIdeal A) (Nat.le_succ (n + 1))).comp gnext = g := by
  let K : Ideal A := maximalIdeal A
  letI : Algebra.FormallySmooth ℚ (ResidueField A) := by
    letI : PerfectField ℚ := PerfectField.ofCharZero
    letI : Algebra.IsSeparableOver ℚ (ResidueField A) :=
      Algebra.IsSeparableOver.of_perfectField
    -- Over the perfect field `ℚ`, every field extension is formally smooth.
    exact Algebra.formallySmooth_of_isSeparableOver
  let qgAlg : ResidueField A →ₐ[ℚ] A ⧸ K ^ (n + 1) := g.toRatAlgHom
  let factor : A ⧸ K ^ (n + 2) →+* A ⧸ K ^ (n + 1) :=
    Ideal.Quotient.factorPow K (Nat.le_succ (n + 1))
  let factorAlg : A ⧸ K ^ (n + 2) →ₐ[ℚ] A ⧸ K ^ (n + 1) := factor.toRatAlgHom
  have hsurj : Function.Surjective factorAlg := by
    dsimp [factorAlg, factor]
    exact Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hnil : IsNilpotent (RingHom.ker factorAlg.toRingHom) := by
    dsimp [factorAlg, factor]
    exact factorPowKernelIsNilpotent (K := K) (n := n + 1) (hn := Nat.succ_pos n)
  let lift : ResidueField A →ₐ[ℚ] A ⧸ K ^ (n + 2) :=
    Algebra.FormallySmooth.liftOfSurjective qgAlg factorAlg hsurj hnil
  -- Compose the formally-smooth lift with the quotient transition to recover the previous stage.
  refine ⟨lift.toRingHom, ?_⟩
  ext x
  calc
    ((Ideal.Quotient.factorPow K (Nat.le_succ (n + 1))).comp lift.toRingHom) x =
        (factorAlg.comp lift) x := by
      rfl
    _ = qgAlg x := by
      rw [Algebra.FormallySmooth.comp_liftOfSurjective]
    _ = g x := by
      rfl

/-- Helper for Chap10 Remark 10 160 9: the power-quotient maps of an equal-characteristic-zero
local ring admit a compatible tower of residue-field lifts. -/
private theorem fieldResidueQuotientTowerLift
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra ℚ A] :
    ∃ g : (n : ℕ) → ResidueField A →+* A ⧸ (maximalIdeal A) ^ (n + 1),
      g 0 =
        (Ideal.quotEquivOfEq
          (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom ∧
      ∀ n, (Ideal.Quotient.factorPow (maximalIdeal A) (Nat.le_succ (n + 1))).comp
        (g (n + 1)) = g n := by
  classical
  let base : ResidueField A →+* A ⧸ (maximalIdeal A) ^ (1 : ℕ) :=
    (Ideal.quotEquivOfEq
      (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom
  let g : (n : ℕ) → ResidueField A →+* A ⧸ (maximalIdeal A) ^ (n + 1) :=
    fun n ↦ Nat.rec base
      (fun m gm ↦ Classical.choose (fieldLiftQuotientStep (A := A) m gm)) n
  refine ⟨g, ?_, ?_⟩
  · dsimp [g, base]
  · intro n
    dsimp [g]
    exact Classical.choose_spec
      (fieldLiftQuotientStep (A := A) n
        (Nat.rec base
          (fun m gm ↦ Classical.choose (fieldLiftQuotientStep (A := A) m gm)) n))

/-- Helper for Chap10 Remark 10 160 9: compatibility after quotienting by `maximalIdeal S ^ 1`
is the same as residue-field compatibility. -/
private theorem residueComp_of_firstPowerQuotientComp
    {C S : Type u} [CommRing C] [IsLocalRing C] [CommRing S] [IsLocalRing S]
    (ψ : C →+* S) (e : ResidueField C ≃+* ResidueField S)
    (hψ : (Ideal.Quotient.mk ((maximalIdeal S) ^ (1 : ℕ))).comp ψ =
      ((Ideal.quotEquivOfEq
        (by simp [pow_one] : maximalIdeal S = (maximalIdeal S) ^ (1 : ℕ))).toRingHom).comp
          (e.toRingHom.comp (IsLocalRing.residue C))) :
    (IsLocalRing.residue S).comp ψ = e.toRingHom.comp (IsLocalRing.residue C) := by
  let E : S ⧸ maximalIdeal S ≃+* S ⧸ (maximalIdeal S) ^ (1 : ℕ) :=
    Ideal.quotEquivOfEq
      (by simp [pow_one] : maximalIdeal S = (maximalIdeal S) ^ (1 : ℕ))
  -- After identifying `S / m` with `S / m^1`, the assumed equality is exactly residue
  -- compatibility.
  ext x
  apply E.injective
  calc
    E (((IsLocalRing.residue S).comp ψ) x) =
        ((Ideal.Quotient.mk ((maximalIdeal S) ^ (1 : ℕ))).comp ψ) x := by
      rfl
    _ = (((Ideal.quotEquivOfEq
        (by simp [pow_one] : maximalIdeal S = (maximalIdeal S) ^ (1 : ℕ))).toRingHom).comp
          (e.toRingHom.comp (IsLocalRing.residue C))) x := by
      exact RingHom.congr_fun hψ x
    _ = E ((e.toRingHom.comp (IsLocalRing.residue C)) x) := by
      rfl

/-- Helper for Chap10 Remark 10 160 9: in positive residue characteristic there is a Cohen ring
whose residue field is `ResidueField A`. -/
private theorem existsCohenRingResidueFieldSource
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hchar : ringChar (ResidueField A) ≠ 0) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsCohenRing C),
      Nonempty (ResidueField C ≃+* ResidueField A) := by
  let p := ringChar (ResidueField A)
  have hpPrime : Nat.Prime p := CharP.char_prime_of_ne_zero (ResidueField A) hchar
  letI : Fact p.Prime := ⟨hpPrime⟩
  letI : CharP (ResidueField A) p := ringChar.of_eq rfl
  exact existsCohenRingWithResidueFieldRingEquiv p (ResidueField A)

/-- Helper for Chap10 Remark 10 160 9: every power of the residue characteristic lies in the
matching power of the maximal ideal. -/
private theorem residueCharPow_mem_maximalIdealPow
    {S : Type u} [CommRing S] [IsLocalRing S] (n : ℕ) :
    ((ringChar (ResidueField S) : S) ^ n) ∈ (maximalIdeal S) ^ n := by
  have hpzero : IsLocalRing.residue S (ringChar (ResidueField S) : S) = 0 := by
    change ((ringChar (ResidueField S) : ℕ) : ResidueField S) = 0
    exact (ringChar.spec (ResidueField S) (ringChar (ResidueField S))).2 dvd_rfl
  have hpmem : (ringChar (ResidueField S) : S) ∈ maximalIdeal S := by
    change Ideal.Quotient.mk (maximalIdeal S) (ringChar (ResidueField S) : S) = 0 at hpzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hpzero
  -- Passing to powers preserves membership in the corresponding ideal powers.
  exact Ideal.pow_mem_pow hpmem n

/-- Helper for Chap10 Remark 10 160 9: a sufficiently high residue-characteristic power vanishes
in a shallower maximal-ideal quotient. -/
private theorem residueCharPow_quotient_eq_zero_of_le
    (A : Type u) [CommRing A] [IsLocalRing A] {a b : ℕ} (hab : a ≤ b) :
    (((ringChar (ResidueField A)) ^ b : ℕ) : A ⧸ (maximalIdeal A)^a) = 0 := by
  rw [Nat.cast_pow]
  change Ideal.Quotient.mk ((maximalIdeal A)^a)
      (((ringChar (ResidueField A) : A) ^ b)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.pow_le_pow_right hab) (residueCharPow_mem_maximalIdealPow (S := A) b)

/-- Helper for Chap10 Remark 10 160 9: the first positive quotient map is the chosen residue-field
equivalence, viewed as a map to `A ⧸ maximalIdeal A ^ 1`. -/
private theorem cohenLiftResidueQuotientMap
    {C : Type u} [CommRing C] [IsCohenRing C]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (e : ResidueField C ≃+* ResidueField A) :
    ∃ g : C →+* A ⧸ (maximalIdeal A) ^ (1 : ℕ),
      g = ((Ideal.quotEquivOfEq
        (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
          (e.toRingHom.comp (IsLocalRing.residue C)) := by
  -- The base stage is just the residue map, followed by the prescribed residue-field equivalence.
  refine ⟨_, rfl⟩

/-- Helper for Chap10 Remark 10 160 9: any Cohen stage map to `A ⧸ m^(n+1)` kills the next
source residue-characteristic power. -/
private theorem cohenLift_kills_residueChar_pow
    {C : Type u} [CommRing C] [IsCohenRing C]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (e : ResidueField C ≃+* ResidueField A) (n : ℕ)
    (g : C →+* A ⧸ (maximalIdeal A) ^ (n + 1)) :
    Ideal.span ({((ringChar (ResidueField C) : C) ^ (n + 2))} : Set C) ≤ RingHom.ker g := by
  rw [Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  change g ((ringChar (ResidueField C) : C) ^ (n + 2)) = 0
  rw [map_pow, map_natCast]
  have hchar : ringChar (ResidueField C) = ringChar (ResidueField A) := by
    rw [ringChar.eq_iff]
    exact e.toRingHom.charP e.injective _
  -- Rewrite the source characteristic through the chosen residue-field equivalence and then kill
  -- it in the quotient by maximal-ideal powers.
  change Ideal.Quotient.mk ((maximalIdeal A) ^ (n + 1))
      (((ringChar (ResidueField C) : ℕ) : A) ^ (n + 2)) = 0
  rw [hchar]
  simpa [Nat.cast_pow] using
    residueCharPow_quotient_eq_zero_of_le (A := A)
      (a := n + 1) (b := n + 2) (by omega)

/-- Helper for Chap10 Remark 10 160 9: a Cohen stage map factors through the next source
residue-characteristic quotient. -/
private theorem cohenLift_factor_through_source_quotient
    {C : Type u} [CommRing C] [IsCohenRing C]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (e : ResidueField C ≃+* ResidueField A) (n : ℕ)
    (g : C →+* A ⧸ (maximalIdeal A) ^ (n + 1)) :
    ∃ qg : C ⧸ Ideal.span ({((ringChar (ResidueField C) : C) ^ (n + 2))} : Set C) →+*
        A ⧸ (maximalIdeal A) ^ (n + 1),
      qg.comp (Ideal.Quotient.mk _) = g := by
  -- The previous power-killing lemma gives the kernel containment required by the quotient
  -- universal property.
  refine ⟨Ideal.Quotient.lift _ g ?_, ?_⟩
  · exact cohenLift_kills_residueChar_pow (A := A) e n g
  · ext x
    rfl

/-- Helper for Chap10 Remark 10 160 9: a ring homomorphism between `ZMod N`-algebras respects the
scalar maps automatically. -/
private theorem zmodAlgebraMap_commutes_of_ringHom
    {N : ℕ} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra (ZMod N) A] [Algebra (ZMod N) B] (f : A →+* B) :
    ∀ z : ZMod N, f ((algebraMap (ZMod N) A) z) = (algebraMap (ZMod N) B) z := by
  intro z
  have h : f.comp (algebraMap (ZMod N) A) = algebraMap (ZMod N) B := by
    exact RingHom.ext_zmod _ _
  exact RingHom.congr_fun h z

/-- Helper for Chap10 Remark 10 160 9: the canonical quotient by a power of the residue
characteristic is naturally a `ZMod`-algebra. -/
noncomputable local instance quotientResidueCharPowAlgebra
    {Λ : Type u} [CommRing Λ] [IsCohenRing Λ] (n : ℕ+) :
    Algebra (ZMod ((ringChar (ResidueField Λ)) ^ (n : ℕ)))
      (Λ ⧸ Ideal.span {(((ringChar (ResidueField Λ)) ^ (n : ℕ)) : Λ)}) := by
  let I : Ideal Λ := Ideal.span {(((ringChar (ResidueField Λ)) ^ (n : ℕ)) : Λ)}
  have hzero :
      (((ringChar (ResidueField Λ)) ^ (n : ℕ) : ℕ) : Λ ⧸ I) = 0 := by
    change Ideal.Quotient.mk I ((((ringChar (ResidueField Λ)) ^ (n : ℕ) : ℕ) : Λ)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.subset_span (by simp)
  exact
    RingHom.toAlgebra
      (ZMod.castHom (ringChar.dvd hzero) (Λ ⧸ I))

section

variable {Λ : Type u} [CommRing Λ] [IsCohenRing Λ]

local notation "p" => ringChar (ResidueField Λ)

/-- Helper for Chap10 Remark 10 160 9: no power of the Cohen-ring uniformizer lies in the ideal
generated by its next power. -/
private theorem residueChar_pow_not_mem_span_succ (m : ℕ) :
    ((p : Λ) ^ m) ∉ Ideal.span {((p : Λ) ^ (m + 1))} := by
  -- Membership in the next principal power would make `p` a unit after canceling `p ^ m`.
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hp0 : (p : Λ) ≠ 0 := by
    intro hp0
    exact IsDiscreteValuationRing.not_a_field Λ (by
      rw [IsCohenRing.maximalIdeal_eq_span_residueChar, hp0]
      simp)
  have hpm0 : (p : Λ) ^ m ≠ 0 := pow_ne_zero m hp0
  have hc' : (p : Λ) ^ m * ((p : Λ) * c) = (p : Λ) ^ m * 1 := by
    calc
      (p : Λ) ^ m * ((p : Λ) * c)
          = (p : Λ) ^ (m + 1) * c := by
              rw [pow_succ']
              ring
      _ = (p : Λ) ^ m * 1 := by
              rw [← hc]
              ring
  have hpunit : IsUnit (p : Λ) := by
    have hcancel := mul_left_cancel₀ hpm0 hc'
    exact IsUnit.of_mul_eq_one c hcancel
  exact IsCohenRing.residueChar_not_isUnit hpunit

/-- Helper for Chap10 Remark 10 160 9: the quotient by `p ^ n` has ring characteristic `p ^ n`. -/
private theorem ringChar_quotient_span_residueChar_pow_eq (n : ℕ+) :
    ringChar (Λ ⧸ Ideal.span {((p : Λ) ^ (n : ℕ))}) = p ^ (n : ℕ) := by
  -- Reduce to a successor exponent so the previous-power nonvanishing test applies.
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ m =>
      let I : Ideal Λ := Ideal.span {((p : Λ) ^ (m + 1))}
      let Q : Type u := Λ ⧸ I
      have hzeroQ : ((p ^ (m + 1) : ℕ) : Q) = 0 := by
        change Ideal.Quotient.mk I (((p ^ (m + 1) : ℕ) : Λ)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        rw [Nat.cast_pow]
        exact Ideal.subset_span (by simp)
      have hq_dvd : ringChar Q ∣ p ^ (m + 1) := ringChar.dvd hzeroQ
      have hq_not_dvd : ¬ ringChar Q ∣ p ^ m := by
        intro hdiv
        have hzeroPrev : ((p ^ m : ℕ) : Q) = 0 := (ringChar.spec Q (p ^ m)).2 hdiv
        have hmem : (p : Λ) ^ m ∈ I := by
          change Ideal.Quotient.mk I (((p ^ m : ℕ) : Λ)) = 0 at hzeroPrev
          rw [Nat.cast_pow] at hzeroPrev
          exact Ideal.Quotient.eq_zero_iff_mem.mp hzeroPrev
        exact residueChar_pow_not_mem_span_succ (Λ := Λ) m hmem
      exact Nat.eq_prime_pow_of_dvd_least_prime_pow
        IsCohenRing.residueChar_prime hq_not_dvd hq_dvd

/-- Helper for Chap10 Remark 10 160 9: the quotient of a Cohen ring by the ideal generated by the
`n`-th power of its residue characteristic has characteristic that same prime power. -/
private theorem quotient_charP_residueCharPow (n : ℕ+) :
    CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) := by
  -- Convert the computed quotient ring characteristic into the required `CharP` instance.
  exact ringChar.of_eq (ringChar_quotient_span_residueChar_pow_eq (Λ := Λ) n)

local instance quotientResidueCharPowCharP (n : ℕ+) :
    CharP (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) (p ^ (n : ℕ)) :=
  quotient_charP_residueCharPow n

/-- Helper for Chap10 Remark 10 160 9: the residue field has characteristic `p`. -/
private theorem residueField_charP_residueChar : CharP (ResidueField Λ) p := by
  -- This is the defining property of `p` as the ring characteristic of the residue field.
  exact ringChar.of_eq rfl

/-- Helper for Chap10 Remark 10 160 9: the first power of the residue characteristic is prime. -/
private theorem residueChar_pow_one_prime : Nat.Prime (p ^ ((1 : ℕ+) : ℕ)) := by
  -- Normalize the first power back to the residue characteristic prime.
  simpa [pow_one] using IsCohenRing.residueChar_prime (R := Λ)

/-- Helper for Chap10 Remark 10 160 9: the first-power ideal is the residue-characteristic ideal. -/
private theorem span_residueChar_pow_one_eq :
    Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)} = Ideal.span {((p : Λ))} := by
  -- This normalizes the quotient used by the positive-natural statement to the residue field
  -- quotient owner from the Cohen-ring definition.
  ext x
  simp [pow_one]

/-- Helper for Chap10 Remark 10 160 9: use first-power primality locally. -/
local instance residueCharPowOnePrimeFact : Fact (Nat.Prime (p ^ ((1 : ℕ+) : ℕ))) :=
  Fact.mk (residueChar_pow_one_prime (Λ := Λ))

/-- Helper for Chap10 Remark 10 160 9: use the first-power characteristic on the residue field. -/
local instance residueFieldCharPResidueCharPowOneInstance :
    CharP (ResidueField Λ) (p ^ ((1 : ℕ+) : ℕ)) := by
  -- Rewrite the characteristic from `p` to `p ^ 1`.
  simpa [pow_one] using residueField_charP_residueChar (Λ := Λ)

/-- Helper for Chap10 Remark 10 160 9: the first truncation has its explicit `ZMod (p ^ 1)`-algebra. -/
noncomputable local instance quotientResidueCharPowOneAlgebra :
    Algebra (ZMod (p ^ ((1 : ℕ+) : ℕ)))
      (Λ ⧸ Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)}) :=
  quotientResidueCharPowAlgebra (Λ := Λ) (n := (1 : ℕ+))

/-- Helper for Chap10 Remark 10 160 9: the residue field is a `ZMod (p ^ 1)`-algebra. -/
noncomputable local instance residueFieldResidueCharPowOneAlgebra :
    Algebra (ZMod (p ^ ((1 : ℕ+) : ℕ))) (ResidueField Λ) :=
  ZMod.algebra _ _

/-- Helper for Chap10 Remark 10 160 9: the first Cohen-ring truncation `Λ ⧸ (p)` is formally
smooth over `ZMod (p ^ 1)`. -/
private theorem cohenRing_residueChar_quotient_formallySmooth :
    Algebra.FormallySmooth (ZMod (p ^ ((1 : ℕ+) : ℕ)))
      (Λ ⧸ Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)}) := by
  -- Identify the first truncation with the residue field as a `ZMod (p ^ 1)`-algebra.
  let eRing : (Λ ⧸ Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)}) ≃+* ResidueField Λ :=
    (Ideal.quotEquivOfEq (span_residueChar_pow_one_eq (Λ := Λ))).trans
      (IsCohenRing.quotientSpanResidueCharRingEquiv (R := Λ))
  let e :
      (Λ ⧸ Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)}) ≃ₐ[ZMod (p ^ ((1 : ℕ+) : ℕ))]
        ResidueField Λ :=
    { eRing with
      commutes' := by
        intro x
        rcases ZMod.intCast_surjective x with ⟨m, rfl⟩
        rw [map_intCast
          (algebraMap (ZMod (p ^ ((1 : ℕ+) : ℕ)))
            (Λ ⧸ Ideal.span {((p ^ ((1 : ℕ+) : ℕ)) : Λ)})) m]
        rw [map_intCast (algebraMap (ZMod (p ^ ((1 : ℕ+) : ℕ))) (ResidueField Λ)) m]
        exact map_intCast eRing m }
  -- The residue field is formally smooth over the perfect prime field, and the algebra
  -- equivalence transports formal smoothness back to the quotient.
  have hResidue :
      Algebra.FormallySmooth (ZMod (p ^ ((1 : ℕ+) : ℕ))) (ResidueField Λ) := by
    letI : PerfectField (ZMod (p ^ ((1 : ℕ+) : ℕ))) := inferInstance
    letI : Algebra.IsSeparableOver (ZMod (p ^ ((1 : ℕ+) : ℕ))) (ResidueField Λ) :=
      Algebra.IsSeparableOver.of_perfectField
    -- Over the perfect prime field `ZMod p`, every field extension is formally smooth.
    exact Algebra.formallySmooth_of_isSeparableOver
  letI : Algebra.FormallySmooth (ZMod (p ^ ((1 : ℕ+) : ℕ))) (ResidueField Λ) := hResidue
  exact Algebra.FormallySmooth.of_equiv e.symm

/-- Helper for Chap10 Remark 10 160 9: the next residue-characteristic power ideal is contained
in the preceding power ideal. -/
private theorem span_residueChar_pow_succ_le (r : ℕ) :
    Ideal.span {((p : Λ) ^ (r + 2))} ≤ Ideal.span {((p : Λ) ^ (r + 1))} := by
  -- It is enough to show that the single generator `p^(r+2)` is a multiple of `p^(r+1)`.
  rw [Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  have hmem : (p : Λ) ^ (r + 1) * p ∈ Ideal.span {((p : Λ) ^ (r + 1))} :=
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ((p : Λ) ^ (r + 1)))
  simpa [show r + 2 = r + 1 + 1 by omega, pow_succ] using hmem

/-- Helper for Chap10 Remark 10 160 9: quotienting `Λ ⧸ (p^(r+2))` by the image of
`(p^(r+1))` recovers the previous truncation `Λ ⧸ (p^(r+1))`. -/
private noncomputable def cohenQuotientPenultimateEquiv (r : ℕ) :
    let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
    let J : Ideal S :=
      Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
        (Ideal.span {((p : Λ) ^ (r + 1))})
    (S ⧸ J) ≃+* (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) := by
  let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
  let J : Ideal S :=
    Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
      (Ideal.span {((p : Λ) ^ (r + 1))})
  -- This is the third-isomorphism theorem for the inclusion of adjacent principal powers.
  exact DoubleQuot.quotQuotEquivQuotOfLE (span_residueChar_pow_succ_le (Λ := Λ) r)

/-- Helper for Chap10 Remark 10 160 9: the kernel of the reduction
`ZMod (p^(r+2)) → ZMod (p^(r+1))` is generated by `p^(r+1)`. -/
private theorem zmod_ker_castHom_eq_penultimate (r : ℕ) :
    RingHom.ker
      (ZMod.castHom (pow_dvd_pow p (by omega : r + 1 ≤ r + 2)) (ZMod (p ^ (r + 1)))) =
      Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))} := by
  -- Work on integer representatives; reduction to the lower modulus is zero exactly when the
  -- representative is divisible by `p^(r+1)`.
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    have hzero : (a : ZMod (p ^ (r + 1))) = 0 := by
      simpa [ZMod.castHom_apply] using hx
    have hdiv : (p ^ (r + 1) : ℤ) ∣ a := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd a (p ^ (r + 1))).mp hzero
    rcases hdiv with ⟨b, hb⟩
    rw [Ideal.mem_span_singleton]
    use (b : ZMod (p ^ (r + 2)))
    rw [hb]
    norm_num
  · intro hx
    rw [RingHom.mem_ker]
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    rw [Ideal.mem_span_singleton] at hx
    rcases hx with ⟨c, hc⟩
    let hdivpow : p ^ (r + 1) ∣ p ^ (r + 2) := pow_dvd_pow p (by omega : r + 1 ≤ r + 2)
    let f : ZMod (p ^ (r + 2)) →+* ZMod (p ^ (r + 1)) :=
      ZMod.castHom hdivpow (ZMod (p ^ (r + 1)))
    have hmap := congrArg f hc
    rw [map_mul] at hmap
    have hpzero : ((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 1))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (p ^ (r + 1))) (p ^ (r + 1)) (p ^ (r + 1))).2 dvd_rfl
    have hzeroF : f (a : ZMod (p ^ (r + 2))) = 0 := by
      rw [map_natCast] at hmap
      simpa [hpzero] using hmap
    simpa [f] using hzeroF

/-- Helper for Chap10 Remark 10 160 9: quotienting `ZMod (p^(r+2))` by the penultimate power
ideal recovers `ZMod (p^(r+1))`. -/
private noncomputable def zmodPowQuotientPenultimateEquiv (r : ℕ) :
    let R : Type := ZMod (p ^ (r + 2))
    let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
    (R ⧸ I) ≃+* ZMod (p ^ (r + 1)) := by
  let R : Type := ZMod (p ^ (r + 2))
  let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
  let hdivpow : p ^ (r + 1) ∣ p ^ (r + 2) := pow_dvd_pow p (by omega : r + 1 ≤ r + 2)
  let f : R →+* ZMod (p ^ (r + 1)) := ZMod.castHom hdivpow (ZMod (p ^ (r + 1)))
  -- The first isomorphism theorem for the reduction map gives the desired quotient form.
  exact (Ideal.quotEquivOfEq (zmod_ker_castHom_eq_penultimate (Λ := Λ) r).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f) (ZMod.castHom_surjective hdivpow))

/-- Helper for Chap10 Remark 10 160 9: in `ZMod (p^(r+2))`, the ideal generated by `p^(r+1)` has
square zero. -/
private theorem zmodPenultimatePower_square_zero (r : ℕ) :
    (Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))}) ^ 2 = ⊥ := by
  -- The square is generated by `p^(2*(r+1))`, which is zero modulo `p^(r+2)`.
  rw [Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_bot]
  rw [← Nat.cast_pow]
  rw [CharP.cast_eq_zero_iff (ZMod (p ^ (r + 2))) (p ^ (r + 2))]
  rw [← pow_mul]
  exact pow_dvd_pow p (by omega)

/-- Helper for Chap10 Remark 10 160 9: multiplying by `p^(r+1)` tests membership in `(p)` modulo
the next principal power. -/
private theorem residueChar_pow_mul_mem_span_pow_succ_iff_mem_span (r : ℕ) (x : Λ) :
    ((p : Λ) ^ (r + 1) * x ∈ Ideal.span {((p : Λ) ^ (r + 2))}) ↔
      x ∈ Ideal.span {((p : Λ))} := by
  constructor
  · intro hx
    rw [Ideal.mem_span_singleton] at hx ⊢
    rcases hx with ⟨c, hc⟩
    use c
    have hp0 : (p : Λ) ≠ 0 := by
      intro hp0
      exact IsDiscreteValuationRing.not_a_field Λ (by
        rw [IsCohenRing.maximalIdeal_eq_span_residueChar, hp0]
        simp)
    have hpow0 : (p : Λ) ^ (r + 1) ≠ 0 := pow_ne_zero _ hp0
    have hcancel : x = (p : Λ) * c := by
      -- Cancel the nonzero power `p^(r+1)` after rewriting the target power as `p^(r+1) * p`.
      apply mul_left_cancel₀ hpow0
      calc
        (p : Λ) ^ (r + 1) * x = (p : Λ) ^ (r + 2) * c := hc
        _ = (p : Λ) ^ (r + 1) * ((p : Λ) * c) := by
          rw [show r + 2 = r + 1 + 1 by omega, pow_succ]
          ring
    exact hcancel
  · intro hx
    rw [Ideal.mem_span_singleton] at hx ⊢
    rcases hx with ⟨c, hc⟩
    use c
    -- The converse is the same power identity, now read as a divisibility witness.
    rw [hc]
    rw [show r + 2 = r + 1 + 1 by omega, pow_succ]
    ring

/-- Helper for Chap10 Remark 10 160 9: the next-next power ideal is contained in `(p)`. -/
private theorem span_residueChar_pow_succ_succ_le_span_residueChar (r : ℕ) :
    Ideal.span {((p : Λ) ^ (r + 2))} ≤ Ideal.span {((p : Λ))} := by
  rw [Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  -- It is enough to exhibit `p^(r+2)` as `p * p^(r+1)`.
  change (p : Λ) ^ (r + 2) ∈ Ideal.span {((p : Λ))}
  rw [Ideal.mem_span_singleton]
  use (p : Λ) ^ (r + 1)
  rw [show r + 2 = 1 + (r + 1) by omega, pow_add]
  ring

/-- Helper for Chap10 Remark 10 160 9: membership in the image of `(p)` can be checked on any
representative modulo `p^(r+2)`. -/
private theorem quotient_mk_mem_map_span_residueChar_iff (r : ℕ) (x : Λ) :
    (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) x) ∈
        Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
          (Ideal.span {((p : Λ))}) ↔
      x ∈ Ideal.span {((p : Λ))} := by
  constructor
  · intro hx
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hsub : x - y ∈ Ideal.span {((p : Λ) ^ (r + 2))} := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp hxy.symm
    have hyx : x - y + y ∈ Ideal.span {((p : Λ))} :=
      add_mem (span_residueChar_pow_succ_succ_le_span_residueChar (Λ := Λ) r hsub) hy
    -- Replace the representative by the chosen image-lift; their difference lies in `(p)`.
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hyx
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

/-- Helper for Chap10 Remark 10 160 9: in `Λ/(p^(r+2))`, the annihilator of multiplication by
`p^(r+1)` is exactly the image of the ideal `(p)`. -/
private theorem cohenPenultimateMul_ker_iff_mem_span_residueChar (r : ℕ)
    (x : Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}) :
    ((Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) ((p : Λ) ^ (r + 1))) * x = 0) ↔
      x ∈ Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
        (Ideal.span {((p : Λ))}) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Move the quotient equality back to the principal-ideal calculation on representatives.
  rw [← map_mul]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (residueChar_pow_mul_mem_span_pow_succ_iff_mem_span (Λ := Λ) r y).trans
    (quotient_mk_mem_map_span_residueChar_iff (Λ := Λ) r y).symm

/-- Helper for Chap10 Remark 10 160 9: use the characteristic of the successor truncation. -/
local instance quotientResidueCharPowSuccCharP (r : ℕ) :
    CharP (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}) (p ^ (r + 2)) :=
  quotient_charP_residueCharPow (Λ := Λ) ⟨r + 2, by omega⟩

/-- Helper for Chap10 Remark 10 160 9: use the `ZMod (p^(r+2))`-algebra on the successor
truncation. -/
noncomputable local instance quotientResidueCharPowSuccAlgebra (r : ℕ) :
    Algebra (ZMod (p ^ (r + 2))) (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}) :=
  ZMod.algebra _ _ 

/-- Helper for Chap10 Remark 10 160 9: a tensor out of a principal ideal is represented by the
principal generator tensored with one module element. -/
private theorem tensorProduct_span_singleton_eq_tmul_generator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) (z : (Ideal.span ({a} : Set R)) ⊗[R] M) :
    ∃ m : M, z =
      ((⟨a, Ideal.mem_span_singleton_self a⟩ : Ideal.span ({a} : Set R)) ⊗ₜ[R] m) := by
  refine TensorProduct.induction_on z ?zero ?tmul ?add
  · exact ⟨0, by simp⟩
  · intro x m
    have hxmem : (x : R) ∈ Ideal.span ({a} : Set R) := x.property
    rw [Ideal.mem_span_singleton] at hxmem
    rcases hxmem with ⟨c, hc⟩
    refine ⟨c • m, ?_⟩
    -- Rewrite the ideal element as a scalar multiple of the chosen generator, then balance.
    rw [show x = c • (⟨a, Ideal.mem_span_singleton_self a⟩ : Ideal.span ({a} : Set R)) by
      ext
      simpa [smul_eq_mul, mul_comm] using hc]
    rw [TensorProduct.smul_tmul]
  · intro x y hx hy
    rcases hx with ⟨m, hm⟩
    rcases hy with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    -- Additivity of tensors combines the two generator-normal forms.
    rw [hm, hn]
    simp [TensorProduct.tmul_add]

/-- Helper for Chap10 Remark 10 160 9: the penultimate tensor multiplication map has trivial
kernel. -/
private theorem cohenPenultimateTensorMul_ker_eq_bot (r : ℕ) :
    LinearMap.ker
      (TensorProduct.lift
        ((LinearMap.lsmul (ZMod (p ^ (r + 2)))
            (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))})).comp
          (Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))}).subtype)) = ⊥ := by
  let R : Type := ZMod (p ^ (r + 2))
  let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
  let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
  let aR : R := ((p ^ (r + 1) : ℕ) : R)
  let aI : I := ⟨aR, by
    dsimp [I, aR]
    exact Ideal.mem_span_singleton_self _⟩
  letI : CharP S (p ^ (r + 2)) := quotient_charP_residueCharPow (Λ := Λ) ⟨r + 2, by omega⟩
  letI : Algebra R S := ZMod.algebra _ _
  rw [Submodule.eq_bot_iff]
  intro z hz
  rcases tensorProduct_span_singleton_eq_tmul_generator (R := R) (M := S) aR z with ⟨s, rfl⟩
  have hzmul : (algebraMap R S aR) * s = 0 := by
    -- The kernel condition says the generator-normal-form tensor multiplies to zero in `S`.
    have hz' := LinearMap.mem_ker.mp hz
    change ((LinearMap.lsmul R S) aI.1) s = 0 at hz'
    simpa [aI, LinearMap.lsmul_apply, Algebra.smul_def] using hz'
  have halg_a : algebraMap R S aR =
      Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) ((p : Λ) ^ (r + 1)) := by
    simp [aR, R, S, Nat.cast_pow]
  have hs_mem : s ∈ Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
        (Ideal.span {((p : Λ))}) := by
    -- Apply the annihilator computation to identify the right tensor factor as a `p`-multiple.
    exact (cohenPenultimateMul_ker_iff_mem_span_residueChar (Λ := Λ) r s).mp
      (by simpa [halg_a] using hzmul)
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hs_mem
  rcases hs_mem with ⟨y, hy, hys⟩
  rw [← hys]
  have hydiv : ∃ c : Λ, y = (p : Λ) * c := by
    rw [Ideal.mem_span_singleton] at hy
    rcases hy with ⟨c, hc⟩
    exact ⟨c, hc⟩
  rcases hydiv with ⟨c, rfl⟩
  have hpa_zero : (p : R) * aR = 0 := by
    change ((p : ℕ) : R) * (((p ^ (r + 1) : ℕ) : R)) = 0
    rw [← Nat.cast_mul]
    have hpow : p * p ^ (r + 1) = p ^ (r + 2) := by
      rw [show r + 2 = r + 1 + 1 by omega, pow_succ]
      ring
    rw [hpow]
    exact (CharP.cast_eq_zero_iff R (p ^ (r + 2)) (p ^ (r + 2))).2 dvd_rfl
  have hmk_pc : (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) ((p : Λ) * c) : S) =
      algebraMap R S (p : R) *
        Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) c := by
    simp [R, S]
  rw [hmk_pc]
  have hsmul_aI : (p : R) • aI = 0 := by
    ext
    simpa [aI] using hpa_zero
  -- The balanced tensor is zero because `p * p^(r+1)` vanishes in `ZMod (p^(r+2))`.
  calc
    aI ⊗ₜ[R]
        (algebraMap R S (p : R) *
          Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) c)
        = aI ⊗ₜ[R]
            ((p : R) •
              (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) c : S)) := by
          rw [Algebra.smul_def]
    _ = ((p : R) • aI) ⊗ₜ[R]
          (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}) c : S) := by
          rw [TensorProduct.tmul_smul]
          rw [TensorProduct.smul_tmul']
    _ = 0 := by
          rw [hsmul_aI]
          simp

/-- Helper for Chap10 Remark 10 160 9: formal smoothness transports across compatible base and
target ring equivalences. -/
private theorem formallySmooth_of_ringEquiv_base_target
    {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : eS.toRingHom.comp (algebraMap R S) =
      (algebraMap R' S').comp eR.toRingHom)
    (h : Algebra.FormallySmooth R' S') :
    Algebra.FormallySmooth R S := by
  -- Compose the smooth base equivalence, the known smooth algebra map, and the inverse target
  -- equivalence, then identify the composite with the source algebra map.
  rw [← RingHom.formallySmooth_algebraMap]
  have hR : RingHom.FormallySmooth eR.toRingHom :=
    RingHom.FormallySmooth.of_bijective eR.bijective
  have hAlg : RingHom.FormallySmooth (algebraMap R' S') :=
    RingHom.formallySmooth_algebraMap.mpr h
  have hcomp : RingHom.FormallySmooth ((algebraMap R' S').comp eR.toRingHom) := hR.comp hAlg
  have hS : RingHom.FormallySmooth eS.symm.toRingHom :=
    RingHom.FormallySmooth.of_bijective eS.symm.bijective
  have htarget :
      RingHom.FormallySmooth
        (eS.symm.toRingHom.comp ((algebraMap R' S').comp eR.toRingHom)) := hcomp.comp hS
  convert htarget using 1
  ext x
  have hx := RingHom.congr_fun hcomm x
  simpa [RingHom.comp_apply] using congrArg eS.symm hx

/-- Helper for Chap10 Remark 10 160 9: module flatness transports across compatible base and
target ring equivalences. -/
private theorem flat_of_ringEquiv_base_target
    {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : eS.toRingHom.comp (algebraMap R S) =
      (algebraMap R' S').comp eR.toRingHom)
    (h : Module.Flat R' S') :
    Module.Flat R S := by
  -- First restrict scalars along the base equivalence, then move the target module across the
  -- compatible ring equivalence.
  letI : Algebra R R' := eR.toRingHom.toAlgebra
  letI : Module R S' := Module.compHom S' eR.toRingHom
  letI : IsScalarTower R R' S' := IsScalarTower.of_compHom R R' S'
  have hflatRR' : Module.Flat R R' := by
    let eAlg : R ≃ₐ[R] R' :=
      AlgEquiv.ofRingEquiv (R := R) (f := eR) (by intro x; rfl)
    exact (Module.Flat.equiv_iff eAlg.toLinearEquiv).mp inferInstance
  have hflatRS' : Module.Flat R S' := by
    letI : Module.Flat R R' := hflatRR'
    letI : Module.Flat R' S' := h
    exact Module.Flat.trans R R' S'
  let eLin : S ≃ₗ[R] S' :=
    { eS.toAddEquiv with
      map_smul' := by
        intro r s
        have hr : eS (algebraMap R S r) = algebraMap R' S' (eR r) :=
          RingHom.congr_fun hcomm r
        calc
          eS.toAddEquiv.toFun (r • s) = eS ((algebraMap R S r) * s) := by
            simp [Algebra.smul_def]
          _ = eS (algebraMap R S r) * eS s := map_mul eS _ _
          _ = algebraMap R' S' (eR r) * eS s := by rw [hr]
          _ = (eR r) • eS s := by rw [Algebra.smul_def]
          _ = (RingHom.id R) r • eS.toAddEquiv.toFun s := rfl }
  letI : Module.Flat R S' := hflatRS'
  exact Module.Flat.of_linearEquiv eLin

/-- Helper for Chap10 Remark 10 160 9: the square-zero ideal's image in the successor Cohen
truncation is the image of the corresponding Cohen-ring power. -/
private theorem cohenPenultimateTargetIdeal_eq (r : ℕ) :
    Ideal.map (algebraMap (ZMod (p ^ (r + 2)))
        (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}))
      (Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))}) =
    Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : Λ) ^ (r + 2))}))
      (Ideal.span {((p : Λ) ^ (r + 1))}) := by
  -- Both ideals are generated by the same quotient class of `p^(r+1)`.
  simp [Ideal.map_span, Nat.cast_pow]

/-- Helper for Chap10 Remark 10 160 9: the adjacent base and target quotient equivalences commute
with the closed-fiber algebra map. -/
private theorem cohenPenultimateClosedFiber_algebraMap_eq (r : ℕ) :
    let R : Type := ZMod (p ^ (r + 2))
    let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
    let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
    let eR : (R ⧸ I) ≃+* ZMod (p ^ (r + 1)) :=
      zmodPowQuotientPenultimateEquiv (Λ := Λ) r
    let eS :
        (S ⧸ Ideal.map (algebraMap R S) I) ≃+*
          (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
      (Ideal.quotEquivOfEq (cohenPenultimateTargetIdeal_eq (Λ := Λ) r)).trans
        (cohenQuotientPenultimateEquiv (Λ := Λ) r)
    letI : CharP (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) (p ^ (r + 1)) :=
      quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
    letI : Algebra (ZMod (p ^ (r + 1))) (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
      ZMod.algebra _ _
    eS.toRingHom.comp (algebraMap (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) =
      (algebraMap (ZMod (p ^ (r + 1)))
        (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))})).comp eR.toRingHom := by
  -- Check the equality on integer representatives; all quotient maps send `m` to the class of
  -- the same integer in the previous Cohen truncation.
  dsimp only
  ext x
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
  simp [zmodPowQuotientPenultimateEquiv, cohenQuotientPenultimateEquiv]

/-- Helper for Chap10 Remark 10 160 9: the closed fiber of the successor truncation is formally
smooth after identifying it with the previous truncation. -/
private theorem cohenPenultimateClosedFiber_formallySmooth (r : ℕ) :
    let R : Type := ZMod (p ^ (r + 2))
    let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
    let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
    let T : Type := ZMod (p ^ (r + 1))
    let B : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}
    letI : CharP B (p ^ (r + 1)) :=
      quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
    letI : Algebra T B := ZMod.algebra _ _
    Algebra.FormallySmooth T B →
      Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) := by
  -- Transport the previous formal-smoothness owner through the named base and target quotients.
  dsimp only
  intro hprev
  letI : CharP (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) (p ^ (r + 1)) :=
    quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
  letI : Algebra (ZMod (p ^ (r + 1))) (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
    ZMod.algebra _ _
  let eR :
      (ZMod (p ^ (r + 2)) ⧸
        Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))}) ≃+*
        ZMod (p ^ (r + 1)) :=
    zmodPowQuotientPenultimateEquiv (Λ := Λ) r
  let eS :
      ((Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}) ⧸
        Ideal.map
          (algebraMap (ZMod (p ^ (r + 2)))
            (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}))
          (Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))})) ≃+*
        (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
    (Ideal.quotEquivOfEq (cohenPenultimateTargetIdeal_eq (Λ := Λ) r)).trans
      (cohenQuotientPenultimateEquiv (Λ := Λ) r)
  exact
    formallySmooth_of_ringEquiv_base_target eR eS
      (cohenPenultimateClosedFiber_algebraMap_eq (Λ := Λ) r) hprev

/-- Helper for Chap10 Remark 10 160 9: the closed fiber of the successor truncation is flat after
identifying it with the previous truncation. -/
private theorem cohenPenultimateClosedFiber_flat (r : ℕ) :
    let R : Type := ZMod (p ^ (r + 2))
    let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
    let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
    let T : Type := ZMod (p ^ (r + 1))
    let B : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}
    letI : CharP B (p ^ (r + 1)) :=
      quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
    letI : Algebra T B := ZMod.algebra _ _
    Module.Flat T B →
      Module.Flat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) := by
  -- The same commuting square gives the closed-fiber flatness owner needed for the induction.
  dsimp only
  intro hprev
  letI : CharP (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) (p ^ (r + 1)) :=
    quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
  letI : Algebra (ZMod (p ^ (r + 1))) (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
    ZMod.algebra _ _
  let eR :
      (ZMod (p ^ (r + 2)) ⧸
        Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))}) ≃+*
        ZMod (p ^ (r + 1)) :=
    zmodPowQuotientPenultimateEquiv (Λ := Λ) r
  let eS :
      ((Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}) ⧸
        Ideal.map
          (algebraMap (ZMod (p ^ (r + 2)))
            (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}))
          (Ideal.span {(((p ^ (r + 1) : ℕ) : ZMod (p ^ (r + 2))))})) ≃+*
        (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
    (Ideal.quotEquivOfEq (cohenPenultimateTargetIdeal_eq (Λ := Λ) r)).trans
      (cohenQuotientPenultimateEquiv (Λ := Λ) r)
  exact
    flat_of_ringEquiv_base_target eR eS
      (cohenPenultimateClosedFiber_algebraMap_eq (Λ := Λ) r) hprev

/-- Helper for Chap10 Remark 10 160 9: flatness of the ideal quotient gives flatness of the same
quotient viewed as the scalar submodule quotient. -/
private theorem flat_quotient_smul_top_of_flat_ideal_quotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R)
    (h : Module.Flat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
  -- Rewrite the scalar submodule `I • S` as the underlying submodule of the mapped ideal, then
  -- upgrade the resulting `R`-linear quotient comparison to `R/I`-linearity.
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let eDenom :
      (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R]
        S ⧸ Submodule.restrictScalars R J :=
    Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_top_eq_map])
  let eRestrict :
      (S ⧸ Submodule.restrictScalars R J) ≃ₗ[R] S ⧸ J :=
    Submodule.Quotient.restrictScalarsEquiv R J
  let eR : (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R] S ⧸ J :=
    eDenom.trans eRestrict
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  let e : (S ⧸ (I • (⊤ : Submodule R S))) ≃ₗ[R ⧸ I] S ⧸ J :=
    eR.extendScalarsOfSurjective hsurj
  exact Module.Flat.of_linearEquiv e

/-- Helper for Chap10 Remark 10 160 9: quotienting a lifted module by `J • ⊤` is canonically the
same as quotienting the original module by `J • ⊤`. -/
private theorem ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    Nonempty ((((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A]
        (N ⧸ (J • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{u} N)))
      (J • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
      (by
        -- The `ULift` module equivalence preserves the quotient denominator `J • ⊤`.
        simp [Submodule.map_smul''])
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Chap10 Remark 10 160 9: choose the quotient-module equivalence induced by
`ULift.moduleEquiv`. -/
private noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N] :
    ((ULift.{u} N) ⧸ (J • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  Classical.choice ulift_module_quotient_equiv_exists

/-- Helper for Chap10 Remark 10 160 9: quotienting the lifted base ring by the image of `J`
recovers the original quotient ring. -/
private theorem ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (J : Ideal A) {N : Type v} [AddCommGroup N] [Module A N] :
    J =
      (J.map (algebraMap A (ULift.{v} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{v} A ≃ₐ[A] A) : ULift.{v} A →+* A) := by
  let eu : ULift.{v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- `ULift.algEquiv` is inverse to the canonical lift `A → ULift A`.
  calc
    J = J.map (RingHom.id A) := by simp
    _ = J.map ((eu : ULift.{v} A →+* A).comp (algebraMap A (ULift.{v} A))) := by
          ext a
          rfl
    _ = (J.map (algebraMap A (ULift.{v} A))).map (eu : ULift.{v} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Chap10 Remark 10 160 9: the `ULift` presentation of the quotient ring is
canonically ring-equivalent to the original quotient ring. -/
private noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (J : Ideal A) {N : Type v} [AddCommGroup N] [Module A N] :
    ((ULift.{v} A) ⧸ J.map (algebraMap A (ULift.{v} A))) ≃+* (A ⧸ J) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux (J := J) (N := N))).toRingEquiv

/-- Helper for Chap10 Remark 10 160 9: an element of an ideal maps linearly into its extension. -/
private noncomputable def ideal_to_mapped_ideal
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    I →ₗ[A] Ideal.map (algebraMap A B) I :=
  { toFun := fun a ↦
      ⟨algebraMap A B (a : A), Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
    map_add' := by
      intro a b
      ext
      simp
    map_smul' := by
      intro r a
      ext
      simp [Algebra.smul_def] }

/-- Helper for Chap10 Remark 10 160 9: the tensor bridge from an ideal to its extension. -/
private noncomputable def mapped_ideal_tensor_map
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    I ⊗[A] N →ₗ[A] Ideal.map (algebraMap A B) I ⊗[B] N :=
  TensorProduct.lift
    { toFun := fun a ↦
        (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
          (ideal_to_mapped_ideal (A := A) (B := B) I a)).restrictScalars A
      map_add' := by
        intro a b
        ext n
        simpa [ideal_to_mapped_ideal] using
          (TensorProduct.add_tmul
            (ideal_to_mapped_ideal (A := A) (B := B) I a)
            (ideal_to_mapped_ideal (A := A) (B := B) I b) n)
      map_smul' := by
        intro r a
        ext n
        simpa [ideal_to_mapped_ideal, Algebra.smul_def] using
          (TensorProduct.smul_tmul'
            (R := B) (r := algebraMap A B r)
            (m := ideal_to_mapped_ideal (A := A) (B := B) I a) (n := n)).symm }

/-- Helper for Chap10 Remark 10 160 9: the tensor bridge from an ideal to its extension is
surjective. -/
private lemma mapped_ideal_tensor_map_surjective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    Function.Surjective (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I) := by
  have hmap_span :
      Ideal.map (algebraMap A B) I =
        Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
    calc
      Ideal.map (algebraMap A B) I =
          Ideal.map (algebraMap A B) (Ideal.span (I : Set A)) := by
            rw [Ideal.span_eq]
      _ = Ideal.span ((algebraMap A B) '' (I : Set A)) := by
            rw [Ideal.map_span]
      _ = Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
            congr 1
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              exact ⟨⟨a, ha⟩, rfl⟩
            · rintro ⟨a, rfl⟩
              exact ⟨a, a.2, rfl⟩
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro y n
    have hy_span :
        (y : B) ∈ Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
      simpa [hmap_span] using y.2
    rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hy_span with ⟨c, hc⟩
    let xPre :=
      Finset.sum c.support fun a ↦ (a ⊗ₜ[A] ((c a) • n) : I ⊗[A] N)
    let yTerms : I → Ideal.map (algebraMap A B) I := fun a ↦
      ⟨c a * algebraMap A B (a : A),
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap A B) a.2)⟩
    refine ⟨xPre, ?_⟩
    calc
      mapped_ideal_tensor_map (A := A) (B := B) (N := N) I xPre =
          Finset.sum c.support fun a ↦
            mapped_ideal_tensor_map (A := A) (B := B) (N := N) I
              (a ⊗ₜ[A] ((c a) • n)) := by
            simp [xPre, mapped_ideal_tensor_map]
      _ = Finset.sum c.support fun a ↦ yTerms a ⊗ₜ[B] n := by
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            change
              (ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] ((c a) • n) =
                yTerms a ⊗ₜ[B] n
            calc
              (ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] ((c a) • n) =
                  (c a • ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] n := by
                    simpa using
                      (TensorProduct.smul_tmul'
                        (R := B) (r := c a)
                        (m := ideal_to_mapped_ideal (A := A) (B := B) I a)
                        (n := n)).symm
              _ = yTerms a ⊗ₜ[B] n := by
                    apply congrArg (fun t : Ideal.map (algebraMap A B) I ↦ t ⊗ₜ[B] n)
                    ext
                    simp [yTerms, ideal_to_mapped_ideal, mul_comm]
      _ = (Finset.sum c.support yTerms) ⊗ₜ[B] n := by
            simpa using (TensorProduct.sum_tmul (R := B) c.support yTerms n).symm
      _ = y ⊗ₜ[B] n := by
            apply congrArg (fun t : Ideal.map (algebraMap A B) I ↦ t ⊗ₜ[B] n)
            ext
            simpa [yTerms, Finsupp.sum] using hc
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    exact ⟨x' + y', by simp [mapped_ideal_tensor_map]⟩

/-- Helper for Chap10 Remark 10 160 9: the mapped-ideal multiplication map agrees with the source
multiplication map after the canonical tensor bridge. -/
private lemma mapped_ideal_tensor_to_module_comp
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    (TensorProduct.lift
      ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)).restrictScalars A ∘ₗ
        mapped_ideal_tensor_map (A := A) (B := B) (N := N) I =
      TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype) := by
  ext a n
  simp [mapped_ideal_tensor_map, ideal_to_mapped_ideal]

/-- Helper for Chap10 Remark 10 160 9: injectivity of `I ⊗[A] N → N` descends to injectivity of
`Ideal.map I ⊗[B] N → N`. -/
private lemma mapped_ideal_tensor_to_module_injective_of_source_injective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N]
    (hinj :
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype))) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)) := by
  let μA : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  let μB : Ideal.map (algebraMap A B) I ⊗[B] N →ₗ[B] N :=
    TensorProduct.lift
      ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)
  have hcompare :
      (μB.restrictScalars A).comp
          (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I) =
        μA := by
    simpa [μA, μB] using
      mapped_ideal_tensor_to_module_comp (A := A) (B := B) (N := N) I
  intro x y hxy
  have hsurj := mapped_ideal_tensor_map_surjective (A := A) (B := B) (N := N) I
  rcases hsurj x with ⟨x', rfl⟩
  rcases hsurj y with ⟨y', rfl⟩
  have hxy' : x' = y' := by
    apply hinj
    have hxcompare :
        (μB.restrictScalars A) (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I x') =
          μA x' := by
      simpa using congrArg (fun f ↦ f x') hcompare
    have hycompare :
        (μB.restrictScalars A) (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I y') =
          μA y' := by
      simpa using congrArg (fun f ↦ f y') hcompare
    exact hxcompare.symm.trans <| hxy.trans hycompare
  simpa using congrArg (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I) hxy'

/-- Helper for Chap10 Remark 10 160 9: injectivity of `J ⊗[A] N → N` is unchanged by lifting only
the module universe. -/
private theorem ulift_injective_tensor_transport
    {A : Type u} [CommRing A] {J : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N]
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp J.subtype)) := by
  let μ : J ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)
  let μu : J ⊗[A] ULift.{u} N →ₗ[A] ULift.{u} N :=
    TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp J.subtype)
  let eTensor :
      J ⊗[A] ULift.{u} N ≃ₗ[A] J ⊗[A] N :=
    TensorProduct.congr (LinearEquiv.refl A J) (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
  have hSquare :
      μ.comp eTensor.toLinearMap =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N).toLinearMap.comp μu := by
    -- Once `ULift N` is identified with `N`, both tensor multiplication maps are the same.
    ext j n
    rfl
  intro x y hxy
  apply eTensor.injective
  apply hinj
  calc
    μ (eTensor x) =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu x) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f x) hSquare
    _ =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu y) := by
          simpa using congrArg (fun z ↦ (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) z) hxy
    _ = μ (eTensor y) := by
          simpa [LinearMap.comp_apply] using (congrArg (fun f ↦ f y) hSquare).symm

/-- Helper for Chap10 Remark 10 160 9: the nilpotent-thickening closing step from quotient
flatness and injectivity of the stage multiplication map. -/
private theorem flat_of_nilpotent_ideal_from_flat_closed_fiber_and_injective_tensor
    {S : Type u} [CommRing S] {J : Ideal S}
    {N : Type u} [AddCommGroup N] [Module S N]
    (hJ : IsNilpotent J)
    (hflat : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))) :
    Module.Flat S N := by
  let _ := hJ
  let _ := hflat
  let _ := hinj
  -- Isolate the final nilpotent-thickening step without reimporting the broken source wrapper.
  exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hJ

/-- Helper for Chap10 Remark 10 160 9: a square-zero ideal with flat closed fiber and injective
tensor multiplication gives flatness after lifting universes to a common level. -/
private theorem flat_of_square_zero_ideal_of_flat_mod_ideal_and_kernel_eq_bot_ulift
    {S : Type u} [CommRing S] {N : Type v} [AddCommGroup N] [Module S N]
    {J : Ideal S}
    (hJ_sq : J ^ 2 = ⊥)
    (hflat : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥) :
    Module.Flat S N := by
  let Su : Type max u v := ULift.{v} S
  let Nu : Type max u v := ULift.{u} N
  letI : CommRing Su := inferInstance
  let Ju : Ideal Su := J.map (algebraMap S Su)
  let T : Type max u v := Su ⧸ Ju
  let B : Type u := S ⧸ J
  let eRing : T ≃+* B := ulift_quotient_ring_equiv (A := S) (J := J) (N := N)
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T (N ⧸ (J • (⊤ : Submodule S N))) :=
    Module.compHom (N ⧸ (J • (⊤ : Submodule S N))) (algebraMap T B)
  letI : IsScalarTower S T (N ⧸ (J • (⊤ : Submodule S N))) :=
    IsScalarTower.of_compHom S T (N ⧸ (J • (⊤ : Submodule S N)))
  letI : IsScalarTower T B (N ⧸ (J • (⊤ : Submodule S N))) :=
    IsScalarTower.of_compHom T B (N ⧸ (J • (⊤ : Submodule S N)))
  have hJu_sq : Ju ^ 2 = ⊥ := by
    -- The square-zero ideal survives the universe lift unchanged.
    simpa [Ju] using Algebra.Extension.ulift_map_square_zero (R := S) J hJ_sq
  have hJu : IsNilpotent Ju := ⟨2, hJu_sq⟩
  have hinj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) :=
    (LinearMap.ker_eq_bot).1 hker
  have hinj_u_source :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul S Nu).comp J.subtype)) := by
    -- First lift only the module universe in the source multiplication map.
    simpa [Nu] using ulift_injective_tensor_transport (A := S) (J := J) (N := N) hinj
  have hinj_u :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul Su Nu).comp Ju.subtype)) := by
    -- Then rewrite the ideal to its mapped image inside the lifted ring.
    simpa [Ju] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (A := S) (B := Su) (I := J) (N := Nu) hinj_u_source
  have hflatTB : Module.Flat T B := by
    -- The lifted closed fiber owner is ring-equivalent to the original quotient ring.
    let eAlg : B ≃ₐ[T] T :=
      AlgEquiv.ofRingEquiv (R := T) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        simp)
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat T (N ⧸ (J • (⊤ : Submodule S N))) := by
    -- Transport the given closed-fiber flatness across the quotient-ring equivalence.
    letI : Module.Flat T B := hflatTB
    letI : Module.Flat B (N ⧸ (J • (⊤ : Submodule S N))) := hflat
    exact Module.Flat.trans T B (N ⧸ (J • (⊤ : Submodule S N)))
  have hJu_restrict :
      ((Ju • (⊤ : Submodule Su Nu)).restrictScalars S) =
        (J • (⊤ : Submodule S Nu)) := by
    -- Restricting the lifted denominator from `Su` to `S` recovers `J • ⊤`.
    simpa [Ju] using
      (Ideal.smul_restrictScalars
        (R := S) (S := Su) (M := Nu) (I := J) (N := (⊤ : Submodule Su Nu)))
  have hsurjST : Function.Surjective (algebraMap S T) := by
    -- Every class in the lifted quotient has a representative coming from the original ring.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases x with ⟨s⟩
    exact ⟨s, rfl⟩
  have eOwnerS :
      (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) ≃ₗ[S]
        N ⧸ (J • (⊤ : Submodule S N)) := by
    let eRestrict :
        (Nu ⧸ ((Ju • (⊤ : Submodule Su Nu)).restrictScalars S)) ≃ₗ[S]
          Nu ⧸ (Ju • (⊤ : Submodule Su Nu)) :=
      Submodule.Quotient.restrictScalarsEquiv S (Ju • (⊤ : Submodule Su Nu))
    let eDenom :
        (Nu ⧸ ((Ju • (⊤ : Submodule Su Nu)).restrictScalars S)) ≃ₗ[S]
          Nu ⧸ (J • (⊤ : Submodule S Nu)) :=
      Submodule.quotEquivOfEq
        ((Ju • (⊤ : Submodule Su Nu)).restrictScalars S)
        (J • (⊤ : Submodule S Nu))
        hJu_restrict
    let eULift :
        (Nu ⧸ (J • (⊤ : Submodule S Nu))) ≃ₗ[S]
          N ⧸ (J • (⊤ : Submodule S N)) :=
      (ulift_module_quotient_equiv (A := S) (J := J) (N := N)).restrictScalars S
    -- Compare the lifted closed fiber to the original one by normalizing each denominator.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  have eOwner :
      (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) ≃ₗ[T]
        N ⧸ (J • (⊤ : Submodule S N)) :=
    -- Since `S → T` is surjective, the `S`-linear comparison upgrades to the owner ring `T`.
    eOwnerS.extendScalarsOfSurjective hsurjST
  have hflatClosed :
      Module.Flat T (Nu ⧸ (Ju • (⊤ : Submodule Su Nu))) := by
    -- The lifted closed fiber is flat by equivalence with the transported target module.
    letI : Module.Flat T (N ⧸ (J • (⊤ : Submodule S N))) := hflatTarget
    exact Module.Flat.of_linearEquiv eOwner
  have hmul_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul Su Nu).comp Ju.subtype)) := by
    simpa using hinj_u
  have hflatSuNu : Module.Flat Su Nu := by
    -- The common-universe nilpotent-thickening criterion applies upstairs.
    simpa [T] using
      flat_of_nilpotent_ideal_from_flat_closed_fiber_and_injective_tensor
        (S := Su) (J := Ju) (N := Nu) hJu hflatClosed hmul_inj
  have hflatSNu : Module.Flat S Nu := by
    have hflatSSu : Module.Flat S Su := by
      -- `ULift S` is flat over `S` because it is linearly equivalent to `S`.
      exact Module.Flat.of_linearEquiv
        (ULift.algEquiv (R := S) (A := S)).toLinearEquiv
    letI : Module.Flat S Su := hflatSSu
    letI : Module.Flat Su Nu := hflatSuNu
    exact Module.Flat.trans S Su Nu
  letI : Module.Flat S (ULift.{u} N) := by
    simpa [Nu] using hflatSNu
  -- Remove the remaining module `ULift`.
  exact Module.Flat.of_linearEquiv
    (ULift.moduleEquiv (R := S) (M := N)).symm

/-- Helper for Chap10 Remark 10 160 9: the induction invariant supplies flatness and formal
smoothness for every positive Cohen truncation. -/
private theorem cohenTruncatedQuotientFlatAndFormallySmooth (m : ℕ) :
    let R : Type := ZMod (p ^ (m + 1))
    let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (m + 1))}
    letI : CharP S (p ^ (m + 1)) :=
      quotient_charP_residueCharPow (Λ := Λ) ⟨m + 1, by omega⟩
    letI : Algebra R S := ZMod.algebra _ _
    Module.Flat R S ∧ Algebra.FormallySmooth R S := by
  -- Inductively thicken from `p^(r+1)` to `p^(r+2)` through the square-zero penultimate ideal.
  induction m with
  | zero =>
      dsimp only
      constructor
      · letI : Fact (Nat.Prime (p ^ (0 + 1))) := by
          simpa using (IsCohenRing.instFactResidueCharPrime (R := Λ))
        infer_instance
      · simpa using cohenRing_residueChar_quotient_formallySmooth (Λ := Λ)
  | succ r ih =>
      dsimp only at ih ⊢
      let R : Type := ZMod (p ^ (r + 2))
      let S : Type u := Λ ⧸ Ideal.span {((p : Λ) ^ (r + 2))}
      let I : Ideal R := Ideal.span {(((p ^ (r + 1) : ℕ) : R))}
      letI : CharP S (p ^ (r + 2)) :=
        quotient_charP_residueCharPow (Λ := Λ) ⟨r + 2, by omega⟩
      letI : Algebra R S := ZMod.algebra _ _
      letI : CharP (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) (p ^ (r + 1)) :=
        quotient_charP_residueCharPow (Λ := Λ) ⟨r + 1, by omega⟩
      letI : Algebra (ZMod (p ^ (r + 1)))
          (Λ ⧸ Ideal.span {((p : Λ) ^ (r + 1))}) :=
        ZMod.algebra _ _
      have hclosedSmooth :
          Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) :=
        cohenPenultimateClosedFiber_formallySmooth (Λ := Λ) r ih.2
      have hclosedFlatIdeal :
          Module.Flat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) :=
        cohenPenultimateClosedFiber_flat (Λ := Λ) r ih.1
      have hclosedFlat :
          Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) :=
        flat_quotient_smul_top_of_flat_ideal_quotient (R := R) (S := S) I hclosedFlatIdeal
      have hsq : I ^ 2 = ⊥ := by
        simpa [I, R] using zmodPenultimatePower_square_zero (Λ := Λ) r
      have hker :
          LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R S).comp I.subtype)) = ⊥ := by
        simpa [I, R, S] using cohenPenultimateTensorMul_ker_eq_bot (Λ := Λ) r
      have hflatTop : Module.Flat R S :=
        flat_of_square_zero_ideal_of_flat_mod_ideal_and_kernel_eq_bot_ulift
          (S := R) (N := S) (J := I) hsq hclosedFlat hker
      have hsmoothTop : Algebra.FormallySmooth R S := by
        letI : Module.Flat R S := hflatTop
        exact
          formallySmooth_of_square_zero_ideal_of_flat_of_quotient_formallySmooth
            (R := R) (S := S) I hsq hclosedSmooth
      exact ⟨hflatTop, hsmoothTop⟩

/-- Helper for Chap10 Remark 10 160 9: the residue-characteristic quotient of a Cohen ring is
formally smooth over the corresponding `ZMod`. -/
private theorem cohenRing_zmodPow_quotient_formallySmooth (n : ℕ+) :
    Algebra.FormallySmooth (ZMod (p ^ (n : ℕ)))
      (Λ ⧸ Ideal.span {((p ^ (n : ℕ)) : Λ)}) := by
  -- Project the formal-smoothness component from the flatness/formal-smoothness induction
  -- invariant at exponent `n = m + 1`.
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ m => exact (cohenTruncatedQuotientFlatAndFormallySmooth (Λ := Λ) m).2

end

/-- Helper for Chap10 Remark 10 160 9: one formally-smooth Cohen lift step raises a stage map
from `A ⧸ m^(n+1)` to `A ⧸ m^(n+2)`. -/
private theorem cohenLiftQuotientStep
    {C : Type u} [CommRing C] [IsCohenRing C]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (e : ResidueField C ≃+* ResidueField A) (n : ℕ)
    (g : C →+* A ⧸ (maximalIdeal A) ^ (n + 1)) :
    ∃ gnext : C →+* A ⧸ (maximalIdeal A) ^ (n + 2),
      (Ideal.Quotient.factorPow (maximalIdeal A) (Nat.le_succ (n + 1))).comp gnext = g := by
  let N : ℕ := ringChar (ResidueField C) ^ (n + 2)
  let I : Ideal C :=
    Ideal.span ({((ringChar (ResidueField C) : C) ^ (n + 2))} : Set C)
  let K : Ideal A := maximalIdeal A
  rcases cohenLift_factor_through_source_quotient (A := A) e n g with ⟨qg, hqg⟩
  have hchar : ringChar (ResidueField C) = ringChar (ResidueField A) := by
    rw [ringChar.eq_iff]
    exact e.toRingHom.charP e.injective _
  have hzeroPrev : ((N : ℕ) : A ⧸ K ^ (n + 1)) = 0 := by
    dsimp [N, K]
    rw [hchar]
    exact residueCharPow_quotient_eq_zero_of_le (A := A)
      (a := n + 1) (b := n + 2) (by omega)
  have hzeroNext : ((N : ℕ) : A ⧸ K ^ (n + 2)) = 0 := by
    dsimp [N, K]
    rw [hchar]
    exact residueCharPow_quotient_eq_zero_of_le (A := A)
      (a := n + 2) (b := n + 2) (by omega)
  letI : Algebra (ZMod N) (A ⧸ K ^ (n + 1)) :=
    RingHom.toAlgebra (ZMod.castHom (ringChar.dvd hzeroPrev) (A ⧸ K ^ (n + 1)))
  letI : Algebra (ZMod N) (A ⧸ K ^ (n + 2)) :=
    RingHom.toAlgebra (ZMod.castHom (ringChar.dvd hzeroNext) (A ⧸ K ^ (n + 2)))
  have hpos : 0 < n + 2 := by
    omega
  letI : Algebra (ZMod N) (C ⧸ I) := by
    dsimp [N, I]
    exact quotientResidueCharPowAlgebra (Λ := C) ⟨n + 2, hpos⟩
  letI : Algebra.FormallySmooth (ZMod N) (C ⧸ I) := by
    dsimp [N, I]
    exact cohenRing_zmodPow_quotient_formallySmooth (Λ := C) ⟨n + 2, hpos⟩
  let qgAlg : C ⧸ I →ₐ[ZMod N] A ⧸ K ^ (n + 1) :=
    { qg with commutes' := zmodAlgebraMap_commutes_of_ringHom qg }
  let factor : A ⧸ K ^ (n + 2) →+* A ⧸ K ^ (n + 1) :=
    Ideal.Quotient.factorPow K (Nat.le_succ (n + 1))
  let factorAlg : A ⧸ K ^ (n + 2) →ₐ[ZMod N] A ⧸ K ^ (n + 1) :=
    { factor with commutes' := zmodAlgebraMap_commutes_of_ringHom factor }
  have hsurj : Function.Surjective factorAlg := by
    dsimp [factorAlg, factor]
    exact Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hnil : IsNilpotent (RingHom.ker factorAlg.toRingHom) := by
    dsimp [factorAlg, factor]
    exact factorPowKernelIsNilpotent (K := K) (n := n + 1) (hn := Nat.succ_pos n)
  let lift : C ⧸ I →ₐ[ZMod N] A ⧸ K ^ (n + 2) :=
    Algebra.FormallySmooth.liftOfSurjective qgAlg factorAlg hsurj hnil
  -- Compose the lifted quotient map with the source quotient map to obtain the next stage.
  refine ⟨lift.toRingHom.comp (Ideal.Quotient.mk I), ?_⟩
  ext x
  calc
    ((Ideal.Quotient.factorPow K (Nat.le_succ (n + 1))).comp
        (lift.toRingHom.comp (Ideal.Quotient.mk I))) x =
        (factorAlg.comp lift) ((Ideal.Quotient.mk I) x) := by
      rfl
    _ = qgAlg ((Ideal.Quotient.mk I) x) := by
      rw [Algebra.FormallySmooth.comp_liftOfSurjective]
    _ = g x := by
      exact RingHom.congr_fun hqg x

/-- Helper for Chap10 Remark 10 160 9: the positive-characteristic quotients of `A` admit a
compatible tower of Cohen lifts. -/
private theorem cohenResidueQuotientTowerLift
    {C : Type u} [CommRing C] [IsCohenRing C]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (e : ResidueField C ≃+* ResidueField A) :
    ∃ g : (n : ℕ) → C →+* A ⧸ (maximalIdeal A) ^ (n + 1),
      g 0 = ((Ideal.quotEquivOfEq
        (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
          (e.toRingHom.comp (IsLocalRing.residue C)) ∧
      ∀ n, (Ideal.Quotient.factorPow (maximalIdeal A) (Nat.le_succ (n + 1))).comp
        (g (n + 1)) = g n := by
  classical
  let base : C →+* A ⧸ (maximalIdeal A) ^ (1 : ℕ) :=
    Classical.choose (cohenLiftResidueQuotientMap (A := A) e)
  have hbase :
      base = ((Ideal.quotEquivOfEq
        (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
          (e.toRingHom.comp (IsLocalRing.residue C)) :=
    Classical.choose_spec (cohenLiftResidueQuotientMap (A := A) e)
  let g : (n : ℕ) → C →+* A ⧸ (maximalIdeal A) ^ (n + 1) :=
    fun n ↦ Nat.rec base
      (fun m gm ↦ Classical.choose (cohenLiftQuotientStep (A := A) e m gm)) n
  refine ⟨g, ?_, ?_⟩
  · dsimp [g]
    exact hbase
  · intro n
    dsimp [g]
    exact Classical.choose_spec
      (cohenLiftQuotientStep (A := A) e n
        (Nat.rec base
          (fun m gm ↦ Classical.choose (cohenLiftQuotientStep (A := A) e m gm)) n))

/-- Helper for Chap10 Remark 10 160 9: in equal characteristic, a Noetherian complete local ring
admits a local field source with bijective residue-field map. -/
private theorem existsFieldSourceMap_of_residueCharZero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    (hchar0 : ringChar (ResidueField A) = 0) :
    ∃ (k : Type u) (_ : Field k) (ι : k →+* A) (_ : IsLocalHom ι),
      Function.Bijective (ResidueField.map ι) := by
  letI : Algebra ℚ A := (nonemptyAlgebraRat_of_residueField_charZero (S := A) hchar0).some
  rcases fieldResidueQuotientTowerLift (A := A) with ⟨g, hg0, hgcompat⟩
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := by
    exact strictMono_nat_of_lt_succ (fun n ↦ by omega)
  let ψ : ResidueField A →+* A :=
    IsAdicComplete.StrictMono.liftRingHom (maximalIdeal A) ha g (by
      intro m
      exact hgcompat m)
  let eκ : ResidueField (ResidueField A) ≃+* ResidueField A :=
    (Ideal.quotEquivOfEq
      (by simpa using (IsLocalRing.maximalIdeal_eq_bot (R := ResidueField A)))).trans
        (RingEquiv.quotientBot (ResidueField A))
  have hfirst :
      (Ideal.Quotient.mk ((maximalIdeal A) ^ (1 : ℕ))).comp ψ =
        ((Ideal.quotEquivOfEq
          (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
            (eκ.toRingHom.comp (IsLocalRing.residue (ResidueField A))) := by
    -- The adic limit map reduces to the chosen base stage at level `n = 0`.
    calc
      (Ideal.Quotient.mk ((maximalIdeal A) ^ (1 : ℕ))).comp ψ = g 0 := by
        simpa [ψ] using
          (IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal A) ha g
            (by
              intro m
              exact hgcompat m) (n := 0))
      _ = ((Ideal.quotEquivOfEq
          (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
            (eκ.toRingHom.comp (IsLocalRing.residue (ResidueField A))) := by
        refine Eq.trans hg0 ?_
        ext x
        rfl
  have hres :
      (IsLocalRing.residue A).comp ψ =
        eκ.toRingHom.comp (IsLocalRing.residue (ResidueField A)) :=
    residueComp_of_firstPowerQuotientComp ψ eκ hfirst
  rcases existsIsLocalHomAndResidueFieldMapBijectiveOfResidueCompat ψ eκ hres with
    ⟨hψlocal, hψres⟩
  exact ⟨ResidueField A, inferInstance, ψ, hψlocal, hψres⟩

/-- Helper for Chap10 Remark 10 160 9: in positive residue characteristic, a Noetherian complete
local ring admits a local Cohen-ring source with bijective residue-field map. -/
private theorem existsCohenSourceMap_of_positiveResidueChar
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]
    (hchar : ringChar (ResidueField A) ≠ 0) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsCohenRing C) (ι : C →+* A) (_ : IsLocalHom ι),
      Function.Bijective (ResidueField.map ι) := by
  rcases existsCohenRingResidueFieldSource (A := A) hchar with ⟨C, hC, hCohen, ⟨e⟩⟩
  letI : CommRing C := hC
  letI : IsCohenRing C := hCohen
  rcases cohenResidueQuotientTowerLift (A := A) e with ⟨g, hg0, hgcompat⟩
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := by
    exact strictMono_nat_of_lt_succ (fun n ↦ by omega)
  let ψ : C →+* A :=
    IsAdicComplete.StrictMono.liftRingHom (maximalIdeal A) ha g (by
      intro m
      exact hgcompat m)
  have hfirst :
      (Ideal.Quotient.mk ((maximalIdeal A) ^ (1 : ℕ))).comp ψ =
        ((Ideal.quotEquivOfEq
          (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
            (e.toRingHom.comp (IsLocalRing.residue C)) := by
    -- The adic limit map matches the prescribed residue-field stage at `n = 0`.
    calc
      (Ideal.Quotient.mk ((maximalIdeal A) ^ (1 : ℕ))).comp ψ = g 0 := by
        simpa [ψ] using
          (IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal A) ha g
            (by
              intro m
              exact hgcompat m) (n := 0))
      _ = ((Ideal.quotEquivOfEq
          (by simp [pow_one] : maximalIdeal A = (maximalIdeal A) ^ (1 : ℕ))).toRingHom).comp
            (e.toRingHom.comp (IsLocalRing.residue C)) := hg0
  have hres :
      (IsLocalRing.residue A).comp ψ = e.toRingHom.comp (IsLocalRing.residue C) :=
    residueComp_of_firstPowerQuotientComp ψ e hfirst
  rcases existsIsLocalHomAndResidueFieldMapBijectiveOfResidueCompat ψ e hres with
    ⟨hψlocal, hψres⟩
  exact ⟨C, inferInstance, inferInstance, ψ, hψlocal, hψres⟩

/-- Helper for Chap10 Remark 10 160 9: the range of a local Cohen-ring source with bijective
residue-field map is a coefficient ring. -/
private theorem isCoefficientRing_range_of_cohenSourceMap
    (A C : Type u) [CommRing A] [IsCompleteLocalRing A] [CommRing C] [IsCohenRing C]
    (ι : C →+* A) [IsLocalHom ι]
    (hres : Function.Bijective (ResidueField.map ι)) :
    IsCoefficientRing A (RingHom.range ι) := by
  -- Route correction: first pass to `C ⧸ ker ι`, where quotient completeness is available, and
  -- then transport the complete-local and maximal-ideal data across the quotient-to-range
  -- equivalence.
  let Q := C ⧸ RingHom.ker ι
  let q : C →+* Q := Ideal.Quotient.mk (RingHom.ker ι)
  let e : Q ≃+* RingHom.range ι := RingHom.quotientKerEquivRange ι
  have hker_le_max : RingHom.ker ι ≤ maximalIdeal C := by
    -- A kernel element cannot be a unit, because its image is `0`.
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal]
    intro hxunit
    exact (IsUnit.map ι hxunit).ne_zero hx
  have hker_ne_top : RingHom.ker ι ≠ ⊤ := by
    -- The kernel lies in the proper maximal ideal, so it is proper as well.
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hker_le_max
  letI : IsCompleteLocalRing Q :=
    quotient_isCompleteLocalRing (A := C) (I := RingHom.ker ι) hker_ne_top
  letI : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  letI : IsCompleteLocalRing (RingHom.range ι) :=
    isCompleteLocalRing_of_ringEquiv (R := Q) (S := RingHom.range ι) e
  have hlocRange : IsLocalHom ((RingHom.range ι).subtype : RingHom.range ι →+* A) := by
    -- Units in the ambient ring lift to units in the range by reflecting along `ι`.
    refine ⟨?_⟩
    intro x hx
    rcases x.2 with ⟨y, hy⟩
    have hunitι : IsUnit (ι y) := by
      simpa [hy] using hx
    have hunitPre : IsUnit y := IsUnit.of_map ι y hunitι
    have hx_eq : x = ι.rangeRestrict y := Subtype.ext hy.symm
    simpa [hx_eq] using IsUnit.map ι.rangeRestrict hunitPre
  letI : IsLocalHom ((RingHom.range ι).subtype : RingHom.range ι →+* A) := hlocRange
  have hqres : Function.Bijective (ResidueField.map q) := by
    -- Route correction: use the canonical proper-quotient residue-field theorem instead of the
    -- deleted local duplicate bridge.
    simpa [Q, q] using
      residueField_map_quotient_mk_bijective (A := C) (I := RingHom.ker ι) hker_ne_top
  have hqrange : (e : Q →+* RingHom.range ι).comp q = ι.rangeRestrict := by
    -- The quotient-to-range equivalence sends the class of `x` to the range element `ι x`.
    ext x
    rfl
  have hsubtype_comp_rangeRestrict :
      ((RingHom.range ι).subtype : RingHom.range ι →+* A).comp ι.rangeRestrict = ι := by
    ext x
    rfl
  have hfactor :
      ((RingHom.range ι).subtype : RingHom.range ι →+* A).comp
          ((e : Q →+* RingHom.range ι).comp q) = ι := by
    rw [hqrange, hsubtype_comp_rangeRestrict]
  have hcomp :
      ResidueField.map ι =
        (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)).comp
          ((ResidueField.map (e : Q →+* RingHom.range ι)).comp (ResidueField.map q)) := by
    -- Rewrite `ι` through the quotient-to-range factorization and pass to residue fields.
    calc
      ResidueField.map ι =
          ResidueField.map (((RingHom.range ι).subtype : RingHom.range ι →+* A).comp
            ((e : Q →+* RingHom.range ι).comp q)) := by
          ext x
          rcases IsLocalRing.residue_surjective x with ⟨c, rfl⟩
          rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
          change IsLocalRing.residue A (ι c) =
            IsLocalRing.residue A
              ((((RingHom.range ι).subtype : RingHom.range ι →+* A).comp
                  ((e : Q →+* RingHom.range ι).comp q)) c)
          rw [hfactor]
      _ = (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)).comp
            (ResidueField.map ((e : Q →+* RingHom.range ι).comp q)) := by
          simpa using
            (IsLocalRing.ResidueField.map_comp
              (f := (e : Q →+* RingHom.range ι).comp q)
              (g := ((RingHom.range ι).subtype : RingHom.range ι →+* A)))
      _ = (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)).comp
            ((ResidueField.map (e : Q →+* RingHom.range ι)).comp (ResidueField.map q)) := by
          simp [IsLocalRing.ResidueField.map_comp]
  have hqe : Function.Bijective (ResidueField.map (e : Q →+* RingHom.range ι)) :=
    (IsLocalRing.ResidueField.mapEquiv e).bijective
  have hqToRange :
      Function.Bijective
        ((ResidueField.map (e : Q →+* RingHom.range ι)).comp (ResidueField.map q)) :=
    hqe.comp hqres
  have hresRange :
      Function.Bijective
        (ResidueField.map ((RingHom.range ι).subtype : RingHom.range ι →+* A)) := by
    -- Peel off the quotient-to-range residue isomorphism from the bijection carried by `ι`.
    constructor
    · intro x y hxy
      rcases hqToRange.2 x with ⟨x0, rfl⟩
      rcases hqToRange.2 y with ⟨y0, rfl⟩
      refine congrArg
        (((ResidueField.map (e : Q →+* RingHom.range ι)).comp (ResidueField.map q))) ?_
      apply hres.1
      simpa [hcomp, RingHom.comp_apply, Function.comp] using hxy
    · intro y
      rcases hres.2 y with ⟨x, hx⟩
      refine ⟨((ResidueField.map (e : Q →+* RingHom.range ι)).comp (ResidueField.map q)) x, ?_⟩
      simpa [hcomp, RingHom.comp_apply, Function.comp] using hx
  have hchar : ringChar (ResidueField C) = ringChar (ResidueField A) :=
    ringChar_eq_of_bijective_ringHom (ResidueField.map ι) hres
  have hmaxQ :
      maximalIdeal Q = Ideal.span ({(ringChar (ResidueField A) : Q)} : Set Q) := by
    -- Map the Cohen-ring maximal-ideal generator into the quotient and rewrite the characteristic.
    calc
      maximalIdeal Q = Ideal.map q (maximalIdeal C) := by
        symm
        simpa [Q, q] using
          quotientMaximalIdealEqMap (A := C) (I := RingHom.ker ι)
      _ = Ideal.map q (Ideal.span ({(ringChar (ResidueField C) : C)} : Set C)) := by
        rw [IsCohenRing.maximalIdeal_eq_span_residueChar]
      _ = Ideal.span ({(q (ringChar (ResidueField C) : C))} : Set Q) := by
        simp [Ideal.map_span]
      _ = Ideal.span ({(ringChar (ResidueField A) : Q)} : Set Q) := by
        simp [q, hchar]
  have hmaxRange :
      maximalIdeal (RingHom.range ι) =
        Ideal.span ({(ringChar (ResidueField A) : RingHom.range ι)} :
          Set (RingHom.range ι)) := by
    -- Transport the quotient maximal ideal across the quotient-to-range equivalence.
    calc
      maximalIdeal (RingHom.range ι) =
          Ideal.map (e : Q →+* RingHom.range ι) (maximalIdeal Q) := by
        symm
        exact IsLocalRing.map_maximalIdeal_of_surjective
          (e : Q →+* RingHom.range ι) e.surjective
      _ = Ideal.map (e : Q →+* RingHom.range ι)
            (Ideal.span ({(ringChar (ResidueField A) : Q)} : Set Q)) := by
        rw [hmaxQ]
      _ = Ideal.span
            ({((e : Q →+* RingHom.range ι) (ringChar (ResidueField A) : Q))} :
              Set (RingHom.range ι)) := by
        simp [Ideal.map_span]
      _ = Ideal.span ({(ringChar (ResidueField A) : RingHom.range ι)} :
            Set (RingHom.range ι)) := by
        simp [e]
  exact
    isCoefficientRing_of_completeLocalSubring
      (A := A) (Λ := RingHom.range ι) hresRange hmaxRange

/-- Helper for Chap10 Remark 10 160 9: a Noetherian complete local ring admits a coefficient
subring in the sense of `IsCoefficientRing`. -/
theorem existsCoefficientSubringOfNoetherianCompleteLocalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    ∃ Λ₀ : Subring A, IsCoefficientRing A Λ₀ :=
  by
    by_cases hchar : ringChar (ResidueField A) = 0
    · -- In equal characteristic, the field source gives the coefficient ring after passing to its
      -- range.
      rcases existsFieldSourceMap_of_residueCharZero (A := A) hchar with ⟨k, _, ι, _, hres⟩
      exact ⟨RingHom.range ι, isCoefficientRing_range_of_field_sourceMap (A := A) k ι hres⟩
    · -- Route correction: the positive-characteristic branch must end at the range of a Cohen
      -- source map, not at an embedded Cohen subring.
      rcases existsCohenSourceMap_of_positiveResidueChar (A := A) hchar with
        ⟨C, _, _, ι, _, hres⟩
      exact ⟨RingHom.range ι, isCoefficientRing_range_of_cohenSourceMap (A := A) C ι hres⟩

/-- Helper for Chap10 Remark 10 160 9: a finite generating family for the maximal ideal can be
used as the formal variable index set. -/
private theorem finiteMaximalIdealGeneratingFamily
    (A : Type u) [CommRing A] [IsLocalRing A] (hfg : (maximalIdeal A).FG) :
    ∃ (σ : Type u) (_ : Finite σ) (x : σ → A),
      (∀ i, x i ∈ maximalIdeal A) ∧ Ideal.span (Set.range x) = maximalIdeal A := by
  -- Unpack finite generation into a finite set of generators and use that set itself as the
  -- variable index type.
  rcases hfg with ⟨s, hs⟩
  refine ⟨s, inferInstance, fun i : s ↦ (i : A), ?_, ?_⟩
  · intro i
    have hmem : (i : A) ∈ Ideal.span (↑s : Set A) := Ideal.subset_span i.2
    simpa [hs] using hmem
  · have hrange : Set.range (fun i : s ↦ (i : A)) = (↑s : Set A) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact i.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    simp [hrange, hs]

/-- Helper for Chap10 Remark 10 160 9: a Noetherian complete local ring admits either a local
field source or a local Cohen-ring source with bijective residue-field map. -/
private theorem existsCompleteLocalSourceMap
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    (∃ (k : Type u) (_ : Field k) (ι : k →+* A) (_ : IsLocalHom ι),
        Function.Bijective (ResidueField.map ι)) ∨
      ∃ (C : Type u) (_ : CommRing C) (_ : IsCohenRing C) (ι : C →+* A) (_ : IsLocalHom ι),
        Function.Bijective (ResidueField.map ι) := by
  by_cases hchar : ringChar (ResidueField A) = 0
  · left
    exact existsFieldSourceMap_of_residueCharZero (A := A) hchar
  · right
    exact existsCohenSourceMap_of_positiveResidueChar (A := A) hchar

/-- Helper for Chap10 Remark 10 160 9: polynomial evaluation sends the variables ideal to the
ideal spanned by the chosen target elements. -/
private theorem mvPolynomialIdealOfVars_eval₂Hom_map_eq_span
    {A S σ : Type u} [CommSemiring A] [CommSemiring S]
    (ι : A →+* S) (x : σ → S) :
    Ideal.map (MvPolynomial.eval₂Hom ι x) (MvPolynomial.idealOfVars σ A) =
      Ideal.span (Set.range x) := by
  -- The variables ideal is generated by the indeterminates, which evaluation sends to the chosen
  -- target family.
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr
  ext y
  simp

/-- Helper for Chap10 Remark 10 160 9: when the chosen target elements generate `maximalIdeal A`,
polynomial evaluation sends the variables ideal onto `maximalIdeal A`. -/
private theorem mvPolynomialIdealOfVars_eval₂Hom_map_eq_maximalIdeal
    {B σ : Type u} [CommSemiring B]
    (A : Type u) [CommRing A] [IsLocalRing A] (ι : B →+* A) (x : σ → A)
    (hxspan : Ideal.span (Set.range x) = maximalIdeal A) :
    Ideal.map (MvPolynomial.eval₂Hom ι x) (MvPolynomial.idealOfVars σ B) =
      maximalIdeal A := by
  -- Reduce to the generic span computation and then rewrite with the chosen generators.
  rw [mvPolynomialIdealOfVars_eval₂Hom_map_eq_span, hxspan]

/-- Helper for Chap10 Remark 10 160 9: polynomial evaluation is surjective modulo the maximal
ideal once the coefficient map is residue-surjective. -/
private theorem mvPolynomialEval_mod_maximal_surjective
    {B σ : Type u} [CommRing B] [IsLocalRing B]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (ι : B →+* A) [IsLocalHom ι]
    (hres : Function.Bijective (ResidueField.map ι)) (x : σ → A) :
    Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal A)).comp (MvPolynomial.eval₂Hom ι x)) := by
  -- A residue class is represented by a constant polynomial coming from a coefficient lift.
  intro y
  rcases hres.2 y with ⟨z, hz⟩
  rcases IsLocalRing.residue_surjective z with ⟨a, rfl⟩
  refine ⟨MvPolynomial.C a, ?_⟩
  simpa [IsLocalRing.ResidueField.map_residue] using hz

/-- Helper for Chap10 Remark 10 160 9: the same residue-level surjectivity holds modulo the image
of the variables ideal once that image is `maximalIdeal A`. -/
private theorem mvPolynomialEval_mod_imageIdeal_surjective
    {B σ : Type u} [CommRing B] [IsLocalRing B]
    (A : Type u) [CommRing A] [IsLocalRing A]
    (ι : B →+* A) [IsLocalHom ι]
    (hres : Function.Bijective (ResidueField.map ι)) (x : σ → A)
    (hmap :
      Ideal.map (MvPolynomial.eval₂Hom ι x) (MvPolynomial.idealOfVars σ B) =
        maximalIdeal A) :
    Function.Surjective
      ((Ideal.Quotient.mk
        (Ideal.map (MvPolynomial.eval₂Hom ι x) (MvPolynomial.idealOfVars σ B))).comp
          (MvPolynomial.eval₂Hom ι x)) := by
  -- Rewrite the image ideal to the maximal ideal and invoke the residue-field calculation.
  rw [hmap]
  exact mvPolynomialEval_mod_maximal_surjective A ι hres x

/-- Helper for Chap10 Remark 10 160 9: powers of an ideal map into the matching powers of its
image ideal. -/
private theorem ideal_pow_le_comap_pow_of_map_eq
    {P S : Type u} [CommRing P] [CommRing S] {J : Ideal P} {I : Ideal S}
    (g : P →+* S) (hmap : Ideal.map g J = I) (n : ℕ) :
    J ^ n ≤ (I ^ n).comap g := by
  -- Rewrite the target power as the image of the source power and use the map/comap adjunction.
  exact Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow, hmap])

/-- Helper for Chap10 Remark 10 160 9: the quotient maps from a source adic completion induced by
a ring map with prescribed ideal image are compatible in the inverse system. -/
private theorem adicCompletionQuotientMaps_compatible
    {P S : Type u} [CommRing P] [CommRing S] {J : Ideal P} {I : Ideal S}
    (g : P →+* S) (hmap : Ideal.map g J = I) :
    let f : (n : ℕ) → AdicCompletion J P →+* S ⧸ I ^ n := fun n ↦
      (Ideal.quotientMap (I ^ n) g (ideal_pow_le_comap_pow_of_map_eq g hmap n)).comp
        (AdicCompletion.evalₐ J n).toRingHom
    ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
  dsimp only
  intro m n hle
  ext y
  -- Check compatibility on Cauchy-sequence representatives of completion elements.
  apply AdicCompletion.induction_on J P y
  intro a
  change (Ideal.Quotient.mk (I ^ m)) (g (↑(a n) : P)) =
    (Ideal.Quotient.mk (I ^ m)) (g (↑(a m) : P))
  rw [Ideal.Quotient.eq]
  have hcong : (↑(a n) : P) ≡ (↑(a m) : P)
      [SMOD (J ^ m • ⊤ : Submodule P P)] := (a.property hle).symm
  have hmemJ : ((↑(a n) : P) - (↑(a m) : P)) ∈ J ^ m := by
    simpa using (SModEq.sub_mem.mp hcong)
  have hmem : g ((↑(a n) : P) - (↑(a m) : P)) ∈ Ideal.map g (J ^ m) :=
    Ideal.mem_map_of_mem g hmemJ
  have hmap_pow : Ideal.map g (J ^ m) = I ^ m := by
    rw [Ideal.map_pow, hmap]
  simpa [map_sub, hmap_pow] using hmem

/-- Helper for Chap10 Remark 10 160 9: the lifted map from the source adic completion agrees with
the original ring map on polynomial elements. -/
private theorem adicCompletionLiftRingHom_comp_algebraMap
    {P S : Type u} [CommRing P] [CommRing S] {J : Ideal P} {I : Ideal S}
    (g : P →+* S) (hmap : Ideal.map g J = I) [IsAdicComplete I S] :
    let f : (n : ℕ) → AdicCompletion J P →+* S ⧸ I ^ n := fun n ↦
      (Ideal.quotientMap (I ^ n) g (ideal_pow_le_comap_pow_of_map_eq g hmap n)).comp
        (AdicCompletion.evalₐ J n).toRingHom
    (IsAdicComplete.liftRingHom I f (adicCompletionQuotientMaps_compatible g hmap)).comp
      (algebraMap P (AdicCompletion J P)) = g := by
  dsimp only
  let f : (n : ℕ) → AdicCompletion J P →+* S ⧸ I ^ n := fun n ↦
    (Ideal.quotientMap (I ^ n) g (ideal_pow_le_comap_pow_of_map_eq g hmap n)).comp
      (AdicCompletion.evalₐ J n).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m :=
    adicCompletionQuotientMaps_compatible g hmap
  let G : AdicCompletion J P →+* S := IsAdicComplete.liftRingHom I f hf
  -- Equality into the separated target is checked on all finite quotient stages.
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n x
  calc
    Ideal.Quotient.mk (I ^ n) (G ((algebraMap P (AdicCompletion J P)) x)) =
        f n ((algebraMap P (AdicCompletion J P)) x) := by
      exact
        RingHom.congr_fun (IsAdicComplete.mk_comp_liftRingHom I f hf n)
          ((algebraMap P (AdicCompletion J P)) x)
    _ = Ideal.Quotient.mk (I ^ n) (g x) := by
      simp [f, Ideal.quotientMap_mk]

/-- Helper for Chap10 Remark 10 160 9: a ring map that is surjective modulo the image ideal
induces a surjective map from the adic completion of the source. -/
private theorem adicCompletionMapRingHom_surjective_of_quotient_surjective
    {P S : Type u} [CommRing P] [CommRing S] {J : Ideal P} {I : Ideal S}
    [IsAdicComplete I S] (g : P →+* S) (hmap : Ideal.map g J = I)
    (hJfg : J.FG) (hmod : Function.Surjective ((Ideal.Quotient.mk I).comp g)) :
    ∃ G : AdicCompletion J P →+* S,
      Function.Surjective G ∧ G.comp (algebraMap P (AdicCompletion J P)) = g := by
  let f : (n : ℕ) → AdicCompletion J P →+* S ⧸ I ^ n := fun n ↦
    (Ideal.quotientMap (I ^ n) g (ideal_pow_le_comap_pow_of_map_eq g hmap n)).comp
      (AdicCompletion.evalₐ J n).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m :=
    adicCompletionQuotientMaps_compatible g hmap
  let G : AdicCompletion J P →+* S := IsAdicComplete.liftRingHom I f hf
  have hGcomp : G.comp (algebraMap P (AdicCompletion J P)) = g := by
    simpa [G, f, hf] using adicCompletionLiftRingHom_comp_algebraMap (g := g) hmap
  refine ⟨G, ?_, hGcomp⟩
  let K : Ideal (AdicCompletion J P) := Ideal.map (algebraMap P (AdicCompletion J P)) J
  have hpre : IsPrecomplete K (AdicCompletion J P) := by
    change IsPrecomplete (Ideal.map (algebraMap P (AdicCompletion J P)) J)
      (AdicCompletion J P)
    have hcomp : IsAdicComplete J (AdicCompletion J P) := AdicCompletion.isAdicComplete hJfg
    let _ : IsAdicComplete J (AdicCompletion J P) := hcomp
    exact (IsPrecomplete.map_algebraMap_iff (I := J) (M := AdicCompletion J P)).2 inferInstance
  have hGmap : Ideal.map G K = I := by
    calc
      Ideal.map G K = Ideal.map (G.comp (algebraMap P (AdicCompletion J P))) J := by
        rw [Ideal.map_map]
      _ = Ideal.map g J := by rw [hGcomp]
      _ = I := hmap
  have hhaus : IsHausdorff (Ideal.map G K) S := by
    rw [hGmap]
    infer_instance
  -- The separated/precomplete surjectivity criterion reduces surjectivity of the completion map
  -- to surjectivity modulo the image ideal.
  apply @surjective_of_mk_map_comp_surjective
    (AdicCompletion J P) inferInstance K S inferInstance G hpre hhaus
  intro y
  let e : S ⧸ Ideal.map G K ≃+* S ⧸ I := Ideal.quotEquivOfEq hGmap
  rcases hmod (e y) with ⟨x, hx⟩
  refine ⟨(algebraMap P (AdicCompletion J P)) x, ?_⟩
  apply e.injective
  change (Ideal.Quotient.mk I) (G ((algebraMap P (AdicCompletion J P)) x)) = e y
  have hxG : G ((algebraMap P (AdicCompletion J P)) x) = g x :=
    RingHom.congr_fun hGcomp x
  rw [hxG]
  exact hx

/-- Helper for Chap10 Remark 10 160 9: a local source with bijective residue-field map and a
chosen generating family for `maximalIdeal A` yields a surjective finite-variable power series map
to `A`. -/
private theorem mvPowerSeriesSurjective_of_residue_bijective_of_generates_maximalIdeal
    {B σ : Type u} [CommRing B] [IsLocalRing B] [Finite σ]
    (A : Type u) [CommRing A] [IsCompleteLocalRing A]
    (ι : B →+* A) [IsLocalHom ι]
    (hres : Function.Bijective (ResidueField.map ι))
    (x : σ → A) (_hxmem : ∀ i, x i ∈ maximalIdeal A)
    (hxspan : Ideal.span (Set.range x) = maximalIdeal A) :
    ∃ φ : MvPowerSeries σ B →+* A, Function.Surjective φ := by
  -- The polynomial evaluation map is already surjective modulo the maximal ideal, and the source
  -- completion identifies with the finite-variable power series ring.
  let g : MvPolynomial σ B →+* A := MvPolynomial.eval₂Hom ι x
  let J : Ideal (MvPolynomial σ B) := MvPolynomial.idealOfVars σ B
  have hmapJ : Ideal.map g J = maximalIdeal A := by
    exact mvPolynomialIdealOfVars_eval₂Hom_map_eq_maximalIdeal A ι x hxspan
  have hmod :
      Function.Surjective ((Ideal.Quotient.mk (Ideal.map g J)).comp g) := by
    exact mvPolynomialEval_mod_imageIdeal_surjective A ι hres x hmapJ
  have hmodMax :
      Function.Surjective ((Ideal.Quotient.mk (maximalIdeal A)).comp g) := by
    -- Transport surjectivity across the explicit identification of the image ideal with the
    -- maximal ideal.
    intro y
    let e : A ⧸ Ideal.map g J ≃+* A ⧸ maximalIdeal A := Ideal.quotEquivOfEq hmapJ
    rcases hmod (e.symm y) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change e (((Ideal.Quotient.mk (Ideal.map g J)).comp g) z) = y
    rw [hz]
    exact e.apply_symm_apply y
  have hJfg : J.FG := MvPolynomial.idealOfVars_fg σ B
  rcases adicCompletionMapRingHom_surjective_of_quotient_surjective
      (I := maximalIdeal A) g hmapJ hJfg hmodMax with
    ⟨G, hGsurj, _hGcomp⟩
  let φ : MvPowerSeries σ B →+* A :=
    G.comp (MvPowerSeries.toAdicCompletionAlgEquiv σ B).toRingHom
  exact ⟨φ, hGsurj.comp (MvPowerSeries.toAdicCompletionAlgEquiv σ B).surjective⟩

/-- Helper for Chap10 Remark 10 160 9: a Noetherian complete local ring is a quotient of a
finite-variable formal power series ring over either a field or a Cohen ring. -/
private theorem existsMvPowerSeriesQuotient_of_isCompleteLocalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    ∃ (σ : Type u) (_ : Finite σ),
      (∃ (k : Type u) (_ : Field k) (I : Ideal (MvPowerSeries σ k)),
        Nonempty ((MvPowerSeries σ k ⧸ I) ≃+* A)) ∨
        ∃ (C : Type u) (_ : CommRing C) (_ : IsCohenRing C)
          (I : Ideal (MvPowerSeries σ C)),
          Nonempty ((MvPowerSeries σ C ⧸ I) ≃+* A) := by
  have hfg : (maximalIdeal A).FG := maximalIdeal_fg_of_isNoetherianRing (A := A)
  rcases finiteMaximalIdealGeneratingFamily A hfg with ⟨σ, hσ, x, hxmem, hxspan⟩
  refine ⟨σ, hσ, ?_⟩
  rcases existsCompleteLocalSourceMap A with hfield | hcohen
  · rcases hfield with ⟨k, _, ι, _, hres⟩
    left
    rcases
        mvPowerSeriesSurjective_of_residue_bijective_of_generates_maximalIdeal
          A ι hres x hxmem hxspan with
      ⟨φ, hφ⟩
    refine ⟨k, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩
  · rcases hcohen with ⟨C, _, _, ι, _, hres⟩
    right
    rcases
        mvPowerSeriesSurjective_of_residue_bijective_of_generates_maximalIdeal
          A ι hres x hxmem hxspan with
      ⟨φ, hφ⟩
    refine ⟨C, inferInstance, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩

/-- Helper for Chap10 Remark 10 160 9: if `N` has full support over `A`, then every prime
localization `N_𝔭` still has full support over `A_𝔭`. -/
private lemma localized_support_eq_univ_of_support_eq_univ
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsupp : Module.support A N = Set.univ) (p : PrimeSpectrum A) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) =
      Set.univ := by
  -- Detect support after localizing by contracting the prime back to `Spec A`.
  ext q
  rw [Module.mem_support_localizationAtPrime_iff (R := A) (M := N) p q, hsupp]
  simp

/-- Helper for Chap10 Remark 10 160 9: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space owner through the induced homeomorphism on spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Chap10 Remark 10 160 9: full support survives arbitrary finite base change. -/
private lemma support_tensor_eq_univ_of_support_eq_univ
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsupp : Module.support A N = Set.univ) :
    Module.support S (S ⊗[A] N) = Set.univ := by
  -- Pull support back along the algebra map, then use that the source support is all of `Spec A`.
  rw [Module.Lemma_10_40_6, hsupp]
  ext q
  simp

/-- Helper for Chap10 Remark 10 160 9: quotient by a prime has Krull dimension equal to the
coheight of the corresponding point of the prime spectrum. -/
private lemma primeQuotientKrullDim_eq_coheight
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  -- Rewrite the quotient spectrum as the upper interval of primes containing `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici p).symm

/-- Helper for Chap10 Remark 10 160 9: Cohen-Macaulayness is preserved by a linear equivalence
over a fixed Noetherian local ring. -/
private theorem cohenMacaulay_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [hM : Module.CohenMacaulay A M] :
    Module.CohenMacaulay A N := by
  -- Transport the defining equality through the support-dimension and depth invariance lemmas.
  let _ : Module.Finite A N := Module.Finite.equiv e
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e,
      hM.supportDim_eq_moduleDepth]⟩

/-- Helper for Chap10 Remark 10 160 9: the full-support Cohen-Macaulay dimension formula with a
module in an arbitrary universe, reduced to the same-universe theorem by `ULift`. -/
private theorem ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    (p : Ideal A) [p.IsPrime] :
    ringKrullDim A = ringKrullDim (Localization.AtPrime p) + ringKrullDim (A ⧸ p) := by
  let Au := ULift.{max u v, u} A
  let Nu := ULift.{max u v, v} N
  let eA : Au ≃+* A := ULift.ringEquiv
  let eN : Nu ≃ₗ[A] N := ULift.moduleEquiv
  letI : IsLocalRing Au := IsLocalRing.of_surjective' eA.symm.toRingHom eA.symm.surjective
  letI : IsNoetherianRing Au := isNoetherianRing_of_ringEquiv A eA.symm
  letI : Algebra Au A := eA.toRingHom.toAlgebra
  letI : Module Au Nu := Module.compHom Nu eA.toRingHom
  letI : IsScalarTower Au A Nu :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hCMNuA : Module.CohenMacaulay A Nu := by
    let _ : Module.CohenMacaulay A N := hCM
    exact cohenMacaulay_of_linearEquiv eN.symm
  have hsuppNuA : Module.support A Nu = Set.univ := by
    rw [LinearEquiv.support_eq eN]
    exact hsupp
  have hCMNuAu : Module.CohenMacaulay Au Nu := by
    let _ : Module.CohenMacaulay A Nu := hCMNuA
    have hTower : IsScalarTower Au A Nu :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact
      (@Module.cohenMacaulay_iff_restrictScalars_of_surjective
        Au A Nu inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hTower eA.surjective).1 hCMNuA
  have hsuppNuAu : Module.support Au Nu = Set.univ := by
    let _ : Module.CohenMacaulay Au Nu := hCMNuAu
    let _ : Module.CohenMacaulay A Nu := hCMNuA
    ext P
    constructor
    · intro _
      simp
    · intro _
      rw [Module.support_eq_zeroLocus]
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hxann
      have hPA_support :
          PrimeSpectrum.comap eA.symm.toRingHom P ∈ Module.support A Nu := by
        simp [hsuppNuA]
      rw [Module.support_eq_zeroLocus] at hPA_support
      have hleA : Module.annihilator A Nu ≤
          (PrimeSpectrum.comap eA.symm.toRingHom P).asIdeal := by
        simpa [PrimeSpectrum.mem_zeroLocus] using hPA_support
      have hxannAu : ∀ n : Nu, x • n = 0 := Module.mem_annihilator.mp hxann
      have hxannA : eA x ∈ Module.annihilator A Nu := by
        rw [Module.mem_annihilator]
        intro n
        simpa using hxannAu n
      have hxP : eA x ∈ Ideal.comap eA.symm.toRingHom P.asIdeal := hleA hxannA
      simpa using hxP
  let pU : Ideal Au := Ideal.comap eA.toRingHom p
  letI : pU.IsPrime := Ideal.comap_isPrime eA.toRingHom p
  have hformulaU :
      ringKrullDim Au =
        ringKrullDim (Localization.AtPrime pU) + ringKrullDim (Au ⧸ pU) := by
    -- Apply the same-universe theorem to the lifted ring and lifted module.
    exact
      ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
        (R := Au) (M := Nu) hCMNuAu hsuppNuAu pU
  have hring : ringKrullDim Au = ringKrullDim A :=
    ringKrullDim_eq_of_ringEquiv eA
  have hloc :
      ringKrullDim (Localization.AtPrime pU) =
        ringKrullDim (Localization.AtPrime p) := by
    let eLoc := Localization.localRingEquiv pU p eA rfl
    exact ringKrullDim_eq_of_ringEquiv eLoc
  have hp_map : p = Ideal.map eA.toRingHom pU := by
    simpa [pU] using (Ideal.map_comap_eq_self_of_equiv eA p).symm
  have hquot : ringKrullDim (Au ⧸ pU) = ringKrullDim (A ⧸ p) := by
    let eQuot := Ideal.quotientEquiv pU p eA hp_map
    exact ringKrullDim_eq_of_ringEquiv eQuot
  -- Transport the lifted dimension formula back through the ring, localization, and quotient
  -- equivalences.
  calc
    ringKrullDim A = ringKrullDim Au := hring.symm
    _ = ringKrullDim (Localization.AtPrime pU) + ringKrullDim (Au ⧸ pU) := hformulaU
    _ = ringKrullDim (Localization.AtPrime p) + ringKrullDim (A ⧸ p) := by
      rw [hloc, hquot]

/-- Helper for Chap10 Remark 10 160 9: the prime-quotient dimension expression strictly decreases
under proper specialization in finite Krull dimension. -/
private lemma primeQuotientKrullDimension_strict_of_specializes
    {A : Type u} [CommRing A] [FiniteRingKrullDim A] {p q : PrimeSpectrum A}
    (hpq : p ⤳ q) (hpq_ne : p ≠ q) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) >
      (((ringKrullDim (A ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) := by
  -- Replace quotient dimensions by coheights and use strict antitonicity of coheight.
  have hpq_lt : p < q :=
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes p q).2 hpq) hpq_ne
  have hq_fin : Order.coheight q < ⊤ := by
    have hq_le :
        ((Order.coheight q : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A :=
      Order.coheight_le_krullDim q
    have hq_lt :
        ((Order.coheight q : ℕ∞) : WithBot ℕ∞) <
          ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hq_le (ringKrullDim_lt_top (R := A))
    exact WithBot.coe_lt_coe.mp hq_lt
  have hp_fin : Order.coheight p < ⊤ := by
    have hp_le :
        ((Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A :=
      Order.coheight_le_krullDim p
    have hp_lt :
        ((Order.coheight p : ℕ∞) : WithBot ℕ∞) <
          ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hp_le (ringKrullDim_lt_top (R := A))
    exact WithBot.coe_lt_coe.mp hp_lt
  have hcoheight : Order.coheight q < Order.coheight p :=
    Order.coheight_strictAnti hpq_lt hq_fin
  have hnat : (Order.coheight q).toNat < (Order.coheight p).toNat := by
    rw [← ENat.coe_lt_coe, ENat.coe_toNat hq_fin.ne, ENat.coe_toNat hp_fin.ne]
    exact hcoheight
  have hpdim := primeQuotientKrullDim_eq_coheight (A := A) p
  have hqdim := primeQuotientKrullDim_eq_coheight (A := A) q
  rw [hpdim, hqdim]
  simp only [WithBot.unbotD_coe]
  exact_mod_cast hnat

/-- Helper for Chap10 Remark 10 160 9: the Krull dimension of a Noetherian local ring is a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  -- Convert the finite local Krull dimension into its natural-number representative.
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Chap10 Remark 10 160 9: a point covered by the top element has coheight one. -/
private lemma coheight_eq_one_of_covBy_top {α : Type*} [PartialOrder α] [OrderTop α]
    {x : α} (hcov : x ⋖ (⊤ : α)) (hfin : Order.coheight x < ⊤) :
    Order.coheight x = (1 : ℕ) := by
  -- Use the recursive characterization of finite coheight and the cover relation with `⊤`.
  rw [Order.coheight_eq_coe_iff]
  refine ⟨hfin, ?_, ?_⟩
  · right
    exact ⟨⊤, hcov.lt, by simp⟩
  · intro y hy
    have hy_top : y = ⊤ := by
      rcases hcov.eq_or_eq hy.le le_top with hyx | hytop
      · exact (hy.ne hyx.symm).elim
      · exact hytop
    simp [hy_top]

/-- Helper for Chap10 Remark 10 160 9: after localizing at the upper prime of an immediate
specialization, the quotient by the lower prime has Krull dimension one. -/
private lemma localizedQuotientKrullDim_eq_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    let pq : PrimeSpectrum (Localization.AtPrime q.asIdeal) :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm
        ⟨p, (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes⟩
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸ pq.asIdeal) = 1 := by
  intro pq
  let Lq := Localization.AtPrime q.asIdeal
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal
  have hp_le_q : p ≤ q := (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes
  have hp_lt_q : p < q := lt_of_le_of_ne hp_le_q hpq.ne
  have hq_mem_iic : q ∈ Set.Iic q := by simp
  have hpq_cov : p ⋖ q := by
    refine covBy_of_eq_or_eq hp_lt_q ?_
    intro r hpr hrq
    have hpr' : p ⤳ r := (PrimeSpectrum.le_iff_specializes p r).1 hpr
    have hrq' : r ⤳ q := (PrimeSpectrum.le_iff_specializes r q).1 hrq
    exact hpq.eq_or_eq hpr' hrq'
  have hcov_sub : (⟨p, hp_le_q⟩ : Set.Iic q) ⋖ ⟨q, hq_mem_iic⟩ := by
    refine covBy_of_eq_or_eq ?_ ?_
    · exact hp_lt_q
    · intro r hpr hrq
      rcases hpq_cov.eq_or_eq hpr hrq with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
  have htop : e (⊤ : PrimeSpectrum Lq) = ⟨q, hq_mem_iic⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap A Lq) (IsLocalRing.maximalIdeal Lq) = q.asIdeal
    exact IsLocalization.AtPrime.comap_maximalIdeal Lq q.asIdeal
  have hpq_apply : e pq = ⟨p, hp_le_q⟩ := by
    change
      (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal)
          ((IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).symm
            ⟨p, hp_le_q⟩) =
        ⟨p, hp_le_q⟩
    exact (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).apply_symm_apply
      ⟨p, hp_le_q⟩
  have hcov_pq_top : pq ⋖ (⊤ : PrimeSpectrum Lq) := by
    -- Transport the ambient cover `p ⋖ q` through the localized spectrum order isomorphism.
    apply (apply_covBy_apply_iff e).mp
    simpa [hpq_apply, htop] using hcov_sub
  have hfin : Order.coheight pq < ⊤ := by
    have hpq_le : ((Order.coheight pq : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim Lq :=
      Order.coheight_le_krullDim pq
    have hpq_lt : ((Order.coheight pq : ℕ∞) : WithBot ℕ∞) <
        ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hpq_le (ringKrullDim_lt_top (R := Lq))
    exact WithBot.coe_lt_coe.mp hpq_lt
  have hcoh : Order.coheight pq = (1 : ℕ) :=
    coheight_eq_one_of_covBy_top hcov_pq_top hfin
  -- Quotient dimension is coheight, and the localized lower prime has coheight one.
  rw [primeQuotientKrullDim_eq_coheight (A := Lq) pq, hcoh]
  norm_num

/-- Helper for Chap10 Remark 10 160 9: local dimension increases by one across an immediate
specialization under the full-support Cohen-Macaulay dimension formula. -/
private lemma localizedRingKrullDim_eq_add_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime p.asIdeal) + 1 := by
  let _ : Module.Finite A N := hCM.toFinite
  let Lq := Localization.AtPrime q.asIdeal
  let Nq := LocalizedModule.AtPrime q.asIdeal N
  have hp_le_q : p ≤ q := (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes
  let pq : PrimeSpectrum Lq :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).symm ⟨p, hp_le_q⟩
  have hLCM : Module.LocallyCohenMacaulay A N := by
    let _ : Module.CohenMacaulay A N := hCM
    exact Module.locallyCohenMacaulay_of_cohenMacaulay A N hsupp
  have hCMq : Module.CohenMacaulay Lq Nq :=
    hLCM.localizedModule_cohenMacaulay q
  have hsuppq : Module.support Lq Nq = Set.univ :=
    localized_support_eq_univ_of_support_eq_univ (A := A) (N := N) hsupp q
  have hformula :
      ringKrullDim Lq =
        ringKrullDim (Localization.AtPrime pq.asIdeal) + ringKrullDim (Lq ⧸ pq.asIdeal) := by
    -- Apply the full-support Cohen-Macaulay dimension formula inside the upper-prime localization.
    exact
      ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
        (A := Lq) (N := Nq) hCMq hsuppq pq.asIdeal
  have hquot : ringKrullDim (Lq ⧸ pq.asIdeal) = 1 := by
    simpa [Lq, pq] using
      localizedQuotientKrullDim_eq_one_of_immediateSpecialization
        (A := A) (p := p) (q := q) hpq
  have hpq_comap : Ideal.comap (algebraMap A Lq) pq.asIdeal = p.asIdeal := by
    have hpq_point : PrimeSpectrum.comap (algebraMap A Lq) pq = p := by
      change ((IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal) pq).1 = p
      simp [pq]
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpq_point
  have hiter :
      ringKrullDim (Localization.AtPrime pq.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    let eDouble :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := q.asIdeal.primeCompl) pq.asIdeal
    have hiter0 :
        ringKrullDim (Localization.AtPrime pq.asIdeal) =
          ringKrullDim
            (Localization.AtPrime (Ideal.comap (algebraMap A Lq) pq.asIdeal)) := by
      exact (ringKrullDim_eq_of_ringEquiv eDouble.toRingEquiv).symm
    let Icomap : Ideal A := Ideal.comap (algebraMap A Lq) pq.asIdeal
    letI : Icomap.IsPrime := Ideal.comap_isPrime (algebraMap A Lq) pq.asIdeal
    have htarget :
        ringKrullDim (Localization.AtPrime Icomap) =
          ringKrullDim (Localization.AtPrime p.asIdeal) := by
      let eEq : Localization.AtPrime Icomap ≃+* Localization.AtPrime p.asIdeal :=
        Localization.localRingEquiv Icomap p.asIdeal (RingEquiv.refl A) (by
          simpa [Icomap] using hpq_comap)
      exact ringKrullDim_eq_of_ringEquiv eEq
    exact hiter0.trans htarget
  -- The localized formula now reads `dim A_q = dim A_p + 1`.
  rw [hquot, hiter] at hformula
  exact hformula

/-- Helper for Chap10 Remark 10 160 9: the prime-quotient dimension drops by exactly one along an
immediate specialization for full-support Cohen-Macaulay modules over local rings. -/
private lemma primeQuotientKrullDimension_eq_add_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) =
      (((ringKrullDim (A ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) + 1 := by
  obtain ⟨dA, hA⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := A)
  obtain ⟨dpLoc, hpLoc⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring
      (A := Localization.AtPrime p.asIdeal)
  obtain ⟨dqLoc, hqLoc⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring
      (A := Localization.AtPrime q.asIdeal)
  letI : IsLocalRing (A ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  letI : IsLocalRing (A ⧸ q.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q.asIdeal) Ideal.Quotient.mk_surjective
  obtain ⟨dpQuot, hpQuot⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring (A := A ⧸ p.asIdeal)
  obtain ⟨dqQuot, hqQuot⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring (A := A ⧸ q.asIdeal)
  have hpFormula :
    ringKrullDim A =
        ringKrullDim (Localization.AtPrime p.asIdeal) + ringKrullDim (A ⧸ p.asIdeal) :=
    ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
      (A := A) (N := N) hCM hsupp p.asIdeal
  have hqFormula :
      ringKrullDim A =
        ringKrullDim (Localization.AtPrime q.asIdeal) + ringKrullDim (A ⧸ q.asIdeal) :=
    ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
      (A := A) (N := N) hCM hsupp q.asIdeal
  have hLoc :
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) + 1 :=
    localizedRingKrullDim_eq_add_one_of_immediateSpecialization
      (A := A) (N := N) hCM hsupp hpq
  have hpNat : dA = dpLoc + dpQuot := by
    have hpNatWB : ((dA : ℕ∞) : WithBot ℕ∞) =
        ((dpLoc + dpQuot : ℕ) : WithBot ℕ∞) := by
      simpa [hA, hpLoc, hpQuot] using hpFormula
    exact_mod_cast hpNatWB
  have hqNat : dA = dqLoc + dqQuot := by
    have hqNatWB : ((dA : ℕ∞) : WithBot ℕ∞) =
        ((dqLoc + dqQuot : ℕ) : WithBot ℕ∞) := by
      simpa [hA, hqLoc, hqQuot] using hqFormula
    exact_mod_cast hqNatWB
  have hLocNat : dqLoc = dpLoc + 1 := by
    have hLocNatWB : ((dqLoc : ℕ∞) : WithBot ℕ∞) =
        ((dpLoc + 1 : ℕ) : WithBot ℕ∞) := by
      simpa [hqLoc, hpLoc] using hLoc
    exact_mod_cast hLocNatWB
  have hQuotNat : dpQuot = dqQuot + 1 := by
    -- Cancel the common local dimension from the two dimension-formula equalities.
    omega
  have hpUnbot :
      (ringKrullDim (A ⧸ p.asIdeal)).unbotD 0 = (dpQuot : ℕ∞) := by
    rw [hpQuot]
    exact WithBot.unbotD_coe 0 (dpQuot : ℕ∞)
  have hqUnbot :
      (ringKrullDim (A ⧸ q.asIdeal)).unbotD 0 = (dqQuot : ℕ∞) := by
    rw [hqQuot]
    exact WithBot.unbotD_coe 0 (dqQuot : ℕ∞)
  rw [hpUnbot, hqUnbot]
  simp only [ENat.toNat_coe]
  exact_mod_cast hQuotNat

/-- Helper for Chap10 Remark 10 160 9: prime-quotient Krull dimension is a dimension function for
a full-support Cohen-Macaulay module over a Noetherian local ring. -/
private lemma primeQuotientKrullDimension_isDimensionFunction_of_fullSupportCohenMacaulay
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    IsDimensionFunction
      (fun p : PrimeSpectrum A ↦
        (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) where
  strict_of_specializes := by
    intro p q hpq hpq_ne
    -- Proper specialization is the already-proved strict coheight decrease.
    exact primeQuotientKrullDimension_strict_of_specializes hpq hpq_ne
  eq_add_one_of_immediateSpecialization := by
    intro p q hpq
    -- Immediate specialization is the exact one-step drop isolated above.
    exact
      primeQuotientKrullDimension_eq_add_one_of_immediateSpecialization
        (A := A) (N := N) hCM hsupp hpq

/-- Helper for Chap10 Remark 10 160 9: a dimension function given by prime-quotient dimensions
forces catenarity of a Noetherian local ring. -/
private theorem isCatenaryRing_of_primeQuotientKrullDimension_isDimensionFunction
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim :
      IsDimensionFunction
        (fun p : PrimeSpectrum A ↦
          (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ))) :
    IsCatenaryRing A := by
  -- The topological criterion turns the dimension function into catenarity of `Spec A`.
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  exact hdim.catenarySpace

/-- Helper for Chap10 Remark 10 160 9: a Noetherian local ring carrying a full-support
Cohen-Macaulay module is catenary. -/
private theorem isCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    IsCatenaryRing A := by
  -- Package the quotient-dimension function, then apply the topological catenarity criterion.
  exact
    isCatenaryRing_of_primeQuotientKrullDimension_isDimensionFunction
      (primeQuotientKrullDimension_isDimensionFunction_of_fullSupportCohenMacaulay
        (A := A) (N := N) hCM hsupp)

/-- Helper for Chap10 Remark 10 160 9: a prime localization is catenary when a locally
Cohen-Macaulay module has full support before localization. -/
private theorem isCatenaryRing_localizationAtPrime_of_locallyCohenMacaulay_support_eq_univ
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hLCM : Module.LocallyCohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    (q : PrimeSpectrum A) :
    IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
  let _ : Module.Finite A N := hLCM.toFinite
  have hCMq :
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal N) :=
    hLCM.localizedModule_cohenMacaulay q
  have hsuppq :
      Module.support (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal N) =
        Set.univ :=
    localized_support_eq_univ_of_support_eq_univ (A := A) (N := N) hsupp q
  -- The localized Cohen-Macaulay module now satisfies the local full-support catenarity
  -- criterion.
  exact
    isCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
      (A := Localization.AtPrime q.asIdeal) (N := LocalizedModule.AtPrime q.asIdeal N)
      hCMq hsuppq

/-- Helper for Chap10 Remark 10 160 9: over a Noetherian local ring, the polynomial ring is
catenary once the base admits a Cohen-Macaulay module with full support. -/
private theorem isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) (n : ℕ) :
    IsCatenaryRing (MvPolynomial (Fin n) A) := by
  let _ : Module.Finite A N := hCM.toFinite
  let S := MvPolynomial (Fin n) A
  let P := S ⊗[A] N
  have hLCM : Module.LocallyCohenMacaulay A N := by
    let _ : Module.CohenMacaulay A N := hCM
    exact Module.locallyCohenMacaulay_of_cohenMacaulay A N hsupp
  have hLCMP : Module.LocallyCohenMacaulay S P :=
    Module.LocallyCohenMacaulay.mvPolynomial hLCM n
  have hsuppP :=
    support_tensor_eq_univ_of_support_eq_univ
      (A := A) (S := S) (N := N) hsupp
  let _ : Module.Finite S P := hLCMP.toFinite
  -- Check catenarity after localizing the polynomial ring at each prime.
  refine ((isCatenaryRing_localization_tfae (R := S)).out 1 0 rfl rfl).mp ?_
  intro q
  -- Each localized polynomial ring is handled by the prime-local criterion just isolated.
  exact
    isCatenaryRing_localizationAtPrime_of_locallyCohenMacaulay_support_eq_univ
      (A := S) (N := P) hLCMP hsuppP q

/-- Helper for Chap10 Remark 10 160 9: over a Noetherian local ring, a Cohen-Macaulay module with
full support forces the ring to be universally catenary. -/
private theorem universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    UniversallyCatenaryRing A := by
  let _ : Module.Finite A N := hCM.toFinite
  refine { catenary_of_finiteType := ?_ }
  intro B _ _ _
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let S := MvPolynomial (Fin n) A
  letI : IsCatenaryRing S :=
    isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
      (A := A) (N := N) hCM hsupp n
  letI : IsCatenaryRing (S ⧸ RingHom.ker π) :=
    quotient_catenaryRing (R := S) (I := RingHom.ker π)
  let e : S ⧸ RingHom.ker π ≃+* B := RingHom.quotientKerEquivOfSurjective hπsurj
  -- Present the finite-type algebra as a quotient of a catenary polynomial ring.
  exact isCatenaryRing_of_ringEquiv e

/-- Helper for Chap10 Remark 10 160 9: a regular local ring is Cohen-Macaulay. -/
private theorem regularLocalRing_cohenMacaulayRing
    (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    CohenMacaulayRing S := by
  -- Route correction: use the owner-level regular-to-Cohen-Macaulay bridge primewise instead of
  -- the older full-support support calculation local to this file.
  refine { toIsNoetherian := inferInstance, toLocallyCohenMacaulay := ?_ }
  refine { toFinite := inferInstance, localizedModule_cohenMacaulay := ?_ }
  intro p
  -- Each prime localization is still regular local, so the self-module is Cohen-Macaulay there.
  let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime p
  simpa using
    (regularLocalRing_selfModule_cohenMacaulay
      (R := Localization.AtPrime p.asIdeal))

/-- Helper for Chap10 Remark 10 160 9: a regular local ring is universally catenary. -/
private theorem universallyCatenaryRing_of_regularLocalRing
    (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    UniversallyCatenaryRing.{u, u} S := by
  -- Route correction: pass through the canonical owner theorem for Cohen-Macaulay rings rather
  -- than the duplicate full-support catenarity development above.
  let _ : CohenMacaulayRing S := regularLocalRing_cohenMacaulayRing S
  exact universallyCatenaryRing_of_cohenMacaulayRing (R := S) inferInstance

/-- Helper for Chap10 Remark 10 160 9: a quotient of a regular local ring is universally
catenary. -/
private theorem universallyCatenaryRing_of_regularLocalRing_quotient
    (R S : Type u) [CommRing R] [CommRing S] [IsRegularLocalRing S] (I : Ideal S)
    (e : (S ⧸ I) ≃+* R) :
    UniversallyCatenaryRing.{u, u} R := by
  -- Route correction: isolate the regular-local core before quotient descent and transport.
  let _ : UniversallyCatenaryRing S :=
    universallyCatenaryRing_of_regularLocalRing S
  -- Universal catenarity descends to the quotient, then transports across the chosen
  -- quotient equivalence.
  let _ : UniversallyCatenaryRing (S ⧸ I) := inferInstance
  exact
    (universallyCatenaryRing_of_ringEquiv (R := S ⧸ I) (S := R) e :
      UniversallyCatenaryRing R)

/-- Helper for Chap10 Remark 10 160 9: any ring admitting a regular-local quotient presentation
is universally catenary. -/
private theorem universallyCatenaryRing_of_exists_regularLocalRing_quotient
    (R : Type u) [CommRing R]
    (hquot : ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (I : Ideal S),
      Nonempty ((S ⧸ I) ≃+* R)) :
    UniversallyCatenaryRing.{u, u} R := by
  -- Unpack the quotient presentation once, then delegate the descent and transport step to the
  -- regular-local quotient bridge.
  rcases hquot with ⟨S, hS, hreg, I, hI⟩
  let _ : CommRing S := hS
  let _ : IsRegularLocalRing S := hreg
  rcases hI with ⟨e⟩
  exact universallyCatenaryRing_of_regularLocalRing_quotient R S I e

/-- Helper for Chap10 Remark 10 160 9: a quotient of a finite-variable power series ring over a
regular local ring is already a quotient of a regular local ring. -/
private theorem exists_regularLocalRing_quotient_of_mvPowerSeries_quotient
    (R A σ : Type u) [CommRing R] [CommRing A] [IsRegularLocalRing A] [Finite σ]
    (I : Ideal (MvPowerSeries σ A)) (e : (MvPowerSeries σ A ⧸ I) ≃+* R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (J : Ideal S),
      Nonempty ((S ⧸ J) ≃+* R) := by
  -- Choose the finite-variable power series ring itself as the regular-local source.
  refine ⟨MvPowerSeries σ A, inferInstance, mvPowerSeries_finite_isRegularLocalRing A σ, I, ?_⟩
  exact ⟨e⟩

-- Proof sketch: apply the Cohen structure theorem. In equal characteristic, the source is a
-- formal power series ring over the residue field; in mixed characteristic, it is a formal power
-- series ring over a Cohen ring. Both source rings are regular local, and the structure theorem
-- identifies `R` with a quotient by a closed ideal.
@[stacks 032C]
/-- Chap10 Remark 10 160 9 (1): every Noetherian complete local ring is a quotient of a regular
local ring. -/
theorem exists_regularLocalRing_quotient_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (I : Ideal S),
      Nonempty ((S ⧸ I) ≃+* R) := sorry

-- Proof sketch: choose a regular local ring `S` and an ideal `I` with `S ⧸ I ≃+* R` from the
-- quotient presentation above. Lemma `10.105.9` makes the regular local ring `S` universally
-- catenary, and universal catenarity descends to the quotient `S ⧸ I`, hence to `R`.
@[stacks 032C]
/-- Chap10 Remark 10 160 9 (2): a Noetherian complete local ring is universally
catenary. -/
theorem universallyCatenaryRing_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    UniversallyCatenaryRing.{u, u} R := sorry

end
