import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Ideal

-- Declarations for this item will be appended below by the statement pipeline.

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
