import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1
import StacksProject_2024.Chap10.Lemma_10_31_2
import StacksProject_2024.Chap10.Lemma_10_106_7
import StacksProject_2024.Chap10.Lemma_10_119_2_Koll_r
import StacksProject_2024.Chap10.Lemma_10_119_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Finset IsLocalRing MvPowerSeries Finsupp
open RingTheory.Sequence
open scoped Pointwise

/-- Helper for Chap10 Example 10 119 4: zero-variable formal power series are just the
coefficient ring. -/
private theorem dualNumberPowerSeriesMvPowerSeries_fin_zero_ringEquiv
    (R : Type u) [CommSemiring R] :
    Nonempty (MvPowerSeries (Fin 0) R ≃+* R) := by
  refine ⟨?_⟩
  exact
    { toFun := MvPowerSeries.constantCoeff
      invFun := MvPowerSeries.C
      left_inv := by
        intro f
        ext d
        have hd : d = 0 := Subsingleton.elim _ _
        simp [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      right_inv := by
        intro r
        simp
      map_mul' := by
        intro f g
        simp
      map_add' := by
        intro f g
        simp }

/-- Helper for Chap10 Example 10 119 4: variables indexed by a sum split as iterated
multivariable power series. -/
private theorem dualNumberPowerSeriesMvPowerSeries_sum_ringEquiv
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
              (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := by
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
        simp [split, unsplit, Finsupp.comapDomain_inl_sumElim,
          Finsupp.comapDomain_inr_sumElim]
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
                (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                  f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := h
      _ = (F * G) d e := by
            calc
              Finset.sum (antidiagonal d)
                  (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
                    Finset.sum (antidiagonal e)
                      (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                        f (sumElim p.1 q.1) * g (sumElim p.2 q.2)))
                  = Finset.sum (antidiagonal d) (fun p ↦ (F p.1 * G p.2) e) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      simpa [F, G] using MvPowerSeries.coeff_mul e (F p.1) (G p.2)
              _ = (Finset.sum (antidiagonal d) (fun p ↦ F p.1 * G p.2)) e := by
                    exact (Finset.sum_apply e (antidiagonal d)
                      fun p ↦ F p.1 * G p.2).symm
              _ = (F * G) d e := by
                    simpa using congrArg (fun s : MvPowerSeries τ A ↦ s e)
                      (MvPowerSeries.coeff_mul d F G)
  · intro f g
    rfl

/-- Helper for Chap10 Example 10 119 4: a distinguished `Option.none` variable is equivalent to
a unit summand. -/
private noncomputable def dualNumberPowerSeriesOptionToUnitSum (σ : Type*) :
    Option σ ≃ Unit ⊕ σ :=
  (Equiv.optionEquivSumPUnit σ).trans (Equiv.sumComm _ _)

/-- Helper for Chap10 Example 10 119 4: an `Option`-indexed power-series ring is a one-variable
power-series ring over the remaining variables. -/
private theorem dualNumberPowerSeriesOptionMvPowerSeries_ringEquiv
    (A : Type u) [CommSemiring A] (σ : Type*) :
    Nonempty (MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)) := by
  rcases dualNumberPowerSeriesMvPowerSeries_sum_ringEquiv A Unit σ with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (dualNumberPowerSeriesOptionToUnitSum σ)).toRingEquiv.trans e⟩

/-- Helper for Chap10 Example 10 119 4: adding one `Fin`-indexed variable gives a one-variable
power-series ring over the previous finite-variable ring. -/
private theorem dualNumberPowerSeriesMvPowerSeries_fin_succ_ringEquiv
    (A : Type u) [CommSemiring A] (d : ℕ) :
    Nonempty (MvPowerSeries (Fin (d + 1)) A ≃+*
      PowerSeries (MvPowerSeries (Fin d) A)) := by
  rcases dualNumberPowerSeriesOptionMvPowerSeries_ringEquiv A (Fin d) with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (_root_.finSuccEquiv d)).toRingEquiv.trans e⟩

/-- Helper for Chap10 Example 10 119 4: the kernel of the constant-coefficient map on
`A⟦X⟧` is generated by `X`. -/
private theorem dualNumberPowerSeriesPowerSeries_constantCoeff_ker_eq_span_X
    (A : Type u) [CommRing A] :
    RingHom.ker (PowerSeries.constantCoeff (R := A)) =
      Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)) := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- Helper for Chap10 Example 10 119 4: quotienting `A⟦X⟧` by `(X)` recovers `A`. -/
private theorem dualNumberPowerSeriesPowerSeries_quotient_span_X_ringEquiv
    (A : Type u) [CommRing A] :
    Nonempty (((PowerSeries A) ⧸
      Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) ≃+* A) := by
  refine ⟨?_⟩
  exact
    (Ideal.quotEquivOfEq
      (dualNumberPowerSeriesPowerSeries_constantCoeff_ker_eq_span_X A).symm).trans
      (RingHom.quotientKerEquivOfSurjective (PowerSeries.constantCoeff_surj (R := A)))

/-- Helper for Chap10 Example 10 119 4: the `(X)`-quotient of a power-series ring over a regular
local ring is regular local. -/
private theorem dualNumberPowerSeriesPowerSeries_quotient_span_X_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing
      ((PowerSeries A) ⧸
        Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A))) := by
  rcases dualNumberPowerSeriesPowerSeries_quotient_span_X_ringEquiv A with ⟨e⟩
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- Helper for Chap10 Example 10 119 4: the power-series variable lies in the maximal ideal. -/
private theorem dualNumberPowerSeriesPowerSeries_X_mem_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro hX_unit
  have hconst_unit :
      IsUnit (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries A)) :=
    PowerSeries.isUnit_constantCoeff _ hX_unit
  simpa using hconst_unit

/-- Helper for Chap10 Example 10 119 4: over a regular local coefficient ring, the power-series
variable is regular. -/
private theorem dualNumberPowerSeriesPowerSeries_X_isRegular
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegular (PowerSeries.X : PowerSeries A) := by
  let _ : IsDomain A := regularLocalRing_isDomain
  exact
    isRegular_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr PowerSeries.X_ne_zero)

/-- Helper for Chap10 Example 10 119 4: a singleton weakly regular sequence in the maximal ideal
is a regular sequence. -/
private theorem dualNumberPowerSeries_regular_singleton_of_mem_maximalIdeal_of_isSMulRegular
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    IsRegular M [x] := by
  -- Proof comment: the maximal-ideal membership upgrades the weakly regular singleton.
  exact
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((isWeaklyRegular_singleton_iff M x).2 hreg)

/-- Helper for Chap10 Example 10 119 4: the singleton list `[X]` is a regular sequence in a
regular local power-series ring. -/
private theorem dualNumberPowerSeriesPowerSeries_X_regular_singleton
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegular (PowerSeries A) [(PowerSeries.X : PowerSeries A)] := by
  let _ : Module.Finite (PowerSeries A) (PowerSeries A) := Module.Finite.self (PowerSeries A)
  have hX_mem :
      (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) :=
    dualNumberPowerSeriesPowerSeries_X_mem_maximalIdeal A
  have hX_smulRegular :
      IsSMulRegular (PowerSeries A) (PowerSeries.X : PowerSeries A) :=
    (dualNumberPowerSeriesPowerSeries_X_isRegular A).isSMulRegular
  exact
    dualNumberPowerSeries_regular_singleton_of_mem_maximalIdeal_of_isSMulRegular
      hX_mem
      hX_smulRegular

/-- Helper for Chap10 Example 10 119 4: quotienting by `Ideal.ofList [X]` is regular local. -/
private theorem dualNumberPowerSeriesPowerSeries_quotient_ofList_singleton_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing ((PowerSeries A) ⧸ Ideal.ofList [(PowerSeries.X : PowerSeries A)]) := by
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
    dualNumberPowerSeriesPowerSeries_quotient_span_X_isRegularLocalRing A
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- Helper for Chap10 Example 10 119 4: a power-series ring over a regular local ring is regular
local. -/
private theorem dualNumberPowerSeriesPowerSeries_isRegularLocalRing_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing (PowerSeries A) := by
  have hregX : IsRegular (PowerSeries A) [(PowerSeries.X : PowerSeries A)] :=
    dualNumberPowerSeriesPowerSeries_X_regular_singleton A
  have hquot :
      IsRegularLocalRing ((PowerSeries A) ⧸ Ideal.ofList [(PowerSeries.X : PowerSeries A)]) :=
    dualNumberPowerSeriesPowerSeries_quotient_ofList_singleton_isRegularLocalRing A
  exact isRegularLocalRing_of_quotient_of_isRegular hregX hquot

/-- Helper for Chap10 Example 10 119 4: finite-variable formal power-series rings over regular
local rings are regular local. -/
private instance dualNumberPowerSeriesMvPowerSeries_fin_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin d) R) := by
  induction d with
  | zero =>
      rcases dualNumberPowerSeriesMvPowerSeries_fin_zero_ringEquiv R with ⟨e⟩
      exact IsRegularLocalRing.of_ringEquiv e.symm
  | succ d ih =>
      rcases dualNumberPowerSeriesMvPowerSeries_fin_succ_ringEquiv R d with ⟨e⟩
      let _ : IsRegularLocalRing (MvPowerSeries (Fin d) R) := ih
      let _ : IsRegularLocalRing (PowerSeries (MvPowerSeries (Fin d) R)) :=
        dualNumberPowerSeriesPowerSeries_isRegularLocalRing_of_isRegularLocalRing
          (MvPowerSeries (Fin d) R)
      exact IsRegularLocalRing.of_ringEquiv e.symm

/-- Helper for Chap10 Example 10 119 4: adjoining one formal power-series variable raises Krull
dimension by one over a Noetherian local domain. -/
private theorem dualNumberPowerSeriesRingKrullDim_powerSeries_eq_succ
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ringKrullDim (PowerSeries A) = ringKrullDim A + 1 := by
  have hX_mem :
      (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) :=
    dualNumberPowerSeriesPowerSeries_X_mem_maximalIdeal A
  have hX_nonZeroDiv :
      (PowerSeries.X : PowerSeries A) ∈ nonZeroDivisors (PowerSeries A) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr PowerSeries.X_ne_zero
  rcases dualNumberPowerSeriesPowerSeries_quotient_span_X_ringEquiv A with ⟨e⟩
  calc
    ringKrullDim (PowerSeries A) =
        ringKrullDim
          (((PowerSeries A) ⧸
            Ideal.span ({(PowerSeries.X : PowerSeries A)} : Set (PowerSeries A)))) + 1 := by
          symm
          simpa using
            (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
              hX_nonZeroDiv hX_mem)
    _ = ringKrullDim A + 1 := by
          rw [ringKrullDim_eq_of_ringEquiv e]

/-- Helper for Chap10 Example 10 119 4: the Krull dimension of a finite-variable formal
power-series ring over a field is the number of variables. -/
private theorem dualNumberPowerSeriesRingKrullDim_mvPowerSeries_fin_field
    (k : Type u) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  induction d with
  | zero =>
      rcases dualNumberPowerSeriesMvPowerSeries_fin_zero_ringEquiv k with ⟨e⟩
      simpa [ringKrullDim_eq_zero_of_field k] using
        (ringKrullDim_eq_of_ringEquiv e)
  | succ d ih =>
      rcases dualNumberPowerSeriesMvPowerSeries_fin_succ_ringEquiv k d with ⟨e⟩
      let _ : IsRegularLocalRing (MvPowerSeries (Fin d) k) := by
        infer_instance
      calc
        ringKrullDim (MvPowerSeries (Fin (d + 1)) k)
            = ringKrullDim (PowerSeries (MvPowerSeries (Fin d) k)) := by
                exact ringKrullDim_eq_of_ringEquiv e
        _ = ringKrullDim (MvPowerSeries (Fin d) k) + 1 := by
              exact dualNumberPowerSeriesRingKrullDim_powerSeries_eq_succ
                (MvPowerSeries (Fin d) k)
        _ = d + 1 := by
              rw [ih]

variable (k : Type u) [Field k]

/- 
Domain-style sampling pass for Example 10.119.4.

Primary domain: formal power-series substitutions and square-zero quotients in local Noetherian
commutative algebra, culminating in the chapter owner
`HasKollarExceptionalFiniteExtension`.

Sampled owner declarations:
* `MvPowerSeries.HasSubst`;
* `MvPowerSeries.substAlgHom`;
* `Ideal.Quotient.lift`;
* `RingHom.toAlgebra`;
* `RingHom.IsKollarExceptionalFiniteExtension`;
* `HasKollarExceptionalFiniteExtension`.

Owner abstraction:
* source-facing owners in this file are the source ring `dualNumberPowerSeriesRing k`, the target
  ring `dualNumberPowerSeriesTargetRing k`, the explicit extension
  `dualNumberPowerSeries_extension k`, and its iterated form
  `dualNumberPowerSeries_iteratedExtension k n`;
* the map-level bridge owner is `RingHom.IsKollarExceptionalFiniteExtension`;
* the exceptional finite-extension conclusion already has the canonical chapter owner
  `HasKollarExceptionalFiniteExtension`, so the example should connect that owner to the explicit
  source-facing map rather than replace the map by a bare existential conclusion.

Primitive vs derived:
* primitive data: the source and target ambient rings, their square-zero ideals, the two quotient
  rings, and the explicit extension map together with its iterated form;
* derived API: the ambient substitution and quotient-lift plumbing, the induced algebra structure
  on the target, the local/Noetherian/Cohen-Macaulay/dimension facts, and the final Kollár
  consequence.

Source/core/bridge triage:
* `source-facing`: `dualNumberPowerSeriesRing`, `dualNumberPowerSeriesTargetRing`,
  `dualNumberPowerSeries_extension`, and `dualNumberPowerSeries_iteratedExtension`;
* `bridge/view`: `RingHom.IsKollarExceptionalFiniteExtension` for the explicit extension map;
* `core/canonical`: `HasKollarExceptionalFiniteExtension`;
* additional `bridge/view`: the ambient substitution, its quotient descent, and the induced
  `Algebra` structure on the target ring.
-/

/-- The ambient two-variable formal power series ring used to model `k[[x, y]]`. -/
abbrev dualNumberPowerSeriesAmbient : Type u :=
  MvPowerSeries (Fin 2) k

/-- The ambient two-variable formal power series ring used to model `k[[x, z]]`. -/
abbrev dualNumberPowerSeriesTargetAmbient : Type u :=
  MvPowerSeries Bool k

local notation "A" => dualNumberPowerSeriesAmbient k
local notation "B" => dualNumberPowerSeriesTargetAmbient k
local notation "xs" => (X (0 : Fin 2) : A)
local notation "y" => (X (1 : Fin 2) : A)
local notation "x" => (X false : B)
local notation "z" => (X true : B)

/-- The square-zero ideal generated by the second variable. -/
def dualNumberPowerSeriesSquareIdeal : Ideal A :=
  Ideal.span ({y ^ 2} : Set A)

local notation "I" => dualNumberPowerSeriesSquareIdeal k

/-- The square-zero ideal generated by `z^2` in the target presentation `k[[x, z]]`. -/
def dualNumberPowerSeriesTargetSquareIdeal : Ideal B :=
  Ideal.span ({z ^ 2} : Set B)

local notation "J" => dualNumberPowerSeriesTargetSquareIdeal k

/-- Helper for Chap10 Example 10 119 4: the two square-zero presentation ideals are proper. -/
private lemma dualNumberPowerSeriesSquareIdeals_ne_top : I ≠ ⊤ ∧ J ≠ ⊤ := by
  constructor
  · -- The source generator has zero constant coefficient, so it cannot generate the unit ideal.
    have hy_not_unit : ¬ IsUnit (y ^ 2) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    exact Ideal.span_singleton_ne_top hy_not_unit
  · -- The target generator is handled by the same constant-coefficient test.
    have hz_not_unit : ¬ IsUnit (z ^ 2) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    exact Ideal.span_singleton_ne_top hz_not_unit

/-- The quotient ring `k[[x, y]]/(y^2)`. -/
abbrev dualNumberPowerSeriesRing : Type u :=
  A ⧸ I

local notation "R" => dualNumberPowerSeriesRing k

/-- Helper for Chap10 Example 10 119 4: the source square-zero quotient is nonzero. -/
private instance dualNumberPowerSeriesRing_nontrivial : Nontrivial R :=
  Ideal.Quotient.nontrivial_iff.mpr (dualNumberPowerSeriesSquareIdeals_ne_top k).1

/-- The quotient `k[[x, y]]/(y^2)` is a local ring. -/
instance dualNumberPowerSeriesRing_isLocalRing : IsLocalRing R := by
  -- The ambient power-series ring is local, and the proper quotient map is surjective.
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The quotient `k[[x, y]]/(y^2)` is Noetherian. -/
instance dualNumberPowerSeriesRing_isNoetherianRing : IsNoetherianRing R := by
  -- Lemma 10.31.2 supplies the Noetherian ambient power-series ring, and quotients inherit it.
  infer_instance

/-- The quotient ring `k[[x, z]]/(z^2)`. -/
abbrev dualNumberPowerSeriesTargetRing : Type u :=
  B ⧸ J

local notation "S" => dualNumberPowerSeriesTargetRing k

/-- Helper for Chap10 Example 10 119 4: the target square-zero quotient is nonzero. -/
private instance dualNumberPowerSeriesTargetRing_nontrivial : Nontrivial S :=
  Ideal.Quotient.nontrivial_iff.mpr (dualNumberPowerSeriesSquareIdeals_ne_top k).2

-- Proof sketch: the index type `Fin 2` is finite, and both substituted power series have zero
-- constant coefficient, so the standard finiteness criterion for power-series substitution applies.
/-- The substitution `x ↦ x`, `y ↦ x^n z` is admissible from `k[[x, y]]` to `k[[x, z]]`. -/
private lemma dualNumberPowerSeries_iteratedHasSubst (n : ℕ) :
    HasSubst (![x, x ^ n * z] : Fin 2 → B) := by
  -- Proof comment: both substituted coordinates have zero constant coefficient, so the finite
  -- variable substitution criterion applies directly.
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro i
  fin_cases i
  · simp
  · simp

/-- The ambient ring map induced by `x ↦ x`, `y ↦ x^n z`. -/
private def dualNumberPowerSeries_iteratedSubst (n : ℕ) : A →ₐ[k] B :=
  substAlgHom (dualNumberPowerSeries_iteratedHasSubst k n)

/-- The ambient substitution followed by reduction modulo the square-zero ideal. -/
private abbrev dualNumberPowerSeries_iteratedTargetRingHom (n : ℕ) : A →+* S :=
  (Ideal.Quotient.mk J).comp
    (dualNumberPowerSeries_iteratedSubst k n).toRingHom

/-- Helper for Chap10 Example 10 119 4: the ambient substitution sends the nilpotent generator
`y` to the class of `x^n z` in the target quotient. -/
private lemma dualNumberPowerSeries_iteratedTargetRingHom_nilpotentGenerator (n : ℕ) :
    dualNumberPowerSeries_iteratedTargetRingHom k n y =
      Ideal.Quotient.mk J (x ^ n * z) := by
  -- Proof comment: evaluate the substitution on the second variable and then reduce modulo `J`.
  rw [dualNumberPowerSeries_iteratedTargetRingHom, RingHom.comp_apply,
    dualNumberPowerSeries_iteratedSubst]
  have hX :
      Ideal.Quotient.mk J ((MvPowerSeries.substAlgHom
          (dualNumberPowerSeries_iteratedHasSubst k n)) (X (1 : Fin 2) : A)) =
        Ideal.Quotient.mk J ((![x, x ^ n * z] : Fin 2 → B) 1) := by
    exact congrArg (Ideal.Quotient.mk J)
      (MvPowerSeries.substAlgHom_X (dualNumberPowerSeries_iteratedHasSubst k n) (1 : Fin 2))
  simpa using hX

-- Proof sketch: the generator `y^2` is sent to `(x^n z)^2 = x^(2n) z^2`, which vanishes in the
-- target quotient because `z^2` generates the defining ideal; then extend from the generator to
-- its span.
/-- The source square-zero ideal is killed by the substitution `y ↦ x^n z` after passing to the
target quotient. -/
private lemma dualNumberPowerSeries_iteratedTargetRingHom_squareIdeal_eq_zero (n : ℕ)
    {f : A} (hf : f ∈ I) :
    dualNumberPowerSeries_iteratedTargetRingHom k n f = 0 := by
  -- Proof comment: it is enough to check the generator `y^2`, since `I = (y^2)`.
  have hker : I ≤ RingHom.ker (dualNumberPowerSeries_iteratedTargetRingHom k n) := by
    rw [dualNumberPowerSeriesSquareIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    -- Proof comment: the image of `y^2` is the class of a multiple of `z^2`, hence zero mod `J`.
    rw [map_pow, dualNumberPowerSeries_iteratedTargetRingHom_nilpotentGenerator, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [dualNumberPowerSeriesTargetSquareIdeal, Ideal.mem_span_singleton']
    refine ⟨x ^ n * x ^ n, ?_⟩
    calc
      (x ^ n * x ^ n) * z ^ 2 = (x ^ n * x ^ n) * (z * z) := by rw [pow_two]
      _ = (x ^ n * z) * (x ^ n * z) := by ring
      _ = (x ^ n * z) ^ 2 := by rw [pow_two]
  -- Proof comment: membership in the kernel is exactly the desired vanishing statement.
  exact RingHom.mem_ker.mp (hker hf)

/-- The quotient ring map modeling the iterated extension that adjoins `y / x^n`. -/
def dualNumberPowerSeries_iteratedExtension (n : ℕ) : R →+* S :=
  Ideal.Quotient.lift I
    (dualNumberPowerSeries_iteratedTargetRingHom k n)
    (fun _ hf ↦ dualNumberPowerSeries_iteratedTargetRingHom_squareIdeal_eq_zero k n hf)

/-- Helper for Chap10 Example 10 119 4: the `y^j` coefficient of a source ambient power series,
viewed as a one-variable power series in `x`. -/
private def dualNumberPowerSeriesSourceCoeff (j : Fin 2) (f : A) : PowerSeries k :=
  PowerSeries.mk fun n =>
    coeff (Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) (j : ℕ)) f

/-- Helper for Chap10 Example 10 119 4: the `z^j` coefficient of a target ambient power series,
viewed as a one-variable power series in `x`. -/
private def dualNumberPowerSeriesTargetCoeff (j : Fin 2) (f : B) : PowerSeries k :=
  PowerSeries.mk fun n =>
    coeff (Finsupp.single false n + Finsupp.single true (j : ℕ)) f

/-- Helper for Chap10 Example 10 119 4: source elements of `(y^2)` have zero first-order
coefficients in the `y` direction. -/
private lemma dualNumberPowerSeriesSourceCoeff_eq_zero_of_mem_squareIdeal
    (j : Fin 2) {f : A} (hf : f ∈ I) :
    dualNumberPowerSeriesSourceCoeff k j f = 0 := by
  -- Proof comment: membership in `(y^2)` is divisibility by `y^2`, so coefficients with
  -- `y`-degree `0` or `1` vanish by `X_pow_dvd_iff`.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk]
  have hdiv : y ^ 2 ∣ f := by
    rw [dualNumberPowerSeriesSquareIdeal] at hf
    exact Ideal.mem_span_singleton.mp hf
  rw [MvPowerSeries.X_pow_dvd_iff] at hdiv
  have hj : (Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) (j : ℕ)) 1 < 2 := by
    simpa using j.isLt
  exact hdiv (Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) (j : ℕ)) hj

/-- Helper for Chap10 Example 10 119 4: target elements of `(z^2)` have zero first-order
coefficients in the `z` direction. -/
private lemma dualNumberPowerSeriesTargetCoeff_eq_zero_of_mem_squareIdeal
    (j : Fin 2) {f : B} (hf : f ∈ J) :
    dualNumberPowerSeriesTargetCoeff k j f = 0 := by
  -- Proof comment: the target argument is the same divisibility-by-the-square calculation for
  -- the variable `z`.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk]
  have hdiv : z ^ 2 ∣ f := by
    rw [dualNumberPowerSeriesTargetSquareIdeal] at hf
    exact Ideal.mem_span_singleton.mp hf
  rw [MvPowerSeries.X_pow_dvd_iff] at hdiv
  have hj : (Finsupp.single false n + Finsupp.single true (j : ℕ)) true < 2 := by
    simpa using j.isLt
  exact hdiv (Finsupp.single false n + Finsupp.single true (j : ℕ)) hj

/-- Helper for Chap10 Example 10 119 4: source first-order coefficients depend only on the class
modulo `(y^2)`. -/
private lemma dualNumberPowerSeriesSourceCoeff_eq_of_sub_mem_squareIdeal
    (j : Fin 2) {a b : A} (h : a - b ∈ I) :
    dualNumberPowerSeriesSourceCoeff k j a = dualNumberPowerSeriesSourceCoeff k j b := by
  -- Proof comment: apply the previous vanishing lemma to the difference and read off each
  -- one-variable coefficient.
  have hzero :
      dualNumberPowerSeriesSourceCoeff k j (a - b) = 0 :=
    dualNumberPowerSeriesSourceCoeff_eq_zero_of_mem_squareIdeal k j h
  apply PowerSeries.ext
  intro n
  have hcoeff := congrArg (PowerSeries.coeff n) hzero
  rw [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk] at hcoeff
  rw [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk]
  exact sub_eq_zero.mp hcoeff

/-- Helper for Chap10 Example 10 119 4: target first-order coefficients depend only on the class
modulo `(z^2)`. -/
private lemma dualNumberPowerSeriesTargetCoeff_eq_of_sub_mem_squareIdeal
    (j : Fin 2) {a b : B} (h : a - b ∈ J) :
    dualNumberPowerSeriesTargetCoeff k j a = dualNumberPowerSeriesTargetCoeff k j b := by
  -- Proof comment: the coefficient of the difference vanishes in every `x`-degree, so the two
  -- target coefficient series agree.
  have hzero :
      dualNumberPowerSeriesTargetCoeff k j (a - b) = 0 :=
    dualNumberPowerSeriesTargetCoeff_eq_zero_of_mem_squareIdeal k j h
  apply PowerSeries.ext
  intro n
  have hcoeff := congrArg (PowerSeries.coeff n) hzero
  rw [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk] at hcoeff
  rw [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk]
  exact sub_eq_zero.mp hcoeff

/-- Helper for Chap10 Example 10 119 4: the source first-order coefficient projection on the
quotient `k[[x,y]]/(y^2)`. -/
private def dualNumberPowerSeriesSourceQuotCoeff (j : Fin 2) : R → PowerSeries k :=
  Quotient.lift (fun f : A => dualNumberPowerSeriesSourceCoeff k j f)
    (fun _ _ h =>
      dualNumberPowerSeriesSourceCoeff_eq_of_sub_mem_squareIdeal k j
        (Ideal.Quotient.eq.mp (Quotient.sound h)))

/-- Helper for Chap10 Example 10 119 4: the target first-order coefficient projection on the
quotient `k[[x,z]]/(z^2)`. -/
private def dualNumberPowerSeriesTargetQuotCoeff (j : Fin 2) : S → PowerSeries k :=
  Quotient.lift (fun f : B => dualNumberPowerSeriesTargetCoeff k j f)
    (fun _ _ h =>
      dualNumberPowerSeriesTargetCoeff_eq_of_sub_mem_squareIdeal k j
        (Ideal.Quotient.eq.mp (Quotient.sound h)))

/-- Helper for Chap10 Example 10 119 4: source quotient first-order coefficients preserve
addition. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_add
    (j : Fin 2) (r s : R) :
    dualNumberPowerSeriesSourceQuotCoeff k j (r + s) =
      dualNumberPowerSeriesSourceQuotCoeff k j r +
        dualNumberPowerSeriesSourceQuotCoeff k j s := by
  -- Proof comment: choose ambient representatives; the coefficient projection is defined
  -- coefficientwise, so addition reduces to addition of one-variable coefficients.
  refine Quotient.inductionOn₂' r s ?_
  intro a b
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (dualNumberPowerSeriesSourceCoeff k j (a + b)) =
    PowerSeries.coeff n (dualNumberPowerSeriesSourceCoeff k j a) +
      PowerSeries.coeff n (dualNumberPowerSeriesSourceCoeff k j b)
  simp [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk]

/-- Helper for Chap10 Example 10 119 4: target quotient first-order coefficients preserve
addition. -/
private lemma dualNumberPowerSeriesTargetQuotCoeff_add
    (j : Fin 2) (r s : S) :
    dualNumberPowerSeriesTargetQuotCoeff k j (r + s) =
      dualNumberPowerSeriesTargetQuotCoeff k j r +
        dualNumberPowerSeriesTargetQuotCoeff k j s := by
  -- Proof comment: target quotient representatives reduce the statement to coefficientwise
  -- additivity in the ambient two-variable power-series ring.
  refine Quotient.inductionOn₂' r s ?_
  intro a b
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (dualNumberPowerSeriesTargetCoeff k j (a + b)) =
    PowerSeries.coeff n (dualNumberPowerSeriesTargetCoeff k j a) +
      PowerSeries.coeff n (dualNumberPowerSeriesTargetCoeff k j b)
  simp [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk]

/-- Helper for Chap10 Example 10 119 4: embed a one-variable power series as the `y`-constant
part of the source ambient ring. -/
private def dualNumberPowerSeriesSourceBase (p : PowerSeries k) : A :=
  fun d => if d (1 : Fin 2) = 0 then PowerSeries.coeff (d (0 : Fin 2)) p else 0

/-- Helper for Chap10 Example 10 119 4: embed a one-variable power series as the `z`-constant
part of the target ambient ring. -/
private def dualNumberPowerSeriesTargetBase (p : PowerSeries k) : B :=
  fun d => if d true = 0 then PowerSeries.coeff (d false) p else 0

/-- Helper for Chap10 Example 10 119 4: the one-variable source base embedding as a rename
algebra hom. -/
private def dualNumberPowerSeriesSourceBaseAlgHom : PowerSeries k →ₐ[k] A :=
  MvPowerSeries.rename (fun _ : Unit => (0 : Fin 2))

/-- Helper for Chap10 Example 10 119 4: the one-variable target base embedding as a rename
algebra hom. -/
private def dualNumberPowerSeriesTargetBaseAlgHom : PowerSeries k →ₐ[k] B :=
  MvPowerSeries.rename (fun _ : Unit => false)

/-- Helper for Chap10 Example 10 119 4: the source rename sends the unique variable to `x`. -/
private lemma dualNumberPowerSeries_unitToFinZero_injective :
    Function.Injective (fun _ : Unit => (0 : Fin 2)) := by
  -- The source map has a singleton domain, so equal images force equal inputs.
  intro a b _
  exact Subsingleton.elim a b

/-- Helper for Chap10 Example 10 119 4: the `y` index is not in the image of the source rename. -/
private lemma dualNumberPowerSeries_finOne_not_mem_unitToFinZero_range :
    (1 : Fin 2) ∉ Set.range (fun _ : Unit => (0 : Fin 2)) := by
  -- The source rename hits only the `x` coordinate.
  rintro ⟨u, hu⟩
  norm_num at hu

/-- Helper for Chap10 Example 10 119 4: the target rename sends the unique variable
injectively to `x`. -/
private lemma dualNumberPowerSeries_unitToBoolFalse_injective :
    Function.Injective (fun _ : Unit => false) := by
  -- The target map also has singleton domain.
  intro a b _
  exact Subsingleton.elim a b

/-- Helper for Chap10 Example 10 119 4: the `z` index is not in the image of the target rename. -/
private lemma dualNumberPowerSeries_true_not_mem_unitToBoolFalse_range :
    true ∉ Set.range (fun _ : Unit => false) := by
  -- The target rename hits only the `x` coordinate.
  rintro ⟨u, hu⟩
  cases hu

/-- Helper for Chap10 Example 10 119 4: coefficient formula for a source base series in
`y`-degree zero. -/
private lemma dualNumberPowerSeriesSourceBase_coeff_of_yDegree_eq_zero
    (p : PowerSeries k) {d : Fin 2 →₀ ℕ} (h : d (1 : Fin 2) = 0) :
    coeff d (dualNumberPowerSeriesSourceBase k p) = PowerSeries.coeff (d 0) p := by
  -- Proof comment: the base embedding is defined coefficientwise, so the zero-degree branch is
  -- immediate.
  rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesSourceBase]
  simp [h]

/-- Helper for Chap10 Example 10 119 4: coefficient formula for a source base series away from
`y`-degree zero. -/
private lemma dualNumberPowerSeriesSourceBase_coeff_of_yDegree_ne_zero
    (p : PowerSeries k) {d : Fin 2 →₀ ℕ} (h : d (1 : Fin 2) ≠ 0) :
    coeff d (dualNumberPowerSeriesSourceBase k p) = 0 := by
  -- Proof comment: nonzero `y`-degree lands in the zero branch of the source base embedding.
  rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesSourceBase]
  simp [h]

/-- Helper for Chap10 Example 10 119 4: multiplying a source base series by `y` has no
`y`-degree zero part. -/
private lemma dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_zero
    (p : PowerSeries k) {d : Fin 2 →₀ ℕ} (h : d (1 : Fin 2) = 0) :
    coeff d (dualNumberPowerSeriesSourceBase k p * y) = 0 := by
  -- Proof comment: the monomial `y` cannot divide a monomial with `y`-degree zero.
  rw [X, coeff_mul_monomial]
  rw [if_neg]
  intro hle
  have : (1 : ℕ) ≤ 0 := by
    simpa [h] using hle (1 : Fin 2)
  omega

/-- Helper for Chap10 Example 10 119 4: the `y`-degree one part of `p*y` is the source base
series `p`. -/
private lemma dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_one
    (p : PowerSeries k) {d : Fin 2 →₀ ℕ} (h : d (1 : Fin 2) = 1) :
    coeff d (dualNumberPowerSeriesSourceBase k p * y) = PowerSeries.coeff (d 0) p := by
  -- Proof comment: rewrite the exponent vector as its `x` part plus one copy of `y`, then use
  -- the monomial multiplication coefficient formula.
  have hd : Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single (1 : Fin 2) 1 = d := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp
    · simp [h]
  rw [← hd, X, coeff_add_mul_monomial, mul_one]
  have hzero : (Finsupp.single (0 : Fin 2) (d 0)) (1 : Fin 2) = 0 := by
    simp
  rw [dualNumberPowerSeriesSourceBase_coeff_of_yDegree_eq_zero (k := k) p hzero]
  simp

/-- Helper for Chap10 Example 10 119 4: a source coefficient series recovers the matching ambient
coefficient. -/
private lemma dualNumberPowerSeriesSourceCoeff_coeff_self
    (j : Fin 2) (f : A) {d : Fin 2 →₀ ℕ} (h : d (1 : Fin 2) = (j : ℕ)) :
    PowerSeries.coeff (d 0) (dualNumberPowerSeriesSourceCoeff k j f) = coeff d f := by
  -- Proof comment: the chosen `x`-degree and `y`-degree reconstruct the original two-variable
  -- exponent vector.
  rw [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk]
  have hd : Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single (1 : Fin 2) (j : ℕ) = d := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp
    · simp [h]
  rw [hd]

/-- Helper for Chap10 Example 10 119 4: the coefficient-defined source base embedding is the
canonical rename of the one-variable power-series ring. -/
private lemma dualNumberPowerSeriesSourceBase_eq_algHom
    (p : PowerSeries k) :
    dualNumberPowerSeriesSourceBase k p =
      dualNumberPowerSeriesSourceBaseAlgHom k p := by
  -- Compare coefficients. The rename has a singleton preimage exactly in `y`-degree zero.
  ext d
  by_cases hy : d (1 : Fin 2) = 0
  · rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesSourceBase, if_pos hy]
    rw [dualNumberPowerSeriesSourceBaseAlgHom, MvPowerSeries.coeff_rename]
    refine (Finset.sum_eq_single (Finsupp.single () (d 0)) ?_ ?_).symm
    · intro b hb hne
      simp only [Fin.isValue, Set.Finite.mem_toFinset, Set.mem_preimage,
        Set.mem_singleton_iff] at hb
      have hmap0 :
          (Finsupp.mapDomain (fun _ : Unit => (0 : Fin 2)) b) (0 : Fin 2) = b () :=
        Finsupp.mapDomain_apply dualNumberPowerSeries_unitToFinZero_injective b ()
      have h0 : b () = d 0 :=
        hmap0.symm.trans (congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) hb)
      have hval : b = Finsupp.single () (d 0) := by
        apply Finsupp.unique_ext
        simpa using h0
      exact (hne hval).elim
    · intro hnot
      exfalso
      apply hnot
      simp only [Fin.isValue, Set.Finite.mem_toFinset, Set.mem_preimage,
        Finsupp.mapDomain_single, Set.mem_singleton_iff]
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [hy]
  · rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesSourceBase, if_neg hy]
    rw [dualNumberPowerSeriesSourceBaseAlgHom, MvPowerSeries.coeff_rename]
    symm
    refine Finset.sum_eq_zero ?_
    intro b hb
    simp only [Fin.isValue, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff] at hb
    have hmapzero :
        (Finsupp.mapDomain (fun _ : Unit => (0 : Fin 2)) b) (1 : Fin 2) = 0 :=
      Finsupp.mapDomain_notin_range b (1 : Fin 2)
        dualNumberPowerSeries_finOne_not_mem_unitToFinZero_range
    have hzero : d (1 : Fin 2) = 0 :=
      (congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) hb).symm.trans hmapzero
    exact (hy hzero).elim

/-- Helper for Chap10 Example 10 119 4: source base series multiply as one-variable power
series. -/
private lemma dualNumberPowerSeriesSourceBase_mul
    (p q : PowerSeries k) :
    dualNumberPowerSeriesSourceBase k (p * q) =
      dualNumberPowerSeriesSourceBase k p * dualNumberPowerSeriesSourceBase k q := by
  -- Move to the rename algebra hom, where multiplicativity is built in.
  rw [dualNumberPowerSeriesSourceBase_eq_algHom,
    dualNumberPowerSeriesSourceBase_eq_algHom,
    dualNumberPowerSeriesSourceBase_eq_algHom]
  exact map_mul (dualNumberPowerSeriesSourceBaseAlgHom k) p q

/-- Helper for Chap10 Example 10 119 4: source base series add as one-variable power series. -/
private lemma dualNumberPowerSeriesSourceBase_add
    (p q : PowerSeries k) :
    dualNumberPowerSeriesSourceBase k (p + q) =
      dualNumberPowerSeriesSourceBase k p + dualNumberPowerSeriesSourceBase k q := by
  -- Additivity is also inherited from the rename algebra hom.
  rw [dualNumberPowerSeriesSourceBase_eq_algHom,
    dualNumberPowerSeriesSourceBase_eq_algHom,
    dualNumberPowerSeriesSourceBase_eq_algHom]
  exact map_add (dualNumberPowerSeriesSourceBaseAlgHom k) p q

/-- Helper for Chap10 Example 10 119 4: the source base embedding sends `0` to `0`. -/
private lemma dualNumberPowerSeriesSourceBase_zero :
    dualNumberPowerSeriesSourceBase k 0 = 0 := by
  -- This is the zero-preservation law for the rename algebra hom.
  rw [dualNumberPowerSeriesSourceBase_eq_algHom]
  exact map_zero (dualNumberPowerSeriesSourceBaseAlgHom k)

/-- Helper for Chap10 Example 10 119 4: the source base embedding sends `1` to `1`. -/
private lemma dualNumberPowerSeriesSourceBase_one :
    dualNumberPowerSeriesSourceBase k 1 = 1 := by
  -- This is the one-preservation law for the rename algebra hom.
  rw [dualNumberPowerSeriesSourceBase_eq_algHom]
  exact map_one (dualNumberPowerSeriesSourceBaseAlgHom k)

/-- Helper for Chap10 Example 10 119 4: every source ambient series is congruent modulo `(y^2)`
to its constant and linear `y` terms. -/
private lemma dualNumberPowerSeriesSource_reconstruction_sub_mem_squareIdeal (f : A) :
    f -
        (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 0 f) +
          dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 1 f) * y) ∈ I := by
  -- Proof comment: membership in `(y^2)` is checked by showing all coefficients of `y`-degree
  -- below `2` vanish after subtracting the first-order truncation.
  rw [dualNumberPowerSeriesSquareIdeal]
  apply Ideal.mem_span_singleton.mpr
  rw [MvPowerSeries.X_pow_dvd_iff]
  intro d hd
  rw [map_sub, map_add]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h0 | h1
  · have hy : d (1 : Fin 2) = 0 := by omega
    have hbase :
        coeff d (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 0 f)) =
          PowerSeries.coeff (d 0) (dualNumberPowerSeriesSourceCoeff k 0 f) :=
      dualNumberPowerSeriesSourceBase_coeff_of_yDegree_eq_zero k
        (dualNumberPowerSeriesSourceCoeff k 0 f) hy
    have hmul :
        coeff d (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 1 f) * y) =
          0 :=
      dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_zero k
        (dualNumberPowerSeriesSourceCoeff k 1 f) hy
    have hcoeff :
        PowerSeries.coeff (d 0) (dualNumberPowerSeriesSourceCoeff k 0 f) = coeff d f :=
      dualNumberPowerSeriesSourceCoeff_coeff_self k 0 f hy
    rw [hbase, hmul, hcoeff]
    simp
  · have hy : d (1 : Fin 2) = 1 := h1
    have hy_ne : d (1 : Fin 2) ≠ 0 := by omega
    have hbase :
        coeff d (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 0 f)) =
          0 :=
      dualNumberPowerSeriesSourceBase_coeff_of_yDegree_ne_zero k
        (dualNumberPowerSeriesSourceCoeff k 0 f) hy_ne
    have hmul :
        coeff d (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceCoeff k 1 f) * y) =
          PowerSeries.coeff (d 0) (dualNumberPowerSeriesSourceCoeff k 1 f) :=
      dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_one k
        (dualNumberPowerSeriesSourceCoeff k 1 f) hy
    have hcoeff :
        PowerSeries.coeff (d 0) (dualNumberPowerSeriesSourceCoeff k 1 f) = coeff d f :=
      dualNumberPowerSeriesSourceCoeff_coeff_self k 1 f hy
    rw [hbase, hmul, hcoeff]
    simp

/-- Helper for Chap10 Example 10 119 4: every source quotient element is represented by its
first-order normal form. -/
private lemma dualNumberPowerSeriesSource_quotient_reconstruction (r : R) :
    r =
      Ideal.Quotient.mk I
        (dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceQuotCoeff k 0 r) +
          dualNumberPowerSeriesSourceBase k (dualNumberPowerSeriesSourceQuotCoeff k 1 r) * y) := by
  -- Proof comment: choose an ambient representative and apply the congruence modulo `(y^2)`.
  refine Quotient.inductionOn r ?_
  intro f
  have hrec := dualNumberPowerSeriesSource_reconstruction_sub_mem_squareIdeal k f
  simpa [dualNumberPowerSeriesSourceQuotCoeff] using (Ideal.Quotient.eq.mpr hrec)

/-- Helper for Chap10 Example 10 119 4: coefficient formula for a target base series in
`z`-degree zero. -/
private lemma dualNumberPowerSeriesTargetBase_coeff_of_zDegree_eq_zero
    (p : PowerSeries k) {d : Bool →₀ ℕ} (h : d true = 0) :
    coeff d (dualNumberPowerSeriesTargetBase k p) = PowerSeries.coeff (d false) p := by
  -- Proof comment: the target base embedding is also coefficientwise.
  rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesTargetBase]
  simp [h]

/-- Helper for Chap10 Example 10 119 4: coefficient formula for a target base series away from
`z`-degree zero. -/
private lemma dualNumberPowerSeriesTargetBase_coeff_of_zDegree_ne_zero
    (p : PowerSeries k) {d : Bool →₀ ℕ} (h : d true ≠ 0) :
    coeff d (dualNumberPowerSeriesTargetBase k p) = 0 := by
  -- Proof comment: nonzero `z`-degree lands in the zero branch of the target base embedding.
  rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesTargetBase]
  simp [h]

/-- Helper for Chap10 Example 10 119 4: multiplying a target base series by `z` has no
`z`-degree zero part. -/
private lemma dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_zero
    (p : PowerSeries k) {d : Bool →₀ ℕ} (h : d true = 0) :
    coeff d (dualNumberPowerSeriesTargetBase k p * z) = 0 := by
  -- Proof comment: the monomial `z` cannot divide a monomial with `z`-degree zero.
  rw [X, coeff_mul_monomial]
  rw [if_neg]
  intro hle
  have : (1 : ℕ) ≤ 0 := by
    simpa [h] using hle true
  omega

/-- Helper for Chap10 Example 10 119 4: the `z`-degree one part of `p*z` is the target base
series `p`. -/
private lemma dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_one
    (p : PowerSeries k) {d : Bool →₀ ℕ} (h : d true = 1) :
    coeff d (dualNumberPowerSeriesTargetBase k p * z) = PowerSeries.coeff (d false) p := by
  -- Proof comment: split the exponent into its `x` part plus one copy of `z`.
  have hd : Finsupp.single false (d false) + Finsupp.single true 1 = d := by
    apply Finsupp.ext
    intro i
    cases i
    · simp
    · simp [h]
  rw [← hd, X, coeff_add_mul_monomial, mul_one]
  have hzero : (Finsupp.single false (d false)) true = 0 := by
    simp
  rw [dualNumberPowerSeriesTargetBase_coeff_of_zDegree_eq_zero (k := k) p hzero]
  simp

/-- Helper for Chap10 Example 10 119 4: a target coefficient series recovers the matching ambient
coefficient. -/
private lemma dualNumberPowerSeriesTargetCoeff_coeff_self
    (j : Fin 2) (f : B) {d : Bool →₀ ℕ} (h : d true = (j : ℕ)) :
    PowerSeries.coeff (d false) (dualNumberPowerSeriesTargetCoeff k j f) = coeff d f := by
  -- Proof comment: the selected `x`-degree and `z`-degree reconstruct the target exponent vector.
  rw [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk]
  have hd : Finsupp.single false (d false) + Finsupp.single true (j : ℕ) = d := by
    apply Finsupp.ext
    intro i
    cases i
    · simp
    · simp [h]
  rw [hd]

/-- Helper for Chap10 Example 10 119 4: the coefficient-defined target base embedding is the
canonical rename of the one-variable power-series ring. -/
private lemma dualNumberPowerSeriesTargetBase_eq_algHom
    (p : PowerSeries k) :
    dualNumberPowerSeriesTargetBase k p =
      dualNumberPowerSeriesTargetBaseAlgHom k p := by
  -- Compare coefficients; only the `z`-degree-zero exponent has a preimage under the rename.
  ext d
  by_cases hz : d true = 0
  · rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesTargetBase, if_pos hz]
    rw [dualNumberPowerSeriesTargetBaseAlgHom, MvPowerSeries.coeff_rename]
    refine (Finset.sum_eq_single (Finsupp.single () (d false)) ?_ ?_).symm
    · intro b hb hne
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hb
      have hmapFalse :
          (Finsupp.mapDomain (fun _ : Unit => false) b) false = b () :=
        Finsupp.mapDomain_apply dualNumberPowerSeries_unitToBoolFalse_injective b ()
      have hfalse : b () = d false :=
        hmapFalse.symm.trans (congrArg (fun e : Bool →₀ ℕ => e false) hb)
      have hval : b = Finsupp.single () (d false) := by
        apply Finsupp.unique_ext
        simpa using hfalse
      exact (hne hval).elim
    · intro hnot
      exfalso
      apply hnot
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finsupp.mapDomain_single,
        Set.mem_singleton_iff]
      apply Finsupp.ext
      intro i
      cases i <;> simp [hz]
  · rw [MvPowerSeries.coeff_apply, dualNumberPowerSeriesTargetBase, if_neg hz]
    rw [dualNumberPowerSeriesTargetBaseAlgHom, MvPowerSeries.coeff_rename]
    symm
    refine Finset.sum_eq_zero ?_
    intro b hb
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hb
    have hmapzero :
        (Finsupp.mapDomain (fun _ : Unit => false) b) true = 0 :=
      Finsupp.mapDomain_notin_range b true
        dualNumberPowerSeries_true_not_mem_unitToBoolFalse_range
    have hzero : d true = 0 :=
      (congrArg (fun e : Bool →₀ ℕ => e true) hb).symm.trans hmapzero
    exact (hz hzero).elim

/-- Helper for Chap10 Example 10 119 4: target base series multiply as one-variable power
series. -/
private lemma dualNumberPowerSeriesTargetBase_mul
    (p q : PowerSeries k) :
    dualNumberPowerSeriesTargetBase k (p * q) =
      dualNumberPowerSeriesTargetBase k p * dualNumberPowerSeriesTargetBase k q := by
  -- The target calculation is again just multiplicativity of the rename algebra hom.
  rw [dualNumberPowerSeriesTargetBase_eq_algHom,
    dualNumberPowerSeriesTargetBase_eq_algHom,
    dualNumberPowerSeriesTargetBase_eq_algHom]
  exact map_mul (dualNumberPowerSeriesTargetBaseAlgHom k) p q

/-- Helper for Chap10 Example 10 119 4: target base series add as one-variable power series. -/
private lemma dualNumberPowerSeriesTargetBase_add
    (p q : PowerSeries k) :
    dualNumberPowerSeriesTargetBase k (p + q) =
      dualNumberPowerSeriesTargetBase k p + dualNumberPowerSeriesTargetBase k q := by
  -- Additivity is inherited from the target rename algebra hom.
  rw [dualNumberPowerSeriesTargetBase_eq_algHom,
    dualNumberPowerSeriesTargetBase_eq_algHom,
    dualNumberPowerSeriesTargetBase_eq_algHom]
  exact map_add (dualNumberPowerSeriesTargetBaseAlgHom k) p q

/-- Helper for Chap10 Example 10 119 4: every target ambient series is congruent modulo `(z^2)`
to its constant and linear `z` terms. -/
private lemma dualNumberPowerSeriesTarget_reconstruction_sub_mem_squareIdeal (f : B) :
    f -
        (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 0 f) +
          dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 1 f) * z) ∈ J := by
  -- Proof comment: as in the source, the first-order truncation matches exactly in `z`-degrees
  -- `0` and `1`.
  rw [dualNumberPowerSeriesTargetSquareIdeal]
  apply Ideal.mem_span_singleton.mpr
  rw [MvPowerSeries.X_pow_dvd_iff]
  intro d hd
  rw [map_sub, map_add]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h0 | h1
  · have hz : d true = 0 := by omega
    have hbase :
        coeff d (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 0 f)) =
          PowerSeries.coeff (d false) (dualNumberPowerSeriesTargetCoeff k 0 f) :=
      dualNumberPowerSeriesTargetBase_coeff_of_zDegree_eq_zero k
        (dualNumberPowerSeriesTargetCoeff k 0 f) hz
    have hmul :
        coeff d (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 1 f) * z) =
          0 :=
      dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_zero k
        (dualNumberPowerSeriesTargetCoeff k 1 f) hz
    have hcoeff :
        PowerSeries.coeff (d false) (dualNumberPowerSeriesTargetCoeff k 0 f) = coeff d f :=
      dualNumberPowerSeriesTargetCoeff_coeff_self k 0 f hz
    rw [hbase, hmul, hcoeff]
    simp
  · have hz : d true = 1 := h1
    have hz_ne : d true ≠ 0 := by omega
    have hbase :
        coeff d (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 0 f)) =
          0 :=
      dualNumberPowerSeriesTargetBase_coeff_of_zDegree_ne_zero k
        (dualNumberPowerSeriesTargetCoeff k 0 f) hz_ne
    have hmul :
        coeff d (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetCoeff k 1 f) * z) =
          PowerSeries.coeff (d false) (dualNumberPowerSeriesTargetCoeff k 1 f) :=
      dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_one k
        (dualNumberPowerSeriesTargetCoeff k 1 f) hz
    have hcoeff :
        PowerSeries.coeff (d false) (dualNumberPowerSeriesTargetCoeff k 1 f) = coeff d f :=
      dualNumberPowerSeriesTargetCoeff_coeff_self k 1 f hz
    rw [hbase, hmul, hcoeff]
    simp

/-- Helper for Chap10 Example 10 119 4: every target quotient element is represented by its
first-order normal form. -/
private lemma dualNumberPowerSeriesTarget_quotient_reconstruction (s : S) :
    s =
      Ideal.Quotient.mk J
        (dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetQuotCoeff k 0 s) +
          dualNumberPowerSeriesTargetBase k (dualNumberPowerSeriesTargetQuotCoeff k 1 s) * z) := by
  -- Proof comment: choose an ambient representative and apply the congruence modulo `(z^2)`.
  refine Quotient.inductionOn s ?_
  intro f
  have hrec := dualNumberPowerSeriesTarget_reconstruction_sub_mem_squareIdeal k f
  simpa [dualNumberPowerSeriesTargetQuotCoeff] using (Ideal.Quotient.eq.mpr hrec)

/-- Helper for Chap10 Example 10 119 4: the source normal form with constant coefficient `p`
and linear `y`-coefficient `q`. -/
private def dualNumberPowerSeriesSourceNormal (p q : PowerSeries k) : R :=
  Ideal.Quotient.mk I
    (dualNumberPowerSeriesSourceBase k p + dualNumberPowerSeriesSourceBase k q * y)

/-- Helper for Chap10 Example 10 119 4: the target normal form with constant coefficient `p`
and linear `z`-coefficient `q`. -/
private def dualNumberPowerSeriesTargetNormal (p q : PowerSeries k) : S :=
  Ideal.Quotient.mk J
    (dualNumberPowerSeriesTargetBase k p + dualNumberPowerSeriesTargetBase k q * z)

/-- Helper for Chap10 Example 10 119 4: every source quotient element is its source normal form. -/
private lemma dualNumberPowerSeriesSource_quotient_reconstruction_normal (r : R) :
    r =
      dualNumberPowerSeriesSourceNormal k
        (dualNumberPowerSeriesSourceQuotCoeff k 0 r)
        (dualNumberPowerSeriesSourceQuotCoeff k 1 r) := by
  -- Proof comment: this repackages the established quotient reconstruction through the named
  -- source normal constructor.
  simpa [dualNumberPowerSeriesSourceNormal] using
    dualNumberPowerSeriesSource_quotient_reconstruction k r

/-- Helper for Chap10 Example 10 119 4: every target quotient element is its target normal form. -/
private lemma dualNumberPowerSeriesTarget_quotient_reconstruction_normal (s : S) :
    s =
      dualNumberPowerSeriesTargetNormal k
        (dualNumberPowerSeriesTargetQuotCoeff k 0 s)
        (dualNumberPowerSeriesTargetQuotCoeff k 1 s) := by
  -- Proof comment: this repackages the established quotient reconstruction through the named
  -- target normal constructor.
  simpa [dualNumberPowerSeriesTargetNormal] using
    dualNumberPowerSeriesTarget_quotient_reconstruction k s

/-- Helper for Chap10 Example 10 119 4: the constant coefficient of a source normal form. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero
    (p q : PowerSeries k) :
    dualNumberPowerSeriesSourceQuotCoeff k 0
      (dualNumberPowerSeriesSourceNormal k p q) = p := by
  -- Proof comment: compare one-variable coefficients after unfolding the quotient coefficient
  -- map on the chosen ambient representative.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesSourceNormal]
  change (PowerSeries.coeff n)
      (dualNumberPowerSeriesSourceCoeff k 0
        (dualNumberPowerSeriesSourceBase k p + dualNumberPowerSeriesSourceBase k q * y)) =
    (PowerSeries.coeff n) p
  simp [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesSourceBase_coeff_of_yDegree_eq_zero,
    dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_zero]

/-- Helper for Chap10 Example 10 119 4: the linear `y` coefficient of a source normal form. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one
    (p q : PowerSeries k) :
    dualNumberPowerSeriesSourceQuotCoeff k 1
      (dualNumberPowerSeriesSourceNormal k p q) = q := by
  -- Proof comment: in `y`-degree one, the base part vanishes and the `q*y` part contributes
  -- exactly `q`.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesSourceNormal]
  change (PowerSeries.coeff n)
      (dualNumberPowerSeriesSourceCoeff k 1
        (dualNumberPowerSeriesSourceBase k p + dualNumberPowerSeriesSourceBase k q * y)) =
    (PowerSeries.coeff n) q
  simp [dualNumberPowerSeriesSourceCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesSourceBase_coeff_of_yDegree_ne_zero,
    dualNumberPowerSeriesSourceBase_mul_y_coeff_of_yDegree_eq_one]

/-- Helper for Chap10 Example 10 119 4: the source normal form with both coordinates zero is
zero. -/
private lemma dualNumberPowerSeriesSourceNormal_zero_zero :
    dualNumberPowerSeriesSourceNormal k 0 0 = 0 := by
  -- Unfold the chosen representative and use that the base embedding preserves zero.
  rw [dualNumberPowerSeriesSourceNormal, dualNumberPowerSeriesSourceBase_zero]
  simp

/-- Helper for Chap10 Example 10 119 4: the source normal form `(1,0)` is the unit. -/
private lemma dualNumberPowerSeriesSourceNormal_one_zero :
    dualNumberPowerSeriesSourceNormal k 1 0 = 1 := by
  -- The representative is `1 + 0*y`, hence the quotient class is the unit.
  rw [dualNumberPowerSeriesSourceNormal, dualNumberPowerSeriesSourceBase_one,
    dualNumberPowerSeriesSourceBase_zero]
  simp

/-- Helper for Chap10 Example 10 119 4: source normal forms are determined by their coordinates. -/
private lemma dualNumberPowerSeriesSourceNormal_ext
    {r s : R}
    (h0 : dualNumberPowerSeriesSourceQuotCoeff k 0 r =
      dualNumberPowerSeriesSourceQuotCoeff k 0 s)
    (h1 : dualNumberPowerSeriesSourceQuotCoeff k 1 r =
      dualNumberPowerSeriesSourceQuotCoeff k 1 s) :
    r = s := by
  -- Proof comment: reconstruct both classes in source normal form and rewrite the two coordinates.
  rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesSource_quotient_reconstruction_normal k s, h0, h1]

/-- Helper for Chap10 Example 10 119 4: the constant coefficient of a target normal form. -/
private lemma dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero
    (p q : PowerSeries k) :
    dualNumberPowerSeriesTargetQuotCoeff k 0
      (dualNumberPowerSeriesTargetNormal k p q) = p := by
  -- Proof comment: the target proof is the same coefficient computation in `z`-degree zero.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesTargetNormal]
  change (PowerSeries.coeff n)
      (dualNumberPowerSeriesTargetCoeff k 0
        (dualNumberPowerSeriesTargetBase k p + dualNumberPowerSeriesTargetBase k q * z)) =
    (PowerSeries.coeff n) p
  simp [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesTargetBase_coeff_of_zDegree_eq_zero,
    dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_zero]

/-- Helper for Chap10 Example 10 119 4: the linear `z` coefficient of a target normal form. -/
private lemma dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one
    (p q : PowerSeries k) :
    dualNumberPowerSeriesTargetQuotCoeff k 1
      (dualNumberPowerSeriesTargetNormal k p q) = q := by
  -- Proof comment: in `z`-degree one, only the linear term of the target normal form remains.
  apply PowerSeries.ext
  intro n
  rw [dualNumberPowerSeriesTargetNormal]
  change (PowerSeries.coeff n)
      (dualNumberPowerSeriesTargetCoeff k 1
        (dualNumberPowerSeriesTargetBase k p + dualNumberPowerSeriesTargetBase k q * z)) =
    (PowerSeries.coeff n) q
  simp [dualNumberPowerSeriesTargetCoeff, PowerSeries.coeff_mk,
    dualNumberPowerSeriesTargetBase_coeff_of_zDegree_ne_zero,
    dualNumberPowerSeriesTargetBase_mul_z_coeff_of_zDegree_eq_one]

/-- Helper for Chap10 Example 10 119 4: target normal forms are determined by their coordinates. -/
private lemma dualNumberPowerSeriesTargetNormal_ext
    {r s : S}
    (h0 : dualNumberPowerSeriesTargetQuotCoeff k 0 r =
      dualNumberPowerSeriesTargetQuotCoeff k 0 s)
    (h1 : dualNumberPowerSeriesTargetQuotCoeff k 1 r =
      dualNumberPowerSeriesTargetQuotCoeff k 1 s) :
    r = s := by
  -- Proof comment: reconstruct both classes in target normal form and rewrite the two coordinates.
  rw [dualNumberPowerSeriesTarget_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s, h0, h1]

/-- Helper for Chap10 Example 10 119 4: source normal forms multiply by the square-zero
dual-number rule. -/
private lemma dualNumberPowerSeriesSourceNormal_mul
    (p q r s : PowerSeries k) :
    dualNumberPowerSeriesSourceNormal k (p * r) (p * s + q * r) =
      dualNumberPowerSeriesSourceNormal k p q *
        dualNumberPowerSeriesSourceNormal k r s := by
  -- Work with chosen ambient representatives; the only discarded term is
  -- `(q*s) y^2`, which lies in the presentation ideal.
  rw [dualNumberPowerSeriesSourceNormal]
  apply Ideal.Quotient.eq.mpr
  rw [dualNumberPowerSeriesSquareIdeal, Ideal.mem_span_singleton']
  refine ⟨-dualNumberPowerSeriesSourceBase k (q * s), ?_⟩
  rw [dualNumberPowerSeriesSourceBase_add, dualNumberPowerSeriesSourceBase_mul,
    dualNumberPowerSeriesSourceBase_mul, dualNumberPowerSeriesSourceBase_mul,
    dualNumberPowerSeriesSourceBase_mul]
  ring

/-- Helper for Chap10 Example 10 119 4: target normal forms multiply by the square-zero
dual-number rule. -/
private lemma dualNumberPowerSeriesTargetNormal_mul
    (p q r s : PowerSeries k) :
    dualNumberPowerSeriesTargetNormal k (p * r) (p * s + q * r) =
      dualNumberPowerSeriesTargetNormal k p q *
        dualNumberPowerSeriesTargetNormal k r s := by
  -- The target quotient has the same multiplication rule, now discarding `(q*s) z^2`.
  rw [dualNumberPowerSeriesTargetNormal]
  apply Ideal.Quotient.eq.mpr
  rw [dualNumberPowerSeriesTargetSquareIdeal, Ideal.mem_span_singleton']
  refine ⟨-dualNumberPowerSeriesTargetBase k (q * s), ?_⟩
  rw [dualNumberPowerSeriesTargetBase_add, dualNumberPowerSeriesTargetBase_mul,
    dualNumberPowerSeriesTargetBase_mul, dualNumberPowerSeriesTargetBase_mul,
    dualNumberPowerSeriesTargetBase_mul]
  ring

/-- Helper for Chap10 Example 10 119 4: the source constant coordinate is multiplicative. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_mul_zero
    (r s : R) :
    dualNumberPowerSeriesSourceQuotCoeff k 0 (r * s) =
      dualNumberPowerSeriesSourceQuotCoeff k 0 r *
        dualNumberPowerSeriesSourceQuotCoeff k 0 s := by
  -- Put both factors in normal form, multiply there, and project the constant coordinate.
  rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesSource_quotient_reconstruction_normal k s,
    ← dualNumberPowerSeriesSourceNormal_mul,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the source linear coordinate satisfies the product rule. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_mul_one
    (r s : R) :
    dualNumberPowerSeriesSourceQuotCoeff k 1 (r * s) =
      dualNumberPowerSeriesSourceQuotCoeff k 0 r *
          dualNumberPowerSeriesSourceQuotCoeff k 1 s +
        dualNumberPowerSeriesSourceQuotCoeff k 1 r *
          dualNumberPowerSeriesSourceQuotCoeff k 0 s := by
  -- Normal-form multiplication is exactly the dual-number product rule in the linear coordinate.
  rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesSource_quotient_reconstruction_normal k s,
    ← dualNumberPowerSeriesSourceNormal_mul,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the target constant coordinate is multiplicative. -/
private lemma dualNumberPowerSeriesTargetQuotCoeff_mul_zero
    (r s : S) :
    dualNumberPowerSeriesTargetQuotCoeff k 0 (r * s) =
      dualNumberPowerSeriesTargetQuotCoeff k 0 r *
        dualNumberPowerSeriesTargetQuotCoeff k 0 s := by
  -- The target proof is the same normal-form projection argument.
  rw [dualNumberPowerSeriesTarget_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s,
    ← dualNumberPowerSeriesTargetNormal_mul,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the target linear coordinate satisfies the product rule. -/
private lemma dualNumberPowerSeriesTargetQuotCoeff_mul_one
    (r s : S) :
    dualNumberPowerSeriesTargetQuotCoeff k 1 (r * s) =
      dualNumberPowerSeriesTargetQuotCoeff k 0 r *
          dualNumberPowerSeriesTargetQuotCoeff k 1 s +
        dualNumberPowerSeriesTargetQuotCoeff k 1 r *
          dualNumberPowerSeriesTargetQuotCoeff k 0 s := by
  -- Project the target normal-form multiplication law to the `z` coefficient.
  rw [dualNumberPowerSeriesTarget_quotient_reconstruction_normal k r,
    dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s,
    ← dualNumberPowerSeriesTargetNormal_mul,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one,
    dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the source constant-coordinate projection sends zero to
zero. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_zero_zero :
    dualNumberPowerSeriesSourceQuotCoeff k 0 (0 : R) = 0 := by
  -- Rewrite zero as its source normal form and read off the constant coordinate.
  rw [← dualNumberPowerSeriesSourceNormal_zero_zero (k := k),
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the source linear-coordinate projection sends zero to
zero. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_one_zero :
    dualNumberPowerSeriesSourceQuotCoeff k 1 (0 : R) = 0 := by
  -- Rewrite zero as its source normal form and read off the linear coordinate.
  rw [← dualNumberPowerSeriesSourceNormal_zero_zero (k := k),
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one]

/-- Helper for Chap10 Example 10 119 4: the source constant-coordinate projection sends one to
one. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_zero_one :
    dualNumberPowerSeriesSourceQuotCoeff k 0 (1 : R) = 1 := by
  -- Rewrite one as the normal form `(1,0)` and read off the constant coordinate.
  rw [← dualNumberPowerSeriesSourceNormal_one_zero (k := k),
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the source constant-coordinate map as a ring hom. -/
private def dualNumberPowerSeriesSourceConstCoeffHom : R →+* PowerSeries k where
  toFun := dualNumberPowerSeriesSourceQuotCoeff k 0
  map_zero' := dualNumberPowerSeriesSourceQuotCoeff_zero_zero k
  map_one' := dualNumberPowerSeriesSourceQuotCoeff_zero_one k
  map_add' := dualNumberPowerSeriesSourceQuotCoeff_add k 0
  map_mul' := dualNumberPowerSeriesSourceQuotCoeff_mul_zero k

/-- Helper for Chap10 Example 10 119 4: the source constant-coordinate ring hom is the zero
coordinate projection. -/
private lemma dualNumberPowerSeriesSourceConstCoeffHom_apply (r : R) :
    dualNumberPowerSeriesSourceConstCoeffHom k r =
      dualNumberPowerSeriesSourceQuotCoeff k 0 r := by
  -- This is immediate from the definition and keeps later rewrites directed.
  rfl

/-- Helper for Chap10 Example 10 119 4: the source constant-coordinate ring hom is surjective. -/
private lemma dualNumberPowerSeriesSourceConstCoeffHom_surjective :
    Function.Surjective (dualNumberPowerSeriesSourceConstCoeffHom k) := by
  -- A series `p` is hit by the source normal form with coordinates `(p,0)`.
  intro p
  refine ⟨dualNumberPowerSeriesSourceNormal k p 0, ?_⟩
  rw [dualNumberPowerSeriesSourceConstCoeffHom_apply,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]

/-- Helper for Chap10 Example 10 119 4: the kernel of the source constant-coordinate ring hom is
square-zero. -/
private lemma dualNumberPowerSeriesSourceConstCoeffHom_ker_sq :
    RingHom.ker (dualNumberPowerSeriesSourceConstCoeffHom k) *
        RingHom.ker (dualNumberPowerSeriesSourceConstCoeffHom k) =
      ⊥ := by
  -- Products of two elements with zero constant coordinate have both source coordinates zero.
  apply le_antisymm ?_ bot_le
  rw [Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha0 : dualNumberPowerSeriesSourceQuotCoeff k 0 a = 0 := by
    simpa [dualNumberPowerSeriesSourceConstCoeffHom_apply] using
      (RingHom.mem_ker.mp ha)
  have hb0 : dualNumberPowerSeriesSourceQuotCoeff k 0 b = 0 := by
    simpa [dualNumberPowerSeriesSourceConstCoeffHom_apply] using
      (RingHom.mem_ker.mp hb)
  apply dualNumberPowerSeriesSourceNormal_ext k
  · rw [dualNumberPowerSeriesSourceQuotCoeff_mul_zero, ha0, hb0,
      dualNumberPowerSeriesSourceQuotCoeff_zero_zero]
    simp
  · rw [dualNumberPowerSeriesSourceQuotCoeff_mul_one, ha0, hb0,
      dualNumberPowerSeriesSourceQuotCoeff_one_zero]
    simp

/-- Helper for Chap10 Example 10 119 4: source normal forms add coordinatewise. -/
private lemma dualNumberPowerSeriesSourceNormal_add
    (p q r s : PowerSeries k) :
    dualNumberPowerSeriesSourceNormal k (p + r) (q + s) =
      dualNumberPowerSeriesSourceNormal k p q + dualNumberPowerSeriesSourceNormal k r s := by
  -- Proof comment: compare the two source coordinates and use additivity of the quotient
  -- coefficient projections.
  apply dualNumberPowerSeriesSourceNormal_ext k
  · rw [dualNumberPowerSeriesSourceQuotCoeff_add,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero]
  · rw [dualNumberPowerSeriesSourceQuotCoeff_add,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one]

/-- Helper for Chap10 Example 10 119 4: target normal forms add coordinatewise. -/
private lemma dualNumberPowerSeriesTargetNormal_add
    (p q r s : PowerSeries k) :
    dualNumberPowerSeriesTargetNormal k (p + r) (q + s) =
      dualNumberPowerSeriesTargetNormal k p q + dualNumberPowerSeriesTargetNormal k r s := by
  -- Proof comment: the target proof mirrors the source coordinate comparison.
  apply dualNumberPowerSeriesTargetNormal_ext k
  · rw [dualNumberPowerSeriesTargetQuotCoeff_add,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero]
  · rw [dualNumberPowerSeriesTargetQuotCoeff_add,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one]

/-- Helper for Chap10 Example 10 119 4: the target base embedding sends `0` to `0`. -/
private lemma dualNumberPowerSeriesTargetBase_zero :
    dualNumberPowerSeriesTargetBase k 0 = 0 := by
  -- This is the zero-preservation law for the target rename algebra hom.
  rw [dualNumberPowerSeriesTargetBase_eq_algHom]
  exact map_zero (dualNumberPowerSeriesTargetBaseAlgHom k)

/-- Helper for Chap10 Example 10 119 4: the target base embedding sends `1` to `1`. -/
private lemma dualNumberPowerSeriesTargetBase_one :
    dualNumberPowerSeriesTargetBase k 1 = 1 := by
  -- This is the one-preservation law for the target rename algebra hom.
  rw [dualNumberPowerSeriesTargetBase_eq_algHom]
  exact map_one (dualNumberPowerSeriesTargetBaseAlgHom k)

/-- Helper for Chap10 Example 10 119 4: the target base embedding sends the one-variable
power-series variable to the target `x` variable. -/
private lemma dualNumberPowerSeriesTargetBase_X :
    dualNumberPowerSeriesTargetBase k (PowerSeries.X : PowerSeries k) = x := by
  -- The target base embedding is the rename sending the unique variable to `false`.
  rw [dualNumberPowerSeriesTargetBase_eq_algHom, dualNumberPowerSeriesTargetBaseAlgHom]
  exact @MvPowerSeries.rename_X Unit Bool k (fun _ : Unit => false) _ _ ()

/-- Helper for Chap10 Example 10 119 4: the target normal form with both coordinates zero is
zero. -/
private lemma dualNumberPowerSeriesTargetNormal_zero_zero :
    dualNumberPowerSeriesTargetNormal k 0 0 = 0 := by
  -- Unfold the chosen representative and use that the target base embedding preserves zero.
  rw [dualNumberPowerSeriesTargetNormal, dualNumberPowerSeriesTargetBase_zero]
  simp

/-- Helper for Chap10 Example 10 119 4: the target normal form `(1,0)` is the unit. -/
private lemma dualNumberPowerSeriesTargetNormal_one_zero :
    dualNumberPowerSeriesTargetNormal k 1 0 = 1 := by
  -- The representative is `1 + 0*z`, hence the quotient class is the unit.
  rw [dualNumberPowerSeriesTargetNormal, dualNumberPowerSeriesTargetBase_one,
    dualNumberPowerSeriesTargetBase_zero]
  simp

/-- Helper for Chap10 Example 10 119 4: the source normal form `(0,1)` is the class of `y`. -/
private lemma dualNumberPowerSeriesSourceNormal_zero_one :
    dualNumberPowerSeriesSourceNormal k 0 1 = Ideal.Quotient.mk I y := by
  -- The representative is exactly `y`.
  rw [dualNumberPowerSeriesSourceNormal, dualNumberPowerSeriesSourceBase_zero,
    dualNumberPowerSeriesSourceBase_one]
  simp

/-- Helper for Chap10 Example 10 119 4: the target normal form `(0,X)` is the class of `xz`. -/
private lemma dualNumberPowerSeriesTargetNormal_zero_X :
    dualNumberPowerSeriesTargetNormal k 0 (PowerSeries.X : PowerSeries k) =
      Ideal.Quotient.mk J (x * z) := by
  -- The representative is exactly `x*z`.
  rw [dualNumberPowerSeriesTargetNormal, dualNumberPowerSeriesTargetBase_zero,
    dualNumberPowerSeriesTargetBase_X]
  simp

/-- Helper for Chap10 Example 10 119 4: the linear source coordinate of `1` is zero. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_one_one :
    dualNumberPowerSeriesSourceQuotCoeff k 1 (1 : R) = 0 := by
  -- Rewrite the unit as source normal form `(1,0)` and read off its linear coordinate.
  rw [← dualNumberPowerSeriesSourceNormal_one_zero (k := k),
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one]

/-- Helper for Chap10 Example 10 119 4: the normal-form map sends `(p,q)` to `(p,Xq)`. -/
private lemma dualNumberPowerSeriesNormalExtension_map_zero :
    dualNumberPowerSeriesTargetNormal k
        (dualNumberPowerSeriesSourceQuotCoeff k 0 (0 : R))
        (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 (0 : R)) = 0 := by
  -- Both source coordinates of zero vanish.
  rw [dualNumberPowerSeriesSourceQuotCoeff_zero_zero,
    dualNumberPowerSeriesSourceQuotCoeff_one_zero, mul_zero,
    dualNumberPowerSeriesTargetNormal_zero_zero]

/-- Helper for Chap10 Example 10 119 4: the normal-form map preserves `1`. -/
private lemma dualNumberPowerSeriesNormalExtension_map_one :
    dualNumberPowerSeriesTargetNormal k
        (dualNumberPowerSeriesSourceQuotCoeff k 0 (1 : R))
        (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 (1 : R)) = 1 := by
  -- The unit has source coordinates `(1,0)`.
  rw [dualNumberPowerSeriesSourceQuotCoeff_zero_one,
    dualNumberPowerSeriesSourceQuotCoeff_one_one, mul_zero,
    dualNumberPowerSeriesTargetNormal_one_zero]

/-- Helper for Chap10 Example 10 119 4: the normal-form map preserves addition. -/
private lemma dualNumberPowerSeriesNormalExtension_map_add (r s : R) :
    dualNumberPowerSeriesTargetNormal k
        (dualNumberPowerSeriesSourceQuotCoeff k 0 (r + s))
        (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 (r + s)) =
      dualNumberPowerSeriesTargetNormal k
          (dualNumberPowerSeriesSourceQuotCoeff k 0 r)
          (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 r) +
        dualNumberPowerSeriesTargetNormal k
          (dualNumberPowerSeriesSourceQuotCoeff k 0 s)
          (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 s) := by
  -- Source and target normal coordinates are additive, and multiplication by `X` distributes.
  rw [dualNumberPowerSeriesSourceQuotCoeff_add, dualNumberPowerSeriesSourceQuotCoeff_add,
    ← dualNumberPowerSeriesTargetNormal_add]
  congr 1
  ring

/-- Helper for Chap10 Example 10 119 4: the normal-form map preserves multiplication. -/
private lemma dualNumberPowerSeriesNormalExtension_map_mul (r s : R) :
    dualNumberPowerSeriesTargetNormal k
        (dualNumberPowerSeriesSourceQuotCoeff k 0 (r * s))
        (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 (r * s)) =
      dualNumberPowerSeriesTargetNormal k
          (dualNumberPowerSeriesSourceQuotCoeff k 0 r)
          (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 r) *
        dualNumberPowerSeriesTargetNormal k
          (dualNumberPowerSeriesSourceQuotCoeff k 0 s)
          (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 s) := by
  -- Multiplication in both quotients is the same dual-number product rule, with `q` sent to
  -- `X*q`.
  rw [dualNumberPowerSeriesSourceQuotCoeff_mul_zero, dualNumberPowerSeriesSourceQuotCoeff_mul_one,
    ← dualNumberPowerSeriesTargetNormal_mul]
  congr 1
  ring

/-- Helper for Chap10 Example 10 119 4: the source-facing extension written in normal
coordinates. -/
private def dualNumberPowerSeriesNormalExtension : R →+* S where
  toFun r :=
    dualNumberPowerSeriesTargetNormal k
      (dualNumberPowerSeriesSourceQuotCoeff k 0 r)
      (PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 r)
  map_zero' := dualNumberPowerSeriesNormalExtension_map_zero k
  map_one' := dualNumberPowerSeriesNormalExtension_map_one k
  map_add' := dualNumberPowerSeriesNormalExtension_map_add k
  map_mul' := dualNumberPowerSeriesNormalExtension_map_mul k

/-- The source-facing extension `k[[x, y]]/(y^2) → k[[x, z]]/(z^2)`, `y ↦ xz`. -/
abbrev dualNumberPowerSeries_extension : R →+* S :=
  dualNumberPowerSeriesNormalExtension k

/-- Helper for Chap10 Example 10 119 4: the extension algebra structure induced by the explicit
normal-form map. -/
private instance dualNumberPowerSeriesExtensionAlgebra : Algebra R S :=
  (dualNumberPowerSeries_extension k).toAlgebra

/-- Helper for Chap10 Example 10 119 4: the target module structure induced by the explicit
extension. -/
private instance dualNumberPowerSeriesExtensionModule : Module R S :=
  Algebra.toModule

/-- Helper for Chap10 Example 10 119 4: the extension sends source normal form `(p,q)` to target
normal form `(p,Xq)`. -/
private lemma dualNumberPowerSeries_extension_sourceNormal (p q : PowerSeries k) :
    dualNumberPowerSeries_extension k (dualNumberPowerSeriesSourceNormal k p q) =
      dualNumberPowerSeriesTargetNormal k p (PowerSeries.X * q) := by
  -- This is immediate from the coordinate definition of the normal-form map.
  change dualNumberPowerSeriesTargetNormal k
      (dualNumberPowerSeriesSourceQuotCoeff k 0 (dualNumberPowerSeriesSourceNormal k p q))
      (PowerSeries.X *
        dualNumberPowerSeriesSourceQuotCoeff k 1 (dualNumberPowerSeriesSourceNormal k p q)) =
    dualNumberPowerSeriesTargetNormal k p (PowerSeries.X * q)
  rw [dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero,
    dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_one]

/-- Helper for Chap10 Example 10 119 4: scalar multiplication by a source normal form on a target
normal form. -/
private lemma dualNumberPowerSeries_extension_smul_targetNormal
    (p q r s : PowerSeries k) :
    dualNumberPowerSeriesSourceNormal k p q • dualNumberPowerSeriesTargetNormal k r s =
      dualNumberPowerSeriesTargetNormal k (p * r) (p * s + PowerSeries.X * q * r) := by
  -- Scalar multiplication is multiplication by the image of the source normal form.
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
    dualNumberPowerSeries_extension_sourceNormal, ← dualNumberPowerSeriesTargetNormal_mul]

/-- Helper for Chap10 Example 10 119 4: target normal forms are generated by `1` and the
nilpotent target class over the source ring. -/
private lemma dualNumberPowerSeriesTargetNormal_mem_span_one_z
    (p q : PowerSeries k) :
    dualNumberPowerSeriesTargetNormal k p q ∈
      Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) := by
  -- Split `(p,q)` as `(p,0) + (0,q)`; the two summands are source multiples of `1` and `z`.
  have hone_mem :
      (1 : S) ∈
        Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) :=
    Submodule.subset_span (by simp)
  have hz_mem :
      dualNumberPowerSeriesTargetNormal k 0 1 ∈
        Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) :=
    Submodule.subset_span (by simp)
  have hp_mem :
      dualNumberPowerSeriesTargetNormal k p 0 ∈
        Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) := by
    have hsmul :
        dualNumberPowerSeriesSourceNormal k p 0 • (1 : S) =
          dualNumberPowerSeriesTargetNormal k p 0 := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        dualNumberPowerSeries_extension_sourceNormal, mul_zero, mul_one]
    simpa [hsmul] using
      Submodule.smul_mem
        (Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S))
        (dualNumberPowerSeriesSourceNormal k p 0) hone_mem
  have hq_mem :
      dualNumberPowerSeriesTargetNormal k 0 q ∈
        Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) := by
    have hsmul :
        dualNumberPowerSeriesSourceNormal k q 0 •
            dualNumberPowerSeriesTargetNormal k 0 1 =
          dualNumberPowerSeriesTargetNormal k 0 q := by
      rw [dualNumberPowerSeries_extension_smul_targetNormal]
      simp
    simpa [hsmul] using
      Submodule.smul_mem
        (Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S))
        (dualNumberPowerSeriesSourceNormal k q 0) hz_mem
  have hsum :
      dualNumberPowerSeriesTargetNormal k p 0 + dualNumberPowerSeriesTargetNormal k 0 q ∈
        Submodule.span R ({(1 : S), dualNumberPowerSeriesTargetNormal k 0 1} : Set S) :=
    Submodule.add_mem _ hp_mem hq_mem
  have hnormal :
      dualNumberPowerSeriesTargetNormal k p q =
        dualNumberPowerSeriesTargetNormal k p 0 + dualNumberPowerSeriesTargetNormal k 0 q := by
    simpa using (dualNumberPowerSeriesTargetNormal_add (k := k) p 0 0 q)
  rw [hnormal]
  exact hsum

/-- Helper for Chap10 Example 10 119 4: the explicit extension makes the target a finite source
module. -/
private lemma dualNumberPowerSeries_extension_moduleFinite :
    Module.Finite R S := by
  -- The two target normal generators `1` and `z` span every target normal form.
  let zeta : S := dualNumberPowerSeriesTargetNormal k 0 1
  have hspan :
      Submodule.span R ({(1 : S), zeta} : Set S) = ⊤ := by
    rw [eq_top_iff]
    intro s hs
    rw [dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s]
    exact dualNumberPowerSeriesTargetNormal_mem_span_one_z k
      (dualNumberPowerSeriesTargetQuotCoeff k 0 s)
      (dualNumberPowerSeriesTargetQuotCoeff k 1 s)
  exact ⟨Submodule.fg_def.mpr
    ⟨{(1 : S), zeta}, by simp, hspan⟩⟩

/-- Helper for Chap10 Example 10 119 4: the explicit extension is injective. -/
private lemma dualNumberPowerSeries_extension_injective :
    Function.Injective (dualNumberPowerSeries_extension k) := by
  -- The target coordinates of the image are `(p,Xq)`, and multiplication by `X` is injective.
  intro r s hrs
  apply dualNumberPowerSeriesSourceNormal_ext k
  · have h0 := congrArg (dualNumberPowerSeriesTargetQuotCoeff k 0) hrs
    simpa [dualNumberPowerSeries_extension, dualNumberPowerSeriesNormalExtension,
      dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero] using h0
  · have h1 := congrArg (dualNumberPowerSeriesTargetQuotCoeff k 1) hrs
    have hX :
        PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 r =
          PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 s := by
      simpa [dualNumberPowerSeries_extension, dualNumberPowerSeriesNormalExtension,
        dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one] using h1
    exact PowerSeries.X_mul_injective hX

/-- Helper for Chap10 Example 10 119 4: the explicit extension has zero kernel. -/
private lemma dualNumberPowerSeries_extension_ker_eq_bot :
    RingHom.ker (dualNumberPowerSeries_extension k) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot (dualNumberPowerSeries_extension k)).1
    (dualNumberPowerSeries_extension_injective k)

/-- Helper for Chap10 Example 10 119 4: a unit constant coordinate makes a source normal form a
unit. -/
private lemma dualNumberPowerSeriesSourceNormal_isUnit_of_isUnit_left
    {p q : PowerSeries k} (hp : IsUnit p) :
    IsUnit (dualNumberPowerSeriesSourceNormal k p q) := by
  -- The inverse is the usual dual-number inverse `p⁻¹ - p⁻¹ q p⁻¹ y`.
  rcases hp with ⟨u, rfl⟩
  refine isUnit_iff_exists_inv.mpr ⟨
    dualNumberPowerSeriesSourceNormal k (↑u⁻¹)
      (-(↑u⁻¹ * q * ↑u⁻¹)), ?_⟩
  rw [← dualNumberPowerSeriesSourceNormal_mul,
    ← dualNumberPowerSeriesSourceNormal_one_zero (k := k)]
  congr 1
  · simp
  · calc
      (↑u : PowerSeries k) * (-(↑u⁻¹ * q * ↑u⁻¹)) + q * ↑u⁻¹ =
          -(((↑u : PowerSeries k) * ↑u⁻¹) * q * ↑u⁻¹) + q * ↑u⁻¹ := by
            ring
      _ = 0 := by
            simp

/-- Helper for Chap10 Example 10 119 4: a maximal-ideal source element has `X` dividing its
constant normal coordinate. -/
private lemma dualNumberPowerSeriesSourceQuotCoeff_zero_dvd_X_of_mem_maximalIdeal
    {r : R} (hr : r ∈ maximalIdeal R) :
    PowerSeries.X ∣ dualNumberPowerSeriesSourceQuotCoeff k 0 r := by
  -- If the constant coordinate were a unit, the source normal form would be a unit, contradicting
  -- maximal-ideal membership.
  rw [PowerSeries.X_dvd_iff]
  by_contra hconst
  have hpunit : IsUnit (dualNumberPowerSeriesSourceQuotCoeff k 0 r) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hconst)
  have hrunit : IsUnit r := by
    rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r]
    exact dualNumberPowerSeriesSourceNormal_isUnit_of_isUnit_left k hpunit
  rw [IsLocalRing.mem_maximalIdeal] at hr
  exact hr hrunit

/-- Helper for Chap10 Example 10 119 4: the source class of `x` lies in the maximal ideal. -/
private lemma dualNumberPowerSeriesSourceNormal_X_zero_mem_maximalIdeal :
    dualNumberPowerSeriesSourceNormal k (PowerSeries.X : PowerSeries k) 0 ∈ maximalIdeal R := by
  -- A unit source class would map to the nonunit power-series variable under the constant
  -- coordinate projection.
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  have hXunit : IsUnit (PowerSeries.X : PowerSeries k) := by
    simpa [dualNumberPowerSeriesSourceConstCoeffHom_apply,
      dualNumberPowerSeriesSourceQuotCoeff_sourceNormal_zero] using
      hunit.map (dualNumberPowerSeriesSourceConstCoeffHom k)
  have hconstUnit :
      IsUnit (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries k)) :=
    PowerSeries.isUnit_constantCoeff _ hXunit
  simpa using hconstUnit

/-- Helper for Chap10 Example 10 119 4: multiplication by the source class of `x` is injective on
the target module. -/
private lemma dualNumberPowerSeries_extension_X_isSMulRegular :
    IsSMulRegular S (dualNumberPowerSeriesSourceNormal k (PowerSeries.X : PowerSeries k) 0) := by
  -- In target coordinates this multiplication is `(p,q) ↦ (Xp,Xq)`, and `X` is regular on
  -- one-variable power series.
  refine
    (@IsSMulRegular.of_right_eq_zero_of_smul R S _ _
      (dualNumberPowerSeriesSourceNormal k (PowerSeries.X : PowerSeries k) 0)) ?_
  intro s hs
  rw [dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s] at hs ⊢
  rw [dualNumberPowerSeries_extension_smul_targetNormal] at hs
  have htarget :
      dualNumberPowerSeriesTargetNormal k
          (PowerSeries.X * dualNumberPowerSeriesTargetQuotCoeff k 0 s)
          (PowerSeries.X * dualNumberPowerSeriesTargetQuotCoeff k 1 s) =
        dualNumberPowerSeriesTargetNormal k 0 0 := by
    simpa [dualNumberPowerSeriesTargetNormal_zero_zero] using hs
  have h0 := congrArg (dualNumberPowerSeriesTargetQuotCoeff k 0) htarget
  have h1 := congrArg (dualNumberPowerSeriesTargetQuotCoeff k 1) htarget
  have h0' :
      PowerSeries.X * dualNumberPowerSeriesTargetQuotCoeff k 0 s =
        PowerSeries.X * 0 := by
    simpa [dualNumberPowerSeriesTargetQuotCoeff_targetNormal_zero] using h0
  have h1' :
      PowerSeries.X * dualNumberPowerSeriesTargetQuotCoeff k 1 s =
        PowerSeries.X * 0 := by
    simpa [dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one] using h1
  have hs0 : dualNumberPowerSeriesTargetQuotCoeff k 0 s = 0 :=
    PowerSeries.X_mul_injective h0'
  have hs1 : dualNumberPowerSeriesTargetQuotCoeff k 1 s = 0 :=
    PowerSeries.X_mul_injective h1'
  rw [hs0, hs1, dualNumberPowerSeriesTargetNormal_zero_zero]

/-- Helper for Chap10 Example 10 119 4: the explicit extension is not surjective. -/
private lemma dualNumberPowerSeries_extension_not_surjective :
    ¬ Function.Surjective (dualNumberPowerSeries_extension k) := by
  -- The target class of `z` would require solving `X*q = 1` in `k[[X]]`.
  intro hsurj
  rcases hsurj (dualNumberPowerSeriesTargetNormal k 0 1) with ⟨r, hr⟩
  rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r,
    dualNumberPowerSeries_extension_sourceNormal] at hr
  have hlinear := congrArg (dualNumberPowerSeriesTargetQuotCoeff k 1) hr
  have hXone :
      PowerSeries.X * dualNumberPowerSeriesSourceQuotCoeff k 1 r = 1 := by
    simpa [dualNumberPowerSeriesTargetQuotCoeff_targetNormal_one] using hlinear
  have hconst :
      (0 : k) = 1 := by
    simpa using congrArg PowerSeries.constantCoeff hXone
  exact zero_ne_one hconst

/-- Helper for Chap10 Example 10 119 4: the explicit extension is not bijective. -/
private lemma dualNumberPowerSeries_extension_not_bijective :
    ¬ Function.Bijective (dualNumberPowerSeries_extension k) := by
  -- Non-surjectivity is enough.
  intro hbij
  exact dualNumberPowerSeries_extension_not_surjective k hbij.2

/-- Helper for Chap10 Example 10 119 4: one maximal-ideal power kills the kernel of the explicit
extension. -/
private lemma dualNumberPowerSeries_extension_maximalIdeal_smul_ker_eq_bot :
    (maximalIdeal R) ^ 1 •
        (RingHom.ker (dualNumberPowerSeries_extension k) : Submodule R R) = ⊥ := by
  -- The extension is injective, so its kernel is already zero.
  rw [dualNumberPowerSeries_extension_ker_eq_bot]
  simp

/-- Helper for Chap10 Example 10 119 4: one maximal-ideal power sends the target into the image
of the explicit extension. -/
private lemma dualNumberPowerSeries_extension_maximalIdeal_smul_top_le_range :
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R S) ≤
      (Algebra.linearMap R S).range := by
  -- For `r ∈ 𝔪`, the constant source coordinate has an `X` factor, so multiplying any target
  -- normal form by `r` has linear coordinate divisible by `X` and is therefore in the image.
  intro w hw
  rw [pow_one] at hw
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro r hr s hs
    obtain ⟨a, ha⟩ :=
      dualNumberPowerSeriesSourceQuotCoeff_zero_dvd_X_of_mem_maximalIdeal k hr
    let r0 := dualNumberPowerSeriesSourceQuotCoeff k 0 r
    let r1 := dualNumberPowerSeriesSourceQuotCoeff k 1 r
    let s0 := dualNumberPowerSeriesTargetQuotCoeff k 0 s
    let s1 := dualNumberPowerSeriesTargetQuotCoeff k 1 s
    refine ⟨dualNumberPowerSeriesSourceNormal k (r0 * s0) (a * s1 + r1 * s0), ?_⟩
    calc
      (Algebra.linearMap R S)
          (dualNumberPowerSeriesSourceNormal k (r0 * s0) (a * s1 + r1 * s0)) =
          dualNumberPowerSeriesTargetNormal k (r0 * s0)
            (PowerSeries.X * (a * s1 + r1 * s0)) := by
            simpa [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra] using
              dualNumberPowerSeries_extension_sourceNormal k (r0 * s0) (a * s1 + r1 * s0)
      _ = dualNumberPowerSeriesTargetNormal k (r0 * s0) (r0 * s1 + PowerSeries.X * r1 * s0) := by
            dsimp [r0]
            rw [ha]
            congr 1
            ring
      _ = dualNumberPowerSeriesSourceNormal k r0 r1 •
            dualNumberPowerSeriesTargetNormal k s0 s1 := by
            rw [dualNumberPowerSeries_extension_smul_targetNormal]
      _ = r • s := by
            rw [dualNumberPowerSeriesSource_quotient_reconstruction_normal k r,
              dualNumberPowerSeriesTarget_quotient_reconstruction_normal k s]
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

/-- Helper for Chap10 Example 10 119 4: the maximal ideal is not an associated prime of the
target module for the explicit extension. -/
private lemma dualNumberPowerSeries_extension_maximalIdeal_not_mem_associatedPrimes :
    maximalIdeal R ∉ associatedPrimes R S := by
  -- The source class of `x` is in the maximal ideal and is regular on the target.
  letI : Module.Finite R S := dualNumberPowerSeries_extension_moduleFinite k
  exact
    maximalIdeal_not_mem_associatedPrimes_of_mem_maximalIdeal_of_isSMulRegular R
      (dualNumberPowerSeriesSourceNormal_X_zero_mem_maximalIdeal k)
      (dualNumberPowerSeries_extension_X_isSMulRegular k)

/-- Helper for Chap10 Example 10 119 4: linear equivalences preserve Cohen-Macaulayness. -/
private theorem cohenMacaulay_of_linearEquiv
    {A₀ M N : Type u} [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀]
    [AddCommGroup M] [Module A₀ M] [AddCommGroup N] [Module A₀ N]
    [Module.Finite A₀ N]
    (e : M ≃ₗ[A₀] N) [hM : Module.CohenMacaulay A₀ M] :
    Module.CohenMacaulay A₀ N := by
  -- Proof comment: both support dimension and depth are invariant under a linear equivalence.
  refine Module.CohenMacaulay.mk ?_
  rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e,
    hM.supportDim_eq_moduleDepth]

/-- Helper for Chap10 Example 10 119 4: the ambient equation `y^2` is a nonzerodivisor. -/
private lemma dualNumberPowerSeriesSquareGenerator_mem_nonZeroDivisors :
    y ^ 2 ∈ nonZeroDivisors A := by
  -- Proof comment: the variable `y` is a monomial nonzerodivisor, and the nonzerodivisors form a
  -- submonoid.
  exact pow_mem (MvPowerSeries.X_mem_nonzeroDivisors (i := (1 : Fin 2))) 2

/-- Helper for Chap10 Example 10 119 4: the ambient equation `y^2` lies in the maximal ideal. -/
private lemma dualNumberPowerSeriesSquareGenerator_mem_maximalIdeal :
    y ^ 2 ∈ maximalIdeal A := by
  -- Proof comment: a power series with zero constant coefficient is not a unit in the local
  -- power-series ring.
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  have hconst :
      IsUnit (MvPowerSeries.constantCoeff (y ^ 2)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mp hunit
  simpa using hconst

/-- Helper for Chap10 Example 10 119 4: the scalar multiple `y^2 A` is the principal ideal
`(y^2)`. -/
private lemma dualNumberPowerSeriesSquareGenerator_smul_top_eq_squareIdeal :
    y ^ 2 • (⊤ : Submodule A A) = (I : Submodule A A) := by
  -- Proof comment: `QuotSMulTop` uses the submodule `y^2 A`, while the presentation of `R` uses
  -- the corresponding principal ideal.
  simp [dualNumberPowerSeriesSquareIdeal, ← Submodule.ideal_span_singleton_smul]

/-- Helper for Chap10 Example 10 119 4: the source quotient is Cohen-Macaulay as an ambient
module. -/
private lemma dualNumberPowerSeriesRing_cohenMacaulay_as_ambientModule :
    Module.CohenMacaulay A R := by
  -- Proof comment: quotient the regular ambient ring by the nonzerodivisor `y^2`.
  have hquot :
      Module.CohenMacaulay A (QuotSMulTop (y ^ 2) A) :=
    (Module.cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal
      (M := A)
      (dualNumberPowerSeriesSquareGenerator_mem_maximalIdeal k)
      (Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := A) (dualNumberPowerSeriesSquareGenerator_mem_nonZeroDivisors k))).1 inferInstance
  letI : Module.CohenMacaulay A (QuotSMulTop (y ^ 2) A) := hquot
  let e : QuotSMulTop (y ^ 2) A ≃ₗ[A] R :=
    Submodule.quotEquivOfEq _ _ (dualNumberPowerSeriesSquareGenerator_smul_top_eq_squareIdeal k)
  exact cohenMacaulay_of_linearEquiv e

/-- Chap10 Example 10 119 4: the explicit extension
`k[[x, y]]/(y^2) → k[[x, z]]/(z^2)`, `y ↦ xz`, satisfies the four conclusions of
Lemma 10.119.3. -/
@[stacks 00PA]
theorem dualNumberPowerSeries_extension_isKollarExceptionalFiniteExtension :
    (dualNumberPowerSeries_extension k).IsKollarExceptionalFiniteExtension := by
  -- Proof comment: unfold the map-level package and supply the coordinate proofs for the
  -- normal-form extension `(p,q) ↦ (p,Xq)`.
  rw [RingHom.IsKollarExceptionalFiniteExtension]
  exact
    ⟨inferInstance,
      dualNumberPowerSeries_extension_moduleFinite k,
      dualNumberPowerSeries_extension_not_bijective k,
      ⟨1,
        dualNumberPowerSeries_extension_maximalIdeal_smul_ker_eq_bot k,
        dualNumberPowerSeries_extension_maximalIdeal_smul_top_le_range k⟩,
      dualNumberPowerSeries_extension_maximalIdeal_not_mem_associatedPrimes k⟩

-- Proof sketch: view the quotient as a one-dimensional hypersurface over the regular local ring
-- `k[[x, y]]`; the nilpotent thickening by `y` does not change the dimension from that of
-- `k[[x]]`.
/-- The quotient `k[[x, y]]/(y^2)` has Krull dimension `1`. -/
theorem dualNumberPowerSeriesRing_ringKrullDim_eq_one :
    ringKrullDim R = 1 := by
  -- Proof comment: quotienting the two-variable regular power-series ring by the nonzerodivisor
  -- `y^2` drops Krull dimension from `2` to `1`.
  have hdrop :
      ringKrullDim R + 1 = ringKrullDim A := by
    simpa [dualNumberPowerSeriesRing, dualNumberPowerSeriesSquareIdeal] using
      (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (dualNumberPowerSeriesSquareGenerator_mem_nonZeroDivisors k)
        (dualNumberPowerSeriesSquareGenerator_mem_maximalIdeal k))
  have hdimA : ringKrullDim A = (2 : WithBot ℕ∞) := by
    simpa using dualNumberPowerSeriesRingKrullDim_mvPowerSeries_fin_field k 2
  have hone :
      ringKrullDim R + 1 = (1 : WithBot ℕ∞) + 1 := by
    rw [hdrop, hdimA]
    norm_num
  exact ENat.WithBot.add_one_cancel.mp hone

-- Proof sketch: `k[[x, y]]/(y^2)` is a hypersurface quotient of the regular local ring
-- `k[[x, y]]` by the nonzerodivisor `y^2`, hence it is Cohen-Macaulay.
/-- The quotient `k[[x, y]]/(y^2)` is Cohen-Macaulay as a module over itself. -/
theorem dualNumberPowerSeriesRing_selfModule_cohenMacaulay :
    Module.CohenMacaulay R R := by
  -- Proof comment: Cohen-Macaulayness over the quotient ring is equivalent to the already proved
  -- ambient Cohen-Macaulayness because the quotient map is surjective.
  have hsurj : Function.Surjective (algebraMap A R) := by
    simpa [Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (N := R) hsurj).2
        (dualNumberPowerSeriesRing_cohenMacaulay_as_ambientModule k)

-- Proof sketch: apply the chapter owner theorem
-- `hasKollarExceptionalFiniteExtension_of_ringKrullDim_eq_one_of_one_lt_finrank_cotangentSpace`
-- to the local ring `R = k[[x, y]]/(y^2)`.
/-- The ring `k[[x, y]]/(y^2)` satisfies Kollár's exceptional finite-extension alternative.
The explicit witness is the map `dualNumberPowerSeries_extension k`, and
`dualNumberPowerSeries_extension_isKollarExceptionalFiniteExtension` records the map-level
bridge from that source-facing witness to the canonical owner proposition. -/
theorem dualNumberPowerSeriesRing_hasKollarExceptionalFiniteExtension :
    HasKollarExceptionalFiniteExtension R :=
  (dualNumberPowerSeries_extension k).hasKollarExceptionalFiniteExtension
    (dualNumberPowerSeries_extension_isKollarExceptionalFiniteExtension k)

/-- Helper for Chap10 Example 10 119 4: the extension
`k[[x, y]]/(y^2) ⊂ k[[x, z]]/(z^2)`, `y ↦ xz`, is given by
`dualNumberPowerSeries_extension k`. -/
theorem dualNumberPowerSeries_extension_apply_nilpotentGenerator :
    dualNumberPowerSeries_extension k (Ideal.Quotient.mk I y) =
      Ideal.Quotient.mk J (x * z) := by
  -- Proof comment: specialize the normal-form formula to the source class `(0,1)`.
  rw [← dualNumberPowerSeriesSourceNormal_zero_one (k := k),
    dualNumberPowerSeries_extension_sourceNormal]
  simpa using dualNumberPowerSeriesTargetNormal_zero_X k

-- Proof sketch: descend the ambient substitution formula defining
-- `dualNumberPowerSeries_iteratedExtension`; the class of the nilpotent generator is sent to the
-- class of `x^n z`.
/-- Repeating the construction sends the class of `y` in `k[[x, y]]/(y^2)` to the class of
`x^n z` in `k[[x, z]]/(z^2)` for every `n`. In other words, the `n`-fold construction adjoins
`y / x^n`. -/
theorem dualNumberPowerSeries_iteratedExtension_apply_nilpotentGenerator (n : ℕ) :
    dualNumberPowerSeries_iteratedExtension k n
        (Ideal.Quotient.mk I y) =
      Ideal.Quotient.mk J (x ^ n * z) := by
  -- Proof comment: evaluate the quotient lift on the class of `y` and rewrite the ambient image.
  rw [dualNumberPowerSeries_iteratedExtension, Ideal.Quotient.lift_mk]
  exact dualNumberPowerSeries_iteratedTargetRingHom_nilpotentGenerator k n
