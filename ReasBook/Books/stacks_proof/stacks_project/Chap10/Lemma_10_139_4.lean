import Mathlib
import StacksProject_2024.Chap10.Lemma_10_131_10
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_139_4.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.139.4:
- primary domain: smooth commutative algebra retractions, their conormal module, and the induced
  formal local structure on adic completions;
- sampled owner declarations:
  `Algebra.Smooth`,
  `KaehlerDifferential.finite`,
  `FormallySmooth.projective_kaehlerDifferential`,
  `retractionKerCotangentToTensorEquivSection`;
- best owner abstraction: the smooth owner `Algebra.Smooth R S` together with the canonical
  conormal owner `(RingHom.ker σ).Cotangent` attached to a section `σ : S →ₐ[R] R`;
- primitive data: the smooth `R`-algebra `S`, the section `σ`, and the left-inverse equation `hσ`;
- derived API: finiteness/projectivity of the conormal module and, after a freeness hypothesis, the
  existence of a formal-power-series description of the `ker σ`-adic completion.

Source/core/bridge triage:
- `source-facing`: the two theorems below about the conormal module and the completed algebra of a
  smooth retraction;
- `core/canonical`: `Algebra.Smooth`, the Kähler/formal-smooth owner theorems, and the canonical
  conormal owner `RingHom.ker σ`;
- `bridge/view`: the textbook identification `I/I²` with `(RingHom.ker σ).Cotangent` and the
  resulting power-series presentation of the completion. -/

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

include hσ

-- Proof sketch: apply the split conormal sequence for the section `σ : S →ₐ[R] R` to identify
-- `(RingHom.ker σ).Cotangent` with a base change of `Ω[S⁄R]`; smoothness makes
-- `Ω[S⁄R]` finite and projective over `S`, and restriction along the section preserves those
-- finiteness and projectivity properties over `R`.
/-- Helper for Chap10 Lemma 10 139 4: if `R → S` is smooth and `σ : S →ₐ[R] R` is a left inverse to the
structure map, then the conormal module `I/I²`, with `I = ker σ`, is a finite projective
`R`-module. This is the canonical mathlib-facing formulation of the source statement that
`I/I²` is finite locally free over `R`. -/
@[stacks 05D5]
theorem smooth_section_cotangent_finite_projective :
    Module.Finite R (RingHom.ker σ).Cotangent ∧
      Module.Projective R (RingHom.ker σ).Cotangent := by
  letI : Algebra S R := σ.toRingHom.toAlgebra
  have hsection :
      (IsScalarTower.toAlgHom R S R).comp (IsScalarTower.toAlgHom R R S) = AlgHom.id R R := by
    exact AlgHom.ext hσ
  have hker : RingHom.ker (algebraMap S R) = RingHom.ker σ := by
    ext x
    rfl
  -- The split conormal sequence identifies `I/I²` with the base change of `Ω[S⁄R]`.
  obtain ⟨hexact, -, ⟨l, hl⟩⟩ :=
    kaehlerDifferential_conormal_sequence_split_of_section (R := R) (S := S) (S' := R)
      (β := IsScalarTower.toAlgHom R R S) hsection
  have hsurjective : Function.Surjective (KaehlerDifferential.kerCotangentToTensor R S R) := by
    intro x
    have hx0 : KaehlerDifferential.mapBaseChange R S R x = 0 := Subsingleton.elim _ _
    exact (hexact x).mp hx0
  let eKer : (RingHom.ker σ).Cotangent ≃ₗ[R] (RingHom.ker (algebraMap S R)).Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ hker.symm).restrictScalars R
  let eBase : (RingHom.ker (algebraMap S R)).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R S R)
      ⟨LinearMap.injective_of_comp_eq_id _ _ hl, hsurjective⟩ |>.restrictScalars R
  let e : (RingHom.ker σ).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] := eKer.trans eBase
  -- Smoothness makes `Ω[S⁄R]` finite projective, and base change preserves both properties.
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Helper for Chap10 Lemma 10 139 4: freeness together with the finite/projective result gives a basis of
the conormal module indexed by `Fin d`, and each basis vector can be lifted back to `ker σ`. -/
private theorem exists_cotangent_fin_basis_and_lifts
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ d : ℕ, ∃ b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent,
      ∃ f : Fin d → RingHom.ker σ, ∀ i, (RingHom.ker σ).toCotangent (f i) = b i := by
  obtain ⟨hfinite, -⟩ :=
    smooth_section_cotangent_finite_projective (R := R) (S := S) (σ := σ) hσ
  letI : Module.Free R (RingHom.ker σ).Cotangent := hfree
  letI : Module.Finite R (RingHom.ker σ).Cotangent := hfinite
  let b0 : Module.Basis (Module.Free.ChooseBasisIndex R (RingHom.ker σ).Cotangent) R
      (RingHom.ker σ).Cotangent := Module.Free.chooseBasis R (RingHom.ker σ).Cotangent
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R
        (RingHom.ker σ).Cotangent))) R (RingHom.ker σ).Cotangent :=
    b0.reindex (Fintype.equivFin _)
  -- Each cotangent basis vector comes from some element of the kernel ideal.
  choose f hf using fun i : Fin (Fintype.card (Module.Free.ChooseBasisIndex R
      (RingHom.ker σ).Cotangent)) ↦
    (RingHom.ker σ).toCotangent_surjective (b i)
  exact ⟨_, b, f, hf⟩

omit [Algebra.Smooth R S] hσ in
/-- Helper for Chap10 Lemma 10 139 4: coefficient and first-order lifts propagate to all powers
of an ideal with the expected adic error bound. -/
private theorem idealPower_lift_mod_highPower
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (J : Ideal A) (I : Ideal B) {n : ℕ}
    (hn : 2 ≤ n)
    (hJ : Ideal.map φ J ≤ I)
    (hcoeff : ∀ b : B, ∃ a : A, b - φ a ∈ I ^ n)
    (hI : ∀ b : B, b ∈ I → ∃ a : A, a ∈ J ∧ b - φ a ∈ I ^ n) :
    ∀ {m : ℕ} {x : B}, x ∈ I ^ m →
      ∃ p : A, p ∈ J ^ m ∧ x - φ p ∈ I ^ (n + m - 1) := by
  intro m x hx
  -- Induct along the power filtration; the base case uses arbitrary coefficient lifts, and the
  -- multiplication step uses a single lift for the new `I`-factor.
  refine Submodule.pow_induction_on_left' (M := I)
    (C := fun i x hx ↦ ∃ p : A, p ∈ J ^ i ∧ x - φ p ∈ I ^ (n + i - 1))
    (fun b ↦ ?_)
    (fun x y i hx hy hxprop hyprop ↦ ?_)
    (fun b hb i x hx hxprop ↦ ?_)
    hx
  · rcases hcoeff b with ⟨a, ha⟩
    refine ⟨a, by simp, ?_⟩
    have hle : n - 1 ≤ n := by omega
    exact (Ideal.pow_le_pow_right (I := I) hle) (by simpa using ha)
  · rcases hxprop with ⟨px, hpx, herrx⟩
    rcases hyprop with ⟨py, hpy, herry⟩
    refine ⟨px + py, Ideal.add_mem _ hpx hpy, ?_⟩
    have hcalc : x + y - φ (px + py) = (x - φ px) + (y - φ py) := by
      simp [map_add]
      abel
    rw [hcalc]
    exact Ideal.add_mem _ herrx herry
  · rcases hI b hb with ⟨a, haJ, haerr⟩
    rcases hxprop with ⟨p, hpJ, hperr⟩
    refine ⟨a * p, ?_, ?_⟩
    · have hmul : a * p ∈ J ^ 1 * J ^ i := by
        simpa [pow_one] using Ideal.mul_mem_mul haJ hpJ
      simpa [pow_succ'] using hmul
    · have hcalc : b * x - φ (a * p) = (b - φ a) * x + (φ a) * (x - φ p) := by
        simp [map_mul]
        ring
      rw [hcalc]
      apply Ideal.add_mem
      · have hleft : (b - φ a) * x ∈ I ^ n * I ^ i :=
          Ideal.mul_mem_mul haerr hx
        have hexp : n + (i + 1) - 1 = n + i := by omega
        rw [hexp, pow_add]
        exact hleft
      · have hφa : φ a ∈ I := hJ (Ideal.mem_map_of_mem φ haJ)
        have hright : φ a * (x - φ p) ∈ I ^ 1 * I ^ (n + i - 1) := by
          simpa [pow_one] using Ideal.mul_mem_mul hφa hperr
        have hexp : n + (i + 1) - 1 = 1 + (n + i - 1) := by omega
        rw [hexp, pow_add]
        exact hright

omit hσ in
/-- Helper for Chap10 Lemma 10 139 4: a right inverse modulo `I^n` gives polynomial
representatives modulo `I^n` for arbitrary coefficients of `S`. -/
private theorem cotangentLift_surjective_mod_pow {d n : ℕ}
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ s : S, ∃ p : MvPolynomial (Fin d) R,
      s - (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f) p ∈
        (RingHom.ker σ) ^ n := by
  intro s
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let φ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  let Ψn := cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (σn (Ideal.Quotient.mk (I ^ n) s))
  refine ⟨p, ?_⟩
  -- Compare the chosen representative with `s` after applying the truncated map.
  have hmkφ : Ψn (Ideal.Quotient.mk (J ^ n) p) = Ideal.Quotient.mk (I ^ n) (φ p) := by
    rfl
  have hq : Ideal.Quotient.mk (I ^ n) (φ p) = Ideal.Quotient.mk (I ^ n) s := by
    calc
      Ideal.Quotient.mk (I ^ n) (φ p) = Ψn (Ideal.Quotient.mk (J ^ n) p) := hmkφ.symm
      _ = Ψn (σn (Ideal.Quotient.mk (I ^ n) s)) := by rw [hp]
      _ = Ideal.Quotient.mk (I ^ n) s := by
        exact AlgHom.congr_fun hΨσ (Ideal.Quotient.mk (I ^ n) s)
  have hmem : φ p - s ∈ I ^ n := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I ^ n) (x := φ p) (y := s)).mp hq
  have hneg : -(φ p - s) ∈ I ^ n := neg_mem hmem
  simpa [φ, I, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-- Helper for Chap10 Lemma 10 139 4: elements of `ker σ` have representatives in the variable
ideal modulo `I^n`. -/
private theorem cotangentLift_ker_lift_mod_pow {d n : ℕ}
    (hn0 : 0 < n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ x : S, x ∈ RingHom.ker σ → ∃ p : MvPolynomial (Fin d) R,
      p ∈ MvPolynomial.idealOfVars (Fin d) R ∧
      x - (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f) p ∈
        (RingHom.ker σ) ^ n := by
  intro x hx
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let φ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  let Ψn := cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n
  let qJn1 :
      MvPolynomial (Fin d) R ⧸ J ^ n →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (show 1 ≤ n by omega))
  let qIn1 : S ⧸ I ^ n →ₐ[R] S ⧸ I ^ 1 :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (show 1 ≤ n by omega))
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (σn (Ideal.Quotient.mk (I ^ n) x))
  refine ⟨p, ?_, ?_⟩
  · have hstage := truncation_inverse_reduces_to_stage_one
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn0 f σn hσΨ hΨσ
    have hqInx : qIn1 (Ideal.Quotient.mk (I ^ n) x) = 0 := by
      have hxquot : Ideal.Quotient.mk (I ^ 1) x = 0 := by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [I, pow_one] using hx)
      simpa [qIn1] using hxquot
    -- Reducing the chosen representative to order one gives zero, so it lies in `J`.
    have hqzero : qJn1 (Ideal.Quotient.mk (J ^ n) p) = 0 := by
      calc
        qJn1 (Ideal.Quotient.mk (J ^ n) p) =
            qJn1 (σn (Ideal.Quotient.mk (I ^ n) x)) := by rw [hp]
        _ = (smooth_section_stageOne_inverse_powOne
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
            (qIn1 (Ideal.Quotient.mk (I ^ n) x)) := by
              exact AlgHom.congr_fun hstage (Ideal.Quotient.mk (I ^ n) x)
        _ = 0 := by
          rw [hqInx]
          simp
    have hmem1 : p ∈ J ^ 1 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [qJn1] using hqzero)
    simpa [J, pow_one] using hmem1
  · have hmkφ : Ψn (Ideal.Quotient.mk (J ^ n) p) = Ideal.Quotient.mk (I ^ n) (φ p) := by
      rfl
    have hq : Ideal.Quotient.mk (I ^ n) (φ p) = Ideal.Quotient.mk (I ^ n) x := by
      calc
        Ideal.Quotient.mk (I ^ n) (φ p) = Ψn (Ideal.Quotient.mk (J ^ n) p) := hmkφ.symm
        _ = Ψn (σn (Ideal.Quotient.mk (I ^ n) x)) := by rw [hp]
        _ = Ideal.Quotient.mk (I ^ n) x := by
          exact AlgHom.congr_fun hΨσ (Ideal.Quotient.mk (I ^ n) x)
    have hmem : φ p - x ∈ I ^ n := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I ^ n) (x := φ p) (y := x)).mp hq
    have hneg : -(φ p - x) ∈ I ^ n := neg_mem hmem
    simpa [φ, I, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-- Helper for Chap10 Lemma 10 139 4: elements of `I^n` lift from `J^n` modulo
`I^(n+1)` under a stage-`n` inverse. -/
private theorem cotangentLift_kerPow_lift_mod_succPow {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ x : S, x ∈ (RingHom.ker σ) ^ n → ∃ p : MvPolynomial (Fin d) R,
      p ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ n ∧
      x - (cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f) p ∈
        (RingHom.ker σ) ^ (n + 1) := by
  intro x hx
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let φ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  -- Feed coefficient lifts and single `I`-factor lifts into the generic power-filtration lemma.
  obtain ⟨p, hpJ, hperr⟩ := idealPower_lift_mod_highPower
    (φ := φ.toRingHom) (J := J) (I := I) hn
    (by
      simpa [φ, J, I] using
        cotangent_lift_polynomial_map_idealOfVars_le_ker (R := R) (S := S) (σ := σ) f)
    (by
      intro b
      exact cotangentLift_surjective_mod_pow
        (R := R) (S := S) (σ := σ) f σn hΨσ b)
    (by
      intro b hb
      exact cotangentLift_ker_lift_mod_pow
        (R := R) (S := S) (σ := σ) (hσ := hσ)
        (d := d) (n := n) hn0 f σn hσΨ hΨσ b (by simpa [I] using hb))
    (m := n) (x := x) (by simpa [I] using hx)
  refine ⟨p, by simpa [J] using hpJ, ?_⟩
  exact (Ideal.pow_le_pow_right (I := I) (show n + 1 ≤ n + n - 1 by omega))
    (by simpa [φ, I] using hperr)

/-- Helper for Chap10 Lemma 10 139 4: the successor map is surjective on the transition kernels
once a two-sided inverse is known at stage `n`. -/
private theorem cotangent_lift_transition_kernel_surjective_of_prev_inverse {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ y : S ⧸ (RingHom.ker σ) ^ (n + 1),
      y ∈ RingHom.ker
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).toRingHom →
      ∃ x : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1),
        x ∈ RingHom.ker
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).toRingHom ∧
        cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1) x = y := by
  intro y hy
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let φ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  let Ψsucc := cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)
  let qI : S ⧸ I ^ (n + 1) →ₐ[R] S ⧸ I ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qJ :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hs : s ∈ I ^ n := by
    have hzero : qI (Ideal.Quotient.mk (I ^ (n + 1)) s) = 0 := by
      simpa [qI, I] using (RingHom.mem_ker.mp hy)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [qI] using hzero)
  obtain ⟨p, hpJ, hperr⟩ := cotangentLift_kerPow_lift_mod_succPow
    (R := R) (S := S) (σ := σ) (hσ := hσ)
    (d := d) (n := n) hn f σn hσΨ hΨσ s (by simpa [I] using hs)
  refine ⟨Ideal.Quotient.mk (J ^ (n + 1)) p, ?_, ?_⟩
  · have hzero : qJ (Ideal.Quotient.mk (J ^ (n + 1)) p) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [J] using hpJ)
    exact RingHom.mem_ker.mpr (by simpa [qJ, J] using hzero)
  · have hq :
        Ideal.Quotient.mk (I ^ (n + 1)) s = Ideal.Quotient.mk (I ^ (n + 1)) (φ p) := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I ^ (n + 1)) (x := s) (y := φ p)).mpr
        (by simpa [φ, I] using hperr)
    calc
      Ψsucc (Ideal.Quotient.mk (J ^ (n + 1)) p) =
          Ideal.Quotient.mk (I ^ (n + 1)) (φ p) := by
            rfl
      _ = Ideal.Quotient.mk (I ^ (n + 1)) s := hq.symm

/-- Chap10 Lemma 10 139 4: if `Ψ_n` already has a two-sided inverse, then `Ψ_(n + 1)` is
surjective. The source proof lifts a preimage modulo `I^n` and absorbs the remaining transition
error with nilpotent Nakayama. -/
private theorem cotangent_lift_truncated_map_surjective_of_prev_inverse {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    Function.Surjective (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)) := by
  intro y
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let Ψn := cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n
  let Ψsucc := cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)
  let qJ :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qI : S ⧸ I ^ (n + 1) →ₐ[R] S ⧸ I ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  -- First lift the lower-stage preimage through the source transition map.
  obtain ⟨x0, hx0⟩ := Ideal.Quotient.factor_surjective
      (by simpa [J] using (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n)))
      (σn (qI y))
  have hx0q : qJ x0 = σn (qI y) := by
    simpa [qJ, J] using hx0
  have hres_kernel : y - Ψsucc x0 ∈ RingHom.ker qI.toRingHom := by
    rw [RingHom.mem_ker]
    calc
      qI (y - Ψsucc x0) = qI y - qI (Ψsucc x0) := by simp
      _ = qI y - Ψn (qJ x0) := by
        congr 1
        exact AlgHom.congr_fun
          (cotangent_lift_truncated_map_compatible
            (R := R) (S := S) (σ := σ) f (m := n) (n := n + 1) (Nat.le_succ n))
          x0
      _ = qI y - Ψn (σn (qI y)) := by
        rw [hx0q]
      _ = qI y - qI y := by
        congr 1
        exact AlgHom.congr_fun hΨσ (qI y)
      _ = 0 := sub_self _
  obtain ⟨xerr, hxerr_kernel, hxerr⟩ :=
    cotangent_lift_transition_kernel_surjective_of_prev_inverse
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn f σn hσΨ hΨσ (y - Ψsucc x0) hres_kernel
  refine ⟨x0 + xerr, ?_⟩
  -- The correction maps to the residual transition error, so adding it to the first lift gives `y`.
  calc
    Ψsucc (x0 + xerr) = Ψsucc x0 + Ψsucc xerr := by simp
    _ = Ψsucc x0 + (y - Ψsucc x0) := by rw [hxerr]
    _ = y := by abel

/-- Helper for Chap10 Lemma 10 139 4: once the verified stage-`1` and stage-`2` inverse data are fixed,
the remaining source-faithful local task is to correct the formally-smooth lift at stage
`n + 1` by a quotient automorphism of `P / J^(n + 1)`. -/
private theorem exists_successor_truncation_inverse {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∃ σsucc : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1),
      σsucc.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) ∧
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)).comp σsucc =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ (n + 1)) := by
  let Ψsucc :=
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (n + 1)
  let qJ :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qI :
      S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R] S ⧸ (RingHom.ker σ) ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  obtain ⟨τbar, hτbar⟩ :=
    formally_smooth_lift_of_truncation_inverse_descends
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn f σn hσΨ hΨσ
  let α :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
    τbar.comp Ψsucc
  have hα : qJ.comp α = qJ := by
    ext x
    -- Reduce the correction problem to the stage-`n` inverse through the descended lift `τbar`.
    calc
      qJ (α x) = (σn.comp qI) (Ψsucc x) := by
        exact congrArg (fun β ↦ β (Ψsucc x)) hτbar
      _ =
        σn ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) (qJ x)) := by
          exact congrArg σn <|
            AlgHom.congr_fun
              (cotangent_lift_truncated_map_compatible
                (R := R) (S := S) (σ := σ) f (m := n) (n := n + 1) (Nat.le_succ n))
              x
      _ = qJ x := by
        exact AlgHom.congr_fun hσΨ (qJ x)
  have hα_factorPow :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) := by
    -- The correction API is stated with `factorPow`; this is the same reduction map as `qJ`.
    change qJ.toRingHom.comp α.toRingHom = qJ.toRingHom
    exact congrArg AlgHom.toRingHom hα
  have hn0 : 0 < n := lt_of_lt_of_le (by simp) hn
  let β :
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
    truncation_selfmap_correction
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow
  have hβ :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp β =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) :=
    truncation_selfmap_correction_factorPow_comp
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow
  have hδ :
      ∀ i : Fin d,
        α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
              (MvPolynomial.X i) ∈
          Ideal.map
            (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
            (MvPolynomial.idealOfVars (Fin d) R) := by
    intro i
    exact truncation_selfmap_variable_error_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 α hα_factorPow i
  have hΨsucc_surj : Function.Surjective Ψsucc :=
    cotangent_lift_truncated_map_surjective_of_prev_inverse
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn f σn hσΨ hΨσ
  -- Route correction: the stalled variable-by-variable cancellation was too weak. The source proof
  -- needs the stronger invariant that `β` and `α` fix the whole transition piece `J^n / J^(n+1)`.
  have hβ_comp :
      β.comp α =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := by
    exact (truncation_selfmap_correction_comp_self
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) hn α hα_factorPow).1
  let σsucc :
      S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
    β.comp τbar
  have hσsuccΨ : σsucc.comp Ψsucc =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := by
    -- The corrected lift has left composite `β ∘ α`, and the correction lemma makes this the
    -- identity on the polynomial truncation.
    calc
      σsucc.comp Ψsucc = (β.comp τbar).comp Ψsucc := by rfl
      _ = β.comp (τbar.comp Ψsucc) := by rw [AlgHom.comp_assoc]
      _ = β.comp α := by rfl
      _ = AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := hβ_comp
  refine ⟨σsucc, hσsuccΨ, ?_⟩
  ext y
  rcases hΨsucc_surj y with ⟨x, rfl⟩
  -- Surjectivity of `Ψsucc` upgrades the left inverse into the right inverse pointwise.
  exact congrArg Ψsucc (AlgHom.congr_fun hσsuccΨ x)

omit hσ in
/-- Helper for Chap10 Lemma 10 139 4: once the stagewise two-sided inverses are available, compatibility
of the inverse family follows formally from the already-known compatibility of `Ψtrunc`. -/
private theorem truncation_inverses_compatible_of_two_sided {d : ℕ}
    (f : Fin d → RingHom.ker σ)
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ : ∀ n,
      (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n,
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
        (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
  intro m n hmn
  ext x
  -- Rewrite both sides through `Ψtrunc m`; its left inverse `σtrunc m` then reduces the
  -- compatibility check to the already-known compatibility of the forward truncation maps.
  calc
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x) =
      (σtrunc m)
        ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x))) := by
            symm
            exact AlgHom.congr_fun (hσΨ m)
              ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) ((σtrunc n) x))
    _ = (σtrunc m)
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) ((σtrunc n) x))) := by
            congr 1
            exact (AlgHom.congr_fun
              (cotangent_lift_truncated_map_compatible
                (R := R) (S := S) (σ := σ) f (m := m) (n := n) hmn)
              ((σtrunc n) x)).symm
    _ = (σtrunc m)
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) x) := by
            congr 1
            exact congrArg
              (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
              (AlgHom.congr_fun (hΨσ n) x)

/-- Helper for Chap10 Lemma 10 139 4: once the verified stage-`1` and stage-`2` inverse data are fixed,
the remaining source-faithful task is to extend them to a compatible inverse family on all
truncations. -/
private theorem exists_truncation_inverse_family {d : ℕ}
    (f : Fin d → RingHom.ker σ)
    (σ1 :
      S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1)
    (hσ1Ψ :
      σ1.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1))
    (hΨ1σ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp σ1 =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1))
    (σ2 :
      S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    (hσ2 :
      σ2.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ∧
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2).comp σ2 =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2)) :
    ∃ σtrunc : (n : ℕ) →
        S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
          MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n,
      (∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) ∧
      (∀ n,
        (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
          AlgHom.id R
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)) ∧
      (∀ n,
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
          AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) := by
  classical
  have hstage :
      ∀ k : ℕ,
        ∃ σk : S ⧸ (RingHom.ker σ) ^ (k + 2) →ₐ[R]
            MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (k + 2),
          (σk.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (k + 2)) =
              AlgHom.id R
                (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (k + 2))) ∧
            ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f (k + 2)).comp σk =
              AlgHom.id R (S ⧸ (RingHom.ker σ) ^ (k + 2))) := by
    intro k
    induction k with
    | zero =>
        exact ⟨σ2, hσ2⟩
    | succ k ih =>
        rcases ih with ⟨σk, hσk⟩
        exact exists_successor_truncation_inverse
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := k + 2) (by omega) f σk hσk.1 hσk.2
  let σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n
    | 0 => by
        letI :
            Subsingleton
              (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 0) := by
          simp
        exact default
    | 1 => σ1
    | k + 2 => Classical.choose (hstage k)
  have hσΨtrunc : ∀ n,
      (σtrunc n).comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    intro n
    cases n with
    | zero =>
        letI :
            Subsingleton
              (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 0) := by
          simpa using
            (inferInstance :
              Subsingleton (MvPolynomial (Fin d) R ⧸ (⊤ : Ideal (MvPolynomial (Fin d) R))))
        ext x
        exact Subsingleton.elim _ _
    | succ n =>
        cases n with
        | zero =>
            simpa [σtrunc] using hσ1Ψ
        | succ k =>
            simpa [σtrunc] using (Classical.choose_spec (hstage k)).1
  have hΨσtrunc : ∀ n,
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp (σtrunc n) =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n) := by
    intro n
    cases n with
    | zero =>
        letI : Subsingleton (S ⧸ (RingHom.ker σ) ^ 0) := by
          simpa using (inferInstance : Subsingleton (S ⧸ (⊤ : Ideal S)))
        ext x
        exact Subsingleton.elim _ _
    | succ n =>
        cases n with
        | zero =>
            simpa [σtrunc] using hΨ1σ
        | succ k =>
            simpa [σtrunc] using (Classical.choose_spec (hstage k)).2
  have hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) :=
    truncation_inverses_compatible_of_two_sided
      (R := R) (S := S) (σ := σ) f σtrunc hσΨtrunc hΨσtrunc
  -- Route correction: keep the stagewise construction and the compatibility proof separate.
  -- The only remaining substantive source-faithful blocker is the successor-step correction
  -- isolated in `exists_successor_truncation_inverse`.
  exact ⟨σtrunc, hσtrunc, hσΨtrunc, hΨσtrunc⟩

-- Proof sketch: choose a finite basis of `(RingHom.ker σ).Cotangent`, lift basis
-- vectors to elements of `ker σ`, and use formal smoothness of `S` over `R` to build compatible
-- inverses modulo successive powers of `ker σ`; the induced map from a multivariable formal power
-- series ring is then an `R`-algebra isomorphism onto the `ker σ`-adic completion.
/-- If the conormal module attached to a smooth retraction is free over `R`, then the
`ker σ`-adic completion of `S` is isomorphic, as an `R`-algebra, to a formal power series ring in
finitely many variables over `R`. -/
theorem smooth_section_adicCompletion_exists_algEquiv_mvPowerSeries
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ d : ℕ,
      Nonempty ((AdicCompletion (RingHom.ker σ) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := by
  -- Route correction: the source proof first fixes a finite basis of `I/I²` and lifts it to
  -- elements of `I`; we record exactly that data before attempting any quotient-by-powers step.
  obtain ⟨d, b, f, hf⟩ :=
    exists_cotangent_fin_basis_and_lifts (R := R) (S := S) (σ := σ) hσ hfree
  let Ψ : MvPolynomial (Fin d) R →ₐ[R] S :=
    cotangent_lift_polynomial_map (R := R) (S := S) (σ := σ) f
  let Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n :=
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f
  have hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
    intro m n hmn
    exact cotangent_lift_truncated_map_compatible
      (R := R) (S := S) (σ := σ) f hmn
  let σ2 :
      S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
    trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b
  have hσ2 :
      σ2.comp (Ψtrunc 2) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ∧
      (Ψtrunc 2).comp σ2 = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2) := by
    -- The explicit level-`2` inverse is the formal base case for the textbook induction.
    simpa [σ2] using
      trunc_two_inverse_via_trivSqZero_models_spec
        (R := R) (S := S) (σ := σ) hσ b f hf
  let σ1 :
      S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1 :=
    smooth_section_stageOne_inverse_powOne (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  have hσ1Ψ :
      σ1.comp (Ψtrunc 1) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
    -- The transported stage-`1` inverse gives the forward base case of the induction.
    simpa [σ1, Ψtrunc] using
      smooth_section_stageOne_inverse_powOne_spec
        (R := R) (S := S) (σ := σ) hσ (d := d) f
  have hΨ1σ :
      (Ψtrunc 1).comp σ1 = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1) := by
    -- The same transported stage-`1` inverse also closes the reverse base case.
    simpa [σ1, Ψtrunc] using
      smooth_section_stageOne_inverse_powOne_spec_symm
        (R := R) (S := S) (σ := σ) hσ (d := d) f
  obtain ⟨σtrunc, hσtrunc, hσΨ, hΨσ⟩ :=
    exists_truncation_inverse_family (R := R) (S := S) (σ := σ) (hσ := hσ)
      f σ1 hσ1Ψ hΨ1σ σ2 hσ2
  -- Once the quotient-level inverse family is available, the completion comparison theorem closes
  -- the source proof immediately.
  exact ⟨d,
    completion_equiv_of_truncation_inverses (R := R) (S := S) (σ := σ) (hσ := hσ)
      Ψtrunc hΨtrunc σtrunc hσtrunc hσΨ hΨσ⟩

end SmoothSection

end
