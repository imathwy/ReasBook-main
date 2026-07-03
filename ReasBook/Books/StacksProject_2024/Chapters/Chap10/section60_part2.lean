import Mathlib
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.TFAE
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_60_9 (from Chap10) -/
universe u

open IsLocalRing
open Pointwise
open CategoryTheory
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Proposition 10.60.9: the quotient by an ideal of definition is Artinian. -/
lemma isArtinianRing_quotient_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    IsArtinianRing (R ⧸ I) := by
  -- A power of the maximal ideal lands inside an ideal of definition because its radical is
  -- already the maximal ideal.
  have hleRad : maximalIdeal R ≤ I.radical := by
    exact le_of_eq hI.symm
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hleRad (IsNoetherian.noetherian (maximalIdeal R))
  let S := R ⧸ I
  have hI_ne_top : I ≠ ⊤ := by
    intro htop
    have hrad : I.radical = ⊤ := by
      rw [htop]
      simp
    have hmax : maximalIdeal R = ⊤ := hI.symm.trans hrad
    exact (maximalIdeal.isMaximal R).ne_top hmax
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (maximalIdeal S) := by
    -- The image maximal ideal in the quotient is nilpotent because a power of `𝔪` is killed.
    refine ⟨n, ?_⟩
    rw [← hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hn
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal S).mpr hnil

/-- Helper for Proposition 10.60.9: any finite upper bound on `ringKrullDim R` identifies it with
an actual natural number. -/
lemma ringKrullDim_eq_nat_of_le {d : ℕ} (h : ringKrullDim R ≤ d) :
    ∃ n : ℕ, n ≤ d ∧ ringKrullDim R = n := by
  -- Convert the finite-dimensional bound into an actual natural-valued Krull dimension.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim : ringKrullDim R = n := by
    have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
      simpa [n] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim R = (ringKrullDim R).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
      _ = n := hdim'
  refine ⟨n, ?_, hdim⟩
  simpa [hdim] using h

/-- Helper for Proposition 10.60.9: a `d`-generated ideal of definition forces
`ringKrullDim R ≤ d`. -/
lemma ringKrullDim_le_of_exists_parameterIdeal {d : ℕ}
    (h : ∃ x : Fin d → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) :
    ringKrullDim R ≤ d := by
  rcases h with ⟨x, hx⟩
  let I : Ideal R := parameterIdeal x
  have hI_le_max : I ≤ maximalIdeal R := by
    -- The parameter ideal is spanned by elements already lying in the maximal ideal.
    rw [show I = parameterIdeal x by rfl, parameterIdeal_eq_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (x i).2
  have hdim_quot : ringKrullDim (R ⧸ I) ≤ 0 := by
    -- Quotienting by an ideal of definition produces an Artinian local ring.
    letI : IsArtinianRing (R ⧸ I) :=
      isArtinianRing_quotient_of_isIdealOfDefinition (R := R) (I := I) hx
    exact (Ring.krullDimLE_iff (R := R ⧸ I) (n := 0)).mp <|
      (isArtinianRing_iff_krullDimLE_zero (R := R ⧸ I)).mp inferInstance
  have hrange_ncard :
      (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R)).ncard ≤ d := by
    -- The range of a `Fin d`-indexed family has at most `d` elements.
    rw [← Nat.card_coe_set_eq]
    simpa using
      (Finite.card_range_le (fun i : Fin d ↦ ((x i : maximalIdeal R) : R)))
  have hspan : I.spanFinrank ≤ d := by
    -- A span of at most `d` elements has span-finrank at most `d`.
    calc
      I.spanFinrank =
          (Ideal.span (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R))).spanFinrank := by
            rw [show I = parameterIdeal x by rfl, parameterIdeal_eq_span]
      _ ≤ (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R)).ncard := by
            exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ d := hrange_ncard
  have hjac : I ≤ Ring.jacobson R := by
    exact hI_le_max.trans <|
      by simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  -- Krull dimension is bounded by quotient dimension plus the span-finrank of the cut ideal.
  calc
    ringKrullDim R ≤ ringKrullDim (R ⧸ I) + I.spanFinrank := by
      exact ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hjac
    _ ≤ (0 : WithBot ℕ∞) + d := by
      exact add_le_add hdim_quot (by exact_mod_cast hspan)
    _ = d := by simp

/-- Helper for Proposition 10.60.9: if `dim R = d`, then no shorter parameter family can generate
an ideal of definition. -/
lemma not_exists_parameterIdeal_of_lt_ringKrullDim {d n : ℕ}
    (hdim : ringKrullDim R = d) (hn : n < d) :
    ¬ ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition := by
  intro h
  have hle : ringKrullDim R ≤ n :=
    ringKrullDim_le_of_exists_parameterIdeal (R := R) h
  have : d ≤ n := by
    simpa [hdim] using hle
  exact Nat.not_le_of_gt hn this

/-- Helper for Proposition 10.60.9: if `x` lies in the maximal ideal and avoids every minimal
prime of `R`, then quotienting by `(x)` lowers the Krull dimension by exactly one. -/
lemma quotient_span_singleton_ringKrullDim_drop_of_avoids_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  -- Identify `R ⧸ (x)` with the canonical owner quotient `QuotSMulTop x R`.
  have hspan : Ideal.span ({x} : Set R) = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have hmin' : ∀ p ∈ (Module.annihilator R R).minimalPrimes, x ∉ p := by
    simpa [hann, minimalPrimes] using hmin
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    hmin' hx

/-- Helper for Proposition 10.60.9: if the Krull dimension is positive, then the maximal ideal
contains an element outside every minimal prime. -/
lemma exists_mem_maximalIdeal_avoiding_minimalPrimes (hpos : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, ∀ p ∈ minimalPrimes R, x ∉ p := by
  let U : Set R := ⋃ p ∈ minimalPrimes R, (p : Set R)
  have hnot_subset : ¬ (maximalIdeal R : Set R) ⊆ U := by
    intro hsubset
    obtain ⟨p, hp, hmp⟩ :=
      ((maximalIdeal R).subset_union_prime_finite
        (minimalPrimes.finite_of_isNoetherianRing R) (maximalIdeal R) (maximalIdeal R)
        fun p hp _ _ ↦ Ideal.minimalPrimes_isPrime hp).mp hsubset
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    have hpeq : p = maximalIdeal R := by
      refine le_antisymm ?_ hmp
      exact le_maximalIdeal Ideal.IsPrime.ne_top'
    have hpheight : (maximalIdeal R).primeHeight = 0 := by
      simpa [hpeq] using (Ideal.primeHeight_eq_zero_iff (I := p)).2 hp
    have hheight : (maximalIdeal R).height = 0 := by
      simpa [Ideal.height_eq_primeHeight (I := maximalIdeal R)] using hpheight
    have hheight' : ↑(maximalIdeal R).height = (0 : WithBot ℕ∞) := by
      exact_mod_cast hheight
    have hzero : ringKrullDim R = 0 := by
      calc
        ringKrullDim R = ↑(maximalIdeal R).height := by
          exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
        _ = 0 := hheight'
    exact (ne_of_gt hpos) hzero
  obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot_subset
  refine ⟨x, hx, ?_⟩
  intro p hp hxp
  exact hxnot <| Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hxp⟩⟩

/-- Helper for Proposition 10.60.9: a parameter ideal in `R / (x)` lifts to a parameter ideal in
`R` after adjoining `x`. -/
lemma exists_parameterIdeal_cons_of_quotient {d : ℕ} {x : R} (hx : x ∈ maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))]
    [IsNoetherianRing (R ⧸ Ideal.span ({x} : Set R))]
    {xbar : Fin d → maximalIdeal (R ⧸ Ideal.span ({x} : Set R))}
    (hbar : (parameterIdeal xbar).IsIdealOfDefinition) :
    ∃ y : Fin d → maximalIdeal R,
      (parameterIdeal (Fin.cons ⟨x, hx⟩ y)).IsIdealOfDefinition := by
  classical
  let I : Ideal R := Ideal.span ({x} : Set R)
  let S := R ⧸ I
  have hI_le_max : I ≤ maximalIdeal R := by
    -- The principal ideal `(x)` lies in the maximal ideal because `x` does.
    dsimp [I]
    exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
  have hmap_max :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal S := by
    -- The quotient map is a surjective local map, so it carries `𝔪_R` onto `𝔪_S`.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hlift :
      ∀ i : Fin d, ∃ r : R, r ∈ maximalIdeal R ∧ Ideal.Quotient.mk I r = (xbar i : S) := by
    intro i
    have hmem : (xbar i : S) ∈ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
      simpa [S, hmap_max] using (xbar i).2
    simpa [S] using
      (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
        (hf := Ideal.Quotient.mk_surjective) (I := maximalIdeal R) (y := (xbar i : S))).1 hmem
  choose r hr_mem hr_eq using hlift
  let y : Fin d → maximalIdeal R := fun i ↦ ⟨r i, hr_mem i⟩
  have hI_le_parameter :
      I ≤ parameterIdeal (Fin.cons ⟨x, hx⟩ y) := by
    -- The adjoined parameter ideal contains the distinguished element `x`.
    dsimp [I]
    exact (Ideal.span_singleton_le_iff_mem
      (I := parameterIdeal (Fin.cons ⟨x, hx⟩ y)) (x := x)).2 <|
      Ideal.subset_span ⟨0, rfl⟩
  have hmap_parameter :
      Ideal.map (Ideal.Quotient.mk I) (parameterIdeal (Fin.cons ⟨x, hx⟩ y)) =
        parameterIdeal xbar := by
    apply le_antisymm
    · -- The quotient image is generated by the lifted tail, while the adjoined `x` dies.
      rw [Ideal.map_le_iff_le_comap, parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Ideal.mem_comap.2 ?_
      refine Fin.cases ?_ ?_ j
      · simp [I, parameterIdeal_eq_span]
      · intro i
        change (Ideal.Quotient.mk I) (((y i : maximalIdeal R) : R)) ∈ parameterIdeal xbar
        rw [show Ideal.Quotient.mk I (((y i : maximalIdeal R) : R)) =
            ((xbar i : maximalIdeal S) : S) by
            simpa [S, y] using hr_eq i]
        exact Ideal.subset_span ⟨i, rfl⟩
    · -- Every quotient generator comes from the chosen lift in the adjoined parameter ideal.
      rw [parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hy_mem :
          (((y i : maximalIdeal R) : R)) ∈ parameterIdeal (Fin.cons ⟨x, hx⟩ y) := by
        rw [parameterIdeal_eq_span]
        exact Ideal.subset_span ⟨i.succ, rfl⟩
      have hy_map_mem :
          ((xbar i : maximalIdeal S) : S) ∈
            Ideal.map (Ideal.Quotient.mk I) (parameterIdeal (Fin.cons ⟨x, hx⟩ y)) := by
        refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
          (hf := Ideal.Quotient.mk_surjective)
          (I := parameterIdeal (Fin.cons ⟨x, hx⟩ y))
          (y := ((xbar i : maximalIdeal S) : S))).2 ?_
        refine ⟨((y i : maximalIdeal R) : R), hy_mem, ?_⟩
        simpa [S, y] using hr_eq i
      simpa using hy_map_mem
  refine ⟨y, ?_⟩
  -- Pull the quotient ideal-of-definition statement back along the quotient map.
  calc
    (parameterIdeal (Fin.cons ⟨x, hx⟩ y)).radical
        = Ideal.comap (Ideal.Quotient.mk I)
            ((Ideal.map (Ideal.Quotient.mk I)
              (parameterIdeal (Fin.cons ⟨x, hx⟩ y))).radical) := by
              rw [Ideal.comap_radical, Ideal.comap_map_mk hI_le_parameter]
    _ = Ideal.comap (Ideal.Quotient.mk I) ((parameterIdeal xbar).radical) := by
          rw [hmap_parameter]
    _ = Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal S) := by rw [hbar]
    _ = maximalIdeal R := by
          rw [← hmap_max, Ideal.comap_map_mk hI_le_max]

/-- Helper for Proposition 10.60.9: the source induction must quantify over the ambient local
Noetherian ring, because the recursive step lives in a quotient ring. -/
lemma exists_parameterIdeal_of_ringKrullDim_eq_aux :
    ∀ d : ℕ, ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      ringKrullDim A = d →
        ∃ x : Fin d → maximalIdeal A, (parameterIdeal x).IsIdealOfDefinition
  | 0, A, _, _, _, hdim => by
      have hdim_le : ringKrullDim A ≤ 0 := by
        simpa [hdim] using (show ((0 : ℕ) : WithBot ℕ∞) ≤ (0 : WithBot ℕ∞) by simp)
      letI : Ring.KrullDimLE 0 A := (Ring.krullDimLE_iff (R := A) (n := 0)).2 hdim_le
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      -- In dimension zero the empty parameter family generates `(0)`, whose radical is the
      -- maximal ideal.
      rw [Ideal.IsIdealOfDefinition, parameterIdeal_eq_span]
      simpa using (Ring.KrullDimLE.nilradical_eq_maximalIdeal A)
  | d + 1, A, _, _, _, hdim => by
      have hpos : 0 < ringKrullDim A := by
        simpa [hdim] using
          (show (0 : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) by
            exact_mod_cast Nat.succ_pos d)
      obtain ⟨x, hx, havoid⟩ :=
        exists_mem_maximalIdeal_avoiding_minimalPrimes (R := A) hpos
      let I : Ideal A := Ideal.span ({x} : Set A)
      have hI_le_max : I ≤ maximalIdeal A := by
        dsimp [I]
        exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
      have hI_ne_top : I ≠ ⊤ := by
        intro htop
        have hmax : maximalIdeal A = ⊤ := top_le_iff.mp (htop ▸ hI_le_max)
        exact (maximalIdeal.isMaximal A).ne_top hmax
      letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
      letI : IsLocalRing (A ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hQdim_succ : ringKrullDim (A ⧸ I) + 1 = ringKrullDim A := by
        simpa [I] using
          quotient_span_singleton_ringKrullDim_drop_of_avoids_minimalPrimes
            (R := A) hx havoid
      have hQdim : ringKrullDim (A ⧸ I) = d := by
        have hQ_ne_bot : ringKrullDim (A ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
        let qd : ℕ∞ := (ringKrullDim (A ⧸ I)).unbot hQ_ne_bot
        have hqd_succ : qd + 1 = d + 1 := by
          apply WithBot.coe_eq_coe.mp
          calc
            (((qd + 1 : ℕ∞) : WithBot ℕ∞))
                = ringKrullDim (A ⧸ I) + 1 := by
                    simp [qd, WithBot.coe_unbot, hQ_ne_bot]
            _ = ringKrullDim A := hQdim_succ
            _ = (((d : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by simpa [hdim]
        have hQ_ne_top : ringKrullDim (A ⧸ I) ≠ ⊤ := ringKrullDim_ne_top
        have hqd_ne_top : qd ≠ ⊤ := by
          intro htop
          exact hQ_ne_top <| by
            calc
              ringKrullDim (A ⧸ I) = ((qd : ℕ∞) : WithBot ℕ∞) := by
                simpa [qd] using
                  (WithBot.coe_unbot (ringKrullDim (A ⧸ I)) hQ_ne_bot).symm
              _ = ⊤ := by simpa [htop]
        have hqd_toNat : qd.toNat = d := by
          have htoNat : qd.toNat + 1 = d + 1 := by
            simpa [ENat.toNat_add, hqd_ne_top] using congrArg ENat.toNat hqd_succ
          exact Nat.succ.inj htoNat
        have hqd_eq : qd = d := by
          calc
            qd = (qd.toNat : ℕ∞) := by
              simpa [hqd_ne_top] using (ENat.coe_toNat hqd_ne_top).symm
            _ = (d : ℕ∞) := by
              exact congrArg (fun n : ℕ ↦ (n : ℕ∞)) hqd_toNat
        calc
          ringKrullDim (A ⧸ I) = ((qd : ℕ∞) : WithBot ℕ∞) := by
            simpa [qd] using (WithBot.coe_unbot (ringKrullDim (A ⧸ I)) hQ_ne_bot).symm
          _ = ((d : ℕ∞) : WithBot ℕ∞) := by rw [hqd_eq]
      obtain ⟨xbar, hxbar⟩ :=
        exists_parameterIdeal_of_ringKrullDim_eq_aux d (A := A ⧸ I) hQdim
      -- Route correction: the earlier fixed-ring induction could not recurse in `A ⧸ (x)`. The
      -- ambient-ring statement fixes that and then lifts the quotient witness back to `A`.
      rcases exists_parameterIdeal_cons_of_quotient (R := A) hx hxbar with ⟨y, hy⟩
      exact ⟨Fin.cons ⟨x, hx⟩ y, hy⟩

/-- Helper for Proposition 10.60.9: a Noetherian local ring of dimension `d` admits an ideal of
definition generated by `d` elements. -/
lemma exists_parameterIdeal_of_ringKrullDim_eq {d : ℕ} (hdim : ringKrullDim R = d) :
    ∃ x : Fin d → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition := by
  -- Specialize the ambient-ring induction to the current ring `R`.
  exact exists_parameterIdeal_of_ringKrullDim_eq_aux d hdim

/-- Helper for Proposition 10.60.9: viewing a quotient ring as an `R`-module does not change its
Hilbert-Samuel degree. -/
lemma hilbertSamuelPolynomialDegree_eq_quotient_self {J : Ideal R}
    [IsLocalRing (R ⧸ J)] [IsNoetherianRing (R ⧸ J)] :
    hilbertSamuelPolynomialDegree R (R ⧸ J) =
      hilbertSamuelPolynomialDegree (R ⧸ J) (R ⧸ J) := by
  let S := R ⧸ J
  have hsurj : Function.Surjective (algebraMap R S) := by
    -- The quotient algebra map is the canonical surjection `R → R ⧸ J`.
    simpa [S, Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk J))
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := by
    -- The maximal ideal descends along any surjective local quotient map.
    exact IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  have hchi :
      ∀ n : ℕ, χ_(maximalIdeal R) S n = χ_(maximalIdeal S) S n := by
    intro n
    -- Compare the two Hilbert-Samuel quotients by identifying the pushed-forward maximal-ideal
    -- powers in the quotient ring.
    simp only [Ideal.hilbertSamuelChi]
    let K : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1))
    have hK :
        (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S)) = K.restrictScalars R := by
      simp [K, Ideal.smul_top_eq_map, Ideal.map_pow]
    calc
      Module.length R (S ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S))) =
          Module.length R (S ⧸ K.restrictScalars R) := by
            rw [hK]
      _ = Module.length R (S ⧸ K) := by
            exact LinearEquiv.length_eq (Submodule.Quotient.restrictScalarsEquiv R K)
      _ = Module.length S (S ⧸ K) := by
            rw [Module.length_eq_of_surjective hsurj]
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) : Ideal S)) := by
            have hK' : K = maximalIdeal S ^ (n + 1) := by
              change
                Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1)) =
                  maximalIdeal S ^ (n + 1)
              rw [Ideal.map_pow, hmap]
            rw [hK']
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) • (⊤ : Submodule S S))) := by
            rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let P := hilbertSamuelChiPolynomial S S
  have hP :
      ∀ᶠ n : ℕ in Filter.atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal S) S n).toNat : ℚ) :=
    hilbertSamuelChiPolynomial_eventuallyEq S S
  have hPR :
      ∀ᶠ n : ℕ in Filter.atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) S n).toNat : ℚ) := by
      -- Transport the eventual quotient-ring polynomial formula back to the ambient ring.
      filter_upwards [hP] with n hn
      simpa [hchi n] using hn
  -- Both Hilbert-Samuel degrees are the degree of the same eventual polynomial `P`.
  rw [hilbertSamuelPolynomialDegree_eq_degree R S hPR, hilbertSamuelPolynomialDegree]

/-- Helper for Proposition 10.60.9: if `x ∉ p` and `p` is prime, then the source term in the
standard colon exact sequence `0 → R/(p : x) → R/p → R/(p + (x)) → 0` is just `R/p`. -/
lemma prime_colon_span_singleton_eq_of_notMem {p : Ideal R} (hp : p.IsPrime) {x : R}
    (hx : x ∉ p) :
    p.colon (Ideal.span ({x} : Set R)) = p := by
  apply le_antisymm
  · intro y hy
    -- Read colon membership as `y * x ∈ p`, then primality and `x ∉ p` force `y ∈ p`.
    rw [Ideal.mem_colon_span_singleton] at hy
    exact (hp.mem_or_mem hy).resolve_right hx
  · -- Every ideal is contained in its own colon ideal.
    simpa using (Ideal.le_colon (I := p) (S := ({x} : Set R)))

/-- Helper for Proposition 10.60.9: when `x ∉ p`, the left endpoint of the source colon exact
sequence is canonically the quotient `R ⧸ p`. -/
noncomputable def quotient_colon_span_singleton_endpoint_iso_of_prime_notMem {p : Ideal R}
    (hp : p.IsPrime) {x : R} (hxp : x ∉ p) :
    ModuleCat.of R (R ⧸ (p.colon (Ideal.span ({x} : Set R)))) ≅ ModuleCat.of R (R ⧸ p) :=
  ((Ideal.quotientEquivAlgOfEq R
      (prime_colon_span_singleton_eq_of_notMem (R := R) hp hxp)).toLinearEquiv).toModuleIso

/-- Helper for Proposition 10.60.9: precomposing the source colon short complex by the endpoint
identification preserves the zero-composition relation. -/
lemma prime_quotient_span_singleton_shortComplex_zero {p : Ideal R} (hp : p.IsPrime)
    {x : R} (hxp : x ∉ p) :
    (((quotient_colon_span_singleton_endpoint_iso_of_prime_notMem (R := R) hp hxp).inv ≫
        (quotient_colon_span_singleton_shortComplex p x).f) ≫
      (quotient_colon_span_singleton_shortComplex p x).g) = 0 := by
  -- First precompose the owner relation `f ≫ g = 0`, then reassociate back to the target shape.
  let e := quotient_colon_span_singleton_endpoint_iso_of_prime_notMem (R := R) hp hxp
  have hprecomp :
      e.inv ≫
          ((quotient_colon_span_singleton_shortComplex p x).f ≫
            (quotient_colon_span_singleton_shortComplex p x).g) =
        e.inv ≫ 0 := by
    exact congrArg (fun α => e.inv ≫ α)
      ((quotient_colon_span_singleton_shortComplex p x).zero)
  calc
    ((e.inv ≫ (quotient_colon_span_singleton_shortComplex p x).f) ≫
        (quotient_colon_span_singleton_shortComplex p x).g) =
        e.inv ≫
          ((quotient_colon_span_singleton_shortComplex p x).f ≫
            (quotient_colon_span_singleton_shortComplex p x).g) := by
          simp [Category.assoc]
    _ = e.inv ≫ 0 := hprecomp
    _ = 0 := by simp

/-- Helper for Proposition 10.60.9: transport the owner short complex from Example 10.28.7 to the
normalized endpoints `R ⧸ p`, `R ⧸ p`, and `R ⧸ (p + (x))`. -/
noncomputable def prime_quotient_span_singleton_shortComplex {p : Ideal R} (hp : p.IsPrime)
    {x : R} (hxp : x ∉ p) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    ((quotient_colon_span_singleton_endpoint_iso_of_prime_notMem (R := R) hp hxp).inv ≫
      (quotient_colon_span_singleton_shortComplex p x).f)
    ((quotient_colon_span_singleton_shortComplex p x).g)
    (prime_quotient_span_singleton_shortComplex_zero (R := R) hp hxp)

/-- Helper for Proposition 10.60.9: after identifying `(p : x)` with `p`, the source colon exact
sequence becomes a short exact sequence with endpoints `R ⧸ p`, `R ⧸ p`, and `R ⧸ (p + (x))`. -/
lemma prime_quotient_span_singleton_shortExact {p : Ideal R} (hp : p.IsPrime)
    {x : R} (hxp : x ∉ p) :
    (prime_quotient_span_singleton_shortComplex (R := R) hp hxp).ShortExact := by
  let S := quotient_colon_span_singleton_shortComplex p x
  let e₁ := quotient_colon_span_singleton_endpoint_iso_of_prime_notMem (R := R) hp hxp
  have hS : S.ShortExact := quotient_colon_span_singleton_shortExact p x
  have e :
      S ≅ prime_quotient_span_singleton_shortComplex (R := R) hp hxp := by
    refine ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _) ?_ ?_
    · -- The normalized left differential is exactly the source one after conjugating by `e₁`.
      change e₁.hom ≫ e₁.inv ≫ S.f = S.f
      simpa using (Iso.hom_inv_id_assoc e₁ S.f)
    · -- The middle-to-right differential is unchanged by the normalization.
      simp [S, prime_quotient_span_singleton_shortComplex]
  exact ShortComplex.shortExact_of_iso e hS

/-- Helper for Proposition 10.60.9: if `p < q` are prime ideals in a local ring, then the
prime quotient `R ⧸ p` cannot have finite length as an `R`-module. -/
lemma quotient_prime_not_isFiniteLength_of_lt_overprime {p q : Ideal R}
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    ¬ IsFiniteLength R (R ⧸ p) := by
  intro hfinite
  obtain ⟨n, hn⟩ :=
    exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength (R := R) (M := R ⧸ p) hfinite
  have hmap_bot : Ideal.map (Ideal.Quotient.mk p) (maximalIdeal R ^ n) = ⊥ := by
    -- Route correction: convert the finite-length annihilation statement into an ideal inclusion
    -- by rewriting `𝔪^n • ⊤` as the mapped ideal in the quotient.
    simpa [Ideal.smul_top_eq_map, Ideal.zero_eq_bot] using hn
  have hpow_le : maximalIdeal R ^ n ≤ p := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hmap_bot
    exact hmap_bot
  have hmax_le : maximalIdeal R ≤ p := by
    -- Every element of `𝔪` has its `n`th power in `p`, hence already lies in `p`.
    intro y hy
    exact hp.mem_of_pow_mem n <| hpow_le <| Ideal.pow_mem_pow hy n
  have hpeq : p = maximalIdeal R := by
    exact le_antisymm (le_maximalIdeal hp.ne_top) hmax_le
  have hq_le : q ≤ maximalIdeal R := le_maximalIdeal hq.ne_top
  exact hpq.not_ge <| by simpa [hpeq] using hq_le

/-- Helper for Proposition 10.60.9: a prime quotient with a strictly larger overprime has
positive Hilbert-Samuel degree. -/
lemma zero_lt_hilbertSamuelPolynomialDegree_of_prime_lt_overprime {p q : Ideal R}
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    0 < hilbertSamuelPolynomialDegree R (R ⧸ p) := by
  -- The overprime witness rules out finite length, so the Hilbert-Samuel polynomial has positive
  -- degree by the canonical degree-positivity criterion.
  exact Ideal.degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
    (R := R) (M := R ⧸ p) (I := maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition
    (quotient_prime_not_isFiniteLength_of_lt_overprime (R := R) hp hq hpq)
    (hilbertSamuelChiPolynomial_eventuallyEq R (R ⧸ p))

/-- Helper for Proposition 10.60.9: in the source short exact sequence
`0 → R / p --x→ R / p → R / (p + (x)) → 0`, the last term has strictly smaller
Hilbert-Samuel degree once `x ∈ q \ p` for some overprime `q > p`. -/
lemma prime_quotient_colon_shortExact_degree_drop {p q : Ideal R}
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) {x : R}
    (hxq : x ∈ q) (hxp : x ∉ p) :
    hilbertSamuelPolynomialDegree R (R ⧸ (p ⊔ Ideal.span ({x} : Set R))) <
      hilbertSamuelPolynomialDegree R (R ⧸ p) := by
  -- Route correction: normalize Example 10.28.7 first, then apply the Hilbert-Samuel degree-drop
  -- theorem to the transported short exact sequence instead of mixing transport with degree
  -- simplification in one step.
  let S : ShortComplex (ModuleCat R) :=
    prime_quotient_span_singleton_shortComplex (R := R) hp hxp
  have hS : S.ShortExact :=
    prime_quotient_span_singleton_shortExact (R := R) hp hxp
  letI : Module.Finite R ↑S.X₁ := by
    change Module.Finite R (R ⧸ p)
    infer_instance
  letI : Module.Finite R ↑S.X₂ := by
    change Module.Finite R (R ⧸ p)
    infer_instance
  letI : Module.Finite R ↑S.X₃ := by
    change Module.Finite R (R ⧸ (p ⊔ Ideal.span ({x} : Set R)))
    infer_instance
  let P : Polynomial ℚ := hilbertSamuelChiPolynomial R (R ⧸ p)
  let Q : Polynomial ℚ :=
    hilbertSamuelChiPolynomial R (R ⧸ (p ⊔ Ideal.span ({x} : Set R)))
  have hP :
      ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) = ((χ_(maximalIdeal R) (R ⧸ p) n).toNat : ℚ) := by
    simpa [P] using hilbertSamuelChiPolynomial_eventuallyEq R (R ⧸ p)
  have hQ :
      ∀ᶠ n : ℕ in Filter.atTop,
        Q.eval (n : ℚ) = ((χ_(maximalIdeal R) (R ⧸ (p ⊔ Ideal.span ({x} : Set R))) n).toNat : ℚ) := by
    simpa [Q] using
      hilbertSamuelChiPolynomial_eventuallyEq R (R ⧸ (p ⊔ Ideal.span ({x} : Set R)))
  have hdrop :
      (P - Q - P).degree < P.degree := by
    exact
      (hilbertSamuelChi_difference_degree_lt_of_shortExact
        (R := R) (I := maximalIdeal R) (S := S) (P₁ := P) (P₂ := P) (P₃ := Q)
        Ideal.maximalIdeal_isIdealOfDefinition hS hP hP hQ
        (quotient_prime_not_isFiniteLength_of_lt_overprime (R := R) hp hq hpq)).2
  have hrewrite : P - Q - P = -Q := by
    -- The identical middle/source polynomials cancel, leaving the negative target polynomial.
    ring
  have hneg : (-Q).degree < P.degree := by
    simpa [hrewrite] using hdrop
  have hdeg : Q.degree < P.degree := by
    simpa [Polynomial.degree_neg] using hneg
  have hleft :
      hilbertSamuelPolynomialDegree R (R ⧸ (p ⊔ Ideal.span ({x} : Set R))) = Q.degree :=
    hilbertSamuelPolynomialDegree_eq_degree (R := R)
      (M := R ⧸ (p ⊔ Ideal.span ({x} : Set R))) (P := Q) hQ
  have hright : hilbertSamuelPolynomialDegree R (R ⧸ p) = P.degree :=
    hilbertSamuelPolynomialDegree_eq_degree (R := R) (M := R ⧸ p) (P := P) hP
  simpa [hleft, hright] using hdeg

/-- Helper for Proposition 10.60.9: the tuple-based parameter ideal agrees with the canonical
list-based owner `Ideal.ofList` on the same generators. -/
lemma parameterIdeal_eq_idealOfList_ofFn {d : ℕ} (x : Fin d → maximalIdeal R) :
    Ideal.ofList (List.ofFn fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) = parameterIdeal x := by
  -- Rewrite both owners as spans of the same underlying finite family.
  rw [Ideal.ofList, parameterIdeal_eq_span]
  congr 1
  ext r
  constructor
  · intro hr
    rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Helper for Proposition 10.60.9: the `n`-th power of a parameter ideal is spanned by the
degree-`n` monomial weights in its generators. -/
lemma parameterIdeal_pow_eq_span_monomial_weight {d n : ℕ}
    (x : Fin d → maximalIdeal R) :
    (parameterIdeal x : Ideal R) ^ n =
      Ideal.span ((fun e : Fin d →₀ ℕ =>
        ∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) '' {e | e.degree = n}) := by
  -- Rewrite the power of a span using the canonical `Finsupp`-product description of set powers.
  rw [parameterIdeal_eq_span, Ideal.span, Submodule.span_pow, ← Set.image_univ,
    Finsupp.image_pow_eq_finsuppProd_image]
  simp

/-- Helper for Proposition 10.60.9: viewing an ideal multiple of a submodule inside the ambient
module agrees with the intrinsic ideal multiple in the submodule. -/
lemma submoduleOf_smul_eq_smul_top {M : Type u} [AddCommGroup M] [Module R M]
    (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = (J • (⊤ : Submodule R N)) := by
  -- Pull the ambient scalar multiple back along the subtype of `N`.
  simpa [Submodule.range_subtype] using
    (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
      (p := N) (I := J) (by simpa [Submodule.range_subtype]))

/-- Helper for Proposition 10.60.9: the degree-`n` exponent vectors in `d` variables are counted
by the stars-and-bars number `d.multichoose n`. -/
lemma parameterIdeal_degreeSubtype_card_eq_multichoose (d n : ℕ)
    [Fintype {e : Fin d →₀ ℕ // e.degree = n}] :
    Fintype.card {e : Fin d →₀ ℕ // e.degree = n} = d.multichoose n := by
  classical
  -- Convert degree-`n` exponent vectors into multisets of size `n` on `Fin d`.
  let e :
      {e : Fin d →₀ ℕ // e.degree = n} ≃ {P : Fin d → ℕ // ∑ i, P i = n} :=
    Finsupp.equivFunOnFinite.subtypeEquiv <| by
      intro f
      simp [Finsupp.degree_eq_sum]
  let _ : Fintype {P : Fin d → ℕ // ∑ i, P i = n} :=
    Fintype.ofEquiv (Sym (Fin d) n) (Sym.equivNatSumOfFintype (Fin d) n)
  calc
    Fintype.card {e : Fin d →₀ ℕ // e.degree = n}
        = Fintype.card {P : Fin d → ℕ // ∑ i, P i = n} := Fintype.card_congr e
    _ = Fintype.card (Sym (Fin d) n) := by
          exact Fintype.card_congr (Sym.equivNatSumOfFintype (Fin d) n).symm
    _ = d.multichoose n := by
          simpa using (Sym.card_sym_eq_multichoose (Fin d) n)

/-- Helper for Proposition 10.60.9: a degree-`n` parameter monomial already lies in the `n`th
power of the parameter ideal. -/
lemma parameterIdeal_monomial_weight_mem_pow {d n : ℕ}
    (x : Fin d → maximalIdeal R) (e : Fin d →₀ ℕ) (he : e.degree = n) :
    (∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) ∈ (parameterIdeal x : Ideal R) ^ n := by
  -- Rewrite the power as the span of all degree-`n` monomial weights and insert the chosen
  -- monomial as one of those generators.
  rw [parameterIdeal_pow_eq_span_monomial_weight (x := x) (n := n)]
  exact Ideal.subset_span ⟨e, by simp [he]⟩

/-- Helper for Proposition 10.60.9: multiplying a degree-`n` parameter monomial by an element of
the parameter ideal lands in the `(n + 1)`st power. -/
lemma parameterIdeal_mul_monomial_weight_mem_pow_succ {d n : ℕ}
    (x : Fin d → maximalIdeal R) {e : Fin d →₀ ℕ} (he : e.degree = n) {r : R}
    (hr : r ∈ parameterIdeal x) :
    r * (∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) ∈
      (parameterIdeal x : Ideal R) ^ (n + 1) := by
  let I : Ideal R := parameterIdeal x
  have hm :
      (∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) ∈ (I : Ideal R) ^ n := by
    -- The monomial term is one of the degree-`n` generators of `I ^ n`.
    simpa [I] using parameterIdeal_monomial_weight_mem_pow (R := R) x e he
  have hmul : r * (∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) ∈ I * I ^ n := by
    -- Products of an element of `I` with an element of `I ^ n` land in the ideal product.
    exact Ideal.mul_mem_mul hr hm
  -- Normalize the ideal product to the canonical power notation.
  simpa [I, pow_succ'] using hmul

/-- Helper for Proposition 10.60.9: the `n`-th Hilbert-Samuel `φ`-value of a `d`-generated
parameter ideal is bounded by the number of degree-`n` monomials times the residue-field length
of `R ⧸ I`. -/
lemma hilbertSamuelPhi_toNat_le_multichoose_mul_length_of_parameterIdeal {d n : ℕ}
    (x : Fin d → maximalIdeal R) (hx : (parameterIdeal x).IsIdealOfDefinition) :
    (φ_ (parameterIdeal x) R n).toNat ≤
      d.multichoose n * (Module.length R (R ⧸ parameterIdeal x)).toNat := by
  classical
  let I : Ideal R := parameterIdeal x
  let σ : Type := {e : Fin d →₀ ℕ // e.degree = n}
  let eσ : σ ≃ {P : Fin d → ℕ // ∑ i, P i = n} :=
    Finsupp.equivFunOnFinite.subtypeEquiv <| by
      intro f
      simp [Finsupp.degree_eq_sum]
  let _ : Fintype σ :=
    Fintype.ofEquiv (Sym (Fin d) n) ((Sym.equivNatSumOfFintype (Fin d) n).trans eσ.symm)
  let A : Submodule R R := I ^ n • (⊤ : Submodule R R)
  let B : Submodule R R := I ^ (n + 1) • (⊤ : Submodule R R)
  let q : Submodule R A := B.submoduleOf A
  let w : σ → R := fun e ↦ ∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e.1 i
  have hrange :
      ((fun e : Fin d →₀ ℕ ↦ ∏ i : Fin d, ((x i : maximalIdeal R) : R) ^ e i) ''
        {e | e.degree = n}) = Set.range w := by
    ext r
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
  have hwA : ∀ e : σ, w e ∈ A := by
    intro e
    -- Each degree-`n` monomial lies in the `n`th ideal power.
    simpa [A, I, w, Ideal.smul_eq_mul, Ideal.mul_top] using
      parameterIdeal_monomial_weight_mem_pow (R := R) x e.1 e.2
  have hf_mem : ∀ e : σ, ∀ r : R, ((LinearMap.id : R →ₗ[R] R).smulRight (w e)) r ∈ A := by
    intro e r
    -- Multiplying any scalar by a generator already in `A` stays inside `A`.
    exact A.smul_mem r (hwA e)
  let f : σ → R →ₗ[R] A := fun e ↦
    LinearMap.codRestrict A (((LinearMap.id : R →ₗ[R] R).smulRight (w e))) (hf_mem e)
  have hf : ∀ e : σ, I ≤ q.comap (f e) := by
    intro e r hr
    -- Coefficients coming from `I` land in the next power, hence vanish in the graded quotient.
    change (((f e) r : A) : R) ∈ B
    simpa [f, B, I, w, Ideal.smul_eq_mul, Ideal.mul_top] using
      parameterIdeal_mul_monomial_weight_mem_pow_succ
        (R := R) (x := x) (e := e.1) e.2 hr
  let g : (σ → R ⧸ I) →ₗ[R] A ⧸ q :=
    Submodule.piQuotientLift (fun _ : σ ↦ I) q f hf
  have hg_surj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective q z
    have hy : (y : R) ∈ (I : Ideal R) ^ n := by
      -- Representatives of the quotient lie in the source filtered piece `I ^ n`.
      simpa [A, Ideal.smul_eq_mul, Ideal.mul_top] using y.2
    have hy_span : (y : R) ∈ Ideal.span (Set.range w) := by
      -- Rewrite `I ^ n` as the span of degree-`n` parameter monomials.
      rw [parameterIdeal_pow_eq_span_monomial_weight (x := x) (n := n)] at hy
      simpa [I, hrange] using hy
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (R := R) (v := w) (x := (y : R))).1 hy_span
    refine ⟨fun e ↦ Ideal.Quotient.mk I (c e), ?_⟩
    have hsum : LinearMap.lsum R (fun _ : σ ↦ R) R f c = y := by
      -- The chosen coefficients reconstruct the representative exactly.
      ext
      simpa [f, w, LinearMap.lsum_apply, hc, smul_eq_mul] using hc
    have hg_eval :=
      Submodule.piQuotientLift_mk (p := fun _ : σ ↦ I) q f hf c
    rw [hsum] at hg_eval
    simpa [g] using hg_eval
  have hlen_le :
      Module.length R (A ⧸ q) ≤ Module.length R (σ → R ⧸ I) := by
    -- A surjection of finite-length modules gives an upper bound on length.
    exact Module.length_le_of_surjective (R := R) (M := (σ → R ⧸ I)) (P := A ⧸ q)
      (g := g) (hg := hg_surj)
  have hquot_ne : Module.length R (R ⧸ I) ≠ ⊤ := by
    -- Quotients by ideals of definition have finite length.
    have hfinite0 :=
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := R) I hx 0
    have hlen0 :
        Module.length R (R ⧸ (((I ^ 1) * ⊤ : Ideal R) : Submodule R R)) ≠ ⊤ := by
      simpa [Module.length_ne_top_iff] using hfinite0
    have hsub : ((((I ^ 1) * ⊤ : Ideal R) : Submodule R R)) = (I : Submodule R R) := by
      simp
    have hlen_eq :
        Module.length R (R ⧸ (((I ^ 1) * ⊤ : Ideal R) : Submodule R R)) =
          Module.length R (R ⧸ (I : Submodule R R)) := by
      simpa using (Submodule.quotEquivOfEq _ _ hsub).length_eq
    simpa using hlen_eq ▸ hlen0
  have hsource_ne : Module.length R (σ → R ⧸ I) ≠ ⊤ := by
    -- A finite product of finite-length quotients still has finite length.
    rw [Module.length_pi_of_fintype]
    exact ENat.sum_ne_top.2 fun _ _ ↦ hquot_ne
  have hsource_toNat :
      (Module.length R (σ → R ⧸ I)).toNat =
        Fintype.card σ * (Module.length R (R ⧸ I)).toNat := by
    -- The source is a finite product of identical factors.
    rw [Module.length_pi_of_fintype]
    rw [ENat.toNat_sum]
    · simp
    · intro _ _
      exact hquot_ne
  have hq :
      (I • (⊤ : Submodule R A)) = q := by
    -- The intrinsic denominator in `φ_I(n)` is exactly the pullback of `I ^ (n + 1)` to `I ^ n`.
    simpa [q, B, A, pow_succ', mul_smul] using
      (submoduleOf_smul_eq_smul_top (R := R) (M := R) I (I ^ n • (⊤ : Submodule R R))).symm
  have hphi : φ_ I R n = Module.length R (A ⧸ q) := by
    -- Rewrite the owner definition of `φ_I(n)` into the quotient used by the surjection.
    rw [Ideal.hilbertSamuelPhi]
    dsimp [A]
    rw [hq]
  have htoNat_le :
      (Module.length R (A ⧸ q)).toNat ≤ (Module.length R (σ → R ⧸ I)).toNat := by
    exact ENat.toNat_le_toNat hlen_le hsource_ne
  simpa [I] using
    calc
      (φ_ I R n).toNat = (Module.length R (A ⧸ q)).toNat := by rw [hphi]
      _ ≤ (Module.length R (σ → R ⧸ I)).toNat := htoNat_le
      _ = Fintype.card σ * (Module.length R (R ⧸ I)).toNat := hsource_toNat
      _ = d.multichoose n * (Module.length R (R ⧸ I)).toNat := by
        simpa [σ] using
          congrArg (fun m : ℕ ↦ m * (Module.length R (R ⧸ I)).toNat)
            (parameterIdeal_degreeSubtype_card_eq_multichoose (d := d) (n := n))

/-- Helper for Proposition 10.60.9: the initial Hilbert-Samuel `χ`-value of an ideal is the
length of the first quotient `R ⧸ I`. -/
lemma hilbertSamuelChi_zero_toNat (I : Ideal R) :
    (χ_ I R 0).toNat = (Module.length R (R ⧸ I)).toNat := by
  -- Unfold the zeroth `χ`-value and simplify the first ideal power.
  rw [Ideal.hilbertSamuelChi]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top]

/-- Helper for Proposition 10.60.9: for an ideal of definition, the Hilbert-Samuel `χ`-function
grows by the corresponding `φ`-value at each step. -/
lemma hilbertSamuelChi_succ_toNat_eq_add_hilbertSamuelPhi_toNat_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    (χ_ I R (n + 1)).toNat = (χ_ I R n).toNat + (φ_ I R (n + 1)).toNat := by
  let N : Submodule R R := I ^ (n + 1) • (⊤ : Submodule R R)
  let J : Submodule R R := I ^ (n + 2) • (⊤ : Submodule R R)
  have hJN : J ≤ N := by
    -- The adic filtration is decreasing.
    simpa [J, N] using Submodule.pow_smul_top_le I R (Nat.le_succ (n + 1))
  have hphi :
      Module.length R (N ⧸ J.submoduleOf N) = φ_ I R (n + 1) := by
    -- The successive quotient `I^(n+1) / I^(n+2)` is exactly the `φ`-owner quotient.
    have hsub :
        J.submoduleOf N = (I • (⊤ : Submodule R N)) := by
      simpa [J, N, pow_succ', mul_smul] using
        submoduleOf_smul_eq_smul_top (R := R) (M := R) I N
    rw [Ideal.hilbertSamuelPhi]
    simpa [N] using congrArg (fun S : Submodule R N ↦ Module.length R (N ⧸ S)) hsub
  have hdecomp :
      χ_ I R (n + 1) = χ_ I R n + Module.length R (N ⧸ J.submoduleOf N) := by
    -- Route correction: specialize the standard quotient decomposition to `M = R` and keep the
    -- Nat-cast step separate from the exact-length identity.
    have hchiPred : Module.length R (R ⧸ N) = χ_ I R n := by
      simpa [Ideal.hilbertSamuelChi, N]
    have hchi : χ_ I R (n + 1) = Module.length R (R ⧸ J) := by
      simp [Ideal.hilbertSamuelChi, J]
    have hlen :
        Module.length R (R ⧸ J) =
          Module.length R (R ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
      simpa [J, N] using
        (Ideal.length_quotient_eq_add_length_submodule_quotient_of_le
          (R := R) (M := R) hJN)
    calc
      χ_ I R (n + 1) = Module.length R (R ⧸ J) := hchi
      _ = Module.length R (R ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := hlen
      _ = χ_ I R n + Module.length R (N ⧸ J.submoduleOf N) := by rw [hchiPred]
  have hχn_ne : χ_ I R n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := R) I hI n
  have hχsucc_ne : χ_ I R (n + 1) ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := R) I hI (n + 1)
  have hquot_ne : Module.length R (N ⧸ J.submoduleOf N) ≠ ⊤ := by
    intro htop
    have : χ_ I R (n + 1) = ⊤ := by simpa [hdecomp, htop]
    exact hχsucc_ne this
  have hnat :
      (χ_ I R (n + 1)).toNat =
        (χ_ I R n).toNat + (Module.length R (N ⧸ J.submoduleOf N)).toNat := by
    have hnat' := congrArg ENat.toNat hdecomp
    simpa [ENat.toNat_add hχn_ne hquot_ne] using hnat'
  simpa [hphi] using hnat

/-- Helper for Proposition 10.60.9: a parameter ideal generated by `d` elements bounds the
Hilbert-Samuel degree by `d`. -/
lemma hilbertSamuelPolynomialDegree_le_of_parameterIdeal {d : ℕ}
    (x : Fin d → maximalIdeal R) (hx : (parameterIdeal x).IsIdealOfDefinition) :
    hilbertSamuelPolynomialDegree R R ≤ d := by
  let I : Ideal R := parameterIdeal x
  let L : ℕ := (Module.length R (R ⧸ I)).toNat
  let S : ℕ → ℕ := fun n ↦ ∑ i ∈ Finset.range (n + 1), d.multichoose i
  have hsum_bound :
      ∀ n : ℕ, (χ_ I R n).toNat ≤ S n * L := by
    intro n
    induction n with
    | zero =>
      -- The zeroth `χ`-value is already the first quotient length.
      rw [hilbertSamuelChi_zero_toNat (R := R) I]
      simp [L, S]
    | succ n ih =>
        have hsucc :
            (χ_ I R (n + 1)).toNat = (χ_ I R n).toNat + (φ_ I R (n + 1)).toNat := by
          exact hilbertSamuelChi_succ_toNat_eq_add_hilbertSamuelPhi_toNat_of_isIdealOfDefinition
            (R := R) I hx n
        have hphi :
            (φ_ I R (n + 1)).toNat ≤ d.multichoose (n + 1) * L := by
          simpa [I, L] using
            hilbertSamuelPhi_toNat_le_multichoose_mul_length_of_parameterIdeal
              (R := R) (n := n + 1) x hx
        calc
          (χ_ I R (n + 1)).toNat = (χ_ I R n).toNat + (φ_ I R (n + 1)).toNat := hsucc
          _ ≤ S n * L + d.multichoose (n + 1) * L := Nat.add_le_add ih hphi
          _ = (S n + d.multichoose (n + 1)) * L := by
                rw [← Nat.add_mul]
          _ = S (n + 1) * L := by
                simp [S, Finset.sum_range_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hchi_bound :
      ∀ n : ℕ, (χ_ I R n).toNat ≤ (n + 1).multichoose d * L := by
    intro n
    -- Summing the monomial-count bounds gives the standard stars-and-bars growth estimate.
    have hsum_eq : S n = (n + 1).multichoose d := by
      rw [Nat.multichoose_eq]
      simpa [S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.sum_range_multichoose n d
    simpa [hsum_eq] using hsum_bound n
  obtain ⟨P, hP⟩ :=
    exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition (R := R) (M := R) hx
  let Q : Polynomial ℚ := Polynomial.C (L : ℚ) * Polynomial.preHilbertPoly ℚ d 0
  have hQeval :
      ∀ n : ℕ, Q.eval (n : ℚ) = (((n + 1).multichoose d * L : ℕ) : ℚ) := by
    intro n
    have hpre :
        (Polynomial.preHilbertPoly ℚ d 0).eval (n : ℚ) =
          ((Nat.multichoose (n + 1) d : ℕ) : ℚ) := by
      simpa [Nat.multichoose_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) d (k := 0) (n := n) (by simp))
    -- The explicit comparison polynomial evaluates to the same combinatorial bound.
    simp [Q, hpre, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  have hbound :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    filter_upwards [hP] with n hn
    constructor
    · rw [hn]
      positivity
    · rw [hn, hQeval]
      exact_mod_cast hchi_bound n
  have hpre_ne : Polynomial.preHilbertPoly ℚ d 0 ≠ 0 := by
    intro hzero
    have hlead : (Polynomial.preHilbertPoly ℚ d 0).leadingCoeff = 0 := by
      simpa [hzero]
    have hfac : (d.factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero d
    rw [Polynomial.leadingCoeff_preHilbertPoly] at hlead
    exact hfac <| inv_eq_zero.mp hlead
  have hpre_deg : (Polynomial.preHilbertPoly ℚ d 0).degree = d := by
    rw [Polynomial.degree_eq_natDegree hpre_ne, Polynomial.natDegree_preHilbertPoly]
  have hQdeg : Q.degree ≤ d := by
    -- The explicit comparison polynomial has degree at most `d`.
    calc
      Q.degree ≤ (Polynomial.C (L : ℚ)).degree + (Polynomial.preHilbertPoly ℚ d 0).degree := by
        exact Polynomial.degree_mul_le _ _
      _ ≤ 0 + (Polynomial.preHilbertPoly ℚ d 0).degree := by
        gcongr
        exact Polynomial.degree_C_le
      _ = (Polynomial.preHilbertPoly ℚ d 0).degree := by simp
      _ = d := hpre_deg
  -- Compare the eventual `χ_I`-polynomial to the explicit degree-`d` bound.
  rw [hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition (R := R) (M := R) hx hP]
  exact le_trans (degree_le_of_eventually_nonneg_le hbound) hQdeg

/-- Helper for Proposition 10.60.9: the Krull dimension is bounded above by the Hilbert-Samuel
degree. -/
lemma ringKrullDim_le_zero_of_hilbertSamuelPolynomialDegree_le_zero
    (hdeg : hilbertSamuelPolynomialDegree R R ≤ 0) :
    ringKrullDim R ≤ 0 := by
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    -- In the degenerate ring, both invariants are definitionally bottom.
    simp [ringKrullDim_eq_bot_of_subsingleton, hilbertSamuelPolynomialDegree_eq_bot]
  have hfinite : IsFiniteLength R R := by
    by_contra hfinite
    -- A non-finite-length module has strictly positive Hilbert-Samuel degree.
    have hpos :
        0 < hilbertSamuelPolynomialDegree R R := by
      exact Ideal.degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
        (R := R) (M := R) (I := maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition hfinite
        (hilbertSamuelChiPolynomial_eventuallyEq R R)
    exact (not_lt_of_ge hdeg) hpos
  have hArt : IsArtinianRing R := by
    -- Finite length over itself is exactly the Artinian condition in the Noetherian setting.
    exact (isFiniteLength_iff_isNoetherian_isArtinian (R := R) (M := R)).mp hfinite |>.2
  have hKrull0 : Ring.KrullDimLE 0 R :=
    (isArtinianRing_iff_krullDimLE_zero (R := R)).mp hArt
  exact (Ring.krullDimLE_iff (R := R) (n := 0)).mp hKrull0

/-- Helper for Proposition 10.60.9: the zero locus of a prime ideal is the upper interval defined
by that prime in `Spec`. -/
lemma primeSpectrum_zeroLocus_prime_eq_Ici {A : Type u} [CommRing A] {p : Ideal A}
    (hp : p.IsPrime) :
    PrimeSpectrum.zeroLocus (R := A) p = Set.Ici ⟨p, hp⟩ := by
  -- Rewrite both sides in terms of ideal inclusion inside `PrimeSpectrum A`.
  ext q
  change p ≤ q.asIdeal ↔ (⟨p, hp⟩ : PrimeSpectrum A) ≤ q
  rfl

/-- Helper for Proposition 10.60.9: the Krull dimension is the supremum of the dimensions of the
prime quotients. -/
lemma ringKrullDim_eq_iSup_prime_quotient {A : Type u} [CommRing A] :
    ringKrullDim A = ⨆ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) := by
  -- Normalize the source supremum to the canonical coheight owner on `Spec A`.
  have hquot :
      ∀ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) = Order.coheight p := by
    intro p
    -- The quotient ring sees exactly the upper interval above the prime `p`.
    rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (A := A) p.isPrime]
    exact (Order.coheight_eq_krullDim_Ici p).symm
  calc
    ringKrullDim A = ⨆ p : PrimeSpectrum A, ↑(Order.coheight p) := by
      rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
    _ = ⨆ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) := by
      -- Replace each coheight term by the Krull dimension of the corresponding prime quotient.
      simp_rw [hquot]

/-- Helper for Proposition 10.60.9: passing from a local Noetherian ring to a quotient cannot
increase the Hilbert-Samuel degree. -/
lemma quotient_hilbertSamuelPolynomialDegree_le_self
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (J : Ideal A) :
    hilbertSamuelPolynomialDegree A (A ⧸ J) ≤ hilbertSamuelPolynomialDegree A A := by
  -- Apply the canonical short exact sequence `0 → J → A → A ⧸ J → 0`.
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  letI : Module.Finite A ↑S.X₁ := by
    change Module.Finite A J
    infer_instance
  letI : Module.Finite A ↑S.X₂ := by
    change Module.Finite A A
    infer_instance
  letI : Module.Finite A ↑S.X₃ := by
    change Module.Finite A (A ⧸ J)
    infer_instance
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- Exactness is the standard kernel/range computation for `J ↪ A → A ⧸ J`.
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_mkQ J)
    · -- The subtype map is injective.
      exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · -- The quotient map is surjective.
      exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
  have hdeg :
      hilbertSamuelPolynomialDegree A A =
        max (hilbertSamuelPolynomialDegree A J)
          (hilbertSamuelPolynomialDegree A (A ⧸ J)) := by
    simpa [S] using hilbertSamuelPolynomialDegree_eq_max_of_shortExact (R := A) hS
  -- Read the quotient degree as the right-hand entry of the maximum.
  calc
    hilbertSamuelPolynomialDegree A (A ⧸ J) ≤
        max (hilbertSamuelPolynomialDegree A J)
          (hilbertSamuelPolynomialDegree A (A ⧸ J)) := le_max_right _ _
    _ = hilbertSamuelPolynomialDegree A A := hdeg.symm

/-- Helper for Proposition 10.60.9: an ambient self-degree bound descends to every quotient ring. -/
lemma quotient_self_degree_le_of_self_degree_le
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {J : Ideal A} [IsLocalRing (A ⧸ J)] [IsNoetherianRing (A ⧸ J)] {d : ℕ}
    (hdeg : hilbertSamuelPolynomialDegree A A ≤ d) :
    hilbertSamuelPolynomialDegree (A ⧸ J) (A ⧸ J) ≤ d := by
  -- Rewrite the quotient self-degree through the ambient `A`-module view, then use monotonicity.
  rw [← hilbertSamuelPolynomialDegree_eq_quotient_self (R := A) (J := J)]
  exact le_trans (quotient_hilbertSamuelPolynomialDegree_le_self (A := A) J) hdeg

/-- Helper for Proposition 10.60.9: positive Hilbert-Samuel degree forces the maximal ideal to
contain a nonzero element. -/
lemma exists_mem_maximalIdeal_ne_zero_of_positive_hilbertSamuelPolynomialDegree
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdeg : 0 < hilbertSamuelPolynomialDegree A A) :
    ∃ x : A, x ∈ maximalIdeal A ∧ x ≠ 0 := by
  -- If the maximal ideal vanished, the empty parameter family would already be an ideal of
  -- definition, forcing Hilbert-Samuel degree at most `0` and contradicting positivity.
  have hm_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hm
    let x0 : Fin 0 → maximalIdeal A := fun i ↦ nomatch i
    have hzero_def : (parameterIdeal x0).IsIdealOfDefinition := by
      -- The empty parameter ideal is `⊥`, so under `maximalIdeal A = ⊥` it is an ideal of
      -- definition.
      letI : Field A := (IsLocalRing.isField_iff_maximalIdeal_eq (R := A)).2 hm |>.toField
      simpa [Ideal.IsIdealOfDefinition, hm, parameterIdeal_eq_span]
    have hzero :
        hilbertSamuelPolynomialDegree A A ≤ 0 :=
      hilbertSamuelPolynomialDegree_le_of_parameterIdeal (R := A) x0 hzero_def
    exact (not_lt_of_ge hzero) hdeg
  -- Once `𝔪_A` is nonzero, choose any nonzero element from it.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm_ne_bot
  exact ⟨x, hx, hx0⟩

/-- Helper for Proposition 10.60.9: quotienting a finite module by a submodule cannot increase its
Hilbert-Samuel degree. -/
lemma quotient_hilbertSamuelPolynomialDegree_le_of_submodule
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) :
    hilbertSamuelPolynomialDegree A (M ⧸ N) ≤ hilbertSamuelPolynomialDegree A M := by
  -- Apply the short-exact degree formula to `0 → N → M → M / N → 0`.
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk N.subtype N.mkQ (by
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2)
  letI : Module.Finite A ↑S.X₁ := by
    change Module.Finite A N
    infer_instance
  letI : Module.Finite A ↑S.X₂ := by
    change Module.Finite A M
    infer_instance
  letI : Module.Finite A ↑S.X₃ := by
    change Module.Finite A (M ⧸ N)
    infer_instance
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- Exactness is the standard kernel/range computation for the quotient map.
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using LinearMap.exact_subtype_mkQ N
    · -- The subtype map is injective.
      exact (ModuleCat.mono_iff_injective _).2 N.subtype_injective
    · -- The quotient map is surjective.
      exact (ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective
  have hdeg :
      hilbertSamuelPolynomialDegree A M =
        max (hilbertSamuelPolynomialDegree A N)
          (hilbertSamuelPolynomialDegree A (M ⧸ N)) := by
    simpa [S] using hilbertSamuelPolynomialDegree_eq_max_of_shortExact (R := A) hS
  calc
    hilbertSamuelPolynomialDegree A (M ⧸ N) ≤
        max (hilbertSamuelPolynomialDegree A N)
          (hilbertSamuelPolynomialDegree A (M ⧸ N)) := le_max_right _ _
    _ = hilbertSamuelPolynomialDegree A M := hdeg.symm

/-- Helper for Proposition 10.60.9: a strict overprime lowers the ambient Hilbert-Samuel degree
of the corresponding prime quotient by one. -/
lemma prime_quotient_degree_le_pred_of_lt_overprime
    {n : ℕ} {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {p q : Ideal A} (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q)
    (hdeg : hilbertSamuelPolynomialDegree A (A ⧸ p) ≤ n + 1) :
    hilbertSamuelPolynomialDegree A (A ⧸ q) ≤ n := by
  classical
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt hpq
  let J : Ideal A := p ⊔ Ideal.span ({x} : Set A)
  have hJ_le_q : J ≤ q := by
    -- The principal cut `J = p + (x)` still lies under `q` because `x ∈ q`.
    refine sup_le hpq.le ?_
    rw [Ideal.span_le]
    rintro _ (rfl : _ = x)
    exact hxq
  have hdrop :
      hilbertSamuelPolynomialDegree A (A ⧸ J) <
        hilbertSamuelPolynomialDegree A (A ⧸ p) := by
    -- Cutting by `x ∈ q \ p` gives the source strict-degree drop.
    simpa [J] using
      prime_quotient_colon_shortExact_degree_drop
        (R := A) hp hq hpq hxq hxp
  have hJdeg : hilbertSamuelPolynomialDegree A (A ⧸ J) ≤ n := by
    -- A strict predecessor of a degree at most `n + 1` is bounded by `n`.
    by_cases hbot : hilbertSamuelPolynomialDegree A (A ⧸ J) = ⊥
    · simpa [hbot]
    · lift hilbertSamuelPolynomialDegree A (A ⧸ J) to ℕ using hbot with m hm
      have hm_lt : m < n + 1 := by
        exact WithBot.coe_lt_coe.mp <| by simpa [hm] using lt_of_lt_of_le hdrop hdeg
      have hm_le : m ≤ n := Nat.lt_succ_iff.mp hm_lt
      change ((m : ℕ) : WithBot ℕ) ≤ n
      exact_mod_cast hm_le
  let N : Submodule A (A ⧸ J) :=
    Submodule.map (Submodule.mkQ (J : Submodule A A)) (q : Submodule A A)
  have hquot :
      hilbertSamuelPolynomialDegree A ((A ⧸ J) ⧸ N) ≤ n := by
    -- Passing to a quotient module cannot increase the ambient Hilbert-Samuel degree.
    exact le_trans
      (quotient_hilbertSamuelPolynomialDegree_le_of_submodule (A := A) (M := A ⧸ J) N)
      hJdeg
  let e₁ :
      ((A ⧸ J) ⧸ N) ≃ₗ[A] A ⧸ ((J : Submodule A A) ⊔ (q : Submodule A A)) :=
    Submodule.quotientQuotientEquivQuotientSup (J : Submodule A A) (q : Submodule A A)
  let e₂ :
      (A ⧸ ((J : Submodule A A) ⊔ (q : Submodule A A))) ≃ₗ[A] A ⧸ q :=
    Submodule.quotEquivOfEq _ _ (sup_eq_right.mpr hJ_le_q)
  have heq :
      hilbertSamuelPolynomialDegree A ((A ⧸ J) ⧸ N) =
        hilbertSamuelPolynomialDegree A (A ⧸ q) := by
    -- The third isomorphism theorem identifies the double quotient with `A ⧸ q`.
    simpa [N] using
      hilbertSamuelPolynomialDegree_eq_of_linearEquiv
        (R := A) (M := ((A ⧸ J) ⧸ N)) (e := e₁.trans e₂)
  rw [← heq]
  exact hquot

/-- Helper for Proposition 10.60.9: the source induction over primes above `p` bounds the Krull
dimension of `A ⧸ p` by the ambient Hilbert-Samuel degree of that quotient. -/
lemma prime_quotient_ringKrullDim_le_of_degree_le :
    ∀ n : ℕ, ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {p : Ideal A}, p.IsPrime →
        hilbertSamuelPolynomialDegree A (A ⧸ p) ≤ n →
          ringKrullDim (A ⧸ p) ≤ n
  | 0, A, _, _, _, p, hp, hdeg => by
      letI : Nontrivial (A ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
      letI : IsLocalRing (A ⧸ p) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      have hdeg' : hilbertSamuelPolynomialDegree (A ⧸ p) (A ⧸ p) ≤ 0 := by
        simpa [hilbertSamuelPolynomialDegree_eq_quotient_self (R := A) (J := p)] using hdeg
      -- The zero-degree base case reduces to the already-proved Artinian branch.
      exact ringKrullDim_le_zero_of_hilbertSamuelPolynomialDegree_le_zero
        (R := A ⧸ p) hdeg'
  | n + 1, A, _, _, _, p, hp, hdeg => by
      let pp : PrimeSpectrum A := ⟨p, hp⟩
      have hdim_eq : ringKrullDim (A ⧸ p) = Order.coheight pp := by
        rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (A := A) hp]
        exact (Order.coheight_eq_krullDim_Ici pp).symm
      -- Rewrite the quotient dimension as the coheight of the prime `p`.
      rw [hdim_eq]
      have hcoh_le' : Order.coheight pp ≤ n + 1 := by
        refine (Order.coheight_le_coe_iff (α := PrimeSpectrum A) (x := pp) (n := n + 1)).2 ?_
        intro q hq
        have hpq : p < q.asIdeal := hq
        have hdeg_q :
            hilbertSamuelPolynomialDegree A (A ⧸ q.asIdeal) ≤ n :=
          prime_quotient_degree_le_pred_of_lt_overprime
            (n := n) (A := A) hp q.isPrime hpq hdeg
        have hdim_q :
            ringKrullDim (A ⧸ q.asIdeal) ≤ n :=
          prime_quotient_ringKrullDim_le_of_degree_le
            (n := n) (A := A) (p := q.asIdeal) q.isPrime hdeg_q
        have hcoheight_q : Order.coheight q ≤ n := by
          -- Convert the induction hypothesis back into the coheight language.
          have hdim_q_eq : ringKrullDim (A ⧸ q.asIdeal) = Order.coheight q := by
            rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (A := A) q.isPrime]
            exact (Order.coheight_eq_krullDim_Ici q).symm
          rw [hdim_q_eq] at hdim_q
          exact WithBot.coe_le_coe.mp hdim_q
        exact lt_of_le_of_lt hcoheight_q <| ENat.coe_lt_coe.2 (Nat.lt_succ_self n)
      have hcoh_le : ((Order.coheight pp : ℕ∞) : WithBot ℕ∞) ≤ n + 1 := by
        exact_mod_cast hcoh_le'
      exact hcoh_le

/-- Helper for Proposition 10.60.9: induction on the Hilbert-Samuel degree bounds the Krull
dimension of every local Noetherian ring by the same natural number. -/
lemma ringKrullDim_le_hilbertSamuelPolynomialDegree_aux :
    ∀ n : ℕ, ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      hilbertSamuelPolynomialDegree A A ≤ n → ringKrullDim A ≤ n := by
  intro n A _ _ _ hdeg
  -- Take the supremum over prime quotients and bound each term by the prime-quotient induction.
  rw [ringKrullDim_eq_iSup_prime_quotient]
  refine iSup_le fun p ↦ ?_
  exact prime_quotient_ringKrullDim_le_of_degree_le (n := n) (A := A) p.isPrime <|
    le_trans (quotient_hilbertSamuelPolynomialDegree_le_self (A := A) p.asIdeal) hdeg

/-- Helper for Proposition 10.60.9: the Krull dimension is bounded above by the Hilbert-Samuel
degree. -/
lemma ringKrullDim_le_hilbertSamuelPolynomialDegree :
    ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) := by
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    -- In the degenerate ring, both sides are definitionally bottom.
    simp [ringKrullDim_eq_bot_of_subsingleton, hilbertSamuelPolynomialDegree_eq_bot]
  have hdeg_ne_bot : hilbertSamuelPolynomialDegree R R ≠ ⊥ := by
    intro hbot
    have hpoly_zero : hilbertSamuelChiPolynomial R R = 0 := by
      apply Polynomial.degree_eq_bot.mp
      simpa [hilbertSamuelPolynomialDegree] using hbot
    have hchi_ne_zero :
        ∀ n : ℕ, χ_(maximalIdeal R) R n ≠ 0 := by
      intro n
      have hpow_ne_top : maximalIdeal R ^ (n + 1) ≠ ⊤ := by
        intro htop
        rcases Ideal.pow_eq_top_iff.mp htop with hmax | hn
        · exact (maximalIdeal.isMaximal R).ne_top hmax
        · exact Nat.succ_ne_zero n hn
      have hsub_ne_top :
          maximalIdeal R ^ (n + 1) • (⊤ : Submodule R R) ≠ ⊤ := by
        simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hpow_ne_top
      letI : Nontrivial (R ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R R))) :=
        Submodule.Quotient.nontrivial_iff.mpr hsub_ne_top
      have hpos :
          0 < Module.length R (R ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R R))) :=
        Module.length_pos
      exact ne_of_gt <| by
        simpa [Ideal.hilbertSamuelChi] using hpos
    have hchi_ne_top :
        ∀ n : ℕ, χ_(maximalIdeal R) R n ≠ ⊤ := by
      intro n
      simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
        Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
          (R := R) (M := R) (maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition n
    have hzero_event :
        ∀ᶠ n : ℕ in Filter.atTop,
          ((χ_(maximalIdeal R) R n).toNat : ℚ) = 0 := by
      filter_upwards [hilbertSamuelChiPolynomial_eventuallyEq R R] with n hn
      calc
        ((χ_(maximalIdeal R) R n).toNat : ℚ) =
            (hilbertSamuelChiPolynomial R R).eval (n : ℚ) := by
              simpa using hn.symm
        _ = 0 := by simpa [hpoly_zero]
    rcases Filter.eventually_atTop.mp hzero_event with ⟨N, hN⟩
    have htoNat_ne_zero : (χ_(maximalIdeal R) R N).toNat ≠ 0 := by
      intro hzero
      rcases ENat.toNat_eq_zero.mp hzero with hzero' | htop'
      · exact hchi_ne_zero N hzero'
      · exact hchi_ne_top N htop'
    exact htoNat_ne_zero <| by
      exact_mod_cast hN N le_rfl
  -- Extract the natural degree and invoke the quantified auxiliary inequality.
  lift hilbertSamuelPolynomialDegree R R to ℕ using hdeg_ne_bot with d hd
  have hdeg_le : hilbertSamuelPolynomialDegree R R ≤ d := by
    exact hd.ge
  have haux : ringKrullDim R ≤ (d : WithBot ℕ∞) :=
    ringKrullDim_le_hilbertSamuelPolynomialDegree_aux (n := d) (A := R) hdeg_le
  have hmap :
      (d : WithBot ℕ∞) =
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) := by
    change Nat.castOrderEmbedding.withBotMap ((d : WithBot ℕ)) =
      Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R)
    exact congrArg (fun x : WithBot ℕ ↦ Nat.castOrderEmbedding.withBotMap x) hd
  simpa [hmap] using haux

-- Source/core/bridge triage:
-- * source-facing: `local_noetherian_ring_dimension_tfae` keeps the textbook third clause in terms
--   of ideals of definition generated by `d` elements, together with the minimality statement for
--   smaller tuples;
-- * core/canonical: `IsSystemOfParameters` from `Definition_10_60_10` is the owner abstraction for
--   a fixed-length parameter family;
-- * bridge/view: the owner/view lemmas `isSystemOfParameters_iff` and
--   `isSystemOfParameters_iff_of_ringKrullDim_eq` convert between the source-facing generated-ideal
--   clause and the canonical owner abstraction when the ambient dimension is fixed.
-- Proof sketch: combine the zero-dimensional and one-dimensional base cases with the standard
-- induction on `d`. The forward direction produces `d` elements whose span is an ideal of
-- definition by cutting dimension with an element outside the minimal primes. The Hilbert-Samuel
-- degree clause is the canonical project invariant `hilbertSamuelPolynomialDegree R R`, and the
-- generated-ideal clause is expressed through the chapter owner/view `parameterIdeal` on tuples in
-- `maximalIdeal R` together with the owner predicate `Ideal.IsIdealOfDefinition`. The minimality
-- assertion records exactly that no smaller tuple yields an ideal of definition.
/-- Proposition 10.60.9: for a Noetherian local ring `R` and an integer `d ≥ 0`, the following are
equivalent: `dim(R) = d`, the Hilbert-Samuel degree invariant `d(R)` is `d`, and there exists an
ideal of definition generated by `d` elements while no ideal of definition is generated by fewer
than `d` elements. The Hilbert-Samuel clause is stated in the canonical project form
`hilbertSamuelPolynomialDegree R R = d`, and the generating family is expressed via the canonical
chapter view `parameterIdeal`. -/
theorem local_noetherian_ring_dimension_tfae (d : ℕ) :
    List.TFAE
      [ ringKrullDim R = d
      , hilbertSamuelPolynomialDegree R R = d
      , (∃ x : Fin d → maximalIdeal R,
          (parameterIdeal x).IsIdealOfDefinition) ∧
          ∀ n : ℕ, n < d →
            ¬ ∃ x : Fin n → maximalIdeal R,
              (parameterIdeal x).IsIdealOfDefinition
      ] := by
  classical
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hdim
      -- The source existence clause gives a `d`-generated ideal of definition at dimension `d`.
      have hexists :
          ∃ x : Fin d → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition :=
        exists_parameterIdeal_of_ringKrullDim_eq (R := R) (d := d) hdim
      rcases hexists with ⟨x, hx⟩
      have hle : hilbertSamuelPolynomialDegree R R ≤ d :=
        hilbertSamuelPolynomialDegree_le_of_parameterIdeal (R := R) x hx
      have hge :
          (d : WithBot ℕ∞) ≤ Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) := by
        have hdimdeg :
            ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) :=
          ringKrullDim_le_hilbertSamuelPolynomialDegree
        simpa [hdim] using hdimdeg
      have hEq :
          Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) =
            (d : WithBot ℕ∞) := by
        exact le_antisymm (Nat.castOrderEmbedding.withBotMap.monotone hle) hge
      exact Nat.castOrderEmbedding.withBotMap.injective hEq
    · intro hdeg
      -- Any finite upper bound on the dimension lets us recover the actual natural value of
      -- `ringKrullDim R`, and the same upper-bound helper forces that value to equal `d`.
      have hdim_le : ringKrullDim R ≤ d := by
        have hdimdeg :
            ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) :=
          ringKrullDim_le_hilbertSamuelPolynomialDegree
        simpa [hdeg] using hdimdeg
      rcases ringKrullDim_eq_nat_of_le (R := R) hdim_le with ⟨n, hnle, hdim⟩
      have hexists :
          ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition :=
        exists_parameterIdeal_of_ringKrullDim_eq (R := R) (d := n) hdim
      rcases hexists with ⟨x, hx⟩
      have hdle : d ≤ n := by
        simpa [hdeg] using
          hilbertSamuelPolynomialDegree_le_of_parameterIdeal (R := R) (d := n) x hx
      have hnd : n = d := le_antisymm hnle hdle
      simpa [hnd] using hdim
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hdim
      -- Existence comes from the source induction, while minimality is the already-proved
      -- dimension lower bound for any ideal of definition.
      refine ⟨exists_parameterIdeal_of_ringKrullDim_eq (R := R) hdim, ?_⟩
      intro n hn
      exact not_exists_parameterIdeal_of_lt_ringKrullDim (R := R) hdim hn
    · rintro ⟨hexists, hmin⟩
      -- The displayed witness gives `dim R ≤ d`; recovering the actual natural dimension then
      -- lets the minimality clause force equality with `d`.
      have hdim_le : ringKrullDim R ≤ d := ringKrullDim_le_of_exists_parameterIdeal hexists
      rcases ringKrullDim_eq_nat_of_le (R := R) hdim_le with ⟨n, hnle, hdim⟩
      rcases exists_parameterIdeal_of_ringKrullDim_eq (R := R) (d := n) hdim with ⟨x, hx⟩
      have hdle : d ≤ n := by
        exact Nat.le_of_not_lt fun hnd ↦ hmin n hnd ⟨x, hx⟩
      have hnd : n = d := le_antisymm hnle hdle
      simpa [hnd] using hdim
  tfae_finish

omit [IsNoetherianRing R] in
/-- With the ambient dimension fixed, the existence part of clause `(3)` in
Proposition 10.60.9 is exactly the owner predicate `IsSystemOfParameters`; the minimality clause
remains the source-facing statement that no smaller tuple generates an ideal of definition. -/
theorem generatedIdeal_clause_iff_exists_systemOfParameters {d : ℕ}
    (hdim : ringKrullDim R = d) :
    ((∃ x : Fin d → maximalIdeal R,
        (parameterIdeal x).IsIdealOfDefinition) ∧
      ∀ n : ℕ, n < d →
        ¬ ∃ x : Fin n → maximalIdeal R,
            (parameterIdeal x).IsIdealOfDefinition) ↔
      ((∃ x : Fin d → maximalIdeal R, IsSystemOfParameters x) ∧
        ∀ n : ℕ, n < d →
          ¬ ∃ x : Fin n → maximalIdeal R,
              (parameterIdeal x).IsIdealOfDefinition) := by
  constructor
  · rintro ⟨⟨x, hx⟩, hmin⟩
    exact ⟨⟨x, (isSystemOfParameters_iff_of_ringKrullDim_eq hdim x).2 hx⟩, hmin⟩
  · rintro ⟨⟨x, hx⟩, hmin⟩
    exact ⟨⟨x, (isSystemOfParameters_iff_of_ringKrullDim_eq hdim x).1 hx⟩, hmin⟩

end
