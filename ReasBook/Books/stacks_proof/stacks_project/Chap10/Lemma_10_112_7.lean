import StacksProject_2024.Chap10.Lemma_10_112_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]

-- Proof sketch: let `P` be the maximal ideal of `S_q` and `I = (q ∩ R)S_q`. Lemma `10.112.6`
-- gives the upper bound `ht P ≤ ht (q ∩ R) + ht (P/I)`, after rewriting heights as the Krull
-- dimensions of `S_q`, `R_(q ∩ R)`, and the canonical local fiber ring via
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`,
-- `IsLocalization.AtPrime.ringKrullDim_eq_height`, and the quotient-to-fiber bridge from
-- Lemma `10.112.6`. For the reverse inequality, lift a maximal chain under `q ∩ R` to `S_q`
-- using going down and splice it with a maximal chain in `Spec (S_q / I)`, recovering the
-- matching lower bound on heights.
/-- Lemma 10.112.7: if `R → S` is a homomorphism of Noetherian rings, `q` is a point of
`Spec S`, and `R → S` satisfies going down, then the Krull dimension of `S_q` is the sum of the
Krull dimensions of `R_(q ∩ R)` and of the canonical local fiber ring at the corresponding point of
`Spec (κ(q ∩ R) ⊗[R] S)`. -/
@[stacks 00ON]
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
    (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim (fiberLocalRingAt R S q) := by
  let p : Ideal R := q.asIdeal.under R
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let Sq := Localization.AtPrime q.asIdeal
  let Rp := Localization.AtPrime p
  let P : Ideal Sq := IsLocalRing.maximalIdeal Sq
  let I : Ideal Sq := Ideal.map (algebraMap R Sq) p
  have hPq : P.LiesOver q.asIdeal := by
    dsimp [P, Sq]
    infer_instance
  letI := hPq
  letI : q.asIdeal.LiesOver p := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  have hPp : P.LiesOver p := Ideal.LiesOver.trans P q.asIdeal p
  letI := hPp
  have hI_le : I ≤ P := Ideal.map_le_iff_le_comap.mpr hPp.over.le
  have hI_ne_top : I ≠ ⊤ := by
    intro hI
    have hP_ne_top : P ≠ ⊤ := by
      dsimp [P, Sq]
      exact (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top
    exact hP_ne_top (top_le_iff.mp (hI ▸ hI_le))
  haveI : Algebra.HasGoingDown S Sq := by infer_instance
  haveI : Algebra.HasGoingDown R Sq := Algebra.HasGoingDown.trans R S Sq
  haveI : Nontrivial (Sq ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI_ne_top
  haveI : IsLocalRing (Sq ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : P.map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (Sq ⧸ I) := by
    dsimp [P]
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hSq : ringKrullDim Sq = ↑P.height := by
    dsimp [P]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
  have hp' : ↑p.height = ringKrullDim Rp := by
    simpa [Rp] using (IsLocalization.AtPrime.ringKrullDim_eq_height p Rp).symm
  have hQdim : ringKrullDim (Sq ⧸ I) = ringKrullDim (fiberLocalRingAt R S q) := by
    simpa [Sq, I, p] using
      ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt q
  have hQ : ↑(P.map (Ideal.Quotient.mk I)).height = ringKrullDim (fiberLocalRingAt R S q) := by
    rw [hmax]
    calc
      ↑(IsLocalRing.maximalIdeal (Sq ⧸ I)).height = ringKrullDim (Sq ⧸ I) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      _ = ringKrullDim (fiberLocalRingAt R S q) := hQdim
  have hp_le_hP : p.height ≤ P.height := by
    rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    refine Order.height_le_iff'.2 ?_
    intro l hl
    letI : P.LiesOver l.last.asIdeal := by
      rw [hl]
      exact hPp
    obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have hL : L.length ≤ Order.height L.last := Order.length_le_height_last
    simpa [Ideal.primeHeight, hlen, hlast] using hL
  haveI : p.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr <| Or.inr <| by
    have hP_height_lt_top : P.height < ⊤ :=
      Ideal.height_lt_top ((IsLocalRing.maximalIdeal.isMaximal Sq).ne_top)
    exact lt_of_le_of_lt hp_le_hP <|
      hP_height_lt_top
  have hmain_ge : p.height + (P.map (Ideal.Quotient.mk I)).height ≤ P.height := by
    obtain ⟨lp, hlp, hlenp⟩ := p.exists_ltSeries_length_eq_height
    obtain ⟨lq, hlq, hlenq⟩ :=
      (P.map (Ideal.Quotient.mk I)).exists_ltSeries_length_eq_height
    let l' : LTSeries (PrimeSpectrum Sq) :=
      lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
    let Q : Ideal Sq := l'.head.asIdeal
    have hPp_comap : Ideal.comap (algebraMap R Sq) P = p := by
      simpa [Ideal.under_def] using hPp.over.symm
    have hhead : Q.LiesOver lp.last.asIdeal := by
      refine ⟨?_⟩
      refine le_antisymm ?_ ?_
      · dsimp [Q]
        rw [LTSeries.head_map, hlp, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
        rw [← Ideal.map_le_iff_le_comap]
        rw [← Ideal.map_le_iff_le_comap]
        have hbot :
            Ideal.map (Ideal.Quotient.mk I) (Ideal.map (algebraMap R Sq) p) = ⊥ := by
          simp [I]
        rw [hbot]
        exact bot_le
      · dsimp [Q]
        rw [LTSeries.head_map, hlp]
        change Ideal.comap (algebraMap R Sq) (Ideal.comap (Ideal.Quotient.mk I) lq.head.asIdeal) ≤ p
        refine le_trans (Ideal.comap_mono (Ideal.comap_mono lq.head_le_last)) ?_
        rw [hlq]
        change Ideal.comap (algebraMap R Sq) (Ideal.comap (Ideal.Quotient.mk I)
          (Ideal.map (Ideal.Quotient.mk I) P)) ≤ p
        rw [Ideal.comap_map_mk hI_le]
        exact hPp_comap.le
    obtain ⟨lp', hlp'len, hlp', _⟩ := Ideal.exists_ltSeries_of_hasGoingDown lp Q
    have hlen : (lp'.smash l' hlp').length = lp.length + lq.length := by
      simp [hlp'len, l']
    rw [← hlenp, ← hlenq, ← Nat.cast_add, ← hlen, Ideal.height_eq_primeHeight]
    apply Order.length_le_height
    rw [RelSeries.last_smash, LTSeries.last_map, hlq]
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) P) ≤ P
    rw [Ideal.comap_map_mk hI_le]
  have hmain_le : P.height ≤ p.height + (P.map (Ideal.Quotient.mk I)).height := by
    have hdim_le :
        ringKrullDim Sq ≤ ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q) := by
      simpa [Sq, Rp, p] using
        ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver
          p q.asIdeal (by simpa [p] using Ideal.over_under q.asIdeal)
    have hdim_le' :
        (↑P.height : WithBot ℕ∞) ≤ ↑p.height + ↑(P.map (Ideal.Quotient.mk I)).height := by
      simpa [hSq, hp', hQ] using hdim_le
    exact_mod_cast hdim_le'
  have hmain : P.height = p.height + (P.map (Ideal.Quotient.mk I)).height :=
    le_antisymm hmain_le hmain_ge
  simpa [Sq, Rp, p] using
    calc
      ringKrullDim Sq = ↑P.height := hSq
      _ = ↑p.height + ↑(P.map (Ideal.Quotient.mk I)).height := by
        exact_mod_cast hmain
      _ = ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q) := by
        rw [hp', hQ]

/-- Explicit lies-over restatement of Lemma `10.112.7`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver_of_hasGoingDown
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim (fiberLocalRingAt R S ⟨q, inferInstance⟩) := by
  have hp : p = q.under R := by
    simpa using hq.over
  subst p
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  simpa [q'] using
    ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
      q'

-- Proof sketch: rewrite the canonical local fiber ring in Lemma `10.112.7` by the quotient
-- presentation `S_q / (q ∩ R)S_q`.
/-- Quotient-form companion to Lemma `10.112.7`: rewriting the canonical local fiber ring at `q`
by its quotient presentation recovers the formula with `S_q / (q ∩ R)S_q`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
    (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
  have hbridge :
      ringKrullDim (fiberLocalRingAt R S q) =
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
    simpa using
      (ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt q).symm
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R S q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim
            ((Localization.AtPrime q.asIdeal) ⧸
              Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
      rw [hbridge]

/-- Explicit lies-over restatement of the quotient form of Lemma `10.112.7`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q)) p) := by
  have hp : p = q.under R := by
    simpa using hq.over
  subst p
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  simpa [q'] using
    ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
      q'

end
