import Mathlib
import stacks_project.Chap10.Definition_10_103_1
import stacks_project.Chap10.Lemma_10_103_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ENat
open IsLocalRing
open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.103.10: the zero locus of a prime ideal is the upper interval above the
corresponding point of `Spec R`. -/
private lemma primeSpectrum_zeroLocus_prime_eq_Ici (𝔭 : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (R := R) 𝔭.asIdeal = Set.Ici 𝔭 := by
  -- Both descriptions say exactly that the ambient prime contains `𝔭.asIdeal`.
  ext 𝔮
  change 𝔭.asIdeal ≤ 𝔮.asIdeal ↔ 𝔭 ≤ 𝔮
  rfl

/-- Helper for Lemma 10.103.10: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring :
    ∃ n : ℕ, ringKrullDim R = n := by
  -- Convert the finite-dimensional local Krull dimension into an actual natural number.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim R = (ringKrullDim R).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.103.10: the quotient by a prime ideal has Krull dimension equal to the
coheight of the corresponding point of `Spec R`. -/
private lemma ringKrullDim_quotient_eq_coheight_primeSpectrum (𝔭 : PrimeSpectrum R) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Order.coheight 𝔭 := by
  -- Rewrite the quotient spectrum as the upper interval over `𝔭`.
  rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (R := R) 𝔭]
  exact (Order.coheight_eq_krullDim_Ici 𝔭).symm

/-- Helper for Lemma 10.103.10: every maximal chain in `Spec R` is finite in the local Noetherian
setting. -/
private lemma finite_flag_primeSpectrum_of_local_noetherian (s : Flag (PrimeSpectrum R)) :
    Finite s := by
  classical
  obtain ⟨d, hd⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (R := R)
  let gradeNat : s → ℕ := fun x ↦ ENat.toNat (Order.height (x : PrimeSpectrum R))
  have hheight_ne_top : ∀ x : s, Order.height (x : PrimeSpectrum R) ≠ ⊤ := by
    intro x
    intro hx_top
    have hle :
        (((Order.height (x : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R) :=
      Order.height_le_krullDim (x : PrimeSpectrum R)
    have : (⊤ : WithBot ℕ∞) ≤ ringKrullDim R := by
      simpa [hx_top] using hle
    exact ringKrullDim_ne_top (top_le_iff.mp this)
  have hgrade_le : ∀ x : s, gradeNat x ≤ d := by
    intro x
    have hle :
        Order.height (x : PrimeSpectrum R) ≤ d := by
      have hle' :
          (((Order.height (x : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R) :=
        Order.height_le_krullDim (x : PrimeSpectrum R)
      rw [hd] at hle'
      exact WithBot.coe_le_coe.mp hle'
    exact ENat.toNat_le_toNat hle (by simp)
  have hgradeNat_lt : ∀ {x y : s}, x < y → gradeNat x < gradeNat y := by
    intro x y hxy
    have hheight_lt :
        Order.height (x : PrimeSpectrum R) < Order.height (y : PrimeSpectrum R) :=
      Order.height_strictMono hxy (lt_top_iff_ne_top.mpr (hheight_ne_top x))
    have htoNat_le : gradeNat x ≤ gradeNat y :=
      ENat.toNat_le_toNat hheight_lt.le (hheight_ne_top y)
    have htoNat_ne : gradeNat x ≠ gradeNat y := by
      intro hEq
      have hheight_eq : Order.height (x : PrimeSpectrum R) = Order.height (y : PrimeSpectrum R) := by
        calc
          Order.height (x : PrimeSpectrum R) = (gradeNat x : ℕ∞) := by
            simp [gradeNat, ENat.coe_toNat (hheight_ne_top x)]
          _ = (gradeNat y : ℕ∞) := by simpa [hEq]
          _ = Order.height (y : PrimeSpectrum R) := by
            simp [gradeNat, ENat.coe_toNat (hheight_ne_top y)]
      exact (ne_of_lt hheight_lt) hheight_eq
    exact lt_of_le_of_ne htoNat_le htoNat_ne
  let grade : s → Fin (d + 1) := fun x ↦
    ⟨gradeNat x, Nat.lt_succ_of_le (hgrade_le x)⟩
  have hgrade_injective : Function.Injective grade := by
    intro x y hxy
    by_contra hne
    rcases s.le_or_le x.2 y.2 with hxy_le | hyx_le
    · have hxy_lt : x < y := lt_of_le_of_ne hxy_le hne
      exact (hgradeNat_lt hxy_lt).ne (congrArg Fin.val hxy)
    · have hyx_lt : y < x := lt_of_le_of_ne hyx_le (fun hyx => hne hyx.symm)
      exact (hgradeNat_lt hyx_lt).ne (congrArg Fin.val hxy).symm
  exact Finite.of_injective grade hgrade_injective

/-- Helper for Lemma 10.103.10: there is a maximal finite prime chain passing through any chosen
point of `Spec R`. -/
private lemma exists_maximal_prime_chain_through (𝔭 : PrimeSpectrum R) :
    ∃ (q : LTSeries (PrimeSpectrum R)) (i : Fin (q.length + 1)),
      IsMaxChain (· ≤ ·) (Set.range q) ∧ q i = 𝔭 := by
  classical
  obtain ⟨s, hs_mem⟩ := Flag.exists_mem 𝔭
  letI : Finite s := finite_flag_primeSpectrum_of_local_noetherian (R := R) s
  letI : Fintype s := Fintype.ofFinite s
  have hcard_pos : 0 < Fintype.card s := Fintype.card_pos_iff.mpr ⟨⟨𝔭, hs_mem⟩⟩
  let m : ℕ := Fintype.card s - 1
  have hm_card : Fintype.card s = m + 1 := by
    dsimp [m]
    exact (Nat.succ_pred_eq_of_pos hcard_pos).symm
  have huniv : (Finset.univ : Finset s).card = m + 1 := by
    simpa using hm_card
  let e₀ : Fin (m + 1) ≃o { x : s // x ∈ (Finset.univ : Finset s) } :=
    (Finset.univ : Finset s).orderIsoOfFin huniv
  let e₁ : { x : s // x ∈ (Finset.univ : Finset s) } ≃o s := by
    refine
      { toFun := fun x ↦ x.1
        invFun := fun x ↦ ⟨x, by simp⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · intro x
      cases x
      rfl
    · intro x
      rfl
    · intro a b
      rfl
  let e : Fin (m + 1) ≃o s := e₀.trans e₁
  let q : LTSeries (PrimeSpectrum R) :=
    { length := m
      toFun := fun i ↦ (e i : PrimeSpectrum R)
      step := fun i ↦ e.strictMono i.castSucc_lt_succ }
  have hq_range : Set.range q = (s : Set (PrimeSpectrum R)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      change ((e (e.symm ⟨x, hx⟩) : s) : PrimeSpectrum R) = x
      simpa using congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hq_max : IsMaxChain (· ≤ ·) (Set.range q) := by
    simpa [hq_range] using s.maxChain
  let i : Fin (q.length + 1) := e.symm ⟨𝔭, hs_mem⟩
  have hi : q i = 𝔭 := by
    change ((e (e.symm ⟨𝔭, hs_mem⟩) : s) : PrimeSpectrum R) = 𝔭
    simpa using congrArg Subtype.val (e.apply_symm_apply ⟨𝔭, hs_mem⟩)
  exact ⟨q, i, hq_max, hi⟩

/-- Helper for Lemma 10.103.10: under the full-support Cohen-Macaulay hypothesis, the ambient
dimension is the sum of the height and coheight of any chosen prime. -/
private lemma ringKrullDim_eq_height_add_coheight_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (𝔭 : PrimeSpectrum R) :
    ringKrullDim R = 𝔭.asIdeal.height + Order.coheight 𝔭 := by
  obtain ⟨q, i, hq_max, hi⟩ := exists_maximal_prime_chain_through (R := R) 𝔭
  have hdim : ringKrullDim R = q.length :=
    ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay
      (R := R) (M := M) hCM hsupp q hq_max
  have hindex :
      (i : ℕ∞) ≤ 𝔭.asIdeal.height := by
    -- The index of `𝔭` in the maximal chain is bounded by its height.
    simpa [hi, Ideal.height_eq_primeHeight, Ideal.primeHeight] using
      (Order.index_le_height q i)
  have hrev :
      (i.rev : ℕ∞) ≤ Order.coheight 𝔭 := by
    -- The reverse index of `𝔭` is bounded by its coheight.
    simpa [hi] using (Order.rev_index_le_coheight q i)
  have hrev_nat : q.length - (i : ℕ) = (i.rev : ℕ) := by
    simpa using congrArg Fin.val (Fin.last_sub i)
  have hlen_eq : q.length = (i : ℕ) + (i.rev : ℕ) := by
    omega
  have hdim_le :
      ringKrullDim R ≤ 𝔭.asIdeal.height + Order.coheight 𝔭 := by
    -- Split the chain length at the chosen index and bound both pieces.
    rw [hdim]
    change
      (((q.length : ℕ∞) : WithBot ℕ∞) ≤
        (((𝔭.asIdeal.height + Order.coheight 𝔭 : ℕ∞)) : WithBot ℕ∞))
    calc
      (((q.length : ℕ∞) : WithBot ℕ∞)) =
          (((i : ℕ∞) + (i.rev : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast hlen_eq
      _ ≤ (((𝔭.asIdeal.height + Order.coheight 𝔭 : ℕ∞)) : WithBot ℕ∞) := by
        exact WithBot.coe_le_coe.mpr (add_le_add hindex hrev)
  have hsum_le :
      𝔭.asIdeal.height + Order.coheight 𝔭 ≤ ringKrullDim R := by
    -- The general height-plus-coheight supremum formula gives the reverse inequality.
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr <| by
      simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using
        (le_iSup (fun x : PrimeSpectrum R ↦ Order.height x + Order.coheight x) 𝔭)
  exact le_antisymm hdim_le hsum_le

/- Domain-style sampling for the local Cohen-Macaulay dimension formula:
- primary domain: Cohen-Macaulay modules over Noetherian local rings, together with local/quotient
  Krull-dimension comparisons at a prime ideal;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth`,
  `Module.supportDim_eq_ringKrullDim_quotient_annihilator`;
- best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
- primitive data: the ambient local Noetherian ring, the module structure on `M`, the
  Cohen-Macaulay owner hypothesis `hCM : Module.CohenMacaulay R M`, the full-support hypothesis
  `hsupp`, and the prime ideal `p`;
- derived API: the finiteness instance on `M`, inherited from `Module.CohenMacaulay`, and the
  support-dimension/depth identities recovered from the owner abstraction.

Source/core/bridge triage:
* `source-facing`: the dimension formula for a full-support Cohen-Macaulay module over a local
  Noetherian ring;
* `core/canonical`: `Module.CohenMacaulay`, `moduleDepth`, `Localization.AtPrime`,
  `ringKrullDim`, and `Module.support`;
* `bridge/view`: the quotient ring `R ⧸ p` and the localization `Localization.AtPrime p`.

The old ambient `[Module.Finite R M]` binder was duplicate primitive data: finiteness already comes
from the owner class `Module.CohenMacaulay R M`, so it should not remain a parallel public
assumption.
-/

-- Proof sketch: apply Lemma `10.103.9` to identify the length of every maximal prime chain in
-- `Spec R` with `ringKrullDim R`. Split a maximal chain through the prime `p` into the part below
-- `p`, whose length computes `ringKrullDim (Localization.AtPrime p)`, and the part above `p`,
-- whose length computes `ringKrullDim (R ⧸ p)`, then add the two lengths.
/-- Lemma 10.103.10: if `R` is a Noetherian local ring and `M` is a finite Cohen-Macaulay
`R`-module with full support, then for every prime ideal `p` of `R` the dimension of `R` is the
sum of the dimensions of the localization `Rₚ` and the quotient `R / p`. -/
theorem ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := by
  let 𝔭 : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hheight :
      ringKrullDim (Localization.AtPrime p) = p.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  have hcoheight :
      ringKrullDim (R ⧸ p) = Order.coheight 𝔭 := by
    simpa [𝔭] using ringKrullDim_quotient_eq_coheight_primeSpectrum (R := R) 𝔭
  -- Rewrite the localization and quotient dimensions as height and coheight at `𝔭`.
  calc
    ringKrullDim R = p.height + Order.coheight 𝔭 := by
      simpa [𝔭] using
        ringKrullDim_eq_height_add_coheight_of_full_support_cohenMacaulay
          (R := R) (M := M) hCM hsupp 𝔭
    _ = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := by
      rw [hheight, hcoheight]

end
