import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_103_10 (from Chap10) -/
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

/-! ### Lemma_10_103_11 (from Chap10) -/
universe u v

open scoped ENat
open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

namespace Module.CohenMacaulay

variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules over Noetherian local rings and their behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: preservation of the Cohen-Macaulay condition under localization at a prime;
* `core/canonical`: the owner class `Module.CohenMacaulay` together with the canonical
  localization objects `Rₚ` and `Mₚ`;
* `bridge/view`: the equality `supportDim_eq_moduleDepth` extracted from the owner class.

The localized depth-equals-support-dimension equality is derived API from the owner class, so the
public statement should return `Module.CohenMacaulay Rₚ Mₚ` directly instead of restating that
equality as a parallel theorem.
-/

-- Proof sketch: use Lemma `10.72.10` to bound the depth of `Mₚ` from below by the depth of `M`
-- minus `dim (R / p)`, and use Lemma `10.72.3` over `Rₚ` to bound the localized depth above by
-- the support dimension of `Mₚ`. Comparing these inequalities with
-- `supportDim_eq_moduleDepth` for `M` yields the Cohen-Macaulay equality for `Mₚ`.
/-- Lemma 10.103.11: if `M` is a Cohen-Macaulay finite module over a Noetherian local ring `R`,
then for any prime ideal `p` of `R`, the localization `Mₚ` is Cohen-Macaulay over `Rₚ`. -/
theorem localizedModule_atPrime : Module.CohenMacaulay Rₚ Mₚ := sorry

end Module.CohenMacaulay

end

/-! ### Definition_10_103_12 (from Chap10) -/
universe u v

open PrimeSpectrum IsLocalRing

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.LocallyCohenMacaulay R M`, the global condition that a finite module over
  a Noetherian ring has Cohen-Macaulay localizations at every prime;
* core/canonical: the owner class `Module.CohenMacaulay` on each localized ring/module pair;
* bridge/view: `LocallyCohenMacaulay.toCohenMacaulay` and
  `locallyCohenMacaulay_of_cohenMacaulay`, which compare the global source-facing condition with
  the local-ring owner abstraction.

Primitive data are exactly the finiteness hypothesis and the family of localized
`Module.CohenMacaulay` instances. The inherited `Module.Finite` instance is derived from the class
extension and should not be restated as a separate local wrapper.
-/
/-- Definition 10.103.12: a finite `R`-module over a Noetherian ring is Cohen-Macaulay if, for
every prime ideal `𝔭` of `R`, the localization `M_𝔭` is a Cohen-Macaulay module over the
localized ring `R_𝔭`. -/
class LocallyCohenMacaulay : Prop extends Module.Finite R M where
  localizedModule_cohenMacaulay :
    ∀ p : PrimeSpectrum R,
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)

namespace LocallyCohenMacaulay

/-- Over a Noetherian local ring, a locally Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay [IsLocalRing R] (h : LocallyCohenMacaulay R M) :
    Module.CohenMacaulay R M := sorry

end LocallyCohenMacaulay

/-- Over a Noetherian local ring, the local-global condition yields the owner class directly. -/
instance cohenMacaulay_of_locallyCohenMacaulay [IsLocalRing R] [h : LocallyCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  h.toCohenMacaulay

/-- Over a Noetherian local ring, a Cohen-Macaulay module is locally Cohen-Macaulay. -/
instance locallyCohenMacaulay_of_cohenMacaulay [IsLocalRing R] [Module.CohenMacaulay R M] :
    LocallyCohenMacaulay R M := sorry

end Module

end

/-! ### Lemma_10_103_13 (from Chap10) -/
universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module.LocallyCohenMacaulay

/-
Source/core/bridge triage:
* source-facing: local Cohen-Macaulayness of a finite module over a Noetherian ring;
* core/canonical: `Module.LocallyCohenMacaulay R M` from `Definition_10_103_12`;
* bridge/view: the polynomial-base-change closure theorem for that owner.

Primitive data are only the module `M` and the owner hypothesis
`Module.LocallyCohenMacaulay R M`. The primewise Cohen-Macaulay localizations of the polynomial
base change are derived API from the resulting owner instance, so the theorem should return
`Module.LocallyCohenMacaulay` directly instead of a parallel family of explicit equalities.
-/

/-- Helper for Lemma 10.103.13: on the polynomial-module model, a polynomial whose leading
coefficient is a unit has trivial kernel. -/
private theorem polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) {g : PolynomialModule A N}
    (hfg : f • g = 0) : g = 0 := by
  by_contra hg
  classical
  let n : ℕ := g.support.max' (Finsupp.support_nonempty_iff.mpr hg)
  have hn_mem : n ∈ g.support := Finset.max'_mem _ _
  have hgn : g n ≠ 0 := Finsupp.mem_support_iff.mp hn_mem
  have htop :
      (f • g) (f.natDegree + n) = f.leadingCoeff • g n := by
    -- At the top index `natDegree f + n`, every antidiagonal summand but the leading one
    -- vanishes, either because the coefficient of `f` is above its degree or because the
    -- corresponding coefficient of `g` lies above the support maximum `n`.
    rw [PolynomialModule.smul_apply]
    calc
      ∑ a ∈ Finset.antidiagonal (f.natDegree + n), f.coeff a.1 • g a.2
          = ∑ a ∈ Finset.antidiagonal (f.natDegree + n),
              if a = (f.natDegree, n) then f.leadingCoeff • g n else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rcases a with ⟨i, j⟩
            by_cases hmain : (i, j) = (f.natDegree, n)
            · rcases Prod.mk.inj hmain with ⟨rfl, rfl⟩
              simp [Polynomial.coeff_natDegree]
            · have hij : i + j = f.natDegree + n := by
                simpa using (Finset.mem_antidiagonal.mp ha)
              have hterm_zero : f.coeff i • g j = 0 := by
                by_cases hi : i = f.natDegree
                · have hj : j = n := by
                    omega
                  exact False.elim (hmain (by simp [hi, hj]))
                · rcases lt_or_gt_of_ne hi with hi_lt | hi_gt
                  · have hj_gt : n < j := by
                      omega
                    have hgj : g j = 0 := by
                      by_contra hgj
                      have hj_mem : j ∈ g.support := Finsupp.mem_support_iff.mpr hgj
                      exact (not_lt_of_ge (Finset.le_max' _ _ hj_mem)) hj_gt
                    simp [hgj]
                  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi_gt]
              simp [hmain, hterm_zero]
      _ = f.leadingCoeff • g n := by
          simp [Finset.mem_antidiagonal]
  have hzero : f.leadingCoeff • g n = 0 := by
    simpa [hfg] using htop.symm
  exact hgn ((hf.smul_eq_zero).1 hzero)

/-- Helper for Lemma 10.103.13: transporting the polynomial-module comparison shows that a
polynomial with unit leading coefficient is a nonzerodivisor on the polynomial tensor module. -/
private theorem polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) :
    IsSMulRegular ((Polynomial A) ⊗[A] N) f := by
  let e := PolynomialModule.polynomialTensorProductLEquivPolynomialModule A N
  have hreg : IsSMulRegular (PolynomialModule A N) f := by
    intro x y hxy
    have hzero : f • (x - y) = 0 := by
      simpa [smul_sub, hxy]
    exact sub_eq_zero.mp <|
      polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff (N := N) f hf hzero
  -- The tensor-product model and the polynomial-module model carry the same `A[X]`-action.
  exact (LinearEquiv.isSMulRegular_congr e f).2 hreg

/-- Helper for Lemma 10.103.13: Cohen-Macaulayness is unchanged by an `R`-linear equivalence over
the same local Noetherian ring. -/
private theorem cohenMacaulay_of_linearEquiv [IsLocalRing R]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.CohenMacaulay R N] : Module.CohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  -- Transport both invariants appearing in the owner definition across the linear equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e, h.supportDim_eq_moduleDepth]⟩

/-- Helper for Lemma 10.103.13: local Cohen-Macaulayness is unchanged by an `R`-linear
equivalence over the same Noetherian ring. -/
private theorem locallyCohenMacaulay_of_linearEquiv
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.LocallyCohenMacaulay R N] :
    Module.LocallyCohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  refine ⟨fun p ↦ ?_⟩
  let ep : LocalizedModule.AtPrime p.asIdeal N ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal N' :=
    LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  -- Localize the linear equivalence and reuse the localized Cohen-Macaulay owner.
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
    h.localizedModule_cohenMacaulay p
  exact cohenMacaulay_of_linearEquiv ep

/-- Helper for Lemma 10.103.13: over a Noetherian local ring, a finite module with
zero-dimensional support is already Cohen-Macaulay. -/
private theorem cohen_macaulay_of_supportDim_zero_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdim : Module.supportDim A N = 0) : Module.CohenMacaulay A N := by
  refine Module.CohenMacaulay.mk ?_
  let _ : Nontrivial N := by
    simp [← Module.supportDim_ne_bot_iff_nontrivial A, hdim]
  have hdepth_le : WithBot.some (moduleDepth A N : ℕ∞) ≤ 0 := by
    -- In dimension zero the standard depth bound forces the depth to be zero as well.
    rw [← hdim]
    exact depth_le_supportDim
  have hdepth_eq : moduleDepth A N = 0 := by
    simpa using hdepth_le
  -- With both invariants equal to zero, the owner equality is immediate.
  simpa [hdepth_eq] using hdim

/-- Helper for Lemma 10.103.13: after adjoining one variable to `A`, tensoring `M` directly over
`R` agrees with first base-changing `M` to `A` and then extending scalars from `A` to
`A[X]`. -/
private noncomputable def polynomial_tensor_baseChange_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] :
    ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
      ((Polynomial A) ⊗[A] (A ⊗[R] M)) := by
  -- Insert the redundant `A`-tensor factor and then reassociate so the one-variable theorem can
  -- be applied to the already base-changed module `A ⊗[R] M`.
  let eInsert :
      ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
        (((Polynomial A) ⊗[A] A) ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (Algebra.TensorProduct.rid A (Polynomial A) (Polynomial A)).symm.toLinearEquiv
      (LinearEquiv.refl R M)
  let eAssoc :
      (((Polynomial A) ⊗[A] A) ⊗[R] M) ≃ₗ[Polynomial A]
        ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
    TensorProduct.AlgebraTensorModule.assoc R A (Polynomial A) (Polynomial A) A M
  exact eInsert.trans eAssoc

/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence identifies the prime complements of
corresponding prime ideals. -/
private theorem primeCompl_map_eq_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Submonoid.map e.toMulEquiv (PrimeSpectrum.comap e.toRingHom q).asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Re-express membership in the contracted prime so the image element can be read in `q`.
    simpa [PrimeSpectrum.comap_asIdeal] using ha
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    -- Pulling `b` back along `e` lands outside the contracted prime for the same reason.
    simpa [PrimeSpectrum.comap_asIdeal] using hb

/-- Helper for Lemma 10.103.13: localizing corresponding prime ideals along an `R`-algebra
equivalence gives an `R`-algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- This is the ring-side transport required by the source-local comparison at each prime.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Lemma 10.103.13: after localizing corresponding prime ideals along an `R`-algebra
equivalence, the localized tensor modules agree over the localized source ring. -/
private noncomputable def localized_tensor_linearEquiv_of_algEquiv_atPrime
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    let p := PrimeSpectrum.comap e.toRingHom q
    let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
    let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      eLoc.toRingHom.toAlgebra
    let _ :
        Module (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
      Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
    LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) := by
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[R] M) :=
    Module.compHom (Localization.AtPrime q.asIdeal ⊗[R] M) eLoc.toRingHom
  let eLocLinear :
      Localization.AtPrime p.asIdeal ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal :=
    { __ := eLoc.toAddEquiv
      map_smul' := fun a x ↦ by
        -- On the codomain, the `Localization.AtPrime p.asIdeal`-action is induced by `eLoc`.
        simpa [Algebra.smul_def] using eLoc.map_mul a x }
  -- Rewrite both localizations as literal tensor base changes over `R`.
  let eLeft :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (A ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R A (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) M)
  let eMid :
      Localization.AtPrime p.asIdeal ⊗[R] M ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eLocLinear (LinearEquiv.refl R M)
  let eRightB :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime q.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl (B ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R B (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) M)
  let eRight :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    { __ := eRightB.toAddEquiv
      map_smul' := fun a x ↦ by
        -- The q-side comparison is `B_q`-linear, hence also `A_p`-linear after restricting
        -- scalars along `eLoc`.
        change
          eRightB ((algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) • x) =
            (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal) a) • eRightB x
        exact
          eRightB.map_smul (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) x }
  -- The middle `TensorProduct.congr` is the only nontrivial transport; the outer equivalences are
  -- the canonical localized-module-to-tensor-product comparisons.
  exact eLeft.trans <| eMid.trans eRight.symm

/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence between scalar-extension rings should
transport local Cohen-Macaulayness of the corresponding tensor-base-changed module. -/
private theorem locallyCohenMacaulay_tensor_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A]
    {B : Type*} [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (e : A ≃ₐ[R] B) (h : Module.LocallyCohenMacaulay A (A ⊗[R] M)) :
    Module.LocallyCohenMacaulay B (B ⊗[R] M) := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  let eBaseChange :
      (B ⊗[R] M) ≃ₗ[B] (B ⊗[A] (A ⊗[R] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm
  let _ : Module.Finite B (B ⊗[A] (A ⊗[R] M)) := inferInstance
  let _ : Module.Finite B (B ⊗[R] M) := Module.Finite.equiv eBaseChange.symm
  refine ⟨fun q ↦ ?_⟩
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      IsScalarTower (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
  let eqv :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) :=
    localized_tensor_linearEquiv_of_algEquiv_atPrime (R := R) (M := M) e q
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M)) :=
    h.localizedModule_cohenMacaulay p
  have hrestrict :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) := by
    -- First move the localized owner across the canonical localized tensor comparison.
    exact cohenMacaulay_of_linearEquiv eqv
  have hsurj :
      Function.Surjective
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- The localized algebra equivalence identifies the target local ring with a quotient-free copy
    -- of the source one, so the induced local map is surjective.
    simpa using eLoc.surjective
  -- Then upgrade from the restricted `A_p`-module view back to the genuine `B_q`-module owner.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime q.asIdeal)
      (N := LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
      hsurj).2 hrestrict

/-- Helper for Lemma 10.103.13: localizing the one-variable scalar extension at a maximal ideal
identifies it with tensoring the localized coefficient ring with the localized source module. -/
private noncomputable def localized_polynomial_tensor_equiv_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
      Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  let eLocalized :
      LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
        Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) :=
    -- First rewrite localization at `m` as tensoring with the local ring `Sm`.
    LocalizedModule.equivTensorProduct m.asIdeal.primeCompl ((Polynomial A) ⊗[A] N)
  let eCancelPolynomial :
      Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) ≃ₗ[Sm] Sm ⊗[A] N :=
    -- Cancel the intermediate polynomial-ring base change.
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Polynomial A) Sm Sm N
  let eInsertLocalization :
      Sm ⊗[A] N ≃ₗ[Sm] Sm ⊗[Ap] (Ap ⊗[A] N) :=
    -- Reinsert the coefficient localization so the source module appears as `N_p`.
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap Sm Sm N).symm
  let eLocalizedSource :
      Sm ⊗[Ap] (Ap ⊗[A] N) ≃ₗ[Sm] Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Sm Sm)
      (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).symm
  exact eLocalized.trans <| eCancelPolynomial.trans <| eInsertLocalization.trans eLocalizedSource

/-- Helper for Lemma 10.103.13: the closed fiber of the local map `A_p → A[X]_m` has Krull
dimension `1`. -/
private theorem ringKrullDim_closedFiber_polynomial_atMaximal_eq_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) = 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  have hformula :
      ringKrullDim Sm =
        ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
    -- The quotient form of Lemma `10.112.7` expresses the local dimension by base plus fiber.
    simpa [p, Ap, Sm] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
        (R := A) (S := Polynomial A) m.toPrimeSpectrum
  have hSm :
      ringKrullDim Sm = p.asIdeal.height + 1 := by
    -- Identify `dim(Sm)` with the height of `m`, then use the polynomial height jump formula.
    calc
      ringKrullDim Sm = m.asIdeal.height := by
        simpa [Sm] using (IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal Sm)
      _ = p.asIdeal.height + 1 := by
        simpa [p] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞))
            (Polynomial.height_eq_height_add_one (p := p.asIdeal) (P := m.asIdeal))
  have hAp : ringKrullDim Ap = p.asIdeal.height := by
    -- The contracted base localization has dimension equal to the height of `p`.
    simpa [Ap] using (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap)
  have hfiber :
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) = 1 := by
    let d : ℕ := p.asIdeal.height.toNat
    have hd : (d : WithBot ℕ∞) = p.asIdeal.height := by
      have hneTop : p.asIdeal.height ≠ ⊤ := ne_of_lt (Ideal.height_lt_top Ideal.IsPrime.ne_top')
      simpa [d] using
        (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm).symm
    have hformula' :
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          p.asIdeal.height + 1 := by
      calc
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
            ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
              rw [hAp]
        _ = ringKrullDim Sm := hformula.symm
        _ = p.asIdeal.height + 1 := hSm
    have hformula'' :
        (d : WithBot ℕ∞) + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          d + 1 := by
      simpa [hd] using hformula'
    exact (ENat.WithBot.natCast_add_cancel (a := ringKrullDim
      (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal)) (b := (1 : WithBot ℕ∞)) (c := d)).1
      hformula''
  have hmap :
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
        Ideal.map (algebraMap A Sm) p.asIdeal := by
    -- The maximal ideal of `Ap` is exactly the extension of `p`, so the two fiber ideals agree.
    calc
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
          Ideal.map (algebraMap Ap Sm) (Ideal.map (algebraMap A Ap) p.asIdeal) := by
            rw [Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      _ = Ideal.map ((algebraMap Ap Sm).comp (algebraMap A Ap)) p.asIdeal := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap A Sm) p.asIdeal := by
            simp [IsScalarTower.algebraMap_eq A Ap Sm]
  simpa [p, Ap, Sm] using
    calc
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) =
          ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
            rw [hmap]
      _ = 1 := hfiber

/-- Helper for Lemma 10.103.13: once the source quotient over `A_p` has zero-dimensional support,
its tensor base change to `A[X]_m` has support dimension `1`. -/
private theorem supportDim_tensor_of_zeroDim_local_eq_one_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A))
    {Q0 : Type*} [AddCommGroup Q0]
    [Module (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal) Q0]
    [Module.Finite (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
      Q0]
    (hQ0 :
      Module.supportDim
          (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
          Q0 = 0) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Module.supportDim Sm (Sm ⊗[Ap] Q0) = 1 := by
  -- TODO for Lemma 10.103.13: use Lemma `10.40.6` to rewrite the support of `Sm ⊗[Ap] Q0` as
  -- the inverse image of the closed point of `Spec(A_p)`, identify that inverse image with the
  -- zero locus of the extended maximal ideal, and invoke the previous closed-fiber-dimension
  -- helper.
  sorry

-- Proof sketch: the source argument first proves the one-variable statement over `A[X]` for an
-- arbitrary locally Cohen-Macaulay `A`-module, and only afterward iterates it through the
-- last-variable identification for `MvPolynomial`.
/-- Helper for Lemma 10.103.13: the source-faithful one-variable step for polynomial scalar
extension. -/
private theorem polynomial
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) :
    Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[A] N) := by
  -- TODO for Lemma 10.103.13: localize at a maximal ideal of `A[X]`, pull back a maximal
  -- regular sequence from `A_p`, identify the closed-fiber quotient support as one-dimensional,
  -- choose a polynomial with unit leading coefficient, and finish with
  -- `polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff`.
  sorry

-- Proof sketch: argue by induction on the number of variables, reducing from
-- `MvPolynomial (Fin (n + 1)) R` to a one-variable polynomial extension over
-- `MvPolynomial (Fin n) R`. For the one-variable step, localize at a prime of `A[X]`, pull back a
-- maximal regular sequence from `A_p`, identify the quotient support in the closed fiber, and use
-- `polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff` for the final nonzerodivisor step.
/-- Lemma 10.103.13: if `M` is a locally Cohen-Macaulay module over a Noetherian ring `R`, then
its scalar extension to `R[x₁, …, xₙ]`, represented canonically by
`MvPolynomial (Fin n) R ⊗[R] M`, is again locally Cohen-Macaulay. -/
theorem mvPolynomial (hCM : Module.LocallyCohenMacaulay R M) (n : ℕ) :
    Module.LocallyCohenMacaulay (MvPolynomial (Fin n) R) ((MvPolynomial (Fin n) R) ⊗[R] M) := by
  -- Route correction: the source proof is local and one-variable at each step, so the remaining
  -- blocker is now isolated into the named one-variable theorem and the algebra-equivalence
  -- transport between successive polynomial presentations.
  induction n with
  | zero =>
      let e₀ : R ≃ₐ[R] MvPolynomial (Fin 0) R := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
      -- First rewrite `M` as `R ⊗[R] M`, then transport that local Cohen-Macaulay owner across
      -- the zero-variable algebra equivalence.
      let hTensor : Module.LocallyCohenMacaulay R (R ⊗[R] M) := by
        let _ : Module.LocallyCohenMacaulay R M := hCM
        exact locallyCohenMacaulay_of_linearEquiv
          (((TensorProduct.comm R R M).trans (TensorProduct.rid R M)).symm)
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) e₀ hTensor
  | succ n ih =>
      let A := MvPolynomial (Fin n) R
      let eLast : Polynomial A ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
        (noetherNormalizationLastVariableEquiv (R := R) (n := n)).symm
      let eAssoc :
          ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial_tensor_baseChange_linearEquiv (R := R) (M := M) (A := A)
      -- Apply the one-variable theorem over the `n`-variable coefficient ring and then undo the
      -- canonical reassociation of the tensor module.
      let hPolyAssoc :
          Module.LocallyCohenMacaulay (Polynomial A)
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial (A := A) (N := A ⊗[R] M) ih
      let hPoly :
          Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[R] M) := by
        let _ :
            Module.LocallyCohenMacaulay (Polynomial A)
              ((Polynomial A) ⊗[A] (A ⊗[R] M)) := hPolyAssoc
        exact locallyCohenMacaulay_of_linearEquiv (R := Polynomial A) eAssoc.symm
      -- Transport the polynomial-ring statement back to the canonical `MvPolynomial` presentation
      -- of the next stage.
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) eLast hPoly

end Module.LocallyCohenMacaulay

end
