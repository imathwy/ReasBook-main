import Mathlib
import stacks_project.Chap10.Definition_10_103_1
import stacks_project.Chap10.Lemma_10_63_2
import stacks_project.Chap10.Lemma_10_72_9
import stacks_project.Chap10.Proposition_10_63_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules, support dimension, and associated primes over
  Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`,
  `minimal_support_iff_minimal_associatedPrimes`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: the two consequences for associated primes of a Cohen-Macaulay module;
* `core/canonical`: `Module.CohenMacaulay`, `Module.support`, `Module.supportDim`,
  `associatedPrimes`, and `ringKrullDim`;
* `bridge/view`: passing between support-minimal prime points and minimal associated ideals.
-/

-- Proof sketch: apply Lemma `10.72.9` to get
-- `.some (moduleDepth R M) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal)`, use the Cohen-Macaulay identity
-- `Module.CohenMacaulay.supportDim_eq_moduleDepth`, and
-- combine this with the general inequality `ringKrullDim (R ⧸ 𝔭.asIdeal) ≤ Module.supportDim R M`
-- coming from `𝔭 ∈ Module.support R M`. Equality of dimensions forces `𝔭` to be minimal in the
-- support.
omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.7: the zero locus of a prime ideal is the upper interval above the
corresponding point of `Spec R`. -/
private lemma primeSpectrum_zeroLocus_prime_eq_Ici (𝔭 : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (R := R) 𝔭.asIdeal = Set.Ici 𝔭 := by
  -- Both descriptions say exactly that the given prime contains `𝔭.asIdeal`.
  ext 𝔮
  change 𝔭.asIdeal ≤ 𝔮.asIdeal ↔ 𝔭 ≤ 𝔮
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.7: support membership bounds the Krull dimension of the corresponding
prime quotient by the support dimension of the module. -/
private theorem ringKrullDim_quotient_le_supportDim_of_mem_support
    (𝔮 : PrimeSpectrum R) (h𝔮 : 𝔮 ∈ Module.support R M) :
    ringKrullDim (R ⧸ 𝔮.asIdeal) ≤ Module.supportDim R M := by
  -- The quotient by `𝔮` is a further quotient of `R / Ann(M)`, so its dimension can only drop.
  have hann_le : Module.annihilator R M ≤ 𝔮.asIdeal :=
    Module.annihilator_le_of_mem_support h𝔮
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
    (Ideal.Quotient.factor_surjective hann_le)

/-- Helper for Lemma 10.103.7: an associated prime of a Cohen-Macaulay module has quotient ring
dimension equal to the support dimension. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M := by
  -- The source proof is the depth sandwich `depth(M) ≤ dim(R/𝔭) ≤ dim(Supp M)`.
  have hlower :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := M) 𝔭.asIdeal h𝔭
  have hlower' : Module.supportDim R M ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hlower
  have h𝔭_support : 𝔭 ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using h𝔭)
  have hup : ringKrullDim (R ⧸ 𝔭.asIdeal) ≤ Module.supportDim R M :=
    ringKrullDim_quotient_le_supportDim_of_mem_support (R := R) (M := M) 𝔭 h𝔭_support
  exact le_antisymm hup hlower'

/-- Helper for Lemma 10.103.7: quotient dimensions strictly decrease along a proper specialization
in `Spec R`. -/
private theorem ringKrullDim_quotient_lt_of_lt_primeSpectrum
    (𝔮 𝔭 : PrimeSpectrum R) (h𝔮𝔭 : 𝔮 < 𝔭) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) < ringKrullDim (R ⧸ 𝔮.asIdeal) := by
  -- Rewrite both quotient dimensions as coheights and use the strict antitonicity of coheight.
  have hrw :
      ∀ 𝔯 : PrimeSpectrum R, ringKrullDim (R ⧸ 𝔯.asIdeal) = Order.coheight 𝔯 := by
    intro 𝔯
    rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (R := R) 𝔯]
    exact (Order.coheight_eq_krullDim_Ici 𝔯).symm
  haveI : Nontrivial (R ⧸ 𝔭.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr 𝔭.isPrime.ne_top
  haveI : IsLocalRing (R ⧸ 𝔭.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭.asIdeal) Ideal.Quotient.mk_surjective
  have h𝔭_fin : Order.coheight 𝔭 < ⊤ := by
    have hdim : ringKrullDim (R ⧸ 𝔭.asIdeal) < ⊤ := ringKrullDim_lt_top
    rw [hrw 𝔭] at hdim
    exact WithBot.coe_lt_coe.mp hdim
  rw [hrw 𝔭, hrw 𝔮]
  exact WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti h𝔮𝔭 h𝔭_fin)

/-- Lemma 10.103.7: if `M` is a Cohen-Macaulay module over a Noetherian local ring and `𝔭` is an
associated prime of `M`, then the Krull dimension of `R / 𝔭` equals the dimension of the support
of `M`, and `𝔭` is minimal in `Module.support R M`. -/
theorem ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M ∧
      Minimal (· ∈ Module.support R M) 𝔭 := by
  have hdim :
      ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M :=
    ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R) (M := M) 𝔭 h𝔭
  have h𝔭_support : 𝔭 ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using h𝔭)
  refine ⟨hdim, ?_⟩
  refine ⟨h𝔭_support, ?_⟩
  intro 𝔮 h𝔮 h𝔮𝔭
  -- If a smaller support point existed, strict dimension drop would contradict the equality above.
  by_contra hnot
  have h𝔮_ne : 𝔮 ≠ 𝔭 := fun hEq ↦ hnot (hEq ▸ le_rfl)
  have h𝔮_lt_𝔭 : 𝔮 < 𝔭 := lt_of_le_of_ne h𝔮𝔭 h𝔮_ne
  have hlt :
      ringKrullDim (R ⧸ 𝔭.asIdeal) < ringKrullDim (R ⧸ 𝔮.asIdeal) :=
    ringKrullDim_quotient_lt_of_lt_primeSpectrum (R := R) 𝔮 𝔭 h𝔮_lt_𝔭
  have hq_le :
      ringKrullDim (R ⧸ 𝔮.asIdeal) ≤ Module.supportDim R M :=
    ringKrullDim_quotient_le_supportDim_of_mem_support (R := R) (M := M) 𝔮 h𝔮
  have hcontr : Module.supportDim R M < Module.supportDim R M := by
    calc
      Module.supportDim R M = ringKrullDim (R ⧸ 𝔭.asIdeal) := hdim.symm
      _ < ringKrullDim (R ⧸ 𝔮.asIdeal) := hlt
      _ ≤ Module.supportDim R M := hq_le
  exact (lt_irrefl (Module.supportDim R M)) hcontr

-- Proof sketch: apply the minimal-support conclusion of
-- `ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay` to the
-- prime point corresponding to `p`, then use Proposition `10.63.6` to pass from minimality in the
-- support to minimality among associated primes.
/-- If `M` is Cohen-Macaulay, then every associated prime of `M` is minimal among the associated
primes; equivalently, `M` has no embedded associated primes. -/
theorem minimal_mem_associatedPrimes_of_mem_associatedPrimes_of_cohenMacaulay
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    Minimal (· ∈ associatedPrimes R M) p := by
  let 𝔭 : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩
  have hmain :
      ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M ∧
        Minimal (· ∈ Module.support R M) 𝔭 :=
    ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R) (M := M) 𝔭 (by simpa [𝔭] using hp)
  -- Proposition `10.63.6` converts minimal support points into minimal associated primes.
  simpa [𝔭] using
    (minimal_support_iff_minimal_associatedPrimes (R := R) (M := M) 𝔭).mp hmain.2

end
