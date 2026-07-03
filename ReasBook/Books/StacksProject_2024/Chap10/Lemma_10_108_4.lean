import Mathlib
import StacksProject_2024.Chap10.Lemma_10_108_2
import StacksProject_2024.Chap10.Lemma_10_108_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

namespace Ideal

/-- Helper for Lemma 10.108.4: the textbook ideal
`{x : R | ∃ y ∈ J, x = x * y}` contains `0`. -/
private theorem pointwiseFixedIdeal_zero_mem (J : Ideal R) :
    (0 : R) ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- The zero element is fixed by multiplication with `0 ∈ J`.
  exact ⟨0, J.zero_mem, by simp⟩

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under addition. -/
private theorem add_fixed_by_pointwise_witness {x y f g : R}
    (hx : x = x * f) (hy : y = y * g) :
    x + y = (x + y) * (f + g - f * g) := by
  -- Rewrite the mixed terms using the original fixed-point identities.
  have hxg : x * g = x * (f * g) := by
    calc
      x * g = (x * f) * g := by rw [← hx]
      _ = x * (f * g) := by rw [mul_assoc]
  have hyf : y * f = y * (f * g) := by
    calc
      y * f = (y * g) * f := by rw [← hy]
      _ = y * (g * f) := by rw [mul_assoc]
      _ = y * (f * g) := by rw [mul_comm g f]
  -- Expand the textbook witness and cancel the cross terms explicitly.
  calc
    x + y = x * f + y := by rw [← hx]
    _ = x * f + y * g := by rw [← hy]
    _ = x * f + x * g - x * (f * g) + (y * f + y * g - y * (f * g)) := by
      rw [hxg, hyf]
      ring
    _ = (x + y) * (f + g - f * g) := by ring

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under addition. -/
private theorem pointwiseFixedIdeal_add_mem {J : Ideal R} {x y : R}
    (hx : x ∈ { x : R | ∃ y ∈ J, x = x * y })
    (hy : y ∈ { x : R | ∃ y ∈ J, x = x * y }) :
    x + y ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- Use the textbook witness `f + g - f * g` coming from the two fixed-point relations.
  rcases hx with ⟨f, hf, hxf⟩
  rcases hy with ⟨g, hg, hyg⟩
  refine ⟨f + g - f * g, ?_, ?_⟩
  · -- Ideal closure gives membership of the textbook witness in `J`.
    exact J.sub_mem (J.add_mem hf hg) (J.mul_mem_right g hf)
  · -- The standalone algebra lemma packages the verification-left-to-the-reader identity.
    exact add_fixed_by_pointwise_witness hxf hyg

/-- Helper for Lemma 10.108.4: the textbook relation `x = x * y` is stable under multiplication
by ring elements. -/
private theorem pointwiseFixedIdeal_smul_mem {J : Ideal R} (r : R) {x : R}
    (hx : x ∈ { x : R | ∃ y ∈ J, x = x * y }) :
    r * x ∈ { x : R | ∃ y ∈ J, x = x * y } := by
  -- The same witness works after multiplying the fixed element by `r`.
  rcases hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, by simpa [mul_assoc] using congrArg (fun t : R ↦ r * t) hxy⟩

/-- Helper for Lemma 10.108.4: the textbook multiplicative set `(R \ p)(1 + J)`. -/
private def primeComplMulOneAdd (p : PrimeSpectrum R) (J : Ideal R) : Submonoid R where
  carrier := { x : R | ∃ a ∈ p.asIdeal.primeCompl, ∃ b ∈ J.oneAdd, x = a * b }
  one_mem' := by
    refine ⟨1, ?_, 1, (Ideal.mem_oneAdd_iff (I := J) (x := (1 : R))).2 ⟨0, J.zero_mem, by simp⟩, by simp⟩
    show (1 : R) ∉ p.asIdeal
    intro h1
    exact p.2.1 ((Ideal.eq_top_iff_one _).2 h1)
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, ?_, b * d, J.oneAdd.mul_mem hb hd, by ring⟩
    show a * c ∈ p.asIdeal.primeCompl
    intro hac
    exact (p.2.mem_or_mem hac).elim ha hc

/-- Helper for Lemma 10.108.4: the source ideal
`I = {x : R | ∃ y ∈ J, x = x * y}`. -/
def pointwiseFixedIdeal (J : Ideal R) : Ideal R where
  carrier := { x : R | ∃ y ∈ J, x = x * y }
  zero_mem' := pointwiseFixedIdeal_zero_mem J
  add_mem' := fun hx hy ↦ pointwiseFixedIdeal_add_mem hx hy
  smul_mem' := fun r _ hx ↦ pointwiseFixedIdeal_smul_mem r hx

/-- Helper for Lemma 10.108.4: the textbook source ideal is contained in `J`. -/
theorem pointwiseFixedIdeal_le (J : Ideal R) :
    pointwiseFixedIdeal J ≤ J := by
  -- Any witness `x = x * y` with `y ∈ J` puts `x` back into `J`.
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩
  rw [hxy]
  exact J.mul_mem_left x hy

/-- Helper for Lemma 10.108.4: if `x = x * y`, then `x = x * y ^ (n + 1)` for every `n`. -/
private theorem eq_mul_pow_succ_of_eq_mul {x y : R} (hxy : x = x * y) :
    ∀ n : ℕ, x = x * y ^ (n + 1) := by
  -- First show that every positive power of `y` still fixes `x`.
  have hpow : ∀ n : ℕ, x * y ^ n = x := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        calc
          x * y ^ (n + 1) = (x * y ^ n) * y := by rw [pow_succ, mul_assoc]
          _ = x * y := by rw [ihn]
          _ = x := by rw [← hxy]
  intro n
  exact (hpow (n + 1)).symm

-- Proof sketch: identify `V(I)` with `Spec (R ⧸ I)` via the quotient-spectrum equivalence. Since
-- `I` is pure, the quotient map `R → R ⧸ I` is flat, so `Spec (R ⧸ I) → Spec R` is generalizing by
-- `RingHom.Flat.generalizingMap_comap`. Transporting this along the quotient identification shows
-- that `V(I)` is stable under generalization.
/-- The zero locus of a pure ideal is stable under generalization in `Spec(R)`. -/
theorem stableUnderGeneralization_zeroLocus_of_pure (I : Ideal R) (hI : I.Pure) :
    StableUnderGeneralization (zeroLocus (I : Set R)) := by
  -- The quotient map realizes `V(I)` as the range of `Spec(R ⧸ I) → Spec(R)`.
  let image : Set (PrimeSpectrum R) := Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  have himage : StableUnderGeneralization image := by
    letI : (Ideal.Quotient.mk I).Flat := hI
    exact (RingHom.Flat.generalizingMap_comap (f := Ideal.Quotient.mk I) hI).stableUnderGeneralization_range
  have hrange : image = zeroLocus (I : Set R) := by
    simpa [image, Ideal.mk_ker] using
      (range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  simpa [image, hrange] using himage

/-- Helper for Lemma 10.108.4: for a radical ideal `J` whose zero locus is stable under
generalization, the source ideal `pointwiseFixedIdeal J` cuts out the same closed subset. -/
theorem zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization {J : Ideal R}
    (hJrad : J.IsRadical) (hJgen : StableUnderGeneralization (zeroLocus (J : Set R))) :
    zeroLocus (pointwiseFixedIdeal J : Set R) = zeroLocus (J : Set R) := by
  apply Set.Subset.antisymm
  · intro p hp
    -- Route correction: keep the Stacks multiplicative-set argument instead of switching to a
    -- clopen/idempotent classification of the closed subset.
    let T : Submonoid R := primeComplMulOneAdd p J
    have hzero_not_mem : (0 : R) ∉ T := by
      intro hzero
      rcases hzero with ⟨a, ha, b, hb, hab⟩
      rcases (Ideal.mem_oneAdd_iff (I := J)).1 hb with ⟨y, hy, hby⟩
      have hab' : a * (1 + y) = 0 := by
        simpa [hby] using hab.symm
      have ha_mem : a ∈ pointwiseFixedIdeal J := by
        refine ⟨-y, J.neg_mem hy, ?_⟩
        calc
          a = a * 1 := by simp
          _ = a * ((1 + y) + (-y)) := by ring
          _ = a * (1 + y) + a * (-y) := by rw [mul_add]
          _ = a * (-y) := by rw [hab', zero_add]
      have ha_in_p : a ∈ p.asIdeal := hp (show a ∈ pointwiseFixedIdeal J from ha_mem)
      exact ha ha_in_p
    have hdisj0 : Disjoint ((⊥ : Ideal R) : Set R) (T : Set R) := by
      rw [Set.disjoint_left]
      intro x hxbot hxT
      have hx0 : x = 0 := by simpa using hxbot
      exact hzero_not_mem (by simpa [hx0] using hxT)
    obtain ⟨q, hqprime, -, hqdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) T hdisj0
    have hqle : q ≤ p.asIdeal := by
      intro x hxq
      by_contra hxp
      have hxT : x ∈ T := by
        refine ⟨x, hxp, 1, (Ideal.mem_oneAdd_iff (I := J) (x := (1 : R))).2 ⟨0, J.zero_mem, by simp⟩, by simp⟩
      exact hqdisj.le_bot ⟨hxq, hxT⟩
    have hq_oneAdd_disj : Disjoint (q : Set R) (J.oneAdd : Set R) := by
      rw [Set.disjoint_left]
      intro x hxq hxone
      have hxT : x ∈ T := by
        refine ⟨1, ?_, x, hxone, by simp⟩
        show (1 : R) ∉ p.asIdeal
        intro h1
        exact p.2.1 ((Ideal.eq_top_iff_one _).2 h1)
      exact hqdisj.le_bot ⟨hxq, hxT⟩
    have hproper : q ⊔ J ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ q ⊔ J := by simpa [htop]
      rcases Submodule.mem_sup.1 h1 with ⟨a, haq, b, hbj, hab⟩
      have hone_eq : 1 - b = a := by
        calc
          1 - b = a + b - b := by rw [hab]
          _ = a := by ring
      have hone_sub : 1 - b ∈ q := by
        simpa [hone_eq] using haq
      have hone_mem : 1 - b ∈ J.oneAdd := by
        exact (Ideal.mem_oneAdd_iff (I := J) (x := 1 - b)).2 ⟨-b, J.neg_mem hbj, by ring⟩
      exact hq_oneAdd_disj.le_bot ⟨hone_sub, hone_mem⟩
    obtain ⟨m, hmmax, hqmJ⟩ := Ideal.exists_le_maximal (q ⊔ J) hproper
    let qSpec : PrimeSpectrum R := ⟨q, hqprime⟩
    let mSpec : PrimeSpectrum R := ⟨m, hmmax.isPrime⟩
    have hm_mem : mSpec ∈ zeroLocus (J : Set R) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      show J ≤ m
      exact le_trans le_sup_right hqmJ
    have hqm : qSpec ≤ mSpec := by
      show q ≤ m
      exact le_trans le_sup_left hqmJ
    have hq_mem : qSpec ∈ zeroLocus (J : Set R) := by
      exact hJgen ((PrimeSpectrum.le_iff_specializes qSpec mSpec).mp hqm) hm_mem
    rw [PrimeSpectrum.mem_zeroLocus] at hq_mem ⊢
    exact le_trans hq_mem hqle
  · -- The source ideal is contained in `J`, so its zero locus contains `V(J)`.
    exact PrimeSpectrum.zeroLocus_anti_mono_ideal (pointwiseFixedIdeal_le J)

/-- Helper for Lemma 10.108.4: if `J` is contained in the radical of its source ideal, then the
source ideal is pure. -/
theorem pointwiseFixedIdeal_pure_of_le_radical (J : Ideal R)
    (hJle : J ≤ (pointwiseFixedIdeal J).radical) :
    (pointwiseFixedIdeal J).Pure := by
  -- Use clause `(5)` of Lemma `10.108.2`, replacing the original witness in `J` by a power that
  -- already lies in the source ideal.
  exact ((Ideal.pure_tfae (pointwiseFixedIdeal J)).out 4 0).mp <| by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases (Ideal.mem_radical_iff.mp (hJle hy)) with ⟨n, hn⟩
    cases n with
    | zero =>
        have htop : pointwiseFixedIdeal J = ⊤ :=
          (pointwiseFixedIdeal J).eq_top_of_isUnit_mem (by simpa using hn) (by simpa)
        refine ⟨1, by simpa [htop], ?_⟩
        simp
    | succ n =>
        refine ⟨y ^ (n + 1), hn, ?_⟩
        simpa using eq_mul_pow_succ_of_eq_mul hxy n

end Ideal

-- Proof sketch: well-definedness is `Ideal.stableUnderGeneralization_zeroLocus_of_pure` together
-- with `PrimeSpectrum.isClosed_zeroLocus`. Injectivity is Lemma `10.108.3`, i.e.
-- `Ideal.zeroLocus_inj_of_pure`. For surjectivity, write a closed generalization-stable subset as
-- `V(J)` for a radical ideal `J`, then define the ideal `I = {x | ∃ y ∈ J, x = x * y}` from the
-- Stacks proof and use Lemma `10.108.2` to show `I` is pure and still satisfies `V(I) = V(J)`.
/-- Lemma 10.108.4: the rule `I ↦ V(I)` gives a bijection between pure ideals of `R` and closed
subsets of `Spec(R)` that are stable under generalization. -/
theorem pureIdeal_zeroLocus_bijective :
    Function.Bijective
      (fun I : { I : Ideal R // I.Pure } ↦
        (⟨zeroLocus (I.1 : Set R), isClosed_zeroLocus (I.1 : Set R),
          Ideal.stableUnderGeneralization_zeroLocus_of_pure I.1 I.2⟩ :
            { Z : Set (PrimeSpectrum R) // IsClosed Z ∧ StableUnderGeneralization Z })) := by
  constructor
  · intro I J hIJ
    -- Injectivity is the canonical owner theorem for pure ideals with the same zero locus.
    apply Subtype.ext
    letI : I.1.Pure := I.2
    letI : J.1.Pure := J.2
    exact (Ideal.zeroLocus_inj_of_pure).mp (congrArg Subtype.val hIJ)
  · intro Z
    -- Start from the radical ideal defining the given closed subset.
    let J : Ideal R := PrimeSpectrum.vanishingIdeal Z.1
    have hJrad : J.IsRadical := PrimeSpectrum.isRadical_vanishingIdeal Z.1
    have hZeq : zeroLocus (J : Set R) = Z.1 := by
      dsimp [J]
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed.mpr Z.2.1]
    have hJgen : StableUnderGeneralization (zeroLocus (J : Set R)) := by
      simpa [hZeq] using Z.2.2
    have hzero :
        zeroLocus (Ideal.pointwiseFixedIdeal J : Set R) = Z.1 := by
      exact
        (Ideal.zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization
          hJrad hJgen).trans hZeq
    have hJle : J ≤ (Ideal.pointwiseFixedIdeal J).radical := by
      simpa [hJrad.radical] using Eq.le ((PrimeSpectrum.zeroLocus_eq_iff).mp
        (Ideal.zeroLocus_pointwiseFixedIdeal_eq_of_radical_of_stableUnderGeneralization
          hJrad hJgen)).symm
    have hPure : (Ideal.pointwiseFixedIdeal J).Pure :=
      Ideal.pointwiseFixedIdeal_pure_of_le_radical J hJle
    refine ⟨⟨Ideal.pointwiseFixedIdeal J, hPure⟩, ?_⟩
    apply Subtype.ext
    exact hzero

end
