import Mathlib
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_15_1 (from Chap15) -/
open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R]

/- Domain triage: this item is `source-facing` in commutative algebra. The primitive owner data are
the canonical local-ring predicate `IsLocalRing R` and the pointwise weak-association predicate
`Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R)`. The class below is just the textbook
bundle of those two existing notions, not a replacement owner. -/
/-- Definition 15.15.1: a commutative ring `R` is auto-associated if it is local and its maximal
ideal is weakly associated to `R` as an `R`-module. -/
class IsAutoAssociatedRing : Prop extends IsLocalRing R where
  /-- The maximal ideal of an auto-associated ring is weakly associated to the regular module. -/
  maximalIdeal_weaklyAssociated :
    Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R)

variable {R}

/-- For a local ring, being auto-associated is exactly weak association of the maximal ideal to the
regular module. -/
theorem isAutoAssociatedRing_iff [IsLocalRing R] :
    IsAutoAssociatedRing R ↔ Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R) := by
  constructor
  · exact fun h ↦ h.maximalIdeal_weaklyAssociated
  · exact fun h ↦
      { toIsLocalRing := inferInstance
        maximalIdeal_weaklyAssociated := h }

namespace IsAutoAssociatedRing

/-- In an auto-associated ring, some torsion ideal `Ann_R(x)` is an ideal of definition. -/
theorem exists_torsionOf_isIdealOfDefinition [IsAutoAssociatedRing R] :
    ∃ x : R, (Ideal.torsionOf R R x).IsIdealOfDefinition := by
  obtain ⟨x, hx⟩ :
      ∃ x : R, maximalIdeal R ∈ (Ideal.torsionOf R R x).minimalPrimes :=
    IsAutoAssociatedRing.maximalIdeal_weaklyAssociated
  refine ⟨x, ?_⟩
  let J : Ideal R := Ideal.torsionOf R R x
  have hJminimal : J.minimalPrimes = {maximalIdeal R} := by
    ext q
    constructor
    · intro hq
      have hq_le : q ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
      exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
    · rintro rfl
      simpa [J] using hx
  rw [Ideal.isIdealOfDefinition_iff_isMaximal_radical, IsLocalRing.isMaximal_iff]
  rw [← Ideal.sInf_minimalPrimes, hJminimal, sInf_singleton]

end IsAutoAssociatedRing

end

section

variable (R : Type u) [Field R]

-- Proof sketch: a field is a local ring with maximal ideal `(0)`. The ideal `(0)` is associated
-- to the regular module via `1`, hence weakly associated by
-- `Ideal.IsAssociatedToModule.isWeaklyAssociatedToModule`.
/-- Fields are auto-associated rings. -/
instance : IsAutoAssociatedRing R where
  toIsLocalRing := Field.instIsLocalRing R
  maximalIdeal_weaklyAssociated := by
    rw [maximalIdeal_eq_bot]
    exact
      (show Ideal.IsAssociatedToModule R R (⊥ : Ideal R) from by
        rw [Ideal.isAssociatedToModule_iff_exists_torsionOf]
        refine ⟨Ideal.isPrime_bot, (1 : R), ?_⟩
        ext a
        rw [Ideal.mem_torsionOf_iff, Ideal.mem_bot]
        simp).isWeaklyAssociatedToModule

end

/-! ### Lemma_15_15_2 (from Chap15) -/
universe u

open Ideal IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace Ideal

/- Domain triage:
* primary domain: local commutative algebra of associated and weakly associated ideals.
* sampled owner abstractions in the same domain:
  `Ideal.IsWeaklyAssociatedToModule`, `Ideal.IsIdealOfDefinition`, `Ideal.IsIdealOfDefinition.isPrimary`,
  `Ideal.exists_pow_le_of_le_radical_of_fg`, and
  `IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition`.
* `core/canonical`: the owner APIs are `Ideal.torsionOf`, `Ideal.IsIdealOfDefinition`,
  `Ideal.exists_pow_le_of_le_radical_of_fg`, and the chapter witness theorem
  `IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition`.
* `source-facing`: `IsAutoAssociatedRing.annihilator_ne_bot_of_fg_of_ne_top` is the chapter's
  property `(P)` for auto-associated rings.
* `bridge/view`: the theorem below passes from the owner witness `Ideal.torsionOf R R x` through
  the canonical predicate `Ideal.IsIdealOfDefinition` to the annihilator conclusion for a given
  proper finitely generated ideal.
-/

local notation "AnnR[" x "]" => torsionOf R R x

-- Proof sketch: take `x` whose torsion ideal is an ideal of definition. For a proper finitely
-- generated ideal `I`, some power `I^n` lies in `Ideal.torsionOf R R x`. Choose `n` minimal.
-- Then `n > 0`, and `I^(n - 1)` contains an element `a` with `a * x ≠ 0`; minimality forces
-- `I * (a * x) = 0`, so `a * x` is a nonzero element of `I.annihilator`.
theorem annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition
    (x : R) (hxdef : AnnR[x].IsIdealOfDefinition)
    {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := by
  let J : Ideal R := AnnR[x]
  have hJ : J.IsIdealOfDefinition := by simpa [J] using hxdef
  have hIle : I ≤ J.radical := by
    calc
      I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hproper
      _ = J.radical := by simpa [Ideal.IsIdealOfDefinition] using hJ.symm
  have hpow : ∃ n : ℕ, I ^ n ≤ J := exists_pow_le_of_le_radical_of_fg hIle hI
  classical
  let n := Nat.find hpow
  have hn : I ^ n ≤ J := Nat.find_spec hpow
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    exact hJ.isPrimary.ne_top <| top_le_iff.mp <| by simpa [n, hn_zero] using hn
  have hnot : ¬ I ^ (n - 1) ≤ J := by
    intro hle
    have hmin : n ≤ n - 1 := Nat.find_min' hpow <| by simpa [n] using hle
    omega
  rw [SetLike.not_le_iff_exists] at hnot
  rcases hnot with ⟨a, ha, hax⟩
  have hy : a * x ∈ I.annihilator := by
    rw [Submodule.mem_annihilator]
    intro b hb
    have hba : b * a ∈ I ^ n := by
      have hba' : b * a ∈ I ^ (n - 1) * I := by
        simpa [mul_comm] using Ideal.mul_mem_mul_rev ha hb
      have hn_eq : n = (n - 1) + 1 := by omega
      rw [hn_eq, pow_succ]
      exact hba'
    have hkill : (b * a) * x = 0 := by
      simpa [J, mem_torsionOf_iff] using hn hba
    simpa [mul_assoc, mul_comm, mul_left_comm] using hkill
  intro hann
  have hax_ne_zero : a * x ≠ 0 := by
    simpa [J, mem_torsionOf_iff] using hax
  have hzero : a * x = 0 := by
    have : a * x ∈ (⊥ : Ideal R) := by simpa [hann] using hy
    simpa [mem_bot] using this
  exact hax_ne_zero hzero

end Ideal

section

variable [IsAutoAssociatedRing R]

namespace IsAutoAssociatedRing

/-- Lemma 15.15.2: in an auto-associated ring, every proper finitely generated ideal has nonzero
annihilator ideal. This is the property `(P)` of an auto-associated ring. -/
theorem annihilator_ne_bot_of_fg_of_ne_top {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := by
  obtain ⟨x, hxdef⟩ :
      ∃ x : R, (torsionOf R R x).IsIdealOfDefinition :=
    exists_torsionOf_isIdealOfDefinition
  exact
    Ideal.annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition x hxdef hI hproper

end IsAutoAssociatedRing

end

end

/-! ### Lemma_15_15_3 (from Chap15) -/
universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]

/- Domain triage:
- primary domain: universal injectivity of linear maps between projective modules over a
  commutative ring;
- sampled owner declarations:
  `LinearMap.UniversallyInjective`,
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  `proper_fg_ideal_annihilator_ne_bot_tfae`;
- best owner abstraction: `LinearMap.UniversallyInjective`;
- primitive data: the ring `R`, the projective modules `N` and `M`, and a linear map `u : N →ₗ[R] M`;
- derived API: the source-facing criterion below, with the `injective → universallyInjective`
  direction obtained canonically from clause `(1) ↔ (2)` of
  `proper_fg_ideal_annihilator_ne_bot_tfae`.

Layering:
- `source-facing`: the theorem below;
- `core/canonical`: `LinearMap.UniversallyInjective`;
- `bridge/view`: `proper_fg_ideal_annihilator_ne_bot_tfae`.
-/

-- Proof sketch: the forward implication holds for any ring by taking the tensor factor `Q = R`.
-- For the converse, use projectivity to split both source and target off free modules, reduce to
-- finite free source by expressing a projective module as a filtered colimit of finite free
-- modules, and then prove the finite free case by induction on the rank using property `(P)` to
-- split off the first basis vector.
/-- Lemma 15.15.3: if `R` has property `(P)` of Lemma 15.15.2, meaning every proper finitely
generated ideal of `R` has nonzero annihilator, then a homomorphism `u : N →ₗ[R] M` of
projective `R`-modules is universally injective if and only if it is injective. -/
theorem universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) (u : N →ₗ[R] M) :
    u.UniversallyInjective ↔ Function.Injective u := by
  constructor
  · intro hu
    sorry
  · intro hu
    exact
      (proper_fg_ideal_annihilator_ne_bot_iff_injective_projective_maps_universallyInjective.mp
        hP) u hu

end

end LinearMap

/-! ### Lemma_15_15_4 (from Chap15) -/
universe u v w

section

variable {R : Type u} [CommRing R]

-- Proof sketch: `(1) → (2)` is Lemma `15.15.3`. The equivalence of `(3)` and `(4)` is the
-- standard splitting criterion for short exact sequences with finite projective end terms, where
-- clause `(4)` is phrased via the canonical owner property `IsComplemented` on submodules, and
-- `(2) → (3)` follows from the universal-exactness splitting criterion of Lemma `10.82.4`
-- applied to `0 → N → M → coker u → 0`. Clause `(5)` is the special case of `(4)` for
-- submodules of finite free modules of rank `n`, while `(5) → (1)` is proved by applying a
-- splitting obstruction to the map `R → Rⁿ` determined by generators of a proper finitely
-- generated ideal and extracting a nonzero annihilator element from its kernel.
/-- Lemma 15.15.4: for a commutative ring `R`, the following are equivalent: every proper finitely
generated ideal of `R` has nonzero annihilator, every injective map of projective `R`-modules is
universally injective, the cokernel of an injective map of finite projective `R`-modules is finite
projective, every finite projective submodule of a finite projective `R`-module is a direct
summand, and every injective map `R → R^{⊕ n}` is split. -/
theorem proper_fg_ideal_annihilator_ne_bot_tfae :
    List.TFAE
      [ (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)),
        (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
            {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective),
        (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
            {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u →
              Module.Finite R (M ⧸ u.range) ∧ Module.Projective R (M ⧸ u.range)),
        (∀ {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (N : Submodule R M) [Module.Finite R N] [Module.Projective R N],
            IsComplemented N),
        (∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
            ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id) ] := sorry

/-- Clause `(1) ↔ (2)` of Lemma `15.15.4`: over a commutative ring `R`, every proper finitely
generated ideal has nonzero annihilator if and only if every injective map of projective
`R`-modules is universally injective. -/
theorem proper_fg_ideal_annihilator_ne_bot_iff_injective_projective_maps_universallyInjective :
    (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) ↔
      (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
          {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
          (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective) := by
  simpa using proper_fg_ideal_annihilator_ne_bot_tfae.out 0 1 rfl rfl

end

/-! ### Example_15_15_5 (from Chap15) -/
open MvPolynomial

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "I∞" =>
  Ideal.span (Set.range fun i : ℕ ↦ ((X i : MvPolynomial ℕ k) ^ 2))
local notation "R∞" => infiniteSquareZeroPolynomialQuotient k
local notation "F∞" => ℕ →₀ R∞

noncomputable local instance : Module R∞ R∞ := Semiring.toModule
noncomputable local instance : Module R∞ F∞ := Finsupp.module ℕ R∞

/- Domain triage:
* primary domain: commutative algebra of local rings and weak association.
* sampled owner abstractions:
  `IsAutoAssociatedRing`,
  `isAutoAssociatedRing_iff`,
  `infiniteSquareZeroPolynomialQuotient`,
  `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv`.
* layer choice: the explicit shift map below is the `source-facing` witness, while
  `IsAutoAssociatedRing` is the chapter's `core/canonical` owner for the ring-side clause of
  Example `15.15.5`; that clause should therefore be exposed as an instance rather than a
  parallel theorem.
* primitive data: the quotient ring `R∞` and the basis prescription `e_i ↦ f_i - x_i f_{i + 1}`.
* derived API: the square-zero identities, the induced linear map `squareZeroShiftMap`, and its
  injective non-split behavior.
-/

/-- The image of the variable `X i` in the square-zero polynomial quotient. -/
abbrev squareZeroVariable (i : ℕ) : R∞ :=
  Ideal.Quotient.mk I∞ (X i : MvPolynomial ℕ k)

-- Proof sketch: each square `X i ^ 2` lies in the defining ideal `I∞`, so its image in the
-- quotient is zero.
/-- Each coordinate variable is square-zero in the quotient ring. -/
@[simp] theorem squareZeroVariable_sq_eq_zero (i : ℕ) :
    squareZeroVariable k i ^ (2 : ℕ) = 0 := sorry

private def squareZeroShiftFamily (i : ℕ) : F∞ :=
  Finsupp.single i 1 - Finsupp.single (i + 1) (squareZeroVariable k i)

/-- The map `e_i ↦ f_i - x_i f_{i + 1}` on the countable free module over the square-zero
polynomial quotient. -/
noncomputable def squareZeroShiftMap :
    F∞ →ₗ[R∞] F∞ :=
  Finsupp.linearCombination R∞ (squareZeroShiftFamily k)

-- Proof sketch: unfold `squareZeroShiftMap`, use `Finsupp.linearCombination_single`, and rewrite
-- scalar multiplication on `Finsupp.single`.
/-- On a single basis term, the shift map acts by `e_i r ↦ e_i r - e_{i+1} (x_i r)`. -/
@[simp] theorem squareZeroShiftMap_single (i : ℕ) (r : R∞) :
    squareZeroShiftMap k (Finsupp.single i r) =
      Finsupp.single i r -
        Finsupp.single (i + 1) (squareZeroVariable k i * r) := sorry

/-- Example 15.15.5 (ring side): the square-zero quotient
`k[x₀, x₁, x₂, \ldots] / (x_i^2)` is an auto-associated local ring. -/
instance :
    IsAutoAssociatedRing R∞ := by
  sorry

-- Proof sketch: prove injectivity by checking linear independence on each finite partial family
-- of images `u(e₁), ..., u(eₙ)`. To rule out a splitting, tensor with the residue field `k` to get
-- a bijection via `infiniteSquareZeroPolynomialQuotientResidueFieldEquiv k`; a left inverse would
-- then force surjectivity, but `f₁` would require the infinite preimage
-- `e₁ + x₁ e₂ + x₁ x₂ e₃ + ⋯`, which is not finitely supported.
/-- Companion to Example 15.15.5 (module side): over the auto-associated local ring
`R = k[x₀, x₁, x₂, \ldots] / (x_i^2)`, whose residue field is canonically `k`, the map
`u(e_i) = f_i - x_i f_{i + 1}` on the free module `ℕ →₀ R` is injective but not a split
injection. -/
theorem squareZeroShiftMap_injective_not_split :
    Function.Injective (squareZeroShiftMap k) ∧
      ¬ ∃ v : F∞ →ₗ[R∞] F∞,
          v ∘ₗ squareZeroShiftMap k = LinearMap.id := sorry

end

/-! ### Lemma_15_15_6 (from Chap15) -/
universe u

open scoped Pointwise
open RingTheory.Sequence

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace Ideal

/-- In a Noetherian local ring, the length-`1` source-style condition for `I` is equivalent to the
owner depth inequality `1 ≤ I.depth R`. -/
theorem eq_top_or_exists_isRegular_iff_one_le_depth (I : Ideal R) :
    (I = ⊤ ∨ ∃ x ∈ I, IsRegular x) ↔ (1 : WithTop ℕ) ≤ I.depth R := by
  constructor
  · rintro (hI | ⟨x, hxI, hxreg⟩)
    · exact (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <| Or.inl hI
    · by_cases hxunit : IsUnit x
      · exact
          (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <|
            Or.inl (I.eq_top_of_isUnit_mem hxI hxunit)
      · refine (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp ?_
        refine Or.inr ⟨[x], ?_, ?_, by simp⟩
        · have hxsmul : IsSMulRegular R x := hxreg.left.isSMulRegular
          have hxsmul_ne_top : x • (⊤ : Ideal R) ≠ ⊤ := by
            intro htop
            apply hxunit
            have hspanTop : Ideal.span ({x} : Set R) = ⊤ := by
              calc
                Ideal.span ({x} : Set R) = Ideal.span ({x} : Set R) • (⊤ : Ideal R) := by simp
                _ = x • (⊤ : Ideal R) := by rw [Submodule.ideal_span_singleton_smul]
                _ = ⊤ := htop
            exact Ideal.span_singleton_eq_top.mp hspanTop
          let _ : Nontrivial (QuotSMulTop x R) := Submodule.Quotient.nontrivial_iff.2 <| by
            simpa [QuotSMulTop] using hxsmul_ne_top
          refine IsRegular.cons hxsmul ?_
          simpa using IsRegular.nil R (QuotSMulTop x R)
        · simpa using (Ideal.span_singleton_le_iff_mem I).2 hxI
  · rintro hdepth
    rcases (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mpr hdepth with
      hI | ⟨rs, hrs, hrs_le, hrs_len⟩
    · exact .inl hI
    · rcases List.length_eq_one_iff.mp hrs_len with ⟨x, rfl⟩
      have hxsmul : IsSMulRegular R x := by
        exact ((isRegular_cons_iff R x []).mp (by simpa using hrs)).1
      refine .inr ⟨x, ?_, ?_⟩
      · exact hrs_le (Ideal.subset_span (by simp : x ∈ {r | r ∈ ([x] : List R)}))
      · refine ⟨hxsmul.isLeftRegular, ?_⟩
        simpa [IsRightRegular, IsSMulRegular, smul_eq_mul, mul_comm] using hxsmul

end Ideal

end

namespace LinearMap

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {m n : ℕ}

/- Domain triage:
* primary domain: injectivity criteria for maps of finite free modules over a local ring, governed
  upstream by the Buchsbaum--Eisenbud exactness criterion for finite free complexes;
* sampled owner declarations of the same kind:
  `LinearMap.exteriorRank`,
  `LinearMap.rankMinorIdeal`,
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion`;
* core/canonical owner: the Chapter 10 Buchsbaum--Eisenbud criterion, specialized here to a
  two-term complex, with the Noetherian ideal-theoretic clause canonically expressed via
  `Ideal.depth`;
* source-facing layer: the injectivity criterion with annihilator zero and its regular-element
  reformulation below;
* bridge/view layer: the depth reformulation and the local length-`1` regular-sequence bridge
  between `Ideal.depth` and `I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x`.

Primitive data are only the map `φ`, its owner invariants `exteriorRank φ` and `I(φ)`, and the
ambient local-ring hypotheses. The annihilator and nonzerodivisor conditions are derived API, so
this file should reuse the chapter owner abstraction instead of introducing a parallel determinantal
package.
-/

-- Proof sketch: for the forward implication, reduce to weakly associated primes of the local
-- ring and use the auto-associated criteria from the preceding lemmas to show that the rank-minor
-- ideal survives in every weakly associated residue field, forcing full exterior rank and trivial
-- annihilator. For the converse, use the full-rank condition to write the identity on `R^m`
-- locally through finitely many maximal minors, and then the trivial annihilator of the rank-minor
-- ideal kills every kernel element.
/-- Lemma 15.15.6: for a map `φ : R^m → R^n` of finite free modules over a local ring, `φ` is
injective if and only if it has exterior rank `m` and the annihilator of its rank-minor ideal
`I(φ)` is zero. -/
theorem injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ)).annihilator = (⊥ : Ideal R) := sorry

section Noetherian

variable [IsNoetherianRing R]

-- Proof sketch: this is the `i = 0` depth form of the Chapter 10 Buchsbaum--Eisenbud owner
-- specialized to the two-term complex attached to `φ`, where `1 ≤ depth I(φ)` is the canonical
-- owner-side replacement for the length-`1` regular-sequence clause.
/-- Companion owner-style reformulation: over a Noetherian local ring, injectivity is equivalently
detected by full exterior rank together with positive depth of the rank-minor ideal. -/
theorem injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (1 : WithTop ℕ) ≤ (I(φ)).depth R := sorry

-- Proof sketch: combine the owner-style depth criterion above with the Noetherian local bridge
-- identifying positive depth with either `I(φ) = ⊤` or the presence of a regular element in
-- `I(φ)`.
/-- In a Noetherian local ring, injectivity is equivalently detected by full exterior rank together
with the rank-minor ideal being the unit ideal or containing a nonzerodivisor. -/
theorem injective_iff_exteriorRank_eq_and_rankMinorIdeal_eq_top_or_exists_isRegular
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x) := by
  rw [injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal]
  rw [Ideal.eq_top_or_exists_isRegular_iff_one_le_depth]

end Noetherian

end

end LinearMap

/-! ### Lemma_15_15_7 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/- Domain-style sampling:
- primary domain: quotient duality and annihilator calculus for submodules of finite free modules;
- sampled owner declarations of the same kind:
  `Module.Free.chooseBasis`,
  `Submodule.dualQuotEquivDualAnnihilator`,
  `Submodule.dualAnnihilator_eq_bot_iff'`,
  `LinearMap.ker_dualMap_eq_dualAnnihilator_range`;
- best owner abstraction: the source-facing theorem should be stated for an intrinsic endomorphism
  `φ : M →ₗ[R] M` of a finite free module `M`, while
  `Submodule.dualQuotEquivDualAnnihilator` is the canonical owner identifying the dual of a
  quotient with the dual annihilator of the defining submodule;
- source/core/bridge triage:
  `source-facing`: every `R`-linear functional on the cokernel of an injective endomorphism of a
    finite free module is zero;
  `core/canonical`: the owner-side vanishing statement
    `(LinearMap.range φ).dualAnnihilator = ⊥`;
  `bridge/view`: `Submodule.dualQuotEquivDualAnnihilator` and
    `Submodule.dualAnnihilator_eq_bot_iff'`.

Primitive data are only the endomorphism `φ` and the finite free owner data on `M`; its range is
derived from `φ`. The quotient-dual vanishing statement is derived API from the
quotient/annihilator owner layer, so this file should keep only the source-facing theorem public
and use the owner-level equality internally as a bridge.
-/

-- Proof sketch: `Submodule.dualQuotEquivDualAnnihilator` identifies the dual of the quotient by
-- `LinearMap.range φ` with the dual annihilator of `LinearMap.range φ`. The private owner-side
-- bridge below shows that annihilator is `⊥`, so the quotient dual is a subsingleton and every
-- functional is zero.
private theorem range_dualAnnihilator_eq_bot_of_injective_free_endomorphism
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    (LinearMap.range φ).dualAnnihilator = ⊥ := by
  sorry

/-- Lemma 15.15.7: if `φ : M → M` is an injective endomorphism of a finite free `R`-module, then
every `R`-linear functional on its cokernel is zero. -/
theorem quotient_range_dual_eq_zero_of_injective_free_endomorphism
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) (f : Module.Dual R (M ⧸ LinearMap.range φ)) :
    f = 0 := by
  have hRange : (LinearMap.range φ).dualAnnihilator = ⊥ :=
    range_dualAnnihilator_eq_bot_of_injective_free_endomorphism φ hφ
  have hsub : Subsingleton (Module.Dual R (M ⧸ LinearMap.range φ)) := by
    simpa using (Submodule.dualAnnihilator_eq_bot_iff').mp hRange
  letI : Subsingleton (Module.Dual R (M ⧸ LinearMap.range φ)) := hsub
  exact Subsingleton.elim f 0

end
