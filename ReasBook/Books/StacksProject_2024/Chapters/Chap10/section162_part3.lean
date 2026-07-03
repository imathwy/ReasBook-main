import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_162_17 (from Chap10) -/
universe u

open scoped PthPowerSubfield

/- 
Domain-style sampling:
- primary domain: Chapter 10 commutative algebra of `N-1`/`N-2`/Nagata conditions for discrete
  valuation rings and their finite overrings;
- sampled owner declarations:
  `IsN1Ring`,
  `IsN2Ring`,
  `NagataRing`,
  `finitePthPowerCoefficientSubring`;
- best owner abstraction: the public owners are already `IsN1Ring`, `IsN2Ring`, and `NagataRing`,
  while Example `10.119.5` contributes the concrete source-facing DVR
  `finitePthPowerCoefficientSubring k p` and its canonical finite overring `A[f]`;
- primitive vs. derived: primitive data are the DVR `A := finitePthPowerCoefficientSubring k p`,
  the finite overring `A[f]`, and the hypothesis `¬ FiniteDimensional (k^[p]) k`; generic
  finite-extension reductions are derived bridge API and should stay companion-only.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Helper for Example 10.162.17: in a discrete valuation ring every prime ideal is either the
zero ideal or the maximal ideal. -/
lemma prime_eq_bot_or_eq_maximalIdeal_of_isDiscreteValuationRing
    (p : Ideal R) [p.IsPrime] :
    p = ⊥ ∨ p = IsLocalRing.maximalIdeal R := by
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  ·
    -- The DVR characterization gives a unique nonzero prime ideal, so every nonzero prime is the
    -- maximal ideal.
    rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance with
      ⟨_, hunique⟩
    rcases hunique with ⟨P, hP, hPunique⟩
    have hpP : p = P := hPunique p ⟨hp0, inferInstance⟩
    have hmaxP : IsLocalRing.maximalIdeal R = P :=
      hPunique (IsLocalRing.maximalIdeal R)
        ⟨IsDiscreteValuationRing.not_a_field R, inferInstance⟩
    exact Or.inr (hpP.trans hmaxP.symm)

/-- Helper for Example 10.162.17: for a discrete valuation ring, the quotient by the zero ideal is
again `N-2` whenever the ring itself is `N-2`. -/
lemma isN2Ring_quotient_bot_of_isN2Ring [IsN2Ring R] :
    IsN2Ring (R ⧸ (⊥ : Ideal R)) := by
  let e : R ⧸ (⊥ : Ideal R) ≃+* R := RingEquiv.quotientBot R
  letI : IsNoetherianRing (R ⧸ (⊥ : Ideal R)) := isNoetherianRing_of_ringEquiv R e.symm
  letI : Algebra (R ⧸ (⊥ : Ideal R)) R := e.toRingHom.toAlgebra
  letI : Algebra R (R ⧸ (⊥ : Ideal R)) := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ (⊥ : Ideal R)) R :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change e (e.symm x) = x
      simp [e]
  letI : Module.Finite (R ⧸ (⊥ : Ideal R)) R :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ (⊥ : Ideal R)) R
  -- Apply `N-2` descent along the quotient-by-bottom equivalence viewed as a finite extension.
  exact isN2Ring_of_finite_extension (R := R ⧸ (⊥ : Ideal R)) (S := R) e.injective

/-- Helper for Example 10.162.17: an `N-2` discrete valuation ring is Nagata. -/
theorem nagataRing_of_isN2Ring_of_isDiscreteValuationRing [IsN2Ring R] :
    NagataRing R := by
  letI : IsNoetherianRing R := inferInstance
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  -- The source proof reduces the Nagata condition to the only two prime quotients of a DVR.
  obtain hp0 | hpmax :=
      prime_eq_bot_or_eq_maximalIdeal_of_isDiscreteValuationRing (R := R) p
  ·
    subst p
    exact isN2Ring_quotient_bot_of_isN2Ring (R := R)
  ·
    subst p
    -- The residue field of a local ring at its maximal ideal is a field, hence `N-2`.
    letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance

-- Proof sketch: a discrete valuation ring is Noetherian and has only two prime ideals, namely
-- `(0)` and the maximal ideal. The quotient by the maximal ideal is a field, hence `N-2`, so the
-- Nagata condition is equivalent to requiring the quotient by `(0)`, i.e. `R` itself, to be
-- `N-2`.
/-- Example 10.162.17 (1): a discrete valuation ring is Nagata if and only if it is `N-2`. -/
theorem nagataRing_iff_isN2Ring_of_isDiscreteValuationRing :
    NagataRing R ↔ IsN2Ring R := by
  constructor
  · intro hR
    letI : NagataRing R := hR
    letI : UniversallyJapaneseRing R := inferInstance
    infer_instance
  · intro hR
    letI : IsN2Ring R := hR
    -- The reverse implication is the DVR-specific quotient-by-primes argument packaged above.
    exact nagataRing_of_isN2Ring_of_isDiscreteValuationRing R

end

section

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

local notation "A" => finitePthPowerCoefficientSubring k p

-- Proof sketch: choose `f ∉ A` from Example `10.119.5`. If `A` were Nagata, then the finite
-- overring `A[f]` would also be Nagata by Proposition `10.162.16`; since `A[f]` is a local
-- domain, Lemma `10.162.13` would make it analytically unramified, contradicting Remark
-- `10.119.6`.
/-- Example 10.162.17 (2): if `k / k^p` is infinite, then the discrete valuation ring
`A := finitePthPowerCoefficientSubring k p` from Example `10.119.5` is not Nagata. -/
theorem finitePthPowerCoefficientSubring_not_nagataRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ NagataRing ↥A := by
  intro hA
  obtain ⟨f, hf⟩ := exists_not_mem_finitePthPowerCoefficientSubring k p hnfd
  letI : NagataRing ↥A := hA
  letI : Module.Finite ↥A ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
    finitePthPowerCoefficientAdjoinSubring_moduleFinite k p f
  letI : NagataRing ↥(finitePthPowerCoefficientAdjoinSubring k p f) :=
    nagataRing_of_finiteType ↥A
  exact
    finitePthPowerCoefficientAdjoinSubring_not_isAnalyticallyUnramified k p hf inferInstance

-- Proof sketch: combine the source-facing non-Nagata statement with part `(1)`.
/-- For the DVR `A := finitePthPowerCoefficientSubring k p` of Example `10.119.5`, infinite
`k / k^p` also forces failure of `N-2`. -/
theorem finitePthPowerCoefficientSubring_not_isN2Ring
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ IsN2Ring ↥A := by
  intro hA
  exact
    finitePthPowerCoefficientSubring_not_nagataRing k p hnfd
      ((nagataRing_iff_isN2Ring_of_isDiscreteValuationRing ↥A).2 hA)

end

section

variable (A : Type u) [CommRing A]

-- Proof sketch: if `A` were Nagata, then in particular it would be `N-2` by the first clause.
-- The example argues that for the specific finite extension `A ⊂ R = A[f]`, the ring `R` is not
-- `N-1`; this contradicts the Nagata property for finite domain extensions.
/-- Companion reduction: a finite domain extension of a Nagata ring cannot fail `N-1`. -/
theorem discreteValuationRing_not_nagataRing_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ NagataRing A := by
  intro hA
  letI : NagataRing A := hA
  letI : NagataRing R := nagataRing_of_finiteType A
  exact hR inferInstance

section

variable [IsDomain A] [IsDiscreteValuationRing A]

-- Proof sketch: combine the previous theorem with
-- `nagataRing_iff_isN2Ring_of_isDiscreteValuationRing`.
/-- A discrete valuation ring with a finite domain extension failing `N-1` is also not `N-2`. -/
theorem discreteValuationRing_not_isN2Ring_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ IsN2Ring A := by
  intro hA
  exact
    discreteValuationRing_not_nagataRing_of_finite_extension_not_isN1Ring
      A R hR
      ((nagataRing_iff_isN2Ring_of_isDiscreteValuationRing A).2 hA)

end

end

/-! ### Lemma_10_162_18 (from Chap10) -/
universe u

open IsLocalRing

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [NagataRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]

/-
Domain-style sampling:
- primary domain: local Nagata domains in characteristic `p`, `p`th-root descent from the
  maximal-ideal completion, and the analytically unramified obstruction coming from reduced
  completions;
- sampled owner and bridge declarations of the same kind:
  `IsAnalyticallyUnramified`,
  `isAnalyticallyUnramified_of_nagataRing`,
  `exists_derivation_with_nonzero_apply_of_not_exists_pth_root`,
  `X_pow_sub_C_irreducible_of_prime`;
- best owner abstraction: this item remains `source-facing`; its intrinsic ambient owner object is
  the canonical completion `AdicCompletion (maximalIdeal A) A`, while the reducedness input used in
  the proof is derived owner API through `IsAnalyticallyUnramified A`;
- primitive data: the local Nagata domain `A`, the characteristic-`p` prime `p`, the element
  `a : A`, and the chosen `p`th root in the canonical completion;
- derived API: analytic unramifiedness of `A`, irreducibility of `X ^ p - C a` when `a` has no
  `p`th root in the fraction field, and the derivation witness used to rule out reducedness of the
  completion in that case.

Source/core/bridge triage:
- `source-facing`: the descent statement for a `p`th root from the maximal-ideal completion back to
  `A`;
- `core/canonical`: `AdicCompletion (maximalIdeal A) A` and `IsAnalyticallyUnramified A`;
- `bridge/view`: the `AdjoinRoot (X ^ p - C a)` / derivation package used in the contradiction
  argument when no `p`th root exists in `A`.
-/

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

-- Proof sketch: let `α` be a `p`th root of the image of `a` in the completion. If `a` has no
-- `p`th root in `A`, then it has none in `FractionRing A`, so `A[X] / (X^p - a)` is a domain.
-- But the completion acquires a nilpotent element from `X - α`, while `A` is analytically
-- unramified by Lemma `10.162.13` because it is a local Nagata domain, contradiction.
/-- Lemma 10.162.18: if `(A, 𝔪)` is a Noetherian local domain which is Nagata, whose fraction
field has characteristic `p`, and the image of `a ∈ A` in the maximal-ideal completion of `A`
has a `p`th root, then `a` already has a `p`th root in `A`. -/
lemma exists_pth_root_of_exists_pth_root_in_completion {a : A}
    (hroot : ∃ α : ACompletion, α ^ p = algebraMap A ACompletion a) :
    ∃ b : A, b ^ p = a := sorry

end
