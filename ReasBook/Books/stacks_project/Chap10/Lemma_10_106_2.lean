import Mathlib
import stacks_project.Chap10.Lemma_10_106_1
import stacks_project.Chap10.Lemma_10_106_1.StageClassAPI

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "m" => maximalIdeal R
local notation "κ" => ResidueField R
local notation "grR" => idealAssociatedGradedRing m

/- Domain-style sampling pass.

Primary domain: local commutative algebra of regular local rings and their basic derived
ring-theoretic consequences.

Sampled owner declarations:
* `IsRegularLocalRing` and `IsRegularLocalRing.iff_finrank_cotangentSpace` from mathlib's
  regular-local-ring owner API;
* the direct downstream owner use `regularLocalRing_uniqueFactorizationMonoid` in
  `Chap15/Lemma_15_122_2.lean`, which consumes the domain consequence through typeclass search.

Best owner abstraction: the ambient owner is `IsRegularLocalRing R`. The target declaration here is
derived API: the canonical ring-theoretic consequence that such an `R` is a domain.

Primitive vs. derived:
* primitive data: only the owner hypothesis `[IsRegularLocalRing R]`;
* derived API: the instance `IsDomain R`.

Source/core/bridge triage:
* source-facing: the Stacks lemma asserting that a regular local ring is a domain;
* core/canonical: the owner predicate `IsRegularLocalRing R`;
* bridge/view: this file's derived typeclass instance `IsDomain R`. -/

/-- Helper for Lemma 10.106.2: every nonzero element lies in some maximal power of the maximal
ideal. -/
private theorem exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (x : R) (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ m ^ n ∧ x ∉ m ^ (n + 1) := by
  classical
  have hintersection : (⨅ n : ℕ, m ^ n) = (⊥ : Ideal R) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing m Ideal.IsPrime.ne_top'
  have hnot_all : ¬ ∀ n : ℕ, x ∈ m ^ n := by
    intro hx_all
    have hx_inf : x ∈ (⨅ n : ℕ, m ^ n) := by
      rw [Ideal.mem_iInf]
      exact hx_all
    have hx_bot : x ∈ (⊥ : Ideal R) := by
      simpa [hintersection] using hx_inf
    exact hx ((Ideal.mem_bot).1 hx_bot)
  have hexists : ∃ n : ℕ, x ∉ m ^ (n + 1) := by
    by_contra h
    apply hnot_all
    intro n
    cases n with
    | zero =>
        simpa using (show x ∈ (⊤ : Ideal R) from Ideal.mem_top)
    | succ k =>
        exact by
          by_contra hx_mem
          exact h ⟨k, hx_mem⟩
  refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
  cases hfind : Nat.find hexists with
  | zero =>
      simpa [hfind]
  | succ k =>
      have hk : ¬ x ∉ m ^ (k + 1) := by
        apply Nat.find_min hexists
        simpa [hfind] using Nat.lt_succ_self k
      exact by
        by_contra hx_mem
        exact hk hx_mem

/-- Helper for Lemma 10.106.2: the associated graded ring of a regular local ring has no zero
divisors because Lemma 10.106.1 identifies it with a polynomial ring over the residue field. -/
private theorem associated_graded_noZeroDivisors : NoZeroDivisors grR := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdim : ringKrullDim R = d := by
    -- A regular local ring has dimension equal to the minimal number of generators of `m`.
    simpa [d] using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  rcases
      regularLocalRing_associatedGraded_nonempty_algEquiv_mvPolynomial (R := R) (d := d) hdim
    with ⟨e⟩
  -- Pull the domain property back across the polynomial presentation of the associated graded ring.
  exact e.symm.toMulEquiv.noZeroDivisors _

/-- Helper for Lemma 10.106.2: a stage class in the associated graded ring vanishes exactly when
its representative already lies in the next power of the maximal ideal. -/
private theorem idealAssociatedGradedStageClass_eq_zero_iff_mem_succ {n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage m R n) :
    idealAssociatedGradedStageClass m n x = 0 ↔
      (x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1) := by
  constructor
  · intro hx
    have hgrade :
        (⟨idealAssociatedGradedStageClass m n x,
            idealAssociatedGradedStageClass_mem_grade m n x⟩ :
          idealAssociatedGradedRingGrade m n) = 0 := by
      apply Subtype.ext
      simpa using hx
    have hpiece :
        (Submodule.Quotient.mk x : RingTheory.Sequence.idealAssociatedGradedPiece m R n) = 0 := by
      -- Transport the vanishing statement across the grade/piece equivalence from the dependency.
      have happly :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := by
        have happly' :
            idealAssociatedGradedRingGrade_equiv_piece m n
                ⟨idealAssociatedGradedStageClass m n x,
                  idealAssociatedGradedStageClass_mem_grade m n x⟩ =
              idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
          exact
            congrArg
              (fun z : idealAssociatedGradedRingGrade m n ↦ idealAssociatedGradedRingGrade_equiv_piece m n z)
              hgrade
        calc
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ =
            idealAssociatedGradedRingGrade_equiv_piece m n 0 := happly'
          _ = 0 := LinearEquiv.map_zero (idealAssociatedGradedRingGrade_equiv_piece m n)
      simpa [idealAssociatedGradedRingGrade_equiv_piece_apply_stage] using happly
    -- Zero in the quotient means the representative lies in the next filtration stage.
    simpa using
      (Submodule.Quotient.mk_eq_zero
        ((RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1)).submoduleOf
          (RingTheory.Sequence.idealAssociatedGradedStage m R n))).1 hpiece
  · intro hx
    have hpiece :
        (Submodule.Quotient.mk x : RingTheory.Sequence.idealAssociatedGradedPiece m R n) = 0 := by
      -- Repackage next-stage membership as vanishing in the quotient piece.
      exact
        (Submodule.Quotient.mk_eq_zero
          ((RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1)).submoduleOf
            (RingTheory.Sequence.idealAssociatedGradedStage m R n))).2 <| by
            simpa using hx
    have hgrade :
        (⟨idealAssociatedGradedStageClass m n x,
            idealAssociatedGradedStageClass_mem_grade m n x⟩ :
          idealAssociatedGradedRingGrade m n) = 0 := by
      -- Move the quotient vanishing back to the owner grade.
      have happly :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := by
        simpa [idealAssociatedGradedRingGrade_equiv_piece_apply_stage] using hpiece
      have happly' :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ =
            idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
        calc
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := happly
          _ = idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
              symm
              exact LinearEquiv.map_zero (idealAssociatedGradedRingGrade_equiv_piece m n)
      exact (idealAssociatedGradedRingGrade_equiv_piece m n).injective happly'
    -- Forgetting the grade subtype recovers the vanishing of the original stage class.
    exact congrArg (fun z : idealAssociatedGradedRingGrade m n ↦ (z : grR)) hgrade

/-- Helper for Lemma 10.106.2: if a product lands one step deeper in the maximal-ideal filtration,
then one factor was already one step deeper. -/
private theorem mem_pow_succ_or_mem_pow_succ_of_mul_mem_pow_add_succ
    {a b : ℕ} {f g : R}
    (hf : f ∈ m ^ a) (hg : g ∈ m ^ b) (hfg : f * g ∈ m ^ (a + b + 1)) :
    f ∈ m ^ (a + 1) ∨ g ∈ m ^ (b + 1) := by
  let xf : RingTheory.Sequence.idealAssociatedGradedStage m R a := ⟨f, by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using hf⟩
  let xg : RingTheory.Sequence.idealAssociatedGradedStage m R b := ⟨g, by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using hg⟩
  let xfg : RingTheory.Sequence.idealAssociatedGradedStage m R (a + b) := ⟨f * g, by
    -- The adic filtration is multiplicative.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
      pow_add] using Ideal.mul_mem_mul hf hg⟩
  have hproduct_zero :
      idealAssociatedGradedStageClass m a xf * idealAssociatedGradedStageClass m b xg = 0 := by
    have hxfg_zero : idealAssociatedGradedStageClass m (a + b) xfg = 0 := by
      -- The deeper filtration hypothesis is exactly the zero criterion in the associated graded ring.
      apply (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := a + b) xfg).2
      simpa [xfg, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hfg
    -- Route correction: translate the product into the associated graded ring before using
    -- no-zero-divisors, rather than trying to compare powers directly in `R`.
    calc
      idealAssociatedGradedStageClass m a xf * idealAssociatedGradedStageClass m b xg =
          idealAssociatedGradedStageClass m (a + b) xfg := by
            symm
            simpa [xf, xg, xfg] using idealAssociatedGradedStageClass_mul_local m xf xg
      _ = 0 := hxfg_zero
  let _ : NoZeroDivisors grR := associated_graded_noZeroDivisors (R := R)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hproduct_zero with hzero_f | hzero_g
  · left
    -- Vanishing of the `a`-stage class means `f` already lies in `m^(a + 1)`.
    simpa [xf, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := a) xf).1 hzero_f
  · right
    -- Vanishing of the `b`-stage class means `g` already lies in `m^(b + 1)`.
    simpa [xg, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := b) xg).1 hzero_g

-- Proof sketch: use Krull's intersection theorem to get `⋂ n, (maximalIdeal R)^n = 0`. If
-- `f * g = 0` with both `f` and `g` nonzero, choose maximal integers `a` and `b` such that
-- `f ∈ (maximalIdeal R)^a` and `g ∈ (maximalIdeal R)^b`. Then
-- `f * g = 0 ∈ (maximalIdeal R)^(a + b + 1)`, and Lemma `10.106.1` forces either
-- `f ∈ (maximalIdeal R)^(a + 1)` or `g ∈ (maximalIdeal R)^(b + 1)`, contradicting maximality.
/-- Lemma 10.106.2: any regular local ring is a domain. -/
instance regularLocalRing_isDomain : IsDomain R := by
  let _ : NoZeroDivisors R := by
    refine ⟨?_⟩
    intro f g hfg
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    by_cases hg0 : g = 0
    · exact Or.inr hg0
    rcases exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (R := R) f hf0 with
      ⟨a, hfa, hfa_succ⟩
    rcases exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (R := R) g hg0 with
      ⟨b, hgb, hgb_succ⟩
    have hmul_mem : f * g ∈ m ^ (a + b + 1) := by
      -- The zero product lies in every power, so the filtration lemma applies.
      simpa [hfg] using (Ideal.zero_mem (m ^ (a + b + 1)))
    rcases
        mem_pow_succ_or_mem_pow_succ_of_mul_mem_pow_add_succ (R := R) hfa hgb hmul_mem
      with hfa_next | hgb_next
    · exact False.elim (hfa_succ hfa_next)
    · exact False.elim (hgb_succ hgb_next)
  -- A nontrivial commutative ring without zero divisors is a domain.
  exact NoZeroDivisors.to_isDomain R

end
