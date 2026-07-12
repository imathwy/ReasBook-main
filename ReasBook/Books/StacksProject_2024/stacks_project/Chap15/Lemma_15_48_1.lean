import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap10.Lemma_10_96_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped RightActions

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for Lemma 15.48.1:
- primary domain: commutative algebra of derivations under adic completion and localization;
- sampled owner declarations of the same kind:
  `Derivation`,
  `Derivation.compAlgebraMap`,
  `LinearMap.compDer`,
  `AdicCompletion.liftAlgHom`,
  `IsLocalization.liftAlgHom`,
  `Localization.awayMapₐ`;
- best owner abstraction: the target of clauses `(1)` and `(2)` is a canonical `Derivation` on the
  completion/localization itself, while the extension property along the structural map is the
  derived source-facing view of the owner-level equality on restricted derivations. For clause
  `(3)`, the chapter's canonical owner for comparison maps between away localizations is
  `Localization.awayMapₐ`, but the source hypothesis is only the existence of an `R`-algebra
  isomorphism between the two away localizations, so the main theorem keeps that source-facing
  shape instead of strengthening it to a statement about the canonical map;
- primitive data: the source derivation `D`, the ideal `I` for completion, and the target
  localization algebra `A`;
- derived API: pointwise restriction-to-`R` formulas, uniqueness lemmas, and the companion `∃!`
  reformulations built from the owner-level restriction equation.

Layer triage:
- `source-facing`: the canonical extensions `D.adicCompletionExtension I` and
  `D.localizationExtension S A`, together with the finite-type existential statement in clause
  `(3)`;
- `core/canonical`: the owner type `Derivation ℤ _ _` on the target algebra;
- `bridge/view`: the companion existence-uniqueness theorems and the restriction formulas along the
  canonical maps `R → AdicCompletion I R` and `R → A`.
-/

namespace Derivation

variable (D : Derivation ℤ R R)

section AdicCompletion

variable (I : Ideal R)

local notation "R̂" => AdicCompletion I R

/-- Helper for Lemma 15.48.1: the quotient transition map equips
`R ⧸ I^(n + 1)` with its canonical `R ⧸ I^(n + 2)`-algebra structure. -/
private instance quotient_pow_succ_algebra (n : ℕ) :
    Algebra (R ⧸ I ^ ((n + 1) + 1)) (R ⧸ I ^ (n + 1)) :=
  RingHom.toAlgebra (Ideal.Quotient.factorPowSucc I (n + 1))

/-- Helper for Lemma 15.48.1: the previous quotient transition algebra structure induces the
corresponding module structure on the lower quotient. -/
private instance quotient_pow_succ_module (n : ℕ) :
    Module (R ⧸ I ^ ((n + 1) + 1)) (R ⧸ I ^ (n + 1)) :=
  Algebra.toModule

/-- Helper for Lemma 15.48.1: a derivation sends `I^(n + 2)` into `I^(n + 1)`. -/
private theorem map_mem_pow_succ (n : ℕ) {x : R} (hx : x ∈ I ^ (n + 2)) :
    D x ∈ I ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
      -- For `I^2`, expand through the product ideal and apply Leibniz termwise.
      have hx' : x ∈ I * I := by
        simpa [pow_succ] using hx
      refine Submodule.mul_induction_on hx' ?_ ?_
      · intro r hr s hs
        rw [Derivation.leibniz]
        simpa [pow_one, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using
          (I.add_mem (I.mul_mem_right (D s) hr) (I.mul_mem_right (D r) hs))
      · intro a b ha hb
        have ha' : D a ∈ I := by
          simpa [pow_one] using ha
        have hb' : D b ∈ I := by
          simpa [pow_one] using hb
        simpa [pow_one, Derivation.map_add] using I.add_mem ha' hb'
  | succ n ih =>
      -- For higher powers, write `x` in `I * I^(n + 2)` and reuse the induction hypothesis on the
      -- second factor.
      have hx' : x ∈ I * I ^ (n + 2) := by
        simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using hx
      refine Submodule.mul_induction_on hx' ?_ ?_
      · intro r hr s hs
        rw [Derivation.leibniz]
        have hDs : D s ∈ I ^ (n + 1) := ih hs
        have hmul : r * D s ∈ I * I ^ (n + 1) := Ideal.mul_mem_mul hr hDs
        simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc, pow_succ'] using
          ((I ^ (n + 2)).add_mem
            (by simpa [pow_succ'] using hmul)
            ((I ^ (n + 2)).mul_mem_right (D r) hs))
      · intro a b ha hb
        simpa [Derivation.map_add] using (I ^ (n + 2)).add_mem ha hb

/-- Helper for Lemma 15.48.1: the quotient-stage additive map induced by `D` from
`R ⧸ I^(n + 2)` to `R ⧸ I^(n + 1)`. -/
private noncomputable def adic_completion_stage_addHom (n : ℕ) :
    R ⧸ I ^ ((n + 1) + 1) →+ R ⧸ I ^ (n + 1) := by
  let f : R →+ R ⧸ I ^ (n + 1) :=
    (Ideal.Quotient.mk (I ^ (n + 1))).toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom
  -- The ideal-power containment makes the quotient lift well defined.
  refine QuotientAddGroup.lift (I ^ ((n + 1) + 1)).toAddSubgroup f ?_
  intro x hx
  change Ideal.Quotient.mk (I ^ (n + 1)) (D x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using map_mem_pow_succ D I n hx)

/-- Helper for Lemma 15.48.1: the quotient-stage additive map sends the class of `r` to the class
of `D r`. -/
private theorem adic_completion_stage_addHom_mk (n : ℕ) (r : R) :
    adic_completion_stage_addHom D I n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (D r) :=
  rfl

/-- Helper for Lemma 15.48.1: the quotient-stage additive maps commute with the quotient
transition maps. -/
private theorem adic_completion_stage_addHom_compatible (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I (n + 1)).toAddMonoidHom.comp
        (adic_completion_stage_addHom D I (n + 1)) =
      (adic_completion_stage_addHom D I n).comp
        (Ideal.Quotient.factorPowSucc I (n + 2)).toAddMonoidHom := by
  -- Both sides agree on every class coming from `R`, so surjectivity of the quotient map gives the
  -- desired equality.
  ext r
  refine Quotient.inductionOn' r ?_
  intro x
  rfl

/-- Helper for Lemma 15.48.1: the quotient-stage additive maps commute with every lower quotient
transition map, not just consecutive ones. -/
private theorem adic_completion_stage_addHom_compatible_le {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1) :
          I ^ (n + 1) ≤ I ^ (m + 1))).toAddMonoidHom.comp
      (adic_completion_stage_addHom D I n) =
    (adic_completion_stage_addHom D I m).comp
      (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 2) :
          I ^ (n + 2) ≤ I ^ (m + 2))).toAddMonoidHom := by
  -- Both composites still send the class of `r` to the class of `D r` in the lower quotient.
  ext r
  refine Quotient.inductionOn' r ?_
  intro x
  rfl

/-- Helper for Lemma 15.48.1: the derivation induced by `D` on the shifted quotient tower
`R ⧸ I^(n + 2) → R ⧸ I^(n + 1)`. -/
private noncomputable def adic_completion_stage_derivation (n : ℕ) :
    Derivation ℤ (R ⧸ I ^ ((n + 1) + 1)) (R ⧸ I ^ (n + 1)) := by
  -- The underlying additive map is the quotient-stage map; the Leibniz rule is checked on lifts.
  refine Derivation.mk' (adic_completion_stage_addHom D I n).toIntLinearMap ?_
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s
  change adic_completion_stage_addHom D I n (Ideal.Quotient.mk _ (r * s)) =
    (Ideal.Quotient.mk _ r) * adic_completion_stage_addHom D I n (Ideal.Quotient.mk _ s) +
      (Ideal.Quotient.mk _ s) * adic_completion_stage_addHom D I n (Ideal.Quotient.mk _ r)
  rw [adic_completion_stage_addHom_mk, adic_completion_stage_addHom_mk,
    adic_completion_stage_addHom_mk]
  simp [Derivation.leibniz]

/-- Helper for Lemma 15.48.1: the quotient-stage derivation sends the class of `r` to the class of
`D r`. -/
private theorem adic_completion_stage_derivation_mk (n : ℕ) (r : R) :
    adic_completion_stage_derivation D I n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (D r) :=
  rfl

/-- Helper for Lemma 15.48.1: the shifted representative sequence still satisfies the adic Cauchy
step condition after applying the derivation. -/
private theorem adic_completion_shifted_derivation_step
    (f : AdicCompletion.AdicCauchySequence I R) (n : ℕ) :
    D (f (n + 1)) ≡ D (f (n + 2)) [SMOD I ^ n • (⊤ : Submodule R R)] := by
  cases n with
  | zero =>
      -- The first stage lands in the whole module, so there is nothing to prove.
      rw [SModEq.sub_mem]
      simp
  | succ n =>
      -- For later stages, apply the original Cauchy relation one step ahead and lower the power.
      rw [SModEq.sub_mem]
      have hstep : f (n + 2) - f (n + 3) ∈ (I ^ (n + 2) • ⊤ : Submodule R R) := by
        exact (SModEq.sub_mem).mp (f.property (Nat.le_succ (n + 2)))
      have hmem : f (n + 2) - f (n + 3) ∈ I ^ (n + 2) := by
        simpa using hstep
      rw [← map_sub]
      simpa using map_mem_pow_succ D I n hmem

/-- Helper for Lemma 15.48.1: shifting an adic Cauchy sequence by one step and applying `D`
still yields an adic Cauchy sequence. -/
private noncomputable def adic_completion_shifted_derivation_sequence
    (f : AdicCompletion.AdicCauchySequence I R) :
    AdicCompletion.AdicCauchySequence I R :=
  AdicCompletion.AdicCauchySequence.mk (I := I) (M := R)
    (fun n ↦ D (f (n + 1)))
    (fun n ↦ adic_completion_shifted_derivation_step D I f n)

/-- Helper for Lemma 15.48.1: pick a Cauchy-sequence representative of a completion element. -/
private noncomputable def adic_completion_representative (x : R̂) :
    AdicCompletion.AdicCauchySequence I R :=
  Classical.choose (AdicCompletion.mk_surjective I R x)

/-- Helper for Lemma 15.48.1: the chosen representative maps back to the original completion
element. -/
private theorem adic_completion_mk_representative (x : R̂) :
    AdicCompletion.mk I R (adic_completion_representative (I := I) x) = x :=
  Classical.choose_spec (AdicCompletion.mk_surjective I R x)

/-- Helper for Lemma 15.48.1: stage `n + 1` evaluation factors through stage `n + 2` via the
canonical quotient transition map. -/
private theorem adic_completion_eval_succ_factor (n : ℕ) (x : R̂) :
    AdicCompletion.evalₐ I (n + 1) x =
      Ideal.Quotient.factorPowSucc I (n + 1) (AdicCompletion.evalₐ I (n + 2) x) := by
  -- Rewrite `x` through the chosen representative so the factorization is a quotient-level
  -- compatibility statement on one explicit Cauchy sequence.
  rw [← adic_completion_mk_representative (I := I) x]
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  -- The inverse-system compatibility already identifies the two quotient classes.
  exact
    (AdicCompletion.Ideal.mk_eq_mk (I := I) (Nat.le_succ (n + 1))
      (adic_completion_representative (I := I) x)).symm

/-- Helper for Lemma 15.48.1: the zeroth quotient `R ⧸ I^0` is trivial. -/
private theorem quotient_pow_zero_eq_zero (x : R ⧸ I ^ 0) : x = 0 := by
  refine Quotient.inductionOn' x ?_
  intro r
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp [pow_zero])

/-- Helper for Lemma 15.48.1: any two elements of the zeroth quotient coincide. -/
private theorem quotient_pow_zero_eq (x y : R ⧸ I ^ 0) : x = y := by
  rw [quotient_pow_zero_eq_zero (I := I) x, quotient_pow_zero_eq_zero (I := I) y]

/-- Helper for Lemma 15.48.1: the representative-level shifted map defines a completion element. -/
private noncomputable def adic_completion_shifted_derivation_apply (x : R̂) : R̂ :=
  AdicCompletion.mk I R
    (adic_completion_shifted_derivation_sequence D I
      (adic_completion_representative (I := I) x))

/-- Helper for Lemma 15.48.1: successor-stage evaluation of the representative-level shifted map
agrees with the quotient-stage derivation. -/
private theorem adic_completion_shifted_derivation_eval_succ (n : ℕ) (x : R̂) :
    AdicCompletion.evalₐ I (n + 1) (adic_completion_shifted_derivation_apply D I x) =
      adic_completion_stage_derivation D I n (AdicCompletion.evalₐ I (n + 2) x) := by
  -- Evaluate the chosen representative and then rewrite the source stage back to `x`.
  simp only [adic_completion_shifted_derivation_apply, AdicCompletion.evalₐ_mk]
  have hrep :
      AdicCompletion.evalₐ I (n + 2) x =
        Ideal.Quotient.mk (I ^ (n + 2))
          ((adic_completion_representative (I := I) x) (n + 2)) := by
    calc
      AdicCompletion.evalₐ I (n + 2) x =
          AdicCompletion.evalₐ I (n + 2)
            (AdicCompletion.mk I R (adic_completion_representative (I := I) x)) := by
            rw [adic_completion_mk_representative (I := I) x]
      _ = Ideal.Quotient.mk (I ^ (n + 2))
            ((adic_completion_representative (I := I) x) (n + 2)) := by
            rw [AdicCompletion.evalₐ_mk]
  rw [hrep, adic_completion_stage_derivation_mk]
  rfl

/-- Helper for Lemma 15.48.1: the shifted representative construction is additive on the
completion, as witnessed stagewise. -/
private noncomputable def adic_completion_shifted_derivation_addHom : R̂ →+ R̂ where
  toFun := adic_completion_shifted_derivation_apply D I
  map_zero' := by
    -- The stage formula shows every successor quotient is zero; stage `0` is tautological.
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
        -- Stage `0` lands in the trivial quotient.
        exact quotient_pow_zero_eq (I := I)
          (AdicCompletion.evalₐ I 0 (adic_completion_shifted_derivation_apply D I 0)) 0
    | succ n =>
        rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n]
        simpa using (adic_completion_stage_derivation D I n).map_zero
  map_add' x y := by
    -- Compare all quotient evaluations and use additivity of the quotient-stage derivations.
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
        -- Stage `0` ignores all additive data because the quotient is trivial.
        exact quotient_pow_zero_eq (I := I)
          (AdicCompletion.evalₐ I 0 (adic_completion_shifted_derivation_apply D I (x + y)))
          (AdicCompletion.evalₐ I 0 (adic_completion_shifted_derivation_apply D I x) +
            AdicCompletion.evalₐ I 0 (adic_completion_shifted_derivation_apply D I y))
    | succ n =>
        rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := x + y)]
        change (adic_completion_stage_derivation D I n)
            (AdicCompletion.evalₐ I (n + 2) (x + y)) =
          AdicCompletion.evalₐ I (n + 1) (adic_completion_shifted_derivation_apply D I x) +
            AdicCompletion.evalₐ I (n + 1) (adic_completion_shifted_derivation_apply D I y)
        rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := x)]
        rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := y)]
        simpa using
          (adic_completion_stage_derivation D I n).map_add
            (AdicCompletion.evalₐ I (n + 2) x) (AdicCompletion.evalₐ I (n + 2) y)

/-- Helper for Lemma 15.48.1: the explicit shifted-sequence derivation on the adic completion. -/
private noncomputable def shifted_completion_derivation : Derivation ℤ R̂ R̂ :=
  Derivation.mk'
    (adic_completion_shifted_derivation_addHom D I).toIntLinearMap
    (fun x y => by
      -- Check Leibniz after evaluating on every quotient stage of the inverse system.
      apply AdicCompletion.ext_evalₐ
      intro n
      cases n with
      | zero =>
          -- Stage `0` is again the trivial quotient.
          exact quotient_pow_zero_eq (I := I)
            (AdicCompletion.evalₐ I 0 (adic_completion_shifted_derivation_apply D I (x * y)))
            (AdicCompletion.evalₐ I 0
              (x * adic_completion_shifted_derivation_apply D I y +
                y * adic_completion_shifted_derivation_apply D I x))
      | succ n =>
          -- Rewrite both sides stagewise and use Leibniz on the quotient derivation.
          change AdicCompletion.evalₐ I (n + 1)
              (adic_completion_shifted_derivation_apply D I (x * y)) =
            AdicCompletion.evalₐ I (n + 1)
              (x * adic_completion_shifted_derivation_apply D I y +
                y * adic_completion_shifted_derivation_apply D I x)
          rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := x * y)]
          have hsum :
              AdicCompletion.evalₐ I (n + 1)
                  (x * adic_completion_shifted_derivation_apply D I y +
                    y * adic_completion_shifted_derivation_apply D I x) =
                AdicCompletion.evalₐ I (n + 1) (x * adic_completion_shifted_derivation_apply D I y) +
                  AdicCompletion.evalₐ I (n + 1) (y * adic_completion_shifted_derivation_apply D I x) := by
            exact map_add (AdicCompletion.evalₐ I (n + 1))
              (x * adic_completion_shifted_derivation_apply D I y)
              (y * adic_completion_shifted_derivation_apply D I x)
          rw [hsum]
          have hxmul :
              AdicCompletion.evalₐ I (n + 1) (x * adic_completion_shifted_derivation_apply D I y) =
                AdicCompletion.evalₐ I (n + 1) x *
                  AdicCompletion.evalₐ I (n + 1) (adic_completion_shifted_derivation_apply D I y) := by
            exact map_mul (AdicCompletion.evalₐ I (n + 1)) x
              (adic_completion_shifted_derivation_apply D I y)
          rw [hxmul]
          rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := y)]
          have hymul :
              AdicCompletion.evalₐ I (n + 1) (y * adic_completion_shifted_derivation_apply D I x) =
                AdicCompletion.evalₐ I (n + 1) y *
                  AdicCompletion.evalₐ I (n + 1) (adic_completion_shifted_derivation_apply D I x) := by
            exact map_mul (AdicCompletion.evalₐ I (n + 1)) y
              (adic_completion_shifted_derivation_apply D I x)
          rw [hymul]
          rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n (x := x)]
          rw [adic_completion_eval_succ_factor (I := I) n x]
          rw [adic_completion_eval_succ_factor (I := I) n y]
          have hxy :
              AdicCompletion.evalₐ I (n + 2) (x * y) =
                AdicCompletion.evalₐ I (n + 2) x * AdicCompletion.evalₐ I (n + 2) y := by
            exact map_mul (AdicCompletion.evalₐ I (n + 2)) x y
          rw [hxy]
          have hxalg :
              Ideal.Quotient.factorPowSucc I (n + 1) (AdicCompletion.evalₐ I (n + 2) x) =
                algebraMap (R ⧸ I ^ ((n + 1) + 1)) (R ⧸ I ^ (n + 1))
                  (AdicCompletion.evalₐ I (n + 2) x) := rfl
          have hyalg :
              Ideal.Quotient.factorPowSucc I (n + 1) (AdicCompletion.evalₐ I (n + 2) y) =
                algebraMap (R ⧸ I ^ ((n + 1) + 1)) (R ⧸ I ^ (n + 1))
                  (AdicCompletion.evalₐ I (n + 2) y) := rfl
          rw [hxalg, hyalg]
          exact (adic_completion_stage_derivation D I n).leibniz
            (AdicCompletion.evalₐ I (n + 2) x) (AdicCompletion.evalₐ I (n + 2) y)
    )

/-- Helper for Lemma 15.48.1: the explicit shifted derivation restricts to the original
derivation on the dense image of `R`. -/
private theorem shifted_completion_derivation_compAlgebraMap :
    (shifted_completion_derivation D I).compAlgebraMap R =
      (Algebra.linearMap R R̂).compDer D := by
  -- The shifted representative formula already computes the restriction on dense points.
  apply Derivation.ext
  intro r
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
      -- Stage `0` is trivial on both sides of the restriction formula.
      exact quotient_pow_zero_eq (I := I)
        (AdicCompletion.evalₐ I 0
          (shifted_completion_derivation D I (algebraMap R R̂ r)))
        (AdicCompletion.evalₐ I 0 (algebraMap R R̂ (D r)))
  | succ n =>
      -- The successor-stage formula reduces to the quotient-stage derivation on `r`.
      change AdicCompletion.evalₐ I (n + 1)
          (adic_completion_shifted_derivation_apply D I (algebraMap R R̂ r)) =
        AdicCompletion.evalₐ I (n + 1) (algebraMap R R̂ (D r))
      rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n
        (x := algebraMap R R̂ r)]
      simpa [AdicCompletion.evalₐ_of] using adic_completion_stage_derivation_mk D I n r

/-- Helper for Lemma 15.48.1: any completion extension of `D` lowers the `I`-adic filtration by
one step. -/
private theorem adic_completion_extension_maps_pow_smul_top
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (n : ℕ) {x : R̂}
    (hx : x ∈ (I ^ (n + 2) • (⊤ : Submodule R R̂))) :
    Dhat x ∈ (I ^ (n + 1) • (⊤ : Submodule R R̂)) := by
  -- Follow the source filtration route: reduce to generators of `I^(n + 2) • ⊤`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    -- The Leibniz rule splits `Dhat (r • y)` into a higher-filtration term and a coefficient
    -- derivative term, and `map_mem_pow_succ` lowers the ideal power on the coefficient.
    change Dhat ((algebraMap R R̂ r) * y) ∈ (I ^ (n + 1) • (⊤ : Submodule R R̂))
    rw [Dhat.leibniz]
    have hleft_hi : algebraMap R R̂ r * Dhat y ∈ (I ^ (n + 2) • (⊤ : Submodule R R̂)) := by
      simpa [Algebra.smul_def] using
        (Submodule.smul_mem_smul hr (show Dhat y ∈ (⊤ : Submodule R R̂) from Submodule.mem_top))
    have hleft : algebraMap R R̂ r * Dhat y ∈ (I ^ (n + 1) • (⊤ : Submodule R R̂)) := by
      exact (Submodule.smul_mono_left
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) hleft_hi
    have hDr : D r ∈ I ^ (n + 1) := by
      simpa using map_mem_pow_succ D I n hr
    have hright : y * Dhat (algebraMap R R̂ r) ∈ (I ^ (n + 1) • (⊤ : Submodule R R̂)) := by
      have hmap : Dhat (algebraMap R R̂ r) = algebraMap R R̂ (D r) := congr_fun hDhat r
      have hcoeff : y * algebraMap R R̂ (D r) ∈ (I ^ (n + 1) • (⊤ : Submodule R R̂)) := by
        simpa [Algebra.smul_def, mul_comm] using Submodule.smul_mem_smul hDr hy
      simpa [hmap] using hcoeff
    exact Submodule.add_mem _ hleft hright
  · intro x y hx hy
    simpa [map_add] using Submodule.add_mem (I ^ (n + 1) • (⊤ : Submodule R R̂)) hx hy

/-- Helper for Lemma 15.48.1: stage evaluation kills every element already lying in the
`I^m`-adic filtration piece of the completion. -/
private theorem adic_completion_eval_zero_of_mem_pow_smul_top
    (m : ℕ) {x : R̂}
    (hx : x ∈ (I ^ m • (⊤ : Submodule R R̂))) :
    AdicCompletion.evalₐ I m x = 0 := by
  -- Evaluate generators of `I^m • ⊤` termwise: the coefficient already vanishes in
  -- `R ⧸ I^m`, so every generated product maps to zero.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    change AdicCompletion.evalₐ I m ((algebraMap R R̂ r) * y) = 0
    rw [map_mul]
    have hr0 : AdicCompletion.evalₐ I m (algebraMap R R̂ r) = 0 := by
      simpa [AdicCompletion.algebraMap_apply] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hr : Ideal.Quotient.mk (I ^ m) r = 0)
    rw [hr0]
    simp
  · intro x y hx hy
    rw [map_add, hx, hy]
    simp

/-- Helper for Lemma 15.48.1: the linear-stage evaluation has the same vanishing consequence as
the algebra-stage evaluation on an `I^m`-power element. -/
private theorem adic_completion_eval_eq_zero_of_mem_pow_smul_top
    (m : ℕ) {x : R̂}
    (hx : x ∈ (I ^ m • (⊤ : Submodule R R̂))) :
    AdicCompletion.eval I R m x = 0 := by
  -- Bridge from the algebra-valued stage evaluation to the linear quotient evaluation.
  rw [← AdicCompletion.factor_evalₐ_eq_eval (I := I) (x := x)
    (h := by
      simpa using (show (I ^ m : Ideal R) ≤ I ^ m from le_rfl))]
  rw [adic_completion_eval_zero_of_mem_pow_smul_top (I := I) (m := m) hx]
  rfl

/-- Helper for Lemma 15.48.1: the difference between a completion class represented by `f`
and its stage-`n + 2` lift already vanishes after evaluation at stage `n + 2`. -/
private theorem adic_completion_mk_sub_stage_lift_eval_eq_zero
    (f : AdicCompletion.AdicCauchySequence I R) (n : ℕ) :
    AdicCompletion.evalₐ I (n + 2)
      (AdicCompletion.mk I R f - algebraMap R R̂ (f (n + 2))) = 0 := by
  -- Evaluate the representative comparison at stage `n + 2`; both terms become the same class.
  rw [map_sub, AdicCompletion.evalₐ_mk]
  simpa [AdicCompletion.algebraMap_apply, sub_eq_zero] using
    (AdicCompletion.evalₐ_of (I := I) (n + 2) (f (n + 2)))

/-- Helper for Lemma 15.48.1: `ofPowSMul` forgets the subtype on dense points. -/
private theorem adic_completion_ofPowSMul_of_eq_of_subtype_module
    {M : Type*} [AddCommGroup M] [Module R M] {m : ℕ}
    (z : ↥(I ^ m • (⊤ : Submodule R M))) :
    AdicCompletion.ofPowSMul I M m
        (AdicCompletion.of I ↥(I ^ m • (⊤ : Submodule R M)) z) =
      AdicCompletion.of I M z.1 := by
  -- `ofPowSMul` is induced by the subtype inclusion, so on dense points it simply forgets the
  -- source subtype before taking the completion class.
  simpa [AdicCompletion.ofPowSMul] using
    (AdicCompletion.map_of (I := I) ((I ^ m • (⊤ : Submodule R M)).subtype) z)

/-- Helper for Lemma 15.48.1: `ofPowSMul` forgets the subtype on dense points. -/
private theorem adic_completion_ofPowSMul_of_eq_of_subtype {m : ℕ}
    (z : ↥(I ^ m • (⊤ : Submodule R R))) :
    AdicCompletion.ofPowSMul I R m
        (AdicCompletion.of I ↥(I ^ m • (⊤ : Submodule R R)) z) =
      algebraMap R R̂ z.1 := by
  -- `ofPowSMul` is induced by the subtype inclusion, so on `of z` it simply forgets the subtype.
  simpa [AdicCompletion.algebraMap_apply] using
    adic_completion_ofPowSMul_of_eq_of_subtype_module (I := I) (M := R) z

/-- Helper for Lemma 15.48.1: the successor-stage vanishing statement already holds on dense
`of`-points in the source completion of `I^(n + 2) • R`. -/
private theorem adic_completion_extension_eval_succ_eq_zero_on_ofPowSMul_of
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (n : ℕ)
    (z : ↥(I ^ (n + 2) • (⊤ : Submodule R R))) :
    AdicCompletion.evalₐ I (n + 1)
        (Dhat
          (AdicCompletion.ofPowSMul I R (n + 2)
            (AdicCompletion.of I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) z))) = 0 := by
  -- On dense points, `ofPowSMul` just forgets the subtype, so the extension formula for `Dhat`
  -- reduces the goal to the ideal-power containment `D z ∈ I^(n + 1)`.
  rw [adic_completion_ofPowSMul_of_eq_of_subtype (I := I) (z := z)]
  have hmap : Dhat (algebraMap R R̂ z.1) = algebraMap R R̂ (D z.1) := congr_fun hDhat z.1
  rw [hmap]
  have hz_mem : z.1 ∈ I ^ (n + 2) := by
    simpa using z.2
  simpa [AdicCompletion.algebraMap_apply] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using map_mem_pow_succ D I n hz_mem) :
      Ideal.Quotient.mk (I ^ (n + 1)) (D z.1) = 0)

/-- Helper for Lemma 15.48.1: any completion extension kills the successor-stage evaluation on
canonical `ofPowSMul` witnesses coming from the stage-`n + 2` filtration piece. -/
private theorem adic_completion_eval_eq_zero_on_ofPowSMul
    (m : ℕ)
    (y : AdicCompletion I ↥(I ^ m • (⊤ : Submodule R R))) :
    AdicCompletion.evalₐ I m (AdicCompletion.ofPowSMul I R m y) = 0 := by
  -- Evaluate on representative sequences: the stage-`m` term already lies in `I ^ m`, so its
  -- quotient class vanishes immediately.
  let P : AdicCompletion I ↥(I ^ m • (⊤ : Submodule R R)) → Prop := fun z =>
    AdicCompletion.evalₐ I m (AdicCompletion.ofPowSMul I R m z) = 0
  change P y
  refine AdicCompletion.induction_on (I := I)
    (M := ↥(I ^ m • (⊤ : Submodule R R))) y ?_
  intro f
  change AdicCompletion.evalₐ I m
      (AdicCompletion.map I ((I ^ m • (⊤ : Submodule R R)).subtype)
        (AdicCompletion.mk I ↥(I ^ m • (⊤ : Submodule R R)) f)) = 0
  rw [AdicCompletion.map_mk, AdicCompletion.evalₐ_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using (f m).2)

/-- Helper for Lemma 15.48.1: any completion extension kills the successor-stage evaluation on
canonical `ofPowSMul` witnesses coming from the stage-`n + 2` filtration piece. -/
private theorem shifted_completion_derivation_eval_succ_eq_zero_on_ofPowSMul
    (n : ℕ)
    (y : AdicCompletion I ↥(I ^ (n + 2) • (⊤ : Submodule R R))) :
    AdicCompletion.evalₐ I (n + 1)
      (shifted_completion_derivation D I
        (AdicCompletion.ofPowSMul I R (n + 2) y)) = 0 := by
  -- The explicit shifted derivation computes successor stages from stage `n + 2`, and every
  -- `ofPowSMul` point is already zero at that stage.
  rw [show shifted_completion_derivation D I
      (AdicCompletion.ofPowSMul I R (n + 2) y) =
        adic_completion_shifted_derivation_apply D I
          (AdicCompletion.ofPowSMul I R (n + 2) y) from rfl]
  rw [adic_completion_shifted_derivation_eval_succ (D := D) (I := I) n
    (x := AdicCompletion.ofPowSMul I R (n + 2) y)]
  have hy_eval :
      AdicCompletion.evalₐ I (n + 2)
        (AdicCompletion.ofPowSMul I R (n + 2) y) = 0 :=
    adic_completion_eval_eq_zero_on_ofPowSMul (I := I) (m := n + 2) y
  rw [hy_eval]
  simpa using (adic_completion_stage_derivation D I n).map_zero

/-- Helper for Lemma 15.48.1: a derivation on the completion whose restriction to `R` is zero
preserves every `I`-adic filtration piece. -/
private theorem zero_restriction_maps_pow_smul_top
    (E : Derivation ℤ R̂ R̂)
    (hE : E.compAlgebraMap R = 0)
    (m : ℕ) {x : R̂}
    (hx : x ∈ (I ^ m • (⊤ : Submodule R R̂))) :
    E x ∈ (I ^ m • (⊤ : Submodule R R̂)) := by
  -- A zero restriction kills the coefficient-derivative term in the Leibniz rule, so the
  -- filtration level is preserved rather than lowered.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    change E ((algebraMap R R̂ r) * y) ∈ (I ^ m • (⊤ : Submodule R R̂))
    rw [E.leibniz]
    have hleft : algebraMap R R̂ r * E y ∈ (I ^ m • (⊤ : Submodule R R̂)) := by
      simpa [Algebra.smul_def] using
        (Submodule.smul_mem_smul hr
          (show E y ∈ (⊤ : Submodule R R̂) from Submodule.mem_top))
    have hright : y * E (algebraMap R R̂ r) ∈ (I ^ m • (⊤ : Submodule R R̂)) := by
      have hEr : E (algebraMap R R̂ r) = 0 := congr_fun hE r
      simpa [hEr]
    exact Submodule.add_mem _ hleft hright
  · intro x y hx hy
    simpa [map_add] using
      (Submodule.add_mem (I ^ m • (⊤ : Submodule R R̂)) hx hy)

/-- Helper for Lemma 15.48.1: a derivation on the completion whose restriction to `R` is zero is
automatically `R`-linear. -/
private noncomputable def zero_restriction_linear_map
    (E : Derivation ℤ R̂ R̂)
    (hE : E.compAlgebraMap R = 0) :
    R̂ →ₗ[R] R̂ where
  toFun := E
  map_add' := E.map_add
  map_smul' r x := by
    -- The Leibniz rule on `(algebraMap r) * x` loses the coefficient-derivative term because
    -- `E` vanishes on the dense image of `R`.
    change E ((algebraMap R R̂ r) * x) = (algebraMap R R̂ r) * E x
    rw [E.leibniz]
    have hEr : E (algebraMap R R̂ r) = 0 := congr_fun hE r
    rw [hEr]
    change (algebraMap R R̂ r) * E x + x * 0 = (algebraMap R R̂ r) * E x
    simp

/-- Helper for Lemma 15.48.1: `R`-linear maps preserve the standard `I^m`-power submodules. -/
private theorem linearMap_map_mem_pow_smul_top
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) {m : ℕ} {x : M}
    (hx : x ∈ I ^ m • (⊤ : Submodule R M)) :
    f x ∈ I ^ m • (⊤ : Submodule R N) := by
  -- The image lands in `I^m • range f`, which is contained in `I^m • ⊤`.
  have hxmap :
      f x ∈ Submodule.map f (I ^ m • (⊤ : Submodule R M)) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Submodule.map_smul'', Submodule.map_top] at hxmap
  exact (Submodule.smul_mono (le_rfl : (I ^ m : Ideal R) ≤ I ^ m)
    (show LinearMap.range f ≤ (⊤ : Submodule R N) from le_top)) hxmap

/-- Helper for Lemma 15.48.1: `I^(n + 1)` acts trivially on the quotient `R ⧸ I^(n + 1)`. -/
private theorem quotient_pow_smul_top_eq_bot (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (R ⧸ I ^ (n + 1))) = ⊥ := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (I ^ (n + 1)) (r * y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (by simpa [mul_comm] using (I ^ (n + 1)).mul_mem_left y hr)
  · exact bot_le

/-- Helper for Lemma 15.48.1: in the completed `I^(n + 2)`-piece, the difference from the
stage-`n + 1` dense lift already comes from the completed `(n + 1)`st filtration piece. -/
private theorem completed_filtration_mk_sub_stage_lift_exists_ofPowSMul
    (n : ℕ)
    (f : AdicCompletion.AdicCauchySequence I ↥(I ^ (n + 2) • (⊤ : Submodule R R))) :
    ∃ y : AdicCompletion I
        ↥(I ^ (n + 1) •
          (⊤ : Submodule R ↥(I ^ (n + 2) • (⊤ : Submodule R R)))),
      AdicCompletion.ofPowSMul I
          ↥(I ^ (n + 2) • (⊤ : Submodule R R)) (n + 1) y =
        AdicCompletion.mk I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) f -
          AdicCompletion.of I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) (f (n + 1)) := by
  let δ :
      AdicCompletion I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) :=
    AdicCompletion.mk I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) f -
      AdicCompletion.of I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) (f (n + 1))
  have hδ :
      δ.val (n + 1) = 0 := by
    -- Evaluate the explicit difference at stage `n + 1`; both terms become the same quotient
    -- class of `f (n + 1)`.
    dsimp [δ]
    simp [AdicCompletion.eval_of]
  refine ⟨AdicCompletion.ofValEqZero I hδ, ?_⟩
  -- The stage-`n + 1` kernel witness is exactly the required tail-difference class.
  simpa [δ] using
    (AdicCompletion.ofPowSMul_ofValEqZero
      (I := I) (M := ↥(I ^ (n + 2) • (⊤ : Submodule R R))) hδ)

/-- Helper for Lemma 15.48.1: after subtracting the explicit shifted derivation, the only
remaining completion-side vanishing problem is the homogeneous zero-restriction case. -/
private theorem zero_restriction_eval_succ_eq_zero_on_ofPowSMul
    (E : Derivation ℤ R̂ R̂)
    (hE : E.compAlgebraMap R = 0)
    (n : ℕ)
    (y : AdicCompletion I ↥(I ^ (n + 2) • (⊤ : Submodule R R))) :
    AdicCompletion.evalₐ I (n + 1) (E (AdicCompletion.ofPowSMul I R (n + 2) y)) = 0 := by
  -- TODO for Lemma 15.48.1: finish the completion-side zero-restriction argument without using
  -- the later stage-formula theorem, since that creates a local dependency cycle in this file.
  -- The intended next route is to prove the zero case directly on `ofPowSMul` via the source
  -- decomposition `mk = of + nested ofPowSMul`, then rebuild the general stage formula.
  sorry

/-- Helper for Lemma 15.48.1: any completion extension kills the successor-stage evaluation on
canonical `ofPowSMul` witnesses coming from the stage-`n + 2` filtration piece. -/
private theorem adic_completion_extension_eval_succ_eq_zero_on_ofPowSMul
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (n : ℕ)
    (y : AdicCompletion I ↥(I ^ (n + 2) • (⊤ : Submodule R R))) :
    AdicCompletion.evalₐ I (n + 1) (Dhat (AdicCompletion.ofPowSMul I R (n + 2) y)) = 0 := by
  -- Route correction: compare `Dhat` to the explicit shifted derivation first, so the remaining
  -- `mk`-case transport problem is isolated to a homogeneous derivation with zero restriction.
  let E : Derivation ℤ R̂ R̂ := Dhat - shifted_completion_derivation D I
  have hE : E.compAlgebraMap R = 0 := by
    -- Both summands restrict to the same base derivation, so their difference is zero on `R`.
    apply Derivation.ext
    intro r
    have hDhat_r : Dhat (algebraMap R R̂ r) = algebraMap R R̂ (D r) := congr_fun hDhat r
    have hshift_r :
        shifted_completion_derivation D I (algebraMap R R̂ r) = algebraMap R R̂ (D r) :=
      congr_fun (shifted_completion_derivation_compAlgebraMap (D := D) (I := I)) r
    dsimp [E]
    rw [hDhat_r, hshift_r]
    simp
  have hEzero :
      AdicCompletion.evalₐ I (n + 1)
        (E (AdicCompletion.ofPowSMul I R (n + 2) y)) = 0 :=
    zero_restriction_eval_succ_eq_zero_on_ofPowSMul (I := I) E hE n y
  have hshift :
      AdicCompletion.evalₐ I (n + 1)
        (shifted_completion_derivation D I
          (AdicCompletion.ofPowSMul I R (n + 2) y)) = 0 :=
    shifted_completion_derivation_eval_succ_eq_zero_on_ofPowSMul
      (D := D) (I := I) n y
  have hsplit :
      Dhat (AdicCompletion.ofPowSMul I R (n + 2) y) =
        E (AdicCompletion.ofPowSMul I R (n + 2) y) +
          shifted_completion_derivation D I
            (AdicCompletion.ofPowSMul I R (n + 2) y) := by
    -- Expand the difference definition and regroup the two summands.
    dsimp [E]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  rw [hsplit, map_add, hEzero, hshift]
  simp

/-- Helper for Lemma 15.48.1: stage-`n + 2` kernel elements are sent by any completion extension
to stage-`n + 1` kernel elements. -/
private theorem adic_completion_extension_eval_succ_eq_zero_of_eval_eq_zero
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (n : ℕ) {x : R̂}
    (hx : AdicCompletion.evalₐ I (n + 2) x = 0) :
    AdicCompletion.evalₐ I (n + 1) (Dhat x) = 0 := by
  -- Route correction: use the canonical kernel witness `ofValEqZero` from the source completion
  -- API, then delegate the only remaining work to the dedicated `ofPowSMul` lemma.
  have hx_eval :
      AdicCompletion.eval I R (n + 2) x = 0 := by
    -- Rewrite the algebra-stage evaluation back to the linear-stage evaluation where the kernel
    -- description is available.
    rw [← AdicCompletion.factor_evalₐ_eq_eval (I := I) (x := x)
      (h := by
        simpa using (show I ^ (n + 2) ≤ I ^ (n + 2) from le_rfl))]
    simpa [hx]
  let y : AdicCompletion I ↥(I ^ (n + 2) • (⊤ : Submodule R R)) :=
    AdicCompletion.ofValEqZero I hx_eval
  have hy : AdicCompletion.ofPowSMul I R (n + 2) y = x := by
    simpa [y] using (AdicCompletion.ofPowSMul_ofValEqZero (I := I) (M := R) hx_eval)
  -- The canonical `ofPowSMul` witness is exactly `x`, so the special vanishing lemma applies.
  simpa [hy] using
    adic_completion_extension_eval_succ_eq_zero_on_ofPowSMul
      (D := D) (I := I) (Dhat := Dhat) hDhat n y

/-- Helper for Lemma 15.48.1: any extension of `D` satisfies the successor-stage formula on
explicit Cauchy-sequence representatives. -/
private theorem adic_completion_extension_eval_succ_eq_stage_derivation_mk
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (f : AdicCompletion.AdicCauchySequence I R) (n : ℕ) :
    AdicCompletion.evalₐ I (n + 1) (Dhat (AdicCompletion.mk I R f)) =
      adic_completion_stage_derivation D I n
        (Ideal.Quotient.mk (I ^ (n + 2)) (f (n + 2))) := by
  -- Route correction: the source proof compares `mk f` with the concrete stage lift
  -- `algebraMap R R̂ (f (n + 2))` and kills the error term by filtration, rather than by an
  -- abstract FG-only kernel identification.
  let err : R̂ := AdicCompletion.mk I R f - algebraMap R R̂ (f (n + 2))
  have hsplit :
      AdicCompletion.mk I R f =
        algebraMap R R̂ (f (n + 2)) + err := by
    dsimp [err]
    simp [sub_eq_add_neg, add_comm]
  have herr_eval :
      AdicCompletion.evalₐ I (n + 1) (Dhat err) = 0 := by
    -- The new route only needs that the comparison error is zero at stage `n + 2`.
    apply adic_completion_extension_eval_succ_eq_zero_of_eval_eq_zero
      (D := D) (I := I) (Dhat := Dhat) hDhat n
    dsimp [err]
    exact adic_completion_mk_sub_stage_lift_eval_eq_zero (I := I) f n
  have hmap :
      Dhat (algebraMap R R̂ (f (n + 2))) = algebraMap R R̂ (D (f (n + 2))) :=
    congr_fun hDhat (f (n + 2))
  calc
    AdicCompletion.evalₐ I (n + 1) (Dhat (AdicCompletion.mk I R f)) =
        AdicCompletion.evalₐ I (n + 1)
          (Dhat (algebraMap R R̂ (f (n + 2)) + err)) := by
          rw [hsplit]
    _ = AdicCompletion.evalₐ I (n + 1)
          (Dhat (algebraMap R R̂ (f (n + 2))) + Dhat err) := by
          rw [map_add]
    _ = AdicCompletion.evalₐ I (n + 1) (Dhat (algebraMap R R̂ (f (n + 2)))) +
          AdicCompletion.evalₐ I (n + 1) (Dhat err) := by
          rw [map_add]
    _ = Ideal.Quotient.mk (I ^ (n + 1)) (D (f (n + 2))) + 0 := by
          rw [hmap, herr_eval]
          simpa [AdicCompletion.algebraMap_apply] using
            (AdicCompletion.evalₐ_of (I := I) (n + 1) (D (f (n + 2))))
    _ = Ideal.Quotient.mk (I ^ (n + 1)) (D (f (n + 2))) := by
          simp
    _ = adic_completion_stage_derivation D I n
          (Ideal.Quotient.mk (I ^ (n + 2)) (f (n + 2))) := by
          simpa using (adic_completion_stage_derivation_mk D I n (f (n + 2))).symm

/-- Helper for Lemma 15.48.1: any extension of `D` satisfies the successor-stage formula on every
completion element. -/
private theorem adic_completion_extension_eval_succ_eq_stage_derivation
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D)
    (n : ℕ) (x : R̂) :
    AdicCompletion.evalₐ I (n + 1) (Dhat x) =
      adic_completion_stage_derivation D I n (AdicCompletion.evalₐ I (n + 2) x) := by
  let p : R̂ → Prop := fun y =>
    AdicCompletion.evalₐ I (n + 1) (Dhat y) =
      adic_completion_stage_derivation D I n (AdicCompletion.evalₐ I (n + 2) y)
  change p x
  -- Check the statement on explicit representatives and then descend by completion induction.
  refine AdicCompletion.induction_on (I := I) (M := R) x ?_
  intro f
  change
    AdicCompletion.evalₐ I (n + 1) (Dhat (AdicCompletion.mk I R f)) =
      adic_completion_stage_derivation D I n
        (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I R f))
  -- The representative formula is already stated using the stage-`n + 2` quotient class.
  simpa [AdicCompletion.evalₐ_mk] using
    adic_completion_extension_eval_succ_eq_stage_derivation_mk
      (D := D) (I := I) Dhat hDhat f n

private theorem existsUnique_adicCompletionExtension_aux :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D := by
  -- Route correction: `AdicCompletion.lift` is `R`-linear, but a derivation is only `ℤ`-linear,
  -- so the completion extension has to be built as an additive endomorphism on the inverse-limit
  -- tower rather than by an `R`-linear lift.
  let Dhat : Derivation ℤ R̂ R̂ := shifted_completion_derivation D I
  have hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D := by
    -- The new helper records the dense-image restriction formula once and for all.
    simpa [Dhat] using shifted_completion_derivation_compAlgebraMap (D := D) (I := I)
  refine ⟨Dhat, hDhat, ?_⟩
  · intro Dhat' hDhat'
    -- Compare both derivations on every completion element by comparing all quotient evaluations.
    apply Derivation.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
        -- Stage `0` is trivial, so both values coincide automatically.
        exact quotient_pow_zero_eq (I := I)
          (AdicCompletion.evalₐ I 0 (Dhat' x))
          (AdicCompletion.evalₐ I 0 (Dhat x))
    | succ n =>
        -- Both derivations satisfy the same successor-stage formula, hence agree on stage
        -- `n + 1`.
        rw [adic_completion_extension_eval_succ_eq_stage_derivation
          (D := D) (I := I) (Dhat := Dhat') hDhat' n x]
        rw [adic_completion_extension_eval_succ_eq_stage_derivation
          (D := D) (I := I) (Dhat := Dhat) hDhat n x]

-- Proof sketch: for `n ≥ 1`, the Leibniz rule implies `D (I ^ (n + 1)) ⊆ I ^ n`, so `D`
-- induces compatible derivations on the quotient system `R ⧸ I ^ (n + 1) → R ⧸ I ^ n`. Passing to
-- the inverse limit yields a derivation on the `I`-adic completion, and uniqueness is checked on
-- the dense image of `R`.
/-- Lemma 15.48.1 (1): for any ideal `I` of a commutative ring `R`, a derivation `D : R → R`
extends canonically to a derivation of the `I`-adic completion `AdicCompletion I R`. -/
noncomputable def adicCompletionExtension : Derivation ℤ R̂ R̂ :=
  (existsUnique_adicCompletionExtension_aux D I).choose

theorem adicCompletionExtension_compAlgebraMap :
    (D.adicCompletionExtension I).compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  (existsUnique_adicCompletionExtension_aux D I).choose_spec.left

@[simp]
theorem adicCompletionExtension_algebraMap (r : R) :
    D.adicCompletionExtension I (algebraMap R R̂ r) = algebraMap R R̂ (D r) :=
  congr_fun (D.adicCompletionExtension_compAlgebraMap I) r

theorem adicCompletionExtension_unique
    (Dhat : Derivation ℤ R̂ R̂)
    (hDhat : Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D) :
    Dhat = D.adicCompletionExtension I := by
  exact (existsUnique_adicCompletionExtension_aux D I).choose_spec.right Dhat hDhat

/-- Existence and uniqueness of the canonical extension of a derivation to the `I`-adic
completion. -/
theorem existsUnique_adicCompletionExtension :
    ∃! Dhat : Derivation ℤ R̂ R̂,
      Dhat.compAlgebraMap R = (Algebra.linearMap R R̂).compDer D :=
  ⟨D.adicCompletionExtension I, D.adicCompletionExtension_compAlgebraMap I,
    fun Dhat hDhat ↦ D.adicCompletionExtension_unique I Dhat hDhat⟩

end AdicCompletion

section Localization

/-- Helper for Lemma 15.48.1: the algebra map `r ↦ (r, D r)` into the trivial square-zero
extension over a localization target. -/
private noncomputable def derivationToTrivSqZero
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    R →ₐ[ℤ] TrivSqZeroExt A A where
  toFun r := (algebraMap R A r, algebraMap R A (D r))
  map_one' := by
    ext <;> simp
  map_mul' x y := by
    ext <;> simp [Derivation.leibniz, mul_comm]
  map_zero' := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp
  commutes' n := by
    ext <;> simp

private theorem existsUnique_localizationExtension_aux
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    : ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D := by
  classical
  let φ : R →ₐ[ℤ] TrivSqZeroExt A A := derivationToTrivSqZero D S A
  have hφ_units : ∀ y : S, IsUnit (φ y) := by
    intro y
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [φ, derivationToTrivSqZero] using (IsLocalization.map_units A y)
  let ψ : A →ₐ[ℤ] TrivSqZeroExt A A := IsLocalization.liftAlgHom (S := A) (f := φ) hφ_units
  have hψ : ψ.comp (IsScalarTower.toAlgHom ℤ R A) = φ := by
    -- The localization lift is characterized by its values on the image of `R`.
    apply AlgHom.ext
    intro r
    change IsLocalization.lift hφ_units ((algebraMap R A) r) = φ r
    simpa [ψ, IsLocalization.liftAlgHom] using IsLocalization.lift_eq hφ_units r
  have hfst_ring : ((TrivSqZeroExt.fstHom ℤ A A).comp ψ).toRingHom = RingHom.id A := by
    -- The first component is the unique ring endomorphism of the localization extending
    -- the structural map `R → A`.
    apply IsLocalization.ringHom_ext S
    ext r
    exact congrArg TrivSqZeroExt.fst (AlgHom.congr_fun hψ r)
  have hfst_apply (a : A) : TrivSqZeroExt.fst (ψ a) = a := by
    exact RingHom.congr_fun hfst_ring a
  let Dloc : Derivation ℤ A A := Derivation.mk'
    ((TrivSqZeroExt.sndHom A A).restrictScalars ℤ ∘ₗ ψ.toLinearMap)
    (fun a b => by
      -- The second component of a multiplicative map into the square-zero extension satisfies the
      -- Leibniz rule once the first component is identified with the identity.
      change TrivSqZeroExt.snd (ψ (a * b)) = a • TrivSqZeroExt.snd (ψ b) + b • TrivSqZeroExt.snd (ψ a)
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst_apply, hfst_apply]
      simp [mul_comm])
  refine ⟨Dloc, ?_, ?_⟩
  · -- Restricting the square-zero lift back to `R` recovers the original derivation.
    ext r
    exact congrArg TrivSqZeroExt.snd (AlgHom.congr_fun hψ r)
  · intro D' hD'
    let φ' : A →ₐ[ℤ] TrivSqZeroExt A A :=
      { toFun := fun a => (a, D' a)
        map_one' := by
          ext <;> simp
        map_mul' := by
          intro x y
          ext <;> simp [D'.leibniz, mul_comm]
        map_zero' := by
          ext <;> simp
        map_add' := by
          intro x y
          ext <;> simp
        commutes' := by
          intro n
          ext <;> simp }
    have hφ' : φ'.comp (IsScalarTower.toAlgHom ℤ R A) = φ := by
      -- Any other extension with the same restriction formula gives the same square-zero lift on
      -- the image of `R`.
      apply AlgHom.ext
      intro r
      ext
      · simpa [φ', φ, derivationToTrivSqZero]
      · simpa [φ', φ, derivationToTrivSqZero] using congr_fun hD' r
    have hφ'_ring : φ'.toRingHom = ψ.toRingHom := by
      -- Ring maps out of a localization are determined by their values on the base ring.
      apply IsLocalization.ringHom_ext S
      apply RingHom.ext
      intro r
      exact (AlgHom.congr_fun hφ' r).trans (AlgHom.congr_fun hψ r).symm
    ext a
    exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun hφ'_ring a)

-- Proof sketch: define the candidate by the quotient rule on fractions,
-- `D(r / s) = D(r) / s - r D(s) / s^2`, and prove it is well defined using the localization
-- relation. The derivation axioms follow from direct computation, and uniqueness is forced by the
-- fact that every element of the localization is represented by a fraction.
/-- Lemma 15.48.1 (2): for any multiplicative subset `S` of `R`, a derivation `D : R → R`
extends canonically to any localization `A` of `R` at `S`. -/
noncomputable def localizationExtension (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Derivation ℤ A A :=
  (existsUnique_localizationExtension_aux D S A).choose

theorem localizationExtension_compAlgebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    (D.localizationExtension S A).compAlgebraMap R =
      (Algebra.linearMap R A).compDer D :=
  (existsUnique_localizationExtension_aux D S A).choose_spec.left

@[simp]
theorem localizationExtension_algebraMap
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] (r : R) :
    D.localizationExtension S A (algebraMap R A r) = algebraMap R A (D r) :=
  congr_fun (D.localizationExtension_compAlgebraMap S A) r

theorem localizationExtension_unique
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    (Dloc : Derivation ℤ A A)
    (hDloc : Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D) :
    Dloc = D.localizationExtension S A := by
  exact (existsUnique_localizationExtension_aux D S A).choose_spec.right Dloc hDloc

/-- Existence and uniqueness of the canonical extension of a derivation to a localization. -/
theorem existsUnique_localizationExtension
    (D : Derivation ℤ R R) (S : Submonoid R) (A : Type v)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∃! Dloc : Derivation ℤ A A,
        Dloc.compAlgebraMap R = (Algebra.linearMap R A).compDer D :=
  ⟨D.localizationExtension S A, D.localizationExtension_compAlgebraMap S A,
    fun Dloc hDloc ↦ D.localizationExtension_unique S A Dloc hDloc⟩

end Localization

section FiniteType

variable {R' : Type v} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']

/-- Helper for Lemma 15.48.1: regularity of `algebraMap R R' g` makes the localization map into
the away ring injective. -/
private theorem away_algebraMap_injective_of_regular (g : R)
    (hg : IsRegular (algebraMap R R' g)) :
    Function.Injective (algebraMap R' (Localization.Away (algebraMap R R' g))) := by
  -- Every power of a regular element stays a non-zero-divisor, so localization is injective.
  have hpow :
      Submonoid.powers (algebraMap R R' g) ≤ nonZeroDivisors R' := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    rw [← isRegular_iff_mem_nonZeroDivisors]
    exact hg.pow n
  exact IsLocalization.injective (Localization.Away (algebraMap R R' g)) hpow

/-- Helper for Lemma 15.48.1: a bijective away comparison map upgrades to an `R`-algebra
equivalence between the two away localizations. -/
private noncomputable def awayMapAlgEquivOfBijective (g : R)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId R R') g)) :
    Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g) :=
  AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId R R') g) hAway

/-- Helper for Lemma 15.48.1: a finite type `R`-algebra admits a surjective finite polynomial
presentation. -/
private theorem finiteType_exists_mvPolynomial_presentation :
    ∃ m, ∃ π : MvPolynomial (Fin m) R →ₐ[R] R', Function.Surjective π := by
  -- The finite-type owner theorem already packages the desired quotient presentation.
  simpa using
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').1
      (inferInstance : Algebra.FiniteType R R')

/-- Helper for Lemma 15.48.1: conjugating a derivation across a ring equivalence keeps the
Leibniz rule and is the right transport for the away-localization comparison map. -/
private noncomputable def transportRingEquivDerivation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (δ : Derivation ℤ A A) : Derivation ℤ B B := by
  let eZ : A ≃ₗ[ℤ] B := LinearEquiv.restrictScalars ℤ e.toAddEquiv.toIntLinearEquiv
  refine Derivation.mk'
    ((eZ : A →ₗ[ℤ] B).comp (δ.toLinearMap.comp (eZ.symm : B →ₗ[ℤ] A))) ?_
  intro x y
  -- Rewrite the transported Leibniz rule back through `e.symm`, then simplify multiplicatively.
  change e (δ (e.symm (x * y))) = x * e (δ (e.symm y)) + y * e (δ (e.symm x))
  rw [map_mul, δ.leibniz]
  simp [map_mul, mul_comm]

/-- Helper for Lemma 15.48.1: finitely many elements of an away localization admit a single common
power denominator. -/
private theorem away_exists_common_power_denominator
    {A : Type v} [CommRing A] (a : A) (m : ℕ) (x : Fin m → Localization.Away a) :
    ∃ N : ℕ, ∃ y : Fin m → A,
      ∀ i, algebraMap A (Localization.Away a) (y i) =
        (algebraMap A (Localization.Away a) a) ^ N * x i := by
  classical
  have hrepr : ∀ i : Fin m, ∃ k : ℕ, ∃ b : A,
      algebraMap A (Localization.Away a) b =
        (algebraMap A (Localization.Away a) a) ^ k * x i := by
    intro i
    obtain ⟨u, hu⟩ := IsLocalization.surj (Submonoid.powers a) (x i)
    rcases u with ⟨b, s⟩
    rcases s.2 with ⟨k, hk⟩
    refine ⟨k, b, ?_⟩
    -- Rewrite the chosen denominator as an explicit power of `a`.
    have hs : (↑s : A) = a ^ k := by
      simpa using hk.symm
    rw [hs] at hu
    simpa [map_pow, mul_comm, mul_left_comm, mul_assoc] using hu.symm
  choose k b hb using hrepr
  let N : ℕ := Finset.univ.sup k
  refine ⟨N, fun i ↦ b i * a ^ (N - k i), ?_⟩
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  -- Multiply each chosen numerator by the missing power so every denominator becomes `a^N`.
  calc
    algebraMap A (Localization.Away a) (b i * a ^ (N - k i)) =
        algebraMap A (Localization.Away a) (b i) *
          algebraMap A (Localization.Away a) (a ^ (N - k i)) := by
            simp
    _ = ((algebraMap A (Localization.Away a) a) ^ k i * x i) *
          (algebraMap A (Localization.Away a) a) ^ (N - k i) := by
            rw [hb i, map_pow]
    _ = ((algebraMap A (Localization.Away a) a) ^ k i *
          (algebraMap A (Localization.Away a) a) ^ (N - k i)) * x i := by
            ac_rfl
    _ = (algebraMap A (Localization.Away a) a) ^ N * x i := by
            rw [← pow_add, add_comm, Nat.sub_add_cancel hki]

/-- Helper for Lemma 15.48.1: the standard square-zero map attached to a derivation sends `0` to
`0`. -/
private theorem source_derivation_to_triv_sq_zero_map_zero
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) :
    TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (f (Δ 0)) = (0 : TrivSqZeroExt B B) := by
  -- Both components vanish because ring homomorphisms and derivations preserve zero.
  ext <;> simp

/-- Helper for Lemma 15.48.1: the standard square-zero map attached to a derivation sends `1` to
`1`. -/
private theorem source_derivation_to_triv_sq_zero_map_one
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) :
    TrivSqZeroExt.inl (f 1) + TrivSqZeroExt.inr (f (Δ 1)) = (1 : TrivSqZeroExt B B) := by
  -- The scalar part is `1`, and every derivation kills `1`.
  ext <;> simp

/-- Helper for Lemma 15.48.1: the standard square-zero map attached to a derivation preserves
addition. -/
private theorem source_derivation_to_triv_sq_zero_map_add
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) (x y : A) :
    TrivSqZeroExt.inl (f (x + y)) + TrivSqZeroExt.inr (f (Δ (x + y))) =
      (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (f (Δ x))) +
        (TrivSqZeroExt.inl (f y) + TrivSqZeroExt.inr (f (Δ y))) := by
  -- Additivity is componentwise in the trivial square-zero extension.
  ext <;> simp

/-- Helper for Lemma 15.48.1: the standard square-zero map attached to a derivation preserves
multiplication. -/
private theorem source_derivation_to_triv_sq_zero_map_mul
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) (x y : A) :
    TrivSqZeroExt.inl (f (x * y)) + TrivSqZeroExt.inr (f (Δ (x * y))) =
      (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (f (Δ x))) *
        (TrivSqZeroExt.inl (f y) + TrivSqZeroExt.inr (f (Δ y))) := by
  -- The second component is exactly the Leibniz rule transported through `f`.
  ext <;> simp [Δ.leibniz, mul_comm]

/-- Helper for Lemma 15.48.1: a derivation and a ring map assemble into the usual square-zero map
`a ↦ (f a, f (Δ a))`. -/
private def source_derivation_to_triv_sq_zero
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) : A →+* TrivSqZeroExt B B :=
  { toFun := fun a ↦ TrivSqZeroExt.inl (f a) + TrivSqZeroExt.inr (f (Δ a))
    map_zero' := source_derivation_to_triv_sq_zero_map_zero f Δ
    map_one' := source_derivation_to_triv_sq_zero_map_one f Δ
    map_add' := source_derivation_to_triv_sq_zero_map_add f Δ
    map_mul' := source_derivation_to_triv_sq_zero_map_mul f Δ }

/-- Helper for Lemma 15.48.1: the square-zero map built from a derivation has the expected first
projection. -/
private theorem source_derivation_to_triv_sq_zero_fst
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) (a : A) :
    TrivSqZeroExt.fst (source_derivation_to_triv_sq_zero f Δ a) = f a := by
  -- The first component simply remembers the structural map `f`.
  simp [source_derivation_to_triv_sq_zero]

/-- Helper for Lemma 15.48.1: the square-zero map built from a derivation has the expected second
projection. -/
private theorem source_derivation_to_triv_sq_zero_snd
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (Δ : Derivation ℤ A A) (a : A) :
    TrivSqZeroExt.snd (source_derivation_to_triv_sq_zero f Δ a) = f (Δ a) := by
  -- The second component records the transported derivation value.
  simp [source_derivation_to_triv_sq_zero]

/-- Helper for Lemma 15.48.1: package the cleared generator values into the square-zero algebra map
on the polynomial presentation. -/
private noncomputable def polynomial_square_zero_map_of_cleared_generators
    {m : ℕ} (g : R) (N : ℕ) (π : MvPolynomial (Fin m) R →ₐ[R] R') (y : Fin m → R') :
    MvPolynomial (Fin m) R →ₐ[ℤ] TrivSqZeroExt R' R' :=
  (MvPolynomial.eval₂Hom
      (source_derivation_to_triv_sq_zero (algebraMap R R') (g ^ N • D))
      (fun i ↦ (π (MvPolynomial.X i), y i))).toIntAlgHom

/-- Helper for Lemma 15.48.1: on coefficients, the repaired polynomial square-zero map records the
scaled derivation `(g ^ N • D)`. -/
private theorem polynomial_square_zero_map_of_cleared_generators_C
    {m : ℕ} (g : R) (N : ℕ) (π : MvPolynomial (Fin m) R →ₐ[R] R') (y : Fin m → R')
    (r : R) :
    polynomial_square_zero_map_of_cleared_generators (D := D) g N π y (MvPolynomial.C r) =
      (algebraMap R R' r, algebraMap R R' ((g ^ N • D) r)) := by
  -- Evaluate on `C r`, which reduces immediately to the source square-zero map on `r`.
  change
    MvPolynomial.eval₂Hom
        (source_derivation_to_triv_sq_zero (algebraMap R R') (g ^ N • D))
        (fun i ↦ (π (MvPolynomial.X i), y i)) (MvPolynomial.C r) =
      (algebraMap R R' r, algebraMap R R' ((g ^ N • D) r))
  rw [MvPolynomial.eval₂Hom_C]
  ext <;> simp [source_derivation_to_triv_sq_zero]

/-- Helper for Lemma 15.48.1: on each polynomial variable, the square-zero map records the chosen
cleared generator value in the second component. -/
private theorem polynomial_square_zero_map_of_cleared_generators_X
    {m : ℕ} (g : R) (N : ℕ) (π : MvPolynomial (Fin m) R →ₐ[R] R') (y : Fin m → R')
    (i : Fin m) :
    polynomial_square_zero_map_of_cleared_generators (D := D) g N π y
      (MvPolynomial.X i) =
      (π (MvPolynomial.X i), y i) := by
  -- Evaluate on `X i`, which is definitionally the chosen generator value.
  change
    MvPolynomial.eval₂Hom
        (source_derivation_to_triv_sq_zero (algebraMap R R') (g ^ N • D))
        (fun j ↦ (π (MvPolynomial.X j), y j)) (MvPolynomial.X i) =
      (π (MvPolynomial.X i), y i)
  rw [MvPolynomial.eval₂Hom_X']

/-- Helper for Lemma 15.48.1: the first component of the polynomial square-zero map is the
original presentation map. -/
private theorem polynomial_square_zero_map_of_cleared_generators_fst
    {m : ℕ} (g : R) (N : ℕ) (π : MvPolynomial (Fin m) R →ₐ[R] R') (y : Fin m → R') :
    (TrivSqZeroExt.fstHom ℤ R' R').comp
        (polynomial_square_zero_map_of_cleared_generators (D := D) g N π y) =
      π.toRingHom.toIntAlgHom := by
  -- Compare the two algebra maps on coefficients and polynomial variables.
  apply MvPolynomial.algHom_ext'
  · ext r
    -- On coefficients, the first projection forgets the derivation term.
    change
      TrivSqZeroExt.fst
        (polynomial_square_zero_map_of_cleared_generators (D := D) g N π y
          (MvPolynomial.C r)) =
        π.toIntAlgHom (MvPolynomial.C r)
    change
      TrivSqZeroExt.fst
        (MvPolynomial.eval₂Hom
          (source_derivation_to_triv_sq_zero (algebraMap R R') (g ^ N • D))
          (fun i ↦ (π (MvPolynomial.X i), y i)) (MvPolynomial.C r)) =
        π.toIntAlgHom (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C]
    simp [source_derivation_to_triv_sq_zero]
  · intro i
    -- On variables, the first projection is exactly the chosen presentation value.
    change
      TrivSqZeroExt.fst
        (polynomial_square_zero_map_of_cleared_generators (D := D) g N π y
          (MvPolynomial.X i)) =
        π.toIntAlgHom (MvPolynomial.X i)
    change
      TrivSqZeroExt.fst
        (MvPolynomial.eval₂Hom
          (source_derivation_to_triv_sq_zero (algebraMap R R') (g ^ N • D))
          (fun j ↦ (π (MvPolynomial.X j), y j)) (MvPolynomial.X i)) =
        π.toIntAlgHom (MvPolynomial.X i)
    rw [MvPolynomial.eval₂Hom_X']
    simp

/-- Helper for Lemma 15.48.1: after transporting the away-localization extension across the away
comparison isomorphism and scaling by one power of `g`, the value on every coefficient still comes
from `R'`. -/
private theorem scaled_transported_away_derivation_algebraMap
    (g : R)
    (eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g))
    (N : ℕ) (r : R) :
    let A := Localization.Away (algebraMap R R' g)
    let a : R' := algebraMap R R' g
    let Δg := transportRingEquivDerivation eAway.toRingEquiv
      (D.localizationExtension (Submonoid.powers g) (Localization.Away g))
    let ΔN := (algebraMap R' A a) ^ N • Δg
    ΔN (algebraMap R' A (algebraMap R R' r)) =
      algebraMap R' A (algebraMap R R' ((g ^ N • D) r)) := by
  dsimp
  have hmap_r :
      algebraMap R' (Localization.Away (algebraMap R R' g)) (algebraMap R R' r) =
        algebraMap R (Localization.Away (algebraMap R R' g)) r := by
    exact
      congrArg
        (fun f : R →+* Localization.Away (algebraMap R R' g) => f r)
        (IsScalarTower.algebraMap_eq R R'
          (Localization.Away (algebraMap R R' g)))
  have hΔg :
      transportRingEquivDerivation eAway.toRingEquiv
          (D.localizationExtension (Submonoid.powers g) (Localization.Away g))
          (algebraMap R' (Localization.Away (algebraMap R R' g))
            (algebraMap R R' r)) =
        algebraMap R' (Localization.Away (algebraMap R R' g))
          (algebraMap R R' (D r)) := by
    -- Rewrite the transported coefficient back through the away equivalence, then use the
    -- localization extension formula on the original away ring.
    change eAway
        ((D.localizationExtension (Submonoid.powers g) (Localization.Away g))
          (eAway.symm
            (algebraMap R' (Localization.Away (algebraMap R R' g))
              (algebraMap R R' r)))) =
      _
    have hsymm :
        eAway.symm
            (algebraMap R' (Localization.Away (algebraMap R R' g))
              (algebraMap R R' r)) =
          algebraMap R (Localization.Away g) r := by
      apply eAway.injective
      simpa [hmap_r] using (eAway.commutes r)
    rw [hsymm, localizationExtension_algebraMap]
    simpa using
      (congrArg
        (fun f : R →+* Localization.Away (algebraMap R R' g) => f (D r))
        (IsScalarTower.algebraMap_eq R R'
          (Localization.Away (algebraMap R R' g))))
  -- The scaled coefficient formula is just multiplicativity of the algebra map.
  rw [show
      ((algebraMap R' (Localization.Away (algebraMap R R' g))
            (algebraMap R R' g)) ^ N •
          transportRingEquivDerivation eAway.toRingEquiv
            (D.localizationExtension (Submonoid.powers g) (Localization.Away g)))
        (algebraMap R' (Localization.Away (algebraMap R R' g))
          (algebraMap R R' r)) =
        (algebraMap R' (Localization.Away (algebraMap R R' g))
            (algebraMap R R' g)) ^ N *
          transportRingEquivDerivation eAway.toRingEquiv
            (D.localizationExtension (Submonoid.powers g) (Localization.Away g))
            (algebraMap R' (Localization.Away (algebraMap R R' g))
              (algebraMap R R' r)) by
      rfl]
  rw [hΔg]
  simp [smul_eq_mul, map_mul, map_pow, mul_assoc]

-- Proof sketch: choose finitely many `R`-algebra generators of `R'` and clear denominators after
-- transporting them across an isomorphism between the two away localizations where `g` becomes
-- invertible. For sufficiently large `N`, the scaled derivation `g ^ N • D` carries each
-- generator into `R'`, hence by the Leibniz rule it extends from `R` to an `R'`-valued derivation
-- on the finite type algebra `R'`.
/-- Canonical-owner reformulation of Lemma 15.48.1 (3): if the canonical comparison
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective and `algebraMap R R' g` is a
nonzerodivisor in `R'`, then some multiple `g ^ N • D` extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_bijective_awayMap (g : R)
    (hAway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId R R') g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) := by
  classical
  -- Route correction: fix the source-proof skeleton first by naming the away-localization
  -- equivalence and a finite polynomial presentation before attempting denominator clearing and
  -- quotient descent.
  let eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g) :=
    awayMapAlgEquivOfBijective (R := R) (R' := R') g hAway
  obtain ⟨m, π, hπ⟩ :=
    finiteType_exists_mvPolynomial_presentation (R := R) (R' := R')
  let A := Localization.Away (algebraMap R R' g)
  let a : R' := algebraMap R R' g
  let Δg :=
    transportRingEquivDerivation eAway.toRingEquiv
      (D.localizationExtension (Submonoid.powers g) (Localization.Away g))
  let generatorDeriv : Fin m → Localization.Away (algebraMap R R' g) := fun i ↦
    Δg (algebraMap R' A (π (MvPolynomial.X i)))
  obtain ⟨N, y, hy⟩ :=
    away_exists_common_power_denominator (a := a) m generatorDeriv
  let ΔN := (algebraMap R' A a) ^ N • Δg
  have hcoeff :
      ∀ r : R, ΔN (algebraMap R' A (algebraMap R R' r)) =
        algebraMap R' A (algebraMap R R' ((g ^ N • D) r)) := by
    intro r
    -- Coefficients are controlled by the transported localization extension formula.
    simpa [A, a, Δg, ΔN] using
      scaled_transported_away_derivation_algebraMap (D := D) (R' := R') g eAway N r
  let S : Subalgebra R R' :=
    { carrier := fun x ↦ ∃ z : R', algebraMap R' A z = ΔN (algebraMap R' A x)
      algebraMap_mem' := by
        intro r
        -- The scaled coefficient computation shows the closure subalgebra contains `R`.
        exact ⟨algebraMap R R' ((g ^ N • D) r), hcoeff r⟩
      zero_mem' := by
        -- The derivation of `0` is zero, so `0` is in the closure subalgebra.
        refine ⟨0, ?_⟩
        rw [map_zero, map_zero, Derivation.map_zero]
      add_mem' := by
        intro x y hx hy'
        rcases hx with ⟨zx, hzx⟩
        rcases hy' with ⟨zy, hzy⟩
        -- Additivity of `ΔN` gives closure under sums.
        refine ⟨zx + zy, ?_⟩
        rw [map_add, hzx, hzy, map_add, ΔN.map_add]
      one_mem' := by
        -- The derivation of `1` is zero, so `1` is in the closure subalgebra as well.
        refine ⟨0, ?_⟩
        rw [map_zero, map_one, Derivation.map_one]
      mul_mem' := by
        intro x y hx hy'
        rcases hx with ⟨zx, hzx⟩
        rcases hy' with ⟨zy, hzy⟩
        -- The Leibniz rule keeps the closure property stable under multiplication.
        refine ⟨x * zy + y * zx, ?_⟩
        rw [map_add, map_mul, map_mul, hzx, hzy, ΔN.leibniz] }
  have hgen : ∀ i : Fin m, π (MvPolynomial.X i) ∈ S := by
    intro i
    -- The common denominator witnesses put each chosen generator into the closure subalgebra.
    refine ⟨y i, ?_⟩
    simpa [A, a, generatorDeriv, ΔN, smul_eq_mul] using hy i
  let β : MvPolynomial (Fin m) R →ₐ[R] S :=
    MvPolynomial.aeval fun i ↦ ⟨π (MvPolynomial.X i), hgen i⟩
  have hβ : S.val.comp β = π := by
    -- Both maps agree on polynomial variables, so they are equal.
    apply MvPolynomial.algHom_ext
    intro i
    simp [β]
  have hpre :
      ∀ x : R', ∃ z : R', algebraMap R' A z = ΔN (algebraMap R' A x) := by
    intro x
    obtain ⟨p, rfl⟩ := hπ x
    have hβ_apply : (β p : R') = π p := by
      exact congrArg (fun f : MvPolynomial (Fin m) R →ₐ[R] R' => f p) hβ
    -- Every element comes from a polynomial in the generators, and the closure subalgebra
    -- contains those generators and the coefficients.
    simpa [hβ_apply] using (β p).2
  have hAinj : Function.Injective (algebraMap R' A) :=
    away_algebraMap_injective_of_regular (R := R) (R' := R') g hg
  let δ : R' → R' := fun x ↦ Classical.choose (hpre x)
  have hδ :
      ∀ x : R', algebraMap R' A (δ x) = ΔN (algebraMap R' A x) := by
    intro x
    exact Classical.choose_spec (hpre x)
  have hδ_zero : δ 0 = 0 := by
    -- Injectivity of the away map lets us descend the zero identity from the localization.
    apply hAinj
    rw [hδ, map_zero, Derivation.map_zero, map_zero]
  have hδ_add : ∀ x y : R', δ (x + y) = δ x + δ y := by
    intro x y
    -- The descended operation is additive because `ΔN` is additive.
    apply hAinj
    rw [hδ, hδ, hδ, map_add, map_add, ΔN.map_add]
  have hδ_leibniz : ∀ x y : R', δ (x * y) = x * δ y + y * δ x := by
    intro x y
    -- The descended operation satisfies Leibniz because `ΔN` does.
    apply hAinj
    rw [hδ, hδ, hδ, map_add, map_mul, map_mul, ΔN.leibniz]
  have hδ_algebraMap :
      ∀ r : R, δ (algebraMap R R' r) = algebraMap R R' ((g ^ N • D) r) := by
    intro r
    -- The restriction to coefficients is exactly the scaled base derivation.
    apply hAinj
    rw [hδ, hcoeff]
  let δAdd : R' →+ R' :=
    { toFun := δ
      map_zero' := hδ_zero
      map_add' := hδ_add }
  let D' : Derivation ℤ R' R' := Derivation.mk' δAdd.toIntLinearMap hδ_leibniz
  refine ⟨N, D', ?_⟩
  -- The descended derivation restricts to `(g ^ N • D)` on `R`.
  apply Derivation.ext
  intro r
  simpa [D', δAdd, δ] using hδ_algebraMap r

/-- Lemma 15.48.1 (3): let `R → R'` be a finite type extension and let `g : R` be such that
`Localization.Away g` and `Localization.Away (algebraMap R R' g)` are isomorphic as `R`-algebras
and `algebraMap R R' g` is a nonzerodivisor in `R'`. Equivalently, the canonical comparison map
`Localization.awayMapₐ (Algebra.ofId R R') g` is bijective. Then some multiple `g ^ N • D`
extends to a derivation of `R'`. -/
theorem exists_pow_smul_extension_of_finiteType_of_away_iso (g : R)
    (eAway : Localization.Away g ≃ₐ[R] Localization.Away (algebraMap R R' g))
    (hg : IsRegular (algebraMap R R' g)) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      D'.compAlgebraMap R = (Algebra.linearMap R R').compDer (g ^ N • D) :=
  D.exists_pow_smul_extension_of_finiteType_of_bijective_awayMap g
    (by
      have hEq : Localization.awayMapₐ (Algebra.ofId R R') g = eAway.toAlgHom := by
        apply Localization.algHom_ext (Submonoid.powers g)
        ext
      simpa [hEq] using eAway.bijective)
    hg

end FiniteType

end Derivation

end
