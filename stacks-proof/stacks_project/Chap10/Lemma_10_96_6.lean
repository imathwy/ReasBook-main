import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal
open Ideal.Quotient

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Helper for Lemma 10.96.6: for a representative Cauchy sequence, a unit modulo `I` gives units
in all quotients `R / I ^ n`. -/
lemma evalₐ_mk_isUnit_of_evalOneₐ_isUnit (f : AdicCompletion.AdicCauchySequence I R)
    (hx : IsUnit (AdicCompletion.evalOneₐ I (AdicCompletion.mk I R f))) :
    ∀ n, IsUnit (Ideal.Quotient.mk (I ^ n) (f n)) := by
  intro n
  induction n with
  | zero =>
      -- Step 2: the zeroth quotient is the quotient by `⊤`, hence every element is equal to `1`.
      letI : Unique (R ⧸ I ^ 0) := by
        simpa [pow_zero] using (inferInstance : Unique (R ⧸ (⊤ : Ideal R)))
      have h0 : IsUnit (Ideal.Quotient.mk (I ^ 0) (f 0)) := by
        have htrivial : Ideal.Quotient.mk (I ^ 0) (f 0) = (1 : R ⧸ I ^ 0) := Subsingleton.elim _ _
        rw [htrivial]
        exact isUnit_one
      exact h0
  | succ n ih =>
      cases n with
      | zero =>
          -- Step 3: at stage `1`, rewrite `evalOneₐ` as the first quotient evaluation.
          rw [← AdicCompletion.factorₐ_evalₐ_one (I := I) (AdicCompletion.mk I R f)] at hx
          have h1 : IsUnit (Ideal.Quotient.mk I (f 1)) := by
            simpa using hx
          rwa [pow_one]
      | succ n =>
          -- Step 4: for higher stages, lift the unit inductively along the transition map.
          have himage :
              Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
                  (Ideal.Quotient.mk (I ^ (n + 2)) (f (n + 2))) =
                Ideal.Quotient.mk (I ^ (n + 1)) (f (n + 1)) := by
            simpa [Ideal.Quotient.factorPow] using
              (AdicCompletion.Ideal.mk_eq_mk (I := I) (m := n + 1) (n := n + 2)
                (Nat.le_succ (n + 1)) f)
          apply factorPowSucc.isUnit_of_isUnit_image (I := I) (n := n + 1) (Nat.succ_pos _)
          exact himage ▸ ih

/-- Helper for Lemma 10.96.6: if an element of the adic completion is a unit modulo `I`, then each
of its quotient coordinates is a unit modulo `I ^ n`. -/
lemma evalₐ_isUnit_of_evalOneₐ_isUnit (x : AdicCompletion I R)
    (hx : IsUnit (AdicCompletion.evalOneₐ I x)) :
    ∀ n, IsUnit (AdicCompletion.evalₐ I n x) := by
  let p : AdicCompletion I R → Prop := fun y ↦
    IsUnit (AdicCompletion.evalOneₐ I y) → ∀ n, IsUnit (AdicCompletion.evalₐ I n y)
  -- Step 1: reduce to a concrete Cauchy sequence representative, so each stage is a quotient class.
  revert hx
  change p x
  refine AdicCompletion.induction_on (I := I) (M := R) x ?_
  intro f hx n
  simpa [AdicCompletion.evalₐ_mk] using evalₐ_mk_isUnit_of_evalOneₐ_isUnit (I := I) f hx n

/-- Helper for Lemma 10.96.6: once inverse classes are chosen in each quotient `R / I ^ n`, the
compatibility of the original Cauchy sequence forces those inverse representatives to form an
`I`-adic Cauchy sequence as well. -/
lemma inverse_coordinates_compatible (f : AdicCompletion.AdicCauchySequence I R)
    (hf : ∀ n, IsUnit (Ideal.Quotient.mk (I ^ n) (f n))) (g : ℕ → R)
    (hg : ∀ n, Ideal.Quotient.mk (I ^ n) (g n) = (↑((hf n).unit⁻¹) : R ⧸ I ^ n)) :
    ∀ n, g n ≡ g (n + 1) [SMOD (I ^ n • ⊤ : Ideal R)] := by
  intro n
  -- Step 1: the chosen lift at stage `n + 1` is still an inverse after passing down to `R / I ^ n`.
  have hsucc :
      Ideal.Quotient.mk (I ^ n) (g (n + 1)) * Ideal.Quotient.mk (I ^ n) (f n) = 1 := by
    have hsucc_top :
        Ideal.Quotient.mk (I ^ (n + 1)) (g (n + 1)) *
            Ideal.Quotient.mk (I ^ (n + 1)) (f (n + 1)) = 1 := by
      calc
        Ideal.Quotient.mk (I ^ (n + 1)) (g (n + 1)) *
            Ideal.Quotient.mk (I ^ (n + 1)) (f (n + 1))
            = (↑((hf (n + 1)).unit⁻¹) : R ⧸ I ^ (n + 1)) *
                Ideal.Quotient.mk (I ^ (n + 1)) (f (n + 1)) := by rw [hg (n + 1)]
        _ = (↑((hf (n + 1)).unit⁻¹) : R ⧸ I ^ (n + 1)) *
              ↑((hf (n + 1)).unit) := by rw [IsUnit.unit_spec (hf (n + 1))]
        _ = 1 := by simp
    have hsucc_image :
        Ideal.Quotient.mk (I ^ n) (g (n + 1)) *
            Ideal.Quotient.mk (I ^ n) (f (n + 1)) = 1 := by
      simpa [Ideal.Quotient.factorPowSucc, Ideal.Quotient.factorPow] using
        congrArg (Ideal.Quotient.factorPow I (Nat.le_succ n)) hsucc_top
    rw [AdicCompletion.Ideal.mk_eq_mk (I := I) (m := n) (n := n + 1) (Nat.le_succ n) f] at hsucc_image
    exact hsucc_image
  -- Step 2: compare that inverse with the chosen inverse at stage `n` and use uniqueness.
  have hquot :
      Ideal.Quotient.mk (I ^ (n : ℕ)) (g (n + 1)) =
        Ideal.Quotient.mk (I ^ n) (g n) := by
    rw [hg n]
    exact ((hf n).unit).eq_inv_of_mul_eq_one_right (by simpa [IsUnit.unit_spec] using hsucc)
  simpa [SModEq.def, smul_eq_mul, Ideal.mul_top] using hquot.symm

-- Proof sketch: represent `x` by a Cauchy sequence `(x_n)`. The previous helper shows that
-- each quotient class `x_n mod I^n` is a unit. Choose representatives of the inverse classes,
-- use the compatibility helper to see that these representatives form a Cauchy sequence, and
-- then compare quotient coordinates to prove that this new sequence gives an inverse in the
-- completion.
-- Route correction: this proof now follows the source inverse-limit construction directly,
-- instead of deducing invertibility from the Jacobson-radical statement.
/-- Lemma 10.96.6 (1): an element of the `I`-adic completion whose image in `R ⧸ I` is a unit is
already a unit in the completion. -/
theorem isUnit_of_isUnit_evalOneₐ (x : AdicCompletion I R)
    (hx : IsUnit (AdicCompletion.evalOneₐ I x)) : IsUnit x := by
  classical
  let p : AdicCompletion I R → Prop := fun y ↦
    IsUnit (AdicCompletion.evalOneₐ I y) → IsUnit y
  -- Step 1: reduce to a Cauchy sequence representative and get units in every quotient stage.
  revert hx
  change p x
  refine AdicCompletion.induction_on (I := I) (M := R) x ?_
  intro f hx
  have hf : ∀ n, IsUnit (Ideal.Quotient.mk (I ^ n) (f n)) :=
    evalₐ_mk_isUnit_of_evalOneₐ_isUnit (I := I) f hx
  -- Step 2: choose representatives of the inverse quotient classes.
  let g : ℕ → R := fun n ↦
    Classical.choose (Ideal.Quotient.mk_surjective (↑((hf n).unit⁻¹) : R ⧸ I ^ n))
  have hg : ∀ n, Ideal.Quotient.mk (I ^ n) (g n) = (↑((hf n).unit⁻¹) : R ⧸ I ^ n) := by
    intro n
    exact Classical.choose_spec (Ideal.Quotient.mk_surjective (↑((hf n).unit⁻¹) : R ⧸ I ^ n))
  let gSeq : AdicCompletion.AdicCauchySequence I R :=
    AdicCompletion.AdicCauchySequence.mk (I := I) (M := R) g
      (inverse_coordinates_compatible (I := I) f hf g hg)
  -- Step 3: check stagewise that the new Cauchy sequence is an inverse.
  refine IsUnit.of_mul_eq_one (AdicCompletion.mk I R gSeq) ?_
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_mul, map_one, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ n) (f n) * Ideal.Quotient.mk (I ^ n) (g n) = 1
  calc
    Ideal.Quotient.mk (I ^ n) (f n) * Ideal.Quotient.mk (I ^ n) (g n)
        = Ideal.Quotient.mk (I ^ n) (f n) * (↑((hf n).unit⁻¹) : R ⧸ I ^ n) := by rw [hg n]
    _ = ↑((hf n).unit) * (↑((hf n).unit⁻¹) : R ⧸ I ^ n) := by rw [IsUnit.unit_spec (hf n)]
    _ = 1 := by simp

-- Proof sketch: if `x` lies in the kernel, then for every `y` the element `1 + x * y` maps to
-- `1` in `R ⧸ I`. Clause (1) lifts that unit back to the completion, which is exactly the
-- criterion `Ideal.mem_jacobson_bot`.
/-- Lemma 10.96.6 (5): the kernel of the canonical projection `R^∧ → R ⧸ I` is contained in the
Jacobson radical of the `I`-adic completion. -/
theorem ker_evalOneₐ_le_jacobson :
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  intro x hx
  -- Step 1: test the Jacobson criterion against an arbitrary multiplier.
  refine Ideal.mem_jacobson_bot.2 ?_
  intro y
  have hx0 : AdicCompletion.evalOneₐ I x = 0 := RingHom.mem_ker.mp hx
  have himage : AdicCompletion.evalOneₐ I (1 + x * y) = 1 := by
    rw [map_add, map_one, map_mul, hx0, zero_mul, add_zero]
  -- Step 2: lift the obvious unit `1` from the quotient back to the completion.
  simpa [add_comm] using
    isUnit_of_isUnit_evalOneₐ (I := I) (1 + x * y) (himage ▸ isUnit_one)

-- Proof sketch: the image of `I` in the completion is sent to `0` by `R^∧ → R ⧸ I`, so it is
-- contained in the kernel; clause (5) then places it in the Jacobson radical.
/-- Lemma 10.96.6 (4): the extended ideal `I R^∧` is contained in the Jacobson radical of the
`I`-adic completion. -/
theorem completion_ideal_le_jacobson :
    Ideal.map (algebraMap R (AdicCompletion I R)) I ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  refine le_trans ?_ (ker_evalOneₐ_le_jacobson I)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap R (AdicCompletion I R) x ∈ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom
  rw [RingHom.mem_ker]
  simpa using (eq_zero_iff_mem.mpr hx)

-- Proof sketch: if `x - 1` lies in the extended ideal `I R^∧`, then clause (4) puts that
-- difference in the Jacobson radical of the completion, and `1 +` an element of the Jacobson
-- radical is invertible.
/-- Lemma 10.96.6 (3): every element of the `I`-adic completion congruent to `1` modulo the
extended ideal `I R^∧` is a unit. -/
theorem isUnit_of_sub_one_mem_completion_ideal (x : AdicCompletion I R)
    (hx : x - 1 ∈ Ideal.map (algebraMap R (AdicCompletion I R)) I) : IsUnit x := by
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot x ((completion_ideal_le_jacobson I) hx)

-- Proof sketch: if `x - 1 ∈ I`, then its image in the completion differs from `1` by an element
-- of the extended ideal `I R^∧`; apply the Jacobson-radical containment from clauses (4) and (5)
-- together with `Ideal.isUnit_of_sub_one_mem_jacobson_bot`.
/-- Lemma 10.96.6 (2): an element of `R` congruent to `1` modulo `I` maps to a unit in the
`I`-adic completion. -/
theorem isUnit_algebraMap_of_sub_one_mem (x : R) (hx : x - 1 ∈ I) :
    IsUnit (algebraMap R (AdicCompletion I R) x) := by
  refine isUnit_of_sub_one_mem_completion_ideal I (algebraMap R (AdicCompletion I R) x) ?_
  simpa [map_sub, map_one] using
    Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) hx

end
