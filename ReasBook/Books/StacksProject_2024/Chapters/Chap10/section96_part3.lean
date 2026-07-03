import Mathlib
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_96_6 (from Chap10) -/
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

/-! ### Lemma_10_96_7 (from Chap10) -/
universe u v

section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: replace the `I`-adic inverse system by the cofinal system built from the chosen
-- generators, using `(f ^ n | f ∈ s)` between `I ^ n` and `I ^ (n * s.card)`. A compatible family
-- in the `I`-adic completion can then be written as a finite sum of generatorwise `f`-adic
-- expansions, and surjectivity for each principal generator ideal provides lifts whose sum maps to
-- the original element.
/-- Helper for Lemma 10.96.7: the ideal generated by the `n`th powers of the chosen generators is
contained in `I ^ n`. -/
private theorem generator_pow_span_le_pow
    {I : Ideal R} (s : Finset R) (hI : Ideal.span (↑s : Set R) = I) (n : ℕ) :
    Ideal.span ((↑s : Set R).image fun f ↦ f ^ n) ≤ I ^ n := by
  -- Each generator `f ^ n` already belongs to `I ^ n` because `f ∈ I`.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ I := by
    rw [← hI]
    exact Ideal.subset_span hf
  exact Ideal.pow_mem_pow hfI n

/-- Helper for Lemma 10.96.7: after passing to the cofinal subsequence `n ↦ n * s.card`, the
`I`-power filtration is dominated by the filtration generated by the `n`th powers of the chosen
generators. -/
private theorem pow_mul_card_le_generator_pow_span
    (s : Finset R) (hs : s.Nonempty) (n : ℕ) :
    Ideal.span (↑s : Set R) ^ (n * s.card) ≤
      Ideal.span ((↑s : Set R).image fun f ↦ f ^ n) := by
  classical
  refine hs.cons_induction ?_ ?_
  · intro a
    -- For a singleton generator set, both filtrations are the same principal-power filtration.
    simpa [Ideal.span_singleton_pow]
  · intro a t hat ht ih
    -- Split off the distinguished generator and compare the power of the supremum with the
    -- supremum of the corresponding powers.
    calc
      Ideal.span (↑(Finset.cons a t hat) : Set R) ^ (n * (Finset.cons a t hat).card)
          = (Ideal.span ({a} : Set R) ⊔ Ideal.span (↑t : Set R)) ^ (n + n * t.card) := by
            rw [Finset.card_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]
            simp [Finset.coe_cons, Ideal.span_insert]
      _ ≤ Ideal.span ({a} : Set R) ^ n ⊔ Ideal.span (↑t : Set R) ^ (n * t.card) := by
            exact Ideal.sup_pow_add_le_pow_sup_pow
      _ ≤ Ideal.span ({a} : Set R) ^ n ⊔
            Ideal.span ((↑t : Set R).image fun f ↦ f ^ n) := by
            exact sup_le_sup le_rfl ih
      _ = Ideal.span ((↑(Finset.cons a t hat) : Set R).image fun f ↦ f ^ n) := by
            simp [Finset.coe_cons, Set.image_insert_eq, Ideal.span_insert, Ideal.span_singleton_pow]

/-- Helper for Lemma 10.96.7: an element of the principal submodule `(f ^ n) M` is literally a
single `f ^ n`-multiple. -/
private theorem mem_span_singleton_pow_smul_top_iff_exists
    (f : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span ({f ^ n} : Set R) : Ideal R) • (⊤ : Submodule R M) ↔
      ∃ a : M, f ^ n • a = x := by
  constructor
  · intro hx
    -- Unfold membership in the ideal-smul submodule and collect the principal coefficient.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      rcases Ideal.mem_span_singleton'.1 hr with ⟨s, hs⟩
      refine ⟨s • m, ?_⟩
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun t : R ↦ t • m) hs
    · intro y z hy hz
      rcases hy with ⟨y', hy'⟩
      rcases hz with ⟨z', hz'⟩
      exact ⟨y' + z', by rw [smul_add, hy', hz']⟩
  · rintro ⟨a, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- Helper for Lemma 10.96.7: every element of the generator-power submodule can be written as a
finite sum `∑_{f ∈ s} f ^ n • a_f`. -/
private theorem mem_generator_pow_span_smul_top_iff_exists_sum
    (s : Finset R) (n : ℕ) (x : M) :
    x ∈ Ideal.span ((↑s : Set R).image fun f ↦ f ^ n) • (⊤ : Submodule R M) ↔
      (∃ a : R → M, (∀ f, f ∉ s → a f = 0) ∧
        (Finset.sum s (fun f ↦ f ^ n • a f) = x)) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
      constructor
      · intro hx
        -- The empty generator set gives the zero submodule, so the only represented element is `0`.
        refine ⟨0, ?_, ?_⟩
        · intro f hf
          simp
        · have hx0 : x = 0 := by
            simpa using hx
          simpa [hx0]
      · rintro ⟨a, ha, hsum⟩
        -- Conversely, a vanishing empty sum lands in the zero submodule.
        simpa [ha] using hsum.symm
  | @insert a s ha ih =>
      constructor
      · intro hx
        -- Split the generator-power submodule into the principal `a ^ n`-part and the tail.
        rcases Submodule.mem_sup.mp (by
          simpa [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Submodule.sup_smul]
            using hx) with ⟨y, hy, z, hz, rfl⟩
        rcases (mem_span_singleton_pow_smul_top_iff_exists a n y).mp hy with ⟨c, rfl⟩
        rcases (ih z).mp hz with ⟨b, hb0, hbsum⟩
        refine ⟨fun g ↦ if g = a then c else b g, ?_, ?_⟩
        · intro g hg
          by_cases hga : g = a
          · subst hga
            exact (hg (by simp)).elim
          · simp [hga, hb0 g fun hgs ↦ hg (Finset.mem_insert_of_mem hgs)]
        · -- The inserted coefficient contributes the principal part, and the tail remains unchanged.
          rw [Finset.sum_insert ha]
          simp
          have htail :
              Finset.sum s (fun f ↦ if f = a then f ^ n • c else f ^ n • b f) =
                Finset.sum s (fun f ↦ f ^ n • b f) := by
            apply Finset.sum_congr rfl
            intro f hf
            have hfa : f ≠ a := by
              intro hfa
              subst hfa
              exact ha hf
            simp [hfa]
          rw [htail, hbsum]
      · rintro ⟨b, hb0, hsum⟩
        -- Write the target sum as the sum of its `a`-term and the contribution from the tail.
        have htail_zero : ∀ f, f ∉ s → (if f = a then 0 else b f) = 0 := by
          intro f hf
          by_cases hfa : f = a
          · simp [hfa]
          · have hnot_insert : f ∉ insert a s := by
              simp [hfa, hf]
            simp [hfa, hb0 f hnot_insert]
        have htail_sum :
            Finset.sum s (fun f ↦ f ^ n • (if f = a then 0 else b f)) =
              Finset.sum s (fun f ↦ f ^ n • b f) := by
          apply Finset.sum_congr rfl
          intro f hf
          have hfa : f ≠ a := by
            intro hfa
            subst hfa
            exact ha hf
          simp [hfa]
        have hy :
            a ^ n • b a ∈ (Ideal.span ({a ^ n} : Set R) : Ideal R) • (⊤ : Submodule R M) := by
          exact (mem_span_singleton_pow_smul_top_iff_exists a n (a ^ n • b a)).2 ⟨b a, rfl⟩
        have hz :
            Finset.sum s (fun f ↦ f ^ n • b f) ∈
              Ideal.span ((↑s : Set R).image fun f ↦ f ^ n) • (⊤ : Submodule R M) := by
          rw [← htail_sum]
          exact (ih _).mpr ⟨fun f ↦ if f = a then 0 else b f, htail_zero, rfl⟩
        have hx' :
            x ∈
              ((Ideal.span ({a ^ n} : Set R) : Ideal R) • (⊤ : Submodule R M)) ⊔
                (Ideal.span ((↑s : Set R).image fun f ↦ f ^ n) • (⊤ : Submodule R M)) := by
          refine Submodule.mem_sup.mpr ?_
          refine ⟨a ^ n • b a, hy, Finset.sum s (fun f ↦ f ^ n • b f), hz, ?_⟩
          rw [Finset.sum_insert ha] at hsum
          simpa [add_comm, add_left_comm, add_assoc] using hsum
        simpa [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Submodule.sup_smul]
          using hx'

/-- Helper for Lemma 10.96.7: successive congruences imply full Cauchy compatibility. -/
private theorem smodEq_of_succ
    {J : Ideal R} {f : ℕ → M}
    (h : ∀ n, f n ≡ f (n + 1) [SMOD (J ^ n • (⊤ : Submodule R M))]) :
    ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (J ^ m • (⊤ : Submodule R M))] := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
      exact SModEq.rfl
  | succ n hmn ih =>
      exact ih.trans <|
        SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (h n)

/-- Helper for Lemma 10.96.7: adjoining the `N`th term changes the principal partial sum by an
element of the `N`th principal modulus. -/
private theorem principal_partial_sums_succ
    (f : R) (a : ℕ → M) (N : ℕ) :
    (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k)) ≡
      (Finset.sum (Finset.range (N + 1)) (fun k ↦ f ^ k • a k))
        [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))] := by
  -- The new summand is exactly an `f ^ N`-multiple, so the difference lies in the principal
  -- modulus at level `N`.
  rw [SModEq.sub_mem]
  have hmem : f ^ N • a N ∈ (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M)) := by
    rw [Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  simpa [Finset.sum_range_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    Submodule.neg_mem _ hmem

/-- Helper for Lemma 10.96.7: the principal partial sums form the full compatibility family
required by `IsPrecomplete.prec`. -/
private theorem principal_partial_sums_compatible
    (f : R) (a : ℕ → M) :
    ∀ {m n : ℕ}, m ≤ n →
      (Finset.sum (Finset.range m) (fun k ↦ f ^ k • a k)) ≡
        (Finset.sum (Finset.range n) (fun k ↦ f ^ k • a k))
          [SMOD (((Ideal.span ({f} : Set R)) ^ m) • (⊤ : Submodule R M))] := by
  -- Package the one-step congruences into the exact Cauchy-compatibility shape expected by
  -- `IsPrecomplete.prec`.
  exact smodEq_of_succ (J := Ideal.span ({f} : Set R))
    (f := fun N ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k))
    (principal_partial_sums_succ (M := M) f a)

/-- Helper for Lemma 10.96.7: each generatorwise principal series has a principal-adic limit once
the corresponding principal ideal is precomplete. -/
private theorem generator_partial_sums_converge
    (f : R) (a : ℕ → M) (hpre : IsPrecomplete (Ideal.span ({f} : Set R)) M) :
    ∃ b : M, ∀ N : ℕ,
      (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k)) ≡ b
        [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))] := by
  -- Route correction: the local source-faithful route was already correct, but Lean needed the
  -- full `{m, n}` compatibility family packaged explicitly before `IsPrecomplete.prec` would
  -- elaborate cleanly.
  -- Apply principal precompleteness to the compatible family of partial sums.
  simpa using
    (hpre.prec (f := fun N ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k))
      (principal_partial_sums_compatible (M := M) f a))

/-- Helper for Lemma 10.96.7: summing the cofinal increments reconstructs the chosen cofinal
subsequence. -/
private theorem cofinal_subsequence_telescope
    (s : Finset R) (r : ℕ) (u : ℕ → M) (a : ℕ → R → M)
    (hstep :
      ∀ n, u ((n + 1) * r) - u (n * r) = Finset.sum s (fun f ↦ f ^ n • a n f)) :
    ∀ N,
      u (N * r) =
        u 0 + Finset.sum s (fun f ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep' : u (N * r) + Finset.sum s (fun f ↦ f ^ N • a N f) = u ((N + 1) * r) := by
        -- Re-express the given difference as an additive recursion step.
        simpa [add_assoc, add_left_comm, add_comm] using
          (sub_eq_iff_eq_add.1 (hstep N)).symm
      calc
        u ((N + 1) * r) = u (N * r) + Finset.sum s (fun f ↦ f ^ N • a N f) := by
          simpa using hstep'.symm
        _ = u 0 +
              Finset.sum s (fun f ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) +
                Finset.sum s (fun f ↦ f ^ N • a N f) := by
              rw [ih]
        _ = u 0 +
              Finset.sum s
                (fun f ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f) + f ^ N • a N f) := by
              rw [add_assoc, ← Finset.sum_add_distrib]
        _ = u 0 +
              Finset.sum s (fun f ↦ Finset.sum (Finset.range (N + 1)) (fun k ↦ f ^ k • a k f)) := by
              apply congrArg (fun t ↦ u 0 + Finset.sum s t)
              funext f
              simp [Finset.sum_range_succ]

/-- Helper for Lemma 10.96.7: each principal modulus `((f)^N) M` is contained in the common
generator-power modulus `J_N M`. -/
private theorem principal_pow_smul_top_le_generator_pow_span_smul_top
    (s : Finset R) {f : R} (hf : f ∈ s) (N : ℕ) :
    (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M)) ≤
      Ideal.span ((↑s : Set R).image fun g ↦ g ^ N) • (⊤ : Submodule R M) := by
  -- Rewrite the principal power as the singleton span and insert that generator into `J_N`.
  rw [Ideal.span_singleton_pow]
  apply Submodule.smul_mono_left
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  exact Ideal.subset_span (Set.mem_image_of_mem (fun g ↦ g ^ N) hf)

/-- Helper for Lemma 10.96.7: once each generatorwise limit is transported to the common modulus
`J_N M`, `SModEq.sum` combines them into one congruence. -/
private theorem sum_of_generatorwise_limits_smodEq
    (s : Finset R) (a : ℕ → R → M) (b : R → M)
    (hb : ∀ f ∈ s, ∀ N,
      (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) ≡ b f
        [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))]) :
    ∀ N,
      Finset.sum s (fun f ↦ Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) ≡
        Finset.sum s b
          [SMOD (Ideal.span ((↑s : Set R).image fun g ↦ g ^ N) • (⊤ : Submodule R M))] := by
  intro N
  -- Move every principal congruence to the shared modulus before summing.
  apply SModEq.sum
  intro f hf
  exact SModEq.mono
    (principal_pow_smul_top_le_generator_pow_span_smul_top (M := M) s hf N)
    (hb f hf N)

/-- Helper for Lemma 10.96.7: the cofinal subsequence `n ↦ x (n * s.card)` converges modulo the
generator-power filtration to the sum of the generatorwise limits. -/
private theorem cofinal_subsequence_limit_smodEq
    (s : Finset R) (x : ℕ → M) (a : ℕ → R → M) (b : R → M)
    (hstep :
      ∀ n, x ((n + 1) * s.card) - x (n * s.card) = Finset.sum s (fun f ↦ f ^ n • a n f))
    (hb : ∀ f ∈ s, ∀ N,
      (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) ≡ b f
        [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))]) :
    ∀ N,
      x (N * s.card) ≡ x 0 + Finset.sum s b
        [SMOD (Ideal.span ((↑s : Set R).image fun g ↦ g ^ N) • (⊤ : Submodule R M))] := by
  intro N
  -- Telescope the cofinal increments, then replace the finite partial sums by their limits.
  rw [cofinal_subsequence_telescope s s.card x a hstep N]
  exact SModEq.add SModEq.rfl (sum_of_generatorwise_limits_smodEq (M := M) s a b hb N)

/-- Lemma 10.96.7 in owner form: if an ideal `I` is generated by a finite set `s` and `M` is
precomplete for the adic topology of each principal generator ideal `(f)` with `f ∈ s`, then `M`
is `I`-adically precomplete. -/
theorem isPrecomplete_of_span_eq_of_generatorwise
    {I : Ideal R} (s : Finset R) (hI : Ideal.span (↑s : Set R) = I)
    (hpre : ∀ f ∈ s, IsPrecomplete (Ideal.span ({f} : Set R)) M) :
    IsPrecomplete I M := by
  classical
  by_cases hs : s.Nonempty
  · refine ⟨fun x hx => ?_⟩
    let r : ℕ := s.card
    let J : ℕ → Ideal R := fun N ↦ Ideal.span ((↑s : Set R).image fun f ↦ f ^ N)
    have hcofinal_le : ∀ n, I ^ (n * r) • (⊤ : Submodule R M) ≤ J n • (⊤ : Submodule R M) := by
      intro n
      -- The cofinal subsequence uses the source inclusion `I^(n * r) ≤ J_n`.
      have hpow :
          I ^ (n * r) ≤ J n := by
        simpa [J, r, hI] using pow_mul_card_le_generator_pow_span (s := s) hs n
      exact Submodule.smul_mono_left hpow
    have hstep_mem : ∀ n, x ((n + 1) * r) - x (n * r) ∈ J n • (⊤ : Submodule R M) := by
      intro n
      -- Compare consecutive terms along the cofinal subsequence and transport the modulus to `J_n`.
      have hcongr :
          x (n * r) ≡ x ((n + 1) * r) [SMOD (J n • (⊤ : Submodule R M))] := by
        exact SModEq.mono (hcofinal_le n)
          (hx (m := n * r) (n := (n + 1) * r) (Nat.mul_le_mul_right r (Nat.le_succ n)))
      have hmem : x (n * r) - x ((n + 1) * r) ∈ J n • (⊤ : Submodule R M) :=
        SModEq.sub_mem.mp hcongr
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Submodule.neg_mem _ hmem
    have hexpansion :
        ∀ n, ∃ a : R → M, (∀ f, f ∉ s → a f = 0) ∧
          Finset.sum s (fun f ↦ f ^ n • a f) = x ((n + 1) * r) - x (n * r) := by
      intro n
      exact (mem_generator_pow_span_smul_top_iff_exists_sum (M := M) s n
        (x ((n + 1) * r) - x (n * r))).mp (hstep_mem n)
    choose a ha_zero hstep_sum using hexpansion
    have hlimits :
        ∀ f ∈ s, ∃ b : M, ∀ N,
          (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) ≡ b
            [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))] := by
      intro f hf
      exact generator_partial_sums_converge (M := M) f (fun k ↦ a k f) (hpre f hf)
    choose b₀ hb₀ using hlimits
    let b : R → M := fun f ↦ if hf : f ∈ s then b₀ f hf else 0
    have hb :
        ∀ f ∈ s, ∀ N,
          (Finset.sum (Finset.range N) (fun k ↦ f ^ k • a k f)) ≡ b f
            [SMOD (((Ideal.span ({f} : Set R)) ^ N) • (⊤ : Submodule R M))] := by
      intro f hf N
      -- Each fixed generator contributes its own principal-adic limit.
      simp [b, hf]
      exact hb₀ f hf N
    let L : M := x 0 + Finset.sum s b
    refine ⟨L, fun N ↦ ?_⟩
    have hNr : N ≤ N * r := by
      have hrone : 1 ≤ r := Nat.succ_le_of_lt (Finset.card_pos.mpr hs)
      simpa [Nat.mul_one] using Nat.mul_le_mul_left N hrone
    have hcompat :
        x N ≡ x (N * r) [SMOD (I ^ N • (⊤ : Submodule R M))] :=
      hx (m := N) (n := N * r) hNr
    have hcofinal :
        x (N * r) ≡ L [SMOD (J N • (⊤ : Submodule R M))] := by
      -- Telescope the cofinal system and replace each generatorwise partial sum by its limit.
      simpa [L, r] using cofinal_subsequence_limit_smodEq (M := M) s x a b
        (fun n ↦ (hstep_sum n).symm) hb N
    have hdescend :
        J N • (⊤ : Submodule R M) ≤ I ^ N • (⊤ : Submodule R M) := by
      -- The generator-power filtration sits inside the original `I`-adic filtration.
      exact Submodule.smul_mono_left (generator_pow_span_le_pow s hI N)
    exact hcompat.trans (SModEq.mono hdescend hcofinal)
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hIbot : I = ⊥ := by
      simpa [hs_empty] using hI.symm
    -- With no generators, the ideal is zero and the `⊥`-adic topology is automatically precomplete.
    simpa [hIbot] using (inferInstance : IsPrecomplete (⊥ : Ideal R) M)

/-- Lemma 10.96.7: if an ideal `I` is generated by a finite set `s` and the canonical map
`M → AdicCompletion (Ideal.span ({f} : Set R)) M` is surjective for every generator `f ∈ s`, then
the canonical map `M → AdicCompletion I M` is surjective. -/
theorem surjective_adicCompletion_of_span_eq_of_generatorwise_surjective
    {I : Ideal R} (s : Finset R) (hI : Ideal.span (↑s : Set R) = I)
    (hsurj : ∀ f ∈ s,
      Function.Surjective (AdicCompletion.of (Ideal.span ({f} : Set R)) M)) :
    Function.Surjective (AdicCompletion.of I M) := by
  rw [AdicCompletion.of_surjective_iff]
  apply isPrecomplete_of_span_eq_of_generatorwise s hI
  intro f hf
  rw [← AdicCompletion.of_surjective_iff]
  exact hsurj f hf

end

/-! ### Lemma_10_96_8 (from Chap10) -/
universe u v

section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem isPrecomplete_span_singleton_of_mem
    {J : Ideal R} {f : R} (hfj : f ∈ J) (hM : IsAdicComplete J M) :
    IsPrecomplete (Ideal.span ({f} : Set R)) M := by
  classical
  let I : Ideal R := Ideal.span ({f} : Set R)
  let _ : IsAdicComplete J M := hM
  have smul_top_mono {A B : Ideal R} (hAB : A ≤ B) :
      A • (⊤ : Submodule R M) ≤ B • (⊤ : Submodule R M) := by
    intro y hy
    exact Submodule.smul_induction_on hy
      (fun r hr m hm ↦ Submodule.smul_mem_smul (hAB hr) hm)
      (fun x y hx hy ↦ by simpa using Submodule.add_mem _ hx hy)
  refine ⟨fun x hx ↦ ?_⟩
  have hstep : ∀ n, x n ≡ x (n + 1) [SMOD (I ^ n • (⊤ : Submodule R M))] := fun n ↦
    hx (Nat.le_succ n)
  have hexpansion : ∀ n, ∃ a : M, x (n + 1) - x n = f ^ n • a := by
    intro n
    have hxmem : x (n + 1) - x n ∈ I ^ n • (⊤ : Submodule R M) := by
      have hxmem' : x n - x (n + 1) ∈ I ^ n • (⊤ : Submodule R M) :=
        SModEq.sub_mem.mp (hstep n)
      simpa using Submodule.neg_mem _ hxmem'
    rw [show I ^ n = Ideal.span ({f ^ n} : Set R) by
      rw [show I = Ideal.span ({f} : Set R) by rfl, Ideal.span_singleton_pow]] at hxmem
    refine Submodule.smul_induction_on hxmem
      (fun r hr m _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · rcases Ideal.mem_span_singleton.mp hr with ⟨s, hs⟩
      refine ⟨s • m, ?_⟩
      calc
        r • m = (f ^ n * s) • m := by rw [hs]
        _ = f ^ n • (s • m) := by rw [smul_smul]
    · rcases hy with ⟨y', hy'⟩
      rcases hz with ⟨z', hz'⟩
      exact ⟨y' + z', by rw [smul_add, hy', hz']⟩
  choose a ha using hexpansion
  let tails : ℕ → ℕ → M := fun n ↦ fun m ↦
    Finset.sum (Finset.range m) (fun k ↦ f ^ k • a (n + k))
  have htails_cauchy : ∀ n : ℕ,
      ∀ m, tails n m ≡ tails n (m + 1) [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n m
    rw [SModEq.sub_mem]
    have hm : f ^ m • a (n + m) ∈ J ^ m • (⊤ : Submodule R M) := by
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      simpa using Ideal.pow_mem_pow hfj m
    have htaildiff : tails n m + -tails n (m + 1) = -(f ^ m • a (n + m)) := by
      simp [tails, Finset.sum_range_succ, add_comm, add_left_comm]
    rw [sub_eq_add_neg, htaildiff]
    exact Submodule.neg_mem _ hm
  have htails_full : ∀ n : ℕ, ∀ {m k}, m ≤ k →
      tails n m ≡ tails n k [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n m k hmk
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
        have hsub : J ^ k • (⊤ : Submodule R M) ≤ J ^ m • (⊤ : Submodule R M) :=
          smul_top_mono (Ideal.pow_le_pow_right hmk)
        exact ih.trans <|
          SModEq.mono hsub (htails_cauchy n k)
  have htails_limit : ∀ n : ℕ, ∃ b : M, ∀ m, tails n m ≡ b [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n
    exact hM.toIsPrecomplete.prec (htails_full n)
  choose b hb using htails_limit
  have hshift : ∀ n m, tails n (m + 1) = a n + f • tails (n + 1) m := by
    intro n m
    induction m with
    | zero =>
        simp [tails]
    | succ m ih =>
        simp [tails, Finset.sum_range_succ, ih, pow_succ, smul_add, smul_smul, mul_comm,
          add_comm, add_left_comm]
  have hb_rec : ∀ n, b n = a n + f • b (n + 1) := by
    intro n
    rw [← sub_eq_zero]
    apply hM.toIsHausdorff.haus
    intro m
    have hsub : J ^ (m + 1) • (⊤ : Submodule R M) ≤ J ^ m • (⊤ : Submodule R M) :=
      smul_top_mono (Ideal.pow_le_pow_right (Nat.le_succ m))
    have hleft : tails n (m + 1) ≡ b n [SMOD (J ^ m • (⊤ : Submodule R M))] := by
      exact SModEq.mono hsub (hb n (m + 1))
    have hright : tails n (m + 1) ≡ a n + f • b (n + 1) [SMOD (J ^ m • (⊤ : Submodule R M))] := by
      rw [hshift n m]
      exact SModEq.add SModEq.rfl (SModEq.smul (hb (n + 1) m) f)
    exact (sub_smodEq_zero).2 (hleft.symm.trans hright)
  let L := x 0 + b 0
  refine ⟨L, fun n ↦ ?_⟩
  have hL : ∀ n, L = x n + f ^ n • b n := by
    intro n
    induction n with
    | zero =>
        simp [L]
    | succ n ihn =>
        rw [ihn, hb_rec n, pow_succ, smul_add, smul_smul]
        have hxsucc : x n + f ^ n • a n = x (n + 1) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (sub_eq_iff_eq_add.1 (ha n)).symm
        simpa [add_assoc] using congrArg (fun t ↦ t + (f ^ n * f) • b (n + 1)) hxsucc
  rw [SModEq.sub_mem]
  rw [hL n]
  have hbmem : f ^ n • b n ∈ I ^ n • (⊤ : Submodule R M) := by
    rw [show I ^ n = Ideal.span ({f ^ n} : Set R) by
      rw [show I = Ideal.span ({f} : Set R) by rfl, Ideal.span_singleton_pow]]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  simpa [L, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Submodule.neg_mem _ hbmem

-- Proof sketch: use `IsAdicComplete J M` to get Hausdorffness for the weaker `I`-adic filtration
-- via `I ≤ J`. For precompleteness, first reduce from a finitely generated ideal to the principal
-- generator case using Lemma 10.96.7, then show a compatible `I`-adic Cauchy sequence is also
-- `J`-adically Cauchy and use `J`-adic completeness to produce the limit.
/-- Lemma 10.96.8: if `I ≤ J`, the ideal `I` is finitely generated, and `M` is `J`-adically
complete, then `M` is `I`-adically complete. -/
theorem isAdicComplete_of_le_of_fg
    {I J : Ideal R} (hIJ : I ≤ J) (hI : I.FG) (hM : IsAdicComplete J M) :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · let _ : IsHausdorff J M := hM.toIsHausdorff
    have hIJ' : Ideal.map (algebraMap R R) I ≤ J := by
      simpa using hIJ
    exact IsHausdorff.of_map hIJ'
  · rcases hI with ⟨s, hs⟩
    apply isPrecomplete_of_span_eq_of_generatorwise s hs
    intro f hf
    exact isPrecomplete_span_singleton_of_mem
      (show f ∈ J from hIJ <| hs ▸ Ideal.subset_span hf) hM

end

/-! ### Lemma_10_96_9 (from Chap10) -/
universe u v

section

open AdicCompletion

variable (R : Type u) [CommRing R]
variable (I J : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.96.9: a power containment `A ^ k ≤ B` propagates to the cofinal subsequence
`A ^ (k * n) ≤ B ^ n`. -/
private theorem ideal_pow_mul_le_pow_of_pow_le
    {A B : Ideal R} {k : ℕ} (hAB : A ^ k ≤ B) (n : ℕ) :
    A ^ (k * n) ≤ B ^ n := by
  -- Rewrite the left-hand side as `(A ^ k) ^ n`, then apply monotonicity of powers.
  rw [pow_mul]
  exact Ideal.pow_right_mono hAB n

/-- Helper for Lemma 10.96.9: the induced containment on powers gives a containment on the
corresponding submodules `I ^ (k * n) M ⊆ J ^ n M`. -/
private theorem pow_smul_top_le_pow_smul_top_of_pow_le
    {A B : Ideal R} {k n : ℕ} (hAB : A ^ k ≤ B) :
    (A ^ (k * n) • (⊤ : Submodule R M)) ≤ B ^ n • (⊤ : Submodule R M) :=
  Submodule.smul_mono_left (ideal_pow_mul_le_pow_of_pow_le
    (R := R) (A := A) (B := B) (k := k) hAB n)

/-- Helper for Lemma 10.96.9: the quotient map from the `I ^ (c * n)`-quotient to the
`J ^ n`-quotient induced by the containment `I ^ (c * n) M ⊆ J ^ n M`. -/
private noncomputable abbrev adicCompletionRightQuotientMap
    (c : ℕ) (hIJ : I ^ c ≤ J) (n : ℕ) :
    M ⧸ (I ^ (c * n) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (J ^ n • ⊤ : Submodule R M) :=
  Submodule.factor (pow_smul_top_le_pow_smul_top_of_pow_le
    (R := R) (M := M) (A := I) (B := J) (k := c) (n := n) hIJ)

/-- Helper for Lemma 10.96.9: the quotient maps along the cofinal subsequence `n ↦ c * n`
commute with the transition maps. -/
private theorem adicCompletionRightQuotientMap_compatible
    (c : ℕ) (hIJ : I ^ c ≤ J) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap J M hmn ∘ₗ
        adicCompletionRightQuotientMap R I J M c hIJ n =
      adicCompletionRightQuotientMap R I J M c hIJ m ∘ₗ
        AdicCompletion.transitionMap I M (Nat.mul_le_mul_left c hmn) := by
  -- Both composites are the quotient map from the `I ^ (c * n)`-quotient to the `J ^ m`-quotient.
  ext x
  simp [adicCompletionRightQuotientMap, AdicCompletion.transitionMap, Submodule.factorPow]

/-- Helper for Lemma 10.96.9: the `n`th coordinate of the right comparison map is obtained from
the `(c * n)`th `I`-adic coordinate by quotienting further to `M / J ^ n M`. -/
private noncomputable abbrev adicCompletionRightFamily
    (c : ℕ) (hIJ : I ^ c ≤ J) (n : ℕ) :
    AdicCompletion I M →ₗ[R] M ⧸ (J ^ n • ⊤ : Submodule R M) :=
  adicCompletionRightQuotientMap R I J M c hIJ n ∘ₗ AdicCompletion.eval I M (c * n)

/-- Helper for Lemma 10.96.9: the quotient maps defining the right comparison map form a
compatible inverse-system morphism. -/
private theorem adicCompletionRightFamily_compatible
    (c : ℕ) (hIJ : I ^ c ≤ J) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap J M hmn ∘ₗ
        adicCompletionRightFamily R I J M c hIJ n =
      adicCompletionRightFamily R I J M c hIJ m := by
  apply LinearMap.ext
  intro x
  -- Push the `J`-transition past the quotient map, then use compatibility of `I`-adic coordinates.
  calc
    AdicCompletion.transitionMap J M hmn (adicCompletionRightFamily R I J M c hIJ n x) =
        adicCompletionRightQuotientMap R I J M c hIJ m
          (AdicCompletion.transitionMap I M (Nat.mul_le_mul_left c hmn)
            (AdicCompletion.eval I M (c * n) x)) := by
          exact congrArg
            (fun f :
              M ⧸ (I ^ (c * n) • ⊤ : Submodule R M) →ₗ[R]
                M ⧸ (J ^ m • ⊤ : Submodule R M) ↦
              f (AdicCompletion.eval I M (c * n) x))
            (adicCompletionRightQuotientMap_compatible (R := R) (I := I) (J := J) (M := M)
              (c := c) (hIJ := hIJ) hmn)
    _ = adicCompletionRightQuotientMap R I J M c hIJ m
          (AdicCompletion.eval I M (c * m) x) := by
          exact congrArg (adicCompletionRightQuotientMap R I J M c hIJ m)
            (AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := M)
              (m := c * m) (n := c * n) (hmn := Nat.mul_le_mul_left c hmn) x)
    _ = adicCompletionRightFamily R I J M c hIJ m x := rfl

/-- Helper for Lemma 10.96.9: the quotient map from the `J ^ (d * n)`-quotient to the
`I ^ n`-quotient induced by the containment `J ^ (d * n) M ⊆ I ^ n M`. -/
private noncomputable abbrev adicCompletionLeftQuotientMap
    (d : ℕ) (hJI : J ^ d ≤ I) (n : ℕ) :
    M ⧸ (J ^ (d * n) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  Submodule.factor (pow_smul_top_le_pow_smul_top_of_pow_le
    (R := R) (M := M) (A := J) (B := I) (k := d) (n := n) hJI)

/-- Helper for Lemma 10.96.9: the quotient maps along the cofinal subsequence `n ↦ d * n`
commute with the transition maps. -/
private theorem adicCompletionLeftQuotientMap_compatible
    (d : ℕ) (hJI : J ^ d ≤ I) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        adicCompletionLeftQuotientMap R I J M d hJI n =
      adicCompletionLeftQuotientMap R I J M d hJI m ∘ₗ
        AdicCompletion.transitionMap J M (Nat.mul_le_mul_left d hmn) := by
  -- Both composites are the quotient map from the `J ^ (d * n)`-quotient to the `I ^ m`-quotient.
  ext x
  simp [adicCompletionLeftQuotientMap, AdicCompletion.transitionMap, Submodule.factorPow]

/-- Helper for Lemma 10.96.9: the `n`th coordinate of the left comparison map is obtained from
the `(d * n)`th `J`-adic coordinate by quotienting further to `M / I ^ n M`. -/
private noncomputable abbrev adicCompletionLeftFamily
    (d : ℕ) (hJI : J ^ d ≤ I) (n : ℕ) :
    AdicCompletion J M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  adicCompletionLeftQuotientMap R I J M d hJI n ∘ₗ AdicCompletion.eval J M (d * n)

/-- Helper for Lemma 10.96.9: the quotient maps defining the left comparison map form a
compatible inverse-system morphism. -/
private theorem adicCompletionLeftFamily_compatible
    (d : ℕ) (hJI : J ^ d ≤ I) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        adicCompletionLeftFamily R I J M d hJI n =
      adicCompletionLeftFamily R I J M d hJI m := by
  apply LinearMap.ext
  intro x
  -- Push the `I`-transition past the quotient map, then use compatibility of `J`-adic coordinates.
  calc
    AdicCompletion.transitionMap I M hmn (adicCompletionLeftFamily R I J M d hJI n x) =
        adicCompletionLeftQuotientMap R I J M d hJI m
          (AdicCompletion.transitionMap J M (Nat.mul_le_mul_left d hmn)
            (AdicCompletion.eval J M (d * n) x)) := by
          exact congrArg
            (fun f :
              M ⧸ (J ^ (d * n) • ⊤ : Submodule R M) →ₗ[R]
                M ⧸ (I ^ m • ⊤ : Submodule R M) ↦
              f (AdicCompletion.eval J M (d * n) x))
            (adicCompletionLeftQuotientMap_compatible (R := R) (I := I) (J := J) (M := M)
              (d := d) (hJI := hJI) hmn)
    _ = adicCompletionLeftQuotientMap R I J M d hJI m
          (AdicCompletion.eval J M (d * m) x) := by
          exact congrArg (adicCompletionLeftQuotientMap R I J M d hJI m)
            (AdicCompletion.transitionMap_comp_eval_apply (I := J) (M := M)
              (m := d * m) (n := d * n) (hmn := Nat.mul_le_mul_left d hmn) x)
    _ = adicCompletionLeftFamily R I J M d hJI m x := rfl

/-- Helper for Lemma 10.96.9: positivity of `a` and `b` makes the subsequence
`n ↦ a * (b * n)` dominate the identity sequence. -/
private theorem nat_le_mul_mul_of_pos
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    n ≤ a * (b * n) := by
  -- First multiply by `b`, then multiply by `a`.
  have hbn : n ≤ b * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
  have han : b * n ≤ a * (b * n) := by
    simpa [one_mul] using Nat.mul_le_mul_right (b * n) (Nat.succ_le_of_lt ha)
  exact hbn.trans han

/-- Helper for Lemma 10.96.9: the direct right comparison map between the two completions. -/
private noncomputable def adicCompletionToRightOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M →ₗ[R] AdicCompletion J M
  | c, _, _, _, hIJ, _ =>
      AdicCompletion.lift J
        (adicCompletionRightFamily R I J M c hIJ)
        (adicCompletionRightFamily_compatible (R := R) (I := I) (J := J) (M := M) (c := c)
          (hIJ := hIJ))

/-- Helper for Lemma 10.96.9: the direct left comparison map between the two completions. -/
private noncomputable def adicCompletionToLeftOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion J M →ₗ[R] AdicCompletion I M
  | _, d, _, _, _, hJI =>
      AdicCompletion.lift I
        (adicCompletionLeftFamily R I J M d hJI)
        (adicCompletionLeftFamily_compatible (R := R) (I := I) (J := J) (M := M) (d := d)
          (hJI := hJI))

/-- Helper for Lemma 10.96.9: the right comparison map sends the canonical class of `x`
to the canonical class of `x`. -/
@[simp]
private theorem adicCompletionToRightOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  -- Check equality on every quotient coordinate of the inverse limit.
  apply AdicCompletion.ext
  intro n
  simp [adicCompletionToRightOfPowLe, adicCompletionRightFamily, adicCompletionRightQuotientMap]

/-- Helper for Lemma 10.96.9: the left comparison map sends the canonical class of `x`
to the canonical class of `x`. -/
@[simp]
private theorem adicCompletionToLeftOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI (of J M x) = of I M x := by
  -- Check equality on every quotient coordinate of the inverse limit.
  apply AdicCompletion.ext
  intro n
  simp [adicCompletionToLeftOfPowLe, adicCompletionLeftFamily, adicCompletionLeftQuotientMap]

/-- Helper for Lemma 10.96.9: applying the left comparison map after the right one recovers the
original `I`-adic completion element. -/
private theorem adicCompletion_left_right_eq_id
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI).comp
        (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  -- Evaluate the composite at the `n`th quotient level and descend from level `c * (d * n)`.
  have hle : n ≤ c * (d * n) := nat_le_mul_mul_of_pos c d n hc hd
  simpa [adicCompletionToLeftOfPowLe, adicCompletionToRightOfPowLe, adicCompletionLeftFamily,
    adicCompletionRightFamily, adicCompletionLeftQuotientMap, adicCompletionRightQuotientMap,
    AdicCompletion.transitionMap, Submodule.factorPow, Nat.mul_assoc] using x.property hle

/-- Helper for Lemma 10.96.9: applying the right comparison map after the left one recovers the
original `J`-adic completion element. -/
private theorem adicCompletion_right_left_eq_id
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI).comp
        (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  -- Evaluate the composite at the `n`th quotient level and descend from level `d * (c * n)`.
  have hle : n ≤ d * (c * n) := nat_le_mul_mul_of_pos d c n hd hc
  simpa [adicCompletionToLeftOfPowLe, adicCompletionToRightOfPowLe, adicCompletionLeftFamily,
    adicCompletionRightFamily, adicCompletionLeftQuotientMap, adicCompletionRightQuotientMap,
    AdicCompletion.transitionMap, Submodule.factorPow, Nat.mul_assoc, Nat.mul_left_comm] using
    x.property hle

-- Proof sketch: the power containments `I ^ c ≤ J` and `J ^ d ≤ I` make the `I`-adic and
-- `J`-adic filtrations cofinal. The direct quotient maps on the cofinal subsequences therefore
-- induce mutually inverse morphisms between the two inverse-limit completions.
/-- Lemma 10.96.9: if positive powers of `I` and `J` contain one another, then the `I`-adic and
`J`-adic completions of any `R`-module are canonically identified. -/
noncomputable def adicCompletionLinearEquivOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M ≃ₗ[R] AdicCompletion J M
  | c, d, hc, hd, hIJ, hJI =>
      LinearEquiv.ofLinear
        (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI)
        (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI)
        (adicCompletion_right_left_eq_id (R := R) (I := I) (J := J) (M := M)
          c d hc hd hIJ hJI)
        (adicCompletion_left_right_eq_id (R := R) (I := I) (J := J) (M := M)
          c d hc hd hIJ hJI)

@[simp]
theorem adicCompletionLinearEquivOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  exact adicCompletionToRightOfPowLe_of R I J M c d hc hd hIJ hJI x

-- Proof sketch: transport bijectivity of the canonical map `M → AdicCompletion I M` across the
-- comparison equivalence, using that the equivalence intertwines the two `of` maps.
/-- Under mutual positive-power containments between `I` and `J`, an `R`-module is `I`-adically
complete if and only if it is `J`-adically complete. -/
theorem isAdicComplete_iff_of_pow_le :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      IsAdicComplete I M ↔ IsAdicComplete J M
  | c, d, hc, hd, hIJ, hJI => by
      constructor
      · intro hI
        -- Compose `of I` with the comparison equivalence to recover `of J`.
        rw [← AdicCompletion.of_bijective_iff]
        let e := adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI
        have hcomp :
            of J M = (e : AdicCompletion I M →ₗ[R] AdicCompletion J M).comp (of I M) := by
          apply LinearMap.ext
          intro x
          exact adicCompletionLinearEquivOfPowLe_of R I J M c d hc hd hIJ hJI x
        rw [hcomp]
        exact e.bijective.comp ((AdicCompletion.of_bijective_iff).mpr hI)
      · intro hJ
        -- Apply the same transport argument to the inverse equivalence.
        rw [← AdicCompletion.of_bijective_iff]
        let e := adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI
        have hcomp :
            of I M = ((e.symm : AdicCompletion J M →ₗ[R] AdicCompletion I M)).comp (of J M) := by
          apply LinearMap.ext
          intro x
          exact adicCompletionToLeftOfPowLe_of R I J M c d hc hd hIJ hJI x
        rw [hcomp]
        exact e.symm.bijective.comp ((AdicCompletion.of_bijective_iff).mpr hJ)

end

/-! ### Lemma_10_96_10 (from Chap10) -/
universe u v

section

open AdicCompletion Submodule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (K : Submodule R M)
variable [IsPrecomplete I M]

-- Domain-style sampling:
-- * primary domain: adic completion / `I`-adic precompleteness and completeness of modules and
--   quotients.
-- * source-facing layer: the quotient criterion for `IsAdicComplete I (M ⧸ K)`.
-- * core/canonical owners: `IsPrecomplete I _` for surjectivity of the completion map, and
--   `IsAdicComplete I _` for the target quotient-completeness statement.
-- * sampled upstream declarations:
--   `IsPrecomplete`,
--   `IsAdicComplete`,
--   `AdicCompletion.of_surjective_iff`,
--   `isHausdorff_iff`,
--   `IsHausdorff.iInf_pow_smul`,
--   `Submodule.comap_map_mkQ`.
-- * primitive data: the quotient map `Submodule.mkQ K`.
-- * derived API: precompleteness of `M ⧸ K`, Hausdorffness of `M ⧸ K`, and the intersection
--   criterion transported through the quotient-submodule correspondence.
-- Proof sketch: apply Lemma `10.96.1` to the quotient map `M → M ⧸ K`. Since `M` is already
-- `I`-adically precomplete, surjectivity of the induced map `M^∧ → (M ⧸ K)^∧` is equivalent to
-- surjectivity of the completion map `(M ⧸ K) → (M ⧸ K)^∧`. The kernel of that completion map is
-- exactly `(⨅ n, K ⊔ I ^ n • ⊤) / K`, so bijectivity is equivalent to
-- `K = ⨅ n, K ⊔ I ^ n • (⊤ : Submodule R M)`.
/-- Lemma 10.96.10: if `M` is `I`-adically precomplete, then a submodule `K` is the intersection
of the submodules `K + I ^ n M` if and only if the quotient module `M ⧸ K` is `I`-adically
complete. -/
theorem submodule_eq_iInf_sup_pow_smul_top_iff_isAdicComplete_quotient :
    K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) ↔ IsAdicComplete I (M ⧸ K) := by
  have hquot_precomplete : IsPrecomplete I (M ⧸ K) := by
    rw [← AdicCompletion.of_surjective_iff]
    intro y
    obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I (Submodule.mkQ_surjective K) y
    obtain ⟨m, rfl⟩ := AdicCompletion.of_surjective I M x
    exact ⟨Submodule.mkQ K m, by rw [AdicCompletion.map_of]⟩
  have hcomap_pow (n : ℕ) :
      Submodule.comap (Submodule.mkQ K) (I ^ n • (⊤ : Submodule R (M ⧸ K))) =
        K ⊔ I ^ n • (⊤ : Submodule R M) := by
    have hmap : Submodule.map (Submodule.mkQ K) (I ^ n • (⊤ : Submodule R M)) =
        I ^ n • (⊤ : Submodule R (M ⧸ K)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap, Submodule.comap_map_mkQ]
  constructor
  · intro hK
    rw [isAdicComplete_iff]
    refine ⟨?_, hquot_precomplete⟩
    rw [isHausdorff_iff]
    rintro ⟨m⟩ hm
    have hm_mem : ∀ n : ℕ, Submodule.mkQ K m ∈ I ^ n • (⊤ : Submodule R (M ⧸ K)) :=
      fun n ↦ SModEq.zero.1 (hm n)
    have hm' : m ∈ ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [← hcomap_pow n, Submodule.mem_comap]
      exact hm_mem n
    have hmK : m ∈ K := by
      rw [hK]
      exact hm'
    change (Submodule.Quotient.mk m : M ⧸ K) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmK
  · intro hquot
    have hhaus : IsHausdorff I (M ⧸ K) := hquot.toIsHausdorff
    have hbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (M ⧸ K))) = ⊥ :=
      IsHausdorff.iInf_pow_smul hhaus
    have hcomap := congrArg (Submodule.comap (Submodule.mkQ K)) hbot
    rw [Submodule.comap_iInf] at hcomap
    simp only [Submodule.comap_bot, Submodule.ker_mkQ] at hcomap
    simpa [hcomap_pow] using hcomap.symm

end

/-! ### Lemma_10_96_11 (from Chap10) -/
universe u v

section

open AdicCompletion

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: since `R` is `I`-adically complete, the canonical map `R → AdicCompletion I R`
-- is bijective. For finite `M`, Lemma `10.96.1` makes the tensor-comparison map
-- `M ⊗[R] AdicCompletion I R → AdicCompletion I M` surjective, and transporting along the
-- completion isomorphism of `R` yields surjectivity of `AdicCompletion.of I M`. The hypothesis
-- `⋂ n, I^n M = 0` gives injectivity of `AdicCompletion.of I M`, so
-- `AdicCompletion.of_bijective_iff` implies that `M` is `I`-adically complete.
/-- Lemma 10.96.11: if `R` is `I`-adically complete, `M` is a finite `R`-module, and
`⋂ n, I^n M = 0`, then `M` is `I`-adically complete. -/
theorem isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot
    [IsAdicComplete I R] [Module.Finite R M]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsAdicComplete I M := by
  let e : M ≃ₗ[R] TensorProduct R (AdicCompletion I R) M :=
    (TensorProduct.lid R M).symm.trans
      (TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M))
  have hof_one : (AdicCompletion.of I R) 1 = 1 := by
    ext n
    simp [AdicCompletion.of_apply]
  have hsurj : Function.Surjective (AdicCompletion.of I M) := by
    intro y
    obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
    obtain ⟨z, rfl⟩ := e.surjective x
    refine ⟨z, ?_⟩
    simp [e, hof_one]
  have hhaus : IsHausdorff I M := by
    refine ⟨fun x hx ↦ ?_⟩
    have hx' : x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) := by
      simpa [SModEq.zero] using hx
    simpa [hM] using hx'
  exact (AdicCompletion.of_bijective_iff).mp
    ⟨(AdicCompletion.of_injective_iff).mpr hhaus, hsurj⟩

end

/-! ### Lemma_10_96_12 (from Chap10) -/
universe u v

section

open AdicCompletion Submodule

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [IsAdicComplete I R]
variable [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]

-- Domain-style sampling:
-- * source-facing layer: the Stacks criterion that finite generation of `M / IM` plus
--   `⋂ n, I ^ n M = 0` over an `I`-adically complete ring forces `M` itself to be finite.
-- * core/canonical owner: `IsHausdorff I M` for the separatedness hypothesis.
-- * sampled upstream declarations:
--   `IsAdicComplete`,
--   `IsHausdorff`,
--   `IsHausdorff.iInf_pow_smul`,
--   `isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot`.
-- * primitive data: the ring-completeness hypothesis and the finite quotient module
--   `M ⧸ I • ⊤`.
-- * derived API: the equality `⨅ n, I ^ n • ⊤ = ⊥` is the source-facing formulation of the
--   canonical separatedness owner `IsHausdorff I M`.

-- Proof sketch: choose finitely many lifts in `M` of generators of `M / IM`, and let `M'` be the
-- submodule they generate. Lemma `10.96.1` gives a surjection `(M')^∧ → M^∧`, while
-- Lemma `10.96.11` makes `M'` complete because it is finite and inherits
-- `⋂ n, I^n M' = 0`. Thus `M' → M^∧` is surjective. Since the kernel of `M → M^∧` is
-- `⋂ n, I^n M = 0`, the inclusion `M' → M` is surjective, so `M` is finitely generated.
omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: the intersection condition `⋂ n, I ^ n M = 0` is exactly the
Hausdorffness condition needed by the completion API. -/
lemma isHausdorff_of_iInf_pow_smul_eq_bot
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsHausdorff I M := by
  -- Repackage the source-facing intersection hypothesis into the owner-facing Hausdorff API.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) := by
    simpa [SModEq.zero] using hx
  simpa [hM] using hx'

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: a submodule of a Hausdorff module is Hausdorff for the induced
`I`-adic topology. -/
lemma isHausdorff_submodule [IsHausdorff I M] (N : Submodule R M) :
    IsHausdorff I N := by
  -- View a compatible system in `N` inside `M`, where Hausdorffness is already available.
  have hhausM : IsHausdorff I M := inferInstance
  refine ⟨fun x hx ↦ ?_⟩
  apply Subtype.ext
  apply hhausM.haus x.1
  intro n
  rw [SModEq.zero]
  have hx_mem : x ∈ I ^ n • (⊤ : Submodule R N) := by
    simpa [SModEq.zero] using hx n
  have hx_map : x.1 ∈ Submodule.map N.subtype (I ^ n • (⊤ : Submodule R N)) := by
    exact ⟨x, hx_mem, rfl⟩
  have hx_in_submodule : x.1 ∈ I ^ n • N := by
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] using hx_map
  exact (smul_mono le_rfl (show N ≤ (⊤ : Submodule R M) from le_top)) hx_in_submodule

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: if a finite family of lifts maps to generators of `M / IM`, then
the span of those lifts maps onto all of `M / IM`. -/
lemma map_mkQ_span_eq_top_of_lifts {n : ℕ} {x : Fin n → M}
    {xbar : Fin n → M ⧸ I • (⊤ : Submodule R M)}
    (hx : ∀ i, Submodule.mkQ (I • (⊤ : Submodule R M)) (x i) = xbar i)
    (hspan : Submodule.span R (Set.range xbar) = ⊤) :
    Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M)))
      (Submodule.span R (Set.range x)) = ⊤ := by
  -- Push the span through the quotient map and identify the image set with the chosen generators.
  have himage :
      (Submodule.mkQ (I • (⊤ : Submodule R M))) '' Set.range x = Set.range xbar := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hx i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hx i⟩
  rw [Submodule.map_span, himage, hspan]

omit [IsAdicComplete I R] [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] in
/-- Helper for Lemma 10.96.12: if the quotient map sends a submodule onto all of `M / IM`, then
the composite of the subtype map with the quotient map is surjective. -/
lemma surjective_mkQ_comp_subtype_of_map_eq_top {N : Submodule R M}
    (hN : Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M))) N = ⊤) :
    Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ₗ N.subtype) := by
  -- Translate the submodule-image equality into the usual `range = ⊤` criterion for surjectivity.
  rw [← LinearMap.range_eq_top]
  simpa [LinearMap.range_comp, Submodule.range_subtype] using hN

/-- Lemma 10.96.12: if `R` is `I`-adically complete, `⋂ n, I ^ n M = 0`, and the quotient
`M / IM` is a finite `R / I`-module, then `M` is a finite `R`-module. -/
theorem moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    Module.Finite R M := by
  -- First convert the source hypothesis to the canonical separatedness API for `M`.
  letI : IsHausdorff I M := isHausdorff_of_iInf_pow_smul_eq_bot (I := I) hM
  let Q : Type v := M ⧸ I • (⊤ : Submodule R M)
  -- Restrict scalars along `R → R / I` so the finite quotient has an `R`-generating family.
  have hfgQ : (⊤ : Submodule R Q).FG := by
    have hfgQ' : (⊤ : Submodule (R ⧸ I) Q).FG :=
      Module.Finite.fg_top (R := R ⧸ I) (M := Q)
    simpa [Q] using
      (Submodule.FG.restrictScalars_of_surjective
        (R := R) (A := R ⧸ I) (M := Q) (S := (⊤ : Submodule (R ⧸ I) Q))
        hfgQ' Ideal.Quotient.mk_surjective)
  -- Choose finitely many quotient generators and lift them back to `M`.
  obtain ⟨n, xbar, hspanbar⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfgQ
  choose x hx using fun i : Fin n ↦
    Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (xbar i)
  let N : Submodule R M := Submodule.span R (Set.range x)
  have hfiniteN : Module.Finite R N := by
    -- The lift-span is finite because it is generated by finitely many elements.
    simpa [N] using Module.Finite.span_of_finite R (Set.finite_range x)
  have hmapN :
      Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R M))) N = ⊤ := by
    -- The chosen lifts still generate after quotienting by `I`.
    simpa [N] using map_mkQ_span_eq_top_of_lifts (I := I) hx hspanbar
  have hsurjQ :
      Function.Surjective (Submodule.mkQ (I • (⊤ : Submodule R M)) ∘ₗ N.subtype) :=
    surjective_mkQ_comp_subtype_of_map_eq_top (I := I) hmapN
  have hhausN : IsHausdorff I N := isHausdorff_submodule (I := I) N
  have hNbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R N) : Submodule R N) = ⊥ :=
    IsHausdorff.iInf_pow_smul hhausN
  letI : Module.Finite R N := hfiniteN
  have hcompleteN : IsAdicComplete I N := by
    -- Lemma `10.96.11` makes the finite Hausdorff span complete.
    exact isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot (I := I) (M := N) hNbot
  letI : IsAdicComplete I N := hcompleteN
  have hsurjN : Function.Surjective N.subtype := by
    -- Lemma `10.96.1` upgrades surjectivity modulo `I` to surjectivity of the inclusion itself.
    exact surjective_of_mkQ_comp_surjective (I := I) (f := N.subtype) hsurjQ
  -- A finite submodule surjecting onto `M` exhibits `M` as finite.
  exact Module.Finite.of_surjective N.subtype hsurjN

/-- Canonical owner-facing form of Lemma `10.96.12`, using `IsHausdorff I M` for the separatedness
hypothesis instead of the explicit intersection formula. -/
theorem moduleFinite_of_finite_quotient_of_isHausdorff [IsHausdorff I M] :
    Module.Finite R M := by
  have hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥ :=
    IsHausdorff.iInf_pow_smul inferInstance
  simpa using moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot hM

end
