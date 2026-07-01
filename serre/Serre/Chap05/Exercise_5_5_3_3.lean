import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (n : ℕ) [NeZero n]

private def halfTurn : ZMod n := (n / 2 : ℕ)

omit [NeZero n] in
private lemma halfTurn_add_self (heven : Even n) : halfTurn n + halfTurn n = (0 : ZMod n) := by
  calc
    halfTurn n + halfTurn n = ((2 * (n / 2) : ℕ) : ZMod n) := by
      simp [halfTurn, two_mul, Nat.cast_add]
    _ = (n : ZMod n) := by rw [Nat.two_mul_div_two_of_even heven]
    _ = 0 := ZMod.natCast_self n

private lemma halfTurn_ne_zero (heven : Even n) : halfTurn n ≠ (0 : ZMod n) := by
  intro hzero
  have hcast : ((n / 2 : ℕ) : ZMod n) = 0 := by
    simpa [halfTurn] using hzero
  have hdiv : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp hcast
  have hhalfpos : 0 < n / 2 := by
    have hn : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
    have hpos : 0 < n := Nat.pos_of_neZero n
    omega
  have hle : n ≤ n / 2 := Nat.le_of_dvd hhalfpos hdiv
  omega

private lemma eq_zero_or_eq_halfTurn (a : ZMod n) (ha : a + a = 0) :
    a = 0 ∨ a = halfTurn n := by
  rcases (ZMod.neg_eq_self_iff a).mp (neg_eq_iff_add_eq_zero.mpr ha) with rfl | hval
  · exact Or.inl rfl
  · right
    rw [← a.natCast_zmod_val]
    have hdiv : a.val = n / 2 := Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) (by omega)
    simp [halfTurn, hdiv]

omit [NeZero n] in
private lemma commute_r_sr_iff (i j : ZMod n) :
    Commute (DihedralGroup.r i) (DihedralGroup.sr j) ↔ i + i = 0 := by
  constructor
  · intro h
    have hs0 : j + -i = j + i := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.eq
    have hs : -i = i := add_left_cancel hs0
    simpa [two_mul] using eq_neg_iff_add_eq_zero.mp hs.symm
  · intro h
    have hs : i = -i := eq_neg_iff_add_eq_zero.mpr (by simpa [two_mul] using h)
    change DihedralGroup.r i * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.r i
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, sub_eq_add_neg, ← hs, add_comm]

omit [NeZero n] in
private lemma commute_sr_r_iff (i j : ZMod n) :
    Commute (DihedralGroup.sr i) (DihedralGroup.r j) ↔ j + j = 0 := by
  constructor
  · intro h
    have hs0 : i + j = i + -j := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.eq
    have hs : j = -j := add_left_cancel hs0
    simpa [two_mul] using eq_neg_iff_add_eq_zero.mp hs
  · intro h
    have hs : j = -j := eq_neg_iff_add_eq_zero.mpr (by simpa [two_mul] using h)
    change DihedralGroup.sr i * DihedralGroup.r j = DihedralGroup.r j * DihedralGroup.sr i
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, ← hs]

omit [NeZero n] in
private lemma commute_sr_sr_iff (i j : ZMod n) :
    Commute (DihedralGroup.sr i) (DihedralGroup.sr j) ↔ (j - i) + (j - i) = 0 := by
  constructor
  · intro h
    have hs0 : j - i = i - j := by simpa using h.eq
    have hs : j - i = -(j - i) := by
      calc
        j - i = i - j := hs0
        _ = -(j - i) := by abel
    simpa using eq_neg_iff_add_eq_zero.mp hs
  · intro h
    have hs : j - i = i - j := by
      have hneg : j - i = -(j - i) := eq_neg_iff_add_eq_zero.mpr h
      calc
        j - i = -(j - i) := hneg
        _ = i - j := by abel
    change DihedralGroup.sr i * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.sr i
    rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr, hs]

private abbrev EvenCommuteCode (n : ℕ) :=
  (ZMod n × ZMod n) ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n

private def evenCommuteEquiv (heven : Even n) :
    { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃ EvenCommuteCode n :=
  { toFun := fun
      | ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, _⟩ => .inl (i, j)
      | ⟨⟨DihedralGroup.r i, DihedralGroup.sr j⟩, _⟩ =>
          if i = 0 then .inr (.inl j) else .inr (.inr (.inl j))
      | ⟨⟨DihedralGroup.sr i, DihedralGroup.r j⟩, _⟩ =>
          if j = 0 then .inr (.inr (.inr (.inl i))) else .inr (.inr (.inr (.inr (.inl i))))
      | ⟨⟨DihedralGroup.sr i, DihedralGroup.sr j⟩, _⟩ =>
          if j - i = 0 then .inr (.inr (.inr (.inr (.inr (.inl i)))))
          else .inr (.inr (.inr (.inr (.inr (.inr i)))))
    invFun := fun
      | .inl (i, j) =>
          ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, by
            change DihedralGroup.r i * DihedralGroup.r j = DihedralGroup.r j * DihedralGroup.r i
            rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]⟩
      | .inr (.inl j) =>
          ⟨⟨DihedralGroup.r 0, DihedralGroup.sr j⟩,
            (commute_r_sr_iff n 0 j).2 (by simp)⟩
      | .inr (.inr (.inl j)) =>
          ⟨⟨DihedralGroup.r (halfTurn n), DihedralGroup.sr j⟩,
            (commute_r_sr_iff n (halfTurn n) j).2 (halfTurn_add_self n heven)⟩
      | .inr (.inr (.inr (.inl i))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.r 0⟩,
            (commute_sr_r_iff n i 0).2 (by simp)⟩
      | .inr (.inr (.inr (.inr (.inl i)))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.r (halfTurn n)⟩,
            (commute_sr_r_iff n i (halfTurn n)).2 (halfTurn_add_self n heven)⟩
      | .inr (.inr (.inr (.inr (.inr (.inl i))))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.sr i⟩,
            (commute_sr_sr_iff n i i).2 (by simp)⟩
      | .inr (.inr (.inr (.inr (.inr (.inr i))))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.sr (i + halfTurn n)⟩,
            (commute_sr_sr_iff n i (i + halfTurn n)).2 (by
              simpa [sub_eq_add_neg, add_assoc] using halfTurn_add_self n heven)⟩
    left_inv := by
      rintro ⟨⟨i | i, j | j⟩, hij⟩
      · rfl
      · dsimp
        split_ifs with hi
        · subst hi
          rfl
        · have hi' := eq_zero_or_eq_halfTurn n i ((commute_r_sr_iff n i j).mp hij)
          rcases hi' with rfl | hi' <;> try contradiction
          subst hi'
          rfl
      · dsimp
        split_ifs with hj
        · subst hj
          rfl
        · have hj' := eq_zero_or_eq_halfTurn n j ((commute_sr_r_iff n i j).mp hij)
          rcases hj' with rfl | hj' <;> try contradiction
          subst hj'
          rfl
      · dsimp
        split_ifs with hji
        · have : j = i := sub_eq_zero.mp hji
          subst this
          rfl
        · have hji' := eq_zero_or_eq_halfTurn n (j - i) ((commute_sr_sr_iff n i j).mp hij)
          rcases hji' with hzero | hhalf
          · contradiction
          · have : j = i + halfTurn n := by
              calc
                j = i + (j - i) := by abel
                _ = i + halfTurn n := by rw [hhalf]
            subst this
            rfl
    right_inv := by
      intro x
      cases x with
      | inl ij =>
          cases ij
          rfl
      | inr x =>
          cases x with
          | inl j => simp
          | inr x =>
              cases x with
              | inl j => simp [halfTurn_ne_zero n heven]
              | inr x =>
                  cases x with
                  | inl i => simp
                  | inr x =>
                      cases x with
                      | inl i => simp [halfTurn_ne_zero n heven]
                      | inr x =>
                          cases x with
                          | inl i => simp
                          | inr i => simp [halfTurn_ne_zero n heven] }

private lemma card_commute_even (heven : Even n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 6) := by
  rw [Nat.card_congr (evenCommuteEquiv n heven)]
  simp_rw [Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

/-
Source/core/bridge triage for Exercise `5-5.3-3`:
* source-facing: the reflections and rotations of `DihedralGroup n` contribute separate
  conjugacy-class counts, and the total number of conjugacy classes matches the number of
  irreducible characters described earlier in Chapter `5`.
* core/canonical: the owner of the total class count is `Nat.card (ConjClasses (DihedralGroup n))`.
* bridge/view: the final comparison theorem rewrites the total class count into the explicit
  Chapter `5` count `2 + (n - 1) / 2` in the odd case and `4 + (n / 2 - 1)` in the even case.

The odd branch of the total count is already owned by mathlib as
`DihedralGroup.card_conjClasses_odd`; this file supplies the missing even branch and keeps the
source-facing rotation/reflection decomposition visible in the public API.
-/
-- Proof sketch: for even `n`, the reflections split into two conjugacy classes while the
-- rotations are indexed by the unordered pairs `{i, -i}`, with fixed points `0` and `n / 2`,
-- giving `n / 2 + 1` rotation classes. Combined with the canonical odd branch from mathlib, this
-- yields the stated parity-dependent formula.
namespace DihedralGroup

/-- Helper for Exercise 5-5.3-3: conjugacy classes with a reflection representative. -/
private abbrev ReflectionConjClasses (n : ℕ) [NeZero n] :=
  { C : ConjClasses (DihedralGroup n) // ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i) }

/-- Helper for Exercise 5-5.3-3: conjugacy classes with a rotation representative. -/
private abbrev RotationConjClasses (n : ℕ) [NeZero n] :=
  { C : ConjClasses (DihedralGroup n) // ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i) }

/-- Helper for Exercise 5-5.3-3: the total number of conjugacy classes is the expected parity
formula. -/
private lemma card_conjClasses_by_parity :
    Nat.card (ConjClasses (DihedralGroup n)) =
      if Even n then n / 2 + 3 else (n + 3) / 2 := by
  by_cases heven : Even n
  · -- The even branch comes from the commuting-pair count already established above.
    rw [if_pos heven]
    have hn : 0 < n := Nat.pos_of_neZero n
    calc
      Nat.card (ConjClasses (DihedralGroup n)) = (n + 6) / 2 := by
        rw [← Nat.mul_div_mul_left (n + 6) 2 hn, ← card_commute_even n heven, mul_comm,
          card_comm_eq_card_conjClasses_mul_card, nat_card,
          Nat.mul_div_left _ (mul_pos two_pos hn)]
      _ = n / 2 + 3 := by
        have htwo : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
        omega
  · -- The odd branch is already available from mathlib.
    rw [if_neg heven]
    exact card_conjClasses_odd (Nat.not_even_iff_odd.mp heven)

/-- Helper for Exercise 5-5.3-3: when `n` is odd, every reflection is conjugate to `sr 0`. -/
private lemma reflection_class_eq_sr_zero_of_odd (hodd : Odd n) (i : ZMod n) :
    ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 0) := by
  -- Odd order makes `2` invertible in `ZMod n`, so a suitable rotation shifts the index to `0`.
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rw [isConj_iff]
  let u : (ZMod n)ˣ :=
    ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat)
  let a : ZMod n := u⁻¹ * i
  refine ⟨DihedralGroup.r a, ?_⟩
  have hu : (2 : ZMod n) * a = i := by
    simpa [u, a, mul_assoc] using u.mul_inv_cancel_left i
  have hdouble : a + a = i := by
    simpa [two_mul, a, add_comm, add_left_comm, add_assoc] using hu
  calc
    DihedralGroup.r a * DihedralGroup.sr i * (DihedralGroup.r a)⁻¹
        = DihedralGroup.sr (i - (a + a)) := by
            simp [sub_eq_add_neg, add_assoc]
    _ = DihedralGroup.sr 0 := by rw [hdouble, sub_self]

/-- Helper for Exercise 5-5.3-3: an even dihedral group has no solution to `2a = 1` in
`ZMod n`. -/
private lemma double_ne_one_of_even (heven : Even n) (a : ZMod n) :
    a + a ≠ (1 : ZMod n) := by
  -- Reduce the equation modulo `2`, where doubling is identically zero.
  intro h
  let f : ZMod n →+* ZMod 2 := ZMod.castHom heven.two_dvd (ZMod 2)
  have hmap := congrArg f h
  rw [map_add] at hmap
  have hone : (ZMod.cast (1 : ZMod n) : ZMod 2) = (1 : ZMod 2) := ZMod.cast_one heven.two_dvd
  have hmap' : (ZMod.cast a : ZMod 2) + ZMod.cast a = (1 : ZMod 2) := by
    simpa [f, hone] using hmap
  have hdouble_zero : (ZMod.cast a : ZMod 2) + ZMod.cast a = (0 : ZMod 2) := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      (ZMod.cast a : ZMod 2) + ZMod.cast a = (2 : ZMod 2) * ZMod.cast a := by ring
      _ = 0 := by rw [htwo, zero_mul]
  exact zero_ne_one (hdouble_zero.symm.trans hmap')

/-- Helper for Exercise 5-5.3-3: when `n` is even, each reflection is conjugate to either `sr 0`
or `sr 1` according to the parity of its index. -/
private lemma reflection_class_eq_sr_zero_or_sr_one_of_even (heven : Even n) (i : ZMod n) :
    ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 0) ∨
      ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 1) := by
  -- Splitting the index by parity gives exactly the two reflection orbits.
  have hi : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i
  rcases Nat.even_or_odd i.val with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨DihedralGroup.r k, ?_⟩
    calc
      DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹
          = DihedralGroup.sr (i - ((k : ZMod n) + (k : ZMod n))) := by
              simp [sub_eq_add_neg, add_assoc]
      _ = DihedralGroup.sr (((k + k : ℕ) : ZMod n) - ((k : ZMod n) + (k : ZMod n))) := by
            rw [← hi, hk]
      _ = DihedralGroup.sr 0 := by
            simp [two_mul, Nat.cast_mul]
  · right
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨DihedralGroup.r k, ?_⟩
    calc
      DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹
          = DihedralGroup.sr (i - ((k : ZMod n) + (k : ZMod n))) := by
              simp [sub_eq_add_neg, add_assoc]
      _ = DihedralGroup.sr (((2 * k + 1 : ℕ) : ZMod n) - ((k : ZMod n) + (k : ZMod n))) := by
            rw [← hi, hk]
      _ = DihedralGroup.sr 1 := by
            simp [two_mul, Nat.cast_add, Nat.cast_mul]

/-- Helper for Exercise 5-5.3-3: the two even reflection classes are distinct. -/
private lemma mk_sr_zero_ne_mk_sr_one_of_even (heven : Even n) :
    ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) ≠
      ConjClasses.mk (DihedralGroup.sr (1 : ZMod n)) := by
  intro hclass
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hclass
  rcases hclass with ⟨g, hg⟩
  cases g with
  | r a =>
      have hdouble : (-a) + (-a) = (1 : ZMod n) := by
        apply DihedralGroup.sr.inj
        simpa [sub_eq_add_neg, add_assoc, two_mul] using hg
      exact double_ne_one_of_even n heven (-a) hdouble
  | sr a =>
      have hdouble : a + a = (1 : ZMod n) := by
        apply DihedralGroup.sr.inj
        simpa [sub_eq_add_neg, add_assoc, two_mul] using hg
      exact double_ne_one_of_even n heven a hdouble

/-- Helper for Exercise 5-5.3-3: a rotation is never conjugate to a reflection. -/
private lemma not_isConj_r_sr (i j : ZMod n) :
    ¬ IsConj (DihedralGroup.r i) (DihedralGroup.sr j) := by
  intro hconj
  rw [isConj_iff] at hconj
  rcases hconj with ⟨g, hg⟩
  cases g with
  | r a =>
      have : DihedralGroup.r i = DihedralGroup.sr j := by
        simpa [sub_eq_add_neg, add_assoc] using hg
      cases this
  | sr a =>
      have : DihedralGroup.r (-i) = DihedralGroup.sr j := by
        simpa [sub_eq_add_neg, add_assoc] using hg
      cases this

/-- Helper for Exercise 5-5.3-3: the full set of conjugacy classes splits into the rotation
classes and the reflection classes. -/
private lemma card_conjClasses_eq_rotation_add_reflection :
    Nat.card (ConjClasses (DihedralGroup n)) =
      Nat.card (RotationConjClasses n) + Nat.card (ReflectionConjClasses n) := by
  classical
  let p : ConjClasses (DihedralGroup n) → Prop :=
    fun C => ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i)
  let q : ConjClasses (DihedralGroup n) → Prop :=
    fun C => ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)
  have hcompl : ∀ C : ConjClasses (DihedralGroup n), ¬ p C ↔ q C := by
    intro C
    constructor
    · intro hC
      -- Every class has a representative, so a class outside the rotation side must come from a
      -- reflection representative.
      obtain ⟨g, hg⟩ := ConjClasses.exists_rep C
      cases g with
      | r i =>
          exact False.elim (hC ⟨i, hg.symm⟩)
      | sr i =>
          exact ⟨i, hg.symm⟩
    · rintro ⟨i, hi⟩ ⟨j, hj⟩
      -- Route correction: use the predicate-complement split rather than `Quotient.out`; the
      -- disjointness is exactly the statement that rotations are never conjugate to reflections.
      exact not_isConj_r_sr (n := n) j i <|
        (ConjClasses.mk_eq_mk_iff_isConj).mp (hj.symm.trans hi)
  let e :
      ConjClasses (DihedralGroup n) ≃
        { C : ConjClasses (DihedralGroup n) // p C } ⊕
          { C : ConjClasses (DihedralGroup n) // q C } :=
    (Equiv.sumCompl p).symm.trans
      (Equiv.sumCongr
        (Equiv.subtypeEquivRight fun _ => Iff.rfl)
        (Equiv.subtypeEquivRight hcompl))
  -- Count the two disjoint families using the canonical sum decomposition of all conjugacy
  -- classes.
  rw [Nat.card_congr e, Nat.card_sum]

/-- Exercise 5-5.3-3: the reflection elements of `DihedralGroup n` contribute one conjugacy class
for odd `n` and two conjugacy classes for even `n`. -/
theorem card_reflection_conjClasses :
    Nat.card { C : ConjClasses (DihedralGroup n) //
        ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i) } =
      if Even n then 2 else 1 := by
  change Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1
  classical
  by_cases heven : Even n
  · rw [if_pos heven]
    have hreflect :
        ∀ C : ConjClasses (DihedralGroup n),
          (∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)) ↔
            C = ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) ∨
              C = ConjClasses.mk (DihedralGroup.sr (1 : ZMod n)) := by
      intro C
      constructor
      · rintro ⟨i, rfl⟩
        exact reflection_class_eq_sr_zero_or_sr_one_of_even (n := n) heven i
      · rintro (hC | hC)
        · exact ⟨0, hC⟩
        · exact ⟨1, hC⟩
    -- The even branch reduces to the two distinct classes represented by `sr 0` and `sr 1`.
    rw [Nat.card_congr (Equiv.subtypeEquivRight hreflect), Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_eq_or_eq_of_ne (mk_sr_zero_ne_mk_sr_one_of_even (n := n) heven)
  · rw [if_neg heven]
    rcases Nat.not_even_iff_odd.mp heven with hodd
    have hreflect :
        ∀ C : ConjClasses (DihedralGroup n),
          (∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)) ↔
            C = ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) := by
      intro C
      constructor
      · rintro ⟨i, rfl⟩
        exact reflection_class_eq_sr_zero_of_odd (n := n) hodd i
      · intro hC
        exact ⟨0, hC⟩
    -- In the odd branch, all reflections collapse to the single class of `sr 0`.
    rw [Nat.card_congr (Equiv.subtypeEquivRight hreflect), Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_eq _

/-- Exercise 5-5.3-3: the rotation elements of `DihedralGroup n` contribute `(n + 1) / 2`
conjugacy classes for odd `n` and `n / 2 + 1` conjugacy classes for even `n`. -/
theorem card_rotation_conjClasses :
    Nat.card { C : ConjClasses (DihedralGroup n) //
        ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i) } =
      if Even n then n / 2 + 1 else (n + 1) / 2 := by
  change Nat.card (RotationConjClasses n) = if Even n then n / 2 + 1 else (n + 1) / 2
  by_cases heven : Even n
  · rw [if_pos heven]
    have hsplit := card_conjClasses_eq_rotation_add_reflection (n := n)
    have htotal := card_conjClasses_by_parity (n := n)
    have hreflect : Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1 := by
      simpa [ReflectionConjClasses] using (card_reflection_conjClasses (n := n))
    rw [if_pos heven] at htotal hreflect
    -- Once the total number of classes and the reflection contribution are fixed, the rotation
    -- count is the remaining summand.
    omega
  · rw [if_neg heven]
    have hsplit := card_conjClasses_eq_rotation_add_reflection (n := n)
    have htotal := card_conjClasses_by_parity (n := n)
    have hreflect : Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1 := by
      simpa [ReflectionConjClasses] using (card_reflection_conjClasses (n := n))
    rw [if_neg heven] at htotal hreflect
    -- The odd branch is the same subtraction after rewriting the parity-dependent totals.
    omega

/-- If `n` is even, then `DihedralGroup n` has `n / 2 + 3` conjugacy classes. -/
theorem card_conjClasses_even (heven : Even n) :
    Nat.card (ConjClasses (DihedralGroup n)) = n / 2 + 3 := by
  have hn : 0 < n := Nat.pos_of_neZero n
  calc
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 6) / 2 := by
      rw [← Nat.mul_div_mul_left (n + 6) 2 hn, ← card_commute_even n heven, mul_comm,
        card_comm_eq_card_conjClasses_mul_card, nat_card,
        Nat.mul_div_left _ (mul_pos two_pos hn)]
    _ = n / 2 + 3 := by
      have htwo : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
      omega

/-- Exercise 5-5.3-3: the number of conjugacy classes of `DihedralGroup n` is `n / 2 + 3` for
even `n` and `(n + 3) / 2` for odd `n`, matching the textbook count of irreducible characters. -/
theorem card_conjClasses :
    Nat.card (ConjClasses (DihedralGroup n)) =
      if Even n then n / 2 + 3 else (n + 3) / 2 := by
  by_cases heven : Even n
  · rw [if_pos heven]
    exact card_conjClasses_even n heven
  · rw [if_neg heven]
    exact card_conjClasses_odd (Nat.not_even_iff_odd.mp heven)

/-- Exercise 5-5.3-3: the conjugacy-class count agrees with the Chapter `5` list of irreducible
characters, namely two degree-`1` characters plus `(n - 1) / 2` two-dimensional characters when
`n` is odd, and four degree-`1` characters plus `n / 2 - 1` two-dimensional characters when `n`
is even. -/
theorem card_conjClasses_eq_irreducible_character_count :
    Nat.card (ConjClasses (DihedralGroup n)) =
      (if Even n then 4 else 2) + (if Even n then n / 2 - 1 else (n - 1) / 2) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  rw [card_conjClasses]
  by_cases heven : Even n
  · rw [if_pos heven, if_pos heven, if_pos heven]
    rcases heven with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    omega
  · rw [if_neg heven, if_neg heven, if_neg heven]
    rcases Nat.not_even_iff_odd.mp heven with ⟨k, rfl⟩
    norm_num [Nat.add_assoc]
    omega

end DihedralGroup

end
