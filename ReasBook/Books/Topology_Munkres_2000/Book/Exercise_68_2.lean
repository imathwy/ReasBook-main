module

public import Topology_Munkres_2000.Book.Exercise_68_2.NormalForm
public import Mathlib.GroupTheory.OrderOfElement

public section

universe u v

namespace Monoid.Coprod

open Monoid.CoprodI

/- Exercise 68.2 (1): The length of an element of a free product is the length of its
canonical reduced word. -/
#check wordLength

/-- Helper for Exercise 68.2: the indexed image of a letter from the left factor. -/
lemma equivIndexed_inl {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] (a : G₁) :
    equivIndexed (inl a : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) false (ULift.up a) := by
  -- Route correction: use owner API rather than unfolding the imported equivalence.
  exact equivIndexed_apply_inl a

/-- Helper for Exercise 68.2: the indexed image of a letter from the right factor. -/
lemma equivIndexed_inr {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] (b : G₂) :
    equivIndexed (inr b : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) true (ULift.up b) := by
  -- Route correction: use owner API rather than unfolding the imported equivalence.
  exact equivIndexed_apply_inr b

/-- Helper for Exercise 68.2: two nonidentity letters from distinct factors are already reduced. -/
lemma Word.equiv_mul_of_ne_toList {G : Bool → Type u} [(i : Bool) → Monoid (G i)]
    [∀ i, DecidableEq (G i)] {i j : Bool} (a : G i) (b : G j) (ha : a ≠ 1)
    (hb : b ≠ 1) (hij : i ≠ j) :
    (Word.equiv (of a * of b)).toList = [⟨i, a⟩, ⟨j, b⟩] := by
  -- First realize the second letter as a one-letter reduced word.
  let tail : Word G := Word.cons b Word.empty (by rintro h; cases h) hb
  have htail : of b • Word.empty = tail := Word.cons_eq_smul.symm
  have hfst : tail.fstIdx ≠ some i := by
    simp [tail, hij.symm]
  -- The distinct endpoint condition lets the first letter prepend without reduction.
  have hword : (of a * of b) • Word.empty = Word.cons a tail hfst ha := by
    rw [mul_smul, htail]
    exact Word.cons_eq_smul.symm
  change ((of a * of b) • Word.empty).toList = _
  rw [hword]
  rfl

/-- Helper for Exercise 68.2: letters from the two Bool-indexed factors do not commute. -/
lemma of_mul_ne_swap {G : Bool → Type u} [(i : Bool) → Monoid (G i)]
    (a : G false) (b : G true) (ha : a ≠ 1) (hb : b ≠ 1) :
    of a * of b ≠ of b * of a := by
  classical
  -- Applying the canonical normal form exposes different first indices.
  intro h
  have hlist := congrArg (fun z : CoprodI G ↦ (Word.equiv z).toList) h
  rw [Word.equiv_mul_of_ne_toList a b ha hb (by decide),
    Word.equiv_mul_of_ne_toList b a hb ha (by decide)] at hlist
  cases hlist

/-- Helper for Exercise 68.2: a positive binary normal form has a nonempty indexed-word model. -/
lemma normalForm_neWord {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (x : Monoid.Coprod G₁ G₂) (h : 0 < wordLength x) :
    ∃ i j, ∃ w : NeWord (LiftedFactors G₁ G₂) i j,
      w.toWord = normalForm x ∧ w.prod = equivIndexed x ∧
        w.toList.length = wordLength x := by
  classical
  -- Positive list length makes the canonical reduced word nonempty.
  have hne : normalForm x ≠ Word.empty := by
    intro hempty
    rw [wordLength_apply, hempty] at h
    simp at h
  obtain ⟨i, j, w, hword⟩ := NeWord.of_word (normalForm x) hne
  refine ⟨i, j, w, hword, ?_, ?_⟩
  · -- Products agree because `w` is exactly the canonical normal form.
    rw [NeWord.prod, hword, normalForm_prod]
  · -- The list equality records the exact binary word length.
    rw [wordLength_apply, ← hword]
    rfl

/-- Helper for Exercise 68.2: parity records whether a Bool-indexed reduced word changes factors. -/
lemma NeWord.even_length_iff_endIdx_ne {G : Bool → Type u} [(i : Bool) → Monoid (G i)]
    {i j : Bool} (w : NeWord G i j) : Even w.toList.length ↔ i ≠ j := by
  -- Concatenation adds lengths and flips the endpoint exactly at each factor change.
  induction w with
  | singleton x hx => simp
  | @append i j k l w₁ hne w₂ ih₁ ih₂ =>
      simp only [NeWord.toList, List.length_append, Nat.even_add, ih₁, ih₂]
      cases i <;> cases j <;> cases k <;> cases l <;> simp_all

/-- Helper for Exercise 68.2: odd Bool-indexed reduced words begin and end in one factor. -/
lemma NeWord.odd_length_iff_endIdx_eq {G : Bool → Type u} [(i : Bool) → Monoid (G i)]
    {i j : Bool} (w : NeWord G i j) : Odd w.toList.length ↔ i = j := by
  -- Natural-number parity is complementary, as is equality of two Bool indices.
  rw [← not_iff_not]
  simpa [Nat.not_odd_iff_even] using NeWord.even_length_iff_endIdx_ne w

/-- Helper for Exercise 68.2: a reduced word of length at least two splits off its final letter. -/
lemma NeWord.exists_init_of_two_le_length {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] {i j : ι} (w : NeWord G i j)
    (h_length : 2 ≤ w.toList.length) :
    ∃ k, ∃ v : NeWord G i k, k ≠ j ∧
      w.prod = v.prod * of w.last ∧ v.toList.length + 1 = w.toList.length := by
  -- Structural induction removes the final singleton, recursively descending through appends.
  induction w with
  | singleton x hx =>
      simp at h_length
  | @append i j k l w₁ hne w₂ ih₁ ih₂ =>
      cases w₂ with
      | singleton x hx =>
          refine ⟨j, w₁, hne, ?_, ?_⟩
          · simp
          · simp
      | @append k m n l w₂₁ hmn w₂₂ =>
          have hleft : 0 < w₂₁.toList.length :=
            List.length_pos_of_ne_nil w₂₁.toList_ne_nil
          have hright : 0 < w₂₂.toList.length :=
            List.length_pos_of_ne_nil w₂₂.toList_ne_nil
          have htwo : 2 ≤ (NeWord.append w₂₁ hmn w₂₂).toList.length := by
            simp only [NeWord.toList, List.length_append]
            omega
          obtain ⟨p, v, hp, hprod, hlen⟩ := ih₂ htwo
          refine ⟨p, NeWord.append w₁ hne v, hp, ?_, ?_⟩
          · simp only [NeWord.append_prod, NeWord.append_last] at hprod ⊢
            rw [hprod, mul_assoc]
          · simp only [NeWord.toList, List.length_append] at hlen ⊢
            omega

/-- Helper for Exercise 68.2: multiplying in the first factor cannot increase word length. -/
lemma Word.length_smul_le_of_fstIdx_eq {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)]
    {i : ι} (m : G i) (w : Word G)
    (hfirst : w.fstIdx = some i) :
    (of m • w).toList.length ≤ w.toList.length := by
  classical
  -- Decompose at the first letter, then merge the two letters in the same factor.
  induction w using Word.consRecOn with
  | empty =>
      simp [Word.fstIdx, Word.empty] at hfirst
  | cons j a tail htail ha ih =>
      rw [Word.fstIdx_cons] at hfirst
      have hji : j = i := Option.some.inj hfirst
      subst j
      have hmul : of m * of a = of (m * a) := (map_mul of m a).symm
      rw [Word.cons_eq_smul, ← mul_smul, hmul]
      by_cases hma : m * a = 1
      · rw [hma, map_one, one_smul, ← Word.cons_eq_smul (h1 := htail) (h2 := ha)]
        simp
      · rw [← Word.cons_eq_smul (h1 := htail) (h2 := hma),
          ← Word.cons_eq_smul (h1 := htail) (h2 := ha)]
        rfl

/-- Helper for Exercise 68.2: cyclic rotation shortens a reduced word with equal endpoints. -/
lemma NeWord.exists_isConj_prod_length_lt_of_endIdx_eq {ι : Type*} {G : ι → Type*}
    [(i : ι) → Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)]
    {i : ι} (w : NeWord G i i) (h_length : 2 ≤ w.toList.length) :
    ∃ y : CoprodI G, IsConj w.prod y ∧
      (Word.equiv y).toList.length < w.toList.length := by
  obtain ⟨k, v, hki, hprod, hlen⟩ :=
    Monoid.Coprod.NeWord.exists_init_of_two_le_length w h_length
  refine ⟨of w.last * v.prod, ?_, ?_⟩
  · -- Conjugating by the final letter rotates it to the front.
    rw [isConj_iff]
    refine ⟨of w.last, ?_⟩
    rw [hprod]
    simp [mul_assoc]
  · -- Equal endpoint indices make the rotated letter merge with the first letter of `v`.
    have hfirst : v.toWord.fstIdx = some i := by
      simp [NeWord.toWord, Word.fstIdx]
    have hrotatedProd : Word.prod (of w.last • v.toWord) = of w.last * v.prod := by
      rw [Word.prod_smul]
      rfl
    have hword : Word.equiv (of w.last * v.prod) = of w.last • v.toWord := by
      calc
        Word.equiv (of w.last * v.prod) =
            Word.equiv (Word.prod (of w.last • v.toWord)) :=
          congrArg Word.equiv hrotatedProd.symm
        _ = of w.last • v.toWord := Word.equiv.apply_symm_apply _
    rw [hword]
    have hle := Word.length_smul_le_of_fstIdx_eq w.last v.toWord hfirst
    have hvlen : v.toWord.toList.length = v.toList.length := rfl
    omega

/-- Helper for Exercise 68.2: transport cyclic shortening across equal monoid-family instances. -/
lemma NeWord.exists_isConj_prod_length_lt_of_monoid_eq {ι : Type*} {G : ι → Type*}
    (mon : (i : ι) → Monoid (G i)) [grp : (i : ι) → Group (G i)]
    [DecidableEq ι] [∀ i, DecidableEq (G i)]
    (hmon : mon = fun i => (grp i).toMonoid) {i : ι}
    (w : @NeWord ι G mon i i) (h_length : 2 ≤ w.toList.length) :
    ∃ y : @CoprodI ι G mon, IsConj w.prod y ∧
      (@Word.equiv ι G mon _ _ y).toList.length < w.toList.length := by
  -- Equality induction changes the instance spelling before applying cyclic shortening.
  subst mon
  exact NeWord.exists_isConj_prod_length_lt_of_endIdx_eq w h_length

/-- Helper for Exercise 68.2: concatenate a cyclically reduced word with itself repeatedly. -/
noncomputable def NeWord.cyclicPowerWord {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] {i j : ι} (w : NeWord G i j) (hji : j ≠ i) :
    ℕ → NeWord G i j
  | 0 => w
  | n + 1 => NeWord.append (NeWord.cyclicPowerWord w hji n) hji w

/-- Helper for Exercise 68.2: repeated reduced words represent positive powers. -/
lemma NeWord.cyclicPowerWord_prod {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] {i j : ι} (w : NeWord G i j) (hji : j ≠ i) (n : ℕ) :
    (NeWord.cyclicPowerWord w hji n).prod = w.prod ^ (n + 1) := by
  -- Each recursive append contributes one further copy of the product.
  induction n with
  | zero => simp [NeWord.cyclicPowerWord]
  | succ n ih => simp [NeWord.cyclicPowerWord, ih, pow_succ]

/-- Helper for Exercise 68.2: a reduced word with distinct endpoint factors has infinite order. -/
lemma NeWord.not_isOfFinOrder_prod_of_endIdx_ne {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] {i j : ι} (w : NeWord G i j) (hji : j ≠ i) :
    ¬ IsOfFinOrder w.prod := by
  classical
  intro hfin
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let p := NeWord.cyclicPowerWord w hji m
  have hprod : p.prod = 1 := by
    rw [show p.prod = w.prod ^ (m + 1) by
      exact NeWord.cyclicPowerWord_prod w hji m]
    exact hpow
  -- Uniqueness of reduced normal forms would force the nonempty repeated word to be empty.
  have hempty : p.toWord = Word.empty := by
    calc
      p.toWord = Word.equiv p.prod := (Word.equiv.apply_symm_apply p.toWord).symm
      _ = Word.equiv (1 : CoprodI G) := congrArg Word.equiv hprod
      _ = Word.empty := rfl
  have hnil : p.toList = [] := by
    simpa [NeWord.toWord] using congrArg Word.toList hempty
  exact p.toList_ne_nil hnil

/-- Part (a) of Exercise 68.2: The free product of two nontrivial groups is not abelian. -/
theorem not_isMulCommutative {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    [Nontrivial G₁] [Nontrivial G₂] :
    ¬ IsMulCommutative (Monoid.Coprod G₁ G₂) := by
  classical
  obtain ⟨a, ha⟩ := exists_ne (1 : G₁)
  obtain ⟨b, hb⟩ := exists_ne (1 : G₂)
  intro hcomm
  letI : IsMulCommutative (Monoid.Coprod G₁ G₂) := hcomm
  -- Transport the alleged commutation relation to the indexed normal-form model.
  have hmul : inl a * inr b = inr b * inl a := mul_comm' _ _
  have hindexed := congrArg equivIndexed hmul
  rw [map_mul, map_mul, equivIndexed_inl, equivIndexed_inr] at hindexed
  have hau : (ULift.up a : LiftedFactors G₁ G₂ false) ≠ 1 := by
    intro h
    exact ha (congrArg ULift.down h)
  have hbu : (ULift.up b : LiftedFactors G₁ G₂ true) ≠ 1 := by
    intro h
    exact hb (congrArg ULift.down h)
  exact of_mul_ne_swap (G := LiftedFactors G₁ G₂) (ULift.up a) (ULift.up b) hau hbu hindexed

/-- The first assertion of part (b) of Exercise 68.2: An element represented by a reduced word
of positive even length has infinite order. -/
theorem not_isOfFinOrder_of_even_wordLength {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (x : Monoid.Coprod G₁ G₂) (h_even : Even (wordLength x))
    (h_length : 2 ≤ wordLength x) : ¬ IsOfFinOrder x := by
  classical
  obtain ⟨i, j, w, hword, hprod, hlen⟩ := normalForm_neWord x (by omega)
  have hij : i ≠ j := (NeWord.even_length_iff_endIdx_ne w).mp (by simpa [hlen] using h_even)
  have hinfinite : ¬ IsOfFinOrder w.prod := NeWord.not_isOfFinOrder_prod_of_endIdx_ne w hij.symm
  -- A multiplicative equivalence preserves finite order, contradicting cyclic reduction.
  intro hfin
  have himage : IsOfFinOrder (equivIndexed x) := equivIndexed.toMonoidHom.isOfFinOrder hfin
  exact hinfinite (hprod.symm ▸ himage)

/-- The second assertion of part (b) of Exercise 68.2: An element represented by a reduced word
of odd length at least three is conjugate to an element represented by a shorter reduced word;
the lower bound excludes the length-one exception to the source's literal odd-length assertion. -/
theorem exists_isConj_wordLength_lt_of_odd {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (x : Monoid.Coprod G₁ G₂) (h_odd : Odd (wordLength x))
    (h_length : 3 ≤ wordLength x) :
    ∃ y : Monoid.Coprod G₁ G₂, IsConj x y ∧ wordLength y < wordLength x := by
  classical
  -- Represent the positive canonical word by an indexed nonempty reduced word.
  obtain ⟨i, j, w, hword, hprod, hlen⟩ := normalForm_neWord x (by omega)
  have hij : i = j := (NeWord.odd_length_iff_endIdx_eq w).mp (by simpa [hlen] using h_odd)
  subst j
  have htwo : 2 ≤ w.toList.length := by omega
  have hmonoid :
      (fun k => instMonoidLiftedFactors G₁ G₂ k) =
        (fun k => (instGroupLiftedFactors G₁ G₂ k).toMonoid) := by
    funext k
    cases k <;> rfl
  obtain ⟨z, hconj, hzlen⟩ :=
    NeWord.exists_isConj_prod_length_lt_of_monoid_eq
      (fun k => instMonoidLiftedFactors G₁ G₂ k) hmonoid w htwo
  refine ⟨equivIndexed.symm z, ?_, ?_⟩
  · -- Map indexed conjugacy back through the inverse equivalence.
    have hmapped := equivIndexed.symm.toMonoidHom.map_isConj hconj
    simpa [hprod] using hmapped
  · -- Both binary lengths are the lengths of their indexed canonical words.
    rw [wordLength_apply, normalForm_eq_wordEquiv]
    have hzlen' : (Word.equiv z).toList.length < wordLength x := by
      rwa [hlen] at hzlen
    simpa using hzlen'

/-- Helper for Exercise 68.2: a reduced word of length at most one represents one generator. -/
lemma Word.prod_eq_one_or_eq_of_of_length_le_one {ι : Type*} {G : ι → Type*}
    [(i : ι) → Monoid (G i)] (w : Word G) (h_length : w.toList.length ≤ 1) :
    w.prod = 1 ∨ ∃ i, ∃ g : G i, w.prod = of g := by
  -- Decompose the reduced word into its first letter and remaining tail.
  induction w using Word.consRecOn with
  | empty =>
      exact Or.inl Word.prod_empty
  | cons i g tail hfirst hg ih =>
      have htail_length : tail.toList.length = 0 := by
        simpa [Word.cons] using h_length
      have htail : tail = Word.empty := by
        apply Word.ext
        exact List.eq_nil_of_length_eq_zero htail_length
      right
      refine ⟨i, g, ?_⟩
      rw [Word.prod_cons, htail, Word.prod_empty, mul_one]

/-- Helper for Exercise 68.2: elements of binary word length at most one lie in a factor. -/
lemma exists_eq_inl_or_eq_inr_of_wordLength_le_one {G₁ : Type u} {G₂ : Type v}
    [Monoid G₁] [Monoid G₂] (x : Monoid.Coprod G₁ G₂) (h_length : wordLength x ≤ 1) :
    (∃ g : G₁, x = inl g) ∨ ∃ g : G₂, x = inr g := by
  classical
  have hnormal_length : (normalForm x).toList.length ≤ 1 := by
    rwa [wordLength_apply] at h_length
  rcases Word.prod_eq_one_or_eq_of_of_length_le_one (normalForm x) hnormal_length with
    hprod | ⟨i, g, hprod⟩
  · left
    refine ⟨1, ?_⟩
    apply equivIndexed.injective
    rw [← normalForm_prod, hprod, equivIndexed_apply_inl]
    exact (map_one of).symm
  · cases i with
    | false =>
        left
        refine ⟨ULift.down g, ?_⟩
        apply equivIndexed.injective
        rw [← normalForm_prod, hprod, equivIndexed_apply_inl]
    | true =>
        right
        refine ⟨ULift.down g, ?_⟩
        apply equivIndexed.injective
        rw [← normalForm_prod, hprod, equivIndexed_apply_inr]

/-- Helper for Exercise 68.2: every finite-order free-product element is conjugate into a factor. -/
lemma isOfFinOrder_isConj_factor {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    (x : Monoid.Coprod G₁ G₂) (hfin : IsOfFinOrder x) :
    (∃ g : G₁, IsOfFinOrder g ∧ IsConj x (inl g)) ∨
      ∃ g : G₂, IsOfFinOrder g ∧ IsConj x (inr g) := by
  -- Strong induction reduces positive odd words to a strictly shorter conjugate.
  let P : ℕ → Prop := fun n ↦ ∀ x : Monoid.Coprod G₁ G₂, wordLength x = n →
    IsOfFinOrder x →
      (∃ g : G₁, IsOfFinOrder g ∧ IsConj x (inl g)) ∨
        ∃ g : G₂, IsOfFinOrder g ∧ IsConj x (inr g)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx hfin
        by_cases hshort : wordLength x ≤ 1
        · rcases exists_eq_inl_or_eq_inr_of_wordLength_le_one x hshort with
            ⟨g, rfl⟩ | ⟨g, rfl⟩
          · left
            refine ⟨g, ?_, IsConj.refl _⟩
            exact Monoid.Coprod.inl_injective.isOfFinOrder_iff.mp hfin
          · right
            refine ⟨g, ?_, IsConj.refl _⟩
            exact Monoid.Coprod.inr_injective.isOfFinOrder_iff.mp hfin
        · rcases Nat.even_or_odd (wordLength x) with heven | hodd
          · exact (not_isOfFinOrder_of_even_wordLength x heven (by omega) hfin).elim
          · obtain ⟨k, hk⟩ := hodd
            have hthree : 3 ≤ wordLength x := by omega
            obtain ⟨y, hxy, hylen⟩ :=
              exists_isConj_wordLength_lt_of_odd x ⟨k, hk⟩ hthree
            have hyfin : IsOfFinOrder y := hxy.isOfFinOrder hfin
            rcases ih (wordLength y) (by omega) y rfl hyfin with
              ⟨g, hg, hyg⟩ | ⟨g, hg, hyg⟩
            · exact Or.inl ⟨g, hg, hxy.trans hyg⟩
            · exact Or.inr ⟨g, hg, hxy.trans hyg⟩
  exact hP (wordLength x) x rfl hfin

/-- Part (c) of Exercise 68.2: The finite-order elements of a free product of two groups are exactly
the elements conjugate to finite-order elements of one of the factors. -/
theorem isOfFinOrder_iff_isConj_factor {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (x : Monoid.Coprod G₁ G₂) :
    IsOfFinOrder x ↔
      (∃ g : G₁, IsOfFinOrder g ∧ IsConj x (inl g)) ∨
        ∃ g : G₂, IsOfFinOrder g ∧ IsConj x (inr g) := by
  constructor
  · -- The forward implication is the remaining strong-induction classification.
    exact isOfFinOrder_isConj_factor x
  · -- Homomorphisms and conjugacy both preserve finite order.
    rintro (⟨g, hg, hconj⟩ | ⟨g, hg, hconj⟩)
    · exact hconj.symm.isOfFinOrder
        ((inl : G₁ →* Monoid.Coprod G₁ G₂).isOfFinOrder hg)
    · exact hconj.symm.isOfFinOrder
        ((inr : G₂ →* Monoid.Coprod G₁ G₂).isOfFinOrder hg)

end Monoid.Coprod

open Monoid.Coprod

/-- Exercise 68.2 theorem suite: free products of two groups are nonabelian when both factors
are nontrivial, and their reduced-word lengths characterize torsion as stated in parts (b) and
(c). -/
theorem Monoid.Coprod.«Exercise 68.2 theorem suite» {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] :
    (Nontrivial G₁ → Nontrivial G₂ →
      ¬ IsMulCommutative (Monoid.Coprod G₁ G₂)) ∧
      (∀ x : Monoid.Coprod G₁ G₂, Even (wordLength x) →
        2 ≤ wordLength x → ¬ IsOfFinOrder x) ∧
      (∀ x : Monoid.Coprod G₁ G₂, Odd (wordLength x) →
        3 ≤ wordLength x →
          ∃ y : Monoid.Coprod G₁ G₂, IsConj x y ∧ wordLength y < wordLength x) ∧
      (∀ x : Monoid.Coprod G₁ G₂, IsOfFinOrder x ↔
        ( ∃ g : G₁, IsOfFinOrder g ∧ IsConj x (inl g)) ∨
          ∃ g : G₂, IsOfFinOrder g ∧ IsConj x (inr g)) := by
  constructor
  · -- Part (a) follows after installing the two nontriviality hypotheses.
    intro hG₁ hG₂
    letI : Nontrivial G₁ := hG₁
    letI : Nontrivial G₂ := hG₂
    exact not_isMulCommutative
  constructor
  · -- The even-length assertion is the cyclically reduced case.
    exact not_isOfFinOrder_of_even_wordLength
  constructor
  · -- The odd-length assertion is cyclic shortening.
    exact exists_isConj_wordLength_lt_of_odd
  · -- Strong induction gives the complete finite-order classification.
    exact isOfFinOrder_iff_isConj_factor
