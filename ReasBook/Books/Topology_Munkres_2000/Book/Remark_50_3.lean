module

import Topology_Munkres_2000.Book.Remark_50_3.CubicalIncidence
public import Topology_Munkres_2000.Book.Theorem_50_4
import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
import Topology_Munkres_2000.Book.Theorem_50_3
public import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Contractible

public section

open scoped CoveringDimension

universe u

namespace StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: a labeled face is alternating when its vertices can be
ordered by increasing unsigned label with alternating Boolean signs. -/
def IsAlternatingLabeledFace {V : Type*} {r ℓ : ℕ} (initial : Bool)
    (label : V → Fin ℓ × Bool) (face : Fin r → V) : Prop :=
  ∃ (vertexOrder : Equiv.Perm (Fin r)) (unsignedOrder : Fin r ↪o Fin ℓ),
    ∀ j, label (face (vertexOrder j)) =
      (unsignedOrder j, if Even j.1 then initial else !initial)

/-- Helper for Remark 50.3: the mod-two indicator of a labeled alternating face. -/
noncomputable def alternatingLabeledFaceWeight {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V) :
    ZMod 2 :=
  @ite (ZMod 2) (IsAlternatingLabeledFace initial label face)
    (Classical.dec _) 1 0

/-- Helper for Remark 50.3: the sign obtained after alternating `n` times from
an initial Boolean sign. -/
def fanAlternatingSignAt (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => !(fanAlternatingSignAt initial n)

/-- Helper for Remark 50.3: shifting a Fan alternating sign sequence toggles
its initial sign. -/
lemma fanAlternatingSignAt_succ (initial : Bool) (n : ℕ) :
    fanAlternatingSignAt initial (n + 1) = fanAlternatingSignAt (!initial) n := by
  -- Induct through the simultaneous sign toggles.
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [fanAlternatingSignAt] using congrArg Bool.not ih

/-- Helper for Remark 50.3: a Boolean tuple follows the prescribed Fan
alternating sign pattern. -/
def IsFanAlternatingSign {r : ℕ} (initial : Bool) (sign : Fin r → Bool) : Prop :=
  ∀ j, sign j = fanAlternatingSignAt initial j.1

/-- Helper for Remark 50.3: the mod-two indicator of a Fan alternating Boolean
tuple. -/
noncomputable def fanAlternatingSignWeight {r : ℕ} (initial : Bool)
    (sign : Fin r → Bool) : ZMod 2 :=
  @ite (ZMod 2) (IsFanAlternatingSign initial sign) (Classical.dec _) 1 0

/-- Helper for Remark 50.3: a sign tuple with a head alternates exactly when
the head is prescribed and the tail starts with the opposite sign. -/
lemma isFanAlternatingSign_cons_iff {r : ℕ} (initial head : Bool)
    (tail : Fin r → Bool) :
    IsFanAlternatingSign initial (Fin.cons head tail) ↔
      head = initial ∧ IsFanAlternatingSign (!initial) tail := by
  -- Read the head and then shift the remaining parity pattern once.
  constructor
  · intro halternating
    constructor
    · have hhead := halternating (0 : Fin (r + 1))
      change head = initial at hhead
      exact hhead
    · intro j
      simpa only [Fin.cons_succ, Fin.val_succ, fanAlternatingSignAt_succ] using
        halternating j.succ
  · rintro ⟨rfl, halternating⟩ j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simpa only [Fin.cons_succ, Fin.val_succ, fanAlternatingSignAt_succ] using
        halternating k

/-- Helper for Remark 50.3: the Fan weight of a tuple with a head reduces to
the opposite-initial weight of its tail. -/
lemma fanAlternatingSignWeight_cons {r : ℕ} (initial head : Bool)
    (tail : Fin r → Bool) :
    fanAlternatingSignWeight initial (Fin.cons head tail) =
      if head = initial then fanAlternatingSignWeight (!initial) tail else 0 := by
  -- Expand both indicators through the head-and-tail characterization.
  by_cases hhead : head = initial
  · subst head
    have hiff := isFanAlternatingSign_cons_iff initial initial tail
    by_cases htail : IsFanAlternatingSign (!initial) tail
    · have hcons : IsFanAlternatingSign initial (Fin.cons initial tail) :=
        hiff.mpr ⟨rfl, htail⟩
      simp [fanAlternatingSignWeight, htail, hcons]
    · have hcons : ¬IsFanAlternatingSign initial (Fin.cons initial tail) :=
        fun h ↦ htail (hiff.mp h).2
      simp [fanAlternatingSignWeight, htail, hcons]
  · have hcons : ¬IsFanAlternatingSign initial (Fin.cons head tail) :=
      fun h ↦ hhead ((isFanAlternatingSign_cons_iff initial head tail).mp h).1
    simp [fanAlternatingSignWeight, hhead, hcons]

/-- Helper for Remark 50.3: the boundary sum of Fan sign weights is the sum
of the two alternating orientations of the full sign tuple. -/
lemma sum_fanAlternatingSignWeight_omit (r : ℕ) (initial : Bool)
    (sign : Fin (r + 1) → Bool) :
    ∑ k : Fin (r + 1),
        fanAlternatingSignWeight initial (fun j ↦ sign (k.succAbove j)) =
      fanAlternatingSignWeight initial sign +
        fanAlternatingSignWeight (!initial) sign := by
  -- Peel off the first vertex and apply the induction hypothesis to the tail.
  induction r generalizing initial with
  | zero =>
      cases initial <;> cases hsign : sign 0 <;>
        simp [fanAlternatingSignWeight, IsFanAlternatingSign,
          fanAlternatingSignAt, hsign]
  | succ r ih =>
      let head := sign 0
      let tail := Fin.tail sign
      have hsign : sign = Fin.cons head tail := (Fin.cons_self_tail sign).symm
      rw [hsign, Fin.sum_univ_succ]
      have homitZero :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              ((0 : Fin (r + 2)).succAbove j)) = tail := by
        funext j
        simp only [Fin.zero_succAbove, Fin.cons_succ]
      have homitSucc (k : Fin (r + 1)) :
          (fun j : Fin (r + 1) ↦
            (Fin.cons head tail : Fin (r + 2) → Bool)
              (k.succ.succAbove j)) =
            Fin.cons head (fun j ↦ tail (k.succAbove j)) := by
        funext j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp only [Fin.succ_succAbove_zero, Fin.cons_zero]
        · simp only [Fin.succ_succAbove_succ, Fin.cons_succ]
      rw [homitZero]
      simp_rw [homitSucc, fanAlternatingSignWeight_cons]
      have hcharTwo (a b : ZMod 2) : a + (b + a) = b := by
        calc
          a + (b + a) = (a + a) + b := by ac_rfl
          _ = 0 + b := by rw [CharTwo.add_self_eq_zero]
          _ = b := zero_add b
      cases initial <;> cases head <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, ih]
      all_goals
        simp only [Finset.sum_const_zero, add_zero, zero_add, hcharTwo]

/-- Helper for Remark 50.3: `alternatingSignAt` is determined by the parity of
its index. -/
lemma alternatingSignAt_eq_ite_even (initial : Bool) (n : ℕ) :
    fanAlternatingSignAt initial n = if Even n then initial else !initial := by
  -- Each successor toggles both the parity test and the alternating sign.
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
      rw [fanAlternatingSignAt_succ, ih]
      by_cases hn : Even n
      · simp [Nat.even_add_one, hn]
      · simp [Nat.even_add_one, hn]

/-- Helper for Remark 50.3: an alternating labeled face has pairwise distinct
unsigned labels. -/
lemma IsAlternatingLabeledFace.unsignedLabel_injective
    {V : Type*} {r ℓ : ℕ} {initial : Bool} {label : V → Fin ℓ × Bool}
    {face : Fin r → V} (halternating :
      IsAlternatingLabeledFace initial label face) :
    Function.Injective (fun j ↦ (label (face j)).1) := by
  -- Transport equality into the stored increasing order, where injectivity is explicit.
  obtain ⟨vertexOrder, unsignedOrder, hlabels⟩ := halternating
  have hordered (j : Fin r) :
      (label (face (vertexOrder j))).1 = unsignedOrder j :=
    congrArg Prod.fst (hlabels j)
  intro j k hlabel
  apply vertexOrder.symm.injective
  apply unsignedOrder.injective
  calc
    unsignedOrder (vertexOrder.symm j) = (label (face j)).1 := by
      simpa only [vertexOrder.apply_symm_apply] using
        (hordered (vertexOrder.symm j)).symm
    _ = (label (face k)).1 := hlabel
    _ = unsignedOrder (vertexOrder.symm k) := by
      simpa only [vertexOrder.apply_symm_apply] using
        hordered (vertexOrder.symm k)

/-- Helper for Remark 50.3: reindexing the vertices of a face preserves the
alternating labeled-face predicate. -/
lemma isAlternatingLabeledFace_reindex {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V)
    (reindex : Equiv.Perm (Fin r)) :
    IsAlternatingLabeledFace initial label (fun j ↦ face (reindex j)) ↔
      IsAlternatingLabeledFace initial label face := by
  -- Compose the witnessing vertex order with the chosen reindexing permutation.
  constructor
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨reindex * vertexOrder, unsignedOrder, ?_⟩
    intro j
    simpa only [Equiv.Perm.mul_apply] using halternating j
  · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
    refine ⟨reindex.symm * vertexOrder, unsignedOrder, ?_⟩
    intro j
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using halternating j

/-- Helper for Remark 50.3: reindexing the vertices of a face preserves its
alternating labeled-face weight. -/
lemma alternatingLabeledFaceWeight_reindex {V : Type*} {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool) (face : Fin r → V)
    (reindex : Equiv.Perm (Fin r)) :
    alternatingLabeledFaceWeight initial label (fun j ↦ face (reindex j)) =
      alternatingLabeledFaceWeight initial label face := by
  -- Evaluate the two indicators through reindexing invariance.
  have hreindex := isAlternatingLabeledFace_reindex initial label face reindex
  by_cases halternating : IsAlternatingLabeledFace initial label face
  · have hreindexed := hreindex.mpr halternating
    simp [alternatingLabeledFaceWeight, halternating, hreindexed]
  · have hreindexed :
        ¬IsAlternatingLabeledFace initial label (fun j ↦ face (reindex j)) :=
      fun h ↦ halternating (hreindex.mp h)
    simp [alternatingLabeledFaceWeight, halternating, hreindexed]

/-- Helper for Remark 50.3: injective enumerations of the same unordered
finite face have the same alternating labeled-face weight. -/
private lemma alternatingLabeledFaceWeight_eq_of_injective_image_eq
    {V : Type*} [DecidableEq V] {r ℓ : ℕ}
    (initial : Bool) (label : V → Fin ℓ × Bool)
    (face₁ face₂ : Fin r → V) (hface₂ : Function.Injective face₂)
    (himage : Finset.univ.image face₁ = Finset.univ.image face₂) :
    alternatingLabeledFaceWeight initial label face₁ =
      alternatingLabeledFaceWeight initial label face₂ := by
  classical
  -- Match each vertex of the second enumeration with its unique preimage in
  -- the first enumeration, using equality of the unordered images.
  have hexists (j : Fin r) : ∃ i : Fin r, face₁ i = face₂ j := by
    have hmem : face₂ j ∈ Finset.univ.image face₁ := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i, hi⟩
  let reindex : Fin r → Fin r := fun j ↦ Classical.choose (hexists j)
  have hreindex_spec (j : Fin r) : face₁ (reindex j) = face₂ j := by
    exact Classical.choose_spec (hexists j)
  have hreindex_injective : Function.Injective reindex := by
    intro j k hjk
    apply hface₂
    rw [← hreindex_spec j, ← hreindex_spec k, hjk]
  let permutation : Equiv.Perm (Fin r) :=
    Equiv.ofBijective reindex
      ⟨hreindex_injective, Finite.surjective_of_injective hreindex_injective⟩
  have hfaces : (fun j ↦ face₁ (permutation j)) = face₂ := by
    funext j
    exact hreindex_spec j
  -- Reindexing invariance now transports the weight to the second enumeration.
  calc
    alternatingLabeledFaceWeight initial label face₁ =
        alternatingLabeledFaceWeight initial label
          (fun j ↦ face₁ (permutation j)) :=
      (alternatingLabeledFaceWeight_reindex initial label face₁ permutation).symm
    _ = alternatingLabeledFaceWeight initial label face₂ :=
      congrArg (alternatingLabeledFaceWeight initial label) hfaces

/-- Helper for Remark 50.3: a permutation preserves inequality from a chosen
omitted position. -/
lemma labeledPerm_ne_iff_image_ne {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x a : Fin (n + 1)) : a ≠ x ↔ p a ≠ p x := by
  -- Reflect equality through injectivity and negate both sides.
  exact p.injective.ne_iff.symm

/-- Helper for Remark 50.3: restricting a permutation to the complements of an
omitted point and its image gives a permutation of the remaining positions. -/
def labeledOmitPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1)) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv x).trans
    ((Equiv.subtypeEquiv p (labeledPerm_ne_iff_image_ne p x)).trans
      (finSuccAboveEquiv (p x)).symm)

/-- Helper for Remark 50.3: the restricted omission permutation makes deletion
commute with the original permutation. -/
lemma labeledOmitPerm_succAbove {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1)) (j : Fin n) :
    (p x).succAbove (labeledOmitPerm p x j) = p (x.succAbove j) := by
  -- Pass through the canonical equivalences with the two point complements.
  change ((finSuccAboveEquiv (p x)) (labeledOmitPerm p x j)).1 = _
  simp only [labeledOmitPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
    finSuccAboveEquiv_apply]
  rfl

/-- Helper for Remark 50.3: simultaneously permuting a face and its omitted
vertex leaves the total deletion weight unchanged. -/
lemma sum_alternatingLabeledFaceWeight_omit_reindex
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (reindex : Equiv.Perm (Fin (r + 1))) :
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
        (fun j ↦ face (reindex (k.succAbove j))) =
      ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) := by
  -- Identify every reindexed deletion with the corresponding original deletion.
  calc
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
          (fun j ↦ face (reindex (k.succAbove j))) =
        ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
          (fun j ↦ face ((reindex k).succAbove j)) := by
      apply Finset.sum_congr rfl
      intro k _
      have hface :
          (fun j ↦ face (reindex (k.succAbove j))) =
            fun j ↦ face ((reindex k).succAbove (labeledOmitPerm reindex k j)) := by
        funext j
        rw [labeledOmitPerm_succAbove]
      rw [hface]
      exact alternatingLabeledFaceWeight_reindex initial label
        (fun j ↦ face ((reindex k).succAbove j)) (labeledOmitPerm reindex k)
    _ = ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
          (fun j ↦ face (k.succAbove j)) :=
      by
        simpa only [] using Equiv.sum_comp reindex
          (fun k ↦ alternatingLabeledFaceWeight initial label
            (fun j ↦ face (k.succAbove j)))

/-- Helper for Remark 50.3: for a face already strictly ordered by unsigned
labels, its labeled weight is exactly the alternating sign weight. -/
lemma alternatingLabeledFaceWeight_eq_signWeight_of_strictMono
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin r → V)
    (hstrict : StrictMono (fun j ↦ (label (face j)).1)) :
    alternatingLabeledFaceWeight initial label face =
      fanAlternatingSignWeight initial (fun j ↦ (label (face j)).2) := by
  -- Strict ordering forces the witnessing vertex permutation to be the identity.
  have hiff : IsAlternatingLabeledFace initial label face ↔
      IsFanAlternatingSign initial (fun j ↦ (label (face j)).2) := by
    constructor
    · rintro ⟨vertexOrder, unsignedOrder, hlabels⟩
      have hordered (j : Fin r) :
          (label (face (vertexOrder j))).1 = unsignedOrder j :=
        congrArg Prod.fst (hlabels j)
      have hpermutedStrict :
          StrictMono ((fun j ↦ (label (face j)).1) ∘ vertexOrder) := by
        intro j k hjk
        simpa only [Function.comp_apply, hordered] using unsignedOrder.strictMono hjk
      have hsameOrder :
          (fun j ↦ (label (face j)).1) ∘ vertexOrder =
            (fun j ↦ (label (face j)).1) ∘ Equiv.refl _ :=
        Tuple.unique_monotone hpermutedStrict.monotone hstrict.monotone
      have hvertexOrder : vertexOrder = Equiv.refl _ := by
        apply Equiv.ext
        intro j
        apply hstrict.injective
        exact congrFun hsameOrder j
      intro j
      have hsign := congrArg Prod.snd (hlabels j)
      rw [hvertexOrder] at hsign
      simpa only [Equiv.refl_apply, alternatingSignAt_eq_ite_even] using hsign
    · intro hsign
      refine ⟨Equiv.refl _, OrderEmbedding.ofStrictMono _ hstrict, ?_⟩
      intro j
      apply Prod.ext
      · rfl
      · simpa only [Equiv.refl_apply, alternatingSignAt_eq_ite_even] using hsign j
  -- The equivalent propositions make the two characteristic functions equal.
  by_cases halternating : IsAlternatingLabeledFace initial label face
  · have hsign := hiff.mp halternating
    simp [alternatingLabeledFaceWeight, fanAlternatingSignWeight, halternating, hsign]
  · have hsign : ¬IsFanAlternatingSign initial (fun j ↦ (label (face j)).2) :=
      fun h ↦ halternating (hiff.mpr h)
    simp [alternatingLabeledFaceWeight, fanAlternatingSignWeight, halternating, hsign]

/-- Helper for Remark 50.3: the Fan coboundary identity holds when the full
face has pairwise distinct unsigned labels. -/
lemma sum_alternatingLabeledFaceWeight_omit_of_injective
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hinjective : Function.Injective (fun j ↦ (label (face j)).1)) :
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) =
      alternatingLabeledFaceWeight initial label face +
        alternatingLabeledFaceWeight (!initial) label face := by
  -- Sort once by unsigned label, reduce every term to signs, and apply the pure identity.
  let unsigned : Fin (r + 1) → Fin ℓ := fun j ↦ (label (face j)).1
  let reindex : Equiv.Perm (Fin (r + 1)) := Tuple.sort unsigned
  let sortedFace : Fin (r + 1) → V := fun j ↦ face (reindex j)
  have hsortedStrict : StrictMono (fun j ↦ (label (sortedFace j)).1) := by
    apply (Tuple.monotone_sort unsigned).strictMono_of_injective
    exact hinjective.comp reindex.injective
  have hdeletedStrict (k : Fin (r + 1)) :
      StrictMono (fun j ↦ (label (sortedFace (k.succAbove j))).1) := by
    exact hsortedStrict.comp (Fin.strictMono_succAbove k)
  calc
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
          (fun j ↦ face (k.succAbove j)) =
        ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
          (fun j ↦ sortedFace (k.succAbove j)) := by
      exact (sum_alternatingLabeledFaceWeight_omit_reindex
        initial label face reindex).symm
    _ = ∑ k : Fin (r + 1), fanAlternatingSignWeight initial
          (fun j ↦ (label (sortedFace (k.succAbove j))).2) := by
      apply Finset.sum_congr rfl
      intro k _
      exact alternatingLabeledFaceWeight_eq_signWeight_of_strictMono
        initial label _ (hdeletedStrict k)
    _ = fanAlternatingSignWeight initial (fun j ↦ (label (sortedFace j)).2) +
          fanAlternatingSignWeight (!initial) (fun j ↦ (label (sortedFace j)).2) :=
      by
        simpa only [] using sum_fanAlternatingSignWeight_omit r initial
          (fun j ↦ (label (sortedFace j)).2)
    _ = alternatingLabeledFaceWeight initial label sortedFace +
          alternatingLabeledFaceWeight (!initial) label sortedFace := by
      rw [alternatingLabeledFaceWeight_eq_signWeight_of_strictMono
        initial label sortedFace hsortedStrict,
        alternatingLabeledFaceWeight_eq_signWeight_of_strictMono
          (!initial) label sortedFace hsortedStrict]
    _ = alternatingLabeledFaceWeight initial label face +
          alternatingLabeledFaceWeight (!initial) label face := by
      rw [alternatingLabeledFaceWeight_reindex initial label face reindex,
        alternatingLabeledFaceWeight_reindex (!initial) label face reindex]

/-- Helper for Remark 50.3: equal signed labels at two vertices make their two
deletions simultaneously alternating. -/
lemma isAlternatingLabeledFace_omit_iff_of_eq_label
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (k l : Fin (r + 1))
    (hlabel : label (face l) = label (face k)) :
    IsAlternatingLabeledFace initial label (fun j ↦ face (l.succAbove j)) ↔
      IsAlternatingLabeledFace initial label (fun j ↦ face (k.succAbove j)) := by
  classical
  -- Swap the equal-label vertices and restrict the swap to the retained positions.
  let reindex : Equiv.Perm (Fin r) := labeledOmitPerm (Equiv.swap k l) l
  have hswapPointwise (j : Fin r) :
      label (face (l.succAbove j)) =
        label (face (k.succAbove (reindex j))) := by
    have hl_ne : l.succAbove j ≠ l := Fin.succAbove_ne l j
    have hcommute := labeledOmitPerm_succAbove (Equiv.swap k l) l j
    simp only [Equiv.swap_apply_right] at hcommute
    rw [hcommute]
    by_cases hjk : l.succAbove j = k
    · rw [hjk, Equiv.swap_apply_left]
      exact hlabel.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hjk hl_ne]
  have hcongr :
      IsAlternatingLabeledFace initial label (fun j ↦ face (l.succAbove j)) ↔
        IsAlternatingLabeledFace initial label
          (fun j ↦ face (k.succAbove (reindex j))) := by
    constructor
    · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
      refine ⟨vertexOrder, unsignedOrder, ?_⟩
      intro j
      exact (hswapPointwise (vertexOrder j)).symm.trans (halternating j)
    · rintro ⟨vertexOrder, unsignedOrder, halternating⟩
      refine ⟨vertexOrder, unsignedOrder, ?_⟩
      intro j
      exact (hswapPointwise (vertexOrder j)).trans (halternating j)
  exact hcongr.trans
    (isAlternatingLabeledFace_reindex initial label
      (fun j ↦ face (k.succAbove j)) reindex)

/-- Helper for Remark 50.3: if the full unsigned-label tuple is not injective,
an alternating deletion has a unique equal-label mate. -/
lemma existsUnique_equalLabel_of_omit_alternating
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V) (k : Fin (r + 1))
    (hsameSign : ∀ l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2)
    (hnoninjective : ¬Function.Injective (fun j ↦ (label (face j)).1))
    (halternating : IsAlternatingLabeledFace initial label
      (fun j ↦ face (k.succAbove j))) :
    ∃! l : Fin (r + 1), l ≠ k ∧ label (face l) = label (face k) := by
  -- Any collision must involve the omitted vertex because the retained labels are injective.
  have hretained : Function.Injective
      (fun j ↦ (label (face (k.succAbove j))).1) :=
    halternating.unsignedLabel_injective
  obtain ⟨a, b, hab, habne⟩ := Function.not_injective_iff.mp hnoninjective
  have haorb : a = k ∨ b = k := by
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne.1
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne.2
    have hretainedEq :
        (label (face (k.succAbove i))).1 =
          (label (face (k.succAbove j))).1 := by
      rw [hi, hj]
      exact hab
    have hij : i = j := hretained hretainedEq
    apply habne
    calc
      a = k.succAbove i := hi.symm
      _ = k.succAbove j := congrArg k.succAbove hij
      _ = b := hj
  rcases haorb with ha | hb
  · refine ⟨b, ?_, ?_⟩
    · have hbk : b ≠ k := by
        intro hbk
        exact habne (ha.trans hbk.symm)
      have hubk : (label (face b)).1 = (label (face k)).1 := by
        rw [← ha]
        exact hab.symm
      refine ⟨hbk, Prod.ext hubk ?_⟩
      exact hsameSign b hubk
    · rintro z ⟨hzk, hzlabel⟩
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hzk
      have hbk : b ≠ k := by
        intro hbk
        exact habne (ha.trans hbk.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hbk
      have hretainedEq :
          (label (face (k.succAbove i))).1 =
            (label (face (k.succAbove j))).1 := by
        rw [hi, hj]
        exact (congrArg Prod.fst hzlabel).trans
          ((congrArg (fun t ↦ (label (face t)).1) ha).symm.trans hab)
      have hij : i = j := hretained hretainedEq
      calc
        z = k.succAbove i := hi.symm
        _ = k.succAbove j := congrArg k.succAbove hij
        _ = b := hj
  · refine ⟨a, ?_, ?_⟩
    · have hak : a ≠ k := by
        intro hak
        exact habne (hak.trans hb.symm)
      have huak : (label (face a)).1 = (label (face k)).1 := by
        rw [← hb]
        exact hab
      refine ⟨hak, Prod.ext huak ?_⟩
      exact hsameSign a huak
    · rintro z ⟨hzk, hzlabel⟩
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hzk
      have hak : a ≠ k := by
        intro hak
        exact habne (hak.trans hb.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hak
      have hretainedEq :
          (label (face (k.succAbove i))).1 =
            (label (face (k.succAbove j))).1 := by
        rw [hi, hj]
        exact (congrArg Prod.fst hzlabel).trans
          ((congrArg (fun t ↦ (label (face t)).1) hb).symm.trans hab.symm)
      have hij : i = j := hretained hretainedEq
      calc
        z = k.succAbove i := hi.symm
        _ = k.succAbove j := congrArg k.succAbove hij
        _ = a := hj

/-- Helper for Remark 50.3: when unsigned labels repeat and equal unsigned
labels have equal signs, all alternating deletion weights cancel in pairs. -/
lemma sum_alternatingLabeledFaceWeight_omit_of_not_injective
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hsameSign : ∀ k l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2)
    (hnoninjective : ¬Function.Injective (fun j ↦ (label (face j)).1)) :
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) = 0 := by
  classical
  -- Filter to the alternating omissions and pair each with its unique equal-label mate.
  let omissions := Finset.univ.filter (fun k : Fin (r + 1) ↦
    IsAlternatingLabeledFace initial label (fun j ↦ face (k.succAbove j)))
  have hmateExists (k : Fin (r + 1)) (hk : k ∈ omissions) :
      ∃! l : Fin (r + 1), l ≠ k ∧ label (face l) = label (face k) := by
    apply existsUnique_equalLabel_of_omit_alternating
      initial label face k (hsameSign k) hnoninjective
    exact (Finset.mem_filter.mp hk).2
  let mate : ∀ k, k ∈ omissions → Fin (r + 1) :=
    fun k hk ↦ (hmateExists k hk).choose
  have hmateSpec (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate k hk ≠ k ∧ label (face (mate k hk)) = label (face k) :=
    (hmateExists k hk).choose_spec.1
  have hmateMem (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate k hk ∈ omissions := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply (isAlternatingLabeledFace_omit_iff_of_eq_label initial label face k
      (mate k hk) (hmateSpec k hk).2).mpr
    exact (Finset.mem_filter.mp hk).2
  have hmateInvolutive (k : Fin (r + 1)) (hk : k ∈ omissions) :
      mate (mate k hk) (hmateMem k hk) = k := by
    apply (hmateExists (mate k hk) (hmateMem k hk)).unique
    · exact hmateSpec (mate k hk) (hmateMem k hk)
    · exact ⟨(hmateSpec k hk).1.symm, (hmateSpec k hk).2.symm⟩
  simp only [alternatingLabeledFaceWeight, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  exact Finset.sum_involution (fun k hk ↦ mate k hk)
    (fun _ _ ↦ CharTwo.add_self_eq_zero 1)
    (fun k hk _ ↦ (hmateSpec k hk).1)
    hmateMem hmateInvolutive

/-- Helper for Remark 50.3: the mod-two sum of the alternating weights of all
vertex deletions is the sum of the two signed weights of the full face. -/
lemma sum_alternatingLabeledFaceWeight_omit
    {V : Type*} {r ℓ : ℕ} (initial : Bool) (label : V → Fin ℓ × Bool)
    (face : Fin (r + 1) → V)
    (hsameSign : ∀ k l, (label (face l)).1 = (label (face k)).1 →
      (label (face l)).2 = (label (face k)).2) :
    ∑ k : Fin (r + 1), alternatingLabeledFaceWeight initial label
        (fun j ↦ face (k.succAbove j)) =
      alternatingLabeledFaceWeight initial label face +
        alternatingLabeledFaceWeight (!initial) label face := by
  -- Distinct labels reduce to the sorted sign identity; repeated labels cancel by an involution.
  by_cases hinjective : Function.Injective (fun j ↦ (label (face j)).1)
  · exact sum_alternatingLabeledFaceWeight_omit_of_injective
      initial label face hinjective
  · have hfullInitial : alternatingLabeledFaceWeight initial label face = 0 := by
      rw [alternatingLabeledFaceWeight, if_neg]
      intro halternating
      exact hinjective halternating.unsignedLabel_injective
    have hfullOpposite : alternatingLabeledFaceWeight (!initial) label face = 0 := by
      rw [alternatingLabeledFaceWeight, if_neg]
      intro halternating
      exact hinjective halternating.unsignedLabel_injective
    rw [sum_alternatingLabeledFaceWeight_omit_of_not_injective
      initial label face hsameSign hinjective, hfullInitial, hfullOpposite, add_zero]

end StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: the singleton family has point multiplicity at most one. -/
lemma singletonCoverHasOrderLEOne (X : Type u) :
    (Set.range (Set.singleton : X → Set X)).HasOrderLE 1 := by
  -- Membership in two singletons through one point identifies their generators.
  rw [Set.hasOrderLE_iff]
  intro x
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro U hU V hV
  obtain ⟨u, rfl⟩ := hU.1
  obtain ⟨v, rfl⟩ := hV.1
  exact congrArg Set.singleton
    ((Set.mem_singleton_iff.mp hU.2).symm.trans (Set.mem_singleton_iff.mp hV.2))

/-- Helper for Remark 50.3: in a discrete space the singleton family openly refines
every cover of the whole space. -/
lemma discreteSingletonCoverIsOpenRefinement {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] {𝒜 : Set (Set X)} (hcover : ⋃₀ 𝒜 = Set.univ) :
    IsOpenRefinement (Set.range (Set.singleton : X → Set X)) 𝒜 := by
  -- Assign to each singleton any original cover member containing its point.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · intro B hB
    obtain ⟨x, rfl⟩ := hB
    obtain ⟨A, hA, hxA⟩ := Set.sUnion_eq_univ_iff.mp hcover x
    exact ⟨A, hA, Set.singleton_subset_iff.mpr hxA⟩
  · intro B _
    exact isOpen_discrete B

/-- Helper for Remark 50.3: every nonempty discrete space has covering dimension zero. -/
lemma coveringDimension_eq_zero_of_discrete (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] [Nonempty X] : dim X = 0 := by
  -- Singleton refinements first give the upper bound `dim X ≤ 0`.
  have hle : HasCoveringDimensionLE X 0 := by
    rw [hasCoveringDimensionLE_iff]
    intro 𝒜 _ hcover
    refine ⟨Set.range (Set.singleton : X → Set X),
      discreteSingletonCoverIsOpenRefinement hcover, ?_, ?_⟩
    · ext x
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        exact Set.mem_sUnion_of_mem (Set.mem_singleton x) ⟨x, rfl⟩
    · simpa only [Nat.zero_add] using singletonCoverHasOrderLEOne X
  apply le_antisymm
  · exact (coveringDimension_le_iff X 0).mpr hle
  · -- Nonemptiness excludes the only dimension strictly below zero, namely `⊥`.
    apply le_of_not_gt
    intro hnegative
    have hbot : dim X = ⊥ :=
      (WithBot.lt_zero_iff_eq_bot (dim X)).mp hnegative
    have hempty : IsEmpty X := (coveringDimension_eq_bot_iff X).mp hbot
    exact not_isEmpty_of_nonempty X hempty

/-- Helper for Remark 50.3: a Euclidean space embeds in every Euclidean space of
greater finite dimension. -/
lemma euclideanSpaceEmbeddingOfLE {N M : ℕ} (hNM : N ≤ M) :
    ∃ e : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin M),
      Topology.IsEmbedding e := by
  -- Write the larger dimension as a sum, then append zero coordinates.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  refine ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := k)).symm ∘
      fun x ↦ (x, 0), ?_⟩
  exact
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := k)).symm.toHomeomorph.isEmbedding.comp
      (isEmbedding_prodMkLeft (0 : EuclideanSpace ℝ (Fin k)))

/-- Helper for Remark 50.3: failure to embed in a Euclidean space persists in every
smaller finite dimension. -/
lemma notEuclideanEmbeddableOfLE {X : Type u} [TopologicalSpace X] {N M : ℕ}
    (hNM : N ≤ M)
    (hM : ¬ ∃ f : X → EuclideanSpace ℝ (Fin M), Topology.IsEmbedding f) :
    ¬ ∃ f : X → EuclideanSpace ℝ (Fin N), Topology.IsEmbedding f := by
  -- Compose a hypothetical small-dimensional embedding with zero-padding.
  rintro ⟨f, hf⟩
  obtain ⟨e, he⟩ := euclideanSpaceEmbeddingOfLE hNM
  exact hM ⟨e ∘ f, he.comp hf⟩

/-- Helper for Remark 50.3: a coordinate face of the ambient standard simplex. -/
private def barycentricSimplexFace (m : ℕ) (s : Finset (Fin (2 * m + 3))) :
    Set (stdSimplex ℝ (Fin (2 * m + 3))) :=
  {x | ∀ i, i ∉ s → x.1 i = 0}

/-- Helper for Remark 50.3: every coordinate face of the ambient standard simplex is closed. -/
private lemma barycentricSimplexFace_isClosed (m : ℕ) (s : Finset (Fin (2 * m + 3))) :
    IsClosed (barycentricSimplexFace m s) := by
  -- A face is the intersection of the zero sets of the omitted coordinates.
  have hcoordinate (i : Fin (2 * m + 3)) :
      IsClosed {x : stdSimplex ℝ (Fin (2 * m + 3)) | x.1 i = 0} :=
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  rw [barycentricSimplexFace, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  by_cases hi : i ∈ s
  · have heq :
        {x : stdSimplex ℝ (Fin (2 * m + 3)) | i ∉ s → x.1 i = 0} = Set.univ := by
      ext x
      simp [hi]
    rw [heq]
    exact isClosed_univ
  · have heq :
        {x : stdSimplex ℝ (Fin (2 * m + 3)) | i ∉ s → x.1 i = 0} =
          {x | x.1 i = 0} := by
      ext x
      simp [hi]
    rw [heq]
    exact hcoordinate i

/-- Helper for Remark 50.3: a coordinate face on at most `m + 1` vertices embeds in
`EuclideanSpace ℝ (Fin m)`. -/
private lemma barycentricSimplexFace_embedsEuclidean (m : ℕ)
    (s : Finset (Fin (2 * m + 3))) (hs : s.card ≤ m + 1) :
    ∃ e : barycentricSimplexFace m s → EuclideanSpace ℝ (Fin m),
      Topology.IsEmbedding e := by
  classical
  -- Closedness makes the face compact, so a continuous injection will be an embedding.
  letI : CompactSpace (barycentricSimplexFace m s) :=
    isCompact_iff_compactSpace.mp (barycentricSimplexFace_isClosed m s).isCompact
  by_cases hsne : s.Nonempty
  · obtain ⟨p, hp⟩ := hsne
    let coordinates : barycentricSimplexFace m s → EuclideanSpace ℝ ↥(s.erase p) :=
      fun x ↦ (EuclideanSpace.equiv ↥(s.erase p) ℝ).symm (fun i ↦ x.1.1 i.1)
    have hcoordinatesContinuous : Continuous coordinates := by
      apply (EuclideanSpace.equiv ↥(s.erase p) ℝ).symm.continuous.comp
      exact continuous_pi fun i ↦
        (continuous_apply i.1).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hcoordinatesInjective : Function.Injective coordinates := by
      intro x y hxy
      have hcoordinate (i : ↥(s.erase p)) : x.1.1 i.1 = y.1.1 i.1 := by
        have hi := congrFun
          (congrArg (EuclideanSpace.equiv ↥(s.erase p) ℝ) hxy) i
        simpa only [coordinates, ContinuousLinearEquiv.apply_symm_apply] using hi
      have haway (i : Fin (2 * m + 3)) (hip : i ≠ p) :
          x.1.1 i = y.1.1 i := by
        by_cases his : i ∈ s
        · exact hcoordinate ⟨i, Finset.mem_erase.mpr ⟨hip, his⟩⟩
        · rw [x.2 i his, y.2 i his]
      have hrest :
          (∑ i ∈ Finset.univ.erase p, x.1.1 i) =
            ∑ i ∈ Finset.univ.erase p, y.1.1 i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact haway i (Finset.mem_erase.mp hi).1
      have hxsum :
          (∑ i ∈ Finset.univ.erase p, x.1.1 i) + x.1.1 p = 1 := by
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ p)).trans
          (stdSimplex.sum_eq_one x.1)
      have hysum :
          (∑ i ∈ Finset.univ.erase p, y.1.1 i) + y.1.1 p = 1 := by
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ p)).trans
          (stdSimplex.sum_eq_one y.1)
      have hpcoordinate : x.1.1 p = y.1.1 p := by
        linarith
      apply Subtype.ext
      apply Subtype.ext
      funext i
      by_cases hip : i = p
      · simpa only [hip] using hpcoordinate
      · exact haway i hip
    have heraseCard : (s.erase p).card ≤ m := by
      rw [Finset.card_erase_of_mem hp]
      omega
    have hindexCard : Fintype.card ↥(s.erase p) ≤ m := by
      simpa only [Fintype.card_coe] using heraseCard
    obtain ⟨pad, hpad⟩ := euclideanSpaceEmbeddingOfLE hindexCard
    let reindex :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ↥(s.erase p))
    let faceMap : barycentricSimplexFace m s → EuclideanSpace ℝ (Fin m) :=
      pad ∘ reindex ∘ coordinates
    have hfaceMapContinuous : Continuous faceMap :=
      hpad.continuous.comp (reindex.continuous.comp hcoordinatesContinuous)
    have hfaceMapInjective : Function.Injective faceMap :=
      hpad.injective.comp (reindex.injective.comp hcoordinatesInjective)
    exact ⟨faceMap, (hfaceMapContinuous.isClosedEmbedding hfaceMapInjective).isEmbedding⟩
  · -- The face indexed by the empty vertex set has no simplex points.
    have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    have hfaceEmpty : IsEmpty (barycentricSimplexFace m s) := by
      constructor
      intro x
      have hzero (i : Fin (2 * m + 3)) : x.1.1 i = 0 := by
        have hi : i ∉ s := by simp [hsempty]
        exact x.2 i hi
      have hsum : ∑ i, x.1.1 i = 1 := stdSimplex.sum_eq_one x.1
      have hsumzero : ∑ i, x.1.1 i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact hzero i
      rw [hsumzero] at hsum
      norm_num at hsum
    let faceMap : barycentricSimplexFace m s → EuclideanSpace ℝ (Fin m) := fun _ ↦ 0
    have hfaceMapInjective : Function.Injective faceMap := by
      intro x _ _
      exact (hfaceEmpty.false x).elim
    exact ⟨faceMap, (continuous_const.isClosedEmbedding hfaceMapInjective).isEmbedding⟩

/-- Helper for Remark 50.3: every coordinate face with at most `m + 1` vertices has
covering dimension at most `m`. -/
private lemma barycentricSimplexFace_coveringDimensionLE (m : ℕ)
    (s : Finset (Fin (2 * m + 3))) (hs : s.card ≤ m + 1) :
    HasCoveringDimensionLE (barycentricSimplexFace m s) m := by
  classical
  -- Embed the compact face into a stereographic chart of the standard `m`-sphere.
  letI : CompactSpace (barycentricSimplexFace m s) :=
    isCompact_iff_compactSpace.mp (barycentricSimplexFace_isClosed m s).isCompact
  obtain ⟨e, he⟩ := barycentricSimplexFace_embedsEuclidean m s hs
  letI : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnonnegative : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨pole, hpole⟩ :=
    (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (m + 1)))).mpr hnonnegative
  let sphereType := Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
  let p : sphereType := ⟨pole, hpole⟩
  let chart : EuclideanSpace ℝ (Fin m) → sphereType :=
    (stereographic' m p).symm
  have hchart : Topology.IsOpenEmbedding chart := by
    apply (stereographic' m p).symm.to_isOpenEmbedding
    exact stereographic'_target p
  let faceMap : barycentricSimplexFace m s → sphereType := chart ∘ e
  have hfaceMap : Topology.IsEmbedding faceMap := hchart.isEmbedding.comp he
  have hclosedRange : IsClosed (Set.range faceMap) :=
    (isCompact_range hfaceMap.continuous).isClosed
  letI : TopologicalManifold m sphereType :=
    TopologicalManifold.of m inferInstance inferInstance
  have hrange : HasCoveringDimensionLE (Set.range faceMap) m :=
    (compactManifold_coveringDimension_le (M := sphereType)).closedSubtype hclosedRange
  -- The embedding identifies the face with its closed range in the sphere.
  exact hrange.homeomorph hfaceMap.toHomeomorph.symm

/-- Helper for Remark 50.3: the `m`-skeleton consists of simplex points supported on at
most `m + 1` vertices. -/
private def barycentricSimplexSkeletonSet (m : ℕ) :
    Set (stdSimplex ℝ (Fin (2 * m + 3))) :=
  {x | Set.encard {i | x.1 i ≠ 0} ≤ m + 1}

/-- Helper for Remark 50.3: the barycentric simplex skeleton is the finite union of its
coordinate faces. -/
private lemma barycentricSimplexSkeletonSet_eq_iUnion_faces (m : ℕ) :
    barycentricSimplexSkeletonSet m =
      ⋃ s : {s : Finset (Fin (2 * m + 3)) // s.card ≤ m + 1},
        barycentricSimplexFace m s.1 := by
  classical
  -- Choose the finite support itself for the forward inclusion and compare
  -- supports by cardinality for the reverse inclusion.
  ext x
  constructor
  · intro hx
    let support : Set (Fin (2 * m + 3)) := {i | x.1 i ≠ 0}
    have hsupport : support.Finite := Set.toFinite support
    have hcard : hsupport.toFinset.card ≤ m + 1 := by
      have hx' : Set.encard support ≤ m + 1 := hx
      rw [hsupport.encard_eq_coe_toFinset_card] at hx'
      exact_mod_cast hx'
    rw [Set.mem_iUnion]
    refine ⟨⟨hsupport.toFinset, hcard⟩, ?_⟩
    intro i hi
    by_contra hne
    exact hi (by simpa [support] using hne)
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨s, hs⟩ := hx
    have hsupport_subset : {i | x.1 i ≠ 0} ⊆ (s.1 : Set (Fin (2 * m + 3))) := by
      intro i hi
      by_contra his
      exact hi (hs i his)
    have hencard := Set.encard_mono hsupport_subset
    rw [barycentricSimplexSkeletonSet]
    calc
      Set.encard {i | x.1 i ≠ 0} ≤ Set.encard (s.1 : Set (Fin (2 * m + 3))) := hencard
      _ = s.1.card := Set.encard_coe_eq_coe_finsetCard s.1
      _ ≤ m + 1 := by exact_mod_cast s.2

/-- Helper for Remark 50.3: the barycentric simplex skeleton is a closed subspace of the
ambient standard simplex. -/
private lemma barycentricSimplexSkeletonSet_isClosed (m : ℕ) :
    IsClosed (barycentricSimplexSkeletonSet m) := by
  -- The face decomposition turns closedness into a finite-union calculation.
  rw [barycentricSimplexSkeletonSet_eq_iUnion_faces]
  exact isClosed_iUnion_of_finite fun s ↦ barycentricSimplexFace_isClosed m s.1

/-- Helper for Remark 50.3: the universe-lifted `m`-skeleton of the standard simplex on
`2 * m + 3` vertices. -/
private abbrev barycentricSimplexSkeleton (m : ℕ) : Type u :=
  ULift.{u} (barycentricSimplexSkeletonSet m)

/-- Helper for Remark 50.3: disjointly supported points of the ambient simplex cannot
both lie outside its `m`-skeleton. -/
private lemma disjointSimplexSupports_one_memSkeleton (m : ℕ)
    (x y : stdSimplex ℝ (Fin (2 * m + 3)))
    (hdisjoint : Disjoint {i | x.1 i ≠ 0} {i | y.1 i ≠ 0}) :
    x ∈ barycentricSimplexSkeletonSet m ∨ y ∈ barycentricSimplexSkeletonSet m := by
  classical
  -- If both supports were too large, their disjoint union would have more vertices
  -- than the ambient simplex.
  by_contra houtside
  have hxoutside : x ∉ barycentricSimplexSkeletonSet m := fun hx ↦ houtside (Or.inl hx)
  have hyoutside : y ∉ barycentricSimplexSkeletonSet m := fun hy ↦ houtside (Or.inr hy)
  let sx : Finset (Fin (2 * m + 3)) := Finset.univ.filter fun i ↦ x.1 i ≠ 0
  let sy : Finset (Fin (2 * m + 3)) := Finset.univ.filter fun i ↦ y.1 i ≠ 0
  have hsx : (sx : Set (Fin (2 * m + 3))) = {i | x.1 i ≠ 0} := by
    ext i
    simp only [sx, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
  have hsy : (sy : Set (Fin (2 * m + 3))) = {i | y.1 i ≠ 0} := by
    ext i
    simp only [sy, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
  have hsxLarge : m + 2 ≤ sx.card := by
    have hnot : ¬ sx.card ≤ m + 1 := by
      intro hcard
      apply hxoutside
      change Set.encard {i | x.1 i ≠ 0} ≤ m + 1
      rw [← hsx, Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hcard
    omega
  have hsyLarge : m + 2 ≤ sy.card := by
    have hnot : ¬ sy.card ≤ m + 1 := by
      intro hcard
      apply hyoutside
      change Set.encard {i | y.1 i ≠ 0} ≤ m + 1
      rw [← hsy, Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hcard
    omega
  have hfinsetDisjoint : Disjoint sx sy := by
    rw [Finset.disjoint_left]
    intro i hix hiy
    apply Set.disjoint_left.mp hdisjoint
    · simpa only [← hsx, Finset.mem_coe] using hix
    · simpa only [← hsy, Finset.mem_coe] using hiy
  have hunionCard : sx.card + sy.card ≤ 2 * m + 3 := by
    calc
      sx.card + sy.card = (sx ∪ sy).card :=
        (Finset.card_union_of_disjoint hfinsetDisjoint).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 * m + 3 := Fintype.card_fin (2 * m + 3)
  omega

/-- Helper for Remark 50.3: the topological Radon coincidence statement needed for the
constraint argument on the simplex with `2 * m + 3` vertices. -/
private def HasTopologicalRadonCoincidence (m : ℕ) : Prop :=
  ∀ g : C(stdSimplex ℝ (Fin (2 * m + 3)), EuclideanSpace ℝ (Fin (2 * m + 1))),
    ∃ x y,
      g x = g y ∧ Disjoint {i | x.1 i ≠ 0} {i | y.1 i ≠ 0}

/-- Helper for Remark 50.3: the sphere parametrizing the Radon decomposition. -/
private abbrev radonParameterSphere (m : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 2))) 1

/-- Helper for Remark 50.3: the standard `n`-sphere used in the Borsuk--Ulam reduction. -/
private abbrev sharpStandardSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Remark 50.3: the closed unit ball bounded by `sharpStandardSphere n`. -/
private abbrev sharpClosedUnitBall (n : ℕ) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Remark 50.3: every point of the standard sphere belongs to its closed ball. -/
private lemma sharpStandardSphere_mem_closedUnitBall {n : ℕ}
    (x : sharpStandardSphere n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- The unit sphere is contained in the corresponding closed unit ball.
  exact Metric.sphere_subset_closedBall x.property

/-- Helper for Remark 50.3: the canonical inclusion of the standard sphere into its ball. -/
private def sharpSphereToBall (n : ℕ) :
    C(sharpStandardSphere n, sharpClosedUnitBall n) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

/-- Helper for Remark 50.3: the sphere-to-ball inclusion preserves the ambient vector. -/
private lemma sharpSphereToBall_apply (n : ℕ) (x : sharpStandardSphere n) :
    (sharpSphereToBall n x : EuclideanSpace ℝ (Fin (n + 1))) = x := by
  -- The inclusion changes only the proof of membership.
  rfl

/-- Helper for Remark 50.3: radial projection of a continuous nonvanishing map is continuous. -/
private lemma continuous_sharpRadialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) :
    Continuous (fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1) := by
  -- Lift to the punctured space and then use its radial-coordinate homeomorphism.
  fun_prop

/-- Helper for Remark 50.3: the radial direction of a continuous nonvanishing map. -/
private noncomputable def sharpRadialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) :
    C(X, Metric.sphere (0 : E) 1) :=
  ⟨fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1,
    continuous_sharpRadialDirection F hF⟩

/-- Helper for Remark 50.3: radial direction is the normalized ambient vector. -/
private lemma sharpRadialDirection_coe {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) (x : X) :
    (sharpRadialDirection F hF x : E) = ‖F x‖⁻¹ • F x := by
  -- Use the first-coordinate computation rule for radial coordinates.
  exact homeomorphUnitSphereProd_apply_fst_coe E ⟨F x, hF x⟩

/-- Helper for Remark 50.3: radial projection preserves oddness. -/
private lemma sharpRadialDirection_odd {X E : Type*} [TopologicalSpace X] [Neg X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E))
    (hFodd : Function.Odd F) : Function.Odd (sharpRadialDirection F hF) := by
  -- Normalization commutes with negation because the norm is even.
  intro x
  apply Subtype.ext
  calc
    (sharpRadialDirection F hF (-x) : E) = ‖F (-x)‖⁻¹ • F (-x) :=
      sharpRadialDirection_coe F hF (-x)
    _ = -(‖F x‖⁻¹ • F x) := by rw [hFodd, norm_neg, smul_neg]
    _ = -(sharpRadialDirection F hF x : E) :=
      congrArg Neg.neg (sharpRadialDirection_coe F hF x).symm
    _ = ((-(sharpRadialDirection F hF x) : Metric.sphere (0 : E) 1) : E) := rfl

/-- Helper for Remark 50.3: the antipodal difference of a continuous map is continuous. -/
private lemma continuous_sharpAntipodalDifference {n : ℕ}
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    Continuous (fun x ↦ f x - f (-x)) := by
  -- Evaluation and antipodal evaluation are continuous, so their difference is continuous.
  fun_prop

/-- Helper for Remark 50.3: package the antipodal difference as a continuous map. -/
private noncomputable def sharpAntipodalDifference {n : ℕ}
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ f x - f (-x), continuous_sharpAntipodalDifference f⟩

/-- Helper for Remark 50.3: evaluate the packaged antipodal difference. -/
private lemma sharpAntipodalDifference_apply {n : ℕ}
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))))
    (x : sharpStandardSphere (n + 1)) :
    sharpAntipodalDifference f x = f x - f (-x) := by
  -- This is the defining computation rule.
  rfl

/-- Helper for Remark 50.3: the antipodal difference is odd. -/
private lemma sharpAntipodalDifference_odd {n : ℕ}
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    Function.Odd (sharpAntipodalDifference f) := by
  -- Interchanging the antipodal pair reverses the subtraction.
  intro x
  rw [sharpAntipodalDifference_apply, sharpAntipodalDifference_apply, neg_neg, neg_sub]

/-- Helper for Remark 50.3: separating all antipodal pairs produces an odd map
from `S^(n+1)` to `S^n`. -/
private lemma existsOddSharpSphereMap_of_antipodal_ne {n : ℕ}
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))))
    (hne : ∀ x, f x ≠ f (-x)) :
    ∃ g : C(sharpStandardSphere (n + 1), sharpStandardSphere n), Function.Odd g := by
  -- The nonzero antipodal difference can be normalized radially.
  have hdifference : ∀ x, sharpAntipodalDifference f x ∈
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, sharpAntipodalDifference_apply]
    exact sub_ne_zero.mpr (hne x)
  exact ⟨sharpRadialDirection (sharpAntipodalDifference f) hdifference,
    sharpRadialDirection_odd (sharpAntipodalDifference f) hdifference
      (sharpAntipodalDifference_odd f)⟩

/-- Helper for Remark 50.3: adjoin one leading real coordinate to a Euclidean vector. -/
private noncomputable def sharpPrependCoordinate {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
    (Fin.cons c (EuclideanSpace.equiv (Fin (n + 1)) ℝ v))

/-- Helper for Remark 50.3: adjoining a coordinate adds its square to the squared norm. -/
private lemma sharpPrependCoordinate_norm_sq {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖sharpPrependCoordinate c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  -- Ordinary Euclidean coordinates split the norm sum at the new first coordinate.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp [sharpPrependCoordinate]

/-- Helper for Remark 50.3: adjoining a leading coordinate commutes with negation. -/
private lemma sharpPrependCoordinate_neg {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpPrependCoordinate (-c) (-v) = -sharpPrependCoordinate c v := by
  -- Compare the ordinary coordinate functions pointwise.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).injective
  simp only [sharpPrependCoordinate, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Helper for Remark 50.3: adjoining varying leading and trailing coordinates is continuous. -/
private lemma continuous_sharpPrependCoordinate {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      sharpPrependCoordinate p.1 p.2) := by
  -- Check the leading and tail coordinates after applying the Euclidean equivalence.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous.comp continuous_snd)

/-- Helper for Remark 50.3: the upper-hemisphere radicand is nonnegative on the unit ball. -/
private lemma sharpUpperHemisphere_radicand_nonneg {n : ℕ}
    (y : sharpClosedUnitBall n) :
    0 ≤ 1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
  -- Ball membership bounds the norm by one.
  have hynorm : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using Metric.mem_closedBall.mp y.property
  nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin (n + 1)))]

/-- Helper for Remark 50.3: the upper-hemisphere formula has unit norm. -/
private lemma sharpUpperHemispherePoint_mem_sphere {n : ℕ}
    (y : sharpClosedUnitBall n) :
    sharpPrependCoordinate
        (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y ∈
      sharpStandardSphere (n + 1) := by
  -- The leading square is exactly the deficit in the squared norm of `y`.
  rw [mem_sphere_zero_iff_norm]
  have hone : (0 : ℝ) ≤ 1 := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) hone).mp
  rw [sharpPrependCoordinate_norm_sq,
    Real.sq_sqrt (sharpUpperHemisphere_radicand_nonneg y)]
  ring

/-- Helper for Remark 50.3: the upper-hemisphere point varies continuously. -/
private lemma continuous_sharpUpperHemispherePoint (n : ℕ) :
    Continuous (fun y : sharpClosedUnitBall n ↦
      (⟨sharpPrependCoordinate
          (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
        sharpUpperHemispherePoint_mem_sphere y⟩ : sharpStandardSphere (n + 1))) := by
  -- Assemble the continuous height and ambient ball coordinate.
  have hheight : Continuous (fun y : sharpClosedUnitBall n ↦
      Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) := by
    fun_prop
  have hvector : Continuous (fun y : sharpClosedUnitBall n ↦
      (y : EuclideanSpace ℝ (Fin (n + 1)))) := continuous_subtype_val
  exact Continuous.subtype_mk
    (continuous_sharpPrependCoordinate.comp (hheight.prodMk hvector)) _

/-- Helper for Remark 50.3: the upper hemisphere extends the standard equator over the ball. -/
private noncomputable def sharpUpperHemisphere (n : ℕ) :
    C(sharpClosedUnitBall n, sharpStandardSphere (n + 1)) :=
  ⟨fun y ↦ ⟨sharpPrependCoordinate
      (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
    sharpUpperHemispherePoint_mem_sphere y⟩, continuous_sharpUpperHemispherePoint n⟩

/-- Helper for Remark 50.3: the standard equator is the boundary of the upper hemisphere. -/
private noncomputable def sharpEquator (n : ℕ) :
    C(sharpStandardSphere n, sharpStandardSphere (n + 1)) :=
  (sharpUpperHemisphere n).comp (sharpSphereToBall n)

/-- Helper for Remark 50.3: the standard equator has zero leading coordinate. -/
private lemma sharpEquator_coe (n : ℕ) (x : sharpStandardSphere n) :
    (sharpEquator n x : EuclideanSpace ℝ (Fin (n + 2))) =
      sharpPrependCoordinate 0 x := by
  -- On the boundary the upper-hemisphere height is zero.
  rw [sharpEquator, ContinuousMap.comp_apply]
  simp only [sharpUpperHemisphere, ContinuousMap.coe_mk, sharpSphereToBall_apply]
  congr 1
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow, sub_self, Real.sqrt_zero]

/-- Helper for Remark 50.3: the standard equator preserves antipodes. -/
private lemma sharpEquator_odd (n : ℕ) : Function.Odd (sharpEquator n) := by
  -- The zero-leading-coordinate formula commutes with ambient negation.
  intro x
  apply Subtype.ext
  calc
    (sharpEquator n (-x) : EuclideanSpace ℝ (Fin (n + 2))) =
        sharpPrependCoordinate 0 (-x) := sharpEquator_coe n (-x)
    _ = sharpPrependCoordinate 0 (-(x : EuclideanSpace ℝ (Fin (n + 1)))) := by
      congr 1
    _ = -sharpPrependCoordinate 0 x := by
      rw [← sharpPrependCoordinate_neg, neg_zero]
    _ = -(sharpEquator n x : EuclideanSpace ℝ (Fin (n + 2))) :=
      congrArg Neg.neg (sharpEquator_coe n x).symm
    _ = ((-(sharpEquator n x) : sharpStandardSphere (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 2))) := rfl

/-- Helper for Remark 50.3: the standard equator is nullhomotopic. -/
private lemma sharpEquator_nullhomotopic (n : ℕ) :
    (sharpEquator n).Nullhomotopic := by
  -- Extend over the contractible closed unit ball and restrict to its boundary.
  have hone : (0 : ℝ) ≤ 1 := by positivity
  letI : ContractibleSpace (sharpClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall hone
  have hinclusion : (sharpSphereToBall n).Nullhomotopic :=
    (id_nullhomotopic (sharpClosedUnitBall n)).comp_left (sharpSphereToBall n)
  exact hinclusion.comp_right (sharpUpperHemisphere n)

/-- Helper for Remark 50.3: a constant weight on a finite fiber of size one or
two contributes its representative weight on a boundary fiber and zero otherwise. -/
private lemma sum_fiber_eq_of_card_one_or_two
    {α β : Type*} [Fintype α] [DecidableEq β]
    (fiberMap : α → β) (representative : β → α)
    (hrepresentative : ∀ b, fiberMap (representative b) = b)
    (boundary : β → Prop)
    [DecidablePred boundary]
    (hcard : ∀ b, Nat.card {a // fiberMap a = b} =
      if boundary b then 1 else 2)
    (weight : α → ZMod 2)
    (hweight : ∀ a c, fiberMap a = fiberMap c → weight a = weight c)
    (b : β) :
    (∑ a : {a // fiberMap a = b}, weight a) =
      if boundary b then weight (representative b) else 0 := by
  -- The singleton boundary fiber is represented by the chosen value.
  by_cases hb : boundary b
  · have hcardOne : Nat.card {a // fiberMap a = b} = 1 := by
      simpa only [hb, if_true] using hcard b
    have hsubsingleton : Subsingleton {a // fiberMap a = b} :=
      (Nat.card_eq_one_iff_unique.mp hcardOne).1
    letI : Subsingleton {a // fiberMap a = b} := hsubsingleton
    have hrepresentativeB : fiberMap (representative b) = b :=
      hrepresentative b
    let fiberRepresentative : {a // fiberMap a = b} :=
      ⟨representative b, hrepresentativeB⟩
    rw [if_pos hb]
    exact Fintype.sum_subsingleton
      (fun a : {a // fiberMap a = b} ↦ weight a.1) fiberRepresentative
  · -- On an interior fiber the two equal weights cancel in characteristic two.
    have hcardTwo : Nat.card {a // fiberMap a = b} = 2 := by
      simpa only [hb, if_false] using hcard b
    rw [if_neg hb]
    calc
      (∑ a : {a // fiberMap a = b}, weight a) =
          ∑ _a : {a // fiberMap a = b}, weight (representative b) := by
        apply Fintype.sum_congr
        intro a
        exact hweight a (representative b)
          (a.property.trans (hrepresentative b).symm)
      _ = Fintype.card {a // fiberMap a = b} • weight (representative b) := by
        simp only [Finset.sum_const, Finset.card_univ]
      _ = 2 • weight (representative b) := by
        rw [Fintype.card_eq_nat_card, hcardTwo]
      _ = weight (representative b) + weight (representative b) := two_nsmul _
      _ = 0 := CharTwo.add_self_eq_zero (weight (representative b))

/-- Helper for Remark 50.3: modulo two, a finite map with singleton boundary
fibers and two-element interior fibers has total weight equal to its boundary sum. -/
private lemma sum_eq_sum_boundary_of_fiber_card
    {α β : Type*} [Fintype α] [Fintype β]
    (fiberMap : α → β) (representative : β → α)
    (hrepresentative : ∀ b, fiberMap (representative b) = b)
    (boundary : β → Prop)
    [DecidablePred boundary]
    (hcard : ∀ b, Nat.card {a // fiberMap a = b} =
      if boundary b then 1 else 2)
    (weight : α → ZMod 2)
    (hweight : ∀ a c, fiberMap a = fiberMap c → weight a = weight c) :
    ∑ a, weight a = ∑ b with boundary b, weight (representative b) := by
  classical
  -- Partition the total sum into fibers and apply the one-or-two fiber formula.
  calc
    ∑ a, weight a =
        ∑ b, ∑ a : {a // fiberMap a = b}, weight a :=
      (Fintype.sum_fiberwise fiberMap weight).symm
    _ = ∑ b, if boundary b then weight (representative b) else 0 := by
      apply Fintype.sum_congr
      intro b
      exact sum_fiber_eq_of_card_one_or_two fiberMap representative
        hrepresentative boundary hcard weight hweight b
    _ = ∑ b with boundary b, weight (representative b) :=
      (Finset.sum_filter boundary (fun b ↦ weight (representative b))).symm

/-- Helper for Remark 50.3: the canonical staircase enumeration of a shared
cubical facet has no repeated vertices. -/
private lemma sharedFacet_vertex_injective {d m : ℕ}
    (facet : StandardSphere.CubicalTucker.SharedFacet d m) :
    Function.Injective facet.vertex := by
  -- A later vertex has crossed the active coordinate occupying its own rank,
  -- while every earlier vertex has not yet crossed that coordinate.
  have hseparate (j k : Fin (d + 1)) (hjk : j.1 < k.1) :
      facet.vertex j ≠ facet.vertex k := by
    have hkzero : k ≠ 0 := by
      intro hk
      subst k
      simp at hjk
    have hactive : facet.leadingOrder k ≠ facet.fixed := by
      intro hfixed
      apply hkzero
      apply facet.leadingOrder.injective
      exact hfixed.trans facet.leadingOrder_zero.symm
    intro heq
    have hcoordinate := congrArg
      (fun v : StandardSphere.CenteredGrid (d + 1) m ↦
        (v (facet.leadingOrder k)).1) heq
    rw [facet.vertex_value j, facet.vertex_value k] at hcoordinate
    simp only [hactive, if_false, facet.leadingOrder.symm_apply_apply] at hcoordinate
    have hbefore : ¬k.1 < j.1 + 1 := by omega
    have hafter : k.1 < k.1 + 1 := by omega
    rw [if_neg hbefore, if_pos hafter] at hcoordinate
    omega
  intro j k heq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hjk | hkj
  · exact hseparate j k hjk heq
  · exact hseparate k j hkj heq.symm

/-- Helper for Remark 50.3: deleting one index from an injective enumeration
of `d + 1` vertices leaves exactly `d` distinct vertices. -/
private lemma finsetImage_succAbove_card {V : Type*} [DecidableEq V] {d : ℕ}
    (vertex : Fin (d + 1) → V) (hvertex : Function.Injective vertex)
    (omitted : Fin (d + 1)) :
    (Finset.univ.image (fun j ↦ vertex (omitted.succAbove j))).card = d := by
  -- Both the deletion embedding and the original vertex enumeration are
  -- injective, so the image has the cardinality of `Fin d`.
  have hinjective : Function.Injective
      (fun j ↦ vertex (omitted.succAbove j)) :=
    hvertex.comp Fin.succAbove_right_injective
  calc
    (Finset.univ.image (fun j ↦ vertex (omitted.succAbove j))).card =
        (Finset.univ : Finset (Fin d)).card :=
      Finset.card_image_of_injective Finset.univ hinjective
    _ = d := Fintype.card_fin d

/-- Helper for Remark 50.3: for an injective finite vertex enumeration, its
unordered deletion image uniquely determines the omitted index. -/
private lemma finsetImage_succAbove_injective {V : Type*} [DecidableEq V]
    {d : ℕ} (vertex : Fin (d + 1) → V)
    (hvertex : Function.Injective vertex) :
    Function.Injective
      (fun omitted : Fin (d + 1) ↦ Finset.univ.image
        (fun j ↦ vertex (omitted.succAbove j))) := by
  -- If two omitted indices differ, the first omitted vertex occurs in the
  -- second deletion image but cannot occur in its own deletion image.
  intro omitted₁ omitted₂ himage
  by_contra hne
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  have hmem₂ : vertex omitted₁ ∈
      Finset.univ.image (fun k ↦ vertex (omitted₂.succAbove k)) := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, congrArg vertex hj⟩
  have himage' :
      Finset.univ.image (fun k ↦ vertex (omitted₁.succAbove k)) =
        Finset.univ.image (fun k ↦ vertex (omitted₂.succAbove k)) :=
    himage
  have hmem₁ : vertex omitted₁ ∈
      Finset.univ.image (fun k ↦ vertex (omitted₁.succAbove k)) := by
    rw [himage']
    exact hmem₂
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem₁
  exact Fin.succAbove_ne omitted₁ k (hvertex hk)

/-- Helper for Remark 50.3: the canonical vertex enumeration of a boundary
shared facet is injective. -/
private lemma boundarySharedFacet_vertex_injective {d m : ℕ}
    (facet : StandardSphere.CubicalTucker.BoundarySharedFacet d m) :
    Function.Injective facet.vertex := by
  -- Forget the boundary-side tag and use injectivity of the underlying shared facet.
  exact facet.vertex_injective

/-- Helper for Remark 50.3: the retained vertex enumeration of a positive
hemisphere ridge occurrence is injective. -/
private lemma positiveHemisphereFaceOccurrence_vertex_injective {d m : ℕ}
    (occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m) :
    Function.Injective occurrence.vertex := by
  -- A ridge enumeration is the injective facet enumeration after `Fin.succAbove`.
  intro j k heq
  have hsucceq :
      occurrence.omitted.succAbove j = occurrence.omitted.succAbove k := by
    apply boundarySharedFacet_vertex_injective occurrence.facet.1
    rw [← occurrence.vertex_eq_facetVertex j,
      ← occurrence.vertex_eq_facetVertex k]
    exact heq
  exact Fin.succAbove_right_injective hsucceq

/-- Helper for Remark 50.3: a positive-hemisphere ridge is an unordered
vertex set presented by at least one positive boundary-facet occurrence. -/
private abbrev PositiveHemisphereRidge (d m : ℕ) :=
  {ridge : Finset (StandardSphere.CenteredGrid (d + 1) m) //
    ∃ occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m,
      occurrence.ridgeVertexSet = ridge}

/-- Helper for Remark 50.3: every occurrence's ridge set is represented by
that occurrence. -/
private lemma positiveHemisphereRidge_mem_range {d m : ℕ}
    (occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m) :
    ∃ presentation : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m,
      presentation.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- Use the occurrence itself as the presentation.
  exact ⟨occurrence, rfl⟩

/-- Helper for Remark 50.3: send a positive boundary-facet occurrence to its
underlying unordered ridge. -/
private def positiveHemisphereRidgeKey {d m : ℕ}
    (occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m) :
    PositiveHemisphereRidge d m :=
  ⟨occurrence.ridgeVertexSet, positiveHemisphereRidge_mem_range occurrence⟩

/-- Helper for Remark 50.3: the underlying vertex set of an occurrence's
ridge key is its unordered ridge vertex set. -/
private lemma positiveHemisphereRidgeKey_val {d m : ℕ}
    (occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m) :
    (positiveHemisphereRidgeKey occurrence).1 = occurrence.ridgeVertexSet := by
  -- Expose the key projection without unfolding it at later transport points.
  rfl

/-- Helper for Remark 50.3: choose one occurrence presenting each unordered
positive-hemisphere ridge. -/
private noncomputable def positiveHemisphereRidgeRepresentative {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m :=
  Classical.choose ridge.2

/-- Helper for Remark 50.3: the chosen ridge occurrence presents exactly the
stored unordered vertex set. -/
private lemma positiveHemisphereRidgeRepresentative_spec {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    (positiveHemisphereRidgeRepresentative ridge).ridgeVertexSet = ridge.1 := by
  -- This is the specification supplied by the range witness.
  exact Classical.choose_spec ridge.2

/-- Helper for Remark 50.3: the chosen occurrence maps back to its stored
unordered positive-hemisphere ridge. -/
private lemma positiveHemisphereRidgeRepresentative_key {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    positiveHemisphereRidgeKey
      (positiveHemisphereRidgeRepresentative ridge) = ridge := by
  -- Compare subtype values using the representative's defining specification.
  apply Subtype.ext
  rw [positiveHemisphereRidgeKey_val]
  exact positiveHemisphereRidgeRepresentative_spec ridge

/-- Helper for Remark 50.3: an unordered positive-hemisphere ridge has exactly
`d` distinct vertices. -/
private lemma positiveHemisphereRidge_card {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : ridge.1.card = d := by
  -- Compute the cardinality using the chosen injective occurrence presentation.
  rw [← positiveHemisphereRidgeRepresentative_spec ridge]
  rw [(positiveHemisphereRidgeRepresentative ridge).ridgeVertexSet_eq_facetImage]
  exact finsetImage_succAbove_card
    (positiveHemisphereRidgeRepresentative ridge).facet.1.vertex
    (boundarySharedFacet_vertex_injective
      (positiveHemisphereRidgeRepresentative ridge).facet.1)
    (positiveHemisphereRidgeRepresentative ridge).omitted

/-- Helper for Remark 50.3: a ridge is equatorial when every vertex in its
unordered vertex set lies on the centered equator. -/
private def PositiveHemisphereRidge.IsEquatorial {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : Prop :=
  ∀ vertex ∈ ridge.1, StandardSphere.centeredGridOnEquator vertex

/-- Helper for Remark 50.3: equatoriality of an unordered ridge is available
as a private classical decision for finite incidence formulas. -/
private noncomputable instance positiveHemisphereRidgeIsEquatorialDecidable
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) :
    Decidable ridge.IsEquatorial :=
  Classical.dec _

/-- Helper for Remark 50.3: a cofacet of a ridge is a positive boundary facet
whose complete vertex set contains the ridge. -/
private abbrev PositiveHemisphereRidge.Cofacet {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :=
  {facet : StandardSphere.CubicalTucker.PositiveHemisphereBoundaryFacet d m //
    ridge.1 ⊆ Finset.univ.image facet.1.vertex}

/-- Helper for Remark 50.3: a ridge occurrence's retained vertex set is
contained in the complete vertex set of its facet. -/
private lemma positiveHemisphereRidgeVertexSet_subset_facetVertexSet {d m : ℕ}
    (occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m) :
    occurrence.ridgeVertexSet ⊆ Finset.univ.image occurrence.facet.1.vertex := by
  -- A retained position maps to the same facet vertex at its `succAbove` index.
  rw [occurrence.ridgeVertexSet_eq_facetImage]
  intro vertex hvertex
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hvertex
  exact Finset.mem_image.mpr
    ⟨occurrence.omitted.succAbove j, Finset.mem_univ _, rfl⟩

/-- Helper for Remark 50.3: the facet of the chosen ridge presentation
contains every vertex of the stored unordered ridge. -/
private lemma positiveHemisphereRidgeRepresentative_facet_mem {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    ridge.1 ⊆ Finset.univ.image
      (positiveHemisphereRidgeRepresentative ridge).facet.1.vertex := by
  -- Rewrite through the representative specification and use occurrence containment.
  rw [← positiveHemisphereRidgeRepresentative_spec ridge]
  exact positiveHemisphereRidgeVertexSet_subset_facetVertexSet
    (positiveHemisphereRidgeRepresentative ridge)

/-- Helper for Remark 50.3: the chosen occurrence supplies a distinguished
positive boundary cofacet of every unordered ridge. -/
private noncomputable def positiveHemisphereRidgeRepresentativeCofacet {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : ridge.Cofacet :=
  ⟨(positiveHemisphereRidgeRepresentative ridge).facet,
    positiveHemisphereRidgeRepresentative_facet_mem ridge⟩

/-- Helper for Remark 50.3: every represented positive-hemisphere ridge has
at least one positive boundary cofacet. -/
private lemma positiveHemisphereRidgeCofacet_nonempty {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : Nonempty ridge.Cofacet := by
  -- Use the cofacet carried by the chosen presentation.
  exact ⟨positiveHemisphereRidgeRepresentativeCofacet ridge⟩

/-- Helper for Remark 50.3: the finite cofacet type of a represented ridge
has positive cardinality. -/
private lemma positiveHemisphereRidgeCofacet_card_pos {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : 0 < Nat.card ridge.Cofacet := by
  -- Convert the explicit cofacet witness and the finite instance into positivity.
  exact Nat.card_pos_iff.mpr
    ⟨positiveHemisphereRidgeCofacet_nonempty ridge, inferInstance⟩

/-- Helper for Remark 50.3: a `d`-element subset of an injectively enumerated
`d + 1`-element set is obtained by deleting a unique enumeration index. -/
private lemma existsUnique_omitted_of_card_subset {V : Type*} [DecidableEq V]
    {d : ℕ} (vertex : Fin (d + 1) → V) (hvertex : Function.Injective vertex)
    (ridge : Finset V) (hridgeCard : ridge.card = d)
    (hridgeSubset : ridge ⊆ Finset.univ.image vertex) :
    ∃! omitted : Fin (d + 1),
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) = ridge := by
  -- The ridge is a proper subset, hence is contained in the erase of one full-set vertex.
  have hfullCard : (Finset.univ.image vertex).card = d + 1 := by
    calc
      (Finset.univ.image vertex).card = (Finset.univ : Finset (Fin (d + 1))).card :=
        Finset.card_image_of_injective Finset.univ hvertex
      _ = d + 1 := Fintype.card_fin (d + 1)
  have hridgeNe : ridge ≠ Finset.univ.image vertex := by
    intro heq
    have hcardEq := congrArg Finset.card heq
    rw [hridgeCard, hfullCard] at hcardEq
    omega
  have hridgeProper : ridge ⊂ Finset.univ.image vertex :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hridgeSubset, hridgeNe⟩
  obtain ⟨missingVertex, hmissingFull, hridgeErase⟩ :=
    Finset.ssubset_iff_exists_subset_erase.mp hridgeProper
  obtain ⟨omitted, _, hmissingEq⟩ := Finset.mem_image.mp hmissingFull
  subst missingVertex
  have hridgeEqErase :
      ridge = (Finset.univ.image vertex).erase (vertex omitted) := by
    apply Finset.eq_of_subset_of_card_le hridgeErase
    rw [Finset.card_erase_of_mem hmissingFull, hfullCard, hridgeCard]
    omega
  have hdeletionSubset :
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) ⊆ ridge := by
    intro value hvalue
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hvalue
    rw [hridgeEqErase]
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      exact Fin.succAbove_ne omitted j (hvertex heq)
    · exact Finset.mem_image.mpr
        ⟨omitted.succAbove j, Finset.mem_univ _, rfl⟩
  have hdeletion :
      Finset.univ.image (fun j ↦ vertex (omitted.succAbove j)) = ridge := by
    apply Finset.eq_of_subset_of_card_le hdeletionSubset
    rw [finsetImage_succAbove_card vertex hvertex omitted, hridgeCard]
  refine ⟨omitted, hdeletion, ?_⟩
  intro other hother
  exact finsetImage_succAbove_injective vertex hvertex
    (hother.trans hdeletion.symm)

/-- Helper for Remark 50.3: a cofacet contains the ridge as the deletion of
a unique facet vertex. -/
private lemma positiveHemisphereRidgeCofacet_existsUnique_omitted {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    ∃! omitted : Fin (d + 1),
      Finset.univ.image
        (fun j ↦ cofacet.1.1.vertex (omitted.succAbove j)) = ridge.1 := by
  -- Apply the finite deletion theorem to the injective cofacet enumeration.
  exact existsUnique_omitted_of_card_subset cofacet.1.1.vertex
    (boundarySharedFacet_vertex_injective cofacet.1.1)
    ridge.1 (positiveHemisphereRidge_card ridge) cofacet.2

/-- Helper for Remark 50.3: choose the unique omitted vertex of a ridge
inside one of its cofacets. -/
private noncomputable def positiveHemisphereRidgeCofacetOmitted {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    Fin (d + 1) :=
  Classical.choose (positiveHemisphereRidgeCofacet_existsUnique_omitted ridge cofacet)

/-- Helper for Remark 50.3: deleting the chosen cofacet vertex recovers the
stored ridge set. -/
private lemma positiveHemisphereRidgeCofacetOmitted_spec {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    Finset.univ.image (fun j ↦ cofacet.1.1.vertex
      ((positiveHemisphereRidgeCofacetOmitted ridge cofacet).succAbove j)) =
        ridge.1 := by
  -- Unpack the chosen omitted index's defining specification.
  exact (Classical.choose_spec
    (positiveHemisphereRidgeCofacet_existsUnique_omitted ridge cofacet)).1

/-- Helper for Remark 50.3: rebuild a ridge occurrence from a cofacet and its
unique omitted vertex. -/
private noncomputable def positiveHemisphereRidgeCofacetOccurrence {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m :=
  { facet := cofacet.1
    omitted := positiveHemisphereRidgeCofacetOmitted ridge cofacet }

/-- Helper for Remark 50.3: the occurrence rebuilt from a cofacet has the
prescribed unordered ridge key. -/
private lemma positiveHemisphereRidgeCofacetOccurrence_key {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    positiveHemisphereRidgeKey
      (positiveHemisphereRidgeCofacetOccurrence ridge cofacet) = ridge := by
  -- Equality of ridge subtypes follows from the chosen deletion equation.
  apply Subtype.ext
  rw [positiveHemisphereRidgeKey_val]
  rw [(positiveHemisphereRidgeCofacetOccurrence ridge cofacet).ridgeVertexSet_eq_facetImage]
  exact positiveHemisphereRidgeCofacetOmitted_spec ridge cofacet

/-- Helper for Remark 50.3: the occurrence fiber over an unordered ridge. -/
private abbrev PositiveHemisphereRidge.Fiber {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :=
  {occurrence : StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m //
    positiveHemisphereRidgeKey occurrence = ridge}

/-- Helper for Remark 50.3: the facet of an occurrence in a ridge fiber is a
cofacet of that ridge. -/
private lemma positiveHemisphereRidgeFiber_facet_mem {d m : ℕ}
    {ridge : PositiveHemisphereRidge d m} (occurrence : ridge.Fiber) :
    ridge.1 ⊆ Finset.univ.image occurrence.1.facet.1.vertex := by
  -- Rewrite the ridge through the fiber equation, then use deletion containment.
  have hridgeSet := congrArg Subtype.val occurrence.2
  rw [← hridgeSet]
  exact positiveHemisphereRidgeVertexSet_subset_facetVertexSet occurrence.1

/-- Helper for Remark 50.3: forget the omitted index of a ridge occurrence
and retain only its containing cofacet. -/
private def positiveHemisphereRidgeFiberToCofacet {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (occurrence : ridge.Fiber) :
    ridge.Cofacet :=
  ⟨occurrence.1.facet, positiveHemisphereRidgeFiber_facet_mem occurrence⟩

/-- Helper for Remark 50.3: rebuilding from a cofacet produces an occurrence
in the prescribed ridge fiber. -/
private lemma positiveHemisphereRidgeCofacetOccurrence_mem_fiber {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    positiveHemisphereRidgeKey
      (positiveHemisphereRidgeCofacetOccurrence ridge cofacet) = ridge := by
  -- Reuse the cofacet occurrence computation rule.
  exact positiveHemisphereRidgeCofacetOccurrence_key ridge cofacet

/-- Helper for Remark 50.3: turn a containing cofacet back into the unique
ridge occurrence that it supports. -/
private noncomputable def positiveHemisphereRidgeCofacetToFiber {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    ridge.Fiber :=
  ⟨positiveHemisphereRidgeCofacetOccurrence ridge cofacet,
    positiveHemisphereRidgeCofacetOccurrence_mem_fiber ridge cofacet⟩

/-- Helper for Remark 50.3: forgetting and rebuilding a ridge occurrence
returns the original occurrence. -/
private lemma positiveHemisphereRidgeFiberToCofacet_leftInverse {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (occurrence : ridge.Fiber) :
    positiveHemisphereRidgeCofacetToFiber ridge
      (positiveHemisphereRidgeFiberToCofacet ridge occurrence) = occurrence := by
  -- Uniqueness of the deleted index identifies the rebuilt occurrence.
  apply Subtype.ext
  refine congrArg₂
    StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence.mk rfl ?_
  apply (positiveHemisphereRidgeCofacet_existsUnique_omitted ridge
        (positiveHemisphereRidgeFiberToCofacet ridge occurrence)).unique
  · exact positiveHemisphereRidgeCofacetOmitted_spec ridge
      (positiveHemisphereRidgeFiberToCofacet ridge occurrence)
  · exact occurrence.1.ridgeVertexSet_eq_facetImage.symm.trans
      (congrArg Subtype.val occurrence.2)

/-- Helper for Remark 50.3: forgetting the rebuilt occurrence recovers the
original containing cofacet at the underlying-facet level. -/
private lemma positiveHemisphereRidgeCofacetToFiber_facet {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    (positiveHemisphereRidgeFiberToCofacet ridge
      (positiveHemisphereRidgeCofacetToFiber ridge cofacet)).1 = cofacet.1 := by
  -- Both sides store the same positive boundary facet.
  rfl

/-- Helper for Remark 50.3: rebuilding and then forgetting a ridge cofacet
returns the original cofacet. -/
private lemma positiveHemisphereRidgeFiberToCofacet_rightInverse {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    positiveHemisphereRidgeFiberToCofacet ridge
      (positiveHemisphereRidgeCofacetToFiber ridge cofacet) = cofacet := by
  -- Cofacets are subtypes, so equality follows from the named facet computation.
  exact Subtype.ext (positiveHemisphereRidgeCofacetToFiber_facet ridge cofacet)

/-- Helper for Remark 50.3: occurrences presenting a ridge are canonically
equivalent to the positive boundary cofacets containing that ridge. -/
private noncomputable def positiveHemisphereRidgeFiberEquivCofacet {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) : ridge.Fiber ≃ ridge.Cofacet :=
  { toFun := positiveHemisphereRidgeFiberToCofacet ridge
    invFun := positiveHemisphereRidgeCofacetToFiber ridge
    left_inv := positiveHemisphereRidgeFiberToCofacet_leftInverse ridge
    right_inv := positiveHemisphereRidgeFiberToCofacet_rightInverse ridge }

/-- Helper for Remark 50.3: a ridge's occurrence fiber and cofacet type have
the same finite cardinality. -/
private lemma positiveHemisphereRidgeFiber_card_eq_cofacet_card {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m) :
    Nat.card ridge.Fiber = Nat.card ridge.Cofacet := by
  -- Transport cardinality along the canonical occurrence/cofacet equivalence.
  exact Nat.card_congr (positiveHemisphereRidgeFiberEquivCofacet ridge)

/-- Helper for Remark 50.3: the one-or-two cofacet classification immediately
gives the corresponding one-or-two occurrence-fiber count. -/
private lemma positiveHemisphereRidgeFiber_card_of_cofacet_card {d m : ℕ}
    (ridge : PositiveHemisphereRidge d m)
    (hcofacet : Nat.card ridge.Cofacet =
      if ridge.IsEquatorial then 1 else 2) :
    Nat.card ridge.Fiber = if ridge.IsEquatorial then 1 else 2 := by
  -- First replace occurrences by cofacets, then apply the geometric count.
  calc
    Nat.card ridge.Fiber = Nat.card ridge.Cofacet :=
      positiveHemisphereRidgeFiber_card_eq_cofacet_card ridge
    _ = if ridge.IsEquatorial then 1 else 2 := hcofacet

/-- Helper for Remark 50.3: alternating weight is constant on every fiber of
the unordered positive-hemisphere ridge map. -/
private lemma positiveHemisphereRidgeWeight_eq_of_key_eq {d m ℓ : ℕ}
    (initial : Bool)
    (label : StandardSphere.CenteredGrid (d + 1) m → Fin ℓ × Bool)
    (first second :
      StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m)
    (hkey : positiveHemisphereRidgeKey first =
      positiveHemisphereRidgeKey second) :
    StandardSphere.CubicalTucker.alternatingLabeledFaceWeight
        initial label first.vertex =
      StandardSphere.CubicalTucker.alternatingLabeledFaceWeight
        initial label second.vertex := by
  -- Equality of ridge keys is equality of the unordered images of the two
  -- injective retained-vertex enumerations.
  have himage : Finset.univ.image first.vertex =
      Finset.univ.image second.vertex := by
    calc
      Finset.univ.image first.vertex = Finset.univ.image
          (fun j ↦ first.facet.1.vertex (first.omitted.succAbove j)) := by
        apply Finset.image_congr
        intro j _
        exact first.vertex_eq_facetVertex j
      _ = first.ridgeVertexSet := first.ridgeVertexSet_eq_facetImage.symm
      _ = (positiveHemisphereRidgeKey first).1 :=
        (positiveHemisphereRidgeKey_val first).symm
      _ = (positiveHemisphereRidgeKey second).1 := congrArg Subtype.val hkey
      _ = second.ridgeVertexSet := positiveHemisphereRidgeKey_val second
      _ = Finset.univ.image
          (fun j ↦ second.facet.1.vertex (second.omitted.succAbove j)) :=
        second.ridgeVertexSet_eq_facetImage
      _ = Finset.univ.image second.vertex := by
        apply Finset.image_congr
        intro j _
        exact (second.vertex_eq_facetVertex j).symm
  exact StandardSphere.CubicalTucker.alternatingLabeledFaceWeight_eq_of_injective_image_eq
    initial label first.vertex second.vertex
    (positiveHemisphereFaceOccurrence_vertex_injective second) himage

/-- Helper for Remark 50.3: once the geometric one-or-two cofacet count is
known, the positive-hemisphere occurrence sum reduces to equatorial ridges. -/
private lemma sum_positiveHemisphereRidgeWeight_eq_equatorial
    {d m ℓ : ℕ}
    (hcofacet : ∀ ridge : PositiveHemisphereRidge d m,
      Nat.card ridge.Cofacet = if ridge.IsEquatorial then 1 else 2)
    (initial : Bool)
    (label : StandardSphere.CenteredGrid (d + 1) m → Fin ℓ × Bool) :
    (∑ occurrence :
        StandardSphere.CubicalTucker.PositiveHemisphereFaceOccurrence d m,
      StandardSphere.CubicalTucker.alternatingLabeledFaceWeight
        initial label occurrence.vertex) =
      ∑ ridge : PositiveHemisphereRidge d m with ridge.IsEquatorial,
        StandardSphere.CubicalTucker.alternatingLabeledFaceWeight initial label
          (positiveHemisphereRidgeRepresentative ridge).vertex := by
  classical
  -- Apply the characteristic-two fiber formula using the chosen occurrence
  -- of each ridge and the verified weight invariance on unordered images.
  apply sum_eq_sum_boundary_of_fiber_card
    positiveHemisphereRidgeKey positiveHemisphereRidgeRepresentative
    positiveHemisphereRidgeRepresentative_key PositiveHemisphereRidge.IsEquatorial
  · intro ridge
    exact positiveHemisphereRidgeFiber_card_of_cofacet_card ridge (hcofacet ridge)
  · intro first second hkey
    exact positiveHemisphereRidgeWeight_eq_of_key_eq
      initial label first second hkey

namespace StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: the coordinate-sum rank of a centered-grid vertex. -/
private def centeredGridCoordinateSum {d m : ℕ} (vertex : CenteredGrid d m) : ℕ :=
  ∑ i, (vertex i).1

/-- Helper for Remark 50.3: consecutive vertices of a shared facet increase
the coordinate-sum rank by exactly one. -/
private lemma SharedFacet.coordinateSum_vertex_succ {d m : ℕ}
    (facet : SharedFacet d m) (j : Fin d) :
    centeredGridCoordinateSum (facet.vertex j.succ) =
      centeredGridCoordinateSum (facet.vertex j.castSucc) + 1 := by
  -- Reindex coordinates by the full staircase order, so the unique newly
  -- crossed active coordinate is the successor of `j`.
  unfold centeredGridCoordinateSum
  rw [← Equiv.sum_comp facet.leadingOrder
      (fun i ↦ ((facet.vertex j.succ) i).1),
    ← Equiv.sum_comp facet.leadingOrder
      (fun i ↦ ((facet.vertex j.castSucc) i).1)]
  calc
    ∑ i, ((facet.vertex j.succ) (facet.leadingOrder i)).1 =
        ∑ i, (((facet.vertex j.castSucc) (facet.leadingOrder i)).1 +
          if i = j.succ then 1 else 0) := by
      apply Fintype.sum_congr
      intro i
      refine Fin.cases ?_ (fun rank ↦ ?_) i
      · rw [facet.leadingOrder_zero, facet.vertex_value,
          facet.vertex_value]
        simp only [if_pos]
        have hzero : (0 : Fin (d + 1)) ≠ j.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_succ] at hval
          omega
        rw [if_neg hzero, add_zero]
      · have hactive : facet.leadingOrder rank.succ ≠ facet.fixed := by
          intro hfixed
          have hrank : rank.succ = 0 := facet.leadingOrder.injective
            (hfixed.trans facet.leadingOrder_zero.symm)
          exact Fin.succ_ne_zero rank hrank
        rw [facet.vertex_value, facet.vertex_value]
        simp only [hactive, if_false, facet.leadingOrder.symm_apply_apply,
          Fin.val_succ, Fin.val_castSucc]
        by_cases hrank : rank = j
        · subst rank
          have hnew : j.1 + 1 < j.1 + 1 + 1 := by omega
          have hold : ¬j.1 + 1 < j.1 + 1 := by omega
          rw [if_pos rfl, if_pos hnew, if_neg hold]
        · have hsucc : rank.succ ≠ j.succ := by
            intro h
            apply hrank
            apply Fin.ext
            have hval := congrArg Fin.val h
            simp only [Fin.val_succ] at hval
            omega
          rw [if_neg hsucc]
          have hltOrGt : rank.1 < j.1 ∨ j.1 < rank.1 :=
            Nat.lt_or_gt_of_ne (fun h ↦ hrank (Fin.ext h))
          rcases hltOrGt with hlt | hgt
          · have hnew : rank.1 + 1 < j.1 + 1 + 1 := by omega
            have hold : rank.1 + 1 < j.1 + 1 := by omega
            rw [if_pos hnew, if_pos hold]
          · have hnew : ¬rank.1 + 1 < j.1 + 1 + 1 := by omega
            have hold : ¬rank.1 + 1 < j.1 + 1 := by omega
            rw [if_neg hnew, if_neg hold]
    _ = (∑ i, ((facet.vertex j.castSucc) (facet.leadingOrder i)).1) +
        ∑ i, if i = j.succ then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, ((facet.vertex j.castSucc) (facet.leadingOrder i)).1) + 1 := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Helper for Remark 50.3: the coordinate-sum rank along a shared facet is
its initial rank plus the vertex index. -/
private lemma SharedFacet.coordinateSum_vertex {d m : ℕ}
    (facet : SharedFacet d m) (j : Fin (d + 1)) :
    centeredGridCoordinateSum (facet.vertex j) =
      centeredGridCoordinateSum (facet.vertex 0) + j.1 := by
  -- Accumulate the one-step rank increase along the staircase enumeration.
  induction j using Fin.induction with
  | zero => simp only [Fin.val_zero, add_zero]
  | succ j ih =>
      rw [facet.coordinateSum_vertex_succ j, ih]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega

/-- Helper for Remark 50.3: if two finite ranks have identical comparisons
with every threshold except an internal omission and the first is smaller,
then they are exactly the two ranks adjacent to that omission. -/
private lemma Fin.eq_pred_and_eq_castPred_of_lt_of_retainedCuts {r : ℕ}
    (omitted : Fin (r + 1)) (hzero : omitted ≠ 0)
    (hlast : omitted ≠ Fin.last r) (a b : Fin r) (hab : a < b)
    (hcuts : ∀ j : Fin r,
      (a.1 < (omitted.succAbove j).1 ↔
        b.1 < (omitted.succAbove j).1)) :
    a = omitted.pred hzero ∧ b = omitted.castPred hlast := by
  -- The threshold at `b` would distinguish the two ranks unless it is the
  -- deleted threshold itself.
  have hbOmitted : b.castSucc = omitted := by
    by_contra hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have hcut := hcuts j
    rw [hj] at hcut
    have hab' : a.1 < b.castSucc.1 := hab
    have hbb : b.1 < b.castSucc.1 := hcut.mp hab'
    exact (Nat.lt_irrefl b.1) hbb
  -- Likewise, the threshold immediately after `a` must be the omission;
  -- otherwise it separates `a` from the larger rank `b`.
  have haOmitted : a.succ = omitted := by
    by_contra hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have hcut := hcuts j
    rw [hj] at hcut
    have haa : a.1 < a.succ.1 := by
      simp only [Fin.val_succ]
      omega
    have hba : ¬b.1 < a.succ.1 := by
      simp only [Fin.val_succ]
      omega
    exact hba (hcut.mp haa)
  constructor
  · apply Fin.ext
    have hvalue := congrArg Fin.val haOmitted
    simp only [Fin.val_succ, Fin.val_pred] at hvalue ⊢
    have hpositive : 0 < omitted.1 := Fin.pos_iff_ne_zero.mpr hzero
    omega
  · apply Fin.ext
    have hvalue := congrArg Fin.val hbOmitted
    simpa only [Fin.val_castSucc, Fin.coe_castPred] using hvalue

/-- Helper for Remark 50.3: identical comparisons with all retained
thresholds determine a finite rank, except that the two ranks adjacent to an
internal omitted threshold may be exchanged. -/
private lemma Fin.eq_or_eq_adjacent_of_retainedCuts {r : ℕ}
    (omitted : Fin (r + 1)) (hzero : omitted ≠ 0)
    (hlast : omitted ≠ Fin.last r) (a b : Fin r)
    (hcuts : ∀ j : Fin r,
      (a.1 < (omitted.succAbove j).1 ↔
        b.1 < (omitted.succAbove j).1)) :
    a = b ∨
      (a = omitted.pred hzero ∧ b = omitted.castPred hlast) ∨
      (a = omitted.castPred hlast ∧ b = omitted.pred hzero) := by
  -- Trichotomy leaves equality or one of the two orientations of the
  -- adjacent pair characterized by the preceding lemma.
  rcases lt_trichotomy a b with hab | hab | hba
  · exact Or.inr (Or.inl
      (Fin.eq_pred_and_eq_castPred_of_lt_of_retainedCuts
        omitted hzero hlast a b hab hcuts))
  · exact Or.inl hab
  · have hadjacent := Fin.eq_pred_and_eq_castPred_of_lt_of_retainedCuts
      omitted hzero hlast b a hba (fun j ↦ (hcuts j).symm)
    exact Or.inr (Or.inr ⟨hadjacent.2, hadjacent.1⟩)

/-- Helper for Remark 50.3: retained threshold cuts determine a finite
permutation up to the single adjacent transposition around the omitted cut. -/
private lemma Equiv.Perm.eq_or_eq_mul_swap_of_retainedCuts {r : ℕ}
    (first second : Equiv.Perm (Fin r)) (omitted : Fin (r + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last r)
    (hcuts : ∀ i j : Fin r,
      ((first.symm i).1 < (omitted.succAbove j).1 ↔
        (second.symm i).1 < (omitted.succAbove j).1)) :
    second = first ∨
      second = first *
        Equiv.swap (omitted.pred hzero) (omitted.castPred hlast) := by
  -- Equality is one outcome. Otherwise choose an output whose inverse ranks
  -- differ; the retained-cut classifier forces that output across the gap.
  by_cases hequal : second = first
  · exact Or.inl hequal
  · right
    have hinverseNe : second.symm ≠ first.symm := by
      intro hinverse
      exact hequal (Equiv.symm_bijective.injective hinverse)
    obtain ⟨witness, hwitness⟩ :
        ∃ i, second.symm i ≠ first.symm i := by
      by_contra hnone
      push Not at hnone
      exact hinverseNe (Equiv.ext hnone)
    let lower := omitted.pred hzero
    let upper := omitted.castPred hlast
    have hlowerUpper : lower ≠ upper := by
      intro h
      have hvalue := congrArg Fin.val h
      dsimp only [lower, upper] at hvalue
      simp only [Fin.val_pred, Fin.coe_castPred] at hvalue
      have hpositive : 0 < omitted.1 := Fin.pos_iff_ne_zero.mpr hzero
      omega
    have hrank (i : Fin r) :
        first.symm i = second.symm i ∨
          (first.symm i = lower ∧ second.symm i = upper) ∨
          (first.symm i = upper ∧ second.symm i = lower) := by
      simpa only [lower, upper] using
        Fin.eq_or_eq_adjacent_of_retainedCuts omitted hzero hlast
          (first.symm i) (second.symm i) (hcuts i)
    have hwitnessPair :
        (first.symm witness = lower ∧ second.symm witness = upper) ∨
          (first.symm witness = upper ∧
            second.symm witness = lower) := by
      rcases hrank witness with hsame | hforward | hreverse
      · exact (hwitness hsame.symm).elim
      · exact Or.inl hforward
      · exact Or.inr hreverse
    have hinverse :
        second.symm = Equiv.swap lower upper * first.symm := by
      apply Equiv.ext
      intro i
      rw [Equiv.Perm.mul_apply]
      rcases hrank i with hsame | hforward | hreverse
      · have hnotLower : first.symm i ≠ lower := by
          intro hiLower
          rcases hwitnessPair with hwitnessForward | hwitnessReverse
          · have hiWitness : i = witness := first.symm.injective
                (hiLower.trans hwitnessForward.1.symm)
            subst i
            exact hlowerUpper
              (hwitnessForward.1.symm.trans
                (hsame.trans hwitnessForward.2))
          · have hsecondLower : second.symm i = lower :=
              hsame.symm.trans hiLower
            have hiWitness : i = witness := second.symm.injective
              (hsecondLower.trans hwitnessReverse.2.symm)
            subst i
            exact hlowerUpper
              (hwitnessReverse.2.symm.trans
                (hsame.symm.trans hwitnessReverse.1))
        have hnotUpper : first.symm i ≠ upper := by
          intro hiUpper
          rcases hwitnessPair with hwitnessForward | hwitnessReverse
          · have hsecondUpper : second.symm i = upper :=
              hsame.symm.trans hiUpper
            have hiWitness : i = witness := second.symm.injective
              (hsecondUpper.trans hwitnessForward.2.symm)
            subst i
            exact hlowerUpper
              (hwitnessForward.1.symm.trans
                (hsame.trans hwitnessForward.2))
          · have hiWitness : i = witness := first.symm.injective
              (hiUpper.trans hwitnessReverse.1.symm)
            subst i
            exact hlowerUpper
              (hwitnessReverse.2.symm.trans
                (hsame.symm.trans hwitnessReverse.1))
        rw [← hsame,
          Equiv.swap_apply_of_ne_of_ne hnotLower hnotUpper]
      · rw [hforward.1, hforward.2, Equiv.swap_apply_left]
      · rw [hreverse.1, hreverse.2, Equiv.swap_apply_right]
    -- Invert the pointwise inverse-permutation formula to recover the desired
    -- right-adjacent multiplication formula for the original permutations.
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.mul_apply]
    have hi := congrArg
      (fun order : Equiv.Perm (Fin r) ↦ order (second i)) hinverse
    simp only [Equiv.Perm.mul_apply, second.symm_apply_apply] at hi
    calc
      second i = first (first.symm (second i)) :=
        (first.apply_symm_apply (second i)).symm
      _ = first (Equiv.swap lower upper i) := by
        apply congrArg first
        have hswapped := congrArg (Equiv.swap lower upper) hi
        simpa only [Equiv.swap_apply_self] using hswapped.symm

/-- Helper for Remark 50.3: an ambient boundary-ridge occurrence consists of
an extreme shared facet and one omitted vertex of its staircase enumeration. -/
private structure BoundaryRidgeOccurrence (d m : ℕ) where
  facet : BoundarySharedFacet d m
  omitted : Fin (d + 1)
deriving DecidableEq

/-- Helper for Remark 50.3: every canonical shared-facet vertex has the
stored level at the distinguished coordinate. -/
private lemma SharedFacet.vertex_fixed {d m : ℕ} (facet : SharedFacet d m)
    (j : Fin (d + 1)) :
    facet.vertex j facet.fixed = facet.level := by
  -- Evaluate the fixed branch of the canonical vertex formula.
  apply Fin.ext
  rw [facet.vertex_value]
  simp only [if_pos]

/-- Helper for Remark 50.3: the existence of a shared-facet corner forces a
positive mesh radius. -/
private lemma SharedFacet.meshRadius_pos {d m : ℕ} (facet : SharedFacet d m) :
    0 < m := by
  -- A corner coordinate inhabits `Fin (2 * m)`, so that bound is positive.
  have hcorner := (facet.corner facet.fixed).isLt
  omega

/-- Helper for Remark 50.3: enumerate the retained vertices of an ambient
boundary-ridge occurrence. -/
private def BoundaryRidgeOccurrence.vertex {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) (j : Fin d) :
    CenteredGrid (d + 1) m :=
  occurrence.facet.vertex (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: every retained ridge vertex has the outer
facet's level at its distinguished coordinate. -/
private lemma BoundaryRidgeOccurrence.vertex_fixed {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) (j : Fin d) :
    occurrence.vertex j occurrence.facet.normalizedFacet.1.fixed =
      occurrence.facet.normalizedFacet.1.level := by
  -- Forget the boundary tag and use the shared-facet fixed-coordinate rule.
  rw [BoundaryRidgeOccurrence.vertex,
    BoundarySharedFacet.vertex_eq_normalizedFacet]
  exact occurrence.facet.normalizedFacet.1.vertex_fixed
    (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: the unordered vertex set retained by an ambient
boundary-ridge occurrence. -/
private def BoundaryRidgeOccurrence.ridgeVertexSet {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) :
    Finset (CenteredGrid (d + 1) m) :=
  Finset.univ.image occurrence.vertex

/-- Helper for Remark 50.3: an ambient boundary-ridge enumeration has no
repeated vertices. -/
private lemma BoundaryRidgeOccurrence.vertex_injective {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) :
    Function.Injective occurrence.vertex := by
  -- Compose the injective facet enumeration with deletion of one position.
  exact occurrence.facet.vertex_injective.comp Fin.succAbove_right_injective

/-- Helper for Remark 50.3: every ambient boundary ridge has exactly `d`
distinct vertices. -/
private lemma BoundaryRidgeOccurrence.ridgeVertexSet_card {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) :
    occurrence.ridgeVertexSet.card = d := by
  -- Count the finite image using injectivity of its retained enumeration.
  rw [BoundaryRidgeOccurrence.ridgeVertexSet,
    Finset.card_image_of_injective Finset.univ occurrence.vertex_injective]
  exact Fintype.card_fin d

/-- Helper for Remark 50.3: the coordinate-sum rank of a retained ridge
vertex is the initial facet rank plus its undeleted staircase position. -/
private lemma BoundaryRidgeOccurrence.coordinateSum_vertex {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) (j : Fin d) :
    centeredGridCoordinateSum (occurrence.vertex j) =
      centeredGridCoordinateSum
          (occurrence.facet.normalizedFacet.1.vertex 0) +
        (occurrence.omitted.succAbove j).1 := by
  -- Forget the boundary tag and apply the affine rank formula for the full facet.
  rw [BoundaryRidgeOccurrence.vertex,
    BoundarySharedFacet.vertex_eq_normalizedFacet]
  exact occurrence.facet.normalizedFacet.1.coordinateSum_vertex
    (occurrence.omitted.succAbove j)

/-- Helper for Remark 50.3: coordinate-sum rank strictly increases along
the retained enumeration of every ambient boundary ridge. -/
private lemma BoundaryRidgeOccurrence.coordinateSum_vertex_strictMono
    {d m : ℕ} (occurrence : BoundaryRidgeOccurrence d m) :
    StrictMono (fun j ↦ centeredGridCoordinateSum (occurrence.vertex j)) := by
  -- The deleted-index embedding is strictly increasing, and the initial rank
  -- contributes the same additive constant at every retained position.
  intro j k hjk
  calc
    centeredGridCoordinateSum (occurrence.vertex j) =
        centeredGridCoordinateSum
            (occurrence.facet.normalizedFacet.1.vertex 0) +
          (occurrence.omitted.succAbove j).1 :=
      occurrence.coordinateSum_vertex j
    _ < centeredGridCoordinateSum
            (occurrence.facet.normalizedFacet.1.vertex 0) +
          (occurrence.omitted.succAbove k).1 :=
      Nat.add_lt_add_left
        (Fin.strictMono_succAbove occurrence.omitted hjk) _
    _ = centeredGridCoordinateSum (occurrence.vertex k) :=
      (occurrence.coordinateSum_vertex k).symm

/-- Helper for Remark 50.3: two ambient ridge occurrences with the same
unordered vertex set enumerate their retained vertices pointwise equally. -/
private lemma BoundaryRidgeOccurrence.vertex_eq_of_ridgeVertexSet_eq
    {d m : ℕ} (first second : BoundaryRidgeOccurrence d m)
    (hridge : first.ridgeVertexSet = second.ridgeVertexSet) :
    first.vertex = second.vertex := by
  classical
  -- Sort the common ridge by coordinate-sum rank. Both retained enumerations
  -- are strictly increasing parametrizations of that same finite rank set.
  let rankSet : Finset ℕ :=
    first.ridgeVertexSet.image centeredGridCoordinateSum
  have hrankSetCard : rankSet.card = d := by
    dsimp only [rankSet]
    calc
      (first.ridgeVertexSet.image centeredGridCoordinateSum).card =
          (Finset.univ.image
            (centeredGridCoordinateSum ∘ first.vertex)).card := by
        rw [BoundaryRidgeOccurrence.ridgeVertexSet, Finset.image_image]
      _ = Finset.univ.card :=
        Finset.card_image_of_injective Finset.univ
          first.coordinateSum_vertex_strictMono.injective
      _ = d := Fintype.card_fin d
  have hfirstMem (j : Fin d) :
      centeredGridCoordinateSum (first.vertex j) ∈ rankSet := by
    apply Finset.mem_image.mpr
    refine ⟨first.vertex j, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hsecondMem (j : Fin d) :
      centeredGridCoordinateSum (second.vertex j) ∈ rankSet := by
    apply Finset.mem_image.mpr
    refine ⟨second.vertex j, ?_, rfl⟩
    rw [hridge]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hrankEq :
      (fun j ↦ centeredGridCoordinateSum (first.vertex j)) =
        fun j ↦ centeredGridCoordinateSum (second.vertex j) := by
    calc
      (fun j ↦ centeredGridCoordinateSum (first.vertex j)) =
          rankSet.orderEmbOfFin hrankSetCard :=
        Finset.orderEmbOfFin_unique hrankSetCard hfirstMem
          first.coordinateSum_vertex_strictMono
      _ = (fun j ↦ centeredGridCoordinateSum (second.vertex j)) :=
        (Finset.orderEmbOfFin_unique hrankSetCard hsecondMem
          second.coordinateSum_vertex_strictMono).symm
  -- Membership in the second image gives a candidate index; equality of its
  -- sorted rank with the same position forces that index to be the position.
  funext j
  have hfirstInSecond : first.vertex j ∈ second.ridgeVertexSet := by
    rw [← hridge]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hfirstInSecond
  have hrankKJ :
      centeredGridCoordinateSum (second.vertex k) =
        centeredGridCoordinateSum (second.vertex j) := by
    calc
      centeredGridCoordinateSum (second.vertex k) =
          centeredGridCoordinateSum (first.vertex j) :=
        congrArg centeredGridCoordinateSum hk
      _ = centeredGridCoordinateSum (second.vertex j) :=
        congrFun hrankEq j
  have hkj : k = j := second.coordinateSum_vertex_strictMono.injective hrankKJ
  subst k
  exact hk.symm

/-- Helper for Remark 50.3: a size-two gap between the two ranks adjacent to
an internal omitted position uniquely identifies that omitted position. -/
private lemma Fin.eq_of_succAbove_adjacent_gap_two {d : ℕ}
    (omitted other : Fin (d + 1)) (hzero : omitted ≠ 0)
    (hlast : omitted ≠ Fin.last d)
    (hgap : (other.succAbove (omitted.castPred hlast)).1 =
      (other.succAbove (omitted.pred hzero)).1 + 2) :
    other = omitted := by
  -- Expanding `succAbove` leaves four comparison branches; only deletion of
  -- the threshold between the adjacent ranks can create a gap of size two.
  have hpredValue : (omitted.pred hzero).1 + 1 = omitted.1 := by
    exact congrArg Fin.val (Fin.succ_pred omitted hzero)
  have hcastPredValue : (omitted.castPred hlast).1 = omitted.1 := by
    rfl
  have hpredCastValue : (omitted.pred hzero).castSucc.1 =
      (omitted.pred hzero).1 := by
    rfl
  have hpredSuccValue : (omitted.pred hzero).succ.1 = omitted.1 := by
    exact congrArg Fin.val (Fin.succ_pred omitted hzero)
  have hcastPredCastValue : (omitted.castPred hlast).castSucc.1 =
      omitted.1 := by
    exact congrArg Fin.val (Fin.castSucc_castPred omitted hlast)
  have hcastPredSuccValue : (omitted.castPred hlast).succ.1 =
      omitted.1 + 1 := by
    simp only [Fin.val_succ, hcastPredValue]
  apply Fin.ext
  unfold Fin.succAbove at hgap
  split_ifs at hgap <;> omega

/-- Helper for Remark 50.3: if an internal ambient occurrence and another
occurrence enumerate the same ridge pointwise, then they omit the same rank. -/
private lemma BoundaryRidgeOccurrence.omitted_eq_of_vertex_eq_of_internal
    {d m : ℕ} (first second : BoundaryRidgeOccurrence d m)
    (hzero : first.omitted ≠ 0) (hlast : first.omitted ≠ Fin.last d)
    (hvertex : first.vertex = second.vertex) :
    second.omitted = first.omitted := by
  -- Compare the two retained ranks immediately around the original omission.
  -- Their coordinate-sum gap is two, so the second deletion must create its
  -- gap at exactly the same rank.
  let lower : Fin d := first.omitted.pred hzero
  let upper : Fin d := first.omitted.castPred hlast
  have hrankLower := congrArg centeredGridCoordinateSum (congrFun hvertex lower)
  have hrankUpper := congrArg centeredGridCoordinateSum (congrFun hvertex upper)
  rw [first.coordinateSum_vertex, second.coordinateSum_vertex] at hrankLower
  rw [first.coordinateSum_vertex, second.coordinateSum_vertex] at hrankUpper
  have hfirstLower : first.omitted.succAbove lower = lower.castSucc := by
    exact Fin.succAbove_pred_self first.omitted hzero
  have hfirstUpper : first.omitted.succAbove upper = upper.succ := by
    exact Fin.succAbove_castPred_self first.omitted hlast
  rw [hfirstLower] at hrankLower
  rw [hfirstUpper] at hrankUpper
  have hgap :
      (second.omitted.succAbove (first.omitted.castPred hlast)).1 =
        (second.omitted.succAbove (first.omitted.pred hzero)).1 + 2 := by
    dsimp only [lower, upper] at hrankLower hrankUpper
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_pred,
      Fin.coe_castPred] at hrankLower hrankUpper
    have homittedPositive : 0 < first.omitted.1 :=
      Fin.pos_iff_ne_zero.mpr hzero
    omega
  exact Fin.eq_of_succAbove_adjacent_gap_two
    first.omitted second.omitted hzero hlast hgap

/-- Helper for Remark 50.3: forgetting a positive-hemisphere certificate
produces the corresponding ambient boundary-ridge occurrence. -/
private def PositiveHemisphereFaceOccurrence.toBoundaryRidge {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    BoundaryRidgeOccurrence d m :=
  ⟨occurrence.facet.1, occurrence.omitted⟩

/-- Helper for Remark 50.3: forgetting the hemisphere certificate preserves
each retained ridge vertex. -/
private lemma PositiveHemisphereFaceOccurrence.toBoundaryRidge_vertex
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m)
    (j : Fin d) : occurrence.toBoundaryRidge.vertex j = occurrence.vertex j := by
  -- Both occurrence types use the same facet and omitted-index projections.
  exact (occurrence.vertex_eq_facetVertex j).symm

/-- Helper for Remark 50.3: forgetting the hemisphere certificate preserves
the unordered retained ridge. -/
private lemma PositiveHemisphereFaceOccurrence.toBoundaryRidge_ridgeVertexSet
    {d m : ℕ} (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.toBoundaryRidge.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- Lift the pointwise projection computation to equality of finite images.
  unfold BoundaryRidgeOccurrence.ridgeVertexSet
  rw [occurrence.ridgeVertexSet_eq_facetImage]
  apply Finset.image_congr
  intro j _
  exact (occurrence.toBoundaryRidge_vertex j).trans
    (occurrence.vertex_eq_facetVertex j)

/-- Helper for Remark 50.3: forget the positivity certificate on a ridge
cofacet while retaining its uniquely reconstructed omitted vertex. -/
private noncomputable def positiveHemisphereRidgeCofacetAmbientOccurrence
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    BoundaryRidgeOccurrence d m :=
  (positiveHemisphereRidgeCofacetOccurrence ridge cofacet).toBoundaryRidge

/-- Helper for Remark 50.3: the ambient occurrence reconstructed from a
positive cofacet presents the stored unordered ridge. -/
private lemma positiveHemisphereRidgeCofacetAmbientOccurrence_ridgeVertexSet
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) (cofacet : ridge.Cofacet) :
    (positiveHemisphereRidgeCofacetAmbientOccurrence ridge cofacet).ridgeVertexSet =
      ridge.1 := by
  -- Forget positivity, then use the chosen omitted vertex's specification.
  rw [positiveHemisphereRidgeCofacetAmbientOccurrence,
    PositiveHemisphereFaceOccurrence.toBoundaryRidge_ridgeVertexSet,
    (positiveHemisphereRidgeCofacetOccurrence ridge cofacet).ridgeVertexSet_eq_facetImage]
  exact positiveHemisphereRidgeCofacetOmitted_spec ridge cofacet

/-- Helper for Remark 50.3: distinct positive cofacets remain distinct after
reconstruction as ambient ridge occurrences. -/
private lemma positiveHemisphereRidgeCofacetAmbientOccurrence_injective
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) :
    Function.Injective (positiveHemisphereRidgeCofacetAmbientOccurrence ridge) := by
  -- Equality of ambient occurrences gives equality of the underlying boundary
  -- facets; the two positivity and containment certificates are proof-irrelevant.
  intro first second heq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg BoundaryRidgeOccurrence.facet heq

/-- Helper for Remark 50.3: reconstructing the distinguished cofacet gives
the ambient occurrence underlying the chosen ridge representative. -/
private lemma positiveHemisphereRidgeRepresentativeCofacetAmbientOccurrence
    {d m : ℕ} (ridge : PositiveHemisphereRidge d m) :
    positiveHemisphereRidgeCofacetAmbientOccurrence ridge
        (positiveHemisphereRidgeRepresentativeCofacet ridge) =
      (positiveHemisphereRidgeRepresentative ridge).toBoundaryRidge := by
  -- The facets agree by construction; uniqueness of the deleted index
  -- identifies the reconstructed omission with the representative's omission.
  apply congrArg PositiveHemisphereFaceOccurrence.toBoundaryRidge
  refine congrArg₂ PositiveHemisphereFaceOccurrence.mk rfl ?_
  apply (positiveHemisphereRidgeCofacet_existsUnique_omitted ridge
    (positiveHemisphereRidgeRepresentativeCofacet ridge)).unique
  · exact positiveHemisphereRidgeCofacetOmitted_spec ridge
      (positiveHemisphereRidgeRepresentativeCofacet ridge)
  · exact (positiveHemisphereRidgeRepresentative ridge).ridgeVertexSet_eq_facetImage.symm.trans
      (positiveHemisphereRidgeRepresentative_spec ridge)

/-- Helper for Remark 50.3: the active coordinate occupying a nonzero rank
in a shared facet's leading order. -/
private def SharedFacet.activeCoordinate {d m : ℕ} (facet : SharedFacet d m)
    (rank : Fin d) : Fin (d + 1) :=
  Equiv.swap 0 facet.fixed rank.succ

/-- Helper for Remark 50.3: an active coordinate of a shared facet is never
its distinguished fixed coordinate. -/
private lemma SharedFacet.activeCoordinate_ne_fixed {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    facet.activeCoordinate rank ≠ facet.fixed := by
  -- Injectivity of the transposition separates the successor rank from zero.
  intro hfixed
  have hzero : Equiv.swap 0 facet.fixed 0 = facet.fixed :=
    Equiv.swap_apply_left 0 facet.fixed
  have hsuccZero : rank.succ = 0 :=
    (Equiv.swap 0 facet.fixed).injective (hfixed.trans hzero.symm)
  exact Fin.succ_ne_zero rank hsuccZero

/-- Helper for Remark 50.3: distinct active ranks determine distinct ambient
coordinates. -/
private lemma SharedFacet.activeCoordinate_injective {d m : ℕ}
    (facet : SharedFacet d m) : Function.Injective facet.activeCoordinate := by
  -- Cancel the ambient transposition and then the successor embedding.
  intro rank₁ rank₂ heq
  exact (Fin.succ_injective _)
    ((Equiv.swap 0 facet.fixed).injective heq)

/-- Helper for Remark 50.3: the transposition defining active coordinates
identifies nonzero ranks with ambient coordinates other than the fixed one. -/
private lemma SharedFacet.activeCoordinateComplement_iff {d m : ℕ}
    (facet : SharedFacet d m) (i : Fin (d + 1)) :
    i ≠ 0 ↔ Equiv.swap 0 facet.fixed i ≠ facet.fixed := by
  -- Transport inequality through the defining transposition and evaluate it at zero.
  simpa only [Equiv.swap_apply_left] using
    labeledPerm_ne_iff_image_ne (Equiv.swap 0 facet.fixed) 0 i

/-- Helper for Remark 50.3: active ranks are canonically equivalent to the
ambient coordinates complementary to a shared facet's fixed coordinate. -/
private def SharedFacet.activeCoordinateEquiv {d m : ℕ}
    (facet : SharedFacet d m) :
    Fin d ≃ {i : Fin (d + 1) // i ≠ facet.fixed} :=
  (finSuccAboveEquiv 0).trans
    (Equiv.subtypeEquiv (Equiv.swap 0 facet.fixed)
      facet.activeCoordinateComplement_iff)

/-- Helper for Remark 50.3: the active-coordinate equivalence has the same
ambient value as `activeCoordinate`. -/
private lemma SharedFacet.activeCoordinateEquiv_apply {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    (facet.activeCoordinateEquiv rank).1 = facet.activeCoordinate rank := by
  -- Evaluate the two complement equivalences in sequence.
  rfl

/-- Helper for Remark 50.3: the inverse leading rank of an active coordinate
is the successor of its inverse active-order rank. -/
private lemma SharedFacet.leadingOrder_symm_activeCoordinate {d m : ℕ}
    (facet : SharedFacet d m) (rank : Fin d) :
    facet.leadingOrder.symm (facet.activeCoordinate rank) =
      (facet.activeOrder.symm rank).succ := by
  -- Apply the leading order; its successor computation cancels the active
  -- permutation and recovers the chosen ambient coordinate.
  apply facet.leadingOrder.injective
  rw [facet.leadingOrder.apply_symm_apply, facet.leadingOrder_succ]
  simp only [SharedFacet.activeCoordinate, Equiv.apply_symm_apply]

/-- Helper for Remark 50.3: at vertex zero, every nonfixed coordinate of a
shared facet is exactly its stored lower corner. -/
private lemma SharedFacet.vertex_zero_of_ne_fixed {d m : ℕ}
    (facet : SharedFacet d m) (i : Fin (d + 1)) (hi : i ≠ facet.fixed) :
    (facet.vertex 0 i).1 = (facet.corner i).1 := by
  -- A nonfixed leading rank is positive, so the zero vertex has not crossed
  -- that coordinate's staircase threshold.
  rw [facet.vertex_value]
  simp only [hi, if_false, Fin.val_zero, zero_add]
  have hrankNe : facet.leadingOrder.symm i ≠ 0 :=
    facet.leadingOrder_symm_ne_zero hi
  have hrankPos : 0 < (facet.leadingOrder.symm i).1 :=
    Fin.pos_iff_ne_zero.mpr hrankNe
  rw [if_neg (Nat.not_lt.mpr hrankPos), add_zero]

/-- Helper for Remark 50.3: equality of all four stored shared-facet fields
determines the shared facet. -/
private lemma SharedFacet.ext_of_fields {d m : ℕ}
    (first second : SharedFacet d m)
    (hfixed : second.fixed = first.fixed)
    (hlevel : second.level = first.level)
    (hcorner : second.corner = first.corner)
    (horder : second.activeOrder = first.activeOrder) :
    second = first := by
  -- Eliminate both records; the four supplied field equalities then identify
  -- their constructors directly.
  cases first
  cases second
  simp_all

/-- Helper for Remark 50.3: transposing zero with a fixed coordinate carries
the nonzero coordinates precisely to its complement. -/
private lemma SharedFacet.activeCoordinateComplementAt_iff {d : ℕ}
    (fixed i : Fin (d + 1)) :
    i ≠ 0 ↔ Equiv.swap 0 fixed i ≠ fixed := by
  -- Transport inequality through the transposition and evaluate its zero image.
  simpa only [Equiv.swap_apply_left] using
    labeledPerm_ne_iff_image_ne (Equiv.swap 0 fixed) 0 i

/-- Helper for Remark 50.3: the standard rank enumeration identifies the
coordinates complementary to any chosen fixed coordinate. -/
private def SharedFacet.activeCoordinateEquivAt {d : ℕ} (fixed : Fin (d + 1)) :
    Fin d ≃ {i : Fin (d + 1) // i ≠ fixed} :=
  (finSuccAboveEquiv 0).trans
    (Equiv.subtypeEquiv (Equiv.swap 0 fixed)
      (SharedFacet.activeCoordinateComplementAt_iff fixed))

/-- Helper for Remark 50.3: the fixed-coordinate complement equivalence has
the expected ambient-coordinate formula. -/
private lemma SharedFacet.activeCoordinateEquivAt_apply {d : ℕ}
    (fixed : Fin (d + 1)) (rank : Fin d) :
    (SharedFacet.activeCoordinateEquivAt fixed rank).1 =
      Equiv.swap 0 fixed rank.succ := by
  -- Evaluate the successor embedding and the ambient transposition.
  rfl

/-- Helper for Remark 50.3: exchanging a facet's fixed coordinate with one
active coordinate carries the old complement to the new complement. -/
private lemma SharedFacet.coordinateExchangeComplement_iff {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) (i : Fin (d + 1)) :
    i ≠ facet.fixed ↔
      Equiv.swap facet.fixed (facet.activeCoordinate innerFixed) i ≠
        facet.activeCoordinate innerFixed := by
  -- Transport inequality through the ambient transposition at the old fixed point.
  simpa only [Equiv.swap_apply_left] using
    labeledPerm_ne_iff_image_ne
      (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)) facet.fixed i

/-- Helper for Remark 50.3: exchange the coordinate ranks in the complements
of an outer fixed coordinate and a selected active coordinate. -/
private def SharedFacet.activeCoordinateExchangeEquiv {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) : Equiv.Perm (Fin d) :=
  facet.activeCoordinateEquiv |>.trans
    ((Equiv.subtypeEquiv
      (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
      (facet.coordinateExchangeComplement_iff innerFixed)).trans
    (SharedFacet.activeCoordinateEquivAt
      (facet.activeCoordinate innerFixed)).symm)

/-- Helper for Remark 50.3: the rank exchange agrees in ambient coordinates
with transposing the two distinguished coordinates. -/
private lemma SharedFacet.activeCoordinateExchangeEquiv_ambient {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed rank : Fin d) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)
          (facet.activeCoordinate rank) := by
  -- Apply the new complement equivalence to its inverse image of the
  -- transposed old complement coordinate.
  let transported :
      {i : Fin (d + 1) // i ≠ facet.activeCoordinate innerFixed} :=
    Equiv.subtypeEquiv
      (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
      (facet.coordinateExchangeComplement_iff innerFixed)
      (facet.activeCoordinateEquiv rank)
  calc
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
        (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        transported.1 := congrArg Subtype.val
      ((SharedFacet.activeCoordinateEquivAt
        (facet.activeCoordinate innerFixed)).apply_symm_apply transported)
    _ = Equiv.swap facet.fixed (facet.activeCoordinate innerFixed)
        (facet.activeCoordinate rank) := by
      simp only [transported]
      simp only [Equiv.subtypeEquiv_apply]
      exact congrArg
        (Equiv.swap facet.fixed (facet.activeCoordinate innerFixed))
        (facet.activeCoordinateEquiv_apply rank)

/-- Helper for Remark 50.3: after exchanging fixed roles, the old inner fixed
rank represents the old outer fixed coordinate. -/
private lemma SharedFacet.activeCoordinateExchangeEquiv_fixed_ambient {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed innerFixed)).1 =
        facet.fixed := by
  -- The ambient exchange sends the selected active coordinate back to the old fixed one.
  rw [facet.activeCoordinateExchangeEquiv_ambient innerFixed innerFixed]
  exact Equiv.swap_apply_right facet.fixed (facet.activeCoordinate innerFixed)

/-- Helper for Remark 50.3: every residual active coordinate is unchanged
by exchanging the two fixed roles. -/
private lemma SharedFacet.activeCoordinateExchangeEquiv_residual_ambient
    {d m : ℕ} (facet : SharedFacet d m) (innerFixed rank : Fin d)
    (hrank : rank ≠ innerFixed) :
    (SharedFacet.activeCoordinateEquivAt (facet.activeCoordinate innerFixed)
      (facet.activeCoordinateExchangeEquiv innerFixed rank)).1 =
        facet.activeCoordinate rank := by
  -- The residual coordinate differs from both endpoints of the ambient transposition.
  rw [facet.activeCoordinateExchangeEquiv_ambient innerFixed rank]
  apply Equiv.swap_apply_of_ne_of_ne
  · exact facet.activeCoordinate_ne_fixed rank
  · intro heq
    exact hrank (facet.activeCoordinate_injective heq)

/-- Helper for Remark 50.3: outside the newly fixed coordinate, every
ambient coordinate is either the old fixed coordinate or a residual active one. -/
private lemma SharedFacet.exchangeCoordinate_eq_fixed_or_active {d m : ℕ}
    (facet : SharedFacet d m) (innerFixed : Fin d) {i : Fin (d + 1)}
    (hi : i ≠ facet.activeCoordinate innerFixed) :
    i = facet.fixed ∨
      ∃ rank, rank ≠ innerFixed ∧ i = facet.activeCoordinate rank := by
  -- Split off the old fixed coordinate; every remaining coordinate has a
  -- unique old active rank, which cannot be the newly fixed rank.
  by_cases hfixed : i = facet.fixed
  · exact Or.inl hfixed
  · let rank := facet.activeCoordinateEquiv.symm ⟨i, hfixed⟩
    have hrankCoordinate : facet.activeCoordinate rank = i := by
      calc
        facet.activeCoordinate rank = (facet.activeCoordinateEquiv rank).1 :=
          (facet.activeCoordinateEquiv_apply rank).symm
        _ = i := congrArg Subtype.val
          (facet.activeCoordinateEquiv.apply_symm_apply ⟨i, hfixed⟩)
    right
    refine ⟨rank, ?_, hrankCoordinate.symm⟩
    intro hrank
    apply hi
    calc
      i = facet.activeCoordinate rank := hrankCoordinate.symm
      _ = facet.activeCoordinate innerFixed := congrArg facet.activeCoordinate hrank

/-- Helper for Remark 50.3: transport a shared facet along an ambient
coordinate permutation. -/
private def SharedFacet.reindex {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) : SharedFacet d m :=
  { fixed := (Equiv.Perm.decomposeFin (e * facet.leadingOrder)).1
    level := facet.level
    corner := fun i ↦ facet.corner (e.symm i)
    activeOrder := (Equiv.Perm.decomposeFin (e * facet.leadingOrder)).2 }

/-- Helper for Remark 50.3: reindexing sends the distinguished coordinate
through the supplied permutation. -/
private lemma SharedFacet.reindex_fixed {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) :
    (facet.reindex e).fixed = e facet.fixed := by
  -- Evaluate reconstruction of the decomposed full order at its initial rank.
  calc
    (facet.reindex e).fixed =
        Equiv.Perm.decomposeFin.symm
          (Equiv.Perm.decomposeFin (e * facet.leadingOrder)) 0 := by
      rw [SharedFacet.reindex,
        Equiv.Perm.decomposeFin_symm_apply_zero]
    _ = (e * facet.leadingOrder) 0 := congrArg
      (fun order : Equiv.Perm (Fin (d + 1)) ↦ order 0)
      (Equiv.symm_apply_apply Equiv.Perm.decomposeFin
        (e * facet.leadingOrder))
    _ = e facet.fixed := by
      rw [Equiv.Perm.mul_apply, facet.leadingOrder_zero]

/-- Helper for Remark 50.3: the full order of a reindexed facet is the
transported original full order. -/
private lemma SharedFacet.reindex_leadingOrder {d m : ℕ}
    (facet : SharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    (facet.reindex e).leadingOrder = e * facet.leadingOrder := by
  -- Check the distinguished rank directly, then reconstruct every successor
  -- rank from the stored decomposition components.
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun rank ↦ ?_) i
  · rw [(facet.reindex e).leadingOrder_zero, facet.reindex_fixed e,
      Equiv.Perm.mul_apply, facet.leadingOrder_zero]
  · calc
      (facet.reindex e).leadingOrder rank.succ =
          Equiv.swap 0 (facet.reindex e).fixed
            ((facet.reindex e).activeOrder rank).succ :=
        (facet.reindex e).leadingOrder_succ rank
      _ = Equiv.Perm.decomposeFin.symm
          (Equiv.Perm.decomposeFin (e * facet.leadingOrder)) rank.succ := by
        rw [Equiv.Perm.decomposeFin_symm_apply_succ]
        rfl
      _ = (e * facet.leadingOrder) rank.succ := congrArg
        (fun order : Equiv.Perm (Fin (d + 1)) ↦ order rank.succ)
        (Equiv.symm_apply_apply Equiv.Perm.decomposeFin
          (e * facet.leadingOrder))

/-- Helper for Remark 50.3: inverse full-order ranks are unchanged after
transporting both a facet and a coordinate. -/
private lemma SharedFacet.reindex_leadingOrder_symm_apply {d m : ℕ}
    (facet : SharedFacet d m) (e : Equiv.Perm (Fin (d + 1)))
    (i : Fin (d + 1)) :
    (facet.reindex e).leadingOrder.symm (e i) = facet.leadingOrder.symm i := by
  -- Apply the transported full order to both sides and use cancellation.
  rw [facet.reindex_leadingOrder e]
  apply (e * facet.leadingOrder).injective
  rw [(e * facet.leadingOrder).apply_symm_apply,
    Equiv.Perm.mul_apply, facet.leadingOrder.apply_symm_apply]

/-- Helper for Remark 50.3: coordinate transport preserves the normalized
fixed-corner certificate. -/
private lemma SharedFacet.reindex_normalized {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    ((facet.1.reindex e).corner (facet.1.reindex e).fixed).1 = 0 := by
  -- Pull the transported fixed coordinate back to the original one.
  rw [facet.1.reindex_fixed e]
  simp only [SharedFacet.reindex, Equiv.symm_apply_apply]
  exact facet.2

/-- Helper for Remark 50.3: reindexing transports every canonical facet
vertex pointwise. -/
private lemma SharedFacet.reindex_vertex {d m : ℕ} (facet : SharedFacet d m)
    (e : Equiv.Perm (Fin (d + 1))) (j : Fin (d + 1)) (i : Fin (d + 1)) :
    (facet.reindex e).vertex j (e i) = facet.vertex j i := by
  -- Compare the fixed branch, corner, and full-order rank after transport.
  apply Fin.ext
  rw [(facet.reindex e).vertex_value, facet.vertex_value,
    facet.reindex_fixed e, facet.reindex_leadingOrder_symm_apply e i]
  simp only [SharedFacet.reindex, Equiv.symm_apply_apply, e.injective.eq_iff]

/-- Helper for Remark 50.3: coordinate transport of a normalized facet is
again normalized. -/
private def SharedFacet.normalizedReindex {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (e : Equiv.Perm (Fin (d + 1))) :
    NormalizedSharedFacet d m :=
  ⟨facet.1.reindex e, SharedFacet.reindex_normalized facet e⟩

/-- Helper for Remark 50.3: replace only the fixed-coordinate level of a
normalized shared facet. -/
private def SharedFacet.withLevel {d m : ℕ} (facet : NormalizedSharedFacet d m)
    (level : Fin (2 * m + 1)) : NormalizedSharedFacet d m :=
  ⟨{ facet.1 with level := level }, facet.2⟩

/-- Helper for Remark 50.3: replacing a normalized facet's level preserves
its distinguished coordinate. -/
private lemma SharedFacet.withLevel_fixed {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1)) :
    (SharedFacet.withLevel facet level).1.fixed = facet.1.fixed := by
  -- The record update changes only the level field.
  rfl

/-- Helper for Remark 50.3: replacing a normalized facet's level gives that
level at every fixed-coordinate vertex. -/
private lemma SharedFacet.withLevel_vertex_fixed {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1))
    (j : Fin (d + 1)) :
    (SharedFacet.withLevel facet level).1.vertex j facet.1.fixed = level := by
  -- Evaluate the fixed branch of the canonical vertex formula.
  apply Fin.ext
  rw [(SharedFacet.withLevel facet level).1.vertex_value]
  simp only [SharedFacet.withLevel, if_pos]

/-- Helper for Remark 50.3: replacing a facet's fixed level preserves its
full coordinate order. -/
private lemma SharedFacet.withLevel_leadingOrder {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1)) :
    (SharedFacet.withLevel facet level).1.leadingOrder =
      facet.1.leadingOrder := by
  -- The full order depends only on the unchanged fixed coordinate and active order.
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun rank ↦ ?_) i
  · rw [(SharedFacet.withLevel facet level).1.leadingOrder_zero,
      facet.1.leadingOrder_zero]
    rfl
  · rw [(SharedFacet.withLevel facet level).1.leadingOrder_succ,
      facet.1.leadingOrder_succ]
    rfl

/-- Helper for Remark 50.3: replacing a normalized facet's level leaves
every nonfixed vertex coordinate unchanged. -/
private lemma SharedFacet.withLevel_vertex_of_ne {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (level : Fin (2 * m + 1))
    (j : Fin (d + 1)) {i : Fin (d + 1)} (hi : i ≠ facet.1.fixed) :
    (SharedFacet.withLevel facet level).1.vertex j i = facet.1.vertex j i := by
  -- Both nonfixed branches use the same corner and full order.
  apply Fin.ext
  rw [(SharedFacet.withLevel facet level).1.vertex_value, facet.1.vertex_value]
  rw [SharedFacet.withLevel_leadingOrder]
  simp only [SharedFacet.withLevel, hi, if_false]

/-- Helper for Remark 50.3: the exchanged inner facet transports its
coordinates and replaces its fixed level by the outer facet's level. -/
private def SharedFacet.exchangedActiveFacet {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) : NormalizedSharedFacet d m :=
  SharedFacet.withLevel
    (SharedFacet.normalizedReindex inner
      (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level

/-- Helper for Remark 50.3: the exchanged inner facet fixes the rank
obtained by exchanging the old inner fixed rank. -/
private lemma SharedFacet.exchangedActiveFacet_fixed {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer inner).1.fixed =
      outer.1.activeCoordinateExchangeEquiv inner.1.fixed inner.1.fixed := by
  -- The level update preserves the fixed rank produced by reindexing.
  rw [SharedFacet.exchangedActiveFacet, SharedFacet.withLevel_fixed,
    SharedFacet.normalizedReindex]
  exact inner.1.reindex_fixed
    (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)

/-- Helper for Remark 50.3: the exchanged inner facet stores the old outer
facet's level. -/
private lemma SharedFacet.exchangedActiveFacet_level {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer inner).1.level =
      outer.1.level := by
  -- Reindexing preserves the level before the final level replacement.
  rfl

/-- Helper for Remark 50.3: the exchanged inner facet has the old outer
boundary level at its fixed rank. -/
private lemma SharedFacet.exchangedActiveFacet_vertex_fixed {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed inner.1.fixed) =
      outer.1.level := by
  -- Rewrite the exchanged fixed rank and use the level-update computation.
  rw [← SharedFacet.exchangedActiveFacet_fixed outer inner]
  exact SharedFacet.withLevel_vertex_fixed
    (SharedFacet.normalizedReindex inner
      (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level j

/-- Helper for Remark 50.3: away from the exchanged fixed rank, the inner
facet's vertices are transported pointwise. -/
private lemma SharedFacet.exchangedActiveFacet_vertex_exchange {d m : ℕ}
    (outer : NormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1))
    (rank : Fin (d + 1)) (hrank : rank ≠ inner.1.fixed) :
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) =
      inner.1.vertex j rank := by
  -- Remove the level update at this nonfixed coordinate, then apply reindexing.
  have hne :
      outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank ≠
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)).1.fixed := by
    rw [SharedFacet.normalizedReindex,
      inner.1.reindex_fixed
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)]
    exact fun heq ↦ hrank
      ((outer.1.activeCoordinateExchangeEquiv inner.1.fixed).injective heq)
  calc
    (SharedFacet.exchangedActiveFacet outer inner).1.vertex j
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) =
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)).1.vertex j
            (outer.1.activeCoordinateExchangeEquiv inner.1.fixed rank) :=
      SharedFacet.withLevel_vertex_of_ne
        (SharedFacet.normalizedReindex inner
          (outer.1.activeCoordinateExchangeEquiv inner.1.fixed)) outer.1.level j hne
    _ = inner.1.vertex j rank :=
      inner.1.reindex_vertex
        (outer.1.activeCoordinateExchangeEquiv inner.1.fixed) j rank

/-- Helper for Remark 50.3: replace the active staircase of a shared facet
while retaining its fixed coordinate and fixed level. -/
private def SharedFacet.withActiveStaircase {d m : ℕ}
    (facet : SharedFacet (d + 1) m) (staircase : ElementaryStaircase (d + 1) m) :
    SharedFacet (d + 1) m :=
  { fixed := facet.fixed
    level := facet.level
    corner := fun i ↦ if hi : i = facet.fixed then facet.corner i
      else staircase.corner (facet.activeCoordinateEquiv.symm ⟨i, hi⟩)
    activeOrder := staircase.order }

/-- Helper for Remark 50.3: replacing the active staircase preserves the
normalized fixed-corner value. -/
private lemma SharedFacet.withActiveStaircase_corner_fixed {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).corner facet.fixed =
      facet.corner facet.fixed := by
  -- The distinguished coordinate selects the retained-corner branch.
  simp only [SharedFacet.withActiveStaircase, dite_true]

/-- Helper for Remark 50.3: replacing the active staircase preserves a
normalized shared facet's normalization certificate. -/
private lemma SharedFacet.withActiveStaircase_normalized {d m : ℕ}
    (facet : NormalizedSharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    ((facet.1.withActiveStaircase staircase).corner
      (facet.1.withActiveStaircase staircase).fixed).1 = 0 := by
  -- Rewrite the retained fixed coordinate and use the original certificate.
  change ((facet.1.withActiveStaircase staircase).corner facet.1.fixed).1 = 0
  rw [facet.1.withActiveStaircase_corner_fixed staircase]
  exact facet.2

/-- Helper for Remark 50.3: replacing the active staircase does not change
the ambient coordinate represented by an active rank. -/
private lemma SharedFacet.withActiveStaircase_activeCoordinate {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).activeCoordinate rank =
      facet.activeCoordinate rank := by
  -- The active-coordinate formula depends only on the retained fixed coordinate.
  rfl

/-- Helper for Remark 50.3: compress a shared facet to the elementary
staircase on its active coordinates. -/
private def SharedFacet.activeStaircase {d m : ℕ} (facet : SharedFacet d m) :
    ElementaryStaircase d m :=
  { corner := fun rank ↦ facet.corner (facet.activeCoordinate rank)
    order := facet.activeOrder }

/-- Helper for Remark 50.3: active-staircase compression preserves every
shared-facet vertex after projecting to the active coordinates. -/
private lemma SharedFacet.activeStaircase_vertex {d m : ℕ}
    (facet : SharedFacet d m) (j : Fin (d + 1)) :
    facet.activeStaircase.vertex j =
      fun rank ↦ facet.vertex j (facet.activeCoordinate rank) := by
  -- Compare the common corner and align the leading-order successor rank.
  funext rank
  apply Fin.ext
  rw [ElementaryStaircase.vertex_value, facet.vertex_value]
  simp only [SharedFacet.activeStaircase,
    facet.activeCoordinate_ne_fixed rank, if_false]
  have hrank :
      facet.leadingOrder.symm (facet.activeCoordinate rank) =
        (facet.activeOrder.symm rank).succ := by
    apply facet.leadingOrder.injective
    rw [facet.leadingOrder.apply_symm_apply, facet.leadingOrder_succ]
    simp only [SharedFacet.activeCoordinate, Equiv.apply_symm_apply]
  rw [hrank]
  simp only [Fin.val_succ]
  split_ifs <;> omega

/-- Helper for Remark 50.3: active compression after replacing the active
staircase recovers the replacement staircase. -/
private lemma SharedFacet.activeStaircase_withActiveStaircase {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).activeStaircase = staircase := by
  -- Compare the replacement corner and order on every active rank.
  apply congrArg₂ ElementaryStaircase.mk
  · funext rank
    rw [facet.withActiveStaircase_activeCoordinate staircase rank]
    simp only [SharedFacet.withActiveStaircase]
    rw [dif_neg (facet.activeCoordinate_ne_fixed rank)]
    apply congrArg staircase.corner
    apply facet.activeCoordinateEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (facet.activeCoordinateEquiv_apply rank).symm
  · rfl

/-- Helper for Remark 50.3: replacing a normalized facet's active staircase
produces another normalized facet. -/
private def SharedFacet.normalizedWithActiveStaircase {d m : ℕ}
    (facet : NormalizedSharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    NormalizedSharedFacet (d + 1) m :=
  ⟨facet.1.withActiveStaircase staircase,
    SharedFacet.withActiveStaircase_normalized facet staircase⟩

/-- Helper for Remark 50.3: a normalized seed stores a chosen fixed
coordinate and level before an active staircase is inserted. -/
private def SharedFacet.activeStaircaseSeed {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1)) :
    SharedFacet (d + 1) m :=
  { fixed := fixed
    level := level
    corner := fun _ ↦ ⟨0, Nat.mul_pos (Nat.succ_pos 1) hm⟩
    activeOrder := 1 }

/-- Helper for Remark 50.3: the seed's irrelevant fixed corner is normalized. -/
private lemma SharedFacet.activeStaircaseSeed_normalized {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1)) :
    ((SharedFacet.activeStaircaseSeed hm fixed level).corner
      (SharedFacet.activeStaircaseSeed hm fixed level).fixed).1 = 0 := by
  -- Every seed corner is the canonical zero coordinate.
  rfl

/-- Helper for Remark 50.3: insert an elementary staircase into the ambient
coordinates complementary to a chosen fixed coordinate. -/
private def SharedFacet.fromActiveStaircase {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    NormalizedSharedFacet (d + 1) m :=
  SharedFacet.normalizedWithActiveStaircase
    ⟨SharedFacet.activeStaircaseSeed hm fixed level,
      SharedFacet.activeStaircaseSeed_normalized hm fixed level⟩ staircase

/-- Helper for Remark 50.3: inserting an active staircase retains the chosen
fixed coordinate. -/
private lemma SharedFacet.fromActiveStaircase_fixed {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.fixed =
      fixed := by
  -- The active replacement does not alter the seed's fixed coordinate.
  rfl

/-- Helper for Remark 50.3: inserting an active staircase retains the chosen
fixed-coordinate level. -/
private lemma SharedFacet.fromActiveStaircase_level {d m : ℕ} (hm : 0 < m)
    (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.level =
      level := by
  -- The active replacement does not alter the seed's level.
  rfl

/-- Helper for Remark 50.3: active compression recovers an inserted
elementary staircase exactly. -/
private lemma SharedFacet.activeStaircase_fromActiveStaircase {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.activeStaircase =
      staircase := by
  -- Apply the existing compression rule to the normalized seed replacement.
  exact (SharedFacet.activeStaircaseSeed hm fixed level).activeStaircase_withActiveStaircase
    staircase

/-- Helper for Remark 50.3: an inserted facet's active coordinates follow
the standard complement equivalence at its chosen fixed coordinate. -/
private lemma SharedFacet.fromActiveStaircase_activeCoordinate {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) (rank : Fin (d + 1)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.activeCoordinate rank =
      (SharedFacet.activeCoordinateEquivAt fixed rank).1 := by
  -- Both sides apply the same transposition to the successor rank.
  rfl

/-- Helper for Remark 50.3: replacing an active staircase preserves the
fixed-coordinate value of every shared-facet vertex. -/
private lemma SharedFacet.withActiveStaircase_vertex_fixed {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (facet.withActiveStaircase staircase).vertex j facet.fixed =
      facet.vertex j facet.fixed := by
  -- Both vertex formulas use the unchanged fixed level at this coordinate.
  apply Fin.ext
  rw [(facet.withActiveStaircase staircase).vertex_value, facet.vertex_value]
  simp only [SharedFacet.withActiveStaircase, if_pos]

/-- Helper for Remark 50.3: replacing an active staircase makes its vertices
the active-coordinate projection of the resulting shared-facet vertices. -/
private lemma SharedFacet.withActiveStaircase_vertex_activeCoordinate {d m : ℕ}
    (facet : SharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).vertex j
        (facet.activeCoordinate rank) = staircase.vertex j rank := by
  -- Pass through active compression, whose replacement computation is exact.
  calc
    (facet.withActiveStaircase staircase).vertex j
          (facet.activeCoordinate rank) =
        (facet.withActiveStaircase staircase).vertex j
          ((facet.withActiveStaircase staircase).activeCoordinate rank) :=
      congrArg ((facet.withActiveStaircase staircase).vertex j)
        (facet.withActiveStaircase_activeCoordinate staircase rank).symm
    _ = (facet.withActiveStaircase staircase).activeStaircase.vertex j rank :=
      (congrFun
        ((facet.withActiveStaircase staircase).activeStaircase_vertex j)
        rank).symm
    _ = staircase.vertex j rank :=
      congrArg (fun active ↦ active.vertex j rank)
        (facet.activeStaircase_withActiveStaircase staircase)

/-- Helper for Remark 50.3: every vertex of an inserted facet has the chosen
level at its fixed coordinate. -/
private lemma SharedFacet.fromActiveStaircase_vertex_fixed {d m : ℕ}
    (hm : 0 < m) (fixed : Fin (d + 2)) (level : Fin (2 * m + 1))
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j fixed =
      level := by
  -- First discard the inserted active data, then evaluate the seed's fixed branch.
  calc
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j fixed =
        (SharedFacet.activeStaircaseSeed hm fixed level).vertex j fixed :=
      (SharedFacet.activeStaircaseSeed hm fixed level).withActiveStaircase_vertex_fixed
        staircase j
    _ = level := by
      apply Fin.ext
      rw [(SharedFacet.activeStaircaseSeed hm fixed level).vertex_value]
      simp only [SharedFacet.activeStaircaseSeed, if_pos]

/-- Helper for Remark 50.3: every active-coordinate vertex of an inserted
facet is the corresponding vertex of the supplied staircase. -/
private lemma SharedFacet.fromActiveStaircase_vertex_activeCoordinate
    {d m : ℕ} (hm : 0 < m) (fixed : Fin (d + 2))
    (level : Fin (2 * m + 1)) (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (SharedFacet.fromActiveStaircase hm fixed level staircase).1.vertex j
        (SharedFacet.activeCoordinateEquivAt fixed rank).1 =
      staircase.vertex j rank := by
  -- Rewrite the standard complement coordinate as the seed's active coordinate.
  exact (SharedFacet.activeStaircaseSeed hm fixed level)
    |>.withActiveStaircase_vertex_activeCoordinate staircase j rank

/-- Helper for Remark 50.3: replace a boundary facet's active staircase
without changing its top-or-bottom boundary tag. -/
private def BoundarySharedFacet.withActiveStaircase {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    BoundarySharedFacet (d + 1) m :=
  match facet with
  | Sum.inl top => Sum.inl
      ⟨SharedFacet.normalizedWithActiveStaircase top.1 staircase, top.2⟩
  | Sum.inr bottom => Sum.inr
      ⟨SharedFacet.normalizedWithActiveStaircase bottom.1 staircase, bottom.2⟩

/-- Helper for Remark 50.3: replacing a boundary facet's active staircase
preserves each fixed-coordinate vertex value. -/
private lemma BoundarySharedFacet.withActiveStaircase_vertex_fixed {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) (j : Fin (d + 2)) :
    (facet.withActiveStaircase staircase).vertex j
        facet.normalizedFacet.1.fixed =
      facet.vertex j facet.normalizedFacet.1.fixed := by
  -- Remove the unchanged boundary tag and use the raw fixed-coordinate formula.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.withActiveStaircase_vertex_fixed staircase j
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.withActiveStaircase_vertex_fixed staircase j

/-- Helper for Remark 50.3: the replacement staircase is the active-coordinate
projection of the resulting boundary-facet vertices. -/
private lemma BoundarySharedFacet.withActiveStaircase_vertex_activeCoordinate
    {d m : ℕ} (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m)
    (j : Fin (d + 2)) (rank : Fin (d + 1)) :
    (facet.withActiveStaircase staircase).vertex j
        (facet.normalizedFacet.1.activeCoordinate rank) =
      staircase.vertex j rank := by
  -- Remove the unchanged boundary tag and use the raw active-coordinate formula.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.withActiveStaircase_vertex_activeCoordinate staircase j rank
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.withActiveStaircase_vertex_activeCoordinate staircase j rank

/-- Helper for Remark 50.3: active compression of a replaced boundary facet
recovers the replacement staircase. -/
private lemma BoundarySharedFacet.activeStaircase_withActiveStaircase
    {d m : ℕ} (facet : BoundarySharedFacet (d + 1) m)
    (staircase : ElementaryStaircase (d + 1) m) :
    (facet.withActiveStaircase staircase).normalizedFacet.1.activeStaircase =
      staircase := by
  -- Remove the unchanged boundary tag and use the raw compression computation.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.normalizedWithActiveStaircase] using
        top.1.1.activeStaircase_withActiveStaircase staircase
  | inr bottom =>
      simpa only [BoundarySharedFacet.withActiveStaircase,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.normalizedWithActiveStaircase] using
        bottom.1.1.activeStaircase_withActiveStaircase staircase

/-- Helper for Remark 50.3: the fixed coordinate has the same value at every
vertex of a boundary shared facet. -/
private lemma BoundarySharedFacet.vertex_fixed_eq {d m : ℕ}
    (facet : BoundarySharedFacet (d + 1) m) (j k : Fin (d + 2)) :
    facet.vertex j facet.normalizedFacet.1.fixed =
      facet.vertex k facet.normalizedFacet.1.fixed := by
  -- On either boundary side the shared-facet formula is the unchanged fixed level.
  cases facet with
  | inl top =>
      apply Fin.ext
      rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        top.1.1.vertex_value, top.1.1.vertex_value]
      simp only [if_pos]
  | inr bottom =>
      apply Fin.ext
      rw [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        bottom.1.1.vertex_value, bottom.1.1.vertex_value]
      simp only [if_pos]

/-- Helper for Remark 50.3: equality of the initial and final vertices of two
shared facets determines their distinguished fixed coordinate. -/
private lemma SharedFacet.fixed_eq_of_endpoint_vertices_eq {d m : ℕ}
    (first second : SharedFacet d m)
    (hzero : first.vertex 0 = second.vertex 0)
    (hlast : first.vertex (Fin.last d) = second.vertex (Fin.last d)) :
    second.fixed = first.fixed := by
  -- At the first facet's fixed coordinate its endpoint values agree, whereas
  -- every active coordinate of the second facet increases exactly once.
  by_contra hfixed
  have hactive : first.fixed ≠ second.fixed := Ne.symm hfixed
  have hrankNeZero : second.leadingOrder.symm first.fixed ≠ 0 :=
    second.leadingOrder_symm_ne_zero hactive
  have hzeroCut :
      ¬(second.leadingOrder.symm first.fixed).1 < (0 : Fin (d + 1)).1 + 1 := by
    have hrankPositive : 0 < (second.leadingOrder.symm first.fixed).1 :=
      Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hrankNeZero)
    simpa only [Fin.val_zero, zero_add] using Nat.not_lt.mpr hrankPositive
  have hlastCut :
      (second.leadingOrder.symm first.fixed).1 <
        (Fin.last d : Fin (d + 1)).1 + 1 := by
    simpa only [Fin.val_last] using
      (second.leadingOrder.symm first.fixed).isLt
  have hzeroValue := congrArg
    (fun vertex : CenteredGrid (d + 1) m ↦ (vertex first.fixed).1) hzero
  have hlastValue := congrArg
    (fun vertex : CenteredGrid (d + 1) m ↦ (vertex first.fixed).1) hlast
  rw [first.vertex_value, second.vertex_value] at hzeroValue hlastValue
  rw [if_pos rfl, if_neg hactive, if_neg hzeroCut] at hzeroValue
  rw [if_pos rfl, if_neg hactive, if_pos hlastCut] at hlastValue
  omega

/-- Helper for Remark 50.3: pointwise equality of two internally retained
ridge enumerations determines the distinguished coordinate of their facets. -/
private lemma BoundaryRidgeOccurrence.fixed_eq_of_vertex_eq_of_internal
    {d m : ℕ} (first second : BoundaryRidgeOccurrence d m)
    (hzero : first.omitted ≠ 0) (hlast : first.omitted ≠ Fin.last d)
    (hvertex : first.vertex = second.vertex)
    (homitted : second.omitted = first.omitted) :
    second.facet.normalizedFacet.1.fixed =
      first.facet.normalizedFacet.1.fixed := by
  -- Internal deletion retains both full-facet endpoints; transport their
  -- equality through the common omitted position and use endpoint rigidity.
  have homittedPositive : 0 < first.omitted.1 := Fin.pos_iff_ne_zero.mpr hzero
  have homittedLtLast : first.omitted.1 < d := by
    exact Fin.lt_last_iff_ne_last.mpr hlast
  have hdPositive : 0 < d := by omega
  have hOnePositive : 0 < 1 := by omega
  have hSubLast : d - 1 < d := Nat.sub_lt hdPositive hOnePositive
  let zeroIndex : Fin d := ⟨0, hdPositive⟩
  let lastIndex : Fin d := ⟨d - 1, hSubLast⟩
  have hsuccZero : first.omitted.succAbove zeroIndex = 0 := by
    calc
      first.omitted.succAbove zeroIndex = zeroIndex.castSucc :=
        Fin.succAbove_of_castSucc_lt first.omitted zeroIndex (by
          exact Fin.mk_lt_mk.mpr homittedPositive)
      _ = 0 := by rfl
  have hsuccLast : first.omitted.succAbove lastIndex = Fin.last d := by
    calc
      first.omitted.succAbove lastIndex = lastIndex.succ :=
        Fin.succAbove_of_le_castSucc first.omitted lastIndex (by
          exact Fin.mk_le_mk.mpr (Nat.le_pred_of_lt homittedLtLast))
      _ = Fin.last d := by
        apply Fin.ext
        simp only [lastIndex, Fin.val_succ, Fin.val_last]
        omega
  apply SharedFacet.fixed_eq_of_endpoint_vertices_eq
  · simpa only [BoundaryRidgeOccurrence.vertex,
      BoundarySharedFacet.vertex_eq_normalizedFacet, homitted, hsuccZero] using
      congrFun hvertex zeroIndex
  · simpa only [BoundaryRidgeOccurrence.vertex,
      BoundarySharedFacet.vertex_eq_normalizedFacet, homitted, hsuccLast] using
      congrFun hvertex lastIndex

/-- Helper for Remark 50.3: at positive mesh radius, equality of underlying
normalized boundary facets also determines their top-or-bottom tags. -/
private lemma BoundarySharedFacet.eq_of_normalizedFacet_eq {d m : ℕ}
    (first second : BoundarySharedFacet d m) (hm : 0 < m)
    (hfacet : second.normalizedFacet = first.normalizedFacet) :
    second = first := by
  -- Equal tags reduce to subtype equality. Opposite tags would force the
  -- common fixed level to be simultaneously zero and `2 * m`.
  cases first with
  | inl firstTop =>
      cases second with
      | inl secondTop =>
          apply congrArg Sum.inl
          apply Subtype.ext
          simpa only [BoundarySharedFacet.normalizedFacet_inl] using hfacet
      | inr secondBottom =>
          have hlevel := congrArg
            (fun facet : NormalizedSharedFacet d m ↦ facet.1.level.1) hfacet
          rw [BoundarySharedFacet.normalizedFacet_inr,
            BoundarySharedFacet.normalizedFacet_inl,
            secondBottom.2, firstTop.2] at hlevel
          omega
  | inr firstBottom =>
      cases second with
      | inl secondTop =>
          have hlevel := congrArg
            (fun facet : NormalizedSharedFacet d m ↦ facet.1.level.1) hfacet
          rw [BoundarySharedFacet.normalizedFacet_inl,
            BoundarySharedFacet.normalizedFacet_inr,
            secondTop.2, firstBottom.2] at hlevel
          omega
      | inr secondBottom =>
          apply congrArg Sum.inr
          apply Subtype.ext
          simpa only [BoundarySharedFacet.normalizedFacet_inr] using hfacet

/-- Helper for Remark 50.3: swap the adjacent active directions around an
internal omitted vertex of a shared facet. -/
private def SharedFacet.internalRidgeMate {d m : ℕ} (facet : SharedFacet d m)
    (omitted : Fin (d + 1)) (hzero : omitted ≠ 0)
    (hlast : omitted ≠ Fin.last d) : SharedFacet d m :=
  { facet with
    activeOrder := facet.activeOrder *
      Equiv.swap (omitted.pred hzero) (omitted.castPred hlast) }

/-- Helper for Remark 50.3: swapping the same two internal active directions
twice restores the shared facet. -/
private lemma SharedFacet.internalRidgeMate_involutive {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    (facet.internalRidgeMate omitted hzero hlast).internalRidgeMate
        omitted hzero hlast = facet := by
  -- Only the active order changes, and the adjacent transposition squares to one.
  cases facet
  simp [SharedFacet.internalRidgeMate, mul_assoc]

/-- Helper for Remark 50.3: the adjacent-order internal mate is distinct
from its original shared facet. -/
private lemma SharedFacet.internalRidgeMate_ne {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    facet.internalRidgeMate omitted hzero hlast ≠ facet := by
  -- A fixed point would identify the two distinct active ranks adjacent to the omission.
  intro hfixed
  have horder := congrArg SharedFacet.activeOrder hfixed
  have happly := congrArg
    (fun order : Equiv.Perm (Fin d) ↦ order (omitted.pred hzero)) horder
  have hadjacent : omitted.castPred hlast = omitted.pred hzero := by
    apply facet.activeOrder.injective
    simpa [SharedFacet.internalRidgeMate, Equiv.Perm.mul_apply] using happly
  have hvalue := congrArg Fin.val hadjacent
  have hpositive : 0 < omitted.1 := Fin.pos_iff_ne_zero.mpr hzero
  simp only [Fin.coe_castPred, Fin.val_pred] at hvalue
  omega

/-- Helper for Remark 50.3: the adjacent-order mate preserves every rank cut
retained after deleting an internal vertex. -/
private lemma SharedFacet.internalRidgeMate_rank_lt_succAbove_iff {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d)
    {i : Fin (d + 1)} (hi : i ≠ facet.fixed) (j : Fin d) :
    (((facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i).1 <
        (omitted.succAbove j).1 + 1) ↔
      (facet.leadingOrder.symm i).1 < (omitted.succAbove j).1 + 1 := by
  -- Express the old nonfixed rank as a successor in the active-coordinate order.
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero
    (facet.leadingOrder_symm_ne_zero hi)
  have hmate :
      (facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i =
        (Equiv.swap (omitted.pred hzero) (omitted.castPred hlast) r).succ := by
    -- Applying the mate order cancels the adjacent swap and returns the coordinate.
    apply (facet.internalRidgeMate omitted hzero hlast).leadingOrder.injective
    rw [(facet.internalRidgeMate omitted hzero hlast).leadingOrder.apply_symm_apply]
    rw [(facet.internalRidgeMate omitted hzero hlast).leadingOrder_succ]
    simp only [SharedFacet.internalRidgeMate, Equiv.Perm.mul_apply,
      Equiv.swap_apply_self]
    rw [← facet.leadingOrder_succ, hr, facet.leadingOrder.apply_symm_apply]
  -- Cancel the common successor offset and apply the imported cut invariance.
  simpa only [hmate, ← hr, Fin.val_succ, Nat.add_lt_add_iff_right] using
    internalFaceMate_rank_lt_succAbove_iff omitted hzero hlast r j

/-- Helper for Remark 50.3: swapping the active directions adjacent to an
internal omission preserves every retained shared-facet vertex. -/
private lemma SharedFacet.internalRidgeMate_vertex {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) (j : Fin d) :
    (facet.internalRidgeMate omitted hzero hlast).vertex
        (omitted.succAbove j) = facet.vertex (omitted.succAbove j) := by
  -- The fixed coordinate is unchanged; active coordinates use the retained-cut law.
  funext i
  apply Fin.ext
  rw [(facet.internalRidgeMate omitted hzero hlast).vertex_value,
    facet.vertex_value]
  have hfixed :
      (facet.internalRidgeMate omitted hzero hlast).fixed = facet.fixed := rfl
  have hlevel :
      (facet.internalRidgeMate omitted hzero hlast).level = facet.level := rfl
  have hcorner :
      (facet.internalRidgeMate omitted hzero hlast).corner = facet.corner := rfl
  rw [hfixed, hlevel, hcorner]
  by_cases hi : i = facet.fixed
  · simp only [hi, if_pos]
  · simp only [hi, if_false]
    have hcut :=
      facet.internalRidgeMate_rank_lt_succAbove_iff omitted hzero hlast hi j
    by_cases hretained :
        (facet.leadingOrder.symm i).1 < (omitted.succAbove j).1 + 1
    · have hmateRetained := hcut.mpr hretained
      simp only [hmateRetained, hretained, if_pos]
    · have hmateRetained :
          ¬(((facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i).1 <
            (omitted.succAbove j).1 + 1) := fun h ↦ hretained (hcut.mp h)
      simp only [hmateRetained, hretained, if_false]

/-- Helper for Remark 50.3: the internal adjacent-order swap preserves the
normalization certificate of a shared facet. -/
private def SharedFacet.internalNormalizedRidgeMate {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    NormalizedSharedFacet d m :=
  ⟨facet.1.internalRidgeMate omitted hzero hlast, facet.2⟩

/-- Helper for Remark 50.3: the normalized internal adjacent-order mate is
an involution. -/
private lemma SharedFacet.internalNormalizedRidgeMate_involutive {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    SharedFacet.internalNormalizedRidgeMate
        (SharedFacet.internalNormalizedRidgeMate facet omitted hzero hlast)
        omitted hzero hlast = facet := by
  -- Subtype equality reduces to the raw shared-facet involution.
  apply Subtype.ext
  exact facet.1.internalRidgeMate_involutive omitted hzero hlast

/-- Helper for Remark 50.3: the normalized internal adjacent-order mate has
no fixed point. -/
private lemma SharedFacet.internalNormalizedRidgeMate_ne {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    SharedFacet.internalNormalizedRidgeMate facet omitted hzero hlast ≠ facet := by
  -- Equality of normalized facets would identify their underlying raw facets.
  intro hfixed
  exact facet.1.internalRidgeMate_ne omitted hzero hlast
    (congrArg Subtype.val hfixed)

/-- Helper for Remark 50.3: apply the internal adjacent-order mate while
preserving the extreme boundary tag. -/
private def BoundarySharedFacet.internalRidgeMate {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    BoundarySharedFacet d m :=
  match facet with
  | Sum.inl top => Sum.inl
      ⟨SharedFacet.internalNormalizedRidgeMate top.1 omitted hzero hlast, top.2⟩
  | Sum.inr bottom => Sum.inr
      ⟨SharedFacet.internalNormalizedRidgeMate bottom.1 omitted hzero hlast,
        bottom.2⟩

/-- Helper for Remark 50.3: the internally paired boundary facet returns
after applying the same adjacent-order swap twice. -/
private lemma BoundarySharedFacet.internalRidgeMate_involutive {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    (facet.internalRidgeMate omitted hzero hlast).internalRidgeMate
        omitted hzero hlast = facet := by
  -- Each boundary-tag branch reduces to normalized-facet involutivity.
  cases facet with
  | inl top =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact SharedFacet.internalNormalizedRidgeMate_involutive
        top.1 omitted hzero hlast
  | inr bottom =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact SharedFacet.internalNormalizedRidgeMate_involutive
        bottom.1 omitted hzero hlast

/-- Helper for Remark 50.3: the internally paired boundary facet is distinct
from its original adjacent-order presentation. -/
private lemma BoundarySharedFacet.internalRidgeMate_ne {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    facet.internalRidgeMate omitted hzero hlast ≠ facet := by
  -- Injectivity of each sum tag exposes the normalized fixed-point contradiction.
  cases facet with
  | inl top =>
      intro hfixed
      have htop := Sum.inl.inj hfixed
      exact SharedFacet.internalNormalizedRidgeMate_ne top.1 omitted hzero hlast
        (congrArg Subtype.val htop)
  | inr bottom =>
      intro hfixed
      have hbottom := Sum.inr.inj hfixed
      exact SharedFacet.internalNormalizedRidgeMate_ne bottom.1 omitted hzero hlast
        (congrArg Subtype.val hbottom)

/-- Helper for Remark 50.3: the tagged boundary-facet mate preserves every
vertex retained after an internal omission. -/
private lemma BoundarySharedFacet.internalRidgeMate_vertex {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) (j : Fin d) :
    (facet.internalRidgeMate omitted hzero hlast).vertex
        (omitted.succAbove j) = facet.vertex (omitted.succAbove j) := by
  -- Remove the boundary tag and invoke the raw shared-facet vertex theorem.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.internalNormalizedRidgeMate] using
        top.1.1.internalRidgeMate_vertex omitted hzero hlast j
  | inr bottom =>
      simpa only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.internalNormalizedRidgeMate] using
        bottom.1.1.internalRidgeMate_vertex omitted hzero hlast j

/-- Helper for Remark 50.3: forgetting the boundary tag of an internal mate
gives the normalized adjacent-order mate. -/
private lemma BoundarySharedFacet.internalRidgeMate_normalizedFacet {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    (facet.internalRidgeMate omitted hzero hlast).normalizedFacet =
      SharedFacet.internalNormalizedRidgeMate facet.normalizedFacet
        omitted hzero hlast := by
  -- Both boundary tags retain the same normalized mate data.
  cases facet with
  | inl top =>
      simp only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.normalizedFacet_inl]
  | inr bottom =>
      simp only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.normalizedFacet_inr]

/-- Helper for Remark 50.3: an internal ridge's pointwise retained vertices
determine its boundary facet up to the adjacent-order mate. -/
private lemma BoundaryRidgeOccurrence.facet_eq_or_eq_internalMate_of_vertex_eq
    {d m : ℕ} (first second : BoundaryRidgeOccurrence d m)
    (hzero : first.omitted ≠ 0) (hlast : first.omitted ≠ Fin.last d)
    (hvertex : first.vertex = second.vertex) :
    second.facet = first.facet ∨
      second.facet = first.facet.internalRidgeMate
        first.omitted hzero hlast := by
  -- The rank gap first identifies the common omission; retained endpoint
  -- vertices then recover the fixed coordinate.
  have homitted := first.omitted_eq_of_vertex_eq_of_internal
    second hzero hlast hvertex
  have hfixed := first.fixed_eq_of_vertex_eq_of_internal
    second hzero hlast hvertex homitted
  have hdPositive : 0 < d := by
    have homittedPositive : 0 < first.omitted.1 :=
      Fin.pos_iff_ne_zero.mpr hzero
    omega
  let zeroIndex : Fin d := ⟨0, hdPositive⟩
  have hsuccZero : first.omitted.succAbove zeroIndex = 0 := by
    calc
      first.omitted.succAbove zeroIndex = zeroIndex.castSucc :=
        Fin.succAbove_of_castSucc_lt first.omitted zeroIndex
          (Fin.mk_lt_mk.mpr (Fin.pos_iff_ne_zero.mpr hzero))
      _ = 0 := by rfl
  -- A retained vertex evaluated at the common fixed coordinate recovers the
  -- fixed level without inspecting either boundary tag.
  have hlevel : second.facet.normalizedFacet.1.level =
      first.facet.normalizedFacet.1.level := by
    calc
      second.facet.normalizedFacet.1.level =
          second.vertex zeroIndex second.facet.normalizedFacet.1.fixed :=
        (second.vertex_fixed zeroIndex).symm
      _ = second.vertex zeroIndex first.facet.normalizedFacet.1.fixed := by
        rw [hfixed]
      _ = first.vertex zeroIndex first.facet.normalizedFacet.1.fixed :=
        congrArg
          (fun vertex : CenteredGrid (d + 1) m ↦
            vertex first.facet.normalizedFacet.1.fixed)
          (congrFun hvertex zeroIndex).symm
      _ = first.facet.normalizedFacet.1.level := first.vertex_fixed zeroIndex
  -- Vertex zero is retained by an internal omission, so it recovers every
  -- active corner; normalization recovers the remaining fixed entry.
  have hcorner : second.facet.normalizedFacet.1.corner =
      first.facet.normalizedFacet.1.corner := by
    funext i
    apply Fin.ext
    by_cases hi : i = first.facet.normalizedFacet.1.fixed
    · subst i
      have hsecondNormalized := second.facet.normalizedFacet.2
      rw [hfixed] at hsecondNormalized
      exact hsecondNormalized.trans first.facet.normalizedFacet.2.symm
    · have hiSecond : i ≠ second.facet.normalizedFacet.1.fixed := by
        intro hieq
        exact hi (hieq.trans hfixed)
      calc
        (second.facet.normalizedFacet.1.corner i).1 =
            (second.facet.normalizedFacet.1.vertex 0 i).1 :=
          (second.facet.normalizedFacet.1.vertex_zero_of_ne_fixed
            i hiSecond).symm
        _ = (second.vertex zeroIndex i).1 := by
          rw [BoundaryRidgeOccurrence.vertex,
            BoundarySharedFacet.vertex_eq_normalizedFacet, homitted, hsuccZero]
        _ = (first.vertex zeroIndex i).1 :=
          congrArg (fun vertex : CenteredGrid (d + 1) m ↦ (vertex i).1)
            (congrFun hvertex zeroIndex).symm
        _ = (first.facet.normalizedFacet.1.vertex 0 i).1 := by
          rw [BoundaryRidgeOccurrence.vertex,
            BoundarySharedFacet.vertex_eq_normalizedFacet, hsuccZero]
        _ = (first.facet.normalizedFacet.1.corner i).1 :=
          first.facet.normalizedFacet.1.vertex_zero_of_ne_fixed i hi
  -- Equality at every retained vertex makes all retained active-order cuts
  -- agree, which is exactly the interface of the permutation classifier.
  have hcuts (i j : Fin d) :
      ((first.facet.normalizedFacet.1.activeOrder.symm i).1 <
          (first.omitted.succAbove j).1 ↔
        (second.facet.normalizedFacet.1.activeOrder.symm i).1 <
          (first.omitted.succAbove j).1) := by
    let coordinate := first.facet.normalizedFacet.1.activeCoordinate i
    have hactiveCoordinate :
        second.facet.normalizedFacet.1.activeCoordinate i = coordinate := by
      unfold coordinate SharedFacet.activeCoordinate
      rw [hfixed]
    have hfirstCoordinateNe :
        coordinate ≠ first.facet.normalizedFacet.1.fixed :=
      first.facet.normalizedFacet.1.activeCoordinate_ne_fixed i
    have hsecondCoordinateNe :
        coordinate ≠ second.facet.normalizedFacet.1.fixed := by
      rw [← hactiveCoordinate]
      exact second.facet.normalizedFacet.1.activeCoordinate_ne_fixed i
    have hfirstRank :
        first.facet.normalizedFacet.1.leadingOrder.symm coordinate =
          (first.facet.normalizedFacet.1.activeOrder.symm i).succ :=
      first.facet.normalizedFacet.1.leadingOrder_symm_activeCoordinate i
    have hsecondRank :
        second.facet.normalizedFacet.1.leadingOrder.symm coordinate =
          (second.facet.normalizedFacet.1.activeOrder.symm i).succ := by
      rw [← hactiveCoordinate]
      exact second.facet.normalizedFacet.1.leadingOrder_symm_activeCoordinate i
    have hvalue := congrArg
      (fun vertex : CenteredGrid (d + 1) m ↦ (vertex coordinate).1)
      (congrFun hvertex j)
    simp only [BoundaryRidgeOccurrence.vertex,
      BoundarySharedFacet.vertex_eq_normalizedFacet, homitted] at hvalue
    rw [first.facet.normalizedFacet.1.vertex_value,
      second.facet.normalizedFacet.1.vertex_value] at hvalue
    rw [if_neg hfirstCoordinateNe, if_neg hsecondCoordinateNe,
      hfirstRank, hsecondRank, hcorner] at hvalue
    simp only [Fin.val_succ] at hvalue
    constructor
    · intro hfirstCut
      by_contra hsecondCut
      have hfirstCut' :
          (first.facet.normalizedFacet.1.activeOrder.symm i).1 + 1 <
            (first.omitted.succAbove j).1 + 1 := by omega
      have hsecondCut' :
          ¬(second.facet.normalizedFacet.1.activeOrder.symm i).1 + 1 <
            (first.omitted.succAbove j).1 + 1 := by omega
      rw [if_pos hfirstCut', if_neg hsecondCut'] at hvalue
      omega
    · intro hsecondCut
      by_contra hfirstCut
      have hfirstCut' :
          ¬(first.facet.normalizedFacet.1.activeOrder.symm i).1 + 1 <
            (first.omitted.succAbove j).1 + 1 := by omega
      have hsecondCut' :
          (second.facet.normalizedFacet.1.activeOrder.symm i).1 + 1 <
            (first.omitted.succAbove j).1 + 1 := by omega
      rw [if_neg hfirstCut', if_pos hsecondCut'] at hvalue
      omega
  rcases Equiv.Perm.eq_or_eq_mul_swap_of_retainedCuts
      first.facet.normalizedFacet.1.activeOrder
      second.facet.normalizedFacet.1.activeOrder first.omitted
      hzero hlast hcuts with horder | horder
  · left
    apply BoundarySharedFacet.eq_of_normalizedFacet_eq first.facet second.facet
      first.facet.normalizedFacet.1.meshRadius_pos
    apply Subtype.ext
    exact SharedFacet.ext_of_fields _ _ hfixed hlevel hcorner horder
  · right
    apply BoundarySharedFacet.eq_of_normalizedFacet_eq
      (first.facet.internalRidgeMate first.omitted hzero hlast) second.facet
      first.facet.normalizedFacet.1.meshRadius_pos
    rw [BoundarySharedFacet.internalRidgeMate_normalizedFacet]
    apply Subtype.ext
    exact SharedFacet.ext_of_fields _ _ hfixed hlevel hcorner horder

/-- Helper for Remark 50.3: ambient boundary-ridge occurrences whose omitted
position is internal to the staircase order. -/
private abbrev InternalBoundaryRidgeOccurrence (d m : ℕ) :=
  {occurrence : BoundaryRidgeOccurrence d m //
    occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d}

/-- Helper for Remark 50.3: pair an internal ambient occurrence by swapping
the active directions adjacent to its omitted position. -/
private def boundaryRidgeInternalMate {d m : ℕ}
    (occurrence : InternalBoundaryRidgeOccurrence d m) :
    InternalBoundaryRidgeOccurrence d m :=
  ⟨⟨occurrence.1.facet.internalRidgeMate occurrence.1.omitted
      occurrence.2.1 occurrence.2.2, occurrence.1.omitted⟩, occurrence.2⟩

/-- Helper for Remark 50.3: every presentation of an internally omitted
ambient ridge is the original occurrence or its adjacent-order mate. -/
private lemma BoundaryRidgeOccurrence.eq_original_or_internalMate_of_ridgeVertexSet_eq
    {d m : ℕ} (occurrence candidate : BoundaryRidgeOccurrence d m)
    (hzero : occurrence.omitted ≠ 0)
    (hlast : occurrence.omitted ≠ Fin.last d)
    (hridge : candidate.ridgeVertexSet = occurrence.ridgeVertexSet) :
    candidate = occurrence ∨
      candidate =
        (boundaryRidgeInternalMate
          ⟨occurrence, hzero, hlast⟩ : InternalBoundaryRidgeOccurrence d m).1 := by
  -- Normalize the common unordered ridge to pointwise equality, then combine
  -- the recovered facet alternative with the already identified omission.
  have hvertex := occurrence.vertex_eq_of_ridgeVertexSet_eq
    candidate hridge.symm
  have homitted := occurrence.omitted_eq_of_vertex_eq_of_internal
    candidate hzero hlast hvertex
  rcases occurrence.facet_eq_or_eq_internalMate_of_vertex_eq
      candidate hzero hlast hvertex with hfacet | hfacet
  · exact Or.inl (congrArg₂ BoundaryRidgeOccurrence.mk hfacet homitted)
  · right
    simpa only [boundaryRidgeInternalMate] using
      congrArg₂ BoundaryRidgeOccurrence.mk hfacet homitted

/-- Helper for Remark 50.3: the internal ambient occurrence mate is an
involution. -/
private lemma boundaryRidgeInternalMate_involutive {d m : ℕ} :
    Function.Involutive
      (boundaryRidgeInternalMate : InternalBoundaryRidgeOccurrence d m →
        InternalBoundaryRidgeOccurrence d m) := by
  intro occurrence
  -- The omitted position is fixed while the boundary-facet mate squares to one.
  apply Subtype.ext
  exact congrArg₂ BoundaryRidgeOccurrence.mk
    (occurrence.1.facet.internalRidgeMate_involutive occurrence.1.omitted
      occurrence.2.1 occurrence.2.2) rfl

/-- Helper for Remark 50.3: the internal ambient occurrence mate has no fixed
points. -/
private lemma boundaryRidgeInternalMate_ne {d m : ℕ}
    (occurrence : InternalBoundaryRidgeOccurrence d m) :
    boundaryRidgeInternalMate occurrence ≠ occurrence := by
  -- A fixed occurrence would force its internally paired facets to coincide.
  intro hfixed
  have hvalue := congrArg Subtype.val hfixed
  exact occurrence.1.facet.internalRidgeMate_ne occurrence.1.omitted
    occurrence.2.1 occurrence.2.2
    (congrArg BoundaryRidgeOccurrence.facet hvalue)

/-- Helper for Remark 50.3: the internal occurrence mate presents the same
unordered boundary ridge. -/
private lemma boundaryRidgeInternalMate_ridgeVertexSet {d m : ℕ}
    (occurrence : InternalBoundaryRidgeOccurrence d m) :
    (boundaryRidgeInternalMate occurrence).1.ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift pointwise preservation of retained vertices to their finite images.
  unfold BoundaryRidgeOccurrence.ridgeVertexSet
  apply Finset.image_congr
  intro j _
  simpa only [boundaryRidgeInternalMate, BoundaryRidgeOccurrence.vertex] using
    occurrence.1.facet.internalRidgeMate_vertex occurrence.1.omitted
      occurrence.2.1 occurrence.2.2 j

/-- Helper for Remark 50.3: every internal ambient boundary-ridge occurrence
has a distinct occurrence presenting the same unordered ridge. -/
private lemma exists_distinct_boundaryRidgeMate_of_internal {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m)
    (hzero : occurrence.omitted ≠ 0)
    (hlast : occurrence.omitted ≠ Fin.last d) :
    ∃ mate : BoundaryRidgeOccurrence d m,
      mate ≠ occurrence ∧ mate.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- Package the verified internal involution as the required second presentation.
  let internal : InternalBoundaryRidgeOccurrence d m :=
    ⟨occurrence, hzero, hlast⟩
  refine ⟨(boundaryRidgeInternalMate internal).1, ?_,
    boundaryRidgeInternalMate_ridgeVertexSet internal⟩
  intro hmate
  apply boundaryRidgeInternalMate_ne internal
  exact Subtype.ext hmate

/-- Helper for Remark 50.3: an internally omitted ambient boundary ridge has
a unique distinct occurrence presenting the same unordered ridge. -/
private lemma BoundaryRidgeOccurrence.existsUnique_distinctMate_of_internal
    {d m : ℕ} (occurrence : BoundaryRidgeOccurrence d m)
    (hzero : occurrence.omitted ≠ 0)
    (hlast : occurrence.omitted ≠ Fin.last d) :
    ∃! mate : BoundaryRidgeOccurrence d m,
      mate ≠ occurrence ∧ mate.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- The explicit adjacent-order mate supplies existence. The internal
  -- classifier forces every other distinct presentation to be that mate.
  let internal : InternalBoundaryRidgeOccurrence d m :=
    ⟨occurrence, hzero, hlast⟩
  refine ⟨(boundaryRidgeInternalMate internal).1, ⟨?_, ?_⟩, ?_⟩
  · intro hmate
    apply boundaryRidgeInternalMate_ne internal
    exact Subtype.ext hmate
  · exact boundaryRidgeInternalMate_ridgeVertexSet internal
  · intro candidate hcandidate
    rcases occurrence.eq_original_or_internalMate_of_ridgeVertexSet_eq
        candidate hzero hlast hcandidate.2 with horiginal | hmate
    · exact (hcandidate.1 horiginal).elim
    · exact hmate

/-- Helper for Remark 50.3: endpoint ambient boundary-ridge occurrences are
exactly those whose omitted position is not internal. -/
private abbrev EndpointBoundaryRidgeOccurrence (d m : ℕ) :=
  {occurrence : BoundaryRidgeOccurrence d m //
    ¬(occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d)}

/-- Helper for Remark 50.3: an endpoint boundary-ridge occurrence omits the
initial or final staircase vertex. -/
private lemma EndpointBoundaryRidgeOccurrence.omitted_eq_zero_or_last
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence d m) :
    occurrence.1.omitted = 0 ∨ occurrence.1.omitted = Fin.last d := by
  -- Eliminate the internal alternative from the finite endpoint dichotomy.
  by_cases hzero : occurrence.1.omitted = 0
  · exact Or.inl hzero
  · right
    by_contra hlast
    exact occurrence.2 ⟨hzero, hlast⟩

/-- Helper for Remark 50.3: compress an endpoint boundary-ridge occurrence
to the endpoint occurrence of its active elementary staircase. -/
private def EndpointBoundaryRidgeOccurrence.activeOccurrence {d m : ℕ}
    (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m) :
    EndpointStaircaseFaceOccurrence d m :=
  ⟨⟨occurrence.1.facet.normalizedFacet.1.activeStaircase,
      occurrence.1.omitted⟩, occurrence.2⟩

/-- Helper for Remark 50.3: active compression preserves every retained
ridge vertex after projecting away the boundary facet's fixed coordinate. -/
private lemma EndpointBoundaryRidgeOccurrence.activeOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (j rank : Fin (d + 1)) :
    occurrence.activeOccurrence.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- First use active-staircase compression at the retained simplex position.
  rw [EndpointBoundaryRidgeOccurrence.activeOccurrence,
    StaircaseFaceOccurrence.mk_vertex, BoundaryRidgeOccurrence.vertex]
  rw [occurrence.1.facet.vertex_eq_normalizedFacet]
  exact congrFun
    (occurrence.1.facet.normalizedFacet.1.activeStaircase_vertex
      (occurrence.1.omitted.succAbove j)) rank

/-- Helper for Remark 50.3: lift a compressed staircase-face occurrence to
the original ambient boundary side. -/
private def EndpointBoundaryRidgeOccurrence.liftActiveOccurrence {d m : ℕ}
    (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m) :
    BoundaryRidgeOccurrence (d + 1) m :=
  ⟨occurrence.1.facet.withActiveStaircase active.simplex, active.omitted⟩

/-- Helper for Remark 50.3: lift a compressed endpoint occurrence while
retaining its endpoint certificate. -/
private def EndpointBoundaryRidgeOccurrence.liftActiveEndpointOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (active : EndpointStaircaseFaceOccurrence d m) :
    EndpointBoundaryRidgeOccurrence (d + 1) m :=
  ⟨occurrence.liftActiveOccurrence active.1, active.2⟩

/-- Helper for Remark 50.3: compressing a lifted endpoint occurrence returns
the endpoint occurrence that was lifted. -/
private lemma EndpointBoundaryRidgeOccurrence.activeOccurrence_liftActiveEndpoint
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (active : EndpointStaircaseFaceOccurrence d m) :
    (occurrence.liftActiveEndpointOccurrence active).activeOccurrence = active := by
  -- The lifted facet compresses to the supplied simplex and retains its omission.
  apply Subtype.ext
  rw [← active.1.mk_eq_self]
  exact congrArg₂ StaircaseFaceOccurrence.mk
    (occurrence.1.facet.activeStaircase_withActiveStaircase active.1.simplex) rfl

/-- Helper for Remark 50.3: a lifted compressed occurrence with the original
compressed vertices preserves every ambient retained vertex. -/
private lemma EndpointBoundaryRidgeOccurrence.liftActiveOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m)
    (hvertex : active.vertex = occurrence.activeOccurrence.1.vertex)
    (j : Fin (d + 1)) :
    (occurrence.liftActiveOccurrence active).vertex j =
      occurrence.1.vertex j := by
  -- The fixed coordinate is constant; every other coordinate has a unique active rank.
  funext i
  by_cases hi : i = occurrence.1.facet.normalizedFacet.1.fixed
  · subst i
    calc
      (occurrence.liftActiveOccurrence active).vertex j
            occurrence.1.facet.normalizedFacet.1.fixed =
          occurrence.1.facet.vertex (active.omitted.succAbove j)
            occurrence.1.facet.normalizedFacet.1.fixed :=
        occurrence.1.facet.withActiveStaircase_vertex_fixed active.simplex
          (active.omitted.succAbove j)
      _ = occurrence.1.facet.vertex
            (occurrence.1.omitted.succAbove j)
            occurrence.1.facet.normalizedFacet.1.fixed :=
        occurrence.1.facet.vertex_fixed_eq _ _
      _ = occurrence.1.vertex j
            occurrence.1.facet.normalizedFacet.1.fixed := rfl
  · let rank : Fin (d + 1) :=
      occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv.symm ⟨i, hi⟩
    have hrank :
        occurrence.1.facet.normalizedFacet.1.activeCoordinate rank = i := by
      calc
        occurrence.1.facet.normalizedFacet.1.activeCoordinate rank =
            (occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv rank).1 :=
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv_apply rank).symm
        _ = i := congrArg Subtype.val
          (Equiv.apply_symm_apply
            occurrence.1.facet.normalizedFacet.1.activeCoordinateEquiv ⟨i, hi⟩)
    calc
      (occurrence.liftActiveOccurrence active).vertex j i =
          (occurrence.liftActiveOccurrence active).vertex j
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
        congrArg ((occurrence.liftActiveOccurrence active).vertex j) hrank.symm
      _ = active.simplex.vertex (active.omitted.succAbove j) rank :=
        occurrence.1.facet.withActiveStaircase_vertex_activeCoordinate
          active.simplex (active.omitted.succAbove j) rank
      _ = (StaircaseFaceOccurrence.mk active.simplex active.omitted).vertex j
            rank :=
        congrArg (fun vertex ↦ vertex rank)
          (StaircaseFaceOccurrence.mk_vertex active.simplex active.omitted j).symm
      _ = active.vertex j rank :=
        congrArg (fun face ↦ face.vertex j rank) active.mk_eq_self
      _ = occurrence.activeOccurrence.1.vertex j rank :=
        congrArg (fun vertex ↦ vertex j rank) hvertex
      _ = occurrence.1.vertex j
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
        occurrence.activeOccurrence_vertex j rank
      _ = occurrence.1.vertex j i :=
        congrArg (occurrence.1.vertex j) hrank

/-- Helper for Remark 50.3: equality of compressed vertex enumerations lifts
to equality of the ambient unordered ridge. -/
private lemma EndpointBoundaryRidgeOccurrence.liftActiveOccurrence_preserves_ridge
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (active : StaircaseFaceOccurrence (d + 1) m)
    (hvertex : active.vertex = occurrence.activeOccurrence.1.vertex) :
    (occurrence.liftActiveOccurrence active).ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift the pointwise ambient computation through the two finite images.
  unfold BoundaryRidgeOccurrence.ridgeVertexSet
  apply Finset.image_congr
  intro j _
  exact occurrence.liftActiveOccurrence_vertex active hvertex j

/-- Helper for Remark 50.3: normalize a compressed endpoint ridge into its
lower or upper shared-facet presentation. -/
private def EndpointBoundaryRidgeOccurrence.normalForm {d m : ℕ}
    (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m) :
    PositiveNormalizedSharedFacet d m ⊕ BelowTopNormalizedSharedFacet d m :=
  endpointStaircaseFaceEquiv d m occurrence.activeOccurrence

/-- Helper for Remark 50.3: the endpoint normal form enumerates precisely the
active-coordinate projection of the original ambient ridge. -/
private lemma EndpointBoundaryRidgeOccurrence.normalForm_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (j rank : Fin (d + 1)) :
    Sum.elim (fun facet ↦ facet.1.1.vertex)
        (fun facet ↦ facet.1.1.vertex) occurrence.normalForm j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- The endpoint equivalence preserves the compressed ridge, and compression
  -- itself preserves the corresponding active coordinates.
  calc
    Sum.elim (fun facet ↦ facet.1.1.vertex)
          (fun facet ↦ facet.1.1.vertex) occurrence.normalForm j rank =
        occurrence.activeOccurrence.1.vertex j rank := by
      exact congrArg (fun vertex ↦ vertex j rank)
        (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
    _ = occurrence.1.vertex j
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
      occurrence.activeOccurrence_vertex j rank

/-- Helper for Remark 50.3: when the old outer facet is on top, the
exchanged inner facet has a lower adjacent cube. -/
private lemma SharedFacet.exchangedActiveFacet_level_pos_of_top {d m : ℕ}
    (outer : TopBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    0 < (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 := by
  -- The exchanged level is the positive top grid level.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]
  have hm := inner.1.meshRadius_pos
  omega

/-- Helper for Remark 50.3: when the old outer facet is on the bottom, the
exchanged inner facet has an upper adjacent cube. -/
private lemma SharedFacet.exchangedActiveFacet_level_lt_of_bottom {d m : ℕ}
    (outer : BottomBoundaryNormalizedSharedFacet (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (SharedFacet.exchangedActiveFacet outer.1 inner).1.level.1 < 2 * m := by
  -- The exchanged level is zero and the inner facet forces a positive mesh.
  rw [SharedFacet.exchangedActiveFacet_level, outer.2]
  have hm := inner.1.meshRadius_pos
  omega

/-- Helper for Remark 50.3: present the exchanged inner facet from the side
selected by the old outer boundary tag. -/
private def EndpointBoundaryRidgeOccurrence.exchangedActiveOccurrence
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) : StaircaseFaceOccurrence (d + 1) m :=
  match occurrence.1.facet with
  | Sum.inl top =>
      (SharedFacet.exchangedActiveFacet top.1 inner).1.lowerOccurrence
        (SharedFacet.exchangedActiveFacet_level_pos_of_top top inner)
  | Sum.inr bottom =>
      (SharedFacet.exchangedActiveFacet bottom.1 inner).1.upperOccurrence
        (SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner)

/-- Helper for Remark 50.3: an occurrence's retained vertex is its simplex
vertex at the corresponding successor-above position. -/
private lemma StaircaseFaceOccurrence.vertex_eq_simplexVertex {d m : ℕ}
    (occurrence : StaircaseFaceOccurrence d m) (j : Fin d) :
    occurrence.vertex j =
      occurrence.simplex.vertex (occurrence.omitted.succAbove j) := by
  -- Rebuild the occurrence from its projections and apply the owner computation rule.
  rw [← occurrence.mk_eq_self]
  exact StaircaseFaceOccurrence.mk_vertex _ _ j

/-- Helper for Remark 50.3: the exchanged active occurrence enumerates the
vertices of its exchanged inner facet. -/
private lemma EndpointBoundaryRidgeOccurrence.exchangedActiveOccurrence_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (occurrence.exchangedActiveOccurrence inner).vertex j =
      (SharedFacet.exchangedActiveFacet
        occurrence.1.facet.normalizedFacet inner).1.vertex j := by
  -- Use the lower or upper occurrence computation according to the boundary tag.
  cases hfacet : occurrence.1.facet with
  | inl top =>
      simpa only [EndpointBoundaryRidgeOccurrence.exchangedActiveOccurrence,
        hfacet, BoundarySharedFacet.normalizedFacet_inl] using
        (SharedFacet.exchangedActiveFacet top.1 inner).1.lowerOccurrence_vertex
          (SharedFacet.exchangedActiveFacet_level_pos_of_top top inner) j
  | inr bottom =>
      simpa only [EndpointBoundaryRidgeOccurrence.exchangedActiveOccurrence,
        hfacet, BoundarySharedFacet.normalizedFacet_inr] using
        (SharedFacet.exchangedActiveFacet bottom.1 inner).1.upperOccurrence_vertex
          (SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner) j

/-- Helper for Remark 50.3: rebuild an ambient normalized facet with the
inner fixed coordinate as its new outer fixed coordinate. -/
private def EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) : NormalizedSharedFacet (d + 1) m :=
  SharedFacet.fromActiveStaircase inner.1.meshRadius_pos
    (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed)
    inner.1.level (occurrence.exchangedActiveOccurrence inner).simplex

/-- Helper for Remark 50.3: the rebuilt ambient facet fixes the old inner
fixed coordinate in ambient coordinates. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (occurrence.extremeCornerAmbientFacet inner).1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed := by
  -- Apply the fixed-coordinate computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_fixed _ _ _ _

/-- Helper for Remark 50.3: the rebuilt ambient facet has the old inner
fixed level. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_level
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) :
    (occurrence.extremeCornerAmbientFacet inner).1.level = inner.1.level := by
  -- Apply the level computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_level _ _ _ _

/-- Helper for Remark 50.3: every rebuilt ambient-facet vertex has the old
inner level at the new fixed coordinate. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_vertex_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (k : Fin (d + 2)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex k
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed) =
      inner.1.level := by
  -- Apply the fixed-coordinate vertex computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_vertex_fixed _ _ _ _ _

/-- Helper for Remark 50.3: on every new active coordinate, the rebuilt
ambient facet uses the exchanged active occurrence's simplex. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_vertex_active
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (k : Fin (d + 2))
    (rank : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex k
        (SharedFacet.activeCoordinateEquivAt
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed)
          rank).1 =
      (occurrence.exchangedActiveOccurrence inner).simplex.vertex k rank := by
  -- Apply the active-coordinate computation for active-staircase insertion.
  exact SharedFacet.fromActiveStaircase_vertex_activeCoordinate _ _ _ _ _ _

/-- Helper for Remark 50.3: at the old outer fixed coordinate, the rebuilt
corner facet and the original ridge have the same retained value. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_oldFixed
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m) (j : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
        occurrence.1.facet.normalizedFacet.1.fixed =
      occurrence.1.vertex j occurrence.1.facet.normalizedFacet.1.fixed := by
  -- Follow the exchanged fixed rank through the inserted active staircase.
  calc
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          occurrence.1.facet.normalizedFacet.1.fixed =
        (occurrence.exchangedActiveOccurrence inner).simplex.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed) := by
      rw [← occurrence.1.facet.normalizedFacet.1
        |>.activeCoordinateExchangeEquiv_fixed_ambient inner.1.fixed]
      exact occurrence.extremeCornerAmbientFacet_vertex_active inner _ _
    _ = (occurrence.exchangedActiveOccurrence inner).vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed inner.1.fixed) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed))
        (StaircaseFaceOccurrence.vertex_eq_simplexVertex
          (occurrence.exchangedActiveOccurrence inner) j).symm
    _ = (SharedFacet.exchangedActiveFacet
          occurrence.1.facet.normalizedFacet inner).1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed inner.1.fixed) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed inner.1.fixed))
        (occurrence.exchangedActiveOccurrence_vertex inner j)
    _ = occurrence.1.facet.normalizedFacet.1.level :=
      SharedFacet.exchangedActiveFacet_vertex_fixed
        occurrence.1.facet.normalizedFacet inner j
    _ = occurrence.1.vertex j occurrence.1.facet.normalizedFacet.1.fixed :=
      (occurrence.1.vertex_fixed j).symm

/-- Helper for Remark 50.3: at every residual active coordinate, the rebuilt
corner facet and the represented original ridge have the same retained value. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_residual
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (hvertex : ∀ j rank, inner.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank))
    (j rank : Fin (d + 1)) (hrank : rank ≠ inner.1.fixed) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Follow the residual exchanged rank and then use the inner vertex specification.
  calc
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) =
        (occurrence.exchangedActiveOccurrence inner).simplex.vertex
          ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank) := by
      rw [← occurrence.1.facet.normalizedFacet.1
        |>.activeCoordinateExchangeEquiv_residual_ambient
          inner.1.fixed rank hrank]
      exact occurrence.extremeCornerAmbientFacet_vertex_active inner _ _
    _ = (occurrence.exchangedActiveOccurrence inner).vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed rank) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank))
        (StaircaseFaceOccurrence.vertex_eq_simplexVertex
          (occurrence.exchangedActiveOccurrence inner) j).symm
    _ = (SharedFacet.exchangedActiveFacet
          occurrence.1.facet.normalizedFacet inner).1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
          inner.1.fixed rank) :=
      congrArg
        (fun vertex ↦ vertex
          (occurrence.1.facet.normalizedFacet.1.activeCoordinateExchangeEquiv
            inner.1.fixed rank))
        (occurrence.exchangedActiveOccurrence_vertex inner j)
    _ = inner.1.vertex j rank :=
      SharedFacet.exchangedActiveFacet_vertex_exchange
        occurrence.1.facet.normalizedFacet inner j rank hrank
    _ = occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) :=
      hvertex j rank

/-- Helper for Remark 50.3: if an inner normal form represents the original
active ridge, the rebuilt corner facet retains every original ridge vertex. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_retainedVertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (hvertex : ∀ j rank, inner.1.vertex j rank =
      occurrence.1.vertex j
        (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank))
    (j : Fin (d + 1)) :
    (occurrence.extremeCornerAmbientFacet inner).1.vertex
        ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j) =
      occurrence.1.vertex j := by
  -- Split ambient coordinates into the new fixed coordinate and its
  -- complement; the latter is either the old fixed coordinate or residual.
  funext i
  by_cases hi :
      i = occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed
  · subst i
    calc
      (occurrence.extremeCornerAmbientFacet inner).1.vertex
            ((occurrence.exchangedActiveOccurrence inner).omitted.succAbove j)
            (occurrence.1.facet.normalizedFacet.1.activeCoordinate
              inner.1.fixed) = inner.1.level :=
        occurrence.extremeCornerAmbientFacet_vertex_fixed inner _
      _ = inner.1.vertex j inner.1.fixed :=
        (inner.1.vertex_fixed j).symm
      _ = occurrence.1.vertex j
          (occurrence.1.facet.normalizedFacet.1.activeCoordinate inner.1.fixed) :=
        hvertex j inner.1.fixed
  · rcases occurrence.1.facet.normalizedFacet.1
        |>.exchangeCoordinate_eq_fixed_or_active inner.1.fixed hi with
      hiOuter | ⟨rank, hrank, hiResidual⟩
    · rw [hiOuter]
      exact occurrence.extremeCornerAmbientFacet_oldFixed inner j
    · rw [hiResidual]
      exact occurrence.extremeCornerAmbientFacet_residual inner hvertex j rank hrank

/-- Helper for Remark 50.3: an extreme lower normal form supplies the inner
vertex specification needed by the coordinate-exchange construction. -/
private lemma EndpointBoundaryRidgeOccurrence.normalForm_inl_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower) (j rank : Fin (d + 1)) :
    lower.1.1.vertex j rank = occurrence.1.vertex j
      (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Select the lower summand in the normal-form vertex computation.
  simpa only [hnormal, Sum.elim_inl] using occurrence.normalForm_vertex j rank

/-- Helper for Remark 50.3: an extreme upper normal form supplies the inner
vertex specification needed by the coordinate-exchange construction. -/
private lemma EndpointBoundaryRidgeOccurrence.normalForm_inr_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper) (j rank : Fin (d + 1)) :
    upper.1.1.vertex j rank = occurrence.1.vertex j
      (occurrence.1.facet.normalizedFacet.1.activeCoordinate rank) := by
  -- Select the upper summand in the normal-form vertex computation.
  simpa only [hnormal, Sum.elim_inr] using occurrence.normalForm_vertex j rank

/-- Helper for Remark 50.3: a top extreme inner normal form makes the rebuilt
ambient facet a top boundary facet. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_top
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeCornerAmbientFacet lower.1).1.level.1 = 2 * m := by
  -- The rebuilt ambient level is exactly the inner normal-form level.
  rw [occurrence.extremeCornerAmbientFacet_level lower.1]
  exact htop

/-- Helper for Remark 50.3: a bottom extreme inner normal form makes the
rebuilt ambient facet a bottom boundary facet. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeCornerAmbientFacet_bottom
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeCornerAmbientFacet upper.1).1.level.1 = 0 := by
  -- The rebuilt ambient level is exactly the inner normal-form level.
  rw [occurrence.extremeCornerAmbientFacet_level upper.1]
  exact hbottom

/-- Helper for Remark 50.3: build the alternate ambient ridge occurrence at
a top extreme coordinate corner. -/
private def EndpointBoundaryRidgeOccurrence.extremeTopMate
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) : BoundaryRidgeOccurrence (d + 1) m :=
  { facet := Sum.inl
      ⟨occurrence.extremeCornerAmbientFacet lower.1,
        occurrence.extremeCornerAmbientFacet_top lower htop⟩
    omitted := (occurrence.exchangedActiveOccurrence lower.1).omitted }

/-- Helper for Remark 50.3: build the alternate ambient ridge occurrence at
a bottom extreme coordinate corner. -/
private def EndpointBoundaryRidgeOccurrence.extremeBottomMate
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) : BoundaryRidgeOccurrence (d + 1) m :=
  { facet := Sum.inr
      ⟨occurrence.extremeCornerAmbientFacet upper.1,
        occurrence.extremeCornerAmbientFacet_bottom upper hbottom⟩
    omitted := (occurrence.exchangedActiveOccurrence upper.1).omitted }

/-- Helper for Remark 50.3: the top corner mate fixes the ambient coordinate
represented by the old inner fixed rank. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeTopMate_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (htop : lower.1.1.level.1 = 2 * m) :
    (occurrence.extremeTopMate lower htop).facet.normalizedFacet.1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate lower.1.1.fixed := by
  -- Forget the top tag and apply the rebuilt facet's fixed-coordinate formula.
  rw [EndpointBoundaryRidgeOccurrence.extremeTopMate,
    BoundarySharedFacet.normalizedFacet_inl]
  exact occurrence.extremeCornerAmbientFacet_fixed lower.1

/-- Helper for Remark 50.3: the bottom corner mate fixes the ambient coordinate
represented by the old inner fixed rank. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeBottomMate_fixed
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hbottom : upper.1.1.level.1 = 0) :
    (occurrence.extremeBottomMate upper hbottom).facet.normalizedFacet.1.fixed =
      occurrence.1.facet.normalizedFacet.1.activeCoordinate upper.1.1.fixed := by
  -- Forget the bottom tag and apply the rebuilt facet's fixed-coordinate formula.
  rw [EndpointBoundaryRidgeOccurrence.extremeBottomMate,
    BoundarySharedFacet.normalizedFacet_inr]
  exact occurrence.extremeCornerAmbientFacet_fixed upper.1

/-- Helper for Remark 50.3: the top corner mate retains every original
ridge vertex pointwise. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeTopMate_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower)
    (htop : lower.1.1.level.1 = 2 * m) (j : Fin (d + 1)) :
    (occurrence.extremeTopMate lower htop).vertex j = occurrence.1.vertex j := by
  -- Remove the top boundary tag and use the coordinatewise rebuilt-facet theorem.
  simpa only [BoundaryRidgeOccurrence.vertex,
    EndpointBoundaryRidgeOccurrence.extremeTopMate,
    BoundarySharedFacet.vertex_eq_normalizedFacet,
    BoundarySharedFacet.normalizedFacet_inl] using
    occurrence.extremeCornerAmbientFacet_retainedVertex lower.1
      (occurrence.normalForm_inl_vertex lower hnormal) j

/-- Helper for Remark 50.3: the bottom corner mate retains every original
ridge vertex pointwise. -/
private lemma EndpointBoundaryRidgeOccurrence.extremeBottomMate_vertex
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper)
    (hbottom : upper.1.1.level.1 = 0) (j : Fin (d + 1)) :
    (occurrence.extremeBottomMate upper hbottom).vertex j = occurrence.1.vertex j := by
  -- Remove the bottom boundary tag and use the coordinatewise rebuilt-facet theorem.
  simpa only [BoundaryRidgeOccurrence.vertex,
    EndpointBoundaryRidgeOccurrence.extremeBottomMate,
    BoundarySharedFacet.vertex_eq_normalizedFacet,
    BoundarySharedFacet.normalizedFacet_inr] using
    occurrence.extremeCornerAmbientFacet_retainedVertex upper.1
      (occurrence.normalForm_inr_vertex upper hnormal) j

/-- Helper for Remark 50.3: a top extreme endpoint occurrence has a distinct
ambient mate with the same unordered ridge. -/
private lemma exists_distinct_boundaryRidgeMate_of_endpoint_top
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (lower : PositiveNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inl lower)
    (htop : lower.1.1.level.1 = 2 * m) :
    ∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Distinguish the exchanged fixed coordinate, then lift pointwise vertex
  -- equality to the unordered finite image.
  refine ⟨occurrence.extremeTopMate lower htop, ?_, ?_⟩
  · intro heq
    have hfixed := congrArg
      (fun mate : BoundaryRidgeOccurrence (d + 1) m ↦
        mate.facet.normalizedFacet.1.fixed) heq
    rw [occurrence.extremeTopMate_fixed lower htop] at hfixed
    exact occurrence.1.facet.normalizedFacet.1
      |>.activeCoordinate_ne_fixed lower.1.1.fixed hfixed
  · unfold BoundaryRidgeOccurrence.ridgeVertexSet
    apply Finset.image_congr
    intro j _
    exact occurrence.extremeTopMate_vertex lower hnormal htop j

/-- Helper for Remark 50.3: a bottom extreme endpoint occurrence has a
distinct ambient mate with the same unordered ridge. -/
private lemma exists_distinct_boundaryRidgeMate_of_endpoint_bottom
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (upper : BelowTopNormalizedSharedFacet d m)
    (hnormal : occurrence.normalForm = Sum.inr upper)
    (hbottom : upper.1.1.level.1 = 0) :
    ∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Distinguish the exchanged fixed coordinate, then lift pointwise vertex
  -- equality to the unordered finite image.
  refine ⟨occurrence.extremeBottomMate upper hbottom, ?_, ?_⟩
  · intro heq
    have hfixed := congrArg
      (fun mate : BoundaryRidgeOccurrence (d + 1) m ↦
        mate.facet.normalizedFacet.1.fixed) heq
    rw [occurrence.extremeBottomMate_fixed upper hbottom] at hfixed
    exact occurrence.1.facet.normalizedFacet.1
      |>.activeCoordinate_ne_fixed upper.1.1.fixed hfixed
  · unfold BoundaryRidgeOccurrence.ridgeVertexSet
    apply Finset.image_congr
    intro j _
    exact occurrence.extremeBottomMate_vertex upper hnormal hbottom j

/-- Helper for Remark 50.3: every endpoint normal form is either on an
interior adjacent side or is one of the two extreme corner flags. -/
private lemma EndpointBoundaryRidgeOccurrence.normalForm_interior_or_corner
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m) :
    (∃ lower : PositiveNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inl lower ∧ lower.1.1.level.1 < 2 * m) ∨
    (∃ upper : BelowTopNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inr upper ∧ 0 < upper.1.1.level.1) ∨
    (∃ lower : PositiveNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inl lower ∧ lower.1.1.level.1 = 2 * m) ∨
    (∃ upper : BelowTopNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inr upper ∧ upper.1.1.level.1 = 0) := by
  -- Split by summand, then compare its level with the only missing endpoint.
  cases hnormal : occurrence.normalForm with
  | inl lower =>
      by_cases htop : lower.1.1.level.1 = 2 * m
      · exact Or.inr (Or.inr (Or.inl ⟨lower, rfl, htop⟩))
      · left
        refine ⟨lower, rfl, ?_⟩
        omega
  | inr upper =>
      by_cases hbottom : upper.1.1.level.1 = 0
      · exact Or.inr (Or.inr (Or.inr ⟨upper, rfl, hbottom⟩))
      · exact Or.inr (Or.inl ⟨upper, rfl, Nat.pos_of_ne_zero hbottom⟩)

/-- Helper for Remark 50.3: every endpoint occurrence whose normal form has
an adjacent cube on the opposite side has a distinct ambient mate. -/
private lemma exists_distinct_boundaryRidgeMate_of_endpoint_interior
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m)
    (hinterior : Sum.elim
      (fun lower : PositiveNormalizedSharedFacet d m ↦
        lower.1.1.level.1 < 2 * m)
      (fun upper : BelowTopNormalizedSharedFacet d m ↦
        0 < upper.1.1.level.1) occurrence.normalForm) :
    ∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Route correction: the imported equivalence does not expose summand/omission
  -- computation. Choose the opposite presentation through its inverse and
  -- distinguish it by the resulting incompatible normal-form summands.
  cases hnormal : occurrence.normalForm with
  | inl lower =>
      have hupper : lower.1.1.level.1 < 2 * m := by
        simpa only [hnormal, Sum.elim_inl] using hinterior
      let upper : BelowTopNormalizedSharedFacet d m := ⟨lower.1, hupper⟩
      let opposite : EndpointStaircaseFaceOccurrence d m :=
        (endpointStaircaseFaceEquiv d m).symm (Sum.inr upper)
      have hoppositeNormal :
          endpointStaircaseFaceEquiv d m opposite = Sum.inr upper :=
        Equiv.apply_symm_apply (endpointStaircaseFaceEquiv d m) (Sum.inr upper)
      have hvertex : opposite.1.vertex = occurrence.activeOccurrence.1.vertex := by
        calc
          opposite.1.vertex = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex)
              (endpointStaircaseFaceEquiv d m opposite) :=
            endpointStaircaseFaceEquiv_vertex opposite
          _ = lower.1.1.vertex := by
            simp only [hoppositeNormal, Sum.elim_inr, upper]
          _ = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex) occurrence.normalForm := by
            simp only [hnormal, Sum.elim_inl]
          _ = occurrence.activeOccurrence.1.vertex :=
            (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
      let lifted := occurrence.liftActiveEndpointOccurrence opposite
      refine ⟨lifted.1, ?_, ?_⟩
      · intro heq
        have hlifted : lifted = occurrence := Subtype.ext heq
        have hactive := congrArg
          EndpointBoundaryRidgeOccurrence.activeOccurrence hlifted
        rw [occurrence.activeOccurrence_liftActiveEndpoint opposite] at hactive
        have hnormalEq := congrArg (endpointStaircaseFaceEquiv d m) hactive
        have hcontradiction : Sum.inr upper = Sum.inl lower := by
          calc
            Sum.inr upper = endpointStaircaseFaceEquiv d m opposite :=
              hoppositeNormal.symm
            _ = endpointStaircaseFaceEquiv d m occurrence.activeOccurrence :=
              hnormalEq
            _ = occurrence.normalForm := rfl
            _ = Sum.inl lower := hnormal
        exact (Sum.inr_ne_inl hcontradiction).elim
      · exact occurrence.liftActiveOccurrence_preserves_ridge opposite.1 hvertex
  | inr upper =>
      have hlower : 0 < upper.1.1.level.1 := by
        simpa only [hnormal, Sum.elim_inr] using hinterior
      let lower : PositiveNormalizedSharedFacet d m := ⟨upper.1, hlower⟩
      let opposite : EndpointStaircaseFaceOccurrence d m :=
        (endpointStaircaseFaceEquiv d m).symm (Sum.inl lower)
      have hoppositeNormal :
          endpointStaircaseFaceEquiv d m opposite = Sum.inl lower :=
        Equiv.apply_symm_apply (endpointStaircaseFaceEquiv d m) (Sum.inl lower)
      have hvertex : opposite.1.vertex = occurrence.activeOccurrence.1.vertex := by
        calc
          opposite.1.vertex = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex)
              (endpointStaircaseFaceEquiv d m opposite) :=
            endpointStaircaseFaceEquiv_vertex opposite
          _ = upper.1.1.vertex := by
            simp only [hoppositeNormal, Sum.elim_inl, lower]
          _ = Sum.elim
              (fun facet ↦ facet.1.1.vertex)
              (fun facet ↦ facet.1.1.vertex) occurrence.normalForm := by
            simp only [hnormal, Sum.elim_inr]
          _ = occurrence.activeOccurrence.1.vertex :=
            (endpointStaircaseFaceEquiv_vertex occurrence.activeOccurrence).symm
      let lifted := occurrence.liftActiveEndpointOccurrence opposite
      refine ⟨lifted.1, ?_, ?_⟩
      · intro heq
        have hlifted : lifted = occurrence := Subtype.ext heq
        have hactive := congrArg
          EndpointBoundaryRidgeOccurrence.activeOccurrence hlifted
        rw [occurrence.activeOccurrence_liftActiveEndpoint opposite] at hactive
        have hnormalEq := congrArg (endpointStaircaseFaceEquiv d m) hactive
        have hcontradiction : Sum.inl lower = Sum.inr upper := by
          calc
            Sum.inl lower = endpointStaircaseFaceEquiv d m opposite :=
              hoppositeNormal.symm
            _ = endpointStaircaseFaceEquiv d m occurrence.activeOccurrence :=
              hnormalEq
            _ = occurrence.normalForm := rfl
            _ = Sum.inr upper := hnormal
        exact (Sum.inl_ne_inr hcontradiction).elim
      · exact occurrence.liftActiveOccurrence_preserves_ridge opposite.1 hvertex

/-- Helper for Remark 50.3: an endpoint occurrence either has the verified
same-side mate or is one of the two extreme coordinate-exchange corners. -/
private lemma EndpointBoundaryRidgeOccurrence.mate_or_extreme_corner
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m) :
    (∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet) ∨
    (∃ lower : PositiveNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inl lower ∧ lower.1.1.level.1 = 2 * m) ∨
    (∃ upper : BelowTopNormalizedSharedFacet d m,
      occurrence.normalForm = Sum.inr upper ∧ upper.1.1.level.1 = 0) := by
  -- Apply the interior mate theorem in the first two cases and retain the two corners.
  rcases occurrence.normalForm_interior_or_corner with
      ⟨lower, hnormal, hupper⟩ |
      ⟨upper, hnormal, hlower⟩ |
      ⟨lower, hnormal, htop⟩ |
      ⟨upper, hnormal, hbottom⟩
  · left
    apply exists_distinct_boundaryRidgeMate_of_endpoint_interior occurrence
    simpa only [hnormal, Sum.elim_inl] using hupper
  · left
    apply exists_distinct_boundaryRidgeMate_of_endpoint_interior occurrence
    simpa only [hnormal, Sum.elim_inr] using hlower
  · exact Or.inr (Or.inl ⟨lower, hnormal, htop⟩)
  · exact Or.inr (Or.inr ⟨upper, hnormal, hbottom⟩)

/-- Helper for Remark 50.3: every endpoint ambient boundary-ridge occurrence
has a distinct occurrence presenting the same unordered ridge. -/
private lemma exists_distinct_boundaryRidgeMate_of_endpoint
    {d m : ℕ} (occurrence : EndpointBoundaryRidgeOccurrence (d + 1) m) :
    ∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence.1 ∧ mate.ridgeVertexSet = occurrence.1.ridgeVertexSet := by
  -- Use the established interior mate or discharge the two remaining corners
  -- with the coordinate-exchange construction.
  rcases occurrence.mate_or_extreme_corner with
      hmate | ⟨lower, hnormal, htop⟩ | ⟨upper, hnormal, hbottom⟩
  · exact hmate
  · exact exists_distinct_boundaryRidgeMate_of_endpoint_top
      occurrence lower hnormal htop
  · exact exists_distinct_boundaryRidgeMate_of_endpoint_bottom
      occurrence upper hnormal hbottom

/-- Helper for Remark 50.3: every ambient boundary-ridge occurrence is either
internal, where the adjacent-order mate applies, or an endpoint occurrence. -/
private lemma boundaryRidgeOccurrence_internal_or_endpoint {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence d m) :
    (occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d) ∨
      ¬(occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d) := by
  -- This case split is decidable because omitted positions are finite.
  exact Classical.em _

/-- Helper for Remark 50.3: every ambient boundary-ridge occurrence has a
distinct occurrence presenting the same unordered ridge. -/
private lemma exists_distinct_boundaryRidgeMate {d m : ℕ}
    (occurrence : BoundaryRidgeOccurrence (d + 1) m) :
    ∃ mate : BoundaryRidgeOccurrence (d + 1) m,
      mate ≠ occurrence ∧ mate.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- Split at the omitted position and apply the internal or endpoint pairing theorem.
  rcases boundaryRidgeOccurrence_internal_or_endpoint occurrence with
      ⟨hzero, hlast⟩ | hendpoint
  · exact exists_distinct_boundaryRidgeMate_of_internal occurrence hzero hlast
  · exact exists_distinct_boundaryRidgeMate_of_endpoint
      (⟨occurrence, hendpoint⟩ : EndpointBoundaryRidgeOccurrence (d + 1) m)

end StandardSphere.CubicalTucker

/-- Helper for Remark 50.3: a point of the zero-dimensional standard sphere
has coordinate square equal to one. -/
private lemma sharpStandardSphereZero_coordinate_sq
    (x : sharpStandardSphere 0) : (x.1 0) ^ 2 = 1 := by
  -- In one Euclidean coordinate, the unit-norm equation is the desired square equation.
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have hnormSq := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hnormSq
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, one_pow] using hnormSq

/-- Helper for Remark 50.3: zero-sphere points are equal when their unique
real coordinates are equal. -/
private lemma sharpStandardSphereZero_ext {x y : sharpStandardSphere 0}
    (hcoordinate : x.1 0 = y.1 0) : x = y := by
  -- Extensionality leaves only the unique coordinate of `Fin 1`.
  apply Subtype.ext
  ext i
  simpa only [Fin.eq_zero i] using hcoordinate

/-- Helper for Remark 50.3: a continuous path in the zero-dimensional
standard sphere is constant. -/
private lemma sharpStandardSphereZero_path_constant
    (f : unitInterval → sharpStandardSphere 0) (hf : Continuous f)
    (s t : unitInterval) : f s = f t := by
  -- The unique coordinate has constant square one on the connected interval.
  let coordinate : unitInterval → ℝ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) ∘
      (Subtype.val : sharpStandardSphere 0 → EuclideanSpace ℝ (Fin 1)) ∘ f
  let reference : unitInterval → ℝ := fun _ ↦ (f s).1 0
  have hcoordinate : Continuous coordinate :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      (continuous_subtype_val.comp hf)
  have hreference : Continuous reference := continuous_const
  have hsquares : Set.EqOn (coordinate ^ 2) (reference ^ 2) Set.univ := by
    intro u _
    change (f u).1 0 ^ 2 = (f s).1 0 ^ 2
    rw [sharpStandardSphereZero_coordinate_sq,
      sharpStandardSphereZero_coordinate_sq]
  have hreferenceNe : ∀ {u : unitInterval}, u ∈ Set.univ → reference u ≠ 0 := by
    intro u _ hzero
    have hsquare := sharpStandardSphereZero_coordinate_sq (f s)
    change (f s).1 0 = 0 at hzero
    rw [hzero] at hsquare
    norm_num at hsquare
  have hconstant : Set.EqOn coordinate reference Set.univ :=
    isPreconnected_univ.eq_of_sq_eq hcoordinate.continuousOn
      hreference.continuousOn hsquares hreferenceNe (Set.mem_univ s) rfl
  -- Equality of the unique coordinates determines the two sphere points.
  apply sharpStandardSphereZero_ext
  exact (hconstant (Set.mem_univ t)).symm

/-- Helper for Remark 50.3: an odd self-map of the zero-dimensional standard
sphere cannot be nullhomotopic. -/
private lemma sharpOddSelfMapZero_not_nullhomotopic
    (h : C(sharpStandardSphere 0, sharpStandardSphere 0))
    (hodd : Function.Odd h) : ¬ h.Nullhomotopic := by
  -- A nullhomotopy would connect both antipodal values to the same endpoint.
  intro hnull
  obtain ⟨endpoint, ⟨H⟩⟩ := hnull
  have hsphereNonempty :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x, hx⟩ := hsphereNonempty
  let spherePoint : sharpStandardSphere 0 := ⟨x, hx⟩
  have hpath (z : sharpStandardSphere 0) : h z = endpoint := by
    calc
      h z = H (0, z) := (H.apply_zero z).symm
      _ = H (1, z) := by
        apply sharpStandardSphereZero_path_constant (fun u ↦ H (u, z))
        · fun_prop
      _ = endpoint := H.apply_one z
  have hantipodal : h (-spherePoint) = h spherePoint :=
    (hpath (-spherePoint)).trans (hpath spherePoint).symm
  rw [hodd spherePoint] at hantipodal
  have hcoordinate := congrArg
    (fun z : sharpStandardSphere 0 ↦ z.1 0) hantipodal
  change -(h spherePoint).1 0 = (h spherePoint).1 0 at hcoordinate
  nlinarith [sharpStandardSphereZero_coordinate_sq (h spherePoint)]

/-- Helper for Remark 50.3: every continuous odd self-map of a standard sphere
is not nullhomotopic. -/
private lemma sharpOddSelfMap_not_nullhomotopic (n : ℕ)
    (h : C(sharpStandardSphere n, sharpStandardSphere n))
    (hodd : Function.Odd h) : ¬ h.Nullhomotopic := by
  -- Route correction: the coordinate-exchange construction now completes the
  -- internal and endpoint pairing of every ambient boundary-ridge occurrence.
  -- The remaining route must classify which of those ambient cofacets lie in
  -- the positive hemisphere and then connect the resulting Fan parity to `h`.
  cases n with
  | zero =>
      -- The base sphere is discrete, so its two antipodal values cannot share a nullhomotopy.
      exact sharpOddSelfMapZero_not_nullhomotopic h hodd
  | succ n =>
      -- TODO: extend the proved internal original-or-mate classifier to
      -- endpoint normal forms, then determine when the unique ambient mate
      -- remains positive. The ridge-weight fiber lemma will reduce the positive
      -- sum to the equator and yield the Tucker contradiction for the extension.
      sorry

/-- Helper for Remark 50.3: every map from `S^(n+1)` to `ℝ^(n+1)` identifies
an antipodal pair. -/
private lemma existsAntipodalEq_sharpStandardSphere (n : ℕ)
    (f : C(sharpStandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ x, f x = f (-x) := by
  -- A counterexample normalizes to an odd dimension-lowering sphere map.
  by_contra hnopair
  push Not at hnopair
  obtain ⟨g, hgodd⟩ := existsOddSharpSphereMap_of_antipodal_ne f hnopair
  have hcompositeOdd : Function.Odd (g.comp (sharpEquator n)) := by
    intro x
    rw [ContinuousMap.comp_apply, sharpEquator_odd n x,
      ContinuousMap.comp_apply, hgodd]
  have hcompositeNull : (g.comp (sharpEquator n)).Nullhomotopic :=
    (sharpEquator_nullhomotopic n).comp_right g
  exact sharpOddSelfMap_not_nullhomotopic n
    (g.comp (sharpEquator n)) hcompositeOdd hcompositeNull

/-- Helper for Remark 50.3: adjoining the negative coordinate sum produces the
sum-zero vector used to split a sphere point into two simplex points. -/
private def radonSignedCoordinates (m : ℕ) (z : radonParameterSphere m) :
    Fin (2 * m + 3) → ℝ :=
  Fin.cons (-(∑ i, z.1 i)) (fun i ↦ z.1 i)

/-- Helper for Remark 50.3: the augmented coordinate vector has total sum zero. -/
private lemma radonSignedCoordinates_sum (m : ℕ) (z : radonParameterSphere m) :
    ∑ i, radonSignedCoordinates m z i = 0 := by
  -- The new leading coordinate cancels the sum of the sphere coordinates.
  simp only [radonSignedCoordinates, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    neg_add_cancel]

/-- Helper for Remark 50.3: antipodal sphere points give opposite augmented vectors. -/
private lemma radonSignedCoordinates_neg (m : ℕ) (z : radonParameterSphere m) :
    radonSignedCoordinates m (-z) = -radonSignedCoordinates m z := by
  -- Negation commutes with both the finite sum and the appended coordinate.
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [radonSignedCoordinates]
  · simp [radonSignedCoordinates]

/-- Helper for Remark 50.3: the total positive mass of the augmented vector. -/
private def radonPositiveMass (m : ℕ) (z : radonParameterSphere m) : ℝ :=
  ∑ i, (radonSignedCoordinates m z i)⁺

/-- Helper for Remark 50.3: every augmented sphere vector has positive positive-part mass. -/
private lemma radonPositiveMass_pos (m : ℕ) (z : radonParameterSphere m) :
    0 < radonPositiveMass m z := by
  -- If every positive part vanished, all sum-zero coordinates would vanish,
  -- contradicting that the original vector lies on the unit sphere.
  have hnonnegative : 0 ≤ radonPositiveMass m z :=
    Finset.sum_nonneg fun i _ ↦ posPart_nonneg (radonSignedCoordinates m z i)
  have hmassNonzero : radonPositiveMass m z ≠ 0 := by
    intro hmass
    have hpartZero (i : Fin (2 * m + 3)) :
        (radonSignedCoordinates m z i)⁺ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ posPart_nonneg (radonSignedCoordinates m z j))).mp hmass i
        (Finset.mem_univ i)
    have hsignedNonpositive (i : Fin (2 * m + 3)) :
        radonSignedCoordinates m z i ≤ 0 :=
      posPart_eq_zero.mp (hpartZero i)
    have hsignedZero (i : Fin (2 * m + 3)) :
        radonSignedCoordinates m z i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ ↦ hsignedNonpositive j)).mp (radonSignedCoordinates_sum m z) i
        (Finset.mem_univ i)
    have hzZero : z.1 = 0 := by
      apply PiLp.ext
      intro i
      simpa only [PiLp.zero_apply, radonSignedCoordinates, Fin.cons_succ] using
        hsignedZero i.succ
    have hzNorm : ‖z.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2
    rw [hzZero, norm_zero] at hzNorm
    norm_num at hzNorm
  exact lt_of_le_of_ne hnonnegative (Ne.symm hmassNonzero)

/-- Helper for Remark 50.3: normalized positive augmented coordinates belong to the simplex. -/
private lemma radonSimplexPoint_mem (m : ℕ) (z : radonParameterSphere m) :
    (fun i ↦ (radonSignedCoordinates m z i)⁺ / radonPositiveMass m z) ∈
      stdSimplex ℝ (Fin (2 * m + 3)) := by
  -- Positivity gives nonnegative coordinates, and normalization makes their sum one.
  constructor
  · intro i
    exact div_nonneg (posPart_nonneg _) (radonPositiveMass_pos m z).le
  · rw [← Finset.sum_div]
    apply div_self
    simpa only [radonPositiveMass] using (radonPositiveMass_pos m z).ne'

/-- Helper for Remark 50.3: the simplex point obtained by normalizing positive coordinates. -/
private noncomputable def radonSimplexPoint (m : ℕ) (z : radonParameterSphere m) :
    stdSimplex ℝ (Fin (2 * m + 3)) :=
  ⟨fun i ↦ (radonSignedCoordinates m z i)⁺ / radonPositiveMass m z,
    radonSimplexPoint_mem m z⟩

/-- Helper for Remark 50.3: each augmented coordinate varies continuously on the sphere. -/
private lemma continuous_radonSignedCoordinate (m : ℕ) (i : Fin (2 * m + 3)) :
    Continuous (fun z : radonParameterSphere m ↦ radonSignedCoordinates m z i) := by
  -- Split off the appended coordinate; both branches are finite coordinate expressions.
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [radonSignedCoordinates, Fin.cons_zero]
    fun_prop
  · simp only [radonSignedCoordinates, Fin.cons_succ]
    fun_prop

/-- Helper for Remark 50.3: positive augmented mass varies continuously. -/
private lemma continuous_radonPositiveMass (m : ℕ) :
    Continuous (radonPositiveMass m) := by
  -- It is a finite sum of continuous positive-part coordinate functions.
  unfold radonPositiveMass
  exact continuous_finsetSum _ fun i _ ↦
    continuous_posPart.comp (continuous_radonSignedCoordinate m i)

/-- Helper for Remark 50.3: the normalized positive-coordinate simplex point is continuous. -/
private lemma continuous_radonSimplexPoint (m : ℕ) :
    Continuous (radonSimplexPoint m) := by
  -- Divide each positive coordinate by the continuous nowhere-zero positive mass.
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_posPart.comp (continuous_radonSignedCoordinate m i)).div
    (continuous_radonPositiveMass m) fun z ↦ (radonPositiveMass_pos m z).ne'

/-- Helper for Remark 50.3: the simplex points associated to antipodal parameters
have disjoint supports. -/
private lemma radonSimplexPoint_supports_disjoint (m : ℕ) (z : radonParameterSphere m) :
    Disjoint {i | (radonSimplexPoint m z).1 i ≠ 0}
      {i | (radonSimplexPoint m (-z)).1 i ≠ 0} := by
  -- A coordinate and its negative cannot both have a nonzero positive part.
  rw [Set.disjoint_left]
  intro i hiz hineg
  change (radonSignedCoordinates m z i)⁺ / radonPositiveMass m z ≠ 0 at hiz
  change (radonSignedCoordinates m (-z) i)⁺ / radonPositiveMass m (-z) ≠ 0 at hineg
  have hzPartNonzero : (radonSignedCoordinates m z i)⁺ ≠ 0 := by
    intro hzero
    exact hiz (by rw [hzero, zero_div])
  have hnegPartNonzero : (radonSignedCoordinates m (-z) i)⁺ ≠ 0 := by
    intro hzero
    exact hineg (by rw [hzero, zero_div])
  have hzPositive : 0 < radonSignedCoordinates m z i :=
    posPart_pos_iff.mp (lt_of_le_of_ne (posPart_nonneg _) (Ne.symm hzPartNonzero))
  have hnegPositive : 0 < radonSignedCoordinates m (-z) i :=
    posPart_pos_iff.mp (lt_of_le_of_ne (posPart_nonneg _) (Ne.symm hnegPartNonzero))
  have hcoordinateNeg := congrFun (radonSignedCoordinates_neg m z) i
  rw [hcoordinateNeg, Pi.neg_apply] at hnegPositive
  linarith

/-- Helper for Remark 50.3: antipodal coincidence on the parameter sphere implies
the topological Radon coincidence needed by the constraint argument. -/
private lemma topologicalRadon_of_antipodalCoincidence (m : ℕ)
    (hAntipodal :
      ∀ f : C(radonParameterSphere m, EuclideanSpace ℝ (Fin (2 * m + 1))),
        ∃ z, f z = f (-z)) :
    HasTopologicalRadonCoincidence m := by
  intro g
  -- Apply antipodal coincidence to the difference of the images of the two
  -- normalized positive-coordinate simplex points.
  let differenceMap : C(radonParameterSphere m, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun z ↦ g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z)), by
      have hpoint := continuous_radonSimplexPoint m
      have hnegPoint : Continuous (fun z : radonParameterSphere m ↦
          radonSimplexPoint m (-z)) := by
        fun_prop
      exact (g.continuous.comp hpoint).sub (g.continuous.comp hnegPoint)⟩
  obtain ⟨z, hcollision⟩ := hAntipodal differenceMap
  refine ⟨radonSimplexPoint m z, radonSimplexPoint m (-z), ?_,
    radonSimplexPoint_supports_disjoint m z⟩
  have hdifference :
      g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z)) =
        g (radonSimplexPoint m (-z)) - g (radonSimplexPoint m z) := by
    simpa only [differenceMap, ContinuousMap.coe_mk, neg_neg] using hcollision
  have hselfNegative :
      g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z)) =
        -(g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z))) := by
    simpa only [neg_sub] using hdifference
  have hzero :
      g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z)) = 0 := by
    -- Compare coordinates, where a real number equal to its negative is zero.
    apply PiLp.ext
    intro i
    have hi := congrArg
      (fun v : EuclideanSpace ℝ (Fin (2 * m + 1)) ↦ v i) hselfNegative
    simp only [PiLp.neg_apply] at hi
    change
      (g (radonSimplexPoint m z) - g (radonSimplexPoint m (-z))) i = (0 : ℝ)
    linarith
  exact sub_eq_zero.mp hzero

/-- Helper for Remark 50.3: topological Radon implies the van Kampen--Flores
nonembedding obstruction for the barycentric simplex skeleton. -/
private lemma barycentricSimplexSkeleton_notEmbeddable_of_radon (m : ℕ)
    (hRadon : HasTopologicalRadonCoincidence m) :
    ¬ ∃ f : barycentricSimplexSkeleton.{u} m → EuclideanSpace ℝ (Fin (2 * m)),
      Topology.IsEmbedding f := by
  classical
  -- Extend a hypothetical embedding from the closed skeleton to the full simplex.
  rintro ⟨f, hf⟩
  let liftedInclusion : barycentricSimplexSkeletonSet m →
      barycentricSimplexSkeleton.{u} m := Homeomorph.ulift.symm
  let skeletonMap : C(barycentricSimplexSkeletonSet m,
      EuclideanSpace ℝ (Fin (2 * m))) :=
    ⟨f ∘ liftedInclusion, hf.continuous.comp Homeomorph.ulift.symm.continuous⟩
  obtain ⟨extension, hextension⟩ :=
    skeletonMap.exists_extension'
      (barycentricSimplexSkeletonSet_isClosed m).isClosedEmbedding_subtypeVal
  let distanceCoordinate : C(stdSimplex ℝ (Fin (2 * m + 3)),
      EuclideanSpace ℝ (Fin 1)) :=
    ⟨fun x ↦ (EuclideanSpace.equiv (Fin 1) ℝ).symm
        (fun _ ↦ Metric.infDist x (barycentricSimplexSkeletonSet m)),
      (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.comp
        (continuous_pi fun _ ↦ Metric.continuous_infDist_pt
          (barycentricSimplexSkeletonSet m))⟩
  let constrainedMap : C(stdSimplex ℝ (Fin (2 * m + 3)),
      EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun x ↦ (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * m) (m := 1)).symm
        (extension x, distanceCoordinate x),
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * m) (m := 1)).symm.continuous.comp
        (extension.continuous.prodMk distanceCoordinate.continuous)⟩
  obtain ⟨x, y, hcollision, hdisjoint⟩ := hRadon constrainedMap
  have hpair :
      (extension x, distanceCoordinate x) = (extension y, distanceCoordinate y) := by
    have := congrArg
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * m) (m := 1)) hcollision
    simpa only [constrainedMap, ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply] using this
  have hextensionEq : extension x = extension y := congrArg Prod.fst hpair
  have hdistanceEq :
      Metric.infDist x (barycentricSimplexSkeletonSet m) =
        Metric.infDist y (barycentricSimplexSkeletonSet m) := by
    have hcoordinate := congrArg
      (fun z ↦ (EuclideanSpace.equiv (Fin 1) ℝ z) 0)
      (congrArg Prod.snd hpair)
    simpa only [distanceCoordinate, ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply] using hcoordinate
  have hskeletonNonempty : (barycentricSimplexSkeletonSet m).Nonempty := by
    refine ⟨stdSimplex.vertex (0 : Fin (2 * m + 3)), ?_⟩
    rw [barycentricSimplexSkeletonSet]
    have hsupport :
        {i | (stdSimplex.vertex (S := ℝ) (0 : Fin (2 * m + 3))).1 i ≠ 0} =
          {(0 : Fin (2 * m + 3))} := by
      ext i
      by_cases hi : i = 0
      · subst i
        norm_num
      · simp only [Pi.single_eq_of_ne hi, ne_eq, not_true_eq_false,
          Set.mem_setOf_eq, Set.mem_singleton_iff, hi]
    change Set.encard
      {i | (stdSimplex.vertex (S := ℝ) (0 : Fin (2 * m + 3))).1 i ≠ 0} ≤ m + 1
    rw [hsupport, Set.encard_singleton]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hmembership := disjointSimplexSupports_one_memSkeleton m x y hdisjoint
  have hxmem : x ∈ barycentricSimplexSkeletonSet m := by
    rcases hmembership with hx | hy
    · exact hx
    · have hydistance : Metric.infDist y (barycentricSimplexSkeletonSet m) = 0 :=
        Metric.infDist_zero_of_mem hy
      have hxdistance : Metric.infDist x (barycentricSimplexSkeletonSet m) = 0 :=
        hdistanceEq.trans hydistance
      exact ((barycentricSimplexSkeletonSet_isClosed m).mem_iff_infDist_zero
        hskeletonNonempty).mpr hxdistance
  have hymem : y ∈ barycentricSimplexSkeletonSet m := by
    have hxdistance : Metric.infDist x (barycentricSimplexSkeletonSet m) = 0 :=
      Metric.infDist_zero_of_mem hxmem
    have hydistance : Metric.infDist y (barycentricSimplexSkeletonSet m) = 0 :=
      hdistanceEq.symm.trans hxdistance
    exact ((barycentricSimplexSkeletonSet_isClosed m).mem_iff_infDist_zero
      hskeletonNonempty).mpr hydistance
  let xs : barycentricSimplexSkeletonSet m := ⟨x, hxmem⟩
  let ys : barycentricSimplexSkeletonSet m := ⟨y, hymem⟩
  have hxextension : extension x = f (liftedInclusion xs) := by
    have := congrFun hextension xs
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, skeletonMap, liftedInclusion, xs,
      Function.comp_apply] using this
  have hyextension : extension y = f (liftedInclusion ys) := by
    have := congrFun hextension ys
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, skeletonMap, liftedInclusion, ys,
      Function.comp_apply] using this
  have hlifted : liftedInclusion xs = liftedInclusion ys :=
    hf.injective (hxextension.symm.trans (hextensionEq.trans hyextension))
  have hxy : x = y := by
    exact congrArg (fun z : barycentricSimplexSkeleton.{u} m ↦ z.down.1) hlifted
  have hsupportDisjoint : Disjoint {i | x.1 i ≠ 0} {i | x.1 i ≠ 0} := by
    simpa only [hxy] using hdisjoint
  have hsupportEmpty : {i | x.1 i ≠ 0} = ∅ :=
    disjoint_self.mp hsupportDisjoint
  have hsum : ∑ i, x.1 i = 1 := stdSimplex.sum_eq_one x
  have hzero (i : Fin (2 * m + 3)) : x.1 i = 0 := by
    by_contra hi
    have : i ∈ ({i | x.1 i ≠ 0} : Set (Fin (2 * m + 3))) := hi
    rw [hsupportEmpty] at this
    exact this.elim
  have hsumzero : ∑ i, x.1 i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hzero i
  rw [hsumzero] at hsum
  norm_num at hsum

/-- Helper for Remark 50.3: the barycentric simplex skeleton is compact. -/
private lemma barycentricSimplexSkeleton_compactSpace (m : ℕ) :
    CompactSpace (barycentricSimplexSkeleton.{u} m) := by
  -- Closedness gives compactness before transport across the universe lift.
  letI : CompactSpace (barycentricSimplexSkeletonSet m) :=
    isCompact_iff_compactSpace.mp (barycentricSimplexSkeletonSet_isClosed m).isCompact
  exact Homeomorph.ulift.symm.compactSpace

/-- Helper for Remark 50.3: the barycentric simplex skeleton is metrizable. -/
private lemma barycentricSimplexSkeleton_metrizableSpace (m : ℕ) :
    TopologicalSpace.MetrizableSpace (barycentricSimplexSkeleton.{u} m) := by
  -- Subspaces of finite Euclidean spaces and their universe lifts are metrizable.
  exact Homeomorph.ulift.isEmbedding.metrizableSpace

/-- Helper for Remark 50.3: the `m`-skeleton of the barycentric simplex has
covering dimension at most `m`. -/
private lemma barycentricSimplexSkeleton_coveringDimensionLE (m : ℕ) :
    HasCoveringDimensionLE (barycentricSimplexSkeleton.{u} m) m := by
  -- Bound each coordinate face and combine the finite closed face cover.
  have hbase : HasCoveringDimensionLE (barycentricSimplexSkeletonSet m) m := by
    rw [barycentricSimplexSkeletonSet_eq_iUnion_faces]
    apply HasCoveringDimensionLE.finiteUnionClosedSubtypes
    · intro s
      exact barycentricSimplexFace_isClosed m s.1
    · intro s
      exact barycentricSimplexFace_coveringDimensionLE m s.1 s.2
  -- Transport the assembled bound across the universe lift.
  exact hbase.homeomorph Homeomorph.ulift.symm

/-- Helper for Remark 50.3: the `m`-skeleton of the simplex on `2 * m + 3`
vertices does not embed in `EuclideanSpace ℝ (Fin (2 * m))`. -/
private lemma barycentricSimplexSkeleton_notEmbeddable (m : ℕ) :
    ¬ ∃ f : barycentricSimplexSkeleton.{u} m → EuclideanSpace ℝ (Fin (2 * m)),
      Topology.IsEmbedding f := by
  -- The proved normalization bridge and constraint argument reduce the result
  -- to the general Borsuk--Ulam antipodal-coincidence prerequisite.
  apply barycentricSimplexSkeleton_notEmbeddable_of_radon m
  apply topologicalRadon_of_antipodalCoincidence m
  -- The local Borsuk--Ulam bridge leaves only the isolated odd-self-map obstruction.
  intro f
  exact existsAntipodalEq_sharpStandardSphere (2 * m) f

/-- Helper for Remark 50.3: in every universe there is a compact metrizable
`m`-dimensional space that does not embed in `EuclideanSpace ℝ (Fin (2 * m))`. -/
lemma existsSharpEuclideanEmbeddingObstruction (m : ℕ) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X)
      (_ : TopologicalSpace.MetrizableSpace X),
      dim X = (m : ℕ∞) ∧
        ¬ ∃ f : X → EuclideanSpace ℝ (Fin (2 * m)), Topology.IsEmbedding f := by
  cases m with
  | zero =>
      -- Two discrete points give the sharp obstruction in dimension zero.
      let X := ULift.{u} Bool
      letI : TopologicalSpace X := ⊥
      letI : DiscreteTopology X := discreteTopology_bot X
      have hcompact : CompactSpace X := inferInstance
      have hmetrizable : TopologicalSpace.MetrizableSpace X := inferInstance
      have hdim : dim X = (0 : ℕ∞) := coveringDimension_eq_zero_of_discrete X
      have hnotEmbed :
          ¬ ∃ f : X → EuclideanSpace ℝ (Fin 0), Topology.IsEmbedding f := by
        rintro ⟨f, hf⟩
        have himages : f (ULift.up true) = f (ULift.up false) := Subsingleton.elim _ _
        have hlifts : (ULift.up true : X) = ULift.up false := hf.injective himages
        exact Bool.false_ne_true (congrArg ULift.down hlifts).symm
      exact ⟨X, inferInstance, hcompact, hmetrizable, hdim, hnotEmbed⟩
  | succ m =>
      -- Route correction: the deleted-product route exposed no usable API.  Use
      -- the simplex skeleton interface and isolate its dimension and Radon facts.
      let X := barycentricSimplexSkeleton.{u} (m + 1)
      letI : CompactSpace X :=
        barycentricSimplexSkeleton_compactSpace (m + 1)
      letI : TopologicalSpace.MetrizableSpace X :=
        barycentricSimplexSkeleton_metrizableSpace (m + 1)
      have hbound : HasCoveringDimensionLE X (m + 1) :=
        barycentricSimplexSkeleton_coveringDimensionLE (m + 1)
      have hnotEmbed :
          ¬ ∃ f : X → EuclideanSpace ℝ (Fin (2 * (m + 1))),
            Topology.IsEmbedding f :=
        barycentricSimplexSkeleton_notEmbeddable (m + 1)
      have hdim : dim X = ((m + 1 : ℕ) : ℕ∞) := by
        -- The face bound gives one inequality; a smaller dimension would make
        -- Theorem 50.4 produce an embedding forbidden by van Kampen--Flores.
        apply le_antisymm
        · exact (coveringDimension_le_iff X (m + 1)).mpr hbound
        · apply le_of_not_gt
          intro hsmall
          have hdimSucc : dim X < ((m + 1 : ℕ) : WithBot ℕ∞) := by
            simpa using hsmall
          have hdimLe : dim X ≤ (m : WithBot ℕ∞) :=
            ENat.WithBot.lt_add_one_iff.mp hdimSucc
          have hsmallerBound : HasCoveringDimensionLE X m :=
            (coveringDimension_le_iff X m).mp hdimLe
          obtain ⟨f, hf⟩ :=
            existsEuclideanEmbedding_of_hasCoveringDimensionLE hsmallerBound
          have hcoordinates : 2 * m + 1 ≤ 2 * (m + 1) := by omega
          exact notEuclideanEmbeddableOfLE hcoordinates hnotEmbed ⟨f, hf⟩
      exact ⟨X, inferInstance, inferInstance, inferInstance, hdim, hnotEmbed⟩

/-- Remark 50.3. The dimension `2 * m + 1` is the least `N` such that every compact
metrizable space of covering dimension exactly `m` embeds in `EuclideanSpace ℝ (Fin N)`. -/
theorem leastEuclideanEmbeddingDimension (m : ℕ) :
    IsLeast
      {N : ℕ |
        ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X]
          [TopologicalSpace.MetrizableSpace X],
          dim X = (m : ℕ∞) →
            ∃ f : X → EuclideanSpace ℝ (Fin N), Topology.IsEmbedding f}
      (2 * m + 1) := by
  constructor
  · -- Theorem 50.4 supplies the universal embedding in dimension `2 * m + 1`.
    intro X _ _ _ hdim
    exact existsEuclideanEmbedding_of_coveringDimension_eq m hdim
  · -- A sharp obstruction rules out every smaller candidate dimension.
    intro N hN
    by_contra hnot
    have hNle : N ≤ 2 * m := by omega
    obtain ⟨X, topology, compact, metrizable, hdim, hnotEmbed⟩ :=
      existsSharpEuclideanEmbeddingObstruction.{u} m
    letI : TopologicalSpace X := topology
    letI : CompactSpace X := compact
    letI : TopologicalSpace.MetrizableSpace X := metrizable
    exact notEuclideanEmbeddableOfLE hNle hnotEmbed (hN X hdim)
