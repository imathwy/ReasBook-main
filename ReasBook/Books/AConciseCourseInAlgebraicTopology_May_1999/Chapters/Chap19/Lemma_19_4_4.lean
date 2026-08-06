import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_4_1
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory

universe u

namespace InverseSequence

variable (S : InverseSequence.{u})

/-- The `ℕᵒᵖ`-indexed functor of abelian groups attached to an inverse sequence. -/
abbrev toFunctor : ℕᵒᵖ ⥤ Ab.{u} :=
  Functor.ofOpSequence S.d

/-- The underlying `ℕᵒᵖ`-indexed functor of types attached to an inverse sequence. -/
abbrev toTypeFunctor : ℕᵒᵖ ⥤ Type u :=
  S.toFunctor ⋙ forget Ab

/-- The transition morphism `A_(n + k) ⟶ A_n` in an inverse sequence, viewed as the canonical
map of the `ℕᵒᵖ`-indexed functor `S.toFunctor`.
-/
abbrev transition (n k : ℕ) : S.A (n + k) ⟶ S.A n :=
  S.toFunctor.map (homOfLE (Nat.le_add_right n k)).op

@[simp] theorem transition_succ (n : ℕ) : S.transition n 1 = S.d n := by
  exact Functor.ofOpSequence_map_homOfLE_succ S.d n

/-- The image in `A_n` of the transition morphism `A_(n + k) ⟶ A_n`. -/
abbrev transitionRange (n k : ℕ) : AddSubgroup (S.A n) :=
  AddMonoidHom.range (S.transition n k).hom

/-- Helper for Lemma 19.4.4: membership in `S.transitionRange n k` is membership in the image of
the corresponding transition map.
-/
theorem mem_transitionRange_iff {n k : ℕ} {y : S.A n} :
    y ∈ S.transitionRange n k ↔ ∃ z, S.transition n k z = y :=
  Iff.rfl

/-- Helper for Lemma 19.4.4: the transition map attached to an arbitrary inequality `n ≤ m`. -/
abbrev transitionOfLE {n m : ℕ} (h : n ≤ m) : S.A m ⟶ S.A n :=
  S.toFunctor.map (homOfLE h).op

/-- Helper for Lemma 19.4.4: transition maps compose along concatenated inequalities. -/
theorem transitionOfLE_comp {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    S.transitionOfLE hml ≫ S.transitionOfLE hnm = S.transitionOfLE (hnm.trans hml) := by
  -- Normalize both sides to the functorial image of a composite `homOfLE`.
  change (((Functor.ofSequence fun n ↦ (S.d n).op).map (homOfLE hml)).unop ≫
      ((Functor.ofSequence fun n ↦ (S.d n).op).map (homOfLE hnm)).unop) =
      ((Functor.ofSequence fun n ↦ (S.d n).op).map (homOfLE (hnm.trans hml))).unop
  apply Quiver.Hom.op_inj
  simpa [Functor.ofOpSequence] using
    (Functor.OfSequence.map_comp (f := fun n ↦ (S.d n).op) n m l hnm hml).symm

/-- Helper for Lemma 19.4.4: later transition images are contained in earlier ones. -/
theorem transitionRange_antitone {n N k : ℕ} (hNk : N ≤ k) :
    S.transitionRange n k ≤ S.transitionRange n N := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hNk
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let hTail : n + N ≤ n + (N + t) := by
    exact Nat.add_le_add_left (Nat.le_add_right N t) n
  refine ⟨S.transitionOfLE hTail x, ?_⟩
  -- Rewrite the long transition through the intermediate stage `n + N`.
  change ((S.transitionOfLE hTail ≫ S.transitionOfLE (Nat.le_add_right n N)) x) =
      S.transition n (N + t) x
  rw [S.transitionOfLE_comp (Nat.le_add_right n N) hTail]
  -- The previous rewrite has already put the morphism into the canonical long-transition form.

/-- An inverse sequence satisfies the Mittag-Leffler condition if, for each `n`, the images of the
transition morphisms `A_(n + k) ⟶ A_n` stabilize for all sufficiently large `k`. This is the
Chapter 19 source-facing name for the canonical mathlib condition on the underlying
`ℕᵒᵖ`-indexed functor of sets, and the companion theorem
`mittagLeffler_iff_stabilizes_transitionRange` recovers the stabilization-of-images formulation.
-/
abbrev MittagLeffler : Prop :=
  S.toTypeFunctor.IsMittagLeffler

/-- For an inverse sequence, the canonical mathlib Mittag-Leffler condition is equivalent to the
stabilization of the transition images in each `A_n`.
-/
theorem mittagLeffler_iff_stabilizes_transitionRange :
    S.MittagLeffler ↔
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → S.transitionRange n k = S.transitionRange n N := by
  constructor
  · intro hS n
    -- Read the abstract Mittag-Leffler condition at `op n` through the canonical transition maps.
    obtain ⟨i, f, hf⟩ :=
      (CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp
        (F := S.toTypeFunctor)).1 hS (Opposite.op n)
    cases i using Opposite.rec
    rename_i m
    have hm : n ≤ m := by
      simpa using (leOfHom f.unop)
    obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hm
    refine ⟨N, fun k hk ↦ ?_⟩
    have hsubset : S.transitionRange n N ≤ S.transitionRange n k := by
      let g : Opposite.op (n + k) ⟶ Opposite.op (n + N) :=
        (homOfLE (by simpa [Nat.add_assoc] using Nat.add_le_add_left hk n)).op
      have hf_eq : f = (homOfLE (Nat.le_add_right n N)).op := Subsingleton.elim _ _
      have hgf_eq : g ≫ f = (homOfLE (Nat.le_add_right n k)).op := Subsingleton.elim _ _
      -- The chosen ML witness forces the stabilized image to lie in every later image.
      intro y hy
      rcases hf g hy with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [transition, hgf_eq] using hx
    exact le_antisymm (S.transitionRange_antitone hk) hsubset
  · intro hS
    change S.toTypeFunctor.IsMittagLeffler
    rw [CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp]
    intro j
    cases j using Opposite.rec
    rename_i n
    obtain ⟨N, hN⟩ := hS n
    refine ⟨Opposite.op (n + N), (homOfLE (Nat.le_add_right n N)).op, ?_⟩
    intro k g
    cases k using Opposite.rec
    rename_i m
    -- Route correction: normalize the composite source as `n + k` directly, instead of
    -- introducing an auxiliary tail `t` after the stabilization stage `N`.
    have hk : n + N ≤ m := by
      simpa using (leOfHom g.unop)
    have hkn : n ≤ m := Nat.le_trans (Nat.le_add_right n N) hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hkn
    have hNk : N ≤ k := Nat.le_of_add_le_add_left hk
    have hgf_eq :
        g ≫ (homOfLE (Nat.le_add_right n N)).op =
          (homOfLE (Nat.le_add_right n k)).op :=
      Subsingleton.elim _ _
    -- Stabilization identifies the chosen range with the normalized composite range.
    intro y hy
    have hy' : y ∈ S.transitionRange n k := (hN k hNk).symm.le hy
    rcases (S.mem_transitionRange_iff).1 hy' with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [transition, hgf_eq] using hz

/-- Helper for Lemma 19.4.4: a surjective inverse system of nonempty types over `ℕᵒᵖ`
admits a section.
-/
theorem nonemptySectionsOfSurjectiveOpSequence (F : ℕᵒᵖ ⥤ Type u)
    (hsurj : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op))
    (hnonempty : ∀ n : ℕ, Nonempty (F.obj (Opposite.op n))) :
    Nonempty F.sections := by
  classical
  let x : ∀ n : ℕ, F.obj (Opposite.op n) :=
    Nat.rec (Classical.choice (hnonempty 0)) fun n xn => Classical.choose (hsurj n xn)
  have hsucc : ∀ n : ℕ,
      F.map (homOfLE (Nat.le_add_right n 1)).op (x (n + 1)) = x n := by
    intro n
    simpa [x] using Classical.choose_spec (hsurj n (x n))
  have hlong : ∀ n k : ℕ, F.map (homOfLE (Nat.le_add_right n k)).op (x (n + k)) = x n := by
    intro n k
    induction k with
    | zero =>
        -- The zero-step transition is the identity.
        simp [x]
    | succ k ih =>
        -- Factor a long transition into one successor step followed by the shorter transition.
        change
          F.map
              ((homOfLE (Nat.le_add_right (n + k) 1)).op ≫
                (homOfLE (Nat.le_add_right n k)).op) (x (n + k + 1)) =
            x n
        rw [Functor.map_comp]
        change
          F.map (homOfLE (Nat.le_add_right n k)).op
              (F.map (homOfLE (Nat.le_add_right (n + k) 1)).op (x (n + k + 1))) =
            x n
        rw [hsucc]
        simpa [Nat.add_assoc] using ih
  refine ⟨⟨fun n ↦ x n.unop, ?_⟩⟩
  intro i j f
  cases i using Opposite.rec
  cases j using Opposite.rec
  rename_i i j
  have hij : j ≤ i := by
    simpa using (leOfHom f.unop)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hf_eq : f = (homOfLE (Nat.le_add_right j k)).op := Subsingleton.elim _ _
  -- Any morphism in `ℕᵒᵖ` is a finite composite of successor maps.
  simpa [hf_eq] using hlong j k

/-- Helper for Lemma 19.4.4: the zero-tail contribution in the `k`-step backward solution. -/
def partialSolutionBase (y : (n : ℕ) → S.A n) (n k : ℕ) : S.A n :=
  Finset.sum (Finset.range k) fun i ↦ S.transition n i (y (n + i))

/-- Helper for Lemma 19.4.4: the one-step inhomogeneous recursion map `z ↦ y_n + d_n z`. -/
abbrev partialSolutionStep (y : (n : ℕ) → S.A n) (n : ℕ) : S.A (n + 1) → S.A n :=
  fun z ↦ y n + S.d n z

/-- Helper for Lemma 19.4.4: the `k`-step backward affine solution map. -/
def partialSolutionMap (y : (n : ℕ) → S.A n) (n k : ℕ) : S.A (n + k) → S.A n :=
  fun z ↦ S.partialSolutionBase y n k + S.transition n k z

/-- Helper for Lemma 19.4.4: the affine recursion is built from the zero-tail base plus the
homogeneous transition map.
-/
theorem partialSolutionMap_eq_base_add_transition
    (y : (n : ℕ) → S.A n) (n k : ℕ) (z : S.A (n + k)) :
    S.partialSolutionMap y n k z = S.partialSolutionBase y n k + S.transition n k z := rfl

/-- Helper for Lemma 19.4.4: the long transition factors through the first successor step. -/
theorem transition_succ_comp (n k : ℕ) :
    S.transitionOfLE
        (show n + 1 ≤ n + (k + 1) by
          exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) n) ≫
      S.d n =
        S.transition n (k + 1) := by
  let hTail : n + 1 ≤ n + (k + 1) := by
    exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) n
  -- Factor the long map through the intermediate stage `n + 1`.
  simpa [transition, transitionOfLE, Nat.add_assoc] using
    (InverseSequence.transitionOfLE_comp (S := S) (Nat.le_add_right n 1) hTail)

/-- Helper for Lemma 19.4.4: evaluating the long transition after one more step rewrites through
`d_n`.
-/
theorem transition_succ_apply (n k : ℕ) (z : S.A (n + (k + 1))) :
    S.transition n (k + 1) z =
      S.d n
        (S.transitionOfLE
          (show n + 1 ≤ n + (k + 1) by
            exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) n) z) := by
  -- Evaluate the factorization of the long transition map at the chosen element.
  simpa using congrArg (fun f => f z) (S.transition_succ_comp n k).symm

/-- Helper for Lemma 19.4.4: the affine inverse system whose sections solve
`x_n = y_n + d_n(x_{n + 1})`.
-/
abbrev partialSolutionFunctor (y : (n : ℕ) → S.A n) : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := fun n ↦ S.A n) (S.partialSolutionStep y)

/-- Helper for Lemma 19.4.4: appending one more stage adds the final homogeneous summand to the
explicit base term.
-/
theorem partialSolutionBase_appendLast
    (y : (n : ℕ) → S.A n) (n k : ℕ) :
    S.partialSolutionBase y n (k + 1) =
      S.partialSolutionBase y n k + S.transition n k (y (n + k)) := by
  -- Split the base sum at its final index instead of at the initial index.
  simpa [partialSolutionBase] using
    (Finset.sum_range_succ (f := fun i ↦ S.transition n i (y (n + i))) k)

/-- Helper for Lemma 19.4.4: a `(k + 1)`-step transition factors through the final successor map
at stage `n + k`.
-/
theorem transition_last_apply (n k : ℕ) (z : S.A (n + (k + 1))) :
    S.transition n (k + 1) z = S.transition n k (S.d (n + k) z) := by
  let hTail : n + k ≤ n + (k + 1) := by
    exact Nat.add_le_add_left (Nat.le_add_right k 1) n
  have hcomp :
      S.d (n + k) ≫ S.transition n k = S.transition n (k + 1) := by
    -- Factor the long transition through the last successor map.
    simpa [transition, transitionOfLE, Nat.add_assoc] using
      (InverseSequence.transitionOfLE_comp (S := S) (Nat.le_add_right n k) hTail)
  simpa using congrArg (fun f => f z) hcomp.symm

/-- Helper for Lemma 19.4.4: the long maps in the affine inverse system are exactly the explicit
partial-solution maps.
-/
theorem partialSolutionFunctor_map_eq_partialSolutionMap
    (y : (n : ℕ) → S.A n) (n k : ℕ) :
    (S.partialSolutionFunctor y).map ((homOfLE (Nat.le_add_right n k)).op) =
      S.partialSolutionMap y n k := by
  induction k with
  | zero =>
      -- The zero-step affine map is the identity and the base term is empty.
      ext z
      simp [partialSolutionFunctor, partialSolutionMap, partialSolutionBase, transition]
  | succ k ih =>
      ext z
      have hcomp :
          (homOfLE (Nat.le_add_right n (k + 1))).op =
            (homOfLE (Nat.le_add_right (n + k) 1)).op ≫
              (homOfLE (Nat.le_add_right n k)).op := by
        apply Subsingleton.elim
      -- Route correction: factor through the final successor step so the induction hypothesis uses
      -- the exact intermediate stage `A_(n + k)` with no source-index cast.
      rw [hcomp, Functor.map_comp, ih]
      change
        S.partialSolutionMap y n k
            (((S.partialSolutionFunctor y).map ((homOfLE (Nat.le_add_right (n + k) 1)).op)) z) =
          S.partialSolutionMap y n (k + 1) z
      simp only [partialSolutionFunctor, partialSolutionStep, homOfLE_leOfHom,
        Functor.ofOpSequence_map_homOfLE_succ]
      calc
        S.partialSolutionMap y n k (y (n + k) + S.d (n + k) z) =
            S.partialSolutionBase y n k +
              S.transition n k (y (n + k) + S.d (n + k) z) := by
          rw [partialSolutionMap_eq_base_add_transition]
        _ =
            S.partialSolutionBase y n k +
              (S.transition n k (y (n + k)) + S.transition n k (S.d (n + k) z)) := by
          rw [map_add]
        _ = S.partialSolutionMap y n (k + 1) z := by
          rw [partialSolutionMap_eq_base_add_transition, S.partialSolutionBase_appendLast,
            S.transition_last_apply]
          abel

/-- Helper for Lemma 19.4.4: the tail contribution added after the stabilization stage already
lies in the stabilized transition image.
-/
theorem partialSolutionBase_tail_mem_transitionRange
    (y : (n : ℕ) → S.A n) {n N t : ℕ}
    (hstable : ∀ k : ℕ, N ≤ k → S.transitionRange n k = S.transitionRange n N) :
    S.partialSolutionBase y n (N + t) - S.partialSolutionBase y n N ∈ S.transitionRange n N := by
  have hsplit :
      S.partialSolutionBase y n (N + t) =
        S.partialSolutionBase y n N +
          ∑ j ∈ Finset.range t, S.transition n (N + j) (y (n + (N + j))) := by
    -- Split the longer base sum into the original prefix and the tail starting at `N`.
    simpa [partialSolutionBase] using
      (Finset.sum_range_add (f := fun i ↦ S.transition n i (y (n + i))) N t)
  have htail :
      ∑ j ∈ Finset.range t, S.transition n (N + j) (y (n + (N + j))) ∈ S.transitionRange n N := by
    -- Every new summand already lies in the stabilized homogeneous image.
    refine AddSubgroup.sum_mem _ ?_
    intro j hj
    have hmem :
        S.transition n (N + j) (y (n + (N + j))) ∈ S.transitionRange n (N + j) := by
      exact ⟨y (n + (N + j)), rfl⟩
    exact (hstable (N + j) (Nat.le_add_right N j)).le hmem
  -- The difference from stage `N` is exactly the tail sum.
  rw [hsplit, add_sub_cancel_left]
  exact htail

/-- Helper for Lemma 19.4.4: the affine partial-solution ranges stabilize once the homogeneous
transition images do.
-/
theorem partialSolutionRange_stabilizes
    (y : (n : ℕ) → S.A n) (hML : S.MittagLeffler) (n : ℕ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      Set.range (S.partialSolutionMap y n k) = Set.range (S.partialSolutionMap y n N) := by
  obtain ⟨N, hstable⟩ := (S.mittagLeffler_iff_stabilizes_transitionRange).1 hML n
  refine ⟨N, fun k hk ↦ ?_⟩
  have hbase :
      S.partialSolutionBase y n k - S.partialSolutionBase y n N ∈ S.transitionRange n N := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    simpa [Nat.add_assoc] using
      S.partialSolutionBase_tail_mem_transitionRange y (n := n) (N := N) (t := t) hstable
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨z, rfl⟩
    rcases (S.mem_transitionRange_iff).1 hbase with ⟨w₀, hw₀⟩
    have hzMem : S.transition n k z ∈ S.transitionRange n N := by
      have hzRange : S.transition n k z ∈ S.transitionRange n k := by
        exact ⟨z, rfl⟩
      exact (hstable k hk).le hzRange
    rcases (S.mem_transitionRange_iff).1 hzMem with ⟨w₁, hw₁⟩
    refine ⟨w₀ + w₁, ?_⟩
    -- Express the stage-`k` affine value using the stabilized stage-`N` range.
    calc
      S.partialSolutionMap y n N (w₀ + w₁) =
        S.partialSolutionBase y n N + S.transition n N (w₀ + w₁) := by
          rw [partialSolutionMap_eq_base_add_transition]
      _ = S.partialSolutionBase y n N +
          (S.transition n N w₀ + S.transition n N w₁) := by
        rw [map_add]
      _ = S.partialSolutionBase y n N +
          ((S.partialSolutionBase y n k - S.partialSolutionBase y n N) + S.transition n k z) := by
        rw [hw₀, hw₁]
      _ = S.partialSolutionMap y n k z := by
        rw [partialSolutionMap_eq_base_add_transition]
        abel
  · intro x hx
    rcases hx with ⟨z, rfl⟩
    have hbase' :
        S.partialSolutionBase y n k - S.partialSolutionBase y n N ∈ S.transitionRange n k := by
      exact (hstable k hk).symm.le hbase
    rcases (S.mem_transitionRange_iff).1 hbase' with ⟨w₀, hw₀⟩
    have hzMem : S.transition n N z ∈ S.transitionRange n k := by
      have hzRange : S.transition n N z ∈ S.transitionRange n N := by
        exact ⟨z, rfl⟩
      exact (hstable k hk).symm.le hzRange
    rcases (S.mem_transitionRange_iff).1 hzMem with ⟨w₁, hw₁⟩
    refine ⟨w₁ - w₀, ?_⟩
    -- Translate the stabilized stage-`N` range back to the explicit stage-`k` affine range.
    calc
      S.partialSolutionMap y n k (w₁ - w₀) =
        S.partialSolutionBase y n k + S.transition n k (w₁ - w₀) := by
          rw [partialSolutionMap_eq_base_add_transition]
      _ = S.partialSolutionBase y n k +
          (S.transition n k w₁ - S.transition n k w₀) := by
        rw [map_sub]
      _ = S.partialSolutionBase y n k +
          (S.transition n N z - (S.partialSolutionBase y n k - S.partialSolutionBase y n N)) := by
        rw [hw₁, hw₀]
      _ = S.partialSolutionMap y n N z := by
        rw [partialSolutionMap_eq_base_add_transition]
        abel

/-- Helper for Lemma 19.4.4: the affine inverse system is Mittag-Leffler whenever the original
inverse sequence is.
-/
theorem partialSolutionFunctor_mittagLeffler
    (y : (n : ℕ) → S.A n) (hML : S.MittagLeffler) :
    (S.partialSolutionFunctor y).IsMittagLeffler := by
  rw [CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp]
  intro j
  cases j using Opposite.rec
  rename_i n
  obtain ⟨N, hN⟩ := S.partialSolutionRange_stabilizes y hML n
  refine ⟨Opposite.op (n + N), (homOfLE (Nat.le_add_right n N)).op, ?_⟩
  intro k g
  cases k using Opposite.rec
  rename_i m
  have hk : n + N ≤ m := by
    simpa using (leOfHom g.unop)
  have hkn : n ≤ m := Nat.le_trans (Nat.le_add_right n N) hk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have hNk : N ≤ k := Nat.le_of_add_le_add_left hk
  have hgf_eq :
      g ≫ (homOfLE (Nat.le_add_right n N)).op =
        (homOfLE (Nat.le_add_right n k)).op :=
    Subsingleton.elim _ _
  -- Normalize both categorical ranges to the explicit affine partial-solution maps.
  intro x hx
  have hx' : x ∈ Set.range (S.partialSolutionMap y n N) := by
    simpa [S.partialSolutionFunctor_map_eq_partialSolutionMap] using hx
  have hx'' : x ∈ Set.range (S.partialSolutionMap y n k) := (hN k hNk).symm.le hx'
  simpa [hgf_eq, S.partialSolutionFunctor_map_eq_partialSolutionMap] using hx''

/-- Helper for Lemma 19.4.4: the product-difference map is surjective for a Mittag-Leffler inverse
sequence.
-/
theorem productDifferenceHom_surjective_of_mittagLeffler (hML : S.MittagLeffler) :
    Function.Surjective S.productDifferenceHom := by
  intro y
  let F := S.partialSolutionFunctor y
  have hFML : F.IsMittagLeffler := S.partialSolutionFunctor_mittagLeffler y hML
  -- Local instance justification (nonempty stages): each `F.obj j` is an abelian group, hence has
  -- a canonical zero element and is therefore nonempty.
  letI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    cases j using Opposite.rec
    rename_i n
    change Nonempty (S.A n)
    exact ⟨0⟩
  have hsurjER :
      ∀ n : ℕ, Function.Surjective ((F.toEventualRanges).map (homOfLE (Nat.le_add_right n 1)).op) :=
    fun n ↦ CategoryTheory.Functor.surjective_toEventualRanges
      (F := F) hFML ((homOfLE (Nat.le_add_right n 1)).op)
  have hnonemptyER :
      ∀ n : ℕ, Nonempty ((F.toEventualRanges).obj (Opposite.op n)) :=
    fun n ↦ CategoryTheory.Functor.toEventualRanges_nonempty
      (F := F) hFML (Opposite.op n)
  obtain ⟨secER⟩ :=
    InverseSequence.nonemptySectionsOfSurjectiveOpSequence
      (F := F.toEventualRanges) hsurjER hnonemptyER
  let x : (n : ℕ) → S.A n := fun n ↦ (secER.val (Opposite.op n)).1
  refine ⟨x, funext fun n ↦ ?_⟩
  have hsec :
      y n + S.d n (x (n + 1)) = x n := by
    -- Read the eventual-range section equation and project it back to the underlying affine system.
    have hsecER := Functor.sections_property secER ((homOfLE (Nat.le_add_right n 1)).op)
    exact congrArg Subtype.val (by simpa [F] using hsecER)
  -- Rearranging the section equation gives exactly the product-difference formula.
  calc
    S.productDifferenceHom x n = x n - S.d n (x (n + 1)) := by
      rw [productDifferenceHom_apply]
    _ = y n := by
      exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hsec.symm)

/-- Helper for Lemma 19.4.4: if the product-difference map is surjective, then the quotient
presentation of `S.limOne` is trivial.
-/
theorem limOne_subsingleton_of_productDifferenceHom_surjective
    (hsurj : Function.Surjective S.productDifferenceHom) :
    Subsingleton S.limOne := by
  have hall : ∀ a : S.limOne, a = 0 := by
    intro a
    obtain ⟨x, rfl⟩ := S.limOneπ_surjective a
    obtain ⟨y, rfl⟩ := hsurj x
    -- Every quotient class coming from the image of `productDifferenceHom` is zero.
    have hcomp := congrArg (fun f : S.sections ⟶ S.limOne ↦ f y)
      (show S.productDifference ≫ S.limOneπ = 0 from S.productDifference_comp_limOneπ)
    simpa [productDifference] using hcomp
  exact ⟨fun a b ↦ by rw [hall a, hall b]⟩

/-- Helper for Lemma 19.4.4: a Mittag-Leffler inverse sequence has trivial `lim¹` via the
canonical quotient presentation.
-/
instance isZeroLimOneOfMittagLeffler [Fact S.MittagLeffler] :
    CategoryTheory.Limits.IsZero S.limOne := by
  -- Route correction: rather than proving `IsZero` directly, first solve the concrete algebraic
  -- problem that `productDifferenceHom` is surjective, then collapse the quotient presentation.
  have hsurj : Function.Surjective S.productDifferenceHom :=
    S.productDifferenceHom_surjective_of_mittagLeffler Fact.out
  have : Subsingleton S.limOne :=
    S.limOne_subsingleton_of_productDifferenceHom_surjective hsurj
  exact AddCommGrpCat.isZero_of_subsingleton S.limOne

/-- Lemma 19.4.4: if an inverse sequence satisfies the Mittag-Leffler condition, then `lim¹`
vanishes.
-/
theorem isZero_limOne_of_mittagLeffler (hS : S.MittagLeffler) :
    CategoryTheory.Limits.IsZero S.limOne := by
  letI : Fact S.MittagLeffler := ⟨hS⟩
  exact isZeroLimOneOfMittagLeffler S

end InverseSequence
