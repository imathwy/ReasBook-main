import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1 (from Items/Chap01) -/
open Set

universe u

variable {X : Type u}

/-- Definition 1.1 (1): A class of sets is intersection-closed, or a pi-system in the textbook
sense, if it contains the intersection of any two of its members. -/
class IsInterClosed (A : Set (Set X)) : Prop where
  inter_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s ∩ t ∈ A

/- Mathlib companion to Definition 1.1 (1): `IsPiSystem` is the canonical library predicate for
closure under nonempty binary intersections. -/
recall IsPiSystem

/-- Binary intersection closure implies mathlib's `IsPiSystem` condition. -/
theorem IsInterClosed.isPiSystem {A : Set (Set X)} (hA : IsInterClosed A) :
    IsPiSystem A := by
  intro s hs t ht _
  exact hA.inter_mem hs ht

/-- If a family contains `∅`, then mathlib's `IsPiSystem` condition is equivalent to the
textbook binary-intersection closure. -/
theorem IsPiSystem.isInterClosed {A : Set (Set X)} (hA : IsPiSystem A) (hEmpty : (∅ : Set X) ∈ A) :
    IsInterClosed A := by
  refine ⟨?_⟩
  intro s t hs ht
  by_cases hst : (s ∩ t : Set X).Nonempty
  · exact hA s hs t ht hst
  · rw [not_nonempty_iff_eq_empty] at hst
    rwa [hst]

/-- Definition 1.1: for item (1), under the additional hypothesis `∅ ∈ A`, the textbook
binary-intersection formulation of a `π`-system agrees with mathlib's canonical predicate
`IsPiSystem`. -/
theorem isPiSystem_iff_isInterClosed_of_empty_mem {A : Set (Set X)} (hEmpty : (∅ : Set X) ∈ A) :
    IsPiSystem A ↔ IsInterClosed A := by
  constructor
  · intro hA
    exact hA.isInterClosed hEmpty
  · intro hA
    exact hA.isPiSystem

/-- Definition 1.1 (2): A class of sets is sigma-intersection-closed if it contains the
intersection of every sequence of its members. This is the canonical Lean formulation of closure
under countable intersections. -/
class IsCountablyInterClosed (A : Set (Set X)) : Prop where
  iInter_mem : ∀ s : ℕ → Set X, (∀ n : ℕ, s n ∈ A) → (⋂ n : ℕ, s n) ∈ A

/-- Countable intersection closure canonically implies binary intersection closure. -/
instance IsCountablyInterClosed.toIsInterClosed {A : Set (Set X)}
    (hA : IsCountablyInterClosed A) : IsInterClosed A where
  inter_mem {s t} hs ht := by
    let u : ℕ → Set X := fun n ↦ if n = 0 then s else t
    have hu : ∀ n : ℕ, u n ∈ A := by
      intro n
      by_cases hn : n = 0
      · simpa [u, hn] using hs
      · simpa [u, hn] using ht
    have hEq : (⋂ n : ℕ, u n) = s ∩ t := by
      rw [← inter_iInter_nat_succ u]
      ext x
      simp [u]
    exact hEq ▸ hA.iInter_mem u hu

/-- A sigma-intersection-closed class contains the intersection of every nonempty countable
subfamily of its members. -/
theorem IsCountablyInterClosed.sInter_mem {A : Set (Set X)} (hA : IsCountablyInterClosed A)
    {S : Set (Set X)} (hS : S.Countable) (hS_ne : S.Nonempty) (hSA : S ⊆ A) :
    ⋂₀ S ∈ A := by
  obtain ⟨s, rfl⟩ := hS.exists_eq_range hS_ne
  simpa [sInter_range] using hA.iInter_mem s (fun n ↦ hSA (mem_range_self n))

/-- Definition 1.1 (3): A class of sets is union-closed if it contains the union of any two of
its members. -/
class IsUnionClosed (A : Set (Set X)) : Prop where
  union_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s ∪ t ∈ A

/-- Definition 1.1 (4): A class of sets is sigma-union-closed if it contains the union of every
sequence of its members. This is the canonical Lean formulation of closure under countable
unions. -/
class IsCountablyUnionClosed (A : Set (Set X)) : Prop where
  iUnion_mem : ∀ s : ℕ → Set X, (∀ n : ℕ, s n ∈ A) → (⋃ n : ℕ, s n) ∈ A

/-- Countable union closure canonically implies binary union closure. -/
instance IsCountablyUnionClosed.toIsUnionClosed {A : Set (Set X)}
    (hA : IsCountablyUnionClosed A) : IsUnionClosed A where
  union_mem {s t} hs ht := by
    let u : ℕ → Set X := fun n ↦ if n = 0 then s else t
    have hu : ∀ n : ℕ, u n ∈ A := by
      intro n
      by_cases hn : n = 0
      · simpa [u, hn] using hs
      · simpa [u, hn] using ht
    have hEq : (⋃ n : ℕ, u n) = s ∪ t := by
      rw [← union_iUnion_nat_succ u]
      ext x
      simp [u]
    exact hEq ▸ hA.iUnion_mem u hu

/-- A sigma-union-closed class contains the union of every nonempty countable subfamily of its
members. -/
theorem IsCountablyUnionClosed.sUnion_mem {A : Set (Set X)} (hA : IsCountablyUnionClosed A)
    {S : Set (Set X)} (hS : S.Countable) (hS_ne : S.Nonempty) (hSA : S ⊆ A) :
    ⋃₀ S ∈ A := by
  obtain ⟨s, rfl⟩ := hS.exists_eq_range hS_ne
  simpa [sUnion_range] using hA.iUnion_mem s (fun n ↦ hSA (mem_range_self n))

/-- Definition 1.1 (5): A class of sets is difference-closed if it contains the difference of any
two of its members. -/
class IsDiffClosed (A : Set (Set X)) : Prop where
  diff_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s \ t ∈ A

/-- Definition 1.1 (6): A class of sets is complement-closed if it contains the complement of each
of its members. -/
class IsComplClosed (A : Set (Set X)) : Prop where
  compl_mem : ∀ ⦃s : Set X⦄, s ∈ A → sᶜ ∈ A

/-! ### Exercise_1_1_1 (from Items/Chap01) -/
open MeasureTheory Set
open scoped MeasureTheory

universe u v

variable {Ω : Type u}

-- Proof sketch: disjointify the countable family by recursively removing the previously covered
-- part; each difference of one semiring set with a finite union of previous semiring sets can be
-- refined into a finite disjoint family in the semiring, and then these finite refinements are
-- reindexed by `ℕ`.
/-- Exercise 1.1.1: A countable union of members of a semiring of sets can be rewritten as a
countable pairwise disjoint union of members of the same semiring. -/
theorem exists_disjoint_iUnion_eq_iUnion_of_isSetSemiring {A : Set (Set Ω)}
    (hA : IsSetSemiring A) (s : ℕ → Set Ω) (hs : ∀ n, s n ∈ A) :
    ∃ d : ℕ → Set Ω, IsDisjointUnionDecomposition A s d := sorry

-- Proof sketch: enumerate the finite family by its index type, apply the same finite-step
-- disjointification argument, and keep only the pieces indexed by the original `Finset`.
/-- A finite union of members of a semiring of sets can be rewritten as a finite pairwise disjoint
union of members of the same semiring. -/
theorem exists_disjoint_biUnion_eq_biUnion_of_isSetSemiring {A : Set (Set Ω)} {ι : Type v}
    (hA : IsSetSemiring A) (t : Finset ι) (s : ι → Set Ω) (hs : ∀ i ∈ t, s i ∈ A) :
    ∃ d : ↑t → Set Ω, IsDisjointUnionDecomposition A (fun i : ↑t ↦ s i) d := sorry

/-! ### Exercise_1_1_2 (from Items/Chap01) -/
open Set
open scoped MeasureTheory

private def sigmaFamilyZero : Set (Set (Fin 3)) :=
  {s : Set (Fin 3) | MeasurableSet[MeasurableSpace.generateFrom {({0} : Set (Fin 3))}] s}

private def sigmaFamilyOne : Set (Set (Fin 3)) :=
  {s : Set (Fin 3) | MeasurableSet[MeasurableSpace.generateFrom {({1} : Set (Fin 3))}] s}

-- Proof sketch: in the measurable families generated by `{0}` and `{1}`, the singletons `{0}`
-- and `{1}` are measurable. If their union family were the measurable sets of some measurable
-- space `m`, then `{0, 1}` would be measurable for `m` by closure under binary unions. But
-- `generateFrom` of a singleton set has exactly four measurable sets, namely `∅`, the singleton,
-- its complement, and `univ`, so `{0, 1}` belongs to neither generated family.
/-- Exercise 1.1.2: On the three-point space `Fin 3`, the union of the σ-algebras generated by
`{0}` and `{1}` is not itself a σ-algebra. Equivalently, this union of measurable-set families is
not the measurable family of any `MeasurableSpace (Fin 3)`. -/
theorem union_of_sigma_algebras_need_not_be_sigma_algebra :
    ¬ ∃ m : MeasurableSpace (Fin 3),
      {s : Set (Fin 3) | MeasurableSet[m] s} = sigmaFamilyZero ∪ sigmaFamilyOne := by
  rintro ⟨m, hm⟩
  have h0_in : ({0} : Set (Fin 3)) ∈ sigmaFamilyZero := by
    change MeasurableSet[MeasurableSpace.generateFrom {({0} : Set (Fin 3))}] ({0} : Set (Fin 3))
    rw [MeasureTheory.measurableSet_generateFrom_singleton_iff]
    exact Or.inr <| Or.inl rfl
  have h1_in : ({1} : Set (Fin 3)) ∈ sigmaFamilyOne := by
    change MeasurableSet[MeasurableSpace.generateFrom {({1} : Set (Fin 3))}] ({1} : Set (Fin 3))
    rw [MeasureTheory.measurableSet_generateFrom_singleton_iff]
    exact Or.inr <| Or.inl rfl
  have h0 : MeasurableSet[m] ({0} : Set (Fin 3)) := by
    have hUnion : ({0} : Set (Fin 3)) ∈ sigmaFamilyZero ∪ sigmaFamilyOne := Or.inl h0_in
    have hmem : ({0} : Set (Fin 3)) ∈ {s : Set (Fin 3) | MeasurableSet[m] s} := by
      rw [hm]
      exact hUnion
    simpa using hmem
  have h1 : MeasurableSet[m] ({1} : Set (Fin 3)) := by
    have hUnion : ({1} : Set (Fin 3)) ∈ sigmaFamilyZero ∪ sigmaFamilyOne := Or.inr h1_in
    have hmem : ({1} : Set (Fin 3)) ∈ {s : Set (Fin 3) | MeasurableSet[m] s} := by
      rw [hm]
      exact hUnion
    simpa using hmem
  have h01 : ({0, 1} : Set (Fin 3)) ∈ sigmaFamilyZero ∪ sigmaFamilyOne := by
    have hmem : ({0, 1} : Set (Fin 3)) ∈ {s : Set (Fin 3) | MeasurableSet[m] s} := h0.union h1
    rw [hm] at hmem
    exact hmem
  rcases h01 with h01 | h01
  · change
      MeasurableSet[MeasurableSpace.generateFrom {({0} : Set (Fin 3))}] ({0, 1} : Set (Fin 3)) at h01
    rw [MeasureTheory.measurableSet_generateFrom_singleton_iff] at h01
    rcases h01 with h01 | h01 | h01 | h01
    · have hmem : (0 : Fin 3) ∈ (∅ : Set (Fin 3)) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (0 : Fin 3) ∈ (({0} : Set (Fin 3))ᶜ) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        rw [h01]
        simp
      simp at hmem
  · change
      MeasurableSet[MeasurableSpace.generateFrom {({1} : Set (Fin 3))}] ({0, 1} : Set (Fin 3)) at h01
    rw [MeasureTheory.measurableSet_generateFrom_singleton_iff] at h01
    rcases h01 with h01 | h01 | h01 | h01
    · have hmem : (0 : Fin 3) ∈ (∅ : Set (Fin 3)) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (0 : Fin 3) ∈ ({1} : Set (Fin 3)) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (1 : Fin 3) ∈ (({1} : Set (Fin 3))ᶜ) := by
        rw [← h01]
        simp
      simp at hmem
    · have hmem : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        rw [h01]
        simp
      simp at hmem

/-! ### Exercise_1_1_3 (from Items/Chap01) -/
universe u v

variable {Ω₁ : Type u} {Ω₂ : Type v}
  [MetricSpace Ω₁] [MeasurableSpace Ω₁] [BorelSpace Ω₁] [MetricSpace Ω₂]

-- Proof sketch: The set `{x | ContinuousAt f x}` is a `Gδ` set in a metrizable domain with
-- pseudometrizable codomain, hence it is Borel measurable by
-- `measurableSet_of_continuousAt`. The discontinuity set is its complement.
/-- Exercise 1.1.3: For a map between metric spaces, the set of points at which the map is
discontinuous is a Borel subset of the domain. -/
theorem discontinuity_set_measurable (f : Ω₁ → Ω₂) :
    MeasurableSet {x : Ω₁ | ¬ ContinuousAt f x} := by
  simpa [Set.compl_setOf] using (measurableSet_of_continuousAt f).compl

/-! ### Exercise_1_1_4 (from Items/Chap01) -/
open Set
open MeasureTheory MeasurableSpace

universe u

/-- A set is measurable in the countable-co-countable measurable space exactly when it is
countable or cocountable. -/
-- Proof sketch: use Example 1.11 (16), which identifies the measurable sets of the canonical
-- generated sigma-algebra.
theorem measurableSet_countable_or_countable_compl_measurable_space_iff
    {Ω : Type u} {s : Set Ω} :
    MeasurableSet[generateFrom (countableOrCocountableFamily Ω)] s ↔
      s.Countable ∨ (sᶜ).Countable := by
  sorry

/-- Exercise 1.1.4: the σ-algebra generated by all singletons is the countable-co-countable
measurable space. -/
-- Proof sketch: prove the forward inclusion by `generateFrom` induction, using that the
-- countable-or-co-countable sets form a measurable space; prove the reverse inclusion by writing
-- every countable set as a countable union of singletons and using complements for cocountable
-- sets.
theorem generateFrom_singletons_eq_countable_or_countable_compl (Ω : Type u) :
    MeasurableSpace.generateFrom (Set.range fun ω : Ω ↦ ({ω} : Set Ω)) =
      generateFrom (countableOrCocountableFamily Ω) := sorry

/-! ### Exercise_1_1_5 (from Items/Chap01) -/
open scoped symmDiff BooleanRingOfBooleanAlgebra
open Set MeasureTheory

universe u

variable {Ω : Type u} {A : Set (Set Ω)}

namespace IsSetRing

/-- Closure of a ring of sets under symmetric difference. -/
-- Proof sketch: expand `s ∆ t` as `(s \ t) ∪ (t \ s)` and use closure under set difference and
-- binary union.
lemma symmDiff_mem (hA : IsSetRing A) {s t : Set Ω} (hs : s ∈ A) (ht : t ∈ A) : s ∆ t ∈ A := by
  rw [Set.symmDiff_def]
  exact hA.union_mem (hA.diff_mem hs ht) (hA.diff_mem ht hs)

/-- The non-unital subring of `Set Ω` determined by a ring of sets. -/
def toNonUnitalSubring (hA : IsSetRing A) : NonUnitalSubring (Set Ω) where
  carrier := A
  zero_mem' := hA.empty_mem
  add_mem' := symmDiff_mem hA
  neg_mem' hs := by simpa using hs
  mul_mem' := hA.inter_mem

/-- Membership in the non-unital subring attached to a ring of sets is membership in the
underlying family. -/
@[simp] lemma mem_toNonUnitalSubring (hA : IsSetRing A) {s : Set Ω} :
    s ∈ toNonUnitalSubring hA ↔ s ∈ A :=
  Iff.rfl

/-- Exercise 1.1.5: A ring of subsets of `Ω` carries the structure of a commutative non-unital
ring, with multiplication given by intersection and addition given by symmetric difference. -/
instance subtype_nonUnitalCommRing (hA : IsSetRing A) :
    NonUnitalCommRing {s : Set Ω // s ∈ A} :=
  (toNonUnitalSubring hA).toNonUnitalCommRing

end IsSetRing
