module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.PNat.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Prod

public section

universe u

namespace AdjacentPair

/-- The positive index `2 * i - 1`, expressed using the predecessor coordinate of `i`. -/
def oddIndex (i : ℕ+) : ℕ+ :=
  Nat.succPNat (2 * i.natPred)

/-- The positive index `2 * i`, expressed using the predecessor coordinate of `i`. -/
def evenIndex (i : ℕ+) : ℕ+ :=
  Nat.succPNat (2 * i.natPred + 1)

/-- The positive integers, indexed as the first and second entries of adjacent pairs,
are equivalent to positive integers in their usual order. -/
def indexEquiv : (Σ _ : ℕ+, Fin 2) ≃ ℕ+ :=
  (Equiv.sigmaEquivProd ℕ+ (Fin 2)).trans
    ((Equiv.prodCongr Equiv.pnatEquivNat finTwoEquiv).trans
      ((Equiv.prodComm ℕ Bool).trans
        (Equiv.boolProdNatEquivNat.trans Equiv.pnatEquivNat.symm)))

/-- The first entry of the `i`th adjacent pair has index `2 * i - 1`. -/
theorem oddIndex_coe (i : ℕ+) : (oddIndex i : ℕ) = 2 * (i : ℕ) - 1 := by
  -- Reduce the positive-natural construction to arithmetic on its underlying natural number.
  have indexPositive : 0 < (i : ℕ) := i.2
  simp only [oddIndex, Nat.succPNat_coe, PNat.natPred]
  omega

/-- The second entry of the `i`th adjacent pair has index `2 * i`. -/
theorem evenIndex_coe (i : ℕ+) : (evenIndex i : ℕ) = 2 * (i : ℕ) := by
  -- Reduce the positive-natural construction to arithmetic on its underlying natural number.
  have indexPositive : 0 < (i : ℕ) := i.2
  simp only [evenIndex, Nat.succPNat_coe, PNat.natPred]
  omega

/-- The first entry of the `i`th adjacent pair is indexed by `oddIndex i`. -/
theorem indexEquiv_zero (i : ℕ+) : indexEquiv ⟨i, 0⟩ = oddIndex i := by
  -- Compute the first `Fin 2` coordinate through the canonical index equivalence.
  rfl

/-- The second entry of the `i`th adjacent pair is indexed by `evenIndex i`. -/
theorem indexEquiv_one (i : ℕ+) : indexEquiv ⟨i, 1⟩ = evenIndex i := by
  -- Compute the second `Fin 2` coordinate through the canonical index equivalence.
  rfl

/-- Regroup a positive-integer-indexed dependent product into adjacent pairs. -/
def sequenceEquiv (A : ℕ+ → Type u) :
    (∀ i, A i) ≃ ∀ i, A (oddIndex i) × A (evenIndex i) :=
  (Equiv.piCongrLeft A indexEquiv).symm.trans
    ((Equiv.piCurry (fun i j ↦ A (indexEquiv ⟨i, j⟩))).trans
      (Equiv.piCongrRight fun i ↦ piFinTwoEquiv fun j ↦ A (indexEquiv ⟨i, j⟩)))

/-- Regrouping a dependent sequence evaluates to its two adjacent coordinates. -/
theorem sequenceEquiv_apply (A : ℕ+ → Type u) (f : ∀ i, A i) (i : ℕ+) :
    sequenceEquiv A f i = (f (oddIndex i), f (evenIndex i)) := by
  -- Compare the two product coordinates after exposing the composite equivalence.
  apply Prod.ext
  · rfl
  · rfl

/-- Helper for Exercise 5.2: ungrouping and regrouping recovers each adjacent pair. -/
theorem sequenceEquiv_symm_apply_pair (A : ℕ+ → Type u)
    (f : ∀ i, A (oddIndex i) × A (evenIndex i)) (i : ℕ+) :
    ((sequenceEquiv A).symm f (oddIndex i),
      (sequenceEquiv A).symm f (evenIndex i)) = f i := by
  -- Evaluate the global inverse law at `i`, then expose the forward coordinate formula.
  have inverseLaw := congrFun ((sequenceEquiv A).apply_symm_apply f) i
  rwa [sequenceEquiv_apply] at inverseLaw

/-- Ungrouping recovers the first coordinate of each adjacent pair. -/
theorem sequenceEquiv_symm_apply_zero (A : ℕ+ → Type u)
    (f : ∀ i, A (oddIndex i) × A (evenIndex i)) (i : ℕ+) :
    (sequenceEquiv A).symm f (oddIndex i) = (f i).1 := by
  -- Project the first coordinate from the pair-valued inverse computation rule.
  exact congrArg Prod.fst (sequenceEquiv_symm_apply_pair A f i)

/-- Ungrouping recovers the second coordinate of each adjacent pair. -/
theorem sequenceEquiv_symm_apply_one (A : ℕ+ → Type u)
    (f : ∀ i, A (oddIndex i) × A (evenIndex i)) (i : ℕ+) :
    (sequenceEquiv A).symm f (evenIndex i) = (f i).2 := by
  -- Project the second coordinate from the pair-valued inverse computation rule.
  exact congrArg Prod.snd (sequenceEquiv_symm_apply_pair A f i)


end AdjacentPair
