module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.PNat.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Prod

public section

universe u

/- Exercise 5.2 (a): split a finite product into its initial segment and last entry. -/
#check fun (n : ℕ) (A : Fin (n + 2) → Type u) ↦
  ((Equiv.prodComm _ _).trans (Fin.snocEquiv A) :
    (((i : Fin (n + 1)) → A i.castSucc) × A (Fin.last (n + 1))) ≃
      ((i : Fin (n + 2)) → A i))

namespace AdjacentPair

/-- Helper for Exercise 5.2: the positive index `2 * i - 1`, expressed using
the predecessor coordinate of `i`. -/
def oddIndex (i : ℕ+) : ℕ+ :=
  Nat.succPNat (2 * i.natPred)

/-- Helper for Exercise 5.2: the positive index `2 * i`, expressed using the
predecessor coordinate of `i`. -/
def evenIndex (i : ℕ+) : ℕ+ :=
  Nat.succPNat (2 * i.natPred + 1)

/-- Helper for Exercise 5.2: adjacent-pair coordinates enumerate the positive integers. -/
def indexEquiv : (Σ _ : ℕ+, Fin 2) ≃ ℕ+ :=
  (Equiv.sigmaEquivProd ℕ+ (Fin 2)).trans
    ((Equiv.prodCongr Equiv.pnatEquivNat finTwoEquiv).trans
      ((Equiv.prodComm ℕ Bool).trans
        (Equiv.boolProdNatEquivNat.trans Equiv.pnatEquivNat.symm)))

/-- Exercise 5.2 (b): regroup a positive-integer-indexed product into adjacent pairs. -/
def sequenceEquiv (A : ℕ+ → Type u) :
    (∀ i, A i) ≃ ∀ i, A (oddIndex i) × A (evenIndex i) :=
  (Equiv.piCongrLeft A indexEquiv).symm.trans
    ((Equiv.piCurry (fun i j ↦ A (indexEquiv ⟨i, j⟩))).trans
      (Equiv.piCongrRight fun i ↦ piFinTwoEquiv fun j ↦ A (indexEquiv ⟨i, j⟩)))

end AdjacentPair
