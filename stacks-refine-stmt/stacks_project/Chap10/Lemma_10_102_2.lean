import Mathlib
import stacks_project.Chap10.Situation_10_102_1

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}

/-- The `a,b` coordinate of the differential `C_{i + 1} → C_i` in the chosen standard bases. -/
def diffEntry (C : _root_.FiniteFreeComplex R e) (i : Fin e)
    (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) : R :=
  C.diffAt i (Pi.single a 1) b

/-- The rank function obtained by removing one basis vector in degrees `i + 1` and `i`. -/
def splitRank (n : Fin (e + 1) → ℕ) (i : Fin e) : Fin (e + 1) → ℕ :=
  fun j ↦ if j = i.succ ∨ j = i.castSucc then n j - 1 else n j

private def identityDiskRank (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

private def identityDiskMatrix (i : Fin e) (j : ℕ) :
    Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

private abbrev identityDiskDifferential (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((identityDiskMatrix i j).toLinearMapRight')

private theorem identityDiskDifferential_sq (i : Fin e) (j : ℕ) :
    identityDiskDifferential i (j + 1) ≫ identityDiskDifferential i j =
      (0 :
        ModuleCat.of R (Fin (identityDiskRank i (j + 2)) → R) ⟶
          ModuleCat.of R (Fin (identityDiskRank i j) → R)) := sorry

/-- The two-term identity complex `… → 0 → R → R → 0 → …` supported in degrees `i + 1` and `i`.
-/
def identityDiskComplex (i : Fin e) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (fun j ↦ ModuleCat.of R (Fin (identityDiskRank i j) → R))
    (identityDiskDifferential i)
    (identityDiskDifferential_sq i)

-- Proof sketch: use elementary row and column operations in the chosen coordinates of `C.diffAt i`
-- to isolate a unit entry, split off the corresponding free rank-one summand in degrees `i + 1`
-- and `i`, and identify the resulting summand with `identityDiskComplex i`.
/-- Lemma 10.102.2: if a differential `R^(n_{i + 1}) → R^(n_i)` in a bounded finite free complex
has a unit coordinate in the chosen standard bases, then the complex is isomorphic to the direct
sum of a reduced finite free complex and the two-term identity complex supported in degrees
`i + 1` and `i`. -/
theorem exists_iso_biprod_identityDisk_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    ∃ C' : _root_.FiniteFreeComplex R e,
      C'.rank = splitRank C.rank i ∧
      Nonempty (C.toChainComplex ≅ biprod C'.toChainComplex (identityDiskComplex i)) := sorry

end FiniteFreeComplex

end
