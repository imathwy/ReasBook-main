import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_5_6

open CategoryTheory

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical mathlib theorem for the `RP^n` cellular
-- differential formula surfaced in the current environment. Construction 13.5.6 supplies the
-- chosen standard CW structure on `RP^n`, while Chapter 12/13 precedent uses `ChainComplex.of`
-- as the canonical owner for explicit chain-level models and keeps separate specification theorems
-- tying those models to the actual cellular data.

/-- The graded `ℤ`-modules underlying the parity-formula cellular chain complex model of `RP^n`:
there is one generator in each degree `m ≤ n` and no generators above degree `n`. -/
private def realProjectiveSpaceParityCellularChainComplexObj (n : ℕ) : ℕ → ModuleCat ℤ
  | m => if m ≤ n then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The boundary map in the parity-formula cellular chain complex model of `RP^n`: in degree
`k ≤ n` it is `0` for odd `k` and `2 • LinearMap.id` for even `k`, and it vanishes above the top
cell degree. -/
private def realProjectiveSpaceParityCellularChainComplexBoundary (n : ℕ) (m : ℕ) :
    realProjectiveSpaceParityCellularChainComplexObj n (m + 1) ⟶
      realProjectiveSpaceParityCellularChainComplexObj n m :=
  if hm : m + 1 ≤ n then
    (eqToHom (by
      simp [realProjectiveSpaceParityCellularChainComplexObj, hm])) ≫
      (if Odd (m + 1) then
        0
      else
        ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
      (eqToHom (by
        simp [realProjectiveSpaceParityCellularChainComplexObj, Nat.le_of_succ_le hm]))
  else
    0

/-- The parity-formula boundary maps for `RP^n` square to zero. -/
private theorem realProjectiveSpaceParityCellularChainComplexBoundary_sq
    (n m : ℕ) :
    realProjectiveSpaceParityCellularChainComplexBoundary n (m + 1) ≫
      realProjectiveSpaceParityCellularChainComplexBoundary n m = 0 := by
  by_cases hm : m + 2 ≤ n
  · have hm' : m + 1 ≤ n := Nat.le_trans (Nat.le_succ (m + 1)) hm
    by_cases hodd : Odd (m + 1)
    · simp [realProjectiveSpaceParityCellularChainComplexBoundary, hm, hm', hodd]
    · have hmEven : Even (m + 1) := Nat.not_odd_iff_even.mp hodd
      have hodd' : Odd (m + 2) := by
        simpa [Nat.add_assoc] using hmEven.add_odd odd_one
      simp [realProjectiveSpaceParityCellularChainComplexBoundary, hm, hm', hodd, hodd']
  · simp [realProjectiveSpaceParityCellularChainComplexBoundary, hm]

/-- The standard parity-formula cellular chain complex model for `RP^n`. Its degree-`m` object is
`ℤ` for `m ≤ n` and `0` above degree `n`; its degree-`k` differential is `0` for odd `k` and
`2 • LinearMap.id` for even `k ≤ n`. -/
abbrev realProjectiveSpaceParityCellularChainComplex (n : ℕ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (realProjectiveSpaceParityCellularChainComplexObj n)
    (realProjectiveSpaceParityCellularChainComplexBoundary n)
    (realProjectiveSpaceParityCellularChainComplexBoundary_sq n)

/-- In the parity-formula cellular chain complex of `RP^n`, degree `m ≤ n` has chain group `ℤ`. -/
@[simp] theorem realProjectiveSpaceParityCellularChainComplex_X_of_le
    (n m : ℕ) (hm : m ≤ n) :
    (realProjectiveSpaceParityCellularChainComplex n).X m = ModuleCat.of ℤ ℤ := by
  rw [ChainComplex.of_x]
  simp [realProjectiveSpaceParityCellularChainComplexObj, hm]

/-- In the parity-formula cellular chain complex of `RP^n`, there are no cells above degree `n`. -/
@[simp] theorem realProjectiveSpaceParityCellularChainComplex_X_of_gt
    (n m : ℕ) (hm : n < m) :
    (realProjectiveSpaceParityCellularChainComplex n).X m = ModuleCat.of ℤ (Fin 0 → ℤ) := by
  rw [ChainComplex.of_x]
  simp [realProjectiveSpaceParityCellularChainComplexObj, Nat.not_le.mpr hm]

/-- If `(k : ℕ) ≤ n`, then also `k.natPred ≤ n`. -/
private theorem realProjectiveSpaceNatPred_le
    (k : ℕ+) {n : ℕ} (hkn : (k : ℕ) ≤ n) :
    k.natPred ≤ n :=
  le_trans (by simpa [PNat.natPred_add_one] using Nat.le_succ k.natPred) hkn

namespace RealProjectiveSpaceStandardCWStructure

/-- A chosen Chapter 13 cellular differential family on the standard CW structure `S` on `RP^n`.
-/
abbrev cellularDifferentialFamily {n : ℕ} (S : RealProjectiveSpaceStandardCWStructure n) :=
  letI := S.cwComplex
  CellularDifferentialFamily (RealProjectiveSpace n)

end RealProjectiveSpaceStandardCWStructure

/-- The degree-`k` differential of `realProjectiveSpaceParityCellularChainComplex n`, transported
to the standard rank-one coordinates on the source and target chain groups. -/
def realProjectiveSpaceParityCellularDifferential
    (n : ℕ) (k : ℕ+) (hkn : (k : ℕ) ≤ n) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  (eqToIso (realProjectiveSpaceParityCellularChainComplex_X_of_le n (k : ℕ) hkn).symm).hom ≫
    (realProjectiveSpaceParityCellularChainComplex n).d (k : ℕ) k.natPred ≫
      (eqToIso
        (realProjectiveSpaceParityCellularChainComplex_X_of_le n k.natPred
          (realProjectiveSpaceNatPred_le k hkn))).hom

/-- In the parity-formula cellular chain complex model of `RP^n`, the transported degree-`k`
differential is `0` for odd `k` and `2 • LinearMap.id` for even `k ≤ n`. -/
@[simp] theorem realProjectiveSpaceParityCellularDifferential_eq
    (n : ℕ) (k : ℕ+) (hkn : (k : ℕ) ≤ n) :
    realProjectiveSpaceParityCellularDifferential n k hkn =
      if Odd (k : ℕ) then
        0
      else
        ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  rcases k with ⟨k, hkpos⟩
  cases k with
  | zero => cases hkpos
  | succ m =>
      have hm : m < n := Nat.lt_of_succ_le hkn
      simp [realProjectiveSpaceParityCellularDifferential,
        realProjectiveSpaceParityCellularChainComplexBoundary, hm]

/-- The unique `m`-cell of a chosen standard CW structure on `RP^n`, obtained from the fact that
the standard structure has exactly one cell in each degree `m ≤ n`. -/
@[reducible]
private def realProjectiveSpaceStandardCellUnique {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (m : ℕ) (hm : m ≤ n) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
    Unique (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) := by
  classical
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
  have hcard :
      Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) = 1 :=
    S.cellCard_eq_one m hm
  have hfinite :
      Finite (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) :=
    Nat.finite_of_card_ne_zero (by simp [hcard])
  letI : Fintype (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) :=
    Fintype.ofFinite _
  exact
    (Classical.choice <|
      Fintype.card_eq_one_iff_nonempty_unique.mp (by
        simpa [Nat.card_eq_fintype_card] using hcard) :
      Unique (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m))

/-- The standard rank-one identification of the cellular chain group `C_m(RP^n)` with `ℤ`,
coming from the unique `m`-cell in the chosen standard CW structure. -/
private def realProjectiveSpaceCellularChainGroupIsoInt {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (m : ℕ) (hm : m ≤ n) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
    ModuleCat.of ℤ (cellularChainGroup (RealProjectiveSpace n) m) ≅ ModuleCat.of ℤ ℤ := by
  classical
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
  letI :
      Unique (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) :=
    realProjectiveSpaceStandardCellUnique S m hm
  exact
    LinearEquiv.toModuleIso <|
      (FreeAbelianGroup.uniqueEquiv
        (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m)).toIntLinearEquiv

/-- The auxiliary parity-formula attaching-degree data for the standard rank-one model of
`RP^n`: the unique `(k - 1)`-cell occurs with coefficient `0` in odd degree `k` and coefficient
`2` in even positive degree `k`. -/
private def realProjectiveSpaceParityAttachingDegreeModel {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (k : ℕ+) (hkn : (k : ℕ) ≤ n) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
    cellularCell (RealProjectiveSpace n) (k.natPred + 1) →
      cellularCell (RealProjectiveSpace n) k.natPred →₀ ℤ := by
  classical
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
  letI : Unique (cellularCell (RealProjectiveSpace n) k.natPred) :=
    realProjectiveSpaceStandardCellUnique S k.natPred
      (le_trans (by simpa [PNat.natPred_add_one] using Nat.le_succ k.natPred) hkn)
  intro _
  exact Finsupp.single default (if Odd (k : ℕ) then 0 else 2)

/-- The transported degree-`k` differential determined by an explicit attaching-degree family on
the chosen standard CW structure on `RP^n`, written in the standard rank-one coordinates on the
source and target cellular chain groups. This remains private because the public source-facing API
for actual cellular differentials should reuse `CellularDifferentialFamily`. -/
private def realProjectiveSpaceCellularDifferentialFromDegrees {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (k : ℕ+) (hkn : (k : ℕ) ≤ n)
    (attachingDegree :
      letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
      cellularCell (RealProjectiveSpace n) (k.natPred + 1) →
        cellularCell (RealProjectiveSpace n) k.natPred →₀ ℤ) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := by
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
  let sourceIso := realProjectiveSpaceCellularChainGroupIsoInt S (k.natPred + 1)
    (by simpa [PNat.natPred_add_one] using hkn)
  let targetIso := realProjectiveSpaceCellularChainGroupIsoInt S k.natPred
    (le_trans (by simpa [PNat.natPred_add_one] using Nat.le_succ k.natPred) hkn)
  exact
    sourceIso.inv ≫
      ModuleCat.ofHom
        ((cellularDifferentialFromDegrees (RealProjectiveSpace n) k.natPred
          attachingDegree).toIntLinearMap) ≫
      targetIso.hom

/-- The actual degree-`k` cellular differential on a chosen standard CW structure `S` on `RP^n`,
expressed in the standard rank-one coordinates on the source and target cellular chain groups,
using the repository's chosen cellular-differential owner `CellularDifferentialFamily`. -/
def realProjectiveSpaceActualCellularDifferential {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (data : S.cellularDifferentialFamily)
    (k : ℕ+) (hkn : (k : ℕ) ≤ n) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := by
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := S.cwComplex
  let sourceIso := realProjectiveSpaceCellularChainGroupIsoInt S (k.natPred + 1)
    (by simpa [PNat.natPred_add_one] using hkn)
  let targetIso := realProjectiveSpaceCellularChainGroupIsoInt S k.natPred
    (le_trans (by simpa [PNat.natPred_add_one] using Nat.le_succ k.natPred) hkn)
  exact
    sourceIso.inv ≫
      ModuleCat.ofHom (data.differential k.natPred).toIntLinearMap ≫
      targetIso.hom

/-- Construction 13.5.6 together with the chosen Chapter 13 cellular differential family on the
standard CW structure `S` identifies the transported actual degree-`k` cellular differential on
`RP^n` with the parity-formula differential in
`realProjectiveSpaceParityCellularChainComplex n`. -/
theorem realProjectiveSpaceActualCellularDifferential_spec {n : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure n) (data : S.cellularDifferentialFamily)
    (k : ℕ+) (hkn : (k : ℕ) ≤ n) :
    realProjectiveSpaceActualCellularDifferential S data k hkn =
      realProjectiveSpaceParityCellularDifferential n k hkn := sorry

/-- Calculation 13.5.7 (1): for a chosen standard CW structure `S` on `RP^n` equipped with a
chosen Chapter 13 cellular differential family, the transported actual degree-`k` cellular
differential is zero whenever `(k : ℕ) ≤ n` and `k` is odd. -/
theorem realProjectiveSpaceActualCellularDifferential_eq_zero_of_odd
    {n : ℕ} (S : RealProjectiveSpaceStandardCWStructure n) (data : S.cellularDifferentialFamily)
    (k : ℕ+) (hkn : (k : ℕ) ≤ n) (hkodd : Odd (k : ℕ)) :
    realProjectiveSpaceActualCellularDifferential S data k hkn = 0 := sorry

/-- Calculation 13.5.7 (2): for a chosen standard CW structure `S` on `RP^n` equipped with a
chosen Chapter 13 cellular differential family, the transported actual degree-`k` cellular
differential is multiplication by `2` whenever `(k : ℕ) ≤ n` and `k` is even. -/
theorem realProjectiveSpaceActualCellularDifferential_eq_two_of_even
    {n : ℕ} (S : RealProjectiveSpaceStandardCWStructure n) (data : S.cellularDifferentialFamily)
    (k : ℕ+) (hkn : (k : ℕ) ≤ n) (hkeven : Even (k : ℕ)) :
    realProjectiveSpaceActualCellularDifferential S data k hkn =
      ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := sorry
