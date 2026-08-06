import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_10

noncomputable section

open CategoryTheory
open Topology
open scoped CellularChainGroup

universe u

-- Semantic recall via `lean_leansearch`: `ChainComplex.of` is the canonical owner for a chain
-- complex assembled from degreewise differentials, and `K.homology n` is the canonical owner for
-- its degree-`n` homology object. Since Definition 13.2.11 depends on the chosen differential
-- family from Lemma 13.2.10, this file packages those chosen cellular differentials into a chain
-- complex and defines cellular homology as its degreewise homology.

variable (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
variable (data : CellularDifferentialFamily X)

/-- The chosen cellular differentials on `X` compose to zero after being viewed as morphisms in
`ModuleCat ℤ`. -/
theorem cellularChainComplex_sq
    (n : ℕ) :
    ModuleCat.ofHom (data.differential (n + 1)).toIntLinearMap ≫
      ModuleCat.ofHom (data.differential n).toIntLinearMap = 0 := by
  ext x
  simpa using congrArg (fun f ↦ f x) (cellularDifferential_squareZero X data n)

/-- The chosen cellular chain complex `C_*(X)` determined by the Chapter 13 cellular
differentials on `X`. -/
abbrev cellularChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (fun n ↦ ModuleCat.of ℤ (C[n](X)))
    (fun n ↦ ModuleCat.ofHom (data.differential n).toIntLinearMap)
    (cellularChainComplex_sq X data)

/-- The differential of `cellularChainComplex X data` in degree `n` is the chosen cellular
differential `data.differential n`. -/
@[simp] theorem cellularChainComplex_d
    (n : ℕ) :
    (cellularChainComplex X data).d (n + 1) n =
      ModuleCat.ofHom (data.differential n).toIntLinearMap := by
  exact
    ChainComplex.of_d
      (fun n ↦ ModuleCat.of ℤ (C[n](X)))
      (fun n ↦ ModuleCat.ofHom (data.differential n).toIntLinearMap)
      (cellularChainComplex_sq X data)
      n

/-- Definition 13.2.11. Cellular homology `H_*(X)` is the homology of the cellular chain complex
`C_*(X)` determined by the chosen Chapter 13 cellular differentials on `X`. -/
abbrev cellularHomology (n : ℕ) : ModuleCat ℤ :=
  (cellularChainComplex X data).homology n

/-- Evaluating `cellularHomology X data` in degree `n` gives the degree-`n` homology object of
the chosen cellular chain complex `C_*(X)`. -/
@[simp] theorem cellularHomology_apply
    (n : ℕ) :
    cellularHomology X data n = (cellularChainComplex X data).homology n :=
  rfl
