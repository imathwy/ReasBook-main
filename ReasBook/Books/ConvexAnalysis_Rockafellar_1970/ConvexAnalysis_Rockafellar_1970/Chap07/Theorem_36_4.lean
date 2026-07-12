import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_1_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v

open Set
open scoped Rockafellar

namespace Bifunction

section Minimax

variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 36.4 says that equivalent saddle-functions determine the same minimax
  problem: they have the same row-infimum function, the same column-supremum function, therefore
  the same lower and upper minimax values, and the same saddle-points.
- `core/canonical`: the Chapter 34 owner for equivalence is `K ∼ L`, i.e. equality of the
  partial closures `cl₁` and `cl₂`; the Chapter 6/7 owner layer for the row and column aggregate
  functions is `perturbationFunction` and `upperPerturbationFunction`, and the Chapter 36
  saddle-point owner is `Bifunction.IsSaddlePointOn`.
- `bridge/view`: the source row/column formulas are companion views of those canonical owners, and
  the saddle-point transfer is mediated by Definition 36.1.1's attained-`iInf`/`iSup`
  characterization of `Bifunction.IsSaddlePointOn`.

Domain-style sampling used here:
- `Bifunction.equivalent_iff` from `Defn_34_4`;
- `Bifunction.perturbationFunction` from `Chap06.Definition_6_29_1`;
- `Bifunction.upperPerturbationFunction` from `Chap06.Definition_6_30_11`;
- `Bifunction.maximinValueOn`, `Bifunction.minimaxValueOn`, and `Bifunction.HasSaddleValueOn` from
  `Definition_36_0_1`;
- whole-space owner bridges `Bifunction.maximinValue`, `Bifunction.minimaxValue`,
  `Bifunction.HasSaddleValue` from `Definition_36_0_1`;
- `Bifunction.isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value` from `Definition_36_1_1`;
- whole-space owner bridge `Bifunction.IsSaddlePoint` from `Chap06.Definition_6_28_7`;
- `cl(·)`, `lowerSemicontinuousHull_le`, and `le_lowerSemicontinuousHull` from Chapter 2;
- `concaveClosure` from Chapter 6.

Primitive data vs derived API:
- primitive owner data: two saddle-functions `K`, `K'` and an equivalence proof `K ∼ K'`;
- derived API: equality of the canonical owner functions `perturbationFunction K` and
  `upperPerturbationFunction (Function.swap K)`, their source-facing row/column companion
  formulas, equality of the two Chapter 36 minimax-value owners on the one-sided set-indexed
  layers `C × univ` and `univ × D`, the induced whole-space owner equalities
  `maximinValue`, `minimaxValue`, `HasSaddleValue`, and invariance of the whole-space saddle-point
  owner `IsSaddlePoint`.

Layer target: `bridge/view`. The source theorem compares two equivalent saddle-functions, while
  the public API should reuse the chapter equivalence owner and the canonical saddle-point owner
  instead of introducing a second saddle-value package.

Codomain-layer split used in this file:
- the bridge from `K ∼ K'` to row/column aggregate equality is stated at codomain
  `WithTopBot 𝕜`, using the Chapter 34 partial-closure owners `cl₁`/`cl₂` together with the
  codomain assumptions needed by the closure-to-`iInf`/`iSup` transport;
- once those aggregate equalities are available, transport of maximin/minimax values and
  saddle-value existence is stated at the primitive codomain layer `SupSet`/`InfSet`;
- source-order saddle-point transport is then stated at the codomain-generic
  `CompleteLattice` layer via `Bifunction.IsSaddlePointOn`.
-/

section EquivalentBridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜] [NoBotOrder 𝕜]

private theorem iSup_concaveClosure_eq_iSup
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜] (g : U → WithTopBot 𝕜) :
    (⨆ u, concaveClosure g u) = ⨆ u, g u := by
  have hcl :
      -((⨅ u, cl(-g) u) : WithTopBot 𝕜) = ⨆ u, -(cl(-g) u) := by
    refine le_antisymm ?_ ?_
    · exact (WithBotTop.neg_le).2 <| le_iInf fun u ↦
        by simpa [neg_neg] using
          (WithBotTop.neg_le_neg_iff).2 (le_iSup (fun u ↦ -(cl(-g) u)) u)
    · refine iSup_le fun u ↦ ?_
      exact (WithBotTop.neg_le_neg_iff).2 (iInf_le (fun u ↦ cl(-g) u) u)
  have hg :
      -((⨅ u, -g u) : WithTopBot 𝕜) = ⨆ u, g u := by
    refine le_antisymm ?_ ?_
    · exact (WithBotTop.neg_le).2 <| le_iInf fun u ↦
        (WithBotTop.neg_le_neg_iff).2 (le_iSup (fun u ↦ g u) u)
    · refine iSup_le fun u ↦ ?_
      exact (WithBotTop.le_neg).2 (iInf_le (fun u ↦ -g u) u)
  calc
    (⨆ u, concaveClosure g u) = ⨆ u, -(cl(-g) u) := by
      simp [concaveClosure_eq_neg_lowerSemicontinuousHull_neg]
    _ = -((⨅ u, cl(-g) u) : WithTopBot 𝕜) := hcl.symm
    _ = -((⨅ u, -g u) : WithTopBot 𝕜) := by
      simpa using congrArg Neg.neg (iInf_lowerSemicontinuousHull_eq_iInf (-g))
    _ = ⨆ u, g u := hg

/-- Equivalent saddle-functions have the same canonical row-infimum owner
`perturbationFunction`. -/
theorem perturbationFunction_eq_of_equivalent
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    perturbationFunction K = perturbationFunction K' := by
  funext u
  rcases (equivalent_iff K K').1 hKK' with ⟨-, h₂⟩
  calc
    perturbationFunction K u = ⨅ x, cl(K u) x := by
      rw [perturbationFunction_apply]
      exact (iInf_lowerSemicontinuousHull_eq_iInf (K u)).symm
    _ = ⨅ x, cl(K' u) x := by
      simpa [closure2_apply] using congrArg (fun F : U → X → WithTopBot 𝕜 ↦ ⨅ x, F u x) h₂
    _ = perturbationFunction K' u := by
      rw [perturbationFunction_apply]
      exact iInf_lowerSemicontinuousHull_eq_iInf (K' u)

/-- Equivalent saddle-functions have the same row-infimum function `u ↦ inf_x K(u, x)`. -/
theorem iInf_eq_iInf_of_equivalent {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x := by
  simpa [perturbationFunction_apply] using perturbationFunction_eq_of_equivalent hKK'

@[simp] theorem iInf_eq_iInf_of_equivalent_apply
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (u : U) :
    (⨅ x, K u x) = ⨅ x, K' u x := by
  simpa using congrArg (fun F : U → WithTopBot 𝕜 ↦ F u) (iInf_eq_iInf_of_equivalent hKK')

/-- Equivalent saddle-functions have the same canonical column-supremum owner, written on the
swapped kernel as `upperPerturbationFunction (Function.swap K)`. -/
theorem upperPerturbationFunction_swap_eq_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    upperPerturbationFunction (Function.swap K) =
      upperPerturbationFunction (Function.swap K') := by
  funext x
  rcases (equivalent_iff K K').1 hKK' with ⟨h₁, -⟩
  calc
    upperPerturbationFunction (Function.swap K) x =
        ⨆ u, concaveClosure (fun u' ↦ K u' x) u := by
      rw [upperPerturbationFunction_apply]
      exact (iSup_concaveClosure_eq_iSup fun u' ↦ K u' x).symm
    _ = ⨆ u, concaveClosure (fun u' ↦ K' u' x) u := by
      simpa [closure1_apply] using congrArg (fun F : U → X → WithTopBot 𝕜 ↦ ⨆ u, F u x) h₁
    _ = upperPerturbationFunction (Function.swap K') x := by
      rw [upperPerturbationFunction_apply]
      exact iSup_concaveClosure_eq_iSup fun u' ↦ K' u' x

/-- Equivalent saddle-functions have the same column-supremum function `x ↦ sup_u K(u, x)`. -/
theorem iSup_eq_iSup_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x := by
  simpa [upperPerturbationFunction_apply, Function.swap] using
    upperPerturbationFunction_swap_eq_of_equivalent hKK'

@[simp] theorem iSup_eq_iSup_of_equivalent_apply
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (x : X) :
    (⨆ u, K u x) = ⨆ u, K' u x := by
  simpa using congrArg (fun F : X → WithTopBot 𝕜 ↦ F x) (iSup_eq_iSup_of_equivalent hKK')

end EquivalentBridge

section CodomainGeneric

variable {β : Type*}
variable {U' : Type*} {X' : Type*}

section

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `C × D`. -/
theorem maximinValueOn_eq_of_iInf₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x) :
    maximinValueOn C D K = maximinValueOn C D K' := by
  simpa [maximinValueOn] using congrArg (fun F : U' → β ↦ ⨆ u ∈ C, F u) hRow

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `C × D`. -/
theorem minimaxValueOn_eq_of_iSup₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x) :
    minimaxValueOn C D K = minimaxValueOn C D K' := by
  simpa [minimaxValueOn] using congrArg (fun F : X' → β ↦ ⨅ x ∈ D, F x) hCol

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `C × univ`. -/
theorem maximinValueOn_eq_of_iInf_eq_right_univ
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) (C : Set U') :
    maximinValueOn C univ K = maximinValueOn C univ K' := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  simpa using maximinValueOn_eq_of_iInf₂_eq C (univ : Set X') hRow'

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `univ × D`. -/
theorem minimaxValueOn_eq_of_iSup_eq_left_univ
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) (D : Set X') :
    minimaxValueOn univ D K = minimaxValueOn univ D K' := by
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using minimaxValueOn_eq_of_iSup₂_eq (univ : Set U') D hCol'

/-- If two bifunctions have the same row-infimum function, they have the same Chapter 36
maximin value on `univ × univ`. -/
theorem maximinValueOn_univ_eq_of_iInf_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) :
    maximinValueOn univ univ K = maximinValueOn univ univ K' := by
  simpa using maximinValueOn_eq_of_iInf_eq_right_univ hRow (univ : Set U')

/-- If two bifunctions have the same column-supremum function, they have the same Chapter 36
minimax value on `univ × univ`. -/
theorem minimaxValueOn_univ_eq_of_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    minimaxValueOn univ univ K = minimaxValueOn univ univ K' := by
  simpa using minimaxValueOn_eq_of_iSup_eq_left_univ hCol (univ : Set X')

/-- If two bifunctions have the same row-infimum function, they have the same whole-space Chapter
36 maximin value. -/
theorem maximinValue_eq_of_iInf_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x) :
    maximinValue K = maximinValue K' := by
  simpa [maximinValue] using maximinValueOn_univ_eq_of_iInf_eq hRow

/-- If two bifunctions have the same column-supremum function, they have the same whole-space
Chapter 36 minimax value. -/
theorem minimaxValue_eq_of_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    minimaxValue K = minimaxValue K' := by
  simpa [minimaxValue] using minimaxValueOn_univ_eq_of_iSup_eq hCol

/-- Row-infimum and column-supremum equality imply simultaneous Chapter 36 saddle-value existence
on `C × D`. -/
theorem hasSaddleValueOn_iff_of_iInf₂_iSup₂_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x)
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x) :
    HasSaddleValueOn C D K ↔ HasSaddleValueOn C D K' := by
  rw [HasSaddleValueOn, HasSaddleValueOn,
    maximinValueOn_eq_of_iInf₂_eq C D hRow,
    minimaxValueOn_eq_of_iSup₂_eq C D hCol]

/-- Row-infimum and column-supremum equality imply simultaneous Chapter 36 saddle-value existence
on `univ × univ`. -/
theorem hasSaddleValueOn_univ_iff_of_iInf_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    HasSaddleValueOn univ univ K ↔ HasSaddleValueOn univ univ K' := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using hasSaddleValueOn_iff_of_iInf₂_iSup₂_eq
    (univ : Set U') (univ : Set X') hRow' hCol'

/-- Row-infimum and column-supremum equality imply simultaneous whole-space Chapter 36
saddle-value existence. -/
theorem hasSaddleValue_iff_of_iInf_iSup_eq
    [SupSet β] [InfSet β]
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x) :
    HasSaddleValue K ↔ HasSaddleValue K' := by
  simpa [HasSaddleValue] using
    hasSaddleValueOn_univ_iff_of_iInf_iSup_eq hRow hCol

end

section

variable [CompleteLattice β]

/-- Equality of the row-infimum and column-supremum functions on `C × D` implies equality of the
source-order saddle-point predicates on `C × D`. -/
theorem isSaddlePointOn_iff_of_iInf₂_iSup₂_eq
    {K K' : U' → X' → β}
    (C : Set U') (D : Set X')
    (hRow : (fun u ↦ ⨅ x ∈ D, K u x) = fun u ↦ ⨅ x ∈ D, K' u x)
    (hCol : (fun x ↦ ⨆ u ∈ C, K u x) = fun x ↦ ⨆ u ∈ C, K' u x)
    {u : U'} (hu : u ∈ C) {x : X'} (hx : x ∈ D) :
    IsSaddlePointOn C D K u x ↔ IsSaddlePointOn C D K' u x := by
  have hRow_u : (⨅ v' ∈ D, K u v') = ⨅ v' ∈ D, K' u v' := by
    simpa using congrArg (fun F : U' → β ↦ F u) hRow
  have hCol_x : (⨆ u' ∈ C, K u' x) = ⨆ u' ∈ C, K' u' x := by
    simpa using congrArg (fun F : X' → β ↦ F x) hCol
  rw [isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value hu hx]
  rw [isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value hu hx]
  have transport {L M : U' → X' → β}
      (hRowLM : (⨅ v' ∈ D, L u v') = ⨅ v' ∈ D, M u v')
      (hColLM : (⨆ u' ∈ C, L u' x) = ⨆ u' ∈ C, M u' x) :
      ((⨅ v' ∈ D, L u v') = L u x ∧ (⨆ u' ∈ C, L u' x) = L u x) →
        ((⨅ v' ∈ D, M u v') = M u x ∧ (⨆ u' ∈ C, M u' x) = M u x) := by
    intro hL
    have hEq : (⨅ v' ∈ D, M u v') = ⨆ u' ∈ C, M u' x := by
      calc
        (⨅ v' ∈ D, M u v') = ⨅ v' ∈ D, L u v' := hRowLM.symm
        _ = L u x := hL.1
        _ = ⨆ u' ∈ C, L u' x := hL.2.symm
        _ = ⨆ u' ∈ C, M u' x := hColLM
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · exact iInf₂_le x hx
      · calc
          M u x ≤ ⨆ u' ∈ C, M u' x := le_iSup₂_of_le u hu le_rfl
          _ = ⨅ v' ∈ D, M u v' := hEq.symm
    · apply le_antisymm
      · calc
          ⨆ u' ∈ C, M u' x = ⨅ v' ∈ D, M u v' := hEq.symm
          _ ≤ M u x := iInf₂_le x hx
      · exact le_iSup₂_of_le u hu le_rfl
  constructor
  · simpa using transport hRow_u hCol_x
  · simpa using transport hRow_u.symm hCol_x.symm

/-- Equality of the row-infimum and column-supremum functions implies equality of the source-order
saddle-point predicates on `univ × univ`. -/
theorem isSaddlePointOn_iff_of_iInf_iSup_eq
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x)
    {u : U'} {x : X'} :
    IsSaddlePointOn univ univ K u x ↔
      IsSaddlePointOn univ univ K' u x := by
  have hRow' :
      (fun u ↦ ⨅ x ∈ (univ : Set X'), K u x) =
        fun u ↦ ⨅ x ∈ (univ : Set X'), K' u x := by
    funext u
    calc
      (⨅ x ∈ (univ : Set X'), K u x) = ⨅ x, K u x := by simp
      _ = ⨅ x, K' u x := by
        simpa using congrArg (fun F : U' → β ↦ F u) hRow
      _ = (⨅ x ∈ (univ : Set X'), K' u x) := by simp
  have hCol' :
      (fun x ↦ ⨆ u ∈ (univ : Set U'), K u x) =
        fun x ↦ ⨆ u ∈ (univ : Set U'), K' u x := by
    funext x
    calc
      (⨆ u ∈ (univ : Set U'), K u x) = ⨆ u, K u x := by simp
      _ = ⨆ u, K' u x := by
        simpa using congrArg (fun F : X' → β ↦ F x) hCol
      _ = (⨆ u ∈ (univ : Set U'), K' u x) := by simp
  simpa using isSaddlePointOn_iff_of_iInf₂_iSup₂_eq
    (univ : Set U') (univ : Set X') hRow' hCol' (u := u) (x := x) (by simp) (by simp)

/-- Equality of the row-infimum and column-supremum functions implies equality of the source-order
saddle-point owners on the whole space. -/
theorem isSaddlePoint_iff_of_iInf_iSup_eq
    {K K' : U' → X' → β}
    (hRow : (fun u ↦ ⨅ x, K u x) = fun u ↦ ⨅ x, K' u x)
    (hCol : (fun x ↦ ⨆ u, K u x) = fun x ↦ ⨆ u, K' u x)
    {u : U'} {x : X'} :
    IsSaddlePoint K u x ↔ IsSaddlePoint K' u x := by
  simpa [IsSaddlePoint] using
    isSaddlePointOn_iff_of_iInf_iSup_eq hRow hCol

end
end CodomainGeneric

section EquivalentBridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜] [NoBotOrder 𝕜]

/-- Equivalent saddle-functions have the same Chapter 36 maximin value on `C × univ`. -/
theorem maximinValueOn_eq_of_equivalent_right_univ
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (C : Set U) :
    maximinValueOn C univ K = maximinValueOn C univ K' := by
  exact maximinValueOn_eq_of_iInf_eq_right_univ (iInf_eq_iInf_of_equivalent hKK') C

/-- Equivalent saddle-functions have the same Chapter 36 minimax value on `univ × D`. -/
theorem minimaxValueOn_eq_of_equivalent_left_univ
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') (D : Set X) :
    minimaxValueOn univ D K = minimaxValueOn univ D K' := by
  exact minimaxValueOn_eq_of_iSup_eq_left_univ (iSup_eq_iSup_of_equivalent hKK') D

/-- Equivalent saddle-functions have the same whole-space Chapter 36 maximin value. -/
theorem maximinValue_eq_of_equivalent {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    maximinValue K = maximinValue K' := by
  exact maximinValue_eq_of_iInf_eq (iInf_eq_iInf_of_equivalent hKK')

/-- Equivalent saddle-functions have the same whole-space Chapter 36 minimax value. -/
theorem minimaxValue_eq_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    minimaxValue K = minimaxValue K' := by
  exact minimaxValue_eq_of_iSup_eq (iSup_eq_iSup_of_equivalent hKK')

/-- Equivalent saddle-functions have a saddle value simultaneously on the whole space. -/
theorem hasSaddleValue_iff_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') :
    HasSaddleValue K ↔ HasSaddleValue K' := by
  exact hasSaddleValue_iff_of_iInf_iSup_eq
    (iInf_eq_iInf_of_equivalent hKK')
    (iSup_eq_iSup_of_equivalent hKK')

/-- Theorem 36.4, saddle-point clause: equivalent saddle-functions have exactly the same
source-order saddle-points on the whole space. -/
theorem isSaddlePoint_iff_of_equivalent
    [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
    {K K' : U → X → WithTopBot 𝕜} (hKK' : K ∼ K') {u : U} {x : X} :
    IsSaddlePoint K u x ↔ IsSaddlePoint K' u x := by
  exact isSaddlePoint_iff_of_iInf_iSup_eq
    (iInf_eq_iInf_of_equivalent hKK')
    (iSup_eq_iSup_of_equivalent hKK')

end EquivalentBridge

end Minimax

end Bifunction
