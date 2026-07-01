import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

universe u v w

open scoped Rockafellar

namespace Bifunction

section Extension

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.2.1 studies an extended-valued bifunction `Kbar` that agrees
  with a finite kernel `K` on `C × D`, equals `+∞` on `C × Dᶜ`, and equals `-∞` on `Cᶜ × D`.
- `core/canonical`: the chapter owners are `saddleExtension`, `maximinValue`, `minimaxValue`,
  `HasSaddleValue`, and `Bifunction.IsSaddlePoint`, together with the restricted-owner forms
  `maximinValueOn`, `minimaxValueOn`, `HasSaddleValueOn`, and `Bifunction.IsSaddlePointOn`.
- `bridge/view`: the proposition is best stated directly on those owners, with the extension data
  kept as pointwise hypotheses on `Kbar`.

Primary domain:
- minimax and saddle-point theory for restricted bifunctions and their ambient `±∞`-extensions.

Domain-style sampling used here:
- `Bifunction.saddleExtension` from `Definition33_0_2`;
- `Bifunction.maximinValueOn` from `Definition_36_0_1`;
- `Bifunction.minimaxValueOn` from `Definition_36_0_1`;
- `Bifunction.HasSaddleValueOn` from `Definition_36_0_1`;
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`.

Primitive data vs derived API:
- primitive data: the sets `C`, `D`, the finite kernel `K`, the extended kernel `Kbar`, and the
  three source boundary conditions on `Kbar`;
- derived API: the ambient/domain row-infimum and column-supremum identities, the induced
  maximin/minimax equalities, and the resulting saddle-value / saddle-point equivalences.

Layer target: `source-facing`, expressed directly through the canonical Chapter 36 owners rather
than through a second packaged extension object.
-/

variable {U : Type u} {V : Type v}
variable {C : Set U} {D : Set V}
variable {α : Type w}
variable {K : U → V → α} {Kbar : U → V → α}

/-- A saddle top/bottom extension on `C × D`: it agrees with `K` on `C × D`, takes value `⊤`
on `C × Dᶜ`, and takes value `⊥` on `Cᶜ × D`. No condition is imposed on `Cᶜ × Dᶜ`.
For Rockafellar's Proposition 36.2.1, instantiate this owner in `WithTopBot α`. -/
def IsSaddleExtensionOn
    [Top α] [Bot α]
    (Kbar : U → V → α) (K : U → V → α) (C : Set U) (D : Set V) : Prop :=
  (∀ ⦃u : U⦄ ⦃v : V⦄, u ∈ C → v ∈ D → Kbar u v = K u v) ∧
    (∀ ⦃u : U⦄ ⦃v : V⦄, u ∈ C → v ∉ D → Kbar u v = ⊤) ∧
      ∀ ⦃u : U⦄ ⦃v : V⦄, u ∉ C → v ∈ D → Kbar u v = ⊥

namespace IsSaddleExtensionOn

variable [Top α] [Bot α]

@[simp] theorem on_mem
    (hExt : IsSaddleExtensionOn Kbar K C D)
    {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    Kbar u v = K u v := by
  rcases hExt with ⟨hOn, _, _⟩
  exact hOn hu hv

@[simp] theorem top_of_mem_left_of_not_mem_right
    (hExt : IsSaddleExtensionOn Kbar K C D)
    {u : U} {v : V} (hu : u ∈ C) (hv : v ∉ D) :
    Kbar u v = ⊤ := by
  rcases hExt with ⟨_, hTop, _⟩
  exact hTop hu hv

@[simp] theorem bot_of_not_mem_left_of_mem_right
    (hExt : IsSaddleExtensionOn Kbar K C D)
    {u : U} {v : V} (hu : u ∉ C) (hv : v ∈ D) :
    Kbar u v = ⊥ := by
  rcases hExt with ⟨_, _, hBot⟩
  exact hBot hu hv

end IsSaddleExtensionOn

-- Proof sketch: unfold `saddleExtensionOn`; on `C × D`, `C × Dᶜ`, and `Cᶜ × D`, the defining
-- branches are exactly the three boundary cases appearing in `IsSaddleExtensionOn`.
/-- The intrinsic simple extension `saddleExtensionOn K C D` is a boundary extension in the sense
of Proposition 36.2.1. -/
theorem isSaddleExtensionOn_saddleExtensionOn
    [Top α] [Bot α] (K : U → V → α) (C : Set U) (D : Set V) :
    IsSaddleExtensionOn (saddleExtensionOn K C D) K C D := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    exact saddleExtensionOn_apply_of_mem (K := K) (C := C) (D := D) hu hv
  · intro u v hu hv
    exact saddleExtensionOn_apply_of_mem_left_of_not_mem_right
      (K := K) (C := C) (D := D) hu hv
  · intro u v hu hv
    exact saddleExtensionOn_apply_of_not_mem_left
      (K := K) (C := C) (D := D) hu

-- Proof sketch: instantiate the intrinsic owner theorem
-- `isSaddleExtensionOn_saddleExtensionOn` at `K := toWithTopBot K`.
/-- The canonical finite-kernel extension `K₁[K | C, D]` is a boundary extension in the sense
of Proposition 36.2.1. -/
theorem isSaddleExtensionOn_saddleExtension
    {β : Type w} (K : U → V → β) (C : Set U) (D : Set V) :
    IsSaddleExtensionOn K₁[K | C, D] (toWithTopBot K) C D := by
  simpa [saddleExtension] using
    (isSaddleExtensionOn_saddleExtensionOn (K := toWithTopBot K) (C := C) (D := D))

section Value

variable [CompleteLattice α]

-- Proof sketch: for `u ∈ C`, the row of `Kbar` agrees with `K` on `D` and is `⊤` on `V \ D`, so
-- adding the outside points does not change the infimum.
/-- For a boundary extension, a row indexed by a point of `C` has the same ambient infimum as the
`D`-restricted infimum of the original kernel. -/
theorem iInf_extension_eq_iInfOn_of_mem_left
    (hExt : IsSaddleExtensionOn Kbar K C D)
    {u : U} (hu : u ∈ C) :
    (⨅ v : V, Kbar u v) = ⨅ v ∈ D, K u v := sorry

-- Proof sketch: choose `v ∈ D`; by the boundary condition on `Cᶜ × D`, the corresponding row
-- value is `⊥`, forcing the whole ambient row infimum to be `⊥`.
/-- For a boundary extension, a row indexed by a point outside `C` has ambient infimum `⊥`,
provided `D` is nonempty. -/
theorem iInf_extension_eq_bot_of_not_mem_left
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hD : D.Nonempty) {u : U} (hu : u ∉ C) :
    (⨅ v : V, Kbar u v) = (⊥ : α) := sorry

-- Proof sketch: for `v ∈ D`, the column of `Kbar` agrees with `K` on `C` and is `⊥` on `U \ C`,
-- so adding the outside points does not change the supremum.
/-- For a boundary extension, a column indexed by a point of `D` has the same ambient
supremum as the `C`-restricted supremum of the original kernel. -/
theorem iSup_extension_eq_iSupOn_of_mem_right
    (hExt : IsSaddleExtensionOn Kbar K C D)
    {v : V} (hv : v ∈ D) :
    (⨆ u : U, Kbar u v) = ⨆ u ∈ C, K u v := sorry

-- Proof sketch: choose `u ∈ C`; by the boundary condition on `C × Dᶜ`, the corresponding column
-- value is `⊤`, forcing the whole ambient column supremum to be `⊤`.
/-- For a boundary extension, a column indexed by a point outside `D` has ambient supremum `⊤`,
provided `C` is nonempty. -/
theorem iSup_extension_eq_top_of_not_mem_right
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hC : C.Nonempty) {v : V} (hv : v ∉ D) :
    (⨆ u : U, Kbar u v) = (⊤ : α) := sorry

-- Proof sketch: rewrite the ambient maximin as a supremum of ambient row infima, then use the
-- preceding two row lemmas to replace the rows indexed by `C` with restricted rows and the rows
-- outside `C` with `⊥`, which do not affect the outer supremum.
/-- The ambient maximin value of a boundary extension equals the Chapter 36 maximin value of the
original kernel on `C × D`. -/
theorem maximinValue_eq_maximinValueOn_of_extension
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hD : D.Nonempty) :
    maximinValue Kbar = maximinValueOn C D K := sorry

-- Proof sketch: rewrite the ambient minimax as an infimum of ambient column suprema, then use the
-- preceding two column lemmas to replace the columns indexed by `D` with restricted columns and
-- the columns outside `D` with `⊤`, which do not affect the outer infimum.
/-- The ambient minimax value of a boundary extension equals the Chapter 36 minimax value of the
original kernel on `C × D`. -/
theorem minimaxValue_eq_minimaxValueOn_of_extension
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hC : C.Nonempty) :
    minimaxValue Kbar = minimaxValueOn C D K := sorry

-- Proof sketch: expand `HasSaddleValueOn` on both sides and rewrite the ambient maximin and
-- minimax values by the two preceding equality theorems.
/-- Proposition 36.2.1: a boundary extension has a saddle-value on the whole product exactly when
the original kernel has a saddle-value on `C × D`; the two saddle-values coincide via the
ambient/domain maximin and minimax identities above. -/
theorem hasSaddleValue_iff_of_extension
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hC : C.Nonempty) (hD : D.Nonempty) :
    HasSaddleValue Kbar ↔ HasSaddleValueOn C D K := by
  simpa [HasSaddleValue, HasSaddleValueOn] using
    (show maximinValue Kbar = minimaxValue Kbar ↔
        maximinValueOn C D K = minimaxValueOn C D K from by
      rw [maximinValue_eq_maximinValueOn_of_extension hExt hD,
        minimaxValue_eq_minimaxValueOn_of_extension hExt hC])

end Value

-- Proof sketch: first show that an ambient saddle-point must lie in `C × D`, since otherwise a
-- comparison with a point from the opposite nonempty domain would force `⊤ ≤ ⊥`, impossible in
-- `WithTopBot β`. Once the point lies in `C × D`, the saddle inequalities reduce to those of `K`
-- by the `C × D` agreement branch in `hExt`.
/-- Ambient saddle-points of a `WithTopBot` boundary extension are exactly the restricted
saddle-points of the source kernel on `C × D`, and any such ambient saddle-point necessarily lies
in `C × D`. -/
theorem isSaddlePoint_iff_of_saddleExtensionOn
    {β : Type w} [Preorder β]
    {K Kbar : U → V → WithTopBot β}
    (hExt : IsSaddleExtensionOn Kbar K C D)
    (hC : C.Nonempty) (hD : D.Nonempty) {u : U} {v : V} :
    IsSaddlePoint Kbar u v ↔
      u ∈ C ∧ v ∈ D ∧
        IsSaddlePointOn C D K u v := sorry

/-- Proposition 36.2.1 bridge form: when the source kernel is finite-valued, convert it by
`toWithTopBot` and apply `isSaddlePoint_iff_of_saddleExtensionOn`. -/
theorem isSaddlePoint_iff_of_extension
    {β : Type w} [Preorder β]
    {K : U → V → β} {Kbar : U → V → WithTopBot β}
    (hExt : IsSaddleExtensionOn Kbar (toWithTopBot K) C D)
    (hC : C.Nonempty) (hD : D.Nonempty) {u : U} {v : V} :
    IsSaddlePoint Kbar u v ↔
      u ∈ C ∧ v ∈ D ∧
        IsSaddlePointOn C D K u v := by
  have hLift :
      IsSaddlePointOn C D (toWithTopBot K) u v ↔ IsSaddlePointOn C D K u v := by
    rw [isSaddlePointOn_iff_forall, isSaddlePointOn_iff_forall]
    constructor
    · intro h u' hu v' hv'
      exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp (h u' hu v' hv'))
    · intro h u' hu v' hv'
      exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr (h u' hu v' hv'))
  constructor
  · intro hsp
    rcases (isSaddlePoint_iff_of_saddleExtensionOn (K := toWithTopBot K) (Kbar := Kbar)
        hExt hC hD).1 hsp with ⟨hu, hv, hspOn⟩
    exact ⟨hu, hv, hLift.mp hspOn⟩
  · rintro ⟨hu, hv, hspOn⟩
    exact (isSaddlePoint_iff_of_saddleExtensionOn (K := toWithTopBot K) (Kbar := Kbar)
      hExt hC hD).2 ⟨hu, hv, hLift.mpr hspOn⟩

end Extension

end Bifunction
