

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_36_2_1 (from Chap07) -/
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

/-! ### Lemma_36_2 (from Chap07) -/
universe u v w

section

variable {U : Type u} {V : Type v} {γ : Type w}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 36.2 is the source-order saddle-point attainment criterion on `C × D`:
  for `u ∈ C` and `v ∈ D`, the `v`-column supremum on `C` is the Chapter 36 maximin value and
  the `u`-row infimum on `D` is the Chapter 36 minimax value.
- `core/canonical`: the owner abstractions are Chapter 6's source-order saddle predicate
  `Bifunction.IsSaddlePointOn` and the Chapter 36 value operators from `Definition_36_0_1`.
- `bridge/view`: this file records the bridge from a source-order saddle point to the Chapter 36
  owner values. The pointwise slice-attainment theorem already exists upstream in
  `Definition_36_1_1`, so it should be reused rather than duplicated locally.

Domain-style sampling used here:
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value` from
  `Chap07.Definition_36_1_1`;
- `Bifunction.iInf_eq_sInf_image_and_iSup_eq_sSup_image` from `Chap07.Definition_36_1_1`;
- `Bifunction.maximinValueOn_eq_of_isSaddlePointOn` from `Chap07.Definition_36_0_1`;
- `Bifunction.minimaxValueOn_eq_of_isSaddlePointOn` from `Chap07.Definition_36_0_1`.

Primitive data vs derived API:
- primitive data: the sets `C`, `D`, the bifunction `K`, and the candidate pair `(u, v)`;
- primitive owner: `Bifunction.IsSaddlePointOn C D K u v`;
- derived bridge API: the owner-attainment equalities
  `maximinValueOn C D K = ⨆ u' ∈ C, K u' v` and
  `minimaxValueOn C D K = ⨅ v' ∈ D, K u v'`.

Layer target: `bridge/view`, with the bounded `iInf`/`iSup` value-owner surface as the primary API
and the intrinsic set-image `sInf`/`sSup` surface as a derived bridge.
-/

/-- Lemma 36.2 at the Chapter 36 value-owner layer: if `u ∈ C` and `v ∈ D`, then `(u, v)` is a
source-order saddle point on `C × D` exactly when the `v`-column bounded `iSup` on `C` is the
Chapter 36 maximin owner and the `u`-row bounded `iInf` on `D` is the Chapter 36 minimax owner. -/
theorem isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      maximinValueOn C D K = ⨆ u' ∈ C, K u' v ∧
      minimaxValueOn C D K = ⨅ v' ∈ D, K u v' := by
  constructor
  · intro h
    have hSlice :=
      (isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value
        (C := C) (D := D) (K := K) hu hv).1 h
    refine ⟨?_, ?_⟩
    · calc
        maximinValueOn C D K = K u v :=
          maximinValueOn_eq_of_isSaddlePointOn hu hv h
        _ = ⨆ u' ∈ C, K u' v := hSlice.2.symm
    · calc
        minimaxValueOn C D K = K u v :=
          minimaxValueOn_eq_of_isSaddlePointOn hu hv h
        _ = ⨅ v' ∈ D, K u v' := hSlice.1.symm
  · intro hValue
    have hCol_le_row : (⨆ u' ∈ C, K u' v) ≤ ⨅ v' ∈ D, K u v' := by
      calc
        (⨆ u' ∈ C, K u' v) = maximinValueOn C D K := hValue.1.symm
        _ ≤ minimaxValueOn C D K := maximin_le_minimax_on C D K
        _ = (⨅ v' ∈ D, K u v') := hValue.2
    have hValue_le_col : K u v ≤ ⨆ u' ∈ C, K u' v :=
      le_iSup₂_of_le u hu le_rfl
    have hRow_le_value : (⨅ v' ∈ D, K u v') ≤ K u v :=
      iInf₂_le v hv
    have hCol_eq_value : (⨆ u' ∈ C, K u' v) = K u v := by
      refine le_antisymm ?_ hValue_le_col
      exact le_trans hCol_le_row hRow_le_value
    have hRow_eq_value : (⨅ v' ∈ D, K u v') = K u v := by
      refine le_antisymm hRow_le_value ?_
      exact le_trans hValue_le_col hCol_le_row
    exact
      (isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value
        (C := C) (D := D) (K := K) hu hv).2 ⟨hRow_eq_value, hCol_eq_value⟩

/-- Lemma 36.2 rewritten through intrinsic set-image owners: if `u ∈ C` and `v ∈ D`, then
`(u, v)` is a source-order saddle point on `C × D` exactly when the intrinsic `v`-column supremum
owner on `C` is the Chapter 36 maximin value and the intrinsic `u`-row infimum owner on `D` is
the Chapter 36 minimax value. -/
theorem isSaddlePointOn_iff_maximinValueOn_eq_sSup_image_and_minimaxValueOn_eq_sInf_image
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      maximinValueOn C D K = sSup ((fun u' ↦ K u' v) '' C) ∧
      minimaxValueOn C D K = sInf (K u '' D) := by
  rcases iInf_eq_sInf_image_and_iSup_eq_sSup_image (C := C) (D := D) (K := K) (u := u) (v := v)
    with ⟨hInf, hSup⟩
  constructor
  · intro h
    have hValue :=
      (isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
        (C := C) (D := D) (K := K) hu hv).1 h
    refine ⟨?_, ?_⟩
    · calc
        maximinValueOn C D K = ⨆ u' ∈ C, K u' v := hValue.1
        _ = sSup ((fun u' ↦ K u' v) '' C) := hSup
    · calc
        minimaxValueOn C D K = ⨅ v' ∈ D, K u v' := hValue.2
        _ = sInf (K u '' D) := hInf
  · intro h
    refine
      (isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
        (C := C) (D := D) (K := K) hu hv).2 ?_
    refine ⟨?_, ?_⟩
    · calc
        maximinValueOn C D K = sSup ((fun u' ↦ K u' v) '' C) := h.1
        _ = ⨆ u' ∈ C, K u' v := hSup.symm
    · calc
        minimaxValueOn C D K = sInf (K u '' D) := h.2
        _ = ⨅ v' ∈ D, K u v' := hInf.symm

/-- A source-order saddle-point realizes the Chapter 36 maximin owner as the intrinsic
`v`-column supremum on `C`. -/
theorem IsSaddlePointOn.maximinValueOn_eq_sSup_image
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    maximinValueOn C D K = sSup ((fun u' ↦ K u' v) '' C) :=
  (isSaddlePointOn_iff_maximinValueOn_eq_sSup_image_and_minimaxValueOn_eq_sInf_image
      (C := C) (D := D) (K := K) hu hv).1 h |>.1

/-- A source-order saddle-point realizes the Chapter 36 minimax owner as the intrinsic
`u`-row infimum on `D`. -/
theorem IsSaddlePointOn.minimaxValueOn_eq_sInf_image
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    minimaxValueOn C D K = sInf (K u '' D) :=
  (isSaddlePointOn_iff_maximinValueOn_eq_sSup_image_and_minimaxValueOn_eq_sInf_image
      (C := C) (D := D) (K := K) hu hv).1 h |>.2

/-- Lemma 36.2: if `u ∈ C` and `v ∈ D`, then `(u, v)` is a source-order saddle point on `C × D`
exactly when the `v`-column supremum on `C` is the Chapter 36 maximin value and the `u`-row
infimum on `D` is the Chapter 36 minimax value. Expanding these owners yields the usual reverse
minimax inequality `⨆ u' ∈ C, K u' v ≤ ⨅ v' ∈ D, K u v'`. -/
theorem isSaddlePointOn_iff_values_eq_iSup₂_and_iInf₂
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      maximinValueOn C D K = ⨆ u' ∈ C, K u' v ∧
      minimaxValueOn C D K = ⨅ v' ∈ D, K u v' :=
  isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
    (C := C) (D := D) (K := K) hu hv

/-- A source-order saddle-point realizes the Chapter 36 maximin owner as the bounded
`iSup` of the `v`-column on `C`. -/
theorem IsSaddlePointOn.maximinValueOn_eq_iSup₂
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    maximinValueOn C D K = ⨆ u' ∈ C, K u' v :=
  (isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
      (C := C) (D := D) (K := K) hu hv).1 h |>.1

/-- A source-order saddle-point realizes the Chapter 36 minimax owner as the bounded
`iInf` of the `u`-row on `D`. -/
theorem IsSaddlePointOn.minimaxValueOn_eq_iInf₂
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    minimaxValueOn C D K = ⨅ v' ∈ D, K u v' :=
  (isSaddlePointOn_iff_maximinValueOn_eq_iSup₂_and_minimaxValueOn_eq_iInf₂
      (C := C) (D := D) (K := K) hu hv).1 h |>.2

end Bifunction

end
