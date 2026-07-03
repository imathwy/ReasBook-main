import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_36_1_1 (from Chap07) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.1.1 is the pointwise attainment characterization of a saddle
  point of a kernel `K(u, v)`, with maximization in the first variable and minimization in the
  second.
- `core/canonical`: the owner abstraction remains the Chapter 6 source-ordered predicate
  `Bifunction.IsSaddlePointOn C D K u v`.
- `bridge/view`: this file should add the intrinsic attained-`sInf`/`sSup` characterization and a
  bounded-`iInf`/`iSup` bridge surface for downstream Chapter 36 files; the swapped canonical
  owner stays available definitionally through
  `_root_.IsSaddlePointOn D C (Function.swap K) v u`, so no extra public wrapper is needed here.

Domain-style sampling used here:
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_isMaxOn_isMinOn` from `Chap06.Definition_6_28_7`;
- `IsMaxOn` / `IsMinOn` from `Mathlib.Order.Filter.Extr`;
- the intrinsic `sInf` / `sSup` set owners for attained slice values;
- the complete-lattice bounded `iSup` / `iInf` bridge syntax.

Primitive data vs derived API:
- primitive data: the sets `C`, `D`, the kernel `K`, and the candidate pair `(u, v)`;
- primitive owner: `Bifunction.IsSaddlePointOn C D K u v`;
- derived API: the attained-slice equalities at intrinsic set-owner level
  `sInf ((fun v' ↦ K u v') '' D) = K u v` and `sSup ((fun u' ↦ K u' v) '' C) = K u v`,
  together with the bounded-`iInf`/`iSup` bridge surface.

Layer target: `source-facing`.
-/

universe u v w

section

variable {U : Type u} {V : Type v} {γ : Type w}

/- Definition 36.1.1 uses the source-order owner from Chapter 6. -/
recall Bifunction.IsSaddlePointOn

namespace Bifunction

-- Proof sketch: pass first through the Chapter 6 owner theorem
-- `Bifunction.isSaddlePointOn_iff_isMaxOn_isMinOn`, then identify the attained extrema via the
-- intrinsic set-level `sInf`/`sSup` owners on the corresponding slices.
/-- If `u ∈ C` and `v ∈ D`, then a source-order saddle point has common value equal to the
attained set infimum of `K u ·` on `D` and the attained set supremum of `K · v` on `C`. -/
theorem isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value
    [ConditionallyCompleteLattice γ] [OrderBot γ] [OrderTop γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      sInf (K u '' D) = K u v ∧
      sSup ((fun u' ↦ K u' v) '' C) = K u v := by
  rw [isSaddlePointOn_iff_isMaxOn_isMinOn hu hv]
  constructor
  · rintro ⟨huMax, hvMin⟩
    rw [isMaxOn_iff] at huMax
    rw [isMinOn_iff] at hvMin
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · exact csInf_le (OrderBot.bddBelow (K u '' D)) ⟨v, hv, rfl⟩
      · refine le_csInf ?_ ?_
        · exact ⟨K u v, ⟨v, hv, rfl⟩⟩
        intro y hy
        rcases hy with ⟨v', hv', rfl⟩
        exact hvMin v' hv'
    · apply le_antisymm
      · refine csSup_le ?_ ?_
        · exact ⟨K u v, ⟨u, hu, rfl⟩⟩
        · intro y hy
          rcases hy with ⟨u', hu', rfl⟩
          exact huMax u' hu'
      · exact le_csSup (OrderTop.bddAbove ((fun u' ↦ K u' v) '' C)) ⟨u, hu, rfl⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rw [isMaxOn_iff]
      intro u' hu'
      calc
        K u' v ≤ sSup ((fun u'' ↦ K u'' v) '' C) := by
          exact le_csSup (OrderTop.bddAbove ((fun u'' ↦ K u'' v) '' C)) ⟨u', hu', rfl⟩
        _ = K u v := h.2
    · rw [isMinOn_iff]
      intro v' hv'
      calc
        K u v = sInf (K u '' D) := h.1.symm
        _ ≤ K u v' := by
          exact csInf_le (OrderBot.bddBelow (K u '' D)) ⟨v', hv', rfl⟩

/-- A source-order saddle point realizes the intrinsic attained infimum of the `u`-slice on `D`. -/
theorem IsSaddlePointOn.sInf_image_eq
    [ConditionallyCompleteLattice γ] [OrderBot γ] [OrderTop γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    sInf (K u '' D) = K u v :=
  ((isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value
      (C := C) (D := D) (K := K) hu hv).1 h).1

/-- A source-order saddle point realizes the intrinsic attained supremum of the `v`-slice on `C`. -/
theorem IsSaddlePointOn.sSup_image_eq
    [ConditionallyCompleteLattice γ] [OrderBot γ] [OrderTop γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    sSup ((fun u' ↦ K u' v) '' C) = K u v :=
  ((isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value
      (C := C) (D := D) (K := K) hu hv).1 h).2

/-- Constructor at intrinsic slice-owner level. -/
theorem isSaddlePointOn_of_sInf_image_eq_of_sSup_image_eq
    [ConditionallyCompleteLattice γ] [OrderBot γ] [OrderTop γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D)
    (hInf : sInf (K u '' D) = K u v)
    (hSup : sSup ((fun u' ↦ K u' v) '' C) = K u v) :
    IsSaddlePointOn C D K u v :=
  (isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value
      (C := C) (D := D) (K := K) hu hv).2 ⟨hInf, hSup⟩

/-- Bridge from the intrinsic set-level slice characterization to bounded `iInf`/`iSup` syntax. -/
theorem iInf_eq_sInf_image_and_iSup_eq_sSup_image
    [CompleteLattice γ] {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} :
    (⨅ v' ∈ D, K u v') = sInf (K u '' D) ∧
      (⨆ u' ∈ C, K u' v) = sSup ((fun u' ↦ K u' v) '' C) := by
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨v', hv', rfl⟩
      exact iInf₂_le v' hv'
    · refine le_iInf₂ ?_
      intro v' hv'
      exact sInf_le ⟨v', hv', rfl⟩
  · apply le_antisymm
    · refine iSup₂_le ?_
      intro u' hu'
      exact le_sSup ⟨u', hu', rfl⟩
    · refine sSup_le ?_
      intro y hy
      rcases hy with ⟨u', hu', rfl⟩
      exact le_iSup₂_of_le u' hu' le_rfl

/-- If `u ∈ C` and `v ∈ D`, then a source-order saddle point has common value equal to the
attained infimum of `K u ·` on `D` and the attained supremum of `K · v` on `C`. -/
theorem isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value [CompleteLattice γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      (⨅ v' ∈ D, K u v') = K u v ∧
      (⨆ u' ∈ C, K u' v) = K u v := by
  rcases iInf_eq_sInf_image_and_iSup_eq_sSup_image (C := C) (D := D) (K := K) (u := u) (v := v)
    with ⟨hInf, hSup⟩
  constructor
  · intro h
    have hset :=
      (isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value (C := C) (D := D)
        (K := K) hu hv).1 h
    refine ⟨?_, ?_⟩
    · calc
        (⨅ v' ∈ D, K u v') = sInf (K u '' D) := hInf
        _ = K u v := hset.1
    · calc
        (⨆ u' ∈ C, K u' v) = sSup ((fun u' ↦ K u' v) '' C) := hSup
        _ = K u v := hset.2
  · intro h
    have hset :
        sInf (K u '' D) = K u v ∧
          sSup ((fun u' ↦ K u' v) '' C) = K u v := by
      refine ⟨?_, ?_⟩
      · calc
          sInf (K u '' D) = (⨅ v' ∈ D, K u v') := hInf.symm
          _ = K u v := h.1
      · calc
          sSup ((fun u' ↦ K u' v) '' C) = (⨆ u' ∈ C, K u' v) := hSup.symm
          _ = K u v := h.2
    exact
      (isSaddlePointOn_iff_sInf_image_eq_value_and_sSup_image_eq_value (C := C) (D := D)
        (K := K) hu hv).2 hset

/-- A source-order saddle point realizes the bounded `iInf` value of the `u`-slice on `D`. -/
theorem IsSaddlePointOn.iInf_eq
    [CompleteLattice γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    (⨅ v' ∈ D, K u v') = K u v :=
  ((isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value
      (C := C) (D := D) (K := K) hu hv).1 h).1

/-- A source-order saddle point realizes the bounded `iSup` value of the `v`-slice on `C`. -/
theorem IsSaddlePointOn.iSup_eq
    [CompleteLattice γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} {v : V} (h : IsSaddlePointOn C D K u v)
    (hu : u ∈ C) (hv : v ∈ D) :
    (⨆ u' ∈ C, K u' v) = K u v :=
  ((isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value
      (C := C) (D := D) (K := K) hu hv).1 h).2

/-- Constructor at bounded `iInf`/`iSup` slice-owner level. -/
theorem isSaddlePointOn_of_iInf_eq_of_iSup_eq
    [CompleteLattice γ]
    {C : Set U} {D : Set V} {K : U → V → γ}
    {u : U} (hu : u ∈ C) {v : V} (hv : v ∈ D)
    (hInf : (⨅ v' ∈ D, K u v') = K u v)
    (hSup : (⨆ u' ∈ C, K u' v) = K u v) :
    IsSaddlePointOn C D K u v :=
  (isSaddlePointOn_iff_iInf_eq_value_and_iSup_eq_value
      (C := C) (D := D) (K := K) hu hv).2 ⟨hInf, hSup⟩

end Bifunction

end

/-! ### Lemma_36_1 (from Chap07) -/
universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w}
variable [CompleteLattice β]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 36.1 is the basic minimax inequality
  `sup_{u ∈ C} inf_{v ∈ D} K(u, v) ≤ inf_{v ∈ D} sup_{u ∈ C} K(u, v)`.
- `core/canonical`: the Chapter 36 owner theorem is
  `Bifunction.maximin_le_minimax_on`, stated directly in terms of the canonical complete-lattice
  owners `maximinValueOn` and `minimaxValueOn`.
- `bridge/view`: this file contributes no additional mathematics beyond recalling that owner
  theorem, so the correct public surface is direct reuse rather than a parallel local theorem
  shell.

Primary mathematical domain:
- minimax inequalities for complete-lattice-valued bifunctions.

Domain-style sampling used here:
- `Bifunction.maximinValueOn` from `Definition_36_0_1`;
- `Bifunction.minimaxValueOn` from `Definition_36_0_1`;
- `Bifunction.maximin_le_minimax_on` from `Definition_36_0_1`;
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7` as the nearby owner abstraction
  governing the Chapter 36 saddle-value API.

Primitive data vs derived API:
- primitive data: the sets `C`, `D`, and the bifunction `K`;
- primitive owner layer: the Chapter 36 value operators `maximinValueOn` and `minimaxValueOn`;
- derived API: the minimax inequality itself.

Layer target: `bridge/view`. This item is a recall-only bridge to the canonical Chapter 36 owner.
-/

/- Lemma 36.1: for a bifunction on a product set, the maximin value
`sup_{u ∈ C} inf_{v ∈ D} K(u, v)` is bounded above by the minimax value
`inf_{v ∈ D} sup_{u ∈ C} K(u, v)`. The source's nonemptiness assumption is redundant once this is
expressed through the Chapter 36 complete-lattice owners. -/
recall Bifunction.maximin_le_minimax_on
    (C : Set E) (D : Set F) (K : E → F → β) :
    Bifunction.maximinValueOn C D K ≤ Bifunction.minimaxValueOn C D K

end
