import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_1_1

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
