import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Topology

variable {V : Type*} {P : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Definition 10.1.5 introduces the local property of a subset of an affine
  space being covered near each of its points by finitely many simplices lying inside the set.
- `core/canonical`: subsets `s : Set P`, relative neighborhoods `𝓝[s] x`, finite simplex families
  represented canonically as finite sets
  `T : Set (Σ m : ℕ, Affine.Simplex k P m)` with witness `T.Finite`; each simplex carrier is
  `t.2.closedInterior`.
- `bridge/view`: `Finset` and open-neighborhood formulations are bridge API.
- Primitive data vs derived API: the primitive data are the finite simplex family and the
  relative-neighborhood witness that the simplex union covers `s` near each point.
- Domain-style sampling: the relevant owner-level declarations are
  `Affine.Simplex.closedInterior`, `𝓝[s] x`, and `Set.exists_finite_iff_finset`.
-/

/-- Definition 10.1.5: a subset of an affine space is locally simplicial if each point admits a
relative neighborhood in the set covered by finitely many simplices lying inside the set. The
owner-level finite-family witness is the intrinsic finite-set layer `Set` + `Finite`. -/
def Set.IsLocallySimplicial (k : Type*) [Ring k] [PartialOrder k]
    [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace P] (s : Set P) : Prop :=
  ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
    (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
      (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x

variable {k : Type*} [Ring k] [PartialOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [TopologicalSpace P]

/-- Relative-neighborhood + finite-`Set` formulation of local simpliciality. -/
theorem Set.isLocallySimplicial_iff_exists {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  Iff.rfl

/-- Deprecated alias for `Set.isLocallySimplicial_iff_exists`. -/
@[deprecated Set.isLocallySimplicial_iff_exists (since := "2026-05-17")]
theorem Set.isLocallySimplicial_iff_exists_finite {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  Set.isLocallySimplicial_iff_exists

/-- `Finset` bridge formulation of `Set.IsLocallySimplicial`. -/
theorem Set.isLocallySimplicial_iff_exists_finset {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x := by
  simp [Set.IsLocallySimplicial, Set.exists_finite_iff_finset]

/-- Open-set + finite-`Finset` bridge formulation of `Set.IsLocallySimplicial` using
relative-neighborhood witnesses. -/
theorem Set.isLocallySimplicial_iff_exists_open_finset {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  constructor
  · intro hs x hx
    rcases (Set.isLocallySimplicial_iff_exists_finset.1 hs) x hx with ⟨T, hTsubset, hcov⟩
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hcov with ⟨u, hu_nhds, hu_sub⟩
    rcases mem_nhds_iff.1 hu_nhds with ⟨v, hv_sub, hv_open, hxv⟩
    refine ⟨v, hv_open, hxv, T, hTsubset, ?_⟩
    intro y hy
    exact hu_sub ⟨hv_sub hy.1, hy.2⟩
  · intro hs
    refine (Set.isLocallySimplicial_iff_exists_finset).2 ?_
    intro x hx
    rcases hs x hx with ⟨u, hu_open, hxu, T, hTsubset, hu_sub⟩
    refine ⟨T, hTsubset, ?_⟩
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨u, hu_open.mem_nhds hxu, hu_sub⟩

/-- Open-set + finite-`Set` bridge formulation of local simpliciality. -/
theorem Set.isLocallySimplicial_iff_exists_open {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  constructor
  · intro hs x hx
    rcases (Set.isLocallySimplicial_iff_exists_open_finset.1 hs) x hx with
      ⟨u, hu_open, hxu, T, hTsubset, hu_sub⟩
    refine ⟨u, hu_open, hxu, (T : Set (Σ m : ℕ, Affine.Simplex k P m)), T.finite_toSet, ?_, ?_⟩
    · intro t ht
      exact hTsubset t (Finset.mem_coe.1 ht)
    · simpa using hu_sub
  · intro hs
    refine (Set.isLocallySimplicial_iff_exists_open_finset).2 ?_
    intro x hx
    rcases hs x hx with ⟨u, hu_open, hxu, T, hTfin, hTsubset, hu_sub⟩
    refine ⟨u, hu_open, hxu, hTfin.toFinset, ?_, ?_⟩
    · intro t ht
      exact hTsubset t (hTfin.mem_toFinset.1 ht)
    · simpa [hTfin.coe_toFinset] using hu_sub

/-- Deprecated alias for `Set.isLocallySimplicial_iff_exists_open`. -/
@[deprecated Set.isLocallySimplicial_iff_exists_open (since := "2026-05-17")]
theorem Set.isLocallySimplicial_iff_exists_open_finite {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior :=
  Set.isLocallySimplicial_iff_exists_open

namespace Set.IsLocallySimplicial

/-- A locally simplicial set admits a finite-family simplicial description in the relative
neighborhood filter near each point. -/
theorem exists_finset {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  (Set.isLocallySimplicial_iff_exists_finset.1 hs) x hx

/-- A locally simplicial set admits a finite-`Set` simplicial description in the relative
neighborhood filter near each point. -/
theorem exists_set {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  hs x hx

/-- Deprecated alias for `Set.IsLocallySimplicial.exists_set`. -/
@[deprecated Set.IsLocallySimplicial.exists_set (since := "2026-05-17")]
theorem exists_finite {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  exists_set hs hx

/-- A locally simplicial set admits an open-neighborhood finite-family simplicial description. -/
theorem exists_open_finset {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact (Set.isLocallySimplicial_iff_exists_open_finset.1 hs) x hx

/-- A locally simplicial set admits an open-neighborhood finite-`Set` simplicial description. -/
theorem exists_open {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact (Set.isLocallySimplicial_iff_exists_open.1 hs) x hx

/-- Deprecated alias for `Set.IsLocallySimplicial.exists_open`. -/
@[deprecated Set.IsLocallySimplicial.exists_open (since := "2026-05-17")]
theorem exists_open_finite {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact exists_open hs hx

end Set.IsLocallySimplicial

end
