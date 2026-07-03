import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_4 (from Chap01) -/
noncomputable section

open Affine
open AffineSubspace

section

variable {𝕜 : Type*} {V : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.4 says that the dimension of a convex set is the maximum of the
  dimensions of the simplices contained in it.
- `core/canonical`: the owner abstractions are the chapter set-dimension bridge `Set.affineDim`
  and the bundled simplex owner `Affine.Simplex`.
- `bridge/view`: the textbook "maximum" statement is expressed canonically as:
  1. an upper-bound theorem for any simplex contained in `C`, and
  2. an existence theorem producing a simplex whose dimension realizes `dim[𝕜](C)` when `C` is
     nonempty, together with the empty-set edge case `dim[𝕜](C) = -1`.
- Domain-style sampling: `Set.affineDim`, `Affine.Simplex`,
  `convexHull`, `exists_affineIndependent`, and
  `AffineIndependent.iff_range_affineDim_eq_of_card_eq`.
- Primitive data vs derived API: the primitive data are the set `C` and the simplex owner
  `Affine.Simplex`; the maximal-dimension conclusion is derived API and should not be repackaged
  as a second public structure.
- Layer target: `source-facing`, stated directly with the chapter owner notions.
-/

section Core

variable {P : Type*}
variable [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
open scoped Rockafellar

namespace Affine.Simplex

/-- Core owner layer: if all simplex vertices lie in `C`, then the simplex dimension is bounded
by the affine dimension of `C`. -/
theorem affineDim_le_of_points_subset {C : Set P} {n : ℕ} (s : Affine.Simplex 𝕜 P n)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hsC : Set.range s.points ⊆ C) :
    (n : ℤ) ≤ dim[𝕜](C) := by
  let simplexSpan := affineSpan 𝕜 (Set.range s.points)
  have hle : simplexSpan ≤ affineSpan 𝕜 C := affineSpan_mono 𝕜 hsC
  have hdim : simplexSpan.affineDim = n := by
    simpa [simplexSpan, Set.affineDim] using s.affineDim_range_points_eq (𝕜 := 𝕜)
  have hsbot : simplexSpan ≠ ⊥ := by
    intro hsbot
    have hmem : s.points 0 ∈ simplexSpan :=
      subset_affineSpan 𝕜 (Set.range s.points) (Set.mem_range_self (0 : Fin (n + 1)))
    rw [hsbot] at hmem
    simpa using hmem
  have hCbot : affineSpan 𝕜 C ≠ ⊥ := by
    intro hCbot
    have hmem : s.points 0 ∈ affineSpan 𝕜 C :=
      hle (subset_affineSpan 𝕜 (Set.range s.points) (Set.mem_range_self (0 : Fin (n + 1))))
    rw [hCbot] at hmem
    simpa using hmem
  rw [Set.affineDim, ← hdim, AffineSubspace.affineDim, if_neg hsbot,
    AffineSubspace.affineDim, if_neg hCbot]
  change (Module.finrank 𝕜 simplexSpan.direction : ℤ) ≤
      Module.finrank 𝕜 (affineSpan 𝕜 C).direction
  exact_mod_cast Submodule.finrank_mono (AffineSubspace.direction_le hle)

end Affine.Simplex

/-- Core owner layer: any nonempty set contains a simplex with vertices in the set whose
dimension realizes the affine dimension of the set. -/
theorem Set.exists_simplex_points_subset_affineDim_eq (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hCne : C.Nonempty) :
    ∃ n : ℕ, dim[𝕜](C) = n ∧
      ∃ s : Affine.Simplex 𝕜 P n, Set.range s.points ⊆ C := by
  obtain ⟨t, htC, htspan, htind⟩ := exists_affineIndependent 𝕜 V C
  have htne : t.Nonempty := by
    by_contra htn
    have htempty : t = ∅ := Set.not_nonempty_iff_eq_empty.mp htn
    have hx : hCne.some ∈ (affineSpan 𝕜 C : Set P) := subset_affineSpan 𝕜 C hCne.some_mem
    rw [← htspan, htempty] at hx
    simp at hx
  letI : Nonempty (affineSpan 𝕜 C) := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨⟨x, subset_affineSpan 𝕜 C hx⟩⟩
  let pointsInSpan : t → affineSpan 𝕜 C := fun x ↦
    ⟨x, by
      rw [← htspan]
      exact subset_affineSpan 𝕜 t x.property⟩
  have htind' : AffineIndependent 𝕜 pointsInSpan := by
    exact AffineIndependent.of_comp (AffineSubspace.subtype (affineSpan 𝕜 C))
      (by simpa [pointsInSpan] using htind)
  have htfin : Set.Finite t := finite_set_of_fin_dim_affineIndependent 𝕜 htind'
  letI := htfin.fintype
  let n : ℕ := Fintype.card t - 1
  have hcard : Fintype.card t = n + 1 := by
    have htcard_pos : 0 < Fintype.card t := Fintype.card_pos_iff.mpr htne.to_subtype
    dsimp [n]
    exact (Nat.succ_pred_eq_of_pos htcard_pos).symm
  let e : Fin (n + 1) ≃ t := hcard ▸ (Fintype.equivFin t).symm
  let s : Affine.Simplex 𝕜 P n := ⟨fun i ↦ (e i : P), (affineIndependent_equiv e).2 htind⟩
  have hsrange : Set.range s.points = t := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      simp [s]
  refine ⟨n, ?_, s, ?_⟩
  · have hsaff : affineSpan 𝕜 (Set.range s.points) = affineSpan 𝕜 C := by
      rw [hsrange, htspan]
    have hsdim : AffineSubspace.affineDim (affineSpan 𝕜 (Set.range s.points)) = n := by
      simpa [Set.affineDim] using s.affineDim_range_points_eq (𝕜 := 𝕜)
    simpa [Set.affineDim, hsaff] using hsdim
  · simpa [hsrange] using htC

/-- Core owner layer, including the empty-set edge case: every set either has affine dimension
`-1`, or contains a simplex whose vertex range realizes its affine dimension. -/
theorem Set.affineDim_eq_neg_one_or_exists_simplex_points_subset (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] :
    dim[𝕜](C) = -1 ∨
      ∃ n : ℕ, dim[𝕜](C) = n ∧
        ∃ s : Affine.Simplex 𝕜 P n, Set.range s.points ⊆ C := by
  by_cases hCne : C.Nonempty
  · right
    exact C.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hCne
  · left
    have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst C
    rw [Set.affineDim]
    simp [AffineSubspace.affineDim]

end Core

section ConvexHullBridge

variable [DivisionRing 𝕜] [PartialOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]
open scoped Rockafellar

namespace Affine.Simplex

/-- Bridge owner surface: any simplex whose convex hull is contained in a set has dimension at
most the affine dimension of that set. -/
theorem affineDim_le_of_convexHull_subset {C : Set V} {n : ℕ} (s : Affine.Simplex 𝕜 V n)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hsC : convexHull 𝕜 (Set.range s.points) ⊆ C) :
    (n : ℤ) ≤ dim[𝕜](C) := by
  exact s.affineDim_le_of_points_subset ((subset_convexHull 𝕜 (Set.range s.points)).trans hsC)

end Affine.Simplex

namespace Convex

/-- Bridge surface for Theorem 2.4 (nonempty case): a nonempty convex set contains a simplex whose
vertex convex hull is contained in the set and whose dimension equals the affine dimension of the
set. The intrinsic simplex-set owner statement uses `s.closedInterior ⊆ C` below. -/
-- Proof sketch: choose an affinely independent subset `t ⊆ C` whose affine span is `affineSpan 𝕜 C`
-- using `exists_affineIndependent`. The intrinsic hypothesis
-- `[FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]` makes `t` finite after viewing it inside the
-- affine subspace `affineSpan 𝕜 C`. Reindex `t` by `Fin (n + 1)` to obtain a bundled simplex `s`;
-- the convex hull of the vertices is contained in `C` by convexity, and the chapter bridge
-- `Text 1.9` identifies its dimension with `n = dim[𝕜](C)`.
theorem exists_simplex_convexHull_subset_affineDim_eq {C : Set V}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hC : Convex 𝕜 C)
    (hCne : C.Nonempty) :
    ∃ n : ℕ, dim[𝕜](C) = n ∧
      ∃ s : Affine.Simplex 𝕜 V n, convexHull 𝕜 (Set.range s.points) ⊆ C := by
  rcases C.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hCne with
    ⟨n, hCdim, s, hsC⟩
  exact ⟨n, hCdim, s, convexHull_min hsC hC⟩

/-- Bridge surface for Theorem 2.4 with the empty-set edge case:
either a convex set has affine dimension `-1`, or it contains a simplex whose convex-hull
presentation realizes that affine dimension. The intrinsic simplex-set owner statement uses
`s.closedInterior ⊆ C` below. -/
theorem affineDim_eq_neg_one_or_exists_simplex_convexHull_subset {C : Set V}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hC : Convex 𝕜 C) :
    dim[𝕜](C) = -1 ∨
      ∃ n : ℕ, dim[𝕜](C) = n ∧
        ∃ s : Affine.Simplex 𝕜 V n, convexHull 𝕜 (Set.range s.points) ⊆ C := by
  rcases C.affineDim_eq_neg_one_or_exists_simplex_points_subset (𝕜 := 𝕜) with
    hdim | ⟨n, hCdim, s, hsC⟩
  · exact Or.inl hdim
  · exact Or.inr ⟨n, hCdim, s, convexHull_min hsC hC⟩

end Convex

end ConvexHullBridge

section Ordered

variable [DivisionRing 𝕜] [PartialOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]
open scoped Rockafellar

namespace Affine.Simplex

/-- Intrinsic simplex-set owner bridge: if the canonical simplex set `s.closedInterior` is
contained in `C`, then the simplex dimension is bounded by the affine dimension of `C`. -/
theorem affineDim_le_of_closedInterior_subset {C : Set V} {n : ℕ} (s : Affine.Simplex 𝕜 V n)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] [ZeroLEOneClass 𝕜]
    (hsC : s.closedInterior ⊆ C) :
    (n : ℤ) ≤ dim[𝕜](C) := by
  refine s.affineDim_le_of_points_subset ?_
  rintro _ ⟨i, rfl⟩
  exact hsC (s.point_mem_closedInterior i)

end Affine.Simplex

end Ordered

section OrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
open scoped Rockafellar

namespace Convex

/-- Theorem 2.4, nonempty case, on the intrinsic simplex-set owner layer:
a nonempty convex set contains a simplex whose canonical simplex set `s.closedInterior` is
contained in the set and whose dimension equals the affine dimension of the set. -/
theorem exists_simplex_closedInterior_subset_affineDim_eq {C : Set V}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hC : Convex 𝕜 C)
    (hCne : C.Nonempty) :
    ∃ n : ℕ, dim[𝕜](C) = n ∧
      ∃ s : Affine.Simplex 𝕜 V n, s.closedInterior ⊆ C := by
  rcases Convex.exists_simplex_convexHull_subset_affineDim_eq
      (𝕜 := 𝕜) (C := C) hC hCne with
    ⟨n, hCdim, s, hsC⟩
  exact ⟨n, hCdim, s, by simpa [s.convexHull_eq_closedInterior] using hsC⟩

/-- Theorem 2.4 with the empty-set edge case on the intrinsic simplex-set owner layer:
either a convex set has affine dimension `-1`, or it contains a simplex whose
`s.closedInterior`-presentation realizes that affine dimension. -/
theorem affineDim_eq_neg_one_or_exists_simplex_closedInterior_subset {C : Set V}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hC : Convex 𝕜 C) :
    dim[𝕜](C) = -1 ∨
      ∃ n : ℕ, dim[𝕜](C) = n ∧
        ∃ s : Affine.Simplex 𝕜 V n, s.closedInterior ⊆ C := by
  rcases Convex.affineDim_eq_neg_one_or_exists_simplex_convexHull_subset
      (𝕜 := 𝕜) (C := C) hC with
    hdim | ⟨n, hCdim, s, hsC⟩
  · exact Or.inl hdim
  · exact Or.inr ⟨n, hCdim, s, by simpa [s.convexHull_eq_closedInterior] using hsC⟩

end Convex

end OrderedField

end

/-! ### Definition_2_4_10 (from Chap01) -/
noncomputable section

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.4.10 names the affine dimension of a set as the
  affine dimension of its affine hull.
- `core/canonical`: the owner abstractions are the affine hull `affineSpan` of a set together
  with the chapter owner notion `AffineSubspace.affineDim` from `AffineDimension`.
- `bridge/view`: the set-level declaration `Set.affineDim` below is the thin composite sending a
  set to the affine dimension of its affine hull. This bridge is intrinsically affine and
  finite-dimensional on the affine-span direction, so it is owned on an arbitrary affine space
  with the needed local finite-dimensional hypothesis.
- Domain-style sampling: the relevant owner declarations are the project owner
  `AffineSubspace.affineDim` from `AffineDimension`, mathlib's `affineSpan`, and the downstream
  bridge pattern from Definition 4.5, where function dimension is read directly as
  `Set.affineDim (dom(f))` rather than through a parallel packaged notion.
- Primitive data vs derived API: the affine hull is primitive; the dimension of a set is derived
  from it and should not be packaged into a separate wrapper structure.
- Layer target: `bridge/view`, preserving the source-facing set-level notion while reusing the
  affine-subspace owner abstraction directly.
-/

namespace Set

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
variable (𝕜)

/-- Definition 2.4.10 as the set-level owner on the intrinsic affine-subspace layer: the affine
dimension of a set whose affine span is finite-dimensional is the affine dimension of its
affine hull. -/
def affineDim (C : Set P) [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] : ℤ :=
  (affineSpan 𝕜 C).affineDim

end Set

/-- Rockafellar-style set-dimension notation over a scalar division ring. -/
scoped[Rockafellar] notation "dim[" 𝕜 "](" C ")" => Set.affineDim 𝕜 C

namespace Set

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open scoped Rockafellar

@[simp] theorem dim_eq_affineSpan_affineDim (C : Set P)
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] :
    dim[𝕜](C) = (affineSpan 𝕜 C).affineDim := rfl

end Set

/-! ### Proposition_2_4_11 (from Chap01) -/
noncomputable section

open AffineSubspace
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.4.11 says that a convex disk has dimension `2`. Source-faithfully,
  the primitive data are a set `C` contained in a plane `s` together with relative openness in the
  subspace topology on `s` and nonemptiness.
- `core/canonical`: the owner declarations are `AffineSubspace.affineDim` and
  `AffineSubspace.is_plane` from Theorem 1.3, with `Module.finrank` on the direction submodule as
  the primitive owner data behind affine dimension.
- `bridge/view`: the canonical bridge first identifies `affineSpan 𝕜 C = s`; the source-facing
  dimension statement is then recovered from the chapter owner `AffineSubspace.is_plane`. The
  intrinsic relative-topology owner is first stated as a theorem for `D : Set s`, and the ambient
  `C ⊆ s` form is recovered as a thin corollary.
- Domain-style sampling: `AffineSubspace.affineDim`, `AffineSubspace.is_plane`, `Set.affineDim`,
  `IsOpen.affineSpan_eq_top`, and `AffineSubspace.map_span`.
- Primitive data vs derived API: intrinsic relative data (`D : Set s`, open/nonempty in `s`) are
  the primitive bridge hypotheses for obtaining the affine-span identity; for the dimension
  conclusion, the primitive owner data are `s.is_plane` together with `affineSpan 𝕜 C = s`. The
  ambient hypotheses (`C ⊆ s` plus relative openness) are a source-facing view recovered by
  pullback along `Subtype.val`. The source `ℝⁿ` statement is recovered by specialization, while the
  public proposition itself stays on the intrinsic set-dimension owner `Set.affineDim` from
  Definition 2.4.10.
- Layer target: the numbered proposition stays `source-facing`, with the affine-span equality kept
  as `bridge/view`.
-/

namespace Set

section AffineDimBridge

variable {𝕜 V P : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-- Primitive affine-dimension owner bridge: if `C` has affine hull exactly the plane `s`, then
`C` has affine dimension `2`. -/
theorem affineDim_eq_two_of_isPlane_of_affineSpan_eq {C : Set P} {s : AffineSubspace 𝕜 P}
    [FiniteDimensional 𝕜 s.direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hs : s.is_plane) (hspan : affineSpan 𝕜 C = s) :
    dim[𝕜](C) = 2 := by
  simpa [Set.affineDim, hspan] using hs

end AffineDimBridge

section TopologicalBridge

variable {𝕜 V P : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- Companion bridge for Proposition 2.4.11: a nonempty subset of an affine subspace that is open
in the subspace topology has that affine subspace as its affine hull. This is the intrinsic
relative-topology owner layer, written directly for subsets `D : Set s`. -/
theorem affineSpan_eq_top_of_isOpen_subtype {s : AffineSubspace 𝕜 P} [Nonempty s] {D : Set s}
    (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) :
    affineSpan 𝕜 D = ⊤ := by
  exact hD_open.affineSpan_eq_top_of_nontriviallyNormedField hD_nonempty

/-- Companion bridge for Proposition 2.4.11 in ambient `P`, obtained by mapping the intrinsic
subtype theorem along `s.subtype`. -/
theorem affineSpan_image_subtype_eq_of_isOpen {s : AffineSubspace 𝕜 P} {D : Set s}
    (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) :
    affineSpan 𝕜 (Subtype.val '' D : Set P) = s := by
  rcases hD_nonempty with ⟨x, hx⟩
  let _ : Nonempty s := ⟨x⟩
  have hD_top : affineSpan 𝕜 D = ⊤ :=
    affineSpan_eq_top_of_isOpen_subtype (s := s) (D := D) hD_open ⟨x, hx⟩
  calc
    affineSpan 𝕜 (Subtype.val '' D : Set P) = AffineSubspace.map s.subtype (affineSpan 𝕜 D) := by
      simpa using (AffineSubspace.map_span s.subtype D).symm
    _ = AffineSubspace.map s.subtype (⊤ : AffineSubspace 𝕜 s) := by rw [hD_top]
    _ = s := by
      ext y
      simp [AffineSubspace.mem_map]

/-- Companion bridge for Proposition 2.4.11 in source-facing ambient form: a nonempty subset of an
affine subspace that is open in the subspace topology has that affine subspace as its affine
hull. -/
theorem affineSpan_eq_of_subset_affineSubspace_of_isOpen_preimage {C : Set P}
    {s : AffineSubspace 𝕜 P} (hCsub : C ⊆ s)
    (hC_open : IsOpen (Subtype.val ⁻¹' C : Set s)) (hC_nonempty : C.Nonempty) :
    affineSpan 𝕜 C = s := by
  let D : Set s := (Subtype.val ⁻¹' C : Set s)
  have hD_nonempty : D.Nonempty := by
    rcases hC_nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hCsub hx⟩, hx⟩
  have himage : (Subtype.val '' D : Set P) = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hCsub hx⟩, hx, rfl⟩
  calc
    affineSpan 𝕜 C = affineSpan 𝕜 (Subtype.val '' D : Set P) := by rw [himage.symm]
    _ = s := affineSpan_image_subtype_eq_of_isOpen (s := s) (D := D) hC_open hD_nonempty

/-- Proposition 2.4.11 on the intrinsic relative-topology owner layer: if `D : Set s` is nonempty
and open in the subspace topology of a plane `s`, then `(s.subtype '' D)` has affine dimension
`2`. -/
theorem affineDim_image_subtype_eq_two_of_isPlane_of_isOpen {s : AffineSubspace 𝕜 P} {D : Set s}
    [FiniteDimensional 𝕜 s.direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (Subtype.val '' D : Set P)).direction]
    (hs : s.is_plane) (hD_open : IsOpen D) (hD_nonempty : D.Nonempty) :
    dim[𝕜]((Subtype.val '' D : Set P)) = 2 := by
  have hspan : affineSpan 𝕜 (Subtype.val '' D : Set P) = s :=
    affineSpan_image_subtype_eq_of_isOpen (s := s) (D := D) hD_open hD_nonempty
  exact affineDim_eq_two_of_isPlane_of_affineSpan_eq
    (C := (Subtype.val '' D : Set P)) (s := s) hs hspan

/-- Proposition 2.4.11 in source-facing ambient form: a nonempty subset of a plane that is open in
the induced topology on that plane has set affine dimension `2`, written as `dim[𝕜](C) = 2`. -/
theorem affineDim_eq_two_of_subset_plane_of_isOpen_preimage
    {C : Set P} {s : AffineSubspace 𝕜 P} [FiniteDimensional 𝕜 s.direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction] (hs : s.is_plane)
    (hCsub : C ⊆ s) (hC_open : IsOpen (Subtype.val ⁻¹' C : Set s))
    (hC_nonempty : C.Nonempty) :
    dim[𝕜](C) = 2 := by
  have hspan : affineSpan 𝕜 C = s :=
    affineSpan_eq_of_subset_affineSubspace_of_isOpen_preimage
      (C := C) (s := s) hCsub hC_open hC_nonempty
  exact affineDim_eq_two_of_isPlane_of_affineSpan_eq (C := C) (s := s) hs hspan

end TopologicalBridge
end Set
