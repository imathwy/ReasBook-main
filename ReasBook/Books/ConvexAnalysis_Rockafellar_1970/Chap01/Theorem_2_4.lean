import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_9

-- Declarations for this item will be appended below by the statement pipeline.

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
