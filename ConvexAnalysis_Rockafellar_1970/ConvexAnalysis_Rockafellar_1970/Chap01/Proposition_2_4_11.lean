import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap01.TopologicalAffineSpan

-- Declarations for this item will be appended below by the statement pipeline.

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
