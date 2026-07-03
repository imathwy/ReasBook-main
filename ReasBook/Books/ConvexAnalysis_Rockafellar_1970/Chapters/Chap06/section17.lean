import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_17 (from Chap02) -/
section

open Topology
open scoped Rockafellar

variable {𝕜 V P : Type*}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [TopologicalSpace P] [AddTorsor V P]

/- 
Source/core/bridge triage:
- `source-facing`: Text 6.17 states that taking closure twice or taking relative interior twice
  does not change a subset of an affine space; the textbook `ℝ^n` wording is a specialization.
- `core/canonical`: the owner abstractions are mathlib's `intrinsicClosure` /
  `intrinsicInterior` for relative topology; ambient `closure` is a textbook bridge surface.
- `bridge/view`: the chapter source-facing predicate `IsRelativelyOpen` gives the natural bridge
  form of clause (2), derived from the owner equality
  `ri[𝕜](ri[𝕜](C)) = ri[𝕜](C)`.
- Domain-style sampling: the relevant owner declarations inspected here are
  `intrinsicClosure_idem`, `closure_closure`, `intrinsicInterior`, `IsOpen.isRelativelyOpen`,
  `AffineSubspace.map_span`, and `Topology.IsEmbedding.toHomeomorph`.
- Primitive data vs derived API: there is no new primitive data here; clause (1) is exact owner
  recall (`intrinsicClosure_idem`) with an ambient companion (`closure_closure`), clause (2) is
  an owner theorem `intrinsicInterior_idem`, with notation surface `ri_idem`,
  and `isRelativelyOpen_ri` is the thin source-facing bridge.
- Layer target: clause (1) is primary `core/canonical` on intrinsic closure with an ambient
  closure companion retained; clause (2) is `core/canonical`, and
  `isRelativelyOpen_ri` is its `bridge/view` companion.
-/

/- Text 6.17 (1), intrinsic/relative-topology owner form: taking intrinsic closure twice does not
change a subset of an affine space. -/
recall intrinsicClosure_idem

/- Text 6.17 (1): taking closure twice does not change a subset of `ℝ^n`; this is exactly the
canonical owner theorem `closure_closure`. -/
recall closure_closure

namespace AffineSubspace

/-- Owner bridge: intrinsic interior commutes with coercing a subset of an affine subspace to the
ambient affine space. -/
private lemma image_intrinsicInterior_subtype (A : AffineSubspace 𝕜 P) [Nonempty A] (s : Set A) :
    ri[𝕜](A.subtype '' s) = A.subtype '' ri[𝕜](s) := by
  change ri[𝕜](((↑) : A → P) '' s) = ((↑) : A → P) '' ri[𝕜](s)
  let S : AffineSubspace 𝕜 A := affineSpan 𝕜 s
  let g : S → P := ((↑) : A → P) ∘ ((↑) : S → A)
  have hEmb : IsEmbedding g := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hrange : Set.range g = (affineSpan 𝕜 (((↑) : A → P) '' s) : Set P) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : (y : A) ∈ S := y.2
      have : (y : P) ∈ AffineSubspace.map A.subtype S :=
        AffineSubspace.mem_map_of_mem A.subtype hy
      simpa [g, S, AffineSubspace.map_span] using this
    · intro hx
      have hx' : x ∈ AffineSubspace.map A.subtype S := by
        simpa [S, AffineSubspace.map_span] using hx
      rcases AffineSubspace.mem_map.1 hx' with ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : S ≃ₜ affineSpan 𝕜 (((↑) : A → P) '' s) :=
    hEmb.toHomeomorph.trans <| Homeomorph.setCongr hrange
  have hsubtype : g ∘ e.symm = ((↑) : affineSpan 𝕜 (((↑) : A → P) '' s) → P) := by
    ext x
    exact congrArg Subtype.val <|
      hEmb.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange).symm x)
  rw [intrinsicInterior, intrinsicInterior, ← hsubtype, Set.image_comp, e.symm.image_interior,
    e.image_symm]
  have hpre : e ⁻¹' (g ∘ e.symm ⁻¹' (((↑) : A → P) '' s)) = (((↑) : S → A) ⁻¹' s) := by
    ext x
    simp [Set.preimage_comp, g]
  rw [hpre]
  simpa [g] using
    (Set.image_comp A.subtype ((↑) : S → A) (interior (((↑) : S → A) ⁻¹' s)))

end AffineSubspace

/-- Text 6.17 (2), canonical owner form: intrinsic interior is idempotent on subsets of an affine
space. The textbook `ℝ^n` statement is the specialization `𝕜 = ℝ`. -/
@[simp] theorem intrinsicInterior_idem (C : Set P) :
    intrinsicInterior 𝕜 (intrinsicInterior 𝕜 C) = intrinsicInterior 𝕜 C := by
  obtain hri_empty | hri_nonempty := Set.eq_empty_or_nonempty (ri[𝕜](C))
  · simp [hri_empty]
  let A : AffineSubspace 𝕜 P := affineSpan 𝕜 C
  let U : Set A := interior (((↑) : A → P) ⁻¹' C)
  have hU : U.Nonempty := by
    simpa [A, U, intrinsicInterior] using hri_nonempty
  letI : Nonempty A := ⟨hU.some⟩
  have hri : ri[𝕜](C) = ((↑) : A → P) '' U := by
    simp [A, U, intrinsicInterior]
  have hU_ri : ri[𝕜](U) = U := by
    exact (isOpen_interior : IsOpen U).isRelativelyOpen
  calc
    ri[𝕜](ri[𝕜](C)) =
        ri[𝕜](((↑) : A → P) '' U) := by
      rw [hri]
    _ = ((↑) : A → P) '' ri[𝕜](U) := by
      simpa using (AffineSubspace.image_intrinsicInterior_subtype (A := A) (s := U))
    _ = ((↑) : A → P) '' U := by
      rw [hU_ri]
    _ = ri[𝕜](C) := hri.symm

/-- Text 6.17 (2), source-facing notation form: relative interior is idempotent. -/
@[simp] theorem ri_idem (C : Set P) :
    ri[𝕜](ri[𝕜](C)) = ri[𝕜](C) := by
  simp [intrinsicInterior_idem]

/-- The intrinsic interior of a subset of an affine space is relatively open in the sense of
`IsRelativelyOpen`. This is the source-facing bridge behind Text 6.17 (2). -/
theorem isRelativelyOpen_ri (C : Set P) :
    IsRelativelyOpen 𝕜 (ri[𝕜](C)) := by
  simp [IsRelativelyOpen, intrinsicInterior_idem]

end
