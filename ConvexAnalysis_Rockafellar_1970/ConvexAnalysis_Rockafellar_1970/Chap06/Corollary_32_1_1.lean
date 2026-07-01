import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_18_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_18_0_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Rockafellar

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {α : Type w}
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedCancelAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulStrictMono 𝕜 (WithTopBot α)]
variable {f : E → WithTopBot α}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.1.1 says that, for a convex function on a convex subset of its
  effective domain, the set of maximizers is a union of faces of that set.
- `core/canonical`: the owner abstractions are `ConvexOn`, `dom(f)`,
  the maximizer owner `Set.maximizers`, `Set.IsFace`, and the face decomposition theorem
  `sUnion_ri_nonempty_faces_eq`.
- `bridge/view`: the source set `W` is rendered directly as the canonical maximizer owner
  `C.maximizers f`; the “union of faces” conclusion is stated concretely as equality
  with the union of all faces of `C` on which every point is a maximizer.

Domain-style sampling used here:
- `ConvexOn.eqOn_of_isMaxOn_of_mem_ri`;
- `sUnion_ri_nonempty_faces_eq`;
- `Set.IsFace.subset`;
- `Set.maximizers` / `Set.mem_maximizers_iff`.

Primitive data vs derived API:
- primitive inputs: a setwise convex owner `ConvexOn 𝕜 C f` and the source hypothesis
  `C ⊆ dom(f)`;
- derived API: the source-facing maximizer owner `C.maximizers f` is exactly the
  union of the faces of `C` contained in that same slice.

Codomain-assumption minimality:
- this corollary introduces no codomain-side structure beyond what is already required by the
  upstream constancy owner `ConvexOn.eqOn_of_isMaxOn_of_mem_ri` (Theorem 32.1), applied
  on each face selected by the Chapter 18 decomposition.

Layer target: `source-facing`, stated directly on the canonical function/set/face owners rather
than through a local wrapper owner.
-/

namespace ConvexOn

/-- Corollary 32.1.1: if `f` is convex and `C` is a convex subset of `dom(f)`, then the set of
points of `C` at which `f` attains its supremum relative to `C` is the union of the faces of `C`
contained in that maximizer set. -/
-- Proof sketch: let `W := C.maximizers f`. The union on the right is contained in
-- `W` by definition. For `x ∈ W`, Theorem 18.2 gives a nonempty face `F` of `C` with
-- `x ∈ ri[𝕜](F)`. Since `C ⊆ dom(f)`, the point `x` lies in `dom(f)`, so Theorem 32.1 shows that
-- `f` is constant on `F`. Hence every point of `F` is again a maximizer on `C`, so `F` is one of
-- the faces in the displayed union and therefore `x` belongs to that union.
theorem maximizers_eq_sUnion_faces
    {C : Set E} (hf : ConvexOn 𝕜 C f) (hC_dom : C ⊆ dom(f)) :
    C.maximizers f = ⋃₀ {F : Set E | F ∈ 𝓕[𝕜](C) ∧ F ⊆ C.maximizers f} := by
  let W : Set E := C.maximizers f
  change W = ⋃₀ {F : Set E | F ∈ 𝓕[𝕜](C) ∧ F ⊆ W}
  refine Set.Subset.antisymm ?_ ?_
  · intro x hxW
    have hxW' : x ∈ C.maximizers f := by
      simpa [W] using hxW
    rcases Set.mem_maximizers_iff.mp hxW' with ⟨hxC, hxmax⟩
    have hxUnion : x ∈ ⋃₀ 𝒰[𝕜](C) := by
      rw [sUnion_ri_nonempty_faces_eq hf.1]
      exact hxC
    rcases Set.mem_sUnion.mp hxUnion with ⟨U, hU, hxU⟩
    have hU' : ∃ F : Set E, F.IsFace 𝕜 C ∧ F.Nonempty ∧ U = ri[𝕜](F) := by
      simpa using hU
    rcases hU' with ⟨F, hF_face, -, rfl⟩
    have hF_faces : F ∈ 𝓕[𝕜](C) := by simpa using hF_face
    have hxdom : x ∈ dom(f) := hC_dom hxC
    have hxmaxF : IsMaxOn f F x := fun y hyF ↦ hxmax (hF_face.subset hyF)
    have hconvF : ConvexOn 𝕜 F f := hf.subset hF_face.subset hF_face.convex
    have hEqOnF : Set.EqOn f (fun _ : E ↦ f x) F :=
      hconvF.eqOn_of_isMaxOn_of_mem_ri hxU hxdom hxmaxF
    have hF_subset_W : F ⊆ W := by
      intro y hyF
      have hymax : IsMaxOn f C y := by
        intro z hzC
        have hzle : f z ≤ f x := hxmax hzC
        have hyEq : f y = f x := hEqOnF hyF
        simpa [hyEq] using hzle
      have hyW : y ∈ C.maximizers f := by
        exact Set.mem_maximizers_iff.mpr ⟨hF_face.subset hyF, hymax⟩
      simpa [W] using hyW
    exact Set.mem_sUnion.mpr ⟨F, ⟨hF_faces, hF_subset_W⟩, intrinsicInterior_subset hxU⟩
  · intro x hxUnion
    rcases Set.mem_sUnion.mp hxUnion with ⟨F, hF, hxF⟩
    exact hF.2 hxF

end ConvexOn

end
