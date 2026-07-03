

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_32_1_1 (from Chap06) -/
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

/-! ### Theorem_32_1 (from Chap06) -/
section

open AffineMap
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 32.1 is the maximum principle for a convex function on a set:
  if the maximum is attained at a point of `ri[𝕜](C)`, then the function is constant on `C`.
- `core/canonical`: the primitive owner input in the proof is the segment-prolongation datum
  `∀ x ∈ C, ∃ μ > 1, lineMap x z μ ∈ C`, together with `ConvexOn`, `IsMaxOn`, and
  finite value at `z`.
- `bridge/view`: membership `z ∈ ri[𝕜](C)` is used only as the canonical bridge that supplies the
  primitive prolongation datum via Theorem 6.4.

Domain-style sampling used here:
- `ConvexOn` and `ConvexOn.convex_epigraph`;
- `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior` from
  `Chap02/Theorem_6_4`;
- `AffineMap.lineMap`, `lineMap_apply_module`, and `lineMap_lineMap_right`;
- `IsMaxOn` as the canonical owner for attainment of a supremum on a set.

Primitive data vs derived API:
- primitive inputs: the convex function `f`, the set `C`, a maximizing finite point
  `z ∈ dom(f)` with `IsMaxOn f C z`, and the segment-prolongation datum at `z`;
- derived API: pointwise constancy `f x = f z` for `x ∈ C`, and the setwise `EqOn` reformulation
  of the same source conclusion; the `ri[𝕜](C)` form is a source-facing bridge.

Layer target: `core/canonical` + `source-facing` bridge. The primitive theorem is stated at the
owner level that the proof actually uses; the textbook `ri[𝕜](C)` statement is a thin wrapper.
-/

namespace ConvexOn

section Core

variable {𝕜 E α : Type*}
variable [DivisionRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedCancelAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulStrictMono 𝕜 (WithTopBot α)]

variable {f : E → WithTopBot α}

/-- Primitive owner form of Theorem 32.1: if a convex function attains its supremum on `C` at a
finite point `z`, and every segment from `x ∈ C` to `z` can be prolonged past `z` while staying
in `C`, then the function has value `f z` at every `x ∈ C`. -/
theorem eq_of_isMaxOn_of_lineMapProlongable
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    {z x : E}
    (hprolong : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C)
    (_hzdom : z ∈ dom(f)) (hzmax : IsMaxOn f C z) (hx : x ∈ C) :
    f x = f z := by
  by_cases hxeq : f x = f z
  · exact hxeq
  · rcases hprolong x hx with ⟨μ, hμ, hyC⟩
    let y := lineMap x z μ
    let t : 𝕜 := μ⁻¹
    have ht : t ∈ Set.Ioo (0 : 𝕜) 1 := by
      constructor
      · exact inv_pos.mpr (lt_trans zero_lt_one hμ)
      · rw [inv_lt_one₀]
        · exact hμ
        · exact lt_trans zero_lt_one hμ
    have hμ0 : μ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hμ)
    have hz_lineMap : lineMap x y t = z := by
      simp [y, t, hμ0]
    have hxf : f x < f z := lt_of_le_of_ne (hzmax hx) hxeq
    have hyz : f y ≤ f z := by
      simpa [y] using hzmax hyC
    have hz_combo : (1 - t) • x + t • y = z := by
      simpa [lineMap_apply_module] using hz_lineMap
    have hpair : f z ≤ (1 - t) • f x + t • f z := by
      have hp : (x, f x) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} := ⟨hx, le_rfl⟩
      have hq : (y, f z) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} := ⟨hyC, hyz⟩
      have hmem :
          (1 - t) • (x, f x) + t • (y, f z) ∈
            {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} :=
        hf.convex_epigraph hp hq (sub_nonneg.mpr ht.2.le) ht.1.le (by simp)
      simpa [hz_combo] using hmem.2
    have h1t : 0 < 1 - t := sub_pos.mpr ht.2
    have hstrict : (1 - t) • f x + t • f z < f z := by
      calc
        (1 - t) • f x + t • f z < (1 - t) • f z + t • f z := by
          exact add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hxf h1t) le_rfl
        _ = ((1 - t) + t) • f z := by
          simpa [add_smul] using (add_smul (1 - t) t (f z)).symm
        _ = (1 : 𝕜) • f z := by
          congr 1
          simp
        _ = f z := by simp
    have : f z < f z := lt_of_le_of_lt hpair hstrict
    exact (lt_irrefl _ this).elim

/-- Setwise primitive owner form of
`eq_of_isMaxOn_of_lineMapProlongable`. -/
theorem eqOn_of_isMaxOn_of_lineMapProlongable
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    {z : E}
    (hprolong : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C)
    (hzdom : z ∈ dom(f)) (hzmax : IsMaxOn f C z) :
    Set.EqOn f (fun _ ↦ f z) C := by
  intro x hx
  exact hf.eq_of_isMaxOn_of_lineMapProlongable hprolong hzdom hzmax hx

end Core

section Source

variable {𝕜 E α : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedCancelAddMonoid (WithTopBot α)]
variable [Module 𝕜 (WithTopBot α)] [PosSMulStrictMono 𝕜 (WithTopBot α)]

variable {f : E → WithTopBot α}

/-- Theorem 32.1: if a convex function attains its supremum on a set `C` at some point
`z ∈ ri[𝕜](C)` where `f z < ⊤`, then it has the same value at every point of `C`. -/
theorem eq_of_isMaxOn_of_mem_ri
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    {z x : E} (hz : z ∈ ri[𝕜](C)) (hzdom : z ∈ dom(f)) (hzmax : IsMaxOn f C z) (hx : x ∈ C) :
    f x = f z := by
  have hzline : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C :=
    Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hz
  exact hf.eq_of_isMaxOn_of_lineMapProlongable hzline hzdom hzmax hx

/-- Theorem 32.1, setwise form: under the same hypotheses, the convex function is constant on
`C`. -/
theorem eqOn_of_isMaxOn_of_mem_ri
    {C : Set E} (hf : ConvexOn 𝕜 C f)
    {z : E} (hz : z ∈ ri[𝕜](C)) (hzdom : z ∈ dom(f)) (hzmax : IsMaxOn f C z) :
    Set.EqOn f (fun _ ↦ f z) C := by
  have hzline : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C :=
    Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hz
  exact hf.eqOn_of_isMaxOn_of_lineMapProlongable hzline hzdom hzmax

end Source

end ConvexOn

end
