import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_9
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable {β : Type*} [Preorder β]

/-!
Source/core/bridge triage:

- `source-facing`: in the constrained-minimum reformulation used in Section 27, one compares the
  epigraph `epi h` with the auxiliary set `C₂ C α`. The source
  content at this stage is the level-feasibility reading of that comparison.
- `core/canonical`: the owner abstractions are the Chapter 1 epigraph owner `epi h` and the
  Chapter 6 auxiliary-set owner `C₂ C α`; no separate public `C₁` wrapper is mathematically
  needed.
- `bridge/view`: intersecting these two owners is equivalent to asking for a feasible point
  `x ∈ C` with value in the finite-level closed-sublevel owner
  `h ⁻¹' Set.Iic (α : WithTopBot β)`.
- Primitive data vs derived API: the primitive data are the function `h`, the constraint set `C`,
  and the level `α`; the intersection-membership and nonemptiness reformulations are derived API.
Domain-style sampling used here:
- `epi` / `mem_epi_iff`;
- `C₂` / `mem_C₂_iff`;
- preimage-sublevel owner `h ⁻¹' Set.Iic (α : WithTopBot β)`;
- `Set.mem_inter_iff` and `Set.Nonempty`.
- Layer target: `bridge/view`, stated directly on the existing owner objects instead of
  introducing a parallel local name for the first set.
-/

/-- Definition 6.27.11, canonical owner form: `epi h` meets `C₂ C α` exactly when the finite-level
sublevel owner `C ∩ h ⁻¹' Set.Iic (α : WithTopBot β)` is nonempty. -/
theorem inter_epi_C₂_nonempty_iff_nonempty_inter_preimage_Iic
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      (C ∩ h ⁻¹' Set.Iic (α : WithTopBot β)).Nonempty := by
  constructor
  · rintro ⟨⟨x, μ⟩, hxμ⟩
    simp only [Set.mem_inter_iff, mem_epi_iff, mem_C₂_iff] at hxμ
    rcases hxμ with ⟨hx_epi, hxC, hμα⟩
    have hμα' : (μ : WithTopBot β) ≤ (α : WithTopBot β) := by
      simpa using hμα
    refine ⟨x, hxC, ?_⟩
    change h x ∈ Set.Iic (α : WithTopBot β)
    exact Set.mem_Iic.mpr (hx_epi.trans hμα')
  · rintro ⟨x, hxC, hxIic⟩
    refine ⟨(x, α), ?_⟩
    refine ⟨?_, ?_⟩
    · exact (mem_epi_iff).2 (Set.mem_Iic.mp hxIic)
    · exact (mem_C₂_iff).2 ⟨hxC, le_rfl⟩

/-- Definition 6.27.11, set-builder companion: `epi h ∩ C₂ C α` is nonempty exactly when the
finite-level sublevel set `C ∩ {x | h x ≤ α}` is nonempty. -/
theorem inter_epi_C₂_nonempty_iff_nonempty_inter_sublevel
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      (C ∩ {x | h x ≤ α}).Nonempty := by
  simpa [Set.mem_preimage, Set.mem_Iic] using
    (inter_epi_C₂_nonempty_iff_nonempty_inter_preimage_Iic (h := h) (C := C) (α := α))

/-- Definition 6.27.11, source-reading companion: `epi h ∩ C₂ C α` is nonempty exactly when
there exists `x ∈ C` with `h x ≤ α`. -/
theorem inter_epi_C₂_nonempty_iff
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      ∃ x ∈ C, h x ≤ α := by
  simpa [Set.Nonempty, Set.mem_inter_iff] using
    (inter_epi_C₂_nonempty_iff_nonempty_inter_sublevel (h := h) (C := C) (α := α))

end
