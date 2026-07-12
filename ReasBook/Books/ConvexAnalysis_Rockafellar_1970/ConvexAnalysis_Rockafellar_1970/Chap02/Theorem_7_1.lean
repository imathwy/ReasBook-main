import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} [TopologicalSpace E]
variable {α : Type v} [LinearOrder α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 7.1 gives three equivalent ways to express lower semicontinuity for an
  extended-codomain function: lower semicontinuity itself, closedness of every scalar sublevel
  set, and closedness of the scalar epigraph.
- `core/canonical`: the chapter owner for scalar epigraphs is `epi`, and the scalar-threshold
  characterization is the direct specialization of
  `lowerSemicontinuous_iff_isClosed_preimage`.
- `bridge/view`: the textbook `EReal`/`ℝ` surface is the specialization `α = ℝ` of the canonical
  `WithTopBot α` codomain layer used throughout the chapter.

Domain-style sampling used here:
- `LowerSemicontinuous`;
- `lowerSemicontinuous_iff_isClosed_preimage`;
- `lowerSemicontinuous_iff_isClosed_epigraph`;
- the chapter epigraph owner `epi`;
- `List.TFAE`.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot α`;
- derived API: the equivalence between lower semicontinuity, closed scalar sublevel sets, and a
  closed epigraph.

Layer target: `source-facing`, stated on the chapter's canonical extended-codomain owner layer
`WithTopBot α` with scalar epigraph owner `epi`.
-/

-- Proof sketch: specialize mathlib's closed-sublevel characterization
-- `lowerSemicontinuous_iff_isClosed_preimage` from arbitrary thresholds to scalar thresholds.
/-- Canonical owner-layer form: a function `f : E → WithTopBot α` is lower semicontinuous exactly
when each lower-level preimage `f ⁻¹' Set.Iic y`, indexed by the true codomain threshold
`y : WithTopBot α`, is closed. -/
theorem lowerSemicontinuous_iff_isClosed_lowerLevel
    {f : E → WithTopBot α} :
    LowerSemicontinuous f ↔ ∀ y : WithTopBot α, IsClosed (f ⁻¹' Set.Iic y) := by
  simpa using (lowerSemicontinuous_iff_isClosed_preimage (f := f))

/-
Source-facing specialization to scalar thresholds `r : α`.
-/
/-- A function `f : E → WithTopBot α` is lower semicontinuous exactly when each scalar sublevel
set `{x | f x ≤ r}` is closed. -/
theorem lowerSemicontinuous_iff_isClosed_sublevel
    [NoMinOrder α] [Nonempty α] {f : E → WithTopBot α} :
    LowerSemicontinuous f ↔ ∀ r : α, IsClosed {x : E | f x ≤ r} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  constructor
  · intro hf r
    simpa using hf ((r : α) : WithTopBot α)
  · intro h y
    change WithTop (WithBot α) at y
    induction y using WithTop.recTopCoe with
    | top =>
        simpa using (isClosed_univ : IsClosed (Set.univ : Set E))
    | coe y =>
        induction y using WithBot.recBotCoe with
        | bot =>
            have hpreimage_eq :
                f ⁻¹' Set.Iic ((⊥ : WithBot α) : WithTopBot α) =
                  ⋂ r : α, {x : E | f x ≤ r} := by
              ext x
              constructor
              · intro hx
                rw [Set.mem_iInter]
                intro r
                have hxbot : f x ≤ ((⊥ : WithBot α) : WithTopBot α) := by
                  simpa [Set.mem_preimage] using hx
                exact le_trans hxbot bot_le
              · intro hx
                rw [Set.mem_iInter] at hx
                by_cases hbot : f x = ((⊥ : WithBot α) : WithTopBot α)
                · exact le_of_eq hbot
                · exfalso
                  cases hfx : f x using WithTop.recTopCoe with
                  | top =>
                      let a : α := Classical.choice inferInstance
                      have hxa : f x ≤ (a : WithTopBot α) := by
                        simpa using hx a
                      rw [hfx] at hxa
                      simp at hxa
                  | coe z =>
                      cases hz : z using WithBot.recBotCoe with
                      | bot =>
                          exact hbot (by simpa [hfx, hz])
                      | coe z =>
                          rcases exists_lt z with ⟨r, hr⟩
                          have hxr : f x ≤ (r : WithTopBot α) := by
                            simpa using hx r
                          rw [hfx, hz] at hxr
                          have hzle' : (z : WithBot α) ≤ (r : WithBot α) :=
                            WithTop.coe_le_coe.mp hxr
                          have hzle : z ≤ r := WithBot.coe_le_coe.mp hzle'
                          exact (not_le_of_gt hr hzle).elim
            have hclosed :
                IsClosed (f ⁻¹' Set.Iic ((⊥ : WithBot α) : WithTopBot α)) := by
              rw [hpreimage_eq]
              exact isClosed_iInter h
            simpa using hclosed
        | coe r =>
            simpa using h r

-- Proof sketch: a closed scalar epigraph gives closed scalar slices by continuous preimage along
-- `x ↦ (x, r)`, and the scalar-slice criterion then yields lower semicontinuity.
/-- Closedness of the scalar epigraph implies lower semicontinuity for
`f : E → WithTopBot α`. -/
theorem lowerSemicontinuous_of_isClosed_epi
    [NoMinOrder α] [Nonempty α] [TopologicalSpace α] {f : E → WithTopBot α}
    (hEpi : IsClosed (epi f)) :
    LowerSemicontinuous f := by
  refine lowerSemicontinuous_iff_isClosed_sublevel.2 ?_
  intro r
  let slice : E → E × α := fun x ↦ (x, r)
  have hslice : Continuous slice := continuous_id.prodMk continuous_const
  have hpreimage :
      {x : E | f x ≤ r} = slice ⁻¹' epi f := by
    ext x
    simp [slice]
  rw [hpreimage]
  exact hEpi.preimage hslice

private theorem isClosed_epi_of_lowerSemicontinuous_core
    [TopologicalSpace α] [OrderTopology α]
    {f : E → WithTopBot α} (hf : LowerSemicontinuous f) :
    IsClosed (epi f) := by
  letI : TopologicalSpace (WithBot α) := by
    change TopologicalSpace ((WithTop (OrderDual α))ᵒᵈ)
    infer_instance
  letI : OrderTopology (WithBot α) := by
    change OrderTopology ((WithTop (OrderDual α))ᵒᵈ)
    infer_instance
  letI : TopologicalSpace (WithTopBot α) :=
    TopologicalSpace.instWithTopOfOrderTopology (ι := WithBot α)
  letI : OrderTopology (WithTopBot α) :=
    TopologicalSpace.instOrderTopologyWithTop (ι := WithBot α)
  letI : ClosedIciTopology (WithTopBot α) := by
    infer_instance
  have hclosedEpigraph : IsClosed {p : E × WithTopBot α | f p.1 ≤ p.2} :=
    (lowerSemicontinuous_iff_isClosed_epigraph (f := f)).1 hf
  let coeProd : E × α → E × WithTopBot α := fun p ↦ (p.1, (p.2 : WithTopBot α))
  have hbotSome : Continuous (WithTop.some : OrderDual α → WithBot α) := by
    simpa [WithBot] using (WithTop.continuous_coe (ι := OrderDual α))
  have hbotCoe : Continuous (fun x : α ↦ (x : WithBot α)) := by
    simpa [Function.comp] using hbotSome.comp continuous_id
  have hcoe : Continuous (fun x : α ↦ (x : WithTopBot α)) := by
    simpa [WithTopBot, Function.comp] using
      (WithTop.continuous_coe (ι := WithBot α)).comp hbotCoe
  have hcoeProd : Continuous coeProd :=
    continuous_fst.prodMk (hcoe.comp continuous_snd)
  have hpreimage :
      epi f = coeProd ⁻¹' {p : E × WithTopBot α | f p.1 ≤ p.2} := by
    ext p
    rcases p with ⟨x, μ⟩
    simp [epi, coeProd]
  rw [hpreimage]
  exact hclosedEpigraph.preimage hcoeProd

-- Proof sketch: package the codomain-threshold closed-level characterization together with the
-- scalar-epigraph criterion as a `List.TFAE`.
/-- Canonical three-way form of Theorem 7.1 on the true codomain-owner layer `WithTopBot α`:
lower semicontinuity, closedness of all lower-level preimages `f ⁻¹' Set.Iic y`, and closedness
of the scalar epigraph `epi f` are equivalent. -/
theorem lowerSemicontinuous_tfae_closed_lower_levels_closed_epi
    [NoMinOrder α] [Nonempty α] [TopologicalSpace α] [OrderTopology α]
    (f : E → WithTopBot α) :
    List.TFAE
      [ LowerSemicontinuous f,
        ∀ y : WithTopBot α, IsClosed (f ⁻¹' Set.Iic y),
        IsClosed (epi f) ] := by
  tfae_have 1 → 2 := by
    exact lowerSemicontinuous_iff_isClosed_lowerLevel.1
  tfae_have 2 → 3 := by
    intro hLower
    have hf : LowerSemicontinuous f :=
      (lowerSemicontinuous_iff_isClosed_lowerLevel (f := f)).2 hLower
    exact isClosed_epi_of_lowerSemicontinuous_core (f := f) hf
  tfae_have 3 → 1 := by
    exact lowerSemicontinuous_of_isClosed_epi
  tfae_finish

-- Proof sketch: combine the scalar-sublevel bridge above with the standard epigraph criterion
-- `lowerSemicontinuous_iff_isClosed_epigraph`, then package the three source clauses as a
-- `List.TFAE`.
/-- Theorem 7.1: for a function `f : E → WithTopBot α`, lower semicontinuity, closedness of every
scalar sublevel set `{x | f x ≤ r}`, and closedness of the scalar epigraph are equivalent. -/
theorem lowerSemicontinuous_tfae_closed_sublevels_closed_epi
    [NoMinOrder α] [Nonempty α] [TopologicalSpace α] [OrderTopology α]
    (f : E → WithTopBot α) :
    List.TFAE
      [ LowerSemicontinuous f,
        ∀ r : α, IsClosed {x : E | f x ≤ r},
        IsClosed (epi f) ] := by
  tfae_have 1 → 2 := by
    exact lowerSemicontinuous_iff_isClosed_sublevel.1
  tfae_have 2 → 3 := by
    intro hSub
    have hf : LowerSemicontinuous f :=
      (lowerSemicontinuous_iff_isClosed_sublevel (f := f)).2 hSub
    exact isClosed_epi_of_lowerSemicontinuous_core (f := f) hf
  tfae_have 3 → 1 := by
    exact lowerSemicontinuous_of_isClosed_epi
  tfae_finish

/-- Lower semicontinuity implies closed scalar epigraph for
`f : E → WithTopBot α`. -/
theorem isClosed_epi_of_lowerSemicontinuous
    [TopologicalSpace α] [OrderTopology α]
    {f : E → WithTopBot α} (hf : LowerSemicontinuous f) :
    IsClosed (epi f) :=
  isClosed_epi_of_lowerSemicontinuous_core (f := f) hf

/-- The scalar epigraph owner `epi` gives the canonical closed-epigraph characterization of lower
semicontinuity for `WithTopBot`-valued functions. -/
theorem lowerSemicontinuous_iff_isClosed_epi
    [NoMinOrder α] [Nonempty α] [TopologicalSpace α] [OrderTopology α]
    {f : E → WithTopBot α} :
    LowerSemicontinuous f ↔ IsClosed (epi f) := by
  constructor
  · exact isClosed_epi_of_lowerSemicontinuous
  · exact lowerSemicontinuous_of_isClosed_epi

end
