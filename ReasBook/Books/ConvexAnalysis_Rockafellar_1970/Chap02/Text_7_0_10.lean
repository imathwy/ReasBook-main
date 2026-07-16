import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {α : Type u} [TopologicalSpace α]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.10 identifies Rockafellar's closure `cl(f)` with the neighborhood
  liminf of `f`.
- `core/canonical`: the owner abstraction is still the Chapter 2 lower-semicontinuous hull
  `lowerSemicontinuousHull`, written `cl(·)`, together with mathlib's filter owner `Filter.liminf`.
- `bridge/view`: the epigraph-closure theorem
  `closure_epi_eq_epi_lowerSemicontinuousHull` from `Text_7_0_4` bridges the owner `cl(·)` to the
  neighborhood-filter characterization used here.

Domain-style sampling used here:
- `lowerSemicontinuousHull` / `cl(·)`;
- `closure_epi_eq_epi_lowerSemicontinuousHull`;
- `Filter.liminf_le_iff`;
- `mem_closure_iff_nhds`.

Layer target: `source-facing`; this file keeps the textbook liminf formula directly on the chapter
owner `cl(·)` rather than introducing a parallel wrapper around neighborhood liminf data.
-/

/- Text 7.0.10 (1): the epigraph of the closure `cl(f)` is exactly the closure of the epigraph of
`f`. This is the canonical Chapter 2 epigraph-closure theorem for the owner `cl(·)`. -/
recall closure_epi_eq_epi_lowerSemicontinuousHull

private def withTopBotRec {β : Type*} {motive : WithTopBot β → Sort*}
    (bot : motive ⊥) (top : motive ⊤) (coe : ∀ b : β, motive (b : WithTopBot β)) :
    ∀ x, motive x :=
  fun x ↦ WithTop.recTopCoe top (fun y ↦ WithBot.recBotCoe bot coe y) x

-- Proof sketch: for any `μ`, membership of `(x, μ)` in `closure (epi f)` is characterized by
-- approaching epigraph points `(y, ν)` with `y → x` and `f y ≤ ν → μ`. This identifies the least
-- such height over `x` with the neighborhood-filter liminf of `f` at `x`; combine this with the
-- epigraph identity from clause (1).
/-- Bridge-level form: if `closure (epi f)` is already identified with `epi cl(f)`, then `cl(f)` is
the pointwise neighborhood-filter liminf. -/
theorem lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) (x : α)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) x = Filter.liminf f (nhds x) := by
  have hfinite : ∀ a : 𝕜,
      cl(f) x ≤ (a : WithTopBot 𝕜) ↔ Filter.liminf f (nhds x) ≤ (a : WithTopBot 𝕜) := by
    intro α
    all_goals
      have hliminf :
          Filter.liminf f (nhds x) ≤ (α : WithTopBot 𝕜) ↔
            ∀ y > (α : WithTopBot 𝕜), ∃ᶠ z in nhds x, f z < y :=
        Filter.liminf_le_iff
      constructor
      · intro hcl
        have hmem : (x, α) ∈ closure (epi f) := by
          have h' : (x, α) ∈ epi cl(f) := mem_epi_iff.mpr hcl
          simpa [hclosure] using h'
        refine hliminf.2 ?_
        intro y hy
        refine (Filter.frequently_iff).2 ?_
        intro u hu
        by_cases hy_top : y = (⊤ : WithTopBot 𝕜)
        · have ht : u ×ˢ (Set.univ : Set 𝕜) ∈ nhds (x, α) := by
            simpa [nhds_prod_eq] using
              (Filter.prod_mem_prod hu (show (Set.univ : Set 𝕜) ∈ nhds α from Filter.univ_mem))
          rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ (Set.univ : Set 𝕜)) ht with ⟨p, hp⟩
          rcases hp with ⟨hpU, hpEpi⟩
          rcases hpU with ⟨hzU, -⟩
          refine ⟨p.1, hzU, ?_⟩
          have hfne : f p.1 ≠ (⊤ : WithTopBot 𝕜) := by
            intro hf_top
            exact (WithTop.not_top_le_coe _ (hf_top ▸ (mem_epi_iff.mp hpEpi))).elim
          simpa [hy_top] using (lt_top_iff_ne_top.mpr hfne)
        · have hy_bot : y ≠ (⊥ : WithTopBot 𝕜) := by
            intro hy_bot
            have hcontra : ¬ ((α : WithTopBot 𝕜) < (⊥ : WithTopBot 𝕜)) := by simp
            exact hcontra (hy_bot ▸ hy)
          induction hβ : y using WithTop.recTopCoe with
          | top => exact (hy_top hβ).elim
          | coe y' =>
              induction y' using WithBot.recBotCoe with
              | bot => exact (hy_bot hβ).elim
              | coe β =>
                  have hαβ : α < β := by
                    exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp (by simpa [hβ] using hy))
                  have ht : u ×ˢ Set.Iio β ∈ nhds (x, α) := by
                    simpa [nhds_prod_eq] using (Filter.prod_mem_prod hu (Iio_mem_nhds hαβ))
                  rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ Set.Iio β) ht with ⟨p, hp⟩
                  rcases hp with ⟨hpU, hpEpi⟩
                  rcases hpU with ⟨hzU, hμβ⟩
                  refine ⟨p.1, hzU, ?_⟩
                  have hf_lt : f p.1 < ((β : 𝕜) : WithTopBot 𝕜) :=
                    lt_of_le_of_lt (mem_epi_iff.mp hpEpi)
                      (WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hμβ))
                  simpa [hβ] using hf_lt
      · intro hlim
        have hmem : (x, α) ∈ closure (epi f) := by
          refine (mem_closure_iff_nhds).2 ?_
          intro s hs
          rcases (mem_nhds_prod_iff.mp hs) with ⟨u, hu, v, hv, huv⟩
          rcases exists_Ico_subset_of_mem_nhds hv (exists_gt α) with ⟨β, hαβ, hβv⟩
          rcases exists_between hαβ with ⟨γ, hαγ, hγβ⟩
          have hfreq_lt : ∃ᶠ z in nhds x, f z < ((γ : 𝕜) : WithTopBot 𝕜) :=
            hliminf.1 hlim ((γ : 𝕜) : WithTopBot 𝕜)
              (WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hαγ))
          rcases (Filter.frequently_iff.1 hfreq_lt) hu with ⟨z, hzU, hzlt⟩
          refine ⟨(z, γ), ?_⟩
          refine ⟨huv ?_, mem_epi_iff.mpr (le_of_lt hzlt)⟩
          exact ⟨hzU, hβv ⟨hαγ.le, hγβ⟩⟩
        have h' : (x, α) ∈ epi cl(f) := by
          simpa [hclosure] using hmem
        exact mem_epi_iff.mp h'
  letI : NoMinOrder 𝕜 := NoBotOrder.to_noMinOrder 𝕜
  cases hcl : cl(f) x using withTopBotRec with
  | bot =>
      cases hli : Filter.liminf f (nhds x) using withTopBotRec with
      | bot => simpa [hcl, hli]
      | top =>
          have h := hfinite (Classical.arbitrary 𝕜)
          simp [hcl, hli] at h
      | coe b =>
          rcases exists_lt b with ⟨a, ha⟩
          have h := hfinite a
          simp [hcl, hli, not_le_of_gt ha] at h
  | top =>
      cases hli : Filter.liminf f (nhds x) using withTopBotRec with
      | bot =>
          have h := hfinite (Classical.arbitrary 𝕜)
          simp [hcl, hli] at h
      | top => simpa [hcl, hli]
      | coe b =>
          have h := hfinite b
          simp [hcl, hli] at h
  | coe a =>
      cases hli : Filter.liminf f (nhds x) using withTopBotRec with
      | bot =>
          rcases exists_lt a with ⟨b, hb⟩
          have h := hfinite b
          simp [hcl, hli, not_le_of_gt hb] at h
      | top =>
          have h := hfinite a
          simp [hcl, hli] at h
      | coe b =>
          have hab_ext : (a : WithTopBot 𝕜) ≤ (b : WithTopBot 𝕜) := by
            rw [← hcl]
            exact (hfinite b).2 (by simpa [hli])
          have hba_ext : (b : WithTopBot 𝕜) ≤ (a : WithTopBot 𝕜) := by
            rw [← hli]
            exact (hfinite a).1 (by simpa [hcl])
          have hab : a ≤ b := WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hab_ext)
          have hba : b ≤ a := WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hba_ext)
          simpa [hcl, hli, le_antisymm hab hba]

/-- The closure owner `cl(·)` is the pointwise neighborhood-filter liminf. -/
@[simp] theorem lowerSemicontinuousHull_apply_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) (x : α) :
    cl(f) x = Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) (closure_epi_eq_epi_lowerSemicontinuousHull f)

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  funext x
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) hclosure

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (closure_epi_eq_epi_lowerSemicontinuousHull f)

end
