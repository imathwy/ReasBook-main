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

-- Proof sketch: for any `μ`, membership of `(x, μ)` in `closure (epi f)` is characterized by
-- approaching epigraph points `(y, ν)` with `y → x` and `f y ≤ ν → μ`. This identifies the least
-- such height over `x` with the neighborhood-filter liminf of `f` at `x`; combine this with the
-- epigraph identity from clause (1).
/-- Bridge-level form: if `closure (epi f)` is already identified with `epi cl(f)`, then `cl(f)` is
the pointwise neighborhood-filter liminf. -/
theorem lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) (x : α)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) x = Filter.liminf f (nhds x) := by
  refine WithBot.eq_of_forall_le_coe_iff ?_
  intro a
  cases a with
  | top =>
      simp
  | coe α =>
      have hliminf :
          Filter.liminf f (nhds x) ≤ (α : WithBotTop 𝕜) ↔
            ∀ y > (α : WithBotTop 𝕜), ∃ᶠ z in nhds x, f z < y :=
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
        by_cases hy_top : y = (⊤ : WithBotTop 𝕜)
        · have ht : u ×ˢ (Set.univ : Set 𝕜) ∈ nhds (x, α) := by
            simpa [nhds_prod_eq] using
              (Filter.prod_mem_prod hu (show (Set.univ : Set 𝕜) ∈ nhds α from Filter.univ_mem))
          rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ (Set.univ : Set 𝕜)) ht with ⟨p, hp⟩
          rcases hp with ⟨hpU, hpEpi⟩
          rcases hpU with ⟨hzU, -⟩
          refine ⟨p.1, hzU, ?_⟩
          have hfne : f p.1 ≠ (⊤ : WithBotTop 𝕜) := by
            intro hf_top
            exact (not_le_of_gt (WithBotTop.coe_lt_top p.2)) (hf_top ▸ (mem_epi_iff.mp hpEpi))
          simpa [hy_top] using (lt_top_iff_ne_top.mpr hfne)
        · have hy_bot : y ≠ (⊥ : WithBotTop 𝕜) := by
            intro hy_bot
            have hcontra : ¬ ((α : WithBotTop 𝕜) < (⊥ : WithBotTop 𝕜)) := by simp
            exact hcontra (hy_bot ▸ hy)
          lift y to 𝕜 using ⟨hy_top, hy_bot⟩ with β hβ
          have hαβ : α < β := by
            exact (WithBotTop.coe_lt_coe).1 (by simpa [hβ] using hy)
          have ht : u ×ˢ Set.Iio β ∈ nhds (x, α) := by
            simpa [nhds_prod_eq] using (Filter.prod_mem_prod hu (Iio_mem_nhds hαβ))
          rcases (mem_closure_iff_nhds.1 hmem) (u ×ˢ Set.Iio β) ht with ⟨p, hp⟩
          rcases hp with ⟨hpU, hpEpi⟩
          rcases hpU with ⟨hzU, hμβ⟩
          refine ⟨p.1, hzU, ?_⟩
          have hf_lt : f p.1 < ((β : 𝕜) : WithBotTop 𝕜) :=
            lt_of_le_of_lt (mem_epi_iff.mp hpEpi) ((WithBotTop.coe_lt_coe).2 hμβ)
          simpa [hβ] using hf_lt
      · intro hlim
        have hmem : (x, α) ∈ closure (epi f) := by
          refine (mem_closure_iff_nhds).2 ?_
          intro s hs
          rcases (mem_nhds_prod_iff.mp hs) with ⟨u, hu, v, hv, huv⟩
          rcases exists_Ico_subset_of_mem_nhds hv (exists_gt α) with ⟨β, hαβ, hβv⟩
          rcases exists_between hαβ with ⟨γ, hαγ, hγβ⟩
          have hfreq_lt : ∃ᶠ z in nhds x, f z < ((γ : 𝕜) : WithBotTop 𝕜) :=
            hliminf.1 hlim ((γ : 𝕜) : WithBotTop 𝕜) ((WithBotTop.coe_lt_coe).2 hαγ)
          rcases (Filter.frequently_iff.1 hfreq_lt) hu with ⟨z, hzU, hzlt⟩
          refine ⟨(z, γ), ?_⟩
          refine ⟨huv ?_, mem_epi_iff.mpr (le_of_lt hzlt)⟩
          exact ⟨hzU, hβv ⟨hαγ.le, hγβ⟩⟩
        have h' : (x, α) ∈ epi cl(f) := by
          simpa [hclosure] using hmem
        exact mem_epi_iff.mp h'

/-- The closure owner `cl(·)` is the pointwise neighborhood-filter liminf. -/
@[simp] theorem lowerSemicontinuousHull_apply_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) (x : α) :
    cl(f) x = Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) (closure_epi_eq_epi_lowerSemicontinuousHull f)

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜)
    (hclosure : closure (epi f) = epi cl(f)) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  funext x
  exact lowerSemicontinuousHull_apply_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (x := x) hclosure

/-- Function-level form: the closure `cl(f)` is the neighborhood-filter liminf of `f`. -/
theorem lowerSemicontinuousHull_eq_liminf_nhds
    [NoBotOrder 𝕜]
    (f : α → WithBotTop 𝕜) :
    cl(f) = fun x ↦ Filter.liminf f (nhds x) := by
  exact lowerSemicontinuousHull_eq_liminf_nhds_of_closure_epi_eq
    (f := f) (closure_epi_eq_epi_lowerSemicontinuousHull f)

end
