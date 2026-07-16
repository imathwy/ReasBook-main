import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {α : Type*} [TopologicalSpace α]

open Function

/-
Source/core/bridge triage:
- `source-facing`: Text 7.0.4 introduces the lower semi-continuous hull of a function in a
  concrete finite-dimensional model as
  the greatest lower semicontinuous function majorized by the given function.
- `core/canonical`: the owner abstractions are the real-epigraph owner `epi`, the chapter
  epigraph-to-function owner `Function.verticalInfimum`, and mathlib's predicate
  `LowerSemicontinuous`.
- `bridge/view`: the source wording "greatest lower semicontinuous minorant" is derived API on top
  of the canonical owner construction obtained by taking the vertical infimum of the closed
  epigraph `closure (epi f)`.

Domain-style sampling used here:
- `epi`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_le_of_mem`;
- `Function.verticalInfimum_le_of_epi_subset`;
- `Function.le_verticalInfimum_of_subset_epi`;
- `lowerSemicontinuous_iff_isClosed_epigraph`;
- `LowerSemicontinuous.isClosed_epigraph`.

Primitive data vs derived API:
- the primitive datum is the function `f : α → WithTopBot 𝕜`;
- the owner construction is the function attached by `Function.verticalInfimum` to the closed
  epigraph `closure (epi f)`;
- the source-facing main statements are the epigraph-closure identity
  `closure (epi f) = epi cl(f)` and the `IsGreatest` characterization of `cl(f)` among lower
  semicontinuous minorants of `f`;
- lower semicontinuity and the pointwise bound `cl(f) ≤ f` are derived companions from that
  owner-level epigraph description.

Layer target: `source-facing`; this file keeps Rockafellar's closure `cl(f)` as the public owner,
but it is refined to grow from the earlier chapter owner `Function.verticalInfimum` on epigraph
sets instead of from a parallel local subtype-of-minorants wrapper.
-/

/-- Text 7.0.4: the lower semi-continuous hull of an extended-codomain function, specialized in
the source to a concrete finite-dimensional model, is the function attached to
the closed scalar epigraph `closure (epi f)` by
the chapter owner `Function.verticalInfimum`. The later source-facing theorem below shows that this
is exactly the greatest lower semicontinuous minorant of `f`. -/
def lowerSemicontinuousHull {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜]
    (f : α → WithTopBot 𝕜) : α → WithTopBot 𝕜 :=
  verticalInfimum (closure (epi f))

scoped[Rockafellar] notation "cl(" f ")" => lowerSemicontinuousHull f

section CoreLattice

variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜]

open scoped Rockafellar

/-- The closure `cl(f)` is majorized by the original function. -/
theorem lowerSemicontinuousHull_le_of_noBot [NoBotOrder 𝕜] (f : α → WithTopBot 𝕜) :
    cl(f) ≤ f := by
  simpa [lowerSemicontinuousHull] using
    (verticalInfimum_le_of_epi_subset
      (subset_closure : epi f ⊆ closure (epi f)) :
        verticalInfimum (closure (epi f)) ≤ f)

/-- Any closed-epigraph minorant of `f` lies below the closure `cl(f)`. -/
private theorem le_lowerSemicontinuousHull_of_isClosed_epi
    {f g : α → WithTopBot 𝕜} (hg_closed : IsClosed (epi g)) (hg_le : g ≤ f) :
    g ≤ cl(f) := by
  have hsubset : closure (epi f) ⊆ epi g := by
    have hfg : epi f ⊆ epi g := by
      intro p hp
      rcases p with ⟨x, μ⟩
      rw [mem_epi_iff] at hp ⊢
      exact le_trans (hg_le x) hp
    exact closure_minimal hfg hg_closed
  simpa [lowerSemicontinuousHull] using
    (le_verticalInfimum_of_subset_epi hsubset :
      g ≤ verticalInfimum (closure (epi f)))

/-- A closed-epigraph function is fixed by the closure operator `cl(·)`. -/
theorem cl_eq_self_of_isClosed_epi
    [NoBotOrder 𝕜] {f : α → WithTopBot 𝕜} (hf_closed : IsClosed (epi f)) :
    cl(f) = f :=
  le_antisymm (lowerSemicontinuousHull_le_of_noBot f)
    (le_lowerSemicontinuousHull_of_isClosed_epi hf_closed le_rfl)

end CoreLattice

section GenericCodomain

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]

open scoped Rockafellar

private theorem mem_closure_epi_of_le
    [OrderTopology 𝕜]
    {f : α → WithTopBot 𝕜} {x : α} {μ ν : 𝕜}
    (hμ : (x, μ) ∈ closure (epi f)) (hμν : μ ≤ ν) :
    (x, ν) ∈ closure (epi f) := by
  let raise : α × 𝕜 → α × 𝕜 := fun p ↦ (p.1, max p.2 ν)
  have hraise : Continuous raise := by
    continuity
  have hraise_epi : raise '' epi f ⊆ epi f := by
    rintro _ ⟨⟨x', r'⟩, hp, rfl⟩
    rw [mem_epi_iff] at hp ⊢
    exact le_trans hp (by exact_mod_cast (le_max_left r' ν))
  have hraise_closure : raise '' closure (epi f) ⊆ closure (epi f) := by
    calc
      raise '' closure (epi f) ⊆ closure (raise '' epi f) :=
        image_closure_subset_closure_image hraise
      _ ⊆ closure (epi f) := closure_mono hraise_epi
  have hraise_eq : raise (x, μ) = (x, ν) := by
    ext
    · rfl
    · change max μ ν = ν
      exact max_eq_right hμν
  exact hraise_eq ▸ hraise_closure ⟨(x, μ), hμ, rfl⟩

/-- The closed scalar epigraph of `cl(f)` is exactly the closure of the scalar epigraph of `f`. -/
theorem closure_epi_eq_epi_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    closure (epi f) = epi cl(f) := by
  ext p
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    exact mem_epi_iff.mpr (verticalInfimum_le_of_mem hp)
  · intro hp
    have hclosed :
        IsClosed {r : 𝕜 | (x, r) ∈ closure (epi f)} := by
      have hcont : Continuous fun r : 𝕜 ↦ (x, r) := by
        continuity
      simpa using (isClosed_closure : IsClosed (closure (epi f))).preimage hcont
    have hclosure_section :
        closure {r : 𝕜 | (x, r) ∈ closure (epi f)} =
          ((↑) : 𝕜 → WithTopBot 𝕜) ⁻¹' Set.Ici
            (verticalInfimum (closure (epi f)) x) := by
      have hupper :
          ∀ {r s : 𝕜}, r ∈ verticalSection (closure (epi f)) x → r ≤ s →
            s ∈ verticalSection (closure (epi f)) x := by
        intro r s hr hrs
        have hr' : (x, r) ∈ closure (epi f) := by
          simpa [verticalSection] using hr
        have hs' : (x, s) ∈ closure (epi f) :=
          mem_closure_epi_of_le (f := f) hr' hrs
        simpa [verticalSection] using hs'
      simpa [verticalSection] using
        (closure_verticalSection_eq_preimage_Ici_of_upward_closed
          (F := closure (epi f)) (x := x) hupper)
    have hfiber : μ ∈ {r : 𝕜 | (x, r) ∈ closure (epi f)} := by
      rw [← hclosed.closure_eq, hclosure_section]
      simpa [lowerSemicontinuousHull, Set.preimage, Set.Ici] using (mem_epi_iff.mp hp)
    exact hfiber

/-- `cl(f)` is the greatest closed-epigraph minorant of `f`. -/
private theorem isGreatest_closedEpiMinorant_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    IsGreatest {g : α → WithTopBot 𝕜 | IsClosed (epi g) ∧ g ≤ f} (cl(f)) := by
  refine ⟨?_, ?_⟩
  · have hcl : IsClosed (epi (cl(f))) := by
      rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
      exact isClosed_closure
    exact ⟨hcl, lowerSemicontinuousHull_le_of_noBot f⟩
  · intro g hg
    exact le_lowerSemicontinuousHull_of_isClosed_epi hg.1 hg.2

/-- Canonical form: the closure `cl(f)` is lower semicontinuous. -/
theorem lowerSemicontinuous_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜]
    (f : α → WithTopBot 𝕜) :
    LowerSemicontinuous (cl(f)) := by
  apply lowerSemicontinuous_of_isClosed_epi
  rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
  exact isClosed_closure

/-- Any lower semicontinuous minorant of `f` lies below `cl(f)`. -/
theorem le_lowerSemicontinuousHull_of_lowerSemicontinuous
    [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f g : α → WithTopBot 𝕜} (hg_lsc : LowerSemicontinuous g) (hg_le : g ≤ f) :
    g ≤ cl(f) :=
  le_lowerSemicontinuousHull_of_isClosed_epi
    (isClosed_epi_of_lowerSemicontinuous hg_lsc) hg_le

/-- The closure `cl(f)` is the greatest lower semicontinuous minorant of `f`. -/
theorem isGreatest_lowerSemicontinuousHull
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜]
    (f : α → WithTopBot 𝕜) :
    IsGreatest {g : α → WithTopBot 𝕜 | LowerSemicontinuous g ∧ g ≤ f} (cl(f)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨
      lowerSemicontinuous_lowerSemicontinuousHull f,
      lowerSemicontinuousHull_le_of_noBot f⟩
  · intro g hg
    exact le_lowerSemicontinuousHull_of_lowerSemicontinuous hg.1 hg.2

/-- Every lower semicontinuous function is fixed by `cl(·)`. -/
theorem lowerSemicontinuousHull_eq_self
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f : α → WithTopBot 𝕜} (hf_lsc : LowerSemicontinuous f) :
    cl(f) = f :=
  cl_eq_self_of_isClosed_epi
    (isClosed_epi_of_lowerSemicontinuous hf_lsc)

end GenericCodomain

section GenericConsequences

open scoped Rockafellar

/-- The closure `cl(f)` is majorized by the original function. -/
theorem lowerSemicontinuousHull_le
    {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
    (f : α → WithTopBot 𝕜) :
    cl(f) ≤ f := by
  exact lowerSemicontinuousHull_le_of_noBot f

/-- Any lower semicontinuous minorant of `f` lies below the closure `cl(f)`. -/
theorem le_lowerSemicontinuousHull
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    {f g : α → WithTopBot 𝕜} (hg_lsc : LowerSemicontinuous g) (hg_le : g ≤ f) :
    g ≤ cl(f) := by
  exact le_lowerSemicontinuousHull_of_lowerSemicontinuous hg_lsc hg_le

/-- The closure operator `cl(·)` is monotone with respect to pointwise order. -/
theorem lowerSemicontinuousHull_mono
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
    [NoBotOrder 𝕜]
    {f g : α → WithTopBot 𝕜} (hfg : f ≤ g) :
    cl(f) ≤ cl(g) := by
  have hcl_closed : IsClosed (epi (cl(f))) := by
    rw [← closure_epi_eq_epi_lowerSemicontinuousHull (f := f)]
    exact isClosed_closure
  have hcl_le_g : cl(f) ≤ g := fun x ↦ le_trans (lowerSemicontinuousHull_le f x) (hfg x)
  exact le_lowerSemicontinuousHull_of_isClosed_epi (f := g) hcl_closed hcl_le_g

/-- Taking the closure `cl(f)` preserves the global infimum of an extended-real-valued function.
-/
theorem iInf_lowerSemicontinuousHull_eq_iInf
    {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
    (f : α → WithTopBot 𝕜) :
    (⨅ x, cl(f) x) = ⨅ x, f x := by
  refine le_antisymm (iInf_mono fun x ↦ lowerSemicontinuousHull_le f x) ?_
  refine le_iInf fun x ↦ ?_
  exact le_lowerSemicontinuousHull lowerSemicontinuous_const (fun y ↦ iInf_le f y) x

end GenericConsequences

end
