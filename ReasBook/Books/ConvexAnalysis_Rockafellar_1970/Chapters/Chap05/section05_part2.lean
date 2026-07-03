import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_5 (from Chap01) -/
universe u v w z

namespace Function

section EpigraphSup

variable {E : Type u}
variable {I : Sort v}
variable {α : Type z} [ConditionallyCompleteLattice α]

-- Owner bridge at primitive layer: epigraph of a pointwise supremum is the intersection
-- of the corresponding epigraph family.
@[simp] theorem epi_iSup
    {f : I → E → WithTopBot α} :
    epi (⨆ i, f i) = ⋂ i, epi (f i) := by
  ext p
  simp [epi, iSup_le_iff]

@[simp] theorem epi_sSup
    (F : Set (E → WithTopBot α)) :
    epi (SupSet.sSup F) = ⋂ f : F, epi ((f : E → WithTopBot α)) := by
  rw [sSup_eq_iSup']
  exact epi_iSup (f := fun f : F ↦ (f : E → WithTopBot α))

end EpigraphSup

section ConvexitySupEpigraph

variable {E : Type u}
variable {α : Type z} [ConditionallyCompleteLattice α]

namespace ConvexOn

/-- Helper for Theorem 5.5: the constrained epigraph of a pointwise supremum is the
intersection of the constrained epigraphs of the family, with an extra bottom branch preserving
the domain condition when the family is empty. -/
theorem sSup_epigraph_iInter {C : Set E}
    {F : Set (E → WithTopBot α)} :
    {p : E × WithTopBot α | p.1 ∈ C ∧ SupSet.sSup F p.1 ≤ p.2} =
      ⋂ o : Option F, {p : E × WithTopBot α | p.1 ∈ C ∧
        (match o with
        | none => (⊥ : E → WithTopBot α)
        | some f => (f : E → WithTopBot α)) p.1 ≤ p.2} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpC, hpSup⟩
    -- Rewrite the supremum pointwise so each family member becomes a visible `iSup` branch.
    rw [Set.mem_iInter]
    intro o
    cases o with
    | none =>
        exact ⟨hpC, bot_le⟩
    | some f =>
        rw [sSup_eq_iSup', iSup_apply] at hpSup
        exact ⟨hpC, (le_iSup (fun g : F ↦ (g : E → WithTopBot α) p.1) f).trans hpSup⟩
  · intro hp
    -- The `none` branch recovers membership in `C`, and the `some` branches bound every member.
    rw [Set.mem_iInter] at hp
    have hpNone := hp none
    refine ⟨hpNone.1, ?_⟩
    rw [sSup_eq_iSup', iSup_apply, iSup_le_iff]
    intro f
    exact (hp (some f)).2

end ConvexOn

end ConvexitySupEpigraph

section ConvexitySup

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {I : Sort v}
variable {α : Type z} [ConditionallyCompleteLattice α]
variable [AddCommMonoid (WithTopBot α)] [IsOrderedAddMonoid (WithTopBot α)]
variable [SMul 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]

namespace ConvexOn

/-- Helper for Theorem 5.5: under the current order-compatible scalar action assumptions,
`ConvexOn` is equivalent to convexity of the constrained epigraph. -/
theorem iff_convex_epigraph {C : Set E} {f : E → WithTopBot α} :
    ConvexOn 𝕜 C f ↔ Convex 𝕜 {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} := by
  constructor
  · intro hf
    -- The Jensen inequality for `hf` closes the epigraph under convex combinations.
    rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
    refine ⟨hf.1 hx hy ha hb hab, ?_⟩
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
      _ ≤ a • r + b • t := by
        gcongr
  · intro h
    -- Test convexity on the canonical epigraph points `(x, f x)` and `(y, f y)`.
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      have hx_epi : (x, f x) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} :=
        ⟨hx, le_rfl⟩
      have hy_epi : (y, f y) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} :=
        ⟨hy, le_rfl⟩
      simpa [Prod.smul_mk, Prod.mk_add_mk] using (h hx_epi hy_epi ha hb hab).1
    · intro x hx y hy a b ha hb hab
      have hx_epi : (x, f x) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} :=
        ⟨hx, le_rfl⟩
      have hy_epi : (y, f y) ∈ {p : E × WithTopBot α | p.1 ∈ C ∧ f p.1 ≤ p.2} :=
        ⟨hy, le_rfl⟩
      simpa [Prod.smul_mk, Prod.mk_add_mk] using (h hx_epi hy_epi ha hb hab).2

/-- Theorem 5.5: on a fixed convex set `C`, the pointwise supremum of an arbitrary family of
convex `WithTopBot α`-valued functions is convex. -/
theorem sSup {C : Set E}
    {F : Set (E → WithTopBot α)}
    (hC : Convex 𝕜 C)
    (hF : ∀ f ∈ F, ConvexOn 𝕜 C f) :
    ConvexOn 𝕜 C (SupSet.sSup F) := by
  -- Follow the source proof: rewrite the constrained epigraph as an arbitrary intersection.
  rw [iff_convex_epigraph]
  rw [sSup_epigraph_iInter]
  -- Each branch is convex, so the whole intersection is convex.
  refine convex_iInter ?_
  intro o
  cases o with
  | none =>
      -- The extra bottom branch keeps the domain condition visible even for an empty family.
      have hDomain : Convex 𝕜 {p : E × WithTopBot α | p.1 ∈ C} := by
        -- Only the first coordinate matters, so this is just convexity of `C` on the product.
        intro p hp q hq a b ha hb hab
        simpa [Prod.smul_mk, Prod.mk_add_mk] using hC hp hq ha hb hab
      simpa using hDomain
  | some f =>
      -- A genuine family branch is exactly the constrained epigraph of one member of `F`.
      exact (iff_convex_epigraph (𝕜 := 𝕜) (C := C) (f := (f : E → WithTopBot α))).1
        (hF f f.property)

/-- Indexed-family form of Theorem 5.5 on the canonical owner `ConvexOn`. -/
theorem iSup {C : Set E}
    {f : I → E → WithTopBot α}
    (hC : Convex 𝕜 C)
    (hf : ∀ i, ConvexOn 𝕜 C (f i)) :
    ConvexOn 𝕜 C (⨆ i, f i) := by
  -- Reindex the family by its range so the set-indexed supremum theorem applies directly.
  simpa [sSup_range] using
    (ConvexOn.sSup (𝕜 := 𝕜) (C := C) (F := Set.range f) hC
      (fun g hg ↦ by
        -- Every element of the range comes from some original index.
        rcases hg with ⟨i, rfl⟩
        exact hf i))

end ConvexOn

end ConvexitySup

end Function

/-! ### Text_5_5_6 (from Chap01) -/
noncomputable section

universe u v w

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.6 states that the convex hull of a family of functions is the
  greatest convex function lying below every member of the family.
- `core/canonical`: the owner abstractions already available in this section are
  `Function.convexHull : (E → WithBotTop 𝕜) → E → WithBotTop 𝕜` and
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop`.
- `bridge/view`: the family statement is expressed directly on the canonical owner
  `conv(⨅ i, f i)` and the canonical convex-minorant owner
  `Function.convexMinorants (⨅ i, f i)`.
- Primitive data vs derived API: the family `f` is primitive; convexity of `conv(⨅ i, f i)` and
  the universal maximality property are derived. The pointwise convexity and minorant
  consequences are just projections of the canonical single-function maximality owner theorem
  specialized to `⨅ i, f i`.

Domain-style sampling used here:
- `Function.convexHull`;
- `Function.isGreatest_conv_minorant_of_isConvex`;
- `Function.IsConvex`;
- `Function.convexMinorants`;
- `IsGreatest`;
- Layer target: `bridge/view`; the source-facing family statement is retained as a direct
  specialization of the canonical single-function hull owner theorem.
- Ambient minimization: the theorem only uses the chapter owner constructions on
  `WithBotTop 𝕜`-valued
  functions and pointwise order against a family infimum, so the canonical ambient level is the
  same arbitrary `𝕜`-module `E` already used by `Function.convexHull` and
  `conv(⨅ i, f i)`.
-/
section

variable {E : Type u} {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

-- Proof sketch: specialize the canonical single-function theorem
-- `isGreatest_conv_minorant` to `g := ⨅ i, f i`.
/-- Text 5.5.6: `conv {f_i | i ∈ I}`, represented by `conv(⨅ i, f i)`, is the greatest convex
minorant of the family infimum `⨅ i, f i`. -/
theorem isGreatest_conv_iInf_minorant
    {ι : Sort v} (f : ι → E → WithBotTop 𝕜) :
    IsGreatest (convexMinorants (⨅ i, f i)) (conv(⨅ i, f i)) := by
  simpa using isGreatest_conv_minorant (g := (⨅ i : ι, f i))

end Function

end
