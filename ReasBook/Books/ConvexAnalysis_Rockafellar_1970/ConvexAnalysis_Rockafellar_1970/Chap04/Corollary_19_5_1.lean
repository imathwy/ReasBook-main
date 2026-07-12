import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_5
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open scoped Pointwise
open Function

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.5.1 says that polyhedral convexity is preserved by nonnegative
  scalar right multiplication and, in the proper case, by passage to the recession function.
- `core/canonical`: the owner predicate is `Function.HasPolyhedralEpigraph` on intrinsic
  epigraphs `epi f`; clause (1) keeps the source scalar-codomain surface
  `f : E → WithTopBot 𝕜`, while clause (2) is upgraded to the intrinsic codomain layer
  `f : E → WithTopBot α`.
- `bridge/view`: clause (1) transports polyhedrality across nonnegative dilates of `epi f`;
  clause (2) applies `Set.IsPolyhedral.recessionCone` to `epi f` and identifies that
  recession cone with `epi ((f)₀⁺)` under properness.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph`;
- `Function.HasPolyhedralEpigraph.isPolyhedral`;
- set-side polyhedral transport across nonnegative dilates of `epi f`;
- `Set.IsPolyhedral.recessionCone`;
- `Function.rightScalarMul`;
- `Function.recessionFunction`.

Primitive data vs derived API:
- primitive owner data: a function `f`;
- source hypotheses: polyhedrality of `epi f`, with properness added only for the
  recession-function clause;
- derived API: polyhedrality of `lam •ʳ f` and of `(f)₀⁺`.

Layer target:
- clause (1) is `core/canonical`, stated directly on `Function.HasPolyhedralEpigraph`
  at the ordered-field layer needed by the nonnegative right-scalar owner `lam •ʳ f`
  together with the explicit positive-scalar epigraph transport used in the proof;
- clause (2) is `bridge/view`, attached to the same core owner at the generic `WithTopBot α`
  recession-function layer rather than a separate `EReal` or scalar-codomain specialization.

Ambient refinement:
- clause (1) keeps exactly the scalar/order structure used by
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` and `Set.IsPolyhedral.smul`;
- clause (2) keeps exactly the scalar/order structure used by
  `Convex.mem_recessionCone_iff_add_singleton_subset_self`,
  `Function.recessionFunction_translationUpperBound`,
  and `Set.IsPolyhedral.recessionCone`;
- both clauses stay on `WithTopBot` codomains rather than hard-coding `EReal`.
-/

namespace Function.HasPolyhedralEpigraph

section RightScalarMul

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

private theorem smul_epi_eq_epi_mul_comp_inv_smul_of_pos
    (f : E → WithTopBot 𝕜) {a : 𝕜} (ha : 0 < a) :
    ((a : 𝕜) • epi f : Set (E × 𝕜)) =
      epi (fun y ↦ (a : WithTopBot 𝕜) * f (a⁻¹ • y)) := by
  ext p
  rcases p with ⟨y, μ⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  rw [mem_epi_iff, mem_epi_iff]
  change f (a⁻¹ • y) ≤ a⁻¹ * μ ↔ (a : WithTopBot 𝕜) * f (a⁻¹ • y) ≤ μ
  set z := f (a⁻¹ • y)
  cases z using WithTopBot.rec with
  | bot =>
      rw [WithTopBot.coe_mul_bot_of_pos ha]
      simp
  | top =>
      have hlhs : ¬ ⊤ ≤ (WithTopBot.coe a)⁻¹ * WithTopBot.coe μ := by
        intro h
        have : (WithTopBot.coe a)⁻¹ * WithTopBot.coe μ = (⊤ : WithTopBot 𝕜) :=
          top_le_iff.mp h
        have hEq : (WithTopBot.coe a)⁻¹ * WithTopBot.coe μ =
            (((a⁻¹ * μ : 𝕜)) : WithTopBot 𝕜) := by
          conv_lhs => rw [← WithTopBot.coe_inv a, ← WithTopBot.coe_mul]
        rw [hEq] at this
        exact (WithTopBot.coe_ne_top (a⁻¹ * μ)) this
      constructor
      · intro h
        exact (hlhs h).elim
      · intro h
        rw [WithTopBot.coe_mul_top_of_pos ha] at h
        simp at h
  | coe r =>
      constructor
      · intro h
        rw [← WithTopBot.coe_mul] at h
        have hmulinv : r ≤ a⁻¹ * μ := WithTopBot.coe_le_coe.mp h
        have hdiv : r ≤ μ / a := by
          simpa [div_eq_mul_inv, mul_comm] using hmulinv
        exact WithTopBot.coe_le_coe.mpr <|
          by simpa [mul_comm] using (le_div_iff₀' ha).mp hdiv
      · intro h
        rw [← WithTopBot.coe_mul] at h
        have hmul : a * r ≤ μ := WithTopBot.coe_le_coe.mp h
        have hdiv : r ≤ μ / a := (le_div_iff₀' ha).mpr <|
          by simpa [mul_comm] using hmul
        have hmulinv : r ≤ a⁻¹ * μ := by
          simpa [div_eq_mul_inv, mul_comm] using hdiv
        exact (WithTopBot.coe_le_coe.mpr hmulinv :
          (r : WithTopBot 𝕜) ≤ ((a⁻¹ * μ : 𝕜) : WithTopBot 𝕜))

private theorem singleton_zero_isPolyhedral :
    ({0} : Set E).IsPolyhedral 𝕜 := by
  have huniv : (Set.univ : Set E).IsPolyhedral 𝕜 := by
    refine ⟨∅, ?_⟩
    simp
  have hzero : ((0 : 𝕜) • (Set.univ : Set E)).IsPolyhedral 𝕜 :=
    Set.IsPolyhedral.smul (hC := huniv) (a := (0 : 𝕜))
  simpa [Set.zero_smul_set] using hzero

-- Proof sketch: split on `lam = 0`. The zero branch uses the explicit Text 5.4.3 formula and
-- the indicator/polyhedral-set bridge; the positive branch rewrites the scaled epigraph by the
-- positive-scalar formula and then applies `Set.IsPolyhedral.smul`.
/-- Corollary 19.5.1 (1), core owner form: if `f : E → WithTopBot 𝕜` has polyhedral epigraph,
then every nonnegative right scalar multiple `f_λ` has polyhedral epigraph. -/
theorem rightScalarMul
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (lam : 𝕜≥0) :
    (lam •ʳ f).HasPolyhedralEpigraph := by
  by_cases hlam0 : (lam : 𝕜) = 0
  · have hlam : lam = (⟨0, le_rfl⟩ : 𝕜≥0) := by
      ext
      simpa using hlam0
    by_cases hf_top : f = ⊤
    · simpa [hlam, rightScalarMul_zero_eq_self_of_eq_top (f := f) hf_top] using hf
    · have hzero_fn :
          ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = (δ(· | ({0} : Set E))) :=
        rightScalarMul_zero_eq_indicator_zero_of_ne_top (f := f) hf_top
      have hdelta : (δ[𝕜](· | ({0} : Set E))).HasPolyhedralEpigraph :=
        Set.IsPolyhedral.hasPolyhedralEpigraph_indicator
          (𝕜 := 𝕜) (E := E) singleton_zero_isPolyhedral
      simpa [hlam, hzero_fn] using hdelta
  · have hlam_pos : 0 < (lam : 𝕜) :=
      lt_of_le_of_ne lam.2 (by simpa [eq_comm] using hlam0)
    have hright :
        (lam •ʳ f) = (fun y ↦ (lam : WithTopBot 𝕜) * f ((lam : 𝕜)⁻¹ • y)) := by
      funext x
      simpa using
        rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
          (f := f) (a := (lam : 𝕜)) hlam_pos x
    have hscaled :
        ((lam : 𝕜) • epi f : Set (E × 𝕜)) =
          epi (fun y ↦ (lam : WithTopBot 𝕜) * f ((lam : 𝕜)⁻¹ • y)) :=
      smul_epi_eq_epi_mul_comp_inv_smul_of_pos (f := f) hlam_pos
    have hsmul : (((lam : 𝕜) • epi f : Set (E × 𝕜))).IsPolyhedral 𝕜 :=
      Set.IsPolyhedral.smul (hC := hf.isPolyhedral) (a := (lam : 𝕜))
    rw [Function.HasPolyhedralEpigraph]
    have hEq : (epi (lam •ʳ f)).IsPolyhedral 𝕜 =
        (((lam : 𝕜) • epi f : Set (E × 𝕜))).IsPolyhedral 𝕜 := by
      calc
        (epi (lam •ʳ f)).IsPolyhedral 𝕜
            = (epi (fun y ↦ (lam : WithTopBot 𝕜) * f ((lam : 𝕜)⁻¹ • y))).IsPolyhedral 𝕜 := by
              simp [hright]
        _ = (((lam : 𝕜) • epi f : Set (E × 𝕜))).IsPolyhedral 𝕜 := by
              simp [hscaled]
    exact hEq ▸ hsmul

end RightScalarMul

section RecessionFunction

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α]

private theorem recessionCone_epi_eq_epi_recessionFunction
    {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) (hproper : f.IsProper) :
    (epi f).recessionCone 𝕜 = epi ((f)₀⁺) := by
  classical
  ext p
  rcases p with ⟨d, w⟩
  have hconv : Convex 𝕜 (epi f) := by
    simpa [epi_univ_eq_setOf_le] using hf.isConvex.convex_epigraph
  constructor
  · intro hrec
    have hsubset : epi f + ({(d, w)} : Set (E × α)) ⊆ epi f :=
      (hconv.mem_recessionCone_iff_add_singleton_subset_self (y := (d, w))).1 hrec
    let hfun : E → WithTopBot α := fun z => if z = d then w else ⊤
    have htrans : Function.TranslationUpperBound f hfun := by
      intro x hx z
      by_cases hz : z = d
      · have hx_not_top : f x ≠ ⊤ := ne_of_lt (mem_effectiveDomain.mp hx)
        have hx_not_bot : f x ≠ ⊥ := hproper.ne_bot x
        lift f x to α using ⟨hx_not_top, hx_not_bot⟩ with μ hμ
        have hxepi : (x, μ) ∈ epi f := by
          simp [hμ]
        have hxy : (x + d, μ + w) ∈ epi f := by
          refine hsubset ?_
          exact Set.mem_add.mpr ⟨(x, μ), hxepi, (d, w), by simp, by simp⟩
        simpa [mem_epi_iff, hfun, hz, hμ, add_assoc, add_left_comm, add_comm] using hxy
      · have hx_not_bot : f x ≠ ⊥ := hproper.ne_bot x
        have : f (x + z) ≤ f x + (⊤ : WithTopBot α) := by
          simp [WithTopBot.add_top_of_ne_bot hx_not_bot]
        simpa [hfun, hz] using this
    have hle : ((f)₀⁺) ≤ hfun :=
      Function.recessionFunction_le_of_translationUpperBound (f := f) hproper htrans
    have hle_d : ((f)₀⁺) d ≤ w := by
      simpa [hfun] using hle d
    simpa [mem_epi_iff] using hle_d
  · intro hp_epi
    have hrec_le : ((f)₀⁺) d ≤ w := by
      simpa [mem_epi_iff] using hp_epi
    have hsubset : epi f + ({(d, w)} : Set (E × α)) ⊆ epi f := by
      intro p hpadd
      rcases Set.mem_add.mp hpadd with ⟨p1, hp1, p2, hp2, rfl⟩
      rcases p1 with ⟨x, μ⟩
      rcases Set.mem_singleton_iff.mp hp2 with rfl
      have hxμ : f x ≤ μ := by simpa [mem_epi_iff] using hp1
      have hxdom : x ∈ dom(f) := by
        exact mem_effectiveDomain.mpr (lt_of_le_of_lt hxμ (WithTopBot.coe_lt_top μ))
      have htrans : f (x + d) ≤ f x + ((f)₀⁺) d :=
        Function.recessionFunction_translationUpperBound (f := f) hproper x hxdom d
      have h1 : f x + ((f)₀⁺) d ≤ f x + w := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hrec_le (f x)
      have h2 : f x + w ≤ μ + w := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hxμ (w : WithTopBot α)
      have hxy : f (x + d) ≤ μ + w := le_trans htrans (le_trans h1 h2)
      simpa [mem_epi_iff, add_assoc, add_left_comm, add_comm] using hxy
    exact (hconv.mem_recessionCone_iff_add_singleton_subset_self (y := (d, w))).2 hsubset

-- Proof sketch: identify `epi ((f)₀⁺)` with the recession cone of `epi f` via
-- `recessionCone_epi_eq_epi_recessionFunction`, then apply
-- `Set.IsPolyhedral.recessionCone` to `hf.isPolyhedral`.
/-- Corollary 19.5.1 (2), recession-function owner form: if `f : E → WithTopBot α` is proper and
has polyhedral epigraph, then its recession function `(f)₀⁺` has polyhedral epigraph. -/
theorem recessionFunction
    {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) (hproper : f.IsProper) :
    ((f)₀⁺).HasPolyhedralEpigraph := by
  rw [Function.HasPolyhedralEpigraph, ← recessionCone_epi_eq_epi_recessionFunction hf hproper]
  exact Set.IsPolyhedral.recessionCone (hC := hf.isPolyhedral)

end RecessionFunction

end Function.HasPolyhedralEpigraph

end
