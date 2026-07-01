import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {𝕜 : Type*} [Ring 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.9 characterizes polyhedral convex functions as a finite maximum of
  affine maps plus the indicator of a polyhedral constraint set.
- `core/canonical`: the chapter owner notion is `Function.HasPolyhedralEpigraph` on the intrinsic
  codomain layer `WithTopBot 𝕜`.
- `bridge/view`: the source-facing domain term is the indicator of a polyhedral set `C`, while the
  explicit finite half-space presentation of `C` is a derived set-side consequence of
  `C.IsPolyhedral 𝕜`.

Domain-style sampling used here:
- `epi` / `Function.HasPolyhedralEpigraph` from `Text_19_0_8`;
- `indicator`/`δ[𝕜](· | C)` from `Defintion_4_8_1`;
- `Set.IsPolyhedral` and finite linear-functional inequalities from `Definition_2_1_2` /
  `Text_19_0_1`;
- the explicit finite-family supremum owner `Finset.sup` on `WithTopBot 𝕜`, which keeps this
  theorem on the same ordered-ring layer as the rest of the file without adding a stronger
  conditional-completeness assumption on `𝕜`.

Primitive data vs derived API:
- primitive source-facing data: the finite family of affine maps defining the finite maximum, and
  the polyhedral constraint set itself;
- derived owner-side statement: polyhedral convexity is expressed canonically through
  `Function.HasPolyhedralEpigraph`, together with the source-faithful codomain restriction
  `∀ x, ⊥ < f x` expressing that Rockafellar's functions take values in `(-∞, +∞]`;
- derived bridge/view data: when one wants the textbook finite-inequality realization of the
  domain set, it should be recovered from `C.IsPolyhedral 𝕜` via the existing chapter
  bridge theorems, rather than stored as a parallel local public parameter list.

Layer target: `source-facing`, stated on the core/canonical owner
`Function.HasPolyhedralEpigraph`, with the finite pointwise supremum of affine maps
plus the indicator term kept as the bridge/view side of the proved source-to-owner direction.
The finite family itself is exposed by an explicit nonempty `Finset` of affine maps, not by an
ordered coordinate choice `Fin (k + 1)`, because no public declaration here uses order or
position data on the family and the `Finset` owner keeps the existing ambient scalar assumptions
minimal.

The source says "a convex function is polyhedral convex iff ...", but the explicit
supremum-plus-indicator presentation already forces convexity, and a polyhedral epigraph is
automatically convex by the chapter's set-level owner API. The extra convexity hypothesis is
therefore redundant and omitted from the formal statement.

Ambient refinement:
- the owner `Function.HasPolyhedralEpigraph` from `Text_19_0_8` already lives on arbitrary ordered
  scalar rings and modules, so this item should not keep `EuclideanSpace ℝ (Fin n)`, inner-product
  owners, or the chapter's real-specialized epigraph alias as public primitive data;
- the textbook `R^n` statement is recovered by specializing `𝕜 = ℝ` and
  `E = EuclideanSpace ℝ (Fin n)`, then identifying linear functionals with inner products by the
  Riesz representation theorem.
-/

-- Proof sketch: combine a finite half-space presentation of the polyhedral domain set `C` with
-- the lifted half-spaces `t ≥ a(x)` defining the epigraph of the finite pointwise supremum
-- `s.sup fun a ↦ (a · : WithTopBot 𝕜)`. This yields the polyhedrality of the epigraph together
-- with
-- the codomain-side bound `∀ x, ⊥ < f x`.
/-- Pullback along a linear map preserves polyhedrality. -/
private theorem isPolyhedral_linear_preimage
    {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
    {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    {D : Set F} (hD : D.IsPolyhedral 𝕜 (F →ₗ[𝕜] 𝕜)) (A : E →ₗ[𝕜] F) :
    (A ⁻¹' D).IsPolyhedral 𝕜 (E →ₗ[𝕜] 𝕜) := by
  classical
  rcases hD with ⟨S, rfl⟩
  refine ⟨S.image fun y ↦ ((y.1).comp A, y.2), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_iInter]
  constructor
  · intro hx z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact hx y hy
  · intro hx y hy
    have hz : ((y.1).comp A, y.2) ∈
        S.image (fun z ↦ ((z.1).comp A, z.2)) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    exact hx ((y.1).comp A, y.2) hz

/-- Internal combined proof for the nonempty-family Text 19.0.9 bridge projections:
`HasPolyhedralEpigraph` and the pointwise `⊥`-exclusion. -/
private theorem exists_nonempty_finset_sup_affine_add_indicator_core
    {f : E → WithTopBot 𝕜}
    (hf :
      ∃ s : Finset (E →ᵃ[𝕜] 𝕜), s.Nonempty ∧
          ∃ C : Set E, C.IsPolyhedral 𝕜 ∧
            f = (fun x ↦ s.sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](· | C))) :
    f.HasPolyhedralEpigraph ∧ ∀ x, ⊥ < f x := by
    rcases hf with ⟨s, hs, C, hC, rfl⟩
    let g : E → WithTopBot 𝕜 :=
      fun x ↦ s.sup fun a ↦ (a x : WithTopBot 𝕜)
    have hg_bot : ∀ x, ⊥ < g x := fun x ↦ by
      rcases hs with ⟨a0, ha0⟩
      have h0 : (a0 x : WithTopBot 𝕜) ≤ g x := by
        change (fun a : E →ᵃ[𝕜] 𝕜 ↦ (a x : WithTopBot 𝕜)) a0 ≤
          (s.sup fun a : E →ᵃ[𝕜] 𝕜 ↦ (a x : WithTopBot 𝕜) : WithTopBot 𝕜)
        exact Finset.le_sup_of_le ha0 le_rfl
      exact lt_of_lt_of_le (WithTopBot.bot_lt_coe _) h0
    refine ⟨?_, ?_⟩
    · change Set.IsPolyhedral 𝕜 (epi (fun x : E ↦ g x + δ[𝕜](x | C)))
      have hmem_epi :
          epi (fun x : E ↦ g x + δ[𝕜](x | C)) =
            {p : E × 𝕜 | p.1 ∈ C ∧ ∀ a ∈ s, a p.1 ≤ p.2} := by
        ext p
        constructor
        · intro hp
          have hp' : g p.1 + δ[𝕜](p.1 | C) ≤ (p.2 : WithTopBot 𝕜) := by
            simpa using (mem_epi_iff.mp hp)
          by_cases hpC : p.1 ∈ C
          · have hg_le : g p.1 ≤ (p.2 : WithTopBot 𝕜) := by
              simpa [hpC] using hp'
            have hgi :
                ∀ a ∈ s,
                  (a p.1 : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := by
              intro a ha
              have hi : (a p.1 : WithTopBot 𝕜) ≤ g p.1 := by
                change (fun a : E →ᵃ[𝕜] 𝕜 ↦ (a p.1 : WithTopBot 𝕜)) a ≤
                  (s.sup fun a : E →ᵃ[𝕜] 𝕜 ↦ (a p.1 : WithTopBot 𝕜) : WithTopBot 𝕜)
                exact Finset.le_sup_of_le ha le_rfl
              exact hi.trans hg_le
            refine ⟨hpC, ?_⟩
            intro a ha
            exact WithTopBot.coe_le_coe.mp (hgi a ha)
          · have htop : g p.1 + δ[𝕜](p.1 | C) = (⊤ : WithTopBot 𝕜) := by
              rw [indicator_of_notMem C hpC]
              simpa using WithTopBot.add_top_of_ne_bot (ne_of_gt (hg_bot p.1))
            have hpTop : (⊤ : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := by
              calc
                (⊤ : WithTopBot 𝕜) = g p.1 + δ[𝕜](p.1 | C) := htop.symm
                _ ≤ (p.2 : WithTopBot 𝕜) := by simpa [hpC] using hp'
            have hnot : ¬ (⊤ : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := by
              simp [top_le_iff]
            exact False.elim (hnot hpTop)
        · rintro ⟨hpC, hpIneq⟩
          have hg_le : g p.1 ≤ (p.2 : WithTopBot 𝕜) := by
            have hs' : s.sup (fun a ↦ (a p.1 : WithTopBot 𝕜)) ≤ (p.2 : WithTopBot 𝕜) := by
              rw [Finset.sup_le_iff]
              intro a ha
              exact WithTopBot.coe_le_coe.mpr (hpIneq a ha)
            simpa [g] using hs'
          have hp'' : g p.1 + δ[𝕜](p.1 | C) ≤ (p.2 : WithTopBot 𝕜) := by
            simpa [hpC] using hg_le
          exact mem_epi_iff.mpr hp''
      have hpoly_rhs :
          ({p : E × 𝕜 | p.1 ∈ C ∧ ∀ a ∈ s, a p.1 ≤ p.2} : Set (E × 𝕜)).IsPolyhedral 𝕜 :=
          by
        let fstMap : E × 𝕜 →ₗ[𝕜] E := LinearMap.fst 𝕜 E 𝕜
        let sndMap : E × 𝕜 →ₗ[𝕜] 𝕜 := LinearMap.snd 𝕜 E 𝕜
        let A : s → E × 𝕜 →ₗ[𝕜] 𝕜 :=
          fun i ↦ i.1.linear.comp fstMap - sndMap
        let γ : s → 𝕜 := fun i ↦ -(i.1 0)
        let hC_prod : (fstMap ⁻¹' C).IsPolyhedral 𝕜 := isPolyhedral_linear_preimage hC fstMap
        let hAff : ({p : E × 𝕜 | ∀ i : s, A i p ≤ γ i} : Set (E × 𝕜)).IsPolyhedral 𝕜 :=
          Set.isPolyhedral_setOf_forall_linear_le A γ
        have hEq :
            ({p : E × 𝕜 | p.1 ∈ C ∧ ∀ a ∈ s, a p.1 ≤ p.2} : Set (E × 𝕜)) =
              fstMap ⁻¹' C ∩ {p : E × 𝕜 | ∀ i : s, A i p ≤ γ i} := by
          ext p
          constructor
          · rintro ⟨hpC, hpIneq⟩
            refine ⟨hpC, ?_⟩
            intro i
            have hdecomp : i.1 p.1 = i.1.linear p.1 + i.1 0 := by
              simpa using congrFun (AffineMap.decomp i.1) p.1
            have hsum : i.1.linear p.1 + i.1 0 ≤ p.2 := by
              simpa [hdecomp] using hpIneq i.1 i.2
            have hle_sub : i.1.linear p.1 ≤ p.2 - i.1 0 := by
              have htmp := add_le_add_right hsum (- (i.1 0))
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            have hpi : i.1.linear p.1 - p.2 ≤ -(i.1 0) := by
              have htmp := add_le_add_right hle_sub (-p.2)
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            simpa [A, γ, fstMap, sndMap, LinearMap.fst_apply, LinearMap.snd_apply,
              LinearMap.comp_apply] using hpi
          · rintro ⟨hpC, hpIneq⟩
            refine ⟨hpC, ?_⟩
            intro a ha
            have hdecomp : a p.1 = a.linear p.1 + a 0 := by
              simpa using congrFun (AffineMap.decomp a) p.1
            have hpi : a.linear p.1 - p.2 ≤ -(a 0) := by
              simpa [A, γ, fstMap, sndMap, LinearMap.fst_apply, LinearMap.snd_apply,
                LinearMap.comp_apply] using hpIneq ⟨a, ha⟩
            have hle_sub : a.linear p.1 ≤ p.2 - a 0 := by
              have htmp := add_le_add_right hpi p.2
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            have hsum : a.linear p.1 + a 0 ≤ p.2 := by
              have htmp := add_le_add_right hle_sub (a 0)
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            simpa [hdecomp] using hsum
        rw [hEq]
        exact
          (Set.IsPolyhedral.inter (𝕜 := 𝕜) hC_prod hAff)
      have hpoly_epi :
          Set.IsPolyhedral 𝕜 (epi (fun x : E ↦ g x + δ[𝕜](x | C))) := by
        rw [hmem_epi]
        exact hpoly_rhs
      simpa using hpoly_epi
    · intro x
      change ⊥ < g x + δ[𝕜](x | C)
      by_cases hxC : x ∈ C
      · simpa [hxC] using hg_bot x
      · have htop : g x + δ[𝕜](x | C) = (⊤ : WithTopBot 𝕜) := by
          rw [indicator_of_notMem C hxC]
          simpa using WithTopBot.add_top_of_ne_bot (ne_of_gt (hg_bot x))
        rw [htop]
        simp

/-- Internal owner projection for Text 19.0.9:
polyhedrality of the epigraph needs no nonemptiness assumption on the affine family. -/
private theorem exists_finset_sup_affine_add_indicator_hasPolyhedralEpigraph
    {f : E → WithTopBot 𝕜}
    (hf :
      ∃ s : Finset (E →ᵃ[𝕜] 𝕜),
          ∃ C : Set E, C.IsPolyhedral 𝕜 ∧
            f = (fun x ↦ s.sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](· | C))) :
    f.HasPolyhedralEpigraph := by
  rcases hf with ⟨s, C, hC, rfl⟩
  by_cases hs : s.Nonempty
  · exact
      (exists_nonempty_finset_sup_affine_add_indicator_core
        ⟨s, hs, C, hC, rfl⟩).1
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    change Set.IsPolyhedral 𝕜
      (epi (fun x : E ↦
        ((∅ : Finset (E →ᵃ[𝕜] 𝕜)).sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](x | C))))
    have hbot :
        (fun x : E ↦
          ((∅ : Finset (E →ᵃ[𝕜] 𝕜)).sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](x | C))) =
          (fun _ : E ↦ (⊥ : WithTopBot 𝕜)) := by
      funext x
      simp
    rw [hbot]
    have hUniv : epi (fun x : E ↦ (⊥ : WithTopBot 𝕜)) = (Set.univ : Set (E × 𝕜)) := by
      ext p
      simp [mem_epi_iff]
    rw [hUniv]
    refine ⟨∅, ?_⟩
    ext p
    simp

namespace Function.HasPolyhedralEpigraph

/-- Text 19.0.9 owner-side bridge: a finite affine-supremum-plus-indicator
representation implies polyhedrality of the epigraph. -/
theorem of_exists_finset_sup_affine_add_indicator
    {f : E → WithTopBot 𝕜}
    (hf :
      ∃ s : Finset (E →ᵃ[𝕜] 𝕜),
          ∃ C : Set E, C.IsPolyhedral 𝕜 ∧
            f = (fun x ↦ s.sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](· | C))) :
    f.HasPolyhedralEpigraph := by
  exact exists_finset_sup_affine_add_indicator_hasPolyhedralEpigraph hf

end Function.HasPolyhedralEpigraph

namespace Function

/-- Text 19.0.9 codomain bridge: a nonempty finite affine-supremum-plus-indicator
representation excludes the value `⊥` pointwise. -/
theorem bot_lt_of_exists_finset_sup_affine_add_indicator
    {f : E → WithTopBot 𝕜}
    (hf :
      ∃ s : Finset (E →ᵃ[𝕜] 𝕜), s.Nonempty ∧
          ∃ C : Set E, C.IsPolyhedral 𝕜 ∧
            f = (fun x ↦ s.sup fun a ↦ (a x : WithTopBot 𝕜)) + (δ[𝕜](· | C))) :
    ∀ x, ⊥ < f x := by
  exact (exists_nonempty_finset_sup_affine_add_indicator_core hf).2

end Function

end
