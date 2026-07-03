import Mathlib
import Mathlib.Algebra.Order.Ring.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_19_0_9 (from Chap04) -/
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

/-! ### Text_19_0_10 (from Chap04) -/
open scoped BigOperators Rockafellar
open Function

noncomputable section

section

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 19.0.10 defines finitely generated convex functions through finite
  generation of their scalar epigraphs, and concretely presents them by finitely many epigraph
  points and directions.
- `core/canonical`: the owner abstractions are `Set.IsFinitelyGeneratedConvex` for the epigraph in
  `E × 𝕜`, the function-side owner `Function.HasFinitelyGeneratedConvexEpigraph`,
  `Function.pointDirectionInfFamily` for finite-family generators, and
  `Function.verticalInfimum` for the function attached to an epigraph set.
- `bridge/view`: explicit `Finset` point and direction families recover the textbook coefficient
  formula as a source-facing specialization of the finite-family owner.

Domain-style sampling used here:
- `Set.IsFinitelyGeneratedConvex`;
- `mixedConvexHull`;
- `Function.verticalInfimum`;
- `convexHullFamilyFunction_eq_sInf_convexCombination_values`.

Primitive data vs derived API:
- primitive source-facing owner data: the finitely generated intrinsic epigraph owner
  `f.HasFinitelyGeneratedConvexEpigraph`;
- primitive finite-family data: point and direction generators indexed by finite types, together
  with their height coordinates;
- source-facing bridge data: `Finset`-indexed point and direction generators;
- derived API: the attached function and coefficient-form specification theorems.

Ambient minimization:
- the epigraph-side owner `Function.HasFinitelyGeneratedConvexEpigraph` itself only needs the
  weaker scalar-ordered module structure already used by `epi` and
  `Set.IsFinitelyGeneratedConvex`;
- the explicit point-and-direction presentation and the `verticalInfimum` bridge below need the
  additional completeness assumption required by `Function.verticalInfimum`;
- the degenerate `f = ⊤` case is represented directly by the empty point family already allowed by
  the set-side owner `Set.IsFinitelyGeneratedConvex`.

Layer target: the public predicate is the epigraph-side owner notion, the canonical explicit
generator owner is finite-family (`pointDirectionInfFamily`), and the `Finset` surface is kept as
the source-facing bridge built directly from `mixedConvexHull`.
-/

section hasFinitelyGeneratedConvexEpigraph

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-- Text 19.0.10 owner predicate: a function has finitely generated convex epigraph when its
scalar epigraph is a finitely generated convex subset of `E × 𝕜`. -/
abbrev HasFinitelyGeneratedConvexEpigraph (f : E → WithTopBot 𝕜) : Prop :=
  (epi f).IsFinitelyGeneratedConvex 𝕜

namespace HasFinitelyGeneratedConvexEpigraph

/-- Owner-side theorem: `HasFinitelyGeneratedConvexEpigraph` is exactly finite generation of the
intrinsic epigraph. -/
theorem isFinitelyGeneratedConvex {f : E → WithTopBot 𝕜}
    (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    (epi f).IsFinitelyGeneratedConvex 𝕜 :=
  hf

end HasFinitelyGeneratedConvexEpigraph

end Function

end hasFinitelyGeneratedConvexEpigraph

section pointDirectionInfFamily

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable [ConditionallyCompleteLattice 𝕜]

variable {ιp : Type u}
variable (points : ιp → E) (pointValues : ιp → 𝕜)
variable {ιd : Type u}
variable (directions : ιd → E) (directionValues : ιd → 𝕜)

namespace Function

private def pointDirectionEpigraphFamily : Set (E × 𝕜) :=
    mconv[𝕜]((Set.range fun i : ιp ↦ (points i, pointValues i))
      | Set.range fun j : ιd ↦ (directions j, directionValues j))

/-- Canonical finite-family owner form: the function generated by finitely many epigraph points
and directions, indexed by finite types, is the vertical infimum of their mixed epigraph hull. -/
def pointDirectionInfFamily : E → WithTopBot 𝕜 :=
  verticalInfimum
    (pointDirectionEpigraphFamily points pointValues directions directionValues)

-- Proof sketch: the mixed epigraph hull records exactly the admissible convex combinations of the
-- point generators together with conic combinations of the direction generators. Applying
-- `verticalInfimum` to that hull recovers the displayed coefficient formula for the vertical fiber
-- above `x`.
/-- Evaluating `pointDirectionInfFamily` at `x` gives the infimum over all finite affine-plus-
conic presentations of `x` using the prescribed point and direction generators. -/
theorem pointDirectionInfFamily_eq_sInf
    [Fintype ιd]
    (x : E) :
    pointDirectionInfFamily points pointValues directions directionValues x =
      sInf
        {r : WithTopBot 𝕜 |
          ∃ pointWeights : StdSimplex 𝕜 ιp,
            ∃ directionWeights : ιd → {a : 𝕜 // 0 ≤ a},
              x =
                  pointWeights.sum (fun i a ↦ a • points i) +
                    ∑ j : ιd, (directionWeights j : 𝕜) • directions j ∧
                r =
                  pointWeights.sum (fun i a ↦ ((a * pointValues i : 𝕜) : WithTopBot 𝕜)) +
                  ∑ j : ιd,
                    (((directionWeights j : 𝕜) * directionValues j : 𝕜) :
                      WithTopBot 𝕜)} := sorry

end Function

end pointDirectionInfFamily

section pointDirectionInf

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable [ConditionallyCompleteLattice 𝕜]

variable (points : Finset E) (pointValues : points → 𝕜)
variable (directions : Finset E) (directionValues : directions → 𝕜)

namespace Function

/-- The function generated by finitely many epigraph points and finitely many epigraph directions
is the vertical-infimum function of their mixed epigraph hull.

This is the source-facing `Finset` bridge of `pointDirectionInfFamily`. -/
def pointDirectionInf : E → WithTopBot 𝕜 :=
  pointDirectionInfFamily
    (fun i : points ↦ (i : E)) pointValues
    (fun j : directions ↦ (j : E)) directionValues

-- Proof sketch: the mixed epigraph hull records exactly the admissible convex combinations of the
-- point generators together with conic combinations of the direction generators. Applying
-- `verticalInfimum` to that hull recovers the displayed coefficient formula for the vertical fiber
-- above `x`.
/-- Evaluating `pointDirectionInf` at `x` gives the infimum over all finite affine-plus-
conic presentations of `x` using the prescribed point and direction generators. -/
theorem pointDirectionInf_eq_sInf
    (x : E) :
    pointDirectionInf points pointValues directions directionValues x =
      sInf
        {r : WithTopBot 𝕜 |
          ∃ pointWeights : StdSimplex 𝕜 points,
            ∃ directionWeights : directions → {a : 𝕜 // 0 ≤ a},
              x =
                  pointWeights.sum (fun i a ↦ a • (i : E)) +
                    ∑ j : directions, (directionWeights j : 𝕜) • (j : E) ∧
                r =
                  pointWeights.sum (fun i a ↦ ((a * pointValues i : 𝕜) : WithTopBot 𝕜)) +
                  ∑ j : directions,
                    (((directionWeights j : 𝕜) * directionValues j : 𝕜) : WithTopBot 𝕜)} := by
  simpa [pointDirectionInf] using
    (pointDirectionInfFamily_eq_sInf
      (points := fun i : points ↦ (i : E)) (pointValues := pointValues)
      (directions := fun j : directions ↦ (j : E)) (directionValues := directionValues)
      (x := x))

end Function

end pointDirectionInf

section pointDirectionInfBridge

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

namespace Function

namespace HasFinitelyGeneratedConvexEpigraph

section pointDirectionInfFamily

variable [ConditionallyCompleteLattice 𝕜]
variable {ιp : Type u} [Finite ιp]
variable (points : ιp → E) (pointValues : ιp → 𝕜)
variable {ιd : Type u} [Finite ιd]
variable (directions : ιd → E) (directionValues : ιd → 𝕜)

-- Proof sketch: the point and direction families define finite subsets of `E × 𝕜`; their mixed
-- convex hull is the epigraph model used in `pointDirectionInfFamily`, so the epigraph of the
-- attached vertical-infimum function is finitely generated by the owner predicate above.
private theorem epi_pointDirectionInfFamily_isFinitelyGeneratedConvex
    : Set.IsFinitelyGeneratedConvex 𝕜
        (epi (pointDirectionInfFamily points pointValues directions directionValues)) := sorry

/-- Any explicit finite-family epigraph model yields a finitely generated convex function. -/
theorem of_pointDirectionInfFamily
    : HasFinitelyGeneratedConvexEpigraph
        (pointDirectionInfFamily points pointValues directions directionValues) :=
  epi_pointDirectionInfFamily_isFinitelyGeneratedConvex
    points pointValues directions directionValues

end pointDirectionInfFamily

section pointDirectionInf

variable [ConditionallyCompleteLattice 𝕜]
variable (points : Finset E) (pointValues : points → 𝕜)
variable (directions : Finset E) (directionValues : directions → 𝕜)

-- Proof sketch: the point and direction families define finite subsets of `E × 𝕜`; their mixed
-- convex hull is the epigraph model used in `pointDirectionInf`, so the epigraph of the
-- attached vertical-infimum function is finitely generated by the owner predicate above.
private theorem epi_pointDirectionInf_isFinitelyGeneratedConvex
    : Set.IsFinitelyGeneratedConvex 𝕜
        (epi (pointDirectionInf points pointValues directions directionValues)) := by
  simpa [Function.pointDirectionInf] using
    (epi_pointDirectionInfFamily_isFinitelyGeneratedConvex
      (fun i : points ↦ (i : E)) pointValues
      (fun j : directions ↦ (j : E)) directionValues)

/-- Any explicit finite point-direction epigraph model yields a finitely generated convex
function. -/
theorem of_pointDirectionInf
    : HasFinitelyGeneratedConvexEpigraph
        (pointDirectionInf points pointValues directions directionValues) :=
  epi_pointDirectionInf_isFinitelyGeneratedConvex points pointValues directions directionValues

end pointDirectionInf

section reconstruct

variable [ConditionallyCompleteLattice 𝕜] [NoBotOrder 𝕜]

-- Proof sketch: unpack the owner witness
-- `(epi f).IsFinitelyGeneratedConvex 𝕜` into finite point and direction sets in `E × 𝕜`.
-- Split their `E × 𝕜` coordinates into `E`-parts and `𝕜`-parts, rewrite the resulting epigraph
-- model as an explicit finite-family point-direction generator form, and apply
-- `verticalInfimum_epi`.
/-- Intrinsic reconstruction at the epigraph owner layer: a finitely generated convex epigraph
function is the vertical infimum of a mixed hull generated by finitely many epigraph points and
finitely many epigraph directions in `Module.Ray 𝕜 (E × 𝕜)`. -/
private theorem exists_eq_verticalInfimum_mixedConvexHull_of_epi_isFinitelyGeneratedConvex
    {f : E → WithTopBot 𝕜} (hf : (epi f).IsFinitelyGeneratedConvex 𝕜) :
    ∃ points : Finset (E × 𝕜),
      ∃ directions : Finset (Module.Ray 𝕜 (E × 𝕜)),
        f = verticalInfimum
          (mconv[𝕜]((points : Set (E × 𝕜))
            | ray (directions : Set (Module.Ray 𝕜 (E × 𝕜))))) := sorry

/-- Source-facing reconstruction wrapper: a function with finitely generated convex epigraph is
the vertical infimum of a mixed hull generated by finitely many epigraph points and directions. -/
theorem exists_eq_verticalInfimum_mixedConvexHull
    {f : E → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    ∃ points : Finset (E × 𝕜),
      ∃ directions : Finset (Module.Ray 𝕜 (E × 𝕜)),
        f = verticalInfimum
          (mconv[𝕜]((points : Set (E × 𝕜))
            | ray (directions : Set (Module.Ray 𝕜 (E × 𝕜))))) :=
  exists_eq_verticalInfimum_mixedConvexHull_of_epi_isFinitelyGeneratedConvex
    hf.isFinitelyGeneratedConvex

/-- The source-facing point-direction presentation attached to a finitely generated convex
function is recovered from the epigraph-side owner predicate; the empty-epigraph case is covered
by the empty point family. -/
private theorem exists_eq_pointDirectionInf_of_epi_isFinitelyGeneratedConvex
    {f : E → WithTopBot 𝕜} (hf : (epi f).IsFinitelyGeneratedConvex 𝕜) :
    ∃ points : Finset E,
      ∃ pointValues : points → 𝕜,
        ∃ directions : Finset E,
          ∃ directionValues : directions → 𝕜,
            f = pointDirectionInf points pointValues directions directionValues := sorry

/-- Canonical finite-family reconstruction: a finitely generated convex epigraph function admits
an explicit finite-family point-direction presentation over finite index types. -/
private theorem exists_eq_pointDirectionInfFamily_of_epi_isFinitelyGeneratedConvex
    {f : E → WithTopBot 𝕜} (hf : (epi f).IsFinitelyGeneratedConvex 𝕜) :
    ∃ (ιp : Type u), ∃ _ : Finite ιp, ∃ points : ιp → E, ∃ pointValues : ιp → 𝕜,
      ∃ (ιd : Type u), ∃ _ : Finite ιd,
        ∃ directions : ιd → E, ∃ directionValues : ιd → 𝕜,
        f = pointDirectionInfFamily points pointValues directions directionValues := sorry

/-- Source-facing wrapper from finite generation to the canonical finite-family presentation over
finite index types. -/
theorem exists_eq_pointDirectionInfFamily
    {f : E → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    ∃ (ιp : Type u), ∃ _ : Finite ιp, ∃ points : ιp → E, ∃ pointValues : ιp → 𝕜,
      ∃ (ιd : Type u), ∃ _ : Finite ιd,
        ∃ directions : ιd → E, ∃ directionValues : ιd → 𝕜,
        f = pointDirectionInfFamily points pointValues directions directionValues :=
  exists_eq_pointDirectionInfFamily_of_epi_isFinitelyGeneratedConvex
    hf.isFinitelyGeneratedConvex

/-- The source-facing point-direction presentation attached to a finitely generated convex
function is recovered from the epigraph-side owner predicate; the empty-epigraph case is covered
by the empty point family. -/
theorem exists_eq_pointDirectionInf
    {f : E → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    ∃ points : Finset E,
      ∃ pointValues : points → 𝕜,
        ∃ directions : Finset E,
          ∃ directionValues : directions → 𝕜,
            f = pointDirectionInf points pointValues directions directionValues :=
  exists_eq_pointDirectionInf_of_epi_isFinitelyGeneratedConvex
    hf.isFinitelyGeneratedConvex

end reconstruct

end HasFinitelyGeneratedConvexEpigraph

end Function

end pointDirectionInfBridge

end

/-! ### Text_19_0_11 (from Chap04) -/
noncomputable section

open scoped BigOperators

section

variable {ι : Type*} [Finite ι]
variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]

local noncomputable instance : Fintype ι := Fintype.ofFinite ι

local notation "E" => ι → 𝕜
local notation "l1Gauge" => (coordinateL1Gauge ι : E → WithTopBot 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.11 is the finite-coordinate example asserting that the coordinate
  `ℓ¹` gauge is polyhedral convex.
  `coordinateL1Gauge ι` from `Chap03.Text_15_0_13` and the finite sign-vector half-space
  presentation of its epigraph.
- `core/canonical`: the Chapter 19 owner predicate is `Function.HasPolyhedralEpigraph`.
- `bridge/view`: the epigraph is presented as the intersection of the finitely many half-spaces
  indexed by sign choices `ε : ι → Bool`; no extra wrapper owner is needed.

Domain-style sampling used here:
- `coordinateL1Gauge` from `Chap03.Text_15_0_13`;
- `Set.isPolyhedral_setOf_forall_linear_le` from `Chap04.Text_19_0_1`;
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Set.IsPolyhedral` from `Chap01.Definition_2_1_2`.

Primitive data vs derived API:
- primitive owner: the function `coordinateL1Gauge ι`;
- derived API: the polyhedral-epigraph predicate on that owner;
- bridge data: the private sign-indexed linear forms cutting out `epi (coordinateL1Gauge ι)`.

Layer target: `source-facing`, with the public statement kept directly on the canonical owner
`coordinateL1Gauge` rather than on a parallel local coordinate-sum wrapper.
-/

private def coordinateL1EpigraphLinearMap (ε : ι → Bool) : (E × 𝕜) →ₗ[𝕜] 𝕜 :=
  (∑ i, if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
      else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) -
    LinearMap.snd 𝕜 E 𝕜

omit [LinearOrder 𝕜] in
@[simp] private theorem coordinateL1EpigraphLinearMap_apply (ε : ι → Bool) (p : E × 𝕜) :
    coordinateL1EpigraphLinearMap ε p =
      (∑ i, if ε i then p.1 i else -p.1 i) - p.2 := by
  rw [coordinateL1EpigraphLinearMap, LinearMap.sub_apply, LinearMap.snd_apply]
  have hsumApply :
      (∑ i, if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
          else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p =
        ∑ i,
          (if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
            else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p := by
    simp [LinearMap.sum_apply]
  rw [hsumApply]
  have hsum :
      ∑ i,
          (if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
            else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p =
        ∑ i, if ε i then p.1 i else -p.1 i := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hε : ε i
    · simp [hε, LinearMap.comp_apply, LinearMap.fst_apply]
    · simp [hε, LinearMap.comp_apply, LinearMap.fst_apply]
  rw [hsum]

private theorem sum_abs_le_iff_forall_signs_le (x : E) (t : 𝕜) :
    (∑ i, |x i|) ≤ t ↔ ∀ ε : ι → Bool, ∑ i, (if ε i then x i else -x i) ≤ t := by
  constructor
  · intro h ε
    calc
      ∑ i, (if ε i then x i else -x i) ≤ ∑ i, |x i| := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        by_cases hε : ε i
        · simp [hε, le_abs_self]
        · simp [hε, neg_le_abs]
      _ ≤ t := h
  · intro h
    let ε : ι → Bool := fun i ↦ decide (0 ≤ x i)
    have hε : ∑ i, (if ε i then x i else -x i) ≤ t := h ε
    have hEq : ∑ i, (if ε i then x i else -x i) = ∑ i, |x i| := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hx : 0 ≤ x i
      · simp [ε, hx, abs_of_nonneg hx]
      · simp [ε, hx, abs_of_neg (lt_of_not_ge hx)]
    simpa [hEq] using hε

private theorem epi_coordinateL1Gauge_eq_setOf_forall_signLinearMap :
    epi l1Gauge =
      {p : E × 𝕜 |
        ∀ ε : ι → Bool, coordinateL1EpigraphLinearMap ε p ≤ 0} := by
  ext p
  rw [mem_epi_iff]
  change ((((∑ i, |p.1 i|) : 𝕜) : WithTopBot 𝕜) ≤ ((p.2 : 𝕜) : WithTopBot 𝕜)) ↔ _
  rw [WithBotTop.coe_le_coe]
  constructor
  · intro hp ε
    rw [coordinateL1EpigraphLinearMap_apply]
    exact sub_nonpos.mpr ((sum_abs_le_iff_forall_signs_le p.1 p.2).1 hp ε)
  · intro hp
    refine (sum_abs_le_iff_forall_signs_le p.1 p.2).2 fun ε ↦ ?_
    exact sub_nonpos.mp <| by simpa [coordinateL1EpigraphLinearMap_apply] using hp ε

/-- Text 19.0.11, owner form: on any finite ordered-ring coordinate space, the coordinate `ℓ¹`
gauge has polyhedral epigraph. Specializing `𝕜 = ℝ` and `ι = Fin n` recovers the textbook
`R^n` statement. -/
theorem coordinateL1Gauge_hasPolyhedralEpigraph :
    (l1Gauge).HasPolyhedralEpigraph := by
  change (epi l1Gauge).IsPolyhedral 𝕜
  rw [epi_coordinateL1Gauge_eq_setOf_forall_signLinearMap]
  simpa using
    (Set.isPolyhedral_setOf_forall_linear_le (I := ι → Bool)
      coordinateL1EpigraphLinearMap
      (fun _ ↦ (0 : 𝕜)))

end

/-! ### Text_19_0_12 (from Chap04) -/
noncomputable section

section OwnerForm

open scoped BigOperators GaugePolar

variable {ι : Type*} [Finite ι]
variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]

local noncomputable instance : Fintype ι := Fintype.ofFinite ι

local notation "E" => ι → 𝕜
local notation "linftyGauge" =>
  Function.toWithTopBot (linftyNorm : E → 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.12 is the finite-coordinate Tchebycheff norm
  `x ↦ max_i |x i|`, whose project owner is `linftyNorm`, viewed on the epigraph codomain as
  `linftyGauge`.
- `core/canonical`: the owner predicate is `Function.HasPolyhedralEpigraph`, and the relevant
  finite half-space owner theorem is `Set.isPolyhedral_setOf_forall_linear_le`.
- `bridge/view`: the polar presentation `(coordinateL1Gauge ι)ᵒ = linftyGauge` is retained only as
  a separate stronger-layer bridge below; the main owner theorem here stays directly on the finite
  `ℓ∞` owner.

Domain-style sampling used here:
- `linftyNorm`;
- `coordinateL1Gauge`;
- `gauge_polar_coordinateL1Gauge_eq_linftyNorm`;
- `Set.isPolyhedral_setOf_forall_linear_le`;
- `Function.HasPolyhedralEpigraph`.

Primitive data vs derived API:
- no new public primitive owner is introduced;
- the only local implementation data is a private finite family of signed coordinate half-space
  maps cutting out `epi linftyGauge`;
- the public output is the owner theorem that `linftyGauge` has polyhedral epigraph.
-/

private def linftyEpigraphLinearMap : Option (Bool × ι) → (E × 𝕜) →ₗ[𝕜] 𝕜
  | none => -LinearMap.snd 𝕜 E 𝕜
  | some (b, i) =>
      (if b then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
        else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) -
        LinearMap.snd 𝕜 E 𝕜

omit [LinearOrder 𝕜] in
@[simp] private theorem linftyEpigraphLinearMap_apply (ε : Option (Bool × ι)) (p : E × 𝕜) :
    linftyEpigraphLinearMap ε p =
      match ε with
      | none => -p.2
      | some (b, i) => (if b then p.1 i else -p.1 i) - p.2 := by
  cases ε with
  | none =>
      simp [linftyEpigraphLinearMap]
  | some ε =>
      rcases ε with ⟨b, i⟩
      by_cases hb : b <;> simp [linftyEpigraphLinearMap, hb, LinearMap.comp_apply]

private theorem epi_linftyGauge_eq_setOf_forall_linearMap :
    epi linftyGauge =
      {p : E × 𝕜 | ∀ ε : Option (Bool × ι), linftyEpigraphLinearMap ε p ≤ 0} := by
  ext p
  rcases p with ⟨x, t⟩
  rw [mem_epi_iff]
  change (((linftyNorm x : 𝕜) : WithTopBot 𝕜) ≤ ((t : 𝕜) : WithTopBot 𝕜)) ↔ _
  rw [WithBotTop.coe_le_coe]
  by_cases hι : Nonempty ι
  · letI := hι
    constructor
    · intro hp ε
      cases ε with
      | none =>
          have hlin_nonneg : 0 ≤ linftyNorm x := by
            obtain ⟨i⟩ := hι
            rw [linftyNorm_eq_sup'_univ_abs x]
            exact le_trans (abs_nonneg (x i))
              (Finset.le_sup' (fun j : ι ↦ |x j|) (Finset.mem_univ i))
          have hp_nonneg : 0 ≤ t := hlin_nonneg.trans hp
          simpa [linftyEpigraphLinearMap] using (neg_nonpos.mpr hp_nonneg)
      | some ε =>
          rcases ε with ⟨b, i⟩
          have hi : |x i| ≤ linftyNorm x := by
            rw [linftyNorm_eq_sup'_univ_abs x]
            exact Finset.le_sup' (fun j : ι ↦ |x j|) (Finset.mem_univ i)
          by_cases hb : b
          · have hsigned : x i ≤ t := (le_abs_self _).trans (hi.trans hp)
            simpa [linftyEpigraphLinearMap, hb, LinearMap.comp_apply] using sub_nonpos.mpr hsigned
          · have hsigned : -x i ≤ t := (neg_le_abs _).trans (hi.trans hp)
            simpa [linftyEpigraphLinearMap, hb, LinearMap.comp_apply] using sub_nonpos.mpr hsigned
    · intro hp
      rw [linftyNorm_eq_sup'_univ_abs x, Finset.sup'_le_iff]
      intro i _
      have hpos : x i ≤ t := by
        exact sub_nonpos.mp <| by
          simpa [linftyEpigraphLinearMap, LinearMap.comp_apply] using hp (some (true, i))
      have hneg : -x i ≤ t := by
        exact sub_nonpos.mp <| by
          simpa [linftyEpigraphLinearMap, LinearMap.comp_apply] using hp (some (false, i))
      exact abs_le.mpr ⟨by simpa using (neg_le_neg hneg), hpos⟩
  · have hι_empty : IsEmpty ι := not_nonempty_iff.mp hι
    have hcard : Fintype.card ι = 0 := Fintype.card_eq_zero_iff.mpr hι_empty
    have hx0 : x = (0 : E) := Subsingleton.elim _ _
    subst x
    constructor
    · intro hp ε
      cases ε with
      | none =>
          have ht_nonneg : 0 ≤ t := by
            simpa [linftyNorm, hcard] using hp
          simpa [linftyEpigraphLinearMap] using (neg_nonpos.mpr ht_nonneg)
      | some ε =>
          rcases ε with ⟨b, i⟩
          exact False.elim (hι_empty.false i)
    · intro hp
      have hp_nonneg : 0 ≤ t := by
        simpa [linftyEpigraphLinearMap] using hp none
      simpa [linftyNorm, hcard] using hp_nonneg

-- Proof sketch: `epi linftyGauge` is the finite intersection of the signed coordinate half-spaces
-- `±x i ≤ t`; the extra `none` index supplies the empty-coordinate branch `0 ≤ t`.
/-- Text 19.0.12, owner form: the coordinate `ℓ∞` norm, viewed in the chapter's epigraph
codomain, has polyhedral epigraph. Specializing `𝕜 = ℝ` and `ι = Fin n` recovers the textbook
`R^n` statement. -/
theorem linftyNorm_hasPolyhedralEpigraph :
    (linftyGauge).HasPolyhedralEpigraph := by
  change (epi linftyGauge).IsPolyhedral 𝕜
  rw [epi_linftyGauge_eq_setOf_forall_linearMap]
  simpa using
    (Set.isPolyhedral_setOf_forall_linear_le
      linftyEpigraphLinearMap
      (fun _ ↦ (0 : 𝕜)))

end OwnerForm

section PolarBridge

open scoped BigOperators GaugePolar

variable {ι : Type*} [Finite ι]
variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]

local noncomputable instance : Fintype ι := Fintype.ofFinite ι

local notation "E" => ι → 𝕜

local instance : HasPairing E E 𝕜 where
  pairing x y := ∑ i, x i * y i
local instance : HasPairing E E (WithTopBot 𝕜) := instHasPairingWithBotTop

/-
The source text also presents the Tchebycheff norm as the polar of the coordinate `ℓ¹` gauge.
That bridge still depends on the chapter's stronger polar owner layer, so the companion theorem is
kept separate from the weaker finite-maximum owner theorem above.
-/
/-- Text 19.0.12, polar companion form: the Tchebycheff norm on a finite coordinate space,
written as the polar gauge of `coordinateL1Gauge`, has polyhedral epigraph. Specializing
`𝕜 = ℝ` and `ι = Fin n` recovers the textbook `R^n` formulation. -/
theorem coordinateL1Gauge_polar_hasPolyhedralEpigraph :
    ((coordinateL1Gauge ι : E → WithTopBot 𝕜)ᵒ).HasPolyhedralEpigraph := by
  simpa [gauge_polar_coordinateL1Gauge_eq_linftyNorm] using
    linftyNorm_hasPolyhedralEpigraph

end PolarBridge

/-! ### Text_19_0_13 (from Chap04) -/
section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.13 is stated at the intrinsic witness owner
  `linearHyperplaneWitnessSet`; this keeps the public theorem independent of any coordinate model
  and independent of any concrete dual-space owner.
- `core/canonical`: the owner abstractions are pairing-parametric `Set.IsPolyhedral`,
  `linearHyperplaneWitnessSet`, the generic closedness obstruction theorem
  `convexHull_linearHyperplaneWitnessSet_not_isClosed`; the polyhedral
  contradiction is packaged as `convexHull_linearHyperplaneWitnessSet_not_isPolyhedral`.
- `bridge/view`: no extra concrete-model bridge is needed in this file; polyhedral-closedness is
  consumed directly from the pairing-continuity owner layer.

Primitive data vs derived API:
- primitive witness data: one linear functional `f : V →ₗ[𝕜] 𝕜` defining a hyperplane,
  one nonzero in-hyperplane direction `u`, and one off-hyperplane point `y`;
- bridge realization: the only bridge step is
  `Set.IsPolyhedral.isClosed_of_forall_continuous`, used at the primitive
  `HasContinuousPairing` owner layer;
- derived API: the source-facing theorem is intrinsic (`linearHyperplaneWitnessSet`) and avoids
  finite-dimensional or concrete-dual specialization.

Layer target: `source-facing`.
-/

/-- Text 19.0.13 (source-facing canonical owner form): if one adjoins an off-hyperplane point to
a hyperplane, the resulting convex hull cannot be polyhedral. -/
theorem convexHull_linearHyperplaneWitnessSet_not_isPolyhedral
    {V : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    [ContinuousAdd V] [ContinuousSMul 𝕜 V]
    {Y : Type*} [HasPairing V Y 𝕜] [HasContinuousPairing V Y 𝕜]
    {f : V →ₗ[𝕜] 𝕜} {u y : V}
    (hu : u ≠ 0)
    (hu_hyperplane : u ∈ linearHyperplane f (0 : 𝕜))
    (hy_offHyperplane : y ∉ linearHyperplane f (0 : 𝕜)) :
    ¬ (convexHull 𝕜 (linearHyperplaneWitnessSet f y)).IsPolyhedral 𝕜 Y := by
  intro hpoly
  have hclosed : IsClosed (convexHull 𝕜 (linearHyperplaneWitnessSet f y)) :=
    Set.IsPolyhedral.isClosed_of_forall_continuous (𝕜 := 𝕜) (E := V) (Y := Y) hpoly
      (fun y' ↦ HasContinuousPairing.continuous_pairing_left (X := V) (Y := Y) (𝕜 := 𝕜) y')
  exact convexHull_linearHyperplaneWitnessSet_not_isClosed hu
    hu_hyperplane hy_offHyperplane
    hclosed

end

/-! ### Text_19_0_14 (from Chap04) -/
section

open scoped Pointwise Rockafellar

open Set

/-!
Source/core/bridge triage:

- `source-facing`: the item fixes a polytope `C ⊆ ℝ^n`, a nonempty subset `S ⊆ C`, defines the
  translation parameter set `D = {y | S + y = C}`, and asserts that `D` is again a polytope.
- `core/canonical`: the project owner predicate for the conclusion is `Set.IsPolytope`, while the
  owner abstraction for set translation is `Set.vaddSet`, written `y +ᵥ S`, and the owner
  abstraction for translation invariance is `Set.lineal`.
- `bridge/view`: the Chapter 2 lineality theorem offers both intrinsic translation and
  singleton-addition views; this file keeps the source-facing bridge at the intrinsic
  translation-equality layer `z +ᵥ C = C` when relating the parameter set to `lin[R](C)`.

Domain-style sampling used here:
- `Set.vaddSet`;
- `Set.IsPolytope`;
- `Set.lineal`;
- `Convex.mem_lineal_iff_vadd_eq_self`;
- the source-facing translation notation `y +ᵥ S`.

Primitive data vs derived API:
- primitive source-facing data: the subset `S`, the ambient polytope `C`, and the translation set
  of parameters sending `S` onto `C`, exposed below as `Set.translationCover S C`;
- derived API: the bridge from that parameter set to `lin[R](C)`, its canonical translation
  description `y₀ +ᵥ lin[R](C)`, and the theorem that this parameter set is a polytope.

Ambient level: the translation-cover owner itself lives on the intrinsic affine-action layer
`[VAdd E P]` rather than the stronger additive-group-on-points layer. The lineality bridge uses
the Chapter 2 scalar layer for `lin[R](C)` and convexity over `R`, while the final polytope
theorem uses boundedness of finite convex hulls in ordered normed-field spaces. In each case,
specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook formulation.

Layer target: `source-facing`.
-/

namespace Set

variable {E P : Type*} [VAdd E P]

/- The set of translation parameters that send `S` exactly onto `C`. -/
def translationCover (S C : Set P) : Set E :=
  {y | y +ᵥ S = C}

/- Membership in `translationCover S C` means that translating `S` by `y` yields exactly
`C`. -/
@[simp]
theorem mem_translationCover_iff {S C : Set P} {y : E} :
    y ∈ translationCover S C ↔ y +ᵥ S = C :=
  Iff.rfl

end Set

variable {E : Type*} [AddCommGroup E]

variable {R : Type*} [Zero R] [LE R] [SMul R E]

-- Proof sketch: if `y₀ ∈ translationCover S C`, then
-- `y +ᵥ S = C` is equivalent to `(y - y₀) +ᵥ C = C`; bridge this to
-- `Set.mem_lineal_iff_vadd_eq_self` at the intrinsic translation-invariance layer.
/-- Primitive bridge form: once one translation parameter `y₀` sending `S` onto `C` is fixed, the
other parameters are exactly the translate of the lineality space of `C` by `y₀`, under the
recession/translation bridge hypothesis. -/
theorem mem_translationCover_iff_sub_mem_lineal_of_hrec
    {S C : Set E} (hrec : ∀ z : E, z ∈ 0⁺[R] C ↔ z +ᵥ C ⊆ C) {y₀ y : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    y ∈ translationCover S C ↔ y - y₀ ∈ lin[R](C) := by
  rw [Set.mem_translationCover_iff] at hy₀
  have hshift : (y - y₀) +ᵥ C = y +ᵥ S := by
    rw [← hy₀]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases hu with ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨y₀ +ᵥ s, ?_, by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
      exact ⟨s, hs, rfl⟩
  rw [Set.mem_lineal_iff_vadd_eq_self hrec]
  constructor
  · intro hy
    calc
      (y - y₀) +ᵥ C = y +ᵥ S := hshift
      _ = C := hy
  · intro hy
    rw [Set.mem_translationCover_iff]
    calc
      y +ᵥ S = (y - y₀) +ᵥ C := hshift.symm
      _ = C := hy

/-- With a fixed parameter `y₀` sending `S` onto `C`, the whole translation cover set is the
canonical translate `y₀ +ᵥ lin[R](C)`, under the recession/translation bridge hypothesis. -/
theorem translationCover_eq_vadd_lineal_of_hrec
    {S C : Set E} (hrec : ∀ z : E, z ∈ 0⁺[R] C ↔ z +ᵥ C ⊆ C) {y₀ : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    translationCover S C = y₀ +ᵥ lin[R](C) := by
  ext y
  rw [Set.mem_vadd_set]
  constructor
  · intro hy
    exact ⟨y - y₀, (mem_translationCover_iff_sub_mem_lineal_of_hrec hrec hy₀).mp hy, by
      simp [vadd_eq_add, sub_eq_add_neg]⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_translationCover_iff_sub_mem_lineal_of_hrec hrec hy₀).mpr <| by
      simpa [vadd_eq_add, sub_eq_add_neg] using hz

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
variable [Module R E]

/-- Convex specialization of `mem_translationCover_iff_sub_mem_lineal_of_hrec`. -/
theorem mem_translationCover_iff_sub_mem_lineal
    {S C : Set E} (hC_convex : Convex R C) {y₀ y : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    y ∈ translationCover S C ↔ y - y₀ ∈ lin[R](C) := by
  exact mem_translationCover_iff_sub_mem_lineal_of_hrec
    (hrec := fun z => hC_convex.mem_recessionCone_iff_vadd_subset_self z) hy₀

/-- Convex specialization of `translationCover_eq_vadd_lineal_of_hrec`. -/
theorem translationCover_eq_vadd_lineal
    {S C : Set E} (hC_convex : Convex R C) {y₀ : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    translationCover S C = y₀ +ᵥ lin[R](C) := by
  exact translationCover_eq_vadd_lineal_of_hrec
    (hrec := fun z => hC_convex.mem_recessionCone_iff_vadd_subset_self z) hy₀

-- Proof sketch: if `translationCover S C` is empty, it is the convex hull of the empty finite
-- set and hence a polytope. Otherwise choose `y₀` in it and rewrite the whole set as
-- `y₀ +ᵥ lin[K](C)` via `translationCover_eq_vadd_lineal`. For a
-- bounded convex set, a nonzero lineality direction would then keep translating any point
-- of `C` along an unbounded arithmetic progression inside `C`, impossible for a bounded set.
-- Hence `lin[K](C) = {0}`, so the
-- translation cover set is either empty or the singleton `{y₀}`, and in either case it is a
-- polytope. The polytope corollary only uses the canonical boundedness of finite convex hulls.
-- The textbook hypothesis `S ⊆ C` is redundant for this conclusion and is omitted.
section Normed

variable {K : Type*} [NormedField K] [LinearOrder K]
  [IsStrictOrderedRing K] [FloorSemiring K] [NormSMulClass ℤ K]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] in
private theorem not_isBounded_range_add_natCast_smul (x y : V) (hy : y ≠ 0) :
    ¬ Bornology.IsBounded (Set.range fun n : ℕ ↦ x + (n : K) • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : V)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + (n : K) • y‖ ≤ R := by
    have hxR : x + (n : K) • y ∈ Metric.closedBall (0 : V) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hxR
  have hny : ‖(n : K)‖ * ‖y‖ ≤ R + ‖x‖ := by
    calc
      ‖(n : K)‖ * ‖y‖ = ‖(n : K) • y‖ := by
        simpa using (norm_smul (n : K) y).symm
      _ = ‖(x + (n : K) • y) - x‖ := by simp
      _ ≤ ‖x + (n : K) • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x‖ < ‖(n : K)‖ * ‖y‖ := by
    calc
      R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : K)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

omit [FloorSemiring K] in
private theorem lineal_eq_singleton_zero_of_nonempty_of_isBounded
    {C : Set V} (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    lin[K](C) = ({0} : Set V) := by
  ext y
  constructor
  · intro hy
    rcases hC_nonempty with ⟨x, hx⟩
    have hy_forall := Set.mem_lineal_iff_forall.mp hy
    have hrange_subset : Set.range (fun n : ℕ ↦ x + (n : K) • y) ⊆ C := by
      rintro _ ⟨n, rfl⟩
      simpa using hy_forall.2 x hx (n : K) (Nat.cast_nonneg n)
    by_cases hy_zero : y = 0
    · simp [hy_zero]
    · exact False.elim <|
        not_isBounded_range_add_natCast_smul x y hy_zero (hC_bounded.subset hrange_subset)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Set.mem_lineal_iff]
    constructor <;> simpa using (zero_mem_recessionCone (R := K) C)

/-- Text 19.0.14: if `C` is convex and bounded in an ordered normed `K`-space, and at least one
of `S`
or `C` is nonempty, then the set `{y | y +ᵥ S = C}` of translation vectors carrying `S` onto `C`
is itself a polytope, possibly empty. Specializing to `K = ℝ`,
`E = EuclideanSpace ℝ (Fin n)`, and `S.Nonempty` recovers the textbook `ℝ^n` statement. -/
theorem isPolytope_translationCover_of_convex_of_isBounded
    {S C : Set V} (hC_convex : Convex K C) (hC_bounded : Bornology.IsBounded C)
    (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  classical
  by_cases hcover_nonempty : ((translationCover S C : Set V)).Nonempty
  · rcases hcover_nonempty with ⟨y₀, hy₀⟩
    have hy₀_cover : y₀ +ᵥ S = C := Set.mem_translationCover_iff.mp hy₀
    have hC_nonempty : C.Nonempty := by
      rcases hSC_nonempty with hS_nonempty | hC_nonempty
      · rcases hS_nonempty with ⟨s, hs⟩
        refine ⟨y₀ +ᵥ s, ?_⟩
        have hs_cover : y₀ +ᵥ s ∈ y₀ +ᵥ S := by
          rw [Set.mem_vadd_set]
          exact ⟨s, hs, rfl⟩
        simpa [hy₀_cover] using hs_cover
      · exact hC_nonempty
    have hlineal :
        lin[K](C) = ({0} : Set V) :=
      lineal_eq_singleton_zero_of_nonempty_of_isBounded
        hC_nonempty hC_bounded
    have hcover_eq : (translationCover S C : Set V) = ({y₀} : Set V) := by
      calc
        (translationCover S C : Set V) = y₀ +ᵥ lin[K](C) :=
          translationCover_eq_vadd_lineal hC_convex hy₀
        _ = y₀ +ᵥ ({0} : Set V) := by simp [hlineal]
        _ = ({y₀} : Set V) := by simp
    rw [hcover_eq]
    exact ⟨{y₀}, Set.finite_singleton y₀, by simp [convexHull_singleton]⟩
  · have hcover_eq : (translationCover S C : Set V) = (∅ : Set V) :=
      Set.not_nonempty_iff_eq_empty.mp hcover_nonempty
    rw [hcover_eq]
    exact ⟨∅, Set.finite_empty, by simp [convexHull_empty]⟩

/-- Field-generic polytope form: if `C` is a `K`-polytope in an ordered normed `K`-space and
bounded, and at least one of `S` or `C` is nonempty, then the set `{y | y +ᵥ S = C}` of
translation vectors carrying `S` onto `C` is itself a `K`-polytope, possibly empty. -/
theorem Set.IsPolytope.translationCover_of_isBounded
    {S C : Set V} (hC : C.IsPolytope K) (hC_bounded : Bornology.IsBounded C)
    (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  exact isPolytope_translationCover_of_convex_of_isBounded
    (hC.convex) hC_bounded hSC_nonempty

/-- Text 19.0.14, scalar-generic polytope form: if `C` is a `K`-polytope in an ordered normed
`K`-space and at least one of `S` or `C` is nonempty, then `{y | y +ᵥ S = C}` is a
`K`-polytope. -/
theorem Set.IsPolytope.translationCover
    [OrderClosedTopology K] [CompactIccSpace K]
    {S C : Set V} (hC : C.IsPolytope K) (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  refine hC.translationCover_of_isBounded ?_ hSC_nonempty
  rcases hC.exists_finset with ⟨t, rfl⟩
  exact (t.finite_toSet.isCompact_convexHull K).isBounded

end Normed

end
