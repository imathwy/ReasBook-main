import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_3_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_17
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace (WithBotTop 𝕜)] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.2.2 says that, for a convex function on a finite-dimensional
  normed primal space, the Fenchel supremum defining `f*` may be restricted from the ambient
  primal space to `ri (dom f)`.
- `core/canonical`: the owner abstraction is the project declaration `convexConjugate`.
- `bridge/view`: Rockafellar's `dom f` is represented by the chapter's effective-domain notation
  `dom(f)`, and `ri` is represented by `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`.

Domain-style sampling used here:
- the project owner `convexConjugate`;
- the paired-space closure-invariance theorem
  `convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices`;
- the primitive pairing-slice lower-semicontinuity hypothesis
  `LowerSemicontinuous (fun x ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))` at the selected dual point `y`;
- the closure-from-relative-interior theorem
  `cl_eq_of_riDom_eq_and_eqOn`;
- the idempotence theorem `ri_idem` for the relative interior bridge
  `riDom[𝕜](g) = riDom[𝕜](f)`.

Primitive data vs derived API:
- primitive inputs: a convex function `f : X → WithBotTop 𝕜` on a finite-dimensional normed
  `𝕜`-space, a dual point `y : Y`, and the pairing-slice lower-semicontinuity data
  `hpair : LowerSemicontinuous (fun x ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))`;
- derived API: the restriction of the conjugate supremum to the relative interior of the effective
  domain of `f`.

Codomain/scalar canonicalization note:
- both statement and proof are written directly on the scalar-generic owner layer
  `WithBotTop 𝕜`, with no codomain-specialization coercion bridge in the pairing-slice
  continuity step.

Layer target: `source-facing`; the corollary is stated directly as a conjugate formula in the
owner language, without introducing a restriction wrapper.
- Ambient refinement: the proof uses only the finite-dimensional normed geometry of
  `riDom[𝕜](f)` on the primal side together with the paired-space closure invariance of
  `convexConjugate` from Theorem 12.2, so coordinate-model wording is treated as a
  downstream specialization rather than as the owner abstraction.
-/

-- Proof sketch: let `g` agree with `f` on `intrinsicInterior 𝕜 {x : X | f x < ⊤}` and take the
-- value `⊤` outside that set. The restricted supremum is then `convexConjugate g y` by the
-- defining formula for conjugation. Corollary 7.3.4 gives
-- `cl(g) = cl(f)`, so Theorem 12.2 identifies
-- `convexConjugate g = convexConjugate f`.
namespace Function.IsConvex

/-- Corollary 12.2.2: for a convex function `f` on a finite-dimensional normed `𝕜`-space, the
supremum defining `f⋆ y` may be restricted to the relative interior `ri (dom f)`, represented
here by the subtype `riDom[𝕜](f)`.
The dual variable lives in an arbitrary paired space `Y`; the only extra owner input beyond the
primal geometry is lower semicontinuity of the selected pairing slice at `y`. -/
theorem convexConjugate_eq_iSup_pairing_sub_riDom
    {f : X → WithBotTop 𝕜} (hf : f.IsConvex 𝕜)
    (y : Y) (hpair : LowerSemicontinuous (fun x : X ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))) :
    f⋆ y = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := by
  classical
  let S : Set X := riDom[𝕜](f)
  let g : X → WithBotTop 𝕜 := S.piecewise f ⊤
  have hS_convex : Convex 𝕜 S := by
    simpa [S] using hf.convex_dom.intrinsicInterior
  have hS_idem : intrinsicInterior 𝕜 S = S := by
    change intrinsicInterior 𝕜 (intrinsicInterior 𝕜 dom(f)) = intrinsicInterior 𝕜 dom(f)
    exact ri_idem (𝕜 := 𝕜) (C := dom(f))
  have hg : g.IsConvex 𝕜 := by
    rw [Function.isConvex_iff_convex_epigraph]
    have hset :
        {p : X × 𝕜 | g p.1 ≤ p.2} =
          (S ×ˢ (Set.univ : Set 𝕜)) ∩ {p : X × 𝕜 | f p.1 ≤ p.2} := by
      ext p
      by_cases hp : p.1 ∈ S <;> simp [g, hp]
    change Convex 𝕜 ({p : X × 𝕜 | g p.1 ≤ (p.2 : WithBotTop 𝕜)})
    rw [hset]
    exact (hS_convex.prod convex_univ).inter hf.convex_epigraph
  have hdom : dom(g) = S := by
    ext x
    constructor
    · intro hxg
      by_contra hxS
      have hxg' : g x < ⊤ := by simpa [mem_effectiveDomain] using hxg
      have hgx : g x = ⊤ := by simp [g, hxS]
      exact (not_lt_of_ge le_rfl) (hgx ▸ hxg')
    · intro hx
      have hfx : f x < ⊤ := by
        simpa [S] using (intrinsicInterior_subset hx : x ∈ dom(f))
      simpa [mem_effectiveDomain, g, hx] using hfx
  have hri : riDom[𝕜](f) = riDom[𝕜](g) := by
    calc
      riDom[𝕜](f) = S := by simp [S]
      _ = intrinsicInterior 𝕜 S := hS_idem.symm
      _ = riDom[𝕜](g) := by simp [hdom]
  have hfg : Set.EqOn f g riDom[𝕜](f) := by
    intro x hx
    have hxS : x ∈ S := by simpa [S] using hx
    simp [g, hxS]
  have hcl : cl(f) = cl(g) :=
    hf.cl_eq_of_riDom_eq_and_eqOn hg hri hfg
  have hcl_conj_eval :
      ∀ h : X → WithBotTop 𝕜,
        (cl(h)⋆ : Y → WithBotTop 𝕜) y = h⋆ y := by
    intro h
    letI : HasPairing X Unit 𝕜 := ⟨fun x _ ↦ (⟪x, y⟫ₚ : 𝕜)⟩
    have hpair_unit :
        ∀ u : Unit, LowerSemicontinuous (fun x : X ↦ (⟪x, u⟫ₚ : WithBotTop 𝕜)) := by
      intro u
      cases u
      simpa using hpair
    have hconj_unit :
        (cl(h)⋆ : Unit → WithBotTop 𝕜) = (h⋆ : Unit → WithBotTop 𝕜) :=
      convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices h hpair_unit
    have hunit :
        (cl(h)⋆ : Unit → WithBotTop 𝕜) () =
          (h⋆ : Unit → WithBotTop 𝕜) () :=
      congrFun hconj_unit ()
    simpa [convexConjugate] using hunit
  have hconj : f⋆ y = g⋆ y := by
    calc
      f⋆ y = (cl(f)⋆ : Y → WithBotTop 𝕜) y := (hcl_conj_eval f).symm
      _ = (cl(g)⋆ : Y → WithBotTop 𝕜) y := by simp [hcl]
      _ = g⋆ y := hcl_conj_eval g
  have hg_formula :
      g⋆ y = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    apply le_antisymm
    · refine iSup_le fun x ↦ ?_
      by_cases hx : x ∈ S
      · calc
          ⟪x, y⟫ₚ - g x = ⟪x, y⟫ₚ - f x := by
            simp [g, hx]
          _ ≤ ⨆ z : riDom[𝕜](f), ⟪z, y⟫ₚ - f z :=
            le_iSup_of_le ⟨x, by simpa [S] using hx⟩ le_rfl
      · simp [g, hx]
    · refine iSup_le fun x ↦ ?_
      have hx : (x : X) ∈ S := by
        change (x : X) ∈ riDom[𝕜](f)
        exact x.property
      calc
        ⟪x, y⟫ₚ - f x = ⟪x, y⟫ₚ - g x := by simp [g, hx]
        _ ≤ ⨆ z : X, ⟪z, y⟫ₚ - g z := le_iSup (fun z : X ↦ ⟪z, y⟫ₚ - g z) (x : X)
  calc
    f⋆ y = g⋆ y := hconj
    _ = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := hg_formula

end Function.IsConvex

end
