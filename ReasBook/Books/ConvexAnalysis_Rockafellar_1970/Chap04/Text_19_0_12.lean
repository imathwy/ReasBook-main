import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_13
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

-- Declarations for this item will be appended below by the statement pipeline.

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
