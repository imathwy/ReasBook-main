import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap12.Proposition_12_36
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.60 states the subdifferential and exactness formulas for the
  source-level infimal postcomposition `L ▷ f`.
- `core/canonical`: `infimalPostcomposition.ExactAt` from Definition 12.34 is the owner notion
  of fiberwise attainment.
- `bridge/view`: Proposition 13.24(4) and Proposition 16.10 convert that owner notion into the
  adjoint-preimage description of the subdifferential.
-/

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 16 60: any chosen point on the fiber `L ⁻¹' {y}` gives the canonical
upper bound on the fiber infimum defining `(L ▷ f) y`. -/
lemma infimalPostcomposition_le_of_map_eq
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (hxy : L x = y) :
    (L ▷ f) y ≤ (f x : EReal) := by
  -- Unfold the owner definition and use the chosen fiber point as an admissible witness.
  change sInf ((fun z ↦ (f z : EReal)) '' ((fun z ↦ L z) ⁻¹' {y})) ≤ (f x : EReal)
  refine sInf_le ?_
  exact ⟨x, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxy, rfl⟩

/-- Helper for Proposition 16 60: a source subgradient pulled back by `L.adjoint` yields the
canonical affine minorant of `L ▷ f` on the target space. -/
private lemma adjoint_subgradient_le_infimalPostcomposition
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H}
    (v : K) (hv : L.adjoint v ∈ (∂ f) x) :
    ∀ w : K, ((⟪w - L x, v⟫_ℝ : ℝ) : EReal) + (f x : EReal) ≤ (L ▷ f) w := by
  rw [mem_subdifferential_iff] at hv
  intro w
  -- Compare the affine lower bound on `f` against every value appearing in the fiber infimum.
  change ((⟪w - L x, v⟫_ℝ : ℝ) : EReal) + (f x : EReal) ≤
      sInf ((fun z ↦ (f z : EReal)) '' ((fun z ↦ L z) ⁻¹' {w}))
  refine le_sInf ?_
  rintro _ ⟨z, hz, rfl⟩
  have hzw : L z = w := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hvz : (⟪z - x, L.adjoint v⟫_ℝ : EReal) + (f x : EReal) ≤ (f z : EReal) := hv z
  have hinner : ⟪z - x, L.adjoint v⟫_ℝ = ⟪w - L x, v⟫_ℝ := by
    calc
      ⟪z - x, L.adjoint v⟫_ℝ = ⟪L (z - x), v⟫_ℝ := by
        simpa using (ContinuousLinearMap.adjoint_inner_right L (z - x) v)
      _ = ⟪L z - L x, v⟫_ℝ := by
        simp [ContinuousLinearMap.map_sub]
      _ = ⟪w - L x, v⟫_ℝ := by
        rw [hzw]
  simpa [hinner] using hvz

/-- Helper for Proposition 16 60: if `L.adjoint v` is a subgradient of `f` at `x`, then `x`
attains the fiber infimum of `L ▷ f` at `y = L x`. -/
private lemma infimalPostcomposition_value_eq_of_adjoint_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (v : K) (hxy : L x = y)
    (hv : L.adjoint v ∈ (∂ f) x) :
    (L ▷ f) y = (f x : EReal) := by
  -- The source subgradient gives the lower bound, while the chosen fiber point gives the upper
  -- bound, so the infimum is attained exactly at `x`.
  have hupper : (L ▷ f) y ≤ (f x : EReal) :=
    infimalPostcomposition_le_of_map_eq (f := f) (L := L) hxy
  have hlower :
      ((⟪y - L x, v⟫_ℝ : ℝ) : EReal) + (f x : EReal) ≤ (L ▷ f) y :=
    adjoint_subgradient_le_infimalPostcomposition (f := f) (L := L) (x := x) v hv y
  have hlower' : (f x : EReal) ≤ (L ▷ f) y := by
    simpa [hxy] using hlower
  exact le_antisymm hupper hlower'

-- Proof sketch: use Proposition 13.24(4) to rewrite the conjugate of `L ▷ f` as `f* ∘ L.adjoint`,
-- then combine Proposition 13.15 and Proposition 16.10 at the active point `x` with
-- `L x = y` and `(L ▷ f) y = f x`.
/-- Proposition 16 60 (1): if `y = L x` and the infimal postcomposition is exact there through the
point `x`, then formula (16.50) identifies the subdifferential of `L ▷ f` at `y` with the adjoint
preimage `(L^*)⁻¹ (∂ f(x))`. -/
theorem subdifferential_infimalPostcomposition_eq_preimage_adjoint_of_value_eq
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (hxy : L x = y) (hEq : (L ▷ f) y = (f x : EReal)) :
    (∂ (L ▷ f)) y = (L.adjoint) ⁻¹' ((∂ f) x) := by
  -- Route correction: work directly with the owner affine-minorant inequalities and the fiber
  -- infimum, rather than importing extra Fenchel-conjugate machinery.
  ext v
  rw [Set.mem_preimage, mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hv z
    -- Test the target-space subgradient inequality at `L z` and dominate the fiber infimum there
    -- by the chosen witness `z`.
    have hvz :
        (⟪L z - y, v⟫_ℝ : EReal) + (L ▷ f) y ≤ (L ▷ f) (L z) :=
      hv (L z)
    have hz_upper : (L ▷ f) (L z) ≤ (f z : EReal) :=
      infimalPostcomposition_le_of_map_eq (f := f) (L := L) rfl
    have hbound :
        (⟪L z - y, v⟫_ℝ : EReal) + (f x : EReal) ≤ (f z : EReal) := by
      simpa [hEq] using le_trans hvz hz_upper
    have hinner : ⟪L z - y, v⟫_ℝ = ⟪z - x, L.adjoint v⟫_ℝ := by
      calc
        ⟪L z - y, v⟫_ℝ = ⟪L z - L x, v⟫_ℝ := by
          simp [hxy]
        _ = ⟪z - x, L.adjoint v⟫_ℝ := by
          simpa [ContinuousLinearMap.map_sub] using
            (ContinuousLinearMap.adjoint_inner_right L (z - x) v).symm
    simpa [hinner] using hbound
  · intro hv w
    -- The source subgradient already provides the global affine minorant for `L ▷ f`; only the
    -- active-point identities `y = L x` and `(L ▷ f) y = f x` remain to be substituted.
    have hw :
        ((⟪w - L x, v⟫_ℝ : ℝ) : EReal) + (f x : EReal) ≤ (L ▷ f) w :=
      adjoint_subgradient_le_infimalPostcomposition (f := f) (L := L) (x := x) v hv w
    simpa [hxy, hEq] using hw

-- Proof sketch: apply the companion equality theorem below to the chosen witness
-- `v` with `L.adjoint v ∈ ∂ f x`, then package the resulting minimizing point `x`
-- with `infimalPostcomposition.ExactAt`. The extra hypothesis `x ∈ effectiveDomain f`
-- is exactly the primitive finiteness datum required by that owner notion.
/-- Proposition 16.60 (2): if some vector `v` satisfies `L.adjoint v ∈ ∂ f x`, then the infimal
postcomposition is exact at `y = L x`, attained by `x`. -/
theorem infimalPostcomposition_exactAt_of_mem_effectiveDomain_of_adjoint_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (v : K) (hx : x ∈ effectiveDomain f) (hxy : L x = y)
    (hv : L.adjoint v ∈ (∂ f) x) :
    infimalPostcomposition.ExactAt L f y := by
  -- Package the active fiber point `x` together with the value equality supplied by the
  -- subgradient.
  have hvalue :
      (L ▷ f) y = (f x : EReal) :=
    infimalPostcomposition_value_eq_of_adjoint_mem_subdifferential
      (f := f) (L := L) (x := x) (y := y) v hxy hv
  exact ⟨x, hx, hxy, hvalue⟩

/-- Companion to Proposition 16.60 (2): the exactness conclusion gives the displayed value
equality `(L ▷ f) y = f x`. Unlike exactness, this value identity does not need the extra
effective-domain hypothesis on `x`. -/
theorem infimalPostcomposition_eq_of_adjoint_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (v : K) (hxy : L x = y)
    (hv : L.adjoint v ∈ (∂ f) x) :
    (L ▷ f) y = (f x : EReal) := by
  -- This is exactly the fiberwise value-attainment helper proved from the source subgradient.
  exact infimalPostcomposition_value_eq_of_adjoint_mem_subdifferential
    (f := f) (L := L) (x := x) (y := y) v hxy hv

end SubdifferentialCalculus

end ERealFunction
