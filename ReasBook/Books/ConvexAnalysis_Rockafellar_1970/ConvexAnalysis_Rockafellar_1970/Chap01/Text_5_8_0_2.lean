import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

namespace Function

/-- Helper for Text 5.8.0.2: the `WithTopBot`-valued heights in the vertical fiber of `F` above
`x`. -/
def verticalHeights (F : Set (E × 𝕜)) (x : E) : Set (WithTopBot 𝕜) :=
  ((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F}

/-- Helper for Text 5.8.0.2: the vertical infimum of `F` takes the infimum of the heights in the
vertical fiber above each base point. -/
noncomputable def verticalInfimum [ConditionallyCompleteLattice 𝕜] (F : Set (E × 𝕜)) :
    E → WithTopBot 𝕜 :=
  fun x ↦ sInf (verticalHeights F x)

/-- Helper for Text 5.8.0.2: every point of `F` gives an upper bound on the vertical infimum at
its base point. -/
theorem verticalInfimum_le_of_mem [ConditionallyCompleteLattice 𝕜]
    {F : Set (E × 𝕜)} {x : E} {μ : 𝕜} (h : (x, μ) ∈ F) :
    verticalInfimum F x ≤ μ := by
  exact sInf_le ⟨μ, h, rfl⟩

/-- Helper for Text 5.8.0.2: if `F` lies in the epigraph of `h`, then `h` is pointwise bounded
above by the vertical infimum attached to `F`. -/
theorem le_verticalInfimum_of_subset_epi [ConditionallyCompleteLattice 𝕜]
    {F : Set (E × 𝕜)} {h : E → WithTopBot 𝕜} (hF : F ⊆ epi h) :
    h ≤ verticalInfimum F := by
  intro x
  refine le_sInf ?_
  rintro _ ⟨μ, hμF, rfl⟩
  simpa [verticalHeights, mem_epi_restrict_iff] using hF hμF

end Function

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

local notation "R≥0" => Set.Ici (0 : R)

variable [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜] [SMul R E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition forms, for each `fᵢ`, the three-variable family obtained from
  the scaled epigraph vertical-infimum view of `fᵢ`, then takes the common-`λ` sum set `K`, its
  `λ = 1` slice `F`, and the vertical infimum of that slice.
- `core/canonical`: the owner abstractions are the earlier chapter declarations
  `+ᶠ` from `Theorem_3_6`, the chapter epigraph owner `epi` applied to the
  canonical function `(λ, x) ↦ verticalInfimum (λ • epi f) x`,
  the item-local owner `Function.verticalInfimum`, and the item-local
  `infimal_convolution` owner below.
- `bridge/view`: the source set `K` is a thin view of the owner `+ᶠ` over the
  common scalar parameter, built directly from the public family
  `rightScalarMulEpigraphFamily`; at `λ = 1`, the scaled-epigraph vertical infimum is just `f`,
  so the slice
  `F` becomes the ordinary epigraph-sum description of infimal convolution from the earlier
  section.
- `primitive data vs derived API`: the source-facing family
  `rightScalarMulEpigraphFamily` is primitive for the later Minkowski-sum item, while the present
  source-facing slice `F` is defined directly from the owners
  `rightScalarMulEpigraphFamily` and `+ᶠ`. The function on the slice is presented
  through the owner `Function.verticalInfimum`, and the identification with the item-local
  `infimal_convolution` is derived API.

Domain-style sampling used here:
- `(+ᶠ)`;
- `Set.mem_fiberwiseSum`;
- `epi`;
- `mem_epi_restrict_iff`;
- `rightScalarMulEpigraphFamily`;
- `Function.verticalInfimum`;
- the item-local `infimal_convolution` owner.

The book states this proposition for proper convex functions, but the displayed identification of
the constructed function with `f₁ □ f₂` depends only on the item-local infimal-convolution owner
and the earlier right-scalar-multiple owner, so the redundant properness and convexity hypotheses
are omitted from the main declaration. The only function-side guard that remains is the pointwise
exclusion of `⊥`, matching the textbook surface without forcing extra structure into the owner.
- Ambient minimization: the primitive owner `rightScalarMulEpigraphFamily` uses only the scalar
  action and the preorder structure needed to form the nonnegative scalar parameter; the scalar
  parameter type and codomain are kept
  separate (`R` and `𝕜`) so this owner does not force the ambient codomain to coincide with the
  scaling type. The primitive common-`λ` slice itself needs additive structure only on the scalar
  height coordinate used by `+ᶠ`; additive structure on `E` appears only when comparing that slice
  with the ordinary epigraph Minkowski sum and then with `infimal_convolution`. No additive-group
  structure is frozen into the public theorem surface.
-/

/-- The three-variable epigraph family of the right scalar multiples `f λ`, with the nonnegative
scalar parameter recorded in the first coordinate. -/
def rightScalarMulEpigraphFamily (f : E → WithTopBot 𝕜) : Set (R × E × 𝕜) :=
  {p |
    ∃ h_lam : 0 ≤ p.1,
      Function.verticalInfimum ((((⟨p.1, h_lam⟩ : R≥0) : R) • epi f) : Set (E × 𝕜)) p.2.1 ≤
        p.2.2}

/-- Membership in `rightScalarMulEpigraphFamily` is exactly the epigraph inequality for the
corresponding canonical scaled epigraph owner. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily
    (f : E → WithTopBot 𝕜) (lam : R≥0) (x : E) (μ : 𝕜) :
    ((lam : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔
      Function.verticalInfimum ((lam : R) • epi f) x ≤ μ := by
  constructor
  · rintro ⟨h_lam, hμ⟩
    -- Compare the witness packaged from `h_lam` with the canonical subtype `lam`.
    have hsubtype : (⟨(lam : R), h_lam⟩ : R≥0) = lam := by
      ext
      rfl
    simpa [hsubtype] using hμ
  · intro h
    -- Reinsert the canonical nonnegative scalar as the defining witness.
    exact ⟨lam.2, by simpa using h⟩

/-- A point `((λ : R), x, μ)` lies in the right-scalar-multiple epigraph family exactly when
the height `μ` lies above the vertical-infimum value at `x` of the scaled epigraph `λ (epi f)`. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily_verticalInfimum
    (f : E → WithTopBot 𝕜) (lam : R≥0) (x : E) (μ : 𝕜) :
    ((lam : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔
      Function.verticalInfimum ((lam : R) • epi f) x ≤ μ := by
  -- This is the direct owner-level membership rewrite for the scaled epigraph family.
  exact mem_rightScalarMulEpigraphFamily (f := f) (lam := lam) x μ

end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

local notation "R≥0" => Set.Ici (0 : R)

variable [Monoid R] [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜] [MulAction R E]

/-- At the unit scalar, membership in the right-scalar-multiple epigraph family is exactly
membership in the ordinary epigraph of `f`. -/
@[simp] theorem mem_rightScalarMulEpigraphFamily_one
    [ZeroLEOneClass R] [NoBotOrder 𝕜]
    (f : E → WithTopBot 𝕜) (x : E) (μ : 𝕜) :
    ((1 : R), x, μ) ∈ rightScalarMulEpigraphFamily f ↔ f x ≤ μ := by
  constructor
  · intro h
    have h_vertical : Function.verticalInfimum (epi f) x ≤ μ := by
      simpa [one_smul] using
        (mem_rightScalarMulEpigraphFamily (f := f)
          (lam := (⟨(1 : R), zero_le_one⟩ : R≥0)) x μ).mp h
    exact (Function.le_verticalInfimum_of_subset_epi
      (F := epi f) (h := f) (by intro p hp; simpa using hp) x).trans h_vertical
  · intro h
    have h_mem : (x, μ) ∈ epi f := by
      simpa using h
    have h_vertical : Function.verticalInfimum (epi f) x ≤ μ :=
      Function.verticalInfimum_le_of_mem h_mem
    have h_vertical' : Function.verticalInfimum ((1 : R) • epi f) x ≤ μ := by
      simpa [one_smul] using h_vertical
    simpa [one_smul] using
      (mem_rightScalarMulEpigraphFamily (f := f)
        (lam := (⟨(1 : R), zero_le_one⟩ : R≥0)) x μ).mpr h_vertical'

end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Zero R] [One R] [Preorder R]
variable [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜]
variable [Add E] [Add 𝕜]
variable [SMul R E]

/-- The slice `F` at `λ = 1` of the owner fiberwise sum of the two common-`λ` epigraph views,
viewed as a subset of `E × 𝕜`. The scalar parameter type `R` is explicit because the slice lives in
`E × 𝕜` and does not otherwise determine `R` by type inference. -/
def common_scalar_epigraph_slice (R : Type*)
    [Zero R] [One R] [Preorder R]
    [ConditionallyCompleteLattice 𝕜] [SMul R 𝕜]
    [Add E] [Add 𝕜] [SMul R E]
    (f₁ f₂ : E → WithTopBot 𝕜) : Set (E × 𝕜) :=
  {q |
    ((1 : R), q.1, q.2) ∈
      rightScalarMulEpigraphFamily f₁ +ᶠ rightScalarMulEpigraphFamily f₂}

-- Proof sketch: rewrite the source-facing slice by
-- `common_scalar_epigraph_slice_eq_epi_add`, then identify the resulting vertical infimum with the
-- item-local infimal-convolution owner.
end

section

open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Monoid R] [Zero R] [Preorder R] [ZeroLEOneClass R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜]
variable [NoBotOrder 𝕜]
variable [Add 𝕜]
variable [Add E] [MulAction R E]

/-- The unit slice `F` is exactly the Minkowski sum of the two chapter epigraph owners
`epi f₁` and `epi f₂`. -/
theorem common_scalar_epigraph_slice_eq_epi_add
    (f₁ f₂ : E → WithTopBot 𝕜) :
    common_scalar_epigraph_slice R f₁ f₂ =
      epi f₁ + epi f₂ := by
  refine Set.ext fun p ↦ ?_
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    -- Expand the common-`λ` fiberwise-sum witnesses and rewrite each `λ = 1` slice to an
    -- ordinary epigraph inequality.
    rcases (by
      simpa [common_scalar_epigraph_slice, Set.mem_fiberwiseSum] using hp :
        ∃ x₁ μ₁ x₂ μ₂,
          ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ ∧
            ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ ∧
              x₁ + x₂ = x ∧ μ₁ + μ₂ = μ) with
      ⟨x₁, μ₁, x₂, μ₂, h₁, h₂, hsumx, hsummu⟩
    refine Set.mem_add.mpr
      ⟨(x₁, μ₁), ?_, (x₂, μ₂), ?_, Prod.ext hsumx hsummu⟩
    · simpa using (mem_rightScalarMulEpigraphFamily_one f₁ x₁ μ₁).mp h₁
    · simpa using (mem_rightScalarMulEpigraphFamily_one f₂ x₂ μ₂).mp h₂
  · intro hp
    -- Read a point of the Minkowski sum as two epigraph points and package them back into the
    -- common-`λ` fiberwise sum at `λ = 1`.
    rcases Set.mem_add.mp hp with ⟨⟨x₁, μ₁⟩, h₁, ⟨x₂, μ₂⟩, h₂, hsum⟩
    have hsumx : x₁ + x₂ = x := by simpa using congrArg Prod.fst hsum
    have hsummu : μ₁ + μ₂ = μ := by simpa using congrArg Prod.snd hsum
    have hmem₁ : ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ :=
      (mem_rightScalarMulEpigraphFamily_one f₁ x₁ μ₁).mpr <| by simpa using h₁
    have hmem₂ : ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ :=
      (mem_rightScalarMulEpigraphFamily_one f₂ x₂ μ₂).mpr <| by simpa using h₂
    simpa [common_scalar_epigraph_slice, Set.mem_fiberwiseSum] using
      (show ∃ x₁ μ₁ x₂ μ₂,
          ((1 : R), x₁, μ₁) ∈ rightScalarMulEpigraphFamily f₁ ∧
            ((1 : R), x₂, μ₂) ∈ rightScalarMulEpigraphFamily f₂ ∧
              x₁ + x₂ = x ∧ μ₁ + μ₂ = μ from
        ⟨x₁, μ₁, x₂, μ₂, hmem₁, hmem₂, hsumx, hsummu⟩)

end

section

open Function
open scoped Pointwise

variable {E : Type*} {R : Type*} {𝕜 : Type*}

variable [Monoid R] [Zero R] [Preorder R] [ZeroLEOneClass R]
variable [ConditionallyCompleteLattice 𝕜] [MulAction R 𝕜]
variable [NoBotOrder 𝕜]
variable [Add 𝕜]
variable [Add E] [MulAction R E]

/-- Helper for Text 5.8.0.2: the item-local infimal convolution is the vertical infimum of the
Minkowski sum of the two epigraphs. -/
def infimal_convolution (f₁ f₂ : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimum (epi f₁ + epi f₂)

infixl:70 " □ " => infimal_convolution

/-- Text 5.8.0.2: applying `Function.verticalInfimum` to the `λ = 1` slice of the common-`λ`
sum of the epigraph families of the right scalar multiples of `f₁` and `f₂` yields the infimal
convolution `f₁ □ f₂`, provided both functions are nowhere `⊥`. -/
theorem verticalInfimum_common_scalar_epigraph_slice_eq_infimal_convolution
    (f₁ f₂ : E → WithTopBot 𝕜)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    verticalInfimum (common_scalar_epigraph_slice R f₁ f₂) =
      (f₁ □ f₂ : E → WithTopBot 𝕜) := by
  let _ := hf₁_ne_bot
  let _ := hf₂_ne_bot
  -- Replace the source-defined unit slice by the canonical epigraph Minkowski sum.
  rw [common_scalar_epigraph_slice_eq_epi_add (f₁ := f₁) (f₂ := f₂)]
  -- The item-local infimal-convolution owner is exactly this vertical infimum.
  rfl

end
