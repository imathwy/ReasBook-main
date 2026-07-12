import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {r₀ : ℤ}

/- Definition 12.24.7 stays in the source-facing property layer for the canonical owner
`CohomologicalSpectralSequence 𝒜 r₀`.
Sampled domain declarations:
- `CategoryTheory.CohomologicalSpectralSequence`;
- `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageX`;
- `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD`;
- `CategoryTheory.FilteredComplex.convergesToCohomology`.
Best owner abstraction: the mathlib owner `CategoryTheory.CohomologicalSpectralSequence 𝒜 r₀`.
Primitive data here are only the owner pages and their differentials. The source-facing predicates
below are stated directly from that owner data. The derived set
`initialPageAntidiagonalSupport` is only a bridge/view of that owner data, not a second owner.
Source/core/bridge triage:
- `source-facing`: `IsRegular`, `IsCoregular`, `IsBounded`, `IsBoundedBelow`, `IsBoundedAbove`;
- `core/canonical`: `CohomologicalSpectralSequence 𝒜 r₀`;
- `bridge/view`: `initialPageAntidiagonalSupport` and its order-boundedness reformulations on each
  initial-page antidiagonal. -/

/-- The support on the initial-page antidiagonal of total degree `n`. -/
def initialPageAntidiagonalSupport (E : CohomologicalSpectralSequence 𝒜 r₀) (n : ℤ) : Set ℤ :=
  { p : ℤ | ¬ IsZero ((E.page r₀).X (p, n - p)) }

/-- Definition 12.24.7 (1): a cohomological spectral sequence is regular if for every bidegree
`(p,q)` there is a page after which all outgoing differentials
`d_r^{p,q} : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}` vanish. -/
@[stacks 0BDU]
def IsRegular (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p, q) (p + r, q - r + 1) = 0

/-- Definition 12.24.7 (2): a cohomological spectral sequence is coregular if for every bidegree
`(p,q)` there is a page after which all incoming differentials
`d_r^{p-r,q+r-1} : E_r^{p-r,q+r-1} ⟶ E_r^{p,q}` vanish. -/
@[stacks 0BDU]
def IsCoregular (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p - r, q + r - 1) (p, q) = 0

/-- Definition 12.24.7 (3): a cohomological spectral sequence is bounded if on each total degree
`n` only finitely many entries `E_{r₀}^{p,n-p}` on the initial page are nonzero. -/
@[stacks 0BDU]
def IsBounded (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, (E.initialPageAntidiagonalSupport n).Finite

/-- Definition 12.24.7 (4): a cohomological spectral sequence is bounded below if on each total
degree `n` the initial-page support on the antidiagonal `p + q = n` is bounded above;
equivalently, the entries `E_{r₀}^{p,n-p}` vanish for all sufficiently large `p`. -/
@[stacks 0BDU]
def IsBoundedBelow (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, b ≤ p → IsZero ((E.page r₀).X (p, n - p))

/-- Definition 12.24.7 (5): a cohomological spectral sequence is bounded above if on each total
degree `n` the initial-page support on the antidiagonal `p + q = n` is bounded below;
equivalently, the entries `E_{r₀}^{p,n-p}` vanish for all sufficiently small `p`. -/
@[stacks 0BDU]
def IsBoundedAbove (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, p ≤ b → IsZero ((E.page r₀).X (p, n - p))

/-- The support-boundedness reformulation of `IsBoundedBelow`: on each total degree `n`, the
initial-page antidiagonal support is bounded above exactly when the initial entries vanish for all
sufficiently large `p`. -/
theorem isBoundedBelow_iff_bddAbove
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsBoundedBelow E ↔
      ∀ n : ℤ, BddAbove (E.initialPageAntidiagonalSupport n) := by
  constructor
  · intro hE n
    have hE' : ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, b ≤ p → IsZero ((E.page r₀).X (p, n - p)) := by
      simpa [IsBoundedBelow] using hE
    rcases hE' n with ⟨b, hb⟩
    refine bddAbove_def.mpr ⟨b - 1, ?_⟩
    intro p hp
    have hmem : ¬ IsZero ((E.page r₀).X (p, n - p)) := hp
    by_contra hp'
    have : b ≤ p := by omega
    exact hmem (hb this)
  · intro hE n
    rcases bddAbove_def.mp (hE n) with ⟨b, hb⟩
    refine ⟨b + 1, ?_⟩
    intro p hp
    by_contra hzero
    have hp' : p ∈ E.initialPageAntidiagonalSupport n := by
      simpa using hzero
    have : p ≤ b := hb p hp'
    omega

/-- The support-boundedness reformulation of `IsBoundedAbove`: on each total degree `n`, the
initial-page antidiagonal support is bounded below exactly when the initial entries vanish for all
sufficiently small `p`. -/
theorem isBoundedAbove_iff_bddBelow
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsBoundedAbove E ↔
      ∀ n : ℤ, BddBelow (E.initialPageAntidiagonalSupport n) := by
  constructor
  · intro hE n
    have hE' : ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, p ≤ b → IsZero ((E.page r₀).X (p, n - p)) := by
      simpa [IsBoundedAbove] using hE
    rcases hE' n with ⟨b, hb⟩
    refine bddBelow_def.mpr ⟨b + 1, ?_⟩
    intro p hp
    have hmem : ¬ IsZero ((E.page r₀).X (p, n - p)) := hp
    by_contra hp'
    have : p ≤ b := by omega
    exact hmem (hb this)
  · intro hE n
    rcases bddBelow_def.mp (hE n) with ⟨b, hb⟩
    refine ⟨b - 1, ?_⟩
    intro p hp
    by_contra hzero
    have hp' : p ∈ E.initialPageAntidiagonalSupport n := by
      simpa using hzero
    have : b ≤ p := hb p hp'
    omega

end CohomologicalSpectralSequence
end CategoryTheory
