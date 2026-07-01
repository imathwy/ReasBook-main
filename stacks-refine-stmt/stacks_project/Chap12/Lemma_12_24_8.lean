import Mathlib
import stacks_project.Chap12.Definition_12_20_2
import stacks_project.Chap12.Definition_12_24_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {r₀ : ℤ}

/- Domain-style sampling for Lemma 12.24.8:
- primary domain: regularity/coregularity and boundedness for cohomological spectral sequences;
- sampled owner declarations:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.SpectralSequence.cycle`,
  `CategoryTheory.SpectralSequence.boundary`,
  `CategoryTheory.CohomologicalSpectralSequence.IsRegular`,
  `CategoryTheory.CohomologicalSpectralSequence.IsCoregular`;
- best owner abstraction: the canonical owner `CohomologicalSpectralSequence 𝒜 r₀`, together with
  its page-`E_{r₀}` reindexing to the chapter owner `SpectralSequence.cycle`/`boundary`;
- primitive data: the owner pages `(E.page r).X (p, q)`, their differentials `(E.page r).d`, and
  the page-to-page isomorphisms `E.iso`;
- derived API in this file: the source-facing recursive pieces `Z_r^{p,q}` and `B_r^{p,q}` on the
  initial page, the stabilization characterizations of regularity/coregularity, and the boundedness
  implications.
Source/core/bridge triage:
- `source-facing`: the recursive pieces `cycle`, `boundary` and the predicates `IsRegular`,
  `IsCoregular`, `IsBounded`, `IsBoundedBelow`, `IsBoundedAbove`;
- `core/canonical`: the spectral sequence `E : CohomologicalSpectralSequence 𝒜 r₀`;
- `bridge/view`: the reindexing `toInitialPageSpectralSequence` from the initial page `E_{r₀}` to
  the page-`E₁` owner used by `SpectralSequence.cycle` and `SpectralSequence.boundary`. -/

/-- Bridge/view layer: reindex a cohomological spectral sequence from its initial page `E_{r₀}`
as a page-`E₁` spectral sequence so that the canonical recursive pieces `Z_r` and `B_r` are
reused from `SpectralSequence.cycle` and `SpectralSequence.boundary` instead of being duplicated
locally. -/
abbrev toInitialPageSpectralSequence (E : CohomologicalSpectralSequence 𝒜 r₀) :
    SpectralSequence 𝒜
      (fun r ↦ ComplexShape.up' (⟨r₀ + r - 1, 1 - (r₀ + r - 1)⟩ : ℤ × ℤ)) 1 where
  page r hr := E.page (r₀ + r - 1) (by omega)
  iso r r' pq hrr' hr := by
    simpa using E.iso (r₀ + r - 1) (r₀ + r' - 1) pq (by omega) (by omega)

/-- The page-`E₁` owner index corresponding to the actual page number `r ≥ r₀`. -/
private def initialPageNumber (r₀ r : ℤ) (hr : r₀ ≤ r) : ℕ+ :=
  ⟨Int.toNat (r - r₀ + 1), by omega⟩

/-- The source-facing cycle piece `Z_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev cycle (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.cycle pq (initialPageNumber r₀ r hr)

/-- The source-facing boundary piece `B_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev boundary (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.boundary pq (initialPageNumber r₀ r hr)

/-- Lemma 12.24.8 (1): a cohomological spectral sequence is regular exactly when, for every
bidegree `(p,q)`, the source-facing cycle pieces `Z_r^{p,q}` eventually stabilize. -/
theorem isRegular_iff_eventually_cycle_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsRegular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.cycle (p, q) r hr = E.cycle (p, q) (r + 1) (by omega) := by
  sorry

/-- Lemma 12.24.8 (2): a cohomological spectral sequence is coregular exactly when, for every
bidegree `(p,q)`, the source-facing boundary pieces `B_r^{p,q}` eventually stabilize. -/
theorem isCoregular_iff_eventually_boundary_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsCoregular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.boundary (p, q) r hr = E.boundary (p, q) (r + 1) (by omega) := by
  sorry

section

variable (E : CohomologicalSpectralSequence 𝒜 r₀)

-- Proof sketch: boundedness on each initial antidiagonal is equivalent to having both an upper and
-- a lower eventual vanishing bound on that antidiagonal; translate between the finite-support
-- condition of `IsBounded` and the two one-sided eventual-vanishing conditions.
/-- Lemma 12.24.8 (3): a cohomological spectral sequence is bounded exactly when it is both
bounded below and bounded above. -/
theorem isBounded_iff_isBoundedBelow_and_isBoundedAbove :
    IsBounded E ↔ IsBoundedBelow E ∧ IsBoundedAbove E := by
  constructor
  · intro hE
    refine ⟨(isBoundedBelow_iff_bddAbove E).2 ?_, (isBoundedAbove_iff_bddBelow E).2 ?_⟩
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).2
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).1
  · rintro ⟨hbelow, habove⟩ n
    exact (Set.finite_iff_bddBelow_bddAbove.2
      ⟨((isBoundedAbove_iff_bddBelow E).1 habove) n,
        ((isBoundedBelow_iff_bddAbove E).1 hbelow) n⟩)

-- Proof sketch: the page transition isomorphism identifies `E_{s+1}^{p,q}` with the homology of
-- the short complex extracted from the `s`th page, so vanishing of `E_s^{p,q}` forces vanishing
-- of the same bidegree on every later page by induction.
/-- If an entry on the initial page is zero, then the corresponding entry on every later page is
zero. -/
theorem isZero_pageObj_of_isZero_initialPageObj
    {pq : ℤ × ℤ} {r : ℤ}
    (h₀ : IsZero ((E.page r₀).X pq)) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) := by
  induction r, hr using Int.le_induction with
  | base =>
      exact h₀
  | succ s hs hsZero =>
      let c : ComplexShape (ℤ × ℤ) := ComplexShape.up' (⟨s, 1 - s⟩ : ℤ × ℤ)
      refine IsZero.of_iso ?_ (E.iso s (s + 1) pq).symm
      simpa [HomologicalComplex.homology] using
        (ShortComplex.isZero_homology_of_isZero_X₂
          ((E.page s).sc' (c.prev pq) pq (c.next pq))
          hsZero)

-- Proof sketch: if the initial page is eventually zero for large `p` on each antidiagonal, then
-- for fixed `(p,q)` the outgoing targets `E_r^{p + r, q - r + 1}` are zero for all sufficiently
-- large `r`, so the outgoing differentials vanish and the spectral sequence is regular.
/-- Lemma 12.24.8 (4): a bounded-below cohomological spectral sequence is regular. -/
theorem isRegular_of_isBoundedBelow
    (hE : IsBoundedBelow E) : IsRegular E := by
  intro p q
  rcases hE (p + q + 1) with ⟨b, hb⟩
  refine ⟨b - p, ?_⟩
  intro r hr hbr
  have hp : b ≤ p + r := by
    omega
  have hq : p + q + 1 - (p + r) = q - r + 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p + r, q - r + 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p + r, q - r + 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_tgt _

-- Proof sketch: if the initial page is eventually zero for small `p` on each antidiagonal, then
-- for fixed `(p,q)` the sources `E_r^{p - r, q + r - 1}` of the incoming differentials are zero
-- for all sufficiently large `r`, so those differentials vanish and the spectral sequence is
-- coregular.
/-- Lemma 12.24.8 (5): a bounded-above cohomological spectral sequence is coregular. -/
theorem isCoregular_of_isBoundedAbove
    (hE : IsBoundedAbove E) : IsCoregular E := by
  intro p q
  rcases hE (p + q - 1) with ⟨b, hb⟩
  refine ⟨p - b, ?_⟩
  intro r hr hbr
  have hp : p - r ≤ b := by
    omega
  have hq : p + q - 1 - (p - r) = q + r - 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p - r, q + r - 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p - r, q + r - 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_src _

end

end CohomologicalSpectralSequence
end CategoryTheory
