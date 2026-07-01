import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry ProjectiveSpectrum

noncomputable section

universe u v

section ProjectiveSpectrumTopology

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage: this file lies in graded commutative algebra and projective-spectrum topology.
the topological owner abstraction is `ProjectiveSpectrum 𝒜`, and its Zariski-topology API already
lives canonically under the weaker `[AddSubmonoidClass σ A]` assumptions. The stronger
scheme-level basic-open charts live on `Proj 𝒜` and are kept in a separate section below. The
non-recall lemmas here are source-facing bridges derived from the owner API rather than parallel
wrapper declarations. -/

/- The subset `D₊(f)` is open in `Proj(S)`. This is `ProjectiveSpectrum.isOpen_basicOpen`. -/
recall ProjectiveSpectrum.isOpen_basicOpen

variable (I : HomogeneousIdeal 𝒜)

/- The subsets `V₊(I)` are closed in `Proj(S)`. This is `ProjectiveSpectrum.isClosed_zeroLocus`
applied to a homogeneous ideal. -/
recall ProjectiveSpectrum.isClosed_zeroLocus

/- Closed subsets of `Proj(S)` are exactly zero loci of subsets of `A`. This is the owner theorem
`ProjectiveSpectrum.isClosed_iff_zeroLocus`. -/
recall ProjectiveSpectrum.isClosed_iff_zeroLocus

/-- A subset of `Proj(S)` is closed exactly when it is the zero locus of its vanishing ideal. -/
theorem isClosed_iff_eq_zeroLocus_vanishingIdeal (T : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed T ↔ T = zeroLocus 𝒜 (vanishingIdeal T : Set A) := by
  constructor
  · intro hT
    simpa [hT.closure_eq] using (zeroLocus_vanishingIdeal_eq_closure 𝒜 T).symm
  · intro hT
    rw [hT]
    exact isClosed_zeroLocus 𝒜 (vanishingIdeal T : Set A)

/-- Every closed subset of `Proj(S)` is the zero locus of a homogeneous ideal. -/
-- Proof sketch: apply `isClosed_iff_eq_zeroLocus_vanishingIdeal` and use the canonical
-- homogeneous ideal `vanishingIdeal T`.
theorem isClosed_iff_exists_zeroLocus_homogeneousIdeal (T : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed T ↔ ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) := by
  constructor
  · intro hT
    exact ⟨vanishingIdeal T, (isClosed_iff_eq_zeroLocus_vanishingIdeal 𝒜 T).mp hT⟩
  · rintro ⟨I, rfl⟩
    simpa using isClosed_zeroLocus 𝒜 (I : Set A)

/-- The zero locus of a homogeneous ideal is empty exactly when its radical contains the irrelevant
ideal. -/
-- Proof sketch: if the irrelevant ideal lies in `√I`, then no relevant homogeneous prime contains
-- `I`. Conversely, if `V₊(I)` is empty and some positive-degree homogeneous element is not in
-- `√I`, localize away from it and use the affine chart together with the existence of a prime in a
-- nonzero localization to construct a point of `Proj(S)` containing `I`.
theorem zeroLocus_eq_empty_iff_irrelevant_le_radical :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔
      HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := sorry

end ProjectiveSpectrumTopology

section ProjBasicOpens

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- The scheme-level basis and chart constructions are owned by `Proj 𝒜`; this section keeps the
stronger `[AddSubgroupClass σ A]` context exactly where the scheme API needs it. -/

/- Lemma 10.57.3 (Topology on Proj): the standard opens `D₊(f)` form a basis for the topology on
`Proj(S)`. This is the canonical mathlib theorem `AlgebraicGeometry.Proj.isBasis_basicOpen`. -/
recall Proj.isBasis_basicOpen

/- The standard opens satisfy `D₊(fg) = D₊(f) ∩ D₊(g)`. This is
`AlgebraicGeometry.Proj.basicOpen_mul`. -/
recall Proj.basicOpen_mul

/-- Separating the degree-zero and positive-degree pieces of a basic open. -/
-- Proof sketch: start from `Proj.basicOpen_eq_iSup_proj 𝒜 g`, isolate the `i = 0` summand, and
-- reindex the remaining supremum by the subtype of positive degrees.
theorem proj_basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    Proj.basicOpen 𝒜 g =
      Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) := sorry

/-- A degree-zero basic open is the union of the positive-degree charts cut out by its multiples. -/
-- Proof sketch: the right-hand side is contained in `D₊(g₀)` by `Proj.basicOpen_mono`. For the
-- converse, if `g₀ ∉ p`, use that `p` is relevant to choose a positive-degree homogeneous element
-- outside `p`; then its product with `g₀` is still outside `p`.
theorem proj_basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    Proj.basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1, Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := sorry

/- For a homogeneous element of positive degree, the affine chart `D₊(f)` is canonically
isomorphic to `Spec(S_(f))`. This is `AlgebraicGeometry.Proj.basicOpenIsoSpec`. -/
recall Proj.basicOpenIsoSpec

end ProjBasicOpens
