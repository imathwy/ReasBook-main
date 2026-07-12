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

/-
Chap10 Lemma 10 57 3 Topology on Proj: the three public declarations below record the empty
zero-locus criterion and the two standard-open decompositions used in the topology on `Proj(S)`.
-/
-- recall zeroLocus_eq_empty_iff_irrelevant_le_radical / proj_basicOpen_eq_projZero_sup_iSup_pos / proj_basicOpen_degreeZero_eq_iSup_mul

/-
/-- Validator bridge for Chap10 Lemma 10 57 3 Topology on Proj: records the three public
declarations that together form the planned main result for this item. -/
theorem zeroLocus_eq_empty_iff_irrelevant_le_radical / proj_basicOpen_eq_projZero_sup_iSup_pos / proj_basicOpen_degreeZero_eq_iSup_mul
-/

/-- Zero-locus clause for Chap10 Lemma 10 57 3 Topology on Proj: the zero locus of a
homogeneous ideal is empty
exactly when its radical contains the irrelevant ideal. -/
-- Proof sketch: if the irrelevant ideal lies in `√I`, then no relevant homogeneous prime contains
-- `I`. Conversely, if `V₊(I)` is empty and some positive-degree homogeneous element is not in
-- `√I`, localize away from it and use the affine chart together with the existence of a prime in a
-- nonzero localization to construct a point of `Proj(S)` containing `I`.
theorem zeroLocus_eq_empty_iff_irrelevant_le_radical :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔
      HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := by
  classical
  constructor
  · intro hEmpty
    -- Show each positive-degree homogeneous element lies in `√I`; otherwise it yields a point
    -- of `Proj(S)` containing `I`, contradicting the empty zero locus.
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi x hx
    by_contra hxRadical
    change x ∉ I.radical.toIdeal at hxRadical
    rw [HomogeneousIdeal.coe_radical, I.isHomogeneous.radical_eq, Ideal.mem_sInf] at hxRadical
    have hxWitness :
        ∃ J : Ideal A, Ideal.IsHomogeneous 𝒜 J ∧ I.toIdeal ≤ J ∧ J.IsPrime ∧ x ∉ J := by
      by_contra h
      apply hxRadical
      intro J hJ
      by_contra hxJ
      exact h ⟨J, hJ.1, hJ.2.1, hJ.2.2, hxJ⟩
    obtain ⟨J, hJHom, hIJ, hJPrime, hxJ⟩ := hxWitness
    let JHom : HomogeneousIdeal 𝒜 := ⟨J, hJHom⟩
    have hJRelevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ JHom := by
      intro hIrrelevant
      have hxHom : x ∈ 𝒜 i := by
        simpa using hx
      exact hxJ (hIrrelevant (HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) hi hxHom))
    let y : ProjectiveSpectrum 𝒜 :=
      ⟨JHom, hJPrime, hJRelevant⟩
    have hy : y ∈ zeroLocus 𝒜 (I : Set A) := by
      rw [ProjectiveSpectrum.mem_zeroLocus]
      exact hIJ
    have : y ∈ (∅ : Set (ProjectiveSpectrum 𝒜)) := by
      simpa [hEmpty] using hy
    exact this.elim
  · intro hIrrelevant
    -- Any point of `V₊(I)` contains `√I`, hence would contain the irrelevant ideal.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hIx : I.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
      simpa [ProjectiveSpectrum.mem_zeroLocus] using hx
    have hRadicalx : I.radical ≤ x.asHomogeneousIdeal := by
      change I.radical.toIdeal ≤ x.asHomogeneousIdeal.toIdeal
      simpa [HomogeneousIdeal.coe_radical, x.isPrime.radical] using Ideal.radical_mono hIx
    exact x.not_irrelevant_le (hIrrelevant.trans hRadicalx)

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

/-- Within Chap10 Lemma 10 57 3 Topology on Proj, the standard opens `D₊(f)` form a basis for
the topology on `Proj(S)`. -/
theorem proj_isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (Proj.basicOpen 𝒜)) := by
  simpa using Proj.isBasis_basicOpen (𝒜 := 𝒜)

/- The standard opens satisfy `D₊(fg) = D₊(f) ∩ D₊(g)`. This is
`AlgebraicGeometry.Proj.basicOpen_mul`. -/
recall Proj.basicOpen_mul

/-- Helper for Chap10 Lemma 10 57 3 Topology on Proj: split an existential over natural
degrees into the degree-zero case and the positive-degree subtype. -/
private lemma exists_nat_iff_zero_or_positiveSubtype {P : ℕ → Prop} :
    (∃ i : ℕ, P i) ↔ P 0 ∨ ∃ i : {n : ℕ // 1 ≤ n}, P i.1 := by
  constructor
  · rintro ⟨i, hi⟩
    -- Separate the degree witness into the zero summand or the positive-degree indexed summand.
    rcases Nat.eq_zero_or_pos i with rfl | hiPos
    · exact Or.inl hi
    · exact Or.inr ⟨⟨i, Nat.succ_le_of_lt hiPos⟩, hi⟩
  · rintro (hZero | ⟨i, hi⟩)
    -- Forget the subtype index when returning to the original existential over all degrees.
    · exact ⟨0, hZero⟩
    · exact ⟨i.1, hi⟩

/-- Positive-degree decomposition clause for Chap10 Lemma 10 57 3 Topology on Proj: separating
the degree-zero and positive-degree pieces of a basic open. -/
-- Proof sketch: start from `Proj.basicOpen_eq_iSup_proj 𝒜 g`, isolate the `i = 0` summand, and
-- reindex the remaining supremum by the subtype of positive degrees.
theorem proj_basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    Proj.basicOpen 𝒜 g =
      Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) := by
  -- Rewrite `D₊(g)` as the supremum over homogeneous projections and split the degree index into
  -- the zero piece and the positive pieces.
  rw [TopologicalSpace.Opens.ext_iff, Set.ext_iff, Proj.basicOpen_eq_iSup_proj]
  intro x
  rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
  change (∃ i : ℕ, x ∈ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i g)) ↔
      x ∈ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g)
  rw [TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_iSup]
  simp only [Proj.mem_basicOpen]
  exact exists_nat_iff_zero_or_positiveSubtype

/-- Degree-zero basic-open clause for Chap10 Lemma 10 57 3 Topology on Proj: a degree-zero basic
open is the union of the positive-degree charts cut out by its multiples. -/
-- Proof sketch: the right-hand side is contained in `D₊(g₀)` by `Proj.basicOpen_mono`. For the
-- converse, if `g₀ ∉ p`, use that `p` is relevant to choose a positive-degree homogeneous element
-- outside `p`; then its product with `g₀` is still outside `p`.
theorem proj_basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    Proj.basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1, Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := by
  rw [TopologicalSpace.Opens.ext_iff, Set.ext_iff]
  intro x
  change x ∈ Proj.basicOpen 𝒜 (g₀ : A) ↔
      x ∈ ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1, Proj.basicOpen 𝒜 ((g₀ : A) * (f : A))
  rw [TopologicalSpace.Opens.mem_iSup]
  simp only [Proj.mem_basicOpen]
  constructor
  · intro hg₀
    -- If every positive-degree multiple of `g₀` vanished at `x`, primeness would force every
    -- positive-degree homogeneous element into `x`, contradicting relevance.
    by_contra hCover
    have hCover' : ∀ d : {n : ℕ // 0 < n}, ∀ f : 𝒜 d.1,
        ((g₀ : A) * (f : A)) ∈ x.asHomogeneousIdeal := by
      intro d f
      have hdCover : x ∉ ⨆ f : 𝒜 d.1, Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := by
        intro hd
        exact hCover ⟨d, hd⟩
      have hNotMem : x ∉ Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := by
        intro hMem
        exact hdCover (by
          rw [TopologicalSpace.Opens.mem_iSup]
          exact ⟨f, hMem⟩)
      simpa [Proj.mem_basicOpen] using hNotMem
    refine x.not_irrelevant_le ?_
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi y hy
    have hyHom : y ∈ 𝒜 i := by
      simpa using hy
    have hmul : ((g₀ : A) * (y : A)) ∈ x.asHomogeneousIdeal := by
      simpa using hCover' ⟨i, hi⟩ ⟨y, hyHom⟩
    exact (x.isPrime.mem_or_mem hmul).resolve_left hg₀
  · rintro ⟨d, hMul⟩ hg₀
    rw [TopologicalSpace.Opens.mem_iSup] at hMul
    obtain ⟨f, hMul⟩ := hMul
    exact hMul (Ideal.mul_mem_right _ _ hg₀)

/- For a homogeneous element of positive degree, the affine chart `D₊(f)` is canonically
isomorphic to `Spec(S_(f))`. This is `AlgebraicGeometry.Proj.basicOpenIsoSpec`. -/
recall Proj.basicOpenIsoSpec

end ProjBasicOpens
