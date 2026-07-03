import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1 (from Chap01) -/
universe u v

section

variable {E : Type u}
variable {α : Type v} [LE α]

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.1 introduces the epigraph of an extended-valued function on a
  subset of an ambient space.
- `core/canonical`: mathlib's convexity and semicontinuity APIs use the raw epigraph predicate
  on `E × WithTopBot α`, namely `{q : E × WithTopBot α | q.1 ∈ S ∧ f q.1 ≤ q.2}`.
  In this project, the stable high-reuse owner on theorem surfaces is the finite-height view
  `epi`, obtained as pullback along `(x, μ) ↦ (x, (μ : WithTopBot α))`.
- `bridge/view`: the textbook notations `epi[S] f` and `epi f`, together with the companion
  membership lemmas below, are the source-facing views of that owner.
- Primitive data vs derived API: the primitive inputs are the subset `S` and the ambient function
  `f : E → WithTopBot α`; the restricted and global membership lemmas are derived API.
-/

/-- Definition 4.1: the epigraph of a `WithTopBot`-valued function on a subset is the set of
pairs `(x, μ)` with `x` in the domain subset and `f x ≤ μ`. -/
def epi (f : E → WithTopBot α) (S : Set E := Set.univ) : Set (E × α) :=
  (fun p : E × α => (p.1, (p.2 : WithTopBot α))) ⁻¹'
    {q : E × WithTopBot α | q.1 ∈ S ∧ f q.1 ≤ q.2}

/-- Textbook notation for the epigraph of `f` restricted to `S`. -/
notation:max "epi[" S "] " f => epi f S

theorem epi_eq_preimage_fullEpigraph_setOf (f : E → WithTopBot α) (S : Set E) :
    (epi[S] f) =
      (fun p : E × α => (p.1, (p.2 : WithTopBot α))) ⁻¹'
        {q : E × WithTopBot α | q.1 ∈ S ∧ f q.1 ≤ q.2} :=
  rfl

theorem epi_eq_setOf_mem_and_le (f : E → WithTopBot α) (S : Set E) :
    (epi[S] f) = {p : E × α | p.1 ∈ S ∧ f p.1 ≤ p.2} :=
by
  ext p
  simp [epi]

theorem epi_restrict_eq_preimage_fst_inter (f : E → WithTopBot α) (S : Set E) :
    (epi[S] f) = (Prod.fst ⁻¹' S) ∩ epi f := by
  ext p
  rcases p with ⟨x, μ⟩
  simp [epi]

@[simp] theorem epi_univ (f : E → WithTopBot α) :
    (epi[Set.univ] f) = epi f :=
  rfl

/-- Membership in `epi[S] f` is the intrinsic owner-level pair condition:
the base coordinate lies in `S` and the height coordinate lies above `f`. -/
@[simp] theorem mem_epi_restrict_iff {S : Set E} {f : E → WithTopBot α} {p : E × α} :
    p ∈ (epi[S] f) ↔ p.1 ∈ S ∧ f p.1 ≤ p.2 :=
by
  simp [epi]

/-- Coordinate view of membership in `epi[S] f`. -/
@[simp] theorem mk_mem_epi_restrict_iff {S : Set E} {f : E → WithTopBot α} {x : E} {μ : α} :
    (x, μ) ∈ (epi[S] f) ↔ x ∈ S ∧ f x ≤ μ :=
by
  simp [epi]

/-- Membership in the global epigraph `epi f` is the intrinsic pair inequality. -/
@[simp] theorem mem_epi_iff {f : E → WithTopBot α} {p : E × α} :
    p ∈ epi f ↔ f p.1 ≤ p.2 := by
  rcases p with ⟨x, μ⟩
  simp

/-- Coordinate view of membership in `epi f`. -/
@[simp] theorem mk_mem_epi_iff {f : E → WithTopBot α} {x : E} {μ : α} :
    (x, μ) ∈ epi f ↔ f x ≤ μ := by
  exact mem_epi_iff (f := f) (p := (x, μ))

theorem epi_mono {S T : Set E} {f : E → WithTopBot α} (hST : S ⊆ T) :
    (epi[S] f) ⊆ (epi[T] f) := by
  intro p hp
  rcases (mem_epi_restrict_iff (S := S) (f := f) (p := p)).1 hp with ⟨hpS, hpLe⟩
  exact (mem_epi_restrict_iff (S := T) (f := f) (p := p)).2 ⟨hST hpS, hpLe⟩

/-- The global epigraph `epi f` of a `WithTopBot`-valued function is the usual set
`{(x, μ) | f x ≤ μ}`. -/
theorem epi_univ_eq_setOf_le (f : E → WithTopBot α) :
    (epi f) = {p : E × α | f p.1 ≤ p.2} := by
  simpa [epi_univ] using epi_eq_setOf_mem_and_le f (S := Set.univ)

end

/-! ### Theorem_4_1 (from Chap01) -/
/-!
Source/core/bridge triage:
- `source-facing`: Theorem 4.1 is Rockafellar's Jensen inequality criterion for convexity on a
  convex set `C`.
- `core/canonical`: the owner surface is the canonical `ConvexOn 𝕜 C f` predicate.
- `bridge/view`: the displayed two-point inequality uses the same codomain scalar action as
  `ConvexOn`; no strict finite-height slack is part of this theorem.
-/

universe u v w

section

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type w} {E : Type u} {α : Type v}
variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid (WithTopBot α)] [PartialOrder (WithTopBot α)]
variable [IsOrderedAddMonoid (WithTopBot α)]
variable [SMul 𝕜 (WithTopBot α)] [PosSMulMono 𝕜 (WithTopBot α)]
variable {C : Set E}

/-- Theorem 4.1, forward direction: a convex function satisfies the displayed Jensen inequality
on every open segment in its convex domain. -/
theorem ConvexOn.le_affine_combination {f : E → WithTopBot α}
    (hf : ConvexOn 𝕜 C f)
    {x y : E} (hxC : x ∈ C) (hyC : y ∈ C)
    {t : 𝕜} (ht0 : 0 < t) (ht1 : t < 1) :
    f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y := by
  sorry

/-- Theorem 4.1: on a convex domain, convexity is equivalent to the two-point Jensen inequality
for every `0 < t < 1`. -/
theorem convexOn_iff_jensen_open_segment {f : E → WithTopBot α}
    (hC : Convex 𝕜 C) :
    ConvexOn 𝕜 C f ↔
      ∀ x y : E, x ∈ C → y ∈ C → ∀ t : 𝕜, 0 < t → t < 1 →
        f ((1 - t) • x + t • y) ≤ (1 - t) • f x + t • f y := by
  sorry

end
