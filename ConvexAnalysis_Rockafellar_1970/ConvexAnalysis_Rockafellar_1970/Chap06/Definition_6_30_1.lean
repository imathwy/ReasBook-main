import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

universe u

section

variable {E : Type u}
variable {β : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.1 introduces the hypograph of a concave function and recalls
  its effective domain.
- `core/canonical`: the relevant owner abstractions are the raw hypograph set
  `{p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1}`, the Chapter 1 effective-domain owner `dom(·)`, and
  mathlib's concavity/hypograph API `ConcaveOn.convex_hypograph` and
  `concaveOn_iff_convex_hypograph`.
- `bridge/view`: the chapter owner `hypo` (with restricted notation `hypo[S] g`) is the
  source-facing hypograph layer. The effective-domain bridge
  `x ∈ dom(-g) ↔ ⊥ < g x` is part of the Chapter 1 `dom(·)` owner API and is reused downstream.

Domain-style sampling used here:
- `epigraph` and `mem_epi_restrict_iff` from Chapter 1;
- `effectiveDomain`, `dom(·)`, `mem_effectiveDomain`, `mem_dom_neg_iff`,
  and `dom_neg_eq_setOf_bot_lt` from Chapter 1;
- `ConcaveOn.convex_hypograph` and `concaveOn_iff_convex_hypograph` from mathlib.

Primitive data vs derived API:
- primitive new owner: `hypo g S`;
- reused owner for the domain clause: `dom(-g)`, with its canonical Chapter 1 bridge lemmas;
- derived API: the membership simplifications for `hypo`, plus bridge lemmas
  `ConcaveOn.convex_hypo` and `concaveOn_iff_convex_hypo` re-expressing mathlib's raw
  hypograph-set characterization on the chapter owner surface.

Layer target:
- `source-facing` for `hypo`;
- `bridge/view` for the effective-domain clause, which reuses `dom(-g)` from the owner file
  `Definition_4_4` rather than introducing a Chapter 6-local duplicate.

Notation evaluation:
- the book writes the hypograph as `exp g`, but that notation clashes with Lean's exponential API;
  this file therefore uses the chapter-parallel owner name `hypo`, matching `epi`.
-/

/-- Definition 6.30.1: the hypograph of an ordered-valued function on a subset is the set
of pairs `(x, μ)` with `x ∈ S` and `μ ≤ g x`. -/
def hypo [LE β] (g : E → β) (S : Set E := Set.univ) : Set (E × β) :=
  {p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1}

/-- Chapter-parallel notation for the hypograph of `g` restricted to `S`. -/
notation:max "hypo[" S "] " g => hypo g S

/-- The restricted hypograph owner `hypo[S] g` is the set of pairs with base point in `S` and
height below `g`. -/
theorem hypo_eq_setOf_mem_and_le [LE β] (g : E → β) (S : Set E) :
    (hypo[S] g) = {p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1} :=
  rfl

/-- Restricting the hypograph owner to `S` is equivalent to intersecting the global hypograph with
the first-coordinate preimage of `S`. -/
theorem hypo_restrict_eq_preimage_fst_inter [LE β] (g : E → β) (S : Set E) :
    (hypo[S] g) = (Prod.fst ⁻¹' S) ∩ hypo g := by
  ext p
  rcases p with ⟨x, μ⟩
  simp [hypo]

/-- Restricting the hypograph owner to `Set.univ` gives the global hypograph. -/
@[simp] theorem hypo_univ [LE β] (g : E → β) :
    (hypo[Set.univ] g) = hypo g :=
  rfl

/-- Membership in `hypo[S] g` is the intrinsic owner-level pair condition. -/
@[simp] theorem mem_hypo_restrict_iff [LE β]
    {S : Set E} {g : E → β} {p : E × β} :
    p ∈ (hypo[S] g) ↔ p.1 ∈ S ∧ p.2 ≤ g p.1 :=
  Iff.rfl

/-- Coordinate view of membership in `hypo[S] g`. -/
@[simp] theorem mk_mem_hypo_restrict_iff [LE β]
    {S : Set E} {g : E → β} {x : E} {μ : β} :
    (x, μ) ∈ (hypo[S] g) ↔ x ∈ S ∧ μ ≤ g x :=
  Iff.rfl

/-- Membership in the global hypograph `hypo g` is the intrinsic pair inequality. -/
@[simp] theorem mem_hypo_iff [LE β] {g : E → β} {p : E × β} :
    p ∈ hypo g ↔ p.2 ≤ g p.1 := by
  rcases p with ⟨x, μ⟩
  simp [hypo]

/-- Coordinate view of membership in the global hypograph `hypo g`. -/
@[simp] theorem mk_mem_hypo_iff [LE β] {g : E → β} {x : E} {μ : β} :
    (x, μ) ∈ hypo g ↔ μ ≤ g x :=
  mem_hypo_iff (g := g) (p := (x, μ))

/-- Monotonicity in the restriction set for the hypograph owner. -/
theorem hypo_mono [LE β] {S T : Set E} {g : E → β} (hST : S ⊆ T) :
    (hypo[S] g) ⊆ (hypo[T] g) := by
  intro p hp
  exact ⟨hST hp.1, hp.2⟩

/-- The global hypograph `hypo g` is the set `{(x, μ) | μ ≤ g x}`. -/
theorem hypo_univ_eq_setOf_le [LE β] (g : E → β) :
    (hypo g) = {p : E × β | p.2 ≤ g p.1} := by
  simpa [hypo_univ] using (hypo_eq_setOf_mem_and_le (g := g) (S := Set.univ))

section ConvexBridge

variable {𝕜 : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]
variable {s : Set E} {g : E → β}

/-- Bridge to mathlib's concavity API: a concave map has convex restricted hypograph owner
`hypo[s] g`. -/
theorem ConcaveOn.convex_hypo (hg : ConcaveOn 𝕜 s g) :
    Convex 𝕜 (hypo[s] g) := by
  simpa [hypo] using hg.convex_hypograph

/-- Bridge to mathlib's canonical characterization: concavity on `s` is equivalent to convexity
of the restricted hypograph owner `hypo[s] g`. -/
theorem concaveOn_iff_convex_hypo :
    ConcaveOn 𝕜 s g ↔ Convex 𝕜 (hypo[s] g) := by
  simpa [hypo] using (concaveOn_iff_convex_hypograph (𝕜 := 𝕜) (s := s) (f := g))

end ConvexBridge

end
