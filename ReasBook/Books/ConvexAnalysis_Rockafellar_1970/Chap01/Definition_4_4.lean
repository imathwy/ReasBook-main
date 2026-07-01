import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u}
variable {α : Type v}
variable {β : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 4.4 introduces the effective domain via epigraph projection.
- `core/canonical`: for any ordered codomain with top, the effective domain is
  intrinsically `{x | f x < ⊤}`.
- `bridge/view`: `effectiveDomain_eq_image_fst_epi` recovers the textbook projection
  description for `WithTopBot α` codomain, while the canonical codomain-lift owners
  `Function.toWithTopBot` and `Bifunction.toWithTopBot` now live in `Chap01.EOrder.Basic`
  (with backward-compatible aliases).

Domain-style sampling used here:
- the chapter epigraph owner `epi`;
- codomain ordered-top structure;
- `WithTop α` and its canonical coercion into `WithTopBot α`;
- the order-theoretic predicate `f x < ⊤`.

Primitive data vs derived API:
- primitive object: for a ordered codomain with top, the effective-domain set
  `{x | f x < ⊤}`;
- derived API: the epigraph-projection characterization through `epi` for `WithTopBot α`, the
  value-level bridge from `WithTop α` into `WithTopBot α`, the function-level bridges
  `Function.toWithTopBot` and `Bifunction.toWithTopBot`, and the
  `dom(·)` notation used downstream for that owner set.
-/

/-- Definition 4.4: the effective domain of a function into a codomain with `(<)` and top
is the
set of points where the function is strictly below `⊤`. -/
def effectiveDomain [LT β] [Top β] (f : E → β) : Set E :=
  {x | f x < ⊤}

/-- Rockafellar's notation for the effective domain of a function with `(<)` and top codomain
data. -/
notation "dom(" f ")" => effectiveDomain f

/-- Scalar-parameterized notation for the relative interior of the effective domain. -/
scoped[Rockafellar] notation "riDom[" 𝕜 "](" f ")" => intrinsicInterior 𝕜 dom(f)

/-- Rockafellar's notation for the relative interior of the effective domain. -/
scoped[Rockafellar] notation "riDom(" f ")" => intrinsicInterior ℝ dom(f)

open scoped Rockafellar

/-- The scalar-parameterized notation `riDom[𝕜](f)` unfolds to intrinsic interior of `dom(f)`. -/
@[simp] theorem riDom_eq_intrinsicInterior_dom [LT β] [Top β] {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} {P : Type*} [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] (f : P → β) :
    riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f) :=
  rfl

/-- Membership in `riDom[𝕜](f)` is exactly membership in the intrinsic interior of `dom(f)`. -/
@[simp] theorem mem_riDom_iff [LT β] [Top β] {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} {P : Type*}
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
    {f : P → β} {x : P} :
    x ∈ riDom[𝕜](f) ↔ x ∈ intrinsicInterior 𝕜 dom(f) :=
  Iff.rfl

/-- Real-scalar notation `riDom(f)` is the `𝕜 = ℝ` specialization of `riDom[𝕜](f)`. -/
@[simp] theorem riDom_real_eq_intrinsicInterior_dom [LT β] [Top β]
    {V : Type*} {P : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace P] [AddTorsor V P]
    (f : P → β) :
    riDom(f) = intrinsicInterior ℝ dom(f) :=
  rfl

/-- Relative projection bridge: over a subset `S`, points of `S` in the effective domain are
exactly first coordinates of points in the restricted epigraph `epi[S] f`. -/
theorem effectiveDomain_inter_eq_image_fst_epi
    [Preorder α] [Nonempty α] (f : E → WithTopBot α)
    (S : Set E) :
    S ∩ dom(f) = Prod.fst '' (epi[S] f) := by
  ext x
  constructor
  · rintro ⟨hxS, hxdom⟩
    have hne_top : f x ≠ ⊤ := ne_of_lt hxdom
    by_cases hne_bot : f x = ⊥
    · rcases ‹Nonempty α› with ⟨μ⟩
      refine ⟨(x, μ), ?_, rfl⟩
      simp [hxS, hne_bot]
    · cases hfx : f x with
      | none => exact (hne_top hfx).elim
      | some y =>
          cases y with
          | bot => exact (hne_bot hfx).elim
          | coe a =>
              refine ⟨(x, a), ?_, rfl⟩
              refine (mem_epi_restrict_iff).2 ?_
              refine ⟨hxS, ?_⟩
              have hfx' : f x = (a : WithTopBot α) := by
                simpa using hfx
              exact hfx'.le
  · rintro ⟨⟨x', μ⟩, hμ, rfl⟩
    rcases (mem_epi_restrict_iff).1 hμ with ⟨hxS, hle⟩
    refine ⟨hxS, lt_of_le_of_lt hle ?_⟩
    simp

/-- The effective domain is the projection of the chapter epigraph owner onto the ambient space. -/
theorem effectiveDomain_eq_image_fst_epi
    [Preorder α] [Nonempty α] (f : E → WithTopBot α) :
    dom(f) = Prod.fst '' epi f := by
  simpa [Set.inter_comm] using
    (effectiveDomain_inter_eq_image_fst_epi (f := f) (S := Set.univ))

/-- A point belongs to the effective domain exactly when the function value is strictly below
`+∞`. -/
@[simp] theorem mem_effectiveDomain [LT β] [Top β] {f : E → β} {x : E} :
    x ∈ dom(f) ↔ f x < ⊤ :=
  Iff.rfl

/-- Helper for Definition 4.4: boundary-swapping negation on `WithTopBot α` lets the domain
statements for `-g` stay local to this item without importing the broken chapter wrapper. -/
local instance instNegWithTopBot [Neg α] : Neg (WithTopBot α) :=
  ⟨fun x =>
    match x with
    | ⊥ => ⊤
    | ⊤ => ⊥
    | (a : α) => (-a : α)⟩

/-- For `WithTopBot` codomain with negation, membership in `dom(-g)` is exactly strict
positivity of `g` above `-∞`. -/
@[simp] theorem mem_dom_neg_iff [Preorder α] [Neg α]
    {g : E → WithTopBot α} {x : E} :
    x ∈ dom(-g) ↔ ⊥ < g x := by
  change (-g x) < ⊤ ↔ ⊥ < g x
  by_cases htop : g x = ⊤
  · rw [htop]
    constructor
    · intro _
      change ((⊥ : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α))
      exact WithTop.coe_lt_top (⊥ : WithBot α)
    · intro _
      change ((⊥ : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α))
      exact WithTop.coe_lt_top (⊥ : WithBot α)
  · by_cases hbot : g x = ⊥
    · rw [hbot]
      constructor
      · intro hlt
        change (⊤ : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α)) at hlt
        exact False.elim ((lt_irrefl (⊤ : WithTop (WithBot α))) hlt)
      · intro hlt
        change
          ((⊥ : WithBot α) : WithTop (WithBot α)) <
            ((⊥ : WithBot α) : WithTop (WithBot α)) at hlt
        exact False.elim ((lt_irrefl (((⊥ : WithBot α) : WithTop (WithBot α)))) hlt)
    · cases hgx : g x using WithBotTop.rec with
      | bot => exact (htop (by simpa using hgx)).elim
      | top => exact (hbot (by simpa using hgx)).elim
      | coe a =>
          constructor
          · intro _
            change
              ((⊥ : WithBot α) : WithTop (WithBot α)) <
                (((a : α) : WithBot α) : WithTop (WithBot α))
            exact WithTop.coe_lt_coe.2 (WithBot.bot_lt_coe a)
          · intro _
            change ((((-a : α) : WithBot α) : WithTop (WithBot α)) < (⊤ : WithTop (WithBot α)))
            exact WithTop.coe_lt_top (((-a : α) : WithBot α))

/-- Set form of `mem_dom_neg_iff`: the effective domain of `-g` is where `g` is strictly above
`-∞`. -/
theorem dom_neg_eq_setOf_bot_lt [Preorder α] [Neg α]
    (g : E → WithTopBot α) :
    dom(-g) = {x : E | ⊥ < g x} := by
  ext x
  exact mem_dom_neg_iff

/-- Relative epigraph bridge: restricting to `S ∩ dom(f)` is equivalent to restricting to `S`. -/
@[simp] theorem epigraph_inter_effectiveDomain_eq [Preorder α]
    (f : E → WithTopBot α)
    (S : Set E) :
    (epi[S ∩ dom(f)] f) = (epi[S] f) := by
  ext ⟨x, μ⟩
  constructor
  · intro h
    rw [mem_epi_restrict_iff] at h
    rw [mem_epi_restrict_iff]
    exact ⟨h.1.1, h.2⟩
  · intro hμ
    rw [mem_epi_restrict_iff] at hμ
    rw [mem_epi_restrict_iff]
    exact ⟨⟨hμ.1, (mem_effectiveDomain).2 (lt_of_le_of_lt hμ.2 (by simp))⟩, hμ.2⟩

/-- Restricting the epigraph of `f` to its effective domain does not change the epigraph. -/
@[simp] theorem epigraph_effectiveDomain_eq [Preorder α] (f : E → WithTopBot α) :
    (epi[dom(f)] f) = (epi f) := by
  simpa [Set.inter_comm] using
    (epigraph_inter_effectiveDomain_eq (f := f) (S := Set.univ))

end
