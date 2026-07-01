import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling:
- primary domain: the Hom complex of cochain complexes and its degree-zero cocycles;
- sampled owner declarations:
  `CochainComplex.HomComplex.Cocycle.equivHom`,
  `CochainComplex.HomComplex.Cocycle.mem_iff`,
  `CochainComplex.HomComplex.Cocycle.ofHom`,
  `CochainComplex.HomComplex.Cocycle.homOf`;
- best owner abstraction: `CochainComplex.HomComplex.Cocycle`, whose degree-zero specialization is
  canonically equivalent to actual morphisms of cochain complexes via `Cocycle.equivHom`;
- primitive data vs. derived API:
  primitive owner data is the cocycle subtype together with the canonical equivalence
  `Cocycle.equivHom`, while the textbook existential criterion for a degree-zero cochain is only a
  source-facing bridge derived from that owner API and the cocycle criterion `Cocycle.mem_iff`;
- ambient minimization: all sampled declarations already live over an arbitrary preadditive
  category, so the remark should be stated for `{C} [Category C] [Preadditive C]` rather than the
  special model `CochainComplex (ModuleCat R) ℤ`;
- source/core/bridge triage:
  `source-facing`: the remark that a degree-zero cochain defines a morphism exactly when its
    differential vanishes;
  `core/canonical`: `Cocycle.equivHom`, `Cocycle.mem_iff`, `Cocycle.ofHom`, `Cocycle.homOf`;
  `bridge/view`: the theorem below translating the textbook existential wording into the canonical
    degree-zero cocycle owner.
-/

/- Remark 15.72.2 is owned canonically by the additive equivalence between morphisms of cochain
complexes and degree-zero cocycles in the Hom complex. -/
recall Cocycle.equivHom

/- The cocycle condition in degree `0` is exactly the vanishing of the Hom-complex differential. -/
recall Cocycle.mem_iff

/-- Companion bridge for Remark 15.72.2: a degree-zero element of the Hom complex
`Hom^•(K^•, L^•)` defines a morphism of complexes exactly when its differential vanishes. -/
theorem degreeZeroCochain_defines_morphism_iff_d_eq_zero (z : Cochain K L 0) :
    (∃ f : K ⟶ L, Cochain.ofHom f = z) ↔ δ 0 1 z = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    simpa using (Cocycle.ofHom f).δ_eq_zero 1
  · intro hz
    let z₀ : Cocycle K L 0 := Cocycle.mk z 1 (zero_add 1) hz
    refine ⟨z₀.homOf, ?_⟩
    change Cochain.ofHom z₀.homOf = (z₀ : Cochain K L 0)
    exact Cocycle.cochain_ofHom_homOf_eq_coe z₀
