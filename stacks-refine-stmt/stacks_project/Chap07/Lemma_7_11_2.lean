import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_3_1
import stacks_project.Chap07.Definition_7_11_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.11.2:
- primary domain: monomorphisms, epimorphisms, and isomorphisms of set-valued sheaves on a site;
- sampled owner declarations:
  `Sheaf.IsLocallyInjective`,
  `Presheaf.mono_iff_injective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Sheaf.isLocallyBijective_iff_isIso`;
- best owner abstraction: the intrinsic owner predicates on sheaf morphisms together with the
  canonical categorical classes `Mono`, `Epi`, and `IsIso`;
- primitive data: only a morphism `φ : F ⟶ G`;
- derived API: the source-facing equivalences relating the sheaf-local predicates to
  `Mono`/`Epi`/`IsIso`, with clause `(1)` derived through the chapter owner theorem
  `Presheaf.mono_iff_injective`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma comparing injective, surjective, and bijective morphisms of
  sheaves of sets with the categorical notions mono, epi, and iso;
- `core/canonical`: the mathlib owners listed above;
- `bridge/view`: the owner-namespace companion `Sheaf.isLocallyInjective_iff_mono` for clause
  `(1)`, since clauses `(2)` and `(3)` already have exact canonical owner theorems.
-/

namespace Sheaf

/-- Lemma 7.11.2 (1): the source-facing injectivity predicate for morphisms of sheaves of sets
agrees with the canonical categorical notion of monomorphism. -/
theorem isLocallyInjective_iff_mono {F G : Sheaf J (Type w)} (φ : F ⟶ G) :
    IsLocallyInjective φ ↔ Mono φ := by
  constructor
  · intro hφ
    letI : IsLocallyInjective φ := hφ
    exact mono_of_isLocallyInjective φ
  · intro hφ
    rw [isLocallyInjective_iff_injective]
    intro X
    letI : Mono φ.hom := (sheafToPresheaf J (Type w)).map_mono φ
    exact (Presheaf.mono_iff_injective φ.hom).1
      inferInstance X.unop

/-
Lemma 7.11.2 (2): the surjective morphisms of sheaves of sets are exactly the epimorphisms.
This is the exact canonical theorem `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.
-/
section

variable [HasSheafify J (Type w)]

recall Sheaf.isLocallySurjective_iff_epi

/- Lemma 7.11.2 (3): a morphism of sheaves of sets is an isomorphism if and only if it is both
injective and surjective. This is the exact canonical theorem
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`. -/
recall Sheaf.isLocallyBijective_iff_isIso

end

end Sheaf

end CategoryTheory
