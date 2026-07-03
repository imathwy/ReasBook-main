import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_11_1 (from Chap07) -/
universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/- Domain-style sampling for Definition 7.11.1:
- primary domain: injective and surjective morphisms of set-valued sheaves on a Grothendieck
  site, expressed through the canonical sheaf-local owner predicates;
- sampled canonical declarations:
  `CategoryTheory.Sheaf.IsLocallyInjective`,
  `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`,
  `CategoryTheory.Sheaf.IsLocallySurjective`,
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`;
- best owner abstraction: for the sheaf-level source notion, the owner predicates are
  `CategoryTheory.Sheaf.IsLocallyInjective` and `CategoryTheory.Sheaf.IsLocallySurjective`;
- primitive data: a morphism of sheaves of sets;
- derived API: the objectwise injectivity criterion on sections and later categorical
  characterizations such as `Mono`/`Epi`.

Source/core/bridge triage:
- `source-facing`: the Stacks predicates that a morphism of sheaves of sets is injective
  objectwise on sections and surjective locally on the site;
- `core/canonical`: the owner predicates `CategoryTheory.Sheaf.IsLocallyInjective` and
  `CategoryTheory.Sheaf.IsLocallySurjective`;
- `bridge/view`: the companion theorem
  `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`, which rewrites the local injectivity
  owner in the textbook objectwise form; for later chapter lemmas, the surjectivity owner also
  has the categorical bridge `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.

No extra chapter-local definition is warranted here: the source notions are already owned by the
sheaf namespace, and this file should stay at the canonical recall layer. -/

/- Definition 7.11.1 (1): for a morphism of sheaves of sets, the canonical injectivity owner is
`Sheaf.IsLocallyInjective`; for sheaves this agrees with the textbook objectwise injectivity
condition recorded in the companion theorem below. -/
recall IsLocallyInjective

/- Definition 7.11.1 (1), canonical objectwise form: the exact mathlib companion theorem says
that a morphism of sheaves is locally injective exactly when each component map on the
underlying presheaf is injective. -/
recall isLocallyInjective_iff_injective

/- Definition 7.11.1 (2): a morphism of sheaves of sets is surjective when every section of the
target is locally in the image; this is the canonical notion
`Sheaf.IsLocallySurjective`. -/
recall IsLocallySurjective

end Sheaf

end CategoryTheory

/-! ### Lemma_7_11_2 (from Chap07) -/
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
    -- First convert local injectivity into injectivity on each section map.
    -- The sheaf owner lemma `mono_of_injective` then upgrades this objectwise data to `Mono φ`.
    exact mono_of_injective φ ((isLocallyInjective_iff_injective (φ := φ)).1 hφ)
  · intro hφ
    -- Reduce the sheaf-local predicate to injectivity of the underlying section maps.
    rw [isLocallyInjective_iff_injective]
    intro X
    -- Map the sheaf monomorphism to the underlying presheaf morphism.
    have hmono_hom : Mono φ.hom := by
      letI : Mono φ := hφ
      exact (sheafToPresheaf J (Type w)).map_mono φ
    -- The presheaf companion criterion identifies monomorphisms with objectwise injectivity.
    exact (Presheaf.mono_iff_injective φ.hom).1 hmono_hom X.unop

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

/-! ### Lemma_7_11_3 (from Chap07) -/
universe u v w

namespace CategoryTheory

open Limits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J (Type w)}

/-
Domain-style sampling for Lemma 7.11.3:
- primary domain: kernel pairs, effective epimorphisms, and coequalizers in the sheaf category;
- sampled owner declarations:
  `Sheaf.epi_of_isLocallySurjective`,
  `regularEpiOfEpi`,
  `isColimitCoforkOfEffectiveEpi`,
  `effectiveEpi_of_kernelPair`;
- best owner abstraction: `isColimitCoforkOfEffectiveEpi` is the canonical owner for the
  coequalizer-of-kernel-pair statement, with `Sheaf.epi_of_isLocallySurjective` as the
  sheaf-specific bridge from the source hypothesis to the categorical owner API;
- primitive data: a morphism `φ : F ⟶ G` together with the source-facing hypothesis that `φ`
  is locally surjective;
- derived API: the induced `Epi` and `EffectiveEpi` instances and the resulting colimit structure
  on the canonical kernel-pair cofork, under the ambient categorical owner hypothesis that
  `Sheaf J (Type w)` is a regular epi category.

Source/core/bridge triage:
- `source-facing`: a locally surjective morphism of sheaves of sets is the coequalizer of its
  kernel pair;
- `core/canonical`: `isColimitCoforkOfEffectiveEpi`;
- `bridge/view`: `Sheaf.epi_of_isLocallySurjective` and `regularEpiOfEpi`.
-/

namespace Sheaf

/-- Lemma 7.11.3: a locally surjective morphism of sheaves of sets is the coequalizer of the two
projections from its kernel pair. -/
noncomputable def isColimitCoforkOfIsLocallySurjective
    [IsRegularEpiCategory (Sheaf J (Type w))]
    (φ : F ⟶ G) (hφ : IsLocallySurjective φ) :
    IsColimit (Cofork.ofπ φ pullback.condition) := by
  let _ : IsLocallySurjective φ := hφ
  let _ : EffectiveEpi φ := (regularEpiOfEpi φ).effectiveEpi
  exact isColimitCoforkOfEffectiveEpi φ (pullback.cone φ φ) (pullback.isLimit φ φ)

/-- The canonical coequalizer witness attached to a locally surjective sheaf morphism agrees with
the standard effective-epimorphism coequalizer witness. -/
-- Proof sketch: unfold `isColimitCoforkOfIsLocallySurjective` and simplify the local bridge
-- instances to identify it with `isColimitCoforkOfEffectiveEpi`.
theorem isColimitCoforkOfIsLocallySurjective_spec
    [IsRegularEpiCategory (Sheaf J (Type w))]
    (φ : F ⟶ G) (hφ : IsLocallySurjective φ) :
    let _ : IsLocallySurjective φ := hφ
    let _ : EffectiveEpi φ := (regularEpiOfEpi φ).effectiveEpi
    isColimitCoforkOfIsLocallySurjective φ hφ =
      isColimitCoforkOfEffectiveEpi φ (pullback.cone φ φ) (pullback.isLimit φ φ) := by
  -- Unfold the source-facing witness so the local bridge instances reduce to the canonical one.
  rfl

end Sheaf

end CategoryTheory
