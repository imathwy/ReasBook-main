import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_8_2 (from Chap16) -/
open CategoryTheory MorphismProperty
open CommRingCat

universe u₁ u₂

namespace RingHom

section

variable {R₁ : Type u₁} {Λ₁ : Type u₁} {R₂ : Type u₂} {Λ₂ : Type u₂}
variable [CommRing R₁] [CommRing Λ₁] [CommRing R₂] [CommRing Λ₂]

/- Domain sampling pass:
* primary domain: filtered colimits of smooth commutative ring maps and their stability under
  products;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the source-facing owner for PT presentations;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `Algebra.smooth_prod_iff`, the product criterion for smooth commutative algebras.
* best owner abstraction: the public owner here is `f.IsFilteredColimitOfSmooth`;
* primitive data: two ring homomorphisms `f₁`, `f₂`;
* derived API: any chosen filtered diagrams, cocones, and smooth stage maps witnessing PT.

Source/core/bridge triage:
* `source-facing`: PT is stable under products of ring maps;
* `core/canonical`: `f.IsFilteredColimitOfSmooth`;
* `bridge/view`: any chosen filtered diagram in `Under (CommRingCat.of _)` presenting the given
  product map.

The Noetherian and regular-map hypotheses from Situation 16.8.1 are mathematically redundant here,
so they should not remain in the public API.
-/

-- Proof sketch: choose filtered diagrams of smooth algebras presenting `f₁` and `f₂`. Their
-- product diagram is again filtered, each stage map to the product is smooth because smoothness is
-- preserved by finite products, and the product cocone presents `f₁.prodMap f₂` as the
-- corresponding filtered colimit.
/-- Lemma 16.8.2: if two ring maps satisfy PT, i.e. each is a filtered colimit of smooth algebras
over its source, then their product map also satisfies PT. -/
theorem smooth_ind_prodMap
    {f₁ : R₁ →+* Λ₁} {f₂ : R₂ →+* Λ₂}
    (hf₁ : f₁.IsFilteredColimitOfSmooth)
    (hf₂ : f₂.IsFilteredColimitOfSmooth) :
    (f₁.prodMap f₂).IsFilteredColimitOfSmooth := sorry

end

end RingHom

/-! ### Lemma_16_8_3 (from Chap16) -/
open IsLocalization

universe u v w

namespace Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]
variable [FinitePresentation R A]

section

variable (S : Submonoid R)

local notation:max "Rₛ" => Localization S
local notation:max "Aₛ" => Localization (Algebra.algebraMapSubmonoid A S)
local notation:max "Λₛ" => Localization (Algebra.algebraMapSubmonoid Λ S)
local notation:max "φₛ" =>
  IsLocalization.mapₐ S Rₛ Aₛ Λₛ (IsScalarTower.toAlgHom R A Λ)

/- Domain-style sampling:
- primary domain: localized smooth commutative algebra and descent from standard smooth
  localizations to elementary standard global elements;
- sampled owner declarations:
  `Smooth`,
  `IsLocalization.mapₐ`,
  `IsStandardSmooth`,
  `IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators`;
- best owner abstraction:
  `IsElementaryStandard R` is the source-facing owner for the descended Jacobian element, while
  the localized comparison map should be expressed directly by the canonical owner
  `IsLocalization.mapₐ`;
- primitive vs. derived:
  primitive public data are the localized smooth factorization and the descended global
  factorization with an elementary standard element. The standard smooth refinement and
  submersive presentation from Lemmas `16.3.4` and `16.3.6` are proof-level bridge data and
  should not appear as parallel wrapper structure in the public API.

Source/core/bridge triage:
- `source-facing`: the existence of a factorization `A → B → Λ` whose distinguished element from
  `S` becomes elementary standard in `B`;
- `core/canonical`: `Smooth`, `IsElementaryStandard`, and the localized comparison morphism
  `IsLocalization.mapₐ`;
- `bridge/view`: the intermediate standard smooth algebra and submersive presentation used to
  descend the Jacobian data from the localized factorization.
-/
-- Proof sketch: apply Lemma 16.3.4 over `Rₛ` to replace the given smooth factorization by one
-- through a standard smooth `Rₛ`-algebra. Then use Lemma 16.3.6 to choose a submersive
-- presentation whose first generators come from `A`, clear denominators in the extra generators,
-- the defining equations, and the Jacobian relation, and descend the presentation to a quotient
-- `B` of a polynomial algebra over `R`. The product of the cleared denominators is an element of
-- `S` whose image in `B` satisfies Definition 16.2.3.
/-- Lemma 16.8.3: from a factorization of the localized map `S⁻¹A → S⁻¹Λ` through a smooth
`Localization S`-algebra, one can descend to a factorization `A → B → Λ` such that some
`s ∈ S` maps to an elementary standard element of `B` over `R`. -/
theorem exists_factorization_with_elementaryStandard_of_localized_smooth_factorization
    {B' : Type (max u v w)} [CommRing B'] [Algebra Rₛ B'] [Smooth Rₛ B']
    (f' : Aₛ →ₐ[Rₛ] B') (g' : B' →ₐ[Rₛ] Λₛ)
    (hfactor : g'.comp f' = φₛ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B)
      (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (s : S),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
      IsElementaryStandard R (algebraMap R B s) := sorry

end

end

end Algebra

/-! ### Lemma_16_8_4 (from Chap16) -/
namespace Algebra

universe u

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain-style sampling:
- primary domain: regular ring maps of Noetherian commutative rings and the PT property
  `RingHom.IsFilteredColimitOfSmooth`;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `IsRegularRingMap`,
  `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers`,
  `RingHom.smooth_ind_prodMap`;
- best owner abstraction: PT is already owned by
  `(algebraMap R Λ).IsFilteredColimitOfSmooth`, while Situation `16.8.1` itself is owned by the
  ambient instance `[IsRegularRingMap R Λ]`;
- primitive vs. derived: the only primitive input of the reduction theorem is the field-case PT
  hypothesis phrased directly at that owner. Any chosen presentation of a filtered diagram of
  smooth algebras is derived API already packaged by `RingHom.IsFilteredColimitOfSmooth`.

Source/core/bridge triage:
- `source-facing`: the reduction from arbitrary regular maps to the case where the source is a
  field;
- `core/canonical`: `[IsRegularRingMap R Λ]` for the ambient situation and
  `(algebraMap R Λ).IsFilteredColimitOfSmooth` for PT;
- `bridge/view`: the auxiliary reductions through quotients, total quotient rings, and product
  decompositions used in the proof sketch.
-/

-- Proof sketch: for an arbitrary regular map `R → Λ`, consider the set of ideals `I ⊆ R` for
-- which the quotient map `R / I → Λ / IΛ` does not satisfy PT, and choose a maximal such ideal if
-- any exist. After replacing the situation by this quotient, every nonzero quotient satisfies PT,
-- so Proposition `16.5.3` shows `R` is reduced. Localizing at the nonzerodivisors reduces to the
-- total ring of fractions, which is a finite product of fields; apply Lemmas `16.8.2`, `16.8.3`,
-- `16.6.1`, and `16.7.2` to descend the field-case smooth factorization back to `Λ`.
/-- Lemma 16.8.4: if PT, namely `RingHom.IsFilteredColimitOfSmooth`, holds for every
Situation 16.8.1 whose source ring is a field, then PT holds for every Situation 16.8.1. -/
theorem isFilteredColimitOfSmooth_of_forall_field_cases
    (hfield :
      ∀ {K A : Type u} [Field K] [CommRing A] [Algebra K A]
        [IsNoetherianRing A] [(algebraMap K A).IsRegularRingMap],
        (algebraMap K A).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
