import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_17_1 (from Chap06) -/
open TopCat

universe u

section

/- Domain-style sampling for Lemma 6.17.1:
- primary domain: sheafification of set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.IsSheaf`,
  `GrothendieckTopology.sheafify_isSheaf`;
- source/core/bridge triage:
  `source-facing`: the textbook assertion that the associated presheaf `ℱ^#` is a sheaf;
  `core/canonical`: the bundled sheafification owner `TopCat.Presheaf.sheafify`;
  `bridge/view`: the underlying-presheaf sheaf predicate `ℱ.sheafify.presheaf.IsSheaf`.

Primitive data are only the topological space `X` and the presheaf `ℱ`. The sheaf-condition proof
is not primitive data here: it is already carried by the bundled owner `ℱ.sheafify`. Therefore the
file should expose the owner directly and treat the unbundled `IsSheaf` statement as a companion
view, rather than keeping a duplicate local theorem wrapper around `.property`.
-/

recall TopCat.Presheaf.sheafify

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

/- Lemma 6.17.1: for a set-valued presheaf `ℱ` on `X`, the associated presheaf `ℱ^#`,
formalized by the underlying presheaf of `ℱ.sheafify`, is a sheaf. This is the sheaf-condition
proof carried by the canonical owner `TopCat.Presheaf.sheafify`. -/
#check (ℱ.sheafify.property : ℱ.sheafify.presheaf.IsSheaf)

end

/-! ### Lemma_6_17_2 (from Chap06) -/
open TopCat

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u)) (x : X)

/- Domain-style sampling for Lemma 6.17.2:
- primary domain: sheafification and stalks of set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.stalkToFiber`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the canonical stalk isomorphism
  `TopCat.Presheaf.sheafifyStalkIso`;
- primitive data: the space `X`, the presheaf `ℱ`, and the point `x : X`;
- derived API: the map on stalks induced by `toSheafify` and its inverse `stalkToFiber`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project statement identifying the stalk of `ℱ^#` at `x` with `ℱ_x`;
- `core/canonical`: `TopCat.Presheaf.sheafifyStalkIso`;
- `bridge/view`: the intermediate morphism `TopCat.Presheaf.stalkToFiber` and the isomorphism on
  stalks induced by `toSheafify`. -/

/- Lemma 6.17.2: the canonical comparison between the stalk of the sheafification `ℱ^#` at `x`
and the original stalk `ℱ_x` is exactly the owner isomorphism `TopCat.Presheaf.sheafifyStalkIso`.
-/
recall TopCat.Presheaf.sheafifyStalkIso

/- Source-facing specialization: for `x : X`, the stalk of `ℱ^#` at `x` is canonically
isomorphic to the original stalk `ℱ_x`. -/
#check (ℱ.sheafifyStalkIso x : ℱ.sheafify.presheaf.stalk x ≅ ℱ.stalk x)

end

/-! ### Lemma_6_17_3 (from Chap06) -/
open CategoryTheory TopCat
open TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u)) (𝒢 : X.Sheaf (Type u))
local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.17.3:
- primary domain: sheafification of set-valued presheaves on a topological space;
- sampled owner API:
  `CategoryTheory.sheafificationAdjunction`,
  `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafifyLift`,
  `CategoryTheory.toSheafify_sheafifyLift`,
  `CategoryTheory.sheafifyLift_unique`;
- best owner abstraction: the sheafification adjunction
  `sheafificationAdjunction J (Type u)`, with `toSheafify J` as the unit and
  `sheafifyLift J` as the derived universal morphism API;
- primitive data: the presheaf `ℱ`, the sheaf `𝒢`, and a morphism `φ : ℱ ⟶ 𝒢.presheaf`;
- derived API: the factorization of `φ` through `toSheafify J ℱ` and its uniqueness.

Source/core/bridge triage:
- `source-facing`: the Stacks-style unique factorization of maps `ℱ ⟶ 𝒢.presheaf` through
  the sheafification unit;
- `core/canonical`: the sheafification adjunction `sheafificationAdjunction J (Type u)`;
- `bridge/view`: the specialized lift `sheafifyLift J φ 𝒢.property` and its uniqueness theorem
  on underlying presheaves. -/

/- Lemma 6.17.3: for a set-valued presheaf `ℱ` and a sheaf `𝒢` on `X`, every morphism
`φ : ℱ ⟶ 𝒢.presheaf` factors uniquely through the canonical sheafification unit.
The canonical owner surface is the adjunction hom-equivalence together with the specialized
lift API below. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.sheafifyLift
recall CategoryTheory.toSheafify_sheafifyLift
recall CategoryTheory.sheafifyLift_unique

variable {ℱ 𝒢}

/- The owner equivalence for this topological-space specialization. -/
#check (sheafificationAdjunction J (Type u)).homEquiv ℱ 𝒢

/- Source-facing specialization: the universal factorization is the canonical lift
`sheafifyLift J φ 𝒢.property`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ sheafifyLift J φ 𝒢.property :
  (ℱ ⟶ 𝒢.presheaf) → (sheafify J ℱ ⟶ 𝒢.presheaf))

/- The factorization equation is exactly `toSheafify_sheafifyLift`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ toSheafify_sheafifyLift J φ 𝒢.property :
  ∀ φ : ℱ ⟶ 𝒢.presheaf, toSheafify J ℱ ≫ sheafifyLift J φ 𝒢.property = φ)

/- Uniqueness is exactly `sheafifyLift_unique`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ fun γ : sheafify J ℱ ⟶ 𝒢.presheaf ↦
  sheafifyLift_unique J φ 𝒢.property γ)

end

/-! ### Example_6_17_4 (from Chap06) -/
/- Domain-style sampling for Example 6.17.4:
- primary domain: set-valued sheaves on a topological space, specifically the comparison between
  the canonical constant sheaf and the source-facing sheaf of locally constant functions;
- sampled owner API:
  `CategoryTheory.constantSheaf`,
  `locallyConstantSheaf`,
  `constantSheafToLocallyConstantSheaf`,
  `constantSheafToLocallyConstantSheaf_isIso`;
- source/core/bridge triage:
  `source-facing`: the sheaf of locally constant `A`-valued functions on `X`;
  `core/canonical`: `CategoryTheory.constantSheaf`;
  `bridge/view`: `constantSheafToLocallyConstantSheaf`, while the isomorphism fact for that
  comparison belongs to the derived API.

The owner abstraction for this example is therefore the project-level bridge
`constantSheafToLocallyConstantSheaf`, not a new `Iso` wrapper around it. Primitive data are only
the space `X`, the value type `A`, and the source-facing sheaf `locallyConstantSheaf X A`; the
`IsIso` fact for the comparison morphism belongs to derived API.
-/

/- Example 6.17.4: the canonical comparison from the constant sheaf with value `A` to the
source-facing sheaf of locally constant `A`-valued functions is the upstream bridge
`constantSheafToLocallyConstantSheaf`, and its invertibility is the companion theorem
`constantSheafToLocallyConstantSheaf_isIso`. -/
recall constantSheafToLocallyConstantSheaf

recall constantSheafToLocallyConstantSheaf_isIso

/-! ### Lemma_6_17_5 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.17.5:
- primary domain: separated presheaves of sets and sheafification on a topological space;
- inspected owner declarations:
  `TopCat.Presheaf.isSeparated_iff_injective_toStalkFamily`,
  `presheaf_mono_iff_app_injective`;
- best owner abstraction: the categorical predicate `Mono` on the canonical unit
  `ℱ.toSheafify : ℱ ⟶ ℱ^#`, with objectwise injectivity as derived API;
- primitive data: the separatedness predicate and the sheafification unit;
- derived API: sectionwise injectivity and the passage between injectivity into the sheafification
  subtype and injectivity of the underlying stalk-family map.

Source/core/bridge triage:
- `source-facing`: the Stacks Project comparison between separatedness and the canonical map to
  sheafification;
- `core/canonical`: `Mono ℱ.toSheafify`;
- `bridge/view`: Definition 6.11.2 and Definition 6.16.2, which express the source statement via
  injectivity on sections. -/

-- Proof sketch: combine the source-facing separatedness criterion from Definition 6.11.2 with the
-- chapter owner theorem that identifies monomorphisms of presheaves of sets with objectwise
-- injectivity, then bridge the subtype-valued sheafification sections with their underlying
-- stalk-family functions.
/-- Lemma 6.17.5: a set-valued presheaf on `X` is separated if and only if the canonical map
`ℱ ⟶ ℱ^#` to its sheafification is a monomorphism. -/
theorem isSeparated_iff_mono_toSheafify :
    Presieve.IsSeparated J ℱ ↔ Mono ℱ.toSheafify := by
  rw [isSeparated_iff_injective_toStalkFamily, presheaf_mono_iff_app_injective]
  constructor
  · intro h U s t hst
    exact h U (congrArg Subtype.val hst)
  · intro h U s t hst
    exact h U (Subtype.ext hst)

end TopCat.Presheaf

/-! ### Lemma_6_17_6 (from Chap06) -/
open CategoryTheory Opposite TopCat TopologicalSpace

universe u

section

/- Domain-style sampling for Lemma 6.17.6:
- primary domain: local surjectivity and local injectivity of sheafified morphisms of set-valued
  presheaves on a topological space;
- inspected owner declarations:
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`,
  `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`,
  `Sheaf.mono_of_isLocallyInjective`,
  `presheaf_epi_iff_app_surjective`,
  `presheaf_mono_iff_app_injective`;
- best owner abstraction: the sheafification comparison theorems for local surjectivity and local
  injectivity together with the canonical bridge `Sheaf.mono_of_isLocallyInjective`; the public
  source-facing outputs are `Sheaf.IsLocallySurjective` in the surjective half and `Mono` in the
  injective half.

Source/core/bridge triage:
- `source-facing`: the textbook statement that sheafification sends sectionwise surjective or
  injective presheaf maps to locally surjective or injective sheaf maps;
- `core/canonical`: the owner equivalences
  `Presheaf.isLocallySurjective_presheafToSheaf_map_iff` and
  `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`, with `Sheaf.IsLocallyInjective` as the
  internal proof owner on the sheaf side;
- `bridge/view`: the Chapter 6 bridge theorems `presheaf_epi_iff_app_surjective` and
  `presheaf_mono_iff_app_injective`, which convert the source `Epi`/`Mono` hypotheses into the
  pointwise input used by the core owners, and the canonical implication
  `Sheaf.mono_of_isLocallyInjective`.

Primitive-vs-derived split:
- primitive data: a morphism `φ : F ⟶ G` of set-valued presheaves;
- owner predicates: local surjectivity or local injectivity of `φ` and of its sheafification map;
- derived source-facing API: the `Epi φ` and `Mono φ` hypotheses from the canonical categorical
  owners for set-valued presheaves.

The exact `Epi`/`Mono` to sectionwise surjectivity/injectivity bridge already lives upstream in
Definition 6.16.2, so this file only applies that chapter owner API to the sheafification
comparison.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
local notation "J" => Opens.grothendieckTopology X
variable {F G : X.Presheaf (Type u)} (φ : F ⟶ G)

-- Proof sketch: rewrite local surjectivity and local injectivity of the sheafified morphism using
-- `Presheaf.isLocallySurjective_presheafToSheaf_map_iff` and
-- `Presheaf.isLocallyInjective_presheafToSheaf_map_iff`, then use the Chapter 6 bridge theorems
-- `presheaf_epi_iff_app_surjective` and `presheaf_mono_iff_app_injective` to reduce to the
-- elementary presheaf theorems
-- `Presheaf.isLocallySurjective_of_surjective` and
-- `Presheaf.isLocallyInjective_of_injective`; in the injective half, conclude with
-- `Sheaf.mono_of_isLocallyInjective`.
/-- Lemma 6.17.6 (surjective case): sheafification sends an epimorphism, equivalently a
sectionwise surjective morphism, of presheaves of sets on `X` to a locally surjective morphism of
sheaves. -/
theorem isLocallySurjective_presheafToSheaf_map_of_epi
    (hφ : Epi φ) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map φ) := by
  simpa [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] using
    Presheaf.isLocallySurjective_of_surjective J φ
      (fun U ↦ (presheaf_epi_iff_app_surjective φ).1 hφ U.unop)

/-- Lemma 6.17.6 (injective case): sheafification sends a monomorphism, equivalently a
sectionwise injective morphism, of presheaves of sets on `X` to a monomorphism of sheaves. -/
theorem mono_presheafToSheaf_map_of_mono
    (hφ : Mono φ) :
    Mono ((presheafToSheaf J (Type u)).map φ) := by
  letI : Sheaf.IsLocallyInjective ((presheafToSheaf J (Type u)).map φ) := by
    simpa [Presheaf.isLocallyInjective_presheafToSheaf_map_iff] using
      Presheaf.isLocallyInjective_of_injective J φ
        (fun U ↦ (presheaf_mono_iff_app_injective φ).1 hφ U.unop)
  exact Sheaf.mono_of_isLocallyInjective ((presheafToSheaf J (Type u)).map φ)

end
