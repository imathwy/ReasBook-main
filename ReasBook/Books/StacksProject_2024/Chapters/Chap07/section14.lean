import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_14_1 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/- Domain-style sampling for Definition 7.14.1:
- primary domain: Grothendieck topologies, continuous functors of sites, and exact inverse-image
  functors on set-valued sheaves;
- sampled owner API:
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of a morphism of sites `(D, K) → (C, J)`;
  `core/canonical`: the owner predicates `Functor.IsContinuous u J K` and
  `RepresentablyFlat u`;
  `bridge/view`: the chapter class `IsMorphismOfSites J K u`.

Primitive data are exactly continuity and representable flatness. Exactness of the induced inverse
image on sheaves is derived API, so the public consequence below is stated from the source-facing
owner `IsMorphismOfSites`, which supplies the canonical owners by inheritance. Cover preservation
is a separate stronger site-level owner and is not part of `IsMorphismOfSites`.
-/

/-- Definition 7.14.1: a morphism of sites `(D, K) → (C, J)` is represented by a continuous
functor `u : C ⥤ D` whose inverse-image functor `u_s` on set-valued sheaves is exact. Mathlib's
canonical owner for that exactness criterion is `RepresentablyFlat u`, so we store continuity and
representable flatness as primitive data and derive exactness of `u.sheafPullback` from the
canonical pullback API. -/
class IsMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) : Prop
    extends u.IsContinuous J K, RepresentablyFlat u

/-- A continuous representably flat functor defines a morphism of sites. This is the canonical
mathlib criterion guaranteeing exactness of the inverse-image functor on sheaves. -/
instance isMorphismOfSites_of_isContinuous_representablyFlat
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] [RepresentablyFlat u] :
    IsMorphismOfSites J K u where
  toIsContinuous := inferInstance
  toRepresentablyFlat := inferInstance

/-- For a morphism of sites, the induced inverse-image functor on set-valued sheaves is exact
once the standard sheafification and Kan-extension hypotheses needed to construct it are
available. -/
theorem isMorphismOfSites_sheafPullback_exact
    [IsMorphismOfSites J K u]
    [HasSheafify J (Type w)]
    [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : (u.sheafPullback (Type w) J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous (Type w) J K).isLeftAdjoint
  simp only [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end

/-! ### Example_7_14_2 (from Chap07) -/
open CategoryTheory
open TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Example 7.14.2:
- primary domain: morphisms of sites attached to continuous maps of topological spaces;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)`;
- source/core/bridge triage:
  `source-facing`: the Stacks example asserting that a continuous map gives a morphism of sites on
  the small Zariski sites of opens;
  `core/canonical`: the owner class `IsMorphismOfSites`, whose primitive data are continuity and
  representable flatness;
  `bridge/view`: the specialization to the functor `Opens.map f`.

This file should therefore be a direct recall of the canonical instance for `Opens.map f`, not a
parallel local wrapper theorem.
-/

/- Example 7.14.2: a continuous map `f : X ⟶ Y` induces a morphism of sites
`X_{Zar} ⟶ Y_{Zar}` via inverse image of opens, i.e. via the functor
`Opens.map f : Opens Y ⥤ Opens X`. -/
#check
  (inferInstance :
    IsMorphismOfSites (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      (Opens.map f))

/-! ### Example_7_14_3 (from Chap07) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/- Domain-style sampling for Example 7.14.3:
- primary domain: Grothendieck topologies, continuous functors, and morphisms of sites;
- sampled owner API:
  `Presheaf.IsSheaf.of_le`,
  `RepresentablyFlat.id`,
  `IsMorphismOfSites`;
- source/core/bridge triage:
  `source-facing`: topology comparison for `J' ≤ J` on the fixed category `C`;
  `core/canonical`: `Functor.IsContinuous` and `IsMorphismOfSites`;
  `bridge/view`: the identity-functor continuity instance below and the thin theorem deriving the
  site-morphism owner.

Primitive data here are only the continuity proof for `𝟭 C` under `J' ≤ J`. The
representable-flat part is already canonical for the identity functor, and the
morphism-of-sites structure is derived API from the chapter owner constructor. -/

-- Proof sketch: if `ℱ` is a `J`-sheaf and `J' ≤ J`, then the sheaf condition for `J'` follows
-- immediately from `Presheaf.IsSheaf.of_le hle`. Since precomposition with the identity functor
-- is definitionally the same presheaf, this is exactly continuity of `𝟭 C`.
/-- The identity functor is continuous `(C, J') → (C, J)` whenever `J' ≤ J`, i.e. whenever every
`J'`-covering sieve is also `J`-covering. -/
instance id_isContinuous_of_le (hle : J' ≤ J) :
    Functor.IsContinuous (𝟭 C) J' J where
  op_comp_isSheaf_of_types G := by
    rw [← isSheaf_iff_isSheaf_of_type]
    simpa using (Presheaf.IsSheaf.of_le hle G.property)

-- Proof sketch: combine `id_isContinuous_of_le hle` with `RepresentablyFlat.id`, then apply the
-- canonical owner instance for a continuous representably flat functor.
/-- Example 7.14.3: if `J' ≤ J` are Grothendieck topologies on `C`, so every `J'`-covering is a
`J`-covering, then the identity functor on `C` defines a morphism of sites
`\mathcal C_J \to \mathcal C_{J'}`. -/
theorem id_isMorphismOfSites_of_le (hle : J' ≤ J) :
    IsMorphismOfSites J' J (𝟭 C) := by
  let _ : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
  exact isMorphismOfSites_of_isContinuous_representablyFlat J' J (𝟭 C)

end CategoryTheory

/-! ### Lemma_7_14_4 (from Chap07) -/
open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C₃ : Type u₁} [Category.{v₁} C₃]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {C₁ : Type u₃} [Category.{v₃} C₁]
variable (v : C₃ ⥤ C₂) (u : C₂ ⥤ C₁)
variable (J₃ : GrothendieckTopology C₃)
variable (J₂ : GrothendieckTopology C₂)
variable (J₁ : GrothendieckTopology C₁)

/- Domain-style sampling for Lemma 7.14.4:
- primary domain: Grothendieck topologies and morphisms of sites;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.isContinuous_comp`,
  `RepresentablyFlat.comp`,
  `IsMorphismOfSites`;
- source/core/bridge triage:
  `source-facing`: composition of morphisms of sites;
  `core/canonical`: the owner class `IsMorphismOfSites`, whose primitive data are continuity and
    representable flatness;
  `bridge/view`: the theorem `isMorphismOfSites_comp`, which exposes the canonical composition
    rule with the explicit middle topology.

Primitive data live in the owner abstraction `IsMorphismOfSites`: continuity and representable
flatness are not separate public fields of this lemma. The composite site morphism is therefore
derived via the canonical composition owners `Functor.isContinuous_comp` and
`RepresentablyFlat.comp`. Since the middle topology `J₂` is a genuine source input and is not
recoverable from the target `IsMorphismOfSites J₃ J₁ (v ⋙ u)`, this composition law belongs as an
explicit bridge theorem rather than as a global typeclass instance.
-/

/- Lemma 7.14.4: if `u : \mathcal C_2 \to \mathcal C_1` and `v : \mathcal C_3 \to \mathcal C_2`
are continuous functors which induce morphisms of sites, then the composite `u \circ v`, written
in Lean as `v ⋙ u`, is continuous. This is the composition statement underlying the induced
composite morphism of sites `\mathcal C_1 \to \mathcal C_3`. -/
recall Functor.isContinuous_comp
    [v.IsContinuous J₃ J₂] [u.IsContinuous J₂ J₁] :
  (v ⋙ u).IsContinuous J₃ J₁

/- Companion recall: representably flat functors are closed under composition, so the exactness
part of the site-morphism owner also composes along `v ⋙ u`. -/
recall RepresentablyFlat.comp [RepresentablyFlat v] [RepresentablyFlat u] :
  RepresentablyFlat (v ⋙ u)

/-- Lemma 7.14.4: if `u : \mathcal C_2 \to \mathcal C_1` and `v : \mathcal C_3 \to \mathcal C_2`
are morphisms of sites, then the composite `u \circ v`, written in Lean as `v ⋙ u`, again defines
a morphism of sites. The intermediate topology `J₂` is a genuine source input and is therefore an
explicit binder rather than a typeclass-inferred parameter. -/
theorem isMorphismOfSites_comp
    [IsMorphismOfSites J₃ J₂ v] [IsMorphismOfSites J₂ J₁ u] :
    IsMorphismOfSites J₃ J₁ (v ⋙ u) := by
  let _ : (v ⋙ u).IsContinuous J₃ J₁ := Functor.isContinuous_comp v u J₃ J₂ J₁
  infer_instance

end

/-! ### Definition_7_14_5 (from Chap07) -/
open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C₃ : Type u₁} [Category.{v₁} C₃]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {C₁ : Type u₃} [Category.{v₃} C₁]
variable (v : C₃ ⥤ C₂) (u : C₂ ⥤ C₁)
variable (J₃ : GrothendieckTopology C₃)
variable (J₂ : GrothendieckTopology C₂)
variable (J₁ : GrothendieckTopology C₁)
variable [IsMorphismOfSites J₃ J₂ v] [IsMorphismOfSites J₂ J₁ u]

/- Domain-style sampling for Definition 7.14.5:
- primary domain: Grothendieck topologies and morphisms of sites;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.isContinuous_comp`,
  `RepresentablyFlat.comp`,
  `isMorphismOfSites_comp`;
- source/core/bridge triage:
  `source-facing`: composition of morphisms of sites;
  `core/canonical`: the owner class `IsMorphismOfSites`;
  `bridge/view`: the theorem `isMorphismOfSites_comp`.

No new primitive data are introduced here. Continuity and representable flatness
already live in the owner abstraction, and Lemma 7.14.4 has already packaged
their canonical composition into the theorem `isMorphismOfSites_comp`.
So this numbered definition should stay a direct recall of that theorem
rather than a parallel wrapper declaration. -/
/- Definition 7.14.5: if `v : (C₃, J₃) ⥤ (C₂, J₂)` and
`u : (C₂, J₂) ⥤ (C₁, J₁)` are morphisms of sites, then the composite functor
`v ⋙ u` again defines a morphism of sites. This file stays at the
`bridge/view` layer by recalling the chapter theorem `isMorphismOfSites_comp`,
rather than introducing a second public wrapper around the owner
`IsMorphismOfSites`. -/
recall isMorphismOfSites_comp

end

/-! ### Lemma_7_14_6 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.14.6:
- primary domain: morphisms of sites built from continuous functors and filtered structured-arrow
  categories;
- sampled owner API:
  `RepresentablyFlat`,
  `RepresentablyFlat.cofiltered`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`,
  `isMorphismOfSites_sheafPullback_exact`;
- source/core/bridge triage:
  `source-facing`: the textbook hypothesis that `(StructuredArrow V u)ᵒᵖ` is filtered for every
  `V : D`;
  `core/canonical`: `RepresentablyFlat u`;
  `bridge/view`: the induced site-morphism and sheaf-exactness statements below.

Primitive data here are only the continuity hypothesis and the filteredness of the opposite
structured-arrow categories. `RepresentablyFlat u` is the owner abstraction for that data, while
`IsMorphismOfSites J K u` and exactness of `u.sheafPullback` are derived API.
-/

/-- Helper for Lemma 7.14.6: the textbook hypothesis that every opposite structured-arrow category
`(StructuredArrow V u)ᵒᵖ` is filtered is exactly the source-facing form of the canonical owner
datum `RepresentablyFlat u`. -/
theorem representablyFlat_of_structuredArrow_op_isFiltered
    (u : C ⥤ D) (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) :
    RepresentablyFlat u where
  cofiltered V := by
    -- Convert the filteredness of the opposite structured-arrow category into the owner field.
    let _ : IsFiltered (StructuredArrow V u)ᵒᵖ := hfiltered V
    exact isCofiltered_of_isFiltered_op (StructuredArrow V u)

-- Proof sketch: build the canonical `RepresentablyFlat u` instance from the textbook hypothesis
-- and then reuse the owner instance from Definition `7.14.1`.
/-- Lemma 7.14.6: if `u : \mathcal C \to \mathcal D` is continuous and each opposite
structured-arrow category `(StructuredArrow V u)ᵒᵖ`, i.e. `(𝓘_V^u)ᵒᵖ`, is filtered, then `u`
defines a morphism of sites `(\mathcal D, K) ⟶ (\mathcal C, J)`. -/
theorem isMorphismOfSites_of_filtered_op_structuredArrow
    (u : C ⥤ D) [u.IsContinuous J K]
    (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) :
    IsMorphismOfSites J K u := by
  let _ : RepresentablyFlat u := representablyFlat_of_structuredArrow_op_isFiltered u hfiltered
  exact isMorphismOfSites_of_isContinuous_representablyFlat J K u

-- Proof sketch: the bridge theorem supplies `IsMorphismOfSites J K u`, and exactness is then the
-- existing canonical consequence `isMorphismOfSites_sheafPullback_exact`.
/-- The inverse-image functor on set-valued sheaves attached to Lemma 7.14.6 is exact. -/
theorem sheafPullback_exact_of_filtered_op_structuredArrow
    (u : C ⥤ D) [u.IsContinuous J K]
    (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ)
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_filtered_op_structuredArrow u hfiltered
  exact isMorphismOfSites_sheafPullback_exact u

end

/-! ### Proposition_7_14_7 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Proposition 7.14.7:
- primary domain: Grothendieck topologies, continuous functors, finite-limit preservation, and
  morphisms of sites;
- sampled owner API:
  `preservesTerminal_of_iso`,
  `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`,
  `flat_of_preservesFiniteLimits`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the explicit final-object and pullback hypotheses from the Stacks statement;
  `core/canonical`: `PreservesFiniteLimits u`;
  `bridge/view`: the theorems below transferring the source hypotheses first to finite-limit
    preservation, then onward to `RepresentablyFlat u` and `IsMorphismOfSites J K u`.

Primitive data here are only continuity together with terminal-object and pullback preservation.
Terminal preservation, finite-limit preservation, representable flatness, and the site-morphism
structure are derived owner API, so the file should expose only the source-facing bridges to those
canonical owners. -/

-- Proof sketch: choose `X` as the terminal object of `C` and `u.obj X` as the terminal object of
-- `D`; the induced comparison `u.obj (⊤_ C) ≅ ⊤_ D` then gives preservation of the empty-diagram
-- limit via `preservesTerminal_of_iso`.
/-- An explicit terminal object whose image is terminal induces terminal-object preservation. -/
theorem preservesTerminal_of_terminal_and_image_terminal
    (u : C ⥤ D) (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X)) :
    PreservesLimit (Functor.empty.{0} C) u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : HasTerminal D := huX.hasTerminal
  exact preservesTerminal_of_iso u <|
    u.mapIso (terminalIsoIsTerminal hX) ≪≫ (terminalIsoIsTerminal huX).symm

-- Proof sketch: terminal-object preservation upgrades to preservation of `Discrete PEmpty`-shaped
-- limits, and together with pullback preservation this is exactly the canonical theorem
-- `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`.
private theorem preservesFiniteLimits_of_terminal_and_pullbacks
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    PreservesFiniteLimits u := by
  let _ : PreservesLimitsOfShape (Discrete PEmpty) u :=
    preservesLimitsOfShape_pempty_of_preservesTerminal u
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks u

-- Proof sketch: terminal preservation and pullback preservation yield finite-limit preservation,
-- hence `u` is representably flat. For a continuous functor,
-- this is exactly the extra hypothesis needed for the canonical instance
-- `isMorphismOfSites_of_isContinuous_representablyFlat`.
/-- Proposition 7.14.7 in canonical form: a continuous functor that preserves terminal objects and
pullbacks defines a morphism of sites `(\mathcal D, K) ⟶ (\mathcal C, J)`. -/
theorem isMorphismOfSites_of_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let _ : PreservesFiniteLimits u := preservesFiniteLimits_of_terminal_and_pullbacks u
  let _ : RepresentablyFlat u :=
    flat_of_preservesFiniteLimits u
  exact isMorphismOfSites_of_isContinuous_representablyFlat J K u

-- Proof sketch: the textbook hypotheses imply preservation of the terminal object, so the
-- canonical finite-limit-preservation theorem applies and hence `flat_of_preservesFiniteLimits`
-- yields representable flatness.
/-- Textbook-form bridge from an explicit final object and pullback preservation to representable
flatness. -/
theorem representablyFlat_of_terminal_and_pullbacks
    (u : C ⥤ D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    RepresentablyFlat u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let _ : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_terminal_and_image_terminal u X hX huX
  let _ : PreservesFiniteLimits u := preservesFiniteLimits_of_terminal_and_pullbacks u
  exact flat_of_preservesFiniteLimits u

-- Proof sketch: a chosen terminal object `X` equips `C` with a terminal object, and `u.obj X`
-- equips `D` with one. The induced isomorphism `u.obj (⊤_ C) ≅ ⊤_ D` gives preservation of the
-- terminal object, so the canonical proposition above applies.
/-- Textbook-form bridge for Proposition 7.14.7, using an explicit final object `X` whose image is
final. -/
theorem isMorphismOfSites_of_terminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K] (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_terminal_and_image_terminal u X hX huX
  exact isMorphismOfSites_of_preservesTerminal_and_pullbacks u

end

/-! ### Remark_7_14_8 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.14.8:
- primary domain: continuous site functors and finite-limit preservation;
- sampled owner API:
  `leftExactFunctor_iff_preserves_terminal_and_pullbacks`,
  `leftExactFunctor_iff`,
  `preservesFiniteLimits_iff_flat`,
  `flat_of_preservesFiniteLimits`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the textbook reformulation of finite-limit preservation in terms of terminal
  objects and pullbacks, together with the continuous finite-limit-preserving hypothesis;
  `core/canonical`: `PreservesFiniteLimits u`, `RepresentablyFlat u`, and
  `IsMorphismOfSites J K u`;
  `bridge/view`: the Chapter 4 equivalence and the site-morphism consequence below.

Primitive data here are only the functor together with the canonical terminal/pullback
preservation hypotheses, or continuity together with finite-limit preservation. The terminal and
pullback criterion is already owned upstream by Chapter 4 through
`leftExactFunctor_iff_preserves_terminal_and_pullbacks`, and `leftExactFunctor C D u` is
definitionally `PreservesFiniteLimits u`. Representable flatness and the morphism-of-sites
structure are derived from the existing owner API, so this file should stay a thin bridge. -/

/- Remark 7.14.8: preserving terminal objects and pullbacks is exactly preserving finite limits.
This is already the Chapter 4 owner theorem
`leftExactFunctor_iff_preserves_terminal_and_pullbacks`, since `leftExactFunctor C D u` is
definitionally `PreservesFiniteLimits u`. -/
recall leftExactFunctor_iff_preserves_terminal_and_pullbacks

/- Remark 7.14.8 also uses the canonical mathlib flatness owner: over a finitely complete source
category, a finite-limit-preserving functor is representably flat. -/
recall flat_of_preservesFiniteLimits

/-- Remark 7.14.8: a continuous functor that preserves finite limits is representably flat, hence
defines a morphism of sites. -/
theorem isMorphismOfSites_of_preservesFiniteLimits
    (u : C ⥤ D) [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u] :
    IsMorphismOfSites J K u := by
  let _ : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  infer_instance

end

/-! ### Remark_7_14_9 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace CategoryTheory

/- Domain-style sampling for Remark 7.14.9:
- primary domain: quasi-continuous functors between sites, morphisms of sites, and exact
  inverse-image functors on set-valued sheaves;
- sampled owner API:
  `Functor.IsQuasiContinuousSiteFunctor`,
  `Functor.IsContinuous`,
  `IsMorphismOfSites`,
  `isMorphismOfSites_sheafPullback_exact`;
- source/core/bridge triage:
  `source-facing`: the Stacks remark that a quasi-morphism is a quasi-continuous functor whose
    inverse-image functor on sheaves is exact;
  `core/canonical`: `Functor.IsQuasiContinuousSiteFunctor u J K` for the extra source data and
    `IsMorphismOfSites J K u` for the exact inverse-image package;
  `bridge/view`: the theorems below upgrading quasi-continuity, terminal preservation, and
    pullback preservation to `IsMorphismOfSites`.

Primitive data here are only quasi-continuity and the finite-limit hypotheses from
Proposition 7.14.7. Exactness of `u.sheafPullback` is already derived API from
`IsMorphismOfSites` via `isMorphismOfSites_sheafPullback_exact`, so this file should not
introduce a second bundled owner class around those existing predicates. -/

/- Remark 7.14.9: in this project the Stacks phrase “quasi-morphism of sites” is expressed by the
existing owners `Functor.IsQuasiContinuousSiteFunctor u J K` and `IsMorphismOfSites J K u`,
rather than by a second wrapper class. The source-facing content of the remark is therefore the
bridge from quasi-continuity and the Proposition 7.14.7 hypotheses to `IsMorphismOfSites`. -/

-- Proof sketch: a quasi-continuous functor is continuous by Remark `7.13.6`. With the chosen
-- terminal-object preservation and pullback-preservation hypotheses, Proposition `7.14.7` gives a
-- morphism of sites. The exactness part of the quasi-morphism remark is then the canonical
-- consequence `isMorphismOfSites_sheafPullback_exact`.
/-- Canonical quasi-continuous analogue of Proposition 7.14.7: a quasi-continuous functor that
preserves terminal objects and pullbacks defines a morphism of sites. -/
theorem isMorphismOfSites_of_isQuasiContinuous_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K] [HasTerminal C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : Functor.IsContinuous u J K := inferInstance
  exact isMorphismOfSites_of_preservesTerminal_and_pullbacks u

/-- Textbook-form bridge for Remark 7.14.9, using an explicit terminal object whose image is
terminal. -/
theorem isMorphismOfSites_of_isQuasiContinuous_terminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K]
    (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : Functor.IsContinuous u J K := inferInstance
  exact isMorphismOfSites_of_terminal_and_pullbacks u X hX huX

-- Proof sketch: first upgrade the quasi-continuous functor to a morphism of sites by the previous
-- bridge theorem, then apply the canonical exactness consequence
-- `isMorphismOfSites_sheafPullback_exact`.
/-- Remark 7.14.9, exactness clause: under the Proposition 7.14.7 finite-limit hypotheses, a
quasi-continuous functor has exact inverse-image functor on set-valued sheaves. -/
theorem sheafPullback_exact_of_isQuasiContinuous_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K] [HasTerminal C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_isQuasiContinuous_preservesTerminal_and_pullbacks u
  exact isMorphismOfSites_sheafPullback_exact u

-- Proof sketch: the explicit terminal-object version first recovers a morphism of sites and then
-- reuses the canonical exactness theorem.
/-- Textbook-form exactness clause for Remark 7.14.9, using an explicit terminal object whose
image is terminal. -/
theorem sheafPullback_exact_of_isQuasiContinuous_terminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K]
    (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_isQuasiContinuous_terminal_and_pullbacks u X hX huX
  exact isMorphismOfSites_sheafPullback_exact u

end CategoryTheory

end

/-! ### Lemma_7_14_10 (from Chap07) -/
open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 7.14.10:
- primary domain: representably flat functors, structured-arrow categories, and fixed-target
  covering families on a Grothendieck site;
- sampled owner API:
  `RepresentablyFlat`,
  `RepresentablyFlat.cofiltered`,
  `StructuredArrow`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `GrothendieckTopology.mem_toPrecoverage_iff`;
- source/core/bridge triage:
  `source-facing`: a covering family over `V` whose members admit maps to objects in the image of
  `u`;
  `core/canonical`: `RepresentablyFlat u`, whose owner field says every `StructuredArrow V u` is
  cofiltered and hence nonempty;
  `bridge/view`: the family covering predicate `SemiRepresentableFamily.Over.IsCovering
  K.toPrecoverage 𝒱`, derived from the generated sieve through `mem_toPrecoverage_iff`.

Primitive mathematical input data are only the topology `K`, the functor `u`, and the canonical
owner `RepresentablyFlat u`. The existence of a map from `V` to some object in the image of `u` is
derived canonically as nonemptiness of `StructuredArrow V u`. The covering family is the singleton
identity family on `V`, and its covering property should be stated using the existing family owner
`SemiRepresentableFamily.Over.IsCovering K.toPrecoverage` rather than the raw sieve-membership
bridge.
-/

/-- Lemma 7.14.10, at the canonical covering-family owner level: if `u : C ⥤ D` is representably
flat, then every object `V` of `D` admits a `K`-covering family whose members each map to some
object of the form `u.obj U` with `U : C`. -/
theorem exists_covering_family_with_maps_to_functor_images
    (K : GrothendieckTopology D) (u : C ⥤ D) [RepresentablyFlat u]
    (V : D) :
    ∃ 𝒱 : SemiRepresentableFamily.Over V,
      IsCovering K.toPrecoverage 𝒱 ∧
        ∀ i : 𝒱.index, Nonempty (StructuredArrow (𝒱.obj i).left u) := by
  -- Use the singleton identity family on `V`, which is visibly a cover and keeps the source route
  -- focused on producing image maps rather than refining the cover itself.
  let 𝒱 : SemiRepresentableFamily.Over V :=
    ofArrows (fun _ : PUnit ↦ V) (fun _ ↦ 𝟙 V)
  refine ⟨𝒱, ?_, ?_⟩
  · rw [IsCovering, GrothendieckTopology.mem_toPrecoverage_iff]
    rw [show 𝒱.toPresieve = Presieve.ofArrows (fun _ : PUnit ↦ V) (fun _ ↦ 𝟙 V) by rfl]
    rw [Presieve.ofArrows_pUnit, Sieve.generateSingleton_eq]
    -- The generated sieve of the identity arrow is the maximal sieve, so the singleton family is a
    -- `K`-covering family.
    have htop : Sieve.generateSingleton (𝟙 V) = (⊤ : Sieve V) := by
      rw [← Sieve.id_mem_iff_eq_top]
      exact ⟨𝟙 V, by simp⟩
    rw [htop]
    exact K.top_mem V
  · intro i
    -- The family has a single member, so it suffices to exhibit one map from `V` into the image of
    -- `u`, encoded canonically by a structured arrow.
    cases i
    change Nonempty (StructuredArrow V u)
    let _ : IsCofiltered (StructuredArrow V u) := inferInstance
    exact IsCofiltered.nonempty

/-- Site-morphism specialization of Lemma 7.14.10. The additional source topology `J` is used only
to obtain the canonical owner instance `RepresentablyFlat u`. -/
theorem exists_covering_family_with_maps_to_functor_images_of_isMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [IsMorphismOfSites J K u]
    (V : D) :
    ∃ 𝒱 : SemiRepresentableFamily.Over V,
      IsCovering K.toPrecoverage 𝒱 ∧
        ∀ i : 𝒱.index, Nonempty (StructuredArrow (𝒱.obj i).left u) := by
  -- The site-morphism hypothesis packages the representable-flatness needed by the owner-level
  -- theorem, so the textbook statement is a direct specialization.
  let _ : RepresentablyFlat u := (inferInstance : IsMorphismOfSites J K u).toRepresentablyFlat
  exact exists_covering_family_with_maps_to_functor_images K u V

end

end CategoryTheory
