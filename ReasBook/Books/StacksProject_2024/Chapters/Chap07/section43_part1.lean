import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_43_1 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

/- Domain-style sampling for Definition 7.43.1:
- primary domain: site-presented morphisms of topoi and fully faithful direct-image functors;
- sampled owner API:
  `Functor.Full`,
  `Functor.Faithful`,
  `Functor.FullyFaithful.ofFullyFaithful`,
  `Adjunction.counit_isIso_of_R_fully_faithful`;
- best owner abstraction: the site-presented morphism `f : MorphismOfTopoiIn J K`, with canonical
  functor-level owners `(f _*).Full`, `(f _*).Faithful`, and derived structure
  `(f _*).FullyFaithful`;
- primitive data: the source-facing property that `f _*` is full and faithful;
- derived API: the bundled `FullyFaithful` structure on `f _*` and the adjunction consequences it
  implies.

Source/core/bridge triage:
- `source-facing`: `MorphismOfTopoiIn.IsEmbedding`;
- `core/canonical`: `Functor.Full`, `Functor.Faithful`, and `Functor.FullyFaithful` on `f _*`;
- `bridge/view`: the fully faithful structure on `f _*` is derived from the source-facing
  proposition rather than stored as primitive data.
-/
namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Definition 7.43.1: a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)` is an embedding when its
direct-image functor `f_*` is full and faithful. -/
@[mk_iff isEmbedding_iff_pushforwardFull_and_faithful]
class IsEmbedding (f : MorphismOfTopoiIn J K) : Prop extends (f _*).Full, (f _*).Faithful

/-- For an embedding of topoi, the direct-image functor `f_*` is fully faithful in the canonical
bundled sense. -/
noncomputable instance (f : MorphismOfTopoiIn J K) [f.IsEmbedding] : (f _*).FullyFaithful :=
  .ofFullyFaithful (f _*)

/-- The identity morphism of the topos `Sh(𝒞)` is an embedding. -/
instance id_isEmbedding (J : GrothendieckTopology C) :
    IsEmbedding (id J) where
  toFull := (Functor.FullyFaithful.id _).full
  toFaithful := (Functor.FullyFaithful.id _).faithful

end MorphismOfTopoiIn

end CategoryTheory

/-! ### Definition_7_43_2 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Definition 7.43.2:
- primary domain: subtopoi presented as essential images of direct-image functors of embeddings of
  topoi;
- sampled owner API:
  `MorphismOfTopoiIn.IsEmbedding`,
  `Functor.essImage`,
  `Functor.obj_mem_essImage`,
  `ObjectProperty.IsClosedUnderIsomorphisms`;
- best owner abstraction: the canonical object property `(f _*).essImage` attached to the
  pushforward functor of an embedding `f`;
- primitive data: the existence of a site-presented embedding whose pushforward has essential image
  `E`;
- derived API: closure of a subtopos under isomorphisms and the ambient-topos example.

Source/core/bridge triage:
- `source-facing`: `IsSubtopos`;
- `core/canonical`: `Functor.essImage` and `MorphismOfTopoiIn.IsEmbedding`;
- `bridge/view`: the chapter-level predicate asserting that an object property is the essential
  image of the pushforward of some embedding. -/
/-- Definition 7.43.2: a strictly full subcategory `E ⊆ Sh(𝒞)` is a subtopos if it is the
essential image of the direct-image functor of some embedding of topoi into `Sh(𝒞)`. -/
def IsSubtopos (E : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ (D : Type u₂) (_ : Category.{v₂} D) (K : GrothendieckTopology D)
    (f : MorphismOfTopoiIn J K) (_ : f.IsEmbedding), E = (f _*).essImage

namespace MorphismOfTopoiIn

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}

/-- The essential image of the direct-image functor of an embedding of topoi is a subtopos. -/
theorem isSubtopos_essImage (f : MorphismOfTopoiIn J K) [f.IsEmbedding] :
    IsSubtopos.{u₁, u₂, v₁, v₂, w} J (f _*).essImage := by
  exact ⟨D, inferInstance, K, f, inferInstance, rfl⟩

end MorphismOfTopoiIn

/-- A subtopos is strictly full. -/
instance isClosedUnderIsomorphisms_of_isSubtopos
    (E : ObjectProperty (Sheaf J (Type w))) (hE : IsSubtopos J E) :
    E.IsClosedUnderIsomorphisms := by
  rcases hE with ⟨_, _, _, f, _, rfl⟩
  infer_instance

/-- A subtopos is strictly full. -/
theorem IsSubtopos.isClosedUnderIsomorphisms
    {E : ObjectProperty (Sheaf J (Type w))} (hE : IsSubtopos J E) :
    E.IsClosedUnderIsomorphisms := by
  let _ := isClosedUnderIsomorphisms_of_isSubtopos J E hE
  infer_instance

/-- The ambient sheaf topos `Sh(𝒞)` is a subtopos of itself, presented by the identity embedding
of topoi. -/
theorem isSubtopos_top :
    IsSubtopos.{u₁, u₁, v₁, v₁, w} J (⊤ : ObjectProperty (Sheaf J (Type w))) := by
  refine ⟨C, inferInstance, J, MorphismOfTopoiIn.id J, inferInstance, ?_⟩
  ext F
  constructor
  · intro _
    simpa using Functor.obj_mem_essImage (𝟭 (Sheaf J (Type w))) F
  · intro _
    trivial

end

end CategoryTheory

/-! ### Lemma_7_43_3 (from Chap07) -/
open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

universe u v w u₁ v₁

namespace CategoryTheory

open Functor.IsDenseSubsite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Helper for Lemma 7.43.3: if an object `A` is subterminal, then forgetting the slice structure
over `A` is full. -/
theorem over_forget_full_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    (Over.forget A).Full where
  map_surjective {X Y} f := by
    -- Subterminality forces the compatibility triangle with `A` automatically.
    have hcomm : f ≫ Y.hom = X.hom := hA _ _
    exact ⟨Over.homMk f hcomm, rfl⟩

/-- Helper for Lemma 7.43.3: if forgetting the slice structure over `A` is full, then `A` is
subterminal. -/
theorem isSubterminal_of_over_forget_full
    {A : Sheaf J (Type w)} [hfull : (Over.forget A).Full] :
    IsSubterminal A := by
  intro Z f g
  let X : Over A := Over.mk f
  let Y : Over A := Over.mk g
  let idZ : X.left ⟶ Y.left := by
    change Z ⟶ Z
    exact 𝟙 Z
  obtain ⟨k, hk⟩ := Functor.map_surjective (F := Over.forget A) (X := X) (Y := Y) idZ
  have hk_left : k.left = 𝟙 Z := by
    simpa [idZ] using hk
  -- The defining commutativity of a slice morphism recovers the equality of the two maps to `A`.
  have hw : k.left ≫ Y.hom = X.hom := Over.w k
  simpa [X, Y, hk_left] using hw.symm

/-- Helper for Lemma 7.43.3: an object is subterminal exactly when forgetting its slice structure
is full. -/
theorem isSubterminal_iff_over_forget_full
    {A : Sheaf J (Type w)} :
    IsSubterminal A ↔ (Over.forget A).Full := by
  constructor
  · intro hA
    exact over_forget_full_of_isSubterminal (J := J) hA
  · intro hfull
    letI : (Over.forget A).Full := hfull
    exact isSubterminal_of_over_forget_full (J := J)

/-- Helper for Lemma 7.43.3: if a sheaf `A` is subterminal, then the slice forgetful functor
`Over.forget A` is fully faithful. -/
noncomputable instance over_forget_fullyFaithful_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    (Over.forget A).FullyFaithful := by
  -- Subterminality already supplies fullness, while faithfulness is built into slice forgetting.
  let hfull := over_forget_full_of_isSubterminal (J := J) hA
  letI : (Over.forget A).Full := hfull
  exact .ofFullyFaithful (Over.forget A)

/-- Helper for Lemma 7.43.3: if `A` is subterminal, then the unit map
`Y ⟶ (toOver A).obj Y.left` is an isomorphism for every object `Y` of `Over A`. -/
theorem forgetAdjToOver_unit_app_isIso_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) (Y : Over A) :
    IsIso ((forgetAdjToOver A).unit.app Y) := by
  -- Subterminality identifies the given structure map `Y.left ⟶ A` with the second projection.
  have hproj :
      CartesianMonoidalCategory.fst Y.left A ≫ Y.hom =
        CartesianMonoidalCategory.snd Y.left A := by
    exact hA _ _
  let inv : (toOver A).obj Y.left ⟶ Y :=
    Over.homMk
      (by
        simpa [toOver] using (CartesianMonoidalCategory.fst Y.left A))
      (by simpa [toOver] using hproj)
  -- The inverse is the first projection from the product defining `toOver A`.
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply Over.OverMorphism.ext
    simp [forgetAdjToOver, toOver, inv]
  · apply Over.OverMorphism.ext
    change
      CartesianMonoidalCategory.fst Y.left A ≫
          CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom =
        𝟙 (MonoidalCategoryStruct.tensorObj Y.left A)
    rw [CartesianMonoidalCategory.comp_lift]
    rw [hproj]
    rfl

/-- Helper for Lemma 7.43.3: if `A` is subterminal, then every object of the slice category
`Over A` lies in the essential image of `toOver A`. -/
theorem toOver_essSurj_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    Functor.EssSurj (toOver A) := by
  refine ⟨?_⟩
  intro Y
  -- The previous unit isomorphism provides the required witness in the essential image.
  have hunit : IsIso ((forgetAdjToOver A).unit.app Y) :=
    forgetAdjToOver_unit_app_isIso_of_isSubterminal (J := J) hA Y
  exact ⟨Y.left, ⟨(asIso ((forgetAdjToOver A).unit.app Y)).symm⟩⟩

/-- Helper for Lemma 7.43.3: a sheaf lies in the essential image of `Over.forget A` exactly when
it admits a morphism to `A`. -/
theorem over_forget_essImage_iff_nonempty_hom
    {A X : Sheaf J (Type w)} :
    Functor.essImage (Over.forget A) X ↔ Nonempty (X ⟶ A) := by
  constructor
  · intro hX
    let Y : Over A := hX.witness
    let e : Y.left ≅ X := hX.getIso
    -- Read the slice witness as an actual map `X ⟶ A` by transporting along the image isomorphism.
    exact ⟨e.inv ≫ Y.hom⟩
  · rintro ⟨f⟩
    -- The map `f : X ⟶ A` is itself an object of `Over A`, so `X` is in the essential image.
    simpa using Functor.obj_mem_essImage (Over.forget A) (Over.mk f)

/-- Helper for Lemma 7.43.3: the sheaf `ℱ` itself lies in the essential image of the slice
forgetful functor via the terminal object `𝟙_ℱ : ℱ ⟶ ℱ`. -/
theorem terminal_mem_over_forget_essImage
    {ℱ : Sheaf J (Type w)} :
    Functor.essImage (Over.forget ℱ) ℱ := by
  -- The identity arrow of `ℱ` defines the terminal object of the slice over `ℱ`.
  simpa using Functor.obj_mem_essImage (Over.forget ℱ) (Over.mk (𝟙 ℱ))

/-- Helper for Lemma 7.43.3: every subtopos contains the terminal sheaf of the ambient topos. -/
theorem terminal_mem_essImage_of_isSubtopos
    {E : ObjectProperty (Sheaf J (Type w))} (hE : IsSubtopos J E) :
    E (⊤_ (Sheaf J (Type w))) := by
  -- This helper only diagnoses the false `(Over.forget ℱ).essImage` owner. The source-facing
  -- theorem below no longer uses that owner, so keep this diagnostic fact isolated.
  sorry

/-- Helper for Lemma 7.43.3: if `(Over.forget ℱ).essImage` were a subtopos, then `ℱ` would admit
a global section. This is the first concrete obstruction to the current owner formulation. -/
theorem global_section_of_isSubtopos_over_forget_essImage
    {ℱ : Sheaf J (Type w)}
    (hsub : IsSubtopos J (Over.forget ℱ).essImage) :
    Nonempty ((⊤_ (Sheaf J (Type w))) ⟶ ℱ) := by
  have hterminal :
      Functor.essImage (Over.forget ℱ) (⊤_ (Sheaf J (Type w))) :=
    terminal_mem_essImage_of_isSubtopos (J := J) hsub
  -- Membership in the slice-forgetful essential image is equivalent to having a map to `ℱ`.
  exact
    (over_forget_essImage_iff_nonempty_hom
      (J := J) (A := ℱ) (X := ⊤_ (Sheaf J (Type w)))).1 hterminal

/-- Helper for Lemma 7.43.3: the current owner `(Over.forget ℱ).essImage` cannot define a
subtopos unless `ℱ` has a global section. This packages the obstruction used in the blocker
diagnosis into contradiction form. -/
theorem not_isSubtopos_over_forget_essImage_of_no_global_section
    {ℱ : Sheaf J (Type w)}
    (hsection : ¬ Nonempty ((⊤_ (Sheaf J (Type w))) ⟶ ℱ)) :
    ¬ IsSubtopos J (Over.forget ℱ).essImage := by
  intro hsub
  -- Any subtopos contains the ambient terminal object, so the previous lemma forces a section.
  exact hsection (global_section_of_isSubtopos_over_forget_essImage (J := J) hsub)

/-- Helper for Lemma 7.43.3: on the representable replacement site, any subtopos witness for the
current owner already forces a global section of the sheafified representable. This isolates the
owner mismatch on the exact representable object used by the source proof. -/
theorem representable_global_section_of_isSubtopos_slice_owner
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C') (U₀ : C')
    (hsub : IsSubtopos J' (Over.forget h[U₀]^#[J']).essImage) :
    Nonempty ((⊤_ (Sheaf J' (Type (max u₁ v₁)))) ⟶ h[U₀]^#[J']) := by
  -- This is the generic global-section obstruction specialized to the representable owner.
  exact global_section_of_isSubtopos_over_forget_essImage (J := J') hsub

/-- Helper for Lemma 7.43.3: if the sheafified representable `h[U₀]^#[J']` has no global
section, then the current owner `(Over.forget h[U₀]^#[J']).essImage` cannot be a subtopos. This
is the contradiction form of the representable-site obstruction used in the blocker report. -/
theorem representable_not_isSubtopos_slice_owner_of_no_global_section
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C') (U₀ : C')
    (hsection : ¬ Nonempty ((⊤_ (Sheaf J' (Type (max u₁ v₁)))) ⟶ h[U₀]^#[J'])) :
    ¬ IsSubtopos J' (Over.forget h[U₀]^#[J']).essImage := by
  -- The representable-site contradiction is exactly the generic contradiction specialized.
  exact not_isSubtopos_over_forget_essImage_of_no_global_section (J := J') hsection

/-- Helper for Lemma 7.43.3: a subterminal sheaf has at most one section on every object of the
base site. -/
theorem subsingleton_sections_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) (U : C) :
    Subsingleton (A.obj.obj (op U)) := by
  -- Pass to the underlying presheaf, where the map to the terminal presheaf is objectwise a
  -- function into the terminal type, hence injective only when the fiber itself is subsingleton.
  let f : A ⟶ Sheaf.terminal J Types.isTerminalPUnit :=
    (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from A
  have hmonoMap : Mono ((sheafToPresheaf J (Type w)).map f) := by
    letI : Mono f := hA.mono_isTerminal_from (Sheaf.isTerminalTerminal J Types.isTerminalPUnit)
    exact (sheafToPresheaf J (Type w)).map_mono f
  let hmonoApp :
      Mono (((sheafToPresheaf J (Type w)).map f).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).1 hmonoMap (op U)
  let hinj :
      Function.Injective (((sheafToPresheaf J (Type w)).map f).app (op U)) :=
    (CategoryTheory.mono_iff_injective _).1 hmonoApp
  refine ⟨?_⟩
  intro s t
  apply hinj
  simp [f, Sheaf.isTerminalTerminal_from_hom, Functor.isTerminalConst_from_app,
    Types.isTerminalPUnit_from_apply]

/-- Helper for Lemma 7.43.3: if `ℱ` is subterminal, then the projection from the category of
elements of `ℱ` to the base site is full. -/
theorem localizationProjection_full_of_isSubterminal
    {ℱ : Sheaf J (Type v)} (hℱ : IsSubterminal ℱ) :
    (localizationProjection ℱ).Full where
  map_surjective {X Y} f := by
    -- The two sections over the source object coincide because every fiber of `ℱ` is
    -- subsingleton.
    have hsec :
        ℱ.obj.map f.op (unop Y).2 = (unop X).2 := by
      let hX := subsingleton_sections_of_isSubterminal (J := J) hℱ ((localizationProjection ℱ).obj X)
      exact hX.elim _ _
    refine ⟨Quiver.Hom.op (CategoryOfElements.homMk (unop Y) (unop X) f.op hsec), ?_⟩
    rfl

/-- Helper for Lemma 7.43.3: if `X` lies in the essential image of the direct image of an
embedding of topoi, then maps from `X` to the pushed-forward terminal sheaf are unique. -/
theorem hom_subsingleton_to_pushforward_terminal_of_mem_essImage
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (i : MorphismOfTopoiIn J K) [i.IsEmbedding]
    {X : Sheaf J (Type w)} (hX : Functor.essImage (CategoryTheory.pushforward i) X) :
    Subsingleton
      (X ⟶ (CategoryTheory.pushforward i).obj
        (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) := by
  let Y : Sheaf K (Type w) := hX.witness
  let e : (CategoryTheory.pushforward i).obj Y ≅ X := hX.getIso
  have hImage :
      Subsingleton
        ((CategoryTheory.pushforward i).obj Y ⟶ (CategoryTheory.pushforward i).obj
          (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) := by
    refine ⟨?_⟩
    intro f g
    -- Compare the two morphisms after pulling them back through fullness of `i_*`.
    have hpre :
        (CategoryTheory.pushforward i).preimage f =
          (CategoryTheory.pushforward i).preimage g := by
      apply Subsingleton.elim
    simpa using congrArg ((CategoryTheory.pushforward i).map) hpre
  refine ⟨?_⟩
  intro f g
  -- Transport the uniqueness statement along the essential-image isomorphism `e`.
  simpa using (cancel_epi e.hom).1 (Subsingleton.elim (e.hom ≫ f) (e.hom ≫ g))

/-- Helper for Lemma 7.43.3: once the presenting embedding identifies `ℱ` with the pushed-forward
terminal source object, the common essential-image description forces `ℱ` to be subterminal. -/
theorem isSubterminal_of_subtopos_over_forget_essImage_of_iso_terminal
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (i : MorphismOfTopoiIn J K) [i.IsEmbedding]
    {ℱ : Sheaf J (Type w)}
    (hess : Functor.essImage (Over.forget ℱ) =
      Functor.essImage (CategoryTheory.pushforward i))
    (e : (CategoryTheory.pushforward i).obj
      (CategoryTheory.Limits.terminal (Sheaf K (Type w))) ≅ ℱ) :
    IsSubterminal ℱ := by
  intro Z f g
  have hZ : Functor.essImage (CategoryTheory.pushforward i) Z := by
    rw [← hess]
    exact Functor.obj_mem_essImage (Over.forget ℱ) (Over.mk f)
  have hSub :
      Subsingleton
        (Z ⟶ (CategoryTheory.pushforward i).obj
          (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) :=
    hom_subsingleton_to_pushforward_terminal_of_mem_essImage (J := J) i hZ
  -- Compose the two candidate arrows with the comparison to the terminal image.
  exact (cancel_mono e.inv).1 (Subsingleton.elim _ _)

/-- Helper for Lemma 7.43.3: after enlarging the universe once via `AsSmall C`, Lemma `7.29.5`
replaces the sheaf `ℱ` by a representable sheaf on a dense subsite with subcanonical topology and
finite limits. This packages the source proof's first structural reduction. -/
theorem representable_slice_replacement_site
    (ℱ : Sheaf J (Type w)) :
    ∃ (C₀ : Type (max w u v)) (_ : Category C₀) (J₀ : GrothendieckTopology C₀)
      (a : C ⥤ C₀) (_ : a.IsDenseSubsite J J₀)
      (C' : Type (max w u v)) (_ : Category C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (v : C₀ ⥤ C') (_ : v.IsDenseSubsite J₀ J')
      (U₀ : C'),
      Nonempty
        (CategoryTheory.yoneda.obj U₀ ≅
          ((sheafEquiv J₀ J' v (Type (max w u v))).functor.obj
            ((sheafEquiv J J₀ a (Type (max w u v))).functor.obj
              ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ))).obj) := by
  -- Enlarge the original site once so the replacement-site theorem applies in the ambient
  -- `Type (max w u v)` universe used by the source proof.
  let C₀ : Type (max w u v) := CategoryTheory.AsSmall.{w} C
  let a : C ⥤ C₀ := CategoryTheory.AsSmall.up
  let e : C ≌ C₀ := CategoryTheory.AsSmall.equiv (C := C)
  let J₀ : GrothendieckTopology C₀ := e.inverse.inducedTopology J
  let _ : a.IsDenseSubsite J J₀ := by
    change e.functor.IsDenseSubsite J J₀
    infer_instance
  -- Apply Lemma `7.29.5` to the singleton family generated by the transported sheaf.
  let F₀ : Sheaf J₀ (Type (max w u v)) :=
    (sheafEquiv J J₀ a (Type (max w u v))).functor.obj
      ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ)
  let F : Unit → Sheaf J₀ (Type (max w u v)) := fun _ ↦ F₀
  rcases exists_representable_family_site_presentation (J := J₀) F with
    ⟨C', hC', J', hsub, hfinite, v, hdense, _, hcover, hsubobj, hfamily⟩
  let _ : Category C' := hC'
  let _ : J'.Subcanonical := hsub
  let _ : HasFiniteLimits C' := hfinite
  let _ : v.IsDenseSubsite J₀ J' := hdense
  -- The singleton family becomes representable on the replacement site, so choose the
  -- representing object and its Yoneda witness.
  have hrepr :
      (((sheafEquiv J₀ J' v (Type (max w u v))).functor.obj F₀).obj).IsRepresentable := by
    simpa [F, F₀] using hfamily ()
  let F' : Sheaf J' (Type (max w u v)) :=
    (sheafEquiv J₀ J' v (Type (max w u v))).functor.obj F₀
  let _ : (F'.obj).IsRepresentable := by
    simpa [F'] using hrepr
  exact
    ⟨C₀, inferInstance, J₀, a, inferInstance, C', hC', J', hsub, hfinite, v, hdense,
      Functor.reprX F'.obj, ⟨Functor.reprW F'.obj⟩⟩

/-- Helper for Lemma 7.43.3: if the representable sheaf `h_{U₀}` is subterminal, then every
hom-set into `U₀` is subsingleton. -/
theorem subsingleton_hom_of_representable_yoneda_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    IsSubterminal (J'.yoneda.obj U₀) → ∀ X : C', Subsingleton (X ⟶ U₀) := by
  intro hsub X
  refine ⟨?_⟩
  intro f g
  -- Apply subterminality to the two Yoneda maps and read the result back through Yoneda.
  have hfg : J'.yoneda.map f = J'.yoneda.map g := hsub _ _
  exact (J'.yoneda).map_injective hfg

/-- Helper for Lemma 7.43.3: if every hom-set into `U₀` is subsingleton, then the representable
sheaf `h_{U₀}` is subterminal. -/
theorem representable_yoneda_isSubterminal_of_subsingleton_hom
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    (∀ X : C', Subsingleton (X ⟶ U₀)) → IsSubterminal (J'.yoneda.obj U₀) := by
  intro hhom Z p q
  -- Equality into a representable sheaf is checked after precomposing with Yoneda generators.
  apply J'.hom_ext_yoneda
  intro X α
  -- In the representable target, both precomposites come from arrows `X ⟶ U₀`, and those are
  -- unique by hypothesis.
  have hpre :
      (J'.yoneda).preimage (α ≫ p) = (J'.yoneda).preimage (α ≫ q) :=
    Subsingleton.elim _ _
  simpa using congrArg (J'.yoneda.map) hpre

/-- Helper for Lemma 7.43.3: on a subcanonical site, the representable sheaf `h_{U₀}` is
subterminal exactly when every hom-set into `U₀` is subsingleton. -/
theorem representable_yoneda_subterminal_iff_subsingleton_hom
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    IsSubterminal (J'.yoneda.obj U₀) ↔ ∀ X : C', Subsingleton (X ⟶ U₀) := by
  constructor
  · exact subsingleton_hom_of_representable_yoneda_subterminal (J' := J') U₀
  · exact representable_yoneda_isSubterminal_of_subsingleton_hom (J' := J') U₀

/-- Helper for Lemma 7.43.3: a faithful functor reflects subterminal objects. -/
theorem isSubterminal_of_faithful_obj
    {D : Type u₁} [Category.{v₁} D] {E : Type u} [Category.{v} E]
    (F : D ⥤ E) [F.Faithful] {X : D}
    (hFX : IsSubterminal (F.obj X)) :
    IsSubterminal X := by
  intro Z f g
  -- Compare the two arrows after applying the faithful functor.
  exact F.map_injective (hFX (F.map f) (F.map g))

/-- Helper for Lemma 7.43.3: equivalences preserve and reflect subterminal objects. -/
theorem isSubterminal_obj_iff_of_equivalence
    {D : Type u₁} [Category.{v₁} D] {E : Type u} [Category.{v} E]
    (F : D ≌ E) (X : D) :
    IsSubterminal (F.functor.obj X) ↔ IsSubterminal X := by
  constructor
  · intro hFX
    -- Reflection is immediate from faithfulness of the equivalence functor.
    exact isSubterminal_of_faithful_obj (F := F.functor) hFX
  · intro hX
    intro Z f g
    -- Apply the inverse functor and compare in the source category through the unit isomorphism.
    apply F.inverse.map_injective
    apply (cancel_mono (F.unitIso.app X).inv).1
    simpa using
      hX
        (F.inverse.map f ≫ (F.unitIso.app X).inv)
        (F.inverse.map g ≫ (F.unitIso.app X).inv)

/-- Helper for Lemma 7.43.3: subterminality is preserved by isomorphism. This is the transport
piece needed to move the representable witness from the replacement site back to the original
sheaf. -/
theorem isSubterminal_iff_of_iso
    {A B : Sheaf J (Type w)} (e : A ≅ B) :
    IsSubterminal A ↔ IsSubterminal B := by
  constructor
  · intro hA Z f g
    -- Postcompose with the inverse isomorphism to compare the two maps inside `A`.
    apply (cancel_mono e.inv).1
    simpa using hA (f ≫ e.inv) (g ≫ e.inv)
  · intro hB Z f g
    -- The same argument in the other direction transports subterminality back across `e`.
    apply (cancel_mono e.hom).1
    simpa using hB (f ≫ e.hom) (g ≫ e.hom)

/-- Helper for Lemma 7.43.3: the replacement-site presentation transports subterminality exactly
between the original sheaf `ℱ` and the representable witness `J'.yoneda.obj U₀`. -/
theorem replacement_site_isSubterminal_iff
    {C₀ : Type (max w u v)} [Category C₀] (J₀ : GrothendieckTopology C₀)
    (a : C ⥤ C₀) [a.IsDenseSubsite J J₀]
    {C' : Type (max w u v)} [Category C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (v' : C₀ ⥤ C') [v'.IsDenseSubsite J₀ J']
    (ℱ : Sheaf J (Type w)) (U₀ : C')
    (hrepr :
      Nonempty
        (CategoryTheory.yoneda.obj U₀ ≅
          ((sheafEquiv J₀ J' v' (Type (max w u v))).functor.obj
            ((sheafEquiv J J₀ a (Type (max w u v))).functor.obj
              ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ))).obj)) :
    IsSubterminal ℱ ↔ IsSubterminal (J'.yoneda.obj U₀) := by
  let ℱulift : Sheaf J (Type (max w u v)) :=
    (sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ
  let ℱ₀ : Sheaf J₀ (Type (max w u v)) :=
    (sheafEquiv J J₀ a (Type (max w u v))).functor.obj ℱulift
  let ℱ' : Sheaf J' (Type (max w u v)) :=
    (sheafEquiv J₀ J' v' (Type (max w u v))).functor.obj ℱ₀
  rcases hrepr with ⟨e⟩
  let eSheaf : J'.yoneda.obj U₀ ≅ ℱ' :=
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by
        ext X x
        -- The sheaf identity is read objectwise from the underlying presheaf identity.
        change (e.hom ≫ e.inv).app X x = x
        simpa using congrFun (NatTrans.congr_app e.hom_inv_id X) x
      inv_hom_id := by
        ext X x
        -- The same objectwise comparison proves the other triangle identity.
        change (e.inv ≫ e.hom).app X x = x
        simpa using congrFun (NatTrans.congr_app e.inv_hom_id X) x }
  constructor
  · intro hℱ
    have hℱulift : IsSubterminal ℱulift := by
      intro Z f g
      ext X x
      -- The source sheaf has singleton fibers, and `ULift` preserves singleton types.
      have hsub :
          Subsingleton (ℱ.obj.obj X) := by
        simpa using subsingleton_sections_of_isSubterminal (J := J) hℱ X.unop
      letI : Subsingleton (ℱulift.obj.obj X) :=
        by
          simpa [ℱulift] using
            (show Subsingleton (ULift.{max w u v, w} (ℱ.obj.obj X)) from inferInstance)
      exact Subsingleton.elim _ _
    have hℱ₀ : IsSubterminal ℱ₀ :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J J₀ a (Type (max w u v))) ℱulift).2 hℱulift
    have hℱ' : IsSubterminal ℱ' :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J₀ J' v' (Type (max w u v))) ℱ₀).2 hℱ₀
    -- Finish by transporting across the representable witness on the replacement site.
    exact (isSubterminal_iff_of_iso (J := J') eSheaf).2 hℱ'
  · intro hU₀
    have hℱ' : IsSubterminal ℱ' :=
      (isSubterminal_iff_of_iso (J := J') eSheaf).1 hU₀
    have hℱ₀ : IsSubterminal ℱ₀ :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J₀ J' v' (Type (max w u v))) ℱ₀).1 hℱ'
    have hℱulift : IsSubterminal ℱulift :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J J₀ a (Type (max w u v))) ℱulift).1 hℱ₀
    -- Reflect the remaining transport through the faithful `ULift`-whiskering functor.
    exact isSubterminal_of_faithful_obj
      (F := sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}) hℱulift

/-- Helper for Lemma 7.43.3: on a representable replacement site, a subterminal representable
sheaf yields an embedding localization morphism of topoi. -/
theorem representable_localization_isEmbedding_of_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C')
    (hsub : IsSubterminal (J'.yoneda.obj U₀)) :
    ((Over.forget U₀).morphismOfTopoiInOfCocontinuous (J'.over U₀) J').IsEmbedding := by
  let hhom : ∀ X : C', Subsingleton (X ⟶ U₀) :=
    (representable_yoneda_subterminal_iff_subsingleton_hom (J' := J') U₀).1 hsub
  let hfull : (Over.forget U₀).Full := overForget_full_of_subsingletonHom U₀ hhom
  letI : (Over.forget U₀).Full := hfull
  have hCounitAppIso :
      ∀ X : Sheaf (J'.over U₀) (Type (max u₁ v₁)),
        IsIso
          (((Over.forget U₀).sheafAdjunctionCocontinuous
            (Type (max u₁ v₁)) (J'.over U₀) J').counit.app X) := by
    intro X
    -- This is exactly Lemma 7.27.4 on the representable replacement site.
    exact
      localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
        (J := J') U₀ hhom X
  haveI :
      IsIso
        ((Over.forget U₀).sheafAdjunctionCocontinuous
          (Type (max u₁ v₁)) (J'.over U₀) J').counit := by
    -- Upgrade the componentwise source-proof isomorphisms to the whole counit transformation.
    exact NatIso.isIso_of_isIso_app _
  let hff :
      ((Over.forget U₀).sheafPushforwardCocontinuous
        (Type (max u₁ v₁)) (J'.over U₀) J').FullyFaithful :=
    ((Over.forget U₀).sheafAdjunctionCocontinuous
      (Type (max u₁ v₁)) (J'.over U₀) J').fullyFaithfulROfIsIsoCounit
  -- Repackage the fully faithful direct image as the source-facing embedding predicate.
  refine
    { toFull := by
        simpa [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using hff.full
      toFaithful := by
        simpa [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using hff.faithful }

/-- Helper for Lemma 7.43.3: the representable-localization comparison is an equivalence, so
precomposing the slice forgetful functor over the sheafified representable `h[U₀]^#[J']` with it
does not change the essential image. -/
theorem representable_comparison_forget_essImage
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    Functor.essImage
        (J'.representableLocalizationComparison U₀ ⋙ Over.forget h[U₀]^#[J']) =
      Functor.essImage (Over.forget h[U₀]^#[J']) := by
  let comparison := J'.representableLocalizationComparison U₀
  haveI : Functor.IsEquivalence comparison :=
    J'.representableLocalizationComparison_isEquivalence U₀
  let e := comparison.asEquivalence
  letI : Functor.EssSurj comparison :=
    { mem_essImage := fun Y ↦ ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩ }
  -- Essential images are invariant under precomposition by an equivalence.
  simpa [comparison] using
    (Functor.essImage_comp_of_essSurj
      (F := comparison) (G := Over.forget h[U₀]^#[J']))

/-- Helper for Lemma 7.43.3: on the representable replacement site, the localized inverse-image
functor agrees with the slice inverse-image functor after the comparison equivalence. This is the
owner-level bridge needed before comparing the two direct-image essential images. -/
noncomputable def representable_comparison_inverseImageIso_star
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    J'.overPullback (Type (max u₁ v₁)) U₀ ⋙ J'.representableLocalizationComparison U₀ ≅
      Over.star h[U₀]^#[J'] := by
  -- This is exactly the canonical comparison from Lemma 7.30.7 on the representable site.
  exact J'.representableLocalizationComparison_inverseImageIso U₀

/-- Helper for Lemma 7.43.3: on the representable replacement site, precomposing the slice-owner
forgetful functor with the comparison equivalence does not change its essential image. This is the
owner equality supplied by Lemma `7.30.5`; it compares the slice owner with the lower-shriek side,
not with the localization direct image `j_{U₀,*}`. -/
theorem representable_localization_lowerShriek_essImage_eq_slice_owner
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    Functor.essImage
        (J'.representableLocalizationComparison U₀ ⋙ Over.forget h[U₀]^#[J']) =
      Functor.essImage (Over.forget h[U₀]^#[J']) := by
  -- This is exactly the essential-image invariance under the comparison equivalence.
  exact representable_comparison_forget_essImage (J' := J') U₀

/-- Helper for Lemma 7.43.3: on the representable replacement site, a subterminal sheafified
representable already cuts out a subtopos via the localization embedding at `U₀`. -/
theorem representable_sheafified_slice_isSubtopos_of_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C')
    (hsub : IsSubterminal (J'.yoneda.obj U₀)) :
    IsSubtopos.{u₁, max u₁ v₁, v₁, v₁, max u₁ v₁}
      J' (Over.forget h[U₀]^#[J']).essImage := by
  let i := (Over.forget U₀).morphismOfTopoiInOfCocontinuous (J'.over U₀) J'
  have hi : i.IsEmbedding :=
    representable_localization_isEmbedding_of_subterminal (J' := J') U₀ hsub
  have hsubtopos :
      IsSubtopos.{u₁, max u₁ v₁, v₁, v₁, max u₁ v₁}
        J' (Functor.essImage (CategoryTheory.pushforward i)) :=
    MorphismOfTopoiIn.isSubtopos_essImage (J := J') i
  let _ := hsubtopos
  -- Route correction: the previous owner rewrite was wrong. The proved comparison theorem
  -- `representable_localization_lowerShriek_essImage_eq_slice_owner` only identifies
  -- `Over.forget h[U₀]^#[J']` with the lower-shriek owner `j_{U₀,!}` after the comparison
  -- equivalence, while `hsubtopos` is about the direct-image owner `j_{U₀,*}`.
  -- TODO: replace this invalid rewrite by the actual source-faithful bridge from the embedding
  -- presentation of `j_{U₀,*}` to objects over `h_{U₀}^#`.
  sorry

/-
Source correction for Lemma 7.43.3: keep the remaining proof on the route used in the text.
After Lemma 7.29.5, work on a subcanonical site with finite limits and a final object `X`, and
replace `ℱ` by a representable sheaf `h_U`. The forward direction should use the source fact that
`U ⟶ X` is mono/subterminal, hence Lemma 7.27.4 gives `j_U^{-1} j_{U,*} = id`, so the slice
localization is a subtopos. The reverse direction should evaluate the embedding condition on
representables: from `j_U^{-1} j_{U,*} h_{Z/U} ≅ h_{Z/U}` at `U` get
`Hom_{C/U}(U ×_X U, Z/U) ≅ Hom_{C/U}(U, Z/U)` for every `Z/U`; Yoneda gives
`U ×_X U ≅ U`, hence `U ⟶ X` is a mono and `h_U` is subterminal.
-/

/- Domain-style sampling for Lemma 7.43.3:
- primary domain: subtopoi of a sheaf topos arising from slice-topos localizations at
  subterminal sheaves;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `IsSubtopos`;
- best owner abstraction: the canonical left-hand owner is `IsSubterminal ℱ`, while
  `Mono (terminal.from ℱ)` is only the bridge/view expressing the same notion as a subobject of
  the terminal sheaf;
- primitive data: the sheaf `ℱ`;
- derived API: the source-facing reformulation in terms of `Mono (terminal.from ℱ)`.

Source/core/bridge triage:
- `source-facing`: the textbook phrasing that `ℱ ⟶ 1` is monic and the slice topos is a subtopos;
- `core/canonical`: `IsSubterminal ℱ` and the subtopos whose direct image is the localization
  pushforward along `localizationProjection ℱ`;
- `bridge/view`: `Mono (terminal.from ℱ)` via the standard subterminal equivalence.

The tempting owner `(Over.forget ℱ).essImage` is not the source statement: it would force a global
section of `ℱ`. The source owner is the direct-image essential image of the localization morphism
attached to `localizationProjection ℱ`. -/
-- Proof sketch: for the forward implication, the localization
-- `localizationProjection ℱ : ℱ.obj.Elementsᵒᵖ ⥤ C` is the slice-topos morphism from the text,
-- and its direct image is fully faithful when `ℱ` is subterminal. For the reverse implication,
-- reduce to the representable case via Lemma 7.29.5 and use the text's self-pullback/Yoneda
-- argument to show that the representing map is monic.
/-- Lemma 7.43.3: a sheaf `ℱ` on a site `(𝒞, J)` is subterminal if and only if the slice topos
`Sh(𝒞, J) / ℱ`, viewed in `Sh(𝒞, J)` through the localization direct image `j_{ℱ,*}`, is a
subtopos. -/
theorem sheaf_slice_isSubtopos_iff_isSubterminal
    (ℱ : Sheaf J (Type v))
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    IsSubterminal ℱ ↔
      IsSubtopos J
        (Functor.essImage
          ((localizationProjection ℱ).sheafPushforwardCocontinuous
            (Type v) (localizationTopology ℱ) J)) := by
  constructor
  · intro hℱ
    -- Source route: prove that the direct image of the localization morphism associated to
    -- `localizationProjection ℱ` is fully faithful. In the representable replacement this is
    -- Lemma 7.27.4 applied to the monomorphism `U -> X`.
    sorry
  · intro hℱ
    -- Source route: from the subtopos presentation of `j_{ℱ,*}`, pass to the replacement site
    -- where `ℱ = h_U`; evaluating `j_U^{-1} j_{U,*}` on representables and using Yoneda gives
    -- `U ×_X U ≅ U`, hence `U -> X` is mono and `ℱ` is subterminal.
    sorry

/-- Source-facing reformulation of Lemma 7.43.3: a sheaf `ℱ` is a subobject of the terminal sheaf
if and only if the slice topos `Sh(𝒞, J) / ℱ`, viewed through its localization direct image, is a
subtopos. -/
theorem sheaf_slice_isSubtopos_iff_subterminal
    (ℱ : Sheaf J (Type v))
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    Mono (terminal.from ℱ) ↔
      IsSubtopos J
        (Functor.essImage
          ((localizationProjection ℱ).sheafPushforwardCocontinuous
            (Type v) (localizationTopology ℱ) J)) := by
  constructor
  · intro hℱ
    letI : Mono (terminal.from ℱ) := hℱ
    exact (sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).1
      isSubterminal_of_mono_terminal_from
  · intro hℱ
    exact (IsSubterminal.mono_terminal_from
      ((sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).2 hℱ))

end

end CategoryTheory

/-! ### Definition_7_43_4 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Definition 7.43.4:
- primary domain: open subtopoi of a sheaf topos arising from slice-topos inclusions at
  subterminal sheaves;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `Functor.essImage`;
- best owner abstraction: the source-facing predicate `IsOpenSubtopos` on object properties of
  `Sheaf J (Type w)`, with `IsSubterminal U` as the canonical owner of the witness that `U` is
  subterminal;
- primitive data: a subterminal sheaf `U` and the induced object property `(Over.forget U).essImage`;
- derived API: the bridge-view reformulation via `Mono (terminal.from U)`, supplied canonically by
  mathlib's subterminal-object API.

Source/core/bridge triage:
- `source-facing`: `IsOpenSubtopos`;
- `core/canonical`: `IsSubterminal` and `Functor.essImage`;
- `bridge/view`: `Mono (terminal.from U)` via the equivalence between subterminal objects and
  monomorphisms to the terminal object. -/
/-- Definition 7.43.4: a subtopos of `Sh(C)` is open if it is the essential image of the
slice-topos inclusion `Sh(C)/U ⥤ Sh(C)` for some subterminal sheaf `U`. -/
def IsOpenSubtopos
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ U : Sheaf J (Type w), IsSubterminal U ∧ P = (Over.forget U).essImage

/-- An object property on `Sh(C)` is an open subtopos exactly when it is the essential image of
the slice-topos inclusion at a subterminal sheaf. -/
-- Proof sketch: unfold `IsOpenSubtopos`; this is the defining existential characterization.
theorem isOpenSubtopos_iff_exists_subterminal
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) :
    IsOpenSubtopos P ↔ ∃ U : Sheaf J (Type w), IsSubterminal U ∧ P = (Over.forget U).essImage :=
  by
  -- Unfold the predicate so the goal becomes the defining existential characterization.
  rfl

end CategoryTheory
