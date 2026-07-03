import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_26_1 (from Chap07) -/
open CategoryTheory Opposite

universe u v w

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ℱ 𝒢 : Sheaf J (Type w)}

private abbrev localizedSheafHomPresheaf
    (J : GrothendieckTopology C) (U : C) (ℱ 𝒢 : Sheaf J (Type w)) :
    (Over U)ᵒᵖ ⥤ Type (max u v w) :=
  (CategoryTheory.sheafHom (J := J.over U) (ℱ.over U) (𝒢.over U)).1

/- Domain-style sampling for Lemma 7.26.1:
- primary domain: descent of morphisms for set-valued sheaves on localized sites;
- sampled owner API:
  `Pseudofunctor.presheafHomObjHomEquiv`,
  `Pseudofunctor.DescentData.subtypeCompatibleHomEquiv`,
  `Pseudofunctor.bijective_toDescentData_map_iff`,
  `CategoryTheory.Pseudofunctor.sheafHom`,
  `Functor.sheafPushforwardContinuousComp'`;
- source-facing layer: explicit local morphisms on a fixed cover and their overlap compatibility;
- core/canonical owner: the descent-data functor
  `((J.pseudofunctorOver (Type w)).toDescentData (fun I : 𝒰.Arrow ↦ I.f))` on the sheaf
  pseudofunctor over slice sites;
- bridge/view: the textbook local family `φ I : ℱ.over I.Y ⟶ 𝒢.over I.Y` is the image of the
  canonical compatible family for the sheaf-Hom presheaf, transported through
  `Functor.sheafPushforwardContinuousComp'`.

Primitive data are the cover `𝒰 : J.Cover U` and the local morphisms on its members. The
comparison isomorphism between iterated localization and direct localization is already owned by
`Functor.sheafPushforwardContinuousComp'`, and the compatible-family owner already lives in the
descent-data API. The public surface here should therefore center the canonical descent-data map on
Homs and keep the overlap-equality formulation only as a source-facing companion.
-/

/-- Helper for Lemma 7.26.1: after transporting sheaves on the iterated slice `(C/U)/(T/U)`
across the canonical equivalence with `C/T`, one recovers the direct localization functor along
`T ⟶ U`. -/
private def iteratedSlicePullbackIsoOverMapPullback
    (T : Over U) (ℱ : Sheaf J (Type w)) :
    (T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
      (((J.over U).overPullback (Type w) T).obj (ℱ.over U)) ≅
    (J.overMapPullback (Type w) T.hom).obj (ℱ.over U) := by
  -- Compare the two sheaves on `C/T` at the presheaf level using the equality
  -- `iteratedSliceBackward ⋙ forget = Over.map T.hom`.
  refine (fullyFaithfulSheafToPresheaf (J.over T.left) (Type w)).preimageIso ?_
  simpa [GrothendieckTopology.overPullback, GrothendieckTopology.overMapPullback,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor] using
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
      ((ℱ.over U).obj))

/-- Helper for Lemma 7.26.1: transporting a morphism between the iterated localizations on
`((C/U)/(T/U))` across the canonical slice equivalence gives a morphism on `C/T`. -/
private def iteratedSliceSheafCongrHomEquiv
    (T : Over U) :
    (((J.over U).overPullback (Type w) T).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) T).obj (𝒢.over U)) ≃
    ((T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
        (((J.over U).overPullback (Type w) T).obj (ℱ.over U)) ⟶
      (T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
        (((J.over U).overPullback (Type w) T).obj (𝒢.over U))) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor)).homEquiv

/-- Helper for Lemma 7.26.1: the ordinary Hom sheaf on `C/U` evaluated at a cover arrow gives the
localized morphisms on that slice member. -/
private def localizedSheafHomEquiv (𝒰 : J.Cover U) (I : 𝒰.Arrow) :
    (localizedSheafHomPresheaf J U ℱ 𝒢).obj
      (Opposite.op (Over.mk I.f)) ≃
      (ℱ.over I.Y ⟶ 𝒢.over I.Y) := by
  -- Route correction: use the ordinary slice-site Hom owner and transport only the objectwise
  -- iterated-slice comparison, rather than building a global NatIso of Hom-presheaves.
  change (((J.over U).overPullback (Type w) (Over.mk I.f)).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) (Over.mk I.f)).obj (𝒢.over U)) ≃
      (ℱ.over I.Y ⟶ 𝒢.over I.Y)
  exact (iteratedSliceSheafCongrHomEquiv (J := J) (ℱ := ℱ) (𝒢 := 𝒢) (T := Over.mk I.f)).trans
    (Iso.homCongr
      (iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk I.f) (ℱ := ℱ))
      (iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk I.f) (ℱ := 𝒢)))

/-- Helper for Lemma 7.26.1: the value of the ordinary Hom sheaf on `C/U` at the terminal object
recovers morphisms on the whole localized site `C/U`. -/
private def localizedSheafHomAtBaseEquiv :
    (localizedSheafHomPresheaf J U ℱ 𝒢).obj
      (Opposite.op (Over.mk (𝟙 U))) ≃
      (ℱ.over U ⟶ 𝒢.over U) := by
  change (((J.over U).overPullback (Type w) (Over.mk (𝟙 U))).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) (Over.mk (𝟙 U))).obj (𝒢.over U)) ≃
      (ℱ.over U ⟶ 𝒢.over U)
  -- The terminal object in `Over U` reduces the direct pullback back to `C/U`.
  refine (iteratedSliceSheafCongrHomEquiv (J := J) (ℱ := ℱ) (𝒢 := 𝒢)
      (T := Over.mk (𝟙 U))).trans ?_
  -- The remaining comparison is the identity pullback on `C/U`.
  simpa using
    (Iso.homCongr
      ((iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk (𝟙 U))
        (ℱ := ℱ)).trans ((J.overMapPullbackId (Type w) U).app (ℱ.over U)))
      ((iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk (𝟙 U))
        (ℱ := 𝒢)).trans ((J.overMapPullbackId (Type w) U).app (𝒢.over U))))

/-- Helper for Lemma 7.26.1: the cover arrows in `Over U` generate exactly the pullback of the
original covering sieve to the terminal object `U/U`. -/
private theorem cover_arrows_sieve_over_terminal
    (𝒰 : J.Cover U) :
    Sieve.overEquiv (Over.mk (𝟙 U))
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) =
      (𝒰 : Sieve U) := by
  -- The generated sieve in the slice site consists exactly of morphisms factoring through one of
  -- the chosen cover members.
  ext Z g
  rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨I, h, _⟩
    have hw : h.left ≫ I.f = g := by
      simpa using Over.w h
    exact hw ▸ (𝒰 : Sieve U).downward_closed I.hf h.left
  · intro hg
    let a : Over.mk (g ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk g := Over.homMk (𝟙 Z) (by simp)
    refine ⟨⟨Z, g, hg⟩, a, ?_⟩
    ext
    simp [a]

/-- The restriction of a morphism on the localized site `C/U` to a chosen member of a cover of
`U`, read through the ordinary slice-site Hom sheaf and then transported across the canonical
slice-site pullback isomorphism. -/
def restrict_sheaf_hom_to_cover_arrow
    (𝒰 : J.Cover U) (ψ : ℱ.over U ⟶ 𝒢.over U) (I : 𝒰.Arrow) :
    ℱ.over I.Y ⟶ 𝒢.over I.Y :=
  localizedSheafHomEquiv 𝒰 I <|
    (localizedSheafHomPresheaf J U ℱ 𝒢).map
      (Over.homMk I.f).op ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ)

/-- A family of local morphisms on the members of a cover of `U` is compatible on overlaps when
the induced family of sections of the ordinary localized Hom sheaf on `C / U` is compatible. -/
def LocalizedSheafHomCompatible
    (𝒰 : J.Cover U) (φ : ∀ I : 𝒰.Arrow, ℱ.over I.Y ⟶ 𝒢.over I.Y) : Prop :=
  Presieve.Arrows.Compatible
    (localizedSheafHomPresheaf J U ℱ 𝒢)
    (fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
    (fun I : 𝒰.Arrow ↦ (localizedSheafHomEquiv 𝒰 I).symm (φ I))

section

variable (𝒰 : J.Cover U)

private theorem localizedSheafHom_isSheafFor_cover :
    ∀ {ℱ 𝒢 : Sheaf (J.over U) (Type w)},
    Presieve.IsSheafFor
      ((CategoryTheory.sheafHom (J := J.over U) ℱ 𝒢).1)
      (Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) := by
  intro ℱ 𝒢
  -- The ordinary internal Hom on the slice site is already a sheaf; we only identify the cover
  -- arrows with the covering sieve of `U/U`.
  rw [Presieve.isSheafFor_iff_generate]
  refine Presheaf.IsSheaf.isSheafFor
    ((CategoryTheory.sheafHom (J := J.over U) ℱ 𝒢).2) _ ?_
  rw [J.mem_over_iff, cover_arrows_sieve_over_terminal (J := J) (U := U) 𝒰]
  exact 𝒰.condition

private theorem coverwise_compatible_sheaf_hom_of_global
    (𝒰 : J.Cover U) (ψ : ℱ.over U ⟶ 𝒢.over U) :
    LocalizedSheafHomCompatible 𝒰
      (fun I ↦ restrict_sheaf_hom_to_cover_arrow 𝒰 ψ I) := by
  -- The local restrictions are literally the compatible family cut out from the section at `U/U`.
  unfold LocalizedSheafHomCompatible restrict_sheaf_hom_to_cover_arrow
  simpa using
    (Presieve.Arrows.toCompatible
      (localizedSheafHomPresheaf J U ℱ 𝒢)
      (fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
      ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ)).property

/-- Lemma 7.26.1, source-facing form: a coverwise family of local morphisms satisfying
`LocalizedSheafHomCompatible` glues uniquely to a morphism on `ℱ|_{C/U}`. -/
theorem exists_unique_localized_hom_of_coverwise_compatible
    (𝒰 : J.Cover U)
    (φ : ∀ I : 𝒰.Arrow, ℱ.over I.Y ⟶ 𝒢.over I.Y)
    (hφ : LocalizedSheafHomCompatible 𝒰 φ) :
    ∃! ψ : ℱ.over U ⟶ 𝒢.over U, ∀ I : 𝒰.Arrow,
      restrict_sheaf_hom_to_cover_arrow 𝒰 ψ I = φ I := by
  let P := localizedSheafHomPresheaf J U ℱ 𝒢
  let π := fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f
  -- The cover sheaf condition gives a bijection between global sections and compatible families.
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp
      (localizedSheafHom_isSheafFor_cover (𝒰 := 𝒰) (ℱ := ℱ.over U) (𝒢 := 𝒢.over U))
  let x : Subtype (Presieve.Arrows.Compatible P π) :=
    by
      refine ⟨fun I ↦ (localizedSheafHomEquiv 𝒰 I).symm (φ I), ?_⟩
      simpa [P, π] using hφ
  obtain ⟨s, hs⟩ := hbij.surjective x
  refine ⟨(localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢) s), ?_, ?_⟩
  · intro I
    -- The glued section restricts to the prescribed local morphism on each cover member.
    rw [restrict_sheaf_hom_to_cover_arrow]
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    change P.map (π I).op
        ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm
          ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)) s)) = x.1 I
    rw [Equiv.symm_apply_apply]
    simpa using congrFun (congrArg Subtype.val hs) I
  · intro ψ hψ
    -- Uniqueness comes from injectivity of the global-section-to-compatible-family map.
    let sψ :=
      (localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ
    have hψ' :
        Presieve.Arrows.toCompatible P π
            sψ = x := by
      apply Subtype.ext
      funext I
      rw [show x.1 I = (localizedSheafHomEquiv 𝒰 I).symm (φ I) by rfl]
      apply (localizedSheafHomEquiv 𝒰 I).injective
      simpa [sψ, restrict_sheaf_hom_to_cover_arrow, P, π] using hψ I
    apply (localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm.injective
    simpa [sψ] using
      (hbij.injective (hψ'.trans hs.symm) : sψ = s)

/-- Lemma 7.26.1, owner-level form: for a fixed cover `𝒰` of `U`, the ordinary Hom sheaf on
`C/U` satisfies the sheaf condition for the presieve generated by the cover arrows. -/
theorem localizedSheafPseudofunctorOver_isPrestackFor_cover
    (𝒰 : J.Cover U) :
    Presieve.IsSheafFor
      (localizedSheafHomPresheaf J U ℱ 𝒢)
      (Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) := by
  -- This is exactly the coverwise sheaf condition proved for the ordinary slice-site Hom owner.
  simpa [localizedSheafHomPresheaf] using
    (localizedSheafHom_isSheafFor_cover (J := J) (U := U) (𝒰 := 𝒰)
      (ℱ := ℱ.over U) (𝒢 := 𝒢.over U))

end

end

end GrothendieckTopology
end CategoryTheory

/-! ### Lemma_7_26_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CartesianClosed

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.26.2:
- primary domain: cartesian closed structure on sheaves of types and the source-facing sheaf-Hom;
- sampled owner declarations:
  `CategoryTheory.sheafHom`,
  `CategoryTheory.sheafHom'Iso`,
  `CategoryTheory.Functor.functorHom`,
  `CategoryTheory.fullyFaithfulSheafToPresheaf`,
  `(ihom.adjunction G).homEquiv`;
- source-facing layer: the Stacks-project sheaf-Hom currying bijection
  `((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H)`;
- core/canonical owner: the cartesian-closed internal Hom `G ⟹ H` in `Sheaf J (Type (max u v))`;
- bridge/view: the canonical presheaf bridge
  `presheafHomIsoFunctorHom : presheafHom F G ≅ F.functorHom G` and its sheaf-level transport
  `ihomIsoSheafHom : G ⟹ H ≅ sheafHom G H`.

Primitive data are only the sheaves `F`, `G`, and `H`. The source and target variance maps on the
right-hand side are derived by transporting the canonical owner maps `pre` and `(ihom G).map`
across `ihomIsoSheafHom`, so they should not remain separate public owner-level definitions.
At the presheaf level, the objectwise bridge `presheafHom F G (X) ≃ (F.functorHom G)(X)` is only
internal proof machinery for this owner-level comparison, not a second local API layer.
-/

/-- The localized Hom presheaf `presheafHom F G` is canonically the functor-category internal Hom
proxy `F.functorHom G`. -/
private def presheafHomIsoFunctorHom (F G : Cᵒᵖ ⥤ Type (max u v)) :
    presheafHom F G ≅ F.functorHom G :=
  NatIso.ofComponents
    (fun X ↦
      (show (presheafHom F G).obj X ≃ (F.functorHom G).obj X from
        { toFun := fun α ↦
            { app := fun Y f ↦ α.app (op (Over.mk f.unop))
              naturality := by
                intro Y Z g f
                simpa using
                  α.naturality
                    (Over.homMk g.unop : Over.mk ((f ≫ g).unop) ⟶ Over.mk f.unop).op }
          invFun := fun α ↦
            { app := fun ⟨Y⟩ ↦ α.app (op Y.left) Y.hom.op
              naturality := by
                rintro ⟨Y⟩ ⟨Z⟩ ⟨g⟩
                dsimp
                have hfg : Y.hom.op ≫ g.left.op = Z.hom.op := by
                  simpa using congrArg Quiver.Hom.op (Over.w g)
                erw [← hfg]
                exact α.naturality g.left.op Y.hom.op }
          left_inv := fun _ ↦ rfl
          right_inv := fun α ↦ by
            ext Y f
            rfl }).toIso)
    fun {X} {Y} f ↦ by
      ext α Z g
      rfl

/-- For sheaves of types, the exponential object in `Sheaf J (Type (max u v))` is canonically the
sheaf `sheafHom G H` of localized morphisms. -/
private def ihomIsoSheafHom (G H : Sheaf J (Type (max u v))) : G ⟹ H ≅ sheafHom G H :=
  (fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
    ((presheafHomIsoFunctorHom G.obj H.obj).symm ≪≫ (sheafHom'Iso G H).symm)

/-- Lemma 7.26.2: for sheaves of types on a site `(C, J)`, morphisms `F × G ⟶ H` are in
canonical bijection with morphisms `F ⟶ sheafHom G H`. This is the Stacks Project sheaf-Hom form
of currying. -/
def sheaf_prod_sheafHom_equiv (F G H : Sheaf J (Type (max u v))) :
    ((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (((prod.braiding F G).homCongr (Iso.refl H)).trans
      ((((tensorLeftIsoProd G).app F).symm.homCongr (Iso.refl H)).trans
        ((ihom.adjunction G).homEquiv F H))).trans
    ((Iso.refl F).homCongr (ihomIsoSheafHom G H))

-- Proof sketch: this is the standard `Equiv.apply_symm_apply` identity for the currying
-- equivalence above.
/-- The inverse of `sheaf_prod_sheafHom_equiv` sends a sheaf-Hom morphism back to the unique
product morphism whose curry is that morphism. -/
theorem sheaf_prod_sheafHom_equiv_apply_symm_apply
    (F G H : Sheaf J (Type (max u v))) (f : F ⟶ sheafHom G H) :
    sheaf_prod_sheafHom_equiv F G H ((sheaf_prod_sheafHom_equiv F G H).symm f) = f := by
  -- This is the left inverse law of the already-constructed currying equivalence.
  exact (sheaf_prod_sheafHom_equiv F G H).apply_symm_apply f

-- Proof sketch: this is the standard `Equiv.symm_apply_apply` identity for the currying
-- equivalence above.
/-- Currying and then uncurrying via `sheaf_prod_sheafHom_equiv` recovers the original morphism
`F × G ⟶ H`. -/
theorem sheaf_prod_sheafHom_equiv_symm_apply_apply
    (F G H : Sheaf J (Type (max u v))) (f : (F ⨯ G) ⟶ H) :
    (sheaf_prod_sheafHom_equiv F G H).symm (sheaf_prod_sheafHom_equiv F G H f) = f := by
  -- This is the right inverse law of the same currying equivalence.
  exact (sheaf_prod_sheafHom_equiv F G H).symm_apply_apply f

end

/-! ### Lemma_7_26_3 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable
open scoped CartesianClosed
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (U : C) (ℱ : Sheaf J (Type (max u v)))

/- Domain-style sampling for Lemma 7.26.3:
- primary domain: internal Hom for sheaves of types and the localization direct image `j_{U*}`;
- sampled owner API:
  `sheaf_prod_sheafHom_equiv`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `GrothendieckTopology.overPullback`/`Sheaf.over`,
  `localization_lowerShriek_overPullback_prodIso`,
  `Functor.sheafAdjunctionCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the canonical identification `sheafHom (h_U^#) ℱ ≅ j_{U*}(ℱ.over U)`;
  `core/canonical`: the localization morphism of topoi
  `(Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J` and its direct image `j_{U*}`;
  `bridge/view`: the product comparison `localization_lowerShriek_overPullback_prodIso U 𝒢`,
  the currying equivalence `sheaf_prod_sheafHom_equiv`, and the adjunction chain induced by
  `Over.forget U`.

Primitive data are only the localized object `U` and the sheaf `ℱ`. The Hom-equivalence for a test
sheaf `𝒢` is derived from these owner-level constructions, so it should remain private proof
machinery rather than a second public owner.
-/

/-- Helper for Lemma 7.26.3: the localized Hom presheaf is canonically identified with the
functor-category internal Hom proxy. -/
private def presheaf_hom_iso_functor_hom
    (F G : Cᵒᵖ ⥤ Type (max u v)) :
    presheafHom F G ≅ F.functorHom G :=
  NatIso.ofComponents
    (fun X ↦
      (show (presheafHom F G).obj X ≃ (F.functorHom G).obj X from
        { toFun := fun α ↦
            { app := fun Y f ↦ α.app (op (Over.mk f.unop))
              naturality := by
                intro Y Z g f
                simpa using
                  α.naturality
                    (Over.homMk g.unop : Over.mk ((f ≫ g).unop) ⟶ Over.mk f.unop).op }
          invFun := fun α ↦
            { app := fun ⟨Y⟩ ↦ α.app (op Y.left) Y.hom.op
              naturality := by
                rintro ⟨Y⟩ ⟨Z⟩ ⟨g⟩
                dsimp
                have hfg : Y.hom.op ≫ g.left.op = Z.hom.op := by
                  simpa using congrArg Quiver.Hom.op (Over.w g)
                erw [← hfg]
                exact α.naturality g.left.op Y.hom.op }
          left_inv := fun _ ↦ rfl
          right_inv := fun α ↦ by
            ext Y f
            rfl }).toIso)
    fun {X} {Y} f ↦ by
      ext α Z g
      rfl

/-- Helper for Lemma 7.26.3: for sheaves of types, the exponential object is canonically the
sheaf of localized morphisms. -/
private def ihom_iso_sheafHom
    (G H : Sheaf J (Type (max u v))) :
    G ⟹ H ≅ sheafHom G H :=
  (fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
    ((presheaf_hom_iso_functor_hom G.obj H.obj).symm ≪≫ (sheafHom'Iso G H).symm)

/-- Helper for Lemma 7.26.3: the standard currying equivalence for sheaf-Hom, written using local
owner-level transports so later naturality proofs do not depend on private declarations from
Lemma 7.26.2. -/
private def sheaf_prod_sheafHom_equiv_local
    (F G H : Sheaf J (Type (max u v))) :
    ((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (((prod.braiding F G).homCongr (Iso.refl H)).trans
      ((((tensorLeftIsoProd G).app F).symm.homCongr (Iso.refl H)).trans
        ((ihom.adjunction G).homEquiv F H))).trans
    ((Iso.refl F).homCongr (ihom_iso_sheafHom G H))

/-- Helper for Lemma 7.26.3: applying the inverse local currying equivalence and currying back
recovers the original sheaf-Hom morphism. -/
private theorem sheaf_prod_sheafHom_equiv_local_apply_symm_apply
    (F G H : Sheaf J (Type (max u v))) (f : F ⟶ sheafHom G H) :
    sheaf_prod_sheafHom_equiv_local F G H
        ((sheaf_prod_sheafHom_equiv_local F G H).symm f) = f := by
  exact (sheaf_prod_sheafHom_equiv_local F G H).apply_symm_apply f

private noncomputable def sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv
    (𝒢 : Sheaf J (Type (max u v))) :
    (𝒢 ⟶ sheafHom h[U]^#[J] ℱ) ≃
      (𝒢 ⟶ ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj
        (ℱ.over U))) := by
  simpa using
    (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm.trans
      (((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr
          (Iso.refl ℱ)).trans
        ((((Over.forget U).sheafAdjunctionContinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
            (Type (max u v)) (J.over U) J).homEquiv _ _)))

/-- Helper for Lemma 7.26.3: the currying equivalence
`((𝒢 × h_U^#) ⟶ ℱ) ≃ (𝒢 ⟶ sheafHom h_U^# ℱ)` is natural in the test sheaf. -/
private theorem sheaf_prod_sheafHom_equiv_naturality_left
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (k : (𝒢 ⨯ h[U]^#[J]) ⟶ ℱ) :
    sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ (prod.map f (𝟙 h[U]^#[J]) ≫ k) =
      f ≫ sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ k := by
  -- Route correction: prove naturality for the forward currying map first, so the only
  -- substantive rewrite is the public `ihom.adjunction` naturality theorem.
  -- Rewrite the currying equivalence into the adjunction `Hom(G ⊗ -, ℱ) ≃ Hom(-, G ⟹ ℱ)`.
  unfold sheaf_prod_sheafHom_equiv_local
  repeat rw [Equiv.trans_apply]
  simp only [Iso.homCongr_apply, Category.assoc, Iso.refl_hom, Iso.refl_inv]
  -- Identify precomposition by `prod.map f (𝟙 _)` with the left adjoint's action on `f`.
  change ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
      (((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
        (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ) ≫
      (ihom_iso_sheafHom h[U]^#[J] ℱ).hom =
    f ≫ ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢 ℱ)
      (((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
        (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ) ≫
      (ihom_iso_sheafHom h[U]^#[J] ℱ).hom
  have hpre :
      ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ =
        (MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
            (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
    have hbraid :
        (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) =
          prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv := by
      apply prod.hom_ext
      · simp
      · simp
    calc
      ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ =
        ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
          prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
        change
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
              ((prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J])) ≫
                k ≫ 𝟙 ℱ =
            ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
              (prod.map (𝟙 h[U]^#[J]) f ≫ (prod.braiding 𝒢 h[U]^#[J]).inv) ≫
                k ≫ 𝟙 ℱ
        exact congrArg
          (fun m ↦ ((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫ m ≫ k ≫ 𝟙 ℱ)
          hbraid
      _ =
        (MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
          ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
            (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ := by
        simpa [Category.assoc] using
          congrArg
            (fun m ↦ m ≫ (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ)
            (((tensorLeftIsoProd h[U]^#[J]).hom.naturality f).symm)
  have harg :
      ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
          (((tensorLeftIsoProd h[U]^#[J]).app 𝒢').hom ≫
            (prod.braiding 𝒢' h[U]^#[J]).inv ≫ prod.map f (𝟙 h[U]^#[J]) ≫ k ≫ 𝟙 ℱ) =
        ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ)
          ((MonoidalCategory.tensorLeft h[U]^#[J]).map f ≫
            ((tensorLeftIsoProd h[U]^#[J]).app 𝒢).hom ≫
              (prod.braiding 𝒢 h[U]^#[J]).inv ≫ k ≫ 𝟙 ℱ) := by
    exact congrArg ((ihom.adjunction h[U]^#[J]).homEquiv 𝒢' ℱ) hpre
  rw [harg]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rfl

/-- Helper for Lemma 7.26.3: the currying equivalence
`((𝒢 × h_U^#) ⟶ ℱ) ≃ (𝒢 ⟶ sheafHom h_U^# ℱ)` is natural in the test sheaf. -/
private theorem sheaf_prod_sheafHom_equiv_naturality_left_symm
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (g : 𝒢 ⟶ sheafHom h[U]^#[J] ℱ) :
    (sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).symm (f ≫ g) =
      prod.map f (𝟙 h[U]^#[J]) ≫
        (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g := by
  -- Apply the forward currying equivalence to both sides and cancel using its inverse laws.
  apply (sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).injective
  -- The left-hand side re-curries to `f ≫ g`, while the right-hand side does so by forward
  -- naturality of the already-proved currying equivalence.
  rw [sheaf_prod_sheafHom_equiv_local_apply_symm_apply]
  rw [sheaf_prod_sheafHom_equiv_naturality_left (U := U) (ℱ := ℱ) f]
  rw [sheaf_prod_sheafHom_equiv_local_apply_symm_apply]

/-- Helper for Lemma 7.26.3: the product comparison of Lemma 7.25.7 is natural in the sheaf
variable. -/
private theorem localization_lowerShriek_overPullback_prodIso_hom_naturality
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.overPullback (Type (max u v)) U).map f) ≫
      (localization_lowerShriek_overPullback_prodIso U 𝒢).hom =
        (localization_lowerShriek_overPullback_prodIso U 𝒢').hom ≫
          prod.map f (𝟙 h[U]^#[J]) := by
  -- Rewrite the packaged comparison once so the goal becomes a product-map identity.
  simp [localization_lowerShriek_overPullback_prodIso,
    GrothendieckTopology.representableLocalizationComparison]
  -- Check the two product projections separately, using naturality of the comparison from
  -- Lemma 7.30.7.
  apply prod.hom_ext
  · rw [prod.lift_fst, prod.lift_fst]
    have h := congrArg (fun k => k ≫ prod.snd)
      (congrArg CommaMorphism.left
        ((J.representableLocalizationComparison_inverseImageIso U).hom.naturality f))
    simpa [Sheaf.over, Category.assoc] using h
  · rw [prod.lift_snd, prod.lift_snd]
    have h := congrArg (fun k => k ≫ prod.fst)
      (congrArg CommaMorphism.left
        ((J.representableLocalizationComparison_inverseImageIso U).hom.naturality f))
    simpa [Sheaf.over, Category.assoc] using h

private theorem sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality
    {𝒢 𝒢' : Sheaf J (Type (max u v))} (f : 𝒢' ⟶ 𝒢)
    (g : 𝒢 ⟶ sheafHom h[U]^#[J] ℱ) :
    sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢' (f ≫ g) =
      f ≫ sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 g := by
  -- Unfold the composite equivalence once so each source-proof step becomes a separate rewrite.
  unfold sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv
  -- First pass through the inverse currying equivalence.
  change
    ((localization_lowerShriek_overPullback_prodIso U 𝒢').symm.homCongr (Iso.refl ℱ)).trans
        ((((Over.forget U).sheafAdjunctionContinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _))
        ((sheaf_prod_sheafHom_equiv_local 𝒢' h[U]^#[J] ℱ).symm (f ≫ g)) =
      f ≫
        ((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr (Iso.refl ℱ)).trans
            ((((Over.forget U).sheafAdjunctionContinuous
                  (Type (max u v)) (J.over U) J).homEquiv _ _).trans
              (((Over.forget U).sheafAdjunctionCocontinuous
                  (Type (max u v)) (J.over U) J).homEquiv _ _))
            ((sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g)
  rw [sheaf_prod_sheafHom_equiv_naturality_left_symm (U := U) (ℱ := ℱ) f g]
  -- Then rewrite across the comparison `j_{U!} j_U^{-1} 𝒢 ≅ 𝒢 × h_U^#`.
  have hloc :
      ((localization_lowerShriek_overPullback_prodIso U 𝒢').symm.homCongr (Iso.refl ℱ))
        (prod.map f (𝟙 h[U]^#[J]) ≫
          (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g) =
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.overPullback (Type (max u v)) U).map f) ≫
        ((localization_lowerShriek_overPullback_prodIso U 𝒢).symm.homCongr (Iso.refl ℱ))
          ((sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g) := by
    simpa [Iso.homCongr_apply, Category.assoc] using
      congrArg
        (fun m ↦ m ≫ (sheaf_prod_sheafHom_equiv_local 𝒢 h[U]^#[J] ℱ).symm g)
        ((localization_lowerShriek_overPullback_prodIso_hom_naturality (U := U)
          (𝒢 := 𝒢) (𝒢' := 𝒢') f).symm)
  simpa [Equiv.trans_apply, Category.assoc,
    CategoryTheory.Adjunction.homEquiv_naturality_left] using
    congrArg
      (fun x ↦
        ((((Over.forget U).sheafAdjunctionContinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _).trans
          (((Over.forget U).sheafAdjunctionCocontinuous
              (Type (max u v)) (J.over U) J).homEquiv _ _)) x)
      hloc
  -- The final two rewrites are the left naturality squares for the localization adjunctions.

/-- Lemma 7.26.3: for a site `(C, J)`, an object `U : C`, and a sheaf of sets `ℱ`, the sheaf-Hom
from the sheafified representable `h_U^#` to `ℱ` is canonically identified with the pushforward of
the restricted sheaf `ℱ.over U` from the slice site `(C/U, J.over U)` back to `(C, J)`. -/
noncomputable def sheafHom_sheafifiedRepresentable_iso_pushforward_restriction
    :
    sheafHom h[U]^#[J] ℱ ≅
      ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj (ℱ.over U)) :=
  Yoneda.ext _ _
    (fun {𝒢} f ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢 f)
    (fun {𝒢} f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ 𝒢).symm f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).left_inv f)
    (fun f ↦
      (sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv U ℱ _).right_inv f)
    (fun f g ↦
      sheafHom_sheafifiedRepresentable_pushforward_restriction_homEquiv_naturality U ℱ f g)

-- Proof sketch: the forward comparison morphism here is the `hom` of an explicit isomorphism, so
-- it is an isomorphism by the standard `Iso.hom` instance.
/-- The forward comparison morphism from `sheafHom h_U^# ℱ` to `j_{U*}(ℱ.over U)` is an
isomorphism. -/
theorem sheafHom_sheafifiedRepresentable_iso_pushforward_restriction_hom_isIso :
    IsIso (sheafHom_sheafifiedRepresentable_iso_pushforward_restriction U ℱ).hom := by
  -- The comparison morphism is already the `hom` field of the explicit Yoneda isomorphism above.
  infer_instance

end
