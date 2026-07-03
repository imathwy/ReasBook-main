import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_24_1 (from Chap06) -/
open CategoryTheory TopCat TopCat.Presheaf PresheafOfModules TopologicalSpace

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf RingCat.{u})

/- Domain-style sampling for Lemma 6.24.1:
- primary domain: direct image for presheaves of modules along a continuous map, obtained by
  reindexing along the induced map of opens;
- sampled owner API:
  `TopCat.Presheaf.pushforward`,
  `Opens.map`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.pushforward`;
- source/core/bridge triage:
  `source-facing`: the direct-image functor
  `f_* : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f_* \mathcal O)`;
  `core/canonical`: `pushforward₀ (Opens.map f) 𝒪`;
  `bridge/view`: the identification of the target ring presheaf with
  `((pushforward RingCat f).obj 𝒪)`.

Primitive data are only the continuous map `f` and the ring presheaf `𝒪` on `X`. The direct-image
functor itself is already the canonical owner `pushforward₀`, so this item should recall that
owner directly rather than keep any parallel local alias.
-/

/- Lemma 6.24.1 (Tag 008S): for a continuous map `f : X ⟶ Y` and a presheaf of rings `𝒪` on
`X`, direct image on opens induces the canonical functor
`f_* : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f_* \mathcal O)`.
In mathlib this is exactly `pushforward₀`, specialized to the map of opens `Opens.map f`. -/
#check (pushforward₀ (Opens.map f) 𝒪 :
  PresheafOfModules 𝒪 ⥤ PresheafOfModules ((pushforward RingCat f).obj 𝒪))

end

/-! ### Lemma_6_24_2 (from Chap06) -/
open CategoryTheory TopCat TopCat.Presheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Presheaf RingCat.{u})

/- Domain-style sampling for Lemma 6.24.2:
- primary domain: inverse image for presheaves of modules along a continuous map, obtained by
  change of rings along the unit of the presheaf pullback-pushforward adjunction;
- sampled owner API:
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pullbackPushforwardAdjunction`;
- source/core/bridge triage:
  `source-facing`: the inverse-image functor on presheaves of modules for a continuous map
  `f : X ⟶ Y`;
  `core/canonical`: `PresheafOfModules.pullback` applied to the unit
  `((pullbackPushforwardAdjunction RingCat f).unit.app 𝒪)`;
  `bridge/view`: the identification of the target ring presheaf with
  `((pullback RingCat f).obj 𝒪)`.

Primitive data are only the continuous map `f` and the ring presheaf `𝒪`. The module pullback
functor itself is already the canonical owner `PresheafOfModules.pullback`; the adjunction unit
and the pulled-back ring presheaf are derived from the presheaf pullback owner, so this file
should recall that owner directly rather than keep a parallel local abbreviation.
-/

/- Lemma 6.24.2 (Tag 008T): for a continuous map `f : X ⟶ Y` and a presheaf of rings `𝒪` on
`Y`, inverse image on opens induces the canonical functor on presheaves of modules
`f_p : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f^{-1}\mathcal O)`.
In mathlib this is exactly `PresheafOfModules.pullback`, specialized to the unit of
`pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullback

#check
  (PresheafOfModules.pullback ((pullbackPushforwardAdjunction RingCat f).unit.app 𝒪) :
    PresheafOfModules 𝒪 ⥤ PresheafOfModules ((pullback RingCat f).obj 𝒪))

end

/-! ### Lemma_6_24_3 (from Chap06) -/
open CategoryTheory TopCat TopCat.Presheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Presheaf RingCat.{u})
variable (𝒢 : PMod(𝒪))
variable (ℱ : PMod((pullback RingCat f).obj 𝒪))

private abbrev continuousMapUnit :
    𝒪 ⟶ (pushforward RingCat f).obj ((pullback RingCat f).obj 𝒪) :=
  (pullbackPushforwardAdjunction RingCat f).unit.app 𝒪

/- Domain-style sampling for Lemma 6.24.3:
- primary domain: the pullback-pushforward adjunction for presheaves of modules along a morphism of
  presheaves of rings arising from a continuous map;
- sampled owner API:
  `PMod`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pushforward`,
  `PresheafOfModules.pullbackPushforwardAdjunction`;
- source/core/bridge triage:
  `source-facing`: the canonical bijection
  `Mor_{PMod(f⁻¹𝒪)}(f⁻¹𝒢, ℱ) ≃ Mor_{PMod(𝒪)}(𝒢, f_* ℱ)`;
  `core/canonical`: the hom-equivalence of
  `PresheafOfModules.pullbackPushforwardAdjunction` specialized to the unit
  `continuousMapUnit f 𝒪`;
  `bridge/view`: the existing chapter notation `PMod(𝒪)` from Definition `6.6.1`, together with
  the identification of the target ring presheaf with `((pullback RingCat f).obj 𝒪)`.

Primitive data are only `f`, `𝒪`, `𝒢`, and `ℱ`. The bijection itself is derived API from the
canonical owner adjunction, so this item should use that owner directly rather than keep a
parallel local abbreviation. On the source-facing theorem surface, the module categories should be
written through the existing `PMod` notation rather than repeated raw owner names.
-/

/- Lemma 6.24.3: for a continuous map `f : X ⟶ Y`, a presheaf of rings `𝒪` on `Y`, a presheaf
of `𝒪`-modules `𝒢`, and a presheaf of `f_p 𝒪`-modules `ℱ`, the required canonical bijection is
exactly the hom-equivalence of `PresheafOfModules.pullbackPushforwardAdjunction`, specialized to
the unit of `TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

#check
  ((PresheafOfModules.pullbackPushforwardAdjunction
      (continuousMapUnit f 𝒪)).homEquiv 𝒢 ℱ :
    ((PresheafOfModules.pullback (continuousMapUnit f 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (PresheafOfModules.pushforward (continuousMapUnit f 𝒪)).obj ℱ))

end

/-! ### Lemma_6_24_4 (from Chap06) -/
open CategoryTheory TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf RingCat.{u})

private abbrev ringPresheafHomOverId
    {Z : TopCat.{u}} {𝒪₁ 𝒪₂ : Z.Presheaf RingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    𝒪₁ ⟶ (𝟭 (Opens Z)).op ⋙ 𝒪₂ :=
  p ≫ 𝒪₂.leftUnitor.inv

/- Domain-style sampling for Lemma 6.24.4:
- primary domain: pullback/pushforward of presheaves of modules along a continuous map, together
  with same-site change of rings along the counit `f_p f_* 𝒪 ⟶ 𝒪`;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pushforwardComp`,
  `TopCat.Presheaf.Lemma_6_6_2`'s identity-on-opens transport `ringPresheafHomOverId`;
- best owner abstraction: the source-facing tensor-pullback functor
  `𝒪 ⊗_{c_𝒪} f_p (-)`, presented canonically as the composite of the two owner pullback functors
  induced by the unit and counit of `TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`;
- primitive data: the continuous map `f`, the ring presheaf `𝒪`, and the canonical unit/counit
  maps derived from the presheaf pullback-pushforward adjunction;
- derived API: the composite tensor functor and its Hom-set equivalence.

Source/core/bridge triage:
- `source-facing`: the tensor-by-counit functor
  `𝒪 ⊗_{c_𝒪} f_p (-) : PMod(f_*𝒪) ⥤ PMod(𝒪)` and the induced bijection
  `Mor_{PMod(𝒪)}(𝒪 ⊗_{c_𝒪} f_p 𝒢, ℱ) ≃ Mor_{PMod(f_*𝒪)}(𝒢, f_*ℱ)`;
- `core/canonical`: `PresheafOfModules.pullbackPushforwardAdjunction` for the unit and counit
  ring maps, together with `PresheafOfModules.pushforwardComp`;
- `bridge/view`: the identity-on-opens transport `ringPresheafHomOverId` for the counit and the
  right triangle identity identifying the composite right adjoint with pushforward along
  `𝟙 (f_*𝒪)`.

Primitive-vs-derived decision:
- the source tensor construction should stay public;
- the owner pullback/pushforward functors and their adjunctions remain derived from the canonical
  mathlib/project API, so there is no need for a parallel wrapper around the owner adjunction;
- the triangle identity is used only on the right-adjoint side, matching the textbook semantics
  and the sheaf analogue `Lemma_6_24_8`.
-/

/- Lemma 6.24.4, owner ingredients: the relevant adjunctions are the canonical
`PresheafOfModules.pullbackPushforwardAdjunction` instances for the unit and counit ring maps, and
the comparison of the composite right adjoint with the identity-ring pushforward comes from
`PresheafOfModules.pushforwardComp` together with the right triangle identity for
`TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction
recall PresheafOfModules.pushforwardComp

/-- The extension-of-scalars functor corresponding to `𝒪 ⊗_{c_𝒪} f_p (-)`. -/
noncomputable def continuous_map_presheaf_module_tensor_functor :
    PMod((pushforward RingCat f).obj 𝒪) ⥤ PMod(𝒪) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  PresheafOfModules.pullback η ⋙ PresheafOfModules.pullback ε

-- Proof sketch: `PresheafOfModules.pushforwardComp` identifies the composite right adjoint
-- `pushforward ε_𝒪 ⋙ pushforward η_{f_* 𝒪}` with pushforward along
-- `η_{f_* 𝒪} ≫ f_*(ε_𝒪)`, and the latter is `𝟙_{f_* 𝒪}` by the right triangle identity for
-- `pullbackPushforwardAdjunction RingCat f`.
/-- The composite right adjoint for the counit and unit ring maps is canonically the ordinary
pushforward along the identity of `f_* 𝒪`. -/
private noncomputable def continuous_map_presheaf_module_pushforwardCompIso :
    let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
    let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
    PresheafOfModules.pushforward ε ⋙ PresheafOfModules.pushforward η ≅
      PresheafOfModules.pushforward (𝟙 ((pushforward RingCat f).obj 𝒪)) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  let hηε : η ≫ (Opens.map f).op.whiskerLeft ε = 𝟙 ((pushforward RingCat f).obj 𝒪) := by
    convert (pullbackPushforwardAdjunction RingCat f).right_triangle_components 𝒪 using 1
  PresheafOfModules.pushforwardComp η ε ≪≫
    eqToIso (congrArg PresheafOfModules.pushforward hηε)

/-- Lemma 6.24.4: the tensor-pullback object `𝒪 ⊗_{c_𝒪} f_p 𝒢` represents morphisms into `ℱ`
exactly as morphisms from `𝒢` into the direct image `f_* ℱ`. -/
noncomputable def continuous_map_presheaf_module_tensor_hom_equiv
    (𝒢 : PMod((pushforward RingCat f).obj 𝒪)) (ℱ : PMod(𝒪)) :
    ((continuous_map_presheaf_module_tensor_functor f 𝒪).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (PresheafOfModules.pushforward (𝟙 ((pushforward RingCat f).obj 𝒪))).obj ℱ) :=
  let η := (pullbackPushforwardAdjunction RingCat f).unit.app ((pushforward RingCat f).obj 𝒪)
  let ε := ringPresheafHomOverId ((pullbackPushforwardAdjunction RingCat f).counit.app 𝒪)
  ((PresheafOfModules.pullbackPushforwardAdjunction ε).homEquiv
      ((PresheafOfModules.pullback η).obj 𝒢) ℱ).trans
    (((PresheafOfModules.pullbackPushforwardAdjunction η).homEquiv 𝒢
        ((PresheafOfModules.pushforward ε).obj ℱ)).trans
      ((Iso.refl 𝒢).homCongr
        ((continuous_map_presheaf_module_pushforwardCompIso f 𝒪).app ℱ)))

-- Proof sketch: `continuous_map_presheaf_module_tensor_hom_equiv` is an equivalence of hom-sets,
-- so its underlying function is bijective.
/-- The morphism correspondence of `continuous_map_presheaf_module_tensor_hom_equiv` is bijective.
-/
theorem continuous_map_presheaf_module_tensor_hom_equiv_bijective
    (𝒢 : PMod((pushforward RingCat f).obj 𝒪)) (ℱ : PMod(𝒪)) :
    Function.Bijective (continuous_map_presheaf_module_tensor_hom_equiv f 𝒪 𝒢 ℱ) :=
  (continuous_map_presheaf_module_tensor_hom_equiv f 𝒪 𝒢 ℱ).bijective

end

/-! ### Lemma_6_24_5 (from Chap06) -/
open CategoryTheory TopCat

universe w v u

/- Domain-style sampling for Lemma 6.24.5:
- primary domain: direct image of sheaves of modules along a continuous map of topological spaces;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardId`,
  `TopCat.Sheaf.pushforward`,
  `PresheafOfModules.pushforward`;
- owner abstraction: the canonical owner is `SheafOfModules.pushforward`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `X`, and a sheaf of
  `𝒪`-modules `ℱ`;
- derived API: the specialized object `f_* ℱ` over the direct-image ring sheaf `f_* 𝒪`.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that direct image carries an `𝒪`-module sheaf on `X`
  to an `f_* 𝒪`-module sheaf on `Y`;
- `core/canonical`: `SheafOfModules.pushforward`;
- `bridge/view`: the identity-morphism specialization over the direct-image ring sheaf
  `(Sheaf.pushforward RingCat f).obj 𝒪`.

This item is only the object-level specialization of the canonical owner, so the refined file
should keep a direct `#check` of that specialization rather than introduce a local alias. -/

section

variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} X)
variable (ℱ : SheafOfModules.{v} 𝒪)

/- Lemma 6.24.5: for a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `X`, and a sheaf
of `𝒪`-modules `ℱ`, the direct image `f_* ℱ` is canonically a sheaf of modules over the direct
image ring sheaf `f_* 𝒪`. In mathlib this is the specialization of
`SheafOfModules.pushforward` to the identity morphism on `(Sheaf.pushforward RingCat f).obj 𝒪`. -/
recall SheafOfModules.pushforward

#check (SheafOfModules.pushforward (𝟙 ((Sheaf.pushforward RingCat f).obj 𝒪))).obj ℱ

end

/-! ### Lemma_6_24_6 (from Chap06) -/
open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : TopCat.Sheaf RingCat.{u} Y)

/- Domain-style sampling for Lemma 6.24.6:
- primary domain: pullback and pushforward of sheaves of modules along a continuous map of
  topological spaces;
- sampled owner declarations:
  `Mod(𝒪)`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Definition_18_13_1`'s direct recall of `SheafOfModules.pullback`;
- best owner abstraction: the inverse-image functor
  `SheafOfModules.pullback ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- primitive data: the continuous map `f` and the sheaf of rings `𝒪`;
- derived API: the specialized functor
  `Mod(𝒪) ⥤ Mod((pullback RingCat.{u} f).obj 𝒪)`.

Source/core/bridge triage:
- `source-facing`: the inverse-image functor `f^{-1} : Mod(𝒪) ⥤ Mod(f^{-1}𝒪)` attached to a
  continuous map;
- `core/canonical`: `SheafOfModules.pullback`;
- `bridge/view`: the specialization along the unit of
  `pullbackPushforwardAdjunction RingCat.{u} f`, together with the chapter notation `Mod(𝒪)` from
  Definition `6.10.1`.
-/

/- Lemma 6.24.6: for a continuous map `f : X ⟶ Y` and a sheaf of rings `𝒪` on `Y`, inverse image
defines the canonical functor on sheaves of modules
`f^{-1} : \operatorname{Mod}(\mathcal O) \to \operatorname{Mod}(f^{-1}\mathcal O)`. In mathlib
this is exactly `SheafOfModules.pullback`, specialized to the unit
`𝒪 ⟶ f_* f^{-1} 𝒪` of `f^{-1} ⊣ f_*`. -/
recall SheafOfModules.pullback

#check
  (SheafOfModules.pullback
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪) :
    Mod(𝒪) ⥤ Mod((pullback RingCat.{u} f).obj 𝒪))

end

/-! ### Lemma_6_24_7 (from Chap06) -/
open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} Y)
variable (𝒢 : SheafOfModules 𝒪)
variable (ℱ : SheafOfModules ((pullback RingCat.{u} f).obj 𝒪))

/- Domain-style sampling for Lemma 6.24.7:
- primary domain: the pullback-pushforward adjunction for sheaves of modules along a continuous
  map;
- sampled owner declarations:
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the recall/check surface in `Lemma_18_12_3` and `Lemma_18_13_2` for the same owner abstraction;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- primitive data: the continuous map `f`, the sheaf of rings `𝒪`, and the module sheaves `𝒢`,
  `ℱ`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its canonical bijectivity
  theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the canonical bijection
  `Mor_{Mod(f^{-1}𝒪)}(f^{-1}𝒢, ℱ) ≃ Mor_{Mod(𝒪)}(𝒢, f_*ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- `bridge/view`: the specialization of `.homEquiv` to `𝒢` and `ℱ`.

This file should therefore recall the owner adjunction directly and reuse its derived API via
`.homEquiv` and `.bijective`, with no parallel local abbreviation for the unit map and no exact-
interface wrapper theorem for bijectivity.
-/

/- Lemma 6.24.7, owner form: for the unit map `𝒪 ⟶ f_* f^{-1} 𝒪` induced by `f`, the
inverse-image functor on sheaves of `𝒪`-modules is left adjoint to the direct-image functor on
sheaves of `f^{-1}𝒪`-modules. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.24.7: for a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `Y`, a sheaf of
`𝒪`-modules `𝒢`, and a sheaf of `f^{-1} 𝒪`-modules `ℱ`, morphisms
`f^{-1} 𝒢 ⟶ ℱ` of `f^{-1} 𝒪`-modules are canonically equivalent to morphisms
`𝒢 ⟶ f_* ℱ` of `𝒪`-modules, where `f_* ℱ` is viewed as an `𝒪`-module via
`𝒪 ⟶ f_* f^{-1} 𝒪`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).obj ℱ))

/- Lemma 6.24.7 companion: the source bijection statement is exactly the canonical bijectivity
theorem for the specialized adjunction equivalence. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ))

end

/-! ### Lemma_6_24_8 (from Chap06) -/
open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} X)
variable (𝒢 : SheafOfModules ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))
variable (ℱ : SheafOfModules 𝒪)

/- Domain-style sampling for Lemma 6.24.8:
- primary domain: pullback-pushforward adjunction for sheaves of modules along a continuous map,
  specialized to the direct-image ring sheaf `f_* 𝒪`;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Lemma_6_24_7`'s direct use of the same adjunction owner;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`;
- primitive data: the continuous map `f`, the sheaf of rings `𝒪`, and module sheaves
  `𝒢 : Mod(f_* 𝒪)` and `ℱ : Mod(𝒪)`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its canonical bijectivity
  theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the tensor-pullback/direct-image correspondence
  `Hom_𝒪(𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢, ℱ) ≃ Hom_{f_* 𝒪}(𝒢, f_* ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`;
- `bridge/view`: the source tensor-pullback notation is exactly the pullback functor
  `SheafOfModules.pullback (𝟙 ((Sheaf.pushforward RingCat.{u} f).obj 𝒪))`, so this item should
  reuse the canonical adjunction owner directly instead of rebuilding it from same-site
  change-of-rings and unit/counit helpers.
-/

private abbrev pushforwardRingSheaf : TopCat.Sheaf RingCat.{u} Y :=
  (Sheaf.pushforward RingCat.{u} f).obj 𝒪

/- Lemma 6.24.8, owner form: for the identity morphism `f_* 𝒪 ⟶ f_* 𝒪`, the canonical
pullback functor
`SheafOfModules.pullback (𝟙 (f_* 𝒪)) : Mod(f_* 𝒪) ⥤ Mod(𝒪)`
is left adjoint to the direct-image functor
`SheafOfModules.pushforward (𝟙 (f_* 𝒪)) : Mod(𝒪) ⥤ Mod(f_* 𝒪)`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.24.8: the tensor-pullback object
`𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢`,
which is the canonical pullback object
`(SheafOfModules.pullback (𝟙 (f_* 𝒪))).obj 𝒢`,
represents morphisms into `ℱ` exactly as morphisms from `𝒢` into the direct image `f_* ℱ`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback (𝟙 (pushforwardRingSheaf f 𝒪))).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward (𝟙 (pushforwardRingSheaf f 𝒪))).obj ℱ))

/- Lemma 6.24.8 companion: the source bijection statement is exactly the canonical bijectivity
theorem for this specialized adjunction equivalence. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (pushforwardRingSheaf f 𝒪))).homEquiv 𝒢 ℱ))

end
