import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic

open CategoryTheory Limits CommRingCat
open IsLocalization.Away

universe u

namespace CategoryTheory
namespace IsPullback

section

variable {R R' B B' Bg Rf Bh Rh : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable [CommRing Bg] [CommRing Rf] [CommRing Bh] [CommRing Rh]
variable {s : B →+* R} {t : R' →+* R} {left : B' →+* B} {right : B' →+* R'}
variable (h : B')
variable [Algebra B Bg] [IsLocalization.Away (left h) Bg]
variable [Algebra R' Rf] [IsLocalization.Away (right h) Rf]
variable [Algebra B' Bh] [IsLocalization.Away h Bh]
variable [Algebra R Rh] [IsLocalization.Away (s (left h)) Rh]

/- Domain-style sampling for Lemma 15.5.3:
- primary domain: pullback squares in `CommRingCat` together with localization-away base change;
- sampled owner API:
  `CategoryTheory.IsPullback`,
  `CategoryTheory.Under.pushout`,
  `CommRingCat.Under.preservesFiniteLimits_of_flat`,
  `CommRingCat.isPushout_of_isLocalization`;
- best owner abstraction: base change in the under-category via
  `CategoryTheory.Under.pushout`, with the public statement still phrased by the source-facing
  owner `CategoryTheory.IsPullback`;
- primitive-vs-derived split:
  primitive data: the original pullback witness
    `IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)`
    together with the localization-away instances at `h`, `left h`, `right h`, and the common
    image of `h` in `R`;
  derived API: the four localized comparison maps
    `IsLocalization.Away.map ...`, where the `R'_right(h) → R_common` map uses the pullback
    commutativity to identify `t (right h)` with `s (left h)`, obtained by base change along
    `ofHom (algebraMap B' Bh)`, and the resulting localized pullback square.

This item is therefore a `bridge/view` theorem: the canonical engine is that pushout along the
localization map `B' ⟶ B'_h` preserves finite limits because localizations are flat, while
`CommRingCat.isPushout_of_isLocalization` identifies the pushed-out objects with the usual
away-localizations. The source-facing output remains the localized `IsPullback` square. -/

/- Source/core/bridge triage for Lemma 15.5.3:
- source-facing: localizing a cartesian square of commutative rings away from an element of the
  pullback ring;
- core/canonical: `CategoryTheory.IsPullback` together with base change by
  `CategoryTheory.Under.pushout`;
- bridge/view: the localized square built from the canonical localization maps
  `IsLocalization.Away.map`, with the target-side `R'_right(h) → R_common` map derived from the
  pullback commutativity. -/

lemma away_right_of_localization_away (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s)
    (ofHom t)) : IsLocalization.Away (t (right h)) Rh := by
  -- Evaluate the pullback commutativity relation on `h` to identify the two distinguished
  -- denominators in `R`.
  have hcomm : s (left h) = t (right h) := by
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) h)
  -- Transport the existing away-localization structure on `R` across this equality.
  simpa [hcomm] using (inferInstance : IsLocalization.Away (s (left h)) Rh)

/-- The canonical localized comparison map `R'[1 / right(h)] → R[1 / s(left(h))]` induced by the
pullback square. -/
noncomputable def localizationAwayRightMap
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    Rf →+* Rh :=
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  IsLocalization.Away.map Rf Rh t (right h)

/-- Helper for Lemma 15.5.3: the original pullback square of rings is the corresponding pullback
square in the under-category of `B'`. -/
lemma under_pullback_of_ring_pullback
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    let U₀ : Under (of B') := Under.mk (𝟙 (of B'))
    let U₁ : Under (of B') := Under.mk (ofHom left)
    let U₂ : Under (of B') := Under.mk (ofHom right)
    let U₃ : Under (of B') := Under.mk (ofHom (s.comp left))
    let f : U₀ ⟶ U₁ := Under.homMk (ofHom left) (by
      dsimp
      rfl)
    let g : U₀ ⟶ U₂ := Under.homMk (ofHom right) (by
      dsimp
      rfl)
    let p : U₁ ⟶ U₃ := Under.homMk (ofHom s) (by
      dsimp
      rfl)
    let q : U₂ ⟶ U₃ := Under.homMk (ofHom t) (by
      dsimp
      simpa [CommRingCat.hom_comp] using hsq.w.symm)
    IsPullback f g p q := by
  dsimp
  -- Reflect the pullback through the forgetful functor from `Under (of B')`.
  refine IsPullback.of_map (CategoryTheory.Under.forget (of B')) ?_ ?_
  · -- The square commutes in the under-category because it already commutes in rings.
    ext x
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) x)
  · -- Forgetting the under-structure recovers the original pullback square.
    simpa using hsq

/-- Helper for Lemma 15.5.3: pushing a `B'`-algebra forward along `B' → B'_h` identifies its
pushout object with the away-localization at the image of `h`. -/
noncomputable def pushout_obj_iso_away
    {X Xh : Type u} [CommRing X] [CommRing Xh]
    (u : B' →+* X)
    [Algebra X Xh] [IsLocalization.Away (u h) Xh] :
    ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom u))) ≅
      Under.mk (ofHom (IsLocalization.Away.map Bh Xh u h)) := by
  -- Rewrite the pushed-out object as the categorical pushout under-object.
  rw [Under.pushout_obj]
  let hpush :
      IsPushout (ofHom u) (ofHom (algebraMap B' Bh))
        (ofHom (algebraMap X Xh)) (ofHom (IsLocalization.Away.map Bh Xh u h)) :=
    CommRingCat.isPushout_of_isLocalization u (IsLocalization.Away.map Bh Xh u h)
      (by
        ext x
        simp [IsLocalization.Away.map])
      (Submonoid.powers h)
  -- The universal pushout is canonically isomorphic to the away-localization.
  refine Under.isoMk hpush.isoPushout.symm ?_
  simp

/-- Helper for Lemma 15.5.3: localizing away and mapping along the identity map gives the identity
endomorphism of the localization. -/
lemma away_map_id {A Ah : Type u} [CommRing A] [CommRing Ah] (a : A)
    [Algebra A Ah] [IsLocalization.Away a Ah] [IsLocalization.Away ((RingHom.id A) a) Ah] :
    IsLocalization.Away.map Ah Ah (RingHom.id A) a = RingHom.id Ah := by
  -- Compare the two endomorphisms after precomposing with the localization map from `A`.
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext x
  simp [IsLocalization.Away.map]

/-- Helper for Lemma 15.5.3: after identifying the pushout with the away-localization, the left
pushout generator becomes the localization map from the left input ring. -/
@[reassoc (attr := simp)]
lemma pushout_inl_pushout_obj_iso_away_hom
    {X Xh : Type u} [CommRing X] [CommRing Xh]
    (u : B' →+* X)
    [Algebra X Xh] [IsLocalization.Away (u h) Xh] :
    pushout.inl (ofHom u) (ofHom (algebraMap B' Bh)) ≫
      ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := X) (Xh := Xh) (u := u)).hom).right =
        ofHom (algebraMap X Xh) := by
  let hpush :
      IsPushout (ofHom u) (ofHom (algebraMap B' Bh))
        (ofHom (algebraMap X Xh)) (ofHom (IsLocalization.Away.map Bh Xh u h)) :=
    CommRingCat.isPushout_of_isLocalization u (IsLocalization.Away.map Bh Xh u h)
      (by
        ext x
        simp [IsLocalization.Away.map])
      (Submonoid.powers h)
  -- The comparison isomorphism is induced by the universal pushout comparison `hpush`.
  simpa [pushout_obj_iso_away, hpush] using hpush.inl_isoPushout_inv

/-- Helper for Lemma 15.5.3: after identifying the pushout with the away-localization, the right
pushout generator becomes the canonical away-localization map. -/
@[reassoc (attr := simp)]
lemma pushout_inr_pushout_obj_iso_away_hom
    {X Xh : Type u} [CommRing X] [CommRing Xh]
    (u : B' →+* X)
    [Algebra X Xh] [IsLocalization.Away (u h) Xh] :
    pushout.inr (ofHom u) (ofHom (algebraMap B' Bh)) ≫
      ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := X) (Xh := Xh) (u := u)).hom).right =
        ofHom (IsLocalization.Away.map Bh Xh u h) := by
  let hpush :
      IsPushout (ofHom u) (ofHom (algebraMap B' Bh))
        (ofHom (algebraMap X Xh)) (ofHom (IsLocalization.Away.map Bh Xh u h)) :=
    CommRingCat.isPushout_of_isLocalization u (IsLocalization.Away.map Bh Xh u h)
      (by
        ext x
        simp [IsLocalization.Away.map])
      (Submonoid.powers h)
  -- The comparison isomorphism is induced by the universal pushout comparison `hpush`.
  simpa [pushout_obj_iso_away, hpush] using hpush.inr_isoPushout_inv

/-- Helper for Lemma 15.5.3: transporting a pushed-out morphism in the under-category agrees with
the canonical map between the corresponding away-localizations. -/
lemma pushout_map_eq_away_map
    {X Xh Y Yh : Type u} [CommRing X] [CommRing Xh] [CommRing Y] [CommRing Yh]
    (u : B' →+* X) (v : X →+* Y)
    [Algebra X Xh] [IsLocalization.Away (u h) Xh]
    [Algebra Y Yh] [IsLocalization.Away (v (u h)) Yh] [IsLocalization.Away ((v.comp u) h) Yh] :
    let eu : (Under.forget (of Bh)).obj
        ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom u))) ≅ of Xh :=
      (Under.forget (of Bh)).mapIso
        (pushout_obj_iso_away (h := h) (Bh := Bh) (X := X) (Xh := Xh) (u := u))
    let evu : (Under.forget (of Bh)).obj
        ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom (v.comp u)))) ≅ of Yh :=
      (Under.forget (of Bh)).mapIso
        (show ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom (v.comp u)))) ≅
            Under.mk (ofHom (IsLocalization.Away.map Bh Yh (v.comp u) h)) from
          by
            simpa using
              (pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh) (u := v.comp u)))
    (Under.forget (of Bh)).map
        ((Under.pushout (ofHom (algebraMap B' Bh))).map
          (Under.homMk (ofHom v) (by
            dsimp
            rfl))) ≫ evu.hom =
      eu.hom ≫ ofHom (IsLocalization.Away.map Xh Yh v (u h)) := by
  -- Compare the transported morphisms on the two pushout generators.
  dsimp
  apply pushout.hom_ext
  · have hdesc :
        pushout.inl (ofHom u) (ofHom (algebraMap B' Bh)) ≫
            pushout.desc
              (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
              (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
              (by
                simpa [Category.assoc] using
                  (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh)))) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
              (u := v.comp u)).hom).right =
          ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
              (u := v.comp u)).hom).right := by
      simpa using
        (pushout.inl_desc_assoc
          (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
          (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
          (by
            simpa [Category.assoc] using
              (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh))))
          (((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
            (u := v.comp u)).hom).right))
    calc
      pushout.inl (ofHom u) (ofHom (algebraMap B' Bh)) ≫
          pushout.desc
            (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
            (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
            (by
              simpa [Category.assoc] using
                (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh)))) ≫
          ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
            (u := v.comp u)).hom).right
          = ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)) ≫
              ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
                (u := v.comp u)).hom).right := hdesc
      _ = ofHom v ≫ ofHom (algebraMap Y Yh) := by
        exact congrArg (fun k => ofHom v ≫ k) <| by
          simpa [CommRingCat.hom_comp] using
            (pushout_inl_pushout_obj_iso_away_hom (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
              (u := v.comp u))
      _ = pushout.inl (ofHom u) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := X) (Xh := Xh)
              (u := u)).hom).right ≫
            ofHom (IsLocalization.Away.map Xh Yh v (u h)) := by
        rw [pushout_inl_pushout_obj_iso_away_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        simp [IsLocalization.Away.map]
  · have hdesc :
        pushout.inr (ofHom u) (ofHom (algebraMap B' Bh)) ≫
            pushout.desc
              (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
              (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
              (by
                simpa [Category.assoc] using
                  (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh)))) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
              (u := v.comp u)).hom).right =
          pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
              (u := v.comp u)).hom).right := by
      simpa using
        (pushout.inr_desc_assoc
          (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
          (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
          (by
            simpa [Category.assoc] using
              (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh))))
          (((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
            (u := v.comp u)).hom).right))
    calc
      pushout.inr (ofHom u) (ofHom (algebraMap B' Bh)) ≫
          pushout.desc
            (ofHom v ≫ pushout.inl (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
            (pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)))
            (by
              simpa [Category.assoc] using
                (pushout.condition (f := ofHom u ≫ ofHom v) (g := ofHom (algebraMap B' Bh)))) ≫
          ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
            (u := v.comp u)).hom).right
          = pushout.inr (ofHom u ≫ ofHom v) (ofHom (algebraMap B' Bh)) ≫
              ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
                (u := v.comp u)).hom).right := hdesc
      _ = ofHom (IsLocalization.Away.map Bh Yh (v.comp u) h) := by
        simpa [CommRingCat.hom_comp] using
          (pushout_inr_pushout_obj_iso_away_hom (h := h) (Bh := Bh) (X := Y) (Xh := Yh)
            (u := v.comp u))
      _ = pushout.inr (ofHom u) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := X) (Xh := Xh)
              (u := u)).hom).right ≫
            ofHom (IsLocalization.Away.map Xh Yh v (u h)) := by
        rw [pushout_inr_pushout_obj_iso_away_hom_assoc]
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (Submonoid.powers h)
        ext x
        simp [IsLocalization.Away.map]


/-- Helper for Lemma 15.5.3: transporting the pushed-out right edge along the localization
comparison identifies it with the canonical localized map induced by `t`. -/
lemma pushout_right_edge_eq_localizationAwayRightMap
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
    letI : IsLocalization.Away ((s.comp left) h) Rh := by
      simpa using (inferInstance : IsLocalization.Away (s (left h)) Rh)
    let e3 : (Under.forget (of Bh)).obj
        ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom right))) ≅ of Rf :=
      (Under.forget (of Bh)).mapIso
        (pushout_obj_iso_away (h := h) (Bh := Bh) (X := R') (Xh := Rf) (u := right))
    let e4 : (Under.forget (of Bh)).obj
        ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom (s.comp left)))) ≅ of Rh :=
      (Under.forget (of Bh)).mapIso
        (show ((Under.pushout (ofHom (algebraMap B' Bh))).obj (Under.mk (ofHom (s.comp left)))) ≅
            Under.mk (ofHom (IsLocalization.Away.map Bh Rh (s.comp left) h)) from
          by
            simpa using
              (pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh) (u := s.comp left)))
    (Under.forget (of Bh)).map
        ((Under.pushout (ofHom (algebraMap B' Bh))).map
          (Under.homMk (ofHom t) (by
            dsimp
            simpa [CommRingCat.hom_comp] using hsq.w.symm))) ≫ e4.hom =
      e3.hom ≫ ofHom (localizationAwayRightMap h hsq) := by
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  letI : IsLocalization.Away ((s.comp left) h) Rh := by
    simpa using (inferInstance : IsLocalization.Away (s (left h)) Rh)
  have hsq_pushout :
      ofHom right ≫ ofHom t ≫
          pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) =
        ofHom (algebraMap B' Bh) ≫
          pushout.inr (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
    calc
      ofHom right ≫ ofHom t ≫
          pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) =
        ofHom left ≫ ofHom s ≫
          pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
          simpa [Category.assoc] using
            congrArg (fun k => k ≫
              pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh))) hsq.w.symm
      _ = ofHom (algebraMap B' Bh) ≫
          pushout.inr (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
          simpa using
            (pushout.condition (f := ofHom left ≫ ofHom s) (g := ofHom (algebraMap B' Bh)))
  -- Compare the transported morphisms on the two pushout generators.
  dsimp
  apply pushout.hom_ext
  · have hdesc :
        pushout.inl (ofHom right) (ofHom (algebraMap B' Bh)) ≫
            pushout.desc
              (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
              (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
              (by
                calc
                  ofHom right ≫ ofHom t ≫
                      pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) =
                    ofHom left ≫ ofHom s ≫
                      pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
                      simpa [Category.assoc] using
                        congrArg (fun k => k ≫
                          pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh))) hsq.w.symm
                  _ = ofHom (algebraMap B' Bh) ≫
                      pushout.inr (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
                      simpa using
                        (pushout.condition (f := ofHom left ≫ ofHom s) (g := ofHom (algebraMap B' Bh)))) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
              (u := s.comp left)).hom).right =
          ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
              (u := s.comp left)).hom).right := by
      simpa using
        (pushout.inl_desc_assoc
          (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
          (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
            (u := s.comp left)).hom).right))
    calc
      pushout.inl (ofHom right) (ofHom (algebraMap B' Bh)) ≫
          pushout.desc
            (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
            (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
            (u := s.comp left)).hom).right
          = ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)) ≫
              ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
                (u := s.comp left)).hom).right := hdesc
      _ = ofHom t ≫ ofHom (algebraMap R Rh) := by
        exact congrArg (fun k => ofHom t ≫ k) <| by
          simpa using
            (pushout_inl_pushout_obj_iso_away_hom (h := h) (Bh := Bh) (X := R) (Xh := Rh)
              (u := s.comp left))
      _ = pushout.inl (ofHom right) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R') (Xh := Rf)
              (u := right)).hom).right ≫
            ofHom (localizationAwayRightMap h hsq) := by
        rw [pushout_inl_pushout_obj_iso_away_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        simp [localizationAwayRightMap, IsLocalization.Away.map]
  · have hdesc :
        pushout.inr (ofHom right) (ofHom (algebraMap B' Bh)) ≫
            pushout.desc
              (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
              (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
              (by
                calc
                  ofHom right ≫ ofHom t ≫
                      pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) =
                    ofHom left ≫ ofHom s ≫
                      pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
                      simpa [Category.assoc] using
                        congrArg (fun k => k ≫
                          pushout.inl (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh))) hsq.w.symm
                  _ = ofHom (algebraMap B' Bh) ≫
                      pushout.inr (ofHom left ≫ ofHom s) (ofHom (algebraMap B' Bh)) := by
                      simpa using
                        (pushout.condition (f := ofHom left ≫ ofHom s) (g := ofHom (algebraMap B' Bh)))) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
              (u := s.comp left)).hom).right =
          pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
              (u := s.comp left)).hom).right := by
      simpa using
        (pushout.inr_desc_assoc
          (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
          (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
            (u := s.comp left)).hom).right))
    calc
      pushout.inr (ofHom right) (ofHom (algebraMap B' Bh)) ≫
          pushout.desc
            (ofHom t ≫ pushout.inl (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
            (pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
            (u := s.comp left)).hom).right
          = pushout.inr (ofHom (s.comp left)) (ofHom (algebraMap B' Bh)) ≫
              ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh)
                (u := s.comp left)).hom).right := hdesc
      _ = ofHom (IsLocalization.Away.map Bh Rh (s.comp left) h) := by
        simpa using
          (pushout_inr_pushout_obj_iso_away_hom (h := h) (Bh := Bh) (X := R) (Xh := Rh)
            (u := s.comp left))
      _ = pushout.inr (ofHom right) (ofHom (algebraMap B' Bh)) ≫
            ((pushout_obj_iso_away (h := h) (Bh := Bh) (X := R') (Xh := Rf)
              (u := right)).hom).right ≫
            ofHom (localizationAwayRightMap h hsq) := by
        rw [pushout_inr_pushout_obj_iso_away_hom_assoc]
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (Submonoid.powers h)
        ext x
        simpa [localizationAwayRightMap, IsLocalization.Away.map, CommRingCat.hom_comp,
          RingHom.comp_apply] using congrArg (fun y => (algebraMap R Rh) y) (congr(($hsq.w) x))

/-- Lemma 15.5.3: localizing a cartesian square of commutative rings away from an element of the
pullback ring again gives a cartesian square. -/
-- Proof sketch: start from the owner witness `hsq : IsPullback ...`. The localized comparison maps
-- are the canonical maps between away-localizations, with the target-side map packaged as the
-- explicit bridge `localizationAwayRightMap h hsq`. Regard the square as a pullback in
-- `Under (CommRingCat.of B')`, apply base change along `ofHom (algebraMap B' Bh)`, and use
-- `CommRingCat.Under.preservesFiniteLimits_of_flat` for the flat localization map. Finally
-- identify the pushed-out objects with the away-localizations via
-- `CommRingCat.isPushout_of_isLocalization`.
theorem localization_away
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    IsPullback (ofHom (IsLocalization.Away.map Bh Bg left h))
      (ofHom (IsLocalization.Away.map Bh Rf right h))
      (ofHom (IsLocalization.Away.map Bg Rh s (left h)))
      (ofHom (localizationAwayRightMap h hsq)) := by
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  let base : of B' ⟶ of Bh := ofHom (algebraMap B' Bh)
  let baseChange : Under (of B') ⥤ Under (of Bh) :=
    Under.pushout base
  have hflat : RingHom.Flat (algebraMap B' Bh) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat Bh (Submonoid.powers h)
  let _ : PreservesFiniteLimits baseChange :=
    CommRingCat.Under.preservesFiniteLimits_of_flat base hflat
  let U₀ : Under (of B') := Under.mk (𝟙 (of B'))
  let U₁ : Under (of B') := Under.mk (ofHom left)
  let U₂ : Under (of B') := Under.mk (ofHom right)
  let U₃ : Under (of B') := Under.mk (ofHom (s.comp left))
  let f : U₀ ⟶ U₁ := Under.homMk (ofHom left) (by
    dsimp [U₀, U₁]
    rfl)
  let g : U₀ ⟶ U₂ := Under.homMk (ofHom right) (by
    dsimp [U₀, U₂]
    rfl)
  let p : U₁ ⟶ U₃ := Under.homMk (ofHom s) (by
    dsimp [U₁, U₃])
  let q : U₂ ⟶ U₃ := Under.homMk (ofHom t) (by
    dsimp [U₂, U₃]
    simpa [CommRingCat.hom_comp] using hsq.w.symm)
  have hunder :
      IsPullback f g p q := by
    simpa [U₀, U₁, U₂, U₃, f, g, p, q] using
      (under_pullback_of_ring_pullback hsq)
  have hbase :
      IsPullback
        (baseChange.map f)
        (baseChange.map g)
        (baseChange.map p)
        (baseChange.map q) :=
    IsPullback.map baseChange hunder
  have hforget :
      IsPullback
        ((CategoryTheory.Under.forget (of Bh)).map (baseChange.map f))
        ((CategoryTheory.Under.forget (of Bh)).map (baseChange.map g))
        ((CategoryTheory.Under.forget (of Bh)).map (baseChange.map p))
        ((CategoryTheory.Under.forget (of Bh)).map (baseChange.map q)) :=
    IsPullback.map (CategoryTheory.Under.forget (of Bh)) hbase
  letI : IsLocalization.Away ((RingHom.id B') h) Bh := by
    simpa using (inferInstance : IsLocalization.Away h Bh)
  let e1 : (Under.forget (of Bh)).obj (baseChange.obj U₀) ≅ of Bh :=
    (Under.forget (of Bh)).mapIso
      (pushout_obj_iso_away (h := h) (Bh := Bh) (X := B') (Xh := Bh) (u := RingHom.id B'))
  let e2 : (Under.forget (of Bh)).obj (baseChange.obj U₁) ≅ of Bg :=
    (Under.forget (of Bh)).mapIso
      (pushout_obj_iso_away (h := h) (Bh := Bh) (X := B) (Xh := Bg) (u := left))
  let e3 : (Under.forget (of Bh)).obj (baseChange.obj U₂) ≅ of Rf :=
    (Under.forget (of Bh)).mapIso
      (pushout_obj_iso_away (h := h) (Bh := Bh) (X := R') (Xh := Rf) (u := right))
  letI : IsLocalization.Away (left ((RingHom.id B') h)) Bg := by
    simpa using (inferInstance : IsLocalization.Away (left h) Bg)
  letI : IsLocalization.Away ((left.comp (RingHom.id B')) h) Bg := by
    simpa using (inferInstance : IsLocalization.Away (left h) Bg)
  letI : IsLocalization.Away (right ((RingHom.id B') h)) Rf := by
    simpa using (inferInstance : IsLocalization.Away (right h) Rf)
  letI : IsLocalization.Away ((right.comp (RingHom.id B')) h) Rf := by
    simpa using (inferInstance : IsLocalization.Away (right h) Rf)
  letI : IsLocalization.Away ((s.comp left) h) Rh := by
    simpa using (inferInstance : IsLocalization.Away (s (left h)) Rh)
  let e4 : (Under.forget (of Bh)).obj (baseChange.obj U₃) ≅ of Rh :=
    (Under.forget (of Bh)).mapIso
      (show ((Under.pushout (ofHom (algebraMap B' Bh))).obj U₃) ≅
          Under.mk (ofHom (IsLocalization.Away.map Bh Rh (s.comp left) h)) from
        by
          simpa using
            (pushout_obj_iso_away (h := h) (Bh := Bh) (X := R) (Xh := Rh) (u := s.comp left)))
  -- Route correction: the remaining work is map-level transport, so we now close the four
  -- `IsPullback.of_iso` equalities using the pushed-out map comparison lemmas.
  refine IsPullback.of_iso hforget e1 e2 e3 e4 ?_ ?_ ?_ ?_
  · -- The top-left edge is the localization map induced by `left`.
    simpa [baseChange, base, U₀, U₁, f, e1, e2] using
      (pushout_map_eq_away_map (h := h) (Bh := Bh) (X := B') (Xh := Bh) (Y := B) (Yh := Bg)
        (u := RingHom.id B') (v := left))
  · -- The top-right edge is the localization map induced by `right`.
    simpa [baseChange, base, U₀, U₂, g, e1, e3] using
      (pushout_map_eq_away_map (h := h) (Bh := Bh) (X := B') (Xh := Bh) (Y := R') (Yh := Rf)
        (u := RingHom.id B') (v := right))
  · -- The lower-left edge is the localization of `s`.
    simpa [baseChange, base, U₁, U₃, p, e2, e4] using
      (pushout_map_eq_away_map (h := h) (Bh := Bh) (X := B) (Xh := Bg) (Y := R) (Yh := Rh)
        (u := left) (v := s))
  · -- The lower-right edge requires the pullback commutativity to match the chosen denominator.
    simpa [baseChange, base, U₂, U₃, q, e3, e4] using
      (pushout_right_edge_eq_localizationAwayRightMap (h := h) (Bh := Bh) (Rh := Rh) hsq)

end

end IsPullback
end CategoryTheory
