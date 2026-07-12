import StacksProject_2024.Chap12.Definition_12_6_2
import StacksProject_2024.Chap12.Lemma_12_6_3
import StacksProject_2024.Chap13.Definition_13_27_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ComposableArrows

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

namespace YonedaExtension

variable {A B : C}

/-
Domain sampling for Lemma 13.27.5.

Primary domain:
* abelian-category `Ext` classes attached to exact sequences.

Sampled owner-style declarations:
* `CategoryTheory.ExtensionClass.toExt`
* `ShortComplex.ShortExact.extClass`
* `Abelian.Ext.covariant_sequence_exact₁`
* `Abelian.Ext.contravariant_sequence_exact₃`

Layering:
* source-facing: `YonedaExtension A B n`
* core/canonical: `Ext B A n`
* bridge/view: the comparison map `YonedaExtension.toExt`

Primitive data here are only the exact composable chain together with the endpoint mono/epi
conditions already packaged by `YonedaExtension`. The comparison map to `Ext` is derived API; in
degree `1` the chapter-owned bridge is `ExtensionClass.toExt`, applied to the class of
`E.toExtension`. Higher degrees should recurse on the actual positive Yoneda degree rather than on
an auxiliary `n + 1` encoding.
-/

private theorem two_le_length (n : ℕ+) : (2 : ℕ) ≤ ((n + 1 : ℕ+) : ℕ) := by
  simpa using Nat.succ_le_succ (Nat.succ_le_of_lt n.2)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the underlying composable row of a degree `n + 1` Yoneda
extension is long enough to read off the first three arrows. -/
private theorem three_le_length (n : ℕ+) : (3 : ℕ) ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by
  simpa using Nat.succ_le_succ (two_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the underlying composable row of a degree `n + 1` Yoneda
extension is long enough to read off the first nontrivial object. -/
private theorem one_le_length_succ (n : ℕ+) : (1 : ℕ) ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by
  exact Nat.succ_le_succ (Nat.zero_le _)

omit [HasExt C] in
private theorem firstMap_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.firstMap ≫ E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) = 0 := by
  let hComplex := E.exact.toIsComplex
  calc
    E.firstMap ≫ E.obj.map' 1 2 (by decide) (two_le_length (n + 1))
        = eqToHom E.leftEq.symm ≫ 0 := by
            simpa [firstMap, Category.assoc] using
              congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ k)
                (hComplex.zero 0 (two_le_length (n + 1)))
    _ = 0 := by
      simpa using
        (show eqToHom E.leftEq.symm ≫
            (0 : E.obj.obj' 0 ⟶ E.obj.obj' 2 (two_le_length (n + 1))) = 0 from comp_zero)

omit [HasExt C] in
private theorem headExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk E.firstMap
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
      (firstMap_comp_next_zero E)).Exact := by
  let hExact := E.exact
  let hComplex := hExact.toIsComplex
  let e :
      ShortComplex.mk E.firstMap
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
          (firstMap_comp_next_zero E) ≅
        E.obj.sc hComplex 0 (two_le_length (n + 1)) :=
    ShortComplex.isoMk
      (eqToIso E.leftEq.symm)
      (Iso.refl _)
      (Iso.refl _)
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', firstMap]
        simpa using
          congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ E.obj.map k)
            (Subsingleton.elim _ _))
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc']
        simp)
  exact ShortComplex.exact_of_iso e.symm (hExact.exact 0 (two_le_length (n + 1)))

omit [HasExt C] in
private noncomputable def quotientMap {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ⟶ E.obj.obj' 2 (two_le_length (n + 1)) :=
  cokernel.desc E.firstMap
    (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
    (firstMap_comp_next_zero E)

omit [HasExt C] in
private theorem quotientMap_mono {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (quotientMap E) := by
  simpa [quotientMap] using (headExact E).mono_cokernelDesc

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient map obtained from the first exact pair still composes
to zero with the next differential. -/
private theorem quotientMap_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    quotientMap E ≫ (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 = 0 := by
  -- Compose with the cokernel projection so the claim becomes the original composable-row
  -- relation `d₁ ≫ d₂ = 0`.
  apply (cancel_epi (cokernel.π E.firstMap)).1
  -- After rewriting the truncated differential, the cokernel-desc equation reduces the claim to
  -- the original composable-row relation `d₁ ≫ d₂ = 0`.
  change cokernel.π E.firstMap ≫ quotientMap E ≫
      E.obj.map' 2 3 (by decide) (three_le_length n) =
    cokernel.π E.firstMap ≫ 0
  simp [quotientMap]
  calc
    E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
        E.obj.map' 2 3 (by decide) (three_le_length n) = 0 := by
          simpa using E.exact.toIsComplex.zero 1 (three_le_length n)
    _ = cokernel.π E.firstMap ≫ 0 := by rw [comp_zero]

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the middle pair in a degree `n + 1` Yoneda extension composes to
zero. -/
private theorem middle_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
      E.obj.map' 2 3 (by decide) (three_le_length n) = 0 := by
  simpa using E.exact.toIsComplex.zero 1 (three_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the middle pair of consecutive arrows in a degree `n + 1`
Yoneda extension is exact. -/
private theorem middleExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
      (E.obj.map' 2 3 (by decide) (three_le_length n))
      (middle_comp_next_zero E)).Exact := by
  -- This is the exactness statement at the first interior object of the original row.
  simpa [ComposableArrows.sc, ComposableArrows.sc'] using
    E.exact.exact 1 (three_le_length n)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient map is available as an instance-level mono for the
canonical image factorization. -/
private instance quotientMap_mono_inst {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Mono (quotientMap E) :=
  quotientMap_mono E

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient object `cokernel E.firstMap` identifies with the
abelian image of the next differential. -/
private noncomputable def quotient_image_iso {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    cokernel E.firstMap ≅ Abelian.image
      (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) :=
  image.isoStrongEpiMono
      (cokernel.π E.firstMap)
      (quotientMap E)
      (by simp [quotientMap]) ≪≫
    (Abelian.imageIsoImage _).symm

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the quotient-image comparison intertwines the quotient map with the
canonical image inclusion of the middle differential. -/
private theorem quotient_image_iso_hom_comp_image_ι {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient_image_iso E).hom ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) =
      quotientMap E := by
  have hImageIso :
      (Abelian.imageIsoImage
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))).inv ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) =
      Limits.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
    rw [Abelian.imageIsoImage_inv]
    simp [Abelian.image.ι]
  -- First convert the abelian image inclusion to the categorical image inclusion.
  calc
    (quotient_image_iso E).hom ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
        =
      (image.isoStrongEpiMono
          (cokernel.π E.firstMap)
          (quotientMap E)
          (by simp [quotientMap])).hom ≫
        (Abelian.imageIsoImage
          (E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))).inv ≫
        Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
            dsimp [quotient_image_iso]
            simp [Category.assoc]
    _
        =
      (image.isoStrongEpiMono
          (cokernel.π E.firstMap)
          (quotientMap E)
          (by simp [quotientMap])).hom ≫
        Limits.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
            let hCompose :=
              congrArg
                (fun k ↦
                  (image.isoStrongEpiMono
                      (cokernel.π E.firstMap)
                      (quotientMap E)
                      (by simp [quotientMap])).hom ≫ k)
                hImageIso
            simpa [Category.assoc] using hCompose
    _ = quotientMap E := by
      simpa using image.isoStrongEpiMono_hom_comp_ι
        (e := cokernel.π E.firstMap)
        (m := quotientMap E)
        (f := E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
        (comm := by simp [quotientMap])

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the inverse quotient-image comparison recovers the abelian image
inclusion from the quotient map. -/
private theorem quotient_image_iso_inv_comp_quotientMap {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient_image_iso E).inv ≫ quotientMap E =
      Abelian.image.ι (E.obj.map' 1 2 (by decide) (two_le_length (n + 1))) := by
  -- Rewrite the quotient map using the forward comparison and then contract the isomorphism.
  rw [← quotient_image_iso_hom_comp_image_ι E]
  rw [← Category.assoc]
  simp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_nextMap_eq_middle_tail {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 =
      E.obj.map' 2 3 (by decide) (three_le_length n) := by
  -- Forgetting the first two arrows exposes the original third arrow definitionally.
  rfl

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after forgetting the new quotient arrow, the tail of the quotient
row is exactly the twice-truncated original row, hence exact. -/
private theorem quotient_tail_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (((E.obj.δ₀.δ₀).precomp (quotientMap E)).δ₀).Exact := by
  -- The tail is definitionally `E.obj.δ₀.δ₀`, whose exactness comes from the original row.
  -- Normalizing the positive index once turns the twice-forgotten tail into a literal `δ₀` tail.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      simpa [ComposableArrows.precomp_δ₀] using (E.exact.δ₀).δ₀

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_head_iso_right_square {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.map' 2 3 (by decide) (three_le_length n) =
      ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2) ≫
        (Iso.refl _).hom := by
  -- The second square is the unchanged tail differential, expressed in the exact `isoMk` shape.
  simpa using (quotient_nextMap_eq_middle_tail E).symm

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: after replacing the quotient head map by the canonical abelian image
inclusion, the resulting first short complex is exact. -/
private theorem quotient_head_exact_via_image {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.mk
      (quotientMap E)
      ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2)
      (quotientMap_comp_next_zero E)).Exact := by
  let d₁ := E.obj.map' 1 2 (by decide) (two_le_length (n + 1))
  let d₂ := E.obj.map' 2 3 (by decide) (three_le_length n)
  let S : ShortComplex C := ShortComplex.mk d₁ d₂ (middle_comp_next_zero E)
  have hImage :
      (ShortComplex.mk (Abelian.image.ι d₁) d₂
        (Abelian.image_ι_comp_eq_zero (middle_comp_next_zero E))).Exact := by
    -- Exactness of the original middle pair transfers to exactness for the image inclusion.
    exact (ShortComplex.exact_iff_exact_image_ι S).1 (middleExact E)
  -- Transport the image-exact short complex across the quotient/image identification.
  refine ShortComplex.exact_of_iso ?_ hImage
  refine ShortComplex.isoMk (quotient_image_iso E).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · -- The first square is exactly the identification of `quotientMap E` with `image.ι`.
    simpa [S, d₁] using quotient_image_iso_inv_comp_quotientMap E
  · -- The second square is the dedicated transport-stable adapter for `ShortComplex.isoMk`.
    calc
      (Iso.refl _).hom ≫ d₂ = d₂ := by simp
      _ = (E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2 := (quotient_nextMap_eq_middle_tail E).symm
      _ = ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2) ≫ (Iso.refl _).hom := by simp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the head of the precomposed quotient row is exact in the precise
`ComposableArrows.mk₂` form required by `ComposableArrows.exact_of_δ₀`. -/
private theorem quotient_precomp_head_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ComposableArrows.mk₂
      (((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' 0 1
        (by decide)
        (show 1 ≤ ((n : ℕ) + 1) from Nat.succ_le_succ (Nat.zero_le _)))
      (((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' 1 2
        (by decide)
        (show 2 ≤ ((n : ℕ) + 1) from Nat.succ_le_succ (Nat.succ_le_of_lt n.2)))).Exact := by
  -- The first two arrows of the precomposed row are exactly the short complex handled above.
  let S : ShortComplex C := ShortComplex.mk
    (quotientMap E)
    ((E.obj.δ₀.δ₀).map' 0 1 (by decide) n.2)
    (quotientMap_comp_next_zero E)
  have hComp : S.toComposableArrows.Exact :=
    (ShortComplex.exact_iff_exact_toComposableArrows S).1 (quotient_head_exact_via_image E)
  simpa [S, ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one,
    ComposableArrows.Precomp.map_one_succ] using hComp

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the composable row obtained by quotienting the leftmost term of a
degree `n + 1` Yoneda extension is exact. -/
private theorem quotient_exact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    ((E.obj.δ₀.δ₀).precomp (quotientMap E)).Exact := by
  -- Assemble exactness from the exact head pair and the already exact twice-truncated tail.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      exact ComposableArrows.exact_of_δ₀
        (S := ((E.obj.δ₀.δ₀).precomp (quotientMap E)))
        (quotient_precomp_head_exact E)
        (quotient_tail_exact E)

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the last arrow of the quotient extension is the original terminal
arrow, hence remains an epimorphism. -/
private theorem quotient_lastMap_epi {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    Epi ((((E.obj.δ₀.δ₀).precomp (quotientMap E)).map' n (n + 1)) ≫ eqToHom E.rightEq) := by
  -- Route correction: normalize the successor index once, then the terminal map is the original
  -- last map by definition of `Precomp.map`.
  cases' n with n hn
  cases n with
  | zero => cases hn
  | succ n =>
      -- After normalizing the positive index, the target is definitionally the original last map.
      change Epi E.lastMap
      infer_instance

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: quotienting the first map of a positive-degree Yoneda extension
produces another Yoneda extension one degree lower. -/
private theorem quotient_property {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    IsYonedaExtension (cokernel E.firstMap) B n ((E.obj.δ₀.δ₀).precomp (quotientMap E)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · -- The right endpoint is unchanged by forgetting the first two arrows and re-precomposing.
    simpa using E.rightEq
  · -- The new first map is the quotient map, already known to be mono.
    simpa [quotientMap] using quotientMap_mono E
  · -- The head exactness now comes from the image-factorization identification.
    exact quotient_exact E
  · -- The terminal arrow is literally the original last map.
    exact quotient_lastMap_epi E

omit [HasExt C] in
private noncomputable def quotient {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    YonedaExtension (cokernel E.firstMap) B n where
  obj := (E.obj.δ₀.δ₀).precomp (quotientMap E)
  property := quotient_property E

omit [HasExt C] in
private theorem firstShortExact {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    (ShortComplex.cokernelSequence E.firstMap).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact E.firstMap)
    (show Mono E.firstMap from inferInstance) inferInstance

private noncomputable def toExtAux (n : ℕ+) :
    ∀ {X Y : C}, YonedaExtension X Y n → Ext Y X n :=
  @PNat.recOn n
    (fun m ↦ ∀ {X Y : C}, YonedaExtension X Y m → Ext Y X m)
    (fun {X Y} (F : YonedaExtension X Y 1) ↦
      ExtensionClass.toExt (⟦F.toExtension⟧ : ExtensionClass X Y))
    (fun n ih {X Y} (F : YonedaExtension X Y (n + 1)) ↦
      (ih (quotient F)).comp (firstShortExact F).extClass rfl)

/-- Lemma 13.27.5: the canonical comparison map from degree `n` Yoneda extensions of `B` by `A`
to `Ext B A n`, defined recursively on the actual positive Yoneda degree by peeling off the
leftmost short exact sequence and using the Chapter `12` degree-`1` bridge
`ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B)` as the base case. -/
noncomputable def toExt {n : ℕ+} (E : YonedaExtension A B n) : Ext B A n :=
  toExtAux n E

/-- Helper for Lemma 13.27.5: a short exact sequence already determines a degree `1` Yoneda
extension by viewing it as a composable row of length `2`. -/
private theorem isYonedaExtension_mk₂_of_extension (S : Extension A B) :
    IsYonedaExtension A B 1 (ComposableArrows.mk₂ S.f S.g) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · -- Proof comment: the first map of the row is literally the monomorphism in the short exact
    -- sequence.
    simpa [ComposableArrows.mk₂] using (inferInstance : Mono S.f)
  · -- Proof comment: exactness of the row is the short-complex exactness of the extension,
    -- rewritten through `ShortComplex.toComposableArrows`.
    change S.toShortComplex.toComposableArrows.Exact
    rw [← S.toShortComplex.exact_iff_exact_toComposableArrows]
    exact S.shortExact.exact
  · -- Proof comment: the last map of the row is literally the epimorphism in the short exact
    -- sequence.
    simpa [ComposableArrows.mk₂] using (inferInstance : Epi S.g)

/-- Helper for Lemma 13.27.5: the Chapter `12` source-facing extension owner embeds into the
degree `1` Yoneda-extension owner. -/
private noncomputable def yonedaExtension_of_extension (S : Extension A B) :
    YonedaExtension A B 1 where
  obj := ComposableArrows.mk₂ S.f S.g
  property := isYonedaExtension_mk₂_of_extension S

/-- Helper for Lemma 13.27.5: the right endpoint identification on the degree `1` Yoneda
extension attached to a short exact sequence is propositionally equal to `rfl`. -/
private theorem yonedaExtension_of_extension_rightEq (S : Extension A B) :
    (yonedaExtension_of_extension S).rightEq = rfl :=
  Subsingleton.elim _ _

/-- Helper for Lemma 13.27.5: converting a short exact sequence to a degree `1` Yoneda extension
does not change its extension class, because the recovered short exact sequence is isomorphic to
the original one by the identity on the middle object. -/
private theorem toExtension_isomorphic_yonedaExtension_of_extension (S : Extension A B) :
    Extension.Isomorphic (yonedaExtension_of_extension S).toExtension S := by
  refine ⟨Iso.refl S.E, ?_, ?_⟩
  · -- The recovered first map is definitionally the original monomorphism.
    simp [YonedaExtension.toExtension, YonedaExtension.firstMap, yonedaExtension_of_extension]
  · -- Move the endpoint transport to the other side, then the underlying second arrow is `S.g`.
    let E : YonedaExtension A B 1 := yonedaExtension_of_extension S
    have hComp : S.g ≫ eqToHom E.property.right_eq = S.g := by
      have hp : E.property.right_eq = rfl := Subsingleton.elim _ _
      rw [hp]
      simp
    calc
      (Iso.refl S.E).hom ≫ S.g = S.g := by
        simp
      _ = E.toExtension.g := by
        unfold YonedaExtension.toExtension YonedaExtension.lastMap
        symm
        refine (CategoryTheory.comp_eqToHom_iff E.property.right_eq
          (E.obj.map' 1 2 (by decide) (by decide)) S.g).2 ?_
        calc
          E.obj.map' 1 2 (by decide) (by decide) = S.g := by
            change Precomp.map (ComposableArrows.mk₁ S.g) S.f 1 2 (by decide) = S.g
            rfl
          _ = S.g ≫ eqToHom E.property.right_eq := by
            simpa using hComp.symm

/-- Surjectivity part of Lemma 13.27.5 for the canonical comparison map `YonedaExtension.toExt`. -/
theorem toExt_surjective (n : ℕ+) :
    Function.Surjective (toExt : YonedaExtension A B n → Ext B A n) := by
  refine PNat.recOn n ?_ ?_
  · intro e
    obtain ⟨ξ, hξ⟩ := ExtensionClass.toExt_bijective.surjective e
    obtain ⟨S, rfl⟩ := Quotient.exists_rep ξ
    refine ⟨yonedaExtension_of_extension S, ?_⟩
    -- Proof comment: in degree `1`, `YonedaExtension.toExt` is exactly the Chapter `12` bridge on
    -- the underlying short exact sequence.
    let hIso : Extension.Isomorphic (yonedaExtension_of_extension S).toExtension S :=
      toExtension_isomorphic_yonedaExtension_of_extension S
    change ExtensionClass.toExt
        (⟦(yonedaExtension_of_extension S).toExtension⟧ : ExtensionClass A B) = e
    rw [ExtensionClass.mk_eq_mk_of_isomorphic hIso]
    exact hξ
  · intro n ih
    -- Route correction: the remaining positive-degree case must follow the textbook roof
    -- construction in `D(𝒜)`, not an ad hoc change of `Ext` presentation.
    -- TODO: represent the given class by a left fraction `B[0] <- L -> A[n + 1]`, truncate away
    -- positive degrees, build the resulting Yoneda extension, and compare its recursive `toExt`
    -- with the original class via the quotient/first-short-exact recursion.
    sorry

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: in degree `1`, an endpoint-fixing ladder induces an isomorphism of
the underlying short exact sequences. -/
private theorem toExtension_isomorphic_of_endpoint_ladder {E F : YonedaExtension A B 1}
    (φ : E ⟶ F)
    (hφ₀ : app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm))
    (hφ₂ : app' φ.hom 2 = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    Extension.Isomorphic E.toExtension F.toExtension := by
  let φ₁ : E.obj.obj' 1 ⟶ F.obj.obj' 1 := app' φ.hom 1 (by decide)
  have hnat₀₁ :
      E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁ =
        app' φ.hom 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide) := by
    simpa [φ₁] using naturality' φ.hom 0 1 (by decide) (by decide)
  have hnat₁₂ :
      φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide) =
        E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ.hom 2 (by decide) := by
    simpa [φ₁] using naturality' φ.hom 1 2 (by decide) (by decide)
  have hcomm₁₂ : E.firstMap ≫ φ₁ = F.firstMap := by
    -- Precompose the left square with the chosen identification of the left endpoint with `A`.
    calc
      E.firstMap ≫ φ₁
          = eqToHom E.leftEq.symm ≫
              (E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁) := by
                simp [YonedaExtension.firstMap, Category.assoc]
      _ = eqToHom E.leftEq.symm ≫
            (app' φ.hom 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide)) := by
              rw [hnat₀₁]
      _ = eqToHom E.leftEq.symm ≫
            (eqToHom (E.leftEq.trans F.leftEq.symm) ≫
              F.obj.map' 0 1 (by decide) (by decide)) := by rw [hφ₀]
      _ = F.firstMap := by simp [YonedaExtension.firstMap, Category.assoc]
  have hcomm₂₃ : φ₁ ≫ F.lastMap = E.lastMap := by
    -- Postcompose the right square with the chosen identification of the right endpoint with `B`.
    calc
      φ₁ ≫ F.lastMap
          = φ₁ ≫ (F.obj.map' 1 2 (by decide) (by decide) ≫ eqToHom F.rightEq) := by
              simp [YonedaExtension.lastMap, Category.assoc]
      _ = (φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide)) ≫ eqToHom F.rightEq := by
            simp [Category.assoc]
      _ = (E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ.hom 2 (by decide)) ≫
            eqToHom F.rightEq := by rw [hnat₁₂]
      _ = E.lastMap := by
            rw [hφ₂]
            calc
              (E.obj.map' 1 2 (by decide) (by decide) ≫
                  eqToHom (E.rightEq.trans F.rightEq.symm)) ≫
                    eqToHom F.rightEq
                  =
                E.obj.map' 1 2 (by decide) (by decide) ≫
                  (eqToHom (E.rightEq.trans F.rightEq.symm) ≫ eqToHom F.rightEq) := by
                      simp [Category.assoc]
              _ = E.lastMap := by
                    simp [YonedaExtension.lastMap, Category.assoc]
  let ψ : E.toExtension.toShortComplex ⟶ F.toExtension.toShortComplex :=
    ShortComplex.homMk
      (𝟙 A)
      φ₁
      (𝟙 B)
      (by
        -- The first short-complex square is exactly the endpoint-normalized left square.
        simpa using hcomm₁₂.symm
      )
      (by
        -- The second short-complex square is exactly the endpoint-normalized right square.
        simpa using hcomm₂₃
      )
  have hIso₂ : IsIso φ₁ := by
    -- The short exact five-lemma upgrades the middle component to an isomorphism.
    change IsIso ψ.τ₂
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ψ E.toExtension.shortExact
      F.toExtension.shortExact
      (by
        dsimp [ψ]
        infer_instance)
      (by
        dsimp [ψ]
        infer_instance)
  refine ⟨asIso φ₁, ?_, ?_⟩
  · -- The left compatibility is exactly the normalized first square.
    simpa using hcomm₁₂
  · -- The right compatibility is exactly the normalized second square.
    simpa using hcomm₂₃

/-- Helper for Lemma 13.27.5: in degree `1`, an endpoint-fixing ladder induces the same
`Ext¹`-class because it is an isomorphism of the underlying short exact sequences. -/
private theorem toExt_eq_of_endpoint_ladder_one {E F : YonedaExtension A B 1}
    (φ : E ⟶ F)
    (hφ₀ : app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm))
    (hφ₂ : app' φ.hom 2 = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    toExt E = toExt F := by
  -- Package the ladder as an isomorphism of short exact sequences, then use the Chapter `12`
  -- bridge from extension isomorphisms to equality of `Ext¹`-classes.
  let hIso : Extension.Isomorphic E.toExtension F.toExtension :=
    toExtension_isomorphic_of_endpoint_ladder φ hφ₀ hφ₂
  change ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B) =
      ExtensionClass.toExt (⟦F.toExtension⟧ : ExtensionClass A B)
  rw [ExtensionClass.mk_eq_mk_of_isomorphic hIso]

/-- Helper for Lemma 13.27.5: in degree `1`, equivalent Yoneda extensions already have the same
class because both endpoint-fixing ladders identify the same short exact sequence class. -/
private theorem equivalent_implies_toExt_eq_one {E F : YonedaExtension A B 1}
    (h : Equivalent E F) :
    toExt E = toExt F := by
  rcases h with ⟨G, φ, ψ, hφ, hψ⟩
  rcases hφ with ⟨hφ₀, hφ₂⟩
  rcases hψ with ⟨hψ₀, hψ₂⟩
  -- Compare both extensions with the common refinement `G`.
  calc
    toExt E = toExt G := by
      symm
      exact toExt_eq_of_endpoint_ladder_one φ hφ₀ hφ₂
    _ = toExt F := by
      exact toExt_eq_of_endpoint_ladder_one ψ hψ₀ hψ₂

/-- Helper for Lemma 13.27.5: in degree `1`, equality of `Ext¹` classes forces equivalence of
Yoneda extensions through the Chapter `12` classification of short exact sequences. -/
private theorem toExt_eq_implies_equivalent_one {E F : YonedaExtension A B 1}
    (h : toExt E = toExt F) :
    Equivalent E F := by
  have hClass : E.toExtension.extClass = F.toExtension.extClass := by
    -- Proof comment: in degree `1`, `YonedaExtension.toExt` is the `extClass` of the underlying
    -- short exact sequence.
    simpa [Extension.extClass] using h
  have hIso : Extension.Isomorphic E.toExtension F.toExtension :=
    ExtensionClass.extension_isomorphic_of_extClass_eq hClass
  -- Proof comment: the source-facing Yoneda equivalence relation in degree `1` is defined through
  -- isomorphism of the underlying short exact sequences.
  exact equivalent_of_toExtension_isomorphic hIso

/-- Equality in `Ext` detects Yoneda equivalence for the canonical comparison map
`YonedaExtension.toExt`. -/
theorem equivalent_iff_toExt_eq {n : ℕ+} (E E' : YonedaExtension A B n) :
    Equivalent E E' ↔ toExt E = toExt E' := by
  revert E E'
  refine PNat.recOn n ?_ ?_
  · intro E E'
    constructor
    · -- Proof comment: in degree `1`, equivalent Yoneda extensions give the same extension class.
      exact equivalent_implies_toExt_eq_one
    · -- Proof comment: conversely, Chapter `12` turns equality of `Ext¹` classes back into an
      -- isomorphism of short exact sequences, hence into Yoneda equivalence.
      exact toExt_eq_implies_equivalent_one
  · intro n ih E E'
    -- Route correction: the higher-degree step must keep the source proof's common-denominator
    -- argument instead of switching to a later 3x3-diagram route.
    -- TODO: first prove ladder-invariance of `toExt` through the quotient recursion, then use the
    -- canonical roof attached to a Yoneda row and a common denominator in the localization to
    -- build a common refinement extension.
    sorry

end YonedaExtension

end CategoryTheory
