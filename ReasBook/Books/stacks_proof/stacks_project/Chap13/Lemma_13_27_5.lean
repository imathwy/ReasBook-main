import stacks_proof.stacks_project.Chap12.Definition_12_6_2
import stacks_proof.stacks_project.Chap12.Lemma_12_6_3
import stacks_proof.stacks_project.Chap13.Definition_13_27_4
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ComposableArrows

universe w v u

attribute [local instance] HasDerivedCategory.standard

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
  let hComplex := E.exact.toIsComplex
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
          simpa using hComplex.zero 1 (three_le_length n)
    _ = cokernel.π E.firstMap ≫ 0 := by rw [comp_zero]

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the middle pair in a degree `n + 1` Yoneda extension composes to
zero. -/
private theorem middle_comp_next_zero {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
      E.obj.map' 2 3 (by decide) (three_le_length n) = 0 := by
  let hComplex := E.exact.toIsComplex
  simpa using hComplex.zero 1 (three_le_length n)

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
        (cokernel.π E.firstMap)
        (quotientMap E)
        (by simp [quotientMap])

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

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: prepending a monomorphism `u : A ⟶ X` to a lower-degree Yoneda
extension first replaces the leftmost short exact sequence by its composite head map
`X ⟶ cokernel u ⟶ ...`. -/
private noncomputable def prependNextMap {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    X ⟶ F.obj.obj' 1 :=
  cokernel.π u ≫ F.firstMap

omit [HasExt C] in
omit [HasExt C] in
/-- Helper for Lemma 13.27.5: prepending `u` should rebuild a higher-degree Yoneda row by splicing
the cokernel sequence of `u` onto the lower-degree extension `F`. -/
private theorem prependYonedaExtension_property {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    IsYonedaExtension A B (n + 1) (((F.obj.δ₀).precomp (prependNextMap u F)).precomp u) := by
  -- Route correction: the splice proof is currently the unstable transport hotspot in the file.
  -- The intended proof packages the head cokernel sequence and the exact tail, then applies
  -- `ComposableArrows.exact_of_δ₀`.
  refine ⟨rfl, F.rightEq, ?_, ?_, ?_⟩
  · -- Proof comment: the first arrow of the spliced row is literally the chosen monomorphism.
    simpa [YonedaExtension.firstMap] using (inferInstance : Mono u)
  · -- Proof comment: build exactness by first proving exactness after forgetting the new left
    -- endpoint, and then glueing back the cokernel sequence of `u`.
    let hlen : 2 ≤ ((n : ℕ) + 1) := Nat.succ_le_succ (Nat.succ_le_of_lt n.2)
    have hFirstComp :
        F.firstMap ≫ F.obj.map' 1 2 (by decide) hlen = 0 := by
      let hComplex := F.exact.toIsComplex
      calc
        F.firstMap ≫ F.obj.map' 1 2 (by decide) hlen
            = eqToHom F.leftEq.symm ≫ 0 := by
                simpa [YonedaExtension.firstMap, Category.assoc] using
                  congrArg (fun k ↦ eqToHom F.leftEq.symm ≫ k) (hComplex.zero 0 hlen)
        _ = 0 := by simp
    have hTailHeadZero :
        prependNextMap u F ≫ F.obj.map' 1 2 (by decide) hlen = 0 := by
      calc
        prependNextMap u F ≫ F.obj.map' 1 2 (by decide) hlen
            = cokernel.π u ≫ (F.firstMap ≫ F.obj.map' 1 2 (by decide) hlen) := by
                simp [prependNextMap, Category.assoc]
        _ = cokernel.π u ≫ 0 := by rw [hFirstComp]
        _ = 0 := by simpa using (comp_zero (cokernel.π u))
    have hTailHead :
        (ShortComplex.mk
          (prependNextMap u F)
          (F.obj.map' 1 2 (by decide) hlen)
          hTailHeadZero).Exact := by
      let S₁ : ShortComplex C := ShortComplex.mk
        F.firstMap
        (F.obj.map' 1 2 (by decide) hlen)
        hFirstComp
      let S₂ : ShortComplex C := ShortComplex.mk
        (prependNextMap u F)
        (F.obj.map' 1 2 (by decide) hlen)
        hTailHeadZero
      let e : S₁ ≅ F.exact.sc 0 hlen :=
        ShortComplex.isoMk
          (eqToIso F.leftEq.symm)
          (Iso.refl _)
          (Iso.refl _)
          (by
            dsimp [S₁, ComposableArrows.sc, ComposableArrows.sc', YonedaExtension.firstMap]
            simpa using
              congrArg (fun k ↦ eqToHom F.leftEq.symm ≫ F.obj.map k) (Subsingleton.elim _ _))
          (by
            dsimp [S₁, ComposableArrows.sc, ComposableArrows.sc']
            simp)
      have hS₁ : S₁.Exact := by
        -- Proof comment: this is the exactness of the first interior pair in `F`.
        exact ShortComplex.exact_of_iso e.symm (F.exact.exact 0 hlen)
      let φ : S₂ ⟶ S₁ := ShortComplex.homMk
        (cokernel.π u)
        (𝟙 _)
        (𝟙 _)
        (by
          dsimp [S₁, S₂, prependNextMap]
          simp [Category.assoc])
        (by
          dsimp [S₁, S₂]
          simp)
      letI : Epi φ.τ₁ := by
        dsimp [φ]
        change Epi (cokernel.π u)
        infer_instance
      letI : IsIso φ.τ₂ := by
        dsimp [φ]
        change IsIso (𝟙 _)
        infer_instance
      letI : Mono φ.τ₃ := by
        dsimp [φ]
        change Mono (𝟙 _)
        infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS₁
    have hTailExact : ((F.obj.δ₀).precomp (prependNextMap u F)).Exact := by
      -- Proof comment: after the new head arrow, the remaining row is exact by the exact first
      -- interior pair and the unchanged exact tail of `F`.
      cases' n with n hn
      cases n with
      | zero =>
          cases hn
      | succ n =>
          refine ComposableArrows.exact_of_δ₀ ?_ ?_
          · have hComp :=
              (ShortComplex.exact_iff_exact_toComposableArrows
                (ShortComplex.mk
                  (prependNextMap u F)
                  (F.obj.map' 1 2 (by decide) hlen)
                  hTailHeadZero)).1 hTailHead
            simpa [ComposableArrows.mk₂, prependNextMap] using hComp
          · simpa [ComposableArrows.precomp_δ₀] using F.exact.δ₀
    have hHeadZero : u ≫ prependNextMap u F = 0 := by
      calc
        u ≫ prependNextMap u F = (u ≫ cokernel.π u) ≫ F.firstMap := by
          simp [prependNextMap, Category.assoc]
        _ = (0 : A ⟶ cokernel u) ≫ F.firstMap := by rw [cokernel.condition]
        _ = 0 := by
          simpa using (show (0 : A ⟶ cokernel u) ≫ F.firstMap = 0 from zero_comp)
    have hHead :
        (ShortComplex.mk
          u
          (prependNextMap u F)
          hHeadZero).Exact := by
      let S₁ : ShortComplex C := ShortComplex.cokernelSequence u
      let S₂ : ShortComplex C := ShortComplex.mk
        u
        (prependNextMap u F)
        hHeadZero
      let φ : S₁ ⟶ S₂ := ShortComplex.homMk
        (𝟙 _)
        (𝟙 _)
        F.firstMap
        (by
          dsimp [S₁, S₂]
          simp)
        (by
          dsimp [S₁, S₂, prependNextMap]
          simp [Category.assoc])
      letI : Epi φ.τ₁ := by
        dsimp [φ]
        change Epi (𝟙 A)
        infer_instance
      letI : IsIso φ.τ₂ := by
        dsimp [φ]
        change IsIso (𝟙 X)
        infer_instance
      letI : Mono φ.τ₃ := by
        dsimp [φ]
        change Mono F.firstMap
        infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
        (ShortComplex.cokernelSequence_exact u)
    -- Proof comment: combine the exact head pair `(u, prependNextMap u F)` with the exact tail.
    refine ComposableArrows.exact_of_δ₀ ?_ hTailExact
    have hComp :=
      ((ShortComplex.exact_iff_exact_toComposableArrows
        (ShortComplex.mk
          u
          (prependNextMap u F)
          hHeadZero)).1 hHead
    )
    simpa [ComposableArrows.mk₂, prependNextMap] using hComp
  · -- Proof comment: forgetting the leftmost splice does not change the terminal map.
    cases' n with n hn
    cases n with
    | zero =>
        cases hn
    | succ n =>
        simpa only [YonedaExtension.lastMap, ComposableArrows.Precomp.map_succ_succ] using
          F.property.epi_last

omit [HasExt C] in
/-- Helper for Lemma 13.27.5: the reverse recursion constructor that prepends a monomorphism
`u : A ⟶ X` to a lower-degree Yoneda extension of `B` by `cokernel u`. -/
private noncomputable def prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    YonedaExtension A B (n + 1) where
  obj := ((F.obj.δ₀).precomp (prependNextMap u F)).precomp u
  property := prependYonedaExtension_property u F

private noncomputable def toExtAux (n : ℕ+) :
    ∀ {X Y : C}, YonedaExtension X Y n → Ext Y X n :=
  @PNat.recOn n
    (fun m ↦ ∀ {X Y : C}, YonedaExtension X Y m → Ext Y X m)
    (fun {X Y} (F : YonedaExtension X Y 1) ↦
      ExtensionClass.toExt (⟦F.toExtension⟧ : ExtensionClass X Y))
    (fun n ih {X Y} (F : YonedaExtension X Y (n + 1)) ↦
      (ih (quotient F)).comp (firstShortExact F).extClass rfl)

/-- Canonical comparison map for Lemma 13.27.5 from degree `n` Yoneda extensions of `B` by `A`
to `Ext B A n`, defined recursively on the actual positive Yoneda degree by peeling off the
leftmost short exact sequence and using the Chapter `12` degree-`1` bridge
`ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B)` as the base case. -/
noncomputable def toExt {n : ℕ+} (E : YonedaExtension A B n) : Ext B A n :=
  toExtAux n E

/-- Helper for Lemma 13.27.5: the recursive definition of `toExt` unfolds one successor step by
peeling off the first short exact sequence and continuing with the quotient Yoneda row. -/
private theorem toExt_succ {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    toExt E = (toExt (quotient E)).comp (firstShortExact E).extClass rfl := by
  -- Proof comment: this is exactly the successor branch of the recursive definition `toExtAux`.
  simpa [toExt, toExtAux]

/-- Helper for Lemma 13.27.5: precomposing the tail of a Yoneda row with its own first map
reconstructs the original composable row. -/
private theorem precomp_firstMap_eq_obj {n : ℕ+} (E : YonedaExtension A B n) :
    (E.obj.δ₀).precomp E.firstMap = E.obj := by
  -- Proof comment: `precomp` adds back the forgotten left endpoint, so it suffices to check that
  -- the new first arrow is exactly the normalized first map of `E`.
  refine ComposableArrows.ext_succ E.leftEq.symm (by simp) ?_
  dsimp [YonedaExtension.firstMap]
  simpa using
    congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ E.obj.map k) (Subsingleton.elim _ _)

/-- Helper for Lemma 13.27.5: the first map of a prepended Yoneda extension is definitionally the
chosen monomorphism `u`. -/
private theorem firstMap_prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    (prependYonedaExtension u F).firstMap = u := by
  -- Proof comment: the prepend constructor inserts `u` as the new leftmost arrow.
  simp [prependYonedaExtension, YonedaExtension.firstMap]

/-- Helper for Lemma 13.27.5: the canonical short exact sequence attached to a monomorphism
`u : A ⟶ X` is the head short exact sequence used when prepending `u` to a Yoneda row. -/
private theorem headCokernelShortExact {X : C} (u : A ⟶ X) [Mono u] :
    (ShortComplex.cokernelSequence u).ShortExact := by
  -- Proof comment: the cokernel sequence of a monomorphism is short exact in any abelian
  -- category.
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u)
    (show Mono u from inferInstance) inferInstance

/-- Helper for Lemma 13.27.5: the quotient map of a prepended Yoneda row still has the expected
composite with the head cokernel projection. -/
private theorem cokernelπ_comp_quotientMap_prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u]
    {n : ℕ+} (F : YonedaExtension (cokernel u) B n) :
    cokernel.π (prependYonedaExtension u F).firstMap ≫
        quotientMap (prependYonedaExtension u F) =
      prependNextMap u F := by
  -- Proof comment: this is the defining equation of `quotientMap`, specialized to the prepended
  -- row.
  simpa [quotientMap, prependYonedaExtension, prependNextMap, YonedaExtension.firstMap]

/-- Helper for Lemma 13.27.5: after identifying the prepended first map with `u`, the quotient
map of the prepended Yoneda row is exactly the original first map of `F`. -/
private theorem quotientMap_prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    quotientMap (prependYonedaExtension u F) =
      (by simpa [firstMap_prependYonedaExtension u F] using F.firstMap) := by
  -- Proof comment: both maps are cokernel descendants of the same composite
  -- `cokernel.π u ≫ F.firstMap`, so it suffices to compare them after postcomposing with
  -- `cokernel.π u`.
  let f : cokernel (prependYonedaExtension u F).firstMap ⟶ F.obj.obj' 1 := by
    simpa [firstMap_prependYonedaExtension u F] using F.firstMap
  change quotientMap (prependYonedaExtension u F) = f
  have cokernelπ_cast_comp {Y : C} {f g : A ⟶ X} (h : g = f) (k : cokernel f ⟶ Y) :
      cokernel.π g ≫ (by simpa [h] using k) = cokernel.π f ≫ k := by
    cases h
    rfl
  have hf :
      cokernel.π (prependYonedaExtension u F).firstMap ≫ f =
        prependNextMap u F := by
    have hfirst := firstMap_prependYonedaExtension u F
    simpa [f, prependNextMap] using
      cokernelπ_cast_comp
        hfirst
        F.firstMap
  have hπ :
      cokernel.π (prependYonedaExtension u F).firstMap ≫
          quotientMap (prependYonedaExtension u F) =
        prependNextMap u F :=
    cokernelπ_comp_quotientMap_prependYonedaExtension u F
  exact Cofork.IsColimit.hom_ext
    (cokernelIsCokernel (prependYonedaExtension u F).firstMap)
    (hπ.trans hf.symm)

/-- Helper for Lemma 13.27.5: quotienting a prepended Yoneda extension recovers the original tail
extension over `cokernel u`. -/
private theorem quotient_prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    quotient (prependYonedaExtension u F) =
      (by simpa [firstMap_prependYonedaExtension u F] using F) := sorry

/-- Helper for Lemma 13.27.5: prepending a monomorphism composes the lower-degree Yoneda class
with the head extension class of the corresponding cokernel sequence. -/
private theorem toExt_prependYonedaExtension {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n) :
    toExt (prependYonedaExtension u F) =
      (toExt F).comp (headCokernelShortExact u).extClass rfl := sorry

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
    let T := S.toShortComplex
    change T.toComposableArrows.Exact
    rw [← T.exact_iff_exact_toComposableArrows]
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

/-- Helper for Lemma 13.27.5: every class in `Ext B A m` can be represented by a bounded roof
`Q.obj K ⟶ Q.obj (A[-m])` whose source complex is supported in degrees `[-m, 0]`. This isolates
the derived-category fraction step from the remaining source-facing task of rebuilding a Yoneda
row from that bounded roof. -/
private theorem boundedRoofOfExtClass [HasDerivedCategory C] (m : ℕ) (x : Ext B A m) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE (-(m : ℤ))) (_ : K.IsStrictlyLE 0)
      (s : K ⟶ (CochainComplex.singleFunctor C 0).obj B)
      (_ : IsIso (DerivedCategory.Q.map s))
      (g : K ⟶ (CochainComplex.singleFunctor C (-(m : ℤ))).obj A),
      ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app B) ≫
          x.hom ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            (m : ℤ) (-(m : ℤ)) 0 (by simp)).hom.app A ≫
          ((DerivedCategory.singleFunctorIsoCompQ C (-(m : ℤ))).hom.app A) =
        inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
  let X : CochainComplex C ℤ := (CochainComplex.singleFunctor C 0).obj B
  let Y : CochainComplex C ℤ := (CochainComplex.singleFunctor C (-(m : ℤ))).obj A
  letI : X.IsStrictlyGE (-(m : ℤ)) :=
    X.isStrictlyGE_of_ge (-(m : ℤ)) 0 (by omega)
  letI : Y.IsStrictlyLE 0 :=
    Y.isStrictlyLE_of_le (-(m : ℤ)) 0 (by omega)
  let f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y :=
    ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app B) ≫
      x.hom ≫
      ((DerivedCategory.singleFunctors C).shiftIso
        (m : ℤ) (-(m : ℤ)) 0 (by simp)).hom.app A ≫
      ((DerivedCategory.singleFunctorIsoCompQ C (-(m : ℤ))).hom.app A)
  obtain ⟨K, hKge, hKle, s, hs, g, hf⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE (-(m : ℤ)) 0 f
  exact ⟨K, hKge, hKle, s, hs, g, hf⟩

/-- Helper for Lemma 13.27.5: if a bounded roof denominator `s : K ⟶ X[j]` is already an
isomorphism in the derived category, then `K` is exact away from the single degree `j`, because
the target complex has zero homology there. -/
private theorem exactAt_of_isIso_Q_map_to_single [HasDerivedCategory C]
    {K : CochainComplex C ℤ} {j : ℤ} {X : C}
    (s : K ⟶ (CochainComplex.singleFunctor C j).obj X)
    (hs : IsIso (DerivedCategory.Q.map s)) {i : ℤ} (hi : i ≠ j) :
    K.ExactAt i := by
  have hQuasi : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso C s).1 hs
  letI : QuasiIsoAt s i := hQuasi.quasiIsoAt i
  have hTarget : ((CochainComplex.singleFunctor C j).obj X).ExactAt i := by
    -- The single complex has zero homology away from its unique nonzero degree.
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    simpa using
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) j X i hi)
  -- Transfer exactness across the quasi-isomorphism at the chosen degree.
  exact (exactAt_iff_of_quasiIsoAt s i).2 hTarget

/-- Helper for Lemma 13.27.5: in the bounded roof representing a positive-degree `Ext` class, the
lowest differential is monic because the term one step further left vanishes and the complex is
exact at the lowest nonzero degree. -/
private theorem boundedRoofBottomDifferentialMono [HasDerivedCategory C]
    {n : ℕ+} {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (hKExact : K.ExactAt (-((n + 1 : ℕ) : ℤ))) :
    Mono (K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))) := by
  let hzero : IsZero (K.X (-((n + 1 : ℕ) : ℤ) - 1)) :=
    K.isZero_of_isStrictlyGE (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) - 1) (by omega)
  have hsc :
      (K.sc' (-((n + 1 : ℕ) : ℤ) - 1) (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).Exact := by
    -- Proof comment: this is the exactness statement at the lowest nonzero degree of the roof.
    simpa using
      (K.exactAt_iff'
        (-((n + 1 : ℕ) : ℤ) - 1)
        (-((n + 1 : ℕ) : ℤ))
        (-(n : ℤ))
        (by simp)
        (by simp)).mp hKExact
  have hprev : K.d (-((n + 1 : ℕ) : ℤ) - 1) (-((n + 1 : ℕ) : ℤ)) = 0 := by
    -- Proof comment: the incoming differential starts at a zero object, so it is zero.
    exact hzero.eq_of_src _ _
  -- Proof comment: exactness with zero incoming differential forces the outgoing differential to
  -- be monic.
  exact hsc.mono_g hprev

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

/-- Helper for Lemma 13.27.5: a chain map that is null-homotopic already becomes zero in the
derived category. -/
private theorem qMap_eq_zero_of_homotopy [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (h : Homotopy f 0) :
    DerivedCategory.Q.map f = 0 := by
  -- Proof comment: `DerivedCategory.Q` factors through the homotopy-category quotient, so this
  -- should be a direct consequence of `HomotopyCategory.eq_of_homotopy`.
  have hQ : DerivedCategory.Q.map f = DerivedCategory.Q.map (0 : K ⟶ L) := by
    have hQ' :
        HomologicalComplexUpToQuasiIso.Q.map f =
          HomologicalComplexUpToQuasiIso.Q.map (0 : K ⟶ L) :=
      HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h
    simpa [DerivedCategory.Q] using hQ'
  calc
    DerivedCategory.Q.map f = DerivedCategory.Q.map (0 : K ⟶ L) := hQ
    _ = 0 := by
      simp

/-- Helper for Lemma 13.27.5: a map to a single complex has zero component away from its support
degree. -/
private theorem mkHomToSingle_component_eq_zero_of_ne
    {K : CochainComplex C ℤ} {q i : ℤ} {X : C}
    (f : K.X q ⟶ X)
    (hf : ∀ j, (ComplexShape.up ℤ).Rel j q → K.d j q ≫ f = 0)
    (hi : i ≠ q) :
    (HomologicalComplex.mkHomToSingle f hf).f i = 0 := by
  -- Proof comment: this is the off-support branch in the definition of `mkHomToSingle`.
  simp [HomologicalComplex.mkHomToSingle, hi]

/-- Helper for Lemma 13.27.5: a map to a single complex is null-homotopic as soon as its unique
nonzero component factors through the outgoing differential one degree to the right. -/
private noncomputable def homotopyToZero_mkHomToSingle_of_factor
    {K : CochainComplex C ℤ} {q : ℤ} {X : C}
    (f : K.X q ⟶ X)
    (hfPrev : K.d (q - 1) q ≫ f = 0)
    (g : K.X (q + 1) ⟶ X)
    (hf : K.d q (q + 1) ≫ g = f) :
    Homotopy
      (HomologicalComplex.mkHomToSingle f
        (fun i hi ↦ by
          have hRel : i + 1 = q := by
            simpa using hi
          have hi' : i = q - 1 := by omega
          subst hi'
          simpa using hfPrev))
      0 := by
  let h : ∀ i j, (ComplexShape.up ℤ).Rel j i →
      (K.X i ⟶ ((CochainComplex.singleFunctor C q).obj X).X j) :=
    fun i j hij ↦ by
      by_cases hj : j = q
      · subst j
        have hi : i = q + 1 := by
          simpa using hij.symm
        subst hi
        exact g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).inv
      · exact 0
  have hMap :
      Homotopy.nullHomotopicMap' h =
        HomologicalComplex.mkHomToSingle f
          (fun i hi ↦ by
            have hRel : i + 1 = q := by
              simpa using hi
            have hi' : i = q - 1 := by omega
            subst hi'
            simpa using hfPrev) := by
    apply HomologicalComplex.to_single_hom_ext
    have hrel₀ : (ComplexShape.up ℤ).Rel (q - 1) q := by
      simpa using (show q - 1 + 1 = q by omega)
    have hrel₁ : (ComplexShape.up ℤ).Rel q (q + 1) := by
      simpa using (show q + 1 = q + 1 by rfl)
    rw [Homotopy.nullHomotopicMap'_f hrel₀ hrel₁]
    simpa [h, Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).inv)
        hf
  simpa [hMap] using (Homotopy.nullHomotopy' h)

/-- Helper for Lemma 13.27.5: postcomposing the numerator of a bounded roof with the pushout head
map gives a null-homotopic map to the corresponding single complex, so it already vanishes after
applying `DerivedCategory.Q`. -/
private theorem boundedRoofHeadPostcompQMap_eq_zero [HasDerivedCategory C]
    {n : ℕ+} {K : CochainComplex C ℤ} {X : C}
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X) :
    let q : ℤ := -((n + 1 : ℕ) : ℤ)
    let d : K.X q ⟶ K.X (q + 1) := K.d q (q + 1)
    let g₀ : K.X q ⟶ X :=
      g.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).hom
    let u : X ⟶ pushout d g₀ := pushout.inr d g₀
    DerivedCategory.Q.map (g ≫ (CochainComplex.singleFunctor C q).map u) = 0 := by
  -- Proof comment: identify the postcomposed roof numerator with the canonical map to a single
  -- complex supported in degree `q`, kill that map by the pushout factorization, and then pass
  -- the resulting null-homotopy through `DerivedCategory.Q`.
  dsimp
  let q : ℤ := -((n + 1 : ℕ) : ℤ)
  let d : K.X q ⟶ K.X (q + 1) := K.d q (q + 1)
  let g₀ : K.X q ⟶ X :=
    g.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).hom
  let u : X ⟶ pushout d g₀ := pushout.inr d g₀
  have hgPrev :
      K.d (q - 1) q ≫ g₀ = 0 := by
    have hrel : (ComplexShape.up ℤ).Rel (q - 1) q := by
      simpa using (show q - 1 + 1 = q by omega)
    have hcomm :
        0 =
          K.d (q - 1) q ≫ g.f q ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).hom := by
      simpa using
        (g.comm_assoc
          (q - 1)
          q
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).hom)
    calc
      K.d (q - 1) q ≫ g₀ =
          K.d (q - 1) q ≫ g.f q ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q X).hom := by
              simp [g₀, Category.assoc]
      _ = 0 := by
        simpa using hcomm.symm
  have hPostcomp :
      g ≫ (CochainComplex.singleFunctor C q).map u =
        HomologicalComplex.mkHomToSingle
          (g₀ ≫ u)
          (fun i hi ↦ by
            have hRel : i + 1 = q := by
              simpa using hi
            have hi' : i = q - 1 := by omega
            subst hi'
            calc
              K.d (q - 1) q ≫ g₀ ≫ u = (K.d (q - 1) q ≫ g₀) ≫ u := by
                  simp [Category.assoc]
              _ = 0 ≫ u := by rw [hgPrev]
              _ = 0 := by simp) := by
    apply HomologicalComplex.to_single_hom_ext
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.mkHomToSingle_f, g₀, u, Category.assoc]
    rfl
  have hHomotopy :
      Homotopy (g ≫ (CochainComplex.singleFunctor C q).map u) 0 := by
    rw [hPostcomp]
    let hPushout : d ≫ pushout.inl d g₀ = g₀ ≫ pushout.inr d g₀ := pushout.condition
    refine homotopyToZero_mkHomToSingle_of_factor
      (g₀ ≫ u)
      (by
        calc
          K.d (q - 1) q ≫ g₀ ≫ u = (K.d (q - 1) q ≫ g₀) ≫ u := by
              simp [Category.assoc]
          _ = 0 ≫ u := by rw [hgPrev]
          _ = 0 := by simp)
      (pushout.inl d g₀)
      ?_
    simpa [u] using hPushout
  exact qMap_eq_zero_of_homotopy _ hHomotopy

/-- Helper for Lemma 13.27.5: once lower-degree surjectivity is available, any bounded roof
representing a class in `Ext Y X (n + 1)` can be rebuilt into a degree `n + 1` Yoneda extension
with the same `Ext` class. -/
private noncomputable def extDerivedMap {n : ℕ+} [HasDerivedCategory C]
    {X Y : C} (x : Ext Y X (n + 1)) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X) :=
  ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y) ≫
    x.hom ≫
    ((DerivedCategory.singleFunctors C).shiftIso
      ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) 0 (by simp)).hom.app X ≫
    ((DerivedCategory.singleFunctorIsoCompQ C (-((n + 1 : ℕ) : ℤ))).hom.app X)

/-- Helper for Lemma 13.27.5: once lower-degree surjectivity is available, any bounded roof
representing a class in `Ext Y X (n + 1)` can be rebuilt into a degree `n + 1` Yoneda extension
with the same `Ext` class. -/
private theorem realizeBoundedRoofStep {n : ℕ+}
    (ih : ∀ {X Y : C}, Function.Surjective (toExt : YonedaExtension X Y n → Ext Y X n))
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y) ≫
          x.hom ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) 0 (by simp)).hom.app X ≫
          ((DerivedCategory.singleFunctorIsoCompQ C (-((n + 1 : ℕ) : ℤ))).hom.app X) =
        inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g) :
    ∃ F : YonedaExtension X Y (n + 1), toExt F = x := sorry

/-- Helper for Lemma 13.27.5: choose one concrete Yoneda extension realizing a bounded roof for
an `Ext` class, so the positive-degree converse can compare both targets to the same realized
common denominator instead of reopening the existential witness each time. -/
private noncomputable def realizeBoundedRoof {n : ℕ+}
    (ih : ∀ {X Y : C}, Function.Surjective (toExt : YonedaExtension X Y n → Ext Y X n))
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y) ≫
          x.hom ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) 0 (by simp)).hom.app X ≫
          ((DerivedCategory.singleFunctorIsoCompQ C (-((n + 1 : ℕ) : ℤ))).hom.app X) =
        inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g) :
    YonedaExtension X Y (n + 1) :=
  (realizeBoundedRoofStep ih x hKge s hs g hg).choose

/-- Helper for Lemma 13.27.5: the chosen bounded-roof realization really represents the original
`Ext` class. This packages the realization step in a rewrite-friendly form for the common-
denominator converse. -/
private theorem realizeBoundedRoof_toExt {n : ℕ+}
    (ih : ∀ {X Y : C}, Function.Surjective (toExt : YonedaExtension X Y n → Ext Y X n))
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y) ≫
          x.hom ≫
          ((DerivedCategory.singleFunctors C).shiftIso
            ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) 0 (by simp)).hom.app X ≫
          ((DerivedCategory.singleFunctorIsoCompQ C (-((n + 1 : ℕ) : ℤ))).hom.app X) =
        inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g) :
    toExt (realizeBoundedRoof ih x hKge s hs g hg) = x := by
  -- Proof comment: this is exactly the specification carried by the existential realization step.
  exact (realizeBoundedRoofStep ih x hKge s hs g hg).choose_spec

/-- Helper for Lemma 13.27.5: surjectivity of `YonedaExtension.toExt` is proved by recursion on
the Yoneda degree, but the recursive step must allow the left endpoint to vary because the tail
extension is over `cokernel u`. -/
private theorem toExt_surjectiveAux (n : ℕ+) :
    ∀ {X Y : C}, Function.Surjective (toExt : YonedaExtension X Y n → Ext Y X n) := by
  -- Proof comment: the base case is Chapter `12`, while the successor case should be the bounded
  -- roof realization packaged in `realizeBoundedRoofStep`.
  refine @PNat.recOn n
    (fun m ↦ ∀ {X Y : C}, Function.Surjective (toExt : YonedaExtension X Y m → Ext Y X m))
    ?_ ?_
  · intro X Y x
    have hBij : Function.Bijective (ExtensionClass.toExt : ExtensionClass X Y → Ext Y X 1) :=
      ExtensionClass.toExt_bijective
    obtain ⟨ξ, rfl⟩ := hBij.2 x
    refine Quotient.inductionOn ξ ?_
    intro S
    refine ⟨yonedaExtension_of_extension S, ?_⟩
    -- Proof comment: in degree `1`, the Yoneda row attached to a short exact sequence recovers
    -- the same extension class.
    have hClass :
        (⟦(yonedaExtension_of_extension S).toExtension⟧ : ExtensionClass X Y) = ⟦S⟧ :=
      ExtensionClass.mk_eq_mk_of_isomorphic
        (toExtension_isomorphic_yonedaExtension_of_extension S)
    simpa [toExt] using congrArg ExtensionClass.toExt hClass
  · intro n ih X Y x
    letI := HasDerivedCategory.standard C
    obtain ⟨K, hKge, _, s, hs, g, hg⟩ :=
      boundedRoofOfExtClass ((n + 1 : ℕ)) x
    -- Proof comment: the recursive realization only needs the bounded roof and the lower-degree
    -- surjectivity hypothesis.
    exact realizeBoundedRoofStep ih x hKge s hs g hg

/-- Surjectivity part of Lemma 13.27.5 for the canonical comparison map `YonedaExtension.toExt`. -/
theorem toExt_surjective (n : ℕ+) :
    Function.Surjective (toExt : YonedaExtension A B n → Ext B A n) :=
  toExt_surjectiveAux n

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

/-- Helper for Lemma 13.27.5: a ladder with right endpoint fixed and left endpoint map
`a : A ⟶ A'` transports the recursively defined Yoneda class by postcomposition with
`Ext.mk₀ a`. -/
private theorem toExt_comp_mk₀_of_rowHom_one {A A' B : C}
    {E : YonedaExtension A B 1} {F : YonedaExtension A' B 1}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm)
    (hφ₂ : app' φ 2 = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    (toExt E).comp (Ext.mk₀ a) (add_zero 1) = toExt F := by
  let ξE := E.toExtension.extClass
  let ξF := F.toExtension.extClass
  let φ₁ : E.obj.obj' 1 ⟶ F.obj.obj' 1 := app' φ 1
  have hnat₀₁ :
      E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁ =
        app' φ 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide) := by
    simpa [φ₁] using naturality' φ 0 1 (by decide) (by decide)
  have hnat₁₂ :
      φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide) =
        E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ 2 (by decide) := by
    simpa [φ₁] using (naturality' φ 1 2 (by decide) (by decide)).symm
  have hcomm₁₂ : E.firstMap ≫ φ₁ = a ≫ F.firstMap := by
    -- Proof comment: normalize the left square to the chosen fixed endpoints `A` and `A'`.
    calc
      E.firstMap ≫ φ₁ =
          eqToHom E.leftEq.symm ≫
            (E.obj.map' 0 1 (by decide) (by decide) ≫ φ₁) := by
              simp [YonedaExtension.firstMap, Category.assoc]
      _ =
          eqToHom E.leftEq.symm ≫
            (app' φ 0 (by decide) ≫ F.obj.map' 0 1 (by decide) (by decide)) := by
              rw [hnat₀₁]
      _ =
          eqToHom E.leftEq.symm ≫
            ((eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) ≫
              F.obj.map' 0 1 (by decide) (by decide)) := by
                rw [hφ₀]
      _ = a ≫ F.firstMap := by
        simp [YonedaExtension.firstMap, Category.assoc]
  have hcomm₂₃ : φ₁ ≫ F.lastMap = E.lastMap := by
    -- Proof comment: the right square is identity on `B`, so the endpoint transport collapses.
    have hright :
        (E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ 2 (by decide)) ≫
          eqToHom F.rightEq = E.lastMap := by
      calc
        (E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ 2 (by decide)) ≫
            eqToHom F.rightEq =
          E.obj.map' 1 2 (by decide) (by decide) ≫
            (app' φ 2 (by decide) ≫ eqToHom F.rightEq) := by
              simp [Category.assoc]
        _ =
          E.obj.map' 1 2 (by decide) (by decide) ≫ eqToHom E.rightEq := by
            rw [hφ₂]
            calc
              E.obj.map' 1 2 (by decide) (by decide) ≫
                  eqToHom (E.rightEq.trans F.rightEq.symm) ≫ eqToHom F.rightEq =
                E.obj.map' 1 2 (by decide) (by decide) ≫
                  eqToHom ((E.rightEq.trans F.rightEq.symm).trans F.rightEq) := by
                    rw [eqToHom_trans]
              _ = E.obj.map' 1 2 (by decide) (by decide) ≫ eqToHom E.rightEq := by
                    simp
        _ = E.lastMap := by
          simp [YonedaExtension.lastMap]
    calc
      φ₁ ≫ F.lastMap =
          (φ₁ ≫ F.obj.map' 1 2 (by decide) (by decide)) ≫ eqToHom F.rightEq := by
            simp [YonedaExtension.lastMap, Category.assoc]
      _ =
          (E.obj.map' 1 2 (by decide) (by decide) ≫ app' φ 2 (by decide)) ≫
            eqToHom F.rightEq := by
              rw [hnat₁₂]
      _ = E.lastMap := hright
  let ψ : E.toExtension.toShortComplex ⟶ F.toExtension.toShortComplex :=
    ShortComplex.homMk
      a
      φ₁
      (𝟙 B)
      (by
        -- Proof comment: this is the normalized left square of the ladder.
        simpa using hcomm₁₂.symm
      )
      (by
        -- Proof comment: this is the normalized right square of the ladder.
        simpa using hcomm₂₃
      )
  have hNat :
      ξE.comp (Ext.mk₀ a) (add_zero 1) =
        (Ext.mk₀ (𝟙 B)).comp ξF (zero_add 1) := by
    -- Proof comment: the boundary class is natural for morphisms of short exact sequences.
    simpa [Extension.extClass, ψ] using
      (ShortComplex.ShortExact.extClass_naturality
        E.toExtension.shortExact
        F.toExtension.shortExact
        ψ)
  calc
    (toExt E).comp (Ext.mk₀ a) (add_zero 1)
        = (Ext.mk₀ (𝟙 B)).comp ξF (zero_add 1) := by
            simpa [toExt] using hNat
    _ = toExt F := by
      change (Ext.mk₀ (𝟙 B)).comp ξF (zero_add 1) = ξF
      simpa using (Ext.mk₀_id_comp ξF)

/-- Helper for Lemma 13.27.5: a row morphism with left endpoint map `a` intertwines the
normalized first maps of two Yoneda rows. -/
private theorem firstMap_naturality_of_rowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    E.firstMap ≫ app' φ 1 = a ≫ F.firstMap := by
  let h₁ : 1 ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by omega
  let h₀₁ : 0 ≤ 1 := by omega
  -- Proof comment: rewrite the left square of `φ` through the chosen endpoint identifications.
  calc
    E.firstMap ≫ app' φ 1 h₁ =
        eqToHom E.leftEq.symm ≫ (E.obj.map' 0 1 h₀₁ h₁ ≫ app' φ 1 h₁) := by
          simp [YonedaExtension.firstMap, Category.assoc]
    _ =
        eqToHom E.leftEq.symm ≫ (app' φ 0 ≫ F.obj.map' 0 1 h₀₁ h₁) := by
          rw [naturality' φ 0 1 h₀₁ h₁]
    _ =
        eqToHom E.leftEq.symm ≫
          ((eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) ≫ F.obj.map' 0 1 h₀₁ h₁) := by
            rw [hφ₀]
    _ = a ≫ F.firstMap := by
      simp [YonedaExtension.firstMap, Category.assoc]

/-- Helper for Lemma 13.27.5: a row morphism with left endpoint map `a` induces the canonical
map between the cokernels of the normalized first maps. -/
private noncomputable def quotientMapOfRowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    cokernel E.firstMap ⟶ cokernel F.firstMap := by
  let h₁ : 1 ≤ (((n + 1 : ℕ+) : ℕ) + 1) := by omega
  refine cokernel.desc E.firstMap (app' φ 1 h₁ ≫ cokernel.π F.firstMap) ?_
  -- Proof comment: the first square of `φ` makes the cokernel relation descend.
  calc
    E.firstMap ≫ (app' φ 1 h₁ ≫ cokernel.π F.firstMap)
        = (E.firstMap ≫ app' φ 1 h₁) ≫ cokernel.π F.firstMap := by
            simp [Category.assoc]
    _ = (a ≫ F.firstMap) ≫ cokernel.π F.firstMap := by
          rw [firstMap_naturality_of_rowHom a φ hφ₀]
    _ = a ≫ (F.firstMap ≫ cokernel.π F.firstMap) := by
          simp [Category.assoc]
    _ = a ≫ 0 := by
          rw [cokernel.condition]
    _ = 0 := by
          simpa using (show a ≫ (0 : A' ⟶ cokernel F.firstMap) = 0 from comp_zero)

/-- Helper for Lemma 13.27.5: the induced quotient map is characterized by its composite with
the source cokernel projection. -/
private theorem cokernel_π_comp_quotientMapOfRowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    cokernel.π E.firstMap ≫ quotientMapOfRowHom a φ hφ₀ =
      app' φ 1 (by omega) ≫ cokernel.π F.firstMap := by
  -- Proof comment: this is the defining equation of the descended cokernel map.
  simp [quotientMapOfRowHom]

/-- Helper for Lemma 13.27.5: quotienting a positive-degree Yoneda extension keeps the new left
endpoint identification definitionally trivial. -/
private theorem quotient_leftEq_rfl {A B : C} {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient E).leftEq = rfl :=
  rfl

/-- Helper for Lemma 13.27.5: the endpoint transports around the descended cokernel map of a
quotient-row ladder are propositionally trivial, because quotient left endpoints are definitionally
`rfl`. -/
private theorem quotientMapOfRowHom_leftEndpoint_normalize {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    eqToHom (quotient E).leftEq ≫
        quotientMapOfRowHom a φ hφ₀ ≫
        eqToHom (quotient F).leftEq.symm =
      quotientMapOfRowHom a φ hφ₀ := by
  -- Proof comment: both endpoint equalities are subsingleton proofs of reflexive equalities, so
  -- the surrounding `eqToHom` transports collapse to identities.
  cases quotient_leftEq_rfl E
  cases quotient_leftEq_rfl F
  change (𝟙 (cokernel E.firstMap)) ≫ quotientMapOfRowHom a φ hφ₀ ≫
      𝟙 (cokernel F.firstMap) = quotientMapOfRowHom a φ hφ₀
  simp

/-- Helper for Lemma 13.27.5: quotienting only removes the head object, so the right endpoint
identification agrees propositionally with the original row. -/
private theorem quotient_rightEq_eq {A B : C} {n : ℕ+}
    (E : YonedaExtension A B (n + 1)) :
    (quotient E).rightEq = E.rightEq := by
  -- Proof comment: endpoint identifications live in a subsingleton, so the quotient inherits the
  -- same right-endpoint proof as the original row.
  apply Subsingleton.elim

/-- Helper for Lemma 13.27.5: forgetting the first two arrows of a row ladder gives the induced
morphism between the double tails. -/
private noncomputable def doubleDeltaRowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (φ : E.obj ⟶ F.obj) :
    E.obj.δ₀.δ₀ ⟶ F.obj.δ₀.δ₀ :=
  ComposableArrows.δ₀Functor.map (ComposableArrows.δ₀Functor.map φ)

/-- Helper for Lemma 13.27.5: the descended cokernel map and the double-shifted tail of a row
ladder satisfy the head square required by `ComposableArrows.homMkSucc`. -/
private theorem quotientHeadSquare_of_rowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    quotientMap E ≫ app' (doubleDeltaRowHom φ) 0 =
      quotientMapOfRowHom a φ hφ₀ ≫ quotientMap F := by
  -- Proof comment: after precomposing with the source cokernel projection, both descended maps
  -- unfold to the original square `naturality' φ 1 2`.
  let h0 : 0 ≤ (n : ℕ) := Nat.zero_le _
  let h1 : 1 ≤ (((n + 1 : ℕ+) : ℕ) + 1) := one_le_length_succ n
  apply (cancel_epi (cokernel.π E.firstMap)).1
  calc
    cokernel.π E.firstMap ≫ quotientMap E ≫ app' (doubleDeltaRowHom φ) 0 h0
        =
      E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
        app' (doubleDeltaRowHom φ) 0 h0 := by
          simp [quotientMap, Category.assoc]
    _ = app' φ 1 h1 ≫ F.obj.map' 1 2 (by decide) (two_le_length (n + 1)) := by
          change E.obj.map' 1 2 (by decide) (two_le_length (n + 1)) ≫
              app' φ 2 (two_le_length (n + 1)) =
            app' φ 1 h1 ≫ F.obj.map' 1 2 (by decide) (two_le_length (n + 1))
          simpa using naturality' φ 1 2 (by decide) (two_le_length (n + 1))
    _ = (app' φ 1 h1 ≫ cokernel.π F.firstMap) ≫ quotientMap F := by
          simp [quotientMap, Category.assoc]
    _ = (cokernel.π E.firstMap ≫ quotientMapOfRowHom a φ hφ₀) ≫ quotientMap F := by
          rw [cokernel_π_comp_quotientMapOfRowHom]
    _ = cokernel.π E.firstMap ≫ (quotientMapOfRowHom a φ hφ₀ ≫ quotientMap F) := by
          simp [Category.assoc]

/-- Helper for Lemma 13.27.5: a ladder with left endpoint map `a` induces a genuine morphism
between the quotient Yoneda rows, so later recursive proofs stay inside the quotient world
instead of reopening cokernel-owner transport. -/
private noncomputable def quotientRowHomOfRowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    (quotient E).obj ⟶ (quotient F).obj := by
  -- Proof comment: package the quotient bridge once as the `homMkSucc` morphism whose head
  -- component is the descended cokernel map and whose tail is the double-shifted ladder.
  refine ComposableArrows.homMkSucc
    (quotientMapOfRowHom a φ hφ₀)
    ?_
    ?_
  · change E.obj.δ₀.δ₀ ⟶ F.obj.δ₀.δ₀
    exact doubleDeltaRowHom φ
  · simpa [doubleDeltaRowHom] using quotientHeadSquare_of_rowHom a φ hφ₀

/-- Helper for Lemma 13.27.5: the quotient-row ladder starts with the descended cokernel map. -/
private theorem quotientRowHomOfRowHom_leftEndpoint {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm) :
    app' (quotientRowHomOfRowHom a φ hφ₀) 0 =
      eqToHom (quotient E).leftEq ≫
        quotientMapOfRowHom a φ hφ₀ ≫
        eqToHom (quotient F).leftEq.symm := by
  -- Proof comment: `homMkSucc` starts with the descended cokernel map, and the quotient endpoint
  -- transports normalize away by the previous lemma.
  let β : (quotient E).obj.δ₀ ⟶ (quotient F).obj.δ₀ := by
    change E.obj.δ₀.δ₀ ⟶ F.obj.δ₀.δ₀
    exact doubleDeltaRowHom φ
  let w :
      (quotient E).obj.map' 0 1 ≫ app' β 0 =
        quotientMapOfRowHom a φ hφ₀ ≫ (quotient F).obj.map' 0 1 := by
    simpa [doubleDeltaRowHom] using quotientHeadSquare_of_rowHom a φ hφ₀
  rw [quotientMapOfRowHom_leftEndpoint_normalize a φ hφ₀]
  simpa [quotientRowHomOfRowHom, doubleDeltaRowHom] using
    (ComposableArrows.homMkSucc_app_zero (quotientMapOfRowHom a φ hφ₀) β w)

/-- Helper for Lemma 13.27.5: the quotient-row ladder keeps the right endpoint fixed. -/
private theorem quotientRowHomOfRowHom_rightEndpoint {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B (n + 1)} {F : YonedaExtension A' B (n + 1)}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm)
    (hφn : app' φ (((n + 1 : ℕ+) : ℕ) + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    app' (quotientRowHomOfRowHom a φ hφ₀) ((n : ℕ) + 1) =
      eqToHom ((quotient E).rightEq.trans (quotient F).rightEq.symm) := by
  -- Proof comment: after shifting by two indices, the last component of the quotient-row ladder
  -- is the original terminal component of `φ`, and the quotient keeps the same right endpoint.
  let β : (quotient E).obj.δ₀ ⟶ (quotient F).obj.δ₀ := by
    change E.obj.δ₀.δ₀ ⟶ F.obj.δ₀.δ₀
    exact doubleDeltaRowHom φ
  let w :
      (quotient E).obj.map' 0 1 ≫ app' β 0 =
        quotientMapOfRowHom a φ hφ₀ ≫ (quotient F).obj.map' 0 1 := by
    simpa [doubleDeltaRowHom] using quotientHeadSquare_of_rowHom a φ hφ₀
  have hApp :
      app' (quotientRowHomOfRowHom a φ hφ₀) ((n : ℕ) + 1) =
        app' β (n : ℕ) := by
    simp [quotientRowHomOfRowHom, β]
  rw [hApp]
  simpa [β, doubleDeltaRowHom, quotient_rightEq_eq] using hφn

/-- Helper for Lemma 13.27.5: a ladder with right endpoint fixed and left endpoint map
`a : A ⟶ A'` transports the recursively defined Yoneda class by postcomposition with
`Ext.mk₀ a`. -/
private theorem toExt_comp_mk₀_of_rowHom {A A' B : C} {n : ℕ+}
    {E : YonedaExtension A B n} {F : YonedaExtension A' B n}
    (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
    (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm)
    (hφn : app' φ ((n : ℕ) + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    (toExt E).comp (Ext.mk₀ a) (add_zero (n : ℕ)) = toExt F := by
  -- Route correction: recurse on the Yoneda degree, keeping the quotient-row bridge explicit so
  -- the successor step is a short-exact naturality calculation followed by the induction
  -- hypothesis on quotient rows.
  revert A A' B E F a φ hφ₀ hφn
  refine @PNat.recOn n
    (fun m ↦
      ∀ {A A' B : C}
        {E : YonedaExtension A B m} {F : YonedaExtension A' B m}
        (a : A ⟶ A') (φ : E.obj ⟶ F.obj)
        (hφ₀ : app' φ 0 = eqToHom E.leftEq ≫ a ≫ eqToHom F.leftEq.symm)
        (hφright : app' φ ((m : ℕ) + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)),
        (toExt E).comp (Ext.mk₀ a) (add_zero (m : ℕ)) = toExt F)
    ?_ ?_
  · intro A A' B E F a φ hφ₀ hφright
    -- Proof comment: degree `1` is the short-exact naturality statement proved separately.
    simpa using
      (toExt_comp_mk₀_of_rowHom_one
        a φ hφ₀ hφright)
  · intro n ih A A' B E F a φ hφ₀ hφright
    have hHeadClass :
        (firstShortExact E).extClass.comp (Ext.mk₀ a) (add_zero 1) =
          (Ext.mk₀ (quotientMapOfRowHom a φ hφ₀)).comp
            (firstShortExact F).extClass (zero_add 1) := by
      let ψ : ShortComplex.cokernelSequence E.firstMap ⟶
          ShortComplex.cokernelSequence F.firstMap :=
        ShortComplex.homMk
          a
          (app' φ 1 (by omega))
          (quotientMapOfRowHom a φ hφ₀)
          (by
            -- Proof comment: the first square of the ladder is the normalized head square.
            simpa using (firstMap_naturality_of_rowHom a φ hφ₀).symm)
          (by
            -- Proof comment: the second square is the defining property of the descended cokernel
            -- map.
            simpa using (cokernel_π_comp_quotientMapOfRowHom a φ hφ₀).symm)
      -- Proof comment: the head short exact sequence class is natural with respect to this square.
      simpa [ψ] using
        (ShortComplex.ShortExact.extClass_naturality
          (firstShortExact E)
          (firstShortExact F)
          ψ)
    have hQuotient :
        (toExt (quotient E)).comp
            (Ext.mk₀ (quotientMapOfRowHom a φ hφ₀))
            (add_zero (n : ℕ)) =
          toExt (quotient F) := by
      -- Proof comment: the quotient-row ladder has the descended cokernel map on the left and
      -- still fixes the right endpoint, so the induction hypothesis applies directly.
      exact ih
        (quotientMapOfRowHom a φ hφ₀)
        (quotientRowHomOfRowHom a φ hφ₀)
        (quotientRowHomOfRowHom_leftEndpoint a φ hφ₀)
        (quotientRowHomOfRowHom_rightEndpoint a φ hφ₀ hφright)
    have hFinish :
        ((toExt (quotient E)).comp
          (Ext.mk₀ (quotientMapOfRowHom a φ hφ₀))
          (add_zero (n : ℕ))).comp
          (firstShortExact F).extClass rfl = toExt F := by
      rw [hQuotient]
      simpa using (toExt_succ F).symm
    have hAssoc :
        (toExt (quotient E)).comp
          ((Ext.mk₀ (quotientMapOfRowHom a φ hφ₀)).comp
            (firstShortExact F).extClass (zero_add 1))
          rfl =
        ((toExt (quotient E)).comp
          (Ext.mk₀ (quotientMapOfRowHom a φ hφ₀))
          (add_zero (n : ℕ))).comp
          (firstShortExact F).extClass rfl := by
      simpa using
        (Ext.comp_assoc_of_second_deg_zero
          (toExt (quotient E))
          (Ext.mk₀ (quotientMapOfRowHom a φ hφ₀))
          (firstShortExact F).extClass
          rfl).symm
    have hStep1 :
        (toExt E).comp (Ext.mk₀ a) (add_zero ((n + 1 : ℕ))) =
          (toExt (quotient E)).comp
            ((firstShortExact E).extClass.comp (Ext.mk₀ a) (add_zero 1))
            rfl := by
      rw [toExt_succ]
      simpa using
        (Ext.comp_assoc_of_third_deg_zero
          (toExt (quotient E))
          (firstShortExact E).extClass
          (Ext.mk₀ a)
          rfl)
    have hStep2 :
        (toExt (quotient E)).comp
            ((firstShortExact E).extClass.comp (Ext.mk₀ a) (add_zero 1))
            rfl =
          (toExt (quotient E)).comp
            ((Ext.mk₀ (quotientMapOfRowHom a φ hφ₀)).comp
              (firstShortExact F).extClass (zero_add 1))
            rfl := by
      exact congrArg (fun t ↦ (toExt (quotient E)).comp t rfl) hHeadClass
    exact hStep1.trans (hStep2.trans (hAssoc.trans hFinish))

/-- Helper for Lemma 13.27.5: an endpoint-fixing ladder should preserve the recursively defined
`Ext` class. -/
private theorem toExt_eq_of_endpoint_ladder {n : ℕ+} {E F : YonedaExtension A B n}
    (φ : E ⟶ F)
    (hφ₀ : app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm))
    (hφn : app' φ.hom ((n : ℕ) + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)) :
    toExt E = toExt F := by
  -- Route correction: rather than recursing separately on endpoint-fixing ladders, specialize the
  -- general row-morphism naturality theorem to the identity map on the left endpoint.
  have hTransport :
      (toExt E).comp (Ext.mk₀ (𝟙 A)) (add_zero (n : ℕ)) = toExt F := by
    simpa [Category.assoc] using
      (toExt_comp_mk₀_of_rowHom (𝟙 A) φ.hom
        (by simpa [Category.assoc] using hφ₀)
        hφn)
  simpa using (Ext.comp_mk₀_id (toExt E)).symm.trans hTransport

/-- Helper for Lemma 13.27.5: equivalent Yoneda extensions define the same `Ext` class because
both compare to a common refinement through endpoint-fixing ladders. -/
private theorem equivalent_implies_toExt_eq {n : ℕ+} {E F : YonedaExtension A B n}
    (h : Equivalent E F) :
    toExt E = toExt F := by
  rcases h with ⟨G, φ, ψ, hφ, hψ⟩
  rcases hφ with ⟨hφ₀, hφn⟩
  rcases hψ with ⟨hψ₀, hψn⟩
  -- Compare both extensions with the common refinement `G`.
  calc
    toExt E = toExt G := by
      symm
      exact toExt_eq_of_endpoint_ladder φ hφ₀ hφn
    _ = toExt F := by
      exact toExt_eq_of_endpoint_ladder ψ hψ₀ hψn

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

/-- Helper for Lemma 13.27.5: the morphism underlying `toExt E` is normalized into the same
single-complex spelling used by bounded roofs. -/
private noncomputable def toExtDerivedMap {n : ℕ+} [HasDerivedCategory C]
    {X Y : C} (E : YonedaExtension X Y (n + 1)) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X) :=
  extDerivedMap (toExt E)

/-- Helper for Lemma 13.27.5: a positive-degree Yoneda extension already determines a bounded roof
for its normalized derived `Ext` class, so the converse direction can stay inside bounded
cochain-complex data instead of reopening localization fractions. -/
private theorem boundedRoofOfYonedaClass {n : ℕ+} [HasDerivedCategory C]
    {X Y : C} (E : YonedaExtension X Y (n + 1)) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ))) (_ : K.IsStrictlyLE 0)
      (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
      (_ : IsIso (DerivedCategory.Q.map s))
      (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X),
      extDerivedMap (toExt E) =
        inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
  -- Proof comment: specialize the generic bounded-roof representation theorem to the `Ext` class
  -- carried by `E`.
  simpa [extDerivedMap] using
    (boundedRoofOfExtClass ((n + 1 : ℕ)) (toExt E))

/-- Helper for Lemma 13.27.5: once one bounded roof is fixed for a class `x`, the remaining task
is to compare its realization directly with any Yoneda row having `toExt = x`. -/
private noncomputable abbrev sharedRoofRealization {n : ℕ+}
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : extDerivedMap x =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g) :
    YonedaExtension X Y (n + 1) :=
  realizeBoundedRoof
    (toExt_surjectiveAux n)
    x hKge s hs g hg

/-- Helper for Lemma 13.27.5: once one bounded roof is fixed for a class `x`, the remaining task
is to compare its realization directly with any Yoneda row having `toExt = x`. -/
private theorem realizeBoundedRoof_toExt_eq_target {n : ℕ+}
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : extDerivedMap x =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g)
    {E : YonedaExtension X Y (n + 1)}
    (hx : x = toExt E) :
    toExt (sharedRoofRealization x hKge s hs g hg) = toExt E := sorry

/-- Helper for Lemma 13.27.5: after an endpoint-fixing ladder from the shared bounded-roof
realization to a target row is built, the `Ext`-class comparison is already forced. -/
private theorem sharedRoofLadder_forces_toExt {n : ℕ+}
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : extDerivedMap x =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g)
    {E : YonedaExtension X Y (n + 1)}
    (hx : x = toExt E)
    (φ : sharedRoofRealization x hKge s hs g hg ⟶ E)
    (hφ₀ : app' φ.hom 0 =
      eqToHom
        ((sharedRoofRealization x hKge s hs g hg).leftEq.trans
          E.leftEq.symm))
    (hφright : app' φ.hom (((n + 1 : ℕ+) : ℕ) + 1) =
      eqToHom
        ((sharedRoofRealization x hKge s hs g hg).rightEq.trans
          E.rightEq.symm)) :
    x = toExt E := by
  -- Proof comment: the realization has class `x`, and an endpoint-fixing ladder preserves the
  -- recursively defined Yoneda class.
  calc
    x =
      toExt (sharedRoofRealization x hKge s hs g hg) := by
          symm
          exact realizeBoundedRoof_toExt
            (toExt_surjectiveAux n)
            x hKge s hs g hg
    _ = toExt E := by
      exact toExt_eq_of_endpoint_ladder φ hφ₀ hφright

/-- Helper for Lemma 13.27.5: once a tail-row morphism into `E.obj.δ₀` is chosen, it can be
spliced with a compatible head map to an endpoint-fixing ladder into `E`. -/
private theorem prependRowHomOfQuotientRowHom {X : C} (u : A ⟶ X) [Mono u] {n : ℕ+}
    (F : YonedaExtension (cokernel u) B n)
    (E : YonedaExtension A B (n + 1))
    (α : X ⟶ E.obj.obj' 1)
    (hα : u ≫ α = E.firstMap)
    (φ : F.obj ⟶ E.obj.δ₀)
    (hφα :
      prependNextMap u F ≫ app' φ 1 =
        α ≫ E.obj.map' 1 2 (by decide) (two_le_length (n + 1)))
    (hφright : app' φ ((n : ℕ) + 1) = eqToHom (F.rightEq.trans E.rightEq.symm)) :
    ∃ ψ : prependYonedaExtension u F ⟶ E,
      app' ψ.hom 0 =
          eqToHom ((prependYonedaExtension u F).leftEq.trans E.leftEq.symm) ∧
        app' ψ.hom (((n + 1 : ℕ+) : ℕ) + 1) =
          eqToHom ((prependYonedaExtension u F).rightEq.trans E.rightEq.symm) := sorry

/-- Helper for Lemma 13.27.5: once one bounded roof is fixed for a class `x`, its chosen
realization is equivalent to any Yoneda row having `toExt = x`. This matches the source proof,
which only constructs a common refinement from the shared roof data. -/
private theorem equivalent_realizeBoundedRoof_of_toExt_eq {n : ℕ+}
    (ih : ∀ {X Y : C} (E E' : YonedaExtension X Y n), Equivalent E E' ↔ toExt E = toExt E')
    {X Y : C} [HasDerivedCategory C]
    (x : Ext Y X (n + 1))
    {K : CochainComplex C ℤ}
    (hKge : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)))
    (s : K ⟶ (CochainComplex.singleFunctor C 0).obj Y)
    (hs : IsIso (DerivedCategory.Q.map s))
    (g : K ⟶ (CochainComplex.singleFunctor C (-((n + 1 : ℕ) : ℤ))).obj X)
    (hg : extDerivedMap x =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g)
    {E : YonedaExtension X Y (n + 1)}
    (hx : x = toExt E) :
    Equivalent
      (sharedRoofRealization x hKge s hs g hg)
      E := sorry

/-- Helper for Lemma 13.27.5: in positive degree, the converse should factor equality in `Ext`
through one realized common denominator roof and then compare that realization to both Yoneda
rows by endpoint-fixing ladders. -/
private theorem toExt_eq_implies_equivalent_succ {n : ℕ+}
    (ih : ∀ {X Y : C} (E E' : YonedaExtension X Y n), Equivalent E E' ↔ toExt E = toExt E')
    {X Y : C} {E E' : YonedaExtension X Y (n + 1)}
    (h : toExt E = toExt E') :
    Equivalent E E' := sorry

/-- Equality in `Ext` detects Yoneda equivalence for the canonical comparison map
`YonedaExtension.toExt`. -/
private theorem equivalent_iff_toExt_eqAux (n : ℕ+) :
    ∀ {X Y : C} (E E' : YonedaExtension X Y n),
      Equivalent E E' ↔ toExt E = toExt E' := sorry

/-- Equality in `Ext` detects Yoneda equivalence for the canonical comparison map
`YonedaExtension.toExt`. -/
theorem equivalent_iff_toExt_eq {n : ℕ+} (E E' : YonedaExtension A B n) :
    Equivalent E E' ↔ toExt E = toExt E' :=
  equivalent_iff_toExt_eqAux n E E'

/-- Lemma 13.27.5: for each positive degree `n`, the canonical comparison map from degree `n`
Yoneda extensions of `B` by `A` to `Ext B A n` is surjective, and two such Yoneda extensions are
equivalent if and only if they define the same `Ext` class. -/
@[stacks 06XU]
theorem toExt_spec {n : ℕ+} :
    Function.Surjective (toExt : YonedaExtension A B n → Ext B A n) ∧
      ∀ E E' : YonedaExtension A B n, Equivalent E E' ↔ toExt E = toExt E' := by
  refine ⟨toExt_surjective n, ?_⟩
  intro E E'
  exact equivalent_iff_toExt_eq E E'

end YonedaExtension

end CategoryTheory
