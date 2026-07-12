import Mathlib.Data.List.TFAE
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import StacksProject_2024.Chap12.Lemma_12_19_12
import Mathlib.Tactic.StacksAttribute

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B : FilteredObject C}

/-- Helper for Lemma 12.19.13: the canonical short complex
`0 ⟶ F^(p + 1) X ⟶ F^p X ⟶ gr^p(X) ⟶ 0`. -/
abbrev stageShortComplex (X : FilteredObject C) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (X.filtration.stageInclusion p) (cokernel.π (X.filtration.stageInclusion p))
    (cokernel.condition _)

/-- Helper for Lemma 12.19.13: the consecutive filtration-stage row is short exact. -/
theorem stage_shortExact (X : FilteredObject C) (p : ℤ) :
    (stageShortComplex X p).ShortExact := by
  -- This is exactly the universal short exact sequence attached to a cokernel of a mono.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  exact ShortComplex.exact_cokernel (X.filtration.stageInclusion p)

/-- Helper for Lemma 12.19.13: if the ambient morphism is monic, then every stage map is monic. -/
theorem stageMap_mono_of_hom_mono {X Y : FilteredObject C} (g : X ⟶ Y) [Mono g.hom] (p : ℤ) :
    Mono (stageMap g p) := by
  -- Postcompose with the monic stage inclusion into `Y` and cancel that inclusion afterward.
  have hcomp : Mono (stageMap g p ≫ (Y.filtration.obj p).arrow) := by
    rw [stageMap_comm]
    infer_instance
  exact mono_of_mono (stageMap g p) (Y.filtration.obj p).arrow

/-- Helper for Lemma 12.19.13: the four-term row
`0 ⟶ F^(p + 1) X ⟶ F^p X ⟶ gr^p(X)` is exact. -/
theorem stageHeadZeroComposableArrows_exact (X : FilteredObject C) (p : ℤ) :
    (ComposableArrows.mk₃
      (0 : 0 ⟶ F^{p + 1} X)
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p))).Exact := by
  have hZero :
      (ShortComplex.mk
        (0 : 0 ⟶ F^{p + 1} X)
        (X.filtration.stageInclusion p)
        (by simp)).Exact := by
    -- The left endpoint exactness is exactly monicity of the stage inclusion.
    exact
      ((ShortComplex.mk
        (0 : 0 ⟶ F^{p + 1} X)
        (X.filtration.stageInclusion p)
        (by simp)).exact_iff_mono (by simp)).2 inferInstance
  -- Attach the canonical short exact stage row to the initial zero map.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (0 : 0 ⟶ F^{p + 1} X)
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p)))
    (h := by simpa [stageShortComplex] using hZero.exact_toComposableArrows)
    (h₀ := by simpa [stageShortComplex] using (stage_shortExact X p).exact.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: the four-term row
`F^(p + 1) X ⟶ F^p X ⟶ gr^p(X) ⟶ 0` is exact. -/
theorem stageTailZeroComposableArrows_exact (X : FilteredObject C) (p : ℤ) :
    (ComposableArrows.mk₃
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p))
      (0 : gr^{p} X ⟶ 0)).Exact := by
  have hZero :
      (ShortComplex.mk
        (cokernel.π (X.filtration.stageInclusion p))
        (0 : gr^{p} X ⟶ 0)
        (by simp)).Exact := by
    -- The right endpoint exactness is exactly epicity of the graded projection.
    exact
      ((ShortComplex.mk
        (cokernel.π (X.filtration.stageInclusion p))
        (0 : gr^{p} X ⟶ 0)
        (by simp)).exact_iff_epi (by simp)).2 inferInstance
  -- Attach the terminal zero map to the canonical short exact stage row.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p))
      (0 : gr^{p} X ⟶ 0))
    (h := by simpa [stageShortComplex] using (stage_shortExact X p).exact.exact_toComposableArrows)
    (h₀ := by simpa [stageShortComplex] using hZero.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: the left square of the canonical stage-row morphism commutes by
filtration preservation. -/
theorem stageShortComplexMap_left_comm {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ) :
    stageMap g (p + 1) ≫ Y.filtration.stageInclusion p =
      X.filtration.stageInclusion p ≫ stageMap g p := by
  -- The left square is exactly the naturality square for consecutive stage inclusions.
  exact (stageInclusion_naturality g p).symm

/-- Helper for Lemma 12.19.13: the right square of the canonical stage-row morphism commutes by
the defining property of the induced map on graded pieces. -/
theorem stageShortComplexMap_right_comm {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ) :
    stageMap g p ≫ cokernel.π (Y.filtration.stageInclusion p) =
      cokernel.π (X.filtration.stageInclusion p) ≫ gradedPieceMap g p := by
  -- The graded-piece map is the universal cokernel map induced by the stage square.
  simp [gradedPieceMap]

/-- Helper for Lemma 12.19.13: a filtered morphism induces a morphism between the canonical stage
rows. -/
def stageShortComplexMap {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ) :
    stageShortComplex X p ⟶ stageShortComplex Y p :=
  ShortComplex.homMk
    (stageMap g (p + 1))
    (stageMap g p)
    (gradedPieceMap g p)
    (stageShortComplexMap_left_comm g p)
    (stageShortComplexMap_right_comm g p)

/-- Helper for Lemma 12.19.13: once a filtration reaches the zero subobject, all later stages are
also zero. -/
theorem filtration_eq_bot_of_le {X : FilteredObject C} {p q : ℤ}
    (hpq : p ≤ q) (hp : X.filtration p = ⊥) : X.filtration q = ⊥ := by
  -- Antitonicity pushes the zero stage forward along the decreasing filtration.
  apply bot_unique
  simpa [hp] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 12.19.13: once a filtration reaches the whole object, all earlier stages are
also the whole object. -/
theorem filtration_eq_top_of_le {X : FilteredObject C} {p q : ℤ}
    (hpq : p ≤ q) (hq : X.filtration q = ⊤) : X.filtration p = ⊤ := by
  -- Antitonicity pulls the top stage backward along the decreasing filtration.
  apply top_unique
  simpa [hq] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 12.19.13: a zero filtration stage is the zero subobject written in canonical
`Subobject.mk` form. -/
theorem stage_eq_mk_zero_of_eq_bot (X : FilteredObject C) (p : ℤ) (hp : X.filtration p = ⊥) :
    X.filtration.obj p = Subobject.mk (0 : (0 : C) ⟶ X.obj) := by
  -- Rewrite the bottom subobject into the explicit zero-arrow model expected by `isoOfEqMk`.
  simpa [Subobject.bot_eq_zero] using hp

/-- Helper for Lemma 12.19.13: a zero filtration stage is canonically isomorphic to the zero
object. -/
noncomputable def stageIsoZeroOfEqBot (X : FilteredObject C) (p : ℤ) (hp : X.filtration p = ⊥) :
    F^{p} X ≅ 0 :=
  Subobject.isoOfEqMk (X.filtration.obj p) (0 : (0 : C) ⟶ X.obj) (stage_eq_mk_zero_of_eq_bot X p hp)

/-- Helper for Lemma 12.19.13: a stage equal to the zero subobject has zero ambient object. -/
theorem stage_isZero_of_eq_bot (X : FilteredObject C) (p : ℤ) (hp : X.filtration p = ⊥) :
    IsZero (F^{p} X) := by
  -- Transport the standard zero-object witness across the canonical zero-stage isomorphism.
  exact Limits.IsZero.of_iso (Limits.isZero_zero C) (stageIsoZeroOfEqBot X p hp)

/-- Helper for Lemma 12.19.13: if both source and target stages are zero, the induced stage map is
automatically an isomorphism. -/
theorem stageMap_isIso_of_eq_bot {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ)
    (hX : X.filtration p = ⊥) (hY : Y.filtration p = ⊥) : IsIso (stageMap g p) := by
  -- Any morphism between zero objects is an isomorphism, so the zero-stage map is invertible.
  let hZX : IsZero (F^{p} X) := stage_isZero_of_eq_bot X p hX
  let hZY : IsZero (F^{p} Y) := stage_isZero_of_eq_bot Y p hY
  exact hZX.isIso hZY (stageMap g p)

/-- Helper for Lemma 12.19.13: an isomorphism on associated graded objects is an isomorphism on
each graded piece after evaluation at the corresponding degree. -/
theorem gradedPieceMap_isIso_of_associatedGradedMap_isIso {X Y : FilteredObject C} (g : X ⟶ Y)
    [IsIso (associatedGradedMap g)] (p : ℤ) : IsIso (gradedPieceMap g p) := by
  -- Evaluate the associated-graded isomorphism at degree `p`.
  change IsIso ((GradedObject.eval p).map (associatedGradedMap g))
  infer_instance

/-- Helper for Lemma 12.19.13: in the canonical short exact stage rows, an isomorphism on
`F^(p + 1)` together with an isomorphism on `gr^p` forces an isomorphism on `F^p`. -/
theorem stageMap_isIso_of_stageMap_succ_and_gradedPiece_isIso
    {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ)
    [IsIso (stageMap g (p + 1))] [IsIso (gradedPieceMap g p)] :
    IsIso (stageMap g p) := by
  -- This is the textbook five-lemma step on the short exact rows
  -- `0 ⟶ F^(p + 1) ⟶ F^p ⟶ gr^p ⟶ 0`.
  let ψ : stageShortComplex X p ⟶ stageShortComplex Y p := stageShortComplexMap g p
  change IsIso ψ.τ₂
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ψ
    (stage_shortExact X p)
    (stage_shortExact Y p)
    (by
      dsimp [ψ, stageShortComplexMap]
      infer_instance)
    (by
      dsimp [ψ, stageShortComplexMap]
      infer_instance)

/-- Helper for Lemma 12.19.13: if the underlying morphism is an isomorphism and the associated
graded map is an isomorphism, then every filtration-stage map is an isomorphism. -/
theorem stageMap_isIso_of_hom_iso_of_graded_iso {X Y : FilteredObject C} (g : X ⟶ Y)
    (m : ℤ) (hXm : X.filtration m = ⊥) (hYm : Y.filtration m = ⊥)
    [IsIso g.hom] [IsIso (associatedGradedMap g)] (p : ℤ) :
    IsIso (stageMap g p) := by
  by_cases hpm : p ≤ m
  · let n : ℕ := Int.toNat (m - p)
    have hdesc : ∀ n : ℕ, IsIso (stageMap g (m - Int.ofNat n)) := by
      intro n
      induction n with
      | zero =>
          -- Start the descent at the common zero filtration stage.
          simpa using
            (stageMap_isIso_of_eq_bot g (m - Int.ofNat 0) (by simpa using hXm)
              (by simpa using hYm) : IsIso (stageMap g (m - Int.ofNat 0)))
      | succ n ih =>
          -- Move one step down in the filtration using the short exact stage rows.
          have hsucc :
              IsIso (stageMap g ((m - Int.ofNat (Nat.succ n)) + 1)) := by
            let q : ℤ := (m - Int.ofNat (Nat.succ n)) + 1
            change IsIso (stageMap g q)
            have hq : q = m - Int.ofNat n := by
              dsimp [q]
              change m - (Int.ofNat n + 1) + 1 = m - Int.ofNat n
              omega
            haveI : IsIso (stageMap g (m - Int.ofNat n)) := ih
            rw [hq]
            infer_instance
          have hgraded :
              IsIso (gradedPieceMap g (m - Int.ofNat (Nat.succ n))) := by
            simpa using
              gradedPieceMap_isIso_of_associatedGradedMap_isIso g
                (m - Int.ofNat (Nat.succ n))
          letI : IsIso (stageMap g ((m - Int.ofNat (Nat.succ n)) + 1)) := hsucc
          letI : IsIso (gradedPieceMap g (m - Int.ofNat (Nat.succ n))) := hgraded
          exact stageMap_isIso_of_stageMap_succ_and_gradedPiece_isIso g
            (m - Int.ofNat (Nat.succ n))
    have hp' : m - Int.ofNat n = p := by
      dsimp [n]
      change m - ((m - p).toNat : Int) = p
      have hnonneg : 0 ≤ m - p := sub_nonneg.mpr hpm
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    -- Rewrite `p` in the stable `m - n` normal form chosen for the descent.
    rw [hp'.symm]
    exact hdesc n
  · have hmp : m ≤ p := le_of_not_ge hpm
    have hXp : X.filtration p = ⊥ :=
      filtration_eq_bot_of_le hmp hXm
    have hYp : Y.filtration p = ⊥ :=
      filtration_eq_bot_of_le hmp hYm
    -- Past the common zero stage, every later stage is again zero.
    simpa using stageMap_isIso_of_eq_bot g p hXp hYp

/-- Helper for Lemma 12.19.13: stagewise isomorphisms upgrade an underlying isomorphism to an
isomorphism of filtered objects. -/
theorem isIso_of_hom_iso_of_stageMap_isIso {X Y : FilteredObject C} (g : X ⟶ Y) [IsIso g.hom]
    (hstage : ∀ p : ℤ, IsIso (stageMap g p)) : IsIso g := by
  let gInv : Y ⟶ X :=
    { hom := inv g.hom
      preserves := by
        intro p
        let s : F^{p} Y ⟶ F^{p} X := by
          haveI : IsIso (stageMap g p) := hstage p
          exact inv (stageMap g p)
        haveI : IsIso (stageMap g p) := hstage p
        -- The inverse stage map gives the factorization of `inv g.hom` through `F^p X`.
        rw [Subobject.factors_iff]
        refine ⟨s, ?_⟩
        calc
          s ≫ (X.filtration.obj p).arrow
              = s ≫
                  (((X.filtration.obj p).arrow ≫ g.hom) ≫ inv g.hom) := by
                    simp [Category.assoc]
          _ = s ≫
                ((stageMap g p ≫ (Y.filtration.obj p).arrow) ≫ inv g.hom) := by
                  rw [stageMap_comm]
          _ = (Y.filtration.obj p).arrow ≫ inv g.hom := by
                dsimp [s]
                simp [Category.assoc] }
  refine ⟨⟨gInv, ?_, ?_⟩⟩
  · -- The left inverse identity is checked after forgetting to the ambient category.
    apply FilteredObject.forget.map_injective
    change g.hom ≫ inv g.hom = 𝟙 X.obj
    simp
  · -- The right inverse identity is checked similarly.
    apply FilteredObject.forget.map_injective
    change inv g.hom ≫ g.hom = 𝟙 Y.obj
    simp

/-- Helper for Lemma 12.19.13: pulling back the zero subobject along a monomorphism again gives
the zero subobject. -/
private theorem pullback_bot_eq_bot_of_mono {X Y : C} (u : X ⟶ Y) [Mono u] :
    (Subobject.pullback u).obj (⊥ : Subobject Y) = ⊥ := by
  -- Rewrite the zero subobject as the image of the zero subobject in the source, then use that
  -- pullback is inverse to map along a monomorphism.
  calc
    (Subobject.pullback u).obj (⊥ : Subobject Y)
        = (Subobject.pullback u).obj ((Subobject.map u).obj (⊥ : Subobject X)) := by
            rw [Subobject.map_bot]
    _ = ⊥ := by
          simpa using (Subobject.pullback_map_self u (⊥ : Subobject X))

/-- Helper for Lemma 12.19.13: a zero source filtration stage stays zero after passing to the
filtered coimage. -/
theorem coimage_filtration_eq_bot_of_source_filtration_eq_bot (f : A ⟶ B) {m : ℤ}
    (hAm : A.filtration m = ⊥) : (coimage f).filtration m = ⊥ := by
  -- Rewrite the coimage stage as the image of the stagewise quotient map from `A`.
  rw [show (coimage f).filtration m =
      imageSubobject ((A.filtration m).arrow ≫ Abelian.coimage.π f.hom) by
    simpa [coimage] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (Abelian.coimage.π f.hom) m)]
  rw [hAm]
  simp [Subobject.bot_eq_zero]

/-- Helper for Lemma 12.19.13: a zero target filtration stage stays zero on the literal filtered
image-subobject model. -/
theorem imageSubobject_filtration_eq_bot_of_target_filtration_eq_bot (f : A ⟶ B) {m : ℤ}
    (hBm : B.filtration m = ⊥) :
    (B.subobjectFilteredObject (imageSubobject f.hom)).filtration m = ⊥ := by
  -- Unfold the induced filtration on the literal image subobject and collapse the pullback of the
  -- zero target stage.
  rw [show (B.subobjectFilteredObject (imageSubobject f.hom)).filtration m =
      (Subobject.pullback (imageSubobject f.hom).arrow).obj (B.filtration m) by
    rfl]
  rw [hBm]
  simpa using pullback_bot_eq_bot_of_mono (imageSubobject f.hom).arrow

/-- Helper for Lemma 12.19.13: a zero target filtration stage stays zero after transporting the
literal image-subobject model to the chosen filtered image owner. -/
theorem image_filtration_eq_bot_of_target_filtration_eq_bot (f : A ⟶ B) {m : ℤ}
    (hBm : B.filtration m = ⊥) : (image f).filtration m = ⊥ := by
  -- Transport the zero stage across the defining isomorphism from the image subobject model.
  have hsub :
      (B.subobjectFilteredObject (imageSubobject f.hom)).filtration m = ⊥ :=
    imageSubobject_filtration_eq_bot_of_target_filtration_eq_bot f hBm
  simpa [image, hsub]

/-- Helper for Lemma 12.19.13: the underlying morphism of the filtered coimage-image comparison is
the usual abelian coimage-image comparison, hence an isomorphism. -/
theorem coimageImageComparison_hom_isIso (f : A ⟶ B) :
    IsIso (coimageImageComparison f).hom := by
  -- Reduce to the ambient abelian coimage-image comparison.
  rw [coimageImageComparison_hom]
  infer_instance

/-- Helper for Lemma 12.19.13: a degreewise associated-graded isomorphism yields a degreewise
graded-piece isomorphism after evaluation. -/
theorem gradedPieceMap_isIso_of_associatedGradedMap_isIso'
    {X Y : FilteredObject C} (g : X ⟶ Y) (hg : IsIso (associatedGradedMap g)) (p : ℤ) :
    IsIso (gradedPieceMap g p) := by
  -- Evaluate the isomorphism of graded objects at the component `p`.
  letI : IsIso (associatedGradedMap g) := hg
  simpa using gradedPieceMap_isIso_of_associatedGradedMap_isIso g p

/-- Helper for Lemma 12.19.13: the map on filtration stages preserves composition. -/
theorem stageMap_comp
    {X Y Z : FilteredObject C} (g : X ⟶ Y) (h : Y ⟶ Z) (p : ℤ) :
    stageMap (g ≫ h) p = stageMap g p ≫ stageMap h p := by
  -- Compare both stage maps after postcomposing with the mono inclusion into the target stage.
  exact (cancel_mono (Z.filtration.obj p).arrow).1 (by
    calc
      stageMap (g ≫ h) p ≫ (Z.filtration.obj p).arrow
          = (X.filtration.obj p).arrow ≫ (g ≫ h).hom := by rw [stageMap_comm]
      _ = ((X.filtration.obj p).arrow ≫ g.hom) ≫ h.hom := by simp [Category.assoc]
      _ = (stageMap g p ≫ (Y.filtration.obj p).arrow) ≫ h.hom := by rw [stageMap_comm]
      _ = stageMap g p ≫ (stageMap h p ≫ (Z.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap g p ≫ stageMap h p) ≫ (Z.filtration.obj p).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 12.19.13: the map on graded pieces preserves composition. -/
theorem gradedPieceMap_comp
    {X Y Z : FilteredObject C} (g : X ⟶ Y) (h : Y ⟶ Z) (p : ℤ) :
    gradedPieceMap (g ≫ h) p = gradedPieceMap g p ≫ gradedPieceMap h p := by
  -- Compare both graded maps after precomposing with the cokernel projection of `gr^p(X)`.
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [FilteredObject.Hom.gradedPieceMap, Category.assoc, stageMap_comp])

/-- Helper for Lemma 12.19.13: the associated-graded functor preserves zero composites. -/
theorem associatedGradedMap_comp_zero
    {X Y Z : FilteredObject C} (g : X ⟶ Y) (h : Y ⟶ Z) (hcomp : g ≫ h = 0) :
    associatedGradedMap g ≫ associatedGradedMap h = 0 := by
  -- Check the composite after evaluating every graded degree.
  ext p
  simpa [associatedGradedMap] using gradedPieceMap_comp_zero g h hcomp p

/-- Helper for Lemma 12.19.13: for finite filtrations, an isomorphism on associated graded pieces
forces the filtered coimage-image comparison itself to be an isomorphism. -/
theorem coimageImageComparison_isIso_of_associatedGradedMap_isIso
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    [IsIso (associatedGradedMap (coimageImageComparison f))] :
    IsIso (coimageImageComparison f) := by
  -- Route correction: follow the textbook descending induction from one common zero stage for
  -- `coim(f)` and `im(f)`.
  rcases hA with ⟨_, mA, _, hmA⟩
  rcases hB with ⟨_, mB, _, hmB⟩
  let m : ℤ := max mA mB
  have hAm : A.filtration m = ⊥ := by
    exact filtration_eq_bot_of_le (X := A) (by omega) hmA
  have hBm : B.filtration m = ⊥ := by
    exact filtration_eq_bot_of_le (X := B) (by omega) hmB
  have hcoim : (coimage f).filtration m = ⊥ :=
    coimage_filtration_eq_bot_of_source_filtration_eq_bot f hAm
  have himage : (image f).filtration m = ⊥ :=
    image_filtration_eq_bot_of_target_filtration_eq_bot f hBm
  letI : IsIso (coimageImageComparison f).hom := coimageImageComparison_hom_isIso f
  have hstage : ∀ p : ℤ, IsIso (stageMap (coimageImageComparison f) p) := by
    intro p
    -- Descend from the common zero stage using the existing five-lemma step.
    exact stageMap_isIso_of_hom_iso_of_graded_iso (coimageImageComparison f) m hcoim himage p
  -- Once every stage map is invertible, the morphism is an isomorphism of filtered objects.
  exact isIso_of_hom_iso_of_stageMap_isIso (coimageImageComparison f) hstage

/-- Helper for Lemma 12.19.13: the literal quotient by `kernelSubobject f.hom` has the same
underlying object as the public filtered coimage of `f`. -/
private noncomputable def quotientKernelIsoCoimage (f : A ⟶ B) :
    cokernel (kernelSubobject f.hom).arrow ≅ Abelian.coimage f.hom :=
  cokernel.mapIso _ _ (kernelSubobjectIso f.hom) (Iso.refl _)
    (by simpa using (kernelSubobjectIso_hom_arrow (f := f.hom)))

/-- Helper for Lemma 12.19.13: the forward quotient-to-coimage comparison identifies the two
quotient projections from `A`. -/
private theorem quotientKernelIsoCoimage_hom_comm (f : A ⟶ B) :
    cokernel.π (kernelSubobject f.hom).arrow ≫ (quotientKernelIsoCoimage f).hom =
      Abelian.coimage.π f.hom := by
  -- The cokernel comparison is built precisely to transport the literal quotient projection to
  -- the canonical abelian coimage projection.
  simp [quotientKernelIsoCoimage]

/-- Helper for Lemma 12.19.13: the inverse quotient-to-coimage comparison recovers the literal
quotient projection. -/
private theorem quotientKernelIsoCoimage_inv_comm (f : A ⟶ B) :
    Abelian.coimage.π f.hom ≫ (quotientKernelIsoCoimage f).inv =
      cokernel.π (kernelSubobject f.hom).arrow := by
  -- This is the same cokernel-owner comparison in the opposite direction.
  simp [quotientKernelIsoCoimage]

/-- Helper for Lemma 12.19.13: postcomposing an epimorphism does not change the image subobject.
-/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : C} (g : X ⟶ Y) [Epi g] (h : Y ⟶ Z) :
    imageSubobject (g ≫ h) = imageSubobject h := by
  -- Replace the image of the composite by the image of the restriction through `imageSubobject g`,
  -- then use that an epimorphism has top image.
  calc
    imageSubobject (g ≫ h) = imageSubobject ((imageSubobject g).arrow ≫ h) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction g h]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ h) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ h))
        (Limits.imageSubobject_eq_top_of_epi g)
    _ = imageSubobject h := by
      simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) h

/-- Helper for Lemma 12.19.13: an ambient codomain isomorphism transports image-factorizations of
the same map. -/
private theorem imageSubobject_factors_of_iso_comp {X Y Y' : C} (k : X ⟶ Y) (e : Y ≅ Y')
    {k' : X ⟶ Y'} (hk : k ≫ e.hom = k') :
    (imageSubobject k').Factors ((imageSubobject k).arrow ≫ e.hom) := by
  -- Compare both images after reintroducing the epimorphic factorization of `k`.
  rw [Subobject.factors_iff]
  refine ⟨factorThruImageSubobject ((imageSubobject k).arrow ≫ e.hom) ≫ Subobject.ofLE _ _ ?_, ?_⟩
  · refine le_of_eq ?_
    calc
      imageSubobject ((imageSubobject k).arrow ≫ e.hom)
          = imageSubobject (factorThruImageSubobject k ≫ (imageSubobject k).arrow ≫ e.hom) := by
              symm
              simpa [Category.assoc] using
                (imageSubobject_comp_eq_of_epi (factorThruImageSubobject k)
                  ((imageSubobject k).arrow ≫ e.hom))
      _ = imageSubobject ((factorThruImageSubobject k ≫ (imageSubobject k).arrow) ≫ e.hom) := by
            simp
      _ = imageSubobject (k ≫ e.hom) := by
            rw [imageSubobject_arrow_comp]
      _ = imageSubobject k' := by
            simpa [hk]
  · simp [Category.assoc, Subobject.ofLE_arrow]

/-- Helper for Lemma 12.19.13: the forward quotient-to-coimage comparison preserves the quotient
filtration stagewise. -/
private theorem quotientFilteredObjectKernelIsoCoimage_hom_preserves (f : A ⟶ B) (p : ℤ) :
    ((coimage f).filtration p).Factors
      (((A.quotientFilteredObject (kernelSubobject f.hom)).filtration p).arrow ≫
        (quotientKernelIsoCoimage f).hom) := by
  let k : (A.filtration p : C) ⟶ cokernel (kernelSubobject f.hom).arrow :=
    (A.filtration.obj p).arrow ≫ cokernel.π (kernelSubobject f.hom).arrow
  let k' : (A.filtration p : C) ⟶ Abelian.coimage f.hom :=
    (A.filtration.obj p).arrow ≫ Abelian.coimage.π f.hom
  have hstage :
      (A.quotientFilteredObject (kernelSubobject f.hom)).filtration p = imageSubobject k := by
    -- Rewrite the literal quotient stage as the image of the stage composite into the literal
    -- quotient object.
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π (kernelSubobject f.hom).arrow) p)
  have hstage' : (coimage f).filtration p = imageSubobject k' := by
    -- The public coimage filtration is the analogous quotient filtration by
    -- `Abelian.coimage.π f.hom`.
    simpa [coimage, k'] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (Abelian.coimage.π f.hom) p)
  have hk : k ≫ (quotientKernelIsoCoimage f).hom = k' := by
    -- The ambient quotient/coimage comparison intertwines the two quotient projections.
    simpa [k, k', Category.assoc] using congrArg ((A.filtration.obj p).arrow ≫ ·)
      (quotientKernelIsoCoimage_hom_comm f)
  rw [hstage, hstage']
  exact imageSubobject_factors_of_iso_comp k (quotientKernelIsoCoimage f) hk

/-- Helper for Lemma 12.19.13: the inverse quotient-to-coimage comparison preserves the quotient
filtration stagewise. -/
private theorem quotientFilteredObjectKernelIsoCoimage_inv_preserves (f : A ⟶ B) (p : ℤ) :
    ((A.quotientFilteredObject (kernelSubobject f.hom)).filtration p).Factors
      (((coimage f).filtration p).arrow ≫ (quotientKernelIsoCoimage f).inv) := by
  let k : (A.filtration p : C) ⟶ cokernel (kernelSubobject f.hom).arrow :=
    (A.filtration.obj p).arrow ≫ cokernel.π (kernelSubobject f.hom).arrow
  let k' : (A.filtration p : C) ⟶ Abelian.coimage f.hom :=
    (A.filtration.obj p).arrow ≫ Abelian.coimage.π f.hom
  have hstage :
      (A.quotientFilteredObject (kernelSubobject f.hom)).filtration p = imageSubobject k := by
    -- Use the literal quotient-stage normal form again.
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π (kernelSubobject f.hom).arrow) p)
  have hstage' : (coimage f).filtration p = imageSubobject k' := by
    -- The public coimage stage has the analogous image-subobject description.
    simpa [coimage, k'] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (Abelian.coimage.π f.hom) p)
  have hk : k' ≫ (quotientKernelIsoCoimage f).inv = k := by
    -- The inverse ambient comparison recovers the literal quotient projection.
    simpa [k, k', Category.assoc] using congrArg ((A.filtration.obj p).arrow ≫ ·)
      (quotientKernelIsoCoimage_inv_comm f)
  rw [hstage, hstage']
  exact imageSubobject_factors_of_iso_comp k' (quotientKernelIsoCoimage f).symm hk

/-- Helper for Lemma 12.19.13: the literal quotient model and the public filtered coimage are
isomorphic as filtered objects. -/
private noncomputable def quotientFilteredObjectKernelIsoCoimage (f : A ⟶ B) :
    A.quotientFilteredObject (kernelSubobject f.hom) ≅ coimage f where
  hom :=
    { hom := (quotientKernelIsoCoimage f).hom
      preserves := quotientFilteredObjectKernelIsoCoimage_hom_preserves f }
  inv :=
    { hom := (quotientKernelIsoCoimage f).inv
      preserves := quotientFilteredObjectKernelIsoCoimage_inv_preserves f }
  hom_inv_id := by
    -- The filtered identity is determined by the ambient cokernel comparison identity.
    apply FilteredObject.Hom.ext
    exact (quotientKernelIsoCoimage f).hom_inv_id
  inv_hom_id := by
    -- Likewise for the inverse followed by the forward comparison.
    apply FilteredObject.Hom.ext
    exact (quotientKernelIsoCoimage f).inv_hom_id

/-- Helper for Lemma 12.19.13: the canonical quotient map from `A` to the public filtered coimage.
-/
def toCoimage (f : A ⟶ B) : A ⟶ coimage f :=
  A.toQuotient (kernelSubobject f.hom) ≫ (quotientFilteredObjectKernelIsoCoimage f).hom

/-- Helper for Lemma 12.19.13: the underlying map of `toCoimage f` is `Abelian.coimage.π f.hom`.
-/
@[simp] theorem toCoimage_hom (f : A ⟶ B) :
    (toCoimage f).hom = Abelian.coimage.π f.hom := by
  -- The filtered quotient map followed by the quotient/coimage comparison is the canonical
  -- abelian coimage projection.
  change cokernel.π (kernelSubobject f.hom).arrow ≫ (quotientKernelIsoCoimage f).hom =
    Abelian.coimage.π f.hom
  exact quotientKernelIsoCoimage_hom_comm f

/-- Helper for Lemma 12.19.13: the filtered kernel inclusion followed by `toCoimage f` is zero.
-/
theorem kernelι_comp_toFilteredCoimage (f : A ⟶ B) :
    kernelι f ≫ toCoimage f = 0 := by
  -- Expand `toCoimage f` and reuse the literal quotient-by-kernel zero composite from
  -- Lemma `12.19.12`.
  rw [toCoimage, ← Category.assoc, kernelι_comp_toCoimage]
  simp

/-- Helper for Lemma 12.19.13: the graded kernel-coimage row for the literal quotient owner
transports to the public `toCoimage` row. -/
private def kernelToCoimageShortComplexIso (f : A ⟶ B) (p : ℤ) :
    kernelCoimageShortComplex f p ≅
      (ShortComplex.mk
        (gradedPieceMap (kernelι f) p)
        (gradedPieceMap (toCoimage f) p)
        (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
          (kernelι_comp_toFilteredCoimage f) p)) := by
  let e₃ : gr^{p} (A.quotientFilteredObject (kernelSubobject f.hom)) ≅ gr^{p} (coimage f) :=
    (GradedObject.eval p).mapIso
      ((associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C).mapIso
        (quotientFilteredObjectKernelIsoCoimage f))
  have hright_grad :
      gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫ e₃.hom =
        gradedPieceMap (toCoimage f) p := by
    -- Apply the graded-piece functor to the defining factorization of `toCoimage f`.
    change gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
        gradedPieceMap (quotientFilteredObjectKernelIsoCoimage f).hom p =
      gradedPieceMap (toCoimage f) p
    simpa [toCoimage, gradedPieceMap_comp]
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e₃ ?_ ?_
  · simp [kernelCoimageShortComplex, FilteredObject.subobjectGradedPieceShortComplex]
  · simpa [kernelCoimageShortComplex, FilteredObject.subobjectGradedPieceShortComplex] using
      hright_grad.symm

/-- Helper for Lemma 12.19.13: the public graded kernel-coimage row is short exact after
transporting the literal quotient owner to the public coimage owner. -/
theorem gradedPiece_kernel_toCoimage_shortExact (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)).ShortExact := by
  -- Transport the already-proved literal kernel-coimage row through the quotient/coimage
  -- isomorphism on graded pieces.
  exact ShortComplex.shortExact_of_iso (kernelToCoimageShortComplexIso f p)
    (gradedPiece_kernel_coimage_shortExact f p)

/-- Helper for Lemma 12.19.13: the canonical factorization
`A ⟶ coim(f) ⟶ im(f) ⟶ B` remains the original map after taking the `p`-th graded piece. -/
theorem gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (toCoimage f) p ≫
        gradedPieceMap (coimageImageComparison f) p ≫
          gradedPieceMap (imageInclusion f) p =
      gradedPieceMap f p := by
  -- First identify the filtered factorization with the original morphism, then apply
  -- `gradedPieceMap`.
  have hfactor :
      toCoimage f ≫ coimageImageComparison f ≫ imageInclusion f = f := by
    apply FilteredObject.Hom.ext
    simpa [toCoimage_hom, coimageImageComparison_hom, imageInclusion, Category.assoc] using
      Abelian.coimage_image_factorisation f.hom
  simpa [gradedPieceMap_comp, Category.assoc] using
    congrArg (fun k : A ⟶ B ↦ gradedPieceMap k p) hfactor

/-- Helper for Lemma 12.19.13: the graded kernel map followed by the graded coimage-image path is
zero. -/
theorem gradedPiece_kernel_toCoimage_comp_coimageImageComparison_zero
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (kernelι f) p ≫
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) =
      0 := by
  -- The filtered kernel map already vanishes after the quotient-to-coimage map, so the extra
  -- coimage-image comparison factor preserves the zero composite.
  simpa [Category.assoc, FilteredObject.Hom.gradedPieceMap_comp] using
    gradedPieceMap_comp_zero (kernelι f) (toCoimage f ≫ coimageImageComparison f)
      (by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ coimageImageComparison f) (kernelι_comp_toFilteredCoimage f)) p

/-- Helper for Lemma 12.19.13: the graded sequence
`gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{im} f)`. -/
abbrev kernelSourceImageShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (kernelι f) p)
    (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
    (gradedPiece_kernel_toCoimage_comp_coimageImageComparison_zero f p)

/-- Helper for Lemma 12.19.13: the graded coimage-image path followed by the graded cokernel map
is zero. -/
theorem gradedPiece_coimageImageComparison_comp_imageInclusion_comp_toCokernel_zero
    (f : A ⟶ B) (p : ℤ) :
    (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p) ≫
        gradedPieceMap (toCokernel f) p =
      0 := by
  -- Cancel the epimorphic graded coimage projection and reduce to the usual graded cokernel
  -- relation for `f`.
  letI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  apply (cancel_epi (gradedPieceMap (toCoimage f) p)).1
  calc
    gradedPieceMap (toCoimage f) p ≫
          ((gradedPieceMap (coimageImageComparison f) p ≫
              gradedPieceMap (imageInclusion f) p) ≫
            gradedPieceMap (toCokernel f) p)
        =
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p ≫
          gradedPieceMap (imageInclusion f) p) ≫
        gradedPieceMap (toCokernel f) p := by
          simp [Category.assoc]
    _ = gradedPieceMap f p ≫ gradedPieceMap (toCokernel f) p := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ gradedPieceMap (toCokernel f) p)
              (gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p)
    _ = gradedPieceMap (toCoimage f) p ≫ 0 := by
          simpa using
            gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p

/-- Helper for Lemma 12.19.13: the graded sequence
`gr^p(\operatorname{coim} f) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)`. -/
abbrev coimageTargetCokernelShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
    (gradedPieceMap (toCokernel f) p)
    (gradedPiece_coimageImageComparison_comp_imageInclusion_comp_toCokernel_zero f p)

/-- Helper for Lemma 12.19.13: exactness of
`gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(B)` upgrades the chosen kernel-stage map to the actual kernel of
`gr^p(f)`. -/
noncomputable def kernel_source_target_is_kernel
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceTargetShortComplex f p).Exact) :
    IsLimit
      (KernelFork.ofι
        (gradedPieceMap (kernelι f) p)
        (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)) := by
  let S : ShortComplex C := kernelSourceTargetShortComplex f p
  have hMono : Mono S.f := by
    -- The same left map occurs in the always short exact kernel-coimage row.
    simpa [S, kernelSourceTargetShortComplex, kernelCoimageShortComplex] using
      (gradedPiece_kernel_coimage_shortExact f p).mono_f
  -- Exactness together with monicity identifies the chosen left map as the actual kernel.
  exact ((S.exact_and_mono_f_iff_f_is_kernel).1 ⟨hExact, hMono⟩).some

/-- Helper for Lemma 12.19.13: under kernel-side exactness, the degree-`p` graded piece of the
filtered coimage is the canonical coimage of `gr^p(f)`. -/
theorem gradedPiece_coimage_iso_pointwise_coimage_of_kernel_source_target_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceTargetShortComplex f p).Exact) :
    ∃ e : (coimage f).gradedPiece p ≅ Abelian.coimage (gradedPieceMap f p),
      gradedPieceMap (toCoimage f) p ≫ e.hom =
        Abelian.coimage.π (gradedPieceMap f p) := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  have hS₁_colim :
      IsColimit
        (CokernelCofork.ofπ
          (gradedPieceMap (toCoimage f) p)
          (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
            (kernelι_comp_toFilteredCoimage f) p)) := by
    have hShort := gradedPiece_kernel_toCoimage_shortExact f p
    exact ((S₁.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hShort.exact, hShort.epi_g⟩).some
  let S₂ : ShortComplex C := kernelSourceTargetShortComplex f p
  have hS₂_colim :
      IsColimit
        (CokernelCofork.ofπ
          (Abelian.coimage.π (gradedPieceMap f p))
          (Abelian.comp_coimage_π_eq_zero
            (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p))) := by
    simpa [S₂, kernelSourceTargetShortComplex] using hExact.isColimitCoimage
  let e : (coimage f).gradedPiece p ≅ Abelian.coimage (gradedPieceMap f p) :=
    IsColimit.coconePointUniqueUpToIso hS₁_colim hS₂_colim
  refine ⟨e, ?_⟩
  simpa [e] using
    IsColimit.comp_coconePointUniqueUpToIso_hom hS₁_colim hS₂_colim WalkingParallelPair.one

/-- Helper for Lemma 12.19.13: exactness of
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)` upgrades the chosen graded cokernel map to
the actual cokernel of `gr^p(f)`. -/
noncomputable def source_target_cokernel_is_cokernel
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    IsColimit
      (CokernelCofork.ofπ
        (gradedPieceMap (toCokernel f) p)
        (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p)) := by
  let S : ShortComplex C := sourceTargetCokernelShortComplex f p
  have hEpi : Epi S.g := by
    -- The same right map occurs in the always short exact image-cokernel row.
    simpa [S, sourceTargetCokernelShortComplex, imageCokernelShortComplex] using
      (gradedPiece_image_cokernel_shortExact f p).epi_g
  -- Exactness together with epicity identifies the chosen right map as the actual cokernel.
  exact ((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hExact, hEpi⟩).some

/-- Helper for Lemma 12.19.13: under cokernel-side exactness, the degree-`p` graded piece of the
filtered image is the canonical image of `gr^p(f)`. -/
theorem gradedPiece_image_iso_pointwise_image_of_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    ∃ e : Abelian.image (gradedPieceMap f p) ≅ (image f).gradedPiece p,
      e.hom ≫ gradedPieceMap (imageInclusion f) p =
        Abelian.image.ι (gradedPieceMap f p) := by
  let S₁ : ShortComplex C := imageCokernelShortComplex f p
  have hS₁_limit :
      IsLimit
        (KernelFork.ofι
          (gradedPieceMap (imageInclusion f) p)
          (gradedPieceMap_comp_zero (imageInclusion f) (toCokernel f)
            (imageInclusion_comp_toCokernel f) p)) := by
    have hShort := gradedPiece_image_cokernel_shortExact f p
    exact ((S₁.exact_and_mono_f_iff_f_is_kernel).1 ⟨hShort.exact, hShort.mono_f⟩).some
  let S₂ : ShortComplex C := sourceTargetCokernelShortComplex f p
  have hS₂_limit :
      IsLimit
        (KernelFork.ofι
          (Abelian.image.ι (gradedPieceMap f p))
          (Abelian.image_ι_comp_eq_zero
            (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p))) := by
    simpa [S₂, sourceTargetCokernelShortComplex] using hExact.isLimitImage
  let e : Abelian.image (gradedPieceMap f p) ≅ (image f).gradedPiece p :=
    IsLimit.conePointUniqueUpToIso hS₂_limit hS₁_limit
  refine ⟨e, ?_⟩
  simpa [e] using
    IsLimit.conePointUniqueUpToIso_hom_comp hS₂_limit hS₁_limit WalkingParallelPair.zero

/-- Helper for Lemma 12.19.13: if the degree-`p` graded coimage-image comparison is an
isomorphism, then the kernel-source-target row is exact in degree `p`. -/
theorem kernel_source_target_exact_of_gradedPiece_coimageImageComparison_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (kernelSourceTargetShortComplex f p).Exact := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  let S₂ : ShortComplex C := kernelSourceTargetShortComplex f p
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  let β : (image f).gradedPiece p ⟶ gr^{p} B :=
    gradedPieceMap (imageInclusion f) p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := α ≫ β
      comm₁₂ := by simp [S₁, S₂, kernelSourceTargetShortComplex]
      comm₂₃ := by
        -- The right square is exactly the graded coimage-image factorization.
        simpa [S₁, S₂, α, β, Category.assoc, kernelSourceTargetShortComplex] using
          (gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p).symm }
  have hShort := gradedPiece_kernel_toCoimage_shortExact f p
  haveI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  haveI : Epi φ.τ₁ := by
    change Epi (𝟙 S₁.X₁)
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (α ≫ β)
    haveI : Mono β := by
      dsimp [β]
      simpa using (inferInstance : Mono (gradedPieceMap (imageInclusion f) p))
    letI : IsIso α := inferInstance
    exact (mono_comp_iff_of_isIso α β).2 inferInstance
  -- Exactness transports across the identity on the first two terms and the mono comparison on
  -- the right.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hShort.exact

/-- Helper for Lemma 12.19.13: kernel-side exactness also gives exactness after replacing the
right term `gr^p(B)` by the chosen graded image object. -/
theorem kernelSourceImageShortComplex_exact_of_kernel_source_target_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceTargetShortComplex f p).Exact) :
    (kernelSourceImageShortComplex f p).Exact := by
  let S₁ : ShortComplex C := kernelSourceImageShortComplex f p
  let S₂ : ShortComplex C := kernelSourceTargetShortComplex f p
  let β : (image f).gradedPiece p ⟶ gr^{p} B :=
    gradedPieceMap (imageInclusion f) p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := β
      comm₁₂ := by simp [S₁, S₂, kernelSourceImageShortComplex, kernelSourceTargetShortComplex]
      comm₂₃ := by
        -- The right square is the public graded factorization through the chosen image object.
        simpa [S₁, S₂, β, kernelSourceImageShortComplex, kernelSourceTargetShortComplex,
          Category.assoc] using
          (gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p).symm }
  haveI : Epi φ.τ₁ := by
    change Epi (𝟙 S₁.X₁)
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono β
    dsimp [β]
    simpa using (gradedPiece_image_cokernel_shortExact f p).mono_f
  -- Exactness transports back across the monic inclusion of the graded image into `gr^p(B)`.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hExact

/-- Helper for Lemma 12.19.13: the graded coimage-image comparison extends the identity maps on
`gr^p(\ker f)` and `gr^p(A)` to a morphism from the public kernel-coimage row to the public
kernel-image row. -/
private theorem kernelToCoimageShortComplexToKernelSourceImage_comm₁₂
    (f : A ⟶ B) (p : ℤ) :
    𝟙 (gr^{p} (kernelFilteredObject f)) ≫ gradedPieceMap (kernelι f) p =
      gradedPieceMap (kernelι f) p ≫ 𝟙 (gr^{p} A) := by
  -- Both sides are the same graded kernel map.
  simp

/-- Helper for Lemma 12.19.13: the right square in the kernel/coimage-to-kernel/image comparison
is the public graded factorization through `gr^p(coim(f) ⟶ im(f))`. -/
private theorem kernelToCoimageShortComplexToKernelSourceImage_comm₂₃
    (f : A ⟶ B) (p : ℤ) :
    𝟙 (gr^{p} A) ≫
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) =
      gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p := by
  -- The identity on the middle term does not change the graded factorization.
  simp [Category.assoc]

/-- Helper for Lemma 12.19.13: the graded coimage-image comparison extends the identity maps on
`gr^p(\ker f)` and `gr^p(A)` to a morphism from the public kernel-coimage row to the public
kernel-image row. -/
private abbrev kernelToCoimageShortComplexToKernelSourceImage
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)) ⟶
      kernelSourceImageShortComplex f p :=
  ShortComplex.homMk
    (𝟙 _)
    (𝟙 _)
    (gradedPieceMap (coimageImageComparison f) p)
    (kernelToCoimageShortComplexToKernelSourceImage_comm₁₂ f p)
    (kernelToCoimageShortComplexToKernelSourceImage_comm₂₃ f p)

/-- Helper for Lemma 12.19.13: kernel-side exactness extends to the four-term public row
`0 ⟶ gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{im} f)`. -/
theorem kernelSourceImageHeadZeroComposableArrows_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceImageShortComplex f p).Exact) :
    (ComposableArrows.mk₃
      (0 : (0 : C) ⟶ gr^{p} (kernelFilteredObject f))
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)).Exact := by
  have hZero :
      (ShortComplex.mk
        (0 : (0 : C) ⟶ gr^{p} (kernelFilteredObject f))
        (gradedPieceMap (kernelι f) p)
        (by simp)).Exact := by
    -- The graded kernel inclusion is always monic.
    exact
      ((ShortComplex.mk
        (0 : (0 : C) ⟶ gr^{p} (kernelFilteredObject f))
        (gradedPieceMap (kernelι f) p)
        (by simp)).exact_iff_mono (by simp)).2
        ((gradedPiece_kernel_coimage_shortExact f p).mono_f)
  -- Attach the initial zero map to the exact kernel-image row.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (0 : (0 : C) ⟶ gr^{p} (kernelFilteredObject f))
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p))
    (h := by simpa [kernelSourceImageShortComplex] using hZero.exact_toComposableArrows)
    (h₀ := by simpa [kernelSourceImageShortComplex] using hExact.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: the public image-side tail
`gr^p(A) ⟶ gr^p(\operatorname{im} f) ⟶ \operatorname{coker}(gr^p(\operatorname{coim} f)
\to gr^p(\operatorname{im} f))`
is exact because `gr^p(\operatorname{coim} f) ⟶ gr^p(\operatorname{im} f)` already has this chosen
cokernel. -/
theorem kernelSourceImageComparisonTailExact
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (gradedPieceMap (coimageImageComparison f) p))
      (by
        -- The chosen cokernel map kills the public image-side composite.
        simpa [Category.assoc] using
          congrArg
            (fun k : gradedPieceMap (coimageImageComparison f) p ⟶
                cokernel (gradedPieceMap (coimageImageComparison f) p) ↦
              gradedPieceMap (toCoimage f) p ≫ k)
            (cokernel.condition (gradedPieceMap (coimageImageComparison f) p)))).Exact := by
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  let β : gr^{p} A ⟶ (image f).gradedPiece p :=
    gradedPieceMap (toCoimage f) p ≫ α
  -- Cancel the epimorphic graded coimage projection to show that `cokernel.π α` is also a
  -- cokernel of the public image-side map `β`.
  refine ShortComplex.exact_of_g_is_cokernel _ ?_
  refine CokernelCofork.IsColimit.ofπ _ _ ?_ ?_ ?_
  · intro Z u hu
    refine cokernel.desc α u ?_
    letI : Epi (gradedPieceMap (toCoimage f) p) :=
      (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
    apply (cancel_epi (gradedPieceMap (toCoimage f) p)).1
    simpa [α, β, Category.assoc] using hu
  · intro Z u hu
    letI : Epi (gradedPieceMap (toCoimage f) p) :=
      (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
    exact cokernel.π_desc α u ((cancel_epi (gradedPieceMap (toCoimage f) p)).1 (by
      simpa [α, β, Category.assoc] using hu))
  · intro Z u hu m hm
    ext
    rw [hm, cokernel.π_desc]

/-- Helper for Lemma 12.19.13: exactness of the public kernel-image row already makes the graded
coimage-image comparison monic. -/
theorem gradedPiece_coimageImageComparison_mono_of_kernel_source_image_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceImageShortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p) := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  let S₂ : ShortComplex C := kernelSourceImageShortComplex f p
  let φ : S₁ ⟶ S₂ := kernelToCoimageShortComplexToKernelSourceImage f p
  have hShort := gradedPiece_kernel_toCoimage_shortExact f p
  letI : Epi S₁.g := by
    change Epi (gradedPieceMap (toCoimage f) p)
    exact hShort.epi_g
  haveI : Epi φ.τ₁ := by
    change Epi (𝟙 S₁.X₁)
    infer_instance
  haveI : Mono φ.τ₂ := by
    change Mono (𝟙 S₁.X₂)
    infer_instance
  -- Compare the canonical short exact row with the public image row and apply the short-complex
  -- four lemma at the right endpoint.
  simpa [S₁, S₂, φ, kernelSourceImageShortComplex] using
    (ShortComplex.mono_of_epi_of_epi_of_mono (φ := φ) hExact
      (by infer_instance) (by infer_instance) (by infer_instance))

/-- Helper for Lemma 12.19.13: under kernel-image exactness, the degree-`p` graded piece of the
filtered coimage represents the canonical image of the public graded map
`gr^p(A) ⟶ gr^p(\operatorname{im} f)`. -/
theorem gradedPiece_coimage_iso_pointwise_image_of_kernel_source_image_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceImageShortComplex f p).Exact) :
    ∃ e :
        (coimage f).gradedPiece p ≅
          Limits.image (gradedPieceMap (toCoimage f) p ≫
            gradedPieceMap (coimageImageComparison f) p),
      gradedPieceMap (toCoimage f) p ≫ e.hom =
        Limits.factorThruImage
          (gradedPieceMap (toCoimage f) p ≫
            gradedPieceMap (coimageImageComparison f) p) := by
  let β : gr^{p} A ⟶ (image f).gradedPiece p :=
    gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  have hS₁_colim :
      IsColimit
        (CokernelCofork.ofπ
          (gradedPieceMap (toCoimage f) p)
          (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
            (kernelι_comp_toFilteredCoimage f) p)) := by
    have hShort := gradedPiece_kernel_toCoimage_shortExact f p
    -- The public graded coimage projection is already the cokernel of the graded kernel map.
    exact ((S₁.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hShort.exact, hShort.epi_g⟩).some
  let S₂ : ShortComplex C := kernelSourceImageShortComplex f p
  have hS₂_colim :
      IsColimit
        (CokernelCofork.ofπ
          (Limits.factorThruImage β)
          (comp_factorThruImage_eq_zero
            (gradedPiece_kernel_toCoimage_comp_coimageImageComparison_zero f p))) := by
    -- Exactness makes the image factor map of the public graded kernel-image row a cokernel.
    simpa [S₂, kernelSourceImageShortComplex, β] using hExact.isColimitImage
  let e :
      (coimage f).gradedPiece p ≅ Limits.image β :=
    IsColimit.coconePointUniqueUpToIso hS₁_colim hS₂_colim
  refine ⟨e, ?_⟩
  -- The comparison isomorphism identifies the two cokernel arrows.
  simpa [β, e] using
    IsColimit.comp_coconePointUniqueUpToIso_hom hS₁_colim hS₂_colim
      WalkingParallelPair.one

/-- Helper for Lemma 12.19.13: the public graded image factorization lands in the chosen graded
image object of `f`. -/
theorem pointwiseImageToFilteredImage_fac
    (f : A ⟶ B) (p : ℤ) :
    (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) ≫
        gradedPieceMap (imageInclusion f) p =
      gradedPieceMap f p := by
  -- This is exactly the graded coimage-image factorization of `f`.
  simpa [Category.assoc] using
    gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p

/-- Helper for Lemma 12.19.13: the canonical image of `gr^p(f)` maps to the chosen graded image
object of `f`. -/
noncomputable def pointwiseImageToFilteredImage
    (f : A ⟶ B) (p : ℤ) :
    Limits.image (gradedPieceMap f p) ⟶ (image f).gradedPiece p := by
  -- Factor `gr^p(f)` through the chosen graded image inclusion.
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  exact Limits.image.lift
    { I := (image f).gradedPiece p
      m := gradedPieceMap (imageInclusion f) p
      e := gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p
      fac := pointwiseImageToFilteredImage_fac f p }

/-- Helper for Lemma 12.19.13: the canonical factor-through-image map for `gr^p(f)` followed by the
explicit comparison to `gr^p(\operatorname{im} f)` is the public graded factorization through
`(coimage f).gradedPiece p`. -/
theorem factorThruImage_comp_pointwiseImageToFilteredImage
    (f : A ⟶ B) (p : ℤ) :
    Limits.factorThruImage (gradedPieceMap f p) ≫ pointwiseImageToFilteredImage f p =
      gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p := by
  -- This is the defining factor-through-image property of the image lift.
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  simpa [pointwiseImageToFilteredImage] using
    Limits.image.fac_lift
      { I := (image f).gradedPiece p
        m := gradedPieceMap (imageInclusion f) p
        e := gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p
        fac := by
          simpa [Category.assoc] using
            gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p }

/-- Helper for Lemma 12.19.13: the public graded image factorization is killed by the cokernel of
the comparison `image(gr^p(f)) ⟶ gr^p(\operatorname{im} f)`. -/
theorem pointwiseImageToFilteredImage_cokernel_condition
    (f : A ⟶ B) (p : ℤ) :
    (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) ≫
        cokernel.π (pointwiseImageToFilteredImage f p) =
      0 := by
  -- Rewrite the public factorization through the canonical image comparison and use the cokernel
  -- relation of `pointwiseImageToFilteredImage`.
  rw [← factorThruImage_comp_pointwiseImageToFilteredImage]
  simp [Category.assoc]

/-- Helper for Lemma 12.19.13: the cokernel of the explicit comparison
`image(gr^p(f)) ⟶ gr^p(\operatorname{im} f)` is already a cokernel of the public graded image
factorization `gr^p(A) ⟶ gr^p(\operatorname{im} f)`. -/
noncomputable def pointwiseImageToFilteredImage_isCokernel
    (f : A ⟶ B) (p : ℤ) :
    IsColimit
      (CokernelCofork.ofπ
        (f := gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (pointwiseImageToFilteredImage_cokernel_condition f p)) := by
  let hExact :
      (ShortComplex.mk
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (pointwiseImageToFilteredImage_cokernel_condition f p)).Exact := by
    let S₁ : ShortComplex C :=
      ShortComplex.mk
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (pointwiseImageToFilteredImage_cokernel_condition f p)
    let S₂ : ShortComplex C :=
      ShortComplex.mk
        (pointwiseImageToFilteredImage f p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (cokernel.condition (pointwiseImageToFilteredImage f p))
    let φ : S₁ ⟶ S₂ :=
      { τ₁ := Limits.factorThruImage (gradedPieceMap f p)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          -- The left square is exactly the normalization of the public graded factorization.
          simpa [S₁, S₂] using
            factorThruImage_comp_pointwiseImageToFilteredImage f p
        comm₂₃ := by
          simp [S₁, S₂] }
    have hExact₂ : S₂.Exact := by
      -- The canonical row `image(gr^p(f)) ⟶ gr^p(im f) ⟶ coker(...)` is always exact.
      simpa [S₂] using ShortComplex.exact_cokernel (pointwiseImageToFilteredImage f p)
    haveI : Epi φ.τ₁ := by
      change Epi (Limits.factorThruImage (gradedPieceMap f p))
      infer_instance
    haveI : IsIso φ.τ₂ := by
      change IsIso (𝟙 S₁.X₂)
      infer_instance
    haveI : Mono φ.τ₃ := by
      change Mono (𝟙 S₁.X₃)
      infer_instance
    -- Transport exactness back across the epic canonical factor-through-image map.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hExact₂
  let S : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (pointwiseImageToFilteredImage_cokernel_condition f p)
  have hEpi : Epi S.g := by
    -- The cokernel projection of the comparison map is always epic.
    change Epi (cokernel.π (pointwiseImageToFilteredImage f p))
    infer_instance
  -- Package the transported exact row as the desired cokernel.
  exact ((S.exact_and_epi_g_iff_g_is_cokernel).1
    ⟨hExact, hEpi⟩).some

/-- Helper for Lemma 12.19.13: the public graded image factorization followed by the cokernel of
the explicit comparison is exact. -/
theorem pointwiseImageToFilteredImage_cokernel_exact
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (pointwiseImageToFilteredImage_cokernel_condition f p)).Exact := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (pointwiseImageToFilteredImage_cokernel_condition f p)
  let S₂ : ShortComplex C :=
    ShortComplex.mk
      (pointwiseImageToFilteredImage f p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (cokernel.condition (pointwiseImageToFilteredImage f p))
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := Limits.factorThruImage (gradedPieceMap f p)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- The left square is exactly the normalization of the public graded factorization.
        simpa [S₁, S₂] using
          factorThruImage_comp_pointwiseImageToFilteredImage f p
      comm₂₃ := by
        simp [S₁, S₂] }
  have hExact : S₂.Exact := by
    -- The canonical row `image(gr^p(f)) ⟶ gr^p(im f) ⟶ coker(...)` is always exact.
    simpa [S₂] using ShortComplex.exact_cokernel (pointwiseImageToFilteredImage f p)
  haveI : Epi φ.τ₁ := by
    change Epi (Limits.factorThruImage (gradedPieceMap f p))
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Transport exactness back across the epic canonical factor-through-image map.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hExact

/-- Helper for Lemma 12.19.13: the explicit comparison from the canonical image of `gr^p(f)` to
the chosen graded image object intertwines the two image inclusions. -/
theorem pointwiseImageToFilteredImage_comp_imageInclusion
    (f : A ⟶ B) (p : ℤ) :
    pointwiseImageToFilteredImage f p ≫ gradedPieceMap (imageInclusion f) p =
      Limits.image.ι (gradedPieceMap f p) := by
  -- This is the defining property of the image lift above.
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  simpa [pointwiseImageToFilteredImage] using
    Limits.image.lift_fac
      { I := (image f).gradedPiece p
        m := gradedPieceMap (imageInclusion f) p
        e := gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p
        fac := by
          simpa [Category.assoc] using
            gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p }

/-- Helper for Lemma 12.19.13: kernel-side exactness already forces the explicit comparison
`image (gr^p(f)) ⟶ gr^p(\operatorname{im} f)` to be monic. -/
theorem pointwiseImageToFilteredImage_mono_of_kernel_source_target_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceTargetShortComplex f p).Exact) :
    Mono (pointwiseImageToFilteredImage f p) := by
  -- Postcompose with the monic graded image inclusion and use the defining image factorization.
  let _ := hExact
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  haveI : Mono (pointwiseImageToFilteredImage f p ≫ gradedPieceMap (imageInclusion f) p) := by
    rw [pointwiseImageToFilteredImage_comp_imageInclusion]
    infer_instance
  exact
    (mono_comp_iff_of_mono (pointwiseImageToFilteredImage f p)
      (gradedPieceMap (imageInclusion f) p)).1 inferInstance

/-- Helper for Lemma 12.19.13: when the public kernel-image row is exact and the source row gives
the needed monicity bridge, the canonical factor-through-image map of `gr^p(f)` is already the
actual cokernel of the graded kernel map. -/
noncomputable def pointwiseImageFactorisation_isCokernel_of_kernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    IsColimit
      (CokernelCofork.ofπ
        (Limits.factorThruImage (gradedPieceMap f p))
        (comp_factorThruImage_eq_zero
          (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p))) := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (Limits.factorThruImage (gradedPieceMap f p))
      (comp_factorThruImage_eq_zero
        (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p))
  let S₂ : ShortComplex C := kernelSourceImageShortComplex f p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := pointwiseImageToFilteredImage f p
      comm₁₂ := by
        simp [S₁, S₂, kernelSourceImageShortComplex]
      comm₂₃ := by
        -- Route correction: transport exactness to the canonical image row before packaging the
        -- cokernel, so the kernel-side argument no longer loops through the public image owner.
        simpa [S₁, S₂, kernelSourceImageShortComplex, Category.assoc] using
          (factorThruImage_comp_pointwiseImageToFilteredImage f p).symm }
  haveI : Epi φ.τ₁ := by
    change Epi (𝟙 S₁.X₁)
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (pointwiseImageToFilteredImage f p)
    exact pointwiseImageToFilteredImage_mono_of_kernel_source_target_exact f p hSourceExact
  have hExact₁ : S₁.Exact := by
    -- Move exactness from the public graded image row to the canonical pointwise-image row.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hImageExact
  have hEpi₁ : Epi S₁.g := by
    -- The canonical factor-through-image map is always epic.
    change Epi (Limits.factorThruImage (gradedPieceMap f p))
    infer_instance
  -- Exactness plus the canonical epicity packages the pointwise image factorization as the
  -- desired cokernel of the graded kernel map.
  exact ((S₁.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hExact₁, hEpi₁⟩).some

/-- Helper for Lemma 12.19.13: the pointwise comparison
`image(gr^p(f)) ⟶ gr^p(\operatorname{im} f)` together with its cokernel projection and terminal
zero map forms an exact tail. -/
theorem pointwiseImageComparisonTailZeroComposableArrows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    (ComposableArrows.mk₃
      (pointwiseImageToFilteredImage f p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (0 : cokernel (pointwiseImageToFilteredImage f p) ⟶ 0)).Exact := by
  let _ := hImageExact
  let _ := hSourceExact
  have hCokernel :
      (ShortComplex.mk
        (pointwiseImageToFilteredImage f p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (cokernel.condition (pointwiseImageToFilteredImage f p))).Exact := by
    -- The pointwise image comparison followed by its cokernel projection is always exact.
    exact ShortComplex.exact_cokernel (pointwiseImageToFilteredImage f p)
  have hZero :
      (ShortComplex.mk
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (0 : cokernel (pointwiseImageToFilteredImage f p) ⟶ 0)
        (by simp)).Exact := by
    -- The cokernel projection is epic, so its terminal zero tail is exact.
    exact
      ((ShortComplex.mk
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (0 : cokernel (pointwiseImageToFilteredImage f p) ⟶ 0)
        (by simp)).exact_iff_epi (by simp)).2
        (by infer_instance)
  -- Attach the terminal zero map to the canonical cokernel row.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (pointwiseImageToFilteredImage f p)
      (cokernel.π (pointwiseImageToFilteredImage f p))
      (0 : cokernel (pointwiseImageToFilteredImage f p) ⟶ 0))
    (h := by
      simpa using hCokernel.exact_toComposableArrows)
    (h₀ := by
      simpa using hZero.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: if the public kernel-image row is exact in degree `p`, then it
extends to the exact four-term row
`gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{im} f) ⟶
\operatorname{coker}(image(gr^p(f)) ⟶ gr^p(\operatorname{im} f))`. -/
theorem kernelSourceImageCokernelComposableArrows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact) :
    (ComposableArrows.mk₃
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (pointwiseImageToFilteredImage f p))).Exact := by
  have hTail :
      (ShortComplex.mk
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
        (cokernel.π (pointwiseImageToFilteredImage f p))
        (pointwiseImageToFilteredImage_cokernel_condition f p)).Exact := by
    -- The public graded image factorization always maps into the chosen cokernel.
    exact pointwiseImageToFilteredImage_cokernel_exact f p
  -- Attach the public cokernel row to the exact kernel-image head.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
      (cokernel.π (pointwiseImageToFilteredImage f p)))
    (h := by
      simpa [kernelSourceImageShortComplex] using hImageExact.exact_toComposableArrows)
    (h₀ := by
      simpa using hTail.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: the public graded coimage maps to the canonical coimage of
`gr^p(f)`. -/
noncomputable def filteredCoimageToPointwiseCoimage
    (f : A ⟶ B) (p : ℤ) :
    (coimage f).gradedPiece p ⟶ Abelian.coimage (gradedPieceMap f p) := by
  let S : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  have hS_colim :
      IsColimit
        (CokernelCofork.ofπ
          (gradedPieceMap (toCoimage f) p)
          (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
            (kernelι_comp_toFilteredCoimage f) p)) := by
    -- The public graded coimage projection is already a cokernel of the graded kernel map.
    have hShort := gradedPiece_kernel_toCoimage_shortExact f p
    exact ((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hShort.exact, hShort.epi_g⟩).some
  -- Descend the canonical coimage projection of `gr^p(f)` across the public graded cokernel.
  exact hS_colim.desc
    (CokernelCofork.ofπ
      (Abelian.coimage.π (gradedPieceMap f p))
      (Abelian.comp_coimage_π_eq_zero
        (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)))

/-- Helper for Lemma 12.19.13: the canonical coimage comparison intertwines the public graded
coimage projection with `Abelian.coimage.π (gr^p(f))`. -/
theorem gradedPiece_toCoimage_comp_filteredCoimageToPointwiseCoimage
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (toCoimage f) p ≫ filteredCoimageToPointwiseCoimage f p =
      Abelian.coimage.π (gradedPieceMap f p) := by
  let S : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
        (kernelι_comp_toFilteredCoimage f) p)
  have hShort := gradedPiece_kernel_toCoimage_shortExact f p
  -- Re-express the definition using the concrete cokernel witness that built it.
  change
    gradedPieceMap (toCoimage f) p ≫
        (((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hShort.exact, hShort.epi_g⟩).some).desc
          (CokernelCofork.ofπ
            (Abelian.coimage.π (gradedPieceMap f p))
            (Abelian.comp_coimage_π_eq_zero
              (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p))) =
      Abelian.coimage.π (gradedPieceMap f p)
  -- The descended map is characterized by its composite with the cokernel arrow.
  exact
    IsColimit.fac
      ((((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hShort.exact, hShort.epi_g⟩).some) :
        IsColimit
          (CokernelCofork.ofπ
            (gradedPieceMap (toCoimage f) p)
            (gradedPieceMap_comp_zero (kernelι f) (toCoimage f)
              (kernelι_comp_toFilteredCoimage f) p)))
      (CokernelCofork.ofπ
        (Abelian.coimage.π (gradedPieceMap f p))
        (Abelian.comp_coimage_π_eq_zero
          (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)))
      WalkingParallelPair.one

/-- Helper for Lemma 12.19.13: the public graded coimage-target map is the pointwise coimage map
followed by the canonical factor-through-coimage map of `gr^p(f)`. -/
theorem filteredCoimageToPointwiseCoimage_comp_factorThruCoimage
    (f : A ⟶ B) (p : ℤ) :
    filteredCoimageToPointwiseCoimage f p ≫
        Abelian.factorThruCoimage (gradedPieceMap f p) =
      gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p := by
  letI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  -- Cancel the epic public graded coimage projection to compare both target maps.
  apply (cancel_epi (gradedPieceMap (toCoimage f) p)).1
  calc
    gradedPieceMap (toCoimage f) p ≫
          (filteredCoimageToPointwiseCoimage f p ≫
            Abelian.factorThruCoimage (gradedPieceMap f p))
        =
      (gradedPieceMap (toCoimage f) p ≫ filteredCoimageToPointwiseCoimage f p) ≫
        Abelian.factorThruCoimage (gradedPieceMap f p) := by
          simp [Category.assoc]
    _ =
      Abelian.coimage.π (gradedPieceMap f p) ≫
        Abelian.factorThruCoimage (gradedPieceMap f p) := by
          rw [gradedPiece_toCoimage_comp_filteredCoimageToPointwiseCoimage]
    _ = gradedPieceMap f p := by
          simpa using Abelian.coimage.fac (gradedPieceMap f p)
    _ =
      gradedPieceMap (toCoimage f) p ≫
        (gradedPieceMap (coimageImageComparison f) p ≫
          gradedPieceMap (imageInclusion f) p) := by
          symm
          simpa [Category.assoc] using
            gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p

/-- Helper for Lemma 12.19.13: the pointwise coimage factorization of `gr^p(f)` is killed by the
graded cokernel map of `f`. -/
theorem pointwiseCoimageTargetCokernel_zero
    (f : A ⟶ B) (p : ℤ) :
    Abelian.factorThruCoimage (gradedPieceMap f p) ≫ gradedPieceMap (toCokernel f) p = 0 := by
  letI : Epi (Abelian.coimage.π (gradedPieceMap f p)) := by infer_instance
  -- Cancel the epic pointwise coimage projection and use the usual graded cokernel relation.
  apply (cancel_epi (Abelian.coimage.π (gradedPieceMap f p))).1
  calc
    Abelian.coimage.π (gradedPieceMap f p) ≫
          Abelian.factorThruCoimage (gradedPieceMap f p) ≫
            gradedPieceMap (toCokernel f) p
        =
      gradedPieceMap f p ≫ gradedPieceMap (toCokernel f) p := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ gradedPieceMap (toCokernel f) p)
              (Abelian.coimage.fac (gradedPieceMap f p))
    _ = Abelian.coimage.π (gradedPieceMap f p) ≫ 0 := by
          simpa [Category.assoc] using
            gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p

/-- Helper for Lemma 12.19.13: cokernel-side exactness also identifies the pointwise coimage row
`coim(gr^p(f)) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)` as exact. -/
theorem pointwiseCoimageTargetCokernel_exact_of_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    (ShortComplex.mk
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (gradedPieceMap (toCokernel f) p)
      (pointwiseCoimageTargetCokernel_zero f p)).Exact := by
  let S₁ : ShortComplex C := sourceTargetCokernelShortComplex f p
  let S₂ : ShortComplex C :=
    ShortComplex.mk
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (gradedPieceMap (toCokernel f) p)
      (pointwiseCoimageTargetCokernel_zero f p)
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := Abelian.coimage.π (gradedPieceMap f p)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- The left square is the pointwise coimage factorization of `gr^p(f)`.
        simpa [S₁, S₂, sourceTargetCokernelShortComplex, Category.assoc] using
          Abelian.coimage.fac (gradedPieceMap f p)
      comm₂₃ := by
        simp [S₁, S₂, sourceTargetCokernelShortComplex] }
  haveI : Epi φ.τ₁ := by
    change Epi (Abelian.coimage.π (gradedPieceMap f p))
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Transport exactness across the epic pointwise coimage projection.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hExact

/-- Helper for Lemma 12.19.13: if the degree-`p` graded coimage-image comparison is an
isomorphism, then the source-target-cokernel row is exact in degree `p`. -/
theorem sourceTargetCokernelExact_of_gradedPieceCoimageImageComparison_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (sourceTargetCokernelShortComplex f p).Exact := by
  let S₁ : ShortComplex C := sourceTargetCokernelShortComplex f p
  let S₂ : ShortComplex C := imageCokernelShortComplex f p
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := gradedPieceMap (toCoimage f) p ≫ α
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- The left square is exactly the graded coimage-image factorization.
        simpa [S₁, S₂, α, Category.assoc, sourceTargetCokernelShortComplex,
          imageCokernelShortComplex] using
          gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p
      comm₂₃ := by
        simp [S₁, S₂, sourceTargetCokernelShortComplex, imageCokernelShortComplex] }
  have hShort := gradedPiece_image_cokernel_shortExact f p
  haveI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  haveI : Epi φ.τ₁ := by
    change Epi (gradedPieceMap (toCoimage f) p ≫ α)
    letI : IsIso α := inferInstance
    exact (epi_comp_iff_of_isIso (gradedPieceMap (toCoimage f) p) α).2 inferInstance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Transport exactness back across the epi comparison on the left.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hShort.exact

/-- Helper for Lemma 12.19.13: exactness of
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)` already makes the public graded factorization
`gr^p(A) ⟶ gr^p(\operatorname{im} f)` epic. -/
theorem gradedPiece_toImage_epi_of_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Epi (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) := by
  let S₁ : ShortComplex C := sourceTargetCokernelShortComplex f p
  let S₂ : ShortComplex C := imageCokernelShortComplex f p
  let β : gr^{p} A ⟶ (image f).gradedPiece p :=
    gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := β
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- The left square is the graded factorization through the chosen filtered image object.
        simpa [S₁, S₂, β, sourceTargetCokernelShortComplex, imageCokernelShortComplex,
          Category.assoc] using
          gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p
      comm₂₃ := by
        -- The right square is unchanged because both rows end with the same cokernel map.
        simp [S₁, S₂, sourceTargetCokernelShortComplex, imageCokernelShortComplex] }
  have hShort := gradedPiece_image_cokernel_shortExact f p
  haveI : Epi φ.τ₂ := by
    change Epi (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Compare the exact source-target row with the canonical image-cokernel row and read off the
  -- left endpoint from the short-complex four lemma.
  simpa [S₁, S₂, φ, β, sourceTargetCokernelShortComplex, imageCokernelShortComplex] using
    (ShortComplex.epi_of_mono_of_epi_of_mono (φ := φ) hExact hShort.mono_f
      (by infer_instance) (by infer_instance))

/-- Helper for Lemma 12.19.13: exactness of the kernel-source-target row in every degree forces
the associated-graded coimage-image comparison to be an isomorphism. -/
theorem gradedPiece_coimageImageComparison_mono_of_kernel_source_target_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (kernelSourceTargetShortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p) := by
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  let β : (image f).gradedPiece p ⟶ gr^{p} B :=
    gradedPieceMap (imageInclusion f) p
  letI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  haveI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  letI : Mono β := by
    simpa [β] using (inferInstance : Mono (gradedPieceMap (imageInclusion f) p))
  letI : IsIso (Abelian.coimageImageComparison (gradedPieceMap f p)) := inferInstance
  rcases gradedPiece_coimage_iso_pointwise_coimage_of_kernel_source_target_exact f p hExact with
    ⟨e, he⟩
  have hcomp :
      α ≫ β =
        e.hom ≫ Abelian.coimageImageComparison (gradedPieceMap f p) ≫
          Abelian.image.ι (gradedPieceMap f p) := by
    apply (cancel_epi (gradedPieceMap (toCoimage f) p)).1
    calc
      gradedPieceMap (toCoimage f) p ≫ (α ≫ β)
          = gradedPieceMap f p := by
              simpa [α, β, Category.assoc] using
                gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p
      _ = Abelian.coimage.π (gradedPieceMap f p) ≫
            Abelian.coimageImageComparison (gradedPieceMap f p) ≫
              Abelian.image.ι (gradedPieceMap f p) := by
              simpa [Category.assoc] using
                (Abelian.coimage_image_factorisation (gradedPieceMap f p)).symm
      _ = gradedPieceMap (toCoimage f) p ≫
            (e.hom ≫ Abelian.coimageImageComparison (gradedPieceMap f p) ≫
              Abelian.image.ι (gradedPieceMap f p)) := by
              calc
                Abelian.coimage.π (gradedPieceMap f p) ≫
                    Abelian.coimageImageComparison (gradedPieceMap f p) ≫
                      Abelian.image.ι (gradedPieceMap f p)
                    =
                  (gradedPieceMap (toCoimage f) p ≫ e.hom) ≫
                    Abelian.coimageImageComparison (gradedPieceMap f p) ≫
                      Abelian.image.ι (gradedPieceMap f p) := by
                        rw [he]
                _ = gradedPieceMap (toCoimage f) p ≫
                      (e.hom ≫ Abelian.coimageImageComparison (gradedPieceMap f p) ≫
                        Abelian.image.ι (gradedPieceMap f p)) := by
                      simp [Category.assoc]
  have hmonoComp : Mono (α ≫ β) := by
    rw [hcomp]
    infer_instance
  -- Cancel the monic inclusion of `gr^p(im f)` into `gr^p(B)`.
  exact (mono_comp_iff_of_mono α β).1 hmonoComp

/-- Helper for Lemma 12.19.13: exactness of the source-target-cokernel row in every degree makes
the graded coimage-image comparison epic. -/
theorem gradedPiece_coimageImageComparison_epi_of_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Epi (gradedPieceMap (coimageImageComparison f) p) := by
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  let q : gr^{p} A ⟶ (coimage f).gradedPiece p :=
    gradedPieceMap (toCoimage f) p
  letI : Epi q :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  haveI : Epi (q ≫ α) :=
    gradedPiece_toImage_epi_of_source_target_cokernel_exact f p hExact
  -- Cancel the epimorphic graded coimage projection from the public factorization.
  exact (epi_comp_iff_of_epi q α).1 inferInstance

/-- Helper for Lemma 12.19.13: exactness of the public kernel-image row together with its source
provenance forces the graded map `gr^p(A) ⟶ gr^p(\operatorname{im} f)` to be epic. -/
theorem pointwiseImageToFilteredImage_epiBridge_of_kernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    Epi (pointwiseImageToFilteredImage f p) := by
  let hPointwiseColim :=
    pointwiseImageFactorisation_isCokernel_of_kernel_rows_exact f p hImageExact hSourceExact
  haveI : Mono (pointwiseImageToFilteredImage f p) :=
    pointwiseImageToFilteredImage_mono_of_kernel_source_target_exact f p hSourceExact
  let hPointwiseTail :=
    pointwiseImageComparisonTailZeroComposableArrows_exact f p hImageExact hSourceExact
  let hPublicRow :=
    kernelSourceImageCokernelComposableArrows_exact f p hImageExact
  -- Route correction: the kernel-side blocker is now isolated to one endpoint upgrade.
  -- The exact rows `hPointwiseTail` and `hPublicRow` now isolate the pointwise cokernel tail and
  -- the public image row against the same endpoint object. The remaining blocker is to bridge
  -- these two exact packages without reintroducing the false middle-complex statement from an
  -- earlier route.
  let _ := hPointwiseColim
  let _ := hPointwiseTail
  let _ := hPublicRow
  -- TODO: compare `hPointwiseTail` and `hPublicRow` by an endpoint diagram chase to
  -- force `cokernel.π (pointwiseImageToFilteredImage f p) = 0`, then conclude by
  -- `Abelian.epi_of_cokernel_π_eq_zero`.
  sorry

/-- Helper for Lemma 12.19.13: exactness of the public kernel-image row together with its source
provenance forces the graded map `gr^p(A) ⟶ gr^p(\operatorname{im} f)` to be epic. -/
theorem gradedPiece_kernelSourceImage_epi_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    Epi (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p) := by
  letI : Epi (Limits.factorThruImage (gradedPieceMap f p)) := by infer_instance
  letI : Epi (pointwiseImageToFilteredImage f p) :=
    pointwiseImageToFilteredImage_epiBridge_of_kernel_rows_exact f p hImageExact hSourceExact
  -- Normalize the public graded image factorization through the canonical pointwise image.
  rw [← factorThruImage_comp_pointwiseImageToFilteredImage]
  infer_instance

/-- Helper for Lemma 12.19.13: when both kernel-side rows are exact, the public graded image map
`gr^p(A) ⟶ gr^p(\operatorname{im} f)` is itself a cokernel of the graded kernel map. -/
-- Route correction: the missing structural input is not another endpoint-vanishing wrapper but the
-- stronger statement that the public graded image map already carries the universal cokernel
-- structure of `gr^p(\ker f) ⟶ gr^p(A)`.
noncomputable def kernelSourceImage_isCokernel_of_kernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    IsColimit
      (CokernelCofork.ofπ
        (gradedPieceMap (toCoimage f) p ≫ gradedPieceMap (coimageImageComparison f) p)
        (gradedPiece_kernel_toCoimage_comp_coimageImageComparison_zero f p)) := by
  let S : ShortComplex C := kernelSourceImageShortComplex f p
  have hEpi : Epi S.g := by
    -- The source-side exact row already makes the public graded image map epic.
    simpa [S, kernelSourceImageShortComplex] using
      gradedPiece_kernelSourceImage_epi_of_exact f p hImageExact hSourceExact
  -- Package the exact public kernel-image row as the desired cokernel.
  exact ((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hImageExact, hEpi⟩).some

/-- Helper for Lemma 12.19.13: when both kernel-side rows are exact, the explicit comparison
`image (gr^p(f)) ⟶ gr^p(\operatorname{im} f)` is epic. -/
theorem pointwiseImageToFilteredImage_epi_of_kernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    Epi (pointwiseImageToFilteredImage f p) := by
  -- Reuse the earlier bridge formulation so downstream lemmas stay on the normalized surface.
  exact pointwiseImageToFilteredImage_epiBridge_of_kernel_rows_exact f p hImageExact hSourceExact

/-- Helper for Lemma 12.19.13: the endpoint cokernel in the kernel/coimage-to-image comparison
vanishes once the source row and the transported image row are both exact. -/
theorem cokernelCoimageImageComparison_π_eq_zero_of_kernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hImageExact : (kernelSourceImageShortComplex f p).Exact)
    (hSourceExact : (kernelSourceTargetShortComplex f p).Exact) :
    cokernel.π (gradedPieceMap (coimageImageComparison f) p) = 0 := by
  letI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  letI : Epi (gradedPieceMap (coimageImageComparison f) p) :=
    (epi_comp_iff_of_epi (gradedPieceMap (toCoimage f) p)
      (gradedPieceMap (coimageImageComparison f) p)).1 <|
      gradedPiece_kernelSourceImage_epi_of_exact f p hImageExact hSourceExact
  -- Once the graded coimage-image comparison is epic, its chosen cokernel is zero.
  simpa using cokernel.π_of_epi (gradedPieceMap (coimageImageComparison f) p)

/-- Helper for Lemma 12.19.13: if both three-term graded exactness conditions hold, then every
graded piece of the coimage-image comparison is an isomorphism. -/
theorem gradedPiece_coimageImageComparison_isIso_of_kernel_and_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ)
    (hKernel : (kernelSourceTargetShortComplex f p).Exact)
    (hCokernel : (sourceTargetCokernelShortComplex f p).Exact) :
    IsIso (gradedPieceMap (coimageImageComparison f) p) := by
  letI :
      Mono (gradedPieceMap (coimageImageComparison f) p) :=
    gradedPiece_coimageImageComparison_mono_of_kernel_source_target_exact f p hKernel
  letI :
      Epi (gradedPieceMap (coimageImageComparison f) p) :=
    gradedPiece_coimageImageComparison_epi_of_source_target_cokernel_exact f p hCokernel
  exact isIso_of_mono_of_epi (gradedPieceMap (coimageImageComparison f) p)

/-- Helper for Lemma 12.19.13: once both pointwise exactness conditions hold in every degree, the
associated-graded coimage-image comparison is an isomorphism. -/
theorem associatedGradedMap_isIso_of_kernel_and_source_target_cokernel_exact
    (f : A ⟶ B)
    (hKernel : ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact)
    (hCokernel : ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  -- Upgrade the pointwise mono+epi criterion to an isomorphism in `GradedObject ℤ C`.
  letI : ∀ p : ℤ,
      IsIso ((associatedGradedMap (coimageImageComparison f)) p) := by
    intro p
    simpa using
      gradedPiece_coimageImageComparison_isIso_of_kernel_and_source_target_cokernel_exact
        f p (hKernel p) (hCokernel p)
  exact GradedObject.isIso_of_isIso_apply (associatedGradedMap (coimageImageComparison f))

theorem associatedGradedMap_isIso_of_kernel_source_target_exact
    (f : A ⟶ B) (hExact : ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  -- Route correction: the stabilized frontier now includes the transported exact row
  -- `gr^p(ker f) ⟶ gr^p(A) ⟶ gr^p(im f)`. Once the public image row is known to be epic in every
  -- degree, the existing mono criterion upgrades the coimage-image comparison to an isomorphism.
  have hImageExact :
      ∀ p : ℤ, (kernelSourceImageShortComplex f p).Exact := by
    intro p
    -- Replace `gr^p(B)` by the chosen graded image object using the existing mono transport.
    exact kernelSourceImageShortComplex_exact_of_kernel_source_target_exact f p (hExact p)
  have hCokernel :
      ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact := by
    intro p
    let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
      gradedPieceMap (coimageImageComparison f) p
    letI : Epi (gradedPieceMap (toCoimage f) p ≫ α) :=
      gradedPiece_kernelSourceImage_epi_of_exact f p (hImageExact p) (hExact p)
    letI : Epi α := epi_of_epi (gradedPieceMap (toCoimage f) p) α
    letI : Mono α :=
      gradedPiece_coimageImageComparison_mono_of_kernel_source_target_exact f p (hExact p)
    letI : IsIso α := isIso_of_mono_of_epi α
    -- Once the degree-`p` coimage-image comparison is an isomorphism, the public cokernel row is
    -- exact by the earlier transport lemma.
    exact sourceTargetCokernelExact_of_gradedPieceCoimageImageComparison_isIso f p
  exact associatedGradedMap_isIso_of_kernel_and_source_target_cokernel_exact f hExact hCokernel

/-- Helper for Lemma 12.19.13: if the degree-`p` graded coimage-image comparison is an
isomorphism, then the source-target-cokernel row is exact in degree `p`. -/
theorem source_target_cokernel_exact_of_gradedPiece_coimageImageComparison_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (sourceTargetCokernelShortComplex f p).Exact := by
  simpa using sourceTargetCokernelExact_of_gradedPieceCoimageImageComparison_isIso f p

/-- Helper for Lemma 12.19.13: cokernel-side exactness also gives exactness after replacing the
left term `gr^p(A)` by the chosen graded coimage object. -/
theorem coimageTargetCokernelShortComplex_exact_of_source_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    (coimageTargetCokernelShortComplex f p).Exact := by
  let S₁ : ShortComplex C := sourceTargetCokernelShortComplex f p
  let S₂ : ShortComplex C := coimageTargetCokernelShortComplex f p
  let q : gr^{p} A ⟶ (coimage f).gradedPiece p :=
    gradedPieceMap (toCoimage f) p
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := q
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- The left square is the public graded factorization through the chosen coimage object.
        simpa [S₁, S₂, q, sourceTargetCokernelShortComplex, coimageTargetCokernelShortComplex,
          Category.assoc] using
          gradedPiece_toCoimage_comp_coimageImageComparison_comp_imageInclusion f p
      comm₂₃ := by
        simp [S₁, S₂, sourceTargetCokernelShortComplex, coimageTargetCokernelShortComplex] }
  haveI : Epi φ.τ₁ := by
    change Epi q
    dsimp [q]
    exact (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Exactness transports back across the epimorphic graded coimage projection.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hExact

/-- Helper for Lemma 12.19.13: the graded coimage-image comparison extends the identity maps on
`gr^p(B)` and `gr^p(\operatorname{coker} f)` to a morphism from the public coimage-target-cokernel
row to the public image-cokernel row. -/
private theorem coimageTargetCokernelShortComplexToImageCokernel_comm₁₂
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p =
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p) ≫
        𝟙 (gr^{p} B) := by
  -- The identity on `gr^p(B)` does not change the public factorization through the image.
  simp [Category.assoc]

/-- Helper for Lemma 12.19.13: the right square in the coimage-target-cokernel to image-cokernel
comparison is unchanged because both rows end with the same graded cokernel map. -/
private theorem coimageTargetCokernelShortComplexToImageCokernel_comm₂₃
    (f : A ⟶ B) (p : ℤ) :
    𝟙 (gr^{p} B) ≫ gradedPieceMap (toCokernel f) p =
      gradedPieceMap (toCokernel f) p ≫ 𝟙 (gr^{p} (cokernelFilteredObject f)) := by
  -- Both sides are the same graded cokernel map.
  simp

/-- Helper for Lemma 12.19.13: the graded coimage-image comparison extends the identity maps on
`gr^p(B)` and `gr^p(\operatorname{coker} f)` to a morphism from the public coimage-target-cokernel
row to the public image-cokernel row. -/
private abbrev coimageTargetCokernelShortComplexToImageCokernel
    (f : A ⟶ B) (p : ℤ) :
    coimageTargetCokernelShortComplex f p ⟶ imageCokernelShortComplex f p :=
  ShortComplex.homMk
    (gradedPieceMap (coimageImageComparison f) p)
    (𝟙 _)
    (𝟙 _)
    (coimageTargetCokernelShortComplexToImageCokernel_comm₁₂ f p)
    (coimageTargetCokernelShortComplexToImageCokernel_comm₂₃ f p)

/-- Helper for Lemma 12.19.13: cokernel-side exactness extends to the four-term public row
`gr^p(\operatorname{coim} f) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f) ⟶ 0`. -/
theorem coimageTargetCokernelTailZeroComposableArrows_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (coimageTargetCokernelShortComplex f p).Exact) :
    (ComposableArrows.mk₃
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
      (gradedPieceMap (toCokernel f) p)
      (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))).Exact := by
  have hZero :
      (ShortComplex.mk
        (gradedPieceMap (toCokernel f) p)
        (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))
        (by simp)).Exact := by
    -- The graded cokernel projection is always epic.
    exact
      ((ShortComplex.mk
        (gradedPieceMap (toCokernel f) p)
        (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))
        (by simp)).exact_iff_epi (by simp)).2
        ((gradedPiece_image_cokernel_shortExact f p).epi_g)
  -- Attach the terminal zero map to the exact coimage-cokernel row.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
      (gradedPieceMap (toCokernel f) p)
      (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C)))
    (h := by simpa [coimageTargetCokernelShortComplex] using hExact.exact_toComposableArrows)
    (h₀ := by simpa [coimageTargetCokernelShortComplex] using hZero.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: source-target-cokernel exactness also extends the pointwise
coimage row to the four-term exact sequence
`coim(gr^p(f)) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f) ⟶ 0`. -/
theorem pointwiseCoimageTargetCokernelTailZeroComposableArrows_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (sourceTargetCokernelShortComplex f p).Exact) :
    (ComposableArrows.mk₃
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (gradedPieceMap (toCokernel f) p)
      (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))).Exact := by
  have hPointwise :
      (ShortComplex.mk
        (Abelian.factorThruCoimage (gradedPieceMap f p))
        (gradedPieceMap (toCokernel f) p)
        (pointwiseCoimageTargetCokernel_zero f p)).Exact := by
    -- Reuse the exact pointwise coimage/cokernel row coming from the source-target exactness.
    exact pointwiseCoimageTargetCokernel_exact_of_source_target_cokernel_exact f p hExact
  have hZero :
      (ShortComplex.mk
        (gradedPieceMap (toCokernel f) p)
        (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))
        (by simp)).Exact := by
    -- The terminal zero map attaches to the always epic graded cokernel projection.
    exact
      ((ShortComplex.mk
        (gradedPieceMap (toCokernel f) p)
        (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C))
        (by simp)).exact_iff_epi (by simp)).2
        ((gradedPiece_image_cokernel_shortExact f p).epi_g)
  -- Attach the terminal zero map to the pointwise coimage/cokernel row.
  exact ComposableArrows.exact_of_δ₀
    (S := ComposableArrows.mk₃
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (gradedPieceMap (toCokernel f) p)
      (0 : gr^{p} (cokernelFilteredObject f) ⟶ (0 : C)))
    (h := by simpa using hPointwise.exact_toComposableArrows)
    (h₀ := by simpa using hZero.exact_toComposableArrows)

/-- Helper for Lemma 12.19.13: when the public and pointwise cokernel-side rows are exact, the
comparison from the public graded coimage to the pointwise coimage of `gr^p(f)` is epic. -/
theorem filteredCoimageToPointwiseCoimage_epi_of_cokernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Epi (filteredCoimageToPointwiseCoimage f p) := by
  let _ := hCoimageExact
  let _ := hCokernelExact
  letI : Epi (gradedPieceMap (toCoimage f) p) :=
    (gradedPiece_kernel_toCoimage_shortExact f p).epi_g
  haveI :
      Epi (gradedPieceMap (toCoimage f) p ≫ filteredCoimageToPointwiseCoimage f p) := by
    rw [gradedPiece_toCoimage_comp_filteredCoimageToPointwiseCoimage]
    infer_instance
  -- Cancel the epic public graded coimage projection.
  exact
    (epi_comp_iff_of_epi (gradedPieceMap (toCoimage f) p)
      (filteredCoimageToPointwiseCoimage f p)).1 inferInstance

/-- Helper for Lemma 12.19.13: the canonical pointwise coimage-to-image map followed by the
categorical image inclusion is the standard factor-through-coimage map of `gr^p(f)`. -/
private theorem pointwiseCoimageToPointwiseImage_comp_imageInclusion
    (f : A ⟶ B) (p : ℤ) :
    Abelian.coimageImageComparison (gradedPieceMap f p) ≫
        (Abelian.imageIsoImage (gradedPieceMap f p)).hom ≫
          Limits.image.ι (gradedPieceMap f p) =
      Abelian.factorThruCoimage (gradedPieceMap f p) := by
  let g : gr^{p} A ⟶ gr^{p} B := gradedPieceMap f p
  letI : Epi (Abelian.coimage.π g) := by infer_instance
  -- Compare both maps after the epic coimage projection, where they are both equal to `g`.
  apply (cancel_epi (Abelian.coimage.π g)).1
  calc
    Abelian.coimage.π g ≫
          (Abelian.coimageImageComparison g ≫ (Abelian.imageIsoImage g).hom ≫ Limits.image.ι g)
        =
      Abelian.coimage.π g ≫ Abelian.coimageImageComparison g ≫
        (Abelian.imageIsoImage g).hom ≫ Limits.image.ι g := by
          simp [Category.assoc]
    _ =
      Abelian.coimage.π g ≫ Abelian.coimageImageComparison g ≫ Abelian.image.ι g := by
          have hImage :
              (Abelian.imageIsoImage g).hom ≫ Limits.image.ι g = Abelian.image.ι g := by
            simpa using (Abelian.imageIsoImage_hom_comp_image_ι (f := g))
          simpa [Category.assoc] using
            congrArg
              (fun k : Abelian.image g ⟶ gr^{p} B ↦
                Abelian.coimage.π g ≫ Abelian.coimageImageComparison g ≫ k)
              hImage
    _ = g := by
          simpa [Category.assoc] using Abelian.coimage_image_factorisation g
    _ = Abelian.coimage.π g ≫ Abelian.factorThruCoimage g := by
          symm
          simpa using Abelian.coimage.fac g

/-- Helper for Lemma 12.19.13: the public graded coimage-image comparison factors through the
pointwise coimage and pointwise image of `gr^p(f)`. -/
theorem filteredCoimageToPointwiseCoimage_comp_pointwiseCoimageToFilteredImage
    (f : A ⟶ B) (p : ℤ) :
    filteredCoimageToPointwiseCoimage f p ≫
        Abelian.coimageImageComparison (gradedPieceMap f p) ≫
          (Abelian.imageIsoImage (gradedPieceMap f p)).hom ≫
            pointwiseImageToFilteredImage f p =
      gradedPieceMap (coimageImageComparison f) p := by
  let β : Limits.image (gradedPieceMap f p) ⟶ (image f).gradedPiece p :=
    pointwiseImageToFilteredImage f p
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  -- Postcompose with the monic filtered image inclusion and normalize both sides to the same map
  -- `gr^p(coim f) ⟶ gr^p(B)`.
  apply (cancel_mono (gradedPieceMap (imageInclusion f) p)).1
  calc
    (filteredCoimageToPointwiseCoimage f p ≫
          Abelian.coimageImageComparison (gradedPieceMap f p) ≫
            (Abelian.imageIsoImage (gradedPieceMap f p)).hom ≫
              β) ≫
        gradedPieceMap (imageInclusion f) p
        =
      filteredCoimageToPointwiseCoimage f p ≫
        Abelian.factorThruCoimage (gradedPieceMap f p) := by
          rw [Category.assoc, Category.assoc, Category.assoc,
            pointwiseImageToFilteredImage_comp_imageInclusion,
            pointwiseCoimageToPointwiseImage_comp_imageInclusion]
    _ = gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p := by
          rw [filteredCoimageToPointwiseCoimage_comp_factorThruCoimage]

/-- Helper for Lemma 12.19.13: once both cokernel-side rows are exact, the explicit comparison
from the categorical image of `gr^p(f)` to the chosen graded image object is an isomorphism. -/
theorem pointwiseImageToFilteredImage_isIso_of_cokernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    IsIso (pointwiseImageToFilteredImage f p) := by
  let e : Abelian.coimage (gradedPieceMap f p) ≅ Limits.image (gradedPieceMap f p) :=
    (asIso (Abelian.coimageImageComparison (gradedPieceMap f p))) ≪≫
      Abelian.imageIsoImage (gradedPieceMap f p)
  let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
    gradedPieceMap (coimageImageComparison f) p
  haveI : Epi (filteredCoimageToPointwiseCoimage f p) :=
    filteredCoimageToPointwiseCoimage_epi_of_cokernel_rows_exact
      f p hCoimageExact hCokernelExact
  haveI : Epi α := by
    let S₁ : ShortComplex C := coimageTargetCokernelShortComplex f p
    let S₂ : ShortComplex C := imageCokernelShortComplex f p
    let φ : S₁ ⟶ S₂ := coimageTargetCokernelShortComplexToImageCokernel f p
    have hShort := gradedPiece_image_cokernel_shortExact f p
    letI : Mono S₂.f := by
      change Mono (gradedPieceMap (imageInclusion f) p)
      exact hShort.mono_f
    haveI : Epi φ.τ₂ := by
      change Epi (𝟙 S₁.X₂)
      infer_instance
    haveI : Mono φ.τ₃ := by
      change Mono (𝟙 S₁.X₃)
      infer_instance
    -- Reuse the image-cokernel comparison to read epicity at the left endpoint.
    simpa [S₁, S₂, φ, α, coimageTargetCokernelShortComplex, imageCokernelShortComplex] using
      (ShortComplex.epi_of_mono_of_epi_of_mono (φ := φ) hCoimageExact
        (by infer_instance) (by infer_instance) (by infer_instance))
  have hFactor :
      filteredCoimageToPointwiseCoimage f p ≫ e.hom ≫ pointwiseImageToFilteredImage f p = α := by
    -- Normalize the public comparison through the canonical pointwise coimage-image map.
    simpa [e, α, Category.assoc] using
      filteredCoimageToPointwiseCoimage_comp_pointwiseCoimageToFilteredImage f p
  haveI : Epi (e.hom ≫ pointwiseImageToFilteredImage f p) := by
    -- Cancel the already epic comparison from the public coimage to the pointwise coimage.
    exact
      (epi_comp_iff_of_epi (filteredCoimageToPointwiseCoimage f p)
        (e.hom ≫ pointwiseImageToFilteredImage f p)).1 <|
        by simpa [Category.assoc, hFactor] using (inferInstance : Epi α)
  haveI : Epi (pointwiseImageToFilteredImage f p) := by
    -- The remaining epicity survives cancellation across the canonical pointwise coimage-image
    -- isomorphism.
    letI : Epi e.hom := by infer_instance
    exact
      (epi_comp_iff_of_epi e.hom (pointwiseImageToFilteredImage f p)).1 inferInstance
  haveI : Mono (pointwiseImageToFilteredImage f p) := by
    letI : Mono (gradedPieceMap (imageInclusion f) p) :=
      (gradedPiece_image_cokernel_shortExact f p).mono_f
    haveI :
        Mono (pointwiseImageToFilteredImage f p ≫ gradedPieceMap (imageInclusion f) p) := by
      rw [pointwiseImageToFilteredImage_comp_imageInclusion]
      infer_instance
    -- Postcompose with the fixed filtered image inclusion to read monicity on the simpler target.
    exact
      (mono_comp_iff_of_mono (pointwiseImageToFilteredImage f p)
        (gradedPieceMap (imageInclusion f) p)).1 inferInstance
  exact isIso_of_mono_of_epi (pointwiseImageToFilteredImage f p)

/-- Helper for Lemma 12.19.13: the public coimage-side head
`\operatorname{ker}(gr^p(\operatorname{coim} f) \to gr^p(\operatorname{im} f))
\to gr^p(\operatorname{coim} f) ⟶ gr^p(B)`
is exact because `gr^p(\operatorname{coim} f) ⟶ gr^p(\operatorname{im} f)` already has this chosen
kernel. -/
theorem coimageTargetCokernelComparisonHeadExact
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (kernel.ι (gradedPieceMap (coimageImageComparison f) p))
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
      (by
        -- The chosen kernel map lands in the kernel of the public coimage-side composite.
        simp [Category.assoc])).Exact := by
  let S₁ : ShortComplex C :=
    ShortComplex.mk
      (kernel.ι (gradedPieceMap (coimageImageComparison f) p))
      (gradedPieceMap (coimageImageComparison f) p)
      (kernel.condition (gradedPieceMap (coimageImageComparison f) p))
  let S₂ : ShortComplex C :=
    ShortComplex.mk
      (kernel.ι (gradedPieceMap (coimageImageComparison f) p))
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
      (by simp [Category.assoc])
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := gradedPieceMap (imageInclusion f) p
      comm₁₂ := by
        simp [S₁, S₂]
      comm₂₃ := by
        simp [S₁, S₂, Category.assoc] }
  have hExact : S₁.Exact := by
    -- The canonical kernel row for the graded coimage-image comparison is exact.
    simpa [S₁] using ShortComplex.exact_kernel (gradedPieceMap (coimageImageComparison f) p)
  haveI : Epi φ.τ₁ := by
    change Epi (𝟙 S₁.X₁)
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (gradedPieceMap (imageInclusion f) p)
    exact (gradedPiece_image_cokernel_shortExact f p).mono_f
  -- Transport exactness across the monic graded image inclusion.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hExact

/-- Helper for Lemma 12.19.13: the pointwise coimage head
`0 ⟶ \operatorname{coim}(gr^p(f)) ⟶ gr^p(B)` is exact. -/
theorem pointwiseCoimageTargetHeadExact
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (0 : 0 ⟶ Abelian.coimage (gradedPieceMap f p))
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (by simp)).Exact := by
  -- Exactness at the pointwise coimage is exactly the monomorphy of its inclusion into
  -- `gr^p(B)`.
  exact
    ((ShortComplex.mk
      (0 : 0 ⟶ Abelian.coimage (gradedPieceMap f p))
      (Abelian.factorThruCoimage (gradedPieceMap f p))
      (by simp)).exact_iff_mono (by simp)).2
      (by infer_instance)

/-- Helper for Lemma 12.19.13: the public kernel-coimage head maps to the pointwise coimage head
through `filteredCoimageToPointwiseCoimage f p`. -/
theorem coimageHeadToPointwiseHeadComparison
    (f : A ⟶ B) (p : ℤ) :
    (ShortComplex.mk
      (kernel.ι (gradedPieceMap (coimageImageComparison f) p))
      (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p)
      (by simp [Category.assoc])) ⟶
      (ShortComplex.mk
        (0 : 0 ⟶ Abelian.coimage (gradedPieceMap f p))
        (Abelian.factorThruCoimage (gradedPieceMap f p))
        (by simp)) := by
  -- The chosen kernel of the public coimage-image comparison is killed by the pointwise
  -- factorization because `factorThruCoimage (gr^p(f))` is monic.
  refine ShortComplex.homMk
    (0 : kernel (gradedPieceMap (coimageImageComparison f) p) ⟶ 0)
    (filteredCoimageToPointwiseCoimage f p)
    (𝟙 _)
    ?_
    ?_
  · letI : Mono (Abelian.factorThruCoimage (gradedPieceMap f p)) := by infer_instance
    apply (cancel_mono (Abelian.factorThruCoimage (gradedPieceMap f p))).1
    rw [zero_comp, Category.assoc, filteredCoimageToPointwiseCoimage_comp_factorThruCoimage]
    simp [Category.assoc]
  · simpa [Category.assoc] using
      filteredCoimageToPointwiseCoimage_comp_factorThruCoimage f p

/-- Helper for Lemma 12.19.13: exactness of the public coimage-cokernel row already makes the
graded coimage-image comparison epic. -/
theorem gradedPiece_coimageImageComparison_epi_of_coimage_target_cokernel_exact
    (f : A ⟶ B) (p : ℤ) (hExact : (coimageTargetCokernelShortComplex f p).Exact) :
    Epi (gradedPieceMap (coimageImageComparison f) p) := by
  let S₁ : ShortComplex C := coimageTargetCokernelShortComplex f p
  let S₂ : ShortComplex C := imageCokernelShortComplex f p
  let φ : S₁ ⟶ S₂ := coimageTargetCokernelShortComplexToImageCokernel f p
  have hShort := gradedPiece_image_cokernel_shortExact f p
  letI : Mono S₂.f := by
    change Mono (gradedPieceMap (imageInclusion f) p)
    exact hShort.mono_f
  haveI : Epi φ.τ₂ := by
    change Epi (𝟙 S₁.X₂)
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 S₁.X₃)
    infer_instance
  -- Compare the public coimage row with the canonical image-cokernel short exact row and apply
  -- the dual short-complex four lemma at the left endpoint.
  simpa [S₁, S₂, φ, coimageTargetCokernelShortComplex, imageCokernelShortComplex] using
    (ShortComplex.epi_of_mono_of_epi_of_mono (φ := φ) hExact
      (by infer_instance) (by infer_instance) (by infer_instance))

/-- Helper for Lemma 12.19.13: when both cokernel-side rows are exact, the graded coimage-image
comparison is monic. -/
-- Route correction: the remaining cokernel-side blocker is the monomorphy of
-- `gradedPieceMap (coimageImageComparison f) p`, not a bespoke endpoint statement about its
-- kernel object.
theorem gradedPiece_coimageTargetCokernel_monoBridge_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p) := by
  let e : Abelian.coimage (gradedPieceMap f p) ≅ Limits.image (gradedPieceMap f p) :=
    (asIso (Abelian.coimageImageComparison (gradedPieceMap f p))) ≪≫
      Abelian.imageIsoImage (gradedPieceMap f p)
  haveI : IsIso (pointwiseImageToFilteredImage f p) :=
    pointwiseImageToFilteredImage_isIso_of_cokernel_rows_exact
      f p hCoimageExact hCokernelExact
  have hFactor :
      filteredCoimageToPointwiseCoimage f p ≫ e.hom ≫ pointwiseImageToFilteredImage f p =
        gradedPieceMap (coimageImageComparison f) p := by
    -- Normalize the public graded comparison through the explicit pointwise coimage/image
    -- comparison and the now-isomorphic pointwise image comparison.
    simpa [e, Category.assoc] using
      filteredCoimageToPointwiseCoimage_comp_pointwiseCoimageToFilteredImage f p
  let hHeadPublic := coimageTargetCokernelComparisonHeadExact f p
  let hHeadPointwise := pointwiseCoimageTargetHeadExact f p
  let φ := coimageHeadToPointwiseHeadComparison f p
  -- Route correction: the cokernel-side blocker is now reduced to the left endpoint of the row
  -- comparison `φ`. The exact head rows are now explicit (`hHeadPublic`, `hHeadPointwise`); what
  -- remains is to upgrade the already epic comparison `filteredCoimageToPointwiseCoimage f p`
  -- across this head comparison, then rewrite the public composite through `hFactor` and cancel
  -- the fixed monomorphisms on the pointwise side.
  let _ := hHeadPublic
  let _ := hHeadPointwise
  let _ :=
    filteredCoimageToPointwiseCoimage_epi_of_cokernel_rows_exact f p hCoimageExact hCokernelExact
  let _ := φ
  let _ := hFactor
  -- TODO: use the exact head comparison `φ` together with the already-proved epicity of
  -- `filteredCoimageToPointwiseCoimage f p` to upgrade it to an isomorphism, then transport
  -- monicity of `Abelian.factorThruCoimage (gradedPieceMap f p)` back to the public composite.
  sorry

/-- Helper for Lemma 12.19.13: when both cokernel-side rows are exact, the graded coimage-image
comparison is monic. -/
theorem gradedPiece_coimageImageComparison_mono_of_cokernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p) := by
  letI : Mono (gradedPieceMap (imageInclusion f) p) :=
    (gradedPiece_image_cokernel_shortExact f p).mono_f
  haveI :
      Mono (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p) :=
    gradedPiece_coimageTargetCokernel_monoBridge_of_exact f p hCoimageExact hCokernelExact
  -- Cancel the fixed monic graded image inclusion from the public composite.
  exact
    (mono_comp_iff_of_mono (gradedPieceMap (coimageImageComparison f) p)
      (gradedPieceMap (imageInclusion f) p)).1 inferInstance

/-- Helper for Lemma 12.19.13: the endpoint kernel in the coimage/image-to-cokernel comparison
vanishes once the transported coimage row and the original cokernel row are both exact. -/
theorem kernelCoimageImageComparison_ι_eq_zero_of_cokernel_rows_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    kernel.ι (gradedPieceMap (coimageImageComparison f) p) = 0 := by
  letI : Mono (gradedPieceMap (coimageImageComparison f) p) :=
    gradedPiece_coimageImageComparison_mono_of_cokernel_rows_exact
      f p hCoimageExact hCokernelExact
  -- A monomorphism has zero kernel inclusion.
  simpa using kernel.ι_of_mono (gradedPieceMap (coimageImageComparison f) p)

/-- Helper for Lemma 12.19.13: exactness of the public coimage-cokernel row together with its
source provenance forces the graded map `gr^p(\operatorname{coim} f) ⟶ gr^p(B)` to be monic. -/
theorem gradedPiece_coimageTargetCokernel_mono_of_exact
    (f : A ⟶ B) (p : ℤ)
    (hCoimageExact : (coimageTargetCokernelShortComplex f p).Exact)
    (hCokernelExact : (sourceTargetCokernelShortComplex f p).Exact) :
    Mono (gradedPieceMap (coimageImageComparison f) p ≫ gradedPieceMap (imageInclusion f) p) := by
  -- Reuse the earlier bridge formulation so downstream lemmas stay on the public composite.
  exact gradedPiece_coimageTargetCokernel_monoBridge_of_exact f p hCoimageExact hCokernelExact

/-- Helper for Lemma 12.19.13: exactness of the source-target-cokernel row in every degree forces
the associated-graded coimage-image comparison to be an isomorphism. -/
theorem associatedGradedMap_isIso_of_source_target_cokernel_exact
    (f : A ⟶ B) (hExact : ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  -- Route correction: the stabilized frontier now includes the transported exact row
  -- `gr^p(coim f) ⟶ gr^p(B) ⟶ gr^p(coker f)`. Once the public coimage row is known to be monic in
  -- every degree, the existing epi criterion upgrades the coimage-image comparison to an
  -- isomorphism.
  have hCoimageExact :
      ∀ p : ℤ, (coimageTargetCokernelShortComplex f p).Exact := by
    intro p
    -- Replace `gr^p(A)` by the chosen graded coimage object using the existing epi transport.
    exact coimageTargetCokernelShortComplex_exact_of_source_target_cokernel_exact f p (hExact p)
  have hKernel :
      ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact := by
    intro p
    let α : (coimage f).gradedPiece p ⟶ (image f).gradedPiece p :=
      gradedPieceMap (coimageImageComparison f) p
    letI : Mono (gradedPieceMap (imageInclusion f) p) :=
      (gradedPiece_image_cokernel_shortExact f p).mono_f
    letI : Mono (α ≫ gradedPieceMap (imageInclusion f) p) :=
      gradedPiece_coimageTargetCokernel_mono_of_exact f p (hCoimageExact p) (hExact p)
    letI : Mono α := (mono_comp_iff_of_mono α (gradedPieceMap (imageInclusion f) p)).1 inferInstance
    letI : Epi α :=
      gradedPiece_coimageImageComparison_epi_of_source_target_cokernel_exact f p (hExact p)
    letI : IsIso α := isIso_of_mono_of_epi α
    -- Once the degree-`p` coimage-image comparison is an isomorphism, the public kernel row is
    -- exact by the previously established bridge.
    exact kernel_source_target_exact_of_gradedPiece_coimageImageComparison_isIso f p
  exact associatedGradedMap_isIso_of_kernel_and_source_target_cokernel_exact f hKernel hExact

/-- Helper for Lemma 12.19.13: the five-term exactness statement is exactly the conjunction of the
kernel-side and cokernel-side three-term exactness statements in degree `p`. -/
theorem five_term_exact_iff_kernel_and_cokernel_exact
    (f : A ⟶ B) (p : ℤ) :
    (ComposableArrows.mk₅
      (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap f p)
      (gradedPieceMap (toCokernel f) p)
      (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact ↔
        ((kernelSourceTargetShortComplex f p).Exact ∧
          (sourceTargetCokernelShortComplex f p).Exact) := by
  let S : ComposableArrows C 5 :=
    ComposableArrows.mk₅
      (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap f p)
      (gradedPieceMap (toCokernel f) p)
      (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)
  constructor
  · intro hExact
    constructor
    · -- The middle-left three-term row is the `i = 1` short complex of the five-term sequence.
      simpa [S, kernelSourceTargetShortComplex] using hExact.exact 1
    · -- The middle-right three-term row is the `i = 2` short complex of the five-term sequence.
      simpa [S, sourceTargetCokernelShortComplex] using hExact.exact 2
  · rintro ⟨hKernel, hCokernel⟩
    have hZeroKernel :
        (ShortComplex.mk
          (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
          (gradedPieceMap (kernelι f) p)
          (by simp)).Exact := by
      -- The left endpoint exactness is just monicity of the graded kernel inclusion.
      exact
        ((ShortComplex.mk
          (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
          (gradedPieceMap (kernelι f) p)
          (by simp)).exact_iff_mono (by simp)).2
          ((gradedPiece_kernel_coimage_shortExact f p).mono_f)
    have hZeroCokernel :
        (ShortComplex.mk
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)
          (by simp)).Exact := by
      -- The right endpoint exactness is just epicity of the graded cokernel map.
      exact
        ((ShortComplex.mk
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)
          (by simp)).exact_iff_epi (by simp)).2
          ((gradedPiece_image_cokernel_shortExact f p).epi_g)
    have hTail₂ :
        (ComposableArrows.mk₃
          (gradedPieceMap f p)
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact := by
      -- First package the cokernel-side exactness with the terminal zero map.
      exact ComposableArrows.exact_of_δ₀
        (S := ComposableArrows.mk₃
          (gradedPieceMap f p)
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0))
        (h := by simpa using hCokernel.exact_toComposableArrows)
        (h₀ := by simpa using hZeroCokernel.exact_toComposableArrows)
    have hTail₁ :
        (ComposableArrows.mk₄
          (gradedPieceMap (kernelι f) p)
          (gradedPieceMap f p)
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact := by
      -- Then attach the kernel-side exactness to that tail.
      exact ComposableArrows.exact_of_δ₀
        (S := ComposableArrows.mk₄
          (gradedPieceMap (kernelι f) p)
          (gradedPieceMap f p)
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0))
        (h := by simpa using hKernel.exact_toComposableArrows)
        (h₀ := hTail₂)
    -- Finally add the initial zero map.
    exact ComposableArrows.exact_of_δ₀
      (S := S)
      (h := by simpa [S] using hZeroKernel.exact_toComposableArrows)
      (h₀ := hTail₁)

-- Proof sketch: the equivalence `(1) ↔ (2)` is `strict_iff_coimageImageComparison_isIso`, the
-- kernel/coimage and image/cokernel short exact sequences from Lemma `12.19.12` identify `(3)`
-- with `(4)`, `(5)`, and `(6)`, and finiteness of the filtrations lets one recover `(2)` from
-- `(3)` by descending induction on the filtration degree.
/-- Lemma 12.19.13: for a morphism `f : A ⟶ B` of finite filtered objects in an abelian category,
the following are equivalent: `f` is strict; the filtered coimage-image comparison
`coim(f) ⟶ im(f)` is an isomorphism; the induced morphism
`gr(coim(f)) ⟶ gr(im(f))` is an isomorphism; the sequence
`gr(\ker(f)) ⟶ gr(A) ⟶ gr(B)` is exact in every degree; the sequence
`gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f))` is exact in every degree; and the sequence
`0 ⟶ gr(\ker(f)) ⟶ gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f)) ⟶ 0` is exact in every
degree. -/
@[stacks 0127]
theorem strict_tfae_coimageImageComparison_isIso_and_graded_exactness
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B) :
    List.TFAE
      [ Strict f
      , IsIso (coimageImageComparison f)
      , IsIso (associatedGradedMap (coimageImageComparison f))
      , ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact
      , ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact
      , ∀ p : ℤ,
          (ComposableArrows.mk₅
            (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
            (gradedPieceMap (kernelι f) p)
            (gradedPieceMap f p)
            (gradedPieceMap (toCokernel f) p)
            (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact
      ] := by
  -- Route correction: the only nonformal implication is `(3) → (2)`, and the source proof gets
  -- it by descending induction from a common zero stage for `coim(f)` and `im(f)`.
  tfae_have 1 ↔ 2 := by
    -- The filtered strictness criterion is exactly Lemma `12.19.4`.
    simpa using strict_iff_coimageImageComparison_isIso f
  tfae_have 2 → 3 := by
    intro hIso
    -- Apply the associated-graded functor to the filtered isomorphism.
    letI : IsIso (coimageImageComparison f) := hIso
    change IsIso (FilteredObject.associatedGradedFunctor.map (coimageImageComparison f))
    infer_instance
  tfae_have 3 → 2 := by
    intro hIsoGr
    -- Descending induction from a common zero stage upgrades the graded isomorphism to a
    -- filtered isomorphism of `coim(f) ⟶ im(f)`.
    letI : IsIso (associatedGradedMap (coimageImageComparison f)) := hIsoGr
    exact coimageImageComparison_isIso_of_associatedGradedMap_isIso f hA hB
  tfae_have 3 ↔ 4 := by
    constructor
    · intro hIsoGr p
      -- Evaluate the graded isomorphism at degree `p`, then apply the kernel-side bridge.
      have hIsoPiece :
          IsIso (gradedPieceMap (coimageImageComparison f) p) :=
        gradedPieceMap_isIso_of_associatedGradedMap_isIso'
          (coimageImageComparison f) hIsoGr p
      letI : IsIso (gradedPieceMap (coimageImageComparison f) p) := hIsoPiece
      exact
        kernel_source_target_exact_of_gradedPiece_coimageImageComparison_isIso f p
    · intro hExact
      -- Use the global graded-object bridge rather than a false pointwise converse.
      exact associatedGradedMap_isIso_of_kernel_source_target_exact f hExact
  tfae_have 3 ↔ 5 := by
    constructor
    · intro hIsoGr p
      -- Evaluate the graded isomorphism at degree `p`, then apply the cokernel-side bridge.
      have hIsoPiece :
          IsIso (gradedPieceMap (coimageImageComparison f) p) :=
        gradedPieceMap_isIso_of_associatedGradedMap_isIso'
          (coimageImageComparison f) hIsoGr p
      letI : IsIso (gradedPieceMap (coimageImageComparison f) p) := hIsoPiece
      exact
        source_target_cokernel_exact_of_gradedPiece_coimageImageComparison_isIso f p
    · intro hExact
      -- Use the dual global graded-object bridge rather than a false pointwise converse.
      exact associatedGradedMap_isIso_of_source_target_cokernel_exact f hExact
  tfae_have 4 → 6 := by
    intro hExact p
    -- Convert clause `(4)` to `(5)` through the common clause `(3)`, then reassemble degreewise.
    letI :
        IsIso (associatedGradedMap (coimageImageComparison f)) :=
      associatedGradedMap_isIso_of_kernel_source_target_exact f hExact
    have hIsoPiece :
        IsIso (gradedPieceMap (coimageImageComparison f) p) :=
      gradedPieceMap_isIso_of_associatedGradedMap_isIso
        (coimageImageComparison f) p
    have hCokernel :
        (sourceTargetCokernelShortComplex f p).Exact :=
      by
        letI : IsIso (gradedPieceMap (coimageImageComparison f) p) := hIsoPiece
        exact source_target_cokernel_exact_of_gradedPiece_coimageImageComparison_isIso f p
    exact
      (five_term_exact_iff_kernel_and_cokernel_exact f p).2
        ⟨hExact p, hCokernel⟩
  tfae_have 6 → 4 := by
    intro hExact p
    -- Split the five-term degreewise exactness back at the first internal break.
    exact (five_term_exact_iff_kernel_and_cokernel_exact f p).1 (hExact p) |>.1
  tfae_finish

end FilteredObject.Hom

end CategoryTheory
