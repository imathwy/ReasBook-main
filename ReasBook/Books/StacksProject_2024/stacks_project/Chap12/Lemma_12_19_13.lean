import Mathlib.Data.List.TFAE
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import StacksProject_2024.Chap12.Lemma_12_19_12

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

/-- Helper for Lemma 12.19.13: the left square of the canonical stage-row morphism commutes by
filtration preservation. -/
theorem stageShortComplexMap_left_comm {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ) :
    X.filtration.stageInclusion p ≫ stageMap g p =
      stageMap g (p + 1) ≫ Y.filtration.stageInclusion p := by
  -- The left square is exactly the naturality square for consecutive stage inclusions.
  exact stageInclusion_naturality g p

/-- Helper for Lemma 12.19.13: the right square of the canonical stage-row morphism commutes by
the defining property of the induced map on graded pieces. -/
theorem stageShortComplexMap_right_comm {X Y : FilteredObject C} (g : X ⟶ Y) (p : ℤ) :
    cokernel.π (X.filtration.stageInclusion p) ≫ gradedPieceMap g p =
      stageMap g p ≫ cokernel.π (Y.filtration.stageInclusion p) := by
  -- The graded-piece map is the universal cokernel map induced by the stage square.
  simp [gradedPieceMap, Category.assoc]

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
  exact Limits.IsZero.of_iso (Limits.isZero_zero C) (stageIsoZeroOfEqBot X p hp).symm

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
  -- Route correction: the textbook proof descends from one common zero stage, not from a
  -- two-sided finite interval.
  by_cases hmp : m ≤ p
  · -- Once `p` is at or beyond the common zero stage, both stages are zero.
    exact stageMap_isIso_of_eq_bot g p
      (filtration_eq_bot_of_le hmp hXm)
      (filtration_eq_bot_of_le hmp hYm)
  · -- Below the zero stage, descend one step at a time along the canonical short exact rows.
    have hdesc : ∀ k : ℕ, IsIso (stageMap g (m - k)) := by
      intro k
      induction k with
      | zero =>
          simpa using stageMap_isIso_of_eq_bot g m hXm hYm
      | succ k hk =>
          have hsucc : (m - (Int.ofNat (Nat.succ k))) + 1 = m - Int.ofNat k := by
            omega
          letI : IsIso (stageMap g ((m - Int.ofNat (Nat.succ k)) + 1)) := by
            simpa [hsucc] using hk
          letI : IsIso (gradedPieceMap g (m - Int.ofNat (Nat.succ k))) :=
            gradedPieceMap_isIso_of_associatedGradedMap_isIso g (m - Int.ofNat (Nat.succ k))
          -- Apply the one-step descent lemma at degree `m - (k + 1)`.
          simpa using
            stageMap_isIso_of_stageMap_succ_and_gradedPiece_isIso g
              (m - Int.ofNat (Nat.succ k))
    have hnonneg : 0 ≤ m - p := by
      omega
    have hp_eq : p = m - Int.toNat (m - p) := by
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    -- Reindex the descended isomorphism back to the requested degree `p`.
    simpa [hp_eq] using hdesc (Int.toNat (m - p))

/-- Helper for Lemma 12.19.13: stagewise isomorphisms upgrade an underlying isomorphism to an
isomorphism of filtered objects. -/
theorem isIso_of_hom_iso_of_stageMap_isIso {X Y : FilteredObject C} (g : X ⟶ Y) [IsIso g.hom]
    (hstage : ∀ p : ℤ, IsIso (stageMap g p)) : IsIso g := by
  -- Build the filtered inverse from the inverse ambient map and the inverse stage maps.
  let gInv : Y ⟶ X :=
    { hom := inv g.hom
      preserves := fun p ↦ by
        let u : F^{p} Y ⟶ F^{p} X := inv (stageMap g p)
        refine ⟨u, ?_⟩
        -- The inverse stage map is characterized by cancelling `stageMap g p` against
        -- `stageMap_comm g p` and the ambient inverse relation.
        calc
          u ≫ (X.filtration.obj p).arrow
              = u ≫ ((X.filtration.obj p).arrow ≫ (g.hom ≫ inv g.hom)) := by
                  simp [Category.assoc]
          _ = u ≫ (stageMap g p ≫ (Y.filtration.obj p).arrow ≫ inv g.hom) := by
                rw [stageMap_comm]
                simp [Category.assoc]
          _ = (u ≫ stageMap g p) ≫ (Y.filtration.obj p).arrow ≫ inv g.hom := by
                simp [Category.assoc]
          _ = (Y.filtration.obj p).arrow ≫ inv g.hom := by
                simp [u, Category.assoc] }
  refine ⟨⟨gInv, ?_, ?_⟩⟩
  · -- The left inverse identity is checked after forgetting to the ambient category.
    apply FilteredObject.forget.map_injective
    change inv g.hom ≫ g.hom = 𝟙 Y.obj
    simp
  · -- The right inverse identity is checked similarly on the underlying morphisms.
    apply FilteredObject.forget.map_injective
    change g.hom ≫ inv g.hom = 𝟙 X.obj
    simp

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
  -- The induced filtration on the image subobject is the pullback of the ambient stage.
  change (Subobject.pullback (imageSubobject f.hom).arrow).obj (B.filtration m) = ⊥
  rw [hBm]
  simp

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
  simpa using
    (NatTrans.isIso_iff_isIso_app (associatedGradedMap g)).1 hg (Discrete.mk p)

/-- Helper for Lemma 12.19.13: evaluation at a fixed degree preserves homology for graded
objects. -/
theorem gradedObject_eval_preservesHomology (p : ℤ) :
    Functor.PreservesHomology (GradedObject.eval p : GradedObject ℤ C ⥤ C) := by
  -- Evaluation is pointwise on the functor category `Discrete ℤ ⥤ C`, so it preserves kernels
  -- and cokernels and therefore preserves homology.
  let E := piEquivalenceFunctorDiscrete ℤ C
  refine
    { preservesKernels := ?_
      preservesCokernels := ?_ }
  · intro X Y f
    simpa [E, GradedObject.eval] using
      (inferInstance : PreservesLimit (parallelPair f 0)
        (E.functor ⋙ (evaluation (Discrete ℤ) C).obj (Discrete.mk p)))
  · intro X Y f
    simpa [E, GradedObject.eval] using
      (inferInstance : PreservesColimit (parallelPair f 0)
        (E.functor ⋙ (evaluation (Discrete ℤ) C).obj (Discrete.mk p)))

/-- Helper for Lemma 12.19.13: a short complex of graded objects is exact exactly when every
evaluated degreewise short complex is exact. -/
theorem graded_shortComplex_exact_iff_exact_app (S : ShortComplex (GradedObject ℤ C)) :
    S.Exact ↔ ∀ p : ℤ, (S.map (GradedObject.eval p)).Exact := by
  let F : Discrete ℤ → GradedObject ℤ C ⥤ C := fun p ↦ GradedObject.eval p.as
  letI : ∀ p : Discrete ℤ, Functor.PreservesHomology (F p) := fun p ↦
    gradedObject_eval_preservesHomology (C := C) p.as
  let hEval : JointlyReflectIsomorphisms F := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro p
    simpa [F] using (inferInstance : IsIso ((F p).map f))
  constructor
  · intro hS p
    -- Apply the functor-category exactness reflection theorem and then evaluate at `p`.
    simpa [F] using (hEval.exact_iff S).1 hS (Discrete.mk p)
  · intro hS
    -- Conversely, reassemble exactness from the degreewise exact short complexes.
    exact (hEval.exact_iff S).2 fun p ↦ by
      simpa [F] using hS p.as

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
  simpa [associatedGradedMap, gradedPieceMap_comp] using
    congrArg (fun k ↦ gradedPieceMap k p) hcomp

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

/-- Helper for Lemma 12.19.13: the canonical factorization
`A ⟶ coim(f) ⟶ im(f) ⟶ B` remains the original map after taking the `p`-th graded piece. -/
theorem gradedPiece_toQuotient_comp_coimageImageComparison_comp_imageInclusion
    (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
        gradedPieceMap (coimageImageComparison f) p ≫
          gradedPieceMap (imageInclusion f) p =
      gradedPieceMap f p := by
  -- First identify the filtered factorization, then pass to graded pieces.
  have hfactor :
      A.toQuotient (kernelSubobject f.hom) ≫ coimageImageComparison f ≫ imageInclusion f = f := by
    apply FilteredObject.forget.map_injective
    change
      Abelian.coimage.π f.hom ≫ (coimageImageComparison f).hom ≫ Abelian.image.ι f.hom = f.hom
    rw [coimageImageComparison_hom]
    simpa [Category.assoc] using Abelian.coimage_image_factorisation f.hom
  simpa [Category.assoc, gradedPieceMap_comp] using
    congrArg (fun g ↦ gradedPieceMap g p) hfactor

/-- Helper for Lemma 12.19.13: exactness of
`gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(B)` upgrades the chosen kernel-stage map to the actual kernel of
`gr^p(f)`. -/
theorem kernel_source_target_is_kernel
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
      gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫ e.hom =
        Abelian.coimage.π (gradedPieceMap f p) := by
  let β : gr^{p} A ⟶ gr^{p} B := gradedPieceMap f p
  let k : gr^{p} (kernelFilteredObject f) ⟶ gr^{p} A := gradedPieceMap (kernelι f) p
  let q : gr^{p} A ⟶ gr^{p} (coimage f) :=
    gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p
  have hKernel :
      IsLimit
        (KernelFork.ofι
          k
          (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)) :=
    kernel_source_target_is_kernel f p hExact
  let eKernel : gr^{p} (kernelFilteredObject f) ≅ kernel β :=
    IsLimit.conePointUniqueUpToIso hKernel (kernelIsKernel β)
  have hk :
      eKernel.hom ≫ kernel.ι β = k := by
    -- This is the standard comparison between the chosen kernel owner and the canonical one.
    simpa [β, k, eKernel] using
      hKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel β) WalkingParallelPair.zero
  let Scoim : ShortComplex C := kernelCoimageShortComplex f p
  have hScoim : Scoim.ShortExact := by
    -- Lemma `12.19.12` supplies the short exact kernel-coimage row degreewise.
    simpa [Scoim, kernelCoimageShortComplex] using gradedPiece_kernel_coimage_shortExact f p
  have hq_zero :
      k ≫ q = 0 := by
    simpa [k, q] using
      gradedPieceMap_comp_zero (kernelι f) (A.toQuotient (kernelSubobject f.hom))
        (kernelι_comp_toCoimage f) p
  obtain ⟨hq_cokernel⟩ :=
    (Scoim.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hScoim.exact, hScoim.epi_g⟩
  have hcoimage_zero :
      kernel.ι β ≫ q = 0 := by
    -- Transport the vanishing of `k ≫ q` across the canonical identification of kernels.
    apply (cancel_epi eKernel.hom).1
    calc
      eKernel.hom ≫ (kernel.ι β ≫ q) = (eKernel.hom ≫ kernel.ι β) ≫ q := by
            simp [Category.assoc]
      _ = k ≫ q := by rw [hk]
      _ = 0 := hq_zero
  have hcoimage_cokernel :
      IsColimit (CokernelCofork.ofπ q hcoimage_zero) := by
    -- Any morphism annihilating `kernel.ι β` also annihilates the chosen kernel map `k`.
    refine CokernelCofork.IsColimit.ofπ' q hcoimage_zero ?_
    intro Z s hs
    have hs' : k ≫ s = 0 := by
      calc
        k ≫ s = (eKernel.hom ≫ kernel.ι β) ≫ s := by rw [hk]
        _ = eKernel.hom ≫ (kernel.ι β ≫ s) := by simp [Category.assoc]
        _ = 0 := by simp [hs, Category.assoc]
    exact ⟨hq_cokernel.desc (CokernelCofork.ofπ s hs'), by
      simpa [q] using hq_cokernel.fac (CokernelCofork.ofπ s hs') WalkingParallelPair.one⟩
  let e : (coimage f).gradedPiece p ≅ Abelian.coimage β :=
    IsColimit.coconePointUniqueUpToIso hcoimage_cokernel (cokernelIsCokernel (kernel.ι β))
  have he :
      q ≫ e.hom = Abelian.coimage.π β := by
    -- The cocone-leg comparison records that `q` is the chosen coimage projection.
    simpa [β, q, e] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        hcoimage_cokernel
        (cokernelIsCokernel (kernel.ι β))
        WalkingParallelPair.one
  exact ⟨e, he⟩

/-- Helper for Lemma 12.19.13: exactness of
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)` upgrades the chosen graded cokernel map to
the actual cokernel of `gr^p(f)`. -/
theorem source_target_cokernel_is_cokernel
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
  let β : gr^{p} A ⟶ gr^{p} B := gradedPieceMap f p
  let i : gr^{p} (image f) ⟶ gr^{p} B := gradedPieceMap (imageInclusion f) p
  let π : gr^{p} B ⟶ gr^{p} (cokernelFilteredObject f) := gradedPieceMap (toCokernel f) p
  have hπ_cokernel :
      IsColimit
        (CokernelCofork.ofπ
          π
          (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p)) :=
    source_target_cokernel_is_cokernel f p hExact
  let Timg : ShortComplex C := imageCokernelShortComplex f p
  have hTimg : Timg.ShortExact := by
    -- Lemma `12.19.12` supplies the short exact image-cokernel row degreewise.
    simpa [Timg, imageCokernelShortComplex] using gradedPiece_image_cokernel_shortExact f p
  obtain ⟨hi_kernel⟩ :=
    (Timg.exact_and_mono_f_iff_f_is_kernel).1 ⟨hTimg.exact, hTimg.mono_f⟩
  let eCok : cokernel β ≅ gr^{p} (cokernelFilteredObject f) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel β) hπ_cokernel
  have hπ :
      cokernel.π β ≫ eCok.hom = π := by
    -- This is the standard comparison between the canonical cokernel and the chosen owner.
    simpa [β, π, eCok] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel β)
        hπ_cokernel
        WalkingParallelPair.one
  have himage_zero :
      i ≫ cokernel.π β = 0 := by
    -- Transport the vanishing of `i ≫ π` across the canonical identification of cokernels.
    apply (cancel_mono eCok.hom).1
    calc
      (i ≫ cokernel.π β) ≫ eCok.hom = i ≫ (cokernel.π β ≫ eCok.hom) := by
            simp [Category.assoc]
      _ = i ≫ π := by rw [hπ]
      _ = 0 := by
            simpa [i, π] using
              gradedPieceMap_comp_zero (imageInclusion f) (toCokernel f)
                (imageInclusion_comp_toCokernel f) p
  have himage_kernel :
      IsLimit (KernelFork.ofι i himage_zero) := by
    -- Any morphism annihilating `cokernel.π β` also annihilates the chosen cokernel map `π`.
    refine KernelFork.IsLimit.ofι' i himage_zero ?_
    intro W s hs
    have hs' : s ≫ π = 0 := by
      calc
        s ≫ π = s ≫ (cokernel.π β ≫ eCok.hom) := by rw [hπ]
        _ = (s ≫ cokernel.π β) ≫ eCok.hom := by simp [Category.assoc]
        _ = 0 := by simp [hs, Category.assoc]
    exact ⟨hi_kernel.lift (KernelFork.ofι s hs'), by
      simpa [i] using hi_kernel.fac (KernelFork.ofι s hs') WalkingParallelPair.zero⟩
  let e : Abelian.image β ≅ (image f).gradedPiece p :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π β)) himage_kernel
  have he :
      e.hom ≫ i = Abelian.image.ι β := by
    -- The cone-leg comparison records that `i` is the chosen image inclusion.
    simpa [β, i, e] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (kernelIsKernel (cokernel.π β))
        himage_kernel
        WalkingParallelPair.zero
  exact ⟨e, he⟩

/-- Helper for Lemma 12.19.13: if the degree-`p` graded coimage-image comparison is an
isomorphism, then the kernel-source-target row is exact in degree `p`. -/
theorem kernel_source_target_exact_of_gradedPiece_coimageImageComparison_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (kernelSourceTargetShortComplex f p).Exact := by
  let Tcoim : ShortComplex C := kernelCoimageShortComplex f p
  have hTcoim : Tcoim.ShortExact := by
    -- Lemma `12.19.12` gives the kernel-to-coimage short exact row degreewise.
    simpa [Tcoim, kernelCoimageShortComplex] using gradedPiece_kernel_coimage_shortExact f p
  have hzero_img :
      gradedPieceMap (kernelι f) p ≫
          (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
            gradedPieceMap (coimageImageComparison f) p) =
        0 := by
    -- The kernel row still composes to zero after postcomposing with the graded comparison.
    calc
      gradedPieceMap (kernelι f) p ≫
          (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
            gradedPieceMap (coimageImageComparison f) p)
          =
            (gradedPieceMap (kernelι f) p ≫
              gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p) ≫
                gradedPieceMap (coimageImageComparison f) p := by
                  simp [Category.assoc]
      _ = 0 := by
        rw [gradedPieceMap_comp_zero (kernelι f)
          (A.toQuotient (kernelSubobject f.hom)) (kernelι_comp_toCoimage f) p]
        simp
  let Timg : ShortComplex C :=
    ShortComplex.mk
      (gradedPieceMap (kernelι f) p)
      (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
        gradedPieceMap (coimageImageComparison f) p)
      hzero_img
  have hφimg₁₂ :
      Tcoim.f ≫ 𝟙 (gr^{p} A) = (𝟙 (gr^{p} (kernelFilteredObject f))) ≫ Timg.f := by
    simp [Tcoim, Timg]
  have hφimg₂₃ :
      Tcoim.g ≫ gradedPieceMap (coimageImageComparison f) p =
        (𝟙 (gr^{p} A)) ≫ Timg.g := by
    simp [Tcoim, Timg, Category.assoc]
  have hφimg : Tcoim ⟶ Timg := by
    exact ShortComplex.homMk
      (𝟙 _)
      (𝟙 _)
      (gradedPieceMap (coimageImageComparison f) p)
      hφimg₁₂
      hφimg₂₃
  have hExactImg : Timg.Exact := by
    -- Transport exactness across the isomorphism on the third term.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono hφimg).1 hTcoim.exact
  letI : Mono (gradedPieceMap (imageInclusion f) p) := by
    -- The image-to-cokernel row is always short exact degreewise.
    simpa [imageCokernelShortComplex] using (gradedPiece_image_cokernel_shortExact f p).mono_f
  have hφbeta₂₃ :
      Timg.g ≫ gradedPieceMap (imageInclusion f) p =
        (𝟙 (gr^{p} A)) ≫ (kernelSourceTargetShortComplex f p).g := by
    simpa [Timg, kernelSourceTargetShortComplex, Category.assoc] using
      gradedPiece_toQuotient_comp_coimageImageComparison_comp_imageInclusion f p
  have hφbeta₁₂ :
      Timg.f ≫ 𝟙 (gr^{p} A) =
        (𝟙 (gr^{p} (kernelFilteredObject f))) ≫ (kernelSourceTargetShortComplex f p).f := by
    simp [Timg, kernelSourceTargetShortComplex]
  have hφbeta : Timg ⟶ kernelSourceTargetShortComplex f p := by
    exact ShortComplex.homMk
      (𝟙 _)
      (𝟙 _)
      (gradedPieceMap (imageInclusion f) p)
      hφbeta₁₂
      hφbeta₂₃
  -- The mono inclusion `gr^p(im f) ↪ gr^p(B)` turns the intermediate exact row into the
  -- desired kernel-source-target row.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono hφbeta).1 hExactImg

/-- Helper for Lemma 12.19.13: exactness of the kernel-source-target row in every degree forces
the associated-graded coimage-image comparison to be an isomorphism. -/
theorem associatedGradedMap_isIso_of_kernel_source_target_exact
    (f : A ⟶ B) (hExact : ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  -- Route correction: the converse direction must be proved globally in `GradedObject ℤ C`,
  -- not by forcing a false pointwise `Exact ↔ IsIso` statement.
  have hGlobalExact :
      (ShortComplex.mk
        (associatedGradedMap (kernelι f))
        (associatedGradedMap f)
        (associatedGradedMap_comp_zero (kernelι f) f (kernelι_comp f))).Exact := by
    -- Reassemble the degreewise kernel exactness into exactness of the graded-object short complex.
    simpa [associatedGradedMap, kernelSourceTargetShortComplex] using
      (graded_shortComplex_exact_iff_exact_app
        (S := (ShortComplex.mk
          (associatedGradedMap (kernelι f))
          (associatedGradedMap f)
          (associatedGradedMap_comp_zero (kernelι f) f (kernelι_comp f)))).2 hExact
  -- TODO: show the cokernel of `associatedGradedMap (kernelι f)` coming from `hGlobalExact`
  -- agrees with `associatedGradedMap (A.toQuotient (kernelSubobject f.hom))`, then compare that
  -- canonical coimage of `associatedGradedMap f` with `associatedGradedMap (imageInclusion f)` by
  -- the functor-category universal property in `GradedObject ℤ C`.
  sorry

/-- Helper for Lemma 12.19.13: if the degree-`p` graded coimage-image comparison is an
isomorphism, then the source-target-cokernel row is exact in degree `p`. -/
theorem source_target_cokernel_exact_of_gradedPiece_coimageImageComparison_isIso
    (f : A ⟶ B) (p : ℤ) [IsIso (gradedPieceMap (coimageImageComparison f) p)] :
    (sourceTargetCokernelShortComplex f p).Exact := by
  let Timg : ShortComplex C := imageCokernelShortComplex f p
  have hTimg : Timg.ShortExact := by
    -- Lemma `12.19.12` gives the image-to-cokernel short exact row degreewise.
    simpa [Timg, imageCokernelShortComplex] using gradedPiece_image_cokernel_shortExact f p
  letI : Epi
      (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
        gradedPieceMap (coimageImageComparison f) p) := by
    -- The left map into `gr^p(im f)` is the composition of an epi with an isomorphism.
    letI : Epi (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p) := by
      simpa [kernelCoimageShortComplex] using
        (gradedPiece_kernel_coimage_shortExact f p).epi_g
    infer_instance
  have hφ₁₂ :
      (sourceTargetCokernelShortComplex f p).f ≫ 𝟙 (gr^{p} B) =
        (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
          gradedPieceMap (coimageImageComparison f) p) ≫ Timg.f := by
    simpa [sourceTargetCokernelShortComplex, Timg, Category.assoc] using
      (gradedPiece_toQuotient_comp_coimageImageComparison_comp_imageInclusion f p).symm
  have hφ₂₃ :
      (sourceTargetCokernelShortComplex f p).g ≫ 𝟙 ((cokernelFilteredObject f).gradedPiece p) =
        (𝟙 (gr^{p} B)) ≫ Timg.g := by
    simp [sourceTargetCokernelShortComplex, Timg]
  have hφ : sourceTargetCokernelShortComplex f p ⟶ Timg := by
    exact ShortComplex.homMk
      (gradedPieceMap (A.toQuotient (kernelSubobject f.hom)) p ≫
        gradedPieceMap (coimageImageComparison f) p)
      (𝟙 _)
      (𝟙 _)
      hφ₁₂
      hφ₂₃
  -- Transport exactness back from the short exact image-cokernel row.
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono hφ).2 hTimg.exact

/-- Helper for Lemma 12.19.13: exactness of the source-target-cokernel row in every degree forces
the associated-graded coimage-image comparison to be an isomorphism. -/
theorem associatedGradedMap_isIso_of_source_target_cokernel_exact
    (f : A ⟶ B) (hExact : ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := by
  -- Route correction: this dual converse must likewise be proved in the graded functor category,
  -- not by forcing another false pointwise biconditional.
  have hGlobalExact :
      (ShortComplex.mk
        (associatedGradedMap f)
        (associatedGradedMap (toCokernel f))
        (associatedGradedMap_comp_zero f (toCokernel f) (comp_toCokernel f))).Exact := by
    -- Reassemble the degreewise cokernel exactness into exactness of the graded-object short
    -- complex.
    simpa [associatedGradedMap, sourceTargetCokernelShortComplex] using
      (graded_shortComplex_exact_iff_exact_app
        (S := (ShortComplex.mk
          (associatedGradedMap f)
          (associatedGradedMap (toCokernel f))
          (associatedGradedMap_comp_zero f (toCokernel f) (comp_toCokernel f)))).2 hExact
  -- TODO: identify the kernel of `associatedGradedMap (toCokernel f)` coming from `hGlobalExact`
  -- with `associatedGradedMap (imageInclusion f)`, then compare that canonical image of
  -- `associatedGradedMap f` with `associatedGradedMap (A.toQuotient (kernelSubobject f.hom))`
  -- using the dual functor-category universal property in `GradedObject ℤ C`.
  sorry

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
  let kι := gradedPieceMap (kernelι f) p
  let g := gradedPieceMap f p
  let π := gradedPieceMap (toCokernel f) p
  let S₅ : ComposableArrows C 5 :=
    ComposableArrows.mk₅
      (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
      kι g π (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)
  constructor
  · intro hExact
    -- Split the five-term exactness twice at the left endpoint to isolate the two middle
    -- three-term clauses.
    have hsplit₀ := (ComposableArrows.exact_iff_δ₀ S₅).1 hExact
    have hsplit₁ := (ComposableArrows.exact_iff_δ₀ S₅.δ₀).1 hsplit₀.2
    have hsplit₂ := (ComposableArrows.exact_iff_δ₀ S₅.δ₀.δ₀).1 hsplit₁.2
    constructor
    · simpa [S₅, kι, g, kernelSourceTargetShortComplex] using hsplit₁.1
    · simpa [S₅, g, π, sourceTargetCokernelShortComplex] using hsplit₂.1
  · intro hExact
    rcases hExact with ⟨hKernel, hCokernel⟩
    have hKernel' :
        (ComposableArrows.mk₂ kι g).Exact := by
      -- Rewrite the short-complex exactness into the `ComposableArrows.mk₂` owner used by
      -- `exact_of_δ₀`.
      simpa [kι, g, kernelSourceTargetShortComplex] using
        ((kernelSourceTargetShortComplex f p).exact_iff_exact_toComposableArrows).1 hKernel
    have hCokernel' :
        (ComposableArrows.mk₂ g π).Exact := by
      -- Do the same for the source-target-cokernel row.
      simpa [g, π, sourceTargetCokernelShortComplex] using
        ((sourceTargetCokernelShortComplex f p).exact_iff_exact_toComposableArrows).1 hCokernel
    have hleftZero : (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p) ≫ kι = 0 := by
      simp
    let Sleft : ShortComplex C :=
      ShortComplex.mk (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p) kι hleftZero
    have hleft :
        (ComposableArrows.mk₂ (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p) kι).Exact := by
      -- The initial two-term row is exact because `gr^p(\ker f) ⟶ gr^p(A)` is mono.
      change Sleft.toComposableArrows.Exact
      rw [← Sleft.exact_iff_exact_toComposableArrows]
      exact (Sleft.exact_iff_mono rfl).2 (by
        simpa [kernelCoimageShortComplex] using
          (gradedPiece_kernel_coimage_shortExact f p).mono_f)
    have hrightZero : π ≫ (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0) = 0 := by
      simp
    let Sright : ShortComplex C :=
      ShortComplex.mk π (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0) hrightZero
    have hright :
        (ComposableArrows.mk₂ π (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact := by
      -- The terminal two-term row is exact because `gr^p(B) ⟶ gr^p(\operatorname{coker} f)` is
      -- epi.
      change Sright.toComposableArrows.Exact
      rw [← Sright.exact_iff_exact_toComposableArrows]
      exact (Sright.exact_iff_epi rfl).2 (by
        simpa [imageCokernelShortComplex] using
          (gradedPiece_image_cokernel_shortExact f p).epi_g)
    have htail₃ :
        (ComposableArrows.mk₃ g π (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact := by
      -- Append the exact terminal two-term row to clause `(5)`.
      exact ComposableArrows.exact_of_δ₀ hCokernel' hright
    have htail₄ :
        (ComposableArrows.mk₄ kι g π (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact := by
      -- Prepend clause `(4)` to the right-hand exact tail.
      exact ComposableArrows.exact_of_δ₀ hKernel' htail₃
    -- Finally prepend the exact initial two-term row.
    exact ComposableArrows.exact_of_δ₀ hleft htail₄

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
