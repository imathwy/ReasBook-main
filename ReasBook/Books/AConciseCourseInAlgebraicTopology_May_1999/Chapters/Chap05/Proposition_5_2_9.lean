import Mathlib.CategoryTheory.Adjunction.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_8

open CategoryTheory

universe u v w

-- Semantic recall via `lean_leansearch` only surfaced the generic `CompactlyGenerated` owner, so
-- the source-facing adjunction API below is verified locally against
-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_8` and `CategoryTheory.Adjunction.Basic`.

/-- The identity map from the k-ification of `Y` to the original space `Y` is continuous. -/
theorem continuousKifiedForget (Y : Type v) [TopologicalSpace Y] :
    Continuous (fun y : Kified Y ↦ y.of) := by
  -- First forget from the induced k-topology to the raw compactly generated topology.
  have hForgetToCompactlyGenerated :
      @Continuous (Kified Y) Y (kifiedTopologicalSpace Y)
        (TopologicalSpace.compactlyGenerated Y) Kified.of := by
    simpa [kifiedTopologicalSpace] using
      (continuous_induced_dom :
        @Continuous (Kified Y) Y
          (TopologicalSpace.induced Kified.of (TopologicalSpace.compactlyGenerated Y))
          (TopologicalSpace.compactlyGenerated Y) Kified.of)
  have hIdFromCompactlyGenerated :
      @Continuous Y Y (TopologicalSpace.compactlyGenerated Y) ‹TopologicalSpace Y› id :=
    continuous_id_compactlyGenerated (X := Y)
  -- Then compose with the identity map from the compactly generated topology back to `Y`.
  simpa [Function.comp] using
    (@Continuous.comp (Kified Y) Y Y (kifiedTopologicalSpace Y)
      (TopologicalSpace.compactlyGenerated Y) ‹TopologicalSpace Y› Kified.of id
      hIdFromCompactlyGenerated hForgetToCompactlyGenerated)

/-- Helper for Proposition 5.2.9: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by `TopologicalSpace.compactlyGenerated`. -/
private theorem continuousToCompactlyGeneratedOfCompHaus
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type v} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, v} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-Hausdorff map is one of the generators for the compactly generated topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, v} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- A continuous map from a compactly generated source remains continuous into the k-ification of
its target. -/
theorem continuousToKifiedOfContinuous
    {X : Type u} [TopologicalSpace X] [UCompactlyGeneratedSpace.{v} X]
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous (fun x : X ↦ Kified.mk (f x)) := by
  -- Maps into the induced k-topology are controlled by the corresponding maps into the raw
  -- compactly generated topology.
  have hToCompactlyGenerated :
      @Continuous X Y ‹TopologicalSpace X›
        (TopologicalSpace.compactlyGenerated.{v, v} Y) f := by
    -- Because the source is compactly generated, it is enough to test the map on compact
    -- Hausdorff probes.
    refine continuous_from_uCompactlyGeneratedSpace
      (tY := TopologicalSpace.compactlyGenerated Y) (fun x : X ↦ f x) ?_
    intro S g
    -- Each compact-Hausdorff probe lands continuously in the compactly generated codomain by
    -- construction of that topology.
    simpa [Function.comp] using
      (continuousToCompactlyGeneratedOfCompHaus (Y := Y) (f := f ∘ g)
        (hf := hf.comp g.continuous))
  have hCompositeToCompactlyGenerated :
      @Continuous X Y ‹TopologicalSpace X›
        (TopologicalSpace.compactlyGenerated.{v, v} Y)
        (Kified.of ∘ fun x : X ↦ Kified.mk (f x)) := by
    simpa [Function.comp] using hToCompactlyGenerated
  simpa [Function.comp, kifiedTopologicalSpace] using
    (continuous_induced_rng.2 hCompositeToCompactlyGenerated :
      @Continuous X (Kified Y) ‹TopologicalSpace X›
        (TopologicalSpace.induced Kified.of (TopologicalSpace.compactlyGenerated.{v, v} Y))
        (fun x : X ↦ Kified.mk (f x)))

/-- The counit component `j (k Y) ⟶ Y` of the k-ification adjunction is the identity on the
underlying points. -/
abbrev weakHausdorffKificationCounitApp (Y : weakHausdorffSpaceCat.{w}) :
    compactlyGeneratedWeakHausdorffToWeakHausdorff.obj (weakHausdorffKificationObj Y) ⟶
      Y :=
  let _ : TopologicalSpace (Kified Y.obj) := kifiedTopologicalSpace.{w, w} Y.obj
  ObjectProperty.homMk <|
    TopCat.ofHom ⟨fun y : Kified Y.obj ↦ y.of, continuousKifiedForget Y.obj⟩

/-- The unit component `X ⟶ k (j X)` of the k-ification adjunction is the identity on the
underlying points. -/
abbrev weakHausdorffKificationUnitApp (X : compactlyGeneratedWeakHausdorffSpaceCat) :
    X ⟶ weakHausdorffKificationObj (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X) :=
  let Y := compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X
  let _ : TopologicalSpace (Kified (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X).obj) :=
    kifiedTopologicalSpace.{w, w} (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X).obj
  let _ : CompactlyGeneratedWeakHausdorffSpace X.obj := X.property
  let g : X.obj → Y.obj := fun x ↦ x
  ObjectProperty.homMk <|
    TopCat.ofHom
      ⟨fun x : X.obj ↦
          (Kified.mk (g x) : Kified Y.obj),
        continuousToKifiedOfContinuous continuous_id⟩

/-- The forward map `U(X, k Y) → wU(j X, Y)` is composition with the counit
`j (k Y) ⟶ Y`. -/
private abbrev weakHausdorffKificationHomEquivToFun
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w}) :
    (X ⟶ weakHausdorffKificationObj Y) →
      (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) :=
  fun f ↦ compactlyGeneratedWeakHausdorffToWeakHausdorff.map f ≫ weakHausdorffKificationCounitApp Y

/-- The inverse map `wU(j X, Y) → U(X, k Y)` is the same underlying function, viewed as landing in
the k-ification of `Y`. -/
private abbrev weakHausdorffKificationHomEquivInvFun
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w}) :
    (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) →
      (X ⟶ weakHausdorffKificationObj Y) :=
  fun f ↦
    let _ : TopologicalSpace (Kified Y.obj) := kifiedTopologicalSpace.{w, w} Y.obj
    let _ : UCompactlyGeneratedSpace X.obj :=
      X.property.toUCompactlyGeneratedSpace
    let g := f.hom.hom
    ObjectProperty.homMk <|
      TopCat.ofHom
        ⟨fun x : X.obj ↦ Kified.mk (g x),
          continuousToKifiedOfContinuous g.continuous⟩

/-- The source-oriented Hom-set equivalence for the k-ification adjunction is left inverse to the
map induced by the universal comparison `j (k Y) ⟶ Y`. -/
private theorem weakHausdorffKificationHomEquiv_left_inv
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w})
    (f : compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) :
    weakHausdorffKificationHomEquivToFun X Y (weakHausdorffKificationHomEquivInvFun X Y f) = f :=
  by
    -- Unfold the comparison maps and reduce the claim to equality
    -- of the underlying continuous maps.
    simp only [weakHausdorffKificationHomEquivToFun, weakHausdorffKificationHomEquivInvFun,
      compactlyGeneratedWeakHausdorffToWeakHausdorff_map]
    apply ObjectProperty.hom_ext
    ext x
    rfl

/-- The source-oriented Hom-set equivalence for the k-ification adjunction is right inverse to the
map induced by the universal comparison `j (k Y) ⟶ Y`. -/
private theorem weakHausdorffKificationHomEquiv_right_inv
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w})
    (f : X ⟶ weakHausdorffKificationObj Y) :
    weakHausdorffKificationHomEquivInvFun X Y (weakHausdorffKificationHomEquivToFun X Y f) = f :=
  by
    -- Unfold the comparison maps and compare the underlying pointwise functions into `Kified Y`.
    simp only [weakHausdorffKificationHomEquivToFun, weakHausdorffKificationHomEquivInvFun,
      compactlyGeneratedWeakHausdorffToWeakHausdorff_map]
    apply ObjectProperty.hom_ext
    ext x
    change Kified.mk ((f.hom.hom x).of) = f.hom.hom x
    cases f.hom.hom x
    rfl

/-- For `X ∈ U` and `Y ∈ wU`, morphisms `X ⟶ k Y` in `U` are naturally
equivalent to morphisms `j X ⟶ Y` in `wU`. -/
def weakHausdorffKificationHomEquiv
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w}) :
    (X ⟶ weakHausdorffKificationObj Y) ≃
      (compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) where
  toFun := weakHausdorffKificationHomEquivToFun X Y
  invFun := weakHausdorffKificationHomEquivInvFun X Y
  left_inv := weakHausdorffKificationHomEquiv_right_inv X Y
  right_inv := weakHausdorffKificationHomEquiv_left_inv X Y

/-- Naturality in the `X`-variable for the Hom-set equivalence defining the k-ification
adjunction. -/
private theorem weakHausdorffKificationHomEquiv_naturality_left_symm
    {X' X : compactlyGeneratedWeakHausdorffSpaceCat} {Y : weakHausdorffSpaceCat.{w}}
    (f : X' ⟶ X) (g : X ⟶ weakHausdorffKificationObj Y) :
    weakHausdorffKificationHomEquiv X' Y (f ≫ g) =
      compactlyGeneratedWeakHausdorffToWeakHausdorff.map f ≫
        weakHausdorffKificationHomEquiv X Y g := by
  -- The forward comparison is postcomposition with the counit, so left naturality is functoriality.
  change weakHausdorffKificationHomEquivToFun X' Y (f ≫ g) =
      compactlyGeneratedWeakHausdorffToWeakHausdorff.map f ≫
        weakHausdorffKificationHomEquivToFun X Y g
  rw [weakHausdorffKificationHomEquivToFun, weakHausdorffKificationHomEquivToFun, Functor.map_comp]
  simp [Category.assoc]

/-- Naturality in the `Y`-variable for the Hom-set equivalence defining the k-ification
adjunction. -/
private theorem weakHausdorffKificationHomEquiv_naturality_right
    {X : compactlyGeneratedWeakHausdorffSpaceCat} {Y Y' : weakHausdorffSpaceCat.{w}}
    (f : compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) (g : Y ⟶ Y') :
    (weakHausdorffKificationHomEquiv X Y').symm (f ≫ g) =
      (weakHausdorffKificationHomEquiv X Y).symm f ≫ weakHausdorffKification.map g := by
  -- Both sides are the same underlying function `x ↦ Kified.mk (g (f x))`.
  change weakHausdorffKificationHomEquivInvFun X Y' (f ≫ g) =
    weakHausdorffKificationHomEquivInvFun X Y f ≫ weakHausdorffKification.map g
  simp only [weakHausdorffKificationHomEquivInvFun, weakHausdorffKification]
  apply ObjectProperty.hom_ext
  ext x
  rfl

/-- The Hom-set equivalences for the k-ification comparison satisfy the naturality axioms needed
to construct the adjunction `j ⊣ k`. -/
private def weakHausdorffKificationCoreHomEquiv :
    CategoryTheory.Adjunction.CoreHomEquiv
      compactlyGeneratedWeakHausdorffToWeakHausdorff weakHausdorffKification where
  homEquiv := fun X Y ↦ (weakHausdorffKificationHomEquiv X Y).symm
  homEquiv_naturality_left_symm := fun f g ↦
    weakHausdorffKificationHomEquiv_naturality_left_symm f g
  homEquiv_naturality_right := fun f g ↦
    weakHausdorffKificationHomEquiv_naturality_right f g

/-- Proposition 5.2.9. The functor `k` is right adjoint to the inclusion
`j : U ⥤ wU`. -/
def weakHausdorffKificationAdjunction :
    compactlyGeneratedWeakHausdorffToWeakHausdorff ⊣ weakHausdorffKification :=
  CategoryTheory.Adjunction.mkOfHomEquiv weakHausdorffKificationCoreHomEquiv

/-- The adjunction Hom-equivalence agrees with the explicit comparison used to construct it. -/
@[simp] theorem weakHausdorffKificationAdjunction_homEquiv_apply
    (X : compactlyGeneratedWeakHausdorffSpaceCat) (Y : weakHausdorffSpaceCat.{w})
    (f : compactlyGeneratedWeakHausdorffToWeakHausdorff.obj X ⟶ Y) :
    weakHausdorffKificationAdjunction.homEquiv X Y f =
      (weakHausdorffKificationHomEquiv X Y).symm f := by
  -- The packaged adjunction reuses the explicit Hom-set equivalence stored in the core data.
  have h :
      weakHausdorffKificationAdjunction.homEquiv X Y =
        (weakHausdorffKificationHomEquiv X Y).symm := by
    simpa [weakHausdorffKificationAdjunction, weakHausdorffKificationCoreHomEquiv] using
      congrFun
        (congrFun
          (CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv weakHausdorffKificationCoreHomEquiv)
          X)
        Y
  exact congrArg (fun e ↦ e f) h
