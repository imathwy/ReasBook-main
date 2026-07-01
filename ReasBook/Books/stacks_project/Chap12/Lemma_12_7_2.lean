import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B)

/- Domain-style sampling for Lemma 12.7.2:
- primary domain: exactness criteria for functors between abelian categories, organized by mapped
  short exact sequences;
- inspected owner declarations:
  * `leftExactFunctor`, `rightExactFunctor`, `exactFunctor`;
  * `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`;
  * `Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi`;
  * `Functor.exact_tfae`;
- best owner abstraction: a short complex `S : ShortComplex A` and its image `S.map F`;
- primitive data: a short exact complex `S`;
- derived API: exactness, monomorphism, epimorphism, and short exactness of `S.map F`.

Source/core/bridge triage:
- `source-facing`: the textbook left-exact, right-exact, and exactness criteria phrased by sending
  short exact sequences to exact sequences;
- `core/canonical`: `leftExactFunctor`, `rightExactFunctor`, `exactFunctor`, and the mapped short
  complex `S.map F`;
- `bridge/view`: the internal converse arguments recovering finite limits or finite colimits from
  mapped short exactness without assuming additivity.

The local `ComposableArrows.mk₂ ...` exactness layer remains the public source-facing surface,
because `(S.map F).Exact` would force an ambient `F.PreservesZeroMorphisms` instance into the
statement. Internally, once zero-preservation is recovered from mapped short exactness, the proofs
switch to the canonical `ShortComplex` owner. -/

/-- Lemma 12.7.2 (1): a functor between abelian categories is additive as soon as it is left exact
or right exact, i.e. as soon as it preserves finite limits or finite colimits. -/
-- Proof sketch: if `F` is left exact, then it lies in the object property `leftExactFunctor A B`,
-- and `leftExactFunctor_le_additiveFunctor` upgrades this to additivity. The right exact case is
-- dual, using `rightExactFunctor_le_additiveFunctor`.
theorem functor_additive_of_leftExact_or_rightExact
    (hF : leftExactFunctor A B F ∨ rightExactFunctor A B F) : F.Additive := by
  rcases hF with hF | hF
  · exact (leftExactFunctor_le_additiveFunctor A B) F hF
  · exact (rightExactFunctor_le_additiveFunctor A B) F hF

private abbrev MapsShortExactToExact (F : A ⥤ B) : Prop :=
  ∀ S : ShortComplex A,
    S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact

private abbrev MapsShortExactToExactMono (F : A ⥤ B) : Prop :=
  ∀ S : ShortComplex A,
    S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧ Mono (F.map S.f)

private abbrev MapsShortExactToExactEpi (F : A ⥤ B) : Prop :=
  ∀ S : ShortComplex A,
    S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧ Epi (F.map S.g)

private theorem mapsShortExactToImageEqKernel
    (hF : MapsShortExactToExact F) :
    ∀ S : ShortComplex A,
      S.ShortExact → imageSubobject (F.map S.f) = kernelSubobject (F.map S.g) :=
  fun S hS ↦ by
    let T : ShortComplex B :=
      ShortComplex.mk (F.map S.f) (F.map S.g) ((hF S hS).toIsComplex.zero 0)
    have hT : T.Exact := by
      exact (T.exact_iff_exact_toComposableArrows).2 (hF S hS)
    simpa [T] using (ShortComplex.exact_iff_image_eq_kernel T).1 hT

private theorem comp_eq_zero_of_image_eq_kernel {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  have hfac : (kernelSubobject g).Factors (imageSubobject f).arrow :=
    Subobject.factors_of_le (imageSubobject f).arrow hfg.le <| Subobject.factors_self _
  have hArrow :
      (kernelSubobject g).factorThru (imageSubobject f).arrow hfac ≫ (kernelSubobject g).arrow =
        (imageSubobject f).arrow :=
    Subobject.factorThru_arrow _ _ _
  have hcomp : (imageSubobject f).arrow ≫ g = 0 := by
    rw [← hArrow, Category.assoc, kernelSubobject_arrow_comp]
    simp
  calc
    f ≫ g = factorThruImageSubobject f ≫ ((imageSubobject f).arrow ≫ g) := by
      rw [← Category.assoc, imageSubobject_arrow_comp]
    _ = 0 := by
      simp [hcomp]

private theorem preservesZeroMorphisms_of_mapsShortExact_to_exact
    (hF : MapsShortExactToExact F) :
    F.PreservesZeroMorphisms where
  map_zero X Y := by
    let S : ShortComplex A :=
      ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (by simp)
    have hS : S.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact
    have hcomp :
        F.map (biprod.inl : X ⟶ X ⊞ Y) ≫ F.map (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
      comp_eq_zero_of_image_eq_kernel ((mapsShortExactToImageEqKernel F hF) S hS)
    have hmap_zero : F.map ((biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd) = 0 := by
      rw [F.map_comp]
      exact hcomp
    have hzero : ((biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd : X ⟶ Y) = 0 := by
      simp
    simpa [hzero] using hmap_zero

private theorem preservesFiniteLimits_of_maps_shortExact_to_exact_mono
    [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f)) :
    PreservesFiniteLimits F := by
  letI : F.PreservesMonomorphisms :=
    ⟨fun {X Y} f ↦ hF _ { exact := ShortComplex.exact_cokernel f } |>.2⟩
  let hExactMono :
      ∀ (S : ShortComplex A), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f) := by
    intro S hS
    have : Mono S.f := hS.2
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map <| Abelian.factorThruCoimage S.g
        comm₂₃ := show 𝟙 _ ≫ F.map _ = F.map (cokernel.π _) ≫ _ by
          rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
    haveI : Epi φ.τ₁ := by
      dsimp [φ]
      infer_instance
    haveI : IsIso φ.τ₂ := by
      dsimp [φ]
      infer_instance
    haveI : Mono φ.τ₃ := by
      dsimp [φ]
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      (hF T ⟨(S.exact_iff_exact_coimage_π).1 hS.1⟩).1
  letI : ∀ {X Y : A} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F := fun {X Y} f ↦ by
    refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ?_
    apply (KernelFork.isLimitMapConeEquiv _ F).2
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    let hS := hExactMono S ⟨ShortComplex.exact_kernel f, inferInstance⟩
    have : Mono (S.map F).f := hS.2
    exact hS.1.fIsKernel
  exact F.preservesFiniteLimits_of_preservesKernels

private theorem preservesFiniteColimits_of_maps_shortExact_to_exact_epi
    [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g)) :
    PreservesFiniteColimits F := by
  letI : F.PreservesEpimorphisms :=
    ⟨fun {X Y} f ↦ hF _ { exact := ShortComplex.exact_kernel f } |>.2⟩
  let hExactEpi :
      ∀ (S : ShortComplex A), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g) := by
    intro S hS
    have : Epi S.g := hS.2
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abelian.factorThruImage S.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := show _ ≫ F.map (kernel.ι _) = F.map _ ≫ 𝟙 _ by
          rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
    haveI : Epi φ.τ₁ := by
      dsimp [φ]
      infer_instance
    haveI : IsIso φ.τ₂ := by
      dsimp [φ]
      infer_instance
    haveI : Mono φ.τ₃ := by
      dsimp [φ]
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
      (hF T ⟨(S.exact_iff_exact_image_ι).1 hS.1⟩).1
  letI : ∀ {X Y : A} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F := fun {X Y} f ↦ by
    refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ F).2
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    let hS := hExactEpi S ⟨ShortComplex.exact_cokernel f, inferInstance⟩
    have : Epi (S.map F).g := hS.2
    exact hS.1.gIsCokernel
  exact F.preservesFiniteColimits_of_preservesCokernels

private theorem preservesFiniteLimits_of_maps_shortExact_to_exact_mono'
    (hF : MapsShortExactToExactMono F) :
    PreservesFiniteLimits F := by
  letI := preservesZeroMorphisms_of_mapsShortExact_to_exact F fun S hS ↦ (hF S hS).1
  exact preservesFiniteLimits_of_maps_shortExact_to_exact_mono F fun S hS ↦
    let T : ShortComplex B :=
      ShortComplex.mk (F.map S.f) (F.map S.g) ((hF S hS).1.toIsComplex.zero 0)
    ⟨(T.exact_iff_exact_toComposableArrows).2 (hF S hS).1, (hF S hS).2⟩

private theorem preservesFiniteColimits_of_maps_shortExact_to_exact_epi'
    (hF : MapsShortExactToExactEpi F) :
    PreservesFiniteColimits F := by
  letI := preservesZeroMorphisms_of_mapsShortExact_to_exact F fun S hS ↦ (hF S hS).1
  exact preservesFiniteColimits_of_maps_shortExact_to_exact_epi F fun S hS ↦
    let T : ShortComplex B :=
      ShortComplex.mk (F.map S.f) (F.map S.g) ((hF S hS).1.toIsComplex.zero 0)
    ⟨(T.exact_iff_exact_toComposableArrows).2 (hF S hS).1, (hF S hS).2⟩

/-- Lemma 12.7.2 (2): a functor between abelian categories is left exact exactly when it sends
every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` to an exact mapped short complex whose first map is
mono. -/
-- Proof sketch: the forward implication is exactly the owner criterion
-- `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` after additivity is supplied by
-- part (1). For the converse, mapped exact short complexes first give preservation of zero
-- morphisms, and then the internal kernel-preservation bridge yields finite-limit preservation.
theorem functor_leftExact_iff_maps_shortExact_to_exact_mono :
    leftExactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Mono (F.map S.f) := by
  constructor
  · intro hF
    haveI : F.Additive := functor_additive_of_leftExact_or_rightExact F (.inl hF)
    let hMap := (F.preservesFiniteLimits_iff_forall_exact_map_and_mono).1 <| by
      simpa [leftExactFunctor_iff] using hF
    intro S hS
    exact ⟨(hMap S hS).1.exact_toComposableArrows, (hMap S hS).2⟩
  · intro hF
    simpa [leftExactFunctor_iff] using
      preservesFiniteLimits_of_maps_shortExact_to_exact_mono' F hF

/-- Lemma 12.7.2 (3): a functor between abelian categories is right exact exactly when it sends
every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` to an exact mapped short complex whose second map is
epi. -/
-- Proof sketch: the forward implication is the owner criterion
-- `Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi` after additivity is supplied by
-- part (1). For the converse, mapped exactness again gives preservation of zero morphisms, and the
-- internal cokernel-preservation bridge upgrades this to finite-colimit preservation.
theorem functor_rightExact_iff_maps_shortExact_to_exact_epi :
    rightExactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Epi (F.map S.g) := by
  constructor
  · intro hF
    haveI : F.Additive := functor_additive_of_leftExact_or_rightExact F (.inr hF)
    let hMap := (F.preservesFiniteColimits_iff_forall_exact_map_and_epi).1 <| by
      simpa [rightExactFunctor_iff] using hF
    intro S hS
    exact ⟨(hMap S hS).1.exact_toComposableArrows, (hMap S hS).2⟩
  · intro hF
    simpa [rightExactFunctor_iff] using
      preservesFiniteColimits_of_maps_shortExact_to_exact_epi' F hF

/-- Lemma 12.7.2 (4): a functor between abelian categories is exact exactly when it sends every
short exact sequence to a short exact mapped short complex. -/
-- Proof sketch: once exactness gives additivity, this is exactly the owner criterion
-- `Functor.exact_tfae`. Conversely, mapped short exactness yields the left- and right-exact
-- criteria of parts (2) and (3) by forgetting the `mono` and `epi` fields from `ShortExact`.
theorem functor_exact_iff_maps_shortExact_to_exact_mono_epi :
    exactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Mono (F.map S.f) ∧ Epi (F.map S.g) := by
  constructor
  · intro hF
    haveI : F.Additive := (exactFunctor_le_additiveFunctor A B) F hF
    let hMap := (Functor.exact_tfae F).out 3 0 |>.1 <| by
      simpa [exactFunctor_iff] using hF
    intro S hS
    exact ⟨(hMap S hS).exact.exact_toComposableArrows, (hMap S hS).mono_f, (hMap S hS).epi_g⟩
  · intro hF
    refine ⟨?_, ?_⟩
    · exact (functor_leftExact_iff_maps_shortExact_to_exact_mono F).2 fun S hS ↦
        ⟨(hF S hS).1, (hF S hS).2.1⟩
    · exact (functor_rightExact_iff_maps_shortExact_to_exact_epi F).2 fun S hS ↦
        ⟨(hF S hS).1, (hF S hS).2.2⟩

end CategoryTheory
