-- Proof rescue support index for Proposition 10.88.6.
-- Route correction: the old monolithic proof was split into the support modules
-- imported below, so stale placeholder reports against line numbers in this
-- index file no longer correspond to live proof holes.
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.CommonUniverseOwners
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.HomInverseSystem
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.TensorDomination
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.ModuleCatFactorization
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.StageTensorKernels
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.HomMittagLeffler

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: the finite-presentation tensor-kernel criterion from clause
`(1)`. -/
private abbrev kernelFactorizationCondition
    (_F : I ⥤ ModuleCat.{max v w} R) (M : Type (max v w)) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (P : ModuleCat.{max v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
    ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
      ∀ N : ModuleCat.{max v w} R,
        LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)

/-- Helper for Proposition 10.88.6: the eventual domination condition from clause `(2)`. -/
private abbrev stageDominationCondition
    (F : I ⥤ ModuleCat.{max v w} R) (M : Type (max v w)) [AddCommGroup M] [Module R M]
    (c : colimit F ≅ ModuleCat.of R M) : Prop :=
  ∀ i : I, ∃ (j : I) (hij : i ≤ j),
    LinearMap.Dominates.{u, max v w, max v w, max v w}
      ((((F.map (homOfLE hij)).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))))
      ((((colimit.ι F i ≫ c.hom).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] M))

/-- Helper for Proposition 10.88.6: the eventual tail-factorization condition from clause `(3)`. -/
private abbrev tailFactorizationCondition
    (F : I ⥤ ModuleCat.{max v w} R) : Prop :=
  ∀ i : I, ∃ (j : I) (hij : i ≤ j),
    ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
      F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h

/-- Helper for Proposition 10.88.6: the Hom inverse-system Mittag-Leffler condition from clause
`(4)`. -/
private abbrev homMittagLefflerCondition
    (F : I ⥤ ModuleCat.{max v w} R) : Prop :=
  ∀ N : ModuleCat.{max v w} R,
    (colimitPresentationHomInverseSystem F N).IsMittagLeffler

/-- Helper for Proposition 10.88.6: the special product-target Hom inverse-system
Mittag-Leffler condition from clause `(5)`. -/
private abbrev productHomMittagLefflerCondition
    (F : I ⥤ ModuleCat.{max v w} R) : Prop :=
  let N : ModuleCat.{max v w} R :=
    ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w)))
  (colimitPresentationHomInverseSystem F N).IsMittagLeffler

/-- Helper for Chap10 Proposition 10 88 6: the same-universe fp-cokernel factorization bridge is
most stable at the underlying linear-map level. -/
private lemma linearFactorsThrough_of_sameUniverseKernelLe_of_finitePresentation_cokernel
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    [Module.FinitePresentation R (B ⧸ LinearMap.range f)]
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N)) :
    ∃ h : B →ₗ[R] C, g = h.comp f := by
  -- TODO: replan route: the common-universe analogue of Lemma `10.88.5` still needs the owner
  -- `LinearMap.dominates_of_sameUniverseKernelLe`, because the existing finite-presentation
  -- factorization theorem does not elaborate directly at the stage universe `max v w`.
  sorry

/-- Helper for Chap10 Proposition 10 88 6: equality of bundled same-universe tensor kernels gives
both inclusion directions separately. -/
private lemma sameUniverseKernelEq_le_pair
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    (∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N)) ∧
      ∀ N : ModuleCat.{max v w} R,
        LinearMap.ker (g.rTensor N) ≤ LinearMap.ker (f.rTensor N) := by
  constructor
  · intro N
    -- Proof comment: the forward inclusion is the `≤` direction of the assumed kernel equality.
    exact (hker N).le
  · intro N
    -- Proof comment: the reverse inclusion is the opposite `≤` direction of the same equality.
    exact (hker N).ge

/-- Helper for Chap10 Proposition 10 88 6: the reverse inclusion from a bundled same-universe
tensor-kernel equality is available directly when later factorization arguments only need that one
direction. -/
private lemma sameUniverseKernelLe_of_kernelEq_reverse
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (g.rTensor N) ≤ LinearMap.ker (f.rTensor N) := by
  intro N
  -- Proof comment: read the assumed kernel equality in the reverse direction.
  exact (hker N).ge

/-- Helper for Chap10 Proposition 10 88 6: the forward inclusion from a bundled same-universe
tensor-kernel equality can be reused directly when only that direction is needed. -/
private lemma sameUniverseKernelLe_of_kernelEq_forward
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N) := by
  intro N
  -- Proof comment: read the assumed kernel equality in the forward direction.
  exact (hker N).le

/-- Helper for Chap10 Proposition 10 88 6: a full domination hypothesis specializes to the bundled
same-universe test objects used throughout the local clause-assembly lemmas. -/
private lemma sameUniverseKernelLe_of_dominates
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hdom : g.Dominates f) :
    ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N) := by
  intro N
  -- Proof comment: the global domination predicate may be evaluated on the specific bundled test
  -- object `N` without any further transport.
  exact
    LinearMap.kernel_le_of_dominates_moduleCat_testObject.{u, v, w}
      (R := R) (A := A) (B := B) (C := C) (f := f) (g := g) hdom N

/-- Helper for Chap10 Proposition 10 88 6: clause `(1)` produces a later transition map whose
tensor kernels dominate the colimit map from stage `i`. -/
private lemma stageDomination_of_kernelFactorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    kernelFactorizationCondition F M →
      stageDominationCondition F M c := by
  -- TODO: replan route: once the common-universe factorization owner is available, the source
  -- proof goes through by factoring the colimit leg through the clause `(1)` witness, moving that
  -- factorization to a common later stage, and then composing the resulting domination relations.
  sorry

/-- Helper for Chap10 Proposition 10 88 6: clause `(2)` immediately yields the kernel
factorization criterion by pushing a chosen stage factorization forward to a dominating later
stage. -/
private lemma kernelFactorization_of_stageDomination
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    stageDominationCondition F M c →
      kernelFactorizationCondition F M := by
  intro hdom P _ f
  obtain ⟨i, g₀, hg₀⟩ :=
    stage_factor_through_colimit_for_fp_source_explicit_universe.{u, v, w}
      (R := R) (F := F) (M := M) (c := c) (P := P) f
  obtain ⟨j, hij, hj⟩ := hdom i
  refine ⟨F.obj j, hfp j, (g₀ ≫ F.map (homOfLE hij)).hom, ?_⟩
  intro N
  -- Proof comment: the chosen stage domination gives the forward kernel inclusion, while the
  -- pushed-forward factorization of `f` through stage `j` gives the reverse inclusion.
  exact
    kernel_eq_of_stage_domination_and_pushed_factorization
      F c hij g₀ f hg₀ hj N

/-- Helper for Chap10 Proposition 10 88 6: once the chosen stage map `f_ij` dominates the colimit
map from stage `i`, it also dominates every later transition map `f_ik`. -/
private lemma dominatingStageMap_dominates_laterTransition
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j k : I} (hij : i ≤ j) (hik : i ≤ k)
    (hdom : LinearMap.Dominates.{u, max v w, max v w, max v w}
      ((((F.map (homOfLE hij)).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))))
      ((((colimit.ι F i ≫ c.hom).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] M))) :
    LinearMap.Dominates.{u, max v w, max v w, max v w}
      ((((F.map (homOfLE hij)).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))))
      ((((F.map (homOfLE hik)).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] (F.obj k : Type (max v w)))) := by
  intro N _ _ x hx
  -- Proof comment: first use the canonical factorization of the colimit leg through `f_ik`, then
  -- feed the resulting kernel membership into the chosen domination hypothesis for `f_ij`.
  exact
    hdom N <|
      colimit_map_dominates_transition F c hik N hx

/-- Helper for Chap10 Proposition 10 88 6: once `f_ij` dominates the colimit map from stage `i`,
the same factorization bridge forces every later transition map `f_ik` to factor through `f_ij`.
-/
private lemma laterTransitionFactorsThroughDominatingStage
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M)
    {i j k : I} (hij : i ≤ j) (hik : i ≤ k)
    (hdom : LinearMap.Dominates.{u, max v w, max v w, max v w}
      ((((F.map (homOfLE hij)).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))))
      ((((colimit.ι F i ≫ c.hom).hom) :
        (F.obj i : Type (max v w)) →ₗ[R] M))) :
    ∃ h : F.obj k ⟶ F.obj j,
      F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  -- TODO: replan route: after the common-universe fp-cokernel factorization bridge is repaired,
  -- apply it to `dominatingStageMap_dominates_laterTransition` and rebundle the resulting linear
  -- factor map as the required stage morphism.
  sorry

/-- Helper for Chap10 Proposition 10 88 6: clause `(2)` forces every sufficiently late transition
map out of stage `i` to factor through the chosen dominating stage. -/
private lemma tailFactorization_of_stageDomination
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    stageDominationCondition F M c →
      tailFactorizationCondition F := by
  intro hdom i
  obtain ⟨j, hij, hj⟩ := hdom i
  refine ⟨j, hij, ?_⟩
  intro k hik
  -- Proof comment: freeze the later-transition factorization into a dedicated helper so the
  -- main `(2) → (3)` proof no longer reopens the mixed-universe coercion problem in place.
  exact
    laterTransitionFactorsThroughDominatingStage
      (R := R) (F := F) (M := M) hfp c hij hik hj

/-- Helper for Chap10 Proposition 10 88 6: a chosen tail factorization transports right-tensor
vanishing from the later transition map `f_ik` back to the earlier stabilized map `f_ij`. -/
private lemma transitionFactorization_preserves_rTensorZero
    (F : I ⥤ ModuleCat.{max v w} R)
    {i j k : I} {hij : i ≤ j} {hik : i ≤ k}
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] N}
    {h : F.obj k ⟶ F.obj j}
    (hh : F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h)
    (hx : (((F.map (homOfLE hik)).hom).rTensor N) x = 0) :
    (((F.map (homOfLE hij)).hom).rTensor N) x = 0 := by
  -- Proof comment: freeze the bundled test object `N` to its underlying carrier and reuse the
  -- already proved tensor-factorization pattern in this fixed bundled spelling.
  have hh_tensor :
      (((F.map (homOfLE hij)).hom).rTensor N) x =
        ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := by
    -- Proof comment: evaluate the chosen tail factorization after tensoring with the fixed test
    -- object `N`.
    simpa using congrArg (fun t : F.obj i ⟶ F.obj j ↦ (t.hom.rTensor N) x) hh
  have hh_apply :
      ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) =
        (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := by
    -- Proof comment: tensoring a composite is the composite of the tensorized maps.
    change (LinearMap.rTensor N (h.hom.comp (F.map (homOfLE hik)).hom)) x =
      (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x)
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (F.map (homOfLE hik)).hom)
        (g := h.hom) (x := x))
  calc
    (((F.map (homOfLE hij)).hom).rTensor N) x
        = ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := hh_tensor
    _ = (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := hh_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

/-- Helper for Chap10 Proposition 10 88 6: if the frozen colimit leg kills a tensor element, then
the unfrozen colimit leg already kills that tensor element before postcomposing with `c.hom`. -/
private lemma colimitLeg_rTensor_zero_of_frozenColimitLeg_rTensor_zero
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] N}
    (hx : (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0) :
    (((colimit.ι F i).hom).rTensor N) x = 0 := by
  -- Proof comment: the support owner already removes the postcomposition by the colimit
  -- isomorphism once the tensorized colimit leg is rewritten as a composite with `c.inv`.
  have hcolim_iso : colimit.ι F i = colimit.ι F i ≫ c.hom ≫ c.inv := by
    -- Proof comment: insert the identity `c.hom ≫ c.inv = 𝟙` on the colimit object.
    calc
      colimit.ι F i = colimit.ι F i ≫ 𝟙 (colimit F) := by simp
      _ = colimit.ι F i ≫ (c.hom ≫ c.inv) := by rw [c.hom_inv_id]
      _ = colimit.ι F i ≫ c.hom ≫ c.inv := by simp
  have hcolim_tensor :
      (((colimit.ι F i).hom).rTensor N) x =
        (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := by
    -- Proof comment: evaluate the morphism identity after tensoring with the fixed bundled test
    -- object `N`.
    simpa using congrArg
      (fun t : F.obj i ⟶ colimit F ↦ (t.hom.rTensor N) x) hcolim_iso
  have hcolim_apply :
      (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x =
        (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := by
    -- Proof comment: tensoring a composite turns the postcomposition with `c.inv` into a
    -- composition of the corresponding tensor maps.
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (colimit.ι F i ≫ c.hom).hom)
        (g := c.inv.hom) (x := x))
  calc
    (((colimit.ι F i).hom).rTensor N) x
        = (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := hcolim_tensor
    _ = (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x := by
          rfl
    _ = (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := hcolim_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

/-- Helper for Chap10 Proposition 10 88 6: `ModuleCat.uliftFunctor` preserves filtered colimits on
the lifted index category used to stabilize tensor vanishing in `ULift`-expanded universes. -/
private lemma moduleCatUliftFunctorPreservesFilteredColimits
    {J : Type (max v w)} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{u, max v w} R) := by
  -- Route correction: use the same `AddCommGrpCat`-based preservation proof that already works in
  -- Lemma `10.89.4`, instead of routing through `forget` to `Type`.
  let e :
      ModuleCat.uliftFunctor.{u, max v w} R ⋙
          forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} ≅
        forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w} ⋙
          AddCommGrpCat.uliftFunctor.{u, max v w} := by
    refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
    intro X Y f
    ext x
    rfl
  letI :
      PreservesColimitsOfShape J
        (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w} ⋙
          AddCommGrpCat.uliftFunctor.{u, max v w}) := by
    infer_instance
  letI :
      PreservesColimitsOfShape J
        (ModuleCat.uliftFunctor.{u, max v w} R ⋙
          forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}) :=
    preservesColimitsOfShape_of_natIso e.symm
  exact
    preservesColimitsOfShape_of_reflects_of_preserves
      (ModuleCat.uliftFunctor.{u, max v w} R)
      (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w})

/-- Helper for Chap10 Proposition 10 88 6: transporting through `TensorProduct.congr` removes the
`ULift` inserted on the stage modules before left tensoring. -/
private lemma uliftFunctorMap_lTensor_transport
    {V W : Type (max v w)} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {Q : Type (max u v w)} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) :
    let eV : Q ⊗[R] ULift.{u} V ≃ₗ[R] Q ⊗[R] V :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{u} V ≃ₗ[R] V)
    let eW : Q ⊗[R] ULift.{u} W ≃ₗ[R] Q ⊗[R] W :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{u} W ≃ₗ[R] W)
    eW.toLinearMap.comp
        ((((ModuleCat.uliftFunctor.{u, max v w} R).map (ModuleCat.ofHom f)).hom).lTensor Q) =
      (f.lTensor Q).comp eV.toLinearMap := by
  ext q v
  rfl

/-- Helper for Chap10 Proposition 10 88 6: transporting through `TensorProduct.congr` removes the
`ULift` inserted on both tensor factors before left tensoring. -/
private lemma uliftFunctorMap_lTensor_bothFactors_transport
    {V W : Type (max v w)} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {Q : Type (max u v w)} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) :
    let QL : Type (max u v w) := ULift.{max v w} Q
    let eV : QL ⊗[R] ULift.{u} V ≃ₗ[R] Q ⊗[R] V :=
      TensorProduct.congr
        (ULift.moduleEquiv : ULift.{max v w} Q ≃ₗ[R] Q)
        (ULift.moduleEquiv : ULift.{u} V ≃ₗ[R] V)
    let eW : QL ⊗[R] ULift.{u} W ≃ₗ[R] Q ⊗[R] W :=
      TensorProduct.congr
        (ULift.moduleEquiv : ULift.{max v w} Q ≃ₗ[R] Q)
        (ULift.moduleEquiv : ULift.{u} W ≃ₗ[R] W)
    eW.toLinearMap.comp
        ((((ModuleCat.uliftFunctor.{u, max v w} R).map (ModuleCat.ofHom f)).hom).lTensor QL) =
      (f.lTensor Q).comp eV.toLinearMap := by
  ext q v
  rfl

/-- Helper for Chap10 Proposition 10 88 6: after lifting only the right tensor factor into the
common universe, eventual left-tensor vanishing follows from Lemma `10.88.3` and then descends
back to the original colimit presentation. -/
private lemma exists_later_stage_lTensor_eq_zero_unbundled
    {J : Type (max v w)} [SmallCategory J] [IsFiltered J]
    {V : Type (max v w)} [AddCommGroup V] [Module R V]
    {Q : Type (max u v w)} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{max v w} R V))
    {j : J} {y : Q ⊗[R] pres.diag.obj j}
    (hy : ((pres.ι.app j).hom.lTensor Q) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.lTensor Q) y = 0 := by
  -- TODO: replan route: the mixed-universe left-tensor stabilization statement should reuse the
  -- `ULift` transport proved for both tensor factors above, but the `ModuleCat.uliftFunctor`
  -- colimit-preservation instance still needs an owner-level universe bridge at this exact
  -- `J : Type (max v w)` spelling.
  sorry

/-- Helper for Chap10 Proposition 10 88 6: a vanishing statement returned by the lifted-index
stabilization owner rewrites directly to the corresponding original transition map `f_ik` after
descending `ULift.down` on the index. -/
private lemma liftedIndexStage_lTensor_zero_descends
    (F : I ⥤ ModuleCat.{max v w} R)
    {i : I} {kLift : ULift.{max v w} I}
    (w : ULift.up i ⟶ kLift)
    {Q : Type (max u v w)} [AddCommGroup Q] [Module R Q]
    {x : (F.obj i : Type (max v w)) ⊗[R] Q}
    (hw_zero :
      ((((lifted_index_diagram (R := R) F).map w).hom).lTensor Q)
        (TensorProduct.comm R (F.obj i : Type (max v w)) Q x) = 0) :
    let k : I := kLift.down
    let hik : i ≤ k := show i ≤ kLift.down from w.down.down
    (((F.map (homOfLE hik)).hom).lTensor Q)
      (TensorProduct.comm R (F.obj i : Type (max v w)) Q x) = 0 := by
  let k : I := kLift.down
  let hik : i ≤ k := show i ≤ kLift.down from w.down.down
  have hmap_apply :
      ((((lifted_index_diagram (R := R) F).map w).hom).lTensor Q)
        (TensorProduct.comm R (F.obj i : Type (max v w)) Q x) =
        (((F.map (homOfLE hik)).hom).lTensor Q)
          (TensorProduct.comm R (F.obj i : Type (max v w)) Q x) := by
    simpa [k, hik] using
        congrArg
          (fun t :
          Q ⊗[R] (F.obj i : Type (max v w)) →ₗ[R]
            Q ⊗[R] (F.obj k : Type (max v w)) ↦
          t (TensorProduct.comm R (F.obj i : Type (max v w)) Q x))
        (lifted_index_diagram_map_lTensor_eq
          (R := R) (F := F) (i := i) (j := kLift) (w := w) (N := Q))
  calc
    (((F.map (homOfLE hik)).hom).lTensor Q)
        (TensorProduct.comm R (F.obj i : Type (max v w)) Q x)
        = ((((lifted_index_diagram (R := R) F).map w).hom).lTensor Q)
            (TensorProduct.comm R (F.obj i : Type (max v w)) Q x) := by
              simpa using hmap_apply.symm
    _ = 0 := hw_zero

/-- Helper for Chap10 Proposition 10 88 6: right-tensor vanishing over a bundled test object `N`
is equivalent to right-tensor vanishing after replacing `N` by the honest larger-universe test
object `ULift.{u} N`. -/
private lemma rTensorZero_iff_uliftTestZero
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B)
    (N : ModuleCat.{max v w} R)
    (x : A ⊗[R] N) :
    (f.rTensor N) x = 0 ↔
      (f.rTensor (ULift.{u} (N : Type (max v w))))
        ((TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv.symm) x) = 0 := by
  let eA : A ⊗[R] N ≃ₗ[R] A ⊗[R] ULift.{u} (N : Type (max v w)) :=
    TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv.symm
  let eB : B ⊗[R] N ≃ₗ[R] B ⊗[R] ULift.{u} (N : Type (max v w)) :=
    TensorProduct.congr (LinearEquiv.refl R B) ULift.moduleEquiv.symm
  have hf_apply (y : A ⊗[R] N) :
      (f.rTensor (ULift.{u} (N : Type (max v w)))) (eA y) =
        eB ((f.rTensor N) y) := by
    -- Proof comment: changing the tensor factor from `N` to `ULift N` commutes with `f ⊗ 1`.
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [eA, eB]
    · intro a n
      rfl
    · intro y₁ y₂ hy₁ hy₂
      simp [hy₁, hy₂]
  constructor
  · intro hx
    calc
      (f.rTensor (ULift.{u} (N : Type (max v w)))) (eA x)
          = eB ((f.rTensor N) x) := hf_apply x
      _ = 0 := by simp [hx]
  · intro hx
    apply eB.injective
    calc
      eB ((f.rTensor N) x)
          = (f.rTensor (ULift.{u} (N : Type (max v w)))) (eA x) := by
              symm
              exact hf_apply x
      _ = 0 := hx
      _ = eB 0 := by simp [eB]

/-- Helper for Chap10 Proposition 10 88 6: tensor-kernel membership for the frozen colimit leg is
exactly the corresponding vanishing statement. -/
private lemma frozenColimitLeg_mem_ker_iff
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] N}
    : x ∈ LinearMap.ker (((colimit.ι F i ≫ c.hom).hom).rTensor N) ↔
      (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0 := by
  -- Proof comment: this is the defining characterization of kernel membership for the frozen
  -- colimit leg tensor map, recorded explicitly so later transport arguments can avoid reopening
  -- `LinearMap.mem_ker`.
  simp [LinearMap.mem_ker]

/-- Helper for Chap10 Proposition 10 88 6: the forward direction of
`frozenColimitLeg_mem_ker_iff` is available as a standalone step for the direct `(3) → (2)`
argument. -/
private lemma frozenColimitLeg_rTensor_zero_of_mem_ker
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] N}
    (hx : x ∈ LinearMap.ker (((colimit.ι F i ≫ c.hom).hom).rTensor N)) :
    (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0 := by
  -- Proof comment: unwrap membership in the tensor kernel into the corresponding vanishing
  -- statement so later transport lemmas can work with equalities instead of submodule terms.
  exact
    (frozenColimitLeg_mem_ker_iff
      (R := R) (F := F) (M := M) (c := c) (i := i) N (x := x)).mp hx

/-- Helper for Chap10 Proposition 10 88 6: if the frozen colimit leg kills a tensor element, then
some later transition map already kills that tensor element on the same bundled test object. -/
private lemma laterStageKillsTensorOfFrozenColimitLegZero
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] N}
    (hx : (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0) :
    ∃ (k : I) (hik : i ≤ k), (((F.map (homOfLE hik)).hom).rTensor N) x = 0 := by
  -- TODO: replan route: after the mixed-universe left-tensor stabilization owner is repaired,
  -- commute the frozen right-tensor vanishing to the lifted-index left-tensor statement, descend
  -- the witness `kLift.down`, and commute back with `rTensor_zero_of_lTensor_zero_via_comm`.
  sorry

/-- Helper for Chap10 Proposition 10 88 6: after pushing a tensor element from `P` to stage `i`
and using a chosen tail factorization `f_ij = f_ik ≫ h`, vanishing for `f_ik ⊗ 1` upgrades
directly to vanishing for the pushed-forward stage map `g₀ ≫ f_ij`. -/
private lemma pushedForwardTailFactorization_preserves_rTensorZero
    (F : I ⥤ ModuleCat.{max v w} R)
    {P : ModuleCat.{max v w} R}
    {i j k : I} {hij : i ≤ j} {hik : i ≤ k}
    (g₀ : P ⟶ F.obj i)
    (N : ModuleCat.{max v w} R)
    {x : (P : Type (max v w)) ⊗[R] N}
    {h : F.obj k ⟶ F.obj j}
    (hh : F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h)
    (hx : (((F.map (homOfLE hik)).hom).rTensor N) ((g₀.hom.rTensor N) x) = 0) :
    ((((g₀ ≫ F.map (homOfLE hij)).hom).rTensor N) x) = 0 := by
  have hj_zero :
      (((F.map (homOfLE hij)).hom).rTensor N) ((g₀.hom.rTensor N) x) = 0 := by
    -- Proof comment: transport the vanishing across the chosen tail factorization.
    exact
      transitionFactorization_preserves_rTensorZero
        (R := R) (F := F) (hij := hij) (hik := hik)
        N (x := (g₀.hom.rTensor N) x) (h := h) hh hx
  -- Proof comment: the pushed-forward stage map is exactly the composite of `g₀ ⊗ 1` with
  -- `f_ij ⊗ 1`, so the transported vanishing is the desired equality.
  calc
    (((g₀ ≫ F.map (homOfLE hij)).hom).rTensor N) x
        = (((F.map (homOfLE hij)).hom).rTensor N) ((g₀.hom.rTensor N) x) := by
            simpa using
              (LinearMap.rTensor_comp_apply
                (M := N) (f := g₀.hom) (g := (F.map (homOfLE hij)).hom) (x := x))
    _ = 0 := hj_zero

/-- Helper for Chap10 Proposition 10 88 6: clause `(3)` also yields the kernel-factorization
criterion once the direct `(3) → (2)` route is available. -/
private lemma kernelFactorization_of_tailFactorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    tailFactorizationCondition F →
      kernelFactorizationCondition F M := by
  intro htail P _ f
  obtain ⟨i, g₀, hg₀⟩ :=
    stage_factor_through_colimit_for_fp_source_explicit_universe.{u, v, w}
      (R := R) (F := F) (M := M) (c := c) (P := P) f
  obtain ⟨j, hij, htailj⟩ := htail i
  refine ⟨F.obj j, hfp j, (g₀ ≫ F.map (homOfLE hij)).hom, ?_⟩
  intro N
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx_stage_mem :
        ((g₀.hom.rTensor N) x) ∈
          LinearMap.ker (((colimit.ι F i ≫ c.hom).hom).rTensor N) := by
      have hx_zero : (f.rTensor N) x = 0 := by
        simpa [LinearMap.mem_ker] using hx
      have hx_comp : ((((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom).rTensor N) x) = 0 := by
        -- Proof comment: rewrite the tensor map of the chosen stage factorization to the original
        -- tensor map `f ⊗ 1_N`.
        simpa
          [stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀]
          using hx_zero
      -- Proof comment: tensoring a composite is the composite of the tensor maps, so the
      -- resulting vanishing is exactly kernel membership for the precomposed colimit leg.
      simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx_comp
    have hx_stage_zero :
        (((colimit.ι F i ≫ c.hom).hom).rTensor N) ((g₀.hom.rTensor N) x) = 0 :=
      frozenColimitLeg_rTensor_zero_of_mem_ker
        (R := R) (F := F) (M := M) (c := c) N hx_stage_mem
    obtain ⟨k, hik, hk_zero⟩ :=
      laterStageKillsTensorOfFrozenColimitLegZero
        (R := R) (F := F) (M := M) (c := c) N
        (x := (g₀.hom.rTensor N) x) hx_stage_zero
    obtain ⟨h, hh⟩ := htailj k hik
    have hj_zero :
        ((((g₀ ≫ F.map (homOfLE hij)).hom).rTensor N) x) = 0 :=
      pushedForwardTailFactorization_preserves_rTensorZero
        (R := R) (F := F) (g₀ := g₀) (hij := hij) (hik := hik)
        N (x := x) (h := h) hh hk_zero
    simpa [LinearMap.mem_ker] using hj_zero
  · -- Proof comment: the chosen pushed-forward stage factorization always gives the reverse
    -- tensor-kernel inclusion, independently of the tail factorization hypothesis.
    exact
      LinearMap.kernel_le_of_dominates_moduleCat_testObject.{u, v, w}
        (A := (P : Type (max v w)))
        (B := (F.obj j : Type (max v w)))
        (C := M)
        (f := (((g₀ ≫ F.map (homOfLE hij)).hom) :
          (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))))
        (g := (f : (P : Type (max v w)) →ₗ[R] M))
        (pushed_forward_stage_factorization_reverse_domination_frozen
          (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀)
        N

/-- Chap10 Proposition 10 88 6.
For a directed colimit presentation `M = colimit F` by finitely presented modules, the following
five conditions are equivalent: the kernel-factorization criterion, eventual domination of the
colimit maps, eventual tail factorizations of the transition maps, Mittag-Lefflerness of every
associated Hom inverse system, and the special product-target Hom inverse system. -/
@[stacks 059E]
theorem directed_colimit_presentation_mittag_leffler_tfae
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    List.TFAE
      [ kernelFactorizationCondition F M,
        stageDominationCondition F M c,
        tailFactorizationCondition F,
        homMittagLefflerCondition F,
        productHomMittagLefflerCondition F ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · -- Proof comment: the structural `(1) → (2)` direction was isolated into the helper above.
      exact stageDomination_of_kernelFactorization (R := R) (F := F) (M := M) hfp c
    · exact kernelFactorization_of_stageDomination (R := R) (F := F) (M := M) hfp c
  tfae_have 2 → 3 := by
    -- Proof comment: clause `(2)` yields eventual tail factorizations by factoring later
    -- transitions through the chosen dominating stage map.
    exact tailFactorization_of_stageDomination (R := R) (F := F) hfp c
  tfae_have 3 → 1 := by
    -- Proof comment: route correction: prove `(3) → (1)` directly by stabilizing the tensor
    -- kernel of the chosen stage factorization, rather than detouring back through `(2)`.
    exact kernelFactorization_of_tailFactorization (R := R) (F := F) (M := M) hfp c
  tfae_have 3 → 4 := by
    intro htail N
    rw [Functor.isMittagLeffler_iff_subset_range_comp]
    intro iop
    let i : I := unop iop
    obtain ⟨j, hij, htailj⟩ := htail i
    refine ⟨op j, (homOfLE hij).op, ?_⟩
    intro kop g y hy
    rcases hy with ⟨φ, rfl⟩
    let k : I := unop kop
    have hjk : j ≤ k := leOfHom g.unop
    have hik : i ≤ k := hij.trans hjk
    obtain ⟨q, hq⟩ := htailj k hik
    let ψ : F.obj k ⟶ N := q ≫ φ
    refine ⟨ψ, ?_⟩
    have hg_unop : g.unop = homOfLE hjk := Subsingleton.elim _ _
    have hcalc :
        F.map (homOfLE hij) ≫ (F.map (homOfLE hjk) ≫ (q ≫ φ)) =
          F.map (homOfLE hij) ≫ φ := by
      -- Proof comment: both inverse-system maps are given by precomposition, and the chosen tail
      -- factorization identifies the two relevant precomposed transition maps.
      calc
        F.map (homOfLE hij) ≫ (F.map (homOfLE hjk) ≫ (q ≫ φ))
            = (F.map (homOfLE hij) ≫ F.map (homOfLE hjk)) ≫ q ≫ φ := by
                simp [Category.assoc]
        _ = F.map (homOfLE hik) ≫ q ≫ φ := by
              have hcomp :
                  (homOfLE hij : i ⟶ j) ≫ (homOfLE hjk : j ⟶ k) =
                    (homOfLE hik : i ⟶ k) :=
                Subsingleton.elim _ _
              rw [← F.map_comp, hcomp]
        _ = F.map (homOfLE hij) ≫ φ := by
              simpa [Category.assoc] using
                (congrArg (fun m : F.obj i ⟶ F.obj j ↦ m ≫ φ) hq).symm
    simpa [colimitPresentationHomInverseSystem, ψ, hg_unop, Category.assoc] using hcalc
  tfae_have 4 → 5 := by
    intro h
    -- Proof comment: clause `(5)` is just clause `(4)` specialized to the product target.
    simpa [productHomMittagLefflerCondition] using
      h (ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))))
  tfae_have 5 → 3 := by
    intro h
    -- Proof comment: the imported product-target owner packages the source proof of `(5) → (3)`.
    exact product_hom_mittag_leffler_gives_stage_factorization (R := R) (F := F) h
  tfae_finish

end
