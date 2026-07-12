import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_32_8
import StacksProject_2024.Chap07.Lemma_7_41_4
import StacksProject_2024.Chap18.Lemma_18_15_1
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap18.Example_18_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped GroupSitePoint

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Φ : GrothendieckTopology.Point.{w} J)
variable [HasWeakSheafify J RingCat.{max u v}]
variable [HasWeakSheafify typesGrothendieckTopology RingCat.{max u v}]
variable
  [(Φ.fiber.sheafPushforwardContinuous RingCat.{max u v} J
    typesGrothendieckTopology).IsRightAdjoint]
variable (𝒪 : Sheaf J RingCat.{max u v})

private abbrev pointUnit :
    𝒪 ⟶
      (Φ.fiber.sheafPushforwardContinuous RingCat.{max u v} J
        typesGrothendieckTopology).obj
        ((Φ.fiber.sheafPullback RingCat.{max u v} J typesGrothendieckTopology).obj 𝒪) :=
  ((Φ.fiber.sheafAdjunctionContinuous RingCat.{max u v} J
    typesGrothendieckTopology).unit.app 𝒪)
/-
Domain-style sampling for Lemma 18.37.2:
- primary domain: pullback and pushforward of sheaves of modules along the morphism of topoi
  attached to a site point;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.Functor.sheafOfModules_pushforward_exact_of_isAlmostCocontinuous`,
  `Pi.constAddMonoidHom`,
  the built-in instance `(SheafOfModules.pushforward φ).IsRightAdjoint`;
- best owner abstraction: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction` for the canonical unit map `pointUnit Φ 𝒪`;
- primitive data: the point `Φ`, the ring sheaf `𝒪`, and that canonical unit map
  `pointUnit Φ 𝒪 : 𝒪 ⟶ p_* p⁻¹ 𝒪`;
- derived API: exactness of the corresponding module pushforward, the inferable epimorphism
  structure on the underlying abelian counit from Lemma `18.37.1`, the `𝒪_p`-linear counit
  component in `SheafOfModules`, and the source-facing nonlinearity of the explicit constant-map
  section from Example `18.37.3`;
- source/core/bridge triage:
  `source-facing`: the exactness and counit-splitting statements of Lemma 18.37.2;
  `core/canonical`: `SheafOfModules.pushforward`, `SheafOfModules.pullback`, and
    `SheafOfModules.pullbackPushforwardAdjunction` on the unit map;
  `bridge/view`: the specialization of those owners to the point `Φ`, plus the group-site model
    from Example `18.37.3` used only to witness that the additive section from Lemma `18.37.1`
    need not be `𝒪_p`-linear.

The deleted public abbreviations in the old version were only local renamings of this owner API,
so the public surface is refined to the canonical declarations directly. -/

variable
  [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint]
  (M : SheafOfModules
    ((Φ.fiber.sheafPullback RingCat.{max u v} J typesGrothendieckTopology).obj 𝒪))

/- Route correction: instead of transporting the module counit to the additive point-adjunction
   counit, prove directly that the module pushforward reflects epimorphisms and then apply the
   abstract adjunction criterion for epic counits. -/

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: forgetting additive structure preserves local surjectivity of a
sheaf morphism. -/
private theorem underlyingLocallySurjectiveOfAdditiveSheafMap
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {X Y : Sheaf K AddCommGrpCat.{max u v}} (φ : X ⟶ Y)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Sheaf.IsLocallySurjective ((sheafCompose K (forget AddCommGrpCat.{max u v})).map φ) := by
  -- Proof comment: forgetting additive structure does not change the underlying image sieve.
  change Presheaf.IsLocallySurjective K
    (Functor.whiskerRight φ.hom (forget AddCommGrpCat.{max u v}))
  change Presheaf.IsLocallySurjective K φ.hom at hφ
  refine Presheaf.IsLocallySurjective.mk ?_
  intro V s
  simpa [Presheaf.imageSieve] using hφ.imageSieve_mem (U := V) s

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: a morphism of sheaves of abelian groups is epic exactly when its
underlying morphism of set-valued sheaves is epic. -/
private theorem sheafAddCommGrp_epi_iff_forget_epi
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {X Y : Sheaf K AddCommGrpCat.{max u v}} (φ : X ⟶ Y) :
    Epi φ ↔ Epi ((sheafCompose K (forget AddCommGrpCat.{max u v})).map φ) := by
  constructor
  · intro hφ
    -- Proof comment: convert the additive epi to local surjectivity, then forget it to sets.
    let hloc : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} φ).2 hφ
    exact (Sheaf.isLocallySurjective_iff_epi _).1
      (underlyingLocallySurjectiveOfAdditiveSheafMap (φ := φ) hloc)
  · intro hφ
    -- Proof comment: the faithful forgetful functor reflects epimorphisms back to additive
    -- sheaves.
    exact (sheafCompose K (forget AddCommGrpCat.{max u v})).epi_of_epi_map hφ

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the type-valued point-pushforward preserves epimorphisms. -/
private theorem pointTypePushforwardPreservesEpimorphisms :
    (Φ.fiber.sheafPushforwardContinuous (Type (max u v)) J
      typesGrothendieckTopology).PreservesEpimorphisms := by
  -- TODO for Lemma 18.37.2: identify the type-valued point pushforward with a point-skyscraper
  -- functor or prove directly that a surjective map of types stays locally surjective after
  -- `Φ.fiber.sheafPushforwardContinuous`; this is the first missing bridge for exactness.
  sorry

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the type-valued point-pushforward reflects epimorphisms. -/
private theorem pointTypePushforwardReflectsEpimorphisms :
    (Φ.fiber.sheafPushforwardContinuous (Type (max u v)) J
      typesGrothendieckTopology).ReflectsEpimorphisms := by
  -- TODO for Lemma 18.37.2: after the same type-valued point-pushforward bridge is in place,
  -- reflect epimorphy back from the pushed-forward sheaf map to the underlying map of types.
  sorry

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: forgetting module pushforward to additive sheaves is definitionally
the same as first forgetting and then applying additive point pushforward. -/
private theorem pointModulePushforwardCompToSheaf :
    SheafOfModules.pushforward (pointUnit Φ 𝒪) ⋙ SheafOfModules.toSheaf 𝒪 =
      SheafOfModules.toSheaf
          ((Φ.fiber.sheafPullback RingCat.{max u v} J typesGrothendieckTopology).obj 𝒪) ⋙
        Φ.fiber.sheafPushforwardContinuous AddCommGrpCat.{max u v} J
          typesGrothendieckTopology := by
  rfl

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the additive point-pushforward functor reflects epimorphisms. -/
private theorem pointAdditivePushforwardReflectsEpimorphisms :
    (Φ.fiber.sheafPushforwardContinuous AddCommGrpCat.{max u v} J
      typesGrothendieckTopology).ReflectsEpimorphisms := by
  -- TODO for Lemma 18.37.2: after establishing the type-valued reflection statement above,
  -- transport it through the additive forgetful functor exactly as in Lemma `18.19.4`.
  sorry

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: if the underlying additive-sheaf map of a module morphism is epic,
then the original module morphism is epic. -/
private theorem epi_of_toSheaf_map_epi
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{max u v})
    {M N : SheafOfModules R}
    (φ : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf R).map φ)] :
    Epi φ := by
  -- Proof comment: faithfulness of `toSheaf` reflects right-cancellability back to module
  -- sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf R).map_injective
  apply (cancel_epi ((SheafOfModules.toSheaf R).map φ)).1
  simpa using congrArg ((SheafOfModules.toSheaf R).map) hgh

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the additive point-pushforward preserves epimorphisms. -/
private theorem pointAdditivePushforwardPreservesEpimorphisms :
    (Φ.fiber.sheafPushforwardContinuous AddCommGrpCat.{max u v} J
      typesGrothendieckTopology).PreservesEpimorphisms := by
  -- TODO for Lemma 18.37.2: once the type-valued preservation statement is proved, lift it to
  -- additive sheaves by forgetting and reassembling epimorphy as in Lemma `18.15.3`.
  sorry

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the point-pushforward functor on modules preserves epimorphisms. -/
private theorem pointModulePushforwardPreservesEpimorphisms :
    (SheafOfModules.pushforward (pointUnit Φ 𝒪)).PreservesEpimorphisms := by
  -- TODO for Lemma 18.37.2: after additive preservation is available, forget module pushforward
  -- to additive sheaves, preserve epimorphy there, and lift it back through `toSheaf`.
  sorry

omit [(SheafOfModules.pushforward (pointUnit Φ 𝒪)).IsRightAdjoint] in
/-- Helper for Lemma 18.37.2: the point-pushforward functor on modules reflects epimorphisms. -/
private theorem pointModulePushforwardReflectsEpimorphisms :
    (SheafOfModules.pushforward (pointUnit Φ 𝒪)).ReflectsEpimorphisms := by
  -- TODO for Lemma 18.37.2: after additive reflection is available, forget module pushforward to
  -- additive sheaves, reflect epimorphy there, and lift it back through `toSheaf`.
  sorry

-- Proof sketch: the point direct image on modules is the pushforward functor along the unit map
-- `\mathcal O \to p_* p^{-1} \mathcal O`; exactness follows from the generic abelian argument
-- for a right adjoint that preserves epimorphisms and hence homology.
/-- Lemma 18.37.2 (1): for a ringed topos `(Sh(\mathcal C), \mathcal O)` and a point `p`, the
direct-image functor `p_*` on modules over `p^{-1} \mathcal O` is exact. -/
theorem point_module_pushforward_exact :
    exactFunctor
      (SheafOfModules
        ((Φ.fiber.sheafPullback RingCat.{max u v} J typesGrothendieckTopology).obj 𝒪))
      (SheafOfModules 𝒪)
      (SheafOfModules.pushforward (pointUnit Φ 𝒪)) := by
  -- TODO for Lemma 18.37.2: the remaining work is to prove that point-pushforward on modules
  -- preserves epimorphisms; then the right-adjoint exactness argument above closes immediately.
  sorry

-- Proof sketch: forgetting scalars identifies the underlying abelian sheaf map of the module
-- counit with the split-epimorphic counit from Lemma `18.37.1`; since `SheafOfModules.toSheaf`
-- reflects epimorphisms, the canonical module counit is epic.
/-- Lemma 18.37.2 (2): for any `p^{-1}\mathcal O`-module `M`, the canonical counit
`p^{-1} p_* M ⟶ M`, namely
`(SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪)).counit.app M`, is an
epimorphism. -/
theorem point_module_counit_epi :
    Epi ((SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪)).counit.app M) := by
  -- Proof comment: once point pushforward on modules is known to reflect epimorphisms, the
  -- module counit is epic by the general adjunction theorem.
  have hReflect :
      (SheafOfModules.pushforward (pointUnit Φ 𝒪)).ReflectsEpimorphisms :=
    pointModulePushforwardReflectsEpimorphisms (Φ := Φ) (𝒪 := 𝒪)
  have hCounit :
      ∀ X : SheafOfModules
        ((Φ.fiber.sheafPullback RingCat.{max u v} J typesGrothendieckTopology).obj 𝒪),
        Epi ((SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪)).counit.app X) :=
    (CategoryTheory.Adjunction.epi_counit_app_iff_reflectsEpimorphisms
      (SheafOfModules.pullbackPushforwardAdjunction (pointUnit Φ 𝒪))).2 hReflect
  exact hCounit M

-- Proof sketch: in the group-site model from Example `18.37.3`, the additive section from
-- Lemma `18.37.1` is the constant-function map `Pi.constAddMonoidHom G M`. Example `18.37.3`
-- shows that this map is not `R`-linear in general for the twisted module structure, so the
-- additive section from Lemma `18.37.1` does not in general upgrade to an `R`-linear splitting
-- of the module counit, identified in that model with the canonical projection
-- `LinearMap.proj (1 : G)`.
/-- Lemma 18.37.2 (3): in the group-site model from Example `18.37.3`, the additive section of
the counit from Lemma `18.37.1`, realized by the constant-function map
`Pi.constAddMonoidHom G M : M →+ Map[R](G, M)`, is not in general `R`-linear for the twisted
module structure, hence does not extend to an `R`-linear splitting of the canonical module
counit `LinearMap.proj (1 : G)`. -/
theorem point_module_counit_section_not_linear_in_general :
    ¬ ∀ {G : Type (max u v)} [Group G] {R : Type v} [Semiring R] [MulSemiringAction G R]
        {M : Type w} [AddCommMonoid M] [Module R M],
        ∃ s : M →ₗ[R] Map[R](G, M),
          ∀ m : M, s m = Pi.constAddMonoidHom G M m := by
  intro h
  let R : Type v := ULift.{v, 0} (Int × Int)
  let G : Type (max u v) := ULift.{u, v} (R ≃+* R)
  let _ : MulSemiringAction G R where
    smul σ r := σ.down r
    one_smul := by
      intro r
      rfl
    mul_smul := by
      intro σ τ r
      rfl
    smul_zero := by
      intro σ
      exact σ.down.map_zero
    smul_add := by
      intro σ a b
      exact σ.down.map_add a b
    smul_one := by
      intro σ
      exact σ.down.map_one
    smul_mul := by
      intro σ a b
      exact σ.down.map_mul a b
  let σ0 : R ≃+* R :=
    { toFun := fun r ↦ ⟨Prod.swap r.down⟩
      invFun := fun r ↦ ⟨Prod.swap r.down⟩
      left_inv := by
        intro r
        cases r
        rfl
      right_inv := by
        intro r
        cases r
        rfl
      map_mul' := by
        intro a b
        cases a
        cases b
        rfl
      map_add' := by
        intro a b
        cases a
        cases b
        rfl }
  let σ : G := ⟨σ0⟩
  have hσ : σ • (⟨(1, 0)⟩ : R) = ((⟨(0, 1)⟩ : R)) := by
    rfl
  -- Proof comment: specialize the universal claim to the swap automorphism of `Int × Int`.
  obtain ⟨s, hs⟩ := h (G := G) (R := R) (M := R)
  have hs_r : s (⟨(1, 0)⟩ : R) σ = (⟨(1, 0)⟩ : R) := by
    simpa using congrFun (hs (⟨(1, 0)⟩ : R)) σ
  have hs_one : s (1 : R) σ = (1 : R) := by
    simpa using congrFun (hs (1 : R)) σ
  have hsmul : (((⟨(1, 0)⟩ : R)) • s 1) σ = ((⟨(0, 1)⟩ : R)) := by
    -- Proof comment: evaluating the twisted scalar action at the swap sends `(1, 0)` to
    -- `(0, 1)`.
    simpa [GroupSitePoint.Coeff, hσ, hs_one] using
      (Pi.smul_apply (⟨(1, 0)⟩ : R) (s 1) σ)
  have hcalc : s (⟨(1, 0)⟩ : R) σ = ((⟨(0, 1)⟩ : R)) := by
    -- Proof comment: linearity rewrites the constant value at `(1, 0)` to the twisted scalar
    -- action of `(1, 0)` on the value at `1`.
    calc
      s (⟨(1, 0)⟩ : R) σ = s ((⟨(1, 0)⟩ : R) • (1 : R)) σ := by simp
      _ = (((⟨(1, 0)⟩ : R)) • s 1) σ := by
        simpa using congrFun (s.map_smul (⟨(1, 0)⟩ : R) (1 : R)) σ
      _ = ((⟨(0, 1)⟩ : R)) := hsmul
  have hpair : (⟨(1, 0)⟩ : R) = ((⟨(0, 1)⟩ : R)) :=
    hs_r.symm.trans hcalc
  have hpairDown : ((1, 0) : Int × Int) = ((0, 1) : Int × Int) :=
    congrArg ULift.down hpair
  have : (1 : Int) = 0 :=
    congrArg Prod.fst hpairDown
  norm_num at this
