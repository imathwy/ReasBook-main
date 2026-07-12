import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.11.4:
- primary domain: finitely presented sheaves of modules over a sheaf of rings on a site, and
  finite-type control of kernels of epimorphisms;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.free`,
  `CategoryTheory.ObjectProperty.prop_of_epi`;
- best owner abstraction:
  the ambient owner category `SheafOfModules R`, with finite type / finite presentation as the
  canonical owner predicates and `kernel` as derived abelian-category data, so the generic
  epimorphism theorem is the owner result and the finite-free case is a source-facing
  specialization;
- primitive data:
  the ambient sheaf of rings `R`, a finitely presented target sheaf, and either an epimorphism
  from a finite free sheaf or an epimorphism from a finite-type sheaf;
- derived API:
  the source-facing finite-type conclusions for the corresponding kernels.

Source/core/bridge triage:
- `source-facing`: the finite-free kernel statement in part `(1)` of Stacks Project Lemma
  `17.11.4`;
- `core/canonical`: the generic owner theorem for kernels of epimorphisms from finite-type
  sheaves into finitely presented sheaves, inside `SheafOfModules R`;
- `bridge/view`: ringed spaces are only the specialization `R = (RingedSpace.ringCatSheaf X)`.

As in Lemma 17.9.3, the public statements are best kept at the generic `SheafOfModules` owner
layer rather than as ringed-space-specific wrappers. Accordingly, the generic finite-type source
theorem is kept as the owner result below, and the finite-free source statement is retained only
as the source-facing specialization. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- Helper for Lemma 17.11.4: the identity family of objects gives the maximal sieve on every
object. -/
lemma sieve_ofObjects_id_eq_top (W : C) :
    Sieve.ofObjects (fun X : C ↦ X) W = ⊤ := by
  -- Every arrow into `W` factors through the identity-family member `W` via `𝟙 W`.
  simpa using Sieve.pullback_ofObjects_eq_top (Y := fun X : C ↦ X) (X := W) (g := 𝟙 W)

/-- Helper for Lemma 17.11.4: the identity family of objects canonically covers the terminal
object of the site. -/
lemma coversTop_id : J.CoversTop (fun X : C ↦ X) := by
  -- After identifying the identity-family sieve with `⊤`, the covering condition is immediate.
  intro W
  rw [sieve_ofObjects_id_eq_top]
  exact J.covering_of_eq_top rfl

/-- Helper for Lemma 17.11.4: the tautological basis of a free sheaf already gives a finite
global generating family. -/
private theorem exists_free_generatingSections (I : Type u) [Finite I] :
    ∃ σ : (free (R := R) I).GeneratingSections, σ.IsFiniteType := by
  refine ⟨{ I := I, s := SheafOfModules.freeSection (R := R), epi := ?_ }, ?_⟩
  · -- Proof comment: the tautological basis family is the image of the identity morphism under
    -- `freeHomEquiv`, so the associated map is literally `𝟙 (free I)`.
    change Epi
      (((free (R := R) I).freeHomEquiv).symm
        (((free (R := R) I).freeHomEquiv) (𝟙 (free (R := R) I))))
    simpa using (show Epi (𝟙 (free (R := R) I)) from inferInstance)
  · -- Proof comment: finiteness is exactly finiteness of the basis index type `I`.
    exact SheafOfModules.GeneratingSections.IsFiniteType.mk inferInstance

/-- Helper for Lemma 17.11.4: the inverse terminal-evaluation section is compatible with
restriction maps in the slice category. -/
private theorem over_sections_equiv_evaluation_inv_naturality
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ f : V ⟶ Y,
      M.val.map f (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of `Over U` has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 17.11.4: rebuild a section on the slice from its value at the terminal
object. -/
private noncomputable def over_sections_from_terminal
    {U : C} (M : SheafOfModules (R.over U))
    (m : M.val.obj (op (Over.mk (𝟙 U)))) : M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (over_sections_equiv_evaluation_inv_naturality (M := M) m)

/-- Helper for Lemma 17.11.4: a slice section is recovered from its value at the terminal object by
restricting along the unique terminal maps. -/
private theorem over_sections_equiv_evaluation_left_inv
    {U : C} {M : SheafOfModules (R.over U)} (s : M.sections) :
    over_sections_from_terminal M (s.1 (op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: a section on the slice is determined by its restrictions from the terminal
  -- object.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 17.11.4: evaluating the reconstructed slice section at the terminal object
returns the original value. -/
private theorem over_sections_equiv_evaluation_right_inv
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (over_sections_from_terminal M m).1 (op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the unique endomorphism of the terminal object is the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.11.4: terminal evaluation identifies sections on a slice with the value at
the terminal object. -/
private noncomputable def over_sections_equiv_evaluation
    {U : C} (M : SheafOfModules (R.over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
    invFun := over_sections_from_terminal M
    left_inv := over_sections_equiv_evaluation_left_inv (M := M)
    right_inv := over_sections_equiv_evaluation_right_inv (M := M) }

/-- Helper for Lemma 17.11.4: terminal evaluation of the inverse equivalence is definitionally the
input value. -/
private theorem over_sections_equiv_evaluation_symm_apply
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (((over_sections_equiv_evaluation (M := M)).symm m).1 (op (Over.mk (𝟙 U)))) = m := by
  -- Proof comment: this is just the right-inverse property of the terminal-evaluation
  -- equivalence.
  simpa using over_sections_equiv_evaluation_right_inv (M := M) m

/-- Helper for Lemma 17.11.4: placeholder for the transport comparing the slice free basis section
with the ambient basis restricted to `U`. -/
private theorem over_sections_equiv_evaluation_freeSection
    (U : C) (I : Type u) (i : I) : True := by
  -- TODO: restate this helper with the correct free-restriction transport map, matching the
  -- `restrictedFreeBasisTransport` shape from the slice-restriction development.
  trivial

/-- Helper for Lemma 17.11.4: placeholder for the tautological comparison between the restricted
ambient free basis and the canonical free basis on the slice. -/
private theorem over_free_tautological_sections_symm
    (U : C) (I : Type u) : True := by
  -- TODO: restate this helper using the missing restriction isomorphism from the free sheaf over
  -- `R.over U` to the restriction of the ambient free sheaf.
  trivial

/-- Helper for Lemma 17.11.4: the canonical free sheaf over the slice site already has finitely
many tautological generators. -/
private theorem exists_sliceFreeGeneratingSections (U : C) (I : Type u) [Finite I] :
    [∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat.{u}] →
    [∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{u}] →
    [∀ X : Over U, ((J.over U).over X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})] →
    ∃ σ : (free (R := R.over U) I).GeneratingSections, σ.IsFiniteType := by
  -- Proof comment: once we move entirely inside the slice site, the tautological basis is exactly
  -- the global finite generating family from `exists_free_generatingSections`.
  intro _ _ _
  exact exists_free_generatingSections (R := R.over U) I

/-- Helper for Lemma 17.11.4: on each slice site, the restricted ambient basis of a free sheaf
should give finitely many generators of the restricted free sheaf. -/
private theorem exists_over_free_generatingSections (U : C) (I : Type u) [Finite I] :
    True := by
  -- Proof comment: this abandoned slice-transport placeholder is not part of the final proof.
  trivial

/-- Helper for Lemma 17.11.4: a free sheaf on a finite index type is of finite type. -/
theorem free_isFiniteType_of_finite (I : Type u) [Finite I] :
    (free (R := R) I).IsFiniteType := by
  -- TODO: compare `(free (R := R) I).over U` with `free (R := R.over U) I` on each slice and use
  -- the tautological finite generators of the slice free sheaf.
  sorry

/-- Helper for Lemma 17.11.4: restriction along the identity comparison of ring sheaves preserves
zero morphisms. -/
private theorem pushforwardIdPreservesZeroMorphisms (U : C) :
    (SheafOfModules.pushforward (𝟙 (R.over U))).PreservesZeroMorphisms := by
  -- Proof comment: for the identity comparison, the pushforward functor acts objectwise on
  -- morphisms, so it sends the zero morphism to the zero morphism definitionally.
  refine ⟨?_⟩
  intro M N
  rfl

/-- Helper for Lemma 17.11.4: restricting the kernel of a morphism to a slice site agrees with the
kernel of the restricted morphism. -/
noncomputable def kernel_over_iso
    {M N : SheafOfModules R} (θ : M ⟶ N) (U : C) :
    ((kernel θ).over U) ≅ kernel ((SheafOfModules.pushforward (𝟙 (R.over U))).map θ) := sorry

/-- Helper for Lemma 17.11.4: for an epimorphism `η`, the canonical map
`kernel (η ≫ θ) ⟶ kernel θ` is epi. -/
theorem kernel_map_of_epi_is_epi
    {A B K : SheafOfModules R} (η : A ⟶ B) [Epi η] (θ : B ⟶ K) :
    Epi (kernel.map (η ≫ θ) θ η (𝟙 K) (by simp)) := by
  -- Proof comment: in an abelian category, the comparison from `kernel (η ≫ θ)` to `kernel θ`
  -- is the pullback of the epi `η`, so it should be epi by the ambient abelian-category API.
  sorry

/-- Helper for Lemma 17.11.4: a finite family of generating sections transports across an
isomorphism on the slice site. -/
private theorem finiteGeneratingSectionsOfIso
    {U : C} {M N : SheafOfModules (R.over U)} (e : M ≅ N)
    (σ : N.GeneratingSections) (hσ : σ.IsFiniteType) :
    ∃ τ : M.GeneratingSections, τ.IsFiniteType := by
  let τ : M.GeneratingSections :=
    (SheafOfModules.GeneratingSections.equivOfIso e).symm σ
  refine ⟨τ, ?_⟩
  -- Proof comment: `GeneratingSections.equivOfIso` keeps the same index type, so finiteness is
  -- unchanged after transport.
  refine SheafOfModules.GeneratingSections.IsFiniteType.mk ?_
  change Finite σ.I
  infer_instance

/-- Helper for Lemma 17.11.4: on a fixed chart `U`, a finite generating family of `𝒢.over U`
should induce a finite generating family of `((kernel θ).over U)` when the target is finitely
presented. -/
private theorem existsFiniteGeneratingSectionsKernelOverOfEpiFinitePresentation
    {𝒢 ℱ : SheafOfModules R} (θ : 𝒢 ⟶ ℱ) [Epi θ] [ℱ.IsFinitePresentation] (U : C)
    (σ : (𝒢.over U).GeneratingSections) (hσ : σ.IsFiniteType) :
    ∃ τ : ((kernel θ).over U).GeneratingSections, τ.IsFiniteType := by
  -- TODO: first produce finitely many global generators of
  -- `kernel ((SheafOfModules.pushforward (𝟙 (R.over U))).map θ)` on the slice site
  -- `SheafOfModules (R.over U)`, using a finite-presentation witness for `ℱ.over U` together with
  -- the finite source generators `σ`. Then transport that family back across
  -- `finiteGeneratingSectionsOfKernelOverIso`.
  sorry

-- Proof sketch: locally choose a surjection from a finite free sheaf onto `𝒢`; the composite with
-- `θ` is still epi, so the finite-free case gives finite type for its kernel. The canonical exact
-- sequence comparing `kernel (ψη)` and `kernel θ` then shows that `kernel θ` is an image of a
-- finite type sheaf, hence is itself of finite type.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.11.4 (2): if `θ : 𝒢 \to ℱ` is surjective, `𝒢` is of finite type, and `ℱ` is of finite
presentation, then `kernel θ` is of finite type. -/
@[stacks 01BP]
theorem isFiniteType_kernel_of_epi_of_finitePresentation
    {𝒢 ℱ : SheafOfModules R} (θ : 𝒢 ⟶ ℱ)
    [Epi θ] [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel θ).IsFiniteType := by
  -- TODO: rebuild the global local-generators datum from the chartwise slice helper once the
  -- restricted finite-presentation bridge is available.
  sorry

-- Proof sketch: this is the finite-free specialization of the owner theorem above, stated with
-- the source's rank-`r` free sheaf surface.
/-- Lemma 17.11.4 (1): if `ℱ` is a finitely presented `\mathcal O`-module and
`ψ : \mathcal O^{\oplus r} \to ℱ` is surjective, then `kernel ψ` is of finite type. -/
@[stacks 01BP]
theorem isFiniteType_kernel_of_epi_free_of_finitePresentation
    {ℱ : SheafOfModules R} [ℱ.IsFinitePresentation] (r : ℕ)
    (ψ : free (ULift.{u} (Fin r)) ⟶ ℱ) [Epi ψ] :
    (kernel ψ).IsFiniteType := by
  -- TODO: specialize the owner theorem after `free_isFiniteType_of_finite` and the owner kernel
  -- theorem are both repaired.
  sorry

end SheafOfModules
