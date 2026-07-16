import Mathlib
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_proof.stacks_project.Chap17.Definition_17_12_1
import stacks_proof.stacks_project.Chap17.Lemma_17_12_4
import stacks_proof.stacks_project.Chap18.Definition_18_23_1
import stacks_proof.stacks_project.Chap18.Lemma_18_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

universe u

/- Domain-style sampling for Lemma 17.22.6:
- primary domain: internal Hom and coherence for sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsCoherent`,
  `AlgebraicGeometry.RingedSpace.internalHomStalkComparison_isIso_of_isFinitePresentation`,
  `CategoryTheory.Limits.kernel`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, with `IsCoherent` as the canonical public target
  property;
- primitive data:
  a finitely presented source `ℱ : RingedSpace.Modules X` and a coherent target
  `𝒢 : RingedSpace.Modules X`;
- derived API:
  the local finite-kernel presentation of `((ihom ℱ).obj 𝒢).over U` and the resulting coherence
  statement for `(ihom ℱ).obj 𝒢`.

Source/core/bridge triage:
- `source-facing`: the local kernel presentation by finite biproducts of copies of `𝒢`;
- `core/canonical`: the owner category `RingedSpace.Modules X`, the predicate `IsCoherent`, and
  categorical kernels;
- `bridge/view`: the coherence theorem deduced from the local presentation.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

/-- Helper for Lemma 17.22.6: a finitely presented module sheaf admits a neighborhood of any
point on which the restricted module has a finite presentation. -/
private theorem existsFinitePresentationNeighborhood
    (ℱ : ModX) (x : X) [ℱ.IsFinitePresentation] :
    ∃ (U : Opens X) (_ : x ∈ U) (P : (ℱ.over U).Presentation), P.IsFinite := by
  -- Proof comment: extract the canonical local finite-presentation data and choose a covering
  -- open containing the given point.
  let τ : ℱ.QuasicoherentData :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData ℱ).choose
  let hτ : τ.IsFinitePresentation :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData ℱ).choose_spec
  obtain ⟨V, _iV, hmem, hxV⟩ := τ.coversTop ⊤ x (by trivial)
  obtain ⟨j, ⟨f⟩⟩ := hmem
  -- The selected cover member already carries the finite presentation required later.
  refine ⟨τ.X j, f.le hxV, τ.presentation j, ?_⟩
  exact hτ.isFinite_presentation j

/-- Helper for Lemma 17.22.6: a family of open neighborhoods containing each point gives a
Grothendieck cover of the terminal object on the site of opens. -/
private theorem pointwiseOpenCoverCoversTop
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) :
    (Opens.grothendieckTopology X).CoversTop U := by
  -- Proof comment: every point of an open `V` lies in `V ∩ U x`, which still refines the chosen
  -- neighborhood and maps into `V`.
  intro V x hx
  refine ⟨V ⊓ U x, homOfLE inf_le_left, ?_, ?_⟩
  · exact ⟨x, ⟨homOfLE inf_le_right⟩⟩
  · exact ⟨hx, hU x⟩

/-- Helper for Lemma 17.22.6: the chosen relations of a presentation define the explicit map from
the relation free module to the generator free module. -/
private noncomputable def presentationRelationMap
    {U : Opens X} {ℱ : ModX} (P : (ℱ.over U).Presentation) :
    (SheafOfModules.free.{u} P.relations.I : SheafOfModules (X.ringCatSheaf.over U)) ⟶
      (SheafOfModules.free.{u} P.generators.I : SheafOfModules (X.ringCatSheaf.over U)) :=
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 17.22.6: the presentation relation map forms a complex with the chosen
generator surjection. -/
private theorem presentationRelationMap_comp_generators
    {U : Opens X} {ℱ : ModX} (P : (ℱ.over U).Presentation) :
    presentationRelationMap P ≫ P.generators.π = 0 := by
  -- Proof comment: the presentation relations already land in the kernel of the generator map.
  simp [presentationRelationMap]

/-- Helper for Lemma 17.22.6: the chosen generators exhibit the target as the cokernel of the
explicit relation map. -/
private noncomputable def presentationGenerators_isCokernel
    {U : Opens X} {ℱ : ModX} (P : (ℱ.over U).Presentation) :
    IsColimit
      (CokernelCofork.ofπ P.generators.π
        (presentationRelationMap_comp_generators (P := P))) := by
  -- Proof comment: `P.isColimit` is already the cokernel statement for this explicit relation
  -- map; only the relation-map spelling needs normalization.
  simpa [presentationRelationMap] using P.isColimit

/-- Helper for Lemma 17.22.6: the short complex attached to a chosen presentation is exact. -/
private theorem presentationShortComplexExact
    {U : Opens X} {ℱ : ModX} (P : (ℱ.over U).Presentation) :
    (ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))).Exact := by
  let S : ShortComplex (SheafOfModules (X.ringCatSheaf.over U)) :=
    ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))
  -- Proof comment: exactness is the standard "second map is a cokernel" criterion for the
  -- packaged presentation.
  simpa [S] using
    ShortComplex.exact_of_g_is_cokernel S (presentationGenerators_isCokernel (P := P))

/-- Helper for Lemma 17.22.6: internal Hom out of a finite free sheaf first identifies with the
limit of the constant diagram on the target sheaf. -/
private noncomputable def internalHomFreeIsoLimitConst
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U)) (I : Type u) [Fintype I] :
    (((MonoidalClosed.internalHom).flip.obj M).obj
        (op (SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) I))) ≅
      limit (Discrete.functor fun _ : I ↦ M) := by
  let F :
      (SheafOfModules (X.ringCatSheaf.over U))ᵒᵖ ⥤
        SheafOfModules (X.ringCatSheaf.over U) :=
    ((MonoidalClosed.internalHom).flip.obj M :
      (SheafOfModules (X.ringCatSheaf.over U))ᵒᵖ ⥤
        SheafOfModules (X.ringCatSheaf.over U))
  let c₀ :
      Cone ((Discrete.functor fun _ : I ↦
        (SheafOfModules.unit (X.ringCatSheaf.over U))).op) :=
    (SheafOfModules.freeCofan (R := X.ringCatSheaf.over U) I).op
  have hc₀ : IsLimit c₀ := by
    -- Proof comment: the opposite of the free coproduct cocone is the corresponding limit cone.
    simpa [c₀] using
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) I).op
  let c₁ :
      Cone (Discrete.functor fun _ : I ↦
        op (SheafOfModules.unit (X.ringCatSheaf.over U))) :=
    (Cone.postcompose Discrete.natIsoFunctor.inv).obj c₀
  have hc₁ : IsLimit c₁ := by
    -- Proof comment: rewrite the opposite constant-unit diagram into the standard discrete form.
    exact (IsLimit.postcomposeInvEquiv Discrete.natIsoFunctor c₀).symm hc₀
  let c₂ :
      Cone (Discrete.functor fun _ : I ↦
        (((MonoidalClosed.internalHom).flip.obj M).obj
          (op (SheafOfModules.unit (X.ringCatSheaf.over U))))) :=
    F.mapCone c₁
  have hc₂ : IsLimit c₂ := by
    -- Proof comment: source-variable internal Hom preserves limits, so it carries the free-source
    -- limit cone to a limit cone on the internal-Hom diagram.
    let _ : PreservesLimitsOfShape (Discrete I) F := by
      exact MonoidalClosed.preservesLimitsOfShape_internalHom_flip_obj
        (A := SheafOfModules (X.ringCatSheaf.over U)) (I := Discrete I) M
    simpa [F, c₂] using isLimitOfPreserves F hc₁
  let α :
      Discrete.functor
          (fun _ : I ↦
            (((MonoidalClosed.internalHom).flip.obj M).obj
              (op (SheafOfModules.unit (X.ringCatSheaf.over U))))) ≅
        Discrete.functor (fun _ : I ↦ M) :=
    Discrete.natIso fun _ : Discrete I ↦ MonoidalClosed.unitIsoSelf M
  let c₃ : Cone (Discrete.functor fun _ : I ↦ M) :=
    (Cone.postcompose α.hom).obj c₂
  have hc₃ : IsLimit c₃ := by
    -- Proof comment: transport the limiting cone along the constant-diagram unit comparison.
    exact (IsLimit.postcomposeHomEquiv α c₂).2 hc₂
  -- Proof comment: the transported cone point is canonically the limit object of the constant
  -- diagram on `M`.
  exact IsLimit.conePointUniqueUpToIso hc₃ (limit.isLimit (Discrete.functor fun _ : I ↦ M))

/-- Helper for Lemma 17.22.6: internal Hom out of a finite free sheaf is the finite biproduct of
copies of the target sheaf. -/
private noncomputable def internalHomFreeIsoFiniteBiproduct
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U)) (I : Type u) [Fintype I] :
    (((MonoidalClosed.internalHom).flip.obj M).obj
        (op (SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) I))) ≅
      ∏ᶜ fun _ : I ↦ M := by
  -- Proof comment: first identify the internal-Hom object with the canonical limit of the
  -- constant `M` diagram, then rewrite that limit as the finite biproduct/product object.
  exact
    internalHomFreeIsoLimitConst (X := X) (U := U) M I ≪≫
      (Pi.isoLimit (Discrete.functor fun _ : I ↦ M)).symm

/-- Helper for Lemma 17.22.6: a finite presentation yields a kernel presentation of the local
internal-Hom object, still indexed by the presentation generators and relations. -/
private theorem presentationInternalHomKernelIso
    {U : Opens X} {ℱ : ModX} (P : (ℱ.over U).Presentation)
    (M : SheafOfModules (X.ringCatSheaf.over U))
    [Fintype P.generators.I] [Fintype P.relations.I] :
    ∃ (φ :
        (∏ᶜ fun _ : P.generators.I ↦ M) ⟶
          (∏ᶜ fun _ : P.relations.I ↦ M)),
      Nonempty (((ihom (ℱ.over U)).obj M) ≅ kernel φ) := by
  let _ : HasFiniteBiproducts (SheafOfModules (X.ringCatSheaf.over U)) :=
    Abelian.hasFiniteBiproducts
  let S : ShortComplex (SheafOfModules (X.ringCatSheaf.over U)) :=
    ShortComplex.mk (presentationRelationMap P) P.generators.π
      (presentationRelationMap_comp_generators (P := P))
  have hSExact : S.Exact := by
    -- Proof comment: package the chosen presentation as the standard exact short complex.
    simpa [S] using presentationShortComplexExact (P := P)
  let T :
      ShortComplex (SheafOfModules (X.ringCatSheaf.over U)) :=
    S.op.map ((MonoidalClosed.internalHom).flip.obj M)
  have hT :
      T.Exact ∧ Mono T.f := by
    -- Proof comment: internal Hom is left exact in the source variable.
    simpa [S, T] using
      ringedSiteModuleInternalHom_exact_in_source
        (J := (Opens.grothendieckTopology X).over U) (𝒪 := X.sheaf.over U)
        (S := S) ⟨hSExact, inferInstance⟩ M
  let eGen :
      T.X₂ ≅ (∏ᶜ fun _ : P.generators.I ↦ M) :=
    internalHomFreeIsoFiniteBiproduct (X := X) (U := U) M P.generators.I
  let eRel :
      T.X₃ ≅ (∏ᶜ fun _ : P.relations.I ↦ M) :=
    internalHomFreeIsoFiniteBiproduct (X := X) (U := U) M P.relations.I
  let φ : (∏ᶜ fun _ : P.generators.I ↦ M) ⟶
      (∏ᶜ fun _ : P.relations.I ↦ M) :=
    eGen.inv ≫ T.g ≫ eRel.hom
  have hKernelT : IsLimit (KernelFork.ofι T.f T.zero) :=
    ((T.exact_and_mono_f_iff_f_is_kernel).1 hT).some
  let eKernel :
      kernel T.g ≅ kernel φ :=
    kernel.mapIso T.g φ eGen eRel (by
      -- Proof comment: `φ` is defined by conjugating `T.g` through the normalization isomorphisms.
      simp [φ, Category.assoc])
  refine ⟨φ, ⟨?_⟩⟩
  -- Proof comment: exactness identifies the first term with the kernel of the middle map, and the
  -- conjugation above transports that kernel to the theorem-surface morphism `φ`.
  exact
    IsLimit.conePointUniqueUpToIso hKernelT (kernelIsKernel T.g) ≪≫
      eKernel

-- Proof sketch: around each point, choose a local finite presentation of `ℱ` by finite free
-- `\mathcal O_U`-modules. Applying internal Hom into `𝒢|_U` turns that local presentation into a
-- left exact sequence whose first term identifies `\mathcal H\!om_{\mathcal O_U}(ℱ|_U, 𝒢|_U)` as
-- the kernel of a morphism between finite biproducts of copies of `𝒢|_U`.
/-- Lemma 17.22.6: if `\mathcal F` is finitely presented, then the internal-Hom sheaf
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is locally the kernel of a map
between finite direct sums of copies of `\mathcal G`, written here via the equivalent finite
biproduct presentation `∏ᶜ`. -/
@[stacks 01CQ]
theorem internalHom_locally_isKernel_of_finiteBiproductMap
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFinitePresentation] :
    ∃ (U : Opens X) (_ : x ∈ U) (m n : ℕ)
      (φ : (∏ᶜ fun _ : Fin m ↦ 𝒢.over U) ⟶ (∏ᶜ fun _ : Fin n ↦ 𝒢.over U)),
      Nonempty ((ℱ ⟶[ModX] 𝒢).over U ≅ kernel φ) := by
  -- Route correction: the source-faithful proof first chooses a finite presentation of `ℱ` on a
  -- neighborhood of `x`, then applies source-variable internal-Hom exactness to that local
  -- presentation and identifies the free terms with finite biproducts of copies of `𝒢.over U`.
  rcases existsFinitePresentationNeighborhood ℱ x with ⟨U, hxU, P, hP⟩
  let _ : Finite P.generators.I := inferInstance
  let _ : Finite P.relations.I := inferInstance
  let _ : Fintype P.generators.I := Fintype.ofFinite P.generators.I
  let _ : Fintype P.relations.I := Fintype.ofFinite P.relations.I
  rcases presentationInternalHomKernelIso (X := X) (P := P) (M := 𝒢.over U) with
    ⟨φI, ⟨eI⟩⟩
  let m : ℕ := Fintype.card P.generators.I
  let n : ℕ := Fintype.card P.relations.I
  let eGen :
      (∏ᶜ fun _ : P.generators.I ↦ 𝒢.over U) ≅
        (∏ᶜ fun _ : Fin m ↦ 𝒢.over U) :=
    biproduct.reindex (Fintype.equivFin P.generators.I) (fun _ : Fin m ↦ 𝒢.over U)
  let eRel :
      (∏ᶜ fun _ : P.relations.I ↦ 𝒢.over U) ≅
        (∏ᶜ fun _ : Fin n ↦ 𝒢.over U) :=
    biproduct.reindex (Fintype.equivFin P.relations.I) (fun _ : Fin n ↦ 𝒢.over U)
  let φ :
      (∏ᶜ fun _ : Fin m ↦ 𝒢.over U) ⟶ (∏ᶜ fun _ : Fin n ↦ 𝒢.over U) :=
    eGen.inv ≫ φI ≫ eRel.hom
  let eKernel :
      kernel φI ≅ kernel φ :=
    kernel.mapIso φI φ eGen eRel (by
      -- Proof comment: the final map is just the `Fin`-reindexed conjugate of `φI`.
      simp [φ, Category.assoc])
  refine ⟨U, hxU, m, n, φ, ⟨eI ≪≫ eKernel⟩⟩

-- Proof sketch: apply the local kernel presentation above. Finite biproducts of a coherent sheaf
-- are coherent, and Lemma `17.12.4` shows that kernels of morphisms between coherent sheaves are
-- coherent; coherence is local on the base, so the local kernel presentations glue.
/-- For a finitely presented source and coherent target, the internal-Hom sheaf is coherent. -/
theorem internalHom_isCoherent_of_isFinitePresentation
    (ℱ 𝒢 : ModX) [ℱ.IsFinitePresentation] [𝒢.IsCoherent] :
    (ℱ ⟶[ModX] 𝒢).IsCoherent := by
  -- Route correction: once the local kernel presentation is available, the remaining argument is
  -- to cover `X` by those neighborhoods, transport each restricted kernel presentation to the
  -- open-subspace module category, and apply coherence of kernels of maps between finite products
  -- of coherent restrictions.
  let U : X → Opens X := fun x ↦ (internalHom_locally_isKernel_of_finiteBiproductMap ℱ 𝒢 x).choose
  let hU : ∀ x : X, x ∈ U x := fun x ↦
    (internalHom_locally_isKernel_of_finiteBiproductMap ℱ 𝒢 x).choose_spec.choose
  let hCover : (Opens.grothendieckTopology X).CoversTop U :=
    pointwiseOpenCoverCoversTop U hU
  refine
    (SheafOfModules.RingedSite.isCoherent_iff_exists_cover_isCoherent_over
      (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf) (ℱ := (ℱ ⟶[ModX] 𝒢))).2 ?_
  exact ⟨X, U, hCover, ?_⟩
  intro x
  rcases (internalHom_locally_isKernel_of_finiteBiproductMap ℱ 𝒢 x).choose_spec.choose_spec with
    ⟨m, n, φ, ⟨e⟩⟩
  -- Proof comment: the local kernel model from the first theorem reduces coherence to the kernel
  -- of a map between finite biproducts of the coherent restriction `𝒢.over (U x)`.
  let _ : (𝒢.over (U x)).IsCoherent := inferInstance
  let _ : (∏ᶜ fun _ : Fin m ↦ 𝒢.over (U x)).IsCoherent := inferInstance
  let _ : (∏ᶜ fun _ : Fin n ↦ 𝒢.over (U x)).IsCoherent := inferInstance
  have hkernel : (kernel φ).IsCoherent := isCoherent_kernel φ
  let _ : (kernel φ).IsCoherent := hkernel
  -- Proof comment: coherence is invariant under isomorphism, so transport the kernel coherence
  -- back along the chosen local comparison isomorphism.
  exact SheafOfModules.IsCoherent.of_iso e.symm

end AlgebraicGeometry.RingedSpace
