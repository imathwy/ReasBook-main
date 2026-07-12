import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open PrimeSpectrum
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced `ModuleCat.tilde` and the affine `Spec`/`Γ` API; the
-- concrete owner here is therefore the actual sheaf of `A`-modules
-- `AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)` over `Spec A`, together
-- with a chosen finite basic-open cover coming from `I.FG`.

/-- The canonical sheaf of `A`-modules attached to `\widetilde M` on `Spec(A)`. -/
private noncomputable def tildeSheaf (M : ModuleCat A) :
    TopCat.Sheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)

private noncomputable def tildePresheaf (M : ModuleCat A) :
    TopCat.Presheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  (tildeSheaf M).1

/-- The open complement `Spec(A) \ V(I)` as an open subset of `Spec(A)`. -/
def idealComplementOpens (I : Ideal A) : (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A chosen finite generating set for a finitely generated ideal, repackaged as a `Fin`-indexed
family. This is internal scaffolding for the finite basic-open cover used in the comparison map. -/
private noncomputable def idealGeneratorsData (I : Ideal A) (hI : I.FG) :
    Σ r : ℕ, Fin r → A := by
  classical
  let s : Finset A := Classical.choose hI
  refine ⟨s.card, fun i ↦ (s.equivFin.symm i : A)⟩

/-- The number of chosen generators in `idealGeneratorsData`. -/
private noncomputable abbrev idealGeneratorCount (I : Ideal A) (hI : I.FG) : ℕ :=
  (idealGeneratorsData I hI).1

/-- The chosen `Fin`-indexed generator family attached to `idealGeneratorsData`. -/
private noncomputable abbrev idealGenerators (I : Ideal A) (hI : I.FG) :
    Fin (idealGeneratorCount I hI) → A :=
  (idealGeneratorsData I hI).2

/-- Each chosen generator belongs to the ideal it generates. -/
private theorem idealGenerators_mem (I : Ideal A) (hI : I.FG) (i : Fin (idealGeneratorCount I hI)) :
    idealGenerators I hI i ∈ I := sorry

/-- The chosen generator family spans the given finitely generated ideal. -/
private theorem span_idealGenerators (I : Ideal A) (hI : I.FG) :
    Ideal.span (Set.range (idealGenerators I hI)) = I := sorry

/-- The chosen basic-open cover attached to a finitely generated ideal. -/
private noncomputable def idealGeneratorBasicOpen (I : Ideal A) (hI : I.FG)
    (i : Fin (idealGeneratorCount I hI)) :
    (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (idealGenerators I hI i)

/-- Each chosen basic open lies in `Spec(A) \ V(I)`. -/
private theorem idealGeneratorBasicOpen_le_complement
    (I : Ideal A) (hI : I.FG) (i : Fin (idealGeneratorCount I hI)) :
    idealGeneratorBasicOpen I hI i ≤ idealComplementOpens I := sorry

/-- The chosen basic opens cover `Spec(A) \ V(I)`. -/
private theorem idealComplementOpens_le_iSup_idealGeneratorBasicOpen
    (I : Ideal A) (hI : I.FG) :
    idealComplementOpens I ≤ iSup (idealGeneratorBasicOpen I hI) := sorry

private def idealComplementSectionType (I : Ideal A) (M : ModuleCat A) : Type u :=
  ((tildePresheaf M).obj (Opposite.op (idealComplementOpens I)) : Type u)

/-- The additive group of sections of `\widetilde M` on `Spec(A) \ V(I)`. -/
noncomputable abbrev idealComplementTildeSections (I : Ideal A) (M : ModuleCat A) :
    AddCommGrpCat :=
  AddCommGrpCat.of (idealComplementSectionType I M)

/-- The `n`-th stage `Hom_A(I^n, M)` of the direct system, viewed as an additive group. -/
private abbrev idealPowerHomType (I : Ideal A) (M : ModuleCat A) (n : ℕ) :=
  ((I ^ n : Ideal A) →ₗ[A] M)

noncomputable abbrev idealPowerHomStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    AddCommGrpCat :=
  AddCommGrpCat.of (idealPowerHomType I M n)

/-- The transition map `Hom_A(I^n, M) → Hom_A(I^(n+1), M)` given by restriction along
`I^(n+1) ⊆ I^n`. -/
noncomputable def idealPowerHomTransition (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    idealPowerHomStage I M n ⟶ idealPowerHomStage I M (n + 1) :=
  AddCommGrpCat.ofHom <|
    (LinearMap.lcomp A M (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ))).toAddMonoidHom

/-- The sequential diagram `n ↦ Hom_A(I^n, M)`. -/
noncomputable def idealPowerHomDiagram (I : Ideal A) (M : ModuleCat A) :
    ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (idealPowerHomTransition I M)

/-- The chosen representative of a quotient class in a submodule quotient. -/
private noncomputable def quotientRepresentative
    {M : Type u} [AddCommGroup M] [Module A M] (N : Submodule A M) (x : M ⧸ N) : M :=
  Classical.choose (Submodule.mkQ_surjective N x)

/-- The chosen representative maps back to the original quotient class. -/
private theorem mkQ_quotientRepresentative
    {M : Type u} [AddCommGroup M] [Module A M] (N : Submodule A M) (x : M ⧸ N) :
    N.mkQ (quotientRepresentative N x) = x :=
  Classical.choose_spec (Submodule.mkQ_surjective N x)

/-- The submodule of elements of `M` annihilated by `I^n` in the source sense
`I^n x = 0`. -/
def idealPowerAnnihilatedSubmodule (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    Submodule A M where
  carrier := {x | ∀ a : A, a ∈ I ^ n → a • x = 0}
  zero_mem' a ha := by simp
  add_mem' hx hy a ha := by simp [hx a ha, hy a ha]
  smul_mem' r x hx a ha := by simp [smul_comm a r, hx a ha]

/-- The annihilated submodules are monotone in the exponent. -/
theorem idealPowerAnnihilatedSubmodule_mono
    (I : Ideal A) (M : ModuleCat A) {m n : ℕ} (h : m ≤ n) :
    idealPowerAnnihilatedSubmodule I M m ≤ idealPowerAnnihilatedSubmodule I M n := by
  intro x hx a ha
  exact hx a ((Ideal.pow_le_pow_right h) ha)

/-- The quotient stage `Hom_A(I^n, M / M_n)` where `M_n = {x | I^n x = 0}`,
viewed as an additive group. -/
private abbrev idealPowerQuotientHomType (I : Ideal A) (M : ModuleCat A) (n : ℕ) :=
  ((I ^ n : Ideal A) →ₗ[A] (M ⧸ idealPowerAnnihilatedSubmodule I M n))

noncomputable abbrev idealPowerQuotientHomStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    AddCommGrpCat :=
  AddCommGrpCat.of (idealPowerQuotientHomType I M n)

/-- The transition map `Hom_A(I^n, M / M_n) → Hom_A(I^(n+1), M / M_(n+1))`. -/
noncomputable def idealPowerQuotientHomTransition (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomStage I M n ⟶ idealPowerQuotientHomStage I M (n + 1) :=
  let inc :
      (I ^ (n + 1) : Ideal A) →ₗ[A] (I ^ n : Ideal A) :=
    Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)
  let q :
      (M ⧸ idealPowerAnnihilatedSubmodule I M n) →ₗ[A]
        (M ⧸ idealPowerAnnihilatedSubmodule I M (n + 1)) :=
    Submodule.mapQ
      (idealPowerAnnihilatedSubmodule I M n)
      (idealPowerAnnihilatedSubmodule I M (n + 1))
      LinearMap.id
      (idealPowerAnnihilatedSubmodule_mono I M n.le_succ)
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦ q ∘ₗ φ ∘ₗ inc
      map_zero' := by ext x; simp
      map_add' := by intro φ ψ; ext x; simp }

/-- The sequential diagram `n ↦ Hom_A(I^n, M / M_n)`. -/
noncomputable def idealPowerQuotientHomDiagram (I : Ideal A) (M : ModuleCat A) :
    ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (idealPowerQuotientHomTransition I M)

private def idealGeneratorBasicOpenSectionType
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (i : Fin (idealGeneratorCount I hI)) : Type u :=
  ((tildePresheaf M).obj (Opposite.op (idealGeneratorBasicOpen I hI i)) : Type u)

private noncomputable abbrev tildeBasicOpenIso (M : ModuleCat A) (f : A) :
    LocalizedModule.Away f M ≃ₗ[A]
      ((tildePresheaf M).obj (Opposite.op (PrimeSpectrum.basicOpen f)) : Type u) :=
  IsLocalizedModule.iso (.powers f) (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom

private noncomputable def tildeBasicOpenPowerSection
    (M : ModuleCat A) (f : A) (n : ℕ) (x : M) :
    ((tildePresheaf M).obj (Opposite.op (PrimeSpectrum.basicOpen f)) : Type u) :=
  tildeBasicOpenIso M f
    (IsLocalizedModule.mk'
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      x
      (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f))

private lemma sequentialAddCommGrpConstCoconeNaturality
    {C : AddCommGrpCat} {B : ℕ → AddCommGrpCat}
    (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ C)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) (n : ℕ) :
    (Functor.ofSequence u).map (homOfLE (Nat.le_succ n)) ≫ φ (n + 1) =
      φ n ≫ ((Functor.const ℕ).obj C).map (homOfLE (Nat.le_succ n)) := by
  simpa [Functor.ofSequence_map_homOfLE_succ] using hcompat n

private noncomputable def sequentialAddCommGrpColimitDesc
    {C : AddCommGrpCat} {B : ℕ → AddCommGrpCat}
    (u : ∀ n : ℕ, B n ⟶ B (n + 1))
    (φ : ∀ n : ℕ, B n ⟶ C)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) :
    colimit (Functor.ofSequence u) ⟶ C :=
  colimit.desc (Functor.ofSequence u)
    (Cocone.mk C
      (NatTrans.ofSequence φ
        (sequentialAddCommGrpConstCoconeNaturality (u := u) φ hcompat)))

private noncomputable def gluedSectionOfCompatibleFamily
    (M : ModuleCat A) {ι : Type _}
    (U : ι → (Spec (.of A)).Opens) (V : (Spec (.of A)).Opens)
    (iota : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U)
    (s : ∀ i, ((tildePresheaf M).obj (Opposite.op (U i)) : Type u))
    (hs : TopCat.Presheaf.IsCompatible (tildePresheaf M) U s) :
    ((tildePresheaf M).obj (Opposite.op V) : Type u) := by
  let F := tildeSheaf M
  exact Classical.choose <|
    ExistsUnique.exists <|
      F.existsUnique_gluing'
        U
        V
        (fun i ↦ homOfLE (iota i))
        hcover
        s
        hs

private theorem gluedSectionOfCompatibleFamily_spec
    (M : ModuleCat A) {ι : Type _}
    (U : ι → (Spec (.of A)).Opens) (V : (Spec (.of A)).Opens)
    (iota : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U)
    (s : ∀ i, ((tildePresheaf M).obj (Opposite.op (U i)) : Type u))
    (hs : TopCat.Presheaf.IsCompatible (tildePresheaf M) U s)
    (i : ι) :
    ((tildePresheaf M).map (homOfLE (iota i)).op)
        (gluedSectionOfCompatibleFamily M U V iota hcover s hs) =
      s i := by
  let F := tildeSheaf M
  exact (Classical.choose_spec <|
    ExistsUnique.exists <|
      F.existsUnique_gluing'
        U
        V
        (fun j ↦ homOfLE (iota j))
        hcover
        s
        hs) i

/-- The local section on the chosen basic open corresponding to `φ : I^n → M`. -/
noncomputable def idealPowerHomLocalSection
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerHomType I M n)
    (i : Fin (idealGeneratorCount I hI)) :
    idealGeneratorBasicOpenSectionType I hI M i :=
  let fi := idealGenerators I hI i
  tildeBasicOpenPowerSection M fi n
    (φ ⟨fi ^ n, Ideal.pow_mem_pow (idealGenerators_mem I hI i) n⟩)

/-- The chosen local sections `φ(f_i^n) / f_i^n` are compatible on pairwise intersections. -/
theorem idealPowerHomLocalSection_compatible
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerHomType I M n) :
    TopCat.Presheaf.IsCompatible
      (tildePresheaf M)
      (idealGeneratorBasicOpen I hI)
      (idealPowerHomLocalSection I hI M n φ) := sorry

/-- The stagewise section of `\widetilde M` on `Spec(A) \ V(I)` attached to
`φ : I^n → M`. -/
noncomputable def idealPowerHomSectionAtStage
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerHomType I M n) :
    idealComplementTildeSections I M :=
  gluedSectionOfCompatibleFamily
    M
    (idealGeneratorBasicOpen I hI)
    (idealComplementOpens I)
    (idealGeneratorBasicOpen_le_complement I hI)
    (idealComplementOpens_le_iSup_idealGeneratorBasicOpen I hI)
    (idealPowerHomLocalSection I hI M n φ)
    (idealPowerHomLocalSection_compatible I hI M n φ)

/-- The stagewise section restricts to the expected local fractions on the chosen cover. -/
theorem idealPowerHomSectionAtStage_spec
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerHomType I M n)
    (i : Fin (idealGeneratorCount I hI)) :
    ((tildePresheaf M).map
        (homOfLE (idealGeneratorBasicOpen_le_complement I hI i)).op)
        (idealPowerHomSectionAtStage I hI M n φ) =
      idealPowerHomLocalSection I hI M n φ i) := sorry

/-- The stagewise section construction is additive. -/
theorem idealPowerHomSectionAtStage_add
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ ψ : idealPowerHomType I M n) :
    idealPowerHomSectionAtStage I hI M n (φ + ψ) =
      idealPowerHomSectionAtStage I hI M n φ +
        idealPowerHomSectionAtStage I hI M n ψ := sorry

/-- The stagewise comparison map `Hom_A(I^n, M) → Γ(Spec(A) \ V(I), \widetilde M)`. -/
noncomputable def idealPowerHomToComplementSectionsStageMap
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ) :
    idealPowerHomStage I M n ⟶ idealComplementTildeSections I M :=
  AddCommGrpCat.ofHom
    { toFun := idealPowerHomSectionAtStage I hI M n
      map_zero' := by
        simpa using (idealPowerHomSectionAtStage_add I hI M n 0 0)
      map_add' := idealPowerHomSectionAtStage_add I hI M n }

/-- The stagewise comparison maps are compatible with the direct-system transition maps. -/
theorem idealPowerHomToComplementSectionsStageMap_naturality
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ) :
    idealPowerHomTransition I M n ≫
        idealPowerHomToComplementSectionsStageMap I hI M (n + 1) =
      idealPowerHomToComplementSectionsStageMap I hI M n := sorry

/-- The canonical comparison map
`colim_n Hom_A(I^n, M) → Γ(Spec(A) \ V(I), \widetilde M)`. -/
noncomputable def idealPowerHomColimitToComplementSections
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) :
    colimit (idealPowerHomDiagram I M) ⟶ idealComplementTildeSections I M :=
  sequentialAddCommGrpColimitDesc
    (fun n ↦ idealPowerHomTransition I M n)
    (idealPowerHomToComplementSectionsStageMap I hI M)
    (idealPowerHomToComplementSectionsStageMap_naturality I hI M)

/-- The local section on the chosen basic open corresponding to
`φ : I^n → M / M_n`, using the chosen quotient representative in `M`. -/
noncomputable def idealPowerQuotientHomLocalSection
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerQuotientHomType I M n)
    (i : Fin (idealGeneratorCount I hI)) :
    idealGeneratorBasicOpenSectionType I hI M i :=
  let fi := idealGenerators I hI i
  let x : M :=
    quotientRepresentative (idealPowerAnnihilatedSubmodule I M n)
      (φ ⟨fi ^ n, Ideal.pow_mem_pow (idealGenerators_mem I hI i) n⟩)
  tildeBasicOpenPowerSection M fi n x

/-- The chosen quotient local sections are compatible on pairwise intersections. -/
theorem idealPowerQuotientHomLocalSection_compatible
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerQuotientHomType I M n) :
    TopCat.Presheaf.IsCompatible
      (tildePresheaf M)
      (idealGeneratorBasicOpen I hI)
      (idealPowerQuotientHomLocalSection I hI M n φ) := sorry

/-- The stagewise section of `\widetilde M` on `Spec(A) \ V(I)` attached to
`φ : I^n → M / M_n`. -/
noncomputable def idealPowerQuotientHomSectionAtStage
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerQuotientHomType I M n) :
    idealComplementTildeSections I M :=
  gluedSectionOfCompatibleFamily
    M
    (idealGeneratorBasicOpen I hI)
    (idealComplementOpens I)
    (idealGeneratorBasicOpen_le_complement I hI)
    (idealComplementOpens_le_iSup_idealGeneratorBasicOpen I hI)
    (idealPowerQuotientHomLocalSection I hI M n φ)
    (idealPowerQuotientHomLocalSection_compatible I hI M n φ)

/-- The stagewise quotient section restricts to the expected local fractions on the chosen cover. -/
theorem idealPowerQuotientHomSectionAtStage_spec
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ : idealPowerQuotientHomType I M n)
    (i : Fin (idealGeneratorCount I hI)) :
    ((tildePresheaf M).map
        (homOfLE (idealGeneratorBasicOpen_le_complement I hI i)).op)
        (idealPowerQuotientHomSectionAtStage I hI M n φ) =
      idealPowerQuotientHomLocalSection I hI M n φ i) := sorry

/-- The quotient stagewise section construction is additive. -/
theorem idealPowerQuotientHomSectionAtStage_add
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ)
    (φ ψ : idealPowerQuotientHomType I M n) :
    idealPowerQuotientHomSectionAtStage I hI M n (φ + ψ) =
      idealPowerQuotientHomSectionAtStage I hI M n φ +
        idealPowerQuotientHomSectionAtStage I hI M n ψ := sorry

/-- The stagewise comparison map `Hom_A(I^n, M / M_n) → Γ(Spec(A) \ V(I), \widetilde M)`. -/
noncomputable def idealPowerQuotientHomToComplementSectionsStageMap
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomStage I M n ⟶ idealComplementTildeSections I M :=
  AddCommGrpCat.ofHom
    { toFun := idealPowerQuotientHomSectionAtStage I hI M n
      map_zero' := by
        simpa using (idealPowerQuotientHomSectionAtStage_add I hI M n 0 0)
      map_add' := idealPowerQuotientHomSectionAtStage_add I hI M n }

/-- The quotient stagewise comparison maps are compatible with the direct-system transition maps. -/
theorem idealPowerQuotientHomToComplementSectionsStageMap_naturality
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomTransition I M n ≫
        idealPowerQuotientHomToComplementSectionsStageMap I hI M (n + 1) =
      idealPowerQuotientHomToComplementSectionsStageMap I hI M n := sorry

/-- The canonical comparison map
`colim_n Hom_A(I^n, M / M_n) → Γ(Spec(A) \ V(I), \widetilde M)`. -/
noncomputable def idealPowerQuotientHomColimitToComplementSections
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) :
    colimit (idealPowerQuotientHomDiagram I M) ⟶ idealComplementTildeSections I M :=
  sequentialAddCommGrpColimitDesc
    (fun n ↦ idealPowerQuotientHomTransition I M n)
    (idealPowerQuotientHomToComplementSectionsStageMap I hI M)
    (idealPowerQuotientHomToComplementSectionsStageMap_naturality I hI M)


end AlgebraicGeometry.Scheme.Modules
