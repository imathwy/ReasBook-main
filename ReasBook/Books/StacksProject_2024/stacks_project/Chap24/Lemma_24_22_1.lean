import StacksProject_2024.Chap24.Definition_24_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasFiniteBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
variable {𝒜 : DGAO}
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

theorem dgModAdd_comm {M N : DGModA 𝒜}
    (f g : M ⟶ N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap + g.toCochainMap).f (n + m) =
      (((f.toCochainMap + g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_add, Preadditive.add_comp, f.comm n m, g.comm n m]

theorem dgModNeg_comm {M N : DGModA 𝒜}
    (f : M ⟶ N) (n m : ℤ) :
    M.smul n m ≫ (-f.toCochainMap).f (n + m) =
      (((-f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_neg, Preadditive.neg_comp] using congrArg (-·) (f.comm n m)

theorem dgModSub_comm {M N : DGModA 𝒜}
    (f g : M ⟶ N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap - g.toCochainMap).f (n + m) =
      (((f.toCochainMap - g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [sub_eq_add_neg] using dgModAdd_comm f (-g) n m

theorem dgModNSMul_comm {M N : DGModA 𝒜}
    (k : ℕ) (f : M ⟶ N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_nsmul, Preadditive.nsmul_comp, f.comm n m]

theorem dgModZSMul_comm {M N : DGModA 𝒜}
    (k : ℤ) (f : M ⟶ N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_zsmul, Preadditive.zsmul_comp, f.comm n m]

instance dgModAddHom (M N : DGModA 𝒜) :
    Add (DifferentialGradedModule.Hom M N) where
  add f g :=
    { toCochainMap := f.toCochainMap + g.toCochainMap
      comm := by
        intro n m
        exact SheafOfModules.RingedSite.dgModAdd_comm f g n m }

instance dgModNegHom (M N : DGModA 𝒜) :
    Neg (DifferentialGradedModule.Hom M N) where
  neg f :=
    { toCochainMap := -f.toCochainMap
      comm := by
        intro n m
        exact SheafOfModules.RingedSite.dgModNeg_comm f n m }

instance dgModSubHom (M N : DGModA 𝒜) :
    Sub (DifferentialGradedModule.Hom M N) where
  sub f g :=
    { toCochainMap := f.toCochainMap - g.toCochainMap
      comm := by
        intro n m
        exact SheafOfModules.RingedSite.dgModSub_comm f g n m }

instance dgModSMulNatHom (M N : DGModA 𝒜) :
    SMul ℕ (DifferentialGradedModule.Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := by
        intro n m
        exact SheafOfModules.RingedSite.dgModNSMul_comm k f n m }

instance dgModSMulIntHom (M N : DGModA 𝒜) :
    SMul ℤ (DifferentialGradedModule.Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := by
        intro n m
        exact SheafOfModules.RingedSite.dgModZSMul_comm k f n m }

instance dgModAddCommGroupHom (M N : DGModA 𝒜) :
    AddCommGroup (DifferentialGradedModule.Hom M N) :=
  Function.Injective.addCommGroup
    (fun f : DifferentialGradedModule.Hom M N ↦
      (f.toCochainMap : M.toComplex ⟶ N.toComplex))
    DifferentialGradedModule.toCochainMap_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

instance dgModArrowAdd (M N : DGModA 𝒜) : Add (M ⟶ N) :=
  dgModAddHom M N

instance dgModArrowNeg (M N : DGModA 𝒜) : Neg (M ⟶ N) :=
  dgModNegHom M N

instance dgModArrowSub (M N : DGModA 𝒜) : Sub (M ⟶ N) :=
  dgModSubHom M N

instance dgModArrowSMulNat (M N : DGModA 𝒜) : SMul ℕ (M ⟶ N) :=
  dgModSMulNatHom M N

instance dgModArrowSMulInt (M N : DGModA 𝒜) : SMul ℤ (M ⟶ N) :=
  dgModSMulIntHom M N

instance dgModArrowAddCommGroup (M N : DGModA 𝒜) : AddCommGroup (M ⟶ N) :=
  dgModAddCommGroupHom M N

instance dgModAPreadditive : Preadditive (Mod(𝒜, d)) where
  homGroup M N := dgModArrowAddCommGroup M N
  add_comp M N P f g h :=
    DifferentialGradedModule.toCochainMap_injective <|
      Preadditive.add_comp M.toComplex N.toComplex P.toComplex _ _ _
  comp_add M N P f g h :=
    DifferentialGradedModule.toCochainMap_injective <|
      Preadditive.comp_add M.toComplex N.toComplex P.toComplex _ _ _

instance dgModAHasZeroMorphisms : HasZeroMorphisms (Mod(𝒜, d)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- Tensoring sheaves of modules on the right by a fixed module is additive. -/
local instance tensorRightAdditive (M : ModO) : (tensorRight M).Additive :=
  tensorRight_additive M

/-- The degree-`n` term of the direct sum of two differential graded modules. -/
private abbrev directSumTerm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) : ModO :=
  ℳ.toComplex.X n ⊞ 𝒩.toComplex.X n

/-- The differential on the explicit degreewise direct sum complex. -/
private noncomputable abbrev directSumDiff
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) :
    directSumTerm ℳ 𝒩 n ⟶ directSumTerm ℳ 𝒩 (n + 1) :=
  biprod.map (ℳ.toComplex.d n (n + 1)) (𝒩.toComplex.d n (n + 1))

/-- The direct-sum differential squares to zero. -/
private theorem directSumDiff_sq
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ n : ℤ, directSumDiff ℳ 𝒩 n ≫ directSumDiff ℳ 𝒩 (n + 1) = 0 := sorry

/-- The explicit cochain complex underlying the direct sum of two differential graded modules. -/
private noncomputable abbrev directSumComplex
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) : CpxO :=
  CochainComplex.of (directSumTerm ℳ 𝒩) (directSumDiff ℳ 𝒩) (directSumDiff_sq ℳ 𝒩)

/-- The direct sum differential graded `\mathcal A`-module used for axiom `(A)`. Its underlying
cochain complex is the binary biproduct of the underlying cochain complexes, and the
`\mathcal A`-action is the degreewise direct sum of the given actions. -/
noncomputable def directSum
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) : Mod(𝒜, d) where
  toComplex := directSumComplex ℳ 𝒩
  smul n m :=
    ((tensorRight (𝒜.toComplex.X m)).mapBiprod (ℳ.toComplex.X n) (𝒩.toComplex.X n)).hom ≫
      biprod.map (ℳ.smul n m) (𝒩.smul n m)
  smul_assoc := by
    sorry
  one_smul := by
    sorry
  d_smul := by
    sorry

/-- The left coprojection commutes with the differentials of the explicit direct sum complex. -/
private theorem directSumInlToComplex_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (biprod.inl : ℳ.toComplex.X i ⟶ directSumTerm ℳ 𝒩 i) ≫
          (directSumComplex ℳ 𝒩).d i j =
        ℳ.toComplex.d i j ≫
          (biprod.inl : ℳ.toComplex.X j ⟶ directSumTerm ℳ 𝒩 j) := sorry

/-- The underlying cochain map of the left coprojection into the direct sum complex. -/
private noncomputable abbrev directSumInlToComplex
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ℳ.toComplex ⟶ directSumComplex ℳ 𝒩 :=
  HomologicalComplex.Hom.mk
    (fun _ ↦ biprod.inl)
    (directSumInlToComplex_comm ℳ 𝒩)

/-- The `\mathcal A`-linearity witness for the left coprojection
`\mathcal M \to \mathcal M \oplus \mathcal N`. -/
private theorem directSumInl_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ n m : ℤ,
      ℳ.smul n m ≫ (directSumInlToComplex ℳ 𝒩).f (n + m) =
        (((directSumInlToComplex ℳ 𝒩).f n) ▷ 𝒜.toComplex.X m) ≫
          (directSum ℳ 𝒩).smul n m := sorry

/-- The left coprojection `\mathcal M \to \mathcal M \oplus \mathcal N` is a morphism of
differential graded `\mathcal A`-modules. -/
noncomputable def directSumInl
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ℳ ⟶ directSum ℳ 𝒩 where
  toCochainMap := directSumInlToComplex ℳ 𝒩
  comm := directSumInl_comm ℳ 𝒩

/-- The right coprojection commutes with the differentials of the explicit direct sum complex. -/
private theorem directSumInrToComplex_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (biprod.inr : 𝒩.toComplex.X i ⟶ directSumTerm ℳ 𝒩 i) ≫
          (directSumComplex ℳ 𝒩).d i j =
        𝒩.toComplex.d i j ≫
          (biprod.inr : 𝒩.toComplex.X j ⟶ directSumTerm ℳ 𝒩 j) := sorry

/-- The underlying cochain map of the right coprojection into the direct sum complex. -/
private noncomputable abbrev directSumInrToComplex
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    𝒩.toComplex ⟶ directSumComplex ℳ 𝒩 :=
  HomologicalComplex.Hom.mk
    (fun _ ↦ biprod.inr)
    (directSumInrToComplex_comm ℳ 𝒩)

/-- The `\mathcal A`-linearity witness for the right coprojection
`\mathcal N \to \mathcal M \oplus \mathcal N`. -/
private theorem directSumInr_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ n m : ℤ,
      𝒩.smul n m ≫ (directSumInrToComplex ℳ 𝒩).f (n + m) =
        (((directSumInrToComplex ℳ 𝒩).f n) ▷ 𝒜.toComplex.X m) ≫
          (directSum ℳ 𝒩).smul n m := sorry

/-- The right coprojection `\mathcal N \to \mathcal M \oplus \mathcal N` is a morphism of
differential graded `\mathcal A`-modules. -/
noncomputable def directSumInr
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    𝒩 ⟶ directSum ℳ 𝒩 where
  toCochainMap := directSumInrToComplex ℳ 𝒩
  comm := directSumInr_comm ℳ 𝒩

/-- The left projection commutes with the differentials of the explicit direct sum complex. -/
private theorem directSumFstToComplex_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (biprod.fst : directSumTerm ℳ 𝒩 i ⟶ ℳ.toComplex.X i) ≫ ℳ.toComplex.d i j =
        (directSumComplex ℳ 𝒩).d i j ≫
          (biprod.fst : directSumTerm ℳ 𝒩 j ⟶ ℳ.toComplex.X j) := sorry

/-- The underlying cochain map of the left projection from the direct sum complex. -/
private noncomputable abbrev directSumFstToComplex
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumComplex ℳ 𝒩 ⟶ ℳ.toComplex :=
  HomologicalComplex.Hom.mk
    (fun _ ↦ biprod.fst)
    (directSumFstToComplex_comm ℳ 𝒩)

/-- The `\mathcal A`-linearity witness for the left projection
`\mathcal M \oplus \mathcal N \to \mathcal M`. -/
private theorem directSumFst_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ n m : ℤ,
      (directSum ℳ 𝒩).smul n m ≫ (directSumFstToComplex ℳ 𝒩).f (n + m) =
        (((directSumFstToComplex ℳ 𝒩).f n) ▷ 𝒜.toComplex.X m) ≫
          ℳ.smul n m := sorry

/-- The left projection `\mathcal M \oplus \mathcal N \to \mathcal M` is a morphism of
differential graded `\mathcal A`-modules. -/
noncomputable def directSumFst
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSum ℳ 𝒩 ⟶ ℳ where
  toCochainMap := directSumFstToComplex ℳ 𝒩
  comm := directSumFst_comm ℳ 𝒩

/-- The right projection commutes with the differentials of the explicit direct sum complex. -/
private theorem directSumSndToComplex_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (biprod.snd : directSumTerm ℳ 𝒩 i ⟶ 𝒩.toComplex.X i) ≫ 𝒩.toComplex.d i j =
        (directSumComplex ℳ 𝒩).d i j ≫
          (biprod.snd : directSumTerm ℳ 𝒩 j ⟶ 𝒩.toComplex.X j) := sorry

/-- The underlying cochain map of the right projection from the direct sum complex. -/
private noncomputable abbrev directSumSndToComplex
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumComplex ℳ 𝒩 ⟶ 𝒩.toComplex :=
  HomologicalComplex.Hom.mk
    (fun _ ↦ biprod.snd)
    (directSumSndToComplex_comm ℳ 𝒩)

/-- The `\mathcal A`-linearity witness for the right projection
`\mathcal M \oplus \mathcal N \to \mathcal N`. -/
private theorem directSumSnd_comm
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    ∀ n m : ℤ,
      (directSum ℳ 𝒩).smul n m ≫ (directSumSndToComplex ℳ 𝒩).f (n + m) =
        (((directSumSndToComplex ℳ 𝒩).f n) ▷ 𝒜.toComplex.X m) ≫
          𝒩.smul n m := sorry

/-- The right projection `\mathcal M \oplus \mathcal N \to \mathcal N` is a morphism of
differential graded `\mathcal A`-modules. -/
noncomputable def directSumSnd
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSum ℳ 𝒩 ⟶ 𝒩 where
  toCochainMap := directSumSndToComplex ℳ 𝒩
  comm := directSumSnd_comm ℳ 𝒩

/-- The degree-`n` component of the left coprojection into `directSum ℳ 𝒩` is the left biproduct
map. -/
@[simp] theorem directSumInl_f
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) :
    (directSumInl ℳ 𝒩).toCochainMap.f n = biprod.inl :=
  rfl

/-- The degree-`n` component of the right coprojection into `directSum ℳ 𝒩` is the right
biproduct map. -/
@[simp] theorem directSumInr_f
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) :
    (directSumInr ℳ 𝒩).toCochainMap.f n = biprod.inr :=
  rfl

/-- The degree-`n` component of the left projection from `directSum ℳ 𝒩` is the left biproduct
projection. -/
@[simp] theorem directSumFst_f
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) :
    (directSumFst ℳ 𝒩).toCochainMap.f n = biprod.fst :=
  rfl

/-- The degree-`n` component of the right projection from `directSum ℳ 𝒩` is the right biproduct
projection. -/
@[simp] theorem directSumSnd_f
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) (n : ℤ) :
    (directSumSnd ℳ 𝒩).toCochainMap.f n = biprod.snd :=
  rfl

/-- Lemma 24.22.1 (1), first identity for the direct-sum datum. -/
@[simp] theorem directSum_inl_fst
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumInl ℳ 𝒩 ≫ directSumFst ℳ 𝒩 = 𝟙 ℳ := sorry

/-- Lemma 24.22.1 (2), companion zero identity on the underlying cochain maps. -/
@[simp] theorem directSum_inl_snd
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumInl ℳ 𝒩 ≫ directSumSnd ℳ 𝒩 = (0 : ℳ ⟶ 𝒩) := sorry

/-- Lemma 24.22.1 (3), companion zero identity on the underlying cochain maps. -/
@[simp] theorem directSum_inr_fst
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumInr ℳ 𝒩 ≫ directSumFst ℳ 𝒩 = (0 : 𝒩 ⟶ ℳ) := sorry

/-- Lemma 24.22.1 (4), companion identity for the direct-sum datum. -/
@[simp] theorem directSum_inr_snd
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    directSumInr ℳ 𝒩 ≫ directSumSnd ℳ 𝒩 = 𝟙 𝒩 := sorry

/-- Lemma 24.22.1 (5), companion total identity for the direct-sum datum. -/
theorem directSum_total
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    (directSumFst ℳ 𝒩 ≫ directSumInl ℳ 𝒩) +
        (directSumSnd ℳ 𝒩 ≫ directSumInr ℳ 𝒩) =
      𝟙 (directSum ℳ 𝒩) := sorry

/-- Lemma 24.22.1 (1)–(5): for differential graded `\mathcal A`-modules `\mathcal M` and
`\mathcal N` on a ringed site, `directSum ℳ 𝒩` together with the morphisms `directSumInl`,
`directSumInr`, `directSumFst`, and `directSumSnd` is the source-faithful direct-sum datum from
axiom `(A)` of Differential Graded Algebra, Section 22.27. Since these structure maps are
morphisms of differential graded modules, they are the required closed homogeneous maps of degree
`0` in the sense of Definition 22.26.4. In the canonical category-theoretic API, this datum is a
binary bicone. -/
noncomputable def directSumBicone
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) : BinaryBicone ℳ 𝒩 where
  pt := directSum ℳ 𝒩
  fst := directSumFst ℳ 𝒩
  snd := directSumSnd ℳ 𝒩
  inl := directSumInl ℳ 𝒩
  inr := directSumInr ℳ 𝒩
  inl_fst := directSum_inl_fst ℳ 𝒩
  inl_snd := directSum_inl_snd ℳ 𝒩
  inr_fst := directSum_inr_fst ℳ 𝒩
  inr_snd := directSum_inr_snd ℳ 𝒩

/-- The direct-sum bicone of differential graded `\mathcal A`-modules is a bilimit. -/
noncomputable def directSumBicone_isBilimit
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) :
    (directSumBicone ℳ 𝒩).IsBilimit :=
  isBinaryBilimitOfTotal (directSumBicone ℳ 𝒩) (directSum_total ℳ 𝒩)

/-- The source-facing direct sum of differential graded `\mathcal A`-modules is a binary
biproduct. -/
noncomputable instance
    {𝒜 : DGAO} (ℳ 𝒩 : Mod(𝒜, d)) : HasBinaryBiproduct ℳ 𝒩 :=
  HasBinaryBiproduct.mk
    { bicone := directSumBicone ℳ 𝒩
      isBilimit := directSumBicone_isBilimit ℳ 𝒩 }

/- Lemma 24.22.1 (6): axiom `(B)` for `\textit{Mod}^{dg}(\mathcal A, \text{d})` is the canonical
integer-shift functor `shiftFunctor`. -/
#check shiftFunctor

/- Lemma 24.22.1 (7): on the source-facing category
`\textit{Mod}^{dg}(\mathcal A, \text{d}) = \mathrm{moduleCategory}(\mathcal A)`, the canonical
shift from Section 24.20 is the specialization `shiftFunctor (DifferentialGradedModule.moduleCategory 𝒜) n`. -/
#check fun (𝒜 : DGAO) [HasShift (DifferentialGradedModule.moduleCategory 𝒜) ℤ] (n : ℤ) ↦
  shiftFunctor (DifferentialGradedModule.moduleCategory 𝒜) n

end

end SheafOfModules.RingedSite
