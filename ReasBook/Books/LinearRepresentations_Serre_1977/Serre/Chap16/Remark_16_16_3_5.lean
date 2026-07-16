import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_2_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionPairing
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonCanonicalBaseChange
import LinearRepresentations_Serre_1977.Serre.Chap16.Remark_16_16_3_5.Core
import LinearRepresentations_Serre_1977.Serre.Chap16.Remark_16_16_3_5.ReductionBaseChange
import LinearRepresentations_Serre_1977.Serre.Chap16.Remark_16_16_3_5.ReverseDirection
import LinearRepresentations_Serre_1977.Serre.Chap16.Remark_16_16_3_5.SimpleClassBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.CharacterDescent
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.GrothendieckCharacter

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped Representation TensorProduct MonoidAlgebra ZeroObject

universe u
universe v

namespace Representation

section

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable (G : Type u) [Group G]

/-- Helper for Remark 16-16.3-5: additive homomorphisms out of `R₀[K](G)` are determined by
their values on finite-representation generator classes. -/
private theorem fdRepGrothendieckAddHom_ext {H : Type v} [AddCommGroup H]
    {K : Type u} [Field K] {G : Type u} [Group G]
    (f g : R₀[K](G) →+ H)
    (h : ∀ V : FDRep K G, f [V]₀ = g [V]₀) : f = g := by
  -- Descend the generator comparison through the free presentation of the Grothendieck group.
  refine AddMonoidHom.ext ?_
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (finiteRepGrothendieckRelations K G) x
  have hcomp :
      f.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) =
        g.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) := by
    apply FreeAbelianGroup.lift_ext
    intro V
    exact h V
  exact DFunLike.congr_fun hcomp y

/-- Helper for Remark 16-16.3-5: scalar extension of an actual finite-dimensional class is
again an actual finite-dimensional class. -/
private theorem finiteRepScalarExtensionClass_mem_finiteRepPositive
    {L L' : Type u} [Field L] [Field L'] [Algebra L L']
    {G : Type u} [Group G] (V : FDRep L G) :
    finiteRepGrothendieckScalarExtensionHom L L' G [V]₀ ∈ R⁺[L'](G) := by
  -- The scalar-extended finite representation itself represents the image class.
  refine (mem_finiteRepPositiveSubset_iff (K := L') (G := G)).2 ?_
  refine ⟨FDRep.scalarExtension V, ?_⟩
  exact (finiteRepGrothendieckScalarExtensionHom_class_eq L L' G V).symm

/-- Helper for Remark 16-16.3-5: the decomposition-image equality in condition `(R)` supplies a
positive generic witness for the residue-field scalar extension of any actual class. -/
private theorem conditionR_positivePreimage_of_residueScalarExtensionClass
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A']
    {K' : Type u} [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [Finite G]
    (hdecomp :
      decompositionHom A' K' G '' R⁺[K'](G) =
        R⁺[IsLocalRing.ResidueField A'](G))
    (V : FDRep (IsLocalRing.ResidueField A) G) :
    ∃ z : R₀[K'](G),
      z ∈ R⁺[K'](G) ∧
        decompositionHom A' K' G z =
          finiteRepGrothendieckScalarExtensionHom
            (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G [V]₀ := by
  -- First put the scalar-extended residue class in the actual positive cone over `k'`.
  have hpositive :
      finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G [V]₀ ∈
        R⁺[IsLocalRing.ResidueField A'](G) :=
    finiteRepScalarExtensionClass_mem_finiteRepPositive
      (G := G) (L := IsLocalRing.ResidueField A)
      (L' := IsLocalRing.ResidueField A') V
  -- Rewrite by the condition-`(R)` decomposition equality and unpack the image witness.
  have himage :
      finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G [V]₀ ∈
        decompositionHom A' K' G '' R⁺[K'](G) := by
    rw [hdecomp]
    exact hpositive
  rcases himage with ⟨z, hzpositive, hz⟩
  exact ⟨z, hzpositive, hz⟩

/-- Helper for Remark 16-16.3-5: the finite-representation Grothendieck group has no nonzero
natural torsion. -/
private theorem finiteRepGrothendieckClass_eq_zero_of_nsmul_eq_zero
    {L : Type u} [Field L] {G : Type u} [Group G]
    {N : ℕ} (hN : N ≠ 0) {x : R₀[L](G)} (hx : N • x = 0) : x = 0 := by
  classical
  -- Read the torsion equation in the integral coordinates of a complete simple-class basis.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := L) (H := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  apply b.repr.injective
  ext i
  have hcoeff := congrArg (fun y : R₀[L](G) ↦ b.repr y i) hx
  have hcoeff' : N • (b.repr x) i = 0 := by
    calc
      N • (b.repr x) i = (N • b.repr x) i := by
        simp
      _ = (b.repr (N • x)) i := by
        rw [map_nsmul]
      _ = 0 := by
        simpa using hcoeff
  simpa using (nsmul_eq_zero_iff_right hN).1 hcoeff'

/-- Helper for Remark 16-16.3-5: a left inverse up to multiplication by a nonzero natural
number makes scalar extension injective on `R₀`. -/
private theorem finiteRepScalarExtensionHom_injective_of_restrictionComposite
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {G : Type u} [Group G] (d : ℕ) (hd : d ≠ 0)
    (r : R₀[E](G) →+ R₀[F](G))
    (hr :
      ∀ x : R₀[F](G),
        r (finiteRepGrothendieckScalarExtensionHom F E G x) = d • x) :
    Function.Injective
      (finiteRepGrothendieckScalarExtensionHom F E G : R₀[F](G) →+ R₀[E](G)) := by
  -- Apply the restriction composite to an equality and cancel the resulting nonzero multiple.
  intro x y hxy
  have hdiff : d • (x - y) = 0 := by
    calc
      d • (x - y) = d • x - d • y := by
        rw [nsmul_sub]
      _ =
          r (finiteRepGrothendieckScalarExtensionHom F E G x) -
            r (finiteRepGrothendieckScalarExtensionHom F E G y) := by
          rw [hr x, hr y]
      _ = 0 := by
          rw [hxy, sub_self]
  have hzero : x - y = 0 :=
    finiteRepGrothendieckClass_eq_zero_of_nsmul_eq_zero (L := F) (G := G) hd hdiff
  exact sub_eq_zero.mp hzero

/-- Helper for Remark 16-16.3-5: a finite-dimensional representation over an extension field,
viewed by restriction of scalars, is a finite-dimensional representation over the base field. -/
private abbrev fdRepRestrictScalars
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] (V : FDRep E G) : FDRep F G :=
  letI : Module F V := Module.compHom V (algebraMap F E)
  letI : IsScalarTower F E V := inferInstance
  letI : Module.Finite F V := Module.Finite.trans E V
  FDRep.of (Representation.restrictScalars F V.ρ)

/-- Helper for Remark 16-16.3-5: the underlying `E`-linear morphism of finite-dimensional
representations, viewed as an `F`-linear map after restriction of scalars. -/
private abbrev fdRepRestrictScalars_linearMap
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] {V W : FDRep E G} (f : V ⟶ W) : V →ₗ[F] W :=
  letI : Module F V := Module.compHom V (algebraMap F E)
  letI : Module F W := Module.compHom W (algebraMap F E)
  let lE : V →ₗ[E] W := ((forget₂ (FDRep E G) (Rep E G)).map f).hom.toLinearMap
  { toFun := fun x ↦ lE x
    map_add' := fun x y ↦ lE.map_add x y
    map_smul' := fun a x ↦ by
      change lE ((algebraMap F E a) • x) = (algebraMap F E a) • lE x
      exact lE.map_smul (algebraMap F E a) x }

/-- Helper for Remark 16-16.3-5: restriction of scalars sends morphisms of finite-dimensional
representations to morphisms of the restricted finite-dimensional representations. -/
private abbrev fdRepRestrictScalars_map
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] {V W : FDRep E G} (f : V ⟶ W) :
    fdRepRestrictScalars (F := F) (E := E) (G := G) V ⟶
      fdRepRestrictScalars (F := F) (E := E) (G := G) W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.ofHom
      ⟨fdRepRestrictScalars_linearMap (F := F) (E := E) (G := G) f,
        by
          intro g
          ext x
          simpa [fdRepRestrictScalars, fdRepRestrictScalars_linearMap,
            Representation.restrictScalars_apply] using
            Rep.hom_comm_apply ((forget₂ (FDRep E G) (Rep E G)).map f) g x⟩)

/-- Helper for Remark 16-16.3-5: after forgetting to `Rep`, the restricted morphism is the
original intertwining map with scalars restricted. -/
private theorem fdRepRestrictScalars_map_forget
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] {V W : FDRep E G} (f : V ⟶ W) :
    (forget₂ (FDRep F G) (Rep F G)).map
        (fdRepRestrictScalars_map (F := F) (E := E) (G := G) f) =
      Rep.ofHom
        ⟨fdRepRestrictScalars_linearMap (F := F) (E := E) (G := G) f,
          by
            intro g
            ext x
            simpa [fdRepRestrictScalars, fdRepRestrictScalars_linearMap,
              Representation.restrictScalars_apply] using
              Rep.hom_comm_apply ((forget₂ (FDRep E G) (Rep E G)).map f) g x⟩ := by
  -- Unpack the `FDRep` fullness equivalence used to define the restricted morphism.
  change (FDRep.forget₂HomLinearEquiv
      (fdRepRestrictScalars (F := F) (E := E) (G := G) V)
      (fdRepRestrictScalars (F := F) (E := E) (G := G) W)).symm
    ((FDRep.forget₂HomLinearEquiv
      (fdRepRestrictScalars (F := F) (E := E) (G := G) V)
      (fdRepRestrictScalars (F := F) (E := E) (G := G) W))
      (Rep.ofHom
        ⟨fdRepRestrictScalars_linearMap (F := F) (E := E) (G := G) f,
          by
            intro g
            ext x
            simpa [fdRepRestrictScalars, fdRepRestrictScalars_linearMap,
              Representation.restrictScalars_apply] using
              Rep.hom_comm_apply ((forget₂ (FDRep E G) (Rep E G)).map f) g x⟩)) = _
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Remark 16-16.3-5: termwise restriction of a short complex is still a short
complex. -/
private theorem fdRepRestrictScalars_shortComplex_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] (S : ShortComplex (FDRep E G)) :
    fdRepRestrictScalars_map (F := F) (E := E) (G := G) S.f ≫
        fdRepRestrictScalars_map (F := F) (E := E) (G := G) S.g = 0 := by
  -- The composite is zero because the underlying `E`-linear composite was already zero.
  apply (forget₂ (FDRep F G) (Rep F G)).map_injective
  rw [Functor.map_comp]
  rw [fdRepRestrictScalars_map_forget (F := F) (E := E) (G := G) S.f]
  rw [fdRepRestrictScalars_map_forget (F := F) (E := E) (G := G) S.g]
  ext x
  let FE : FDRep E G ⥤ Rep E G := forget₂ (FDRep E G) (Rep E G)
  have hzeroRepHom : FE.map S.f ≫ FE.map S.g = 0 := by
    rw [← FE.map_comp, S.zero, FE.map_zero]
  have hzeroRep :
      (FE.map S.g).hom.toLinearMap ∘ₗ (FE.map S.f).hom.toLinearMap = 0 := by
    simpa using congrArg (fun m ↦ m.hom.toLinearMap) hzeroRepHom
  -- Evaluate the inherited zero composite on the same underlying vector, after the morphism
  -- normal form exposes the restricted linear maps.
  simpa [fdRepRestrictScalars, fdRepRestrictScalars_linearMap] using
    LinearMap.congr_fun hzeroRep x

/-- Helper for Remark 16-16.3-5: the short complex obtained by restricting each term and map of
a finite-representation short complex. -/
private abbrev fdRepRestrictScalars_shortComplex
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] (S : ShortComplex (FDRep E G)) : ShortComplex (FDRep F G) :=
  ShortComplex.mk
    (fdRepRestrictScalars_map (F := F) (E := E) (G := G) S.f)
    (fdRepRestrictScalars_map (F := F) (E := E) (G := G) S.g)
    (fdRepRestrictScalars_shortComplex_zero (F := F) (E := E) (G := G) S)

/-- Helper for Remark 16-16.3-5: restriction of scalars preserves short exact sequences of
finite-dimensional representations. -/
private theorem fdRepRestrictScalars_shortExact
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] (S : ShortComplex (FDRep E G)) (hS : S.ShortExact) :
    (fdRepRestrictScalars_shortComplex (F := F) (E := E) (G := G) S).ShortExact := by
  -- Exactness, injectivity, and surjectivity are the same statements for the underlying maps.
  let FE : FDRep E G ⥤ ModuleCat E :=
    (forget₂ (FDRep E G) (Rep E G)) ⋙ (forget₂ (Rep E G) (ModuleCat E))
  have hSFE : (S.map FE).ShortExact := by
    simpa [FE] using hS.map_of_exact FE
  let fE : S.X₁.V →ₗ[E] S.X₂.V :=
    ((forget₂ (FDRep E G) (Rep E G)).map S.f).hom.toLinearMap
  let gE : S.X₂.V →ₗ[E] S.X₃.V :=
    ((forget₂ (FDRep E G) (Rep E G)).map S.g).hom.toLinearMap
  have hExactE : Function.Exact fE gE := by
    simpa [FE, fE, gE] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map FE)).mp hSFE.exact
  have hInjE : Function.Injective fE := by
    simpa [FE, fE] using hSFE.moduleCat_injective_f
  have hSurjE : Function.Surjective gE := by
    simpa [FE, gE] using hSFE.moduleCat_surjective_g
  have hExactF : Function.Exact (fE.restrictScalars F) (gE.restrictScalars F) := by
    intro x
    exact hExactE x
  have hInjF : Function.Injective (fE.restrictScalars F) := hInjE
  have hSurjF : Function.Surjective (gE.restrictScalars F) := hSurjE
  let SFRep : ShortComplex (Rep F G) :=
    (fdRepRestrictScalars_shortComplex (F := F) (E := E) (G := G) S).map
      (forget₂ (FDRep F G) (Rep F G))
  have hRepMap : (SFRep.map (forget₂ (Rep F G) (ModuleCat F))).ShortExact := by
    -- Rebuild the short-exact proof over `F` from the inherited function-level facts.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (SFRep.map (forget₂ (Rep F G) (ModuleCat F)))).2 <|
          by
            simpa [SFRep, fdRepRestrictScalars_shortComplex,
              fdRepRestrictScalars_map_forget, fE, gE] using hExactF
    · rw [ModuleCat.mono_iff_injective]
      simpa [SFRep, fdRepRestrictScalars_shortComplex,
        fdRepRestrictScalars_map_forget, fE] using hInjF
    · rw [ModuleCat.epi_iff_surjective]
      simpa [SFRep, fdRepRestrictScalars_shortComplex,
        fdRepRestrictScalars_map_forget, gE] using hSurjF
  have hRepShort : SFRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SFRep) (F := forget₂ (Rep F G) (ModuleCat F))).1 hRepMap
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := fdRepRestrictScalars_shortComplex (F := F) (E := E) (G := G) S)
      (F := forget₂ (FDRep F G) (Rep F G))).1 hRepShort

/-- Helper for Remark 16-16.3-5: the free abelian-group lift sending an `E`-representation to
its restriction-of-scalars class over `F`. -/
private abbrev finiteRepGrothendieckRestrictScalarsLift
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] :
    FreeAbelianGroup (FDRep E G) →+ R₀[F](G) :=
  FreeAbelianGroup.lift fun V ↦ [fdRepRestrictScalars (F := F) (E := E) (G := G) V]₀

/-- Helper for Remark 16-16.3-5: restriction of scalars kills the defining short-exact
relations of the finite-representation Grothendieck group. -/
private theorem finiteRepGrothendieckRelations_le_restrictScalarsLift_ker
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] :
    finiteRepGrothendieckRelations E G ≤
      (finiteRepGrothendieckRestrictScalarsLift (F := F) (E := E) (G := G)).ker := by
  -- Each defining relation maps to the corresponding restricted short-exact relation.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₂]₀ -
      [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₁]₀ -
      [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₃]₀ = 0
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := F) (G := G)
      (fdRepRestrictScalars_shortComplex (F := F) (E := E) (G := G) S)
      (fdRepRestrictScalars_shortExact (F := F) (E := E) (G := G) S hS)
  have hrelation' :
      [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₂]₀ =
        ([fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₁]₀ : R₀[F](G)) +
          [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₃]₀ := by
    simpa [fdRepRestrictScalars_shortComplex] using hrelation
  calc
    [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₂]₀ -
        [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₁]₀ -
        [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₃]₀ =
      ([fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₁]₀ +
          [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₃]₀) -
        [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₁]₀ -
        [fdRepRestrictScalars (F := F) (E := E) (G := G) S.X₃]₀ := by
          rw [hrelation']
    _ = 0 := by
          abel

/-- Helper for Remark 16-16.3-5: on generator classes, restriction after scalar extension is
multiplication by the field degree. -/
private theorem restrictScalars_scalarExtension_class_eq_finrank_nsmul
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] (V : FDRep F G) :
    finiteRepGrothendieckRestrictScalarsHom F E G
        (finiteRepGrothendieckScalarExtensionHom F E G [V]₀) =
      Module.finrank F E • ([V]₀ : R₀[F](G)) := by
  -- Use the canonical Chapter 15 restriction-after-scalar-extension computation.
  simpa using
    finiteRepGrothendieckRestrictScalarsHom_scalarExtension_class_eq_finrank_nsmul
      (K := F) (K' := E) (G := G) V

/-- Helper for Remark 16-16.3-5: restricting scalars after finite scalar extension multiplies
classes in `R₀` by the field degree. -/
private theorem finiteRepRestrictionCompositeEqFinrankNsmul
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] [Finite G] :
    ∃ r : R₀[E](G) →+ R₀[F](G),
      ∀ x : R₀[F](G),
        r (finiteRepGrothendieckScalarExtensionHom F E G x) = Module.finrank F E • x := by
  -- Use the descended restriction-of-scalars homomorphism and compare the composite on
  -- generator classes, which determine additive homomorphisms out of `R₀[F](G)`.
  let r : R₀[E](G) →+ R₀[F](G) := finiteRepGrothendieckRestrictScalarsHom F E G
  refine ⟨r, ?_⟩
  have hcomp :
      r.comp (finiteRepGrothendieckScalarExtensionHom F E G) =
        Module.finrank F E • AddMonoidHom.id (R₀[F](G)) := by
    apply fdRepGrothendieckAddHom_ext
    intro V
    -- The composite has already been reduced to the generator compatibility lemma.
    simpa [r, AddMonoidHom.comp_apply] using
      restrictScalars_scalarExtension_class_eq_finrank_nsmul (F := F) (E := E) (G := G) V
  intro x
  have hx := congrArg (fun f : R₀[F](G) →+ R₀[F](G) ↦ f x) hcomp
  simpa [r, AddMonoidHom.comp_apply] using hx

/-- Helper for Remark 16-16.3-5: finite scalar extension is injective on finite-representation
Grothendieck groups. -/
private theorem finiteRepScalarExtensionHom_injectiveOfFiniteDimensional
    {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {G : Type u} [Group G] [Finite G] :
    Function.Injective
      (finiteRepGrothendieckScalarExtensionHom F E G : R₀[F](G) →+ R₀[E](G)) := by
  -- The cancellation step is formal; it remains to construct restriction of scalars on `R₀`
  -- and prove that restricting after scalar extension is multiplication by `[E : F]`.
  let d : ℕ := Module.finrank F E
  have hd : d ≠ 0 := by
    -- A finite-dimensional field extension has positive `F`-dimension.
    dsimp [d]
    exact Module.finrank_pos.ne'
  -- Restriction of scalars gives a left inverse up to the nonzero degree `[E : F]`.
  rcases finiteRepRestrictionCompositeEqFinrankNsmul
      (F := F) (E := E) (G := G) with
    ⟨r, hr⟩
  exact
    finiteRepScalarExtensionHom_injective_of_restrictionComposite
      (F := F) (E := E) (G := G) d hd r hr

/-- Helper for Remark 16-16.3-5: adjoining a Laurent-series uniformizer preserves the chosen
primitive roots of unity. -/
private theorem hasEnoughRootsOfUnity_laurentSeries_forRemark
    [Finite G] [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := by
  classical
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent G)
  have hprim : (primitiveRoots (Monoid.exponent G) K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos (Monoid.exponent G))]
    exact hζ
  exact
    MulEquiv.hasEnoughRootsOfUnity
      (rootsOfUnityEquivOfPrimitiveRoots
        (S := LaurentSeries K)
        (f := algebraMap K (LaurentSeries K))
        (algebraMap K (LaurentSeries K)).injective
        hprim)

/-- Helper for Remark 16-16.3-5: replacing a field by an isomorphic coefficient field does not
change finite dimension. -/
private theorem finrank_compHom_ringEquiv_forRemark
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    (M : Type u) [AddCommGroup M] [Module K' M] [FiniteDimensional K' M] :
    @Module.finrank F M _ _ (Module.compHom M e.toRingHom) = Module.finrank K' M := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K' M) K' M :=
    Module.Free.chooseBasis K' M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K' M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  rw [Module.finrank_eq_card_basis bF, Module.finrank_eq_card_basis bK]

/-- Helper for Remark 16-16.3-5: transport a representation to an isomorphic coefficient field,
keeping the same underlying additive group and group action. -/
private noncomputable def repOverRingEquiv_forRemark
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation F G S := by
  letI : Module F S := Module.compHom S e.toRingHom
  exact
    { toFun := fun g ↦
        { toFun := fun x ↦ S.ρ g x
          map_add' := by intro x y; exact (S.ρ g).map_add x y
          map_smul' := by
            intro a x
            change S.ρ g (e a • x) = e a • S.ρ g x
            exact (S.ρ g).map_smul (e a) x }
      map_one' := by
        ext x
        change S.ρ 1 x = x
        simp
      map_mul' := by
        intro g h
        ext x
        change S.ρ (g * h) x = S.ρ g (S.ρ h x)
        simp }

/-- Helper for Remark 16-16.3-5: simplicity is preserved by transport across an isomorphic
coefficient field. -/
private theorem transported_irreducible_of_ringEquiv_forRemark
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) [Simple S] :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation.IsIrreducible (repOverRingEquiv_forRemark e S) := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  change Representation.IsIrreducible (repOverRingEquiv_forRemark e S)
  have hSK : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hS_nontriv : Nontrivial S := by
    by_contra h
    letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp h
    have hzero : (𝟙 S : S ⟶ S) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero S hzero
  let ρF : Representation F G S := repOverRingEquiv_forRemark e S
  have hbot_ne_top : (⊥ : Subrepresentation ρF) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    have hsub := congrArg Subrepresentation.toSubmodule h
    have hxbot : x ∈ (⊥ : Submodule F S) := by
      change x ∈ (⊥ : Subrepresentation ρF).toSubmodule
      rw [hsub]
      exact Submodule.mem_top
    exact hx (by simpa using hxbot)
  letI : Nontrivial (Subrepresentation ρF) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro N
  let NK : Subrepresentation S.ρ :=
    { toSubmodule :=
        { carrier := N.toSubmodule
          zero_mem' := N.toSubmodule.zero_mem'
          add_mem' := N.toSubmodule.add_mem'
          smul_mem' := by
            intro c x hx
            have hx' : (e.symm c) • x ∈ N.toSubmodule :=
              N.toSubmodule.smul_mem (e.symm c) hx
            convert hx' using 1
            change c • x = e (e.symm c) • x
            simp }
      apply_mem_toSubmodule := by
        intro g x hx
        exact N.apply_mem_toSubmodule g hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top NK with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊥ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊥ : Subrepresentation S.ρ).toSubmodule := by
      rw [hbot]
    exact hmem
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊤ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊤ : Subrepresentation S.ρ).toSubmodule := by
      rw [htop]
    exact hmem

/-- Helper for Remark 16-16.3-5: transport self-intertwining maps across an isomorphic
coefficient field. -/
private noncomputable def intertwiningMap_ringEquiv_linearEquiv_forRemark
    {F K' : Type u} [Field F] [Field K'] (e : F ≃+* K')
    {G : Type u} [Group G] (S : FDRep K' G) :
    letI : Module F S := Module.compHom S e.toRingHom
    let ρF : Representation F G S := repOverRingEquiv_forRemark e S
    letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
      Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
    Representation.IntertwiningMap ρF ρF ≃ₗ[F]
      Representation.IntertwiningMap S.ρ S.ρ := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv_forRemark e S
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  exact
    { toFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by intro x y; exact f.map_add x y
              map_smul' := by
                intro c x
                have h := f.toLinearMap.map_smul (e.symm c) x
                change f (e (e.symm c) • x) = e (e.symm c) • f x at h
                simpa using h }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv_forRemark] using
              (Representation.IntertwiningMap.isIntertwining
                (repOverRingEquiv_forRemark e S) (repOverRingEquiv_forRemark e S) f g x) }
      invFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by intro x y; exact f.map_add x y
              map_smul' := by
                intro a x
                change f (e a • x) = e a • f x
                exact f.map_smul (e a) x }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv_forRemark] using
              (Representation.IntertwiningMap.isIntertwining S.ρ S.ρ f g x) }
      left_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      right_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      map_add' := by
        intro f g
        apply Representation.IntertwiningMap.ext
        rfl
      map_smul' := by
        intro a f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl }

/-- Helper for Remark 16-16.3-5: sufficiently large generic fields make simple
finite-dimensional representations absolutely irreducible in Schur's sense. -/
private theorem genericSimple_selfIntertwining_finrank_eq_one_forRemark
    [Finite G] [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep K G) [Simple S] :
    Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  classical
  let F := IsLocalRing.ResidueField (PowerSeries K)
  let e : F ≃+* K := PowerSeries.residueFieldOfPowerSeries
  -- The residue field of `K⟦X⟧` is `K`, characteristic zero here, hence perfect (DVR theorem need).
  haveI : CharZero (IsLocalRing.ResidueField (PowerSeries K)) :=
    (RingHom.charZero_iff e.toRingHom.injective).2 inferInstance
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv_forRemark e S
  haveI : FiniteDimensional F S := by
    let bK : Module.Basis (Module.Free.ChooseBasisIndex K S) K S :=
      Module.Free.chooseBasis K S
    let bF : Module.Basis (Module.Free.ChooseBasisIndex K S) F S :=
      bK.mapCoeffs e.symm (by
        intro c x
        change e (e.symm c) • x = c • x
        simp)
    exact bF.finiteDimensional_of_finite
  let SF : FDRep F G := FDRep.of ρF
  haveI : Representation.IsIrreducible SF.ρ := by
    simpa [SF, ρF] using transported_irreducible_of_ringEquiv_forRemark e S
  haveI : Simple SF := FDRep.simple_of_isIrreducible SF
  have hroots : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_laurentSeries_forRemark (K := K) (G := G)
  have hHom : Module.finrank F (SF ⟶ SF) = 1 := by
    letI : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := hroots
    exact
      simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
        (A := PowerSeries K) (K := LaurentSeries K) (G := G) SF
  let eHom : (SF ⟶ SF) ≃ₗ[F] Representation.IntertwiningMap ρF ρF :=
    ((FDRep.forget₂HomLinearEquiv SF SF).symm).trans
      (Rep.homLinearEquiv
        ((forget₂ (FDRep F G) (Rep F G)).obj SF)
        ((forget₂ (FDRep F G) (Rep F G)).obj SF))
  have hIF : Module.finrank F (Representation.IntertwiningMap ρF ρF) = 1 := by
    simpa [hHom] using (LinearEquiv.finrank_eq eHom).symm
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  have hIKF : Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
    let E := intertwiningMap_ringEquiv_linearEquiv_forRemark e S
    simpa [hIF, ρF] using (LinearEquiv.finrank_eq E).symm
  have hfinrank_eq :
      Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) =
        Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) := by
    exact finrank_compHom_ringEquiv_forRemark e (Representation.IntertwiningMap S.ρ S.ρ)
  rw [← hfinrank_eq]
  exact hIKF

/-- Helper for Remark 16-16.3-5: if a simple representation has one-dimensional
self-intertwining space, every Schur denominator for it is trivial. -/
private theorem schurDenominator_eq_one_of_selfIntertwining_finrank_eq_one_forRemark
    [CharZero K] [Finite G]
    (V : FDRep K G) [Simple V]
    (hEnd : Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) = 1)
    {m : ℕ+} (hm : FDRep.IsSchurDenominator V m) :
    m = 1 := by
  classical
  let χscaled : R[AlgebraicClosure K](G) :=
    ⟨((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
        (FDRep.schurScaledCharacter V m),
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K)
        (FDRep.schurScaledCharacter V m)).1 hm.1⟩
  obtain ⟨ι, _, ψ, d, hd_pos, hψ_fd, hψ_pairwise, hψ_irr, hpacket⟩ :=
    scalar_extension_character_eq_sum_irreducible_family_with_nat_coefficients
      (K := K) (G := G) V
  letI : Fintype ι := inferInstance
  have hsource_pair :
      ⟪V.character, V.character⟫ = (1 : K) := by
    simpa [hEnd] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        (K := K) (G := G) V.ρ V.ρ)
  have hpacket_sum :
      ∑ i, d i * d i = 1 := by
    have hcardK : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcardK
    have hcardC : (Nat.card G : AlgebraicClosure K) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcardC
    let χ : G → AlgebraicClosure K :=
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character
    have hmap_pair :
        ⟪χ, χ⟫ = (1 : AlgebraicClosure K) := by
      calc
        ⟪χ, χ⟫ = algebraMap K (AlgebraicClosure K) ⟪V.character, V.character⟫ := by
            exact groupFunctionPairing_compLeft_toAlgClosure (K := K) (G := G)
              V.character V.character
        _ = 1 := by simp [hsource_pair]
    have hcoeff :
        ∀ j, ⟪χ, (ψ j).ρ.character⟫ = (d j : AlgebraicClosure K) := by
      exact
        packet_constituent_pairing_eq_multiplicity
          (K := K) (G := G) V ψ d hψ_fd hψ_pairwise hψ_irr hpacket
    have hpair_sum :
        ⟪χ, χ⟫ = ∑ i, (d i : AlgebraicClosure K) * (d i : AlgebraicClosure K) := by
      calc
        ⟪χ, χ⟫ =
            ⟪∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character, χ⟫ := by
              change
                ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
                    V.character, χ⟫ =
                  ⟪∑ i, (d i : AlgebraicClosure K) • (ψ i).ρ.character, χ⟫
              rw [← scalarExtension_character_eq_map_fdRep_character (K := K) (G := G) V]
              rw [hpacket]
        _ = ∑ i, (d i : AlgebraicClosure K) *
              ⟪(ψ i).ρ.character, χ⟫ := by
            simpa using
              groupFunctionPairing_sum_field_smul_left
                (K := K) (G := G) (s := Finset.univ)
                (a := fun i ↦ (d i : AlgebraicClosure K))
                (χ := fun i ↦ (ψ i).ρ.character) χ
        _ = ∑ i, (d i : AlgebraicClosure K) * (d i : AlgebraicClosure K) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Representation.groupFunctionPairing_comm]
            rw [hcoeff i]
    have hcast :
        ((∑ i, d i * d i : ℕ) : AlgebraicClosure K) = 1 := by
      calc
        ((∑ i, d i * d i : ℕ) : AlgebraicClosure K) =
            ∑ i, (d i : AlgebraicClosure K) * (d i : AlgebraicClosure K) := by
              simp
        _ = ⟪χ, χ⟫ := hpair_sum.symm
        _ = 1 := hmap_pair
    exact Nat.cast_injective (by simpa only [Nat.cast_one] using hcast)
  have hone_coeff : ∃ i, d i = 1 := by
    by_contra h
    push Not at h
    have htwo : ∀ i, 2 ≤ d i * d i := by
      intro i
      have hdi_one_le : 1 ≤ d i := Nat.succ_le_of_lt (hd_pos i)
      have hdi_two : 2 ≤ d i :=
        Nat.succ_le_of_lt (lt_of_le_of_ne hdi_one_le (Ne.symm (h i)))
      have hsq_ge : d i * d i ≥ d i * 1 :=
        Nat.mul_le_mul_left (d i) (by exact Nat.succ_le_of_lt (hd_pos i))
      exact hdi_two.trans (by simpa using hsq_ge)
    have hsum_ge_two : 2 ≤ ∑ i, d i * d i := by
      have hsum_ne_zero : (∑ i, d i * d i) ≠ 0 := by
        rw [hpacket_sum]
        norm_num
      obtain ⟨i0, hi0_mem, _hi0_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero
      exact
        (htwo i0).trans
          (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun i ↦ d i * d i)
          (fun i _ ↦ Nat.zero_le _)
          hi0_mem)
    omega
  rcases hone_coeff with ⟨i0, hi0⟩
  have hpair_i0 :
      ⟪(χscaled : G → AlgebraicClosure K), (ψ i0).ρ.character⟫ =
        ((m : ℕ) : AlgebraicClosure K)⁻¹ := by
    have hχscaled_eq :
        (χscaled : G → AlgebraicClosure K) =
          ((m : ℕ) : AlgebraicClosure K)⁻¹ •
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character := by
      ext g
      simp [χscaled, FDRep.schurScaledCharacter, smul_eq_mul, map_mul]
    have hraw :
        ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
          (ψ i0).ρ.character⟫ = (1 : AlgebraicClosure K) := by
      simpa [hi0] using
        packet_constituent_pairing_eq_multiplicity
          (K := K) (G := G) V ψ d hψ_fd hψ_pairwise hψ_irr hpacket i0
    calc
      ⟪(χscaled : G → AlgebraicClosure K), (ψ i0).ρ.character⟫ =
          ⟪(((m : ℕ) : AlgebraicClosure K)⁻¹) •
              ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
            (ψ i0).ρ.character⟫ := by
            rw [hχscaled_eq]
      _ = ((m : ℕ) : AlgebraicClosure K)⁻¹ *
          ⟪((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) V.character,
            (ψ i0).ρ.character⟫ := by
            rw [Representation.groupFunctionPairing_smul_left]
      _ = ((m : ℕ) : AlgebraicClosure K)⁻¹ := by simp [hraw]
  obtain ⟨z, hz⟩ :=
    pairing_eq_int_of_mem_characterRingOverAlgClosure_local
      (K' := K) (G := G) χscaled (ψ i0).ρ
  have hm_ne : ((m : ℕ) : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmul : ((m : ℕ) : AlgebraicClosure K) * (z : AlgebraicClosure K) = 1 := by
    calc
      ((m : ℕ) : AlgebraicClosure K) * (z : AlgebraicClosure K) =
          ((m : ℕ) : AlgebraicClosure K) *
            ⟪(χscaled : G → AlgebraicClosure K), (ψ i0).ρ.character⟫ := by
            rw [hz]
      _ = ((m : ℕ) : AlgebraicClosure K) *
            ((m : ℕ) : AlgebraicClosure K)⁻¹ := by rw [hpair_i0]
      _ = 1 := by field_simp [hm_ne]
  have hmulZ : ((m : ℤ) * z : ℤ) = 1 := by
    exact_mod_cast hmul
  have hm_dvd_one_int : ((m : ℤ) : ℤ) ∣ (1 : ℤ) := ⟨z, hmulZ.symm⟩
  have hm_dvd_one_nat : (m : ℕ) ∣ 1 :=
    Int.natCast_dvd_natCast.mp (by simpa using hm_dvd_one_int)
  exact Subtype.ext (Nat.dvd_one.mp hm_dvd_one_nat)

/-- Helper for Remark 16-16.3-5: over a sufficiently large base field of characteristic zero, the
group algebra `K[G]` is quasisplit, i.e. `R[K](G) = R̄[K](G)`. This is Serre Theorem 24 over an
arbitrary characteristic-`0` field, now proven non-circularly via the field-independence project
(`characterRing_eq_overlineCharacterRing_of_isSplittingField`, Chapter 14). Previously this went
through the `d_E = 1` self-intertwiner computation, which depended on the still-open modular case
of the splitting-field theorem; the direct delegation removes that circular dependency. -/
private theorem quasisplitOfHasEnoughRoots
    [CharZero K] [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    R[K](G) = R̄[K](G) :=
  characterRing_eq_overlineCharacterRing_of_isSplittingField

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension of an ordinary character
belongs to the ordinary character ring over the extension field. -/
private theorem characterRingScalarExtensionForRemark_mem
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G]
    (χ : R[K](G)) :
    ((IsScalarTower.toAlgHom ℤ K K').compLeft G) (χ : G → K) ∈ R[K'](G) :=
  Representation.ProjectiveScalarExtensionSplitInjective.map_mem_characterRingOverField_local
    (G := G) (f := IsScalarTower.toAlgHom ℤ K K') (χ : G → K) χ.2

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension on ordinary character rings as
a function on bundled character-ring elements. -/
private noncomputable def characterRingScalarExtensionForRemarkToFun
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G] :
    R[K](G) → R[K'](G) :=
  fun χ ↦
    ⟨((IsScalarTower.toAlgHom ℤ K K').compLeft G) (χ : G → K),
      characterRingScalarExtensionForRemark_mem (K := K) (G := G) χ⟩

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension sends the zero character to
zero. -/
private theorem characterRingScalarExtensionForRemarkToFun_zero
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G] :
    characterRingScalarExtensionForRemarkToFun (K := K) (G := G) (K' := K')
      (0 : R[K](G)) = 0 := by
  ext g
  simp [characterRingScalarExtensionForRemarkToFun]

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension preserves addition of
ordinary characters. -/
private theorem characterRingScalarExtensionForRemarkToFun_add
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G]
    (χ ψ : R[K](G)) :
    characterRingScalarExtensionForRemarkToFun (K := K) (G := G) (K' := K') (χ + ψ) =
      characterRingScalarExtensionForRemarkToFun (K := K) (G := G) (K' := K') χ +
        characterRingScalarExtensionForRemarkToFun (K := K) (G := G) (K' := K') ψ := by
  ext g
  simp [characterRingScalarExtensionForRemarkToFun]

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension on ordinary character rings. -/
private noncomputable def characterRingScalarExtensionHomForRemark
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G] :
    R[K](G) →+ R[K'](G) where
  toFun := characterRingScalarExtensionForRemarkToFun (K := K) (G := G) (K' := K')
  map_zero' := characterRingScalarExtensionForRemarkToFun_zero (K := K) (G := G) (K' := K')
  map_add' :=
    characterRingScalarExtensionForRemarkToFun_add (K := K) (G := G) (K' := K')

/-- Helper for Remark 16-16.3-5: coefficientwise scalar extension on ordinary character rings is
injective. -/
private theorem characterRingScalarExtensionHomForRemark_injective
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G] :
    Function.Injective
      (characterRingScalarExtensionHomForRemark (K := K) (G := G) (K' := K')) := by
  intro χ ψ hχψ
  ext g
  apply (algebraMap K K').injective
  have hfun := congrArg (fun η : R[K'](G) ↦ (η : G → K')) hχψ
  exact congrFun hfun g

/-- Helper for Remark 16-16.3-5: the ordinary Grothendieck character map commutes with scalar
extension. -/
private theorem finiteRepGrothendieckCharacterScalarExtensionForRemark
    {K' : Type u} [Field K'] [Algebra K K'] [Finite G]
    (x : R₀[K](G)) :
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local (F := K')
        ((finiteRepGrothendieckScalarExtensionHom K K' G) x) =
      characterRingScalarExtensionHomForRemark (K := K) (G := G) (K' := K')
        (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · ext g
    simp [characterRingScalarExtensionHomForRemark, characterRingScalarExtensionForRemarkToFun]
  · intro V
    ext g
    rw [show (FreeAbelianGroup.of V : R₀[K](G)) = finiteRepGrothendieckClass K G V from rfl]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
    rw [ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class]
    change (FDRep.scalarExtension V).character g =
      algebraMap K K'
        ((ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (finiteRepGrothendieckClass K G V)) g)
    rw [ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class]
    exact congrFun
      (ProjectiveScalarExtensionSplitInjective.scalarExtension_character_eq_map_local
        (G := G) (F := K) (E := K') (τ := V.ρ)) g
  · intro V hV
    simpa using congrArg Neg.neg hV
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Remark 16-16.3-5: if the base field is quasisplit and has enough roots, every
ordinary virtual character over a finite extension descends coefficientwise to the base field. -/
private theorem characterRingScalarExtensionHomForRemark_surjectiveOfHasEnoughRoots
    [CharZero K] {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
    [Finite G]
    (hquasi : R[K](G) = R̄[K](G))
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective
      (characterRingScalarExtensionHomForRemark (K := K) (G := G) (K' := K')) := by
  intro χ'
  open Representation.ProjectiveScalarExtensionSplitInjective in
  have hχ'_valued :
      IsValuedInBaseField K (χ' : G → K') :=
    character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_compiled
      (K := K) (K' := K') (G := G) χ'.2
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχ'_valued
  rcases hχ'_valued with ⟨χK, hχK_map⟩
  have hχK_overline : χK ∈ R̄[K](G) := by
    let ι : K' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift (R := K)
    letI : Algebra K' (AlgebraicClosure K) := ι.toAlgebra
    letI : IsScalarTower K K' (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
    let ιZ : K' →ₐ[ℤ] AlgebraicClosure K := ι.restrictScalars ℤ
    have hχ'_alg :
        (ιZ.compLeft G) (χ' : G → K') ∈ R[AlgebraicClosure K](G) :=
      Representation.ProjectiveScalarExtensionSplitInjective.map_mem_characterRingOverField_local
        (G := G) (f := ιZ) (χ' : G → K') χ'.2
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χK]
    convert hχ'_alg using 1
    ext g
    have hg : algebraMap K K' (χK g) = (χ' : G → K') g := congrFun hχK_map g
    change algebraMap K (AlgebraicClosure K) (χK g) = ι (χ' g)
    calc
      algebraMap K (AlgebraicClosure K) (χK g)
          = algebraMap K' (AlgebraicClosure K) (algebraMap K K' (χK g)) :=
              IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K) (χK g)
      _ = ι (algebraMap K K' (χK g)) := by
            rw [RingHom.algebraMap_toAlgebra]
            rfl
      _ = ι (χ' g) := by rw [hg]
  have hχK_mem : χK ∈ R[K](G) := by
    simpa [hquasi] using hχK_overline
  refine ⟨⟨χK, hχK_mem⟩, ?_⟩
  ext g
  exact congrFun hχK_map g

/-- Helper for Remark 16-16.3-5: quasisplitness and enough roots give retract data for scalar
extension on ordinary finite-representation Grothendieck groups. -/
private theorem finiteRepGrothendieckScalarExtensionRetractOfHasEnoughRootsForRemark
    [CharZero K] {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
    [Finite G]
    (hquasi : R[K](G) = R̄[K](G))
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  classical
  letI : CharZero K' := (RingHom.charZero_iff (algebraMap K K').injective).1 inferInstance
  letI : NeZero (Nat.card G : K) :=
    ProjectiveScalarExtensionSplitInjective.nat_card_neZero_of_hasEnoughRoots_local
      (K := K) (L := K) (G := G)
  letI : NeZero (Nat.card G : K') :=
    ProjectiveScalarExtensionSplitInjective.nat_card_neZero_of_hasEnoughRoots_local
      (K := K) (L := K') (G := G)
  obtain ⟨sK, hsK_comp, _hsK_left⟩ :=
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_has_inverse
      (F := K) (G := G)
  have hsK_apply :
      ∀ χ : R[K](G),
        ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (sK χ) = χ := by
    intro χ
    have h :=
      congrArg (fun f : R[K](G) →+ R[K](G) ↦ f χ) hsK_comp
    simpa [AddMonoidHom.comp_apply] using h
  obtain ⟨ι, π', hπ'_pairwise, hπ'_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field
      (F := K') (H := G)
  let b' : Module.Basis ι ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π' hπ'_pairwise hπ'_complete
  have hpre :
      ∀ i : ι,
        ∃ χK : R[K](G),
          characterRingScalarExtensionHomForRemark (K := K) (K' := K') (G := G) χK =
            ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
              (F := K') [π' i]₀ := by
    intro i
    exact
      characterRingScalarExtensionHomForRemark_surjectiveOfHasEnoughRoots
        (K := K) (K' := K') (G := G) hquasi
        (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K') [π' i]₀)
  choose χK hχK using hpre
  let rL : R₀[K'](G) →ₗ[ℤ] R₀[K](G) := b'.constr ℤ (fun i ↦ sK (χK i))
  have hbasis : ∀ i,
      finiteRepGrothendieckScalarExtensionHom K K' G (rL (b' i)) = b' i := by
    intro i
    apply
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_eq_iff_general_local
        (F := K') (G := G)).1
    calc
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K')
          ((finiteRepGrothendieckScalarExtensionHom K K' G) (rL (b' i)))
          =
        characterRingScalarExtensionHomForRemark (K := K) (K' := K') (G := G)
          (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K) (rL (b' i))) := by
            rw [finiteRepGrothendieckCharacterScalarExtensionForRemark]
      _ =
        characterRingScalarExtensionHomForRemark (K := K) (K' := K') (G := G) (χK i) := by
            simp [rL, hsK_apply]
      _ = ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K') [π' i]₀ := hχK i
      _ = ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K') (b' i) := by
            simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]
  have hrightL :
      (finiteRepGrothendieckScalarExtensionHom K K' G).toIntLinearMap.comp rL =
        LinearMap.id := by
    apply b'.ext
    intro i
    simpa [LinearMap.comp_apply] using hbasis i
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    have hx :=
      congrArg (fun f : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) ↦ f x) hrightL
    simpa [r, LinearMap.comp_apply] using hx
  · intro x y hxy
    apply
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_eq_iff_general_local
        (F := K) (G := G)).1
    apply characterRingScalarExtensionHomForRemark_injective (K := K) (K' := K') (G := G)
    calc
      characterRingScalarExtensionHomForRemark (K := K) (K' := K') (G := G)
          (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K) x)
          =
        ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K') ((finiteRepGrothendieckScalarExtensionHom K K' G) x) := by
            rw [finiteRepGrothendieckCharacterScalarExtensionForRemark]
      _ =
        ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K') ((finiteRepGrothendieckScalarExtensionHom K K' G) y) := by
            rw [hxy]
      _ =
        characterRingScalarExtensionHomForRemark (K := K) (K' := K') (G := G)
          (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
            (F := K) y) := by
            rw [finiteRepGrothendieckCharacterScalarExtensionForRemark]

/-- Helper for Remark 16-16.3-5: over a sufficiently large base field of characteristic zero,
finite scalar extension is surjective on finite-representation Grothendieck groups.  This is the
Grothendieck-level reformulation of quasisplitness, routed through the ordinary
scalar-extension retract data isolated in Corollary 16-16.1-3. -/
private theorem finiteRepScalarExtensionHom_surjectiveOfHasEnoughRoots
    [CharZero K] {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective
      (finiteRepGrothendieckScalarExtensionHom K K' G : R₀[K](G) →+ R₀[K'](G)) := by
  -- Quasisplitness over the sufficiently large field `K` produces the retract of ordinary scalar
  -- extension `R₀[K](G) → R₀[K'](G)`, and evaluating the retract identity gives surjectivity.
  have hquasi : R[K](G) = R̄[K](G) :=
    quasisplitOfHasEnoughRoots (K := K) (G := G)
  obtain ⟨r, hr, _hinj⟩ :=
    finiteRepGrothendieckScalarExtensionRetractOfHasEnoughRootsForRemark
      (K := K) (K' := K') (G := G) hquasi
  intro y
  refine ⟨r y, ?_⟩
  have h := congrArg (fun f : R₀[K'](G) →+ R₀[K'](G) ↦ f y) hr
  simpa [AddMonoidHom.comp_apply] using h

/-- Helper for Remark 16-16.3-5: decomposition of a generator commutes with finite scalar
extension of the DVR, fraction field, and residue field. -/
private theorem decompositionHomScalarExtensionClass
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    [FaithfulSMul A A'] [IsLocalHom (algebraMap A A')]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K']
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [IsDomain A] [IsDiscreteValuationRing A] [Finite G]
    (X : FDRep K G) :
    finiteRepGrothendieckScalarExtensionHom
        (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G
        (decompositionHom A K G [X]₀) =
      decompositionHom A' K' G
        (finiteRepGrothendieckScalarExtensionHom K K' G [X]₀) := by
  -- Choose a stable lattice over `A`; its base change computes the decomposition of the
  -- scalar-extended representation over `A'`.
  obtain ⟨L⟩ := Representation.exists_stableLattice A X.ρ
  have hleft :
      finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G
          (decompositionHom A K G [X]₀) =
        [FDRep.scalarExtension
            (k := IsLocalRing.ResidueField A')
            (FDRep.of L.reductionRepresentation)]₀ := by
    -- The left side is scalar extension of the class of the original lattice reduction.
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  have hright :
      decompositionHom A' K' G
          (finiteRepGrothendieckScalarExtensionHom K K' G [X]₀) =
        [FDRep.scalarExtension
            (k := IsLocalRing.ResidueField A')
            (FDRep.of L.reductionRepresentation)]₀ := by
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
    -- Module-owner diamond bridge.  The base-change lattice `latBaseStableLattice L` lives over
    -- `TensorProduct.leftModule`, while `decompositionHom_finiteRepClass_eq` reads the canonical
    -- `FDRep.instModuleRestrictScalars` owner on `↥(FDRep.scalarExtension X).V`; constructing
    -- any lattice on that concrete carrier resolves to the wrong (`leftModule`) instance.  We
    -- therefore keep the scalar-extension owner *abstract* (`V`), so instance synthesis on
    -- `↥V.V` resolves to the canonical `FDRep` restrict-scalars instances expected by
    -- `decompositionHom_finiteRepClass_eq`, and transport `latBaseStableLattice L` into `V`
    -- along the structural iso.
    suffices key : ∀ (V : FDRep K' G)
        (e : (FDRep.scalarExtension (k := K') X) ≅ V),
        decompositionHom A' K' G [V]₀ =
          [FDRep.scalarExtension (k := IsLocalRing.ResidueField A')
            (FDRep.of L.reductionRepresentation)]₀ by
      exact key (FDRep.scalarExtension (k := K') X) (Iso.refl _)
    intro V e
    -- The base-change lattice over the `TensorProduct.leftModule` owner.
    let Lbc := StableLattice.latBaseStableLattice (A' := A') (K' := K') L
    -- The `K'`-linear equivalence underlying the structural iso `e`, read through `Rep`.
    let eR := (forget₂ (FDRep K' G) (Rep K' G)).mapIso e
    let φK : (FDRep.scalarExtension (k := K') X).V ≃ₗ[K'] V.V :=
      { toFun := eR.hom.hom.toLinearMap
        invFun := eR.inv.hom.toLinearMap
        left_inv := by
          intro x
          have h := congrArg
            (fun f : (forget₂ (FDRep K' G) (Rep K' G)).obj (FDRep.scalarExtension (k := K') X) ⟶
              (forget₂ (FDRep K' G) (Rep K' G)).obj (FDRep.scalarExtension (k := K') X) =>
                f.hom.toLinearMap x) eR.hom_inv_id
          simp
        right_inv := by
          intro x
          have h := congrArg
            (fun f : (forget₂ (FDRep K' G) (Rep K' G)).obj V ⟶
              (forget₂ (FDRep K' G) (Rep K' G)).obj V => f.hom.toLinearMap x) eR.inv_hom_id
          simp
        map_add' := eR.hom.hom.toLinearMap.map_add
        map_smul' := eR.hom.hom.toLinearMap.map_smul }
    -- `φK` is equivariant: it is a morphism of representations.
    have he : ∀ g : G, ∀ x : (FDRep.scalarExtension (k := K') X).V,
        φK ((FDRep.scalarExtension (k := K') X).ρ g x) = V.ρ g (φK x) := by
      intro g x
      have hx := LinearMap.congr_fun (eR.hom.hom.isIntertwining' g) x
      simpa using hx
    -- Transport `Lbc` along `φK` into `V.ρ`.  Because `V` is abstract, `Le` lives over the
    -- canonical `FDRep` restrict-scalars owner expected by `decompositionHom_finiteRepClass_eq`.
    let Le : StableLattice A' V.ρ :=
      stableLatticeTransportOfIntertwiningEquiv (A := A') (K := K') (G' := G) φK he Lbc
    rw [decompositionHom_finiteRepClass_eq (A := A') (K := K') (G := G) V Le]
    -- The `A'`-linear submodule equivalence `Lbc.toSubmodule ≃ₗ[A'] Le.toSubmodule`.
    let φA' : (FDRep.scalarExtension (k := K') X).V ≃ₗ[A'] V.V := φK.restrictScalars A'
    have hLeSub : Le.toSubmodule = Lbc.toSubmodule.map (φA'.toLinearMap) := rfl
    let eSub : Lbc.toSubmodule ≃ₗ[A'] Le.toSubmodule := by
      rw [hLeSub]
      exact Submodule.equivMapOfInjective (φA'.toLinearMap) φA'.injective Lbc.toSubmodule
    have heSub : ∀ g : G, ∀ x : Lbc.toSubmodule,
        eSub (Lbc.toRepresentation g x) = Le.toRepresentation g (eSub x) := by
      intro g x
      apply Subtype.ext
      change (φA' ((Lbc.toRepresentation g x : Lbc.toSubmodule) :
            (FDRep.scalarExtension (k := K') X).V))
          = V.ρ g (φA' ((x : Lbc.toSubmodule) : (FDRep.scalarExtension (k := K') X).V))
      rw [StableLattice.toRepresentation_apply_coe]
      exact he g x
    -- The two transported reductions agree, and the base-change reduction iso closes the chain.
    have hred1 :
        Nonempty (FDRep.of Lbc.reductionRepresentation ≅ FDRep.of Le.reductionRepresentation) :=
      ⟨Representation.Equiv.toFDRepIso
        (StableLattice.reductionNonemptyEquivOfIntertwining (A := A') (K := K') eSub heSub).some⟩
    calc
      [FDRep.of Le.reductionRepresentation]₀
          = [FDRep.of Lbc.reductionRepresentation]₀ :=
        (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := IsLocalRing.ResidueField A') (G := G)
          hred1).symm
      _ = [FDRep.scalarExtension (k := IsLocalRing.ResidueField A')
            (FDRep.of L.reductionRepresentation)]₀ :=
        finiteRepGrothendieckClass_eq_of_nonempty_iso (L := IsLocalRing.ResidueField A') (G := G)
          (StableLattice.latBaseReduction_nonempty_iso (A' := A') (K' := K') L)
  rw [hleft, hright]

/-- Helper for Remark 16-16.3-5: the stabilized `z'` witness from condition `(R)` descends to a
fixed-field `(R')` lift. -/
private theorem hasRPrimeLiftOfConditionRFrontier
    [CharZero K]
    [IsDomain A] [IsDiscreteValuationRing A] [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
    [FaithfulSMul A A'] [IsLocalHom (algebraMap A A')]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
    [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [FiniteDimensional K K']
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
    (S : FDRep (IsLocalRing.ResidueField A) G) (hS : Simple S)
    (hpre :
      R⁺[K](G) =
        (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G))
    {z' : R₀[K'](G)}
    (hz'positive : z' ∈ R⁺[K'](G))
    (hz'decomp :
      decompositionHom A' K' G z' =
        finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G [S]₀) :
    FDRep.HasRPrimeLift S K := by
  -- Choose a virtual fixed-field preimage of the condition-`(R)` witness over `K'`.
  obtain ⟨x, hxscalar⟩ :=
    finiteRepScalarExtensionHom_surjectiveOfHasEnoughRoots
      (K := K) (G := G) (K' := K') z'
  have hxpos : x ∈ R⁺[K](G) := by
    rw [hpre]
    simpa [Set.mem_preimage, hxscalar] using hz'positive
  have hxdec : decompositionHom A K G x = ([S]₀ : R₀[IsLocalRing.ResidueField A](G)) := by
    rcases (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hxpos with ⟨X, hXclass⟩
    apply finiteRepScalarExtensionHom_injectiveOfFiniteDimensional
      (F := IsLocalRing.ResidueField A) (E := IsLocalRing.ResidueField A') (G := G)
    calc
      finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G
          (decompositionHom A K G x) =
        finiteRepGrothendieckScalarExtensionHom
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G
          (decompositionHom A K G [X]₀) := by
            rw [hXclass]
      _ = decompositionHom A' K' G
            (finiteRepGrothendieckScalarExtensionHom K K' G [X]₀) := by
            exact decompositionHomScalarExtensionClass (A := A) (K := K) (G := G) (A' := A')
              (K' := K') X
      _ = decompositionHom A' K' G
            (finiteRepGrothendieckScalarExtensionHom K K' G x) := by
            rw [hXclass]
      _ = decompositionHom A' K' G z' := by rw [hxscalar]
      _ = finiteRepGrothendieckScalarExtensionHom
            (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') G [S]₀ := hz'decomp
  -- The fixed positive class with simple decomposition class is exactly an `(R')` lift.
  exact
    hasRPrimeLiftOfPositiveDecompositionClassEqSimple
      (A := A) (K := K) (G := G) S hS hxpos hxdec

/-- Condition `(R')` implies condition `(R)` with the trivial witnesses `A' = A` and `K' = K`.
(De-privatised: this is the placeholder-free direction of the `(R) ↔ (R')` equivalence, reused by
the Fong–Swan theorem 16-16.3-6 to avoid dragging the still-open `(R) → (R')` direction.) -/
theorem satisfiesConditionR_of_satisfiesConditionRPrime
    [Finite G] [IsDomain A] [IsDiscreteValuationRing A]
    (hR' : SatisfiesConditionRPrime A K G) :
    SatisfiesConditionR (R⁺[K](G)) A := by
  simpa using
    satisfiesConditionRPrime_imp_satisfiesConditionR (A := A) (K := K) (G := G) hR'

/-- Helper for Remark 16-16.3-5: condition `(R)` should give condition `(R')` after descending
the finite extension witness back to the sufficiently large base field. -/
private theorem satisfiesConditionRPrime_of_satisfiesConditionR
    [CharZero K] [Finite G] [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hR : SatisfiesConditionR (R⁺[K](G)) A) :
    SatisfiesConditionRPrime A K G := by
  -- Route correction: direct descent of a chosen simple lift over the witness field is not data
  -- supplied by condition `(R)`.  The remaining route should stay at Grothendieck-class level:
  -- descend the positive witness through scalar extension from sufficiently large `K`, commute it
  -- with decomposition and residue-field scalar extension, then convert fixed image membership of
  -- `[S]₀` into an actual stable-lattice `(R')` lift.
  intro S hS
  rcases hR with
    ⟨A', instCommA', instLocalA', instDomainA', instDVRA', instAlgAA',
      instFiniteAA', K', instFieldK', instAlgA'K', instAlgAK', instFracA'K',
      instAlgKK', instTowerAA'K', instTowerAKK', instFiniteDimKK', _hpre, hdecomp⟩
  letI : CommRing A' := instCommA'
  letI : IsLocalRing A' := instLocalA'
  letI : IsDomain A' := instDomainA'
  letI : IsDiscreteValuationRing A' := instDVRA'
  letI : Algebra A A' := instAlgAA'
  letI : Module.Finite A A' := instFiniteAA'
  letI : Field K' := instFieldK'
  letI : Algebra A' K' := instAlgA'K'
  letI : Algebra A K' := instAlgAK'
  letI : IsFractionRing A' K' := instFracA'K'
  letI : Algebra K K' := instAlgKK'
  letI : IsScalarTower A A' K' := instTowerAA'K'
  letI : IsScalarTower A K K' := instTowerAKK'
  letI : FiniteDimensional K K' := instFiniteDimKK'
  -- The finite local extension `A → A'` induces the residue-field scalar map `k → k'`.
  have hAK : Function.Injective (algebraMap A K) := by
    simpa [faithfulSMul_iff_algebraMap_injective] using
      (inferInstance : FaithfulSMul A K)
  have hKK' : Function.Injective (algebraMap K K') := RingHom.injective _
  have hAK' : Function.Injective (algebraMap A K') := by
    simpa [IsScalarTower.algebraMap_eq A K K'] using hKK'.comp hAK
  have hcomp : Function.Injective ((algebraMap A' K') ∘ (algebraMap A A')) := by
    simpa [IsScalarTower.algebraMap_eq A A' K'] using hAK'
  have hAA' : Function.Injective (algebraMap A A') :=
    Function.Injective.of_comp hcomp
  letI : FaithfulSMul A A' :=
    (faithfulSMul_iff_algebraMap_injective A A').2 hAA'
  letI : IsLocalHom (algebraMap A A') := by
    infer_instance
  -- Use the canonical residue-field algebra/tower induced by the finite local map `A → A'`.
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') := inferInstance
  let _ : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') :=
    IsLocalRing.ResidueField.finite_of_module_finite (R := A) (S := A')
  letI : IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') :=
    inferInstance
  letI : FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') :=
    inferInstance
  obtain ⟨z', hz'positive, hz'decomp⟩ :=
    conditionR_positivePreimage_of_residueScalarExtensionClass
      (A := A) (G := G) (A' := A') (K' := K') hdecomp S
  -- The named frontier bridge now consumes both condition-`(R)` conjuncts: `_hpre` supplies
  -- positivity after choosing a scalar-extension preimage, and `hdecomp` supplies `z'`.
  exact
    hasRPrimeLiftOfConditionRFrontier
      (A := A) (K := K) (G := G) (A' := A') (K' := K') S hS _hpre
      hz'positive hz'decomp

/-- Remark 16-16.3-5 (faithful form).  For the modular system `(A, K, k)` — `A` a discrete
valuation ring with fraction field `K` *sufficiently large*
(`HasEnoughRootsOfUnity K (Monoid.exponent G)`) — Serre's condition `(R)` for `R⁺[K](G)` is
*equivalent* to condition `(R')`: every simple `k[G]`-module is the reduction modulo `𝔪` of a
(necessarily simple) finite-dimensional `K[G]`-representation.

⚠️ Two hypotheses are essential and were absent from the earlier form (which made the equivalence
**FALSE**):

* `[IsDomain A] [IsDiscreteValuationRing A]` — Serre's `(A, K, k)` is a *modular system*, so `A` is
  a genuine DVR (never a field).  Without it one may take `A = K` a field: then `(R)` is vacuously
  **false** (`SatisfiesConditionR` demands a finite DVR extension of `A`, impossible over a field)
  while `(R')` is trivially **true** (here `k = K`, so every simple `k[G]`-module lifts to itself),
  and the equivalence collapses.
* `[HasEnoughRootsOfUnity K (Monoid.exponent G)]` — Serre's "`K` sufficiently large".  Without it
  `(R)` can hold (using an extension `A'/K'`) while the *fixed-`K`* condition `(R')` fails; e.g.
  `A = ℤ_(2)`, `K = ℚ`, `p = 2`, `G = C₇`: the simple `𝔽₂[C₇]`-modules have dimensions `1, 3, 3`,
  but every simple `ℚ[C₇]`-representation has dimension `1` or `6`, so the `3`-dimensional simple
  modular modules are not reductions of simple `ℚ[C₇]`-representations and `(R')` fails over
  `K = ℚ`.

(Note also: `(R')` does NOT hold merely because `K` is large — it lifts every simple modular
representation to characteristic `0`, which holds for `p`-solvable `G` by Fong–Swan but fails for
general `G`.  Serre 16.3.5 only asserts the *equivalence* `(R) ↔ (R')`, never that either holds
unconditionally.) -/
theorem satisfiesConditionR_iff_satisfiesConditionRPrime
    [CharZero K] [Finite G] [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionR (R⁺[K](G)) A ↔ SatisfiesConditionRPrime A K G := by
  -- Assemble the two source-facing directions isolated above.
  constructor
  · exact satisfiesConditionRPrime_of_satisfiesConditionR (A := A) (K := K) (G := G)
  · exact satisfiesConditionR_of_satisfiesConditionRPrime (A := A) (K := K) (G := G)

end

end Representation
