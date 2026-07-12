import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FieldTransport

noncomputable section
open CategoryTheory
open scoped MonoidAlgebra Representation
universe u x
namespace Representation

section FDRepTransport

variable {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
variable {G : Type u} [Group G]

/-- Helper for Exercise 18-18.3-2: a `K`-linear map between finite-dimensional representations is
automatically `F`-linear after transporting the scalar action across `e`, since the `F`-action
factors through `e`. -/
def transportLinearMap {S T : FDRep K G} (φ : S ⟶ T) :
    (fdRepOverRingEquiv e S) →ₗ[F] (fdRepOverRingEquiv e T) where
  toFun := φ.hom.hom.hom
  map_add' x y := φ.hom.hom.hom.map_add x y
  map_smul' a x := φ.hom.hom.hom.map_smul (e a) x

/-- Helper for Exercise 18-18.3-2: transport a morphism of finite-dimensional representations
across `e`, keeping the same underlying linear map. -/
def transportHom {S T : FDRep K G} (φ : S ⟶ T) :
    (fdRepOverRingEquiv e S) ⟶ (fdRepOverRingEquiv e T) :=
  letI iMS : Module F (↑S.V) := Module.compHom (↑S.V) e.toRingHom
  letI iMT : Module F (↑T.V) := Module.compHom (↑T.V) e.toRingHom
  letI iFS : Module.Finite F (↑S.V) := moduleFinite_compHom_ringEquiv e (↑S.V)
  letI iFT : Module.Finite F (↑T.V) := moduleFinite_compHom_ringEquiv e (↑T.V)
  { hom := FGModuleCat.ofHom (transportLinearMap e φ)
    comm := fun g => by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun m : S.V ⟶ T.V => m.hom.hom x) (φ.comm g)
      simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, FDRep.hom_hom_action_ρ] at hx
      simpa only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, FDRep.hom_hom_action_ρ] using hx }

@[simp] theorem transportHom_apply {S T : FDRep K G} (φ : S ⟶ T) (x : S) :
    (transportHom e φ).hom.hom.hom x = φ.hom.hom.hom x := rfl

variable (G) in
/-- Transport of finite-dimensional representations across a ring isomorphism of the coefficient
field, as a functor `FDRep K G ⥤ FDRep F G`. The object map is `fdRepOverRingEquiv e`, and the
morphism map keeps the same underlying linear map (a `K`-linear map is automatically `F`-linear
since the `F`-action factors through `e`). -/
def fdRepFunctor [Finite G] : FDRep K G ⥤ FDRep F G where
  obj S := fdRepOverRingEquiv e S
  map {S T} φ := transportHom e φ
  map_id S := by
    apply Action.hom_ext; apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; simp
  map_comp {S T U} φ ψ := by
    apply Action.hom_ext; apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; simp

@[simp] theorem fdRepFunctor_obj [Finite G] (S : FDRep K G) :
    (fdRepFunctor e G).obj S = fdRepOverRingEquiv e S := rfl

@[simp] theorem fdRepFunctor_map_apply [Finite G] {S T : FDRep K G} (φ : S ⟶ T) (x : S) :
    ((fdRepFunctor e G).map φ).hom.hom.hom x = φ.hom.hom.hom x := rfl

instance fdRepFunctor_preservesZeroMorphisms [Finite G] :
    (fdRepFunctor e G).PreservesZeroMorphisms where
  map_zero X Y := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (transportHom e (0 : X ⟶ Y)).hom.hom.hom x = _
    rw [transportHom_apply]
    rfl

/-- Helper for Exercise 18-18.3-2: transport preserves simplicity. -/
theorem fdRepOverRingEquiv_simple (S : FDRep K G) [Simple S] :
    Simple (fdRepOverRingEquiv e S) := by
  letI : Module F S := Module.compHom S e.toRingHom
  letI : Representation.IsIrreducible ((fdRepOverRingEquiv e S).ρ) := by
    change Representation.IsIrreducible (repOverRingEquiv e S)
    exact transported_irreducible_of_ringEquiv e S
  exact FDRep.simple_of_isIrreducible (fdRepOverRingEquiv e S)

/-- Helper for Exercise 18-18.3-2: the underlying `K`-linear identity is a linear equivalence
between the `e.symm`-then-`e` round trip and the original representation. -/
def roundtripLinearEquiv (S : FDRep K G) :
    (fdRepOverRingEquiv e.symm (fdRepOverRingEquiv e S)) ≃ₗ[K] S where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := congrArg (fun c : K => c • (id x : S)) (e.apply_symm_apply a)

/-- Helper for Exercise 18-18.3-2: the underlying `F`-linear identity is a linear equivalence
between the `e`-then-`e.symm` round trip and the original representation. -/
def roundtripLinearEquiv' (S : FDRep F G) :
    (fdRepOverRingEquiv e (fdRepOverRingEquiv e.symm S)) ≃ₗ[F] S where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := congrArg (fun c : F => c • (id x : S)) (e.symm_apply_apply a)

/-- Helper for Exercise 18-18.3-2: round-trip transport (along `e` then `e.symm`) returns to the
original representation. -/
def fdRepOverRingEquiv_roundtrip (S : FDRep K G) :
    fdRepOverRingEquiv e.symm (fdRepOverRingEquiv e S) ≅ S := by
  letI : Module K (↑(fdRepOverRingEquiv e S).V) :=
    Module.compHom (↑(fdRepOverRingEquiv e S).V) e.symm.toRingHom
  letI : Module.Finite K (↑(fdRepOverRingEquiv e S).V) :=
    moduleFinite_compHom_ringEquiv e.symm (↑(fdRepOverRingEquiv e S).V)
  exact Action.mkIso (LinearEquiv.toFGModuleCatIso (roundtripLinearEquiv e S)) (fun g => by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)

/-- Helper for Exercise 18-18.3-2: round-trip transport (along `e.symm` then `e`) returns to the
original representation. -/
def fdRepOverRingEquiv_roundtrip' (S : FDRep F G) :
    fdRepOverRingEquiv e (fdRepOverRingEquiv e.symm S) ≅ S := by
  letI : Module F (↑(fdRepOverRingEquiv e.symm S).V) :=
    Module.compHom (↑(fdRepOverRingEquiv e.symm S).V) e.toRingHom
  letI : Module.Finite F (↑(fdRepOverRingEquiv e.symm S).V) :=
    moduleFinite_compHom_ringEquiv e (↑(fdRepOverRingEquiv e.symm S).V)
  exact Action.mkIso (LinearEquiv.toFGModuleCatIso (roundtripLinearEquiv' e S)) (fun g => by
    apply FGModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)

/-- Helper for Exercise 18-18.3-2: transport preserves pairwise non-isomorphy. -/
theorem fdRepOverRingEquiv_pairwise [Finite G] {ι : Type x} (π : ι → FDRep K G)
    (h : PairwiseNonisomorphic π) :
    PairwiseNonisomorphic (fun i => fdRepOverRingEquiv e (π i)) := by
  intro i j hij
  rintro ⟨φ⟩
  refine h hij ⟨?_⟩
  exact (fdRepOverRingEquiv_roundtrip e (π i)).symm ≪≫ (fdRepFunctor e.symm G).mapIso φ ≪≫
    fdRepOverRingEquiv_roundtrip e (π j)

/-- Helper for Exercise 18-18.3-2: transport preserves the property of being a complete irreducible
family. -/
theorem fdRepOverRingEquiv_complete [Finite G] {ι : Type x} (π : ι → FDRep K G)
    [IsCompleteIrreducibleFamily π] :
    IsCompleteIrreducibleFamily (fun i => fdRepOverRingEquiv e (π i)) where
  isSimple i := fdRepOverRingEquiv_simple e (π i)
  exists_iso τ hτ := by
    letI : Simple τ := hτ
    letI : Simple (fdRepOverRingEquiv e.symm τ) := fdRepOverRingEquiv_simple e.symm τ
    obtain ⟨i, ⟨φ⟩⟩ := IsCompleteIrreducibleFamily.exists_iso (π := π)
      (fdRepOverRingEquiv e.symm τ) inferInstance
    exact ⟨i, ⟨(fdRepOverRingEquiv_roundtrip' e τ).symm ≪≫ (fdRepFunctor e G).mapIso φ⟩⟩

/-- Helper for Exercise 18-18.3-2: the transport functor preserves short exact sequences. The
underlying additive groups and underlying maps are unchanged, so exactness is reflected through the
forgetful functors to `ModuleCat`. -/
theorem fdRepFunctor_shortExact [Finite G] (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    (S.map (fdRepFunctor e G)).ShortExact := by
  set S' := S.map (fdRepFunctor e G) with hS'
  let GK : FDRep K G ⥤ ModuleCat K :=
    forget₂ (FDRep K G) (Rep K G) ⋙ forget₂ (Rep K G) (ModuleCat K)
  let GF : FDRep F G ⥤ ModuleCat F :=
    forget₂ (FDRep F G) (Rep F G) ⋙ forget₂ (Rep F G) (ModuleCat F)
  have hSK : (S.map GK).ShortExact := hS.map_of_exact GK
  have hf_inj : Function.Injective ⇑(S.map GK).f := (ModuleCat.mono_iff_injective _).1 hSK.mono_f
  have hg_surj : Function.Surjective ⇑(S.map GK).g := (ModuleCat.epi_iff_surjective _).1 hSK.epi_g
  have hex := (ShortComplex.moduleCat_exact_iff _).1 hSK.exact
  have hSEF : (S'.map GF).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      obtain ⟨y, hy⟩ := hex x hx
      exact ⟨y, hy⟩
    · rw [ModuleCat.mono_iff_injective]; exact hf_inj
    · rw [ModuleCat.epi_iff_surjective]; exact hg_surj
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (S'.exact_map_iff_of_faithful GF).1 hSEF.exact
  · exact GF.mono_of_mono_map hSEF.mono_f
  · exact GF.epi_of_epi_map hSEF.epi_g

/-- Helper for Exercise 18-18.3-2: transport sends a defining short-exact-sequence generator of the
Grothendieck relations to a vanishing class. -/
theorem grothendieckTransport_generator_eq_zero [Finite G]
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    (FreeAbelianGroup.lift fun V : FDRep K G => ([fdRepOverRingEquiv e V]₀ : R₀[F](G)))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0 := by
  have hSE : (S.map (fdRepFunctor e G)).ShortExact := fdRepFunctor_shortExact e S hS
  have hrel := finiteRepGrothendieckClass_middle_eq_left_add_right
    (L := F) (G := G) (S.map (fdRepFunctor e G)) hSE
  simp only [map_sub, FreeAbelianGroup.lift_apply_of]
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm]
  exact hrel

variable (G) in
/-- The Grothendieck group of finite-dimensional representations is transported across a ring
isomorphism `e : F ≃+* K` of the coefficient field. -/
def grothendieckTransport [Finite G] : R₀[K](G) →+ R₀[F](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (FreeAbelianGroup.lift fun V : FDRep K G => ([fdRepOverRingEquiv e V]₀ : R₀[F](G)))
    (by
      rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
      rintro _ ⟨⟨S, hS⟩, rfl⟩
      exact grothendieckTransport_generator_eq_zero e S hS)

@[simp] theorem grothendieckTransport_class [Finite G] (V : FDRep K G) :
    grothendieckTransport e G ([V]₀ : R₀[K](G)) = ([fdRepOverRingEquiv e V]₀ : R₀[F](G)) := rfl

end FDRepTransport

end Representation
