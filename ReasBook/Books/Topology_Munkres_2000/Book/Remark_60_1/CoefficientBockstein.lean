module

public import Topology_Munkres_2000.Book.Remark_60_1.IntegralSingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearMap

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits

/-- Helper for Remark 60.1: singular cochains with values in an integral
coefficient module. -/
abbrev singularCochainGroupWithCoefficients
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((integralSingularChainComplex X).X n →ₗ[ℤ] M)

/-- Helper for Remark 60.1: the singular coboundary with arbitrary integral
module coefficients is precomposition by the singular boundary. -/
lemma singularCoboundaryWithCoefficients_map_zero
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) :
    (0 : (integralSingularChainComplex X).X n →ₗ[ℤ] M).comp
      ((integralSingularChainComplex X).d (n + 1) n).hom = 0 := by
  -- Precomposition preserves the zero cochain.
  exact LinearMap.zero_comp _

/-- Helper for Remark 60.1: precomposition by a singular boundary preserves
addition of coefficient-valued cochains. -/
lemma singularCoboundaryWithCoefficients_map_add
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (φ ψ : (integralSingularChainComplex X).X n →ₗ[ℤ] M) :
    (φ + ψ).comp ((integralSingularChainComplex X).d (n + 1) n).hom =
      φ.comp ((integralSingularChainComplex X).d (n + 1) n).hom +
        ψ.comp ((integralSingularChainComplex X).d (n + 1) n).hom := by
  -- Composition distributes over addition in its left argument.
  exact LinearMap.add_comp _ _ _

/-- Helper for Remark 60.1: precomposition by a singular boundary as an
additive homomorphism on cochains. -/
def singularCoboundaryWithCoefficientsAddHom
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) :
    ((integralSingularChainComplex X).X n →ₗ[ℤ] M) →+
      ((integralSingularChainComplex X).X (n + 1) →ₗ[ℤ] M) :=
  { toFun := fun φ ↦
      φ.comp ((integralSingularChainComplex X).d (n + 1) n).hom
    map_zero' := singularCoboundaryWithCoefficients_map_zero X M n
    map_add' := singularCoboundaryWithCoefficients_map_add X M n }

/-- Helper for Remark 60.1: the singular coboundary with arbitrary integral
module coefficients is precomposition by the singular boundary. -/
def singularCoboundaryWithCoefficients
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) :
    singularCochainGroupWithCoefficients X M n ⟶
      singularCochainGroupWithCoefficients X M (n + 1) :=
  ModuleCat.ofHom (singularCoboundaryWithCoefficientsAddHom X M n).toIntLinearMap

/-- Helper for Remark 60.1: a coefficient-valued singular coboundary evaluates
by precomposition with the singular boundary. -/
lemma singularCoboundaryWithCoefficients_apply
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (φ : singularCochainGroupWithCoefficients X M n)
    (x : (integralSingularChainComplex X).X (n + 1)) :
    singularCoboundaryWithCoefficients X M n φ x =
      φ (((integralSingularChainComplex X).d (n + 1) n) x) := by
  -- Expose the additive-hom construction through its stable evaluation formula.
  rfl

/-- Helper for Remark 60.1: consecutive coefficient-valued singular
coboundaries compose to zero. -/
lemma singularCoboundaryWithCoefficients_sq
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) :
    singularCoboundaryWithCoefficients X M n ≫
      singularCoboundaryWithCoefficients X M (n + 1) = 0 := by
  -- Evaluate the two precompositions and use the singular boundary's square-zero law.
  ext φ x
  change φ (((integralSingularChainComplex X).d (n + 1) n).hom
    (((integralSingularChainComplex X).d (n + 1 + 1) (n + 1)).hom x)) = 0
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using
    congrArg (fun f ↦ φ (f.hom x))
      ((integralSingularChainComplex X).d_comp_d (n + 1 + 1) (n + 1) n)

/-- Helper for Remark 60.1: the singular cochain complex with values in an
arbitrary integral coefficient module. -/
@[expose]
def singularCochainComplexWithCoefficients
    (X : TopCat) (M : ModuleCat ℤ) : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (singularCochainGroupWithCoefficients X M)
    (singularCoboundaryWithCoefficients X M)
    (singularCoboundaryWithCoefficients_sq X M)

/-- Helper for Remark 60.1: the adjacent differential of the packaged
coefficient-valued complex is the named singular coboundary. -/
lemma singularCochainComplexWithCoefficients_d
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) :
    (singularCochainComplexWithCoefficients X M).d n (n + 1) =
      singularCoboundaryWithCoefficients X M n := by
  -- Apply the adjacent-differential computation rule of `CochainComplex.of`.
  simpa only [singularCochainComplexWithCoefficients] using
    (CochainComplex.of_d (singularCochainGroupWithCoefficients X M)
      (singularCoboundaryWithCoefficients X M) n)

/-- Helper for Remark 60.1: the adjacent differential of the packaged
coefficient-valued cochain complex evaluates by precomposition. -/
lemma singularCochainComplexWithCoefficients_d_apply
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (φ : singularCochainGroupWithCoefficients X M n) :
    ((singularCochainComplexWithCoefficients X M).d n (n + 1)).hom φ =
      φ.comp ((integralSingularChainComplex X).d (n + 1) n).hom := by
  -- Use the `CochainComplex.of` computation rule and the coboundary API.
  rw [singularCochainComplexWithCoefficients_d]
  apply LinearMap.ext
  intro x
  change singularCoboundaryWithCoefficients X M n φ x =
    φ (((integralSingularChainComplex X).d (n + 1) n) x)
  exact singularCoboundaryWithCoefficients_apply X M n φ x

/-- Helper for Remark 60.1: postcomposition with a coefficient homomorphism
acts linearly on singular cochains in each degree. -/
lemma singularCoefficientMapComponent_map_zero
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ) :
    f.hom.comp (0 : (integralSingularChainComplex X).X n →ₗ[ℤ] M) = 0 := by
  -- Postcomposition preserves the zero cochain.
  exact LinearMap.comp_zero _

/-- Helper for Remark 60.1: postcomposition by a coefficient homomorphism
preserves addition of cochains. -/
lemma singularCoefficientMapComponent_map_add
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ)
    (φ ψ : (integralSingularChainComplex X).X n →ₗ[ℤ] M) :
    f.hom.comp (φ + ψ) = f.hom.comp φ + f.hom.comp ψ := by
  -- Composition distributes over addition in its right argument.
  exact LinearMap.comp_add _ _ _

/-- Helper for Remark 60.1: postcomposition by a coefficient homomorphism as
an additive homomorphism on cochains. -/
def singularCoefficientMapComponentAddHom
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ) :
    ((integralSingularChainComplex X).X n →ₗ[ℤ] M) →+
      ((integralSingularChainComplex X).X n →ₗ[ℤ] N) :=
  { toFun := fun φ ↦ f.hom.comp φ
    map_zero' := singularCoefficientMapComponent_map_zero X f n
    map_add' := singularCoefficientMapComponent_map_add X f n }

/-- Helper for Remark 60.1: postcomposition with a coefficient homomorphism
acts linearly on singular cochains in each degree. -/
def singularCoefficientMapComponent
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ) :
    singularCochainGroupWithCoefficients X M n ⟶
      singularCochainGroupWithCoefficients X N n :=
  ModuleCat.ofHom (singularCoefficientMapComponentAddHom X f n).toIntLinearMap

/-- Helper for Remark 60.1: coefficient postcomposition commutes with the
singular coboundary. -/
lemma singularCoefficientMapComponent_comm
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ) :
    singularCoefficientMapComponent X f n ≫
        singularCoboundaryWithCoefficients X N n =
      singularCoboundaryWithCoefficients X M n ≫
        singularCoefficientMapComponent X f (n + 1) := by
  -- Both sides send a cochain to postcomposition by `f` after one boundary.
  ext φ x
  change f.hom (φ (((integralSingularChainComplex X).d (n + 1) n).hom x)) =
    f.hom (φ (((integralSingularChainComplex X).d (n + 1) n).hom x))
  rfl

/-- Helper for Remark 60.1: coefficient postcomposition commutes with the
packaged differentials of the coefficient-valued cochain complexes. -/
lemma singularCoefficientCochainMap_comm
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) (n : ℕ) :
    singularCoefficientMapComponent X f n ≫
        (singularCochainComplexWithCoefficients X N).d n (n + 1) =
      (singularCochainComplexWithCoefficients X M).d n (n + 1) ≫
        singularCoefficientMapComponent X f (n + 1) := by
  -- Expose the single computation rule of `CochainComplex.of`.
  simpa only [singularCochainComplexWithCoefficients, CochainComplex.of_d] using
    singularCoefficientMapComponent_comm X f n

/-- Helper for Remark 60.1: a homomorphism of coefficient modules induces a
map of singular cochain complexes. -/
def singularCoefficientCochainMap
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N) :
    singularCochainComplexWithCoefficients X M ⟶
      singularCochainComplexWithCoefficients X N :=
  CochainComplex.ofHom (fun n ↦ singularCoefficientMapComponent X f n)
    (singularCoefficientCochainMap_comm X f)

/-- Helper for Remark 60.1: the integral singular-chain module in every
degree is projective, since it is a coproduct of copies of `ℤ`. -/
lemma integralSingularChainComplex_projective (X : TopCat) (n : ℕ) :
    Projective ((integralSingularChainComplex X).X n) := by
  -- Normalize directly to the coproduct presentation to avoid expensive instance unfolding.
  change Projective
    (∐ fun _ : (TopCat.toSSet.obj X).obj (.op (SimplexCategory.mk n)) ↦
      ModuleCat.of ℤ ℤ)
  infer_instance

/-- Helper for Remark 60.1: multiplication by two followed by reduction
modulo two is zero. -/
lemma two_mul_then_modTwo_zero :
    (Int.castAddHom (ZMod 2)).toIntLinearMap.comp
      (LinearMap.lsmul ℤ ℤ 2) = 0 := by
  -- Reduction modulo two kills every even integer.
  apply LinearMap.ext
  intro x
  change ((2 * x : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul]
  change ((2 : ℤ) : ZMod 2) * (x : ZMod 2) = 0
  calc
    ((2 : ℤ) : ZMod 2) * (x : ZMod 2) = 0 * (x : ZMod 2) := by
      rw [show ((2 : ℤ) : ZMod 2) = 0 by decide]
    _ = 0 := zero_mul _

/-- Helper for Remark 60.1: the coefficient sequence
`ℤ --2→ ℤ → ZMod 2`. -/
abbrev integralModTwoCoefficientShortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero
    (LinearMap.lsmul ℤ ℤ 2)
    (Int.castAddHom (ZMod 2)).toIntLinearMap
    two_mul_then_modTwo_zero

/-- Helper for Remark 60.1: multiplication by two is injective on the
integers. -/
lemma two_mul_injective :
    Function.Injective (LinearMap.lsmul ℤ ℤ 2) := by
  -- Cancel the nonzero integer factor.
  intro x y hxy
  simpa only [LinearMap.lsmul_apply, smul_eq_mul] using
    (mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) hxy)

/-- Helper for Remark 60.1: reduction from the integers onto `ZMod 2` is
surjective. -/
lemma modTwoReduction_surjective :
    Function.Surjective (Int.castAddHom (ZMod 2)).toIntLinearMap := by
  -- Every residue class has its canonical integer representative.
  intro x
  exact ⟨ZMod.cast x, ZMod.intCast_zmod_cast x⟩

/-- Helper for Remark 60.1: the kernel of reduction modulo two consists
exactly of the multiples of two. -/
lemma two_mul_modTwo_functionExact :
    Function.Exact (LinearMap.lsmul ℤ ℤ 2)
      (Int.castAddHom (ZMod 2)).toIntLinearMap := by
  -- Express exactness elementwise as divisibility by two.
  intro x
  constructor
  · intro hx
    have hx' : (x : ZMod 2) = 0 := hx
    have hdiv : (2 : ℤ) ∣ x := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx'
    obtain ⟨y, rfl⟩ := hdiv
    exact ⟨y, by simp⟩
  · rintro ⟨y, rfl⟩
    change (((2 : ℤ) * y : ℤ) : ZMod 2) = 0
    rw [Int.cast_mul]
    change ((2 : ℤ) : ZMod 2) * (y : ZMod 2) = 0
    calc
      ((2 : ℤ) : ZMod 2) * (y : ZMod 2) = 0 * (y : ZMod 2) := by
        rw [show ((2 : ℤ) : ZMod 2) = 0 by decide]
      _ = 0 := zero_mul _

/-- Helper for Remark 60.1: the integral multiplication-by-two and mod-two
reduction coefficient sequence is short exact. -/
lemma integralModTwoCoefficientShortExact :
    integralModTwoCoefficientShortComplex.ShortExact := by
  -- Assemble exactness, injectivity, and surjectivity of the two coefficient maps.
  exact ModuleCat.shortComplex_shortExact integralModTwoCoefficientShortComplex
    two_mul_modTwo_functionExact two_mul_injective modTwoReduction_surjective

/-- Helper for Remark 60.1: multiplication by two remains injective after
postcomposition on singular cochains. -/
lemma singularTwoCoefficientMapComponent_injective (X : TopCat) (n : ℕ) :
    Function.Injective
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.f n) := by
  -- Test equality pointwise and cancel multiplication by two in `ℤ`.
  intro φ ψ hφψ
  apply LinearMap.ext
  intro x
  apply two_mul_injective
  exact DFunLike.congr_fun hφψ x

/-- Helper for Remark 60.1: reduction modulo two is surjective on singular
cochains because every singular-chain group is projective. -/
lemma singularModTwoCoefficientMapComponent_surjective (X : TopCat) (n : ℕ) :
    Function.Surjective
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.g n) := by
  -- Local instance justification (projectivity): the explicit coproduct proof
  -- and the named epimorphism avoid recursive inference through the two complexes.
  letI : Projective ((integralSingularChainComplex X).X n) :=
    integralSingularChainComplex_projective X n
  letI : Epi integralModTwoCoefficientShortComplex.g :=
    integralModTwoCoefficientShortExact.epi_g
  intro φ
  let lift := Projective.factorThru (ModuleCat.ofHom φ)
    integralModTwoCoefficientShortComplex.g
  refine ⟨lift.hom, ?_⟩
  change integralModTwoCoefficientShortComplex.g.hom.comp lift.hom = φ
  exact ModuleCat.hom_ext_iff.mp
    (Projective.factorThru_comp (ModuleCat.ofHom φ)
      integralModTwoCoefficientShortComplex.g)

/-- Helper for Remark 60.1: exactness of multiplication by two and mod-two
reduction is preserved on each singular-cochain group. -/
lemma singularTwoModTwoCoefficientMapComponent_exact (X : TopCat) (n : ℕ) :
    Function.Exact
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.f n)
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.g n) := by
  -- Local instance justification (projectivity): exact lifting uses the
  -- explicit coproduct proof and the named coefficient epimorphism.
  letI : Projective ((integralSingularChainComplex X).X n) :=
    integralSingularChainComplex_projective X n
  letI : Epi integralModTwoCoefficientShortComplex.g :=
    integralModTwoCoefficientShortExact.epi_g
  intro φ
  constructor
  · intro hφ
    have hzero :
        ModuleCat.ofHom φ ≫ integralModTwoCoefficientShortComplex.g = 0 := by
      apply ModuleCat.hom_ext
      change integralModTwoCoefficientShortComplex.g.hom.comp φ = 0
      exact hφ
    let lift := integralModTwoCoefficientShortExact.exact.liftFromProjective
      (ModuleCat.ofHom φ) hzero
    refine ⟨lift.hom, ?_⟩
    change integralModTwoCoefficientShortComplex.f.hom.comp lift.hom = φ
    exact ModuleCat.hom_ext_iff.mp
      (integralModTwoCoefficientShortExact.exact.liftFromProjective_comp
        (ModuleCat.ofHom φ) hzero)
  · rintro ⟨ψ, rfl⟩
    change integralModTwoCoefficientShortComplex.g.hom.comp
      (integralModTwoCoefficientShortComplex.f.hom.comp ψ) = 0
    rw [← LinearMap.comp_assoc]
    have hzero :
        integralModTwoCoefficientShortComplex.g.hom.comp
          integralModTwoCoefficientShortComplex.f.hom = 0 :=
      ModuleCat.hom_ext_iff.mp integralModTwoCoefficientShortComplex.zero
    rw [hzero, LinearMap.zero_comp]

/-- Helper for Remark 60.1: the two coefficient maps compose to zero as maps
of coefficient-valued singular cochain complexes. -/
lemma singularIntegralModTwoCoefficientCochainMap_comp (X : TopCat) :
    singularCoefficientCochainMap X integralModTwoCoefficientShortComplex.f ≫
      singularCoefficientCochainMap X integralModTwoCoefficientShortComplex.g = 0 := by
  -- Check the coefficient composite pointwise on every cochain and chain.
  ext n φ
  change ((integralSingularChainComplex X).X n →ₗ[ℤ] ℤ) at φ
  apply LinearMap.ext
  intro x
  change integralModTwoCoefficientShortComplex.g.hom
    (integralModTwoCoefficientShortComplex.f.hom (φ x)) = 0
  exact integralModTwoCoefficientShortComplex.moduleCat_zero_apply (φ x)

/-- Helper for Remark 60.1: the coefficient sequence
`ℤ --2→ ℤ → ZMod 2` applied to singular cochains. -/
abbrev singularCochainCoefficientShortComplex (X : TopCat) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk
    (singularCoefficientCochainMap X integralModTwoCoefficientShortComplex.f)
    (singularCoefficientCochainMap X integralModTwoCoefficientShortComplex.g)
    (singularIntegralModTwoCoefficientCochainMap_comp X)

/-- Helper for Remark 60.1: the integral-to-mod-two coefficient sequence of
singular cochain complexes is short exact. -/
lemma singularCochainCoefficientShortExact (X : TopCat) :
    (singularCochainCoefficientShortComplex X).ShortExact := by
  -- Degreewise short exactness follows from projectivity of singular chains.
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.f n)
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.g n)
    exact singularTwoModTwoCoefficientMapComponent_exact X n
  · change Function.Injective
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.f n)
    exact singularTwoCoefficientMapComponent_injective X n
  · change Function.Surjective
      (singularCoefficientMapComponent X
        integralModTwoCoefficientShortComplex.g n)
    exact singularModTwoCoefficientMapComponent_surjective X n

/-- Helper for Remark 60.1: singular cohomology with values in an arbitrary
integral coefficient module. -/
abbrev SingularCohomologyWithCoefficients
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ) : ModuleCat ℤ :=
  (singularCochainComplexWithCoefficients X M).homology n

/-- Helper for Remark 60.1: the degree-one-to-degree-two integral Bockstein
associated to reduction modulo two. -/
noncomputable def integralBockstein (X : TopCat) :
    SingularCohomologyWithCoefficients X (ModuleCat.of ℤ (ZMod 2)) 1 ⟶
      SingularCohomologyWithCoefficients X (ModuleCat.of ℤ ℤ) 2 :=
  (singularCochainCoefficientShortExact X).δ 1 2 (by simp)

/-- Helper for Remark 60.1: a mod-two degree-one class has zero Bockstein
exactly when it lifts to an integral degree-one class. -/
lemma integralBockstein_eq_zero_iff_lifts (X : TopCat)
    (a : SingularCohomologyWithCoefficients X (ModuleCat.of ℤ (ZMod 2)) 1) :
    integralBockstein X a = 0 ↔
      ∃ b : SingularCohomologyWithCoefficients X (ModuleCat.of ℤ ℤ) 1,
        HomologicalComplex.homologyMap
          (singularCoefficientCochainMap X
            integralModTwoCoefficientShortComplex.g) 1 b = a := by
  -- Read the lifting criterion directly from exactness before the connecting map.
  constructor
  · intro ha
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((singularCochainCoefficientShortExact X).homology_exact₃ 1 2 (by simp)) a ha
  · rintro ⟨b, rfl⟩
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp
        ((singularCochainCoefficientShortExact X).comp_δ 1 2 (by simp))) b

/-- Helper for Remark 60.1: coefficient multiplication by two induces twice
the identity map on the integral coefficient cochain complex. -/
lemma singularTwoCoefficientCochainMap_eq_two_nsmul_id (X : TopCat) :
    singularCoefficientCochainMap X integralModTwoCoefficientShortComplex.f =
      2 • 𝟙 (singularCochainComplexWithCoefficients X (ModuleCat.of ℤ ℤ)) := by
  -- Compare the cochain maps degreewise and evaluate on a chain.
  ext n φ
  change ((integralSingularChainComplex X).X n →ₗ[ℤ] ℤ) at φ
  apply LinearMap.ext
  intro x
  change (2 : ℤ) * φ x = (2 • φ) x
  simp

/-- Helper for Remark 60.1: the homology map induced by coefficient
multiplication by two acts as doubling. -/
lemma homologyMap_singularTwoCoefficientCochainMap_apply
    (X : TopCat) (n : ℕ)
    (a : SingularCohomologyWithCoefficients X (ModuleCat.of ℤ ℤ) n) :
    HomologicalComplex.homologyMap
      (singularCoefficientCochainMap X
        integralModTwoCoefficientShortComplex.f) n a = 2 • a := by
  -- Rewrite the chain map as a double identity and use additivity of homology.
  rw [singularTwoCoefficientCochainMap_eq_two_nsmul_id]
  simp only [two_nsmul, HomologicalComplex.homologyMap_add,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_add, ModuleCat.hom_id,
    LinearMap.add_apply, LinearMap.id_apply]

/-- Helper for Remark 60.1: every integral Bockstein class is annihilated by
two. -/
lemma two_nsmul_integralBockstein (X : TopCat)
    (a : SingularCohomologyWithCoefficients X (ModuleCat.of ℤ (ZMod 2)) 1) :
    2 • integralBockstein X a = 0 := by
  -- Exactness after the Bockstein says its coefficient-double vanishes.
  have hzero := DFunLike.congr_fun
    (ModuleCat.hom_ext_iff.mp
      ((singularCochainCoefficientShortExact X).δ_comp 1 2 (by simp))) a
  change HomologicalComplex.homologyMap
    (singularCoefficientCochainMap X
      integralModTwoCoefficientShortComplex.f) 2 (integralBockstein X a) = 0 at hzero
  rw [homologyMap_singularTwoCoefficientCochainMap_apply] at hzero
  exact hzero

/-- Helper for Remark 60.1: the coefficient-parametric and original integral
cochain groups have the same underlying linear-dual module. -/
def singularIntegralCoefficientCochainGroupIso (X : TopCat) (n : ℕ) :
    (singularCochainComplexWithCoefficients X (ModuleCat.of ℤ ℤ)).X n ≅
      (integralSingularCochainComplex X).X n :=
  Iso.refl _

/-- Helper for Remark 60.1: the integral coefficient-group comparison is the
identity on every cochain. -/
lemma singularIntegralCoefficientCochainGroupIso_hom_apply
    (X : TopCat) (n : ℕ)
    (φ : (singularCochainComplexWithCoefficients X (ModuleCat.of ℤ ℤ)).X n) :
    (singularIntegralCoefficientCochainGroupIso X n).hom φ = φ := by
  -- The comparison only aligns two spellings of the same linear-dual module.
  rfl

/-- Helper for Remark 60.1: the identity components intertwine the generic
integral-coefficient coboundary with the original integral dual coboundary. -/
lemma singularIntegralCoefficientCochainComplexIso_comm (X : TopCat)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (singularIntegralCoefficientCochainGroupIso X i).hom ≫
        (integralSingularCochainComplex X).d i j =
      (singularCochainComplexWithCoefficients X (ModuleCat.of ℤ ℤ)).d i j ≫
        (singularIntegralCoefficientCochainGroupIso X j).hom := by
  -- Adjacent differentials on both complexes evaluate by precomposition.
  simp only [ComplexShape.up_Rel] at hij
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change ((integralSingularChainComplex X).X i →ₗ[ℤ] ℤ) at φ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    singularIntegralCoefficientCochainGroupIso_hom_apply,
    integralSingularCochainComplex_d_apply,
    singularCochainComplexWithCoefficients_d_apply]

/-- Helper for Remark 60.1: the coefficient-parametric integral cochain
complex agrees with the original integral singular cochain complex. -/
def singularIntegralCoefficientCochainComplexIso (X : TopCat) :
    singularCochainComplexWithCoefficients X (ModuleCat.of ℤ ℤ) ≅
      integralSingularCochainComplex X :=
  HomologicalComplex.Hom.isoOfComponents
    (singularIntegralCoefficientCochainGroupIso X)
    (singularIntegralCoefficientCochainComplexIso_comm X)

/-- Helper for Remark 60.1: coefficient-parametric integral cohomology agrees
with the original integral singular cohomology in every degree. -/
def singularIntegralCoefficientCohomologyIso (X : TopCat) (n : ℕ) :
    SingularCohomologyWithCoefficients X (ModuleCat.of ℤ ℤ) n ≅
      IntegralSingularCohomology X n :=
  HomologicalComplex.homologyMapIso
    (singularIntegralCoefficientCochainComplexIso X) n

end AlgebraicTopology
