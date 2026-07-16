import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Remark_15_119_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_119_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_119_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ExteriorAlgebra
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace Module

/-- Helper for Lemma 15.123.1: an `R`-linear equivalence preserves the local rank function. -/
theorem rankAtStalk_eq_of_linearEquiv
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.rankAtStalk N p := by
  let A := Localization.AtPrime p.asIdeal
  let ep : LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal N :=
    LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  -- Proof comment: `rankAtStalk` is defined by the localized finite rank, so it is invariant
  -- under the localized equivalence induced by `e`.
  rw [Module.rankAtStalk_eq_finrank_tensorProduct (M := M) p,
    Module.rankAtStalk_eq_finrank_tensorProduct (M := N) p]
  calc
    Module.finrank A (TensorProduct R A M) =
        Module.finrank A (LocalizedModule.AtPrime p.asIdeal M) := by
          simpa [A] using
            (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm.finrank_eq
    _ = Module.finrank A (LocalizedModule.AtPrime p.asIdeal N) := ep.finrank_eq
    _ = Module.finrank A (TensorProduct R A N) := by
          simpa [A] using
            (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).finrank_eq

/-- Helper for Lemma 15.123.1: if two finite projective modules have the same local rank at every
prime, then the exterior-algebra image of a determinant element stays in the determinant line. -/
theorem map_det_mem_det_of_rankAtStalk_eq
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hMN : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (x : Module.det R M) :
    ExteriorAlgebra.map f (x : ExteriorAlgebra R M) ∈ Module.det R N := by
  -- TODO: follow the source route by localizing at each prime, identify both determinant lines
  -- with the corresponding top exterior powers via `det_eq_topExteriorPower_of_rankAtStalk_eq`,
  -- observe that `ExteriorAlgebra.map f` preserves degree there, and descend the membership.
  sorry

/-- Helper for Lemma 15.123.1: a surjection onto a finite projective module adds local ranks
across its kernel row. -/
theorem rankAtStalk_eq_ker_add_of_surjective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (p : PrimeSpectrum R) :
    Module.rankAtStalk M p =
      Module.rankAtStalk (LinearMap.ker f) p + Module.rankAtStalk N p := by
  obtain ⟨σ, hσ⟩ :=
    LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.2 hf)
  let r : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - σ.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      -- Proof comment: the splitting correction lands in the kernel because `σ` is a right
      -- inverse of `f`.
      rw [LinearMap.mem_ker]
      have hσ_apply : f (σ (f x)) = f x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ (f x)
      simp [LinearMap.sub_apply, LinearMap.comp_apply, hσ_apply])
  have hr : r.comp (LinearMap.ker f).subtype = LinearMap.id := by
    -- Proof comment: on a kernel element the correction term vanishes, so the retraction is the
    -- identity.
    ext x
    simp [r, sub_eq_add_neg, LinearMap.comp_apply]
  have hsurj_r : Function.Surjective r := by
    intro x
    refine ⟨x, ?_⟩
    simpa using LinearMap.congr_fun hr x
  let _ : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective r hsurj_r
  let _ : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r hr
  let e : (LinearMap.ker f × N) ≃ₗ[R] M := kernel_prod_equiv_of_rightInverse f σ hσ
  have hprod :
      Module.rankAtStalk (LinearMap.ker f × N) p =
        Module.rankAtStalk (LinearMap.ker f) p + Module.rankAtStalk N p := by
    let A := Localization.AtPrime p.asIdeal
    let _ : Module.Flat A (LocalizedModule.AtPrime p.asIdeal (LinearMap.ker f)) := inferInstance
    let _ : Module.Flat A (LocalizedModule.AtPrime p.asIdeal N) := inferInstance
    let _ : Module.Flat A (LocalizedModule.AtPrime p.asIdeal (LinearMap.ker f × N)) := inferInstance
    let _ : Module.Free A (LocalizedModule.AtPrime p.asIdeal (LinearMap.ker f)) :=
      Module.free_of_flat_of_isLocalRing
    let _ : Module.Free A (LocalizedModule.AtPrime p.asIdeal N) :=
      Module.free_of_flat_of_isLocalRing
    let _ : Module.Free A (LocalizedModule.AtPrime p.asIdeal (LinearMap.ker f × N)) :=
      Module.free_of_flat_of_isLocalRing
    let _ : Module.Free A (TensorProduct R A (LinearMap.ker f)) :=
      Module.Free.of_equiv
        (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (LinearMap.ker f))
    let _ : Module.Free A (TensorProduct R A N) :=
      Module.Free.of_equiv (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N)
    let _ : Module.Free A (TensorProduct R A (LinearMap.ker f × N)) :=
      Module.Free.of_equiv
        (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (LinearMap.ker f × N))
    -- Proof comment: after localizing, the split short exact row becomes a product decomposition,
    -- so the local rank is the sum of the two localized finranks.
    rw [Module.rankAtStalk_eq_finrank_tensorProduct (M := LinearMap.ker f × N) p,
      Module.rankAtStalk_eq_finrank_tensorProduct (M := LinearMap.ker f) p,
      Module.rankAtStalk_eq_finrank_tensorProduct (M := N) p]
    calc
      Module.finrank A (TensorProduct R A (LinearMap.ker f × N)) =
          Module.finrank A
            ((TensorProduct R A (LinearMap.ker f)) × TensorProduct R A N) := by
            simpa using
              (TensorProduct.prodRight R A A (LinearMap.ker f) N).finrank_eq
      _ = Module.finrank A (TensorProduct R A (LinearMap.ker f)) +
            Module.finrank A (TensorProduct R A N) := by
            simpa using
              (Module.finrank_prod
                (R := A)
                (M := TensorProduct R A (LinearMap.ker f))
                (M' := TensorProduct R A N))
  -- Proof comment: transport the split product decomposition back along the global linear
  -- equivalence `((ker f) × N) ≃ₗ M`.
  calc
    Module.rankAtStalk M p = Module.rankAtStalk (LinearMap.ker f × N) p := by
      symm
      exact Module.rankAtStalk_eq_of_linearEquiv e p
    _ = Module.rankAtStalk (LinearMap.ker f) p + Module.rankAtStalk N p := hprod

end Module

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.1:
- primary domain: bounded finite-projective cochain complexes of `R`-modules concentrated in
  degrees `-1` and `0`, together with the determinant-line comparison maps attached to short exact
  rows;
- sampled owner declarations of the same kind:
  `CochainComplex.of`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `determinantTensorIsoOfShortExact`,
  `determinantLineMap`;
- best owner abstraction:
  `core/canonical`: the owner is the underlying `CochainComplex (ModuleCat R) ℤ`, with the
    primitive data kept as finite/projective terms in degrees `-1` and `0`;
  `source-facing`: the admissibility hypotheses `(1)`, `(2)`, `(3)`, the rank-zero condition, and
    the determinant statement for a morphism of two-term complexes, with the support conditions
    `IsStrictlyGE (-1)` and `IsStrictlyLE 0` built into the owner-level API;
  `bridge/view`: the determinant comparison maps from Lemma `15.119.2` on the short exact kernel
    rows in degrees `-1` and `0`.
- primitive data: the cochain complexes themselves, their degreewise map, and the exactness data
  on the kernel rows, together with finite/projective hypotheses only in the degrees actually used;
- derived API: the determinant line, the canonical determinant element, the determinant map on a
  degreewise surjective morphism, and the rank-zero preservation theorem.

This file therefore removes the ad hoc two-term wrapper and works directly with the cochain complex
plus its primitive degree `-1/0` data.
-/

/-- The determinant line attached to a cochain complex supported in degrees `-1` and `0`. -/
abbrev determinantLine (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)] :=
  Module.det R (K.X (-1)) →ₗ[R] Module.det R (K.X 0)

/- Textbook surface notation for the determinant line of a two-term complex. -/
local notation3 "det(" K "^•)" => determinantLine K

instance determinantLineModule (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)] :
    Module R (det(K^•)) := by
  change Module R (Module.det R (K.X (-1)) →ₗ[R] Module.det R (K.X 0))
  let _ : Module R (Module.det R (K.X (-1))) := inferInstance
  let _ : AddCommGroup (Module.det R (K.X 0)) := inferInstance
  let _ : Module R (Module.det R (K.X 0)) := inferInstance
  let _ : IsScalarTower R R (Module.det R (K.X 0)) := inferInstance
  let _ : SMulCommClass R R (Module.det R (K.X 0)) := IsScalarTower.to_smulCommClass
  exact LinearMap.module

-- Proof sketch: a surjection onto a projective module splits, so its kernel is a direct summand
-- of the finite source module and hence finite.
private theorem finite_kernel_of_surjective {M N : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) := by
  obtain ⟨σ, hσ⟩ :=
    LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.2 hf)
  let r : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - σ.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      -- Proof comment: the correction term kills the image of `f` because `σ` is a right inverse.
      rw [LinearMap.mem_ker]
      have hσ_apply : f (σ (f x)) = f x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ (f x)
      simp [LinearMap.sub_apply, LinearMap.comp_apply, hσ_apply])
  have hr : r.comp (LinearMap.ker f).subtype = LinearMap.id := by
    -- Proof comment: on a kernel element the correction term vanishes, so the retraction is the
    -- identity after composing with the subtype map.
    ext x
    simp [r, sub_eq_add_neg, LinearMap.comp_apply]
  have hsurj_r : Function.Surjective r := by
    intro x
    refine ⟨x, ?_⟩
    simpa using LinearMap.congr_fun hr x
  exact Module.Finite.of_surjective r hsurj_r

-- Proof sketch: a surjection onto a projective module splits, and a direct summand of a
-- projective module is projective.
private theorem projective_kernel_of_surjective {M N : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨σ, hσ⟩ :=
    LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.2 hf)
  let r : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - σ.comp f).codRestrict (LinearMap.ker f) (by
      intro x
      -- Proof comment: the same correction term lands in the kernel because `σ` splits `f`.
      rw [LinearMap.mem_ker]
      have hσ_apply : f (σ (f x)) = f x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ (f x)
      simp [LinearMap.sub_apply, LinearMap.comp_apply, hσ_apply])
  have hr : r.comp (LinearMap.ker f).subtype = LinearMap.id := by
    -- Proof comment: restricting the retraction to the kernel gives the identity.
    ext x
    simp [r, sub_eq_add_neg, LinearMap.comp_apply]
  exact Module.Projective.of_split (LinearMap.ker f).subtype r hr

-- Proof sketch: apply the chain-map commutativity square in degrees `-1` and `0` to an element
-- of `ker(a^{-1})`.
/-- Helper for Lemma 15.123.1: restricting the chain-map square to `ker(a^{-1})` makes the degree
`0` component vanish. -/
private theorem kernel_square_vanishes_on_negOne_kernel {K L : Cpx} (a : K ⟶ L)
    (x : LinearMap.ker (a.f (-1)).hom) :
    (a.f 0).hom ((K.d (-1) 0).hom x) = 0 := by
  -- Route correction: instead of fighting subtype coercions directly inside `kernelDifferential`,
  -- first rewrite the chain-map square as an equality of linear maps and only then restrict to
  -- `ker(a^{-1})`.
  have hx : (a.f (-1)).hom x = 0 := x.2
  have hcomm_eval :
      (a.f 0).hom ((K.d (-1) 0).hom x) = (L.d (-1) 0).hom ((a.f (-1)).hom x) := by
    simpa only [LinearMap.comp_apply] using
      congrArg (fun f : K.X (-1) ⟶ L.X 0 ↦ f.hom x) (a.comm (-1) 0).symm
  calc
    (a.f 0).hom ((K.d (-1) 0).hom x) = (L.d (-1) 0).hom ((a.f (-1)).hom x) := hcomm_eval
    _ = 0 := by simp [hx]

/-- The differential of a morphism of cochain complexes carries `ker(a^{-1})` into `ker(a^0)`. -/
theorem kernelDifferential_mem {K L : Cpx} (a : K ⟶ L)
    (x : LinearMap.ker (a.f (-1)).hom) :
    (K.d (-1) 0).hom x ∈ LinearMap.ker (a.f 0).hom := by
  -- Proof comment: the restricted commutative square shows that the image under the differential
  -- is annihilated by `a.f 0`.
  rw [LinearMap.mem_ker]
  exact kernel_square_vanishes_on_negOne_kernel a x

/-- The differential on the kernel complex attached to a morphism in degrees `-1` and `0`. -/
def kernelDifferential {K L : Cpx} (a : K ⟶ L) :
    LinearMap.ker (a.f (-1)).hom →ₗ[R] LinearMap.ker (a.f 0).hom :=
  LinearMap.codRestrict
    (LinearMap.ker (a.f 0).hom)
    ((K.d (-1) 0).hom.comp (LinearMap.ker (a.f (-1)).hom).subtype)
    (kernelDifferential_mem a)

/-- The Stacks Project hypotheses `(1)`, `(2)`, `(3)` on a morphism in degrees `-1` and `0`:
surjectivity in those degrees, together with acyclicity of the kernel complex expressed by
bijectivity of its differential. -/
structure IsAdmissible {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    (a : K ⟶ L) : Prop where
  mapNegOne_surjective : Function.Surjective (a.f (-1)).hom
  mapZero_surjective : Function.Surjective (a.f 0).hom
  kernelDifferential_bijective : Function.Bijective (kernelDifferential a)

/-- Admissibility is stable under composition. -/
theorem IsAdmissible.comp {K L M : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [M.IsStrictlyGE (-1)] [M.IsStrictlyLE 0]
    {a : K ⟶ L} {b : L ⟶ M} (ha : IsAdmissible a) (hb : IsAdmissible b) :
    IsAdmissible (a ≫ b) := by
  -- TODO: prove the kernel differential of the composite is bijective by showing:
  -- injectivity reduces to the injectivity of the kernel differentials of `b` and `a`, while
  -- surjectivity is obtained by lifting through `hb` and correcting the residual kernel term
  -- through `ha`.
  sorry

/-- A cochain complex has rank `0` in degrees `-1` and `0` if those terms have the same local rank
at every point of `Spec R`. -/
def IsRankZero (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0] : Prop :=
  ∀ p : PrimeSpectrum R, Module.rankAtStalk (K.X (-1)) p = Module.rankAtStalk (K.X 0) p

-- Proof sketch: on a rank-zero two-term complex, the differential induces the canonical map on
-- determinant lines coming from exterior-algebra functoriality in top degree.
/-- The exterior-algebra map of the differential lands in the determinant line of degree `0` when
the complex has rank `0` in degrees `-1` and `0`. -/
theorem canonicalElement_mem {K : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hK : IsRankZero K)
    (x : Module.det R (K.X (-1))) :
    ExteriorAlgebra.map (K.d (-1) 0).hom (x : ExteriorAlgebra R (K.X (-1))) ∈
      Module.det R (K.X 0) := by
  -- Proof comment: the only input needed here is that the two terms have the same local rank, so
  -- the general determinant-image lemma applies directly to the differential.
  exact Module.map_det_mem_det_of_rankAtStalk_eq (f := (K.d (-1) 0).hom) hK x

/-- The canonical determinant element `δ(K^•)` attached to a rank-zero cochain complex supported in
degrees `-1` and `0`. -/
def canonicalElement (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hK : IsRankZero K) :
    det(K^•) :=
  LinearMap.codRestrict
    (Module.det R (K.X 0))
    ((ExteriorAlgebra.map (K.d (-1) 0).hom).toLinearMap.comp (Module.det R (K.X (-1))).subtype)
    (canonicalElement_mem hK)

/- Textbook surface notation for the canonical determinant element of a rank-zero two-term
complex. -/
local notation3 "δ(" K "^•; " hK ")" => canonicalElement K hK

/-- Helper for Lemma 15.123.1: when the two-term differential is bijective, the canonical
determinant element is exactly the determinant-line map induced by that differential. -/
private theorem canonicalElement_eq_determinantLineMap_of_bijective
    {K : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hd : Function.Bijective (K.d (-1) 0).hom) (hK : IsRankZero K) :
    canonicalElement K hK =
      (determinantLineMap (LinearEquiv.ofBijective (K.d (-1) 0).hom hd)).toLinearMap := by
  -- Proof comment: both determinant-line elements are defined by the same exterior-algebra map;
  -- the only difference is that `canonicalElement` packages membership via `hK`.
  ext x
  change
    (ExteriorAlgebra.map (K.d (-1) 0).hom (x : ExteriorAlgebra R (K.X (-1))) :
      ExteriorAlgebra R (K.X 0)) =
      (determinantLineMap (LinearEquiv.ofBijective (K.d (-1) 0).hom hd) x :
        ExteriorAlgebra R (K.X 0))
  rw [determinantLineMap_apply]
  rfl

private noncomputable def determinantMapApply {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (φ : det(L^•)) :
    det(K^•) :=
  let _ : Module.Finite R (LinearMap.ker (a.f (-1)).hom) :=
    finite_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  let _ : Module.Projective R (LinearMap.ker (a.f (-1)).hom) :=
    projective_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  let _ : Module.Finite R (LinearMap.ker (a.f 0).hom) :=
    finite_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  let _ : Module.Projective R (LinearMap.ker (a.f 0).hom) :=
    projective_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  let kerDet :=
    determinantLineMap
      (LinearEquiv.ofBijective
        (kernelDifferential a)
        ha.kernelDifferential_bijective)
  let detNeg :=
    determinantTensorIsoOfShortExact
      (LinearMap.ker (a.f (-1)).hom).subtype
      (a.f (-1)).hom
      (LinearMap.ker (a.f (-1)).hom).injective_subtype
      ha.mapNegOne_surjective
      (LinearMap.exact_subtype_ker_map (a.f (-1)).hom)
  let detZero :=
    determinantTensorIsoOfShortExact
      (LinearMap.ker (a.f 0).hom).subtype
      (a.f 0).hom
      (LinearMap.ker (a.f 0).hom).injective_subtype
      ha.mapZero_surjective
      (LinearMap.exact_subtype_ker_map (a.f 0).hom)
  detZero.toLinearMap.comp
    ((TensorProduct.map kerDet.toLinearMap φ).comp detNeg.symm.toLinearMap)

/-- Helper for Lemma 15.123.1: tensoring by a fixed left map respects addition in the right map. -/
private theorem tensorProduct_map_right_add
    {A B C D : Type*}
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid D] [Module R D]
    (f : A →ₗ[R] B) (g h : C →ₗ[R] D) :
    TensorProduct.map f (g + h) = TensorProduct.map f g + TensorProduct.map f h := by
  -- Proof comment: equality is checked on pure tensors and then extended linearly.
  ext a c
  simp [TensorProduct.map, TensorProduct.tmul_add]

/-- Helper for Lemma 15.123.1: tensoring by a fixed left map respects scalar multiplication in the
right map. -/
private theorem tensorProduct_map_right_smul
    {A B C D : Type*}
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid D] [Module R D]
    (f : A →ₗ[R] B) (r : R) (g : C →ₗ[R] D) :
    TensorProduct.map f (r • g) = r • TensorProduct.map f g := by
  -- Proof comment: scalar compatibility is also visible on pure tensors.
  ext a c
  simp [TensorProduct.map]

/-- Helper for Lemma 15.123.1: tensoring by a fixed linear map on the left is linear in the right
input map. -/
private noncomputable def tensorProduct_map_right_linear
    {A B C D : Type*}
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid D] [Module R D]
    (f : A →ₗ[R] B) :
    (C →ₗ[R] D) →ₗ[R] ((A ⊗[R] C) →ₗ[R] (B ⊗[R] D)) where
  toFun g := TensorProduct.map f g
  map_add' := tensorProduct_map_right_add (R := R) f
  map_smul' := tensorProduct_map_right_smul (R := R) f

/-- Helper for Lemma 15.123.1: package the determinant comparison as a composition of genuine
`Hom`-space equivalences, so bijectivity is reduced to invertibility of the determinant line of the
kernel row. -/
private noncomputable def determinantMapLinearEquiv {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    det(L^•) ≃ₗ[R] det(K^•) :=
  -- TODO: package the source-faithful determinant comparison as the composition of the tensor-side
  -- short exact equivalences and the kernel determinant-line equivalence, with explicit arrow-space
  -- transports that avoid the current `rTensorEquiv` elaboration timeout.
  sorry

/-- Helper for Lemma 15.123.1: the determinant comparison is the underlying linear map of the
packaged `Hom`-space equivalence. -/
private noncomputable def determinantMapLinear {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    det(L^•) →ₗ[R] det(K^•) where
  toFun := determinantMapApply a ha
  map_add' φ ψ := by
    -- Proof comment: the source-faithful determinant comparison is linear in the input
    -- determinant-line map because the only varying term is `TensorProduct.map _ φ`.
    ext x
    simp only [determinantMapApply, tensorProduct_map_right_add, LinearMap.add_comp,
      LinearMap.comp_add, LinearMap.add_apply]
  map_smul' r φ := by
    -- Proof comment: scalar multiplication is handled by the same tensor-side linearity in the
    -- right map variable.
    ext x
    simp only [determinantMapApply, tensorProduct_map_right_smul, LinearMap.comp_smul,
      LinearMap.smul_comp, LinearMap.smul_apply]

private theorem determinantMapLinear_bijective {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    Function.Bijective (determinantMapLinear a ha) := by
  -- TODO: once `determinantMapLinearEquiv` is rebuilt from standard `Hom`-space equivalences,
  -- this bijectivity statement should be discharged by the explicit inverse on the determinant
  -- comparison map `determinantMapApply`.
  sorry

/-- The canonical determinant isomorphism `det(a^•) : det(K^•) → det(L^•)` attached to an
admissible morphism. -/
noncomputable def determinantIso {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    det(K^•) ≃ₗ[R] det(L^•) :=
  (LinearEquiv.ofBijective (determinantMapLinear a ha)
    (determinantMapLinear_bijective a ha)).symm

/- Textbook surface notation for the canonical determinant isomorphism of an admissible morphism of
two-term complexes. -/
local notation3 "det(" a "^•; " ha ")" => determinantIso a ha

/-- Bridge/view: the determinant map attached to an admissible morphism, viewed contravariantly as
an `R`-linear map `det(L^•) → det(K^•)`. -/
abbrev determinantMap {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    det(L^•) →ₗ[R] det(K^•) :=
  (det(a^•; ha)).symm.toLinearMap

/-- Helper for Lemma 15.123.1: after unfolding the canonical determinant isomorphism, evaluating
the contravariant bridge/view `determinantMap` on a determinant-line element recovers the explicit
tensor-side comparison `determinantMapApply`. -/
@[simp] private theorem determinantMap_apply_eq_determinantMapApply {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (φ : det(L^•)) :
    ((determinantMap a ha) φ : det(K^•)) = determinantMapApply a ha φ := rfl

/-- Bridge/view: the contravariant determinant map is the inverse linear map of the canonical
determinant isomorphism. -/
@[simp] theorem determinantIso_symm_toLinearMap {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    (det(a^•; ha)).symm.toLinearMap = determinantMap a ha := rfl

/-- Helper for Lemma 15.123.1: admissibility identifies the two kernel rows by a linear
equivalence, hence their local ranks agree pointwise. -/
private theorem kernel_rankAtStalk_eq_of_admissible
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (p : PrimeSpectrum R) :
    Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p =
      Module.rankAtStalk (LinearMap.ker (a.f 0).hom) p := by
  let e : LinearMap.ker (a.f (-1)).hom ≃ₗ[R] LinearMap.ker (a.f 0).hom :=
    LinearEquiv.ofBijective (kernelDifferential a) ha.kernelDifferential_bijective
  -- Proof comment: local rank is invariant under the localized equivalence induced by the kernel
  -- differential.
  exact Module.rankAtStalk_eq_of_linearEquiv e p

/-- Helper for Lemma 15.123.1: composing the restricted kernel differential with the target kernel
subtype recovers the original differential on degree `-1`. -/
private theorem kernelDifferential_subtype_comp {K L : Cpx} (a : K ⟶ L) :
    (LinearMap.ker (a.f 0).hom).subtype.comp (kernelDifferential a) =
      (K.d (-1) 0).hom.comp (LinearMap.ker (a.f (-1)).hom).subtype := by
  -- Proof comment: `kernelDifferential` is obtained from `K.d (-1) 0` by codomain restriction to
  -- the target kernel, so forgetting that restriction gives back the original composite.
  ext x
  rfl

-- Proof sketch: compare the split exact rows
-- `0 → ker(a^{-1}) → K^{-1} → L^{-1} → 0` and
-- `0 → ker(a^{0}) → K^{0} → L^{0} → 0`. Since the kernel differential is bijective, the kernel
-- complex has rank `0`, so the source and target rank functions differ by zero.
/-- A morphism satisfying the determinant-complex hypotheses preserves the rank-zero condition from
target to source. -/
theorem isRankZero_source_of_rankZero_target {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (hL : IsRankZero L) : IsRankZero K := by
  -- Route correction: follow the source proof literally by expanding the two short exact kernel
  -- rows and cancelling the equal kernel ranks coming from admissibility.
  intro p
  calc
    Module.rankAtStalk (K.X (-1)) p
        = Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p
            + Module.rankAtStalk (L.X (-1)) p := by
          exact Module.rankAtStalk_eq_ker_add_of_surjective (f := (a.f (-1)).hom)
            ha.mapNegOne_surjective p
    _ = Module.rankAtStalk (LinearMap.ker (a.f 0).hom) p
          + Module.rankAtStalk (L.X (-1)) p := by
          rw [kernel_rankAtStalk_eq_of_admissible a ha p]
    _ = Module.rankAtStalk (LinearMap.ker (a.f 0).hom) p
          + Module.rankAtStalk (L.X 0) p := by
          rw [hL p]
    _ = Module.rankAtStalk (K.X 0) p := by
          symm
          exact Module.rankAtStalk_eq_ker_add_of_surjective (f := (a.f 0).hom)
            ha.mapZero_surjective p

/-- Helper for Lemma 15.123.1: the source-faithful tensor-side short-exact argument gives the
contravariant determinant comparison on canonical elements. -/
private theorem determinantMap_maps_canonicalElement_of_rankZero_target_aux
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (hL : IsRankZero L) :
    determinantMap a ha (δ(L^•; hL)) =
      δ(K^•; isRankZero_source_of_rankZero_target a ha hL) := by
  let hK := isRankZero_source_of_rankZero_target a ha hL
  let _ : Module.Finite R (LinearMap.ker (a.f (-1)).hom) :=
    finite_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  let _ : Module.Projective R (LinearMap.ker (a.f (-1)).hom) :=
    projective_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  let _ : Module.Finite R (LinearMap.ker (a.f 0).hom) :=
    finite_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  let _ : Module.Projective R (LinearMap.ker (a.f 0).hom) :=
    projective_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  let kerDet :=
    determinantLineMap
      (LinearEquiv.ofBijective
        (kernelDifferential a)
        ha.kernelDifferential_bijective)
  let detNeg :=
    determinantTensorIsoOfShortExact
      (LinearMap.ker (a.f (-1)).hom).subtype
      (a.f (-1)).hom
      (LinearMap.ker (a.f (-1)).hom).injective_subtype
      ha.mapNegOne_surjective
      (LinearMap.exact_subtype_ker_map (a.f (-1)).hom)
  let detZero :=
    determinantTensorIsoOfShortExact
      (LinearMap.ker (a.f 0).hom).subtype
      (a.f 0).hom
      (LinearMap.ker (a.f 0).hom).injective_subtype
      ha.mapZero_surjective
      (LinearMap.exact_subtype_ker_map (a.f 0).hom)
  -- Proof comment: rewrite the published contravariant map as the explicit tensor-side composite
  -- and then verify the source proof on the tensor domain, reducing to pure tensors.
  ext x
  -- Route correction: rewrite on applications of `determinantMap`; the old whole-map equality
  -- forced a coercion-heavy `change` step.
  rw [determinantMap_apply_eq_determinantMapApply (a := a) (ha := ha) (φ := δ(L^•; hL))]
  have htensor :
      ∀ t :
          Module.det R (LinearMap.ker (a.f (-1)).hom) ⊗[R]
            Module.det R (L.X (-1)),
        detZero (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL)) t) =
          δ(K^•; hK) (detNeg t) := by
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · -- Proof comment: both sides are linear maps on the tensor product, so the zero tensor maps
      -- to zero.
      simp
    · intro xker xL
      ext
      have hsurjNeg :
          Function.Surjective
            (ExteriorAlgebra.map (a.f (-1)).hom) :=
        (ExteriorAlgebra.map_surjective_iff).2 ha.mapNegOne_surjective
      obtain ⟨yNeg, hyNeg⟩ := hsurjNeg (xL : ExteriorAlgebra R (L.X (-1)))
      have hker :
          ExteriorAlgebra.map (LinearMap.ker (a.f 0).hom).subtype
              ((kerDet xker : Module.det R (LinearMap.ker (a.f 0).hom)) :
                ExteriorAlgebra R (LinearMap.ker (a.f 0).hom)) =
            ExteriorAlgebra.map (K.d (-1) 0).hom
              (ExteriorAlgebra.map (LinearMap.ker (a.f (-1)).hom).subtype
                (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom))) := by
        -- Proof comment: the determinant factor on the kernel row is the determinant-line map of
        -- the kernel differential, and forgetting the codomain restriction recovers `d_K`.
        calc
          ExteriorAlgebra.map (LinearMap.ker (a.f 0).hom).subtype
              ((kerDet xker : Module.det R (LinearMap.ker (a.f 0).hom)) :
                ExteriorAlgebra R (LinearMap.ker (a.f 0).hom)) =
            ExteriorAlgebra.map (LinearMap.ker (a.f 0).hom).subtype
              (ExteriorAlgebra.map (kernelDifferential a)
                (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom))) := by
              rw [determinantLineMap_apply]
          _ =
            ExteriorAlgebra.map
              ((LinearMap.ker (a.f 0).hom).subtype.comp (kernelDifferential a))
              (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom)) := by
              simpa using
                congrArg
                  (fun ψ :
                      ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom) →ₐ[R]
                        ExteriorAlgebra R (K.X 0) ↦
                    ψ (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom)))
                  (ExteriorAlgebra.map_comp_map
                    (kernelDifferential a)
                    (LinearMap.ker (a.f 0).hom).subtype)
          _ =
            ExteriorAlgebra.map
              ((K.d (-1) 0).hom.comp (LinearMap.ker (a.f (-1)).hom).subtype)
              (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom)) := by
              rw [kernelDifferential_subtype_comp a]
          _ =
            ExteriorAlgebra.map (K.d (-1) 0).hom
              (ExteriorAlgebra.map (LinearMap.ker (a.f (-1)).hom).subtype
                (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom))) := by
              simpa using
                congrArg
                  (fun ψ :
                      ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom) →ₐ[R]
                        ExteriorAlgebra R (K.X 0) ↦
                    ψ (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom)))
                  (ExteriorAlgebra.map_comp_map
                    (LinearMap.ker (a.f (-1)).hom).subtype
                    (K.d (-1) 0).hom).symm
      have hyZero :
          ExteriorAlgebra.map (a.f 0).hom
              (ExteriorAlgebra.map (K.d (-1) 0).hom yNeg) =
            ((δ(L^•; hL) xL : Module.det R (L.X 0)) :
              ExteriorAlgebra R (L.X 0)) := by
        -- Proof comment: the differential of a chosen lift in degree `-1` is a lift of the image
        -- under `δ(L^•)` because the square of the chain map commutes.
        calc
          ExteriorAlgebra.map (a.f 0).hom
              (ExteriorAlgebra.map (K.d (-1) 0).hom yNeg) =
            ExteriorAlgebra.map ((a.f 0).hom.comp (K.d (-1) 0).hom) yNeg := by
              simpa using
                congrArg
                  (fun ψ :
                      ExteriorAlgebra R (K.X (-1)) →ₐ[R]
                        ExteriorAlgebra R (L.X 0) ↦ ψ yNeg)
                  (ExteriorAlgebra.map_comp_map
                    (K.d (-1) 0).hom
                    (a.f 0).hom)
          _ = ExteriorAlgebra.map ((L.d (-1) 0).hom.comp (a.f (-1)).hom) yNeg := by
              congr 1
              simpa using congrArg ModuleCat.Hom.hom (a.comm (-1) 0).symm
          _ =
            ExteriorAlgebra.map (L.d (-1) 0).hom
              (ExteriorAlgebra.map (a.f (-1)).hom yNeg) := by
              simpa using
                congrArg
                  (fun ψ :
                      ExteriorAlgebra R (K.X (-1)) →ₐ[R]
                        ExteriorAlgebra R (L.X 0) ↦ ψ yNeg)
                  (ExteriorAlgebra.map_comp_map
                    (a.f (-1)).hom
                    (L.d (-1) 0).hom).symm
          _ =
            ExteriorAlgebra.map (L.d (-1) 0).hom
              (xL : ExteriorAlgebra R (L.X (-1))) := by
              rw [hyNeg]
          _ =
            ((δ(L^•; hL) xL : Module.det R (L.X 0)) :
              ExteriorAlgebra R (L.X 0)) := rfl
      have hneg :=
        determinantTensorIsoOfShortExact_spec
          (LinearMap.ker (a.f (-1)).hom).subtype
          (a.f (-1)).hom
          (LinearMap.ker (a.f (-1)).hom).injective_subtype
          ha.mapNegOne_surjective
          (LinearMap.exact_subtype_ker_map (a.f (-1)).hom)
          xker
          xL
          yNeg
          hyNeg
      have hzero :=
        determinantTensorIsoOfShortExact_spec
          (LinearMap.ker (a.f 0).hom).subtype
          (a.f 0).hom
          (LinearMap.ker (a.f 0).hom).injective_subtype
          ha.mapZero_surjective
          (LinearMap.exact_subtype_ker_map (a.f 0).hom)
          (kerDet xker)
          (δ(L^•; hL) xL)
          (ExteriorAlgebra.map (K.d (-1) 0).hom yNeg)
          hyZero
      -- Proof comment: both routes around the kernel-row square are the same wedge expression in
      -- `ExteriorAlgebra R (K.X 0)`.
      change
        ((detZero
            (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL))
              (xker ⊗ₜ[R] xL)) :
              Module.det R (K.X 0)) : ExteriorAlgebra R (K.X 0)) =
          ((δ(K^•; hK) (detNeg (xker ⊗ₜ[R] xL)) :
              Module.det R (K.X 0)) : ExteriorAlgebra R (K.X 0))
      calc
        ((detZero
            (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL))
              (xker ⊗ₜ[R] xL)) :
              Module.det R (K.X 0)) : ExteriorAlgebra R (K.X 0)) =
          ExteriorAlgebra.map (LinearMap.ker (a.f 0).hom).subtype
              ((kerDet xker : Module.det R (LinearMap.ker (a.f 0).hom)) :
                ExteriorAlgebra R (LinearMap.ker (a.f 0).hom)) *
            ExteriorAlgebra.map (K.d (-1) 0).hom yNeg := by
              simpa using hzero
        _ =
          ExteriorAlgebra.map (K.d (-1) 0).hom
              (ExteriorAlgebra.map (LinearMap.ker (a.f (-1)).hom).subtype
                (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom))) *
            ExteriorAlgebra.map (K.d (-1) 0).hom yNeg := by
              rw [hker]
        _ =
          ExteriorAlgebra.map (K.d (-1) 0).hom
              (ExteriorAlgebra.map (LinearMap.ker (a.f (-1)).hom).subtype
                (xker : ExteriorAlgebra R (LinearMap.ker (a.f (-1)).hom)) * yNeg) := by
              rw [← map_mul]
        _ =
          ExteriorAlgebra.map (K.d (-1) 0).hom
              ((detNeg (xker ⊗ₜ[R] xL) : Module.det R (K.X (-1))) :
                ExteriorAlgebra R (K.X (-1))) := by
              rw [hneg]
        _ =
          ((δ(K^•; hK) (detNeg (xker ⊗ₜ[R] xL)) :
              Module.det R (K.X 0)) : ExteriorAlgebra R (K.X 0)) := rfl
    · intro t₁ t₂ ht₁ ht₂
      calc
        detZero (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL)) (t₁ + t₂)) =
          detZero (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL)) t₁) +
            detZero (TensorProduct.map kerDet.toLinearMap (δ(L^•; hL)) t₂) := by
              simp
        _ = δ(K^•; hK) (detNeg t₁) + δ(K^•; hK) (detNeg t₂) := by
              rw [ht₁, ht₂]
        _ = δ(K^•; hK) (detNeg (t₁ + t₂)) := by
              simp
  simpa using htensor (detNeg.symm x)

-- Proof sketch: apply Lemma `15.119.3` to the two short exact kernel rows. The determinant
-- isomorphism of `a` is obtained by inserting the determinant element of the acyclic kernel
-- complex, and that element is the unit because the kernel differential is an isomorphism.
/-- Lemma 15.123.1: let `a^• : K^• → L^•` be an admissible morphism of bounded finite-projective
cochain complexes concentrated in degrees `-1` and `0`. If `L^•` has rank `0`, then the canonical
determinant isomorphism `det(a^•) : det(K^•) → det(L^•)` sends the canonical element `δ(K^•)` to
`δ(L^•)`. -/
theorem determinantIso_maps_canonicalElement_of_rankZero_target
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (hL : IsRankZero L) :
    det(a^•; ha)
        (δ(K^•; isRankZero_source_of_rankZero_target a ha hL)) =
      δ(L^•; hL) := by
  -- Proof comment: once the tensor-side comparison is known, the published covariant statement is
  -- just `LinearEquiv.symm_apply_eq`.
  have haux := determinantMap_maps_canonicalElement_of_rankZero_target_aux a ha hL
  change (det(a^•; ha)).symm (δ(L^•; hL)) =
      δ(K^•; isRankZero_source_of_rankZero_target a ha hL) at haux
  exact ((det(a^•; ha)).symm_apply_eq.1 haux).symm

/-- Bridge/view: applying the inverse of `determinantIso` recovers the contravariant formulation
`det(L^•) → det(K^•)` of Lemma 15.123.1. -/
theorem determinantMap_maps_canonicalElement_of_rankZero_target
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (hL : IsRankZero L) :
    (det(a^•; ha)).symm (δ(L^•; hL)) =
      δ(K^•; isRankZero_source_of_rankZero_target a ha hL) := by
  -- Proof comment: this is exactly the covariant statement with `det(a^•; ha)` moved across the
  -- equivalence by applying its inverse.
  refine (det(a^•; ha)).symm_apply_eq.2 ?_
  exact (determinantIso_maps_canonicalElement_of_rankZero_target a ha hL).symm

end CochainComplex

end

/- Exported textbook notation for the determinant line of a two-term complex. -/
notation3 "det(" K "^•)" => CochainComplex.determinantLine K

/- Exported textbook notation for the canonical determinant element of a rank-zero two-term
complex. -/
notation3 "δ(" K "^•; " hK ")" => CochainComplex.canonicalElement K hK

/- Exported textbook notation for the canonical determinant isomorphism of an admissible morphism of
two-term complexes. -/
notation3 "det(" a "^•; " ha ")" => CochainComplex.determinantIso a ha
