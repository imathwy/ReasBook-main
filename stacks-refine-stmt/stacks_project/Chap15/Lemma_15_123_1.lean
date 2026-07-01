import Mathlib
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_119_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ExteriorAlgebra
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

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
    Module.Finite R (LinearMap.ker f) := sorry

-- Proof sketch: a surjection onto a projective module splits, and a direct summand of a
-- projective module is projective.
private theorem projective_kernel_of_surjective {M N : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Projective R (LinearMap.ker f) := sorry

-- Proof sketch: apply the chain-map commutativity square in degrees `-1` and `0` to an element
-- of `ker(a^{-1})`.
/-- The differential of a morphism of cochain complexes carries `ker(a^{-1})` into `ker(a^0)`. -/
theorem kernelDifferential_mem {K L : Cpx} (a : K ⟶ L)
    (x : LinearMap.ker (a.f (-1)).hom) :
    (K.d (-1) 0).hom x ∈ LinearMap.ker (a.f 0).hom := sorry

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
    IsAdmissible (a ≫ b) := sorry

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
      Module.det R (K.X 0) := sorry

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

private noncomputable def determinantMapLinear {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    det(L^•) →ₗ[R] det(K^•) :=
  { toFun := determinantMapApply a ha
    map_add' := by
      sorry
    map_smul' := by
      sorry }

private theorem determinantMapLinear_bijective {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    Function.Bijective (determinantMapLinear a ha) := by
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
    (a : K ⟶ L) (ha : IsAdmissible a) (hL : IsRankZero L) : IsRankZero K := sorry

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
      δ(L^•; hL) := sorry

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
  sorry

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
