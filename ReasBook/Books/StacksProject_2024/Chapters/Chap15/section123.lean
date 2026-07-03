import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_123_1 (from Chap15) -/
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

/-! ### Lemma_15_123_2 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.2:
- primary domain: determinant maps of admissible morphisms between bounded finite-projective
  two-term cochain complexes, and invariance of those maps under chain homotopy;
- sampled owner declarations of the same kind:
  `_root_.Homotopy`,
  `_root_.Homotopy.dNext_eq`,
  `determinantMap`,
  `determinantIso`;
- best owner abstraction:
  `core/canonical`: the homotopy datum should be owned by `_root_.Homotopy a b`, and the
    determinant comparison should be stated using the chapter owner `determinantMap`;
  `source-facing`: the Stacks statement that chain-homotopic admissible perturbations induce the
    same determinant map;
  `bridge/view`: in these degrees a homotopy is equivalently determined by its degree-`0`
    component `K.X 0 ⟶ L.X (-1)`, while `determinantMap` is the contravariant view of
    `determinantIso`.
- primitive data: the two morphisms `a`, `b`, their admissibility witnesses, and a chain homotopy
  `_root_.Homotopy a b`;
- derived API: the degree `-1/0` perturbation formulas and the expanded inverse linear map
  `(determinantIso _ _).symm.toLinearMap`, so those should not remain primitive public input or
  output data here.
-/

-- Proof sketch: locally on `Spec R`, the homotopy perturbation is given by conjugating the short
-- exact kernel rows by automorphisms of the middle terms. Lemma `15.119.6` then identifies the
-- determinant contributions of `a` and `b`.
/-- Lemma 15.123.2: if `a^•, b^• : K^• → L^•` are chain-homotopic, both satisfy the
determinant-complex hypotheses, and the degree maps are surjective, then the attached determinant
maps `det(L^•) → det(K^•)` agree. For two-term complexes concentrated in degrees `-1` and `0`,
this homotopy is equivalently determined by its single component `K^0 → L^{-1}`. -/
theorem determinantMap_eq_of_chainHomotopic_surjective_perturbation
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a b : K ⟶ L) (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b) :
    determinantMap b hb = determinantMap a ha := sorry

end CochainComplex

end

/-! ### Lemma_15_123_3 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.3:
- primary domain: determinant-line comparison maps attached to admissible morphisms of bounded
  finite-projective two-term cochain complexes;
- sampled owner declarations:
  `determinantIso`,
  `determinantMap`,
  `determinantTensorIsoOfShortExact`,
  `determinant_tensor_iso_tower_commutes`;
- best owner abstraction:
  `core/canonical`: the determinant comparison maps are built from the short-exact-sequence owner
    `determinantTensorIsoOfShortExact` and its naturality/tower compatibilities;
  `source-facing`: multiplicativity of the canonical determinant isomorphism `det(a^•)` for
    composable admissible morphisms of two-term complexes;
  `bridge/view`: the contravariant map `determinantMap`, identified as the inverse linear map of
    `determinantIso`.
- primitive data: the composable morphisms `a`, `b` and admissibility of `a` and `b`;
- derived API: admissibility of `a ≫ b` via `IsAdmissible.comp`, together with the explicit
  degreewise formulas for `(a ≫ b).f (-1)` and `(a ≫ b).f 0`, so none of this should remain
  separate public input data.
-/

section

variable {K L M : Cpx}
variable [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
variable [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
variable [M.IsStrictlyGE (-1)] [M.IsStrictlyLE 0]
variable [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
variable [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
variable [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
variable [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
variable [Module.Finite R (M.X (-1))] [Module.Projective R (M.X (-1))]
variable [Module.Finite R (M.X 0)] [Module.Projective R (M.X 0)]

-- Proof sketch: apply Lemmas `15.119.2`, `15.119.3`, and `15.119.4` to the short exact kernel rows
-- in degrees `-1` and `0` for `a`, `b`, and `a ≫ b`. The determinant tensor compatibilities
-- identify the determinant isomorphism of the composite with the composite of the determinant
-- isomorphisms.
/-- Lemma 15.123.3: for composable admissible morphisms of two-term bounded finite-projective
complexes, the canonical determinant isomorphism of the composite is the composite of the
canonical determinant isomorphisms `det(K^•) → det(L^•) → det(M^•)`. -/
theorem determinantIso_comp
    (a : K ⟶ L) (ha : IsAdmissible a) (b : L ⟶ M) (hb : IsAdmissible b)
    : det((a ≫ b)^•; IsAdmissible.comp ha hb) =
        (det(a^•; ha)).trans ((det(b^•; hb) : det(L^•) ≃ₗ[R] det(M^•))) :=
  sorry

/-- Bridge/view: applying `symm` to `determinantIso_comp` recovers multiplicativity of the
contravariant determinant map `det(M^•) → det(K^•)`. -/
theorem determinantMap_comp
    (a : K ⟶ L) (ha : IsAdmissible a) (b : L ⟶ M) (hb : IsAdmissible b)
    : determinantMap (a ≫ b) (IsAdmissible.comp ha hb) =
      LinearMap.comp (determinantMap a ha)
        ((determinantMap b hb) : det(M^•) →ₗ[R] det(L^•)) :=
  congrArg (fun e ↦ e.symm.toLinearMap) (determinantIso_comp a ha b hb)

end

end CochainComplex

end

/-! ### Lemma_15_123_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Domain-style sampling for Stacks tag `0FJM` / Lemma `15.123.4`:
- primary domain: the determinant functor on the groupoid of perfect derived `R`-complexes with
  tor-amplitude in `[-1, 0]`, together with its canonical comparison isomorphisms and rank-zero
  determinant elements;
- sampled owner declarations:
  `DPerf`,
  `CategoryTheory.Core`,
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeIn`,
  `CochainComplex.determinantIso`;
- best owner abstraction:
  `source-facing`: the full subcategory of `D(R)` cut out by perfectness and tor-amplitude in
    `[-1, 0]`, its determinant line, the comparison isomorphism for an isomorphism, the canonical
    rank-zero determinant element, and the functor `det` from its core to the core of invertible
    modules;
  `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeIn`, `DPerf`, and the complex
    determinant owners from Lemmas `15.123.1`–`15.123.3`, together with the core of the
    invertible-module subcategory of `ModuleCat R`;
  `bridge/view`: two-term finite-projective representatives and good diagrams, which are only the
    comparison devices used in the proof.
- primitive vs. derived:
  primitive data are the derived object, its perfectness and tor-amplitude hypotheses, and
  isomorphisms in `D(R)`;
  the good complexes and admissible comparison diagrams are derived bridge data and should stay
  private rather than forming the public API.

This file therefore restores the source-facing owner/API: a direct determinant-line construction on
the tor-amplitude `[-1, 0]` perfect subcategory, direct comparison isomorphisms on isomorphisms,
the canonical rank-zero determinant element, and the functor `det` from the core of that
subcategory to the core of invertible modules. The good-complex machinery remains internal bridge
data.
-/

namespace CochainComplex

/-- A good complex in the proof of Stacks Lemma `15.123.4`: a cochain complex concentrated in
degrees `-1` and `0` with finite projective terms there. -/
private structure IsGood (P : Cpx) : Prop where
  isStrictlyGE : P.IsStrictlyGE (-1)
  isStrictlyLE : P.IsStrictlyLE 0
  finite_negOne : Module.Finite R (P.X (-1))
  projective_negOne : Module.Projective R (P.X (-1))
  finite_zero : Module.Finite R (P.X 0)
  projective_zero : Module.Projective R (P.X 0)

attribute [instance] IsGood.isStrictlyGE IsGood.isStrictlyLE
attribute [instance] IsGood.finite_negOne IsGood.projective_negOne
attribute [instance] IsGood.finite_zero IsGood.projective_zero

/-- The determinant line of a good two-term complex, viewed as an object of `ModuleCat R`. -/
private abbrev determinantModule (P : Cpx) (hP : IsGood P) : ModuleCat R :=
  let _ : P.IsStrictlyGE (-1) := hP.isStrictlyGE
  let _ : P.IsStrictlyLE 0 := hP.isStrictlyLE
  let _ : Module.Finite R (P.X (-1)) := hP.finite_negOne
  let _ : Module.Projective R (P.X (-1)) := hP.projective_negOne
  let _ : Module.Finite R (P.X 0) := hP.finite_zero
  let _ : Module.Projective R (P.X 0) := hP.projective_zero
  ModuleCat.of R (CochainComplex.determinantLine P)

/-- Admissibility for a morphism between good complexes, with the support and finite-projective
hypotheses supplied by the two good-complex structures. -/
private abbrev IsGoodAdmissible {K L : Cpx} (hK : IsGood K) (hL : IsGood L) (a : K ⟶ L) : Prop :=
  let _ : K.IsStrictlyGE (-1) := hK.isStrictlyGE
  let _ : K.IsStrictlyLE 0 := hK.isStrictlyLE
  let _ : Module.Finite R (K.X (-1)) := hK.finite_negOne
  let _ : Module.Projective R (K.X (-1)) := hK.projective_negOne
  let _ : Module.Finite R (K.X 0) := hK.finite_zero
  let _ : Module.Projective R (K.X 0) := hK.projective_zero
  let _ : L.IsStrictlyGE (-1) := hL.isStrictlyGE
  let _ : L.IsStrictlyLE 0 := hL.isStrictlyLE
  let _ : Module.Finite R (L.X (-1)) := hL.finite_negOne
  let _ : Module.Projective R (L.X (-1)) := hL.projective_negOne
  let _ : Module.Finite R (L.X 0) := hL.finite_zero
  let _ : Module.Projective R (L.X 0) := hL.projective_zero
  CochainComplex.IsAdmissible a

/-- The determinant isomorphism of an admissible morphism between good complexes. -/
private abbrev determinantIsoOfGood {K L : Cpx} (hK : IsGood K) (hL : IsGood L) (a : K ⟶ L)
    (ha : IsGoodAdmissible hK hL a) :
    determinantModule K hK ≅ determinantModule L hL :=
  let _ : K.IsStrictlyGE (-1) := hK.isStrictlyGE
  let _ : K.IsStrictlyLE 0 := hK.isStrictlyLE
  let _ : Module.Finite R (K.X (-1)) := hK.finite_negOne
  let _ : Module.Projective R (K.X (-1)) := hK.projective_negOne
  let _ : Module.Finite R (K.X 0) := hK.finite_zero
  let _ : Module.Projective R (K.X 0) := hK.projective_zero
  let _ : L.IsStrictlyGE (-1) := hL.isStrictlyGE
  let _ : L.IsStrictlyLE 0 := hL.isStrictlyLE
  let _ : Module.Finite R (L.X (-1)) := hL.finite_negOne
  let _ : Module.Projective R (L.X (-1)) := hL.projective_negOne
  let _ : Module.Finite R (L.X 0) := hL.finite_zero
  let _ : Module.Projective R (L.X 0) := hL.projective_zero
  (CochainComplex.determinantIso a ha).toModuleIso

private def goodOfData (P : Cpx)
    (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0)
    (hPfiniteNegOne : Module.Finite R (P.X (-1)))
    (hPprojectiveNegOne : Module.Projective R (P.X (-1)))
    (hPfiniteZero : Module.Finite R (P.X 0))
    (hPprojectiveZero : Module.Projective R (P.X 0)) :
    IsGood P where
  isStrictlyGE := hPge
  isStrictlyLE := hPle
  finite_negOne := hPfiniteNegOne
  projective_negOne := hPprojectiveNegOne
  finite_zero := hPfiniteZero
  projective_zero := hPprojectiveZero

private abbrev goodOfInstances (P : Cpx)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    IsGood P :=
  goodOfData P inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

end CochainComplex

open CochainComplex

/-- Bridge/view: every perfect object of `D(R)` with tor-amplitude in `[-1, 0]` admits a good
two-term finite-projective representative. -/
private theorem exists_twoTermFiniteProjectiveRepresentative
    (K : DPerf R) (hamp : HasTorAmplitudeIn K.obj (-1) 0) :
    ∃ P : Cpx, ∃ _ : K.obj ≅ Q.obj P, CochainComplex.IsGood P := by
  have hKpc :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K.obj).1 K.property |>.1
  obtain ⟨E, eK, hEGE, hELE⟩ :=
    exists_strictlySupported_finiteProjective_complex_of_isPseudoCoherent_of_hasTorAmplitudeIn
      hKpc hamp
  refine ⟨(E : Cpx), eK, ?_⟩
  exact
    { isStrictlyGE := hEGE
      isStrictlyLE := hELE
      finite_negOne := by simpa using (E.term_mem (-1)).1
      projective_negOne := by simpa using (E.term_mem (-1)).2
      finite_zero := by simpa using (E.term_mem 0).1
      projective_zero := by simpa using (E.term_mem 0).2 }

namespace DPerf

/-- The full subcategory of perfect derived `R`-complexes whose tor-amplitude is contained in
`[-1, 0]`. -/
abbrev TorNegOneZero (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun K : DPerf R ↦ HasTorAmplitudeIn K.obj (-1) 0)

end DPerf

namespace DPerf.TorNegOneZero

open CochainComplex

local notation "PerfTor" => DPerf.TorNegOneZero R
private abbrev perfectObjectProperty : ObjectProperty DMod :=
  (DerivedCategory.IsPerfect : ObjectProperty DMod)

private abbrev perfTorProperty : ObjectProperty (DPerf R) :=
  (fun K : DPerf R ↦ HasTorAmplitudeIn K.obj (-1) 0 : ObjectProperty (DPerf R))

private structure Representative (K : PerfTor) where
  P : Cpx
  e : K.obj.obj ≅ Q.obj P
  hP : IsGood P

namespace Representative

instance {K : PerfTor} (rep : Representative K) : rep.P.IsStrictlyGE (-1) :=
  rep.hP.isStrictlyGE

instance {K : PerfTor} (rep : Representative K) : rep.P.IsStrictlyLE 0 :=
  rep.hP.isStrictlyLE

instance {K : PerfTor} (rep : Representative K) : Module.Finite R (rep.P.X (-1)) :=
  rep.hP.finite_negOne

instance {K : PerfTor} (rep : Representative K) : Module.Projective R (rep.P.X (-1)) :=
  rep.hP.projective_negOne

instance {K : PerfTor} (rep : Representative K) : Module.Finite R (rep.P.X 0) :=
  rep.hP.finite_zero

instance {K : PerfTor} (rep : Representative K) : Module.Projective R (rep.P.X 0) :=
  rep.hP.projective_zero

/-- The determinant line of a specific two-term finite-projective representative. -/
private abbrev determinantLine {K : PerfTor} (rep : Representative K) : ModuleCat R :=
  determinantModule rep.P rep.hP

end Representative

private noncomputable def chosenGoodRepresentative (K : PerfTor) : Cpx :=
  Classical.choose
    (exists_twoTermFiniteProjectiveRepresentative K.obj K.property)

private theorem chosenGoodRepresentative_spec (K : PerfTor) :
    ∃ _ : K.obj.obj ≅ Q.obj (chosenGoodRepresentative K),
      IsGood (chosenGoodRepresentative K) :=
  Classical.choose_spec
    (exists_twoTermFiniteProjectiveRepresentative K.obj K.property)

private noncomputable def chosenGoodRepresentativeIso (K : PerfTor) :
    K.obj.obj ≅ Q.obj (chosenGoodRepresentative K) :=
  Classical.choose (chosenGoodRepresentative_spec K)

private theorem chosenGoodRepresentative_isGood (K : PerfTor) :
    IsGood (chosenGoodRepresentative K) :=
  Classical.choose_spec (chosenGoodRepresentative_spec K)

private instance chosenGoodRepresentative_isStrictlyGE (K : PerfTor) :
    (chosenGoodRepresentative K).IsStrictlyGE (-1) :=
  (chosenGoodRepresentative_isGood K).isStrictlyGE

private instance chosenGoodRepresentative_isStrictlyLE (K : PerfTor) :
    (chosenGoodRepresentative K).IsStrictlyLE 0 :=
  (chosenGoodRepresentative_isGood K).isStrictlyLE

private instance chosenGoodRepresentative_finite_negOne (K : PerfTor) :
    Module.Finite R ((chosenGoodRepresentative K).X (-1)) :=
  (chosenGoodRepresentative_isGood K).finite_negOne

private instance chosenGoodRepresentative_projective_negOne (K : PerfTor) :
    Module.Projective R ((chosenGoodRepresentative K).X (-1)) :=
  (chosenGoodRepresentative_isGood K).projective_negOne

private instance chosenGoodRepresentative_finite_zero (K : PerfTor) :
    Module.Finite R ((chosenGoodRepresentative K).X 0) :=
  (chosenGoodRepresentative_isGood K).finite_zero

private instance chosenGoodRepresentative_projective_zero (K : PerfTor) :
    Module.Projective R ((chosenGoodRepresentative K).X 0) :=
  (chosenGoodRepresentative_isGood K).projective_zero

private noncomputable def someRepresentative (K : PerfTor) : Representative K where
  P := chosenGoodRepresentative K
  e := chosenGoodRepresentativeIso K
  hP := chosenGoodRepresentative_isGood K

/-- The determinant line of a good representative is invertible. -/
private theorem representativeDeterminantLine_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft rep.determinantLine).IsEquivalence := by
  sorry

private structure ComparisonWitness {K L : DMod} (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) where
  middle : Cpx
  middleGood : IsGood middle
  b : middle ⟶ PK
  hb : IsGoodAdmissible middleGood hPK b
  c : middle ⟶ PL
  hc : IsGoodAdmissible middleGood hPL c
  comm : Q.map b ≫ eK.inv ≫ a.hom = Q.map c ≫ eL.inv

namespace ComparisonWitness

def determinantIso {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w : ComparisonWitness a PK eK hPK PL eL hPL) :
    determinantModule PK hPK ≅ determinantModule PL hPL :=
  (determinantIsoOfGood w.middleGood hPK w.b w.hb).symm ≪≫
    determinantIsoOfGood w.middleGood hPL w.c w.hc

end ComparisonWitness

private theorem exists_comparisonWitness
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    Nonempty (ComparisonWitness a PK eK hPK PL eL hPL) := by
  sorry

private theorem ComparisonWitness.determinantIso_eq
    {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w₁ w₂ : ComparisonWitness a PK eK hPK PL eL hPL) :
    w₁.determinantIso = w₂.determinantIso := by
  sorry

private def IsComparisonIso
    {K L : DMod} (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL)
    (e : determinantModule PK hPK ≅ determinantModule PL hPL) : Prop :=
  ∃ w : ComparisonWitness a PK eK hPK PL eL hPL, w.determinantIso = e

private theorem existsUnique_isComparisonIso
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    ∃! e : determinantModule PK hPK ≅ determinantModule PL hPL,
      IsComparisonIso a PK eK hPK PL eL hPL e := by
  refine (exists_comparisonWitness a PK eK hPK PL eL hPL).elim ?_
  intro w
  refine ⟨w.determinantIso, ?_, ?_⟩
  · exact ⟨w, rfl⟩
  · intro e he
    rcases he with ⟨w', rfl⟩
    exact (w.determinantIso_eq w').symm

private noncomputable def comparisonIso
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    determinantModule PK hPK ≅ determinantModule PL hPL :=
  Classical.choose
    (ExistsUnique.exists (existsUnique_isComparisonIso a PK eK hPK PL eL hPL))

private theorem comparisonIso_spec
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    IsComparisonIso a PK eK hPK PL eL hPL (comparisonIso a PK eK hPK PL eL hPL) :=
  Classical.choose_spec
    (ExistsUnique.exists (existsUnique_isComparisonIso a PK eK hPK PL eL hPL))

/-- The determinant line attached to a perfect derived `R`-complex of tor-amplitude in
`[-1, 0]`. -/
private noncomputable def rawDeterminantLine (K : PerfTor) : ModuleCat R :=
  determinantModule (chosenGoodRepresentative K) (chosenGoodRepresentative_isGood K)

/-- The canonical comparison isomorphism from the determinant line of `K` to the determinant line
of any two-term finite-projective representative of `K`. -/
private noncomputable def rawDeterminantLineIso (K : PerfTor)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    rawDeterminantLine K ≅ ModuleCat.of R det(P^•) :=
  comparisonIso (Iso.refl K.obj.obj)
    (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K) (chosenGoodRepresentative_isGood K)
    P e (goodOfInstances P)

/-- The determinant line of a tor-amplitude `[-1, 0]` perfect complex is invertible. -/
private theorem rawDeterminantLine_isEquivalence (K : PerfTor) :
    (tensorLeft (rawDeterminantLine K)).IsEquivalence := by
  exact representativeDeterminantLine_isEquivalence (someRepresentative K)

/-- The underlying isomorphism in `D(R)` induced by an isomorphism in the tor-amplitude full
subcategory of `D_{perf}(R)`. -/
private abbrev underlyingIso {K L : PerfTor} (a : K ≅ L) :
    K.obj.obj ≅ L.obj.obj :=
  perfectObjectProperty.ι.mapIso (perfTorProperty.ι.mapIso a)

/-- The determinant comparison isomorphism attached to an isomorphism of tor-amplitude `[-1, 0]`
perfect complexes on the chosen bridge objects. -/
private noncomputable def rawDeterminantIso {K L : PerfTor} (a : K ≅ L) :
    rawDeterminantLine K ≅ rawDeterminantLine L :=
  comparisonIso
    (underlyingIso a)
    (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K) (chosenGoodRepresentative_isGood K)
    (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L) (chosenGoodRepresentative_isGood L)

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`. -/
private noncomputable def detToModule : Core PerfTor ⥤ ModuleCat R where
  obj K := rawDeterminantLine K.of
  map f := (rawDeterminantIso f.iso).hom
  map_id := by
    intro K
    sorry
  map_comp := by
    intro X Y Z f g
    sorry

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`, landing in the full subcategory of invertible `R`-modules. -/
private noncomputable def detToInvertible :
    Core PerfTor ⥤ ModuleCat.InvertibleSubcategory R :=
  ObjectProperty.lift
    ((fun M : ModuleCat R ↦ (tensorLeft M).IsEquivalence) : ObjectProperty (ModuleCat R))
    detToModule
    (fun K ↦ rawDeterminantLine_isEquivalence K.of)

/-- The determinant line attached to a perfect derived `R`-complex of tor-amplitude in
`[-1, 0]`. -/
abbrev determinantLine (K : PerfTor) : ModuleCat R :=
  rawDeterminantLine K

private theorem determinantLine_eq_rawDeterminantLine (K : PerfTor) :
    K.determinantLine = rawDeterminantLine K :=
  rfl

/-- The determinant line of a tor-amplitude `[-1, 0]` perfect complex is invertible. -/
theorem determinantLine_isEquivalence (K : PerfTor) :
    (tensorLeft K.determinantLine).IsEquivalence :=
  rawDeterminantLine_isEquivalence K

/-- The canonical comparison isomorphism from the determinant line of `K` to the determinant line
of any two-term finite-projective representative of `K`. -/
noncomputable abbrev determinantLineIso (K : PerfTor)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.determinantLine ≅ ModuleCat.of R det(P^•) :=
  (eqToIso (K.determinantLine_eq_rawDeterminantLine)).symm ≪≫
    rawDeterminantLineIso K P e

/-- Rank `0` for a tor-amplitude `[-1, 0]` perfect complex, computed on any two-term finite
projective representative in degrees `-1` and `0`. The comparison theorem below identifies this
with the rank-zero condition on every such representative. -/
def IsRankZero (K : PerfTor) : Prop :=
  ∀ (P : Cpx) (_ : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
      CochainComplex.IsRankZero P

/-- Bridge/view: the intrinsic rank-zero condition on a tor-amplitude `[-1, 0]` perfect complex is
computed by any two-term finite-projective representative. -/
theorem isRankZero_iff
    (K : PerfTor) (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.IsRankZero ↔ CochainComplex.IsRankZero P := by
  sorry

/-- The determinant comparison isomorphism attached to an isomorphism of tor-amplitude `[-1, 0]`
perfect complexes. -/
noncomputable abbrev determinantIso {K L : PerfTor} (a : K ≅ L) :
    K.determinantLine ≅ L.determinantLine :=
  rawDeterminantIso a

/-- The chosen good representative stays internal. Its determinant-line comparison isomorphism is
the bridge used to prove the representative-independent canonical-element characterization. -/
private noncomputable abbrev chosenDeterminantLineIso (K : PerfTor) :
    K.determinantLine ≅ ModuleCat.of R det((chosenGoodRepresentative K)^•) :=
  K.determinantLineIso (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)

/-- A determinant-line element is canonical if every two-term finite-projective representative
evaluates to the canonical complex-level determinant element. The companion theorem
`isCanonicalElementValue_iff` re-expresses this criterion at any single representative. -/
def IsCanonicalElementValue (K : PerfTor) (hK : K.IsRankZero) (δ : K.determinantLine) : Prop :=
  ∀ (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
      (K.determinantLineIso P e).hom δ = δ(P^•; (K.isRankZero_iff P e).1 hK)

theorem isCanonicalElementValue_iff
    (K : PerfTor) (hK : K.IsRankZero) (δ : K.determinantLine)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.IsCanonicalElementValue hK δ ↔
      (K.determinantLineIso P e).hom δ = δ(P^•; (K.isRankZero_iff P e).1 hK) := by
  sorry

private theorem existsUnique_isCanonicalElementValue
    (K : PerfTor) (hK : K.IsRankZero) :
    ∃! δ : K.determinantLine, K.IsCanonicalElementValue hK δ := by
  sorry

/-- The canonical determinant element attached to a rank-zero tor-amplitude `[-1, 0]` perfect
complex. -/
noncomputable def canonicalElement (K : PerfTor) (hK : K.IsRankZero) :
    K.determinantLine :=
  Classical.choose (ExistsUnique.exists (existsUnique_isCanonicalElementValue K hK))

/-- The canonical determinant element satisfies its defining representative-independent
characterization. -/
theorem canonicalElement_spec
    (K : PerfTor) (hK : K.IsRankZero) :
    K.IsCanonicalElementValue hK (K.canonicalElement hK) := by
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_isCanonicalElementValue K hK))

/-- The canonical determinant element is computed by any rank-zero two-term finite-projective
representative. -/
theorem determinantLineIso_hom_canonicalElement
    (K : PerfTor) (hK : K.IsRankZero)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    (K.determinantLineIso P e).hom (K.canonicalElement hK) =
      δ(P^•; (K.isRankZero_iff P e).1 hK) :=
  (K.isCanonicalElementValue_iff hK (K.canonicalElement hK) P e).1
    (K.canonicalElement_spec hK)

/-- An isomorphism preserves the rank-zero condition. -/
theorem isRankZero_of_iso {K L : PerfTor} (a : K ≅ L) (hL : L.IsRankZero) :
    K.IsRankZero := by
  sorry

/-- The determinant comparison isomorphism carries canonical rank-zero determinant elements to
canonical rank-zero determinant elements. -/
theorem determinantIso_hom_canonicalElement
    {K L : PerfTor} (a : K ≅ L) (hL : L.IsRankZero) :
    (determinantIso a).hom (K.canonicalElement (isRankZero_of_iso a hL)) =
      L.canonicalElement hL := by
  sorry

end DPerf.TorNegOneZero

end

namespace DPerf.TorNegOneZero

variable {R : Type u} [CommRing R]

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`, presented canonically as a functor to the core of invertible `R`-modules. -/
noncomputable abbrev det :
    Core (DPerf.TorNegOneZero R) ⥤ ModuleCat.InvertibleCore R :=
  let F : Core (DPerf.TorNegOneZero R) ⥤ ModuleCat.InvertibleSubcategory R :=
    detToInvertible
  Core.functorToCore F

@[simp] theorem det_obj (K : DPerf.TorNegOneZero R) :
    (det.obj ⟨K⟩).of.obj = K.determinantLine :=
  rfl

end DPerf.TorNegOneZero

end CategoryTheory
