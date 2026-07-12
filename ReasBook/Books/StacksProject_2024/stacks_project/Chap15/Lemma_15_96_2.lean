import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.RingTheory.Regular.IsSMulRegular

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u

section

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A]
open LinearEquiv

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus `η_f` operator on cochain complexes of `A`-modules and the
  induced comparison on cohomology modulo `f`-torsion;
- sampled chapter/project owner declarations in this domain:
  `CochainComplex (ModuleCat A) ℕ`,
  `CochainComplex.extend ComplexShape.embeddingUpNat`,
  `HomologicalComplex.cycles`,
  `HomologicalComplex.homology`;
- best owner abstraction:
  `source-facing`: the bounded-below Berthelot-Ogus complex `η_f M` for
    `M : NatModuleCochainComplex A`;
  `core/canonical`: `NatModuleCochainComplex A := CochainComplex (ModuleCat A) ℕ`;
  `bridge/view`: the `ℤ`-indexed extension-by-zero presentation
    `M.extend ComplexShape.embeddingUpNat`, together with the corresponding `ℤ`-indexed
    Berthelot-Ogus construction on `K : ModuleComplex A` under the support hypothesis
    `[K.IsStrictlyGE 0]`;
- primitive data vs derived API: the source-facing primitive data are the degreewise Berthelot-Ogus
  submodules and their restricted differentials for `NatModuleCochainComplex A`. The
  `ℤ`-indexed extension-by-zero construction is only a bounded-below bridge, and the homology
  comparison equivalence is derived API built from that bridge. -/

/-- A cochain complex of `A`-modules indexed by `ℤ`. -/
abbrev ModuleComplex (A : Type u) [CommRing A] := CochainComplex (ModuleCat A) ℤ

/-- A cochain complex of `A`-modules indexed by `ℕ`. This is the source-facing owner for
Lemma `15.96.2`. -/
abbrev NatModuleCochainComplex (A : Type u) [CommRing A] :=
  CochainComplex (ModuleCat A) ℕ

namespace BerthelotOgusInt

/-- A cochain complex is termwise `f`-torsion free if multiplication by `f` is injective in every
degree. -/
class IsTermwiseFTorsionFree (f : A) (K : ModuleComplex A) : Prop where
  /-- Multiplication by `f` is injective in each degree. -/
  isSMulRegular (i : ℤ) : IsSMulRegular (K.X i) f

/-- The owner class `IsTermwiseFTorsionFree` is equivalent to degreewise `f`-regularity. -/
theorem isTermwiseFTorsionFree_iff
    (f : A) (K : ModuleComplex A) :
    IsTermwiseFTorsionFree f K ↔ ∀ i : ℤ, IsSMulRegular (K.X i) f := by
  constructor
  · intro h i
    exact h.isSMulRegular i
  · intro h
    exact ⟨h⟩

instance (f : A) (K : ModuleComplex A) [h : IsTermwiseFTorsionFree f K] (i : ℤ) :
    IsSMulRegular (K.X i) f :=
  h.isSMulRegular i

/-- The degree-`i` Berthelot-Ogus term on the `ModuleComplex A` owner. -/
abbrev degreeSubmodule (f : A) (K : ModuleComplex A) (i : ℤ) :
    Submodule A (K.X i) :=
  LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1)))).comap (K.d i (i + 1)).hom

-- Proof sketch: if `x` lies in the defining intersection for degree `i`, then `d(x)` already
-- lies in the required range for degree `i + 1`; the second condition for `d(x)` is automatic
-- because `d ∘ d = 0`, and `0` belongs to every range.
/-- The differential of `K` sends the degree-`i` bridge term of `η_f K` into degree `i + 1`. -/
private theorem differential_mem
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : degreeSubmodule f K i) :
    K.d i (i + 1) x ∈ degreeSubmodule f K (i + 1) := by
  -- The first defining condition is exactly the second component of `x`.
  refine ⟨?_, ?_⟩
  · simpa [degreeSubmodule] using x.2.2
  · -- The next differential vanishes by `d ∘ d = 0`, so the image lies in the next range.
    refine ⟨0, ?_⟩
    have hdd := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (K.d_comp_d i (i + 1) (i + 2))) x
    rw [show i + 2 = i + 1 + 1 by abel] at hdd
    calc
      ((LinearMap.lsmul A (K.X (i + 1 + 1)) (f ^ Int.toNat (i + 1 + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (K.d (i + 1) (i + 1 + 1))) ((ConcreteCategory.hom (K.d i (i + 1))) x) :=
        hdd.symm

/-- The degree-`i` differential on the Berthelot-Ogus complex `η_f K`. -/
abbrev differentialLinear (f : A) (K : ModuleComplex A) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f K (i + 1) :=
  ((K.d i (i + 1)).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f K (i + 1))
    (differential_mem f K i)

-- Proof sketch: `η_f K` uses the same differentials as `K`, only codomain-restricted to the
-- defining submodules. Hence the square of two successive differentials is the restriction of
-- `d ∘ d = 0` on `K`.
/-- The successive differentials of `η_f K` compose to zero. -/
theorem differential_sq (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (differentialLinear f K i) ≫
        ModuleCat.ofHom (differentialLinear f K (i + 1)) =
      0 := by
  -- After forgetting the codomain restrictions, this is exactly `d ∘ d = 0`.
  ext x
  simp [differentialLinear]
  rw [show i + 1 + 1 = i + 2 by abel]
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (K.d_comp_d i (i + 1) (i + 2))) x

/-- The Berthelot-Ogus complex `η_f K` on the `ModuleComplex A` owner. -/
def complex (f : A) (K : ModuleComplex A) : ModuleComplex A :=
  CochainComplex.of
    (fun i ↦ ModuleCat.of A (degreeSubmodule f K i))
    (fun i ↦ ModuleCat.ofHom (differentialLinear f K i))
    (fun i ↦ differential_sq f K i)

instance complex_isStrictlyGE_zero
    (f : A) (K : ModuleComplex A) [K.IsStrictlyGE 0] :
    (complex f K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let hzero : CategoryTheory.Limits.IsZero (K.X i) := K.isZero_of_isStrictlyGE 0 i hi
  letI : Subsingleton (K.X i) := ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((complex f K).X i) := by
    change Subsingleton (degreeSubmodule f K i)
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

scoped[BerthelotOgusInt] notation "η[" f "] " K:arg => complex f K

open scoped BerthelotOgusInt

/-- A morphism of bounded-below bridge complexes sends the degree-`i` Berthelot-Ogus term of `K`
into that of `L`. -/
theorem map_mem_degreeSubmodule
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) (x : degreeSubmodule f K i) :
    φ.f i x ∈ degreeSubmodule f L i := by
  -- Transport the two defining range witnesses of `x` through the cochain map `φ`.
  refine ⟨?_, ?_⟩
  · rcases x.2.1 with ⟨y, hy⟩
    refine ⟨φ.f i y, ?_⟩
    calc
      (LinearMap.lsmul A (L.X i) (f ^ Int.toNat i)) (φ.f i y)
          = φ.f i ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) y) := by
            simp [LinearMap.lsmul_apply]
      _ = φ.f i x := by rw [hy]
  · rcases x.2.2 with ⟨z, hz⟩
    refine ⟨φ.f (i + 1) z, ?_⟩
    calc
      (LinearMap.lsmul A (L.X (i + 1)) (f ^ Int.toNat (i + 1))) (φ.f (i + 1) z)
          = φ.f (i + 1)
              ((LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1))) z) := by
            simp [LinearMap.lsmul_apply]
      _ = φ.f (i + 1) ((K.d i (i + 1)).hom x) := by rw [hz]
      _ = (L.d i (i + 1)).hom (φ.f i x) := by
            exact
              (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (φ.comm i (i + 1))) x).symm

/-- The degree-`i` component of the morphism induced on Berthelot-Ogus complexes by `φ`. -/
abbrev mapLinear
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f L i :=
  ((φ.f i).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f L i)
    (map_mem_degreeSubmodule f φ i)

/-- Helper for Lemma 15.96.2: linear maps into a submodule agree once their compositions with the
ambient subtype map agree. -/
private theorem codRestrict_subtype_ext
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (S : Submodule A N) {g h : M →ₗ[A] S}
    (hcomp : S.subtype.comp g = S.subtype.comp h) :
    g = h := by
  -- Equality in the subtype is detected by the ambient values.
  ext x
  exact LinearMap.congr_fun hcomp x

-- Proof sketch: both sides are restrictions of the commutative square defining the cochain map
-- `φ`; after forgetting the subtype codomains, the equality is exactly `φ.comm`.
/-- The induced Berthelot-Ogus component maps commute with the differentials. -/
theorem map_comm
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      (ModuleCat.ofHom (mapLinear f φ i))
      ((η[f] K).d i j)
      ((η[f] L).d i j)
      (ModuleCat.ofHom (mapLinear f φ j)) := by
  rcases hij with rfl
  refine CommSq.mk ?_
  apply ModuleCat.hom_ext
  -- Compare the codomain-restricted maps after composing with the ambient subtype map.
  refine
    (codRestrict_subtype_ext (A := A) (M := degreeSubmodule f K i) (N := L.X (i + 1))
      (degreeSubmodule f L (i + 1)) ?_)
  ext x
  -- After discarding the codomain restriction, the square is exactly `φ.comm`.
  simp [complex, mapLinear, differentialLinear]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (φ.comm i (i + 1))) x

/-- The morphism of Berthelot-Ogus complexes induced by a morphism `φ : K ⟶ L`. -/
def map (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) :
    η[f] K ⟶ η[f] L where
  f i := ModuleCat.ofHom (mapLinear f φ i)
  comm' i j hij := (map_comm f φ i j hij).w

-- Proof sketch: `BerthelotOgusInt.map f φ` is defined degreewise by `mapLinear f φ`, so its
-- `i`th component is the corresponding codomain-restricted map.
/-- The degree-`i` component of the Berthelot-Ogus map induced by `φ`. -/
theorem map_f
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    (map f φ).f i = ModuleCat.ofHom (mapLinear f φ i) := by
  rfl

-- Proof sketch: if `x` is a cocycle, then `f ^ Int.toNat i x` lies in the image of multiplication
-- by `f ^ Int.toNat i`, and its differential is zero, hence also lies in the image of
-- multiplication by `f ^ Int.toNat (i + 1)`. Therefore `f ^ Int.toNat i x` defines a term of
-- `η_f K` in degree `i`.
/-- Multiplication by `f ^ Int.toNat i` sends cocycles of `K` in degree `i` into the degree-`i`
term of `η_f K`. -/
private theorem cycleScale_mem_degreeSubmodule
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.cycles i) :
    ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom) x ∈
      degreeSubmodule f K i := by
  -- The scaled cocycle is visibly in the first range.
  refine ⟨?_, ?_⟩
  · exact ⟨(K.iCycles i).hom x, rfl⟩
  · -- Its differential vanishes because `x` already lies in the kernel defining `cycles`.
    have hcycle := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (K.iCycles_d i (i + 1))) x
    change (ModuleCat.Hom.hom (K.d i (i + 1))) ((ModuleCat.Hom.hom (K.iCycles i)) x) = 0 at hcycle
    refine ⟨0, ?_⟩
    calc
      ((LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (K.d i (i + 1)))
            (((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom) x) := by
          change 0 = (ModuleCat.Hom.hom (K.d i (i + 1))) (f ^ Int.toNat i • (ModuleCat.Hom.hom (K.iCycles i)) x)
          rw [_root_.map_smul, hcycle]
          simp

/-- Multiplication by `f ^ Int.toNat i` on cocycles, viewed as a morphism into the degree-`i`
term of `η_f K`. -/
abbrev cyclesToEtaXLinear (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i →ₗ[A] degreeSubmodule f K i :=
  ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom).codRestrict
    (degreeSubmodule f K i) (cycleScale_mem_degreeSubmodule f K i)

-- Proof sketch: the source is already a cycle in `K`, so after multiplying by `f ^ Int.toNat i`
-- its differential is still zero. Since `η_f K` uses the restricted differential of `K`, the
-- image in degree `i` is a cocycle of `η_f K`.
/-- The scaled cocycle morphism lands in the cycles of `η_f K`. -/
theorem cyclesToEtaX_comp_d_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (cyclesToEtaXLinear f K i) ≫ (η[f] K).d i (i + 1) = 0 := by
  -- Route correction: `cycles` is the kernel object, so we use `iCycles_d` rather than subtype
  -- projections to express the cocycle condition.
  ext x
  simp [cyclesToEtaXLinear, complex, differentialLinear]
  apply Subtype.ext
  change (ModuleCat.Hom.hom (K.d i (i + 1))) (f ^ Int.toNat i • (ModuleCat.Hom.hom (K.iCycles i)) x) = 0
  rw [_root_.map_smul]
  have hcycle := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (K.iCycles_d i (i + 1))) x
  change (ModuleCat.Hom.hom (K.d i (i + 1))) ((ModuleCat.Hom.hom (K.iCycles i)) x) = 0 at hcycle
  rw [hcycle, smul_zero]

/-- The cocycle-level comparison map from `K` to `η_f K` in degree `i`. -/
abbrev cyclesToEtaCycles (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i ⟶ (η[f] K).cycles i :=
  (η[f] K).liftCycles'
    (ModuleCat.ofHom (cyclesToEtaXLinear f K i))
    (i + 1) (by simp) (cyclesToEtaX_comp_d_eq_zero f K i)

/-- The homology-class map induced on cocycles by multiplication by `f ^ Int.toNat i`. -/
abbrev cyclesToEtaHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.cycles i ⟶ (η[f] K).homology i :=
  cyclesToEtaCycles f K i ≫ (η[f] K).homologyπ i

/-- Helper for Lemma 15.96.2: multiplying a predecessor representative in degree `j` by
`f ^ Int.toNat (j + 1)` defines a canonical element of the degree-`j` Berthelot-Ogus term. -/
private theorem boundary_scale_mem_degreeSubmodule_pred
    (f : A) (K : ModuleComplex A) (j : ℤ) (x : K.X j) :
    ((LinearMap.lsmul A (K.X j) (f ^ Int.toNat (j + 1))) x) ∈
      degreeSubmodule f K j := by
  -- The predecessor scaling already provides the successor-range witness, and the first range
  -- witness is obtained by normalizing `Int.toNat j` against `Int.toNat (j + 1)`.
  refine ⟨?_, ?_⟩
  · by_cases hj : 0 < j + 1
    · refine ⟨f • x, ?_⟩
      have hj_nonneg : 0 ≤ j := by omega
      have hsucc_nonneg : 0 ≤ j + 1 := by omega
      have hpow : Int.toNat (j + 1) = Int.toNat j + 1 := by
        apply Int.ofNat.inj
        calc
          Int.ofNat (Int.toNat (j + 1)) = j + 1 := Int.toNat_of_nonneg hsucc_nonneg
          _ = Int.ofNat (Int.toNat j) + 1 := by
                simpa using congrArg (fun t : ℤ => t + 1) (Int.toNat_of_nonneg hj_nonneg).symm
          _ = Int.ofNat (Int.toNat j + 1) := by simp
      calc
        (LinearMap.lsmul A (K.X j) (f ^ Int.toNat j)) (f • x)
            = f ^ Int.toNat j • (f • x) := by
                rfl
        _ = (f ^ Int.toNat j * f) • x := by
              rw [smul_smul]
        _ = f ^ Int.toNat (j + 1) • x := by
              rw [hpow, pow_succ]
    · refine ⟨x, ?_⟩
      have hsucc_nonpos : j + 1 ≤ 0 := le_of_not_gt hj
      have hj_nonpos : j ≤ 0 := by omega
      simp [LinearMap.lsmul_apply, Int.toNat_of_nonpos hsucc_nonpos,
        Int.toNat_of_nonpos hj_nonpos]
  · refine ⟨(K.d j (j + 1)).hom x, ?_⟩
    -- The second defining condition is just linearity of the differential through the common
    -- visible scalar factor.
    simp [LinearMap.lsmul_apply, _root_.map_smul]

/-- Helper for Lemma 15.96.2: a predecessor boundary representative in degree `j` determines a
term of `η[f] K` whose differential is the scaled boundary in degree `j + 1`. -/
private abbrev boundaryToEtaDegreeLinear
    (f : A) (K : ModuleComplex A) (j : ℤ) :
    K.X j →ₗ[A] degreeSubmodule f K j :=
  (LinearMap.lsmul A (K.X j) (f ^ Int.toNat (j + 1))).codRestrict
    (degreeSubmodule f K j)
    (boundary_scale_mem_degreeSubmodule_pred f K j)

/-- Helper for Lemma 15.96.2: the source object of `K.sc i` is the predecessor term
`K.X (i - 1)`. -/
private theorem sc_X₁_eq
    (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).X₁ = K.X (i - 1) := by
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', CochainComplex.prev]

/-- Helper for Lemma 15.96.2: after identifying the source object of `K.sc i`, its source map is
the predecessor differential `d (i - 1) i`. -/
private theorem sc_f_eq
    (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).f =
      (CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫ K.d (i - 1) i := by
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor', CochainComplex.prev]

/-- Helper for Lemma 15.96.2: transporting an ambient predecessor into `(K.sc i).X₁` and back
through `sc_X₁_eq` is the identity. -/
private theorem sc_X₁_eq_transport_cancel
    (K : ModuleComplex A) (i : ℤ) (y : K.X (i - 1)) :
    (CategoryTheory.eqToHom (sc_X₁_eq K i)).hom
        ((CategoryTheory.eqToHom (Eq.symm (sc_X₁_eq K i))).hom y) =
      y := by
  let e : (K.sc i).X₁ ≅ K.X (i - 1) := CategoryTheory.eqToIso (sc_X₁_eq K i)
  -- Evaluate the inverse-then-forward identity of `eqToIso (sc_X₁_eq K i)` on the chosen
  -- predecessor element.
  change (e.hom).hom ((e.inv).hom y) = y
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) y

/-- Helper for Lemma 15.96.2: `ShortComplex.toCycles_i` identifies the ambient value of the
boundary representative in degree `i` with the predecessor differential. -/
private theorem sc_toCycles_i_apply
    (K : ModuleComplex A) (i : ℤ) (x : (K.sc i).X₁) :
    (K.iCycles i).hom (((K.sc i).toCycles).hom x) =
      ((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫ K.d (i - 1) i).hom x := by
  -- The cycles inclusion turns the chosen boundary representative back into the source map of
  -- `K.sc i`, which has already been identified with `d (i - 1) i`.
  have htoCycles :
      ((K.iCycles i).hom (((K.sc i).toCycles).hom x)) =
        ((K.sc i).f).hom x := by
    simpa using LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i (K.sc i))) x
  have hf :
      ((K.sc i).f).hom x =
        ((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫ K.d (i - 1) i).hom x := by
    rw [sc_f_eq]
    rfl
  simpa using htoCycles.trans hf

/-- Helper for Lemma 15.96.2: before entering the cycles object of `η[f] K`, the left boundary
composite is the visible scalar multiple of the ambient cycle representative. -/
private theorem toCycles_comp_cyclesToEtaX_apply_val
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : (K.sc i).X₁) :
    Subtype.val
        ((((K.sc i).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f K i)).hom) x) =
      f ^ Int.toNat i • (K.iCycles i).hom (((K.sc i).toCycles).hom x) := by
  -- Unfold the codomain restriction once to read the composite in the ambient module.
  rfl

/-- Helper for Lemma 15.96.2: the right boundary composite has ambient value equal to the
ordinary differential of the scaled predecessor. -/
private theorem boundaryToEtaDegree_comp_differential_apply_val_aux
    (f : A) (K : ModuleComplex A) (j : ℤ) (y : K.X j) :
    Subtype.val
        ((((ModuleCat.ofHom (boundaryToEtaDegreeLinear f K j) ≫
          (η[f] K).d j (j + 1)).hom) y)) =
      (K.d j (j + 1)).hom
        (f ^ Int.toNat (j + 1) • y) := by
  -- At the ambient level, the restricted differential of `η[f] K` is exactly the differential of
  -- `K` in consecutive degrees.
  have hd_int :
      (η[f] K).d j (j + 1) = ModuleCat.ofHom (differentialLinear f K j) := by
    simpa [complex] using
      (CochainComplex.of_d
        (fun i ↦ ModuleCat.of A (degreeSubmodule f K i))
        (fun i ↦ ModuleCat.ofHom (differentialLinear f K i))
        (fun i ↦ differential_sq f K i)
        j)
  rw [hd_int]
  rfl

/-- Helper for Lemma 15.96.2: the right boundary composite has ambient value equal to the
ordinary differential of the scaled predecessor. -/
private theorem boundaryToEtaDegree_comp_differential_apply_val_pred
    (f : A) (K : ModuleComplex A) (i : ℤ) (y : K.X (i - 1)) :
    Subtype.val
        ((((ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫
          (η[f] K).d (i - 1) ((i - 1) + 1)).hom) y)) =
      (K.d (i - 1) ((i - 1) + 1)).hom
        (f ^ Int.toNat i • y) := by
  -- Specialize the ambient predecessor computation to degree `i`; only the exponent needs
  -- normalization from `Int.toNat ((i - 1) + 1)` to `Int.toNat i`.
  simpa [show Int.toNat ((i - 1) + 1) = Int.toNat i by omega] using
    (boundaryToEtaDegree_comp_differential_apply_val_aux
      (f := f) (K := K) (j := i - 1) (y := y))

/-- Helper for Lemma 15.96.2: the right boundary composite has ambient value equal to the
ordinary differential of the scaled predecessor. -/
private theorem boundaryToEtaDegree_comp_differential_apply_val
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : (K.sc i).X₁) :
    Subtype.val
        ((((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫
          ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫
          (η[f] K).d (i - 1) i).hom) x) =
      (K.d (i - 1) i).hom
        (f ^ Int.toNat i • ((CategoryTheory.eqToHom (sc_X₁_eq K i)).hom x)) := by
  -- Route correction: compute the ambient value after the source cast has already been applied,
  -- then normalize the `CochainComplex.of` differential directly at index `i - 1`.
  have haux (y : K.X (i - 1)) :
      Subtype.val
          ((((ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫
            (η[f] K).d (i - 1) i).hom) y)) =
        (K.d (i - 1) i).hom (f ^ Int.toNat i • y) := by
    -- Once the input already lives in `K.X (i - 1)`, the remaining index change is the plain
    -- successor normalization `((i - 1) + 1) = i`.
    have hpred :
        Subtype.val
            ((((ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫
              (η[f] K).d (i - 1) ((i - 1) + 1)).hom) y)) =
          (K.d (i - 1) ((i - 1) + 1)).hom (f ^ Int.toNat i • y) :=
      boundaryToEtaDegree_comp_differential_apply_val_pred f K i y
    have hi : ((i - 1) + 1) = i := by
      omega
    rw [hi] at hpred
    exact hpred
  simpa using haux (((CategoryTheory.eqToHom (sc_X₁_eq K i)).hom) x)

/-- Helper for Lemma 15.96.2: in ambient degree `i`, the cocycle comparison on boundaries is the
differential of the canonical predecessor term in `η[f] K`. -/
private theorem toCycles_comp_cyclesToEtaX_eq_boundary
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f K i) =
      (CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫
        ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫ (η[f] K).d (i - 1) i := by
  -- Compare both maps after forgetting the target subtype, where only linearity of `d`
  -- remains once the predecessor normalization lemmas are in place.
  apply ModuleCat.hom_ext
  ext x
  calc
    Subtype.val
        ((((K.sc i).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f K i)).hom) x) =
      f ^ Int.toNat i • (K.iCycles i).hom (((K.sc i).toCycles).hom x) := by
        rw [toCycles_comp_cyclesToEtaX_apply_val]
    _ = f ^ Int.toNat i • (((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫ K.d (i - 1) i).hom x) := by
        rw [sc_toCycles_i_apply]
    _ = (K.d (i - 1) i).hom
          (f ^ Int.toNat i • ((CategoryTheory.eqToHom (sc_X₁_eq K i)).hom x)) := by
        rw [_root_.map_smul]
        rfl
    _ =
      Subtype.val
        ((((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫
          ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)) ≫
          (η[f] K).d (i - 1) i).hom) x) := by
        symm
        exact boundaryToEtaDegree_comp_differential_apply_val f K i x

-- Proof sketch: a boundary in degree `i` is represented by `d(y)` from degree `i - 1`. After
-- multiplying by `f ^ Int.toNat i`, this becomes the boundary of the corresponding scaled
-- predecessor in the subcomplex `η_f K`, so its class in `H^i(η_f K)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).toCycles ≫ cyclesToEtaHomology f K i = 0 := by
  -- Route correction: the integer-indexed source proof is executed at the ambient degree level
  -- first, and only then descended through `liftCycles` to homology.
  have hk :
      ((K.sc i).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f K i)) ≫
          (η[f] K).d i (i + 1) =
        0 := by
    -- The source map already lands in cycles of `η[f] K`, so the successor differential vanishes.
    simpa [Category.assoc] using
      congrArg
        (((K.sc i).toCycles) ≫ ·)
        (cyclesToEtaX_comp_d_eq_zero f K i)
  have hcomp :
      (K.sc i).toCycles ≫ cyclesToEtaCycles f K i =
        (η[f] K).liftCycles
            ((K.sc i).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f K i))
            (i + 1) (by simp) hk := by
    -- Reassociate the lifted cycles map so the ambient boundary composite becomes the input of
    -- `liftCycles`.
    simpa [cyclesToEtaCycles] using
      (HomologicalComplex.comp_liftCycles
        (η[f] K)
        (ModuleCat.ofHom (cyclesToEtaXLinear f K i))
        (i + 1) (by simp)
        (cyclesToEtaX_comp_d_eq_zero f K i)
        ((K.sc i).toCycles))
  -- The normalized composite is a boundary in degree `i`, hence its homology class vanishes.
  change
    (K.sc i).toCycles ≫ cyclesToEtaCycles f K i ≫
        (η[f] K).homologyπ i =
      0
  rw [← Category.assoc]
  rw [hcomp]
  simpa [Category.assoc] using
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (η[f] K)
      (((K.sc i).toCycles ≫
        ModuleCat.ofHom (cyclesToEtaXLinear f K i)))
      (i + 1) (by simp)
      ((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫
        ModuleCat.ofHom (boundaryToEtaDegreeLinear f K (i - 1)))
      (toCycles_comp_cyclesToEtaX_eq_boundary f K i)

/-- The homology comparison map `H^i(K) → H^i(η_f K)` induced by multiplication by
`f ^ Int.toNat i`. -/
abbrev homologyToEtaHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.homology i ⟶ (η[f] K).homology i :=
  (K.sc i).descHomology
    (cyclesToEtaHomology f K i)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f K i)

/-- Helper for Lemma 15.96.2: the descended owner comparison map evaluates on a homology class
represented by a cycle exactly by applying the cycle-level comparison first. -/
private theorem homologyToEtaHomology_homologyπ
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.homologyπ i ≫ homologyToEtaHomology f K i =
      cyclesToEtaHomology f K i := by
  -- This is the defining `descHomology` computation for the owner short complex `K.sc i`.
  change
    (K.sc i).homologyπ ≫
        (K.sc i).descHomology
          (cyclesToEtaHomology f K i)
          (toCycles_comp_cyclesToEtaHomology_eq_zero f K i) =
      cyclesToEtaHomology f K i
  exact
    ShortComplex.π_descHomology (S := K.sc i)
      (k := cyclesToEtaHomology f K i)
      (hk := toCycles_comp_cyclesToEtaHomology_eq_zero f K i)

/-- Helper for Lemma 15.96.2: in a short complex of `A`-modules, the concrete cycles inclusion
obtained from `toCycles` agrees with `moduleCatToCycles` after passing through
`moduleCatCyclesIso`. -/
private theorem moduleCatCyclesIso_hom_toCycles_eq_moduleCatToCycles
    (S : ShortComplex (ModuleCat A)) [S.HasHomology] (b : S.X₁) :
    (S.moduleCatCyclesIso.hom).hom ((S.toCycles).hom b) = S.moduleCatToCycles b := by
  -- Compare both concrete kernel elements by their ambient values in `S.X₂`.
  apply Subtype.ext
  change ((S.iCycles).hom ((S.toCycles).hom b) : S.X₂) = S.f.hom b
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i S)) b

/-- Helper for Lemma 15.96.2: transporting a cycle through `moduleCatCyclesIso.hom` forgets to
the same ambient element as the canonical inclusion `iCycles`. -/
private theorem moduleCatCyclesIso_hom_iCycles
    (S : ShortComplex (ModuleCat A)) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).1 = S.iCycles.hom z := by
  -- The categorical cycles object is definitionally the kernel used by `moduleCatCyclesIso`.
  rfl

/-- Helper for Lemma 15.96.2: a concrete short-complex boundary witness already determines the
corresponding categorical boundary representative in cycles. -/
private theorem shortComplex_toCycles_eq_of_moduleCat_boundary_witness
    (K : ModuleComplex A) (i : ℤ) (b : (K.sc i).X₁) (q : K.cycles i)
    (hb : (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q) :
    ((K.sc i).toCycles).hom b = q := by
  -- First identify both cycle representatives after pushing them into the concrete kernel model.
  have hinj : Function.Injective ((K.sc i).moduleCatCyclesIso.hom).hom :=
    (ModuleCat.mono_iff_injective ((K.sc i).moduleCatCyclesIso.hom)).1 inferInstance
  apply hinj
  exact
    (moduleCatCyclesIso_hom_toCycles_eq_moduleCatToCycles (K.sc i) b).trans <|
      by simpa using hb

/-- Helper for Lemma 15.96.2: for the cochain shape on `ℤ`, the predecessor of `i + 1` is `i`.
-/
private theorem shortComplex_prev_degree_transport (i : ℤ) :
    (ComplexShape.up ℤ).prev (i + 1) = i := by
  -- The cochain predecessor on `ℤ` is the evident arithmetic predecessor.
  classical
  simp [ComplexShape.prev, ComplexShape.up, ComplexShape.up']

/-- Helper for Lemma 15.96.2: a concrete owner short-complex boundary witness rewrites to the
ambient differential equation used in the source proof. -/
private theorem shortComplex_boundary_witness_ambient_eq
    (K : ModuleComplex A) (i : ℤ) (b : (K.sc i).X₁) (q : K.cycles i)
    (hb : (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q) :
    (K.d (i - 1) i).hom ((CategoryTheory.eqToHom (sc_X₁_eq K i)).hom b) = (K.iCycles i).hom q := by
  -- Freeze the categorical cycle representative first; the ambient differential equality is then
  -- the `toCycles_i` computation rewritten through `sc_X₁_eq`.
  have htoCycles :
      ((K.sc i).toCycles).hom b = q :=
    shortComplex_toCycles_eq_of_moduleCat_boundary_witness K i b q hb
  calc
    (K.d (i - 1) i).hom ((CategoryTheory.eqToHom (sc_X₁_eq K i)).hom b) =
        ((CategoryTheory.eqToHom (sc_X₁_eq K i)) ≫ K.d (i - 1) i).hom b := by
          rfl
    _ = (K.iCycles i).hom (((K.sc i).toCycles).hom b) := by
          symm
          exact sc_toCycles_i_apply K i b
    _ = (K.iCycles i).hom q := by rw [htoCycles]

/-- Helper for Lemma 15.96.2: on the owner short complex `K.sc i`, a left-homology class vanishes
exactly when its cycle representative lies in the boundary range. -/
private theorem leftHomologyπ_eq_zero_iff_exists_boundary
    (K : ModuleComplex A) (i : ℤ) (q : K.cycles i) :
    ((K.sc i).leftHomologyπ).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  let S := K.sc i
  have hcomm :
      S.leftHomologyπ ≫ S.moduleCatLeftHomologyData.leftHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Compare abstract left homology with the concrete quotient of cycles by boundaries.
    simpa [S] using
      (ShortComplex.leftHomologyMapData (𝟙 S) S.leftHomologyData S.moduleCatLeftHomologyData).commπ
  constructor
  · intro hq
    -- Evaluating the comparison at `q` moves vanishing into the concrete quotient.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (((S.leftHomologyπ).hom q)) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- An explicit boundary witness is zero in the concrete quotient.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    -- Transport that zero back across the quotient comparison isomorphism.
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (((S.leftHomologyπ).hom q)) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.leftHomologyIso.hom).1
        inferInstance
    have h0 : 0 = S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.96.2: in degree `i`, a homology class of the owner complex vanishes
exactly when its cycle representative comes from the predecessor differential. -/
private theorem homologyπ_eq_zero_iff_exists_boundary
    (K : ModuleComplex A) (i : ℤ) (q : K.cycles i) :
    (K.homologyπ i).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  -- Rewrite the abstract homology quotient through left homology, then use the concrete quotient.
  rw [HomologicalComplex.homologyπ, ShortComplex.homologyπ]
  constructor
  · intro hq
    -- Since `leftHomologyIso` is mono, vanishing after transport implies vanishing before it.
    have hleft : ((K.sc i).leftHomologyπ).hom q = 0 := by
      have hinj : Function.Injective ((K.sc i).leftHomologyIso.hom).hom :=
        (ModuleCat.mono_iff_injective ((K.sc i).leftHomologyIso.hom)).1 inferInstance
      apply hinj
      simpa using hq
    exact (leftHomologyπ_eq_zero_iff_exists_boundary K i q).1 hleft
  · intro hq
    -- Conversely, a concrete boundary witness already kills the transported class.
    have hleft : ((K.sc i).leftHomologyπ).hom q = 0 :=
      (leftHomologyπ_eq_zero_iff_exists_boundary K i q).2 hq
    change ((K.sc i).leftHomologyIso.hom).hom (((K.sc i).leftHomologyπ).hom q) = 0
    rw [hleft]
    simp

/-- Helper for Lemma 15.96.2: once a short-complex predecessor maps to a target cycle under
`toCycles`, it already yields the corresponding concrete boundary witness in `moduleCatCycles`. -/
private theorem moduleCat_boundary_witness_of_toCycles_eq
    (K : ModuleComplex A) (i : ℤ) (b : (K.sc i).X₁) (q : K.cycles i)
    (hb : ((K.sc i).toCycles).hom b = q) :
    (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  -- The concrete cycles object is just the `moduleCatCyclesIso` image of the categorical one.
  calc
    (K.sc i).moduleCatToCycles b =
        (K.sc i).moduleCatCyclesIso.hom (((K.sc i).toCycles).hom b) := by
          symm
          exact moduleCatCyclesIso_hom_toCycles_eq_moduleCatToCycles (K.sc i) b
    _ = (K.sc i).moduleCatCyclesIso.hom q := by
          rw [hb]

/-- Helper for Lemma 15.96.2: an ambient predecessor equation already yields the corresponding
short-complex boundary witness. -/
private theorem shortComplex_boundary_witness_of_ambient_eq
    (K : ModuleComplex A) (j : ℤ) (y : K.X (j - 1)) (q : K.cycles j)
    (hy : (K.d (j - 1) j).hom y = (K.iCycles j).hom q) :
    ∃ b : (K.sc j).X₁, (K.sc j).moduleCatToCycles b = (K.sc j).moduleCatCyclesIso.hom q := by
  let b : (K.sc j).X₁ := (CategoryTheory.eqToHom (Eq.symm (sc_X₁_eq K j))).hom y
  refine ⟨b, ?_⟩
  -- First show that the categorical cycle represented by `b` is exactly `q`.
  have htoCycles : ((K.sc j).toCycles).hom b = q := by
    have hinj : Function.Injective (K.iCycles j).hom :=
      (ModuleCat.mono_iff_injective (K.iCycles j)).1 inferInstance
    apply hinj
    calc
      (K.iCycles j).hom (((K.sc j).toCycles).hom b) =
          ((CategoryTheory.eqToHom (sc_X₁_eq K j)) ≫ K.d (j - 1) j).hom b := by
            exact sc_toCycles_i_apply K j b
      _ = (K.d (j - 1) j).hom ((CategoryTheory.eqToHom (sc_X₁_eq K j)).hom b) := by
            rfl
      _ = (K.d (j - 1) j).hom y := by
            rw [show (CategoryTheory.eqToHom (sc_X₁_eq K j)).hom b = y by
              simpa [b] using sc_X₁_eq_transport_cancel K j y]
      _ = (K.iCycles j).hom q := hy
  -- Then translate that categorical boundary witness back to the concrete kernel model.
  exact moduleCat_boundary_witness_of_toCycles_eq K j b q htoCycles

/-- Helper for Lemma 15.96.2: a degree-`j` owner homology class vanishes exactly when its cycle
comes from the ambient predecessor differential. -/
private theorem homologyπ_eq_zero_iff_exists_prev_boundary
    (K : ModuleComplex A) (j : ℤ) (q : K.cycles j) :
    (K.homologyπ j).hom q = 0 ↔
      ∃ b : K.X (j - 1),
        (K.d (j - 1) j).hom b = (K.iCycles j).hom q := by
  constructor
  · intro hq
    rcases (homologyπ_eq_zero_iff_exists_boundary K j q).1 hq with ⟨b, hb⟩
    -- Read the concrete short-complex witness back in the ambient predecessor module.
    refine ⟨(CategoryTheory.eqToHom (sc_X₁_eq K j)).hom b, ?_⟩
    exact shortComplex_boundary_witness_ambient_eq K j b q hb
  · rintro ⟨b, hb⟩
    -- The ambient predecessor equality is exactly the reverse bridge to the short-complex model.
    exact
      (homologyπ_eq_zero_iff_exists_boundary K j q).2
        (shortComplex_boundary_witness_of_ambient_eq K j b q hb)

/-- Helper for Lemma 15.96.2: in positive degree, a predecessor witness `y` with
`d y = f • z` already defines the expected degree-`i - 1` Berthelot-Ogus term. -/
private theorem predecessor_scale_mem_degreeSubmodule_of_d_eq_smul
    (f : A) (K : ModuleComplex A) (i : ℤ) (hi : 0 < i)
    {z : K.X ((i - 1) + 1)} {y : K.X (i - 1)}
    (hy : (K.d (i - 1) ((i - 1) + 1)).hom y = f • z) :
    (f ^ Int.toNat (i - 1) • y) ∈ degreeSubmodule f K (i - 1) := by
  -- The scaled predecessor is visibly in the first range, and the boundary hypothesis supplies
  -- the second range witness after normalizing the exponent from `i - 1` to `i`.
  refine ⟨?_, ?_⟩
  · exact ⟨y, rfl⟩
  · refine ⟨z, ?_⟩
    have hi_nonneg : 0 ≤ (i - 1) + 1 := by omega
    have hpred_nonneg : 0 ≤ i - 1 := by omega
    have hpow : Int.toNat ((i - 1) + 1) = Int.toNat (i - 1) + 1 := by
      have hpred : Int.ofNat (Int.toNat (i - 1)) = i - 1 := Int.toNat_of_nonneg hpred_nonneg
      apply Int.ofNat.inj
      calc
        Int.ofNat (Int.toNat ((i - 1) + 1)) = (i - 1) + 1 := Int.toNat_of_nonneg hi_nonneg
        _ = Int.ofNat (Int.toNat (i - 1)) + 1 := by rw [hpred]
        _ = Int.ofNat (Int.toNat (i - 1) + 1) := by simp
    exact
      (show
        (LinearMap.lsmul A (K.X ((i - 1) + 1)) (f ^ Int.toNat ((i - 1) + 1))) z =
          (K.d (i - 1) ((i - 1) + 1)).hom (f ^ Int.toNat (i - 1) • y) from by
        calc
      (LinearMap.lsmul A (K.X ((i - 1) + 1)) (f ^ Int.toNat ((i - 1) + 1))) z =
          f ^ Int.toNat ((i - 1) + 1) • z := by
        rfl
      _ = (f ^ Int.toNat (i - 1) * f) • z := by
            rw [hpow, pow_succ]
      _ = f ^ Int.toNat (i - 1) • (f • z) := by rw [mul_smul]
      _ = (K.d (i - 1) ((i - 1) + 1)).hom (f ^ Int.toNat (i - 1) • y) := by
            rw [_root_.map_smul, hy])

/-- Helper for Lemma 15.96.2: after including into owner cycles, the cocycle comparison is just
the visibly scaled ambient cycle representative. -/
private theorem cyclesToEtaCycles_iCycles
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    cyclesToEtaCycles f K i ≫ (η[f] K).iCycles i =
      ModuleCat.ofHom (cyclesToEtaXLinear f K i) := by
  -- The defining property of `liftCycles'` identifies the lifted map after composing with the
  -- cycles inclusion.
  change
    (η[f] K).liftCycles'
        (ModuleCat.ofHom (cyclesToEtaXLinear f K i))
        (i + 1) (by simp) (cyclesToEtaX_comp_d_eq_zero f K i) ≫
          (η[f] K).iCycles i =
      ModuleCat.ofHom (cyclesToEtaXLinear f K i)
  simpa [HomologicalComplex.liftCycles'] using
    (HomologicalComplex.liftCycles_i
      (K := η[f] K)
      (k := ModuleCat.ofHom (cyclesToEtaXLinear f K i))
      (j := i + 1)
      (hj := by simp)
      (hk := cyclesToEtaX_comp_d_eq_zero f K i))

/-- Helper for Lemma 15.96.2: the owner cocycle comparison sends a cycle to the visibly scaled
ambient representative in `η_f K`. -/
private theorem cyclesToEtaCycles_iCycles_apply_val
    (f : A) (K : ModuleComplex A) (i : ℤ) (q : K.cycles i) :
    Subtype.val (((η[f] K).iCycles i).hom ((cyclesToEtaCycles f K i).hom q)) =
      f ^ Int.toNat i • (K.iCycles i).hom q := by
  -- Evaluate the stabilized `liftCycles'` computation on `q`, then forget the subtype in the
  -- degree term of `η[f] K`.
  have hpoint :=
    congrArg
      (fun k : K.cycles i ⟶ (η[f] K).X i ↦ k.hom q)
      (cyclesToEtaCycles_iCycles f K i)
  change ((η[f] K).iCycles i).hom ((cyclesToEtaCycles f K i).hom q) =
    (cyclesToEtaXLinear f K i) q at hpoint
  simpa [cyclesToEtaXLinear] using congrArg Subtype.val hpoint

/-- Helper for Lemma 15.96.2: in positive degree, a predecessor equation `d y = f • z`
produces the corresponding predecessor boundary in `η[f] K`. -/
private theorem eta_prev_boundary_witness_of_d_eq_smul
    (f : A) (K : ModuleComplex A) (i : ℤ) (hi : 0 < i)
    (q : K.cycles i) (y : K.X (i - 1))
    (hy : (K.d (i - 1) i).hom y = f • (K.iCycles i).hom q) :
    ∃ b : (η[f] K).X (i - 1),
      ((η[f] K).d (i - 1) i).hom b =
        ((η[f] K).iCycles i).hom ((cyclesToEtaCycles f K i).hom q) := by
  have hprev : (i - 1) + 1 = i := by omega
  cases hprev
  let b : (η[f] K).X (i - 1) :=
    ⟨f ^ Int.toNat (i - 1) • y,
      predecessor_scale_mem_degreeSubmodule_of_d_eq_smul
        (f := f) (K := K) (i := i) (hi := hi)
        (z := (K.iCycles i).hom q) (y := y) hy⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  -- Compare both elements in the ambient degree-`i` module of `K`.
  have hpow : Int.toNat i = Int.toNat (i - 1) + 1 := by
    have hi_nonneg : 0 ≤ i := by omega
    have hpred_nonneg : 0 ≤ i - 1 := by omega
    apply Int.ofNat.inj
    calc
      Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hi_nonneg
      _ = (i - 1) + 1 := by omega
      _ = Int.ofNat (Int.toNat (i - 1)) + 1 := by
            rw [Int.toNat_of_nonneg hpred_nonneg]
      _ = Int.ofNat (Int.toNat (i - 1) + 1) := by simp
  calc
    Subtype.val (((η[f] K).d (i - 1) i).hom b) =
        (K.d (i - 1) i).hom (f ^ Int.toNat (i - 1) • y) := by
          simp [complex, differentialLinear, b]
    _ = f ^ Int.toNat i • (K.iCycles i).hom q := by
          calc
            (K.d (i - 1) i).hom (f ^ Int.toNat (i - 1) • y) =
                f ^ Int.toNat (i - 1) • (K.d (i - 1) i).hom y := by
                  rw [_root_.map_smul]
            _ = f ^ Int.toNat (i - 1) • (f • (K.iCycles i).hom q) := by rw [hy]
            _ = (f ^ Int.toNat (i - 1) * f) • (K.iCycles i).hom q := by
                  rw [mul_smul]
            _ = f ^ Int.toNat i • (K.iCycles i).hom q := by
                  rw [hpow, pow_succ]
    _ = Subtype.val (((η[f] K).iCycles i).hom ((cyclesToEtaCycles f K i).hom q)) := by
          symm
          exact cyclesToEtaCycles_iCycles_apply_val f K i q

/-- Helper for Lemma 15.96.2: if `d y = f • z` in positive degree, then the scaled class of `z`
already vanishes in `H^i(η_f K)`. -/
private theorem cyclesToEtaHomology_eq_zero_of_smul_eq_boundary
    (f : A) (K : ModuleComplex A) (i : ℤ) (hi : 0 < i)
    (q : K.cycles i) (y : K.X (i - 1))
    (hy : (K.d (i - 1) i).hom y = f • (K.iCycles i).hom q) :
    (cyclesToEtaHomology f K i).hom q = 0 := by
  -- Use the packaged predecessor witness in `η[f] K`, then descend to homology via the owner
  -- boundary criterion.
  rcases eta_prev_boundary_witness_of_d_eq_smul f K i hi q y hy with ⟨b, hb⟩
  exact
    (homologyπ_eq_zero_iff_exists_prev_boundary
      (K := η[f] K) (j := i) (q := (cyclesToEtaCycles f K i).hom q)).2
      ⟨b, hb⟩

/-- Helper for Lemma 15.96.2: if `d x = f • q` in degree `i + 1`, then the homology class of `q`
is `f`-torsion. -/
private theorem homology_class_mem_torsionBy_of_d_eq_smul
    (f : A) (K : ModuleComplex A) (i : ℤ)
    {x : K.X i} {q : K.cycles (i + 1)}
    (hqx : (K.d i (i + 1)).hom x = f • (K.iCycles (i + 1)).hom q) :
    (K.homologyπ (i + 1)).hom q ∈ Submodule.torsionBy A (K.homology (i + 1)) f := by
  have hprev : (i + 1) - 1 = i := by omega
  cases hprev
  -- Show that the scaled cycle `f • q` already vanishes in homology, which is exactly the
  -- `f`-torsion condition.
  rw [Submodule.mem_torsionBy_iff]
  have hzero : (K.homologyπ (i + 1)).hom (f • q) = 0 := by
    apply
      (homologyπ_eq_zero_iff_exists_prev_boundary
        (K := K) (j := i + 1) (q := f • q)).2
    refine ⟨x, ?_⟩
    calc
      (K.d i (i + 1)).hom x = f • (K.iCycles (i + 1)).hom q := hqx
      _ = (K.iCycles (i + 1)).hom (f • q) := by
            symm
            rw [_root_.map_smul]
  calc
    f • (K.homologyπ (i + 1)).hom q = (K.homologyπ (i + 1)).hom (f • q) := by
      symm
      rw [_root_.map_smul]
    _ = 0 := hzero

-- Proof sketch: if a class in `H^i(K)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ Int.toNat i` becomes a boundary in `η_f K`; this is exactly the kernel
-- statement proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^i(K)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0] (hK : IsTermwiseFTorsionFree f K) :
    Submodule.torsionBy A (K.homology i) f ≤
      LinearMap.ker (homologyToEtaHomology f K i).hom := by
  intro x hx
  rw [LinearMap.mem_ker]
  rw [Submodule.mem_torsionBy_iff] at hx
  have hsurj : Function.Surjective (K.homologyπ i).hom :=
    (ModuleCat.epi_iff_surjective (K.homologyπ i)).1 inferInstance
  obtain ⟨q, rfl⟩ := hsurj x
  by_cases hi_neg : i < 0
  · -- In negative degree the owner homology is zero on a bounded-below complex.
    let hzero : CategoryTheory.Limits.IsZero (K.homology i) := K.isZero_of_isGE 0 i hi_neg
    letI : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero hzero
    have hq0 : (K.homologyπ i).hom q = 0 := Subsingleton.elim _ _
    simpa [hq0]
  · by_cases hi_zero : i = 0
    · -- In degree `0`, vanishing of `f • [q]` forces `f • q = 0`; regularity on cycles then gives
      -- `q = 0`.
      subst i
      have hscaled : (K.homologyπ i).hom (f • q) = 0 := by
        calc
          (K.homologyπ 0).hom (f • q) = f • (K.homologyπ 0).hom q := by
            rw [_root_.map_smul]
          _ = 0 := hx
      rcases
          (homologyπ_eq_zero_iff_exists_prev_boundary
            (K := K) (j := 0) (q := f • q)).1 hscaled with
        ⟨b, hb⟩
      let hzeroPrev : CategoryTheory.Limits.IsZero (K.X (-1)) :=
        K.isZero_of_isStrictlyGE 0 (-1) (by omega)
      letI : Subsingleton (K.X (0 - 1)) := by
        simpa using (ModuleCat.subsingleton_of_isZero hzeroPrev)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hcycle_zero : (K.iCycles 0).hom (f • q) = 0 := by
        calc
          (K.iCycles 0).hom (f • q) = (K.d (0 - 1) 0).hom b := by
            simpa using hb.symm
          _ = 0 := by simpa [hb0]
      have hiCycles_inj : Function.Injective (K.iCycles 0).hom :=
        (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
      have hqsmul0 : f • q = 0 := by
        apply hiCycles_inj
        simpa using hcycle_zero
      have hcycles_reg : IsSMulRegular (K.cycles 0) f :=
        (hK.isSMulRegular 0).of_injective
          (K.iCycles 0).hom
          ((ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance)
      have hq0 : q = 0 :=
        hcycles_reg.right_eq_zero_of_smul hqsmul0
      have hmap :
          (homologyToEtaHomology f K 0).hom ((K.homologyπ 0).hom q) =
            (cyclesToEtaHomology f K 0).hom q := by
        simpa using
          congrArg
            (fun g : K.cycles 0 ⟶ (η[f] K).homology 0 ↦
              g.hom q)
            (homologyToEtaHomology_homologyπ f K 0)
      rw [hmap]
      simpa [hq0]
    · have hi_pos : 0 < i := by omega
      -- In positive degree, `f • [q] = 0` produces an ambient predecessor of `f • q`, which is
      -- exactly the textbook input for the repaired eta-boundary criterion.
      have hscaled : (K.homologyπ i).hom (f • q) = 0 := by
        calc
          (K.homologyπ i).hom (f • q) = f • (K.homologyπ i).hom q := by
            rw [_root_.map_smul]
          _ = 0 := hx
      rcases
          (homologyπ_eq_zero_iff_exists_prev_boundary
            (K := K) (j := i) (q := f • q)).1 hscaled with
        ⟨y, hy⟩
      have hy' : (K.d (i - 1) i).hom y = f • (K.iCycles i).hom q := by
        calc
          (K.d (i - 1) i).hom y = (K.iCycles i).hom (f • q) := hy
          _ = f • (K.iCycles i).hom q := by rw [_root_.map_smul]
      have heta :
          (cyclesToEtaHomology f K i).hom q = 0 :=
        cyclesToEtaHomology_eq_zero_of_smul_eq_boundary f K i hi_pos q y hy'
      have hmap :
          (homologyToEtaHomology f K i).hom ((K.homologyπ i).hom q) =
            (cyclesToEtaHomology f K i).hom q := by
        simpa using
          congrArg
            (fun g : K.cycles i ⟶ (η[f] K).homology i ↦ g.hom q)
            (homologyToEtaHomology_homologyπ f K i)
      rw [hmap]
      exact heta

/-- Helper for Lemma 15.96.2: on the valid bounded-below owner branch, the comparison map from
homology modulo `f`-torsion to the Berthelot-Ogus homology is the canonical quotient lift of
`homologyToEtaHomology`. -/
abbrev homologyComparisonOfRegular
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0] (hK : IsTermwiseFTorsionFree f K) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A] (η[f] K).homology i :=
  (Submodule.torsionBy A (K.homology i) f).liftQ
    (homologyToEtaHomology f K i).hom
    (torsionBy_le_ker_homologyToEtaHomology f K i hK)

/-- The canonical comparison map
`H^i(K) / H^i(K)[f] → H^i(η_f K)` induced by multiplication by `f ^ Int.toNat i`. -/
abbrev homologyComparison (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0] :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A] (η[f] K).homology i :=
  if hK : IsTermwiseFTorsionFree f K then
    homologyComparisonOfRegular f K i hK
  else
    0

/-- Helper for Lemma 15.96.2: the bounded-below owner comparison is bijective on the valid
regular branch. -/
theorem homologyComparisonOfRegular_bijective
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseFTorsionFree f K) :
    Function.Bijective (homologyComparisonOfRegular f K i hK) := by
  -- TODO: run the textbook surjectivity/injectivity argument on the repaired regular branch,
  -- using `torsionBy_le_ker_homologyToEtaHomology` for the quotient lift and `hf`, `hK` for the
  -- injectivity step.
  sorry

-- Proof sketch: surjectivity comes from the description of cocycles in `η_f K` as
-- `f ^ Int.toNat i` times cocycles of `K`. For injectivity, if `f ^ Int.toNat i z` is a boundary
-- in `η_f K`, the textbook argument rewrites it using the previous degree and the
-- `f`-torsion-free hypotheses together with the assumption that `f` is a nonzerodivisor to
-- conclude that the class of `z` is `f`-torsion. This bridge statement is valid only for
-- bounded-below `ℤ`-indexed complexes.
/-- The canonical comparison map `H^i(K) / H^i(K)[f] → H^i(η_f K)` is bijective for bounded-below
`ℤ`-indexed complexes under the nonzerodivisor and termwise `f`-torsion-free hypotheses. -/
theorem homologyComparison_bijective
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseFTorsionFree f K) :
    Function.Bijective (homologyComparison f K i) := by
  -- On the valid branch, the public comparison map is definitionally the repaired canonical lift.
  simpa [homologyComparison, hK] using
    homologyComparisonOfRegular_bijective f K i hf hK

/-- The canonical comparison
`H^i(K) / H^i(K)[f] ≃ H^i(η_f K)` for bounded-below `ℤ`-indexed complexes under the
nonzerodivisor and termwise `f`-torsion-free hypotheses. -/
noncomputable abbrev homologyComparisonEquiv
    (f : A) (K : ModuleComplex A) (i : ℤ)
    [K.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseFTorsionFree f K) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) ≃ₗ[A] (η[f] K).homology i :=
  LinearEquiv.ofBijective
    (homologyComparison f K i)
    (homologyComparison_bijective f K i hf hK)

end BerthelotOgusInt

open BerthelotOgusInt

/-- A nonnegative cochain complex is termwise `f`-torsion free if multiplication by `f` is
injective in every degree. This is the source-facing owner predicate for Lemma `15.96.2`. -/
class IsTermwiseFTorsionFree (f : A) (M : NatModuleCochainComplex A) : Prop where
  /-- Multiplication by `f` is injective in degree `n`. -/
  isSMulRegular (n : ℕ) : IsSMulRegular (M.X n) f

/-- The source-facing owner predicate is equivalent to degreewise `f`-regularity. -/
theorem isTermwiseFTorsionFree_iff
    (f : A) (M : NatModuleCochainComplex A) :
    IsTermwiseFTorsionFree f M ↔ ∀ n : ℕ, IsSMulRegular (M.X n) f := by
  constructor
  · intro h n
    exact h.isSMulRegular n
  · intro h
    exact ⟨h⟩

instance (f : A) (M : NatModuleCochainComplex A) [h : IsTermwiseFTorsionFree f M] (n : ℕ) :
    IsSMulRegular (M.X n) f :=
  h.isSMulRegular n

namespace IsTermwiseFTorsionFree

/-- Passing to the extension by zero gives the bounded-below `ℤ`-indexed bridge predicate. -/
theorem toIsTermwiseFTorsionFree
    {f : A} {M : NatModuleCochainComplex A} (hM : IsTermwiseFTorsionFree f M) :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) := by
  constructor
  intro i
  by_cases hi : 0 ≤ i
  · -- In nonnegative degrees, extension by zero identifies the term with the original degree.
    let e :
        ((M.extend ComplexShape.embeddingUpNat).X i) ≃ₗ[A] M.X i.toNat :=
      (M.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hi)).toLinearEquiv
    exact (LinearEquiv.isSMulRegular_congr e f).2 (hM.isSMulRegular i.toNat)
  · -- In negative degrees, the extended complex is zero, so regularity is automatic.
    let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X i) :=
      M.isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hni
        exact hi (hni ▸ Int.natCast_nonneg n))
    letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact IsSMulRegular.of_right_eq_zero_of_smul (fun x _hx => Subsingleton.elim _ _)

end IsTermwiseFTorsionFree

instance (f : A) (M : NatModuleCochainComplex A) [hM : IsTermwiseFTorsionFree f M] :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) :=
  hM.toIsTermwiseFTorsionFree

/-- The degree-`n` Berthelot-Ogus term for a nonnegative complex. This is the source-facing owner
for the bounded-below Berthelot-Ogus construction. -/
abbrev etaFDegreeSubmodule (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    Submodule A (M.X n) :=
  LinearMap.range (LinearMap.lsmul A (M.X n) (f ^ n)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1)))).comap (M.d n (n + 1)).hom

-- Proof sketch: if `x` lies in the defining intersection for degree `n`, then `d(x)` already
-- lies in the required range for degree `n + 1`; the second condition for `d(x)` is automatic
-- because `d ∘ d = 0`, and `0` belongs to every range.
/-- The differential of `M` sends the degree-`n` Berthelot-Ogus term into degree `n + 1`. -/
private theorem etaFDifferential_mem
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : etaFDegreeSubmodule f M n) :
    M.d n (n + 1) x ∈ etaFDegreeSubmodule f M (n + 1) := by
  -- The first intersection condition is already built into the defining data of `x`.
  refine ⟨?_, ?_⟩
  · simpa [etaFDegreeSubmodule] using x.2.2
  · -- The second condition is automatic from `d ∘ d = 0`.
    refine ⟨0, ?_⟩
    calc
      ((LinearMap.lsmul A (M.X ((n + 1) + 1)) (f ^ ((n + 1) + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (M.d (n + 1) ((n + 1) + 1))) ((ConcreteCategory.hom (M.d n (n + 1))) x) :=
        (LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (M.d_comp_d n (n + 1) ((n + 1) + 1))) x).symm

/-- The degree-`n` differential on the source-facing Berthelot-Ogus complex `η_f M`. -/
private abbrev etaFDifferentialLinear
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    etaFDegreeSubmodule f M n →ₗ[A] etaFDegreeSubmodule f M (n + 1) :=
  ((M.d n (n + 1)).hom.comp (etaFDegreeSubmodule f M n).subtype).codRestrict
    (etaFDegreeSubmodule f M (n + 1))
    (etaFDifferential_mem f M n)

-- Proof sketch: `η_f M` uses the same differentials as `M`, only codomain-restricted to the
-- defining submodules. Hence the square of two successive differentials is the restriction of
-- `d ∘ d = 0` on `M`.
/-- The successive differentials of `η_f M` compose to zero. -/
private theorem etaFDifferential_sq (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDifferentialLinear f M n) ≫
        ModuleCat.ofHom (etaFDifferentialLinear f M (n + 1)) =
      0 := by
  -- Forgetting the codomain restrictions reduces the claim to the square-zero differential on `M`.
  ext x
  simp [etaFDifferentialLinear]
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (M.d_comp_d n (n + 1) ((n + 1) + 1))) x

/-- The source-facing Berthelot-Ogus complex `η_f M` on `NatModuleCochainComplex A`. -/
def etaFComplex (f : A) (M : NatModuleCochainComplex A) : NatModuleCochainComplex A :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
    (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
    (fun n ↦ etaFDifferential_sq f M n)

notation "η[" f "] " M:arg => etaFComplex f M

/-- Helper for Lemma 15.96.2: the degreewise `extendXIso` identifies the first scaled-range
condition in the Berthelot-Ogus term. -/
private theorem extendXIso_mem_scaled_range_iff
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    x ∈ LinearMap.range
        (LinearMap.lsmul A ((M.extend ComplexShape.embeddingUpNat).X (n : ℤ))
          (f ^ Int.toNat (n : ℤ))) ↔
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv x) ∈
        LinearMap.range (LinearMap.lsmul A (M.X n) (f ^ n)) := by
  let e := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  constructor
  · rintro ⟨y, rfl⟩
    -- Transport the range witness through the degreewise linear equivalence.
    refine ⟨e y, ?_⟩
    simp [e, LinearMap.lsmul_apply]
  · rintro ⟨y, hy⟩
    -- Pull the range witness back along the inverse equivalence.
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    simpa [e, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.96.2: after applying the successor-degree `extendXIso`, the extended
differential becomes the original differential in consecutive nonnegative degrees. -/
private theorem extendXIso_d_apply
    (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv)
        (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) =
      (M.d n (n + 1)).hom
        (((M.extendXIso ComplexShape.embeddingUpNat
            (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x) := by
  let e0 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  let e1 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv
  -- Rewrite the extended differential once using `extend_d_eq`, then cancel the successor
  -- degree identification by applying `e1`.
  have hd :=
    congrArg ModuleCat.Hom.hom
      (HomologicalComplex.extend_d_eq
        (K := M) (e := ComplexShape.embeddingUpNat)
        (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ))
        (i := n) (j := n + 1) (by simp : ((n : ℕ) : ℤ) = (n : ℤ))
        (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1))
  have hd' := LinearMap.congr_fun hd x
  rw [hd']
  change e1 (e1.symm ((M.d n (n + 1)).hom (e0 x))) =
      (M.d n (n + 1)).hom (e0 x)
  simp

/-- Helper for Lemma 15.96.2: the degreewise `extendXIso` identifies the differential-image
scaled-range condition in the Berthelot-Ogus term. -/
private theorem extendXIso_d_mem_scaled_range_iff
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) ∈
        LinearMap.range
          (LinearMap.lsmul A
            ((M.extend ComplexShape.embeddingUpNat).X ((n + 1 : ℕ) : ℤ))
            (f ^ Int.toNat (((n + 1 : ℕ) : ℤ)))) ↔
      (M.d n (n + 1)).hom
          (((M.extendXIso ComplexShape.embeddingUpNat
              (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x) ∈
        LinearMap.range (LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1))) := by
  let y :=
    ((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x
  -- First transport the successor-degree scaled range, then rewrite the transported differential.
  constructor
  · intro hx
    have hx' :=
      (extendXIso_mem_scaled_range_iff (f := f) (M := M) (n := n + 1) (x := y)).1 hx
    have hx'' :
        ∃ z, f ^ (n + 1) • z =
          ((M.extendXIso ComplexShape.embeddingUpNat
                (by simp : (((n + 1 : ℕ) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ))).toLinearEquiv)
            (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) := by
      simpa [y] using hx'
    rcases hx'' with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← extendXIso_d_apply (M := M) (n := n) (x := x)]
    exact hz
  · intro hx
    rcases hx with ⟨z, hz⟩
    have hx' :
        ((M.extendXIso ComplexShape.embeddingUpNat
              (by simp : (((n + 1 : ℕ) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ))).toLinearEquiv y) ∈
          LinearMap.range (LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1))) := by
      refine ⟨z, ?_⟩
      have hy_eq :
          ((M.extendXIso ComplexShape.embeddingUpNat
                (by simp : (((n + 1 : ℕ) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ))).toLinearEquiv y) =
            (M.d n (n + 1)).hom
              (((M.extendXIso ComplexShape.embeddingUpNat
                    (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x) := by
        simpa [y] using extendXIso_d_apply (M := M) (n := n) (x := x)
      rw [hy_eq]
      exact hz
    exact (extendXIso_mem_scaled_range_iff (f := f) (M := M) (n := n + 1) (x := y)).2 hx'

/-- Helper for Lemma 15.96.2: membership in the owner-level degree term transports pointwise to
the source-facing degree term under the standard degree identification. -/
private theorem etaFDegreeSubmodule_transport_iff
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : (M.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :
    x ∈ degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ) ↔
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv x) ∈
        etaFDegreeSubmodule f M n := by
  constructor
  · intro hx
    -- Transport the two defining conditions of the intersection separately.
    refine ⟨?_, ?_⟩
    · exact (extendXIso_mem_scaled_range_iff (f := f) (M := M) (n := n) (x := x)).1 hx.1
    · exact (extendXIso_d_mem_scaled_range_iff (f := f) (M := M) (n := n) (x := x)).1 hx.2
  · intro hx
    -- Pull back the transported range witnesses to recover membership in the extended term.
    refine ⟨?_, ?_⟩
    · exact (extendXIso_mem_scaled_range_iff (f := f) (M := M) (n := n) (x := x)).2 hx.1
    · exact (extendXIso_d_mem_scaled_range_iff (f := f) (M := M) (n := n) (x := x)).2 hx.2

/-- The `ℤ`-indexed degree term on `M.extend embeddingUpNat` identifies with the source-facing
degree term on `M`. -/
private theorem etaFDegreeSubmodule_map_eq
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).map
        (M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv.toLinearMap =
      etaFDegreeSubmodule f M n := by
  let e := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv
  -- Route correction: replace the brittle global transport of the intersection/comap definition by
  -- a pointwise membership bridge under `extendXIso`.
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    -- The pointwise transport iff turns a mapped witness into source-facing membership.
    exact (etaFDegreeSubmodule_transport_iff (f := f) (M := M) (n := n) (x := x)).1 hx
  · intro hy
    rw [Submodule.mem_map]
    refine ⟨e.symm y, ?_, by simp [e]⟩
    -- Pull the source-facing membership back along the inverse degree identification.
    exact
      (etaFDegreeSubmodule_transport_iff (f := f) (M := M) (n := n) (x := e.symm y)).2
        (by simpa [e] using hy)

/-- The canonical linear equivalence from the bounded-below `ℤ`-indexed bridge term to the
source-facing degree term. -/
private noncomputable abbrev etaFDegreeSubmoduleLinearEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ) ≃ₗ[A]
      etaFDegreeSubmodule f M n :=
  (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.ofSubmodules _ _
    (etaFDegreeSubmodule_map_eq f M n)

/-- Helper for Lemma 15.96.2: after forgetting the target subtype, the degreewise bridge
equivalence is just the ambient `extendXIso` in degree `n`. -/
private theorem etaFDegreeSubmoduleLinearEquiv_subtype_comp
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (etaFDegreeSubmodule f M n).subtype.comp
        (etaFDegreeSubmoduleLinearEquiv f M n).toLinearMap =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv.toLinearMap).comp
        (degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).subtype := by
  -- Route correction: normalize the `LinearEquiv.ofSubmodules` bridge once so later proofs only
  -- see the ambient `extendXIso`.
  ext x
  rfl

/-- Helper for Lemma 15.96.2: on elements, the degreewise bridge equivalence is the ambient
degreewise `extendXIso`. -/
private theorem etaFDegreeSubmoduleLinearEquiv_apply
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)) :
    (((etaFDegreeSubmoduleLinearEquiv f M n) x : etaFDegreeSubmodule f M n) : M.X n) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x := by
  -- Evaluate the normalized subtype composition at the chosen element.
  exact LinearMap.congr_fun
    (etaFDegreeSubmoduleLinearEquiv_subtype_comp (f := f) (M := M) (n := n)) x

/-- Helper for Lemma 15.96.2: in successor degree, applying the bridge equivalence to the
owner-level restricted differential is the same as applying the ambient successor `extendXIso`
to the underlying extended differential value. -/
private theorem etaFDegreeSubmoduleLinearEquiv_differential_apply
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)) :
    (((etaFDegreeSubmoduleLinearEquiv f M (n + 1))
        (BerthelotOgusInt.differentialLinear f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)
          x) : etaFDegreeSubmodule f M (n + 1)) : M.X (n + 1)) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv)
        (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) := by
  -- Normalize the successor-degree bridge on the concrete owner differential output.
  simpa [BerthelotOgusInt.differentialLinear] using
    etaFDegreeSubmoduleLinearEquiv_apply
      (f := f) (M := M) (n := n + 1)
      (x := BerthelotOgusInt.differentialLinear f (M.extend ComplexShape.embeddingUpNat)
        (n : ℤ) x)

/-- Helper for Lemma 15.96.2: the differential square commutes pointwise after passing to the
ambient successor-degree module `M.X (n + 1)`. -/
private theorem etaFDegreeSubmoduleLinearEquiv_comm_apply
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (x : degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)) :
    Subtype.val (((η[f] M).d n (n + 1)).hom ((etaFDegreeSubmoduleLinearEquiv f M n) x)) =
      Subtype.val
        ((etaFDegreeSubmoduleLinearEquiv f M (n + 1))
          ((((η[f] (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
            x))) := by
  -- Route correction: compare only the ambient values of the two restricted differentials.
  have hleft :
      Subtype.val (((η[f] M).d n (n + 1)).hom ((etaFDegreeSubmoduleLinearEquiv f M n) x)) =
        (M.d n (n + 1)).hom
          ((((etaFDegreeSubmoduleLinearEquiv f M n) x : etaFDegreeSubmodule f M n) : M.X n)) := by
    -- `CochainComplex.of_d` exposes the chosen degree-`n` restricted differential of `η[f] M`.
    have hd_nat : (η[f] M).d n (n + 1) = ModuleCat.ofHom (etaFDifferentialLinear f M n) := by
      simpa [etaFComplex] using
        (CochainComplex.of_d
          (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
          (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
          (fun n ↦ etaFDifferential_sq f M n)
          n)
    rw [hd_nat]
    rfl
  rw [hleft]
  -- The bridge equivalence is `extendXIso` in degree `n`, so the left-hand differential is the
  -- ambient differential applied to the transported element.
  rw [etaFDegreeSubmoduleLinearEquiv_apply]
  -- The right-hand side is the successor-degree bridge applied to the owner differential, and the
  -- ambient values agree by `extendXIso_d_apply`.
  calc
    (M.d n (n + 1)).hom
        (((M.extendXIso ComplexShape.embeddingUpNat
            (by simp : ((n : ℕ) : ℤ) = (n : ℤ))).toLinearEquiv) x) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)).toLinearEquiv)
        (((M.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x) := by
          symm
          exact extendXIso_d_apply (M := M) (n := n) (x := x)
    _ =
        Subtype.val
          ((etaFDegreeSubmoduleLinearEquiv f M (n + 1))
            ((((η[f] (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom
              x))) := by
          symm
          simpa [BerthelotOgusInt.complex, BerthelotOgusInt.differentialLinear] using
            etaFDegreeSubmoduleLinearEquiv_differential_apply
              (f := f) (M := M) (n := n) (x := x)

/-- The degreewise bridge equivalences commute with the `ℤ`-indexed and `ℕ`-indexed
Berthelot-Ogus differentials. -/
private theorem etaFDegreeSubmoduleLinearEquiv_comm
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M n) ≫ (η[f] M).d n (n + 1) =
      (η[f] (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
        ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M (n + 1)) := by
  -- Route correction: package the transport-heavy square as an equality of ambient values on
  -- each element, then recover the morphism equality by subtype extensionality.
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  simpa using etaFDegreeSubmoduleLinearEquiv_comm_apply (f := f) (M := M) (n := n) (x := x)

/-- Restricting the `ℤ`-indexed Berthelot-Ogus complex on `M.extend ComplexShape.embeddingUpNat`
to nonnegative degrees recovers the source-facing complex `η[f] M`. -/
noncomputable def etaFExtendRestrictionIso
    (f : A) (M : NatModuleCochainComplex A) :
    (η[f] (M.extend ComplexShape.embeddingUpNat)).restriction (ComplexShape.embeddingUpIntGE 0) ≅
      η[f] M :=
  Hom.isoOfComponents
    (fun n ↦
      ((η[f] (M.extend ComplexShape.embeddingUpNat)).restrictionXIso
          (ComplexShape.embeddingUpIntGE 0) (by simp)) ≪≫
        (etaFDegreeSubmoduleLinearEquiv f M n).toModuleIso)
    (by
      rintro n _ rfl
      dsimp only
      have hn : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ) := by simp
      have hn1 : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ) := by simp
      rw [(η[f] (M.extend ComplexShape.embeddingUpNat)).restriction_d_eq
        (ComplexShape.embeddingUpIntGE 0) hn hn1]
      simpa using etaFDegreeSubmoduleLinearEquiv_comm f M n)

/-- The morphism of bounded-below Berthelot-Ogus complexes induced by a morphism of nonnegative
cochain complexes. This is the source-facing bridge obtained by transporting the owner-level
`BerthelotOgusInt.map` on `M.extend ComplexShape.embeddingUpNat` across
`etaFExtendRestrictionIso`. -/
def etaFMap (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N) :
    η[f] M ⟶ η[f] N :=
  (etaFExtendRestrictionIso f M).inv ≫
    restrictionMap
      (BerthelotOgusInt.map f (extendMap φ ComplexShape.embeddingUpNat))
      (ComplexShape.embeddingUpIntGE 0) ≫
    (etaFExtendRestrictionIso f N).hom

-- Proof sketch: if `x` is a cocycle, then `f ^ n x` lies in the image of multiplication by
-- `f ^ n`, and its differential is zero, hence also lies in the image of multiplication by
-- `f ^ (n + 1)`. Therefore `f ^ n x` defines a term of `η_f M` in degree `n`.
/-- Multiplication by `f ^ n` sends cocycles of `M` in degree `n` into the degree-`n` term of
`η_f M`. -/
private theorem cycleScale_mem_etaFDegreeSubmodule
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : M.cycles n) :
    ((LinearMap.lsmul A (M.X n) (f ^ n)).comp (M.iCycles n).hom) x ∈
      etaFDegreeSubmodule f M n := by
  -- The first range condition is tautological from the chosen witness.
  refine ⟨?_, ?_⟩
  · exact ⟨(M.iCycles n).hom x, rfl⟩
  · -- The cycle condition forces the differential of the scaled representative to vanish.
    have hcycle := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (M.iCycles_d n (n + 1))) x
    change (ModuleCat.Hom.hom (M.d n (n + 1))) ((ModuleCat.Hom.hom (M.iCycles n)) x) = 0 at hcycle
    refine ⟨0, ?_⟩
    calc
      ((LinearMap.lsmul A (M.X (n + 1)) (f ^ (n + 1))) 0) = 0 := by
        simp
      _ = (ModuleCat.Hom.hom (M.d n (n + 1)))
            (((LinearMap.lsmul A (M.X n) (f ^ n)).comp (M.iCycles n).hom) x) := by
          change 0 = (ModuleCat.Hom.hom (M.d n (n + 1))) (f ^ n • (ModuleCat.Hom.hom (M.iCycles n)) x)
          rw [_root_.map_smul, hcycle]
          simp

/-- Multiplication by `f ^ n` on cocycles, viewed as a morphism into the degree-`n` term of
`η_f M`. -/
abbrev cyclesToEtaXLinear (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n →ₗ[A] etaFDegreeSubmodule f M n :=
  ((LinearMap.lsmul A (M.X n) (f ^ n)).comp (M.iCycles n).hom).codRestrict
    (etaFDegreeSubmodule f M n) (cycleScale_mem_etaFDegreeSubmodule f M n)

-- Proof sketch: the source is already a cycle in `M`, so after multiplying by `f ^ n` its
-- differential is still zero. Since `η_f M` uses the restricted differential of `M`, the image in
-- degree `n` is a cocycle of `η_f M`.
/-- The scaled cocycle morphism lands in the cycles of `η_f M`. -/
theorem cyclesToEtaX_comp_d_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (cyclesToEtaXLinear f M n) ≫ (η[f] M).d n (n + 1) = 0 := by
  -- Route correction: the cocycle condition is expressed through `iCycles_d` on the kernel
  -- object `M.cycles n`, not by subtype membership.
  ext x
  simp [_root_.cyclesToEtaXLinear, etaFComplex, etaFDifferentialLinear]
  apply Subtype.ext
  change (ModuleCat.Hom.hom (M.d n (n + 1))) (f ^ n • (ModuleCat.Hom.hom (M.iCycles n)) x) = 0
  rw [_root_.map_smul]
  have hcycle := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (M.iCycles_d n (n + 1))) x
  change (ModuleCat.Hom.hom (M.d n (n + 1))) ((ModuleCat.Hom.hom (M.iCycles n)) x) = 0 at hcycle
  rw [hcycle, smul_zero]

/-- The cocycle-level comparison map from `M` to `η_f M` in degree `n`. -/
abbrev cyclesToEtaCycles (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n ⟶ (η[f] M).cycles n :=
  (η[f] M).liftCycles'
    (ModuleCat.ofHom (cyclesToEtaXLinear f M n))
    (n + 1) (by simp) (cyclesToEtaX_comp_d_eq_zero f M n)

/-- The homology-class map induced on cocycles by multiplication by `f ^ n`. -/
abbrev cyclesToEtaHomology (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.cycles n ⟶ (η[f] M).homology n :=
  cyclesToEtaCycles f M n ≫ (η[f] M).homologyπ n

/-- Helper for Lemma 15.96.2: multiplying a predecessor in degree `n - 1` by `f ^ n` produces a
valid degree-`n - 1` element of `η[f] M`. -/
private theorem boundary_scale_mem_etaFDegreeSubmodule
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : M.X n) :
    ((LinearMap.lsmul A (M.X n) (f ^ (n + 1))) x) ∈ etaFDegreeSubmodule f M n := by
  -- In the bounded-below case, the visible `f ^ (n + 1)` factor gives both defining witnesses.
  refine ⟨?_, ?_⟩
  · refine ⟨f • x, ?_⟩
    simp [LinearMap.lsmul_apply, pow_succ, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  · refine ⟨(M.d n (n + 1)).hom x, ?_⟩
    simpa [LinearMap.lsmul_apply] using
      (_root_.map_smul (ModuleCat.Hom.hom (M.d n (n + 1))) x (f ^ (n + 1))).symm

/-- Helper for Lemma 15.96.2: a boundary representative in degree `n` defines a canonical
predecessor in `η[f] M` whose differential is the scaled boundary in degree `n + 1`. -/
private abbrev boundaryToEtaFDegreeLinear
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.X n →ₗ[A] etaFDegreeSubmodule f M n :=
  (LinearMap.lsmul A (M.X n) (f ^ (n + 1))).codRestrict
    (etaFDegreeSubmodule f M n)
    (boundary_scale_mem_etaFDegreeSubmodule f M n)

/-- Helper for Lemma 15.96.2: the source map of the degree-`0` short complex is the zero
differential `d 0 0`, hence vanishes. -/
private theorem sc_zero_f_eq_zero
    (M : NatModuleCochainComplex A) :
    (M.sc 0).f = 0 := by
  -- At degree `0`, `ComplexShape.up ℕ` uses `prev 0 = 0`, so the short-complex source map is
  -- `d 0 0`, which vanishes because `0` is not related to itself.
  change M.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  simpa [CochainComplex.prev] using
    (M.shape 0 0 (by simp : ¬ (ComplexShape.up ℕ).Rel 0 0))

/-- Helper for Lemma 15.96.2: once the degree-`0` source map of `M.sc 0` is zero, the associated
boundary map into cycles is also zero. -/
private theorem sc_zero_toCycles_eq_zero
    (M : NatModuleCochainComplex A) :
    (M.sc 0).toCycles = 0 := by
  -- `toCycles` becomes zero after composing with the mono inclusion of cycles, so cancellation
  -- against that inclusion reduces the claim to `sc_zero_f_eq_zero`.
  rw [← cancel_mono ((M.sc 0).iCycles), ShortComplex.toCycles_i, sc_zero_f_eq_zero]
  symm
  simpa using
    (CategoryTheory.Limits.zero_comp :
      (0 : (M.sc 0).X₁ ⟶ (M.sc 0).cycles) ≫ (M.sc 0).iCycles =
        (0 : (M.sc 0).X₁ ⟶ (M.sc 0).X₂))

/-- Helper for Lemma 15.96.2: in successor degree, the source object of `M.sc (n + 1)` is the
expected predecessor term `M.X n`. -/
private theorem sc_succ_X₁_eq
    (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc (n + 1)).X₁ = M.X n := by
  -- Unfold the short-complex functor once; for `ComplexShape.up ℕ`, the predecessor of `n + 1`
  -- is `n`.
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']

/-- Helper for Lemma 15.96.2: in successor degree, the source map of `M.sc (n + 1)` is the
expected differential `d n (n + 1)` after identifying the source object with `M.X n`. -/
private theorem sc_succ_f_eq
    (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc (n + 1)).f =
      (CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫ M.d n (n + 1) := by
  -- Unfold the short-complex source map once; for `ComplexShape.up ℕ`, the predecessor of
  -- `n + 1` is `n`, so the source differential is the expected ambient differential.
  simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor']

/-- Helper for Lemma 15.96.2: in successor degree, `ShortComplex.toCycles_i` identifies the
ambient value of the boundary representative with the expected differential from degree `n`. -/
private theorem sc_succ_toCycles_i_apply
    (M : NatModuleCochainComplex A) (n : ℕ) (x : (M.sc (n + 1)).X₁) :
    (M.iCycles (n + 1)).hom (((M.sc (n + 1)).toCycles).hom x) =
      ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫ M.d n (n + 1)).hom x := by
  -- `ShortComplex.toCycles_i` turns the cycle representative back into the short-complex source
  -- map, and in successor degree that source map is exactly the differential `d n (n + 1)`.
  have htoCycles :
      ((M.sc (n + 1)).iCycles).hom (((M.sc (n + 1)).toCycles).hom x) =
        ((M.sc (n + 1)).f).hom x := by
    simpa using LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i (M.sc (n + 1)))) x
  have hf :
      ((M.sc (n + 1)).f).hom x =
        ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫ M.d n (n + 1)).hom x := by
    rw [sc_succ_f_eq]
    rfl
  simpa using htoCycles.trans hf

/-- Helper for Lemma 15.96.2: the left successor composite into `η[f] M` has ambient value
`f ^ (n + 1)` times the ambient cycle representative. -/
private theorem toCycles_comp_cyclesToEtaX_succ_apply_val
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : (M.sc (n + 1)).X₁) :
    Subtype.val
        ((((M.sc (n + 1)).toCycles ≫ ModuleCat.ofHom
          (cyclesToEtaXLinear f M (n + 1))).hom) x) =
      f ^ (n + 1) • (M.iCycles (n + 1)).hom (((M.sc (n + 1)).toCycles).hom x) := by
  -- Unfold the codomain restriction once to read the composite in the ambient module.
  rfl

/-- Helper for Lemma 15.96.2: the right successor composite has ambient value equal to the
ordinary differential of the scaled predecessor. -/
private theorem boundaryToEtaFDegree_comp_etaFDifferential_apply_val
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) (x : (M.sc (n + 1)).X₁) :
    Subtype.val
        ((((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫
          ModuleCat.ofHom (boundaryToEtaFDegreeLinear f M n) ≫
          (η[f] M).d n (n + 1)).hom) x) =
      (M.d n (n + 1)).hom
        (f ^ (n + 1) • ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)).hom x)) := by
  -- Compute the ambient value after the transport has already been applied to the input.
  have haux (y : M.X n) :
      Subtype.val
          ((((ModuleCat.ofHom (boundaryToEtaFDegreeLinear f M n) ≫
            (η[f] M).d n (n + 1)).hom) y)) =
        (M.d n (n + 1)).hom (f ^ (n + 1) • y) := by
    have hd_nat : (η[f] M).d n (n + 1) = ModuleCat.ofHom (etaFDifferentialLinear f M n) := by
      simpa [etaFComplex] using
        show
            (CochainComplex.of
              (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
              (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
              (fun n ↦ etaFDifferential_sq f M n)).d n (n + 1) =
            ModuleCat.ofHom (etaFDifferentialLinear f M n) by
          simp [CochainComplex.of]
    rw [hd_nat]
    rfl
  simpa using haux (((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)).hom) x)

/-- Helper for Lemma 15.96.2: in successor degree, the boundary representative obtained from
`(M.sc (n + 1)).toCycles` agrees in the ambient term of `η_f M` with the differential of the
scaled predecessor. -/
private theorem toCycles_comp_cyclesToEtaX_succ_eq_boundary
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc (n + 1)).toCycles ≫ ModuleCat.ofHom (cyclesToEtaXLinear f M (n + 1)) =
      (CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫
        ModuleCat.ofHom (boundaryToEtaFDegreeLinear f M n) ≫ (η[f] M).d n (n + 1) := by
  -- Route correction: compare the two maps before entering the cycles object of `η[f] M`; this
  -- is the cast-stable ambient equality needed for the successor boundary descent.
  apply ModuleCat.hom_ext
  ext x
  -- Both sides now live in the ambient module `M.X (n + 1)`, so only the linearity of `d`
  -- remains after the two normalization lemmas.
  calc
    Subtype.val
        ((((M.sc (n + 1)).toCycles ≫ ModuleCat.ofHom
          (cyclesToEtaXLinear f M (n + 1))).hom) x) =
      f ^ (n + 1) • (M.iCycles (n + 1)).hom (((M.sc (n + 1)).toCycles).hom x) := by
        rw [toCycles_comp_cyclesToEtaX_succ_apply_val]
    _ = f ^ (n + 1) • ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n) ≫ M.d n (n + 1)).hom x) := by
        rw [sc_succ_toCycles_i_apply]
    _ = (M.d n (n + 1)).hom
          (f ^ (n + 1) • ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)).hom x)) := by
        rw [_root_.map_smul]
        rfl
    _ =
      Subtype.val
        ((((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫
          ModuleCat.ofHom (boundaryToEtaFDegreeLinear f M n) ≫
          (η[f] M).d n (n + 1)).hom) x) := by
        symm
        exact boundaryToEtaFDegree_comp_etaFDifferential_apply_val f M n x

/-- Helper for Lemma 15.96.2: the successor-degree branch of the cocycle comparison kills
boundaries once the ambient boundary identity is known. -/
private theorem toCycles_comp_cyclesToEtaHomology_succ_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc (n + 1)).toCycles ≫ cyclesToEtaHomology f M (n + 1) = 0 := by
  -- Route correction: first rewrite the lifted cycles map in ambient degree `n + 1`, then apply
  -- the standard `liftCycles` boundary-to-zero lemma on `η[f] M`.
  have hk :
      ((M.sc (n + 1)).toCycles ≫ ModuleCat.ofHom (_root_.cyclesToEtaXLinear f M (n + 1))) ≫
          (η[f] M).d (n + 1) (n + 2) =
        0 := by
    -- The source map already lands in cycles of `η[f] M`, so the successor differential vanishes.
    simpa [Category.assoc] using
      congrArg
        (((M.sc (n + 1)).toCycles) ≫ ·)
        (_root_.cyclesToEtaX_comp_d_eq_zero f M (n + 1))
  have hcomp :
      (M.sc (n + 1)).toCycles ≫ _root_.cyclesToEtaCycles f M (n + 1) =
        (η[f] M).liftCycles
            ((M.sc (n + 1)).toCycles ≫
              ModuleCat.ofHom (_root_.cyclesToEtaXLinear f M (n + 1)))
            (n + 2) (by simp) hk := by
    -- Reassociate the lifted cycles map so that the ambient successor composite becomes the input
    -- of `liftCycles`.
    simpa [_root_.cyclesToEtaCycles] using
      (HomologicalComplex.comp_liftCycles
        (η[f] M)
        (ModuleCat.ofHom (_root_.cyclesToEtaXLinear f M (n + 1)))
        (n + 2) (by simp)
        (_root_.cyclesToEtaX_comp_d_eq_zero f M (n + 1))
        ((M.sc (n + 1)).toCycles))
  -- The normalized composite is a boundary in degree `n + 1`, hence its homology class vanishes.
  change
    (M.sc (n + 1)).toCycles ≫ _root_.cyclesToEtaCycles f M (n + 1) ≫
        (η[f] M).homologyπ (n + 1) =
      0
  rw [← Category.assoc]
  rw [hcomp]
  simpa [Category.assoc] using
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (η[f] M)
      (((M.sc (n + 1)).toCycles ≫
        ModuleCat.ofHom (_root_.cyclesToEtaXLinear f M (n + 1))))
      (n + 2) (by simp)
      ((CategoryTheory.eqToHom (sc_succ_X₁_eq M n)) ≫
        ModuleCat.ofHom (boundaryToEtaFDegreeLinear f M n))
      (toCycles_comp_cyclesToEtaX_succ_eq_boundary f M n)

-- Proof sketch: a boundary in degree `n` is represented by `d(y)` from degree `n - 1`. After
-- multiplying by `f ^ n`, this becomes the boundary of the corresponding scaled predecessor in
-- the subcomplex `η_f M`, so its class in `H^n(η_f M)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc n).toCycles ≫ cyclesToEtaHomology f M n = 0 := by
  cases n with
  | zero =>
      -- In degree `0`, the short-complex boundary map already vanishes, so the descended
      -- comparison is the zero morphism.
      rw [sc_zero_toCycles_eq_zero]
      simpa using
        (CategoryTheory.Limits.zero_comp :
          (0 : (M.sc 0).X₁ ⟶ M.cycles 0) ≫ _root_.cyclesToEtaHomology f M 0 = 0)
  | succ n =>
      -- Positive degrees are reduced to the dedicated successor boundary computation.
      exact toCycles_comp_cyclesToEtaHomology_succ_eq_zero f M n

/-- The homology comparison map `H^n(M) → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyToEtaHomology (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.homology n ⟶ (η[f] M).homology n :=
  (M.sc n).descHomology
    (cyclesToEtaHomology f M n)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f M n)

/-- Helper for Lemma 15.96.2: the descended source-facing comparison map evaluates on a homology
class represented by a cycle by first applying the cocycle-level comparison. -/
private theorem homologyToEtaHomology_homologyπ
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.homologyπ n ≫ homologyToEtaHomology f M n =
      cyclesToEtaHomology f M n := by
  -- Route correction: descend through the short-complex API once, so later kernel arguments can
  -- work on explicit cycle representatives instead of unfolding `descHomology` repeatedly.
  change
    (M.sc n).homologyπ ≫
        (M.sc n).descHomology
          (cyclesToEtaHomology f M n)
          (toCycles_comp_cyclesToEtaHomology_eq_zero f M n) =
      cyclesToEtaHomology f M n
  -- This is exactly the defining computation rule for `descHomology` on `M.sc n`.
  exact
    ShortComplex.π_descHomology (S := M.sc n)
      (k := cyclesToEtaHomology f M n)
      (hk := toCycles_comp_cyclesToEtaHomology_eq_zero f M n)

/-- Helper for Lemma 15.96.2: in a short complex of `A`-modules, a homology class vanishes
exactly when its cycle representative is a boundary. -/
private theorem shortComplex_homologyπ_eq_zero_iff_exists_boundary
    (S : ShortComplex (ModuleCat A)) [S.HasHomology] (q : S.cycles) :
    S.homologyπ.hom q = 0 ↔
      ∃ b : S.X₁, S.moduleCatToCycles b = S.moduleCatCyclesIso.hom q := by
  have hcomm :
      S.homologyπ ≫ S.moduleCatHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Compare abstract homology with the concrete quotient of cycles by boundaries.
    simpa using S.π_moduleCatCyclesIso_hom
  constructor
  · intro hq
    -- Evaluating at `q` moves vanishing into the concrete quotient.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- A boundary witness is zero in the concrete quotient and hence also in homology.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1 inferInstance
    have h0 : 0 = S.moduleCatHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.96.2: in degree `n` of a nonnegative cochain complex, a homology class
vanishes exactly when its cycle representative comes from the boundary map of `M.sc n`. -/
private theorem nat_homologyπ_eq_zero_iff_exists_boundary
    (M : NatModuleCochainComplex A) (n : ℕ) (q : M.cycles n) :
    (M.homologyπ n).hom q = 0 ↔
      ∃ b : (M.sc n).X₁, (M.sc n).moduleCatToCycles b = (M.sc n).moduleCatCyclesIso.hom q := by
  -- Rewrite degree-`n` homology through the canonical short complex `M.sc n`.
  simpa [HomologicalComplex.homologyπ, ShortComplex.homologyπ] using
    (shortComplex_homologyπ_eq_zero_iff_exists_boundary (M.sc n) q)

-- Proof sketch: if a class in `H^n(M)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ n` becomes a boundary in `η_f M`; this is exactly the kernel statement
-- proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^n(M)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    Submodule.torsionBy A (M.homology n) f ≤
      LinearMap.ker (homologyToEtaHomology f M n).hom := by
  -- Route correction: transport the repaired owner kernel theorem across
  -- `M.extend ComplexShape.embeddingUpNat`, using the degree-`0` restriction bridge only where
  -- the standard restriction homology API stops.
  -- TODO: combine the owner theorem for `M.extend ComplexShape.embeddingUpNat` with
  -- `extendHomologyIso_torsionBy_map`, `restrictionHomologyIso_nat_of_isStrictlyGE`, and the
  -- transported `homologyToEtaHomology` identification.
  sorry

/-- Helper for Lemma 15.96.2: on the valid source-facing branch, the comparison map from homology
modulo `f`-torsion to the Berthelot-Ogus homology is the canonical quotient lift of
`homologyToEtaHomology`. -/
abbrev homologyComparisonOfRegular
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) →ₗ[A] (η[f] M).homology n :=
  (Submodule.torsionBy A (M.homology n) f).liftQ
    (homologyToEtaHomology f M n).hom
    (torsionBy_le_ker_homologyToEtaHomology f M n hM)

/-- The canonical comparison map
`H^n(M) / H^n(M)[f] → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyComparison (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) →ₗ[A] (η[f] M).homology n :=
  if hM : IsTermwiseFTorsionFree f M then
    homologyComparisonOfRegular f M n hM
  else
    0

/-- Helper for Lemma 15.96.2: the canonical homology identification
`M.extend embeddingUpNat` transports `f`-torsion submodules exactly. -/
private theorem extendHomologyIso_torsionBy_map
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f).map
        (M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv.toLinearMap =
      Submodule.torsionBy A (M.homology n) f := by
  -- Membership in `torsionBy` is preserved by the degreewise homology equivalence.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f at hy
    change ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv y) ∈
      Submodule.torsionBy A (M.homology n) f
    rw [Submodule.mem_torsionBy_iff] at hy ⊢
    simpa using congrArg
      ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).hom) hy
  · intro hx
    refine ⟨(M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv x, ?_, by simp⟩
    change ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv x) ∈
      Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    simpa using congrArg
      ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).inv) hx

/-- Helper for Lemma 15.96.2: in positive degrees, restriction from a bounded-below `ℤ`-indexed
complex to nonnegative degrees computes the same homology. The degree-`0` case is the only place
where the standard `restrictionHomologyIso` API does not apply directly. -/
private noncomputable def restrictionCyclesIso_nat_zero
    (K : ModuleComplex A) [K.IsStrictlyGE 0] :
    (K.restriction (ComplexShape.embeddingUpIntGE 0)).cycles 0 ≅ K.cycles (0 : ℤ) := by
  let Kr := K.restriction (ComplexShape.embeddingUpIntGE 0)
  let Sr : ShortComplex (ModuleCat A) := Kr.sc' 0 0 1
  let Sf : ShortComplex (ModuleCat A) := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) :=
    K.restrictionXIso (ComplexShape.embeddingUpIntGE 0) (by simp)
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) :=
    K.restrictionXIso (ComplexShape.embeddingUpIntGE 0) (by simp)
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp [CochainComplex.prev]
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Restricting in degree `0` only inserts the standard `restrictionXIso` identifications.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpIntGE 0)
      (i' := (0 : ℤ)) (j' := (1 : ℤ)) (by simp) (by simp)]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Route correction: compare degree-`0` cycles first, before passing to homology on either side.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      CategoryTheory.Limits.kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 15.96.2: in degree `0`, restricting a bounded-below `ℤ`-indexed complex to
nonnegative degrees does not change homology. -/
private noncomputable def restrictionHomologyIso_nat_of_isStrictlyGE
    (K : ModuleComplex A) [K.IsStrictlyGE 0] (n : ℕ) :
    (K.restriction (ComplexShape.embeddingUpIntGE 0)).homology n ≅ K.homology (n : ℤ) := by
  cases n with
  | zero =>
      -- Route correction: the source proof computes degree `0` by replacing the predecessor term
      -- with `0` using `K.X (-1) = 0`, rather than forcing `restrictionHomologyIso`.
      let Kr := K.restriction (ComplexShape.embeddingUpIntGE 0)
      let eCycles := restrictionCyclesIso_nat_zero (A := A) K
      let eπr : Kr.homology 0 ≅ Kr.cycles 0 := (CochainComplex.isoHomologyπ₀ Kr).symm
      have hzero_prev : K.d (-1) 0 = 0 := by
        -- The predecessor term `K.X (-1)` is zero on a bounded-below complex, so the incoming
        -- degree-`0` differential vanishes.
        exact (K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
      let eπf : K.cycles (0 : ℤ) ≅ K.homology (0 : ℤ) :=
        K.isoHomologyπ (-1) 0 (by simp) hzero_prev
      -- Compare the restricted and full degree-`0` cycles, then transport to homology on each
      -- side by the standard degree-`0` identifications.
      exact eπr ≪≫ eCycles ≪≫ eπf
  | succ n =>
      -- In successor degree, the predecessor and successor both stay in the embedding range, so
      -- the standard restriction homology comparison applies directly.
      simpa using
        (HomologicalComplex.restrictionHomologyIso
          K (ComplexShape.embeddingUpIntGE 0) n (n + 1) (n + 2)
          (by simp) (by simp)
          (by simp : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ))
          (by simp : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ))
          (by norm_num : (ComplexShape.embeddingUpIntGE 0).f (n + 2) = ((n + 2 : ℕ) : ℤ))
          (by simp)
          (by
            calc
              (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) := by
                simpa using (CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ)))
              _ = ((n + 2 : ℕ) : ℤ) := by omega))

/-- Helper for Lemma 15.96.2: the owner-side `η_f` homology of the extension by zero transports
back to the source-facing `η_f` homology in degree `n`. -/
private noncomputable def etaF_homology_transport_nat
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (η[f] (M.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅ (η[f] M).homology n :=
  (restrictionHomologyIso_nat_of_isStrictlyGE
      (A := A) (K := η[f] (M.extend ComplexShape.embeddingUpNat)) n).symm ≪≫
    HomologicalComplex.homologyMapIso (etaFExtendRestrictionIso f M) n

/-- Helper for Lemma 15.96.2: a linear equivalence transports quotient modules once the source
submodule maps exactly onto the target submodule. -/
private noncomputable def quotientLinearEquiv_of_submodule_map_eq
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (S : Submodule A V) (T : Submodule A W)
    (hST : S.map e.toLinearMap = T) :
    (V ⧸ S) ≃ₗ[A] (W ⧸ T) := by
  let hForward : S ≤ Submodule.comap e.toLinearMap T := by
    intro x hx
    change e x ∈ T
    rw [← hST]
    exact ⟨x, hx, rfl⟩
  let hBackward : T ≤ Submodule.comap e.symm.toLinearMap S := by
    intro y hy
    change e.symm y ∈ S
    have hy' : y ∈ S.map e.toLinearMap := by
      simpa [hST] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    simpa using hx
  let f : (V ⧸ S) →ₗ[A] (W ⧸ T) := Submodule.mapQ S T e.toLinearMap hForward
  let g : (W ⧸ T) →ₗ[A] (V ⧸ S) := Submodule.mapQ T S e.symm.toLinearMap hBackward
  -- Check the two quotient maps on representatives; the ambient composites are identities.
  exact
    LinearEquiv.ofLinear f g
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hg :
            g (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e.symm x) : V ⧸ S) := by
          simpa [g] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) x
        rw [hg]
        have hf :
            f (Submodule.Quotient.mk (e.symm x)) =
              (Submodule.Quotient.mk (e (e.symm x)) : W ⧸ T) := by
          simpa [f] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) (e.symm x)
        rw [hf]
        simp)
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hf :
            f (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e x) : W ⧸ T) := by
          simpa [f] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) x
        rw [hf]
        have hg :
            g (Submodule.Quotient.mk (e x)) =
              (Submodule.Quotient.mk (e.symm (e x)) : V ⧸ S) := by
          simpa [g] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) (e x)
        rw [hg]
        simp)

/-- Helper for Lemma 15.96.2: transporting the owner-side Berthelot-Ogus comparison equivalence
through the extension/restriction bridge yields the expected source and target objects in degree
`n`. -/
-- Route correction: the degree-safe target transport is now factored through
-- `restrictionHomologyIso_nat_of_isStrictlyGE` and `etaF_homology_transport_nat`. The remaining
-- work is the pre-quotient comparison identifying the transported owner map with the repaired
-- regular-branch source-facing `homologyComparisonOfRegular`.
private noncomputable abbrev transportedHomologyComparisonEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) ≃ₗ[A] (η[f] M).homology n :=
  let eQ :=
    quotientLinearEquiv_of_submodule_map_eq
      ((M.extendHomologyIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv)
      (Submodule.torsionBy A ((M.extend ComplexShape.embeddingUpNat).homology (n : ℤ)) f)
      (Submodule.torsionBy A (M.homology n) f)
      (extendHomologyIso_torsionBy_map f M n)
  -- Transport the owner equivalence first across the source quotient bridge, then across the
  -- target homology bridge back to the bounded-below `ℕ`-indexed complex.
  (eQ.symm.trans
      (BerthelotOgusInt.homologyComparisonEquiv
        f (M.extend ComplexShape.embeddingUpNat) (n : ℤ) hf hM.toIsTermwiseFTorsionFree)).trans
    (etaF_homology_transport_nat f M n).toLinearEquiv

-- Proof sketch: surjectivity comes from the description of cocycles in `η_f M` as `f ^ n`
-- times cocycles of `M`. For injectivity, if `f ^ n z` is a boundary in `η_f M`, the textbook
-- argument rewrites it using the previous degree and the `f`-torsion-free hypotheses together
-- with the assumption that `f` is a nonzerodivisor to conclude that the class of `z` is
-- `f`-torsion.
/-- Helper for Lemma 15.96.2: the source-facing comparison is bijective on the valid regular
branch. -/
theorem homologyComparisonOfRegular_bijective
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    Function.Bijective (homologyComparisonOfRegular f M n hM) := by
  -- TODO: identify `homologyComparisonOfRegular` with the linear map underlying
  -- `transportedHomologyComparisonEquiv`, then read off bijectivity from that transported owner
  -- equivalence.
  sorry

/-- Lemma `15.96.2`: for an `ℕ`-indexed cochain complex of `A`-modules that is termwise
`f`-torsion free, the canonical Berthelot-Ogus comparison map
`H^n(M^\bullet) / H^n(M^\bullet)[f] → H^n(η_f M^\bullet)` is bijective under the nonzerodivisor
hypothesis. -/
theorem homologyComparison_bijective
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    Function.Bijective (_root_.homologyComparison f M n) := by
  -- On the valid branch, the public source-facing comparison is definitionally the repaired
  -- canonical lift, so the theorem reduces to the regular-branch bijectivity statement.
  simpa [_root_.homologyComparison, hM] using
    (_root_.homologyComparisonOfRegular_bijective f M n hf hM)

/-- The canonical comparison
`H^n(M^\bullet) / H^n(M^\bullet)[f] ≃ H^n(η_f M^\bullet)` under the nonzerodivisor and termwise
`f`-torsion-free hypotheses. -/
noncomputable abbrev homologyComparisonEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) ≃ₗ[A] (η[f] M).homology n :=
  LinearEquiv.ofBijective
    (_root_.homologyComparison f M n)
    (_root_.homologyComparison_bijective f M n hf hM)

end
