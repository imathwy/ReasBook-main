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
    K.d i (i + 1) x ∈ degreeSubmodule f K (i + 1) := sorry

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
      0 := sorry

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
    φ.f i x ∈ degreeSubmodule f L i := sorry

/-- The degree-`i` component of the morphism induced on Berthelot-Ogus complexes by `φ`. -/
abbrev mapLinear
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    degreeSubmodule f K i →ₗ[A] degreeSubmodule f L i :=
  ((φ.f i).hom.comp (degreeSubmodule f K i).subtype).codRestrict
    (degreeSubmodule f L i)
    (map_mem_degreeSubmodule f φ i)

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
      (ModuleCat.ofHom (mapLinear f φ j)) := sorry

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
    (map f φ).f i = ModuleCat.ofHom (mapLinear f φ i) := sorry

-- Proof sketch: if `x` is a cocycle, then `f ^ Int.toNat i x` lies in the image of multiplication
-- by `f ^ Int.toNat i`, and its differential is zero, hence also lies in the image of
-- multiplication by `f ^ Int.toNat (i + 1)`. Therefore `f ^ Int.toNat i x` defines a term of
-- `η_f K` in degree `i`.
/-- Multiplication by `f ^ Int.toNat i` sends cocycles of `K` in degree `i` into the degree-`i`
term of `η_f K`. -/
private theorem cycleScale_mem_degreeSubmodule
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.cycles i) :
    ((LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)).comp (K.iCycles i).hom) x ∈
      degreeSubmodule f K i := sorry

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
    ModuleCat.ofHom (cyclesToEtaXLinear f K i) ≫ (η[f] K).d i (i + 1) = 0 := sorry

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

-- Proof sketch: a boundary in degree `i` is represented by `d(y)` from degree `i - 1`. After
-- multiplying by `f ^ Int.toNat i`, this becomes the boundary of the corresponding scaled
-- predecessor in the subcomplex `η_f K`, so its class in `H^i(η_f K)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (K.sc i).toCycles ≫ cyclesToEtaHomology f K i = 0 := sorry

/-- The homology comparison map `H^i(K) → H^i(η_f K)` induced by multiplication by
`f ^ Int.toNat i`. -/
abbrev homologyToEtaHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.homology i ⟶ (η[f] K).homology i :=
  (K.sc i).descHomology
    (cyclesToEtaHomology f K i)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f K i)

-- Proof sketch: if a class in `H^i(K)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ Int.toNat i` becomes a boundary in `η_f K`; this is exactly the kernel
-- statement proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^i(K)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    Submodule.torsionBy A (K.homology i) f ≤
      LinearMap.ker (homologyToEtaHomology f K i).hom := sorry

/-- The canonical comparison map
`H^i(K) / H^i(K)[f] → H^i(η_f K)` induced by multiplication by `f ^ Int.toNat i`. -/
abbrev homologyComparison (f : A) (K : ModuleComplex A) (i : ℤ) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A] (η[f] K).homology i :=
  (Submodule.torsionBy A (K.homology i) f).liftQ
    (homologyToEtaHomology f K i).hom
    (torsionBy_le_ker_homologyToEtaHomology f K i)

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
    Function.Bijective (homologyComparison f K i) := sorry

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
  sorry

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
    M.d n (n + 1) x ∈ etaFDegreeSubmodule f M (n + 1) := sorry

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
      0 := sorry

/-- The source-facing Berthelot-Ogus complex `η_f M` on `NatModuleCochainComplex A`. -/
def etaFComplex (f : A) (M : NatModuleCochainComplex A) : NatModuleCochainComplex A :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
    (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
    (fun n ↦ etaFDifferential_sq f M n)

notation "η[" f "] " M:arg => etaFComplex f M

/-- The `ℤ`-indexed degree term on `M.extend embeddingUpNat` identifies with the source-facing
degree term on `M`. -/
private theorem etaFDegreeSubmodule_map_eq
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ)).map
        (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.toLinearMap =
      etaFDegreeSubmodule f M n := by
  sorry

/-- The canonical linear equivalence from the bounded-below `ℤ`-indexed bridge term to the
source-facing degree term. -/
private noncomputable abbrev etaFDegreeSubmoduleLinearEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (n : ℤ) ≃ₗ[A]
      etaFDegreeSubmodule f M n :=
  (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.ofSubmodules _ _
    (etaFDegreeSubmodule_map_eq f M n)

/-- The degreewise bridge equivalences commute with the `ℤ`-indexed and `ℕ`-indexed
Berthelot-Ogus differentials. -/
private theorem etaFDegreeSubmoduleLinearEquiv_comm
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M n) ≫ (η[f] M).d n (n + 1) =
      (η[f] (M.extend ComplexShape.embeddingUpNat)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
        ModuleCat.ofHom (etaFDegreeSubmoduleLinearEquiv f M (n + 1)) := by
  sorry

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
      etaFDegreeSubmodule f M n := sorry

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
    ModuleCat.ofHom (cyclesToEtaXLinear f M n) ≫ (η[f] M).d n (n + 1) = 0 := sorry

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

-- Proof sketch: a boundary in degree `n` is represented by `d(y)` from degree `n - 1`. After
-- multiplying by `f ^ n`, this becomes the boundary of the corresponding scaled predecessor in
-- the subcomplex `η_f M`, so its class in `H^n(η_f M)` is zero.
/-- The cocycle-level comparison annihilates boundaries, so it descends to homology. -/
theorem toCycles_comp_cyclesToEtaHomology_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    (M.sc n).toCycles ≫ cyclesToEtaHomology f M n = 0 := sorry

/-- The homology comparison map `H^n(M) → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyToEtaHomology (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    M.homology n ⟶ (η[f] M).homology n :=
  (M.sc n).descHomology
    (cyclesToEtaHomology f M n)
    (toCycles_comp_cyclesToEtaHomology_eq_zero f M n)

-- Proof sketch: if a class in `H^n(M)` is killed by `f`, then multiplying a cocycle
-- representative by `f ^ n` becomes a boundary in `η_f M`; this is exactly the kernel statement
-- proved in the textbook argument.
/-- The homology comparison map kills the `f`-torsion in `H^n(M)`. -/
theorem torsionBy_le_ker_homologyToEtaHomology
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    Submodule.torsionBy A (M.homology n) f ≤
      LinearMap.ker (homologyToEtaHomology f M n).hom := sorry

/-- The canonical comparison map
`H^n(M) / H^n(M)[f] → H^n(η_f M)` induced by multiplication by `f ^ n`. -/
abbrev homologyComparison (f : A) (M : NatModuleCochainComplex A) (n : ℕ) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) →ₗ[A] (η[f] M).homology n :=
  (Submodule.torsionBy A (M.homology n) f).liftQ
    (homologyToEtaHomology f M n).hom
    (torsionBy_le_ker_homologyToEtaHomology f M n)

-- Proof sketch: surjectivity comes from the description of cocycles in `η_f M` as `f ^ n`
-- times cocycles of `M`. For injectivity, if `f ^ n z` is a boundary in `η_f M`, the textbook
-- argument rewrites it using the previous degree and the `f`-torsion-free hypotheses together
-- with the assumption that `f` is a nonzerodivisor to conclude that the class of `z` is
-- `f`-torsion.
/-- Lemma `15.96.2`: for an `ℕ`-indexed cochain complex of `A`-modules that is termwise
`f`-torsion free, the canonical Berthelot-Ogus comparison map
`H^n(M^\bullet) / H^n(M^\bullet)[f] → H^n(η_f M^\bullet)` is bijective under the nonzerodivisor
hypothesis. -/
theorem homologyComparison_bijective
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    Function.Bijective (homologyComparison f M n) := sorry

/-- The canonical comparison
`H^n(M^\bullet) / H^n(M^\bullet)[f] ≃ H^n(η_f M^\bullet)` under the nonzerodivisor and termwise
`f`-torsion-free hypotheses. -/
noncomputable abbrev homologyComparisonEquiv
    (f : A) (M : NatModuleCochainComplex A) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hM : IsTermwiseFTorsionFree f M) :
    ((M.homology n) ⧸ Submodule.torsionBy A (M.homology n) f) ≃ₗ[A] (η[f] M).homology n :=
  LinearEquiv.ofBijective
    (homologyComparison f M n)
    (homologyComparison_bijective f M n hf hM)

end
