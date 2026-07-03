import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Data.Int.Range
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.AtPrime.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_97_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped BigOperators
open scoped FittingIdeal

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CpxA ⥤ DModA)

/- Domain-style sampling:
- primary domain: determinantal ideals of bounded finite-free cochain complexes, expressed through
  the intrinsic Fitting ideal of the degree-`i` presentation map `(f, d^i)`;
- sampled owner declarations:
  `fittingIdeal`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the chapter Fitting-ideal owner `fittingIdeal`;
  `bridge/view`: the specific presentation map `etaPresentationLinearMap` and its quotient
    `etaPresentationQuotient`;
- primitive data vs. derived API: the primitive data are the presentation map and its quotient.
  The alternating rank tail is derived theorem-supporting data, and the pointwise rank helper stays
  internal. -/

/-- The linear map `(f, d^i) : M^i → M^i ⊕ M^{i + 1}` used to define the determinantal ideal
attached to `M^•` and `f` in degree `i`. -/
abbrev etaPresentationLinearMap (f : A) (M : CpxA) (i : ℤ) :
    M.X i →ₗ[A] M.X i × M.X (i + 1) :=
  LinearMap.prod ((f • LinearMap.id : M.X i →ₗ[A] M.X i)) (M.d i (i + 1)).hom

/-- The quotient module presented by `(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
abbrev etaPresentationQuotient (f : A) (M : CpxA) (i : ℤ) :=
  (M.X i × M.X (i + 1)) ⧸ LinearMap.range (etaPresentationLinearMap f M i)

/-- The rank of the `j`th term of a termwise finite free complex, computed by `Module.finrank`. -/
private def termwiseFiniteFreeRank (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M]
    (j : ℤ) : ℕ :=
  Module.finrank A (M.X j)

/-- The truncated alternating tail sum `∑_{j = i}^b (-1)^{j - i} rk(M^j)` for a termwise finite
free complex. -/
def alternatingRankTail (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M] (i b : ℤ) : ℤ :=
  ((Int.range i (b + 1)).map fun j ↦
      ((-1 : ℤ) ^ Int.toNat (j - i)) * (termwiseFiniteFreeRank M j : ℤ)).sum

/-- The ideal `I_i(M^•, f)`, defined intrinsically as the Fitting ideal of the cokernel of the map
`(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
def etaDeterminantalIdeal (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)

namespace EtaDeterminantalIdeal

scoped notation "I[" f "]_(" i ")(" M ")" => etaDeterminantalIdeal f M i

end EtaDeterminantalIdeal

open scoped EtaDeterminantalIdeal

local instance termwiseFiniteFreeTermModuleFree
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Free A (M.X j) :=
  inferInstance

local instance termwiseFiniteFreeTermModuleFinite
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Finite A (M.X j) :=
  inferInstance

-- Proof sketch: localize at each prime ideal and use Lemma `15.76.8` to replace derived-equivalent
-- bounded finite free complexes by stabilizations with finite direct sums of trivial two-term
-- complexes. The resulting determinantal ideals are compared case-by-case according to the degree
-- of the trivial summand, using the block-diagonal minors formula from Lemma `15.8.1`; this gives
-- the claimed equality after correcting by the shift in alternating tail ranks.
/-- Lemma 15.97.1: if bounded complexes `M^•` and `N^•` of finite free `A`-modules represent the
same object of `D(A)`, then the determinantal ideals `I_i(M^•, f)` and `I_i(N^•, f)` agree up to
a power of the nonzerodivisor `f`, with exponent shift measured by the alternating tail ranks. -/
theorem pow_etaDeterminantalIdeal_eq_of_same_derivedObject
    (f : A) (hf : IsRegular f) {M N : CpxA} (i : ℤ)
    [hMff : CochainComplex.IsTermwiseFiniteFree M]
    [hNff : CochainComplex.IsTermwiseFiniteFree N]
    {bM bN : ℤ} (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRankTail M i bM =
        (n : ℤ) + alternatingRankTail N i bN) :
    principalIdeal (f ^ m) * I[f]_(i)(M) =
      principalIdeal (f ^ n) * I[f]_(i)(N) := sorry

end

/-! ### Lemma_15_97_2 (from Chap15) -/
noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

/- Domain-style sampling:
- primary domain: determinantal ideals of cochain-complex presentation maps, expressed through the
  chapter Fitting-ideal owner API;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationLinearMap`,
  `etaPresentationQuotient`,
  `fittingIdeal_eq_of_linearEquiv`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting ideal of the presentation quotient;
  `bridge/view`: the quotient linear equivalence induced by rescaling the first summand by a unit.
- primitive data vs. derived API: the primitive data are the degree-`i` presentation map and its
  quotient. The invariance statement is derived by transporting that quotient along the canonical
  target automorphism `LinearEquiv.prodCongr (LinearEquiv.smulOfUnit u) (LinearEquiv.refl A _)`. -/

-- Proof sketch: rescaling the first summand of the target product by the unit `u` carries the
-- presentation map `(f, d^i)` to `((u : A) * f, d^i)`, so it induces a canonical linear
-- equivalence between the corresponding presentation quotients.
private noncomputable def etaPresentationQuotient_unitMulEquiv
    (f : A) (u : Aˣ) (M : CpxA) (i : ℤ) :
    etaPresentationQuotient f M i ≃ₗ[A] etaPresentationQuotient ((u : A) * f) M i :=
  let e :=
    LinearEquiv.prodCongr (LinearEquiv.smulOfUnit u) (LinearEquiv.refl A (M.X (i + 1)))
  let η := etaPresentationLinearMap f M i
  let ηu := etaPresentationLinearMap ((u : A) * f) M i
  let hη : ηu = e.toLinearMap.comp η := by
    ext x
    · change ((u : A) * f) • x = (u : A) • (f • x)
      rw [smul_smul]
    · rfl
  let hrange : LinearMap.range ηu = (LinearMap.range η).map e.toLinearMap := by
    simpa [hη] using LinearMap.range_comp η e.toLinearMap
  Submodule.Quotient.equiv (LinearMap.range η) (LinearMap.range ηu) e hrange.symm

/-- Lemma 15.97.2: multiplying `f` by a unit does not change the degree-`i` determinantal ideal
of a cochain complex. -/
theorem etaDeterminantalIdeal_eq_unit_mul
    (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (f : A) (u : Aˣ) :
    I[f]_(i)(M) = I[(u : A) * f]_(i)(M) := by
  let bi := Module.Free.chooseBasis A (M.X i)
  let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
  let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
    Module.Finite.of_basis (bi.prod bi1)
  let _ : Module.Finite A (etaPresentationQuotient f M i) :=
    Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
  simpa [etaDeterminantalIdeal] using
    fittingIdeal_eq_of_linearEquiv A
      (etaPresentationQuotient f M i)
      (Module.finrank A (M.X (i + 1)))
      (etaPresentationQuotient_unitMulEquiv f u M i)

end

/-! ### Lemma_15_97_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped FittingIdeal
open scoped TensorProduct

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv (M : CpxA) (i : ℤ) :
    ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
      ModuleCat B) ≃ₗ[B] (B ⊗[A] (M.X i)) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (M.X i)))

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFree
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] :
    Module.Free B
      ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
        ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Free.of_basis (b.map (extendScalarsTermLinearEquiv M i).symm)

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFinite
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] [Module.Finite A (M.X i)] :
    Module.Finite B
      ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M).X i :
        ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Finite.of_basis
    (b.map (extendScalarsTermLinearEquiv M i).symm)

/-
Domain-style sampling:
- primary domain: determinantal ideals for the Berthelot-Ogus presentation map `(f, d^i)` under
  tensor-product base change;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationQuotient`,
  `(ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting ideal together with the chapter base-change owner
    `fittingIdeal_baseChange`;
  `bridge/view`: the scalar-extended cochain complex
    `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`;
- primitive data vs. derived API: the primitive source-facing data are the presentation map
  `etaPresentationLinearMap f M i` and its quotient; the base-changed complex itself is derived
  bridge data, and the equality below is the source-facing statement. -/

-- Proof sketch: `etaDeterminantalIdeal` is the intrinsic Fitting ideal of
-- `etaPresentationQuotient f M i`. After scalar extension, the degree terms remain finite free by
-- the canonical tensor-product instances.
-- Comparing the scalar-extended quotient with the quotient attached to the canonical scalar
-- extension `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`
-- reduces the statement to the chapter owner
-- `fittingIdeal_baseChange`.
/-- Lemma 15.97.3: the degree-`i` determinantal ideal attached to `(f, d^i)` commutes with base
change along `A → B`. The primitive data are only the finite free terms in degrees `i` and
`i + 1`; boundedness and nonzerodivisor hypotheses are not needed for this base-change identity
itself. -/
theorem etaDeterminantalIdeal_baseChange
    (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    I[algebraMap A B f]_(i)(
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)) =
      Ideal.map (algebraMap A B)
        (I[f]_(i)(M)) := sorry

end

/-! ### Lemma_15_97_4 (from Chap15) -/
noncomputable section

open Matrix
open scoped nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

/- Domain-style sampling:
- primary domain: determinantal ideals of cochain-complex presentation maps, localized at a prime
  and compared with powers of a nonzerodivisor;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationLinearMap`,
  `fittingIdeal_eq_presentationFittingIdeal`,
  `fittingIdeal_baseChange`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting-ideal owner from `15.97.1`;
  `bridge/view`: the chosen-basis matrix of `etaPresentationLinearMap f M i`, used only to
    compare the owner with the classical maximal-minors presentation;
- primitive data vs. derived API: the primitive public data already live in `15.97.1` as the map
  `etaPresentationLinearMap f M i` and its quotient. The matrix formula here is derived bridge
  data and should not be a second owner. -/

-- Proof sketch: compute the intrinsic owner `etaDeterminantalIdeal` from the canonical quotient
-- presentation `etaPresentationQuotient f M i`, then identify that quotient with the cokernel of
-- the chosen matrix of `etaPresentationLinearMap f M i`.
/-- The intrinsic determinantal ideal `I_i(M^\bullet, f)` is computed from the maximal minors of
the chosen matrix of `(f, d^i)`. -/
theorem etaDeterminantalIdeal_def (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    let bi := Module.Free.chooseBasis A (M.X i)
    let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
    I[f]_(i)(M) =
      I_((Module.finrank A (M.X i)))(
        (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i))) := sorry

local instance etaDeterminantalIdealTermModuleFree
    {M : CpxA} [hMff : CategoryTheory.CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Free A (M.X j) :=
  (hMff j).1

local instance etaDeterminantalIdealTermModuleFinite
    {M : CpxA} [hMff : CategoryTheory.CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Finite A (M.X j) :=
  (hMff j).2

-- Proof sketch: localize at `p`, use the base-change formula for `I_i(M^\bullet, f)` and the
-- invariance under replacing `M^\bullet` by a quasi-isomorphic bounded finite free complex, then
-- apply the splitting result for complexes with free localized cohomology to replace `M^\bullet_p`
-- by the zero-differential complex on its cohomology. For a zero-differential complex, `(f, d^i)`
-- becomes `(f, 0)`, whose maximal minors generate a power of `f`.
/-- Lemma 15.97.4: let `A` be a ring, let `𝔭 ⊂ A` be a prime ideal, and let `f ∈ A` be a
nonzerodivisor. Let `M^\bullet` be a bounded complex of finite free `A`-modules. If
`H^i(M^\bullet)_𝔭` is free for all `i`, then `I_i(M^\bullet, f)_𝔭` is generated by a power of the
image of `f` for every `i`. -/
theorem etaDeterminantalIdeal_atPrime_eq_principalIdeal_pow_of_homology_free
    (p : PrimeSpectrum A) (f : A) (hf : f ∈ nonZeroDivisors A) (M : CpxA)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    [CategoryTheory.CochainComplex.IsTermwiseFiniteFree M]
    (hcohom :
      ∀ j : ℤ,
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M.homology j)))
    (i : ℤ) :
    let Aₚ := Localization.AtPrime p.asIdeal
    ∃ n : ℕ,
      Ideal.map (algebraMap A Aₚ) (I[f]_(i)(M)) =
        principalIdeal ((algebraMap A Aₚ f) ^ n) := sorry

end

/-! ### Lemma_15_97_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]
local notation "CpxA" => NatModuleCochainComplex A

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` for bounded-above `ℕ`-indexed cochain complexes, together
  with the degree-`i` determinantal ideal `I_i(M^•, f)`;
- sampled owner declarations:
  `_root_.etaDeterminantalIdeal`,
  `CochainComplex.IsStrictlyLE`,
  `etaFDegreeSubmodule`,
  `etaPairMap`,
  `Module.Free`,
  `Module.FiniteLocallyFreeOfRank`;
- best owner abstraction:
  `source-facing`: the two theorems of this file about `(η_f M)^i`, the unreduced map
    `(1, d^i)`, and the degree-`i` ideal `I_i(M^•, f)` on `M : NatModuleCochainComplex A`;
  `core/canonical`: the chapter owner `etaDeterminantalIdeal` on `ℤ`-indexed complexes together
    with the `ℤ`-indexed bounded-above predicate on `M.extend embeddingUpNat`;
  `bridge/view`: extension by zero along `embeddingUpNat`, used only internally to recall the
    `ℤ`-indexed determinantal-ideal owner and bounded-above predicate.
- primitive data vs derived API: the primitive public data are the degreewise finite-free terms of
  `M` and the nat-level ideal `M.etaDeterminantalIdeal f i`; the extension-by-zero presentation is
  derived bridge data and should not remain in theorem interfaces. -/

private noncomputable instance extend_embeddingUpNat_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X i)] :
    Module.Free A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X i)] :
    Module.Finite A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Finite.equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X (i + 1))] :
    Module.Free A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X (i + 1))] :
    Module.Finite A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Finite.equiv e.symm

namespace NatModuleCochainComplex

/-- A bounded-below complex is bounded above if its extension by zero vanishes above some
nonnegative degree. This keeps the `ℤ`-indexed support bridge internal to the owner. -/
abbrev IsBoundedAbove (M : CpxA) : Prop :=
  ∃ b : ℕ, CochainComplex.IsStrictlyLE (M.extend embeddingUpNat) (b : ℤ)

/-- The degree-`i` Berthelot-Ogus determinantal ideal `I_i(M^•, f)` for a bounded-below complex,
viewed through the canonical extension-by-zero bridge. -/
abbrev etaDeterminantalIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  _root_.etaDeterminantalIdeal f (M.extend embeddingUpNat) (i : ℤ)

end NatModuleCochainComplex

variable (f : A) (M : CpxA) (i : ℕ)
variable [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
variable [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
variable (hf : f ∈ nonZeroDivisors A)
variable (hI : (M.etaDeterminantalIdeal f i).IsPrincipal)

-- Proof sketch: after localizing at each prime, choose a generator of the principal ideal
-- `I_i(M^\bullet, f)` and apply Lemma `15.8.10` to the quotient by the torsion of the cokernel of
-- `(f, d^i)`. The textbook argument identifies `(η_f M)^i` with the kernel of `(d^i, -1)` inside
-- the split exact three-term complex built from `f^i M^i`, `f^(i + 1) M^i`, and
-- `f^(i + 1) M^(i + 1)`, which yields the claimed local freeness and rank.
/-- Lemma 15.97.5: if `f` is a nonzerodivisor in `A`, the terms `M^i` and `M^{i + 1}` are finite
free, and `I_i(M^\bullet, f)` is principal, then the degree-`i` term `(η_f M)^i` is finite locally
free of rank `rk(M^i)`. -/
theorem etaFDegree_finiteLocallyFreeOfRank_of_determinantalIdeal_isPrincipal
    :
    Module.FiniteLocallyFreeOfRank A ((η[f] M).X i) (Module.finrank A (M.X i)) := sorry

-- Proof sketch: with the same local normal form as in the rank statement, the image of
-- `(1, d^i)` identifies with the kernel of `(d^i, -1)` in a short exact sequence whose cokernel
-- is the torsion-free quotient controlled by Lemma `15.8.10`. The quotient is projective, so the
-- short exact sequence splits and `(1, d^i)` becomes the inclusion of a direct summand.
/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, the canonical map
`(1, d^i) : (η_f M)^i → f^i M^i × f^(i + 1) M^(i + 1)` is a split monomorphism, i.e. the
inclusion of a direct summand. -/
theorem etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
    :
    IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) := sorry

end

/-! ### Lemma_15_97_6 (from Chap15) -/
open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => NatModuleCochainComplex A
local notation "baseChange" =>
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A B)) (up ℕ)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv
    (K : CpxA) (i : ℕ) :
    ((((baseChange).obj K).X i : ModuleCat B)) ≃ₗ[B] (B ⊗[A] (K.X i)) := by
  simpa [Functor.mapHomologicalComplex_obj_X, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (K.X i)))

private theorem etaFDegreeSubmodule_toBaseChange_bijective
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    Function.Bijective ((etaFDegreeSubmodule f M i).toBaseChange B) := by
  sorry

private theorem etaFDegreeSubmodule_baseChange_map_eq
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    ((etaFDegreeSubmodule f M i).baseChange B).map
        ((extendScalarsTermLinearEquiv M i).symm.toLinearMap) =
      etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i := by
  sorry

private noncomputable def etaFDegreeTensorBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (B ⊗[A] (((η[f] M).X i : ModuleCat A))) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B := by
  simpa using
    (LinearEquiv.ofBijective
      ((etaFDegreeSubmodule f M i).toBaseChange B)
      (etaFDegreeSubmodule_toBaseChange_bijective f M hf hg hI i) :
        (B ⊗[A] etaFDegreeSubmodule f M i) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B)

private noncomputable def etaFDegreeBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (((baseChange).obj (η[f] M)).X i) ≅
      (η[algebraMap A B f] ((baseChange).obj M)).X i := by
  let eLeft :
      ((((baseChange).obj (η[f] M)).X i : ModuleCat B)) ≃ₗ[B]
        (B ⊗[A] (((η[f] M).X i : ModuleCat A))) :=
    extendScalarsTermLinearEquiv (η[f] M) i
  let eRight :
      (etaFDegreeSubmodule f M i).baseChange B ≃ₗ[B]
        etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i :=
    ((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _
      (etaFDegreeSubmodule_baseChange_map_eq f M hf hg hI i)
  exact ((eLeft.trans (etaFDegreeTensorBaseChangeIso f M hf hg hI i)).trans
    eRight).toModuleIso

private theorem etaFDegreeBaseChangeIso_comm_succ
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i (i + 1) =
      ((baseChange).obj (η[f] M)).d i (i + 1) ≫
        (etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom := by
  sorry

private theorem etaFDegreeBaseChangeIso_comm
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i j =
      ((baseChange).obj (η[f] M)).d i j ≫
        (etaFDegreeBaseChangeIso f M hf hg hI j).hom := by
  cases hij
  simpa using etaFDegreeBaseChangeIso_comm_succ f M hf hg hI i

/-
Domain-style sampling:
- primary domain: scalar extension of the source-facing Berthelot-Ogus complex `η[f] M` on
  `ℕ`-indexed cochain complexes of finite free modules;
- sampled owner declarations:
  `η[_] _`,
  `NatModuleCochainComplex.etaDeterminantalIdeal`,
  `etaDeterminantalIdeal_baseChange`,
  `etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction:
  `source-facing`: the canonical base-change isomorphism for `η[f] M`;
  `core/canonical`: the owners `η[_] _`, `NatModuleCochainComplex.etaDeterminantalIdeal`, and
    scalar extension by `baseChange`;
  `bridge/view`: the comparison between `baseChange.obj (η[f] M)` and
    `η[algebraMap A B f] (baseChange.obj M)`;
- primitive data vs derived API: the primitive data are the finite-free complex `M`, the
  nonzerodivisor hypotheses on `f` and its image, and principality of the source
  determinantal ideals. The comparison isomorphism is derived bridge data and should stay a direct
  named isomorphism rather than a wrapper around auxiliary comparison packages. -/

/-- Lemma 15.97.6: let `A → B` be a ring map, let `f ∈ A` be a nonzerodivisor, and let `M^\bullet`
be a complex of finite free `A`-modules. If the image of `f` in `B` is a nonzerodivisor and every
determinantal ideal `I_i(M^\bullet, f)` is principal, then the base change of `η_f M^\bullet` is
canonically isomorphic to `η_g(M^\bullet ⊗_A B)` for `g = algebraMap A B f`. No bounded-above
hypothesis is needed for this comparison. -/
noncomputable def etaFComplex_baseChangeIso_of_determinantalIdeal_isPrincipal
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ((baseChange).obj (η[f] M)) ≅ η[algebraMap A B f] ((baseChange).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (etaFDegreeBaseChangeIso f M hf hg hI)
    (etaFDegreeBaseChangeIso_comm f M hf hg hI)

end

/-! ### Lemma_15_97_7 (from Chap15) -/
open CategoryTheory
universe u v y

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module A N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module A N₂]

-- Proof sketch: choose a retraction `π` of `s`, form the induced endomorphisms of `M`
-- corresponding to the two projections `N₁ × N₂ → Nᵢ`, and let `J` be the finitely generated
-- ideal cutting out the locus where these endomorphisms become complementary idempotents. After
-- base change to `B`, the condition `J ≤ ker(algebraMap A B)` is equivalent to the base-changed
-- map identifying `B ⊗[A] M` with a product of submodules of the two ambient summands.
/-- Lemma 15.97.7: for a split injection of a finite projective `A`-module into `N₁ × N₂`, there
exists a finitely generated ideal `J` whose quotient detects exactly when every base change of the
map identifies `M` with a direct sum of submodules of the two base-changed summands. -/
theorem exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection
    [Module.Finite A M] [Module.Projective A M]
    (s : M →ₗ[A] N₁ × N₂)
    (hs : IsSplitMono (ModuleCat.ofHom s)) :
    ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type y) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔
          s.baseChangeIdentifiesWithProdSubmodules B := sorry

end

/-! ### Lemma_15_97_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped TensorProduct nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

local notation "CpxA" => NatModuleCochainComplex A
local notation "Q" => natComplexToDerived

/- Domain-style sampling:
- primary domain: splitting loci in commutative algebra for the reduced Berthelot-Ogus pair map
  `(1, d^i)` on `η_f M^•`;
- sampled owner declarations:
  `LinearMap.identifiesWithProdSubmodules`,
  `LinearMap.baseChangeIdentifiesWithProdSubmodules`,
  `exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection`,
  `BerthelotOgusEtaReduction.Nat.etaReductionPairMap`;
- best owner abstraction:
  `source-facing`: the degree-`i` ideal `J_i(M^•, f)` attached to a bounded-above
    `M : NatModuleCochainComplex A`, available only under the principal-ideal and splitting
    hypotheses that produce it;
  `core/canonical`: the reduced pair map `etaReductionPairMap f M i` together with the generic
    owner predicate `LinearMap.baseChangeIdentifiesWithProdSubmodules`;
  `bridge/view`: the universal-property predicate on ideals of `A ⧸ principalIdeal f`, together
    with the conditional chosen witness obtained after existence and uniqueness are established;
- primitive data vs derived API: the primitive public data are the complex `M`, the degree `i`,
  and the reduced pair map; the universal-property predicate and the conditional canonical ideal are
  derived API on that owner. -/

namespace NatModuleCochainComplex

/-- An ideal of `A / fA` has the universal property of `J_i(M^\bullet, f)` if its quotient cuts
out exactly the base changes where the reduced map `(1, d^i)` splits as a product of submodules. -/
abbrev etaReductionDecompositionIdealProperty
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type*) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

private abbrev etaReductionDecompositionIdealPropertySelf
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

/-- The universal property of `J_i(M^\bullet, f)` determines the ideal uniquely whenever such an
ideal exists. -/
theorem etaReductionDecompositionIdeal_eq_of_property
    (M : CpxA) (f : A) (i : ℕ)
    {J J' : Ideal (A ⧸ principalIdeal f)}
    (hJ : M.etaReductionDecompositionIdealProperty f i J)
    (hJ' : M.etaReductionDecompositionIdealProperty f i J') :
    J = J' := sorry

-- Proof sketch: Lemma `15.97.5` makes the degree-`i` unreduced pair map `(1, d^i)` a split
-- monomorphism with finite projective source over `A ⧸ (f)`, and Lemma `15.97.7` then supplies
-- the finitely generated ideal cutting out exactly the base changes where the reduced map
-- identifies its source with a product of submodules.
/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, there exists a finitely
generated ideal `J_i(M^\bullet, f)` in `A / fA` with the universal splitting property for the
reduced map `(1, d^i)`. -/
theorem exists_fg_etaReductionDecompositionIdeal_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ M.etaReductionDecompositionIdealProperty f i J := sorry

private theorem exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ etaReductionDecompositionIdealPropertySelf M f i J := sorry

/-- The degree-`i` ideal `J_i(M^\bullet, f)` in `A / fA`, defined only under the principal-ideal
hypothesis that guarantees its existence. -/
noncomputable def etaReductionDecompositionIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    Ideal (A ⧸ principalIdeal f) :=
  Classical.choose
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)

/-- The ideal `J_i(M^\bullet, f)` satisfies its defining universal splitting property. -/
theorem etaReductionDecompositionIdeal_property
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    M.etaReductionDecompositionIdealProperty f i
      (M.etaReductionDecompositionIdeal f i hf hI) := sorry

/-- The degree-`i` ideal `J_i(M^\bullet, f)` is finitely generated. -/
theorem etaReductionDecompositionIdeal_fg
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (M.etaReductionDecompositionIdeal f i hf hI).FG :=
  (Classical.choose_spec
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)).1

end NatModuleCochainComplex

namespace EtaReductionDecompositionIdeal

scoped notation "J[" f "]_(" i ")(" M " ; " hf ", " hI ")" =>
  NatModuleCochainComplex.etaReductionDecompositionIdeal M f i hf hI

end EtaReductionDecompositionIdeal

open scoped EtaReductionDecompositionIdeal

-- Proof sketch: apply Lemma `15.97.1` to the bounded-above extensions by zero of `M` and `N`.
-- After balancing the alternating-rank tails by suitable powers of `f`, the resulting equality
-- `f^m I_i(M^•, f) = f^n I_i(N^•, f)` and regularity of `f` show that principality of
-- `I_i(M^•, f)` forces principality of `I_i(N^•, f)`.
/-- The degree-`i` determinantal ideal is principal for `N^\bullet` as soon as it is principal for
`M^\bullet` and the two bounded-above finite free complexes represent the same derived object. This
is the bounded-below bridge/view of Lemma `15.97.1`, used below so that the source-facing equality
of the ideals `J_i` needs only the principality hypothesis on the `M`-side; the comparison
hypothesis stays on the chapter’s canonical theorem-level owner `CategoryTheory.IsIsomorphic`. -/
theorem etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (N.etaDeterminantalIdeal f i).IsPrincipal := sorry

-- Proof sketch: use the principal-ideal hypothesis together with Lemma `15.97.5` to see that the
-- reduced maps attached to `M` and `N` are split injections of finite projective modules over
-- `A / fA`. Lemma `15.97.7` identifies the corresponding universal splitting loci, while the
-- derived equivalence transports the reduced `η_f` complexes and their degree-`i` maps. The
-- source-facing ideals with that universal property are therefore equal.
/-- If `M^\bullet` and `N^\bullet` represent the same derived object, then any degree-`i` ideals
of `A / fA` satisfying the universal property of `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`
agree; the derived comparison is expressed through `CategoryTheory.IsIsomorphic`, not through a
chosen `Iso`. -/
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject_of_property
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    {JM JN : Ideal (A ⧸ principalIdeal f)}
    (hJM : M.etaReductionDecompositionIdealProperty f i JM)
    (hJN : N.etaReductionDecompositionIdealProperty f i JN) :
    JM = JN := sorry

-- Proof sketch: apply the preceding witness-equality theorem to the canonical ideals
-- `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`, using their defining universal properties from the
-- existence-and-uniqueness construction above. The principality hypothesis needed to define the
-- `N`-side ideal is derived internally from Lemma `15.97.1` via the bridge theorem just above.
/-- Lemma 15.97.8: if `f` is a nonzerodivisor in `A` and `M^\bullet`, `N^\bullet` are bounded
complexes of finite free `A`-modules representing the same derived object, then the canonical
degree-`i` ideals `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)` of `A / fA` are equal whenever the
degree-`i` determinantal ideal for `M^\bullet` is principal; the corresponding principality for
`N^\bullet` follows from Lemma `15.97.1`. -/
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    J[f]_(i)(M ; hf, hIM) =
      J[f]_(i)(N ; hf,
        etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
          f hf M N hMbounded hNbounded hMN i hIM) := sorry

end

/-! ### Lemma_15_97_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped nonZeroDivisors
open scoped EtaReductionDecompositionIdeal

universe u

section

variable {A : Type u} [CommRing A]

private abbrev baseChange
    {B : Type u} [CommRing B] [Algebra A B] :
    NatModuleCochainComplex A ⥤ NatModuleCochainComplex B :=
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A B)) (up ℕ)

/- Domain-style sampling:
- primary domain: commutative algebra of principal quotients and localizations for the
  Berthelot-Ogus `η_f` construction;
- sampled owner declarations:
  `principalIdeal`,
  `NatModuleCochainComplex.etaReductionDecompositionIdeal`,
  `ModFSquared.Nat.cyclesReductionSurjective`,
  `ModFSquared.Nat.bockstein`,
  `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`;
- best owner abstraction:
  `source-facing`: the sum ideal `J(M^\bullet, f)`, the quotient ring
    `C = (A / fA) / J(M^\bullet, f)`, and the vanishing set `E`;
  `core/canonical`: the principal quotient `A ⧸ principalIdeal f`, ideal images under
    `Ideal.Quotient.mk`, together with the localized Berthelot-Ogus reduction owners
    `ModFSquared.Nat.cyclesReductionSurjective` and `ModFSquared.Nat.bockstein`;
  `bridge/view`: the localized extension-by-zero complex of `M`;
- primitive data vs derived API: the primitive data are the canonical principal quotient
  `A ⧸ principalIdeal f`, the conditional degreewise ideals `J_i(M^\bullet, f)`, the sum ideal,
  and the quotient ring `C`; the vanishing criterion and the localization / finite presentation /
  finite locally free statements are derived API built from those owners. -/

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]

/-- The set `E` from Lemma `15.97.9`, formulated for a complex of finite free `A`-modules as the
primes containing `f` where every localized map `Ker(d^i mod f^2) → Ker(d^i mod f)` is
surjective in every nonnegative degree. When `f` is a nonzerodivisor in `A`, flatness of
localization makes its image a nonzerodivisor in each `Aₚ`, so Lemma `15.96.7` identifies the same
locus with vanishing of the localized Bockstein operators. -/
def etaReductionVanishingSet : Set (PrimeSpectrum A) :=
  { p : PrimeSpectrum A |
      let Aₚ := Localization.AtPrime p.asIdeal
      letI : CommRing Aₚ := inferInstance
      letI : Algebra A Aₚ := inferInstance
      let baseChangeAₚ : NatModuleCochainComplex A ⥤ NatModuleCochainComplex Aₚ := baseChange
      f ∈ p.asIdeal ∧
        ∀ i : ℕ,
          ModFSquared.Nat.cyclesReductionSurjective (algebraMap A Aₚ f) (baseChangeAₚ.obj M) i }

section

variable (hf : f ∈ nonZeroDivisors A)
variable (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)

/-- The ideal `J(M^\bullet, f) = \sum_i J_i(M^\bullet, f)` in `A / fA`, expressed as the supremum
of the conditional degreewise ideals from Lemma `15.97.8`. -/
def etaReductionDecompositionIdealSum :
    Ideal (A ⧸ principalIdeal f) :=
  ⨆ i : ℕ, J[f]_(i)(M ; hf, hI i)

/-- The quotient ring `C = (A / fA) / J(M^\bullet, f)`. -/
abbrev etaReductionDecompositionQuotient :=
  (A ⧸ principalIdeal f) ⧸ etaReductionDecompositionIdealSum f M hf hI

private abbrev etaReductionDecompositionPrime
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal) :=
  let hpV : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set A) :=
    (PrimeSpectrum.mem_zeroLocus p (principalIdeal f : Set A)).2 <| by
      simpa [principalIdeal] using (Ideal.span_singleton_le_iff_mem p.asIdeal).2 hpf
  (principalIdeal f).primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p, hpV⟩

/-- The localization of `J(M^\bullet, f)` at a prime `p` containing `f`. -/
def etaReductionDecompositionIdealSumLocalization
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal) :
    Ideal (Localization.AtPrime (etaReductionDecompositionPrime f p hpf).asIdeal) :=
  Ideal.map
    (algebraMap (A ⧸ principalIdeal f)
      (Localization.AtPrime (etaReductionDecompositionPrime f p hpf).asIdeal))
    (etaReductionDecompositionIdealSum f M hf hI)

-- Proof sketch: each degreewise ideal `J_i(M^\bullet, f)` is finitely generated by the universal
-- splitting criterion from Lemma `15.97.7`, applied to the split monomorphism from Lemma
-- `15.97.5`; boundedness implies `J_i(M^\bullet, f) = 0` for all sufficiently large `i`, so the
-- supremum `J(M^\bullet, f)` is a finite sum of finitely generated ideals.
/-- Lemma 15.97.9 (1): if `M^\bullet` is bounded above, then the ideal
`J(M^\bullet, f) = \sum_i J_i(M^\bullet, f)` of `A / fA` is finitely generated. -/
theorem etaReductionDecompositionIdealSum_fg
    (hbounded : M.IsBoundedAbove) :
    (etaReductionDecompositionIdealSum f M hf hI).FG := sorry

-- Proof sketch: `C` is the quotient of `A / fA` by the finitely generated ideal from part `(1)`,
-- and quotient maps by finitely generated ideals are ring maps of finite presentation.
/-- Lemma 15.97.9 (2): if `M^\bullet` is bounded above, then the quotient ring
`C = (A / fA) / J(M^\bullet, f)` is finitely presented over `A / fA`, so the canonical map
`A / fA → C` is surjective of finite presentation. -/
theorem etaReductionDecompositionQuotient_finitePresentation
    (hbounded : M.IsBoundedAbove) :
    Algebra.FinitePresentation (A ⧸ principalIdeal f)
      (etaReductionDecompositionQuotient f M hf hI) :=
  sorry

-- Proof sketch: the localized kernel-surjectivity hypothesis gives the direct-sum decomposition
-- in each degree via Lemma `15.96.8`; under the global nonzerodivisor hypothesis, flatness of
-- localization makes the image of `f` a nonzerodivisor in `Aₚ`, so Lemma `15.96.7` applies at
-- `p`. The universal property of the ideals `J_i(M^\bullet, f)` then forces every localized
-- `J_i` to vanish, hence so does their sum.
/-- Lemma 15.97.9 (3): if `M^\bullet` is bounded above and `p` belongs to the vanishing set
`E`, then the localization of `J(M^\bullet, f)` at the corresponding prime of `A / fA` is zero. -/
theorem etaReductionDecompositionIdealSumLocalization_eq_bot_of_mem_etaReductionVanishingSet
    (hbounded : M.IsBoundedAbove)
    (p : PrimeSpectrum A) (hp : p ∈ etaReductionVanishingSet f M) :
    etaReductionDecompositionIdealSumLocalization f M hf hI p hp.1 = ⊥ := sorry

end

end

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]

-- Proof sketch: after localizing at `p`, the assumed freeness of the nat-indexed cohomology of
-- `M` is transported internally to the bounded-above owner complex `M.extend embeddingUpNat`,
-- with negative degrees handled by the vanishing of the extension outside `ℕ`. Lemma `15.97.4`
-- then gives the power-of-`f` description of the determinantal ideals, hence the localized
-- `f`-torsion in homology vanishes. Flatness of localization then keeps the image of `f` a
-- nonzerodivisor, so Lemma `15.96.7` gives surjectivity of
-- `Ker(d^i mod f^2) → Ker(d^i mod f)` in every nonnegative degree.
/-- Lemma 15.97.9 (4): if `f` is a nonzerodivisor, `M^\bullet` is bounded above, `p` contains
`f`, and all localized cohomology modules `H^i(M^\bullet)_𝔭` in nonnegative degrees are free over
`A_𝔭`, then `p` belongs to the vanishing set `E`. -/
theorem mem_etaReductionVanishingSet_of_localizedHomology_free
    (hf : f ∈ nonZeroDivisors A)
    (hbounded : M.IsBoundedAbove)
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal)
    (hcohom :
      ∀ i : ℕ,
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M.homology i))) :
    p ∈ etaReductionVanishingSet f M := sorry

end

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
variable (hf : f ∈ nonZeroDivisors A)
variable (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)

-- Proof sketch: after quotienting by `J(M^\bullet, f)`, every degreewise reduced map
-- `(1, d^i)` identifies its source with a product of submodules by the defining universal property
-- of `J_i`; the differential then splits off matching direct summands degreewise, so each
-- cohomology module is a quotient of a finite locally free module by a direct summand and hence is
-- finite locally free.
/-- Lemma 15.97.9 (5): if `M^\bullet` is bounded above, then the cohomology modules of
`η_f M^\bullet ⊗_A C`, where `C = (A / fA) / J(M^\bullet, f)`, are finite locally free
`C`-modules. -/
theorem etaFComplexOverDecompositionQuotient_homology_finiteLocallyFree
    (hbounded : M.IsBoundedAbove)
    (i : ℕ) :
    let C := etaReductionDecompositionQuotient f M hf hI
    letI : CommRing C := inferInstance
    letI : Algebra A C := inferInstance
    let baseChangeC : NatModuleCochainComplex A ⥤ NatModuleCochainComplex C := baseChange
    Module.FiniteLocallyFree C ((baseChangeC.obj (η[f] M)).homology i) :=
  sorry

end

end
