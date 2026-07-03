import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_99_1 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for 15.99.1:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasFiniteInjectiveDimension`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, and the Chapter 15 owners
    `K.IsPerfect`, `K.IsPseudoCoherent`, and `HasFiniteInjectiveDimension M`;
  `bridge/view`: the bounded-below branch hypothesis `∃ n : ℤ, L.IsGE n`, which expresses the
    source condition without forcing a global `D⁺(R)` owner on the perfect branch.
- primitive vs. derived:
  the primitive input is the comparison owner `H`, the object `L : D(R)`, and the branch-level
  hypotheses on `K`, `L`, and `M`; a bounded-below owner object `L : D⁺(R)` is derived data, so
  it should not be built into the theorem header when only one disjunct needs it.
-/

-- Proof sketch: choose the bounded-above finite-projective representative of `K` supplied either
-- by perfectness or by pseudo-coherence, and compute the comparison on cochain complexes as in
-- Lemma `15.72.6`. In the perfect case the boundedness of the representative makes the degreewise
-- tensor-Hom comparison a finite direct-sum argument; in the pseudo-coherent case, combine the
-- bounded-above representative of `K` with a bounded-below representative of `L` and a bounded
-- injective representative of `M` coming from finite injective dimension to get the same finiteness
-- on the relevant total-complex degrees.
/-- Lemma 15.99.1: for the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)`, the morphism is an isomorphism whenever either `K`
is perfect, or `K` is pseudo-coherent, `L` is bounded below, and `M` has finite injective
dimension. -/
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
    (H : RHomPkg)
    (K L M : DMod)
    (hcases : K.IsPerfect ∨
      K.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ HasFiniteInjectiveDimension M) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := sorry

end

end CategoryTheory

/-! ### Lemma_15_99_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom

/- Domain-style sampling for 15.99.2:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`,
  propagated along truncation triangles;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `CategoryTheory.derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension`,
  `CategoryTheory.HasFiniteTorDimension`,
  `DerivedCategory.TStructure.t.truncLE`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`, now reduced through the owner-level criterion of Lemma `15.99.1`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, the source-facing notation
    `RHom[H](L, M)`, and the Chapter 15 owners `HasFiniteInjectiveDimension`,
    `HasFiniteTorDimension`, and `X.IsPseudoCoherent`;
  `bridge/view`: the lower truncations `τ_{\le n} K` used to reduce to Lemma `15.99.1`.
- primitive vs. derived:
  the primitive inputs are the owner `H`, the finite-injective-dimension hypotheses on `L` and
  `M`, the finite-tor-dimension hypothesis on `RHom[H](L, M)`, and the pseudo-coherence of the
  lower truncations of `K`; the bounded-below hypothesis needed to invoke Lemma `15.99.1` is
  derived locally from the injective-amplitude witness inside `hL`, so there is no need for an
  additional public bridge declaration here.
-/

/-- Lemma 15.99.2: the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)` is an isomorphism when `L` and `M` have finite
injective dimension, `R\mathrm{Hom}_R(L, M)` has finite tor dimension, and every lower truncation
`τ_{\le n} K` is pseudo-coherent. -/
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_finiteInjectiveDimension_of_finiteTorDimension_of_truncLE_isPseudoCoherent
    (H : RHomPkg)
    (K L M : DMod)
    (hL : HasFiniteInjectiveDimension L)
    (hM : HasFiniteInjectiveDimension M)
    (hLM : HasFiniteTorDimension (RHom[H](L, M)))
    (hτK : ∀ n : ℤ, ((t.truncLE n).obj K).IsPseudoCoherent) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  have hLge : ∃ n : ℤ, L.IsGE n := by
    sorry
  sorry

end

end CategoryTheory

/-! ### Lemma_15_99_3 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for 15.99.3:
- primary domain: the derived tensor/internal-Hom comparison from Lemma `15.74.5` and its
  isomorphism criteria;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_left_comparison`,
  `CategoryTheory.derivedTensorProduct`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.HasTorAmplitudeGE`;
- best owner abstraction:
  `source-facing`: the tor-amplitude/perfection hypotheses of Lemma `15.99.3`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the upstream
    comparison map, and the chapter tor-amplitude owner `HasTorAmplitudeGE`;
  `bridge/view`: none beyond reuse of the comparison owner from `Lemma_15_74_5`;
- primitive data vs. derived API: the primitive non-perfect branch is the direct conjunction of
  pseudo-coherence of `M`, lower boundedness of `L`, and lower tor-amplitude of `K` for a chosen
  bound `a`; the two perfect branches are separate companion uses of the same upstream comparison
  owner, so the tor-amplitude index should stay local to the third branch rather than burdening
  the whole theorem header.
-/

-- Proof sketch: in the first two cases, reduce by triangulated-generation and direct-sum
-- preservation to the generator `R[n]`, where the comparison is tautological. In the third case,
-- choose a bounded-above finite-free representative of `M`, a bounded-below representative of
-- `L`, and a K-flat representative of `K` with the stated lower tor-amplitude bound, then identify
-- both sides with the two termwise equal total complexes from the textbook proof.
/-- Lemma 15.99.3, perfect source case: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` from Lemma `15.74.5` is an isomorphism when the
source object `M` of the internal Hom is perfect. -/
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_source_isPerfect
    (H : RHomPkg)
    (K L M : DMod)
    (hM : M.IsPerfect) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := sorry

/-- Lemma 15.99.3, perfect tensor-factor case: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` is an isomorphism when the tensor factor `K` is
perfect. -/
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_tensor_isPerfect
    (H : RHomPkg)
    (K L M : DMod)
    (hK : K.IsPerfect) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := sorry

/-- Lemma 15.99.3, tor-amplitude branch: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` is an isomorphism when `M` is pseudo-coherent,
`L` lies in `D^+(R)`, and `K` has tor-amplitude in `[a, ∞]`. -/
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
    (H : RHomPkg)
    (K L M : DMod) (a : ℤ)
    (hM : M.IsPseudoCoherent)
    (hL : ∃ n : ℤ, L.IsGE n)
    (hK : HasTorAmplitudeGE K a) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := sorry

/-- Lemma 15.99.3: the canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to
R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)` from Lemma `15.74.5` is an isomorphism whenever
either `M` is perfect, or `K` is perfect, or for some integer `a`, `M` is pseudo-coherent, `L`
lies in `D^+(R)`, and `K` has tor-amplitude in `[a, ∞]`. -/
theorem derivedInternalHomTensorLeftComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_torAmplitudeGE
    (H : RHomPkg)
    (K L M : DMod)
    (hcases : M.IsPerfect ∨ K.IsPerfect ∨
      ∃ a : ℤ, M.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ HasTorAmplitudeGE K a) :
    IsIso (derivedInternalHom_tensor_left_comparison H K L M) := sorry

end

end CategoryTheory

/-! ### Lemma_15_99_4 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "ProjMinus" => CochainComplex.ProjectiveMinus (ModuleCat R)

open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom

/- Domain-style sampling for Lemma 15.99.4:
- primary domain: the canonical Hom complex of cochain complexes of `R`-modules and its comparison
  with the chosen derived internal Hom on `D(R)`, for bounded-above termwise-projective source
  complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.HomComplex`,
  `module_complex_internal_hom`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `DerivedCategory.IsPerfect`,
  the source-facing notation `RHom[H](K, L)`;
- best owner abstraction:
  `source-facing`: the K-flatness upgrade for `⟪P, K⟫` when `P : ProjectiveMinus` represents a
  perfect object and `K` is K-flat;
  `core/canonical`: the chapter owner `module_complex_internal_hom` from `Lemma_15_72_1` together
  with the source-side owner `CochainComplex.ProjectiveMinus` from Chapter 13 and the chosen
  monoidal-closed owner `H : MonoidalClosed DMod`;
  `bridge/view`: the resulting isomorphism
  `DerivedCategory.Q.obj ⟪P, K⟫ ≅ RHom[H](Q.obj P, Q.obj K)` for `P : ProjectiveMinus`;
- primitive data vs. derived API: the primitive source-side data here are exactly the owner datum
  `P : ProjectiveMinus`. Perfectness is derived additional structure used only for the K-flatness
  upgrade, not for the representation theorem itself. The Hom complex is already primitive
  upstream, so the local degreewise/differential reconstruction was duplicate derived API and
  should be deleted.
-/

-- Proof sketch: bounded-above termwise-projective complexes are K-projective, so the canonical
-- Hom complex already computes `RHom(P^•, K^•)` in the derived category without any perfectness
-- or K-flatness hypothesis on the target complex.
/-- The canonical comparison between the Hom complex `\mathrm{Hom}^\bullet(P^•, K^•)` and the
chosen derived internal Hom `R\mathrm{Hom}_R(P^•, K^•)` when `P^•` is bounded above and
termwise projective. This is the direct theorem-level representation layer; the perfectness
hypothesis is only needed later for the K-flatness upgrade. -/
theorem module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx) :
    IsIsomorphic
      (DerivedCategory.Q.obj ⟪P, K⟫)
      (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := sorry

-- Proof sketch: use the direct representation theorem above for the derived-Hom clause. For the
-- K-flatness clause, replace `P^•` in the derived category by a bounded finite-projective complex
-- using perfectness, compare the two Hom complexes via the bounded-above projective invariance,
-- and then apply the K-flatness results from Section `15.59`.
/-- Lemma 15.99.4: if `P^•` is a bounded-above cochain complex of projective `R`-modules, `K^•`
is K-flat, and `P^•` represents a perfect object of `D(R)`, then the module-valued internal-Hom
complex `\mathrm{Hom}^\bullet(P^•, K^•)` is K-flat, and the canonical comparison with
`R\mathrm{Hom}_R(P^•, K^•)` is an isomorphism in the derived category. -/
theorem module_complex_internal_hom_isKFlat_and_represents_derivedInternalHom_of_isPerfect
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat ∧
      IsIsomorphic
        (DerivedCategory.Q.obj ⟪P, K⟫)
        (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := sorry

-- Proof sketch: apply the main theorem and project to its first conjunct.
/-- The Hom complex against a K-flat complex is K-flat when the source complex is bounded above,
termwise projective, and perfect in the derived category. -/
theorem module_complex_internal_hom_isKFlat_of_isPerfect
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat := sorry

end

end CategoryTheory
