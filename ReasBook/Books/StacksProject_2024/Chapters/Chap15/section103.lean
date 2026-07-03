import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_103_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)

/- Domain-style sampling for Lemma 15.103.1:
- primary domain: derived `Ext` towers over ideal-power quotient inverse systems of finite
  modules;
- sampled owner declarations:
  `derivedExtModuleFunctor`,
  `idealPowerModuleQuotient`,
  `Functor.ofOpSequence`,
  `IsEssentiallyConstantCofilteredCone`;
- best owner abstraction in the present import closure: the source-facing tower is a sequential
  inverse system in `ModuleCat A` obtained by postcomposing the quotient transitions
  `M / I^(n + 2) M ⟶ M / I^(n + 1) M` with the fixed-degree Ext functor
  `derivedExtModuleFunctor K i`;
- primitive vs. derived:
  primitive data are the ideal `I`, the pseudo-coherent complex `K`, the finite module `M`, the
  fixed degree `i`, and the torsion hypothesis on higher Ext modules;
  derived API is the essentially constant cone and the resulting limit cone on that tower;
- source/core/bridge triage:
  `source-facing`: the two existence theorems below;
  `core/canonical`: `derivedExtModuleFunctor`, `idealPowerModuleQuotient`,
    `AdicCompletion.transitionMap`, `Functor.ofOpSequence`, and the Chapter 4 essentially
    constant-cone owner;
  `bridge/view`: the tower abbreviation `derivedExtIdealPowerQuotientTower`. -/

/-- The `n`th term `Ext^i_A(K, M / I^(n+1)M)` in the ideal-power quotient Ext tower. -/
abbrev derivedExtIdealPowerQuotientStage
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) (n : ℕ) : ModuleCat A :=
  (derivedExtModuleFunctor K i).obj (ModuleCat.of A (idealPowerModuleQuotient I M n))

/-- The transition morphism
`Ext^i_A(K, M / I^(n+2)M) ⟶ Ext^i_A(K, M / I^(n+1)M)`
in the ideal-power quotient Ext tower. -/
abbrev derivedExtIdealPowerQuotientStep
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) (n : ℕ) :
    derivedExtIdealPowerQuotientStage I K M i (n + 1) ⟶
      derivedExtIdealPowerQuotientStage I K M i n :=
  (derivedExtModuleFunctor K i).map
    (ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))))
/-- The sequential inverse system `(Ext^i_A(K, M / I^(n+1)M))_n` attached to `K`, `M`, and `I`.
The Lean indexing starts at `n = 0`, corresponding to the textbook quotient `M / IM`. -/
abbrev derivedExtIdealPowerQuotientTower
    (I : Ideal A) (K : DMod) (M : ModuleCat A) (i : ℤ) : SeqMod :=
  Functor.ofOpSequence (derivedExtIdealPowerQuotientStep I K M i)

/-- The hypothesis that all higher Ext modules `Ext^j_A(K, N)` with `j ≥ a` are `I`-power
torsion for finite `A`-modules `N`. -/
def DerivedExtIsIdealPowerTorsionAbove (I : Ideal A) (K : DMod) (a : ℤ) : Prop :=
  ∀ (N : ModuleCat.{u} A), Module.Finite A N → ∀ ⦃j : ℤ⦄, a ≤ j →
    Module.IsIdealPowerTorsion I ((derivedExtModuleFunctor K j).obj N)

-- Proof sketch: for `Ext^i_A(K, M)`, pseudo-coherence makes the group finite, so the torsion
-- hypothesis gives a power of `I` killing it. Apply Lemma `15.102.4` to the finite modules
-- `I^m M` to see that the images of `Ext^i_A(K, I^nM)` and `Ext^(i+1)_A(K, I^nM)` in the long
-- exact sequence of `0 → I^nM → M → M / I^nM → 0` vanish for large `n`. The resulting diagram
-- chase produces an essentially constant cone with vertex `Ext^i_A(K, M)`.
/-- Lemma 15.103.1: let `A` be a Noetherian ring, `I ⊆ A` an ideal, `K ∈ D(A)` a
pseudo-coherent complex, and `a ∈ ℤ`. Assume that for every finite `A`-module `N`, the modules
`Ext^j_A(K, N)` are `I`-power torsion for all `j ≥ a`. Then for every `i ≥ a` and every finite
`A`-module `M`, the inverse system `(Ext^i_A(K, M / I^(n+1)M))_n` is essentially constant with
value `Ext^i_A(K, M)`. The Lean indexing starts at `n = 0`, corresponding to the textbook
quotient `M / IM`. -/
theorem derivedExt_idealPowerQuotientTower_exists_essentiallyConstantCone
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : DerivedExtIsIdealPowerTorsionAbove I K a)
    (i : ℤ) (hi : a ≤ i) (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : Cone (derivedExtIdealPowerQuotientTower I K M i),
      c.pt = (derivedExtModuleFunctor K i).obj M ∧
        IsEssentiallyConstantCofilteredCone c := sorry

-- Proof sketch: use the essentially constant cone from
-- `derivedExt_idealPowerQuotientTower_exists_essentiallyConstantCone`; Chapter 4 upgrades an
-- essentially constant cofiltered cone to a genuine `LimitCone`, so the tower admits a limit cone
-- whose vertex is `Ext^i_A(K, M)`.
/-- The ideal-power quotient Ext tower admits a limit cone whose vertex is `Ext^i_A(K, M)` under
the hypotheses of Lemma `15.103.1`. -/
theorem exists_limitCone_derivedExt_idealPowerQuotientTower
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (a : ℤ)
    (hExt : DerivedExtIsIdealPowerTorsionAbove I K a)
    (i : ℤ) (hi : a ≤ i) (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : LimitCone (derivedExtIdealPowerQuotientTower I K M i),
      c.cone.pt = (derivedExtModuleFunctor K i).obj M ∧
        IsEssentiallyConstantCofilteredCone c.cone := sorry

end

end CategoryTheory

/-! ### Lemma_15_103_2 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling for Lemma 15.103.2:
- primary domain: Tor functoriality for the inclusion `I^[n] M ↪ M` of ideal-power submodules of a
  finite module over a Noetherian ring;
- sampled owner declarations:
  `Tor[A, p](X, Y)`,
  `idealPowerSubtype`,
  `idealPowerSubtypeTorMap`,
  `exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `idealPowerSubtypeTorMap` for the induced map
  `Tor_p^A(I^[n] M, N) → Tor_p^A(M, N)`, while the factorization through the derived tensor map
  from Lemma `15.102.7` remains proof-level bridge data;
- primitive data: the ideal `I`, the finite module `M`, the target module `N`, and the
  annihilator containment `I ≤ Module.annihilator A N`;
- derived API: the existential vanishing statement below for the canonical Tor map
  `idealPowerSubtypeTorMap`.

Source/core/bridge triage:
- `source-facing`: existence of an ideal-power stage where the canonical map on all Tor groups
  vanishes;
- `core/canonical`: `Tor[A, p](X, Y)` and `idealPowerSubtypeTorMap`;
- `bridge/view`: the derived-tensor factorization from Lemma `15.102.7`. -/

-- Proof sketch: apply Lemma `15.102.7` to factor the inclusion `I^[n] M → M` through the derived
-- tensor map induced by `I → A`, then tensor with `N`. Since `I ≤ Module.annihilator A N`, the
-- map `I ⊗_A^{\mathbf L} N → N` is zero, so the induced maps on all Tor groups vanish.
/-- Lemma 15.103.2: if `A` is Noetherian, `I ⊆ A` is an ideal, `M` is a finite `A`-module, and
`N` is annihilated by `I`, then some positive power `I^n M` maps trivially to `M` on every
`Tor_p^A(-, N)`. -/
theorem exists_idealPower_tor_map_eq_zero_of_annihilator_le
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ,
      idealPowerSubtypeTorMap I n M N p = 0 := sorry

end

end CategoryTheory

/-! ### Lemma_15_103_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

private abbrev stageSingle : ModuleCat A ⥤ DMod :=
  ModuleCat.single0Functor

private abbrev systemSingle : SeqMod ⥤ DSeq :=
  show SeqMod ⥤ DSeq from
    DerivedCategory.singleFunctor SeqMod 0

/- Domain-style sampling for Lemma 15.103.3:
- primary domain: sequential derived inverse limits in `D(A)` and their compatibility with the
  exact tensor functor `- ⊗[A]^L K`;
- sampled owner declarations:
  * `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`
  * the fixed-base bridge owner notation `R lim(_)` from `Lemma_15_88_1_FixedBase`
  * `CategoryTheory.IsDerivedLimit`
  * `ModuleCat.single0Functor`
  * `DerivedCategory.singleFunctor`
  * `CategoryTheory.derivedTensorProduct`
- best owner abstraction: the source-facing statement remains an `IsDerivedLimit` claim for the
  tensor tower, while the chosen derived-limit object is the canonical fixed-base Chapter 15 owner
  `R lim(systemSingle.obj M)` from `Lemma_15_88_1_FixedBase`; the bridge data are the stagewise
  degree-zero embedding `stageSingle` and the system-level degree-zero embedding `systemSingle`;
- primitive vs. derived:
  primitive data are only the pseudo-coherent object `K : D(A)` and the sequential inverse system
  `M : ℕᵒᵖ ⥤ Mod_A`;
  derived API is the tower `M ⋙ stageSingle ⋙ derivedTensorProduct K` and the tensorized chosen
  derived inverse limit `(R lim(systemSingle.obj M)) ⊗[A]^L K`.

Source/core/bridge triage:
- `source-facing`: the tensor compatibility statement that
  `(R lim(systemSingle.obj M)) ⊗[A]^L K` is a derived limit of the tensor tower;
- `core/canonical`: `R lim(_)`, `IsDerivedLimit`, and `derivedTensorProduct`;
- `bridge/view`: the degree-zero embeddings `stageSingle` and `systemSingle`, and the tower
  `M ⋙ stageSingle`.
-/

-- Proof sketch: apply the Milnor distinguished triangle defining the chosen derived inverse limit
-- of `M`, then apply the exact functor `derivedTensorProduct K`. Lemma `15.66.5` identifies the
-- images of the two product terms with the corresponding products of the stagewise derived tensor
-- products because `K` is pseudo-coherent, so the resulting triangle is exactly the Milnor
-- triangle for the tensor tower.
/-- Lemma 15.103.3: if `K ∈ D(A)` is pseudo-coherent and `(M_n)` is a sequential inverse system
of `A`-modules, then tensoring the chosen derived inverse limit of `(M_n[0])` with `K` gives a
derived limit of the stagewise tensor tower `((M_n[0]) \otimes_A^{\mathbf L} K)_n`. By symmetry
of the derived tensor product, this is the statement form of the textbook identity
`R\!\varprojlim_n (K \otimes_A^{\mathbf L} M_n) = K \otimes_A^{\mathbf L} R\!\varprojlim_n M_n`.
-/
lemma moduleDerivedInverseLimit_tensor_isDerivedLimit_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (M : SeqMod) :
    IsDerivedLimit
      ((M ⋙ stageSingle) ⋙ derivedTensorProduct K)
      ((R lim(systemSingle.obj M)) ⊗[A]^L K) := sorry

end

end CategoryTheory

/-! ### Lemma_15_103_4 (from Chap15) -/
open CategoryTheory
open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E] [Module.Finite (R ⧸ I) E]

/-
Domain-style sampling:
* primary domain: projective dimension and the Auslander--Buchsbaum formula for finite modules over
  Noetherian local rings, together with restriction of scalars along a quotient map;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `projectiveDimension_le_iff`,
  `projectiveDimension_eq_bot_iff`,
  `ringDepth_eq_projectiveDimension_add_moduleDepth`,
  `ModuleCat.restrictScalars`,
  `ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms`;
* source/core/bridge triage:
  `source-facing`: the additive change-of-rings formula for a finite `(R ⧸ I)`-module;
  `core/canonical`: `projectiveDimension` on `ModuleCat` objects and `moduleDepth`;
  `bridge/view`: the categorical restriction functor `ModuleCat.restrictScalars
    (Ideal.Quotient.mk I)`, used directly through the canonical object
    `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* primitive data: the canonical module-category objects `ModuleCat.of R (R ⧸ I)`,
  `ModuleCat.of (R ⧸ I) E`, and the restricted object
  `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* derived API: the hypotheses `projectiveDimension _ ≠ ⊤`, the zero-module fallback via
  `projectiveDimension_eq_bot_iff`, and the resulting additive equality.
-/

-- Proof sketch: reinterpret finite projective dimension as perfectness for finite modules, use the
-- finiteness of `R ⧸ I` over `R` together with the perfectness of `E` over `R ⧸ I`, and then apply
-- the change-of-rings result from the perfect derived category to conclude that `E` is perfect,
-- hence has finite projective dimension over `R` after viewing `E` as an `R`-module by
-- restriction of scalars along `Ideal.Quotient.mk I`.
/- Internal finiteness step used in the additive formula below. -/
theorem projectiveDimension_ne_top_of_idealQuotient_module
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) ≠
      ⊤ := sorry

-- Proof sketch: first use the companion theorem to know that `E` has finite projective dimension
-- over `R`. Then apply Auslander--Buchsbaum to `E` over `R`, to `E` over `R ⧸ I`, and to the
-- quotient ring `R ⧸ I` over `R`; finally use that the depth of `E` computed over `R` agrees with
-- the depth computed over `R ⧸ I` to eliminate the depth terms and obtain the stated sum formula;
-- when `E = 0`, both projective dimensions of `E` are `⊥`, so the identity reduces to the
-- canonical `WithBot` arithmetic.
/-- Lemma 15.103.4: for a finite `(R ⧸ I)`-module `E` over a Noetherian local ring `R`, if `R ⧸ I`
has finite projective dimension as an `R`-module and `E` has finite projective dimension as an
`(R ⧸ I)`-module, then the projective dimension of the restricted `R`-module
`RestrictScalars R (R ⧸ I) E` is the sum of the projective dimension of `R ⧸ I` over `R` and the
projective dimension of `E` over `R ⧸ I`. -/
theorem projectiveDimension_idealQuotient_module_eq_add
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) =
      projectiveDimension (ModuleCat.of R (R ⧸ I)) +
        projectiveDimension (ModuleCat.of (R ⧸ I) E) := sorry

end

/-! ### Lemma_15_103_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "QA" => (DerivedCategory.Q : CpxA ⥤ DModA)
local notation "QB" => (DerivedCategory.Q : CpxB ⥤ DModB)
local notation "Res" =>
  (Functor.mapHomologicalComplex (ModuleCat.restrictScalars (algebraMap A B)) (up ℤ) :
    CpxB ⥤ CpxA)

/- Domain-style sampling for Lemma 15.103.5:
- primary domain: derived base change along `A → B` for cochain complexes of modules, together
  with compatible subcomplex inclusions and the induced maps on cohomology;
- sampled owner declarations:
  `CochainComplex`,
  `derivedTensorWithAlgebraAdjunction`,
  `DerivedCategory.Q`,
  `Functor.mapDerivedCategoryFactors`,
  `Subobject.factorThru`;
- best owner abstraction: the canonical owner of the comparison
  `M^• ⊗_A^{\mathbf L} B ⟶ N^•` attached to a complex map
  `a : M ⟶ ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj N`
  is the adjunction
  `derivedTensorWithAlgebraAdjunction`, together with the standard `Q`/restriction comparison
  isomorphism `Functor.mapDerivedCategoryFactors`, here specialized to the restriction functor
  on cochain complexes;
- primitive vs. derived:
  primitive data are the complex map `a`, the subobjects `M'`, `N'`, and the factorization witness
  expressing that `a` carries `M'` into `N'` after restricting scalars;
  the induced maps on derived base change and on cohomology are derived API and should not be
  stored as primitive wrapper fields;
- source/core/bridge triage:
  `source-facing`: the enlargement theorem for actual subcomplexes `M₁ ⊆ M₂ ⊆ M` and
    `N₁ ⊆ N₂ ⊆ N`;
  `core/canonical`: `derivedTensorWithAlgebraAdjunction`, `DerivedCategory.Q`,
  `Functor.mapDerivedCategoryFactors`, and `Subobject.factorThru`;
  `bridge/view`: the canonical comparison maps below, obtained by transposing the corresponding
    complex maps under the derived extension/restriction adjunction, together with the standard
    cardinality owner `CochainComplex.termCardinal` for the size bounds in the source statement.
-/

namespace CochainComplex

/-- The total cardinality of the terms of a cochain complex of modules. -/
def termCardinal {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℤ) : Cardinal :=
  Cardinal.mk (Σ i : ℤ, (K.X i : Type _))

end CochainComplex

/-- The canonical derived base-change morphism attached to a complex map
`f : M ⟶ Res.obj N`. -/
noncomputable def derivedTensorWithAlgebraComparison {M : CpxA} {N : CpxB}
    (f : M ⟶ (Res).obj N) :
    (((QA).obj M) ⊗[A]^L[B]) ⟶ (QB).obj N :=
  (derivedTensorWithAlgebraAdjunction.homEquiv _ _).symm
    ((QA).map f ≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.inv.app N)

/-- Given compatible subcomplexes `M' ⊆ M` and `N' ⊆ N`, the map `a : M ⟶ Res N` restricts to a
map `M' ⟶ Res N'`. -/
private def restrictToSubcomplexes {M : CpxA} {N : CpxB}
    (M' : Subobject M) (N' : Subobject N)
    (a : M ⟶ (Res).obj N)
    (h : (Subobject.mk ((Res).map N'.arrow)).Factors (M'.arrow ≫ a)) :
    (M' : CpxA) ⟶ (Res).obj (N' : CpxB) :=
  (Subobject.mk ((Res).map N'.arrow)).factorThru (M'.arrow ≫ a) h ≫
    (Subobject.underlyingIso ((Res).map N'.arrow)).hom

/-- The induced homology map on the derived base-change comparison for compatible subcomplexes. -/
noncomputable def derivedTensorWithAlgebraSubcomplexHomologyMap {M : CpxA} {N : CpxB}
    (M' : Subobject M) (N' : Subobject N)
    (a : M ⟶ (Res).obj N)
    (h : (Subobject.mk ((Res).map N'.arrow)).Factors (M'.arrow ≫ a))
    (i : ℤ) :
    (H i).obj (((QA).obj (M' : CpxA)) ⊗[A]^L[B]) ⟶ (H i).obj ((QB).obj (N' : CpxB)) :=
  (H i).map (derivedTensorWithAlgebraComparison (restrictToSubcomplexes M' N' a h))

-- Proof sketch: choose a cardinal bounding the sizes of `A`, `B`, and a free `A`-resolution of
-- `B`; then enlarge the initial subcomplexes by adjoining small stable subcomplexes that kill the
-- relevant kernel classes and realize the relevant image classes after derived base change.
/-- Lemma 15.103.5: for a ring map `A → B`, there exists a cardinal `κ` such that whenever
`a : M^• ⟶ N^•` induces an isomorphism
`M^• \otimes_A^{\mathbf L} B \to N^•` in `D(B)`, every compatible pair of subcomplexes
`M₁^• ⊆ M^•` and `N₁^• ⊆ N^•` admits enlargements `M₂^•` and `N₂^•` through which the kernel and
image conditions on cohomology hold in every degree, with total cardinality bounded by
`max(κ, |M₁^•|, |N₁^•|)`. -/
theorem exists_cardinal_for_derivedTensor_subcomplex_approximation :
    ∃ κ : Cardinal,
        ∀ ⦃M : CpxA⦄ ⦃N : CpxB⦄
        (a : M ⟶ (Res).obj N)
        (haIso : IsIso (derivedTensorWithAlgebraComparison a))
        (M₁ : Subobject M) (N₁ : Subobject N)
        (h₁ : (Subobject.mk ((Res).map N₁.arrow)).Factors (M₁.arrow ≫ a)),
        ∃ (M₂ : Subobject M) (N₂ : Subobject N)
          (hM : M₁ ≤ M₂) (hN : N₁ ≤ N₂)
          (h₂ : (Subobject.mk ((Res).map N₂.arrow)).Factors (M₂.arrow ≫ a)),
          (∀ i : ℤ,
              (kernelSubobject (derivedTensorWithAlgebraSubcomplexHomologyMap M₁ N₁ a h₁ i)).arrow ≫
                (H i).map
                    ((derivedTensorWithAlgebra (algebraMap A B)).map
                      ((QA).map (Subobject.ofLE M₁ M₂ hM))) = 0) ∧
          (∀ i : ℤ,
              imageSubobject ((H i).map ((QB).map (Subobject.ofLE N₁ N₂ hN))) ≤
                imageSubobject (derivedTensorWithAlgebraSubcomplexHomologyMap M₂ N₂ a h₂ i)) ∧
          max ((M₂ : CpxA).termCardinal)
              ((N₂ : CpxB).termCardinal) ≤
            max κ
              (max ((M₁ : CpxA).termCardinal)
                ((N₁ : CpxB).termCardinal)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_103_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Pretriangulated
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: distinguished triangles in `D(R)`, their homology long exact sequences, and
  localization of homology modules away from a single element;
- sampled owner declarations:
  `Triangle.mk`,
  `distTriang`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`,
  `LocalizedModule.Away`,
  `Localization.Away`;
- best owner abstraction: the cone bound and conclusion should use the canonical t-structure owner
  `IsGE`, while the distinguished-triangle relation remains
  `Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod`; homology and localization use the canonical
  owners `H` and `LocalizedModule.Away`;
- primitive data: the comparison maps `g : M ⟶ C` and `δ : C ⟶ M⟦1⟧` together with the
  distinguished-triangle proof for `Triangle.mk (f • 𝟙 M) g δ`, the localized negative homology
  vanishing of `M`, and the lower bound `C.IsGE (-1)`;
- derived API: the canonical conclusion `M.IsGE 0`, with the textbook negative-homology
  vanishing statement retained only as a thin bridge via `DerivedCategory.isGE_iff`.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion for the cone of multiplication by `f`;
- `core/canonical`: `Triangle`, `distTriang`, `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`, `DerivedCategory.homologyFunctor`, and `LocalizedModule.Away`;
- `bridge/view`: the explicit cohomology-vanishing formulation from `DerivedCategory.isGE_iff`,
  together with the direct categorical packaging
  `ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))` of localized
  homology modules used here and in the immediate downstream local criterion
  `Lemma_15_127_4`. -/

section

variable {M C : DerivedCategory (ModuleCat R)} {f : R} {g : M ⟶ C} {δ : C ⟶ M⟦(1 : ℤ)⟧}

-- Proof sketch: use the long exact homology sequence of the distinguished triangle
-- `M --f·id--> M --> C --> M[1]`. If some negative homology of `M` were nonzero, its localization
-- would vanish by hypothesis, so it would contain nonzero `f`-power torsion; the kernel of
-- multiplication by `f` would then contribute nontrivially to the previous homology of the cone,
-- contradicting the vanishing of `H^i(C)` for `i < -1`.
/-- Canonical `t`-structure form of Lemma 15.103.6: let `C` be the cone of multiplication by
`f : R` on `M` in `D(R)`, written as a
distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`M` lies in degrees `≥ 0`. -/
theorem isGE_zero_of_localized_isZero_and_cone_isGE_neg_one
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC : C.IsGE (-1)) :
    M.IsGE 0 := by
  sorry

/-- Lemma 15.103.6: let `C` be the cone of multiplication by `f : R` on `M` in `D(R)`, written as
the distinguished triangle `M \xrightarrow{f} M \to C \to M[1]`. If the localized homology
`H^i(M)_f` vanishes for all `i < 0` and the homology of `C` vanishes for all `i < -1`, then
`H^i(M)` vanishes for all `i < 0`. -/
theorem isZero_homology_of_neg_of_localized_isZero_and_cone_isZero
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang DMod)
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f ((H i).obj M))))
    (hC :
      ∀ i : ℤ, i < -1 →
        IsZero ((H i).obj C)) :
    ∀ i : ℤ, i < 0 →
      IsZero ((H i).obj M) := by
  simpa [DerivedCategory.isGE_iff] using
    isGE_zero_of_localized_isZero_and_cone_isGE_neg_one hT hMloc
      ((DerivedCategory.isGE_iff C (-1)).2 hC)

end

end

end CategoryTheory

/-! ### Lemma_15_103_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.103.7:
- primary domain: tor-amplitude in `D(R)` and its source-facing degree-zero flatness
  reformulation;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `DerivedCategory.IsLE`,
  `CategoryTheory.hasTorAmplitudeIn_iff_exists_flat_representative`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`;
- best owner abstraction: the chapter owner is `HasTorAmplitudeIn`, with the degree-zero flatness
  wording treated as a bridge/view used only to restore the textbook statement of Lemma 15.103.7;
- primitive vs. derived:
  primitive data are the derived object and its tor-amplitude predicate;
  derived API is the degree-zero bridge
  `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`, used to recover the textbook flat-module
  formulation from the owner predicate.

Source/core/bridge triage:
- `source-facing`: `isFlatModuleInDegreeZero_of_localizationAway_and_quotient`;
- `core/canonical`: `HasTorAmplitudeIn _ 0 0`;
- `bridge/view`: `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`. -/

-- Proof sketch: specialize `hasTorAmplitudeIn_iff_exists_flat_representative` to the interval
-- `[0, 0]`. The representative then has a single possibly nonzero term in degree `0`, and
-- `ModuleCat.hasTorDimensionLE_zero_iff_flat` identifies that term as flat.
/-- An object of `D(R)` has tor-amplitude in `[0, 0]` exactly when it is isomorphic to a flat
`R`-module placed in degree `0`. -/
theorem hasTorAmplitudeIn_zero_zero_iff_exists_flat_module (M : DMod) :
    HasTorAmplitudeIn M 0 0 ↔
      ∃ N : ModuleCat R, Module.Flat R N ∧ IsIsomorphic M ((single₀).obj N) := sorry

variable (f : R)

local notation "Rf" => Localization.Away f
local notation "Rbar" => R ⧸ Ideal.span (Set.singleton f)
local notation "single₀Rf" => DerivedCategory.singleFunctor (ModuleCat Rf) (0 : ℤ)
local notation "single₀Rbar" => DerivedCategory.singleFunctor (ModuleCat Rbar) (0 : ℤ)

-- Proof sketch: tensor `M` with an arbitrary `R`-module concentrated in degree `0`, use `hM`
-- to keep the tensor product in `D^{≤ 0}(R)`, then apply Lemma `15.103.6` to the multiplication
-- triangle by `f`. The localization and quotient hypotheses are fed in through the chapter owner
-- `HasTorAmplitudeIn _ 0 0`, which is the canonical degree-zero flatness condition.
/-- Canonical companion to Lemma 15.103.7: under the source hypotheses, `M` has tor-amplitude in
`[0, 0]`. -/
theorem hasTorAmplitudeIn_zero_zero_of_isLE_zero_of_localizationAway_and_quotient
    (M : DMod)
    (hM : M.IsLE 0)
    (hlocalization : HasTorAmplitudeIn (M ⊗[R]^L[Rf]) 0 0)
    (hquotient : HasTorAmplitudeIn (M ⊗[R]^L[Rbar]) 0 0) :
    HasTorAmplitudeIn M 0 0 := sorry

-- Proof sketch: translate the source-facing localization and quotient hypotheses to
-- `HasTorAmplitudeIn _ 0 0` via `hasTorAmplitudeIn_zero_zero_iff_exists_flat_module`, apply the
-- canonical tor-amplitude companion above, and then translate the conclusion back to the source
-- wording by the same bridge.
/-- Lemma 15.103.7: if `M` has no positive cohomology, the derived localization
`M \otimes_R^{\mathbf L} R_f` is isomorphic to a flat module placed in degree `0`, and the
derived reduction `M \otimes_R^{\mathbf L} R/fR` is isomorphic to a flat module placed in degree
`0`, then `M` itself is isomorphic in `D(R)` to a flat `R`-module placed in degree `0`. -/
theorem isFlatModuleInDegreeZero_of_localizationAway_and_quotient
    (M : DMod)
    (hM : M.IsLE 0)
    (hlocalization :
      ∃ N : ModuleCat Rf, Module.Flat Rf N ∧ IsIsomorphic (M ⊗[R]^L[Rf]) ((single₀Rf).obj N))
    (hquotient :
      ∃ N : ModuleCat Rbar, Module.Flat Rbar N ∧
        IsIsomorphic (M ⊗[R]^L[Rbar]) ((single₀Rbar).obj N)) :
    ∃ N : ModuleCat R, Module.Flat R N ∧ IsIsomorphic M ((single₀).obj N) := sorry

end

end CategoryTheory
