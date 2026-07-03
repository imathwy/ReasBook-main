import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_102_1 (from Chap15) -/
open CategoryTheory
open Limits
open Opposite
open SequentialProObjectMorphismRep
open scoped IdealPowerSubmodule

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A]

local notation "Mod" => ModuleCat A
local notation "SeqMod" => SequentialInverseSystem Mod

/- Domain-style sampling for `15.102.1`:
- primary domain: homology of short complexes of finite modules and the induced `I`-adic inverse
  systems;
- sampled core/canonical owners:
  `ShortComplex.leftHomology`,
  `ShortComplex.leftHomologyMap`,
  `ShortComplex.map`,
  `ShortComplex.mapNatTrans`,
  `Functor.ofOpSequence`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `Submodule.pow_smul_top_le`;
- best owner abstraction: the ambient short complex `S : ShortComplex (ModuleCat A)` should own
  the ideal-power stage complexes, the ambient homology `S.leftHomology`, and the induced towers;
  the ideal-power stage maps should be induced from the owner-level short-complex APIs
  `ShortComplex.map` and `ShortComplex.mapNatTrans`, the inverse systems should use the canonical
  owner `Functor.ofOpSequence`, and the resulting pro-comparison should live in
  `SequentialProObjectMorphismRep` with owner property `r.IsProIsomorphism`;
- primitive data: the short complex `S` together with the ideal-power submodules
  `I^n S.X₁`, `I^n S.X₂`, and `I^n S.X₃`;
- derived API: the stage homology objects, their transition maps, the map to the ambient
  homology, and the eventual comparison data;
-- source/core/bridge triage:
  `source-facing`: the eventual comparison between filtered homology and the `I`-adic filtration on
    ambient homology;
  `core/canonical`: `ShortComplex.leftHomology`, `ShortComplex.leftHomologyMap`,
    `ShortComplex.map`, `ShortComplex.mapNatTrans`, `Functor.ofOpSequence`,
    `idealPowerSubmodule`, and
    `SequentialProObjectMorphismRep.IsProIsomorphism`;
  `bridge/view`: the ideal-power stage complexes and the induced maps from those stages to `S`. -/

section Comparison

variable (S : ShortComplex Mod) (I : Ideal A)

/-- The `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleStageComplex
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : ShortComplex Mod :=
  S.map (idealPowerSubmoduleFunctor I n)

instance idealPowerSubmoduleStageComplex_hasLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I n).HasLeftHomology := by
  let T : ShortComplex Mod := S.idealPowerSubmoduleStageComplex I n
  let _ : HasKernel T.g := inferInstance
  let _ : HasCokernel (kernel.lift T.g T.f T.zero) := inferInstance
  exact HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel T)

/-- The homology object `H[n]` of the `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleHomologyStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  (S.idealPowerSubmoduleStageComplex I n).leftHomology

/-- The canonical map from the homology of the `n`th ideal-power subcomplex to the ambient left
homology of `S`, induced by the inclusion `I^[n] S ⟶ S`. -/
abbrev idealPowerSubmoduleHomologyToLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I n ⟶ S.leftHomology :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubtypeNatTrans I n)

/-- The transition map `(H[n+1]) ⟶ H[n]` on the homology tower of the ideal-power subcomplexes of
`S`. -/
abbrev idealPowerSubmoduleHomologyStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I (n + 1) ⟶
      S.idealPowerSubmoduleHomologyStage I n :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ n))

/-- The inverse system `(H[n])_n` obtained by taking left homology of the ideal-power
subcomplexes of `S`. -/
abbrev idealPowerSubmoduleHomologyTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.idealPowerSubmoduleHomologyStep I n)

/-- The `n`th ideal-power stage `I^[n] H` of the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  idealPowerStage I n S.leftHomology

/-- The transition map `I^[n+1] H ⟶ I^[n] H` on the ideal-power tower of the ambient left homology
`H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomologyIdealPowerStage I (n + 1) ⟶ S.leftHomologyIdealPowerStage I n :=
  ModuleCat.ofHom <|
    Submodule.inclusion
      (show I^[n + 1] S.leftHomology ≤ I^[n] S.leftHomology from
        idealPowerSubmodule_mono I (Nat.le_succ n))

/-- The inverse system `(I^[n] H)_n` on the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.leftHomologyIdealPowerStep I n)

variable [IsNoetherianRing A]
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

/-- Arithmetic helper for the shifted transition maps in Lemma 15.102.1. -/
theorem shiftComparison_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Lemma 15.102.1: for a complex `K ⟶ L ⟶ M` of finite `A`-modules over a Noetherian ring and an
ideal `I`, the filtered homology groups `H[n]` are eventually compared with the `I`-adic
filtration on `H = ker β / im α` by shifted natural transformations in both directions whose
stagewise composites are the canonical transition morphisms. -/
theorem exists_idealPowerSubmoduleHomologyComparison
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ toPower :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        ∃ fromPower :
          (S.leftHomologyIdealPowerTower I).shift c ⟶ S.idealPowerSubmoduleHomologyTower I,
          (∀ n : ℕ,
            toPower.app (Opposite.op n) ≫ ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
              S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)) ∧
            (∀ n : ℕ,
              ((fromPower.app (Opposite.op (c + n))) :
                  S.leftHomologyIdealPowerStage I (c + (c + n)) ⟶
                    S.idealPowerSubmoduleHomologyStage I (c + n)) ≫
                toPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
                  (shiftComparison_le n c)) ∧
            ∀ n : ℕ,
              ((toPower.app (Opposite.op (c + n))) :
                  S.idealPowerSubmoduleHomologyStage I (c + (c + n)) ⟶
                    S.leftHomologyIdealPowerStage I (c + n)) ≫
                fromPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
                  (shiftComparison_le n c) := sorry

/-- Companion to Lemma 15.102.1: the filtered homology tower `(H[n])_n` and the `I`-adic tower
`(H^[n])_n`, with `H^[n] = I^n H`, are pro-isomorphic via the explicit shift representative coming
from the forward comparison natural transformation. -/
theorem idealPowerSubmoduleHomologyTower_isProIsomorphic_to_leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        (ofShiftNatTrans c comparison).IsProIsomorphism := sorry

end Comparison

end CategoryTheory.ShortComplex

/-! ### Lemma_15_102_2 (from Chap15) -/
noncomputable section

attribute [local instance] CategoryTheory.HasExt.standard

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open scoped IdealPowerSubmodule

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]

local notation "Mod" => ModuleCat A

/- Domain-style sampling:
- primary domain: Ext-groups of finite modules over a Noetherian ring, with restriction maps
  induced by the inclusions `I^[n] M ↪ M` and `I^[n - c] N ↪ N`;
- sampled owner declarations:
  `idealPowerSubtype`,
  `idealPowerSubtypeExtPrecomp`,
  `idealPowerSubtypeExtPostcomp`;
- best owner abstraction: the chapter owner surface for these restriction maps is
  `idealPowerSubtypeExtPrecomp` in the source variable and `idealPowerSubtypeExtPostcomp` in the
  target variable, both derived canonically from `idealPowerSubtype`;
- primitive data: the ideal `I`, the finite source module `M`, the target module `N`, the degree
  `p`, and the ideal-power inclusions on `M` and `N`;
- derived API: the eventual factorization of the restriction map through
  `Ext^p_A(I^[n] M, I^[n - c] N)`.

Layer triage:
- `source-facing`: the eventual factorization statement from the Stacks lemma;
- `core/canonical`: `idealPowerSubtype`, `Ext.precompOfLinear`, and `Ext.postcompOfLinear`;
- `bridge/view`: the witness map `φ` giving the factorization through the ideal-power target. -/

-- Proof sketch: the source lemma is the positive-degree statement. In degree `0`, the
-- restriction map already factors with `c = 0` by viewing a morphism `M ⟶ N` as a morphism
-- `I^n M ⟶ I^n N`. For `p > 0`, apply Artin-Rees to a finite presentation of `M` to obtain a
-- uniform constant `c`; for each `n ≥ c`, the induced map on a free resolution of `I^n M` lands
-- in `I^(n - c) N`, which yields the required factorization on `Ext^p` by induction on `p`.
/-- Lemma 15.102.2: for every degree `p > 0`, the canonical `A`-linear restriction map
`Ext^p_A(M, N) → Ext^p_A(I^n M, N)` factors for large `n` through some `A`-linear map
`Ext^p_A(M, N) → Ext^p_A(I^n M, I^(n - c) N)`, whose postcomposition with the canonical map
`Ext^p_A(I^n M, I^(n - c) N) → Ext^p_A(I^n M, N)` induced by `I^(n - c) N ↪ N` recovers the
restriction map. -/
theorem exists_ext_factorization_through_ideal_power_target (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      let Mn := idealPowerStage I n M
      let Nn := idealPowerStage I (n - c) N
      ∃ φ :
        Ext M N p →ₗ[A] Ext Mn Nn p,
        ∀ x : Ext M N p,
          idealPowerSubtypeExtPostcomp I (n - c) Mn N p (φ x) =
            idealPowerSubtypeExtPrecomp I n M N p x :=
  sorry

end

/-! ### Lemma_15_102_3 (from Chap15) -/
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open scoped IdealPowerSubmodule

universe u

noncomputable section

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling:
- primary domain: Ext-groups of finite modules over a Noetherian ring, with the restriction map
  induced by the inclusion `I^n M ↪ M`;
- sampled owner declarations:
  `idealPowerSubtype`,
  `idealPowerSubtypeExtPrecomp`,
  `idealPowerSubtypeExtPostcomp`,
  `exists_ext_factorization_through_ideal_power_target`;
- best owner abstraction: the chapter owner `idealPowerSubtypeExtPrecomp` is the canonical
  restriction map on Ext for the ideal-power inclusion, and Lemma `15.102.2` already supplies the
  needed factorization through `Ext^p_A(I^n M, I^(n - c) N)`;
- primitive data: the ideal `I`, the finite source module `M`, the target module `N`, and an
  explicit exponent `m` with `I^[m] N = ⊥`; there is no upstream owner predicate in the chapter
  for this stronger uniform-annihilation hypothesis, so the file should keep it directly rather
  than weaken it to the owner `Module.IsIdealPowerTorsion`;
- derived API: the source-facing existential vanishing statement is the numbered item, while the
  stronger eventual-vanishing statement is a companion obtained from the same factorization proof.

Layer triage:
- `source-facing`: existence of one ideal-power stage where the restriction map
  `Ext^p_A(M, N) → Ext^p_A(I^n M, N)` vanishes when some power of `I` kills `N`;
- `core/canonical`: `idealPowerSubtypeExtPrecomp`;
- `bridge/view`: the factorization theorem
  `exists_ext_factorization_through_ideal_power_target`.
-/

-- Proof sketch: apply Lemma `15.102.2` in positive degree to obtain a constant `c` and a
-- factorization of the restriction map through `Ext^p_A(I^n M, I^(n - c) N)` for all `n ≥ c`.
-- For every `n ≥ c + m`, the target `I^(n - c) N` is zero because `I^[m] N = 0`, so the
-- factorization forces the restriction map to vanish.
/-- Companion to Lemma 15.102.3: if `I^[m]` annihilates `N`, then for every positive degree `p`
the restriction maps `Ext^p_A(M, N) → Ext^p_A(I^n M, N)` are zero for all sufficiently large
`n`. -/
theorem eventually_ext_restriction_zero_of_target_annihilated_by_ideal_power
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] (p : ℕ) (hp : 0 < p)
    (m : ℕ) (hm : I^[m] N = ⊥) :
    ∃ c : ℕ, ∀ n ≥ c,
      idealPowerSubtypeExtPrecomp I n M N p = 0 := by
  obtain ⟨c, hc⟩ := exists_ext_factorization_through_ideal_power_target I M N p hp
  refine ⟨c + m, ?_⟩
  intro n hn
  have hc' := hc n (le_trans (Nat.le_add_right c m) hn)
  dsimp only at hc'
  obtain ⟨φ, hφ⟩ := hc'
  have hmc : m ≤ n - c := by
    omega
  have hzeroSub : I^[n - c] N = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (Submodule.pow_smul_top_le I N hmc).trans (by simp [hm])
  have hmk₀ : mk₀ (ModuleCat.ofHom (idealPowerSubtype I (n - c) N)) = 0 := by
    rw [mk₀_eq_zero_iff]
    ext x
    simpa [hzeroSub] using x.2
  have hpost :
      idealPowerSubtypeExtPostcomp I (n - c) (idealPowerStage I n M) N p = 0 := by
    ext x
    rw [idealPowerSubtypeExtPostcomp, hmk₀]
    change x.comp 0 (add_zero p) = 0
    simp
  ext x
  rw [← hφ x, hpost]
  simp

/-- Lemma 15.102.3: if `A` is Noetherian, `M` is a finite `A`-module, and `I^[m]` annihilates
`N`, then for every degree `p > 0` there exists some `n` such that the restriction map
`Ext^p_A(M, N) → Ext^p_A(I^n M, N)` is zero. -/
theorem exists_ext_restriction_zero_of_target_annihilated_by_ideal_power
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] (p : ℕ) (hp : 0 < p)
    (m : ℕ) (hm : I^[m] N = ⊥) :
    ∃ n : ℕ, idealPowerSubtypeExtPrecomp I n M N p = 0 := by
  obtain ⟨c, hc⟩ :=
    eventually_ext_restriction_zero_of_target_annihilated_by_ideal_power I M N p hp m hm
  exact ⟨c, hc c le_rfl⟩

end

/-! ### Lemma_15_102_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

open scoped IdealPowerSubmodule

local notation "DMod" => DerivedCategory (ModuleCat A)
variable (K : DMod) (p : ℤ)
local notation "Extp" => derivedExtModuleFunctor K p

/- Domain-style sampling:
- primary domain: functorial derived `Ext` for a pseudo-coherent object against finite modules,
  with Artin-Rees control on the image of the restriction map `I^[n] M ↪ M`;
- sampled owner declarations:
  `derivedExtModuleFunctor`,
  `idealPowerSubmodule`,
  `idealPowerSubtypeNatTrans`;
- best owner abstraction: the canonical Ext module owner here is
  `(Extp).obj M`, and the source-facing map is the induced `A`-linear morphism
  `(Extp).map ((idealPowerSubtypeNatTrans I n).app M)` coming from the chapter owner
  `idealPowerSubtypeNatTrans`;
- primitive data: the ideal `I`, the pseudo-coherent complex `K`, the finite module `M`, the
  inclusion `I^[n] M ↪ M`, and the ambient Ext module `(Extp).obj M`;
- derived API: the range containment in the ideal-power submodule of `(Extp).obj M`.

Source/core/bridge triage:
- `source-facing`: the eventual Artin-Rees containment for the image of
  `Ext^p_A(K, I^[n] M) → Ext^p_A(K, M)`;
- `core/canonical`: `(Extp).obj M`;
- `bridge/view`: the induced `ModuleCat` morphism `(Extp).map ((idealPowerSubtypeNatTrans I n).app M)`.
-/

-- Proof sketch: represent the pseudo-coherent complex `K` by a bounded-above complex of finite
-- free `A`-modules. Then `Ext^p_A(K, M)` is computed by a finite three-term Hom complex, and the
-- restriction map from `I^[n] M` to `M` is induced by multiplying those finite modules by `I^n`.
-- Apply Lemma `15.102.1` to this finite complex to obtain a uniform Artin-Rees constant `c`
-- controlling the image in cohomology.
/-- Lemma 15.102.4: if `A` is Noetherian, `K ∈ D(A)` is pseudo-coherent, and `M` is a finite
`A`-module, then for every integer `p` there is a constant `c` such that for `n ≥ c` the image of
`Ext^p_A(K, I^[n] M) → Ext^p_A(K, M)` is contained in `I^[n - c] Ext^p_A(K, M)`. -/
theorem exists_derivedExt_image_le_idealPower_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (M : ModuleCat A) [Module.Finite A M]
    (p : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      LinearMap.range
          (((Extp).map ((idealPowerSubtypeNatTrans I n).app M)).hom) ≤
        I^[n - c] ((Extp).obj M) := sorry

end

end CategoryTheory

/-! ### Lemma_15_102_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open SequentialProObjectMorphismRep
open scoped IdealPowerSubmodule
universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.102.5:
- primary domain: sequential pro-object comparisons in `D(A)` between ideal-power towers and the
  derived powered-Koszul tower attached to a finite generating family;
- sampled owner declarations:
  `idealPowerStage`,
  `idealPowerSubmoduleInclusionNatTrans`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `Functor.ofOpSequence`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the ideal-power side should be built from the chapter owner
  `idealPowerStage I n (ModuleCat.of A A)` and its canonical inclusion maps, while the comparison
  itself should be expressed by a sequential representative together with the owner morphism
  `a.toProObjectHom`;
- primitive data: an ideal `I : Ideal A`, or concretely `Ideal.span (Set.range f)`, together with
  the canonical powered-Koszul tower from Situation `15.92.15`;
- derived API: the derived-category ideal-power tower and the induced isomorphism of the
  associated sequential pro-objects.

Source/core/bridge triage:
- `source-facing`: the pro-isomorphism from the ideal-power tower for `I = (f_1, …, f_r)` to the
  derived powered-Koszul tower;
- `core/canonical`: `idealPowerStage`, `idealPowerSubmoduleInclusionNatTrans`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the specialization `I = Ideal.span (Set.range f)`. -/

/-- The `n`th ideal-power stage `(I^[n+1] A)[0]` in `D(A)`, using the chapter owner
`idealPowerStage`. -/
abbrev idealPowerDerivedStage (I : Ideal A) (n : ℕ) : DMod :=
  (single0).obj (idealPowerStage I (n + 1) (ModuleCat.of A A))

/-- The transition morphism `(I^[n+2] A)[0] ⟶ (I^[n+1] A)[0]` in the ideal-power tower. -/
abbrev idealPowerDerivedStep (I : Ideal A) (n : ℕ) :
    idealPowerDerivedStage I (n + 1) ⟶ idealPowerDerivedStage I n :=
  (single0).map
    ((idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app (ModuleCat.of A A))

/-- The inverse system `((I^[n+1] A)[0])_n` in `D(A)`. -/
abbrev idealPowerDerivedInverseSystem (I : Ideal A) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerDerivedStep I)

variable [IsNoetherianRing A]

-- Proof sketch: use the augmentation triangles for the powered Koszul complexes to compare the
-- truncated tower `(I_n^\bullet)_n` with the quotient tower from Lemma `15.95.1`; the cone tower
-- is pro-zero by the Noetherian argument from that lemma, and Lemma `13.42.4` then identifies the
-- ideal-power tower with `(I_n^\bullet)_n` up to pro-isomorphism.
/-- Lemma 15.102.5: in Situation `15.92.15`, let `I = (f_1, \ldots, f_r)` and assume `A` is
Noetherian. Then the inverse system `((I^[n+1] A)[0])_n`, equivalently `((I^(n+1))[0])_n`, is
isomorphic as a sequential pro-object of `D(A)` to the inverse system `(I_n^\bullet)_n`, where
`I_n^\bullet` is represented by the truncation of the powered Koszul complex
`K(A; f_1^(n+1), \ldots, f_r^(n+1))`. This item-file indexing convention has stage `0`
corresponding to the textbook stage `n = 1`. -/
theorem exists_pro_isomorphism_ideal_powers_to_derived_completion_koszul_ideal_tower
    (f : Fin r → A) :
    ∃ a :
        SequentialProObjectMorphismRep
          (idealPowerDerivedInverseSystem (Ideal.span (Set.range f)))
          (derivedCompletionKoszulPowersDerivedInverseSystem f),
      IsIso a.toProObjectHom := sorry

end

/-! ### Lemma_15_102_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite
open SequentialProObjectMorphismRep

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

open scoped IdealPowerSubmodule

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "singleCpx0" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev Q : CpxA ⥤ DMod := DerivedCategory.Q

private noncomputable instance : (DerivedCategory.Q : CpxA ⥤ DMod).Monoidal := by
  change
    (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙ Qh)).Monoidal
  infer_instance

private abbrev ringAsModule : ModuleCat A :=
  ModuleCat.of A A

private abbrev idealPowerRingStage (I : Ideal A) (n : ℕ) : ModuleCat A :=
  idealPowerStage I n ringAsModule

/- Domain-style sampling for Lemma 15.102.6:
- primary domain: ideal-power towers of cochain complexes in `D(A)` and their comparison with the
  derived tensor tower;
- sampled owner declarations:
  `idealPowerDerivedInverseSystem`,
  `derivedTensorProduct`,
  `idealPowerSubmoduleFunctor`,
  `Functor.mapHomologicalComplex`,
  `NatTrans.mapHomologicalComplex`;
- best owner abstraction: the source-facing source tower is the canonical derived tensor tower
  `idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (DerivedCategory.Q.obj M)`, built from
  the chapter owner `idealPowerDerivedInverseSystem`; the explicit tensor-on-complex model
  `((I^(n+1)A) ⊗_A M^•)_n` is only bridge data for the proof;
- primitive data: the ideal `I`, the cochain complex `M`, the canonical ideal-power stage
  `idealPowerStage I (n + 1) (ModuleCat.of A A)`, and the multiplication map
  `I^(n+1)A ⊗ M^i → I^(n+1) M^i`;
- derived API: the canonical derived tensor tower, the ideal-power subcomplex tower, and the
  resulting pro-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the derived tensor tower `(I^(n+1)[0] ⊗^L_A M^•)_n`, the ideal-power tower
  `(I^(n+1) M^•)_n`, and the pro-isomorphism comparison between them;
- `core/canonical`: `idealPowerDerivedInverseSystem`, `derivedTensorProduct`,
  `idealPowerSubmoduleFunctor`, `idealPowerSubmoduleInclusionNatTrans`,
  `Functor.mapHomologicalComplex`, and `NatTrans.mapHomologicalComplex`;
- `bridge/view`: the explicit tensor-on-complex model and the degreewise multiplication maps
  `I^(n+1)A ⊗ M^i → I^(n+1) M^i`. -/

private abbrev idealPowerTensorToSubmoduleBilinear
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    I^[n] A →ₗ[A] M →ₗ[A] I^[n] M where
  toFun a :=
    { toFun := fun m ↦
        ⟨(a : A) • m,
          by
            have ha : (a : A) ∈ (I ^ n : Ideal A) := by
              simpa [idealPowerSubmodule] using a.2
            exact Submodule.smul_mem_smul ha (by simp : m ∈ (⊤ : Submodule A M))⟩
      map_add' x y := by
        ext
        simp [smul_add]
      map_smul' r x := by
        ext
        simpa [smul_smul] using congrArg (fun t : A ↦ t • x) (mul_comm (a : A) r) }
  map_add' a b := by
    ext m
    simp [add_smul]
  map_smul' r a := by
    ext m
    simpa [smul_smul] using congrArg (fun t : A ↦ t • m) (mul_comm (a : A) r)

private abbrev idealPowerTensorToSubmodule
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    (tensorLeft (idealPowerRingStage I n)).obj M ⟶ idealPowerStage I n M :=
  ModuleCat.ofHom (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n M))

private theorem idealPowerTensorToSubmodule_naturality_linear
    (I : Ideal A) (n : ℕ) {X Y : ModuleCat A} (f : X ⟶ Y) :
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n Y) ∘ₗ
        ModuleCat.Hom.hom ((tensorLeft (idealPowerRingStage I n)).map f) =
      idealPowerSubmoduleMap I f.hom n ∘ₗ
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n X) := sorry

private abbrev idealPowerTensorToSubmoduleNatTrans
    (I : Ideal A) (n : ℕ) :
    tensorLeft (idealPowerRingStage I n) ⟶ idealPowerSubmoduleFunctor I n where
  app M := idealPowerTensorToSubmodule I n M
  naturality {X} {Y} f := by
    apply ModuleCat.hom_ext
    exact idealPowerTensorToSubmodule_naturality_linear I n f

private abbrev idealPowerRingStep (I : Ideal A) (n : ℕ) :
    idealPowerRingStage I (n + 2) ⟶ idealPowerRingStage I (n + 1) :=
  (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app ringAsModule

-- The bridge cochain complex `I^(n+1)A ⊗_A M^\bullet` used internally to compare the
-- source-facing derived tensor tower with the ideal-power tower.
private abbrev idealPowerTensorComplex (I : Ideal A) (M : CpxA) (n : ℕ) : CpxA :=
  ((tensorLeft (idealPowerRingStage I (n + 1))).mapHomologicalComplex (up ℤ)).obj M

private abbrev idealPowerTensorComplexFunctor (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (tensorLeft (idealPowerRingStage I (n + 1))).mapHomologicalComplex (up ℤ)

private abbrev idealPowerTensorStepNatTrans (I : Ideal A) (n : ℕ) :
    tensorLeft (idealPowerRingStage I (n + 2)) ⟶
      tensorLeft (idealPowerRingStage I (n + 1)) :=
  (tensoringLeft (ModuleCat A)).map (idealPowerRingStep I n)

private abbrev idealPowerTensorComplexStepNatTrans (I : Ideal A) (n : ℕ) :
    idealPowerTensorComplexFunctor I (n + 1) ⟶ idealPowerTensorComplexFunctor I n :=
  NatTrans.mapHomologicalComplex (idealPowerTensorStepNatTrans I n) (up ℤ)

private abbrev idealPowerTensorStepLinear (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    TensorProduct A (idealPowerRingStage I (n + 2)) M →ₗ[A]
      TensorProduct A (idealPowerRingStage I (n + 1)) M :=
  ModuleCat.Hom.hom ((idealPowerTensorStepNatTrans I n).app M)

private abbrev idealPowerSubmoduleStepLinear (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    idealPowerStage I (n + 2) M →ₗ[A] idealPowerStage I (n + 1) M :=
  ModuleCat.Hom.hom ((idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app M)

private abbrev idealPowerTensorComplexStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M (n + 1) ⟶ idealPowerTensorComplex I M n :=
  (idealPowerTensorComplexStepNatTrans I n).app M

-- The cochain complex `I^(n+1) M^\bullet`, obtained by applying the canonical ideal-power
-- submodule functor degreewise to `M^\bullet`.
private abbrev idealPowerComplexFunctor (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (idealPowerSubmoduleFunctor I (n + 1)).mapHomologicalComplex (up ℤ)

private abbrev idealPowerComplex (I : Ideal A) (M : CpxA) (n : ℕ) : CpxA :=
  (idealPowerComplexFunctor I n).obj M

private abbrev idealPowerComplexStepNatTrans (I : Ideal A) (n : ℕ) :
    idealPowerComplexFunctor I (n + 1) ⟶ idealPowerComplexFunctor I n :=
  NatTrans.mapHomologicalComplex
    (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))) (up ℤ)

private abbrev idealPowerComplexStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerComplex I M (n + 1) ⟶ idealPowerComplex I M n :=
  (idealPowerComplexStepNatTrans I n).app M

private abbrev idealPowerComplexDerivedStage (I : Ideal A) (M : CpxA) (n : ℕ) : DMod :=
  Q.obj (idealPowerComplex I M n)

private abbrev idealPowerComplexDerivedStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerComplexDerivedStage I M (n + 1) ⟶ idealPowerComplexDerivedStage I M n :=
  Q.map (idealPowerComplexStep I M n)

/-- The inverse system `(Q(I^(n+1) M^\bullet))_n` in `D(A)`. -/
abbrev idealPowerComplexDerivedInverseSystem (I : Ideal A) (M : CpxA) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerComplexDerivedStep I M)

-- The internal stagewise comparison map
-- `I^(n+1)A ⊗_A M^\bullet ⟶ I^(n+1) M^\bullet`.
private abbrev idealPowerTensorComplexToIdealPowerComplex (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M n ⟶ idealPowerComplex I M n :=
  (NatTrans.mapHomologicalComplex (idealPowerTensorToSubmoduleNatTrans I (n + 1)) (up ℤ)).app M

private theorem idealPowerTensorToSubmodule_step_comm
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
        idealPowerTensorStepLinear I n M =
      idealPowerSubmoduleStepLinear I n M ∘ₗ
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M) := sorry

private theorem idealPowerTensorToSubmodule_step_comm_hom
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    (idealPowerTensorStepNatTrans I n).app M ≫
      idealPowerTensorToSubmodule I (n + 1) M =
    idealPowerTensorToSubmodule I (n + 2) M ≫
      (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app M := by
  apply ModuleCat.hom_ext
  exact idealPowerTensorToSubmodule_step_comm I n M

private theorem idealPowerTensorToSubmodule_step_natTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerTensorStepNatTrans I n ≫
      idealPowerTensorToSubmoduleNatTrans I (n + 1) =
    idealPowerTensorToSubmoduleNatTrans I (n + 2) ≫
      idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1)) := by
  apply NatTrans.ext
  funext M
  exact idealPowerTensorToSubmodule_step_comm_hom I n M

private theorem idealPowerTensorComplexToIdealPowerComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexStep I M n ≫ idealPowerTensorComplexToIdealPowerComplex I M n =
      idealPowerTensorComplexToIdealPowerComplex I M (n + 1) ≫ idealPowerComplexStep I M n := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (up ℤ)).app M)
      (idealPowerTensorToSubmodule_step_natTrans I n)
  simpa [idealPowerTensorComplexStep, idealPowerTensorComplexToIdealPowerComplex,
    idealPowerComplexStep] using h

private abbrev idealPowerTensorComplexDerivedStage (I : Ideal A) (M : CpxA) (n : ℕ) : DMod :=
  Q.obj (idealPowerTensorComplex I M n)

private abbrev idealPowerTensorComplexDerivedStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M (n + 1) ⟶
      idealPowerTensorComplexDerivedStage I M n :=
  Q.map (idealPowerTensorComplexStep I M n)

-- The bridge inverse system `(Q(I^(n+1)A ⊗_A M^\bullet))_n` in `D(A)`.
private abbrev idealPowerTensorComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerTensorComplexDerivedStep I M)

private theorem idealPowerTensorComplexToIdealPowerComplexDerived_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStep I M n ≫
        Q.map (idealPowerTensorComplexToIdealPowerComplex I M n) =
      Q.map (idealPowerTensorComplexToIdealPowerComplex I M (n + 1)) ≫
        idealPowerComplexDerivedStep I M n := by
  simpa [idealPowerTensorComplexDerivedStep] using
    congrArg Q.map
      (idealPowerTensorComplexToIdealPowerComplex_step_comm I M n)

private abbrev idealPowerTensorComplexToIdealPowerComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerTensorComplexDerivedInverseSystem I M ⟶
      idealPowerComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ Q.map (idealPowerTensorComplexToIdealPowerComplex I M n))
    (fun n ↦ by
      simpa using idealPowerTensorComplexToIdealPowerComplexDerived_step_comm I M n)

private abbrev idealPowerStageSingleComplex (I : Ideal A) (n : ℕ) : CpxA :=
  (singleCpx0).obj (idealPowerRingStage I (n + 1))

private theorem idealPowerTensorComplex_eq_tensorObj
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M n =
      HomologicalComplex.tensorObj (idealPowerStageSingleComplex I n) M :=
  sorry

private noncomputable abbrev idealPowerTensorComplexDerivedStageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M n ≅
      ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)).obj (op n)) :=
  (Q.mapIso (eqToIso (idealPowerTensorComplex_eq_tensorObj I M n))) ≪≫
    (Functor.Monoidal.μIso Q
      (idealPowerStageSingleComplex I n) M).symm ≪≫
    (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl _) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct
        (idealPowerDerivedStage I n) (Q.obj M)

private theorem idealPowerDerivedTensorToTensorComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    ((derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n)) ≫
        (idealPowerTensorComplexDerivedStageIso I M n).inv =
      (idealPowerTensorComplexDerivedStageIso I M (n + 1)).inv ≫
        idealPowerTensorComplexDerivedStep I M n := sorry

private abbrev idealPowerDerivedTensorToTensorComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerTensorComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ (idealPowerTensorComplexDerivedStageIso I M n).inv)
    (fun n ↦ by
      simpa using idealPowerDerivedTensorToTensorComplex_step_comm I M n)

-- Proof sketch: choose generators of `I`, replace the ideal-power tower by the pro-isomorphic
-- powered-Koszul tower from Lemma `15.102.5`, then tensor that pro-isomorphism with `Q.obj M`
-- using the canonical owner `derivedTensorProduct`. For the concrete comparison to
-- `(I^(n+1) M^\bullet)_n`, use the explicit tensor-on-complex bridge above and then apply Lemma
-- `13.42.5` after passing to cohomology. For each cohomological degree, resolve `M^\bullet` by a
-- bounded-above finite free complex and use Lemma `15.102.1` to identify the induced homology
-- tower with the ideal-power filtration on `H^p(M^\bullet)`.
/-- The canonical comparison from the derived tensor tower
`((I^(n+1)A)[0] \otimes_A^{\mathbf L} Q(M^\bullet))_n` to the ideal-power tower
`(Q(I^(n+1) M^\bullet))_n`, assembled directly from the canonical tensor and ideal-power stage
maps. -/
abbrev idealPowerDerivedTensorToIdealPowerComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerComplexDerivedInverseSystem I M :=
  idealPowerDerivedTensorToTensorComplexNatTrans I M ≫
    idealPowerTensorComplexToIdealPowerComplexNatTrans I M

/-- Lemma 15.102.6: let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `M^\bullet`
be a bounded complex of finite `A`-modules. Then the canonical comparison from the derived tensor
tower `((I^(n+1)A)[0] \otimes_A^{\mathbf L} Q(M^\bullet))_n`, equivalently
`idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (DerivedCategory.Q.obj M)`, to the
ideal-power tower `(Q(I^(n+1) M^\bullet))_n` is an isomorphism of sequential pro-objects. In this
item-file convention, stage `0` corresponds to the textbook power `I^1`. -/
theorem idealPowerDerivedTensorToIdealPowerComplex_isIso
    (I : Ideal A) (M : CpxA)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (ofNatTrans (idealPowerDerivedTensorToIdealPowerComplexNatTrans I M)).toProObjectHom :=
  sorry

end

/-! ### Lemma_15_102_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct IdealPowerSubmodule

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.102.7:
- primary domain: eventual factorization in `D(A)` of the ideal-power inclusion through the first
  stage of the derived ideal-power tensor tower;
- sampled owner declarations:
  `idealPowerStage`,
  `idealPowerSubtype`,
  `derivedTensorProduct`,
  `singleZeroDerivedTensorIso`;
- best owner abstraction: the source-facing factorization should reuse the chapter owner
  `singleZeroDerivedTensorIso` for the canonical tensor-unit identification
  `A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`, rather than restating that bridge by an expanded
  whiskered composite;
- primitive data: the ideal `I`, the finite module `M`, and the canonical inclusion
  `idealPowerSubtype I n M`;
- derived API: the existence of a power `n` and a factorization of that inclusion through
  `I[0] \otimes_A^{\mathbf L} M[0]`.

Source/core/bridge triage:
- `source-facing`: the eventual factorization statement below;
- `core/canonical`: `idealPowerStage`, `idealPowerSubtype`, and `derivedTensorProduct`;
- `bridge/view`: `singleZeroDerivedTensorIso`, identifying `A[0] \otimes_A^{\mathbf L} -` with the
  identity on `D(A)`. -/

-- Proof sketch: view `M` as the complex `M[0]` and apply Lemma `15.102.6` to compare the tower
-- `(I^n \otimes_A^{\mathbf L} M[0])_n` with `(I^n M[0])_n`. For sufficiently large `n`, the map
-- `I^n M[0] → M[0]` is represented by the tensor-stage map coming from the inclusion
-- `I^n ⟶ I ⟶ A`, followed by the canonical tensor-unit identification
-- `A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`.
/-- Lemma 15.102.7: if `A` is Noetherian, `I ⊆ A` is an ideal, and `M` is a finite `A`-module,
then for some integer `n > 0` the canonical map `I^n M[0] → M[0]` in `D(A)` factors through the
map induced by `I → A`,
`I[0] \otimes_A^{\mathbf L} M[0] → A[0] \otimes_A^{\mathbf L} M[0]`,
together with the canonical tensor-unit identification
`A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`. -/
theorem exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map
    (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ n : ℕ, 0 < n ∧
      ∃ α : (single₀).obj (idealPowerStage I n M) ⟶
          (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M,
        α ≫
            (derivedTensorProduct ((single₀).obj M)).map
              ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
            (singleZeroDerivedTensorIso ((single₀).obj M)).hom =
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_102_Basic (from Chap15) -/
noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A]

/-- The `n`th `I`-power submodule `I^n X`. -/
abbrev idealPowerSubmodule (I : Ideal A) (n : ℕ) (X : Type v)
    [AddCommGroup X] [Module A X] : Submodule A X :=
  I ^ n • (⊤ : Submodule A X)

end

namespace IdealPowerSubmodule

/- Textbook notation for the `n`th ideal-power submodule `I^n X`. -/
scoped notation:max I "^[" n "]" => idealPowerSubmodule I n

end IdealPowerSubmodule

section

variable {A : Type u} [CommRing A]

open scoped IdealPowerSubmodule

/-- The canonical inclusion `I^[n] X ↪ X`. -/
abbrev idealPowerSubtype (I : Ideal A) (n : ℕ) (X : Type v)
    [AddCommGroup X] [Module A X] : (I^[n] X) →ₗ[A] X :=
  (I^[n] X).subtype

-- Proof sketch: if `m ≤ n`, then `I^n ≤ I^m`; smul monotonicity on submodules gives
-- `I^n X ⊆ I^m X`.
/-- Higher ideal-power submodules are contained in lower ones. -/
theorem idealPowerSubmodule_mono
    (I : Ideal A) {X : Type v} [AddCommGroup X] [Module A X] {m n : ℕ} (h : m ≤ n) :
    I^[n] X ≤ I^[m] X := by
  have smul_top_mono {J K : Ideal A} (hJK : J ≤ K) :
      J • (⊤ : Submodule A X) ≤ K • (⊤ : Submodule A X) := by
    intro y hy
    exact Submodule.smul_induction_on hy
      (fun r hr x hx ↦ Submodule.smul_mem_smul (hJK hr) hx)
      (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  exact smul_top_mono (Ideal.pow_le_pow_right h)

/-- Restriction of a linear map to the `n`th ideal-power submodules. -/
abbrev idealPowerSubmoduleMap
    {X Y : Type v} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (I : Ideal A) (f : X →ₗ[A] Y) (n : ℕ) :
    I^[n] X →ₗ[A] I^[n] Y :=
  f.restrict fun x hx ↦ by
    have hmap : Submodule.map f (I^[n] X) ≤ I^[n] Y := by
      rw [idealPowerSubmodule, idealPowerSubmodule, Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    exact hmap (Submodule.mem_map_of_mem hx)

/-- Passage to the `n`th ideal-power submodule as an endofunctor of `Mod_A`. -/
abbrev idealPowerSubmoduleFunctor
    (I : Ideal A) (n : ℕ) :
    ModuleCat A ⥤ ModuleCat A where
  obj M := ModuleCat.of A ↥(I^[n] M)
  map f := ModuleCat.ofHom (idealPowerSubmoduleMap I f.hom n)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

instance (I : Ideal A) (n : ℕ) :
    (idealPowerSubmoduleFunctor (A := A) I n).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    rfl

/-- Inclusion of higher ideal-power stages into lower ones as a natural transformation. -/
abbrev idealPowerSubmoduleInclusionNatTrans
    (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    idealPowerSubmoduleFunctor I n ⟶ idealPowerSubmoduleFunctor I m where
  app M := ModuleCat.ofHom (Submodule.inclusion (idealPowerSubmodule_mono I h))
  naturality {X} {Y} f := by
    ext x
    rfl

/-- Inclusion of the `n`th ideal-power stage into the ambient module as a natural
transformation. -/
abbrev idealPowerSubtypeNatTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerSubmoduleFunctor I n ⟶ 𝟭 (ModuleCat A) where
  app M := ModuleCat.ofHom (idealPowerSubtype I n M)
  naturality {X} {Y} f := by
    ext x
    rfl

local notation "Mod" => ModuleCat A

/-- The `n`th ideal-power stage of a module, viewed as an object of `Mod_A`. -/
def idealPowerStage (I : Ideal A) (n : ℕ) (M : Mod) : Mod :=
  ModuleCat.of A (I^[n] M)

/-- The map on `Tor_p^A(-, N)` induced by the inclusion `I^[n] M ↪ M`. -/
abbrev idealPowerSubtypeTorMap
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Tor[A, p](↥(I^[n] M), N) ⟶ Tor[A, p](M, N) :=
  (((Tor (ModuleCat A) p).flip.obj N).map (ModuleCat.ofHom (idealPowerSubtype I n M)))

/-- The restriction map on `Ext^p_A(-, N)` induced by the inclusion `I^[n] M ↪ M`. -/
abbrev idealPowerSubtypeExtPrecomp
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Ext M N p →ₗ[A] Ext (idealPowerStage I n M) N p :=
  (mk₀ (ModuleCat.ofHom (idealPowerSubtype I n M))).precompOfLinear A N (zero_add p)

/-- The map on `Ext^p_A(M, -)` induced by the inclusion `I^[n] N ↪ N`. -/
abbrev idealPowerSubtypeExtPostcomp
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Ext M (idealPowerStage I n N) p →ₗ[A] Ext M N p :=
  (mk₀ (ModuleCat.ofHom (idealPowerSubtype I n N))).postcompOfLinear A M (add_zero p)

end
