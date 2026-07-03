import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {M : 𝒜}

local notation "D𝒜" => DerivedCategory 𝒜
local notation "single0" => DerivedCategory.singleFunctor 𝒜 (0 : ℤ)
local notation "singleComplex0" => CochainComplex.singleFunctor 𝒜 (0 : ℤ)

/- Domain-style sampling for Lemma 20.39.2:
- primary domain: sequential pro-object comparisons in `D(𝒜)` between the cokernel tower of the
  powers of an endomorphism and the corresponding two-term mapping-cone tower;
- sampled owner declarations:
  `SequentialProObjectMorphismRep`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `Functor.ofOpSequence`,
  `exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients`;
- best owner abstraction: the source-facing towers should remain explicit sequential inverse
  systems, while the pro-comparison itself should live directly in
  `SequentialProObjectMorphismRep ...` together with its owner morphism `r.toProObjectHom`;
- primitive data: the stage objects `cokernel (f ^ (n + 1))` and
  `mappingCone ((singleComplex0).map (f ^ (n + 1)))`, their transition morphisms, and the
  stabilization predicate on the kernel subobjects of the powers of `f`;
- derived API: the existence of a shift-by-`c` representative whose induced morphism in the
  sequential pro-category is an isomorphism.

Source/core/bridge triage:
- `source-facing`: `endomorphismPowerCokernelTower`, `endomorphismPowerTwoTermTower`, and
  `endomorphismPowerKernelStabilizes`;
- `core/canonical`: `SequentialProObjectMorphismRep ...` and `.toProObjectHom`;
- `bridge/view`: the explicit stagewise cokernel and mapping-cone models used to assemble the
  sequential towers. -/

/-- The degree-zero derived object represented by `\operatorname{Coker}(f^(n+1))`. -/
abbrev endomorphismPowerCokernelStage (f : End M) (n : ℕ) : D𝒜 :=
  (single0).obj (cokernel (f ^ (n + 1) : M ⟶ M))

/-- The two-term cochain complex `M \xrightarrow{f^(n+1)} M`, modeled as the mapping cone of
`f^(n+1)` placed in degree `0`. -/
abbrev endomorphismPowerTwoTermComplex (f : End M) (n : ℕ) : CochainComplex 𝒜 ℤ :=
  CochainComplex.mappingCone ((singleComplex0).map (f ^ (n + 1) : M ⟶ M))

/-- The derived object represented by the two-term complex `M \xrightarrow{f^(n+1)} M`. -/
abbrev endomorphismPowerTwoTermStage (f : End M) (n : ℕ) : D𝒜 :=
  DerivedCategory.Q.obj (endomorphismPowerTwoTermComplex f n)

-- Proof sketch: `f^(n + 2)` factors through `f^(n + 1)`, so the cokernel projection of
-- `f^(n + 1)` annihilates `f^(n + 2)`.
/-- The defining factorization condition for the transition map
`coker(f^(n+2)) ⟶ coker(f^(n+1))`. -/
theorem endomorphismPowerCokernelTransition_condition (f : End M) (n : ℕ) :
    (f ^ (n + 2) : M ⟶ M) ≫ cokernel.π (f ^ (n + 1) : M ⟶ M) = 0 := sorry

/-- The transition morphism `coker(f^(n+2)) ⟶ coker(f^(n+1))` in the cokernel tower. -/
abbrev endomorphismPowerCokernelTransition (f : End M) (n : ℕ) :
    endomorphismPowerCokernelStage f (n + 1) ⟶ endomorphismPowerCokernelStage f n :=
  (single0).map <|
    cokernel.desc (f ^ (n + 2) : M ⟶ M) (cokernel.π (f ^ (n + 1) : M ⟶ M))
      (endomorphismPowerCokernelTransition_condition f n)

-- Proof sketch: the square defining the transition between the two-term complexes commutes
-- because `f^(n + 2) = f ≫ f^(n + 1)` as endomorphisms of `M`.
/-- The commutative square used to define the transition
`(M \xrightarrow{f^(n+2)} M) ⟶ (M \xrightarrow{f^(n+1)} M)`. -/
theorem endomorphismPowerTwoTermTransition_comm (f : End M) (n : ℕ) :
    CommSq
      ((singleComplex0).map (f ^ (n + 2) : M ⟶ M))
      ((singleComplex0).map (f : M ⟶ M))
      (𝟙 ((singleComplex0).obj M))
      ((singleComplex0).map (f ^ (n + 1) : M ⟶ M)) := sorry

/-- The transition morphism
`(M \xrightarrow{f^(n+2)} M) ⟶ (M \xrightarrow{f^(n+1)} M)` in the two-term tower. -/
abbrev endomorphismPowerTwoTermTransition (f : End M) (n : ℕ) :
    endomorphismPowerTwoTermStage f (n + 1) ⟶ endomorphismPowerTwoTermStage f n :=
  DerivedCategory.Q.map <|
    CochainComplex.mappingCone.map
      ((singleComplex0).map (f ^ (n + 2) : M ⟶ M))
      ((singleComplex0).map (f ^ (n + 1) : M ⟶ M))
      ((singleComplex0).map (f : M ⟶ M))
      (𝟙 ((singleComplex0).obj M))
      (endomorphismPowerTwoTermTransition_comm f n).w

/-- The inverse system whose `n`th stage is `\operatorname{Coker}(f^(n+1))` in
`D(\mathcal A)`. -/
abbrev endomorphismPowerCokernelTower (f : End M) : ℕᵒᵖ ⥤ D𝒜 :=
  Functor.ofOpSequence (endomorphismPowerCokernelTransition f)

/-- The inverse system whose `n`th stage is the two-term complex
`M \xrightarrow{f^(n+1)} M` in `D(\mathcal A)`. -/
abbrev endomorphismPowerTwoTermTower (f : End M) : ℕᵒᵖ ⥤ D𝒜 :=
  Functor.ofOpSequence (endomorphismPowerTwoTermTransition f)

/-- The stabilization condition `\ker(f^c) = \ker(f^n)` for all `n ≥ c`, expressed as eventual
constancy of the kernel subobjects of the powers of `f`. -/
def endomorphismPowerKernelStabilizes (f : End M) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
    kernelSubobject (f ^ n : M ⟶ M) = kernelSubobject (f ^ c : M ⟶ M)

-- Proof sketch: choose a stage `c` from which the kernels of the powers of `f` stabilize. The
-- evident map from the two-term tower to the cokernel tower has identity reindexing. In the
-- opposite direction, use the quotient `M / \ker(f^c)` and the diagrams
-- `M / \ker(f^c) \xrightarrow{f^(n+c+1)} M` mapping down to `M \xrightarrow{f^(n+1)} M`; once
-- the kernels stabilize, the top horizontal map is monic and the resulting two-term complex is
-- quasi-isomorphic to `\operatorname{Coker}(f^(n+c+1))`, giving a shift-by-`c` inverse system
-- map which is inverse up to common refinement.
/-- Lemma 20.39.2: let `\mathcal A` be an abelian category, let `f : M ⟶ M` be an endomorphism,
and suppose the kernels `\ker(f^n)` stabilize. Then the inverse systems
`(M \xrightarrow{f^(n+1)} M)_n` and `(\operatorname{Coker}(f^(n+1)))_n` are pro-isomorphic in
`D(\mathcal A)`. In the project's canonical sequential pro-object API this is recorded by a
shifted representative whose induced pro-object morphism is an isomorphism, using the standard
chapter convention that stage `n` corresponds to the exponent `n + 1`. -/
theorem exists_cokernel_to_endomorphismPowerTwoTerm_shiftedProIsomorphism
    (f : End M)
    (hstable : endomorphismPowerKernelStabilizes f) :
    ∃ c : ℕ,
      ∃ r :
        SequentialProObjectMorphismRep
          (endomorphismPowerCokernelTower f)
          (endomorphismPowerTwoTermTower f),
        (∀ n : ℕ, r.reindex n = n + c) ∧ IsIso r.toProObjectHom := sorry

end

end CategoryTheory
