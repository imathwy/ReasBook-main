import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_35_1 (from Chap20) -/
/-
Domain-style sampling for Lemma 20.35.1:
- primary domain: sheaf cohomology towers of `A`-module sheaves on a topological space, controlled
  by the associated graded ring of an ideal and the canonical Mittag-Leffler predicate on the
  underlying inverse system of abelian groups;
- sampled owners:
  * `idealAssociatedGradedRing` from `Chap10/10_69_0_1`;
  * `CategoryTheory.Functor.IsMittagLeffler`;
  * `Sheaf.cohomologyPresheafFunctor`.
- owner choice: this lemma is `source-facing`; its `core/canonical` owners are
  `idealAssociatedGradedRing` for the graded ring and `Functor.IsMittagLeffler` for the
  stabilization condition.
- primitive data: the chosen tower `ℱ`, the chosen models `powSheaf n`, and the chosen short exact
  sequences `ses n`.
- derived API: the cohomology tower and the direct sum of the degree-`p + 1` cohomology groups.
  Those are used only as canonical functor/type expressions here, so they should not survive as
  separate local public wrappers.
-/

open CategoryTheory
open Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} A)
local notation "AbSheaf" => Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The forgetful functor from sheaves of `A`-modules on `X` to sheaves of abelian groups. -/
abbrev topologicalSpaceModuleSheafUnderlyingAbelian : ModSheaf ⥤ AbSheaf :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- The degree-`p` cohomology functor on sheaves of `A`-modules on `X`, computed on the
underlying abelian sheaf and then evaluated on the top open. -/
abbrev topologicalSpaceModuleCohomologyFunctor (p : ℕ) : ModSheaf ⥤ AddCommGrpCat.{u} :=
  topologicalSpaceModuleSheafUnderlyingAbelian ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

/-- The inverse system `n ↦ H^p(X, \mathcal F_n)` attached to a sequential tower of sheaves of
`A`-modules on `X`. -/
abbrev topologicalSpaceModuleCohomologyTower
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (p : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ℱ ⋙ topologicalSpaceModuleCohomologyFunctor p

/-- The graded direct sum `\bigoplus_n H^p(X,\mathcal G_n)` attached to a family of sheaves of
`A`-modules on `X`. -/
abbrev topologicalSpaceModuleCohomologyDirectSum
    (𝒢 : ℕ → ModSheaf) (p : ℕ) : Type u :=
  DirectSum ℕ fun n ↦ (topologicalSpaceModuleCohomologyFunctor p).obj (𝒢 n)

-- Proof sketch: for each `n`, the short exact sequence
-- `0 → powSheaf n → \mathcal F_{n+1} → \mathcal F_n → 0` gives a boundary map
-- `H^p(X, \mathcal F_n) → H^{p+1}(X, powSheaf n)`. The direct sum of the images of these boundary
-- maps is stable under the action of the associated graded ring, so the Noetherian hypothesis
-- yields finite generation in bounded degree. The long exact sequence then shows that the images
-- of the transition maps in the tower `H^p(X, \mathcal F_n)` stabilize, which is exactly the
-- Mittag-Leffler condition `1`.
/-- Lemma 20.35.1: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X` such that
`0 → I^n \mathcal F_{n + 1} → \mathcal F_{n + 1} → \mathcal F_n → 0` is represented by the chosen
short exact sequence `ses n`. If the direct sum
`\bigoplus_{n \ge 0} H^{p + 1}(X, I^n \mathcal F_{n + 1})`, encoded here by the direct sum
`DirectSum ℕ fun n ↦ H^{p + 1}(X, powSheaf n)`, is Noetherian over the associated graded ring of
`I`, then the inverse system `M_n = H^p(X, \mathcal F_n)` satisfies Mittag-Leffler condition `1`.
-/
theorem topologicalSpace_moduleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ModSheaf)
    (ses : ∀ n : ℕ, ShortComplex ModSheaf)
    (hses : ∀ n : ℕ, (ses n).ShortExact)
    (ses_left_iso : ∀ n : ℕ, (ses n).X₁ ≅ powSheaf n)
    (ses_middle_iso : ∀ n : ℕ, (ses n).X₂ ≅ ℱ.obj (op (n + 1)))
    (ses_right_iso : ∀ n : ℕ, (ses n).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    [Module (idealAssociatedGradedRing I)
      (topologicalSpaceModuleCohomologyDirectSum powSheaf (p + 1))]
    [IsNoetherian (idealAssociatedGradedRing I)
      (topologicalSpaceModuleCohomologyDirectSum powSheaf (p + 1))] :
    ((topologicalSpaceModuleCohomologyTower ℱ p) ⋙
      forget AddCommGrpCat.{u}).IsMittagLeffler := sorry

end

end CategoryTheory

/-! ### Lemma_20_35_2 (from Chap20) -/
open Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- For fixed `n`, this is the inverse system `m ↦ H^p(X, I^n \mathcal F_{m+1})`, modeled by
the chosen tower `powSheaf n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerTower
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p n : ℕ) : ℕᵒᵖ ⥤ Type u :=
  (powSheaf n ⋙ topologicalSpaceModuleCohomologyFunctor p) ⋙ forget AddCommGrpCat

-- Proof sketch: unfold `topologicalSpaceModuleCohomologyIdealPowerTower`; evaluating at `op m`
-- just computes degree-`p` cohomology of the `m`-th stage of the chosen ideal-power tower.
/-- Evaluating the ideal-power cohomology tower at `op m` gives the degree-`p` cohomology of the
corresponding stage of `powSheaf n`. -/
theorem topologicalSpaceModuleCohomologyIdealPowerTower_obj
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p n m : ℕ) :
    (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).obj (op m) =
      (topologicalSpaceModuleCohomologyFunctor p).obj ((powSheaf n).obj (op m)) := sorry

/-- For fixed `n`, this is the subgroup `N_n` from the source, encoded as the eventual range of
the tower `m ↦ H^{p+1}(X, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerEventualRange
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : Set ((topologicalSpaceModuleCohomologyIdealPowerTower powSheaf (p + 1) n).obj
      (op n)) :=
  (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf (p + 1) n).eventualRange (op n)

/-- The graded object `\bigoplus N_n` from the source, realized as the direct sum of the
eventual-range pieces. The additive structure on each graded piece is supplied explicitly as a
parameter when this construction is used. -/
abbrev topologicalSpaceIdealPowerEventualRangeDirectSum
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p : ℕ)
    [∀ n : ℕ, AddCommMonoid (topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n)] :
    Type u :=
  DirectSum ℕ fun n ↦ topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n

-- Proof sketch: argue exactly as in Lemma `20.35.1`, replacing the full graded cohomology direct
-- sum by the graded submodule `⊕ N_n` of eventual ranges. The boundary maps land in `N_n`, and
-- multiplication by classes in `I^k / I^{k+1}` sends `N_n` into `N_{n+k}`; the Noetherian
-- hypothesis then forces stabilization of the images in the cohomology tower.
/-- Lemma 20.35.2: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X`. For each
`n`, let `powSheaf n` model the inverse system `m ↦ I^n \mathcal F_{m+1}` and write
`N_n = topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n`, so that `N_n` is
the intersection of the images of the maps
`H^{p+1}(X, I^n \mathcal F_{m+1}) → H^{p+1}(X, I^n \mathcal F_{n+1})` for `m ≥ n`. Assume the
short exact sequences `0 → I^n \mathcal F_{m+1} → \mathcal F_{m+1} → \mathcal F_n → 0` are
encoded by `ses`, and assume the graded direct sum `\bigoplus N_n` is Noetherian over the
associated graded ring `\bigoplus_{n \ge 0} I^n / I^{n+1}`. Then the inverse system
`M_n = H^p(X, \mathcal F_n)` satisfies the Mittag-Leffler condition `2`, expressed here by the
standard categorical predicate `IsMittagLeffler`. -/
theorem topologicalSpace_moduleCohomologyTower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    (p : ℕ)
    [∀ n : ℕ, AddCommMonoid (topologicalSpaceModuleCohomologyIdealPowerEventualRange powSheaf p n)]
    [Module (idealAssociatedGradedRing I) (topologicalSpaceIdealPowerEventualRangeDirectSum powSheaf p)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSum powSheaf p)] :
    ((topologicalSpaceModuleCohomologyTower ℱ p) ⋙ forget AddCommGrpCat).IsMittagLeffler := sorry

end

end CategoryTheory

/-! ### Lemma_20_35_3 (from Chap20) -/
/-
Domain-style sampling for Lemma 20.35.3:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules, compared with
  `I`-adic module topologies via the kernel filtration on the limit;
- sampled owner declarations:
  * `_root_.idealAssociatedGradedRing`;
  * `Ideal.adicModuleTopology`;
  * `LinearMap.ker`;
  * `TopologicalSpace.induced`;
  * `CategoryTheory.Limits.limit.π`.
- owner choice:
  * `source-facing`: the cohomological topology statement proved downstream from this abstract
    module lemma;
  * `core/canonical`: `CategoryTheory.inverseLimitTopology`, defined below from
    `TopologicalSpace.induced` and `limit.π`, together with the intrinsic kernel filtration on
    `limit cohomologySystem`;
  * `bridge/view`: the downstream comparison from source cohomology groups
    `H^p(X, I^n \mathcal F_{n + 1})` or their eventual images to the associated graded of that
    kernel filtration.
- primitive data: the ideal `I` and the inverse system `cohomologySystem`;
- derived API: `CategoryTheory.inverseLimitTopology cohomologySystem`,
  `inverseLimitKernelFiltration cohomologySystem`, and
  `inverseLimitKernelAssociatedGraded cohomologySystem`.
-/

noncomputable section

universe u

namespace CategoryTheory

open Limits Opposite
open scoped DirectSum

section

variable {A : Type u} [CommRing A]

/-- The topology on the inverse limit of a sequential system of `A`-modules induced from the
product of the discrete quotient modules. -/
abbrev inverseLimitTopology (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) :
    TopologicalSpace ↥(limit cohomologySystem) :=
  let _ : (n : ℕ) → TopologicalSpace ↥(cohomologySystem.obj (op n)) := fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : ↥(limit cohomologySystem) ↦
      fun n : ℕ ↦ ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)))
    inferInstance

/-- The `n`-th step of the kernel filtration on the inverse limit, given by the kernel of the
projection to stage `n`. -/
abbrev inverseLimitKernelFiltration (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Submodule A ↥(limit cohomologySystem) :=
  LinearMap.ker ((limit.π cohomologySystem (op n)).hom)

/-- The kernel filtration is decreasing: the kernel of the projection to stage `n + 1` lies in the
kernel of the projection to stage `n`. -/
theorem inverseLimitKernelFiltration_succ_le
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    inverseLimitKernelFiltration cohomologySystem (n + 1) ≤
      inverseLimitKernelFiltration cohomologySystem n := by
  intro x hx
  have hx' : ((limit.π cohomologySystem (op (n + 1))).hom x :
      cohomologySystem.obj (op (n + 1))) = 0 := by
    simpa [inverseLimitKernelFiltration] using hx
  have hw :
      ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)) =
        (cohomologySystem.map (homOfLE (Nat.le_succ n)).op).hom
          ((limit.π cohomologySystem (op (n + 1))).hom x) := by
    simpa using congrArg
      (fun f : limit cohomologySystem ⟶ cohomologySystem.obj (op n) ↦ f x)
      ((limit.w cohomologySystem ((homOfLE (Nat.le_succ n)).op)).symm)
  calc
    ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n))
        = (cohomologySystem.map (homOfLE (Nat.le_succ n)).op).hom
            ((limit.π cohomologySystem (op (n + 1))).hom x) := hw
    _ = 0 := by simp [hx']

/-- The degree-`n` quotient `F^n / F^{n + 1}` of the kernel filtration on the inverse limit. -/
abbrev inverseLimitKernelFiltrationPiece (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Type u :=
  ↥(inverseLimitKernelFiltration cohomologySystem n) ⧸
    (inverseLimitKernelFiltration cohomologySystem (n + 1)).submoduleOf
      (inverseLimitKernelFiltration cohomologySystem n)

/-- The associated graded direct sum `⊕_n F^n / F^{n + 1}` of the kernel filtration on the inverse
limit. This is the intrinsic graded module that the source compares to ideal-power cohomology in
later lemmas. -/
abbrev inverseLimitKernelAssociatedGraded
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) : Type u :=
  DirectSum ℕ fun n ↦ inverseLimitKernelFiltrationPiece cohomologySystem n

-- Proof sketch: let `F^n` be the kernel of the projection from `lim_n M_n` to `M_n`. If the
-- associated graded module `⊕_n F^n / F^{n + 1}` is Noetherian over the associated graded ring of
-- `I`, then the kernel filtration satisfies the stabilization required in the source argument, so
-- the neighborhoods defined by the inverse-limit topology agree with the `I`-power neighborhoods.
-- The downstream cohomological lemmas are responsible for constructing the comparison from source
-- cohomology groups to this intrinsic associated graded module.
/-- Lemma 20.35.3: let `F^n` be the kernel of the projection
`lim_n M_n → M_n` for a sequential inverse system `cohomologySystem = (M_n)_n` of `A`-modules. If
the associated graded module `⊕_{n ≥ 0} F^n / F^{n + 1}` is Noetherian over the associated graded
ring `⊕_{n ≥ 0} I^n / I^(n + 1)`, then the inverse-limit topology on `lim_n M_n` is the
`I`-adic topology. In later source-facing applications, the relevant cohomology groups
`H^p(X, I^n \mathcal F_{n + 1})` are used only through a comparison with this intrinsic associated
graded module. -/
lemma inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded cohomologySystem)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded cohomologySystem)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end

end CategoryTheory

/-! ### Lemma_20_35_4 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- For fixed `n`, this is the subgroup `N_n` from the source in degree `p`, encoded as the
eventual range of the tower `m ↦ H^p(X, I^n \mathcal F_{m+1})` at stage `n`. -/
abbrev topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (p n : ℕ) : Set ((topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).obj (op n)) :=
  (topologicalSpaceModuleCohomologyIdealPowerTower powSheaf p n).eventualRange (op n)

/-- The graded object `\bigoplus N_n` from the source, realized as the direct sum of the
degree-`p` eventual-range pieces. The additive structure on each graded piece is supplied
explicitly when this construction is used. -/
abbrev topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf) (p : ℕ)
    [∀ n : ℕ, AddCommMonoid
      (topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n)] :
    Type u :=
  DirectSum ℕ fun n ↦ topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n

-- Proof sketch: use the abstract topology statement of Lemma `20.35.3` with
-- `cohomologySystem` modeling `H^p(X, \mathcal F_n)` as `A`-modules. The proof from the source
-- shows that the degree-`p` eventual ranges `N_n` form a graded submodule of
-- `⊕_n H^p(X, I^n \mathcal F_{n+1})` and that the successive quotients of the kernel filtration on
-- `lim_n H^p(X, \mathcal F_n)` are controlled by the images of the `N_n`; the Noetherian
-- hypothesis on `⊕_n N_n` then forces the inverse-limit topology to agree with the `I`-adic
-- topology.
/-- Lemma 20.35.4: let `I` be an ideal of a ring `A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be an inverse system of sheaves of `A`-modules on `X` such that
`\mathcal F_n = \mathcal F_{n + 1} / I^n \mathcal F_{n + 1}`. Let `cohomologySystem` model the
inverse system `n ↦ H^p(X, \mathcal F_n)` as `A`-modules, and for each `n` let
`N_n = topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n`, where
`powSheaf n` models the tower `m ↦ I^n \mathcal F_{m + 1}`. If the graded direct sum
`\bigoplus N_n` satisfies the ascending chain condition over the associated graded ring
`\bigoplus_{n \ge 0} I^n / I^{n + 1}`, then the inverse-limit topology on
`M = \lim_n H^p(X, \mathcal F_n)` is the `I`-adic topology. -/
theorem topologicalSpace_moduleCohomology_inverseLimitTopology_eq_adicModuleTopology_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (p : ℕ)
    (cohomologySystemIso :
      cohomologySystem ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat ≅
        topologicalSpaceModuleCohomologyTower ℱ p)
    (powSheaf : ℕ → ℕᵒᵖ ⥤ ModSheaf)
    (ses : ∀ n m : ℕ, n ≤ m → ShortComplex ModSheaf)
    (hses : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).ShortExact)
    (ses_left_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₁ ≅ (powSheaf n).obj (op m))
    (ses_middle_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₂ ≅ ℱ.obj (op (m + 1)))
    (ses_right_iso : ∀ n m : ℕ, ∀ hnm : n ≤ m, (ses n m hnm).X₃ ≅ ℱ.obj (op n))
    [∀ n : ℕ, AddCommMonoid
      (topologicalSpaceModuleCohomologyIdealPowerEventualRangeAtDegree powSheaf p n)]
    [Module (_root_.idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree powSheaf p)]
    [IsNoetherian (_root_.idealAssociatedGradedRing I)
      (topologicalSpaceIdealPowerEventualRangeDirectSumAtDegree powSheaf p)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end

end CategoryTheory
