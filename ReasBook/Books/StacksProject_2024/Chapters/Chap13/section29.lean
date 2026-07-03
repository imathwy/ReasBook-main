import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_29_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex

noncomputable section

universe v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/-
Domain-style sampling for Lemma `13.29.1`.
- primary domain: sequential upper truncation towers of cochain complexes together with compatible
  bounded-above resolutions in an object property;
- sampled owner declarations:
  `Over` for objects over a fixed diagram in a functor category,
  `Functor.ofSequence` / `NatTrans.ofSequence` for sequential diagrams and cocones,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn` from `Lemma_13_15_4` for the stagewise bounded-above
  resolution predicate,
  `LowerTruncationResolutionSystem` from `Lemma_13_29_3` as the nearby dual source-facing pattern;
- best owner abstraction: the intrinsic tower data is an object of
  `Over (upperTruncationDiagram K)`, i.e. a sequential diagram together with a natural
  transformation into the canonical upper truncation tower;
- primitive-vs-derived split:
  primitive data: the over-object `T : Over (upperTruncationDiagram K)` together with the proof
    fields that each stage and each transition map satisfy the textbook conditions;
  derived API: the source-facing accessors `T.diagram` and `T.comparison`, then the stage complex
    `T.stage n`, the step map `T.step n`, the stage map `T.toTarget n`, and the cocone/colimit
    comparison built from the owner abstraction.

Source/core/bridge triage:
- source-facing: `UpperTruncationResolutionTower` and the existence theorem below;
- core/canonical: `Over (upperTruncationDiagram K)` and
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- bridge/view: the accessors `diagram`, `comparison`, `stage`, `step`, `toTarget`, `cocone`, and
  `fromColimit`.
-/

/-- The stage `τ_{\le n + 1} K^•` in the upper truncation tower of a cochain complex. The index
`0` corresponds to `τ_{\le 1} K^•`. -/
abbrev upperTruncationStage (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  K.truncLE ((n : ℤ) + 1)

/-- The canonical transition map `τ_{\le n + 1} K^• ⟶ τ_{\le n + 2} K^•` in the upper truncation
tower of a cochain complex. -/
noncomputable abbrev truncLEStep (K : CochainComplex A ℤ) (n : ℕ) :
    upperTruncationStage K n ⟶ upperTruncationStage K (n + 1) :=
  letI : (upperTruncationStage K n).IsStrictlyLE ((n : ℤ) + 2) :=
    (upperTruncationStage K n).isStrictlyLE_of_le ((n : ℤ) + 1) ((n : ℤ) + 2) (by simp)
  inv ((upperTruncationStage K n).ιTruncLE ((n : ℤ) + 2)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE ((n : ℤ) + 1)) ((n : ℤ) + 2)

/-- The canonical inclusion of the `n`th stage of the upper truncation tower into `K^•`. -/
abbrev upperTruncationInclusion (K : CochainComplex A ℤ) (n : ℕ) :
    upperTruncationStage K n ⟶ K :=
  K.ιTruncLE ((n : ℤ) + 1)

-- Proof sketch: unfold `truncLEStep`; the inserted inverse cancels against the higher truncation
-- inclusion, and the remaining composite is the naturality square for `ιTruncLE`.
/-- The truncation transition map and the canonical inclusions into `K^•` form a commutative
square. -/
theorem truncLEStep_comp_ιTruncLE (K : CochainComplex A ℤ) (n : ℕ) :
    CommSq
      (upperTruncationInclusion K n)
      (truncLEStep K n)
      (𝟙 K)
      (upperTruncationInclusion K (n + 1)) := sorry

/-- The direct system `τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ ⋯` of upper truncations of `K^•`. -/
noncomputable abbrev upperTruncationDiagram (K : CochainComplex A ℤ) :
    ℕ ⥤ CochainComplex A ℤ :=
  Functor.ofSequence (truncLEStep K)

/-- A tower resolving the upper truncations `τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ ⋯` by bounded-above
cochain complexes with terms in an object property `P`. The index `0` corresponds to the textbook
complex `P_1^•`. -/
structure UpperTruncationResolutionTower
    (P : ObjectProperty A) (K : CochainComplex A ℤ) extends Over (upperTruncationDiagram K) where
  /-- Each stage is a bounded-above complex with terms in `P`, and the comparison to the
  corresponding truncation is termwise epimorphic and a quasi-isomorphism. -/
  isResolutionStage (n : ℕ) :
    IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P ((n : ℤ) + 1)
      (upperTruncationStage K n) (left.obj n) (hom.app n)
  /-- Each transition map `P_{n + 1}^• ⟶ P_{n + 2}^•` is termwise split monomorphic. -/
  termwiseSplitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((left.map (homOfLE (Nat.le_add_right n 1))).f i)
  /-- Each degreewise cokernel `P_{n + 2}^i / P_{n + 1}^i` again lies in `P`. -/
  cokernel_mem (n : ℕ) (i : ℤ) :
    P (cokernel ((left.map (homOfLE (Nat.le_add_right n 1))).f i))

namespace UpperTruncationResolutionTower

section

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- The underlying direct system `P_1^• ⟶ P_2^• ⟶ \cdots` of an upper truncation resolution
tower. -/
abbrev diagram
    (T : UpperTruncationResolutionTower P K) :
    ℕ ⥤ CochainComplex A ℤ :=
  T.left

/-- The natural comparison from a chosen upper truncation resolution tower to the canonical upper
truncation tower. -/
abbrev comparison
    (T : UpperTruncationResolutionTower P K) :
    T.diagram ⟶ upperTruncationDiagram K :=
  T.hom

/-- The `n`th stage `P_{n + 1}^•` of an upper truncation resolution tower. -/
abbrev stage
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CochainComplex A ℤ :=
  T.diagram.obj n

/-- The transition map `P_{n + 1}^• ⟶ P_{n + 2}^•` at stage `n` of the resolution tower. -/
abbrev step
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    T.stage n ⟶ T.stage (n + 1) :=
  T.diagram.map (homOfLE (Nat.le_add_right n 1))

/-- The stage map `P_{n + 1}^• ⟶ K^•` obtained by composing the comparison with the canonical
upper truncation inclusion. -/
abbrev toTarget
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    T.stage n ⟶ K :=
  T.comparison.app n ≫ upperTruncationInclusion K n

-- Proof sketch: this is the naturality square of `T.comparison` for the successor morphism
-- `n ⟶ n + 1`, rewritten using `upperTruncationDiagram`.
/-- The transition maps of an upper truncation resolution tower are compatible with the canonical
upper truncation tower. -/
theorem step_comp_comparison
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CommSq (T.comparison.app n) (T.step n) (truncLEStep K n) (T.comparison.app (n + 1)) := by
  refine CommSq.mk ?_
  simpa [UpperTruncationResolutionTower.step, upperTruncationDiagram] using
    (T.comparison.naturality (homOfLE (Nat.le_add_right n 1))).symm

-- Proof sketch: compose `step_comp_comparison` with `truncLEStep_comp_ιTruncLE`.
/-- The stage maps `P_{n + 1}^• ⟶ K^•` and the transition maps of the tower form commutative
squares. -/
theorem step_comp_toTarget
    (T : UpperTruncationResolutionTower P K) (n : ℕ) :
    CommSq
      (T.toTarget n)
      (T.step n)
      (𝟙 K)
      (T.toTarget (n + 1)) := by
  simpa [UpperTruncationResolutionTower.toTarget] using
    CommSq.horiz_comp
      (UpperTruncationResolutionTower.step_comp_comparison T n)
      (truncLEStep_comp_ιTruncLE K n)

/-- The canonical cocone from an upper truncation resolution tower to `K^•`. -/
noncomputable def cocone
    (T : UpperTruncationResolutionTower P K) :
    Cocone T.diagram where
  pt := K
  ι := NatTrans.ofSequence
    (fun n ↦ T.toTarget n)
    (fun n ↦ by
      simpa [UpperTruncationResolutionTower.step] using
        (UpperTruncationResolutionTower.step_comp_toTarget T n).w.symm)

/-- The canonical morphism from the sequential colimit of an upper truncation resolution tower to
`K^•`. -/
noncomputable abbrev fromColimit
    (T : UpperTruncationResolutionTower P K) [HasColimit T.diagram] :
    colimit T.diagram ⟶ K :=
  colimit.desc T.diagram T.cocone

-- Proof sketch: apply `colimit.ι_desc` to the canonical cocone `T.cocone`.
/-- Composing the `n`th colimit inclusion with the canonical map to `K^•` recovers the stagewise
comparison to the `n`th upper truncation followed by the truncation inclusion. -/
theorem ι_comp_fromColimit
    (T : UpperTruncationResolutionTower P K) [HasColimit T.diagram] (n : ℕ) :
    colimit.ι T.diagram n ≫ T.fromColimit = T.toTarget n := sorry

end

end UpperTruncationResolutionTower

-- Proof sketch: apply the bounded-above resolution lemma to each truncation `τ_{\le n} K^•`, and
-- then inductively compare consecutive stages inside the homotopy category. Lemma `13.10.7`
-- replaces the relevant distinguished triangle by a degreewise split short exact sequence, giving
-- termwise split transition maps with cokernels in `P`; a final two-term correction restores
-- surjectivity in the top degrees.
/-- Lemma 13.29.1: if `P` contains `0`, is closed under finite direct sums, and every object of an
abelian category is a quotient of an object of `P`, then every cochain complex `K^•` admits a
compatible tower `P_1^• ⟶ P_2^• ⟶ \cdots` over the upper truncation tower
`τ_{\le 1} K^• ⟶ τ_{\le 2} K^• ⟶ \cdots` such that each comparison
`P_{n + 1}^• ⟶ τ_{\le n + 1} K^•` is termwise epimorphic and a quasi-isomorphism, each
`P_{n + 1}^•` is bounded above with terms in `P`, each transition map is termwise split
monomorphic, and each degreewise cokernel again lies in `P`. -/
theorem exists_upperTruncationResolutionTower
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts]
    [P.HasEpiCover]
    (K : CochainComplex A ℤ) :
    Nonempty (UpperTruncationResolutionTower P K) := sorry

end

end CategoryTheory

/-! ### Proposition_13_29_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [PreservesFiniteColimits F]

local instance : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts F

local instance : F.Additive := Functor.additive_of_preservesBinaryBiproducts F

variable (P : ObjectProperty 𝒜)
  [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [HasEpiCover P]
  [HasColimitsOfShape ℕ 𝒜] [HasColimitsOfShape ℕ ℬ]
  [HasExactColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ ℬ]
  [PreservesColimitsOfShape ℕ F]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

/- Domain-style sampling for Proposition 13.29.2:
- primary domain: unbounded left derived functors of additive functors, built from bounded-above
  acyclic resolutions and exact sequential colimits;
- sampled owner declarations:
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`,
  `UpperTruncationResolutionTower`,
  `Functor.hasPointwiseLeftDerivedFunctor_of_subset`;
- best owner abstraction: the canonical owner is
  `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`; the total left derived functor is then the
  standard bridge/view consequence;
- primitive-vs-derived split:
  primitive data: `P`, the bounded-above acyclicity hypothesis `hFacyclic`, and the exact
    sequential-colimit assumptions on `𝒜`, `ℬ`, and `F`;
  derived API: pointwise left-derived existence for `KtoD`, and then the total left derived
    functor by the canonical instance.

Source/core/bridge triage:
- `source-facing`: the proposition that `LF` is defined on all of `D(\mathcal A)`;
- `core/canonical`: `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`;
- `bridge/view`: the corollary upgrading the pointwise owner to
  `Functor.HasLeftDerivedFunctor KtoD Qis`.
-/

-- Proof sketch: use Lemma `13.15.4` to resolve each bounded-above truncation by a bounded-above
-- complex of objects in `P`, and Lemma `13.29.1` to assemble these into a sequential system whose
-- colimit is quasi-isomorphic to the original complex. The hypothesis `hFacyclic` shows that the
-- bounded-above stages compute the bounded-above left derived functor, while exact sequential
-- colimits in `𝒜` and `ℬ` and preservation of those colimits by `F` upgrade this computation from
-- bounded-above complexes to arbitrary complexes. Then apply the pointwise-to-total criterion for
-- left derived functors.
/-- Under the hypotheses of Proposition 13.29.2, the unbounded functor
`K(\mathcal A) ⟶ D(\mathcal B)` has a pointwise left derived functor at every object. This is the
canonical owner-level formulation; the source-facing proposition below is its standard corollary.
-/
theorem hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasPointwiseLeftDerivedFunctor KtoD Qis := sorry

/-- Proposition 13.29.2: let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories, and let
`P` be an object property on `𝒜` containing `0`, closed under finite direct sums, and admitting
an objectwise epimorphic cover of every object. Assume every bounded-above acyclic cochain
complex with terms in `P` is sent by `F` to an acyclic complex, that `𝒜` and `ℬ` have exact
sequential colimits, and that `F` preserves sequential colimits. Then the left derived functor
`LF` is defined on all of `D(𝒜)`. -/
theorem hasLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasLeftDerivedFunctor KtoD Qis := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KtoD Qis :=
    hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
      F P hFacyclic
  infer_instance

end

end CategoryTheory

/-! ### Lemma_13_29_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/- 
Domain-style sampling for Lemma `13.29.3`.
- primary domain: sequential lower truncation towers of cochain complexes together with compatible
  bounded-below resolutions in an object property;
- sampled owner declarations:
  `SequentialInverseSystem`, `SequentialInverseSystem.transitionMap`, and
    `SequentialInverseSystem.stepMap` from
    `Definition_12_31_2`,
  `Under (lowerTruncationDiagram K)` for an inverse system equipped with a natural transformation
    from the canonical lower truncation tower,
  `Functor.ofOpSequence` / `NatTrans.ofOpSequence` for sequential inverse systems and cones,
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn` from `Lemma_13_15_5`,
  `UpperTruncationResolutionTower` from `Lemma_13_29_1` as the nearby dual owner pattern;
- best owner abstraction: the intrinsic inverse-system data is an object of
  `Under (lowerTruncationDiagram K)`, where `lowerTruncationDiagram K` is the chapter owner
  `SequentialInverseSystem (CochainComplex A ℤ)`;
- primitive-vs-derived split:
  primitive data: the under-object `S : Under (lowerTruncationDiagram K)` and the proof fields
    that each stage and each owner-level transition morphism satisfy the textbook conditions;
  derived API: the stage complex `S.stage n`, the stagewise map `S.fromSource n`, and the cone /
    limit comparison built from the under-object.

Source/core/bridge triage:
- `source-facing`: `LowerTruncationResolutionSystem` and the existence theorem below;
- `core/canonical`: `Under (lowerTruncationDiagram K)` and
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`;
- `bridge/view`: the accessors `diagram`, `comparison`, `stage`, `step`, `fromSource`, `cone`,
  and `intoLimit`.
-/

/-- The stage `τ_{\ge -(n + 1)} K^•` in the lower truncation tower of a cochain complex. The
index `0` corresponds to `τ_{\ge -1} K^•`. -/
abbrev lowerTruncationStage (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  K.truncGE (-(((n + 1 : ℕ)) : ℤ))

/-- The canonical transition map
`τ_{\ge -(n + 2)} K^• ⟶ τ_{\ge -(n + 1)} K^•` in the lower truncation tower. -/
noncomputable abbrev lowerTruncationStep (K : CochainComplex A ℤ) (n : ℕ) :
    lowerTruncationStage K (n + 1) ⟶ lowerTruncationStage K n :=
  let a : ℤ := -(((n + 2 : ℕ)) : ℤ)
  let b : ℤ := -(((n + 1 : ℕ)) : ℤ)
  let hab : a ≤ b :=
    neg_le_neg
      (show (((n + 1 : ℕ)) : ℤ) ≤ (((n + 2 : ℕ)) : ℤ) from
        Int.ofNat_le.mpr (Nat.le_succ (n + 1)))
  letI : (K.truncGE b).IsStrictlyGE a :=
    (K.truncGE b).isStrictlyGE_of_ge a b hab
  CochainComplex.truncGEMap (K.πTruncGE b) a ≫ inv ((K.truncGE b).πTruncGE a)

-- Proof sketch: unfold `lowerTruncationStep`; the inserted inverse identifies
-- `(K.truncGE (-(n + 1))).truncGE (-(n + 2))` with `K.truncGE (-(n + 2))`, and the remaining
-- composite is the naturality square for `πTruncGE`.
/-- The lower truncation transition map and the canonical maps from `K^•` to its truncation
stages form a commutative square. -/
theorem πTruncGE_comp_lowerTruncationStep (K : CochainComplex A ℤ) (n : ℕ) :
    CommSq
      (K.πTruncGE (-(((n + 2 : ℕ)) : ℤ)))
      (𝟙 K)
      (lowerTruncationStep K n)
      (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ))) := by
  refine CommSq.mk ?_
  sorry

/-- The inverse system `⋯ ⟶ τ_{\ge -2} K^• ⟶ τ_{\ge -1} K^•` of lower truncations of
`K^•`. -/
noncomputable abbrev lowerTruncationDiagram (K : CochainComplex A ℤ) :
    SequentialInverseSystem (CochainComplex A ℤ) :=
  Functor.ofOpSequence (lowerTruncationStep K)

@[simp] theorem lowerTruncationDiagram_step (K : CochainComplex A ℤ) (n : ℕ) :
    (lowerTruncationDiagram K).stepMap n = lowerTruncationStep K n := by
  simp [SequentialInverseSystem.stepMap, lowerTruncationDiagram]

/-- A lower truncation resolution system for `K^•` with terms in the object property `P`
consists of a diagram `⋯ ⟶ I_2^• ⟶ I_1^•` together with a natural transformation from the
canonical lower truncation diagram, such that each stage is a bounded-below termwise monomorphic
quasi-isomorphism with terms in `P`, each transition map is termwise split epic, and its
degreewise kernel again lies in `P`. -/
structure LowerTruncationResolutionSystem
    (P : ObjectProperty A) (K : CochainComplex A ℤ)
    extends Under (lowerTruncationDiagram K) where
  /-- Each stage is a bounded-below complex with terms in `P`, and the comparison from the
  corresponding truncation is termwise monomorphic and a quasi-isomorphism. -/
  isResolutionStage (n : ℕ) :
    IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P (-(((n + 1 : ℕ)) : ℤ))
      (lowerTruncationStage K n) (right.obj (op n))
      (hom.app (op n))
  /-- Each transition map `I_{n + 2}^• ⟶ I_{n + 1}^•` is termwise split epic. -/
  termwiseSplitEpi (n : ℕ) (i : ℤ) :
    IsSplitEpi ((right.stepMap n).f i)
  /-- The degreewise kernel of each transition map again satisfies `P`. -/
  kernel_mem (n : ℕ) (i : ℤ) :
    P (kernel ((right.stepMap n).f i))

namespace LowerTruncationResolutionSystem

section

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- The underlying inverse system `⋯ ⟶ I_2^• ⟶ I_1^•` of a lower truncation resolution system. -/
abbrev diagram
    (S : LowerTruncationResolutionSystem P K) :
    SequentialInverseSystem (CochainComplex A ℤ) :=
  S.right

/-- The natural comparison from the canonical lower truncation tower to a chosen lower truncation
resolution system. -/
abbrev comparison
    (S : LowerTruncationResolutionSystem P K) :
    lowerTruncationDiagram K ⟶ S.diagram :=
  S.hom

/-- The `n`th stage `I_{n + 1}^•` of a lower truncation resolution system. -/
abbrev stage
    (S : LowerTruncationResolutionSystem P K) (n : ℕ) :
    CochainComplex A ℤ :=
  S.diagram.obj (op n)

/-- The transition map `I_{n + 2}^• ⟶ I_{n + 1}^•` at stage `n` of the resolution system. -/
abbrev step
    (S : LowerTruncationResolutionSystem P K) (n : ℕ) :
    S.stage (n + 1) ⟶ S.stage n :=
  S.diagram.stepMap n

/-- The stage map `K^• ⟶ I_{n + 1}^•` obtained by composing the canonical lower truncation map
with the comparison to the chosen resolution system. -/
abbrev fromSource
    (S : LowerTruncationResolutionSystem P K) (n : ℕ) :
    K ⟶ S.stage n :=
  K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)) ≫ S.comparison.app (op n)

-- Proof sketch: this is the naturality square of `S.comparison` for the successor morphism
-- `op (n + 1) ⟶ op n`, rewritten using `lowerTruncationDiagram`.
/-- The transition maps of a lower truncation resolution system are compatible with the canonical
lower truncation tower. -/
theorem comparison_comp_step
    (S : LowerTruncationResolutionSystem P K) (n : ℕ) :
    CommSq
      (S.comparison.app (op (n + 1)))
      (lowerTruncationStep K n)
      (S.step n)
      (S.comparison.app (op n)) := by
  refine CommSq.mk ?_
  simpa [LowerTruncationResolutionSystem.step, SequentialInverseSystem.stepMap,
    lowerTruncationDiagram] using
    (S.comparison.naturality (homOfLE (Nat.le_add_right n 1)).op).symm

-- Proof sketch: combine `comparison_comp_step` with `πTruncGE_comp_lowerTruncationStep`.
/-- The stagewise maps from `K^•` to a lower truncation resolution system and the inverse-system
transition maps form commutative squares. -/
theorem fromSource_comp_step
    (S : LowerTruncationResolutionSystem P K) (n : ℕ) :
    CommSq
      (S.fromSource (n + 1))
      (𝟙 K)
      (S.step n)
      (S.fromSource n) := by
  have hcomparison :
      CommSq
        (S.comparison.app (op (n + 1)))
        (lowerTruncationStep K n)
        (S.step n)
        (S.comparison.app (op n)) := by
    simpa using S.comparison_comp_step n
  simpa [LowerTruncationResolutionSystem.fromSource, Category.assoc] using
    CommSq.horiz_comp
      (πTruncGE_comp_lowerTruncationStep K n)
      hcomparison

/-- The canonical cone from `K^•` to the inverse system underlying a lower truncation resolution
system. -/
noncomputable def cone
    (S : LowerTruncationResolutionSystem P K) :
    Cone S.diagram where
  pt := K
  π := NatTrans.ofOpSequence
    (fun n ↦ S.fromSource n)
    (fun n ↦ by
      simpa [LowerTruncationResolutionSystem.step] using (S.fromSource_comp_step n).w.symm)

/-- The canonical morphism from `K^•` to the inverse limit of a lower truncation resolution
system. -/
noncomputable abbrev intoLimit
    (S : LowerTruncationResolutionSystem P K) [HasLimit S.diagram] :
    K ⟶ limit S.diagram :=
  limit.lift S.diagram S.cone

-- Proof sketch: apply `limit.lift_π` to the canonical cone `S.cone`.
/-- Composing the canonical map into `lim I_n^•` with the `n`th limit projection recovers the
stage comparison map. -/
theorem intoLimit_comp_π
    (S : LowerTruncationResolutionSystem P K) [HasLimit S.diagram] (n : ℕ) :
    S.intoLimit ≫ limit.π S.diagram (Opposite.op n) = S.fromSource n := sorry

end

end LowerTruncationResolutionSystem

-- Proof sketch: this is the dual of Lemma `13.29.1`. Apply the bounded-below replacement lemma
-- to each lower truncation `τ_{\ge -(n + 1)} K^•`, then compare consecutive stages by forming the
-- pullback-style dual of the upper-truncation construction. Closure of `P` under finite products
-- keeps the new terms in `P`, and the resulting transition maps are termwise split epimorphisms
-- with kernels again in `P`.
/-- Lemma 13.29.3: let `\mathcal A` be an abelian category and let `P` be a class of objects
containing `0`, closed under finite products, and such that every object embeds into an object of
`P`. Then every cochain complex `K^•` admits a commutative inverse system
`⋯ ⟶ I_2^• ⟶ I_1^•` under the lower truncation tower
`⋯ ⟶ τ_{\ge -2} K^• ⟶ τ_{\ge -1} K^•` in which each comparison
`τ_{\ge -(n + 1)} K^• ⟶ I_{n + 1}^•` is termwise monomorphic and a quasi-isomorphism, each
`I_{n + 1}^•` is bounded below with terms in `P`, each transition map is termwise split
surjective, and each degreewise kernel again lies in `P`. -/
theorem exists_lowerTruncationResolutionSystem
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderFiniteProducts]
    [P.HasMonoEmbedding]
    (K : CochainComplex A ℤ) :
    Nonempty (LowerTruncationResolutionSystem P K) := sorry

end

end CategoryTheory
