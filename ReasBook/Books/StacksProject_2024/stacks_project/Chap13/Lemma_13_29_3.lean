import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap13.Lemma_13_29_1

-- Declarations for this item will be appended below by the statement pipeline.

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
  -- Proof comment: unfold the transition map and rewrite the first composite by truncation
  -- naturality for `K ⟶ τ_{\ge -(n + 1)} K`; the remaining inverse then cancels.
  dsimp [lowerTruncationStep]
  letI :
      IsIso ((K.truncGE (-(((n + 1 : ℕ)) : ℤ))).πTruncGE (-(((n + 2 : ℕ)) : ℤ))) :=
    by
      letI :
          (K.truncGE (-(((n + 1 : ℕ)) : ℤ))).IsStrictlyGE (-(((n + 2 : ℕ)) : ℤ)) :=
        (K.truncGE (-(((n + 1 : ℕ)) : ℤ))).isStrictlyGE_of_ge
          (-(((n + 2 : ℕ)) : ℤ))
          (-(((n + 1 : ℕ)) : ℤ))
          (neg_le_neg (show (((n + 1 : ℕ)) : ℤ) ≤ (((n + 2 : ℕ)) : ℤ) from
            Int.ofNat_le.mpr (Nat.le_succ (n + 1))))
      infer_instance
  rw [Category.id_comp]
  calc
    K.πTruncGE (-(((n + 2 : ℕ)) : ℤ)) ≫
        truncGEMap (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ))) (-(((n + 2 : ℕ)) : ℤ)) ≫
          inv ((K.truncGE (-(((n + 1 : ℕ)) : ℤ))).πTruncGE (-(((n + 2 : ℕ)) : ℤ))) =
      (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)) ≫
        (K.truncGE (-(((n + 1 : ℕ)) : ℤ))).πTruncGE (-(((n + 2 : ℕ)) : ℤ))) ≫
          inv ((K.truncGE (-(((n + 1 : ℕ)) : ℤ))).πTruncGE (-(((n + 2 : ℕ)) : ℤ))) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦
              t ≫ inv ((K.truncGE (-(((n + 1 : ℕ)) : ℤ))).πTruncGE (-(((n + 2 : ℕ)) : ℤ))))
            (πTruncGE_naturality
              (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)))
              (-(((n + 2 : ℕ)) : ℤ)))
    _ = K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)) := by
      simp [Category.assoc]

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
    S.intoLimit ≫ limit.π S.diagram (Opposite.op n) = S.fromSource n := by
  -- Proof comment: this is the universal-property identity for the limit lift from `S.cone`.
  rw [LowerTruncationResolutionSystem.intoLimit, LowerTruncationResolutionSystem.fromSource]
  exact limit.lift_π (F := S.diagram) (c := S.cone) (j := Opposite.op n)

end

end LowerTruncationResolutionSystem

/-- Helper for Lemma 13.29.3: finite products in `P` become finite coproducts in the opposite
category. -/
instance oppositeProperty_isClosedUnderFiniteCoproducts
    (P : ObjectProperty A) [P.IsClosedUnderFiniteProducts] :
    (oppositeProperty P).IsClosedUnderFiniteCoproducts := by
  refine ⟨fun J _ ↦ ?_⟩
  let _ : P.IsClosedUnderLimitsOfShape (Discrete J)ᵒᵖ :=
    IsClosedUnderLimitsOfShape.of_equivalence (P := P) (Discrete.opposite J).symm
  infer_instance

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
    Nonempty (LowerTruncationResolutionSystem P K) := by
  -- Route correction: the source proof is the formal dual of `exists_upperTruncationResolutionTower`
  -- in the opposite abelian category, not a fresh direct recursive construction.
  -- TODO: after the upstream Lake state for `stacks_project/Chap13/Lemma_13_15_4.lean` is repaired,
  -- apply `exists_upperTruncationResolutionTower` to
  -- `(CochainComplex.opEquivalence A).functor.obj (Opposite.op K)` and `oppositeProperty P`, then
  -- transport the resulting upper-truncation tower back to a
  -- `LowerTruncationResolutionSystem P K` stagewise using the opposite-category API.
  sorry

end

end CategoryTheory
