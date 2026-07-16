import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_19_2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open SimplexCategory.Truncated (incl inclCompInclusion)

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 14.19.10:
- primary domain: simplicial-object truncation/coskeleton adjunctions and coskeletality;
- sampled owner declarations:
  `truncation`,
  `Truncated.trunc`,
  `Functor.ranAdjunction`,
  `coskAdj`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`;
- best owner abstraction: `coskAdj n` for part (1), the generic right Kan extension adjunction
  `((SimplexCategory.Truncated.incl n m h).op.ranAdjunction C)` together with the owner-scoped
  source-facing bridge `SimplicialObject.Truncated.trunc.adj`, whose internal comparison is
  `((SimplexCategory.Truncated.incl n m h).op.ran) ≅ Truncated.cosk n ⋙ truncation m`
  for part (2), and the owner predicate `SimplicialObject.IsCoskeletal n` for the monotonicity
  statement behind parts (3) and (4);
- primitive data: the truncation functors, the inclusion `Δ≤n ↪ Δ≤m`, and the right Kan
  extensions defining the relevant coskeleta;
- derived API: the adjunctions for truncation and further truncation, plus the unit-isomorphism
  consequences phrased via `isCoskeletal_iff_isIso`.

Source/core/bridge triage:
- `source-facing`: the textbook adjunction for further truncation, whose right adjoint is the
  `m`-truncation of the `n`-coskeleton, together with the unit-isomorphism statements
  `U ⟶ cosk_n sk_n U` and their monotonicity in `n`;
- `core/canonical`: `coskAdj`, `Functor.ranAdjunction`, and `SimplicialObject.IsCoskeletal`;
- `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso`, which converts the owner predicate to
  the source-facing unit-isomorphism form, together with the finite-limit bridge supplying the
  right Kan extensions along `SimplexCategory.Truncated.incl`.

The file should therefore reuse `coskAdj` directly for part (1), expose the source-facing right
adjoint `Truncated.cosk n ⋙ truncation m` for part (2) through the owner-scoped bridge
`SimplicialObject.Truncated.trunc.adj`, and keep the unit-isomorphism lemmas as thin companions to
the owner-level coskeletality statements. -/

-- Proof sketch: finite limits give the pointwise right Kan extensions along
-- `(SimplexCategory.Truncated.inclusion n).op` needed to construct the right Kan extension functor,
-- and hence the right adjoint to `truncation n`.
section

variable (n : ℕ)
variable [HasFiniteLimits C]

recall coskAdj

/- Lemma 14.19.10 (1): if `C` has finite limits, then the `n`-truncation functor
`truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n` is a left adjoint, with right
adjoint given by the `n`-coskeleton functor. This is direct owner-level API from the adjunction
`coskAdj n : truncation n ⊣ Truncated.cosk n`. -/
#check (coskAdj n :
  (truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n) ⊣ Truncated.cosk n)

end

private noncomputable def truncInclStructuredArrowEquiv (n m : ℕ) (h : n ≤ m)
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    StructuredArrow Y (incl n m h).op ≌
      StructuredArrow ((SimplexCategory.Truncated.inclusion m).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op :=
  (StructuredArrow.post Y (incl n m h).op (SimplexCategory.Truncated.inclusion m).op).asEquivalence.trans
    (StructuredArrow.mapNatIso
      ((Functor.opComp (incl n m h) (SimplexCategory.Truncated.inclusion m)).symm ≪≫
        NatIso.op (inclCompInclusion h).symm))

/- Internal bridge: along `Δ≤n ↪ Δ≤m`, the right Kan extensions needed for the generic
`ranAdjunction` are pointwise because the corresponding structured-arrow indexing category is
canonically equivalent to the one already handled by Lemma `14.19.2` for `Δ≤n ↪ Δ`. This supports
only the source-facing adjunction `SimplicialObject.Truncated.trunc.adj`. -/
private instance truncIncl_hasPointwiseRightKanExtension (n m : ℕ) (h : n ≤ m)
    [HasFiniteLimits C] (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (incl n m h).op.HasPointwiseRightKanExtension F := by
  intro Y
  let e := truncInclStructuredArrowEquiv n m h Y
  change HasLimit
    (e.functor ⋙
      StructuredArrow.proj ((SimplexCategory.Truncated.inclusion m).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op ⋙ F)
  infer_instance

section Coskeleton

variable {n m : ℕ}

namespace SimplicialObject.Truncated

section

variable [HasFiniteLimits C]

/-- Helper for Lemma 14.19.10: after passing to opposites, the inclusion
`Δ≤n ↪ Δ≤m ↪ Δ` identifies with the standard inclusion `Δ≤n ↪ Δ`. -/
private noncomputable def inclCompInclusionOpIso {n m : ℕ} (h : n ≤ m) :
    (SimplexCategory.Truncated.incl n m h).op ⋙
      (SimplexCategory.Truncated.inclusion m).op ≅
    (SimplexCategory.Truncated.inclusion n).op :=
  Functor.opComp (SimplexCategory.Truncated.incl n m h)
      (SimplexCategory.Truncated.inclusion m) ≪≫
    NatIso.op (inclCompInclusion h)

/-- Helper for Lemma 14.19.10: the counit of `truncation n ⊣ Truncated.cosk n` should be an
isomorphism on every `n`-truncated simplicial object, using only fully faithfulness of
`(SimplexCategory.Truncated.inclusion n).op` and the universal property of the right Kan
extension. -/
private theorem cosk_counit_app_isIso (U : SimplicialObject.Truncated C n) :
    IsIso ((coskAdj n).counit.app U) := by
  -- Finite limits supply the pointwise right Kan extensions behind `Truncated.cosk`,
  -- so the generic counit of `coskAdj n` is already an isomorphism.
  infer_instance

omit [HasFiniteLimits C] in
/-- Helper for Lemma 14.19.10: coskeletality is preserved under isomorphism. -/
private theorem isCoskeletal_of_iso_aux {k : ℕ} {X Y : SimplicialObject C} (e : X ≅ Y)
    (hX : X.IsCoskeletal k) :
    Y.IsCoskeletal k := by
  -- Rewrite both sides as right Kan extension statements and transport along the object isomorphism.
  rw [SimplicialObject.isCoskeletal_iff] at hX ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (𝟙 ((SimplexCategory.Truncated.inclusion k).op ⋙ X))
    (𝟙 ((SimplexCategory.Truncated.inclusion k).op ⋙ Y))
    (Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion k).op e) e
    (by simp [Functor.isoWhiskerLeft_hom])).1 hX

/-- The canonical `n`-coskeleton of an `n`-truncated simplicial object is canonically
`n`-coskeletal. This is the owner-level instance form of the fact that the unit of
`truncation n ⊣ Truncated.cosk n` is an isomorphism on the image of `Truncated.cosk n`. -/
instance instIsCoskeletalCosk (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n).obj U).IsCoskeletal n := by
  -- Transport the canonical counit-based right Kan extension of `coskₙ U`
  -- across the counit isomorphism so that the comparison map becomes the identity.
  letI : IsIso ((coskAdj n).counit.app U) := cosk_counit_app_isIso U
  rw [SimplicialObject.isCoskeletal_iff]
  let e :
      U ≅ (truncation n).obj ((Truncated.cosk n).obj U) :=
    (asIso ((coskAdj n).counit.app U)).symm
  let α :
      (SimplexCategory.Truncated.inclusion n).op ⋙ (Truncated.cosk n).obj U ⟶ U :=
    (coskAdj n).counit.app U
  let α' :
      (SimplexCategory.Truncated.inclusion n).op ⋙ (Truncated.cosk n).obj U ⟶
        (truncation n).obj ((Truncated.cosk n).obj U) :=
    𝟙 _
  -- The counit is already universal, and the target isomorphism turns it into the identity map.
  exact
    (Functor.isRightKanExtension_iff_of_iso₂ α α' e (Iso.refl _)
      (by
        ext i
        have hi :
            𝟙 (((Truncated.cosk n).obj U).obj (op (unop i).obj)) =
              ((coskAdj n).counit.app U).app i ≫ e.hom.app i := by
          rw [show e.hom.app i = (asIso ((coskAdj n).counit.app U)).inv.app i by rfl]
          exact ((asIso ((coskAdj n).counit.app U)).hom_inv_id_app i).symm
        simpa [α, α'] using hi))
      |>.1 (by
        -- Unfold the `Truncated.cosk` and `coskAdj` abbreviations to recover the generic
        -- `ranCounit` right-Kan-extension instance.
        change (((SimplexCategory.Truncated.inclusion n).op.ran).obj U).IsRightKanExtension
          (((SimplexCategory.Truncated.inclusion n).op.ranAdjunction C).counit.app U)
        rw [Functor.ranAdjunction_counit]
        infer_instance)

end

section

variable [HasFiniteLimits C]

/-- Helper for Lemma 14.19.10: the generic right Kan extension along `Δ≤n ↪ Δ≤m` exists as soon
as the standard inclusion `Δ≤n ↪ Δ` admits right Kan extensions for all diagrams. -/
private instance incl_hasRightKanExtension_of_inclusion (h : n ≤ m)
    (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.incl n m h).op.HasRightKanExtension F := by
  -- Finite limits give pointwise right Kan extensions along `Δ≤n ↪ Δ≤m`,
  -- and the chosen right Kan extension follows from that pointwise construction.
  infer_instance

/-- Helper for Lemma 14.19.10: composing the right Kan extension along `Δ≤n ↪ Δ≤m` with the
`m`-coskeleton recovers the `n`-coskeleton. This is the right-adjoint-uniqueness comparison
needed for monotonicity of coskeletality. -/
private noncomputable def ran_comp_cosk_iso_of_le (h : n ≤ m) :
    (((SimplexCategory.Truncated.incl n m h).op.ran :
        SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C m) ⋙
      Truncated.cosk m) ≅
    Truncated.cosk n := by
  -- The composed left adjoint is still `truncation n`, so uniqueness of right adjoints identifies
  -- the two candidate right adjoints.
  let adj :=
    ((coskAdj m).comp ((SimplexCategory.Truncated.incl n m h).op.ranAdjunction C)).ofNatIsoLeft
      (truncationCompTrunc h)
  exact Adjunction.rightAdjointUniq adj (coskAdj n)

-- Proof sketch: the canonical `n`-coskeleton is `n`-coskeletal by the previous instance, and the
-- ambient monotonicity theorem upgrades `n`-coskeletality to `m`-coskeletality when `n ≤ m`.
/-- Lemma 14.19.10 (3): if `n ≤ m`, then for every `n`-truncated simplicial object `U`, its
canonical `n`-coskeleton is also `m`-coskeletal. This is the owner-level form of the identity
`cosk_m sk_m cosk_n U = cosk_n U`. -/
theorem isCoskeletal_of_le (h : n ≤ m) (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n).obj U).IsCoskeletal m := by
  -- Route correction: instead of identifying `truncation m (coskₙ U)` directly, compare right
  -- adjoints to `truncation n` and transport `m`-coskeletality across the resulting component.
  exact isCoskeletal_of_iso_aux
    ((ran_comp_cosk_iso_of_le h).app U)
    (instIsCoskeletalCosk (((SimplexCategory.Truncated.incl n m h).op.ran).obj U))

/-- Companion to Lemma 14.19.10 (3): the canonical unit map exhibiting
`(Truncated.cosk n).obj U` as recovered from its `m`-truncation is an isomorphism. -/
theorem cosk_unit_app_isIso_of_le (h : n ≤ m) (U : SimplicialObject.Truncated C n) :
    IsIso ((coskAdj m).unit.app ((Truncated.cosk n).obj U)) := by
  rw [← SimplicialObject.isCoskeletal_iff_isIso]
  exact isCoskeletal_of_le h U

end

end SimplicialObject.Truncated

namespace SimplicialObject

/-- Coskeletality is invariant under isomorphism. -/
theorem isCoskeletal_of_iso {X Y : SimplicialObject C} (e : X ≅ Y) (hX : X.IsCoskeletal n) :
    Y.IsCoskeletal n := by
  rw [isCoskeletal_iff] at hX ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ Y))
    (Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion n).op e) e
    (by simp [Functor.isoWhiskerLeft_hom])).1 hX

section

variable [HasFiniteLimits C]

-- Proof sketch: identify `U` with its canonical `n`-coskeleton, apply the previous truncated
-- owner-level statement there, and transport the resulting `m`-coskeletality back across the
-- canonical isomorphism.
/-- Lemma 14.19.10 (4): if `U` is `n`-coskeletal and `n ≤ m`, then `U` is also `m`-coskeletal. -/
theorem isCoskeletal_of_le {U : SimplicialObject C} (h : n ≤ m) (hU : U.IsCoskeletal n) :
    U.IsCoskeletal m := by
  letI : U.IsCoskeletal n := hU
  have hcosk : ((cosk n).obj U).IsCoskeletal m := by
    change ((Truncated.cosk n).obj ((truncation n).obj U)).IsCoskeletal m
    exact SimplicialObject.Truncated.isCoskeletal_of_le h ((truncation n).obj U)
  have e : U ≅ (cosk n).obj U := U.isoCoskOfIsCoskeletal n
  exact isCoskeletal_of_iso e.symm hcosk

/-- Companion to Lemma 14.19.10 (4): if `U ⟶ cosk_n sk_n U` is an isomorphism and `n ≤ m`, then
`U ⟶ cosk_m sk_m U` is also an isomorphism. -/
theorem cosk_unit_app_isIso_of_le {U : SimplicialObject C} (h : n ≤ m)
    (hn : IsIso ((coskAdj n).unit.app U)) :
    IsIso ((coskAdj m).unit.app U) := by
  rw [← isCoskeletal_iff_isIso]
  exact isCoskeletal_of_le h ((isCoskeletal_iff_isIso U n).2 hn)

end

end SimplicialObject

end Coskeleton

namespace SimplicialObject.Truncated

section FurtherTruncationBridge

variable [HasFiniteLimits C]

namespace trunc

/- Internal bridge: compare the right adjoint to further truncation after composing with the
fully faithful right adjoint `Truncated.cosk m`. This uses only canonical owner-level adjunction
operations: compose the generic `ranAdjunction` with `coskAdj m`, transport the left adjoint via
`truncationCompTrunc h`, and identify the resulting right adjoint with `Truncated.cosk n` by
uniqueness of right adjoints. -/
private noncomputable def truncAdjCompIso (n m : ℕ) (h : n ≤ m) :
    ((incl n m h).op.ran) ⋙ (Truncated.cosk m : SimplicialObject.Truncated C m ⥤
      SimplicialObject C) ≅
      Truncated.cosk n := by
  let adj :=
    ((coskAdj m).comp ((incl n m h).op.ranAdjunction C)).ofNatIsoLeft
      (truncationCompTrunc h)
  exact Adjunction.rightAdjointUniq adj (coskAdj n)

private noncomputable def coskTruncCompIso (n m : ℕ) (h : n ≤ m) :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m) ⋙
      (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) ≅
    Truncated.cosk n := by
  let unitIso :
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ≅
        ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
          truncation m) ⋙
            (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) :=
    NatIso.ofComponents
      (fun U ↦ by
        let f := (coskAdj m).unit.app ((Truncated.cosk n).obj U)
        let hf := SimplicialObject.Truncated.cosk_unit_app_isIso_of_le h U
        let g := Classical.choose hf.out
        exact ⟨f, g, (Classical.choose_spec hf.out).left, (Classical.choose_spec hf.out).right⟩)
      (fun f ↦ by
        simpa using (coskAdj m).unit.naturality ((Truncated.cosk n).map f))
  exact unitIso.symm

/- Internal comparison used to transport the generic `ranAdjunction` to the source-facing
right adjoint of Lemma 14.19.10 (2). After composing both candidate right adjoints with the
fully faithful functor `Truncated.cosk m`, they identify canonically, so we cancel on the right. -/
private noncomputable def truncAdjRightIso (n m : ℕ) (h : n ≤ m) :
    ((incl n m h).op.ran) ≅
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m := by
  let compIso :
      ((incl n m h).op.ran) ⋙
          (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) ≅
        ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
            truncation m) ⋙
          (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) :=
    truncAdjCompIso n m h ≪≫
      (coskTruncCompIso n m h).symm
  exact Functor.fullyFaithfulCancelRight (Truncated.cosk m) compIso

/-- Lemma 14.19.10 (2): the further truncation functor has right adjoint given by the
`m`-truncation of the `n`-coskeleton. This is obtained by transporting the generic right Kan
extension adjunction along an internal comparison with `Truncated.cosk n ⋙ truncation m`. -/
noncomputable def adj (n m : ℕ) (h : n ≤ m) :
    Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m :=
  ((incl n m h).op.ranAdjunction C).ofNatIsoRight (truncAdjRightIso n m h)

end trunc

end FurtherTruncationBridge

end SimplicialObject.Truncated

variable {m : ℕ} (h : n ≤ m)

/- Lemma 14.19.10 (2): if `C` has finite limits and `n ≤ m`, then the further truncation functor
`Truncated.trunc C m n h` is left adjoint to the `m`-truncation of the `n`-coskeleton. The file
keeps the generic right Kan extension owner only as internal support for this adjunction. -/
section

variable [HasFiniteLimits C]

#check (Truncated.trunc.adj n m h :
  Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m)

end

end CategoryTheory
