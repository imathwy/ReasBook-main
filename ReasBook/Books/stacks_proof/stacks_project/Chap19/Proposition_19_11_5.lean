import Mathlib
import stacks_proof.stacks_project.Chap19.Definition_19_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite MorphismProperty

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{max u v} C]

open Ordinal.ToType

/- Domain-style sampling for 19.11.5:
- primary domain: cardinal-bounded presentability of objects in Grothendieck abelian categories,
  expressed by preservation of colimits of ordinal-indexed monomorphism diagrams under
  `coyoneda.obj (op M)`;
- sampled owner declarations:
  `is_alpha_small_wrt`,
  `HasCardinalLT (Subobject M) α.cof`,
  `hasCardinalLT_iff_cardinal_mk_lt`,
  `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`,
  `IsCardinalFiltered.isCardinalFiltered_preorder`;
- best owner abstraction: the core owner is
  `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`; the Stacks proposition is the
  source-facing ordinal-shape specialization of that owner to the chapter predicate
  `is_alpha_small_wrt`;
- primitive data: the object `M`, the ordinal `α`, and the canonical size owner
  `HasCardinalLT (Subobject M) α.cof`;
- derived API: the source-facing inequality `Cardinal.mk (Subobject M) < α.cof` and the resulting
  `α`-smallness statement with respect to monomorphisms.

Source/core/bridge triage:
- `source-facing`: `is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof`;
- `core/canonical`: `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`;
- `bridge/view`: `is_alpha_small_wrt_monomorphisms_of_hasCardinalLT_cof`, the
  `α.ToType`-indexed specialization of the core owner using the primitive `HasCardinalLT` input.
-/

-- Proof sketch: compare with Proposition 19.2.5. For a morphism `f : M ⟶ colim B` into an
-- `α`-indexed transfinite composition of monomorphisms, consider the inverse-image subobjects
-- `f ⁻¹(B_β) ≤ M`. Since there are at most `Cardinal.mk (Subobject M)` such subobjects and
-- `α.cof` is larger, the corresponding indices are bounded in `α`; AB5 then implies one inverse
-- image is all of `M`, so `f` factors through some stage, which is exactly `α`-smallness with
-- respect to monomorphisms.
/-- Companion bridge: if the canonical size owner `HasCardinalLT (Subobject M) α.cof` holds, then
`M` is `α`-small with respect to monomorphisms. -/
theorem is_alpha_small_wrt_monomorphisms_of_hasCardinalLT_cof
    (M : C) (α : Ordinal.{max u v}) (hM : HasCardinalLT (Subobject M) α.cof) :
    is_alpha_small_wrt M (monomorphisms C) α := by
  have hα : Cardinal.mk (Subobject M) < α.cof := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hM
  have hcof_gt_one : 1 < α.cof := by
    refine lt_of_le_of_lt ?_ hα
    rw [Cardinal.one_le_iff_ne_zero, Cardinal.mk_ne_zero_iff]
    exact ⟨⊤⟩
  have hsucc : Order.IsSuccLimit α := (Ordinal.one_lt_cof_iff).1 hcof_gt_one
  letI : Fact α.cof.IsRegular := ⟨Cardinal.isRegular_cof hsucc⟩
  letI : IsCardinalFiltered α.ToType α.cof :=
    isCardinalFiltered_preorder α.ToType α.cof fun K s hs ↦ by
      let j : α.ToType :=
        mk
          ⟨⨆ k, (s k : Ordinal),
            Ordinal.iSup_lt_of_lt_cof hs
              fun k ↦ (show (s k : Ordinal) < α from (s k).toOrd.2)⟩
      refine ⟨j, ?_⟩
      intro k
      have hle : (s k).toOrd ≤ j.toOrd := by
        exact
          show (s k : Ordinal) ≤ j.toOrd from by
            simpa [j] using Ordinal.le_iSup (fun k ↦ (s k : Ordinal)) k
      simpa [j] using mk.monotone hle
  intro B hB
  letI : ∀ (j j' : α.ToType) (f : j ⟶ j'), Mono (B.map f) := fun _ _ f ↦ hB f
  exact IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono B hM

/-- Proposition 19.11.5: in a Grothendieck abelian category, if the cofinality of `α` is strictly
larger than the size `|M| = Cardinal.mk (Subobject M)` of an object `M`, then `M` is `α`-small
with respect to injections, i.e. with respect to monomorphisms. -/
@[stacks 079F]
theorem is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof
    (M : C) (α : Ordinal.{max u v}) (hα : Cardinal.mk (Subobject M) < α.cof) :
    is_alpha_small_wrt M (monomorphisms C) α := by
  have hM : HasCardinalLT (Subobject M) α.cof := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hα
  exact is_alpha_small_wrt_monomorphisms_of_hasCardinalLT_cof M α hM

end

end CategoryTheory
