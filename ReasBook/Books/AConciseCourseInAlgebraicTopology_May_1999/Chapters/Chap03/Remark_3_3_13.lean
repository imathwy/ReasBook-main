import Mathlib.GroupTheory.QuotientGroup.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Membership in `p(π(E, e))` is equivalent to fixing the distinguished point `⟨e, rfl⟩` under
direct fiber translation. -/
theorem mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq
    (hp : Functor.IsCovering p) (e : E) (γ : p.obj e ⟶ p.obj e) :
    γ ∈ (Functor.mapVertexGroup p e).range ↔
      fiberTranslationMap hp γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro hγ
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hstab
    calc
      fiberTranslationMap hp γ x₀ = fiberTranslationMap hp γ (fiberTranslationMap hp γ⁻¹ x₀) := by
        rw [hstab]
      _ = x₀ := by
        simpa using
          (FunctorToTypes.map_hom_map_inv_apply (fiberTranslationFunctor hp) (asIso γ) x₀)
  · intro hγ
    have hinv : fiberTranslationMap hp γ⁻¹ x₀ = x₀ := by
      calc
        fiberTranslationMap hp γ⁻¹ x₀ =
            fiberTranslationMap hp γ⁻¹ (fiberTranslationMap hp γ x₀) := by
          rw [hγ]
        _ = x₀ := by
          simpa using
            (FunctorToTypes.map_inv_map_hom_apply (fiberTranslationFunctor hp) (asIso γ) x₀)
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      change fiberTranslationMap hp γ⁻¹ x₀ = x₀
      exact hinv
    rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e] at hstab

/-- Helper for Remark 3.3.13: the direct endpoint map on the fiber is visibly compatible with the
right-coset relation attached to `p(π(E,e))`. -/
private theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel
    (hp : Functor.IsCovering p) (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  -- First note that the subgroup element appended on the left fixes the base fiber point.
  have hfix : fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀ = x₀ := by
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e
      (γ₂ * γ₁⁻¹)).mp hγ
  -- Then rewrite `γ₂` as `(γ₂ * γ₁⁻¹) * γ₁` and collapse the fixed-point factor.
  calc
    fiberTranslationMap hp γ₁ x₀ =
        fiberTranslationMap hp γ₁ (fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀) := by
      rw [hfix]
    _ = fiberTranslationMap hp ((γ₂ * γ₁⁻¹) * γ₁) x₀ := by
      symm
      simpa [mul_assoc] using
        congrArg (fun m ↦ m x₀)
          (fiberTranslationMap_comp hp (γ₂ * γ₁⁻¹) γ₁)
    _ = fiberTranslationMap hp γ₂ x₀ := by
      simp

/-- If two loops differ on the right by an element of `p(π(E, e))`, then they determine the same
endpoint in the distinguished fiber over `p.obj e`. -/
-- Proof sketch: this is exactly the right-coset compatibility already verified for direct fiber
-- translation at the chosen basepoint.
theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range (hp : Functor.IsCovering p)
    (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  -- Route correction: the public helper now records the right-coset compatibility that matches
  -- the direct endpoint geometry, instead of the false left-coset variant.
  exact fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel hp e γ₁ γ₂ hγ

/-- The canonical map from `π(B, p.obj e) / p(π(E, e))` to the fiber over `p.obj e`. -/
noncomputable def quotientMapVertexGroupRangeToFiber (hp : Functor.IsCovering p) (e : E) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range → p.Fiber (p.obj e) :=
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  (MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀) ∘
    Subgroup.quotientEquivOfEq
      (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm

/-- Helper for Remark 3.3.13: on a representative, the quotient-to-fiber map acts by inverse-loop
fiber translation from the distinguished basepoint. -/
@[simp] theorem quotientMapVertexGroupRangeToFiber_mk (hp : Functor.IsCovering p) (e : E)
    (γ : p.obj e ⟶ p.obj e) :
    quotientMapVertexGroupRangeToFiber hp e (QuotientGroup.mk γ) =
      fiberTranslationMap hp γ⁻¹ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  -- Unfold the stabilizer identification and evaluate both quotient maps on the representative.
  change
    MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀
        (Subgroup.quotientEquivOfEq
          (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm
          (QuotientGroup.mk γ)) =
      fiberTranslationMap hp γ⁻¹ x₀
  rw [Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk]
  rfl

/-- A subgroup of the source-facing loop group `b ⟶ b` viewed inside the reversed endomorphism
group `End b`. -/
def loopSubgroupToEndSubgroup {b : B} (K : Subgroup (b ⟶ b)) : Subgroup (CategoryTheory.End b) where
  carrier := K.carrier
  one_mem' := by
    simpa using K.one_mem
  mul_mem' ha hb := by
    simpa [CategoryTheory.End.mul_def] using K.mul_mem hb ha
  inv_mem' ha := by
    change ((show b ⟶ b from _ )⁻¹) ∈ K
    exact K.inv_mem ha

@[simp] theorem mem_loopSubgroupToEndSubgroup {b : B} {K : Subgroup (b ⟶ b)}
    (γ : CategoryTheory.End b) :
    γ ∈ loopSubgroupToEndSubgroup K ↔ (γ : b ⟶ b) ∈ K := Iff.rfl

/-- The carrier-preserving passage from loop-group subgroups to `End`-subgroups is injective. -/
theorem loopSubgroupToEndSubgroup_injective {b : B} :
    Function.Injective
      (loopSubgroupToEndSubgroup : Subgroup (b ⟶ b) → Subgroup (CategoryTheory.End b)) := by
  intro K L hKL
  ext γ
  exact Iff.of_eq (congrArg (fun H : Subgroup (CategoryTheory.End b) ↦ γ ∈ H) hKL)

/-- The fiber over `b` carries the direct `End b`-action induced by fiber translation. -/
noncomputable instance instFiberTranslationEndMulAction [hp : Functor.IsCovering p] (b : B) :
    MulAction (CategoryTheory.End b) { a : E // p.obj a = b } := by
  change MulAction (CategoryTheory.End b) (p.Fiber b)
  exact Functor.vertexGroupMulAction (fiberTranslationFunctor hp) b

/-- Helper for Remark 3.3.13: for the direct `End`-action on the fiber over `p.obj e`, the
stabilizer of the distinguished point is exactly `p(π(E,e))`. -/
theorem vertexGroupMulAction_basepoint_stabilizer_eq_mapVertexGroup_range
    [hp : Functor.IsCovering p] (e : E) :
    MulAction.stabilizer (CategoryTheory.End (p.obj e)) (⟨e, rfl⟩ : p.Fiber (p.obj e)) =
      loopSubgroupToEndSubgroup (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  ext γ
  constructor
  · intro hγ
    -- Rewrite stabilizer membership as a fixed-point statement for direct fiber translation.
    change fiberTranslationMap hp γ x₀ = x₀ at hγ
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mpr hγ
  · intro hγ
    -- The explicit `End`-subgroup has the same carrier as the image subgroup in the loop group.
    change fiberTranslationMap hp γ x₀ = x₀
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mp hγ

/-- Remark 3.3.13: if the fiber-translation action of `π(B, p.obj e)` on the fiber over `p.obj e`
is pretransitive, then the canonical map from `π(B, p.obj e) / p(π(E, e))` to that fiber is
bijective. -/
-- Proof sketch: identify `p(π(E, e))` with the stabilizer of the distinguished fiber point
-- `⟨e, rfl⟩`, then apply the quotient-stabilizer equivalence for the pretransitive
-- fiber-translation action.
theorem quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    Function.Bijective (quotientMapVertexGroupRangeToFiber hp e) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := htrans
  -- Route correction: work on Lean's actual left quotient by first identifying the subgroup with
  -- the stabilizer of `x₀`, then apply the standard orbit-stabilizer bijection.
  exact
    (ofQuotientStabilizer_bijective_of_isPretransitive x₀).comp
      (Subgroup.quotientEquivOfEq
        (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm).bijective

noncomputable def quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (quotientMapVertexGroupRangeToFiber hp e)
    (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp e htrans)

@[simp] theorem quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive_apply
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e))
    (q : (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :
    quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive hp e htrans q =
      quotientMapVertexGroupRangeToFiber hp e q := rfl

/-- The underlying orbit map of the regular `π(B, p.obj e)`-set equivalence is bijective. -/
-- Proof sketch: specialize the quotient-stabilizer description to the trivial subgroup
-- `p(π(E, e)) = ⊥`, and identify `π(B, p.obj e) / ⊥` with `π(B, p.obj e)`.
theorem vertexGroupToFiber_bijectiveOfIsUniversalCovering (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    Function.Bijective
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let quotientToFiber :
      (p.obj e ⟶ p.obj e) ⧸ (⊥ : Subgroup (p.obj e ⟶ p.obj e)) → p.Fiber (p.obj e) :=
    quotientMapVertexGroupRangeToFiber hp.isCovering e ∘
      Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm
  have hquotientToFiber : Function.Bijective quotientToFiber := by
    -- First identify the quotient by `p(π(E,e))` with the quotient by `⊥`.
    exact
      (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp.isCovering e htrans).comp
        (Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm).bijective
  let inverseVertexToFiber : (p.obj e ⟶ p.obj e) → p.Fiber (p.obj e) :=
    quotientToFiber ∘ quotientBot.symm
  have hinverseVertexToFiber : Function.Bijective inverseVertexToFiber := by
    -- Then use the canonical identification `π(B,p.obj e) / ⊥ ≃ π(B,p.obj e)`.
    exact hquotientToFiber.comp quotientBot.symm.bijective
  have hinverseVertexToFiber_eq :
      inverseVertexToFiber =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) := by
    funext γ
    -- On representatives, the quotient map uses the inverse-loop action from `x₀`.
    change quotientMapVertexGroupRangeToFiber hp.isCovering e
        ((Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm)
          (quotientBot.symm γ)) =
      fiberTranslationMap hp.isCovering γ⁻¹ x₀
    rw [quotientBot_symm_apply, Subgroup.quotientEquivOfEq_mk]
    exact quotientMapVertexGroupRangeToFiber_mk hp.isCovering e γ
  rw [hinverseVertexToFiber_eq] at hinverseVertexToFiber
  have hdirect_eq :
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ x₀) =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) ∘ fun γ : p.obj e ⟶ p.obj e ↦ γ⁻¹ := by
    funext γ
    -- Precomposing the inverse-representative orbit map with inversion recovers the textbook map.
    change fiberTranslationMap hp.isCovering γ x₀ =
      fiberTranslationMap hp.isCovering ((γ⁻¹)⁻¹) x₀
    simp
  have hinv : Function.Bijective (fun γ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv γ) := by
    constructor
    · intro γ₁ γ₂ hγ
      simpa using congrArg (fun δ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv δ) hγ
    · intro γ
      refine ⟨CategoryTheory.inv γ, ?_⟩
      simp
  -- Compose the inverse-representative bijection with inversion on the vertex group.
  simpa [x₀, hdirect_eq] using
    hinverseVertexToFiber.comp hinv

/-- For a universal covering with pretransitive fiber translation, the fiber over `p.obj e` is
canonically equivalent to the regular `π(B, p.obj e)`-set. -/
noncomputable def vertexGroupToFiberEquivOfIsUniversalCovering
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    (p.obj e ⟶ p.obj e) ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (fun γ : p.obj e ⟶ p.obj e ↦ fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩)
    (vertexGroupToFiber_bijectiveOfIsUniversalCovering hp htrans)

@[simp] theorem vertexGroupToFiberEquivOfIsUniversalCovering_apply
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e))
    (γ : p.obj e ⟶ p.obj e) :
    vertexGroupToFiberEquivOfIsUniversalCovering hp htrans γ =
      fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩ := rfl

end CategoryTheory.Functor.IsCovering
