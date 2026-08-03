module

public import Topology_Munkres_2000.Book.Lemma_81_1
public import Topology_Munkres_2000.Book.Notation_52_1.RightCosets
public import Mathlib.GroupTheory.QuotientGroup.Basic
import all Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence
import all Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v

open scoped CoveringTransformation

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [hE : PathConnectedSpace E] [hB : PathConnectedSpace B]
variable [hlE : LocallyPathConnectedSpace E] [hlB : LocallyPathConnectedSpace B]
variable {p : E → B}

/-- The normalizer of the covering subgroup inside the fundamental group. -/
noncomputable abbrev normalizerSubgroup (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) : Subgroup (FundamentalGroup B b₀) :=
  Subgroup.normalizer
    (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀))

/-- The quotient of the normalizer of the covering subgroup by that subgroup. -/
abbrev normalizerQuotient (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) :=
  let H₀ := hp.fundamentalGroupMapRange he₀
  normalizerSubgroup hp he₀ ⧸ H₀.subgroupOf (normalizerSubgroup hp he₀)

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: the left-coset relation inside the normalizer is the
ambient right-coset relation on normalizer elements. -/
theorem normalizerLeftRel_iff_rightRel (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) {a b : normalizerSubgroup hp he₀} :
    QuotientGroup.leftRel
        ((hp.fundamentalGroupMapRange he₀).subgroupOf
          (normalizerSubgroup hp he₀)) a b ↔
      QuotientGroup.rightRel (hp.fundamentalGroupMapRange he₀)
        (a : FundamentalGroup B b₀) (b : FundamentalGroup B b₀) := by
  -- Normality permits commuting the two factors in the subgroup-membership test.
  rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply]
  exact Subgroup.Normal.mem_comm_iff inferInstance

/-- The canonical map from the normalizer quotient to right cosets of the covering subgroup. -/
noncomputable def normalizerQuotientRightCoset (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) : normalizerQuotient hp he₀ →
      FundamentalGroup B b₀ ⧸ᵣ hp.fundamentalGroupMapRange he₀ :=
  Quotient.map' (fun x : normalizerSubgroup hp he₀ ↦ (x : FundamentalGroup B b₀))
    (fun _ _ hab ↦ (normalizerLeftRel_iff_rightRel hp he₀).mp hab)

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: the canonical normalizer-quotient map keeps the same
representative in the ambient right-coset space. -/
theorem normalizerQuotientRightCoset_mk (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) (n : normalizerSubgroup hp he₀) :
    normalizerQuotientRightCoset hp he₀ (QuotientGroup.mk n) =
      Quotient.mk'' (n : FundamentalGroup B b₀) := by
  -- Evaluate the quotient lift on its chosen representative.
  rfl

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: the canonical normalizer-quotient map has exactly the
right cosets represented by elements of the normalizer as its range. -/
theorem range_normalizerQuotientRightCoset (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) :
    Set.range (normalizerQuotientRightCoset hp he₀) =
      Quotient.mk'' '' (normalizerSubgroup hp he₀ : Set (FundamentalGroup B b₀)) := by
  -- Reduce quotient elements to representatives in each direction.
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨n, n.2, normalizerQuotientRightCoset_mk hp he₀ n⟩
  · rintro ⟨n, hn, rfl⟩
    let n' : normalizerSubgroup hp he₀ := ⟨n, hn⟩
    exact ⟨QuotientGroup.mk n', normalizerQuotientRightCoset_mk hp he₀ n'⟩

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: the canonical map from the normalizer quotient to
ambient right cosets is injective. -/
theorem normalizerQuotientRightCoset_injective (hp : IsCoveringMap p)
    {e₀ : E} {b₀ : B} (he₀ : p e₀ = b₀) :
    Function.Injective (normalizerQuotientRightCoset hp he₀) := by
  intro q r hqr
  -- Compare representatives and transport the ambient relation back to the quotient group.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective r
  rw [normalizerQuotientRightCoset_mk, normalizerQuotientRightCoset_mk] at hqr
  exact Quotient.sound ((normalizerLeftRel_iff_rightRel hp he₀).mpr (Quotient.exact hqr))

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- The canonical right coset of a normalizer-quotient element is represented by the
normalizer. -/
theorem normalizerQuotientRightCoset_mem (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (he₀ : p e₀ = b₀) (q : normalizerQuotient hp he₀) :
    normalizerQuotientRightCoset hp he₀ q ∈
      Quotient.mk'' '' (normalizerSubgroup hp he₀ : Set (FundamentalGroup B b₀)) := by
  -- The exact range description supplies the required normalizer representative.
  rw [← range_normalizerQuotientRightCoset hp he₀]
  exact ⟨q, rfl⟩

omit [PathConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: monodromy commutes with evaluation by a covering
transformation. -/
private theorem monodromy_commutes_evalInFiber (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀)
    (γ : FundamentalGroup B b₀) (h : 𝒞(E, p, B)) :
    hp.monodromy γ (evalInFiber b₀ e₀ he₀ h) =
      evalInFiber b₀
        (hp.monodromy γ (IsCoveringMap.basepointInFiber p he₀) : E)
        (hp.monodromy γ (IsCoveringMap.basepointInFiber p he₀)).2 h := by
  let Γ := hp.liftPathQuotient γ (IsCoveringMap.basepointInFiber p he₀)
  let h' : C(E, E) := ⟨fun e ↦ h • e, continuous_const_smul h⟩
  let p' : C(E, B) := ⟨p, hp.continuous⟩
  -- Map the canonical lift through `h`; it remains a lift because `h` lies over `p`.
  have hhp : p'.comp h' = p' := by
    ext e
    exact map_smul p h e
  apply hp.monodromy_eq_of_map_eq (Γ.map h')
  change (Γ.map h').map p' = _
  rw [← Path.Homotopic.Quotient.map_comp]
  convert hp.map_liftPathQuotient γ (IsCoveringMap.basepointInFiber p he₀) using 2
  · exact congrArg (fun f : C(E, B) ↦ f _) hhp
  · exact congrArg (fun f : C(E, B) ↦ f _) hhp
  · grind
  · grind

/-- Helper for Theorem 81.2: the underlying comparison function selects the unique
normalizer-quotient class whose right coset has the evaluated monodromy endpoint. -/
@[expose]
noncomputable def normalizerQuotientComparisonValue (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    𝒞(E, p, B) → normalizerQuotient hp he₀ :=
  fun h ↦
    Function.invFun (normalizerQuotientRightCoset hp he₀)
      (Function.invFun (hp.monodromyRightCosetMap he₀) (evalInFiber b₀ e₀ he₀ h))

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: applying the right-coset monodromy map to the comparison
value recovers evaluation at the chosen point. -/
theorem normalizerQuotientComparisonValue_spec (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (h : 𝒞(E, p, B)) :
    hp.monodromyRightCosetMap he₀
        (normalizerQuotientRightCoset hp he₀
          (normalizerQuotientComparisonValue hp e₀ b₀ he₀ h)) =
      evalInFiber b₀ e₀ he₀ h := by
  let M := hp.monodromyRightCosetMap he₀
  let R := normalizerQuotientRightCoset hp he₀
  let e := evalInFiber b₀ e₀ he₀ h
  -- First identify the inverse-monodromy coset with a coset supplied by Lemma 81.1.
  have hM : M (Function.invFun M e) = e :=
    Function.rightInverse_invFun (hp.monodromyRightCosetMap_bijective he₀).2 e
  have he_range : e ∈ Set.range (evalInFiber b₀ e₀ he₀) := ⟨h, rfl⟩
  rw [hp.range_evalInFiber_eq_image_normalizer p e₀ b₀ he₀] at he_range
  obtain ⟨q, hq_normalizer, hqM⟩ := he_range
  have hinv_eq : Function.invFun M e = q :=
    (hp.monodromyRightCosetMap_bijective he₀).1 (hM.trans hqM.symm)
  have hinv_range : Function.invFun M e ∈ Set.range R := by
    rw [range_normalizerQuotientRightCoset hp he₀]
    exact hinv_eq.symm ▸ hq_normalizer
  -- Both inverse-function applications now cancel on their established ranges.
  unfold normalizerQuotientComparisonValue
  dsimp only [M, R, e] at hM hinv_range ⊢
  rw [Function.invFun_eq hinv_range, hM]

omit [PathConnectedSpace B] [LocallyPathConnectedSpace B] in
/-- Helper for Theorem 81.2: the underlying comparison function preserves
multiplication. -/
theorem normalizerQuotientComparisonValue_mul (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (h k : 𝒞(E, p, B)) :
    normalizerQuotientComparisonValue hp e₀ b₀ he₀ (h * k) =
      normalizerQuotientComparisonValue hp e₀ b₀ he₀ h *
        normalizerQuotientComparisonValue hp e₀ b₀ he₀ k := by
  -- It suffices to compare the two classes after the two injective canonical maps.
  apply normalizerQuotientRightCoset_injective hp he₀
  apply (hp.monodromyRightCosetMap_bijective he₀).1
  rw [normalizerQuotientComparisonValue_spec]
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective
    (normalizerQuotientComparisonValue hp e₀ b₀ he₀ h)
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective
    (normalizerQuotientComparisonValue hp e₀ b₀ he₀ k)
  have ha_endpoint :
      hp.monodromy ((a⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀) =
        evalInFiber b₀ e₀ he₀ h := by
    calc
      hp.monodromy ((a⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀) =
          hp.monodromyRightCosetMap he₀
            (normalizerQuotientRightCoset hp he₀ (QuotientGroup.mk a)) := by
        rw [normalizerQuotientRightCoset_mk, hp.monodromyRightCosetMap_mk]
        rw [IsCoveringMap.liftingCorrespondence, Subgroup.coe_inv]
      _ = hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀
            (normalizerQuotientComparisonValue hp e₀ b₀ he₀ h)) :=
        congrArg (fun q ↦ hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀ q)) ha
      _ = evalInFiber b₀ e₀ he₀ h :=
        normalizerQuotientComparisonValue_spec hp e₀ b₀ he₀ h
  have hb_endpoint :
      hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀) =
        evalInFiber b₀ e₀ he₀ k := by
    calc
      hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀) =
          hp.monodromyRightCosetMap he₀
            (normalizerQuotientRightCoset hp he₀ (QuotientGroup.mk b)) := by
        rw [normalizerQuotientRightCoset_mk, hp.monodromyRightCosetMap_mk]
        rw [IsCoveringMap.liftingCorrespondence, Subgroup.coe_inv]
      _ = hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀
            (normalizerQuotientComparisonValue hp e₀ b₀ he₀ k)) :=
        congrArg (fun q ↦ hp.monodromyRightCosetMap he₀
          (normalizerQuotientRightCoset hp he₀ q)) hb
      _ = evalInFiber b₀ e₀ he₀ k :=
        normalizerQuotientComparisonValue_spec hp e₀ b₀ he₀ k
  -- Representatives turn the product into concatenated inverse monodromy paths.
  rw [← ha, ← hb, ← QuotientGroup.mk_mul,
    normalizerQuotientRightCoset_mk, hp.monodromyRightCosetMap_mk]
  symm
  calc
    hp.liftingCorrespondence (IsCoveringMap.basepointInFiber p he₀)
        (((a * b)⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀) =
        hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (hp.monodromy ((a⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
            (IsCoveringMap.basepointInFiber p he₀)) := by
      rw [IsCoveringMap.liftingCorrespondence, mul_inv_rev,
        Subgroup.coe_mul, FundamentalGroup.mul_def, hp.monodromy_trans_apply]
    _ = hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
        (evalInFiber b₀ e₀ he₀ h) := congrArg _ ha_endpoint
    _ = evalInFiber b₀
        (hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀) : E)
        (hp.monodromy ((b⁻¹ : normalizerSubgroup hp he₀) : FundamentalGroup B b₀)
          (IsCoveringMap.basepointInFiber p he₀)).2 h :=
      monodromy_commutes_evalInFiber hp e₀ b₀ he₀ _ h
    _ = evalInFiber b₀ (evalInFiber b₀ e₀ he₀ k : E)
        (evalInFiber b₀ e₀ he₀ k).2 h := by
      rw [hb_endpoint]
    _ = evalInFiber b₀ e₀ he₀ (h * k) := by
      apply Subtype.ext
      simp only [evalInFiber_apply, mul_smul]

end CoveringTransformation
