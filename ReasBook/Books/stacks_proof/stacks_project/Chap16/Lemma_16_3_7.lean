import Mathlib
import StacksProject_2024.Chap15.Definition_15_3_1
import StacksProject_2024.Chap16.Definition_16_2_3
import StacksProject_2024.Chap16.Lemma_16_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

local notation:max "A[" a "]" => Localization.Away a

/-- Helper for Chap16 Lemma 16 3 7: a standard-smooth algebra admits a normalized finite
submersive presentation whose first distinguished variables realize any prescribed finite family.
This is the earlier-safe family-valued specialization needed to compare a standard-smooth chart of
`A[1 / a]` with the frozen localization of a fixed presentation. -/
theorem isStandardSmooth_existsSubmersivePresentationWithPrescribedFamily_local
    {n : ℕ} [IsStandardSmooth R A] (β : Fin n → A) :
    ∃ (c m : ℕ) (P : SubmersivePresentation R A (Fin c ⊕ Fin m) (Fin c)) (h : n ≤ c),
      P.map = Sum.inl ∧ ∀ i : Fin n, P.val (.inl (Fin.castLE h i)) = β i := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P₀⟩⟩ := IsStandardSmooth.out (R := R) (S := A)
  letI : Finite σ := hσ
  letI : Finite ι := hι
  -- Normalize the chosen standard-smooth witness so its distinguished variables occupy the left
  -- `Fin c₀` summand.
  obtain ⟨c₀, m₀, Pstd, hPstd_map⟩ :=
    SubmersivePresentation.exists_sum_fin_reindex (R := R) (A := A) P₀
  -- Adjoin the prescribed family as new distinguished variables via the linear presentation.
  let Qβ : SubmersivePresentation A A (Fin n) (Fin n) := linearSubmersivePresentation β
  have hQβ_map : Qβ.map = (fun i ↦ i) := linearSubmersivePresentation_map β
  have hQβ_val : ∀ i : Fin n, Qβ.val i = β i := linearSubmersivePresentation_val β
  let eRel : Fin (n + c₀) ≃ Fin n ⊕ Fin c₀ := finSumFinEquiv.symm
  let eVar : Fin (n + c₀) ⊕ Fin m₀ ≃ Fin n ⊕ (Fin c₀ ⊕ Fin m₀) :=
    (Equiv.sumCongr (finSumFinEquiv.symm) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)
  let P : SubmersivePresentation R A (Fin (n + c₀) ⊕ Fin m₀) (Fin (n + c₀)) :=
    (Qβ.comp Pstd).reindex eVar eRel
  refine ⟨n + c₀, m₀, P, Nat.le_add_right n c₀, ?_⟩
  constructor
  · -- Compute the normalized map by splitting along the adjoined linear summand.
    ext x
    change eVar.symm
        (Sum.elim (fun rq : Fin n ↦ Sum.inl (Qβ.map rq))
          (fun rp : Fin c₀ ↦ Sum.inr (Pstd.map rp)) (eRel x)) = Sum.inl x
    rw [hQβ_map, hPstd_map]
    cases h : eRel x with
    | inl i =>
        have hx : x = Fin.castAdd c₀ i := by
          simpa [eRel] using congrArg finSumFinEquiv h
        simp [eVar, hx]
    | inr j =>
        have hx : x = Fin.natAdd n j := by
          simpa [eRel] using congrArg finSumFinEquiv h
        simp [eVar, hx]
  · intro i
    -- The first `n` distinguished variables come from the linear presentation of `β`.
    rw [fin_castLE_le_add_right_eq_castAdd]
    change Sum.elim Qβ.val ((algebraMap A A) ∘ Pstd.val) (eVar (.inl (Fin.castAdd c₀ i))) = β i
    have hx : eVar (.inl (Fin.castAdd c₀ i)) = Sum.inl i := by
      simp [eVar, finSumFinEquiv]
    rw [hx]
    exact hQβ_val i

namespace Presentation

section

variable {n m c : ℕ}

/-- Helper for Lemma 16.3.7: the leading Jacobian determinant is the Jacobian minor indexed by the
first `c` variables. -/
lemma jacobianColumnMinor_eq_leadingJacobianDet
    (P : Presentation R A (Fin n) (Fin m)) (hcₙ : c ≤ n) (hcₘ : c ≤ m) :
    let I : Set.powersetCard (Fin n) c :=
      Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hcₙ)
    P.jacobianColumnMinor hcₘ I = P.leadingJacobianDet hcₙ hcₘ := by
  classical
  -- Use the canonical `c`-element subset given by the first `c` variables.
  let I : Set.powersetCard (Fin n) c := Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hcₙ)
  change P.jacobianColumnMinor hcₘ I = P.leadingJacobianDet hcₙ hcₘ
  -- Both determinants are computed from the same Jacobian submatrix once the index set is
  -- identified with the embedding `Fin.castLE hcₙ`.
  unfold jacobianColumnMinor leadingJacobianDet
  have hI : I.1.orderEmbOfFin I.2 = Fin.castLEOrderEmb hcₙ := by
    calc
      I.1.orderEmbOfFin I.2 = Set.powersetCard.ofFinEmbEquiv.symm I := by
        symm
        exact Set.powersetCard.ofFinEmbEquiv_symm_apply I
      _ = Fin.castLEOrderEmb hcₙ := by
        simp [I]
  rw [hI]
  rfl

/-- Helper for Lemma 16.3.7: an elementary-standard witness is a strict-standard witness supported
on the canonical first-`c` Jacobian minor. -/
lemma isStrictlyStandardElement_of_isElementaryStandardElement
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    (h : P.IsElementaryStandardElement a) :
    P.IsStrictlyStandardElement a := by
  classical
  rcases h with ⟨c, hcₙ, hcₘ, a', ha, htail⟩
  let I₀ : Set.powersetCard (Fin n) c :=
    Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hcₙ)
  let aI : Set.powersetCard (Fin n) c → A := fun I ↦ if I = I₀ then a' else 0
  have hminor :
      algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ) =
        algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I₀) := by
    simpa [I₀] using
      congrArg (algebraMap P.Ring A) (P.jacobianColumnMinor_eq_leadingJacobianDet hcₙ hcₘ).symm
  refine ⟨c, hcₘ, aI, ?_, htail⟩
  -- Collapse the strict Jacobian expansion to the single leading minor indexed by `I₀`.
  calc
    a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ) := ha
    _ = a' * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I₀) := by
      rw [hminor]
    _ = aI I₀ * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I₀) := by
      simp [aI]
    _ = ∑ I : Set.powersetCard (Fin n) c,
          aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I) := by
      simp [aI, I₀]

/-- Helper for Lemma 16.3.7: an elementary-standard witness can be unpacked using the canonical
section `P.σ a` in the tail condition. -/
lemma exists_elementaryStandard_data_with_sigma_tail
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    (h : P.IsElementaryStandardElement a) :
    ∃ (c : ℕ) (hcₙ : c ≤ n) (hcₘ : c ≤ m) (a' : A),
      a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ) ∧
        ∀ j : Fin (m - c),
          P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
            P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  rcases h with ⟨c, hcₙ, hcₘ, a', ha, htail⟩
  refine ⟨c, hcₙ, hcₘ, a', ha, ?_⟩
  -- Rewrite the tail condition through the canonical section `P.σ a`.
  simpa [P.tailRelationCondition_iff_sigma a hcₘ] using htail

/-- Helper for Lemma 16.3.7: a strict-standard witness can be unpacked using the canonical
section `P.σ a` in the tail condition. -/
lemma exists_strictlyStandard_data_with_sigma_tail
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    (h : P.IsStrictlyStandardElement a) :
    ∃ (c : ℕ) (hcₘ : c ≤ m) (aI : Set.powersetCard (Fin n) c → A),
      a = ∑ I : Set.powersetCard (Fin n) c,
          aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I) ∧
        ∀ j : Fin (m - c),
          P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
            P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  rcases h with ⟨c, hcₘ, aI, ha, htail⟩
  refine ⟨c, hcₘ, aI, ha, ?_⟩
  -- Rewrite the shared tail condition through the canonical section `P.σ a`.
  simpa [P.tailRelationCondition_iff_sigma a hcₘ] using htail

/-- Helper for Lemma 16.3.7: the displayed Jacobian identity together with the `σ`-tail condition
already packages an elementary-standard witness. -/
lemma isElementaryStandardElement_of_sigma_tail
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    {c : ℕ} (hcₙ : c ≤ n) (hcₘ : c ≤ m) (a' : A)
    (ha : a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ))
    (htail : ∀ j : Fin (m - c),
      P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
        P.leadingRelationIdeal hcₘ + P.ker ^ 2) :
    P.IsElementaryStandardElement a := by
  refine ⟨c, hcₙ, hcₘ, a', ha, ?_⟩
  -- Repackage the canonical `σ`-tail condition back into the intrinsic definition.
  simpa [P.tailRelationCondition_iff_sigma a hcₘ] using htail

/-- Helper for Lemma 16.3.7: the displayed Jacobian-minor expansion together with the `σ`-tail
condition already packages a strict-standard witness. -/
lemma isStrictlyStandardElement_of_sigma_tail
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    {c : ℕ} (hcₘ : c ≤ m) (aI : Set.powersetCard (Fin n) c → A)
    (ha : a = ∑ I : Set.powersetCard (Fin n) c,
      aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I))
    (htail : ∀ j : Fin (m - c),
      P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
        P.leadingRelationIdeal hcₘ + P.ker ^ 2) :
    P.IsStrictlyStandardElement a := by
  refine ⟨c, hcₘ, aI, ha, ?_⟩
  -- Repackage the canonical `σ`-tail condition back into the intrinsic definition.
  simpa [P.tailRelationCondition_iff_sigma a hcₘ] using htail

/-- Helper for Lemma 16.3.7: the source-localized presentation is obtained by composing the fixed
presentation `P` with the one-relation presentation adjoining an inverse to `a`. -/
noncomputable abbrev localizationAway_sigma_tail_presentation
    (P : Presentation R A (Fin n) (Fin m)) (a : A) :
    Presentation R A[a] (Sum Unit (Fin n)) (Sum Unit (Fin m)) :=
  (Presentation.localizationAway A[a] a).comp P

/-- Helper for Lemma 16.3.7: in the localized sigma-tail presentation, every old relation of `P`
survives unchanged after renaming the variables into the `Sum Unit (Fin n)` order. -/
lemma localizationAway_sigma_tail_relation_inr
    (P : Presentation R A (Fin n) (Fin m)) (a : A) (j : Fin m) :
    (P.localizationAway_sigma_tail_presentation a).relation (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.relation j) := by
  -- This is the defining formula for the `P`-part of a composite presentation.
  rfl

/-- Helper for Lemma 16.3.7: the frozen localized sigma-tail presentation carries the canonical
quotient equivalence onto `A[a]`. -/
noncomputable abbrev localizationAway_sigma_tail_model_equiv
    (P : Presentation R A (Fin n) (Fin m)) (a : A) :=
  (P.localizationAway_sigma_tail_presentation a).quotientEquiv

/-- Helper for Lemma 16.3.7: the arbitrary section `P.σ` sends `0` to a lift whose image in the
quotient algebra is zero, hence the lift itself lies in the presentation kernel. -/
lemma sigma_zero_mem_ker
    (P : Presentation R A (Fin n) (Fin m)) :
    P.σ (0 : A) ∈ P.ker := by
  -- The chosen lift of `0` maps to zero under the presentation algebra map.
  rw [P.ker_eq_ker_aeval_val]
  change MvPolynomial.aeval P.val (P.σ (0 : A)) = 0
  exact P.aeval_val_σ (0 : A)

/-- Helper for Lemma 16.3.7: the arbitrary section `P.σ` sends `-1` to a lift differing from the
constant polynomial `-1` by an element of the presentation kernel. -/
lemma sigma_neg_one_add_one_mem_ker
    (P : Presentation R A (Fin n) (Fin m)) :
    P.σ (-1 : A) + 1 ∈ P.ker := by
  -- The chosen lift of `-1` differs from the constant polynomial `-1` by a kernel element.
  rw [P.ker_eq_ker_aeval_val]
  change MvPolynomial.aeval P.val (P.σ (-1 : A) + 1) = 0
  simp [P.aeval_val_σ]

/-- Helper for Lemma 16.3.7: the source inverse polynomial `x₀ * σ(a) - 1` already vanishes in
the localized sigma-tail model, so it belongs to the localized presentation kernel. -/
lemma localizationAway_sigma_tail_inverse_poly_mem_ker
    (P : Presentation R A (Fin n) (Fin m)) (a : A) :
    MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1 ∈
      (P.localizationAway_sigma_tail_presentation a).ker := by
  classical
  -- Evaluate the explicit inverse polynomial in the frozen localized presentation.
  rw [(P.localizationAway_sigma_tail_presentation a).ker_eq_ker_aeval_val]
  change MvPolynomial.aeval (P.localizationAway_sigma_tail_presentation a).val
      (MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1) = 0
  simp [Algebra.Presentation.localizationAway_sigma_tail_presentation,
    Algebra.Presentation.localizationAway, Algebra.Presentation.comp, MvPolynomial.aeval_rename]
  change MvPolynomial.aeval (fun i ↦ algebraMap A A[a] (P.val i)) (P.σ a) *
      IsLocalization.Away.invSelf a - 1 = 0
  -- Collapse the renamed lift back to the image of `a` in the localization.
  rw [show MvPolynomial.aeval (fun i ↦ algebraMap A A[a] (P.val i)) (P.σ a) =
      algebraMap A A[a] ((MvPolynomial.aeval P.val) (P.σ a)) by
        simpa [MvPolynomial.aeval_def, RingHom.comp_apply,
          IsScalarTower.algebraMap_eq R A A[a]] using
          (MvPolynomial.map_aeval P.val (algebraMap A A[a]) (P.σ a)).symm]
  rw [P.aeval_val_σ]
  -- The distinguished localization variable evaluates to `a⁻¹`, so the product is `1`.
  rw [show algebraMap A A[a] a * IsLocalization.Away.invSelf a = 1 by
    exact IsLocalization.Away.mul_invSelf (S := A[a]) a]
  simp

/-- Helper for Lemma 16.3.7: any source-kernel relation remains a relation after renaming the
variables into the localized sigma-tail presentation. -/
lemma localizationAway_sigma_tail_rename_mem_ker
    (P : Presentation R A (Fin n) (Fin m)) (a : A) {p : P.Ring}
    (hp : p ∈ P.ker) :
    MvPolynomial.rename Sum.inr p ∈ (P.localizationAway_sigma_tail_presentation a).ker := by
  -- Evaluate the renamed source relation in the frozen localized presentation and use that `p`
  -- already vanishes in the source quotient.
  rw [(P.localizationAway_sigma_tail_presentation a).ker_eq_ker_aeval_val]
  change MvPolynomial.aeval (P.localizationAway_sigma_tail_presentation a).val
      (MvPolynomial.rename Sum.inr p) = 0
  simp [Algebra.Presentation.localizationAway_sigma_tail_presentation,
    Algebra.Presentation.localizationAway, Algebra.Presentation.comp, MvPolynomial.aeval_rename]
  change MvPolynomial.aeval (fun i ↦ algebraMap A A[a] (P.val i)) p = 0
  rw [show MvPolynomial.aeval (fun i ↦ algebraMap A A[a] (P.val i)) p =
      algebraMap A A[a] ((MvPolynomial.aeval P.val) p) by
        simpa [MvPolynomial.aeval_def, RingHom.comp_apply,
          IsScalarTower.algebraMap_eq R A A[a]] using
          (MvPolynomial.map_aeval P.val (algebraMap A A[a]) p).symm]
  have hp' : (MvPolynomial.aeval P.val) p = 0 := by
    rw [P.ker_eq_ker_aeval_val] at hp
    exact hp
  rw [hp']
  simp

/-- Helper for Lemma 16.3.7: the new localization relation is congruent modulo the localized
presentation kernel to the explicit inverse polynomial `x₀ * σ(a) - 1`. -/
lemma localizationAway_sigma_tail_relation_inl_sub_mem_ker
    (P : Presentation R A (Fin n) (Fin m)) (a : A) :
    (P.localizationAway_sigma_tail_presentation a).relation (Sum.inl ()) -
        (MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1) ∈
      (P.localizationAway_sigma_tail_presentation a).ker := by
  -- Both summands vanish in the localized model, so their difference lies in the kernel.
  rw [(P.localizationAway_sigma_tail_presentation a).ker_eq_ker_aeval_val]
  change
    MvPolynomial.aeval (P.localizationAway_sigma_tail_presentation a).val
        ((P.localizationAway_sigma_tail_presentation a).relation (Sum.inl ()) -
          (MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1)) = 0
  have hrel :
      MvPolynomial.aeval (P.localizationAway_sigma_tail_presentation a).val
        ((P.localizationAway_sigma_tail_presentation a).relation (Sum.inl ())) = 0 :=
    (P.localizationAway_sigma_tail_presentation a).aeval_val_relation (Sum.inl ())
  have hinv :
      MvPolynomial.aeval (P.localizationAway_sigma_tail_presentation a).val
        (MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1) = 0 := by
    have hinv' := P.localizationAway_sigma_tail_inverse_poly_mem_ker a
    rw [(P.localizationAway_sigma_tail_presentation a).ker_eq_ker_aeval_val] at hinv'
    exact hinv'
  -- Subtract the two vanishing relations in the quotient model.
  rw [map_sub, hrel, hinv]
  simp

/-- Helper for Lemma 16.3.7: each localized tail relation satisfies the exact source identity
`f = x₀ (σ(a) f) - (x₀σ(a) - 1) f`. -/
lemma localizationAway_sigma_tail_tail_relation_factor
    (P : Presentation R A (Fin n) (Fin m)) (a : A)
    {c : ℕ} (hcₘ : c ≤ m) (j : Fin (m - c)) :
    (P.localizationAway_sigma_tail_presentation a).relation (Sum.inr (tailRelationIndex hcₘ j)) =
      MvPolynomial.X (Sum.inl ()) *
          MvPolynomial.rename Sum.inr (P.σ a * P.relation (tailRelationIndex hcₘ j)) -
        (MvPolynomial.rename Sum.inr (P.σ a) * MvPolynomial.X (Sum.inl ()) - 1) *
          (P.localizationAway_sigma_tail_presentation a).relation
            (Sum.inr (tailRelationIndex hcₘ j)) := by
  -- Expand the localized old relation and rearrange the source polynomial identity.
  simp [Algebra.Presentation.localizationAway_sigma_tail_presentation]
  ring

/-- Helper for Lemma 16.3.7: an elementary-standard witness in a fixed finite presentation gives
standard smoothness after localizing away from the witnessed element. -/
theorem isStandardSmooth_localizationAway_of_sigma_tail_data
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    {c : ℕ} (hcₙ : c ≤ n) (hcₘ : c ≤ m) (a' : A)
    (ha : a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ))
    (htail : ∀ j : Fin (m - c),
      P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
        P.leadingRelationIdeal hcₘ + P.ker ^ 2) :
    IsStandardSmooth R A[a] := by
  -- Route correction: after unpacking the witness into the canonical `σ`-tail form, the remaining
  -- source-faithful task is purely presentation-local on
  -- `P.localizationAway_sigma_tail_presentation a`.
  -- The arbitrary section `P.σ` is not a ring homomorphism, so the inverse relation must be
  -- normalized modulo `P.ker` using `sigma_zero_mem_ker` and `sigma_neg_one_add_one_mem_ker`,
  -- not by false literal equalities `P.σ 0 = 0` and `P.σ (-1) = -1`.
  -- TODO: use `P.localizationAway_sigma_tail_model_equiv a` to freeze the transport from the
  -- composite localized presentation to `A[a]`, compute the new `Sum.inl` relation as the source
  -- inverse relation `x₀ * σ(a) - 1`, combine that with
  -- `localizationAway_sigma_tail_relation_inr` to identify the model with the source quotient
  -- `R[x₀, x₁, …, xₙ]/(x₀ * σ(a) - 1, f₁, …, fₘ)`, then prove the localized conormal module is
  -- generated by the inverse relation and the first `c` relations using `htail`, and finally
  -- conclude by the Jacobian-inverted standard-smooth presentation theorem.
  sorry

/-- Helper for Lemma 16.3.7: a strict-standard witness in canonical `σ`-tail form gives
smoothness of the localization together with stable freeness of its Kähler differentials. -/
theorem smooth_stablyFreeKaehler_localizationAway_of_strict_sigma_tail_data
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    {c : ℕ} (hcₘ : c ≤ m) (aI : Set.powersetCard (Fin n) c → A)
    (ha : a = ∑ I : Set.powersetCard (Fin n) c,
      aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I))
    (htail : ∀ j : Fin (m - c),
      P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
        P.leadingRelationIdeal hcₘ + P.ker ^ 2) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  -- Route correction: once the strict witness is rewritten with the canonical section `P.σ a`,
  -- the remaining source proof is the localized conormal-splitting argument in one fixed
  -- presentation.
  -- TODO: obtain a localized left inverse to the transpose Jacobian from the Jacobian-minor
  -- identity `ha`, convert it to a retraction of `kerCotangentToTensor`, and then read off both
  -- smoothness and stable freeness from the split conormal sequence.
  sorry

/-- Helper for Lemma 16.3.7: an elementary-standard witness in a fixed finite presentation gives
standard smoothness after localizing away from the witnessed element. -/
theorem isStandardSmooth_localizationAway_of_isElementaryStandardElement
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    (h : P.IsElementaryStandardElement a) :
    IsStandardSmooth R A[a] := by
  obtain ⟨c, hcₙ, hcₘ, a', ha, htail⟩ :=
    P.exists_elementaryStandard_data_with_sigma_tail h
  -- Reduce the source implication to the fixed-presentation sigma-tail datum isolated above.
  exact P.isStandardSmooth_localizationAway_of_sigma_tail_data hcₙ hcₘ a' ha htail

/-- Helper for Lemma 16.3.7: a strict-standard witness in a fixed finite presentation gives
smoothness of the localization together with stable freeness of its Kähler differentials. -/
theorem smooth_stablyFreeKaehler_localizationAway_of_isStrictlyStandardElement
    (P : Presentation R A (Fin n) (Fin m)) {a : A}
    (h : P.IsStrictlyStandardElement a) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  obtain ⟨c, hcₘ, aI, ha, htail⟩ := P.exists_strictlyStandard_data_with_sigma_tail h
  -- Reduce the source implication to the fixed-presentation sigma-tail datum isolated above.
  exact P.smooth_stablyFreeKaehler_localizationAway_of_strict_sigma_tail_data hcₘ aI ha htail

/-- Helper for Lemma 16.3.7: after freezing one finite presentation of `A`, smoothness of
`A[1/a]` together with stable freeness of `Ω[A[1/a]⁄R]` eventually yields strict-standard powers
inside that same presentation. -/
theorem exists_eventually_isStrictlyStandardElement_of_smooth_stablyFreeKaehler_localizationAway
    (P : Presentation R A (Fin n) (Fin m)) (a : A)
    (hsmooth : Smooth R A[a]) (hstablyFree : Module.StablyFree A[a] Ω[A[a]⁄R]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → P.IsStrictlyStandardElement (a ^ e) := by
  -- Route correction: the denominator-clearing argument must stay in the frozen presentation `P`
  -- instead of repackaging through an abstract existential witness.
  -- TODO: use the localized conormal short exact sequence for `P.localizationAway a`, stabilize
  -- the localized conormal module until it becomes free, clear denominators in a localized left
  -- inverse matrix, and apply Lemma 16.2.4 to obtain strict-standard witnesses for large powers.
  sorry

/-- Helper for Lemma 16.3.7: after freezing one finite presentation of `A`, standard smoothness
of `A[1/a]` eventually yields elementary-standard powers inside that same presentation. -/
theorem exists_eventually_isElementaryStandardElement_of_isStandardSmooth_localizationAway
    (P : Presentation R A (Fin n) (Fin m)) (a : A)
    (h : IsStandardSmooth R A[a]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → P.IsElementaryStandardElement (a ^ e) := by
  -- Route correction: the comparison must descend the normalized standard-smooth chart of
  -- `A[1/a]` back to the fixed presentation `P`, rather than proving an abstract existence theorem
  -- first and only later trying to recover `P`-local witness data.
  let β : Fin (n + 1) → A[a] := fun i ↦
    Fin.cases (IsLocalization.Away.invSelf a) (fun j ↦ algebraMap A A[a] (P.val j)) i
  obtain ⟨c, m', Q, hc, hQmap, hβ⟩ :=
    Algebra.isStandardSmooth_existsSubmersivePresentationWithPrescribedFamily_local
      (R := R) (A := A[a]) β
  -- The normalized chart now contains both the inverse of `a` and the images of the frozen
  -- generators `P.val j` among its distinguished variables.
  -- TODO: choose a prescribed-generator submersive presentation of `A[1/a]`, compare it with the
  -- localization of `P`, use `hQmap` and `hβ` to identify the distinguished variables carrying
  -- `a⁻¹` and the frozen generators, clear denominators in the descended generators and Jacobian
  -- inverse relation, and package the resulting data as elementary-standard witnesses for large
  -- powers.
  sorry

end

end Presentation

/- Domain-style sampling for local smoothness criteria in finitely presented commutative algebra:
* primary domain: standard smooth localizations, Kähler differentials, and the Chapter 16
  predicates `IsElementaryStandard` and `IsStrictlyStandard`;
* sampled owner declarations:
  `Algebra.IsStandardSmooth`,
  `IsStandardSmooth.smooth`,
  `IsStandardSmooth.free_kaehlerDifferential`,
  `Module.StablyFree`;
* best owner abstraction:
  `Algebra.IsStandardSmooth` and `Smooth` are the canonical owners for the localized algebra
  `A[a]`, while `Module.StablyFree` is the chapter owner for the stable-freeness clause on
  `Ω[A[a]⁄R]`; the predicates `IsElementaryStandard` and `IsStrictlyStandard` remain the
  source-facing conditions on `a`;
* primitive vs. derived:
  the primitive source-facing data are only the two Chapter 16 predicates on `a`. Standard
  smoothness and smoothness of `A[a]`, together with freeness or stable freeness of `Ω[A[a]⁄R]`,
  are derived owner-level consequences and should be stated directly through those owners rather
  than repackaged in a local wrapper.

Source/core/bridge triage:
* `source-facing`: the six conditions in Stacks Lemma 16.3.7 on a single element `a : A`;
* `core/canonical`: `Algebra.IsStandardSmooth`, `Smooth`, `Module.Free`, and `Module.StablyFree`
  for the localized algebra and its Kähler differentials;
* `bridge/view`: the Chapter 16 predicates `IsElementaryStandard` and `IsStrictlyStandard`
  translate presentation-level Jacobian conditions into those canonical owner conclusions.
-/

-- Proof sketch for Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: this is the direct source-facing
-- conjunction of the canonical owner consequences
-- `IsStandardSmooth.free_kaehlerDifferential` and `[IsStandardSmooth R A_a] : Smooth R A_a`.
/-- Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: if `A_a` is standard smooth over `R`, then `A_a`
is smooth over `R` and its module of Kähler differentials is free. -/
@[stacks 07EZ]
theorem standardSmoothAway_implies_freeKaehler
    (a : A) (h : IsStandardSmooth R A[a]) :
    Smooth R A[a] ∧ Module.Free A[a] Ω[A[a]⁄R] := by
  letI := h
  exact ⟨inferInstance, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: this is the direct owner-level
-- upgrade from `Module.Free` to `Module.StablyFree`, via the canonical instance
-- `Module.stablyFree_of_free`, together with the unchanged smoothness hypothesis.
/-- Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: if `A_a` is smooth over `R` and `Ω[(A_a)/R]` is
free, then `A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
@[stacks 07EZ]
theorem freeKaehlerAway_implies_stablyFreeKaehler
    (a : A) (hsmooth : Smooth R A[a]) (hfree : Module.Free A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  letI := hfree
  exact ⟨hsmooth, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: this is the tautological
-- projection from condition `(2)` to its smoothness component.
/-- Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: condition `(2)` implies that `A_a` is smooth over
`R`. -/
@[stacks 07EZ]
theorem stablyFreeKaehlerAway_implies_smooth
    (a : A) (h : Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] := h.1

-- Proof sketch for Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: an elementary standard element is,
-- by definition, a special case of a strictly standard element using a single leading Jacobian
-- determinant.
/-- Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: every elementary standard element of `A` over `R`
is strictly standard. -/
@[stacks 07EZ]
theorem isElementaryStandard_implies_isStrictlyStandard
    (a : A) (h : IsElementaryStandard R a) :
    IsStrictlyStandard R a := by
  rcases h with ⟨n, m, P, hP⟩
  -- Repackage the presentation-level conversion of witnesses into the algebra-level existential.
  exact ⟨n, m, P, P.isStrictlyStandardElement_of_isElementaryStandardElement hP⟩

-- Proof sketch for Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: starting from an elementary
-- standard presentation, adjoin an inverse to the chosen Jacobian determinant and rewrite the
-- localization as a standard smooth presentation.
/-- Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: if `a` is elementary standard in `A` over `R`,
then the localization `A_a` is standard smooth over `R`. -/
@[stacks 07EZ]
theorem isElementaryStandard_implies_standardSmoothAway
    (a : A) (h : IsElementaryStandard R a) :
    IsStandardSmooth R A[a] := by
  rcases h with ⟨n, m, P, hP⟩
  -- The owner-level statement is just the existential packaging of the presentation-local bridge.
  exact P.isStandardSmooth_localizationAway_of_isElementaryStandardElement hP

-- Proof sketch for Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: a strictly standard presentation
-- gives a smooth localization, and the conormal sequence shows that `Ω[(A_a)/R]` is a direct
-- summand of a finite free module, hence stably free.
/-- Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: if `a` is strictly standard in `A` over `R`, then
`A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
@[stacks 07EZ]
theorem isStrictlyStandard_implies_stablyFreeKaehlerAway
    (a : A) (h : IsStrictlyStandard R a) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  rcases h with ⟨n, m, P, hP⟩
  -- Repackage the localized smoothness and stable-freeness conclusions from the chosen witness.
  exact P.smooth_stablyFreeKaehler_localizationAway_of_isStrictlyStandardElement hP

section

variable [FinitePresentation R A]

-- Proof sketch for Lemma 16.3.7 (e): choose a finite presentation of `A` over `R`, stabilize the
-- conormal module so it becomes free after adjoining dummy variables, and then use the Jacobian
-- criterion to obtain that all sufficiently large powers of `a` are strictly standard.
/-- Lemma 16.3.7 (e): if condition `(2)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is strictly standard in `A` over `R`. -/
@[stacks 07EZ]
theorem stablyFreeKaehlerAway_eventually_strictlyStandard_pow
    (a : A) (hsmooth : Smooth R A[a]) (hstablyFree : Module.StablyFree A[a] Ω[A[a]⁄R]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsStrictlyStandard R (a ^ e) := by
  let n := Presentation.ofFinitePresentationVars R A
  let m := Presentation.ofFinitePresentationRels R A
  let P : Presentation R A (Fin n) (Fin m) := Presentation.ofFinitePresentation R A
  obtain ⟨e0, he0⟩ :=
    P.exists_eventually_isStrictlyStandardElement_of_smooth_stablyFreeKaehler_localizationAway
      a hsmooth hstablyFree
  refine ⟨e0, ?_⟩
  intro e hge
  -- Freeze one presentation of `A` and package the resulting presentation-local witness globally.
  exact ⟨n, m, P, he0 e hge⟩

-- Proof sketch for Lemma 16.3.7 (f): from a standard smooth presentation of `A_a`, clear
-- denominators in the chosen generators and defining equations to descend to a presentation of
-- `A`; for all sufficiently large powers of `a`, the Jacobian determinant and tail
-- ideal-membership conditions then witness elementary standardness.
/-- Lemma 16.3.7 (f): if condition `(4)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is elementary standard in `A` over `R`. -/
@[stacks 07EZ]
theorem standardSmoothAway_eventually_elementaryStandard_pow
    (a : A) (h : IsStandardSmooth R A[a]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsElementaryStandard R (a ^ e) := by
  let n := Presentation.ofFinitePresentationVars R A
  let m := Presentation.ofFinitePresentationRels R A
  let P : Presentation R A (Fin n) (Fin m) := Presentation.ofFinitePresentation R A
  obtain ⟨e0, he0⟩ :=
    P.exists_eventually_isElementaryStandardElement_of_isStandardSmooth_localizationAway a h
  refine ⟨e0, ?_⟩
  intro e hge
  -- Freeze one presentation of `A` and package the resulting presentation-local witness globally.
  exact ⟨n, m, P, he0 e hge⟩

end

end

end Algebra
