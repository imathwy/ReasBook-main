import stacks_proof.stacks_project.Chap10.Lemma_10_154_2
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3
import stacks_proof.stacks_project.Chap10.Lemma_10_159_1.Index
import stacks_proof.stacks_project.Chap10.Lemma_10_159_2.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Domain-style sampling:
* primary domain: local commutative algebra of filtered colimits of étale `R`-algebras and the
  induced residue-field extension on a local target;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`;
  - `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
  - `IsStrictHenselizationOf.isFilteredColimitOfEtale`;
  - `exists_flat_localAlgebra_with_residueField_equiv`.
* owner decision:
  - `source-facing`: the existence of a local `R`-algebra whose residue field realizes the given
    separable algebraic extension;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the hidden `ULift`-based same-universe presentation packaged by the source-facing
    owner `(algebraMap R R').IsFilteredColimitOfEtale`.

Primitive data are the local `R`-algebra itself, the locality of `R → R'`, and the owner-level
filtered-colimit-of-étale hypothesis. A chosen directed system of finite étale local stages is
derived bridge data, so it should not remain the main public output. Likewise the residue-field
comparison should be a direct existential `AlgEquiv` over `ResidueField R`, not a `Nonempty`
wrapper. The witness ring should range over the same ambient universe as in
`exists_flat_localAlgebra_with_residueField_equiv`, namely `Type (max u w)`. The universe-lift
needed to express the canonical owner should stay inside the owner wrapper rather than appearing in
the public theorem statement.
-/

variable (R)

/-- Helper for Chap10 Lemma 10 159 2: the ind-étale invariant for stage rings in the
universe used by the transfinite construction. -/
abbrev stageIndEtale
    (A : Type (max u w)) [CommRing A] [Algebra R A] : Prop :=
  RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R A)

/-- Helper for Chap10 Lemma 10 159 2: the ind-étale owner of a stage is unchanged when the
stage is transported across an equality of its target intermediate field. -/
theorem stageIndEtale_of_stage_cast_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    (e : L = M)
    (S : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (hS : stageIndEtale (R := R) S.A) :
    stageIndEtale (R := R)
      (cast (by rw [e]) S :
        ResidueExtensionStage.{u, w, max u w} (R := R) K M).A := by
  -- Eliminate the target-field equality once; after that the transported stage is the same stage.
  subst M
  simpa using hS

/-- Helper for Lemma 10.159.2: an index below the successor ordinal `α + 1` is either the new top
index or it already lies in the previous closed prefix `Set.Iic α`. -/
lemma iic_succ_eq_top_or_le
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic (α + 1)) :
    β.1 = α + 1 ∨ β.1 ≤ α := by
  -- Split according to whether the index is the successor top or a genuinely earlier stage.
  by_cases hβ : β.1 = α + 1
  · exact Or.inl hβ
  · exact Or.inr (by simpa [Order.lt_succ_iff] using lt_of_le_of_ne β.2 hβ)

/-- Helper for Chap10 Lemma 10 159 2: in the closed interval below a successor ordinal, any
index that is not below the predecessor is the successor top. -/
lemma successor_eq_top_of_not_le
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic (α + 1)) (hβ : ¬ β.1 ≤ α) :
    β = (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1)) := by
  -- Antisymmetry pins the underlying ordinal between its interval bound and the successor top.
  apply Subtype.ext
  apply le_antisymm
  · exact β.2
  · exact le_of_not_gt (by simpa [Order.lt_succ_iff] using hβ)

/-- Helper for Chap10 Lemma 10 159 2: a non-top index in `Set.Iic (α + 1)` lies below the
predecessor ordinal `α`. -/
theorem successorIndex_le_of_ne_top_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic (α + 1))
    (hβ : β ≠ (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1))) :
    β.1 ≤ α := by
  -- If the index were not below `α`, the successor classifier would make it the top index.
  by_contra hle
  exact hβ (successor_eq_top_of_not_le (R := R) (K := K) β hle)

/-- Helper for Chap10 Lemma 10 159 2: non-topness propagates backwards along the order on
`Set.Iic (α + 1)`. -/
theorem successorIndex_ne_top_of_le_ne_top_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {β γ : Set.Iic (α + 1)} (hβγ : β ≤ γ)
    (hγ : γ ≠ (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1))) :
    β ≠ (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1)) := by
  -- If the lower index were top, the upper index would also be forced to be top.
  intro hβ
  subst β
  apply hγ
  apply Subtype.ext
  exact le_antisymm γ.2 hβγ

namespace ResidueExtensionStage.Hom

/-- Helper for Chap10 Lemma 10 159 2: copying only the proof of the same intermediate-field
inclusion preserves a residue-extension-stage morphism's algebra map. -/
noncomputable abbrev copyLeFilteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom h S T) :
    ResidueExtensionStage.Hom h' S T where
  toAlgHom := f.toAlgHom
  isLocalHom := f.isLocalHom
  residue_comm := f.residue_comm

/-- Helper for Chap10 Lemma 10 159 2: the copied morphism has the same algebra-map projection. -/
@[simp] theorem copyLeFilteredColimit_toAlgHom
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom h S T) :
    (copyLeFilteredColimit (R := R) (K := K) (h' := h') f).toAlgHom = f.toAlgHom := by
  -- The adapter reuses all morphism fields and changes only a proof-irrelevant inclusion witness.
  rfl

/-- Helper for Chap10 Lemma 10 159 2: changing the proof that two stage-morphism types are
equal does not change the algebra-map projection when the source and target stages are unchanged. -/
@[simp] theorem toAlgHom_cast_same_stages
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (e :
      ResidueExtensionStage.Hom h S T =
        ResidueExtensionStage.Hom h' S T)
    (f : ResidueExtensionStage.Hom h S T) :
    (cast e f : ResidueExtensionStage.Hom h' S T).toAlgHom = f.toAlgHom := by
  -- Eliminate the type equality once; the projection is then literally the same field.
  cases e
  rfl

/-- Helper for Chap10 Lemma 10 159 2: stage equalities identify the corresponding
stage-morphism types, up to proof irrelevance in the intermediate-field inclusion. -/
theorem homType_eq_of_stage_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S S' : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (hS : S = S') (hT : T = T') :
    ResidueExtensionStage.Hom h S T =
      ResidueExtensionStage.Hom h' S' T' := by
  -- After the endpoint stages are identified, only the proof-irrelevant order witness remains.
  subst S'
  subst T'
  rw [Subsingleton.elim h h']

/-- Helper for Chap10 Lemma 10 159 2: stage equalities identify the corresponding algebra-map
types carried by stage morphisms. -/
theorem algHomType_eq_of_stage_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {S S' : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (hS : S = S') (hT : T = T') :
    (S.A →ₐ[R] T.A) = (S'.A →ₐ[R] T'.A) := by
  -- The carrier types are projections of the two endpoint stages.
  subst S'
  subst T'
  rfl

/-- Helper for Chap10 Lemma 10 159 2: casting a stage morphism across endpoint-stage
equalities transports only its `toAlgHom` projection. -/
@[simp] theorem toAlgHom_cast_stage_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S S' : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (hS : S = S') (hT : T = T')
    (f : ResidueExtensionStage.Hom h S T) :
    (cast (homType_eq_of_stage_eq (R := R) hS hT) f :
        ResidueExtensionStage.Hom h' S' T').toAlgHom =
      cast (algHomType_eq_of_stage_eq (R := R) hS hT) f.toAlgHom := by
  -- Reduce to unchanged endpoints; proof irrelevance removes the inclusion-witness cast.
  subst S'
  subst T'
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Chap10 Lemma 10 159 2: the same `toAlgHom` cast normalization holds for any
proof of the endpoint-transported stage-morphism type equality. -/
theorem toAlgHom_cast_stage_eq_of_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S S' : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (hS : S = S') (hT : T = T')
    (e :
      ResidueExtensionStage.Hom h S T =
        ResidueExtensionStage.Hom h' S' T')
    (f : ResidueExtensionStage.Hom h S T) :
    (cast e f : ResidueExtensionStage.Hom h' S' T').toAlgHom =
      cast (algHomType_eq_of_stage_eq (R := R) hS hT) f.toAlgHom := by
  -- Proof irrelevance for the type equality lets us replace an elaborator-generated cast proof by
  -- the canonical endpoint-transport proof above.
  rw [Subsingleton.elim e (homType_eq_of_stage_eq (R := R) hS hT)]
  exact toAlgHom_cast_stage_eq (R := R) hS hT f

end ResidueExtensionStage.Hom

/-- Helper for Lemma 10.159.2: the source-proof successor step upgrades the top stage of a closed
prefix chain by adjoining the next well-ordered residue-field generator, before transporting the
target field along `wellOrder_prefixField_succ`. -/
theorem exists_successor_adjoin_top_stage_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A) :
    let Lsucc : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lsucc,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R)
            (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
            (wellOrder_prefixElement (R := R) (K := K) hα))
          C.topStage T) ∧
      stageIndEtale (R := R) T.A := by
  let βtop : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  have htopOwner : stageIndEtale (R := R) C.topStage.A := by
    -- Read the ind-étale owner from the old top stage of the chain.
    simpa [βtop, PrefixStageChain.topStage] using howner βtop
  -- Keep the successor stage in the raw adjoin-field form; the remaining blocker is the transport
  -- from this canonical field to the proof-dependent `closedPrefixField` at `α + 1`.
  simpa [PrefixStageChain.topStage] using
    extend_stage_by_separable_element_with_filteredColimit (R := R) (S := C.topStage)
      htopOwner (wellOrder_prefixElement (R := R) (K := K) hα)

/-- Helper for Lemma 10.159.2: the successor step already produces a top stage whose structural
map from `R` is ind-étale, after rewriting the target field with
`wellOrder_prefixField_succ`. -/
theorem successor_top_stage_exists_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A) :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
          ⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩),
      stageIndEtale (R := R) T.A := by
  -- Rewrite the successor target field once; after that, the raw successor-stage theorem already
  -- has the required existential shape.
  rw [closedPrefixField, wellOrder_prefixField_succ (R := R) (K := K) hα]
  rcases exists_successor_adjoin_top_stage_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨T, -, hT⟩
  exact ⟨T, hT⟩

/-- Helper for Lemma 10.159.2: the successor closed-prefix field is exactly the one-element
adjoin field used by the raw successor-stage theorem. -/
theorem successor_closedPrefixField_eq_adjoin
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K)) :
    closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩ =
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R) := by
  -- Rewrite the closed-prefix field through its underlying well-ordered prefix-field definition.
  simpa [closedPrefixField] using
    wellOrder_prefixField_succ (R := R) (K := K) hα

/-- Helper for Lemma 10.159.2: every successor-stage index strictly below the new top already
uses the old closed-prefix field. -/
theorem closedPrefixField_succ_below_top_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β =
      closedPrefixField (R := R) K (le_of_lt hα) ⟨β.1, hβ⟩ := by
  -- Both sides are the same well-ordered prefix field; only the proof of the ambient bound
  -- changes.
  simpa [closedPrefixField] using
    (wellOrder_prefixField_proof_irrel (R := R) (K := K)
      (α := β.1)
      (h₁ := le_trans β.2 (Order.succ_le_of_lt hα))
      (h₂ := le_trans hβ (le_of_lt hα)))

/-- Helper for Lemma 10.159.2: below the new successor top, the normalized stage is just the old
stage transported along `closedPrefixField_succ_below_top_eq`. -/
noncomputable abbrev successor_stage_of_below_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β) :=
  Eq.ndrec
    (motive := fun L ↦
      ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (C.stage ⟨β.1, hβ⟩)
    (closedPrefixField_succ_below_top_eq (R := R) (K := K) hα β hβ).symm

/-- Helper for Chap10 Lemma 10 159 2: an index below `α + 1` that is not the new top lies
below the old top `α`. -/
theorem successor_below_of_not_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic (α + 1)) (hβtop : ¬ β.1 = α + 1) :
    β.1 ≤ α := by
  -- Convert non-topness in the closed successor interval into the usual predecessor bound.
  simpa [Order.lt_succ_iff] using lt_of_le_of_ne β.2 hβtop

/-- Helper for Chap10 Lemma 10 159 2: the successor chain stage selector is the old transported
stage below `α` and the supplied stage at the new top. -/
noncomputable def successorPrefixStage
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (β : Set.Iic (α + 1)) :
    ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β) :=
  if hβtop : β.1 = α + 1 then
    Eq.ndrec
      (motive := fun β' : Set.Iic (α + 1) ↦
        ResidueExtensionStage.{u, w, max u w} (R := R) K
          (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β'))
      Ttop
      (Subtype.ext hβtop).symm
  else
    successor_stage_of_below_top (R := R) (K := K) hα C β
      (successor_below_of_not_top (R := R) (K := K) β hβtop)

/-- Helper for Chap10 Lemma 10 159 2: the successor stage selector returns the supplied top
stage at `α + 1`. -/
theorem successorPrefixStage_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩)) :
    successorPrefixStage (R := R) (K := K) hα C Ttop
        (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1)) =
      Ttop := by
  -- Unfold the selector once; the positive branch is judgmentally the supplied top stage.
  dsimp [successorPrefixStage]
  simp

/-- Helper for Chap10 Lemma 10 159 2: below the successor top, the successor stage selector
returns the transported old-chain stage. -/
theorem successorPrefixStage_below
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    successorPrefixStage (R := R) (K := K) hα C Ttop β =
      successor_stage_of_below_top (R := R) (K := K) hα C β hβ := by
  -- The top branch would force `α + 1 ≤ α`, so the selector takes the below-top branch.
  have hβnot : ¬ β.1 = α + 1 := by
    intro htop
    have hsucc_le : α + 1 ≤ α := by
      calc
        α + 1 = β.1 := htop.symm
        _ ≤ α := hβ
    exact not_le_of_gt (Order.lt_succ α) hsucc_le
  dsimp [successorPrefixStage]
  simp [hβnot]

/-- Helper for Chap10 Lemma 10 159 2: the ind-étale owner of a stage transports across an
equality of realizing stages. -/
theorem stageIndEtale_of_stage_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    {S T : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    (hST : S = T) (hT : stageIndEtale (R := R) T.A) :
    stageIndEtale (R := R) S.A := by
  -- Rewrite the whole stage first, so the owner predicate sees the same ring and instances.
  subst S
  exact hT

/-- Helper for Chap10 Lemma 10 159 2: the successor stage selector preserves the ind-étale
owner, using the old-chain owners below `α` and the supplied owner at the new top stage. -/
theorem successorPrefixStage_indEtale
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (howner : ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A)
    (htopOwner : stageIndEtale (R := R) Ttop.A) :
    ∀ β : Set.Iic (α + 1),
      stageIndEtale (R := R)
        (successorPrefixStage (R := R) (K := K) hα C Ttop β).A := by
  intro β
  -- Split the successor interval into old stages below `α` and the new top stage.
  by_cases hβ : β.1 ≤ α
  · have hcast :
        stageIndEtale (R := R)
          (successor_stage_of_below_top (R := R) (K := K) hα C β hβ).A := by
      -- The below branch is only the old stage transported along the prefix-field equality.
      exact
        stageIndEtale_of_stage_cast_eq (R := R) (K := K)
          (closedPrefixField_succ_below_top_eq (R := R) (K := K) hα β hβ).symm
          (C.stage ⟨β.1, hβ⟩) (howner ⟨β.1, hβ⟩)
    exact
      stageIndEtale_of_stage_eq (R := R) (K := K)
        (successorPrefixStage_below (R := R) (K := K) hα C Ttop β hβ) hcast
  · have hβtop :
        β = (⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩ : Set.Iic (α + 1)) := by
      simpa using successor_eq_top_of_not_le (R := R) (K := K) β hβ
    subst β
    -- At the successor top, the selector returns exactly the supplied top stage.
    simpa using
      stageIndEtale_of_stage_eq (R := R) (K := K)
        (successorPrefixStage_top (R := R) (K := K) hα C Ttop) htopOwner

/-- Helper for Chap10 Lemma 10 159 2: the base-stage morphism into the old zero stage also
lands in the zero stage of the successor selector. -/
theorem successorPrefixStage_baseHom
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩))) :
    Nonempty
      (ResidueExtensionStage.Hom
        (show (⊥ : IntermediateField (ResidueField R) K) ≤
            closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
              ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ by
            simpa [closedPrefixField, wellOrder_prefixField_zero])
        (ResidueExtensionStage.base (R := R) K)
        (successorPrefixStage (R := R) (K := K) hα C Ttop
          ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩)) := by
  -- The successor zero index is below `α`, so the stage selector normalizes to the transported
  -- old zero stage and the original base morphism applies.
  have hzeroNot : ¬ (0 : Ordinal) = α + 1 := by
    intro hzero
    have hpos : (0 : Ordinal.{w}) < 0 := by
      calc
        (0 : Ordinal.{w}) < α + 1 := lt_of_le_of_lt bot_le (Order.lt_succ α)
        _ = 0 := hzero.symm
    exact (not_lt_of_ge le_rfl) hpos
  simpa [successorPrefixStage, successor_stage_of_below_top, successor_below_of_not_top,
    closedPrefixField_succ_below_top_eq, hzeroNot] using hbase

/-- Helper for Lemma 10.159.2: between two indices that both stay below the successor top, the
successor-chain transition map is exactly the inherited map from the old chain. -/
theorem successor_hom_of_below_below
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    {β γ : Set.Iic (α + 1)} (hβ : β.1 ≤ α) (hγ : γ.1 ≤ α) (hβγ : β ≤ γ) :
    Nonempty
      (ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans β.2 (Order.succ_le_of_lt hα))
          (le_trans γ.2 (Order.succ_le_of_lt hα)) hβγ)
        (successor_stage_of_below_top (R := R) (K := K) hα C β hβ)
        (successor_stage_of_below_top (R := R) (K := K) hα C γ hγ)) := by
  -- Normalize both successor endpoints back to the old chain, where the required map is already
  -- stored as `C.hom`.
  refine ⟨?_⟩
  simpa [successor_stage_of_below_top, closedPrefixField_succ_below_top_eq] using
    (C.hom (β := ⟨β.1, hβ⟩) (γ := ⟨γ.1, hγ⟩) hβγ)

/-- Helper for Lemma 10.159.2: from an old stage below the successor top, the successor-chain map
to the new top stage is the inherited old map into `C.topStage`, followed by `htop`. -/
theorem successor_hom_of_below_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (htop :
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage Ttop))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    Nonempty
      (ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans β.2 (Order.succ_le_of_lt hα))
          (Order.succ_le_of_lt hα) (show β.1 ≤ α + 1 from β.2))
        (successor_stage_of_below_top (R := R) (K := K) hα C β hβ)
        Ttop) := by
  classical
  let htop' := Classical.choice htop
  -- Compose the inherited map into the old top stage with the chosen successor top map.
  have hOld :
      ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans hβ (le_of_lt hα))
          (le_of_lt hα) hβ)
        (C.stage ⟨β.1, hβ⟩) C.topStage := by
    simpa [PrefixStageChain.topStage] using
      (C.hom (β := ⟨β.1, hβ⟩) (γ := ⟨α, by simp⟩) hβ)
  -- After normalizing the source field, the composite is exactly the desired below-top branch.
  refine ⟨?_⟩
  simpa [successor_stage_of_below_top, closedPrefixField_succ_below_top_eq] using
    ResidueExtensionStage.Hom.comp hOld htop'

/-
Route correction: the detailed successor transport API above turned into a large block of
proof-irrelevant endpoint bookkeeping. For the present item, the only mathematically meaningful
successor-side frontier is the final chain constructor `prefixStageChain_succ_of_top_hom` below.
-/
/-- Helper for Lemma 10.159.2: a stage over one target intermediate field, together with an
incoming morphism and the carried ind-étale owner, can be transported across an equality of target
fields without changing the underlying ring data. -/
theorem hom_transport_target_of_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M M' : IntermediateField (ResidueField R) K}
    {hLM : L ≤ M} {hLM' : L ≤ M'}
    (S : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K M)
    (e : M' = M)
    (hHom : Nonempty (ResidueExtensionStage.Hom hLM S T))
    (howner : stageIndEtale (R := R) T.A) :
    ∃ T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M',
      Nonempty (ResidueExtensionStage.Hom hLM' S T') ∧
      stageIndEtale (R := R) T'.A := by
  -- Rewrite the target field first so the only remaining change is proof-irrelevant data in the
  -- inclusion proof carried by the morphism witness.
  subst M'
  exact ⟨T, by simpa using hHom, howner⟩

/-- Helper for Lemma 10.159.2: after transporting the successor top field to
`closedPrefixField ... ⟨α + 1, le_rfl⟩`, the raw successor-stage existence theorem still provides
the incoming morphism from the previous top stage together with the ind-étale owner. -/
theorem successor_top_stage_hom_exists_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A) :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩),
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage T) ∧
      stageIndEtale (R := R) T.A := by
  -- Route correction: transport the whole successor package at theorem level, rather than trying
  -- to cast the raw `ResidueExtensionStage.Hom` witness inside a term.
  rcases exists_successor_adjoin_top_stage_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨T, hHom, hT⟩
  exact
    hom_transport_target_of_eq (R := R) (K := K) C.topStage T
      (successor_closedPrefixField_eq_adjoin (R := R) (K := K) hα)
      hHom hT

/-- Helper for Lemma 10.159.2: once a successor top stage with an incoming morphism from the old
top stage is known, the full closed prefix chain on `α + 1` is obtained by keeping the old stages
below `α` and composing their maps into the new top stage. -/
theorem prefixStageChain_succ_of_top_hom
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A)
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (htop :
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage Ttop))
    (htopOwner : stageIndEtale (R := R) Ttop.A) :
    ∃ Csucc : PrefixStageChain (R := R) K (α + 1) (Order.succ_le_of_lt hα),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (Csucc.stage ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩)) ∧
      ∀ β : Set.Iic (α + 1), stageIndEtale (R := R) (Csucc.stage β).A := by
  classical
  -- Route correction: split successor indices by equality with the new top, then use `copyLe`
  -- so transition maps keep the same algebra-map projections as the old chain or top composite.
  let htop' := Classical.choice htop
  let βtopSucc : Set.Iic (α + 1) := ⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩
  let βtopOld : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  let lowerOfNeTop : (β : Set.Iic (α + 1)) → β ≠ βtopSucc → Set.Iic α :=
    fun β hβ ↦
      ⟨β.1, successorIndex_le_of_ne_top_filteredColimit (R := R) (K := K) β
        (by simpa [βtopSucc] using hβ)⟩
  have lowerOfNeTop_le_top :
      ∀ (β : Set.Iic (α + 1)) (hβ : β ≠ βtopSucc),
        lowerOfNeTop β hβ ≤ βtopOld := by
    intro β hβ
    exact (lowerOfNeTop β hβ).2
  have ne_top_of_le_ne_top :
      ∀ {β γ : Set.Iic (α + 1)}, β ≤ γ → γ ≠ βtopSucc → β ≠ βtopSucc := by
    intro β γ hβγ hγ
    exact successorIndex_ne_top_of_le_ne_top_filteredColimit (R := R) (K := K) hβγ
      (by simpa [βtopSucc] using hγ)
  let stageSucc :
      (β : Set.Iic (α + 1)) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K
          (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β) :=
    fun β ↦ by
      -- The top branch is the supplied new stage; every other index is an old stage.
      by_cases hβtop : β = βtopSucc
      · subst β
        exact Ttop
      · exact successor_stage_of_below_top (R := R) (K := K) hα C β
          (successorIndex_le_of_ne_top_filteredColimit (R := R) (K := K) β
            (by simpa [βtopSucc] using hβtop))
  let homSucc :
      {β γ : Set.Iic (α + 1)} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom.{u, w, max u w, max u w}
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2 (Order.succ_le_of_lt hα))
              (le_trans γ.2 (Order.succ_le_of_lt hα)) hβγ)
            (stageSucc β) (stageSucc γ) :=
    fun {β γ} hβγ ↦ by
      -- Each branch builds the stage morphism in the expected endpoint spelling, so later
      -- projections see the chosen algebra map instead of a casted whole morphism.
      by_cases hγtop : γ = βtopSucc
      · subst γ
        by_cases hβtop : β = βtopSucc
        · subst β
          dsimp [stageSucc]
          rw [dif_pos rfl]
          let g := ResidueExtensionStage.Hom.id (R := R) (K := K) Ttop
          exact
            { toAlgHom := g.toAlgHom
              isLocalHom := g.isLocalHom
              residue_comm := g.residue_comm }
        · dsimp [stageSucc]
          rw [dif_neg hβtop, dif_pos rfl]
          let f := C.hom (β := lowerOfNeTop β hβtop) (γ := βtopOld)
            (lowerOfNeTop_le_top β hβtop)
          let g := f.comp htop'
          exact
            { toAlgHom := g.toAlgHom
              isLocalHom := g.isLocalHom
              residue_comm := g.residue_comm }
      · have hβtop : β ≠ βtopSucc := ne_top_of_le_ne_top hβγ hγtop
        dsimp [stageSucc]
        rw [dif_neg hβtop, dif_neg hγtop]
        let g := C.hom (β := lowerOfNeTop β hβtop) (γ := lowerOfNeTop γ hγtop) hβγ
        exact
          { toAlgHom := g.toAlgHom
            isLocalHom := g.isLocalHom
            residue_comm := g.residue_comm }
  -- Build the successor chain from the stable local selector and transition API above.
  refine ⟨?Csucc, ?_, ?_⟩
  · refine
      { stage := stageSucc
        hom := fun {β γ} hβγ ↦ homSucc hβγ
        hom_id := ?_
        hom_comp := ?_ }
    · intro β
      -- Identity transitions reduce to the old-chain identity away from top and to the top
      -- identity at the new endpoint.
      -- TODO: prove a transport-stable `.toAlgHom` projection lemma for `homSucc`: after the
      -- top/non-top split above, the remaining casts are only proof-irrelevant endpoint casts
      -- around `copyLeFilteredColimit`.
      sorry
    · intro β γ δ hβγ hγδ
      -- Composition is checked by the final target branch: below-top uses the old chain law,
      -- while maps ending at the new top factor through `htop'` and ordinary associativity.
      -- TODO: once the identity blocker above is solved by a cast-stability lemma, split on
      -- `δ = βtopSucc` and `γ = βtopSucc`. The lower/lower/lower branch is `C.hom_comp`; the
      -- lower/lower/top branch is `congrArg (fun f ↦ htop'.toAlgHom.comp f)` applied to
      -- `C.hom_comp`, followed by `AlgHom.comp_assoc`; top-identity branches close by the same
      -- transport-stable top identity lemma.
      sorry
  · -- The zero index remains below the successor top, so the old base morphism is reused.
    have hzero :
        (⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ : Set.Iic (α + 1)) ≠
          βtopSucc := by
      intro h
      have hval : (0 : Ordinal) = α + 1 := congrArg Subtype.val h
      have hpos : (0 : Ordinal) < 0 := by
        calc
          (0 : Ordinal) < α + 1 := lt_of_le_of_lt bot_le (Order.lt_succ α)
          _ = 0 := hval.symm
      exact (not_lt_of_ge le_rfl) hpos
    simpa [stageSucc, lowerOfNeTop, hzero, closedPrefixField_succ_below_top_eq, βtopSucc] using hbase
  · intro β
    -- The ind-étale owner is inherited below the new top and supplied directly at the top; the
    -- lower branch is routed through the named transported-stage normal form.
    by_cases hβtop : β = βtopSucc
    · subst β
      have hstage : stageSucc βtopSucc = Ttop := by
        simp [stageSucc]
      exact stageIndEtale_of_stage_eq (R := R) (K := K) hstage htopOwner
    · let hle : β.1 ≤ α :=
        successorIndex_le_of_ne_top_filteredColimit (R := R) (K := K) β
          (by simpa [βtopSucc] using hβtop)
      let Scast := successor_stage_of_below_top (R := R) (K := K) hα C β hle
      have hcast : stageIndEtale (R := R) Scast.A := by
        dsimp [Scast, successor_stage_of_below_top]
        exact
          stageIndEtale_of_stage_cast_eq (R := R) (K := K)
            (closedPrefixField_succ_below_top_eq (R := R) (K := K) hα β hle).symm
            (C.stage ⟨β.1, hle⟩) (howner ⟨β.1, hle⟩)
      have hstage : stageSucc β = Scast := by
        simp [stageSucc, hβtop, Scast]
      exact stageIndEtale_of_stage_eq (R := R) (K := K) hstage hcast

/-- Helper for Lemma 10.159.2: once the source-proof successor stage has been upgraded, the full
closed prefix chain on `α + 1` is obtained by keeping the old chain below `α` and composing the
old transition maps into the new top stage. -/
theorem exists_prefixStageChain_succ_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A) :
    ∃ Csucc : PrefixStageChain (R := R) K (α + 1) (Order.succ_le_of_lt hα),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (Csucc.stage ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩)) ∧
      ∀ β : Set.Iic (α + 1), stageIndEtale (R := R) (Csucc.stage β).A := by
  -- The successor chain is now a thin wrapper around the transported top-stage package and the
  -- structural constructor that inserts this new top stage.
  rcases successor_top_stage_hom_exists_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨Ttop, htop, htopOwner⟩
  exact
    prefixStageChain_succ_of_top_hom (R := R) (K := K) hα C hbase howner Ttop htop htopOwner

/-- Helper for Lemma 10.159.2: a coherent tower remembers, for each `β ≤ α`, a full closed prefix
chain up to `β`, together with the base-stage map, the ind-étale owner on every stage, and the
restriction compatibilities needed to compare the same transition map inside larger chains. -/
structure PrefixStageTower
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  chain :
    (β : Set.Iic α) →
      PrefixStageChain (R := R) K β.1 (le_trans β.2 hα)
  base :
    ∀ β : Set.Iic α,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_trans β.2 hα)
                ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          ((chain β).stage ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩))
  owner :
    ∀ β : Set.Iic α,
      ∀ δ : Set.Iic β.1, stageIndEtale (R := R) ((chain β).stage δ).A
  stage_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) (δ : Set.Iic β.1),
      (chain γ).stage
          ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩ =
        (chain β).stage δ
  hom_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) {δ ε : Set.Iic β.1} (hδε : δ ≤ ε),
      HEq
        (((chain γ).hom
          (β := ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩)
          (γ := ⟨ε.1, show ε.1 ≤ γ.1 from
            le_trans ε.2 (show β.1 ≤ γ.1 from hβγ)⟩) hδε).toAlgHom)
        (((chain β).hom (β := δ) (γ := ε) hδε).toAlgHom)

/-- Helper for Lemma 10.159.2: a recursive family of closed prefix chains yields the open system
of top stages on `Set.Iio α`, together with explicit transition maps, the identity law on each
open stage, and the carried ind-etale owners available before the final limit-stage coherence is
packaged. -/
theorem limit_recursive_family_to_open_top_stage_system
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : ∀ β : Set.Iio α,
      PrefixStageChain (R := R) K β.1 (le_trans β.2.le hα))
    (hrestrict :
      ∀ {β γ : Set.Iio α} (hβγ : β ≤ γ),
        (C γ).stage ⟨β.1, hβγ⟩ =
          by
            simpa [PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
              (C β).topStage)
    (howner :
      ∀ β : Set.Iio α,
        ∀ δ : Set.Iic β.1, stageIndEtale (R := R) ((C β).stage δ).A) :
    ∃ S : (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β),
      ∃ hom :
        {β γ : Set.Iio α} →
          (hβγ : β ≤ γ) →
            ResidueExtensionStage.Hom
              (wellOrder_prefixField_mono (R := R) (K := K)
                (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
              (S β) (S γ),
        (∀ β : Set.Iio α,
          (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A) ∧
        ∀ β : Set.Iio α, stageIndEtale (R := R) (S β).A := by
  let S :
      (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β) :=
    fun β ↦ by
      -- Reinterpret the top stage of the recursive chain at `β` as the open stage indexed by `β`.
      simpa [PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
        (C β).topStage
  let hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ) :=
    fun {β γ} hβγ ↦ by
      -- The transition map from `β` to `γ` is already stored inside the larger chain `C γ`.
      simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField, hrestrict hβγ] using
        (C γ).hom (β := ⟨β.1, hβγ⟩) (γ := ⟨γ.1, show γ.1 ≤ γ.1 from le_rfl⟩) hβγ
  refine ⟨S, hom, ?_, ?_⟩
  · intro β
    -- At a fixed open stage, the chosen transition map is the identity map stored in `C β`.
    dsimp [hom]
    simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
      (C β).hom_id ⟨β.1, show β.1 ≤ β.1 from le_rfl⟩
  · intro β
    -- Read the ind-étale owner off the top stage of the recursive chain at `β`.
    simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
      howner β ⟨β.1, show β.1 ≤ β.1 from le_rfl⟩

/-- Helper for Lemma 10.159.2: a coherent prefix-stage tower yields the open-stage system below a
limit ordinal, now with the composition law needed for the direct-limit package. -/
theorem coherent_prefixStageTower_to_open_top_stage_system
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (T : PrefixStageTower (R := R) K α hα) :
    ∃ S : (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β),
      ∃ hom :
        {β γ : Set.Iio α} →
          (hβγ : β ≤ γ) →
            ResidueExtensionStage.Hom
              (wellOrder_prefixField_mono (R := R) (K := K)
                (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
              (S β) (S γ),
        (∀ β : Set.Iio α,
          (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A) ∧
        (∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
          ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
              (hom (β := β) (γ := γ) hβγ).toAlgHom) =
            (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom) ∧
        ∀ β : Set.Iio α, stageIndEtale (R := R) (S β).A := by
  let _ := hlimit
  let top : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  let S :
      (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β) :=
    fun β ↦ by
      -- Read the open stage directly from the top closed chain stored in the tower.
      simpa [top, openPrefixField, closedPrefixField] using
        (T.chain top).stage ⟨β.1, show β.1 ≤ α from β.2.le⟩
  let hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ) :=
    fun {β γ} hβγ ↦ by
      -- Every open transition map is already present in the top closed chain.
      simpa [top, S, openPrefixField, closedPrefixField] using
        (T.chain top).hom
          (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
          (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩) hβγ
  refine ⟨S, hom, ?_, ?_, ?_⟩
  · intro β
    -- The self-map at an open stage is the identity map stored in the top closed chain.
    dsimp [hom]
    simpa [top, S, openPrefixField, closedPrefixField] using
      (T.chain top).hom_id ⟨β.1, show β.1 ≤ α from β.2.le⟩
  · intro β γ δ hβγ hγδ
    -- Route correction: work entirely inside the top closed chain, where the composition law is
    -- already part of the stored `PrefixStageChain` data.
    simpa [top, S, openPrefixField, closedPrefixField] using
      (T.chain top).hom_comp
        (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
        (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩)
        (δ := ⟨δ.1, show δ.1 ≤ α from δ.2.le⟩) hβγ hγδ
  · intro β
    -- Read the ind-étale owner off the corresponding stage of the top closed chain.
    simpa [top, S, openPrefixField, closedPrefixField] using
      T.owner top ⟨β.1, show β.1 ≤ α from β.2.le⟩

/-- Helper for Lemma 10.159.2: a coherent family of open-stage morphisms yields the directed
system of the underlying stage rings needed for `Ring.DirectLimit`. -/
theorem open_top_stage_transition_directedSystem
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    {S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β)}
    (hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    (hom_id : ∀ β : Set.Iio α,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A)
    (hom_comp :
      ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
        ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
            (hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom) :
    DirectedSystem
      (fun β : Set.Iio α ↦ (S β).A)
      (fun β γ hβγ ↦ (hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom) := by
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro β x
    -- The chosen self-map is definitionally the identity on the underlying stage ring.
    change (hom (β := β) (γ := β) le_rfl).toAlgHom x = x
    simpa using congrArg (fun f : (S β).A →ₐ[R] (S β).A ↦ f x) (hom_id β)
  · intro δ γ β hβγ hγδ x
    -- Composition in the directed system is the underlying ring-hom form of the stored
    -- algebra-hom composition law.
    change (hom (β := γ) (γ := δ) hγδ).toAlgHom
        ((hom (β := β) (γ := γ) hβγ).toAlgHom x) =
      (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom x
    exact congrArg (fun f : (S β).A →ₐ[R] (S δ).A ↦ f x) (hom_comp hβγ hγδ)

/-- Helper for Chap10 Lemma 10 159 2: composing inclusions of intermediate fields agrees with
the direct inclusion along the transitive containment. -/
theorem intermediateField_inclusion_comp_toRingHom
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M N : IntermediateField (ResidueField R) K}
    (hLM : L ≤ M) (hMN : M ≤ N) :
    ((IntermediateField.inclusion hMN).toRingHom.comp
        (IntermediateField.inclusion hLM).toRingHom) =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom := by
  -- Both homomorphisms are the same inclusion into the ambient field.
  apply RingHom.ext
  intro x
  rfl

/-- Helper for Chap10 Lemma 10 159 2: the intrinsic compatibility of a stage morphism gives
equality of the two induced ambient `K`-values after coercing through the target intermediate
field. -/
theorem ResidueExtensionStage.Hom.toIntermediateFieldHom_comm_val
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K} {hLM : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom hLM S T) (x : S.A) :
    (((T.toIntermediateFieldHom (f.toAlgHom x) : M) : K) =
      ((S.toIntermediateFieldHom x : L) : K)) := by
  -- Evaluate the stored quotient-map square at `x` and then forget both intermediate-field
  -- subtypes to the common ambient field.
  have h :=
    congrArg (fun φ : S.A →+* M ↦ φ x) f.toIntermediateFieldHom_comm
  simpa [RingHom.comp_apply] using congrArg Subtype.val h

/-- Helper for Chap10 Lemma 10 159 2: a stage morphism remains compatible with quotient maps
after both sides are composed with an inclusion into a larger intermediate field. -/
theorem ResidueExtensionStage.Hom.toIntermediateFieldHom_comm_comp_inclusion
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M N : IntermediateField (ResidueField R) K}
    {hLM : L ≤ M} (hMN : M ≤ N)
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom hLM S T) :
    ((IntermediateField.inclusion hMN).toRingHom.comp T.toIntermediateFieldHom).comp
        f.toAlgHom.toRingHom =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom.comp
        S.toIntermediateFieldHom := by
  -- Normalize composition of ring homomorphisms first, then use the intrinsic stage-morphism
  -- square and the elementary transitivity of intermediate-field inclusions.
  calc
    ((IntermediateField.inclusion hMN).toRingHom.comp T.toIntermediateFieldHom).comp
        f.toAlgHom.toRingHom
        =
      (IntermediateField.inclusion hMN).toRingHom.comp
        (T.toIntermediateFieldHom.comp f.toAlgHom.toRingHom) := by
          rfl
    _ =
      (IntermediateField.inclusion hMN).toRingHom.comp
        ((IntermediateField.inclusion hLM).toRingHom.comp S.toIntermediateFieldHom) := by
          rw [f.toIntermediateFieldHom_comm]
    _ =
      ((IntermediateField.inclusion hMN).toRingHom.comp
        (IntermediateField.inclusion hLM).toRingHom).comp S.toIntermediateFieldHom := by
          rfl
    _ =
      (IntermediateField.inclusion (le_trans hLM hMN)).toRingHom.comp
        S.toIntermediateFieldHom := by
          rw [intermediateField_inclusion_comp_toRingHom (R := R) (K := K) hLM hMN]

/-- Helper for Lemma 10.159.2: after composing each open-stage quotient map with the canonical
inclusion into the limit prefix field, the resulting maps are compatible with the open-stage
transition morphisms. This is the field-side descent datum needed for the later direct-limit
comparison map. -/
theorem limit_stage_toIntermediateFieldHom_comm
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    {S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β)}
    (hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    {β γ : Set.Iio α} (hβγ : β ≤ γ) :
    (((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans γ.2.le hα) hα γ.2.le)).toRingHom).comp
        (S γ).toIntermediateFieldHom).comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom
      =
    ((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) hα β.2.le)).toRingHom).comp
        (S β).toIntermediateFieldHom := by
  -- Route correction: consume the generic composed-inclusion compatibility lemma, avoiding the
  -- previous kernel-heavy pointwise `Subtype.ext` term in this limit-specific theorem.
  simpa using
    ResidueExtensionStage.Hom.toIntermediateFieldHom_comm_comp_inclusion (R := R) (K := K)
      (hMN := wellOrder_prefixField_mono (R := R) (K := K)
        (le_trans γ.2.le hα) hα γ.2.le)
      (hom (β := β) (γ := γ) hβγ)

/-- Helper for Chap10 Lemma 10 159 2: a closed-prefix index at a limit stage is either the top
index or an open index below it. -/
theorem limitIndex_eq_top_or_lt
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic α) :
    β.1 = α ∨ β.1 < α := by
  -- Split by equality with the endpoint; non-equality upgrades the interval bound to strictness.
  by_cases hβ : β.1 = α
  · exact Or.inl hβ
  · exact Or.inr (lt_of_le_of_ne β.2 hβ)

/-- Helper for Chap10 Lemma 10 159 2: a closed-prefix field at an index strictly below a limit
ordinal is the corresponding open-prefix field. -/
theorem closedPrefixField_limit_lt_eq_openPrefixField
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic α) (hβ : β.1 < α) :
    closedPrefixField (R := R) K hα β =
      openPrefixField (R := R) K hα ⟨β.1, hβ⟩ := by
  -- Both fields are the same well-ordered prefix field; only the proof of the ambient bound is
  -- different.
  simpa [closedPrefixField, openPrefixField] using
    (wellOrder_prefixField_proof_irrel (R := R) (K := K)
      (α := β.1)
      (h₁ := le_trans β.2 hα)
      (h₂ := le_trans hβ.le hα))

/-- Helper for Lemma 10.159.2: once the limit branch already has a coherent open-stage system
below `α`, a compatible top stage, and the stagewise ind-étale owners, those data assemble into
the closed prefix chain required at the limit ordinal itself. -/
theorem assemble_limit_prefixStageChain_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β))
    (open_hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    (open_hom_id : ∀ β : Set.Iio α,
      (open_hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A)
    (open_hom_comp :
      ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
        ((open_hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
            (open_hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (open_hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom)
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K hα
        (⟨α, show α ≤ α from le_rfl⟩ : Set.Iic α)))
    (top_hom :
      (β : Set.Iio α) →
        ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) hα β.2.le)
          (S β) Ttop)
    (top_hom_comp :
      ∀ {β γ : Set.Iio α} (hβγ : β ≤ γ),
        ((top_hom γ).toAlgHom.comp (open_hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (top_hom β).toAlgHom)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              openPrefixField (R := R) K hα ⟨0, hlimit.bot_lt⟩ by
              simpa [openPrefixField, closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (S ⟨0, hlimit.bot_lt⟩)))
    (howner_open : ∀ β : Set.Iio α, stageIndEtale (R := R) (S β).A)
    (howner_top : stageIndEtale (R := R) Ttop.A) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A := by
  -- TODO: the stage-by-stage case split is mathematically routine now: stages below `α` come from
  -- `S`, the top stage is `Ttop`, open-transition maps stay unchanged, and maps into the top stage
  -- use `top_hom`. The remaining work is to make those definitional transports between
  -- `openPrefixField` and `closedPrefixField` elaborate efficiently enough for Lean.
  sorry

/-- Helper for Lemma 10.159.2: once a single closed prefix chain has been constructed together
with the base map and the ind-étale owner on every stage, restricting that chain to smaller
ordinals already provides the full coherent tower required by the strengthened recursion. -/
theorem exists_prefixStageTower_of_prefixStageChain_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α hα)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A) :
    ∃ T : PrefixStageTower (R := R) K α hα, True := by
  -- The tower stores every initial segment of the already constructed chain `C`.
  refine ⟨?T, trivial⟩
  refine
    { chain := ?_
      base := ?_
      owner := ?_
      stage_restrict := ?_
      hom_restrict := ?_ }
  · intro β
    -- Restrict `C` to the closed interval below `β`.
    refine
      { stage := ?_
        hom := ?_
        hom_id := ?_
        hom_comp := ?_ }
    · intro δ
      exact C.stage ⟨δ.1, show δ.1 ≤ α from le_trans δ.2 β.2⟩
    · intro δ ε hδε
      exact C.hom
        (β := ⟨δ.1, show δ.1 ≤ α from le_trans δ.2 β.2⟩)
        (γ := ⟨ε.1, show ε.1 ≤ α from le_trans ε.2 β.2⟩) hδε
    · intro δ
      simpa using
        C.hom_id ⟨δ.1, show δ.1 ≤ α from le_trans δ.2 β.2⟩
    · intro δ ε ζ hδε hεζ
      simpa using
        C.hom_comp
          (β := ⟨δ.1, show δ.1 ≤ α from le_trans δ.2 β.2⟩)
          (γ := ⟨ε.1, show ε.1 ≤ α from le_trans ε.2 β.2⟩)
          (δ := ⟨ζ.1, show ζ.1 ≤ α from le_trans ζ.2 β.2⟩) hδε hεζ
  · intro β
    -- The base map is the base map of `C`, with only the proof of the zero index changed.
    simpa using hbase
  · intro β δ
    -- Owners are inherited from `C` at the corresponding global index.
    exact howner ⟨δ.1, show δ.1 ≤ α from le_trans δ.2 β.2⟩
  · intro β γ hβγ δ
    -- Both restricted stages are the same global stage of `C`.
    dsimp
  · intro β γ hβγ δ ε hδε
    -- The two restricted morphisms are the same morphism of `C`, up to the proof-irrelevant
    -- endpoints required by the tower API.
    exact HEq.rfl

/-- Helper for Chap10 Lemma 10 159 2: the universe-lifted identity stage ring is a filtered
colimit of étale `R`-algebras. -/
theorem stageIndEtale_lifted_base_ring :
    stageIndEtale (R := R) (ULift.{max u w, u} R) := by
  let A := ULift.{max u w, u} R
  letI : CommRing A := inferInstance
  letI : Algebra R A := inferInstance
  -- Unfold the ind-étale wrapper and use the one-object presentation of the identity up to
  -- `ULift`.
  dsimp [stageIndEtale, RingHom.IsFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap (ULift.{max u w} R) (ULift A)))
      (by
        dsimp [CommRingCat.etale]
        exact RingHom.Etale.of_bijective
          (by
            simpa using
              (ULift.ringEquiv.symm : ULift.{max u w} R ≃+* ULift A).bijective))

/-- Helper for Chap10 Lemma 10 159 2: the zero prefix field is realized by the universe-lifted
base stage, and that stage has an ind-étale structural map from `R`. -/
theorem exists_lifted_zero_prefix_stage_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊥ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by rfl)
          (ResidueExtensionStage.base (R := R) K) T) ∧
      stageIndEtale (R := R) T.A := by
  let A := ULift.{max u w, u} R
  letI : CommRing A := inferInstance
  letI : IsLocalRing A :=
    RingEquiv.isLocalRing (ULift.ringEquiv.symm : R ≃+* A)
  letI : Algebra R A := inferInstance
  have hlocal : IsLocalHom (algebraMap R A) := by
    change IsLocalHom (ULift.ringEquiv.symm.toRingHom : R →+* A)
    exact IsLocalHom.of_surjective
      (ULift.ringEquiv.symm.toRingHom : R →+* A)
      (show Function.Surjective (ULift.ringEquiv.symm.toRingHom : R →+* A) from
        ULift.ringEquiv.symm.surjective)
  have hflat : (algebraMap R A).Flat := by
    change RingHom.Flat (ULift.ringEquiv.symm.toRingHom : R →+* A)
    exact RingHom.Flat.of_bijective
      (f := (ULift.ringEquiv.symm.toRingHom : R →+* A))
      (show Function.Bijective (ULift.ringEquiv.symm.toRingHom : R →+* A) from
        ULift.ringEquiv.symm.bijective)
  have hmap : Ideal.map (algebraMap R A) (maximalIdeal R) = maximalIdeal A := by
    change Ideal.map (ULift.ringEquiv.symm.toRingHom : R →+* A)
        (maximalIdeal R) = maximalIdeal A
    exact IsLocalRing.map_ringEquiv_maximalIdeal
      (ULift.ringEquiv.symm : R ≃+* A)
  let eκ : ResidueField A ≃+* ResidueField R :=
    IsLocalRing.ResidueField.mapEquiv (ULift.ringEquiv : A ≃+* R)
  let T : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (⊥ : IntermediateField (ResidueField R) K) :=
    { A := A
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := hlocal
      flat := hflat
      map_maximalIdeal := hmap
      residueEquiv := eκ.trans (ResidueExtensionStage.base (R := R) K).residueEquiv }
  refine ⟨T, ?_, ?_⟩
  · refine ⟨?_⟩
    refine
      { toAlgHom :=
          { toRingHom := ULift.ringEquiv.symm.toRingHom
            commutes' := fun r ↦ rfl }
        isLocalHom := hlocal
        residue_comm := ?_ }
    -- The lifted base-stage map has the same residue-field map as the original base stage.
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  · -- The structural map `R → ULift R` is an isomorphism, hence étale and therefore ind-étale.
    simpa [A] using (stageIndEtale_lifted_base_ring (R := R) :
      stageIndEtale (R := R) (ULift.{max u w, u} R))

/-- Helper for Chap10 Lemma 10 159 2: the zero closed-prefix field is the bottom intermediate
field. -/
theorem closedPrefixField_zero_eq_bot_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (h0 : (0 : Ordinal) ≤ α) :
    closedPrefixField (R := R) K hα
      (⟨0, h0⟩ : Set.Iic α) = (⊥ : IntermediateField (ResidueField R) K) := by
  -- Normalize the proof-dependent zero prefix to the canonical zero prefix.
  dsimp [closedPrefixField]
  rw [wellOrder_prefixField_proof_irrel (R := R) (K := K)
    (h₁ := le_trans h0 hα)
    (h₂ := show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) by simp)]
  exact wellOrder_prefixField_zero (R := R) (K := K)

/-- Helper for Chap10 Lemma 10 159 2: a zero-stage package over `⊥` can be transported to any
field identified with `⊥` without changing its base morphism or ind-étale owner. -/
theorem stage_transport_from_bot_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (hL : L = (⊥ : IntermediateField (ResidueField R) K))
    {hbaseL : (⊥ : IntermediateField (ResidueField R) K) ≤ L}
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (⊥ : IntermediateField (ResidueField R) K))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by rfl)
          (ResidueExtensionStage.base (R := R) K) T))
    (howner : stageIndEtale (R := R) T.A) :
    ∃ T' : ResidueExtensionStage.{u, w, max u w} (R := R) K L,
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T') ∧
      stageIndEtale (R := R) T'.A := by
  -- Rewrite the target field first; the remaining base-morphism proof changes only by proof
  -- irrelevance in the inclusion witness.
  subst L
  exact ⟨T, by simpa using hbase, howner⟩

/-- Helper for Chap10 Lemma 10 159 2: the closed zero-prefix field has a lifted base-stage
realization with the base morphism and ind-étale owner already attached. -/
theorem exists_zero_closedPrefixStage_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (h0 : (0 : Ordinal) ≤ α) :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (closedPrefixField (R := R) K hα (⟨0, h0⟩ : Set.Iic α)),
      Nonempty
        (ResidueExtensionStage.Hom
          (base_le_prefixField (R := R) (K := K) (hα := le_trans h0 hα))
          (ResidueExtensionStage.base (R := R) K) T) ∧
      stageIndEtale (R := R) T.A := by
  -- Start from the lifted zero package over `⊥`, then transport along the zero-prefix
  -- normalization.
  rcases exists_lifted_zero_prefix_stage_with_filteredColimit (R := R) K with
    ⟨T, hbase, howner⟩
  exact stage_transport_from_bot_with_filteredColimit (R := R) (K := K)
    (L := closedPrefixField (R := R) K hα (⟨0, h0⟩ : Set.Iic α))
    (hL := closedPrefixField_zero_eq_bot_filteredColimit (R := R) (K := K) hα h0)
    (hbaseL := base_le_prefixField (R := R) (K := K) (hα := le_trans h0 hα))
    T hbase howner

/-- Helper for Lemma 10.159.2: the zero closed-prefix chain has only the base stage, and that
single stage already carries the ind-étale owner. -/
theorem exists_zero_prefixStageChain_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (h0 : (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ C : PrefixStageChain (R := R) K 0 h0,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K h0 ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩)) ∧
      ∀ β : Set.Iic (0 : Ordinal), stageIndEtale (R := R) (C.stage β).A := by
  let βzero : Set.Iic (0 : Ordinal) :=
    ⟨0, show (0 : Ordinal) ≤ (0 : Ordinal) from le_rfl⟩
  rcases exists_zero_closedPrefixStage_with_filteredColimit (R := R) K h0 le_rfl with
    ⟨Tzero, hbase, howner⟩
  have hsubsingleton : ∀ β : Set.Iic (0 : Ordinal), β = βzero := by
    intro β
    apply Subtype.ext
    exact le_antisymm β.2 bot_le
  -- Build the unique zero chain from the lifted base stage; all transition maps are identities.
  refine ⟨?C, ?_, ?_⟩
  · refine
      { stage := ?_
        hom := ?_
        hom_id := ?_
        hom_comp := ?_ }
    · intro β
      have hβ : β = βzero := hsubsingleton β
      subst β
      exact Tzero
    · intro β γ hβγ
      have hβ : β = βzero := hsubsingleton β
      have hγ : γ = βzero := hsubsingleton γ
      subst β
      subst γ
      simpa using ResidueExtensionStage.Hom.id (R := R) (K := K) Tzero
    · intro β
      have hβ : β = βzero := hsubsingleton β
      subst β
      simp [ResidueExtensionStage.Hom.id]
    · intro β γ δ hβγ hγδ
      have hβ : β = βzero := hsubsingleton β
      have hγ : γ = βzero := hsubsingleton γ
      have hδ : δ = βzero := hsubsingleton δ
      subst β
      subst γ
      subst δ
      simp [ResidueExtensionStage.Hom.id]
  · -- The base-to-zero map is the identity stage morphism after the zero-prefix normalization.
    simpa [βzero, closedPrefixField, wellOrder_prefixField_zero] using hbase
  · intro β
    have hβ : β = βzero := hsubsingleton β
    subst β
    simpa [βzero] using howner

/-- Helper for Lemma 10.159.2: at a succ-limit ordinal, the recursive family of smaller coherent
towers should be assembled into a single closed prefix chain whose stages still carry the
ind-étale owner. -/
theorem exists_prefixStageChain_limit_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (IH :
      ∀ β : Set.Iio α,
        ∃ T : PrefixStageTower (R := R) K β.1 (le_trans β.2.le hα), True) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A := by
  -- TODO: the source-faithful limit step now has its first field-side compatibility lemma
  -- (`limit_stage_toIntermediateFieldHom_comm`), and the final closed-chain assembly has been
  -- isolated in `assemble_limit_prefixStageChain_with_filteredColimit`. The remaining blocker is
  -- structural: the current hypothesis only supplies existential towers on each `β < α`,
  -- whereas the direct-limit package needs one coherent open-stage family on `Set.Iio α` and a
  -- compatible top stage before that assembly lemma can be applied.
  sorry

/-- Helper for Lemma 10.159.2: the source-proof transfinite recursion from Lemma `10.159.1`
should first be strengthened to a coherent closed prefix chain whose stage maps from `R` are
already filtered colimits of étale `R`-algebras, and whose zero stage is reached from the base
stage. -/
theorem exists_prefixStageTower_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ T : PrefixStageTower (R := R) K α hα, True := by
  -- TODO: this is the global recursion wrapper. The source-faithful decomposition is already in
  -- place, but the file is not yet back to a stable compiling frontier for the zero, successor,
  -- and limit constructor helpers it depends on.
  sorry

/-- Helper for Lemma 10.159.2: once the stronger coherent tower exists, the old chain-valued
statement is just its top-index projection. -/
theorem exists_prefixStageChain_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, stageIndEtale (R := R) (C.stage β).A := by
  rcases exists_prefixStageTower_with_filteredColimit (R := R) K α hα with ⟨T, -⟩
  let top : Set.Iic α := ⟨α, by simp⟩
  refine ⟨T.chain top, T.base top, ?_⟩
  intro β
  -- The stronger tower stores the ind-étale owner on every stage of the top chain.
  simpa [top] using T.owner top β

/-- Helper for Lemma 10.159.2: the terminal closed prefix field is `⊤`. This isolates the
one dependent cast needed when extracting the final stage from the recursive chain. -/
theorem closedPrefixField_top_eq_top
    (K : Type w) [Field K] [Algebra (ResidueField R) K] :
    closedPrefixField (R := R) K le_rfl
      (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
        Set.Iic (Ordinal.type (@WellOrderingRel K))) =
      (⊤ : IntermediateField (ResidueField R) K) := by
  -- Rewrite the proof-dependent closed prefix field to the terminal well-ordered prefix field.
  dsimp [closedPrefixField]
  rw [wellOrder_prefixField_proof_irrel (R := R) (K := K)
    (h₁ := le_trans (show Ordinal.type (@WellOrderingRel K) ≤
      Ordinal.type (@WellOrderingRel K) by exact le_rfl) le_rfl)
    (h₂ := le_rfl)]
  -- The source well-order construction reaches all of `K` at the terminal ordinal.
  simpa using wellOrder_prefixField_top (R := R) (K := K)

/-- Helper for Lemma 10.159.2: once the recursive chain has produced the terminal closed-prefix
stage, transporting that stage across `closedPrefixField_top_eq_top` gives the required stage over
`⊤` without changing the ring or its ind-étale owner. -/
theorem stage_transport_to_top
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (hL : L = (⊤ : IntermediateField (ResidueField R) K))
    {hbaseL : (⊥ : IntermediateField (ResidueField R) K) ≤ L}
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T))
    (howner : stageIndEtale (R := R) T.A) :
    ∃ Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) Ttop) ∧
      stageIndEtale (R := R) Ttop.A := by
  -- Rewrite the target field through the explicit variable `L`, so the dependent transport stays
  -- confined to this small helper.
  subst L
  refine ⟨T, ?_, howner⟩
  -- After the field rewrite, the base morphism is the original map with only proof-irrelevant data changed.
  simpa using hbase

/-- Helper for Lemma 10.159.2: once the recursive chain has produced the terminal closed-prefix
stage, transporting that stage across `closedPrefixField_top_eq_top` gives the required stage over
`⊤` without changing the ring or its ind-étale owner. -/
theorem closedPrefixField_top_stage_transport
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {hbaseL :
      (⊥ : IntermediateField (ResidueField R) K) ≤
        closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))}
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K le_rfl
        (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
          Set.Iic (Ordinal.type (@WellOrderingRel K)))))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T))
    (howner : stageIndEtale (R := R) T.A) :
    ∃ Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) Ttop) ∧
      stageIndEtale (R := R) Ttop.A := by
  -- Route correction: use the generic field-transport helper so the dependent cast happens on an
  -- explicit field variable rather than on the closed-prefix expression itself.
  exact
    stage_transport_to_top (R := R) (K := K)
      (L := closedPrefixField (R := R) K le_rfl
        (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
          Set.Iic (Ordinal.type (@WellOrderingRel K))))
      (hL := closedPrefixField_top_eq_top (R := R) (K := K))
      (T := T) hbase howner

/-- Helper for Lemma 10.159.2: once the strengthened prefix-chain recursion is available, the
top-stage theorem is just the terminal-stage extraction from that chain. -/
theorem exists_top_stage_with_filteredColimit_via_well_order_recursion
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) T) ∧
      stageIndEtale (R := R) T.A := by
  let αtop : Ordinal := Ordinal.type (@WellOrderingRel K)
  let βzero : Set.Iic αtop := ⟨0, by simp⟩
  let βtop : Set.Iic αtop := ⟨αtop, by simp⟩
  rcases exists_prefixStageChain_with_filteredColimit (R := R) K αtop le_rfl with
    ⟨C, hbase₀, howner⟩
  rcases hbase₀ with ⟨f₀⟩
  have hbaseTop :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl βtop by
                simpa [βtop, closedPrefixField] using
                  (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K)
          (C.stage βtop)) := by
    -- Follow the source route: first reach the zero stage from the base stage, then move along
    -- the coherent chain to the terminal stage.
    refine ⟨?_⟩
    simpa [βzero, βtop, closedPrefixField, wellOrder_prefixField_zero] using
      (f₀.comp (C.hom (β := βzero) (γ := βtop) bot_le))
  -- The terminal closed-prefix stage is now transported once to a stage over `⊤`.
  exact
    closedPrefixField_top_stage_transport (R := R) (K := K) (T := C.stage βtop)
      hbaseTop (howner βtop)

/-- Lemma 10.159.2: for a separable algebraic extension `K / ResidueField R`, there exists a
local `R`-algebra `R'` such that `R → R'` is a local map, `R'` is a filtered colimit of étale
`R`-algebras, and the residue field of `R'` is isomorphic to `K` over `ResidueField R`. -/
@[stacks 09E0]
theorem exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K] :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      stageIndEtale (R := R) R' := by
  -- Route correction: the public theorem is reduced to the strengthened top-stage recursion, and
  -- the residue-field unpacking is isolated in the helper above.
  have hT := exists_top_stage_with_filteredColimit_via_well_order_recursion (R := R) K
  exact
    exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv_of_top_stage
      (R := R) K hT

end
