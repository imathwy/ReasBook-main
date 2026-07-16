import Mathlib
import stacks_proof.stacks_project.Chap04.Example_4_22_6
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite OrderHom
open scoped BigOperators

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.87.4:
- primary domain: sequential inverse systems of abelian groups, their associated sequential
  pro-objects, and the Milnor presentations of `\varprojlim` and `R^1 \!\varprojlim`;
- sampled owner declarations:
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `exists_representative`,
  `represents_eq_iff_equivalent`,
  `derivedLimitDifferenceMap`,
  `limit`,
  `cokernel.map`;
- best owner abstraction: a morphism of the associated sequential pro-objects, written directly as
  the canonical Chapter 4 pro-object morphism type
  `colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor A ⋙ uliftFunctor.{0}`;
  a sequential representative is only bridge data used to construct the Milnor comparison maps;
- primitive data: the towers `A`, `B`, and the pro-morphism `η`;
- derived API: the induced maps on `limit A` and
  `SequentialInverseSystem.firstDerivedLimit A`, with representative-level `CommSq` and cokernel
  maps used only to descend those constructions from `η`.

Source/core/bridge triage:
- `source-facing`: the maps induced on `\varprojlim` and on `R^1 \!\varprojlim` by a morphism of
  pro-systems;
- `core/canonical`: `SequentialProObjectMorphismRep.toProObjectHom`, `limit`,
  `derivedLimitDifferenceMap`, and `cokernel.map`;
- `bridge/view`: the Milnor `CommSq` and the representative-level maps attached to a chosen
  sequential representative. -/

namespace SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}

/-- The representative-level map on inverse limits attached to a sequential representative of a
pro-system morphism. This is bridge data for the owner-level map `inducedLimitMap`. -/
def limitMap (r : SequentialProObjectMorphismRep A B) :
    limit A ⟶ limit B :=
  limit.pre A (toFunctor r.reindex).op ≫ limMap r.hom

/-- The induced map on inverse limits of a sequential representative is computed componentwise by
the representative-level maps. -/
theorem limitMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    r.limitMap ≫ limit.π B (op n) =
      limit.π A (op (r.reindex n)) ≫ r.map n := by
  rw [limitMap, Category.assoc, limMap_π, ← Category.assoc, limit.pre_π]
  simp [toFunctor]

/-- Helper for Lemma 15.87.4: the representative-level map on inverse limits attached to the
identity representative is the identity. -/
private theorem limitMap_idRep (A : SequentialInverseSystem C) :
    (SequentialProObjectMorphismRep.idRep A).limitMap = 𝟙 (limit A) := by
  -- Compare both maps after every limit projection of `A`.
  apply limit.hom_ext
  rintro ⟨n⟩
  -- The identity representative has identity reindexing and identity stage maps.
  calc
    (SequentialProObjectMorphismRep.idRep A).limitMap ≫ limit.π A (op n) =
        limit.π A (op ((OrderHom.id : ℕ →o ℕ) n)) ≫
          (SequentialProObjectMorphismRep.idRep A).map n := by
            simpa using
              (SequentialProObjectMorphismRep.limitMap_π
                (SequentialProObjectMorphismRep.idRep A) n)
    _ = limit.π A (op n) := by
          change limit.π A (op n) ≫ 𝟙 (A.obj (op n)) = limit.π A (op n)
          simp
    _ = 𝟙 (limit A) ≫ limit.π A (op n) := by
          simp

/-- Helper for Lemma 15.87.4: composing representatives composes their induced inverse-limit
maps. -/
private theorem limitMap_compRep
    {D : Type u} [Category.{v} D] [HasLimitsOfShape ℕᵒᵖ D]
    {A B C : SequentialInverseSystem D}
    (r : SequentialProObjectMorphismRep A B) (s : SequentialProObjectMorphismRep B C) :
    (SequentialProObjectMorphismRep.compRep r s).limitMap = r.limitMap ≫ s.limitMap := by
  -- Compare both maps after every limit projection of `C`.
  apply limit.hom_ext
  rintro ⟨m⟩
  calc
    (SequentialProObjectMorphismRep.compRep r s).limitMap ≫ limit.π C (op m) =
        limit.π A (op (r.reindex (s.reindex m))) ≫ r.map (s.reindex m) ≫ s.map m := by
          simpa [SequentialProObjectMorphismRep.compRep, Category.assoc] using
            (SequentialProObjectMorphismRep.limitMap_π
              (SequentialProObjectMorphismRep.compRep r s) m)
    _ = r.limitMap ≫ limit.π B (op (s.reindex m)) ≫ s.map m := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ s.map m)
              (SequentialProObjectMorphismRep.limitMap_π r (s.reindex m)).symm
    _ = r.limitMap ≫ (s.limitMap ≫ limit.π C (op m)) := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ r.limitMap ≫ t)
              (SequentialProObjectMorphismRep.limitMap_π s m).symm
    _ = (r.limitMap ≫ s.limitMap) ≫ limit.π C (op m) := by
          rw [Category.assoc]

-- Proof sketch: if two representatives define the same pro-object morphism, Example `4.22.6`
-- identifies them after common refinement; the Stacks Project argument shows that the induced map
-- on the canonical inverse-limit object is unchanged by passing to such a refinement.
/-- Representatives defining the same pro-object morphism induce the same map on inverse limits.
-/
private theorem limitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.limitMap = r₂.limitMap := by
  -- Pass to a common refinement and compare the limit maps after each projection of `limit B`.
  rcases (represents_eq_iff_equivalent r₁ r₂).1 h with ⟨reindex', h₁, h₂, hmaps⟩
  apply limit.hom_ext
  intro n
  let m := n.unop
  rw [limitMap_π, limitMap_π]
  calc
    limit.π A (op (r₁.reindex m)) ≫ r₁.map m =
        limit.π A (op (reindex' m)) ≫
          (A.map (homOfLE (h₁ m)).op ≫ r₁.map m) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ r₁.map m) (limit.w A (homOfLE (h₁ m)).op)
    _ = limit.π A (op (reindex' m)) ≫
          (A.map (homOfLE (h₂ m)).op ≫ r₂.map m) := by
            simp [m, hmaps m]
    _ = limit.π A (op (r₂.reindex m)) ≫ r₂.map m := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ r₂.map m) (limit.w A (homOfLE (h₂ m)).op).symm

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}

/-- Helper for Lemma 15.87.4: transition maps in a sequential inverse system compose in the
expected order. -/
private theorem transitionMap_comp
    (F : SequentialInverseSystem AddCommGrpCat.{v}) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (hij.trans hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- This is the functoriality of the inverse-system functor on the unique order morphisms.
  have hh :
      (homOfLE (hij.trans hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, hh] using
    (F.map_comp ((homOfLE hjk).op) ((homOfLE hij).op))

/-- Helper for Lemma 15.87.4: if two projection indices agree, then composing the corresponding
projection with the matching transition map is unchanged after transporting along that equality. -/
private theorem projection_transition_transport_eq
    (F : SequentialInverseSystem AddCommGrpCat.{v}) {m i j : ℕ}
    (hij : i = j) (hi : m ≤ i) (hj : m ≤ j) :
    Pi.π (inverseSystemFamily F) i ≫ F.transitionMap hi =
      Pi.π (inverseSystemFamily F) j ≫ F.transitionMap hj := by
  -- Route correction: the projected Milnor square only needs one stable rewrite for the dependent
  -- endpoint transport, so isolate that transport before returning to the source telescope.
  subst hij
  simpa using congrArg
    (fun h : m ≤ i ↦ Pi.π (inverseSystemFamily F) i ≫ F.transitionMap h)
    (Subsingleton.elim hi hj)

/-- The map on ambient products given by the component maps
`A_{m_n} ⟶ B_n` of a sequential representative. -/
private abbrev firstProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n

/-- Helper for Lemma 15.87.4: after enlarging the source stage of a representative at each target
index, the resulting first-product map is computed from the transported level maps. -/
private abbrev refinedFirstProductMap
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) (reindex' n) ≫ A.transitionMap (hle n) ≫ r.map n

/-- The `n`-th component of the second Milnor product map attached to a sequential representative,
given by summing the transition maps over the interval `[m_n, m_{n + 1})`. -/
private abbrev secondProductComponent (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (r.reindex (n + 1) - r.reindex n)) fun k ↦
    Pi.π (inverseSystemFamily A) (r.reindex n + k) ≫
      A.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.map n

/-- The second map on ambient products attached to a sequential representative, making the Milnor
square commute. -/
private def secondProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ secondProductComponent r n

/-- Helper for Lemma 15.87.4: after enlarging the chosen source stages of a representative, the
refinement-side second Milnor product component is obtained by summing the transported level maps
over the interval `[reindex' n, reindex' (n + 1))`. -/
private abbrev refinedSecondProductComponent
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n)
    (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (reindex' (n + 1) - reindex' n)) fun k ↦
    Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
      A.transitionMap ((hle n).trans (Nat.le_add_right (reindex' n) k)) ≫ r.map n

/-- Helper for Lemma 15.87.4: the refinement-side second Milnor product map is assembled from the
transported interval sums. -/
private def refinedSecondProductMap
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ refinedSecondProductComponent r reindex' hle n

/-- Helper for Lemma 15.87.4: the first Milnor product map is computed projectionwise. -/
private theorem firstProductMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n := by
  -- The `n`-th product projection picks out the `n`-th representative component.
  rw [firstProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.4: the refinement-side first-product map is computed projectionwise. -/
private theorem refinedFirstProductMap_π
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) (n : ℕ) :
    refinedFirstProductMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (reindex' n) ≫ A.transitionMap (hle n) ≫ r.map n := by
  -- The `n`-th product projection picks out the transported `n`-th representative component.
  rw [refinedFirstProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.4: the successor projection of the first Milnor product map is the
successor representative component. -/
private theorem firstProductMap_π_succ (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ Pi.π (inverseSystemFamily B) (n + 1) =
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫ r.map (n + 1) := by
  -- This is the projection formula specialized to the successor stage.
  simpa using firstProductMap_π r (n + 1)

/-- Helper for Lemma 15.87.4: the second Milnor product map is computed projectionwise. -/
private theorem secondProductMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    secondProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      secondProductComponent r n := by
  -- The `n`-th product projection picks out the `n`-th telescoping component.
  rw [secondProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.4: partitioning a finite interval according to a monotone sequence of
endpoints does not change the total sum. -/
private theorem sum_range_partition_by_monotone
    {α : Type*} [AddCommMonoid α]
    (g : ℕ → ℕ) (hg : Monotone g) (h0 : g 0 = 0) (q : ℕ) (f : ℕ → α) :
    Finset.sum (Finset.range q) (fun j ↦
      Finset.sum (Finset.range (g (j + 1) - g j)) fun k ↦
        f (g j + k)) =
      Finset.sum (Finset.range (g q)) f := by
  induction q with
  | zero =>
      -- The empty partition contributes no blocks, and `g 0 = 0` makes the target sum empty.
      simp [h0]
  | succ q ih =>
      -- Split off the last block and identify it with the tail interval `[g q, g (q + 1))`.
      rw [Finset.sum_range_succ, ih]
      have hq : g (q + 1) = g q + (g (q + 1) - g q) := by
        exact (Nat.add_sub_of_le (hg (Nat.le_succ q))).symm
      have hq' : g q + (g (q + 1) - g q) = g (q + 1) := by
        omega
      have hsplit :
          Finset.sum (Finset.range (g q + (g (q + 1) - g q))) f =
            Finset.sum (Finset.range (g q)) f +
              Finset.sum (Finset.range (g (q + 1) - g q)) fun k ↦ f (g q + k) :=
        Finset.sum_range_add (f := f) (n := g q) (m := g (q + 1) - g q)
      calc
        Finset.sum (Finset.range (g q)) f +
            Finset.sum (Finset.range (g (q + 1) - g q)) (fun k ↦ f (g q + k)) =
          Finset.sum (Finset.range (g q + (g (q + 1) - g q))) f := hsplit.symm
        _ = Finset.sum (Finset.range (g (q + 1))) f := by rw [hq']

/-- Helper for Lemma 15.87.4: the second Milnor product map attached to the identity
representative is the identity on the ambient product. -/
private theorem secondProductMap_idRep
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    secondProductMap (SequentialProObjectMorphismRep.idRep A) =
      𝟙 (∏ᶜ inverseSystemFamily A) := by
  -- TODO: normalize the dependent endpoint transport in `secondProductComponent (idRep A) n`,
  -- then identify the unique summand with `Pi.π (inverseSystemFamily A) n`.
  sorry

/-- Helper for Lemma 15.87.4: the `n`-th telescoping component of a composite representative is
obtained by composing the telescoping components of the two representatives. -/
private theorem secondProductComponent_compRep
    {C : SequentialInverseSystem AddCommGrpCat.{v}}
    (r : SequentialProObjectMorphismRep A B)
    (s : SequentialProObjectMorphismRep B C)
    (n : ℕ) :
    secondProductComponent (SequentialProObjectMorphismRep.compRep r s) n =
      secondProductMap r ≫ secondProductComponent s n := by
  -- TODO: compare the `n`-th projection of the composite with the block decomposition coming from
  -- `s`, rewrite each block through `r.comm`, and flatten the resulting partition of the interval.
  sorry

/-- Helper for Lemma 15.87.4: composing representatives composes the second Milnor product maps.
-/
private theorem secondProductMap_compRep
    {C : SequentialInverseSystem AddCommGrpCat.{v}}
    (r : SequentialProObjectMorphismRep A B)
    (s : SequentialProObjectMorphismRep B C) :
    secondProductMap (SequentialProObjectMorphismRep.compRep r s) =
      secondProductMap r ≫ secondProductMap s := by
  -- Compare the two ambient product maps after each target projection and reuse the componentwise
  -- block decomposition from `secondProductComponent_compRep`.
  apply Pi.hom_ext
  intro n
  calc
    secondProductMap (SequentialProObjectMorphismRep.compRep r s) ≫
        Pi.π (inverseSystemFamily C) n =
      secondProductComponent (SequentialProObjectMorphismRep.compRep r s) n := by
        rw [secondProductMap_π]
    _ = secondProductMap r ≫ secondProductComponent s n := by
        rw [secondProductComponent_compRep]
    _ = secondProductMap r ≫ (secondProductMap s ≫ Pi.π (inverseSystemFamily C) n) := by
        rw [secondProductMap_π]
    _ = (secondProductMap r ≫ secondProductMap s) ≫ Pi.π (inverseSystemFamily C) n := by
        rw [Category.assoc]

/-- Helper for Lemma 15.87.4: the successor projection of the second Milnor product map is the
successor telescoping component. -/
private theorem secondProductMap_π_succ (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    secondProductMap r ≫ Pi.π (inverseSystemFamily B) (n + 1) =
      secondProductComponent r (n + 1) := by
  -- This is the projection formula specialized to the successor stage.
  simpa using secondProductMap_π r (n + 1)

/-- Helper for Lemma 15.87.4: the refinement-side second Milnor product map is computed
projectionwise. -/
private theorem refinedSecondProductMap_π
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) (n : ℕ) :
    refinedSecondProductMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n =
      refinedSecondProductComponent r reindex' hle n := by
  -- The `n`-th product projection picks out the `n`-th transported interval sum.
  rw [refinedSecondProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.4: the finite sum of successive transported differences telescopes to
the two boundary terms. -/
private theorem transition_sum_telescope
    (A : SequentialInverseSystem AddCommGrpCat.{v}) (m c : ℕ) :
    Finset.sum (Finset.range c) (fun k ↦
      ((Pi.π (inverseSystemFamily A) (m + k) ≫
          A.transitionMap (Nat.le_add_right m k) :
            (∏ᶜ inverseSystemFamily A) ⟶ A.obj (op m)) -
        Pi.π (inverseSystemFamily A) (m + k + 1) ≫
          A.transitionMap (Nat.le_add_right m (k + 1)))) =
      Pi.π (inverseSystemFamily A) m -
        Pi.π (inverseSystemFamily A) (m + c) ≫
          A.transitionMap (Nat.le_add_right m c) := by
  induction c with
  | zero =>
      -- The empty interval contributes no summands, so only the initial boundary term remains.
      simp [SequentialInverseSystem.transitionMap]
  | succ c ih =>
      -- Split off the last summand and rewrite the new boundary via functoriality of transitions.
      rw [Finset.sum_range_succ, ih]
      have hcomp :
          A.transitionMap (Nat.le_add_right m (c + 1)) =
            A.transitionMap (Nat.le_succ (m + c)) ≫
              A.transitionMap (Nat.le_add_right m c) := by
        simpa [Nat.add_assoc] using
          transitionMap_comp A (Nat.le_add_right m c) (Nat.le_succ (m + c))
      -- After expressing the last transition as a composite, the middle terms cancel additively.
      have hsucc :
        Pi.π (inverseSystemFamily A) m -
            Pi.π (inverseSystemFamily A) (m + c) ≫
              A.transitionMap (Nat.le_add_right m c) +
          (Pi.π (inverseSystemFamily A) (m + c) ≫
              A.transitionMap (Nat.le_add_right m c) -
            Pi.π (inverseSystemFamily A) (m + c + 1) ≫
              A.transitionMap (Nat.le_add_right m (c + 1))) =
            Pi.π (inverseSystemFamily A) m -
              Pi.π (inverseSystemFamily A) (m + c + 1) ≫
                A.transitionMap (Nat.le_add_right m (c + 1)) := by
          calc
            Pi.π (inverseSystemFamily A) m -
                Pi.π (inverseSystemFamily A) (m + c) ≫
                  A.transitionMap (Nat.le_add_right m c) +
              (Pi.π (inverseSystemFamily A) (m + c) ≫
                  A.transitionMap (Nat.le_add_right m c) -
                Pi.π (inverseSystemFamily A) (m + c + 1) ≫
                  A.transitionMap (Nat.le_add_right m (c + 1))) =
                Pi.π (inverseSystemFamily A) m -
                  Pi.π (inverseSystemFamily A) (m + c + 1) ≫
                    A.transitionMap (Nat.le_succ (m + c)) ≫
                      A.transitionMap (Nat.le_add_right m c) := by
                    rw [hcomp]
                    simpa [Preadditive.sub_comp, sub_eq_add_neg, Category.assoc,
                      add_assoc, add_left_comm, add_comm]
            _ = Pi.π (inverseSystemFamily A) m -
                  Pi.π (inverseSystemFamily A) (m + c + 1) ≫
                    A.transitionMap (Nat.le_add_right m (c + 1)) := by
                      rw [← hcomp]
      convert hsucc using 1

-- Proof sketch: compare the `n`-th product projection on both sides. Expanding the definition of
-- `derivedLimitDifferenceMap` and the finite sum in `secondProductComponent`, the terms telescope,
-- and the compatibility relation `r.comm` identifies the remaining boundary terms with the
-- `n`-th component of `firstProductMap r ≫ derivedLimitDifferenceMap B`.
/-- Helper for Lemma 15.87.4: projecting the right side of the Milnor square along the `n`-th
product projection leaves only the two boundary terms coming from stages `n` and `n + 1`. -/
private theorem firstProductMap_comp_difference_projection
    (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ derivedLimitDifferenceMap B ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
  -- Expand the Milnor difference projection and read off the two relevant first-product terms.
  have hproj :
      firstProductMap r ≫ derivedLimitDifferenceMap B ≫ Pi.π (inverseSystemFamily B) n =
        firstProductMap r ≫
          (Pi.π (inverseSystemFamily B) n -
            Pi.π (inverseSystemFamily B) (n + 1) ≫ B.transitionMap (Nat.le_succ n)) := by
    simpa [Category.assoc, Preadditive.comp_sub] using
      congrArg (fun t ↦ firstProductMap r ≫ t) (derivedLimitDifferenceMap_comp_π B n)
  rw [Preadditive.comp_sub, firstProductMap_π] at hproj
  have hsucc_proj :
      firstProductMap r ≫ Pi.π (inverseSystemFamily B) (n + 1) ≫
          B.transitionMap (Nat.le_succ n) =
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ B.transitionMap (Nat.le_succ n))
        (firstProductMap_π_succ r n)
  rw [hsucc_proj] at hproj
  exact hproj

/-- Helper for Lemma 15.87.4: projecting the left side of the Milnor square along the `n`-th
product projection telescopes to the interval endpoints
`r.reindex n` and `r.reindex n + (r.reindex (n + 1) - r.reindex n)`. -/
private theorem secondProductMap_comp_difference_projection
    (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    derivedLimitDifferenceMap A ≫ secondProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A)
            (r.reindex n + (r.reindex (n + 1) - r.reindex n)) ≫
          A.transitionMap
            (Nat.le_add_right (r.reindex n) (r.reindex (n + 1) - r.reindex n)) ≫
          r.map n := by
  let m := r.reindex n
  let c := r.reindex (n + 1) - r.reindex n
  -- Project the second product map and rewrite each summand with the Milnor difference formula.
  rw [secondProductMap_π, secondProductComponent, Preadditive.comp_sum]
  have hsum :
      Finset.sum (Finset.range c) (fun k ↦
        derivedLimitDifferenceMap A ≫
          Pi.π (inverseSystemFamily A) (m + k) ≫
            A.transitionMap (Nat.le_add_right m k) ≫ r.map n) =
        Finset.sum (Finset.range c) (fun k ↦
          (((Pi.π (inverseSystemFamily A) (m + k) ≫
                A.transitionMap (Nat.le_add_right m k)) -
              Pi.π (inverseSystemFamily A) (m + k + 1) ≫
                A.transitionMap (Nat.le_add_right m (k + 1))) ≫
            r.map n)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hcomp :
        A.transitionMap (Nat.le_add_right m (k + 1)) =
          A.transitionMap (Nat.le_succ (m + k)) ≫ A.transitionMap (Nat.le_add_right m k) := by
      simpa [Nat.add_assoc] using
        transitionMap_comp A (Nat.le_add_right m k) (Nat.le_succ (m + k))
    -- Each projected Milnor difference term is one summand of the telescoping interval.
    calc
      derivedLimitDifferenceMap A ≫
          Pi.π (inverseSystemFamily A) (m + k) ≫
            A.transitionMap (Nat.le_add_right m k) ≫ r.map n =
        ((Pi.π (inverseSystemFamily A) (m + k) -
              Pi.π (inverseSystemFamily A) (m + k + 1) ≫
                A.transitionMap (Nat.le_succ (m + k))) ≫
            A.transitionMap (Nat.le_add_right m k)) ≫ r.map n := by
              simpa [Category.assoc] using
                (show
                  derivedLimitDifferenceMap A ≫
                      Pi.π (inverseSystemFamily A) (m + k) ≫
                        A.transitionMap (Nat.le_add_right m k) ≫ r.map n =
                    (Pi.π (inverseSystemFamily A) (m + k) -
                        Pi.π (inverseSystemFamily A) (m + k + 1) ≫
                          A.transitionMap (Nat.le_succ (m + k))) ≫
                      A.transitionMap (Nat.le_add_right m k) ≫
                        r.map n by
                          simp [Category.assoc])
      _ =
        (((Pi.π (inverseSystemFamily A) (m + k) ≫
              A.transitionMap (Nat.le_add_right m k)) -
            (Pi.π (inverseSystemFamily A) (m + k + 1) ≫
              A.transitionMap (Nat.le_succ (m + k)) ≫
                A.transitionMap (Nat.le_add_right m k))) ≫
          r.map n) := by
            simpa [Category.assoc] using
              (show
                (((Pi.π (inverseSystemFamily A) (m + k) -
                      Pi.π (inverseSystemFamily A) (m + k + 1) ≫
                        A.transitionMap (Nat.le_succ (m + k))) ≫
                    A.transitionMap (Nat.le_add_right m k)) ≫
                  r.map n) =
                (((Pi.π (inverseSystemFamily A) (m + k) ≫
                      A.transitionMap (Nat.le_add_right m k)) -
                    ((Pi.π (inverseSystemFamily A) (m + k + 1) ≫
                        A.transitionMap (Nat.le_succ (m + k))) ≫
                      A.transitionMap (Nat.le_add_right m k))) ≫
                  r.map n) by
                    simp [Preadditive.sub_comp, Category.assoc])
      _ =
        (((Pi.π (inverseSystemFamily A) (m + k) ≫
              A.transitionMap (Nat.le_add_right m k)) -
            Pi.π (inverseSystemFamily A) (m + k + 1) ≫
              A.transitionMap (Nat.le_add_right m (k + 1))) ≫
          r.map n) := by
            simp [Category.assoc, hcomp]
  rw [hsum]
  -- The finite sum now matches the source telescoping identity, postcomposed with `r.map n`.
  have htel :
      Finset.sum (Finset.range c) (fun k ↦
        (((Pi.π (inverseSystemFamily A) (m + k) ≫
              A.transitionMap (Nat.le_add_right m k)) -
            Pi.π (inverseSystemFamily A) (m + k + 1) ≫
              A.transitionMap (Nat.le_add_right m (k + 1))) ≫
          r.map n)) =
        (Pi.π (inverseSystemFamily A) m -
            Pi.π (inverseSystemFamily A) (m + c) ≫
              A.transitionMap (Nat.le_add_right m c)) ≫
          r.map n := by
    simpa [Preadditive.sum_comp, Preadditive.sub_comp, Category.assoc] using
      congrArg (fun t ↦ t ≫ r.map n) (transition_sum_telescope A m c)
  simpa [m, c, Preadditive.sub_comp, Category.assoc] using htel

/-- The two product maps attached to a sequential representative form a commutative square with
the Milnor difference maps. -/
private theorem milnorDifferenceCommSq (r : SequentialProObjectMorphismRep A B) :
    CommSq (derivedLimitDifferenceMap A) (firstProductMap r) (secondProductMap r)
      (derivedLimitDifferenceMap B) := by
  refine CommSq.mk ?_
  apply Pi.hom_ext
  intro n
  have hendpoint :
      Pi.π (inverseSystemFamily A)
          (r.reindex n + (r.reindex (n + 1) - r.reindex n)) ≫
        A.transitionMap
          (Nat.le_add_right (r.reindex n) (r.reindex (n + 1) - r.reindex n)) =
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
        A.transitionMap (r.reindex.monotone (Nat.le_succ n)) := by
    -- Rewrite the telescoping endpoint to the actual successor stage of the representative.
    exact projection_transition_transport_eq A
      (Nat.add_sub_of_le (r.reindex.monotone (Nat.le_succ n)))
      (Nat.le_add_right _ _) (r.reindex.monotone (Nat.le_succ n))
  have hcomm :
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          A.transitionMap (r.reindex.monotone (Nat.le_succ n)) ≫
            r.map n =
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
    -- The representative compatibility identifies the remaining endpoint with the right boundary.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫ t)
        (r.comm (Nat.le_succ n)).w
  have hendpoint_comp :
      Pi.π (inverseSystemFamily A)
          (r.reindex n + (r.reindex (n + 1) - r.reindex n)) ≫
        A.transitionMap
          (Nat.le_add_right (r.reindex n) (r.reindex (n + 1) - r.reindex n)) ≫
          r.map n =
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
        A.transitionMap (r.reindex.monotone (Nat.le_succ n)) ≫
          r.map n := by
    -- Postcompose the transport rewrite with `r.map n` so it can be used under subtraction.
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.map n) hendpoint
  -- Projecting both sides reduces the commutative-square claim to the two boundary formulas.
  calc
    derivedLimitDifferenceMap A ≫ secondProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A)
            (r.reindex n + (r.reindex (n + 1) - r.reindex n)) ≫
          A.transitionMap
            (Nat.le_add_right (r.reindex n) (r.reindex (n + 1) - r.reindex n)) ≫
          r.map n := by
            simpa [Category.assoc] using secondProductMap_comp_difference_projection r n
    _ =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          A.transitionMap (r.reindex.monotone (Nat.le_succ n)) ≫
            r.map n := by
              simpa using congrArg
                (fun t ↦ Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n - t)
                hendpoint_comp
    _ =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
            simpa using congrArg
              (fun t ↦ Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n - t)
              hcomm
    _ = firstProductMap r ≫ derivedLimitDifferenceMap B ≫ Pi.π (inverseSystemFamily B) n := by
          simpa [Category.assoc] using
            (firstProductMap_comp_difference_projection r n).symm

/-- The representative-level map on `R^1 \!\varprojlim`, obtained from the Milnor square attached
to a sequential representative. -/
abbrev firstDerivedLimitMap (r : SequentialProObjectMorphismRep A B) :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  cokernel.map (derivedLimitDifferenceMap A) (derivedLimitDifferenceMap B)
    (firstProductMap r) (secondProductMap r) (milnorDifferenceCommSq r).w

/-- Helper for Lemma 15.87.4: the representative-level map on `R^1 \!\varprojlim` attached to
the identity representative is the identity. -/
private theorem firstDerivedLimitMap_idRep
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    (SequentialProObjectMorphismRep.idRep A).firstDerivedLimitMap =
      𝟙 A.firstDerivedLimit := by
  -- Compare both maps after precomposition with the cokernel projection, where `cokernel.map`
  -- exposes the bottom horizontal map of the Milnor square.
  apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap A))).1
  simp [firstDerivedLimitMap, secondProductMap_idRep, Category.assoc]

/-- Helper for Lemma 15.87.4: composing representatives composes their induced maps on
`R^1 \!\varprojlim`. -/
private theorem firstDerivedLimitMap_compRep
    {C : SequentialInverseSystem AddCommGrpCat.{v}}
    (r : SequentialProObjectMorphismRep A B)
    (s : SequentialProObjectMorphismRep B C) :
    (SequentialProObjectMorphismRep.compRep r s).firstDerivedLimitMap =
      r.firstDerivedLimitMap ≫ s.firstDerivedLimitMap := by
  -- Compare both maps after precomposition with the source cokernel projection and use the
  -- representative-level composition law for `secondProductMap`.
  apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap A))).1
  calc
    cokernel.π (derivedLimitDifferenceMap A) ≫
        (SequentialProObjectMorphismRep.compRep r s).firstDerivedLimitMap =
      secondProductMap (SequentialProObjectMorphismRep.compRep r s) ≫
        cokernel.π (derivedLimitDifferenceMap C) := by
          simp [firstDerivedLimitMap]
    _ = (secondProductMap r ≫ secondProductMap s) ≫
          cokernel.π (derivedLimitDifferenceMap C) := by
            rw [secondProductMap_compRep]
    _ = secondProductMap r ≫
          (secondProductMap s ≫ cokernel.π (derivedLimitDifferenceMap C)) := by
            rw [Category.assoc]
    _ = secondProductMap r ≫
          (cokernel.π (derivedLimitDifferenceMap B) ≫ s.firstDerivedLimitMap) := by
            simp [firstDerivedLimitMap]
    _ = (cokernel.π (derivedLimitDifferenceMap A) ≫ r.firstDerivedLimitMap) ≫
          s.firstDerivedLimitMap := by
            simp [firstDerivedLimitMap, Category.assoc]
    _ = cokernel.π (derivedLimitDifferenceMap A) ≫
          (r.firstDerivedLimitMap ≫ s.firstDerivedLimitMap) := by
            rw [Category.assoc]

/-- Helper for Lemma 15.87.4: two representatives that become literally equal after transport to a
common refinement have equal refinement-side first-product maps. -/
private theorem refinedFirstProductMap_eq_of_equivalent
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    {reindex' : ℕ →o ℕ}
    (h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n)
    (h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n)
    (hmaps : ∀ n : ℕ,
      A.map (homOfLE (h₁ n)).op ≫ r₁.map n =
        A.map (homOfLE (h₂ n)).op ≫ r₂.map n) :
    refinedFirstProductMap r₁ reindex' h₁ = refinedFirstProductMap r₂ reindex' h₂ := by
  -- Compare the two refinement-side maps after each product projection of `B`.
  apply Pi.hom_ext
  intro n
  rw [refinedFirstProductMap_π, refinedFirstProductMap_π]
  -- The common-refinement hypothesis makes the transported level maps literally equal.
  simpa [Category.assoc] using
    congrArg
      (fun t ↦ Pi.π (inverseSystemFamily A) (reindex' n) ≫ t)
      (hmaps n)

/-- Helper for Lemma 15.87.4: two representatives that become literally equal after transport to a
common refinement have equal refinement-side second-product maps. -/
private theorem refinedSecondProductMap_eq_of_equivalent
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    {reindex' : ℕ →o ℕ}
    (h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n)
    (h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n)
    (hmaps : ∀ n : ℕ,
      A.map (homOfLE (h₁ n)).op ≫ r₁.map n =
        A.map (homOfLE (h₂ n)).op ≫ r₂.map n) :
    refinedSecondProductMap r₁ reindex' h₁ = refinedSecondProductMap r₂ reindex' h₂ := by
  -- Compare the two refinement-side maps after each product projection of `B`.
  apply Pi.hom_ext
  intro n
  rw [refinedSecondProductMap_π, refinedSecondProductMap_π, refinedSecondProductComponent,
    refinedSecondProductComponent]
  -- Each summand shares the same transition prefix, so the common-refinement hypothesis applies
  -- after rewriting the transported source stage by functoriality.
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hcomp₁ :
      A.transitionMap ((h₁ n).trans (Nat.le_add_right (reindex' n) k)) =
        A.transitionMap (Nat.le_add_right (reindex' n) k) ≫ A.transitionMap (h₁ n) := by
    simpa using transitionMap_comp A (h₁ n) (Nat.le_add_right (reindex' n) k)
  have hcomp₂ :
      A.transitionMap ((h₂ n).trans (Nat.le_add_right (reindex' n) k)) =
        A.transitionMap (Nat.le_add_right (reindex' n) k) ≫ A.transitionMap (h₂ n) := by
    simpa using transitionMap_comp A (h₂ n) (Nat.le_add_right (reindex' n) k)
  calc
    Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
        A.transitionMap ((h₁ n).trans (Nat.le_add_right (reindex' n) k)) ≫
          r₁.map n =
      Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
        A.transitionMap (Nat.le_add_right (reindex' n) k) ≫
          A.transitionMap (h₁ n) ≫ r₁.map n := by
            simp [hcomp₁, Category.assoc]
    _ =
      Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
        A.transitionMap (Nat.le_add_right (reindex' n) k) ≫
          A.transitionMap (h₂ n) ≫ r₂.map n := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
                    A.transitionMap (Nat.le_add_right (reindex' n) k) ≫ t)
                (hmaps n)
    _ =
      Pi.π (inverseSystemFamily A) (reindex' n + k) ≫
        A.transitionMap ((h₂ n).trans (Nat.le_add_right (reindex' n) k)) ≫
          r₂.map n := by
            simp [hcomp₂, Category.assoc]

/-- Helper for Lemma 15.87.4: the boundary correction at stage `n` for passing from `r.reindex n`
to a larger refinement stage `reindex' n`. -/
private abbrev refinementBoundaryComponent
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (reindex' n - r.reindex n)) fun k ↦
    Pi.π (inverseSystemFamily A) (r.reindex n + k) ≫
      A.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.map n

/-- Helper for Lemma 15.87.4: the boundary correction map assembled from the stagewise refinement
intervals. -/
private def refinementBoundaryMap
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (_hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ refinementBoundaryComponent r reindex' n

/-- Helper for Lemma 15.87.4: the boundary correction map is computed projectionwise. -/
private theorem refinementBoundaryMap_π
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n)
    (n : ℕ) :
    refinementBoundaryMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n =
      refinementBoundaryComponent r reindex' n := by
  -- The `n`-th product projection picks out the `n`-th refinement boundary component.
  rw [refinementBoundaryMap, Pi.lift_π]

/-- Helper for Lemma 15.87.4: the refinement boundary projects to the difference between the
original and refined `secondProductMap` components. -/
private theorem secondProductMap_refinement_boundary_projection
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n)
    (n : ℕ) :
    refinementBoundaryMap r reindex' hle ≫ derivedLimitDifferenceMap B ≫
        Pi.π (inverseSystemFamily B) n =
      secondProductMap r ≫ Pi.π (inverseSystemFamily B) n -
        refinedSecondProductMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n := by
  let a := r.reindex n
  let b := reindex' n
  let c := r.reindex (n + 1)
  let d := reindex' (n + 1)
  have hab_le : a ≤ b := by
    simpa [a, b] using hle n
  have hac_le : a ≤ c := by
    simpa [a, c] using r.reindex.monotone (Nat.le_succ n)
  have hbd_le : b ≤ d := by
    simpa [b, d] using reindex'.monotone (Nat.le_succ n)
  have hcd_le : c ≤ d := by
    simpa [c, d] using hle (n + 1)
  let term : ℕ → ((∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n)) := fun k ↦
    Pi.π (inverseSystemFamily A) (a + k) ≫ A.transitionMap (Nat.le_add_right a k) ≫ r.map n
  have hdiff :
      refinementBoundaryMap r reindex' hle ≫ derivedLimitDifferenceMap B ≫
          Pi.π (inverseSystemFamily B) n =
        refinementBoundaryMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n -
          refinementBoundaryMap r reindex' hle ≫
            Pi.π (inverseSystemFamily B) (n + 1) ≫
              B.transitionMap (Nat.le_succ n) := by
    -- Expand the Milnor difference at the `n`-th target projection.
    simpa [Category.assoc, Preadditive.comp_sub] using
      congrArg
        (fun t ↦ refinementBoundaryMap r reindex' hle ≫ t)
        (derivedLimitDifferenceMap_comp_π B n)
  have hboundary :
      refinementBoundaryMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n =
        Finset.sum (Finset.range (b - a)) fun k ↦ term k := by
    -- The boundary map at stage `n` is exactly the interval sum `[a, b)`.
    rw [refinementBoundaryMap_π, refinementBoundaryComponent]
  have hsecond :
      secondProductMap r ≫ Pi.π (inverseSystemFamily B) n =
        Finset.sum (Finset.range (c - a)) fun k ↦ term k := by
    -- The original second product map is the interval sum `[a, c)`.
    rw [secondProductMap_π, secondProductComponent]
  have hrefined :
      refinedSecondProductMap r reindex' hle ≫ Pi.π (inverseSystemFamily B) n =
        Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k) := by
    -- Transport the refined interval `[b, d)` back to the common base stage `a`.
    rw [refinedSecondProductMap_π, refinedSecondProductComponent]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hab :
        a + (b - a + k) = b + k := by
      omega
    have htransport :
        Pi.π (inverseSystemFamily A) (a + (b - a + k)) ≫
            A.transitionMap (Nat.le_add_right a (b - a + k)) =
          Pi.π (inverseSystemFamily A) (b + k) ≫
            A.transitionMap ((hle n).trans (Nat.le_add_right b k)) := by
      exact projection_transition_transport_eq A hab
        (Nat.le_add_right a (b - a + k))
        ((hle n).trans (Nat.le_add_right b k))
    -- Postcompose the transport rewrite with `r.map n` to identify the refined summand.
    simpa [term, Category.assoc] using
      congrArg (fun t ↦ t ≫ r.map n) htransport.symm
  have hshift :
      refinementBoundaryMap r reindex' hle ≫
          Pi.π (inverseSystemFamily B) (n + 1) ≫
            B.transitionMap (Nat.le_succ n) =
        Finset.sum (Finset.range (d - c)) fun k ↦ term (c - a + k) := by
    -- Rewrite the successor boundary component using the representative compatibility square, then
    -- transport its source stage back to the common base `a`.
    have hproj :
        refinementBoundaryMap r reindex' hle ≫
            Pi.π (inverseSystemFamily B) (n + 1) ≫
              B.transitionMap (Nat.le_succ n) =
          refinementBoundaryComponent r reindex' (n + 1) ≫
            B.transitionMap (Nat.le_succ n) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦ t ≫ B.transitionMap (Nat.le_succ n))
          (refinementBoundaryMap_π r reindex' hle (n + 1))
    rw [hproj, refinementBoundaryComponent, Preadditive.sum_comp]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hcomp :
        A.transitionMap
            ((r.reindex.monotone (Nat.le_succ n)).trans
              (Nat.le_add_right c k)) =
          A.transitionMap (Nat.le_add_right c k) ≫
            A.transitionMap (r.reindex.monotone (Nat.le_succ n)) := by
      simpa [c] using
        transitionMap_comp A
          (r.reindex.monotone (Nat.le_succ n))
          (Nat.le_add_right c k)
    have hcomm :
        Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap (Nat.le_add_right c k) ≫
              r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) =
          Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap
              ((r.reindex.monotone (Nat.le_succ n)).trans
                (Nat.le_add_right c k)) ≫
              r.map n := by
      calc
        Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap (Nat.le_add_right c k) ≫
              r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) =
          Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap (Nat.le_add_right c k) ≫
              (r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n)) := by
                simp
        _ =
          Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap (Nat.le_add_right c k) ≫
              (A.transitionMap (r.reindex.monotone (Nat.le_succ n)) ≫ r.map n) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      Pi.π (inverseSystemFamily A) (c + k) ≫
                        A.transitionMap (Nat.le_add_right c k) ≫ t)
                    (r.comm (Nat.le_succ n)).w.symm
        _ =
          Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap
              ((r.reindex.monotone (Nat.le_succ n)).trans
                (Nat.le_add_right c k)) ≫
              r.map n := by
                simp [hcomp, Category.assoc]
    have hac :
        a + (c - a + k) = c + k := by
      omega
    have htransport :
        Pi.π (inverseSystemFamily A) (a + (c - a + k)) ≫
            A.transitionMap (Nat.le_add_right a (c - a + k)) =
          Pi.π (inverseSystemFamily A) (c + k) ≫
            A.transitionMap
              ((r.reindex.monotone (Nat.le_succ n)).trans
                (Nat.le_add_right c k)) := by
      exact projection_transition_transport_eq A hac
        (Nat.le_add_right a (c - a + k))
        ((r.reindex.monotone (Nat.le_succ n)).trans
          (Nat.le_add_right c k))
    -- The successor boundary interval `[c, d)` becomes a shifted tail of the common interval
    -- `[a, d)`.
    calc
      Pi.π (inverseSystemFamily A) (c + k) ≫
          A.transitionMap (Nat.le_add_right c k) ≫
            r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) =
        Pi.π (inverseSystemFamily A) (c + k) ≫
          A.transitionMap
            ((r.reindex.monotone (Nat.le_succ n)).trans
              (Nat.le_add_right c k)) ≫
            r.map n := hcomm
      _ =
        Pi.π (inverseSystemFamily A) (a + (c - a + k)) ≫
          A.transitionMap (Nat.le_add_right a (c - a + k)) ≫
            r.map n := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ r.map n) htransport.symm
      _ = term (c - a + k) := by
            rfl
  have hsplit_boundary :
      Finset.sum (Finset.range (d - a)) term =
        Finset.sum (Finset.range (b - a)) term +
          Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k) := by
    -- Split the full interval `[a, d)` at the refinement point `b`.
    have hlen : d - a = (b - a) + (d - b) := by
      omega
    simpa [hlen] using
      (Finset.sum_range_add (f := term) (n := b - a) (m := d - b))
  have hsplit_second :
      Finset.sum (Finset.range (d - a)) term =
        Finset.sum (Finset.range (c - a)) term +
          Finset.sum (Finset.range (d - c)) fun k ↦ term (c - a + k) := by
    -- Split the same full interval `[a, d)` at the original successor stage `c`.
    have hlen : d - a = (c - a) + (d - c) := by
      omega
    simpa [hlen] using
      (Finset.sum_range_add (f := term) (n := c - a) (m := d - c))
  have hsum :
      (Finset.sum (Finset.range (b - a)) term +
          Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k)) =
        (Finset.sum (Finset.range (c - a)) term +
          Finset.sum (Finset.range (d - c)) fun k ↦ term (c - a + k)) := by
    exact hsplit_boundary.symm.trans hsplit_second
  rw [hdiff, hboundary, hsecond, hrefined, hshift]
  -- Both sides are complementary decompositions of the same full interval `[a, d)`.
  calc
    Finset.sum (Finset.range (b - a)) term -
        Finset.sum (Finset.range (d - c)) (fun k ↦ term (c - a + k)) =
      (Finset.sum (Finset.range (b - a)) term +
          Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k)) -
        (Finset.sum (Finset.range (d - c)) (fun k ↦ term (c - a + k)) +
          Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k)) := by
            abel
    _ =
      (Finset.sum (Finset.range (c - a)) term +
          Finset.sum (Finset.range (d - c)) fun k ↦ term (c - a + k)) -
        (Finset.sum (Finset.range (d - c)) (fun k ↦ term (c - a + k)) +
          Finset.sum (Finset.range (d - b)) fun k ↦ term (b - a + k)) := by
            rw [hsum]
    _ = Finset.sum (Finset.range (c - a)) term -
        Finset.sum (Finset.range (d - b)) (fun k ↦ term (b - a + k)) := by
          abel

/-- Helper for Lemma 15.87.4: enlarging the chosen source stages of a representative does not
change the induced map to the Milnor cokernel on the `secondProductMap` side exposed by
`cokernel.map`. -/
private theorem secondProductMap_eq_mod_boundary_of_refinement
    (r : SequentialProObjectMorphismRep A B)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    secondProductMap r ≫ cokernel.π (derivedLimitDifferenceMap B) =
      refinedSecondProductMap r reindex' hle ≫ cokernel.π (derivedLimitDifferenceMap B) := by
  -- Route correction: `firstDerivedLimitMap` simplifies through `cokernel.map`, so the quotient
  -- comparison must be built on the bottom horizontal `secondProductMap`, not on
  -- `firstProductMap`.
  have hfactor :
      refinementBoundaryMap r reindex' hle ≫ derivedLimitDifferenceMap B =
        secondProductMap r - refinedSecondProductMap r reindex' hle := by
    -- The projected refinement-boundary identity determines the whole map by product extensionality.
    apply Pi.hom_ext
    intro n
    simpa [Category.assoc, Preadditive.sub_comp] using
      secondProductMap_refinement_boundary_projection r reindex' hle n
  -- Postcompose the difference factorization with the Milnor cokernel projection.
  calc
    secondProductMap r ≫ cokernel.π (derivedLimitDifferenceMap B) =
      ((secondProductMap r - refinedSecondProductMap r reindex' hle) +
          refinedSecondProductMap r reindex' hle) ≫
        cokernel.π (derivedLimitDifferenceMap B) := by
            abel
    _ =
      ((refinementBoundaryMap r reindex' hle ≫ derivedLimitDifferenceMap B) +
          refinedSecondProductMap r reindex' hle) ≫
        cokernel.π (derivedLimitDifferenceMap B) := by
            rw [hfactor]
    _ =
      (refinementBoundaryMap r reindex' hle ≫ derivedLimitDifferenceMap B) ≫
          cokernel.π (derivedLimitDifferenceMap B) +
        refinedSecondProductMap r reindex' hle ≫
          cokernel.π (derivedLimitDifferenceMap B) := by
            simp [Preadditive.add_comp]
    _ = refinedSecondProductMap r reindex' hle ≫
          cokernel.π (derivedLimitDifferenceMap B) := by
            simp [Category.assoc, cokernel.condition]

-- Proof sketch: use the same common-refinement argument as for `limitMap`; after passing to
-- cokernels of the Milnor difference maps, the two second product maps define the same morphism.
/-- Representatives defining the same pro-object morphism induce the same map on
`R^1 \!\varprojlim`. -/
private theorem firstDerivedLimitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.firstDerivedLimitMap = r₂.firstDerivedLimitMap := by
  -- Route correction: the source-faithful common-refinement proof still goes through a quotient
  -- comparison, but unfolding `cokernel.map` here exposes `secondProductMap`, not
  -- `firstProductMap`. The remaining step is therefore to transport the refinement
  -- comparison to the actual `secondProductMap` interface used by `cokernel.map`.
  rcases (represents_eq_iff_equivalent r₁ r₂).1 h with ⟨reindex', h₁, h₂, hmaps⟩
  have hsecond₁ :
      secondProductMap r₁ ≫ cokernel.π (derivedLimitDifferenceMap B) =
        refinedSecondProductMap r₁ reindex' h₁ ≫ cokernel.π (derivedLimitDifferenceMap B) :=
    secondProductMap_eq_mod_boundary_of_refinement r₁ reindex' h₁
  have hsecond₂ :
      secondProductMap r₂ ≫ cokernel.π (derivedLimitDifferenceMap B) =
        refinedSecondProductMap r₂ reindex' h₂ ≫ cokernel.π (derivedLimitDifferenceMap B) :=
    secondProductMap_eq_mod_boundary_of_refinement r₂ reindex' h₂
  have hcommon :
      refinedSecondProductMap r₁ reindex' h₁ =
        refinedSecondProductMap r₂ reindex' h₂ :=
    refinedSecondProductMap_eq_of_equivalent h₁ h₂ hmaps
  -- The source cokernel projection is epi, so it is enough to compare the descended maps after
  -- precomposition with `cokernel.π`; there `cokernel.map` exposes the bottom horizontal map.
  apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap A))).1
  calc
    cokernel.π (derivedLimitDifferenceMap A) ≫ r₁.firstDerivedLimitMap =
        secondProductMap r₁ ≫ cokernel.π (derivedLimitDifferenceMap B) := by
          simp [firstDerivedLimitMap]
    _ =
        refinedSecondProductMap r₁ reindex' h₁ ≫
          cokernel.π (derivedLimitDifferenceMap B) := hsecond₁
    _ =
        refinedSecondProductMap r₂ reindex' h₂ ≫
          cokernel.π (derivedLimitDifferenceMap B) := by
            rw [hcommon]
    _ = secondProductMap r₂ ≫ cokernel.π (derivedLimitDifferenceMap B) := by
          rw [hsecond₂]
    _ = cokernel.π (derivedLimitDifferenceMap A) ≫ r₂.firstDerivedLimitMap := by
          simp [firstDerivedLimitMap]

end

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

private noncomputable abbrev chosenRepresentative :
    SequentialProObjectMorphismRep A B :=
  Classical.choose (exists_representative η)

set_option linter.unusedSectionVars false in
private theorem chosenRepresentative_spec :
    (chosenRepresentative η).toProObjectHom = η :=
  Classical.choose_spec (exists_representative η)

/-- The map on inverse limits induced by a morphism between the sequential pro-objects associated
to `A` and `B`. -/
noncomputable def inducedLimitMap :
    limit A ⟶ limit B :=
  (chosenRepresentative η).limitMap

/-- The owner-level map `inducedLimitMap η` is characterized by any sequential representative of
`η`. -/
theorem inducedLimitMap_eq_limitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedLimitMap η = r.limitMap := by
  exact SequentialProObjectMorphismRep.limitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then `inducedLimitMap η` may be computed using `r.limitMap`;
-- applying the same construction to `inv η` gives the inverse map on inverse limits.
/-- An isomorphism between sequential pro-objects induces an isomorphism on inverse limits. -/
theorem inducedLimitMap_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) := by
  -- TODO: the remaining owner-level step is to identify the pro-object morphism represented by
  -- `compRep r s` with the actual composite `η ≫ inv η` (and similarly for `compRep s r`). The
  -- naive natural-transformation composition `r.toProObjectHom ≫ s.toProObjectHom` is ill-typed,
  -- so this needs the correct Chapter 4 owner-level composition bridge for `toProObjectHom`.
  sorry

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

/-- The map on `R^1 \!\varprojlim` induced by a morphism between the sequential pro-objects
associated to `A` and `B`. -/
noncomputable def inducedFirstDerivedLimitMap :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  (chosenRepresentative η).firstDerivedLimitMap

/-- The owner-level map `inducedFirstDerivedLimitMap` agrees with the representative-level bridge
map for any sequential representative of `η`. -/
theorem inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedFirstDerivedLimitMap η = r.firstDerivedLimitMap := by
  exact SequentialProObjectMorphismRep.firstDerivedLimitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

/-- Helper for Lemma 15.87.4: an isomorphism of sequential pro-objects induces an isomorphism on
`R^1 \!\varprojlim`. -/
private theorem inducedFirstDerivedLimitMap_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedFirstDerivedLimitMap η) := by
  -- TODO: once the owner-level composition bridge for `toProObjectHom` is available, the
  -- representative-level composition law `firstDerivedLimitMap_compRep` and the identity lemma
  -- `firstDerivedLimitMap_idRep` will package the inverse representative of `inv η`.
  sorry

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then the induced maps on `limit` and on `R^1 \!\varprojlim`
-- are independent of the chosen representative and hence may be computed using any representative
-- of `η`; for that representative, the Stacks Project argument gives inverse maps induced by a
-- representative of `inv η`.
/-- Lemma 15.87.4: a morphism of pro-systems of abelian groups induces maps on
`\varprojlim` and on `R^1 \!\varprojlim`. If the corresponding morphism of sequential
pro-objects is an isomorphism, then both induced maps are isomorphisms. -/
@[stacks 0H9K]
theorem inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) ∧
      IsIso (inducedFirstDerivedLimitMap η) := by
  -- Proof comment: the limit and derived-limit arguments are parallel once the representative
  -- functoriality lemmas are established.
  exact ⟨inducedLimitMap_isIso_of_isIso η, inducedFirstDerivedLimitMap_isIso_of_isIso η⟩

end

end CategoryTheory
