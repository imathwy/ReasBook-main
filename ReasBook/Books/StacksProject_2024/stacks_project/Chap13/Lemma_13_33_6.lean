import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasColimitsOfShape ℕ C]

/- Domain-style sampling for Lemma 13.33.6:
- primary domain: exactness of countable coproducts in abelian categories obtained from exact
  sequential colimits, together with the canonical telescope map for a sequential diagram;
- inspected owner declarations:
  `CategoryTheory.CountableAB4.of_countableAB5`,
  `CategoryTheory.Limits.liftToFinsetColimitCocone`,
  `CategoryTheory.sequentialTelescopeMap`,
  `CategoryTheory.Functor.ofSequence`;
- best owner abstraction: the Grothendieck-axiom owner `CountableAB4.of_countableAB5`, with the
  internal countable-coproduct bridge below supplying the remaining owner hypothesis from
  sequential colimits;
- primitive-vs-derived split:
  the primitive data here are finite coproducts, sequential colimits, and the diagram `K : ℕ ⥤ C`;
  the countable-coproduct structure and the `CountableAB4` consequence are derived API, while the
  telescope comparison map to the sequential colimit is the source-facing morphism needed
  downstream.

Source/core/bridge triage:
- `source-facing`: the telescope map to the sequential colimit and the resulting short exact
  sequence;
- `core/canonical`: `CountableAB4.of_countableAB5`;
- `bridge/view`: the local instance below, which supplies the owner theorem with its remaining
  hypothesis at exactly the assumption level used in this file family. -/

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Proof sketch: compute on each coproduct summand. The identity part of
-- `sequentialTelescopeMap K = 𝟙 - Sigma.map' Nat.succ _` contributes the
-- colimit cocone leg
-- `colimit.ι _ n`, and the shifted part contributes
-- `K.map (homOfLE (Nat.le_add_right n 1)) ≫ colimit.ι _ (n + 1) = colimit.ι _ n` by cocone
-- naturality, so the difference is zero.
/-- The telescope map of a sequential diagram becomes zero after postcomposition with any
compatible cocone map. -/
theorem sequentialTelescopeMap_comp_sigmaDesc
    (K : ℕ ⥤ C) [HasCoproduct K.obj] {X : C} (ι : ∀ n, K.obj n ⟶ X)
    (hι : ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) :
    sequentialTelescopeMap K ≫ Limits.Sigma.desc ι = 0 := by
  apply Limits.Sigma.hom_ext
  intro n
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, comp_zero, sub_eq_zero,
    Sigma.ι_desc]
  rw [Category.assoc, Sigma.ι_desc]
  exact (hι n).symm

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasColimitsOfShape ℕ 𝒜]

/-- Sequential colimits in an abelian category induce countable coproducts by expressing a
countable family as the filtered colimit of its finite partial sums. -/
theorem hasCountableCoproducts_of_sequentialColimits : HasCountableCoproducts 𝒜 where
  out J := by
    intro _
    classical
    let _ : HasColimitsOfShape (Finset (Discrete J)) 𝒜 :=
      Functor.Final.hasColimitsOfShape_of_final
        (IsFiltered.sequentialFunctor (Finset (Discrete J)))
    exact ⟨fun F ↦ HasColimit.mk (liftToFinsetColimitCocone F)⟩

/-- Companion instance: exact sequential-colimit contexts can use countable coproducts through
typeclass search. -/
noncomputable instance instHasCountableCoproductsOfSequentialColimits :
    HasCountableCoproducts 𝒜 :=
  hasCountableCoproducts_of_sequentialColimits

/- Exactness of countable direct sums from exact sequential colimits is provided by the canonical
Grothendieck-axiom owner `CategoryTheory.CountableAB4.of_countableAB5`, applied with the bridge
above supplying countable coproducts from sequential colimits internally. -/
recall CountableAB4.of_countableAB5

/-- Helper for Lemma 13.33.6: the canonical map from the countable coproduct to the sequential
colimit presents a cokernel of the telescope map. -/
theorem sigma_desc_cokernelCofork_nonempty_of_sequentialTelescope
    [HasExactColimitsOfShape ℕ 𝒜] (K : ℕ ⥤ 𝒜) :
    Nonempty
      (IsColimit
      (CokernelCofork.ofπ (Limits.Sigma.desc (colimit.ι K))
        (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
          (fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))))) := by
  -- The universal property of the sequential colimit turns any cocone-killing map on the
  -- coproduct into the unique factor through `Sigma.desc (colimit.ι K)`.
  refine ⟨CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_⟩
  -- Each coproduct summand provides a cocone leg once the telescope relation is read off from
  -- the vanishing of `sequentialTelescopeMap K ≫ k`.
  have hkCompat :
      ∀ n,
        K.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι K.obj (n + 1) ≫ k) =
          Sigma.ι K.obj n ≫ k := by
    intro n
    have hzero : Sigma.ι K.obj n ≫ sequentialTelescopeMap K ≫ k = 0 := by
      simpa using congrArg (fun t ↦ Sigma.ι K.obj n ≫ t) hk
    have hdiff :
        Sigma.ι K.obj n ≫ k - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) ≫ k = 0 := by
      simpa [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, Category.assoc] using
        hzero
    have hEq :
        Sigma.ι K.obj n ≫ k = K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) ≫ k := by
      simpa [sub_eq_zero] using hdiff
    exact hEq.symm
  have hkNat :
      ∀ n,
        K.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι K.obj (n + 1) ≫ k) =
          (Sigma.ι K.obj n ≫ k) ≫ ((Functor.const ℕ).obj A).map (homOfLE (Nat.le_succ n)) := by
    intro n
    simpa using hkCompat n
  let c : Cocone K :=
    Cocone.mk A <|
      NatTrans.ofSequence
        (fun n ↦ Sigma.ι K.obj n ≫ k)
        hkNat
  refine ⟨colimit.desc K c, ?_⟩
  -- The factorization is checked on each coproduct summand.
  apply Limits.Sigma.hom_ext
  intro n
  have hι :
      Sigma.ι K.obj n ≫ Limits.Sigma.desc (colimit.ι K) ≫ colimit.desc K c =
        colimit.ι K n ≫ colimit.desc K c := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ colimit.desc K c) (Limits.Sigma.ι_desc (colimit.ι K) n)
  rw [hι, colimit.ι_desc]
  simp [c]

/-- Helper for Lemma 13.33.6: the `n`th finite partial sum of a sequential diagram, built
recursively by adjoining one more summand. -/
def finite_prefix_obj [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ → 𝒜
  | 0 => (0 : 𝒜)
  | n + 1 => finite_prefix_obj K n ⊞ K.obj n

/-- Helper for Lemma 13.33.6: the canonical inclusion of one finite prefix into the next. -/
def finite_prefix_inclusion [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    finite_prefix_obj K n ⟶ finite_prefix_obj K (n + 1) :=
  biprod.inl

/-- Helper for Lemma 13.33.6: the inclusion of the new last summand into the next finite prefix. -/
def finite_prefix_lastι [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    K.obj n ⟶ finite_prefix_obj K (n + 1) :=
  biprod.inr

/-- Helper for Lemma 13.33.6: the recursively corrected projection from a finite prefix to its
last quotient summand. -/
def finite_prefix_stage_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K (n + 1) ⟶ K.obj n
  | 0 => biprod.snd
  | n + 1 =>
      biprod.desc
        (finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n)))
        (𝟙 _)

/-- Helper for Lemma 13.33.6: the finite-stage telescope map
`A₀ ⊞ ⋯ ⊞ Aₙ₋₁ ⟶ A₀ ⊞ ⋯ ⊞ Aₙ`. -/
def finite_prefix_stage_map [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K n ⟶ finite_prefix_obj K (n + 1)
  | 0 => finite_prefix_inclusion K 0
  | n + 1 =>
      biprod.desc
        (finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1))
        (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1) -
          K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))

/-- Helper for Lemma 13.33.6: the recursive retraction showing that each finite-stage telescope
map is split mono. -/
def finite_prefix_stage_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    (n : ℕ) → finite_prefix_obj K (n + 1) ⟶ finite_prefix_obj K n
  | 0 => biprod.fst
  | n + 1 =>
      biprod.desc
        (biprod.lift (finite_prefix_stage_retraction K n)
          (finite_prefix_stage_projection K n))
        0

/-- Helper for Lemma 13.33.6: the last summand of a finite prefix is sent isomorphically to the
stage quotient. -/
theorem finite_prefix_lastι_comp_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_stage_projection K n = 𝟙 _ :=
  by
    intro n
    -- The quotient map reads off the newest biproduct summand directly.
    cases n with
    | zero =>
        rw [finite_prefix_lastι, finite_prefix_stage_projection]
        exact biprod.inr_snd
    | succ n =>
        rw [finite_prefix_lastι, finite_prefix_stage_projection]
        exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the newest last summand is annihilated by the recursive retraction. -/
theorem finite_prefix_lastι_comp_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_stage_retraction K n = 0 :=
  by
    intro n
    -- The retraction discards the newest outer summand by construction.
    cases n with
    | zero =>
        rw [finite_prefix_lastι, finite_prefix_stage_retraction]
        exact biprod.inr_fst
    | succ n =>
        rw [finite_prefix_lastι, finite_prefix_stage_retraction]
        exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the old finite-prefix inclusion becomes the previous stage
projection followed by the next transition map after postcomposition with the successor-stage
projection. -/
theorem finite_prefix_inclusion_comp_stage_projection [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    finite_prefix_inclusion K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) =
      finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n)) := by
  -- The successor-stage projection is defined by descending from the old prefix and the new
  -- summand, so the old inclusion picks out the transported previous projection.
  rw [finite_prefix_inclusion, finite_prefix_stage_projection]
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the correction term in the successor-stage telescope map is killed
by the successor-stage projection. -/
theorem finite_prefix_correction_comp_stage_projection [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    ((finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))) ≫
      finite_prefix_stage_projection K (n + 1) = 0 := by
  -- Route correction: normalize the raw correction term after postcomposition first, so both
  -- summands become the same transition map and cancel before re-entering the wrapped branch proof.
  rw [Preadditive.sub_comp]
  have hold :
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) := by
    calc
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        finite_prefix_lastι K n ≫
          (finite_prefix_inclusion K (n + 1) ≫ finite_prefix_stage_projection K (n + 1)) := by
            simp [Category.assoc]
      _ = finite_prefix_lastι K n ≫
          (finite_prefix_stage_projection K n ≫ K.map (homOfLE (Nat.le_succ n))) := by
            rw [finite_prefix_inclusion_comp_stage_projection]
      _ = (finite_prefix_lastι K n ≫ finite_prefix_stage_projection K n) ≫
          K.map (homOfLE (Nat.le_succ n)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) := by
            rw [finite_prefix_lastι_comp_projection, Category.id_comp]
  have hnew :
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) := by
    calc
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_stage_projection K (n + 1) =
        K.map (homOfLE (Nat.le_succ n)) ≫
          (finite_prefix_lastι K (n + 1) ≫ finite_prefix_stage_projection K (n + 1)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) := by
            rw [finite_prefix_lastι_comp_projection, Category.comp_id]
  rw [hold, hnew]
  exact sub_self _

/-- Helper for Lemma 13.33.6: on the old summands, the successor-stage telescope map followed by
the stage projection is the previous stage projection transported by the next transition map. -/
theorem finite_prefix_stage_projection_successor_old_branch [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) =
      finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n ≫
        K.map (homOfLE (Nat.le_succ n)) := by
  -- The old branch of the successor-stage map is the previous stage map followed by the old
  -- inclusion, so the raw inclusion/projection formula finishes the transport.
  rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc,
    finite_prefix_inclusion_comp_stage_projection]

/-- Helper for Lemma 13.33.6: on the newest summand, the successor-stage projection cancels the
correction term in the telescope map. -/
theorem finite_prefix_stage_projection_successor_new_branch [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ) :
    biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_projection K (n + 1) = 0 := by
  -- The wrapped new branch is exactly the raw correction term after precomposing with
  -- `biprod.inr`.
  rw [finite_prefix_stage_map, biprod.inr_desc_assoc]
  exact finite_prefix_correction_comp_stage_projection K n

/-- Helper for Lemma 13.33.6: the finite-stage telescope map kills the corrected projection to the
new quotient summand. -/
theorem finite_prefix_stage_map_comp_projection [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n = 0 :=
  by
    intro n
    induction n with
    | zero =>
        -- At the initial stage the telescope map is the old inclusion into the first biproduct.
        rw [finite_prefix_stage_map, finite_prefix_stage_projection]
        exact biprod.inl_snd
    | succ n ih =>
        -- Compare the successor-stage composite on the old and new summands separately.
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_stage_projection K (n + 1) =
              finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n ≫
                K.map (homOfLE (Nat.le_succ n)) := by
                  exact finite_prefix_stage_projection_successor_old_branch K n
            _ = 0 := by
                  simpa [Category.assoc] using
                    congrArg (fun f ↦ f ≫ K.map (homOfLE (Nat.le_succ n))) ih
            _ = biprod.inl ≫
                (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) := by
                  symm
                  change biprod.inl ≫
                      (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) =
                    (0 : finite_prefix_obj K n ⟶ K.obj (n + 1))
                  exact comp_zero
        · calc
            biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_stage_projection K (n + 1) = 0 := by
                  exact finite_prefix_stage_projection_successor_new_branch K n
            _ = biprod.inr ≫
                (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) := by
                  symm
                  change biprod.inr ≫
                      (0 : finite_prefix_obj K (n + 1) ⟶ K.obj (n + 1)) =
                    (0 : K.obj n ⟶ K.obj (n + 1))
                  exact comp_zero

/-- Helper for Lemma 13.33.6: the successor-stage telescope composite with the recursive
retraction restricts to the two biproduct inclusions on the old and new branches. -/
theorem finite_prefix_stage_retraction_successor_branches [HasFiniteBiproducts 𝒜]
    (K : ℕ ⥤ 𝒜) (n : ℕ)
    (hret : finite_prefix_stage_map K n ≫ finite_prefix_stage_retraction K n = 𝟙 _)
    (hproj : finite_prefix_stage_map K n ≫ finite_prefix_stage_projection K n = 0) :
    biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
        biprod.inl ∧
      biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
        biprod.inr := by
  constructor
  · -- The old branch lands in the old prefix via the retraction and has zero new component.
    have hold :
        biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
          finite_prefix_stage_map K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
      calc
        biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
            finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1) ≫
              finite_prefix_stage_retraction K (n + 1) := by
              rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc]
        _ = finite_prefix_stage_map K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
              rw [finite_prefix_inclusion, finite_prefix_stage_retraction]
              exact congrArg (fun t ↦ finite_prefix_stage_map K n ≫ t)
                (biprod.inl_desc
                  (biprod.lift (finite_prefix_stage_retraction K n)
                    (finite_prefix_stage_projection K n))
                  0)
    rw [hold]
    apply biprod.hom_ext
    · -- Postcomposing with `biprod.fst` recovers the induction hypothesis `hret`.
      simpa [Category.assoc, hret] using hret
    · -- Postcomposing with `biprod.snd` recovers the vanishing hypothesis `hproj`.
      simpa [Category.assoc, hproj] using hproj
  · -- The new branch is the last summand together with the correction term, whose retraction part
    -- vanishes while the projection part is the identity.
    have hnew :
        biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
          finite_prefix_lastι K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
      calc
        biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫ finite_prefix_stage_retraction K (n + 1) =
            (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1) -
                K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
              finite_prefix_stage_retraction K (n + 1) := by
              rw [finite_prefix_stage_map, biprod.inr_desc_assoc]
        _ =
            (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
                finite_prefix_stage_retraction K (n + 1) -
              (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
                finite_prefix_stage_retraction K (n + 1) := by
              rw [Preadditive.sub_comp]
        _ = finite_prefix_lastι K n ≫
            biprod.lift (finite_prefix_stage_retraction K n)
              (finite_prefix_stage_projection K n) := by
              have hleft :
                  (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
                      finite_prefix_stage_retraction K (n + 1) =
                    finite_prefix_lastι K n ≫
                      biprod.lift (finite_prefix_stage_retraction K n)
                        (finite_prefix_stage_projection K n) := by
                rw [finite_prefix_inclusion, finite_prefix_stage_retraction, Category.assoc]
                exact congrArg (fun t ↦ finite_prefix_lastι K n ≫ t)
                  (biprod.inl_desc
                    (biprod.lift (finite_prefix_stage_retraction K n)
                      (finite_prefix_stage_projection K n))
                    0)
              have hright :
                  (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
                      finite_prefix_stage_retraction K (n + 1) = 0 := by
                rw [Category.assoc, finite_prefix_lastι_comp_retraction]
                rw [Limits.comp_zero]
              rw [hleft, hright]
              simp
    rw [hnew]
    apply biprod.hom_ext
    · -- The old component vanishes because the newest summand is killed by the retraction.
      simpa [Category.assoc] using finite_prefix_lastι_comp_retraction (K := K) n
    · -- The new component is read off by the stage projection.
      simpa [Category.assoc] using finite_prefix_lastι_comp_projection (K := K) n

/-- Helper for Lemma 13.33.6: the finite-stage telescope map admits the recursive retraction above,
so it is split mono. -/
theorem finite_prefix_stage_map_comp_retraction [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_stage_map K n ≫ finite_prefix_stage_retraction K n = 𝟙 _ :=
  by
    intro n
    induction n with
    | zero =>
        -- The initial-stage retraction is the left projection from the first biproduct.
        rw [finite_prefix_stage_map, finite_prefix_stage_retraction]
        exact biprod.inl_fst
    | succ n ih =>
        -- The successor-stage identity is determined by its restrictions to the two biproduct
        -- summands, which are exactly the branch equalities proved above.
        apply biprod.hom_ext'
        · exact
            (finite_prefix_stage_retraction_successor_branches K n ih
              (finite_prefix_stage_map_comp_projection K n)).1.trans <|
              (Category.comp_id biprod.inl).symm
        · exact
            (finite_prefix_stage_retraction_successor_branches K n ih
              (finite_prefix_stage_map_comp_projection K n)).2.trans <|
              (Category.comp_id biprod.inr).symm

/-- Helper for Lemma 13.33.6: each finite-stage telescope map is a split monomorphism. -/
theorem finite_prefix_stage_splitMono [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    IsSplitMono (finite_prefix_stage_map K n) :=
  IsSplitMono.mk' ⟨finite_prefix_stage_retraction K n,
    finite_prefix_stage_map_comp_retraction K n⟩

/-- Helper for Lemma 13.33.6: each finite-stage telescope map is a monomorphism. -/
theorem finite_prefix_stage_mono [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) (n : ℕ) :
    Mono (finite_prefix_stage_map K n) := by
  let _ : IsSplitMono (finite_prefix_stage_map K n) := finite_prefix_stage_splitMono K n
  infer_instance

/-- Helper for Lemma 13.33.6: the finite prefixes form the left sequential diagram. -/
def finite_prefix_left_functor [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ ⥤ 𝒜 :=
  Functor.ofSequence (fun n ↦ finite_prefix_inclusion K n)

/-- Helper for Lemma 13.33.6: the shifted finite prefixes form the middle sequential diagram. -/
def finite_prefix_middle_functor [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) : ℕ ⥤ 𝒜 :=
  Functor.ofSequence (X := fun n ↦ finite_prefix_obj K (n + 1))
    (fun n ↦ finite_prefix_inclusion K (n + 1))

/-- Helper for Lemma 13.33.6: the recursive finite-stage telescope maps satisfy the successor
naturality equation required by `NatTrans.ofSequence`. -/
theorem finite_prefix_stage_naturality_succ [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    ∀ n,
      finite_prefix_inclusion K n ≫ finite_prefix_stage_map K (n + 1) =
        finite_prefix_stage_map K n ≫ finite_prefix_inclusion K (n + 1) := by
  intro n
  -- The successor-stage map restricts to the previous stage map on the older summands.
  rw [finite_prefix_inclusion, finite_prefix_stage_map]
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the finite-stage telescope maps assemble into a natural
transformation from the left prefix system to the shifted one. -/
def finite_prefix_stage_natTrans [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) :
    finite_prefix_left_functor K ⟶ finite_prefix_middle_functor K :=
  NatTrans.ofSequence
    (fun n ↦ finite_prefix_stage_map K n)
    (fun n ↦ by
      -- The sequence constructor only needs the successor-step naturality.
      simpa [finite_prefix_left_functor, finite_prefix_middle_functor,
        Functor.ofSequence_map_homOfLE_succ] using finite_prefix_stage_naturality_succ K n)

/-- Helper for Lemma 13.33.6: the canonical map from a finite prefix to the countable coproduct. -/
def finite_prefix_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    (n : ℕ) → finite_prefix_obj K n ⟶ ∐ K.obj
  | 0 => 0
  | n + 1 => biprod.desc (finite_prefix_to_sigma K n) (Sigma.ι K.obj n)

/-- Helper for Lemma 13.33.6: finite-prefix inclusions are compatible with the canonical maps into
the countable coproduct. -/
theorem finite_prefix_inclusion_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      finite_prefix_inclusion K n ≫ finite_prefix_to_sigma K (n + 1) =
        finite_prefix_to_sigma K n := by
  intro n
  -- This is the defining property of the left summand inclusion of a biproduct.
  exact biprod.inl_desc _ _

/-- Helper for Lemma 13.33.6: the new last summand of a finite prefix maps to the corresponding
summand of the countable coproduct. -/
theorem finite_prefix_lastι_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      finite_prefix_lastι K n ≫ finite_prefix_to_sigma K (n + 1) = Sigma.ι K.obj n := by
  intro n
  -- The recursive coproduct map adjoins the new summand by `Sigma.ι`.
  rw [finite_prefix_lastι, finite_prefix_to_sigma]
  exact biprod.inr_desc _ _

/-- Helper for Lemma 13.33.6: the correction term in the successor-stage telescope map becomes the
expected `1 - f_n` branch after postcomposition with the canonical map to the countable coproduct. -/
theorem finite_prefix_correction_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (n : ℕ) :
    ((finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1))) ≫
      finite_prefix_to_sigma K (n + 2) =
        Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  -- The old part becomes the `n`th coproduct summand, and the new corrected part becomes the
  -- shifted summand after transport by the transition morphism.
  rw [Preadditive.sub_comp]
  have hold :
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        Sigma.ι K.obj n := by
    calc
      (finite_prefix_lastι K n ≫ finite_prefix_inclusion K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        finite_prefix_lastι K n ≫
          (finite_prefix_inclusion K (n + 1) ≫ finite_prefix_to_sigma K (n + 2)) := by
            simp [Category.assoc]
      _ = finite_prefix_lastι K n ≫ finite_prefix_to_sigma K (n + 1) := by
            rw [finite_prefix_inclusion_comp_to_sigma]
      _ = Sigma.ι K.obj n := finite_prefix_lastι_comp_to_sigma K n
  have hnew :
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
    calc
      (K.map (homOfLE (Nat.le_succ n)) ≫ finite_prefix_lastι K (n + 1)) ≫
          finite_prefix_to_sigma K (n + 2) =
        K.map (homOfLE (Nat.le_succ n)) ≫
          (finite_prefix_lastι K (n + 1) ≫ finite_prefix_to_sigma K (n + 2)) := by
            simp [Category.assoc]
      _ = K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
            rw [finite_prefix_lastι_comp_to_sigma]
  rw [hold, hnew]

/-- Helper for Lemma 13.33.6: the finite-stage telescope maps are compatible with the global
telescope endomorphism of the countable coproduct. -/
theorem finite_prefix_stage_map_comp_to_sigma [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
        finite_prefix_to_sigma K n ≫ sequentialTelescopeMap K =
        finite_prefix_stage_map K n ≫ finite_prefix_to_sigma K (n + 1) :=
  by
    intro n
    induction n with
    | zero =>
        -- The zero-stage map is initial, and the first finite-stage telescope map is the
        -- inclusion into the first biproduct.
        simpa [finite_prefix_stage_map, finite_prefix_to_sigma] using
          (finite_prefix_inclusion_comp_to_sigma (K := K) 0).symm
    | succ n ih =>
        -- Route correction: compare the old and new branches after postcomposition with
        -- `finite_prefix_to_sigma` using the raw successor formulas, rather than asking Lean to
        -- normalize the wrapped branches directly.
        apply biprod.hom_ext'
        · calc
            biprod.inl ≫ finite_prefix_to_sigma K (n + 1) ≫ sequentialTelescopeMap K =
                finite_prefix_to_sigma K n ≫ sequentialTelescopeMap K := by
                  rw [finite_prefix_to_sigma, biprod.inl_desc_assoc]
            _ = finite_prefix_stage_map K n ≫ finite_prefix_to_sigma K (n + 1) := ih
            _ = biprod.inl ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_to_sigma K (n + 2) := by
                  rw [finite_prefix_stage_map, biprod.inl_desc_assoc, Category.assoc,
                    finite_prefix_inclusion_comp_to_sigma]
        · calc
            biprod.inr ≫ finite_prefix_to_sigma K (n + 1) ≫ sequentialTelescopeMap K =
                Sigma.ι K.obj n ≫ sequentialTelescopeMap K := by
                  rw [finite_prefix_to_sigma, biprod.inr_desc_assoc]
            _ = Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
                  simpa using
                    (Sigma.ι_comp_sequentialTelescopeMap_assoc (K := K) n
                      (h := 𝟙 (∐ K.obj)))
            _ = biprod.inr ≫ finite_prefix_stage_map K (n + 1) ≫
                finite_prefix_to_sigma K (n + 2) := by
                  rw [finite_prefix_stage_map, biprod.inr_desc_assoc,
                    finite_prefix_correction_comp_to_sigma]

/-- Helper for Lemma 13.33.6: the left cocone legs satisfy the `NatTrans.ofSequence` successor
compatibility. -/
theorem finite_prefix_left_cocone_naturality [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_left_functor K).map (homOfLE (Nat.le_succ n)) ≫
          finite_prefix_to_sigma K (n + 1) =
        finite_prefix_to_sigma K n ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
          (homOfLE (Nat.le_succ n)) :=
  by
    intro n
    -- Unfold the successor map of the sequence functor and use the left-summand formula.
    simpa [finite_prefix_left_functor, Functor.ofSequence_map_homOfLE_succ] using
      finite_prefix_inclusion_comp_to_sigma K n

/-- Helper for Lemma 13.33.6: the middle cocone legs satisfy the `NatTrans.ofSequence` successor
compatibility. -/
theorem finite_prefix_middle_cocone_naturality [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_middle_functor K).map (homOfLE (Nat.le_succ n)) ≫
          finite_prefix_to_sigma K (n + 2) =
        finite_prefix_to_sigma K (n + 1) ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
          (homOfLE (Nat.le_succ n)) :=
  by
    intro n
    -- The shifted finite-prefix system has the same successor map one stage later.
    simpa [finite_prefix_middle_functor, Functor.ofSequence_map_homOfLE_succ] using
      finite_prefix_inclusion_comp_to_sigma K (n + 1)

/-- Helper for Lemma 13.33.6: the left finite-prefix cocone lands in the countable coproduct. -/
def finite_prefix_left_cocone [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    Cocone (finite_prefix_left_functor K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence
      (fun n ↦ finite_prefix_to_sigma K n)
      (finite_prefix_left_cocone_naturality K)

/-- Helper for Lemma 13.33.6: the shifted finite-prefix cocone lands in the countable coproduct. -/
def finite_prefix_middle_cocone [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    Cocone (finite_prefix_middle_functor K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence
      (fun n ↦ finite_prefix_to_sigma K (n + 1))
      (finite_prefix_middle_cocone_naturality K)

/-- Helper for Lemma 13.33.6: a morphism out of each finite prefix is determined by its
restriction to the previous prefix and by its value on the newest summand. -/
theorem finite_prefix_desc_eq_sigma_desc_of_branches [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] {X : 𝒜} (g : ∀ n, finite_prefix_obj K n ⟶ X)
    (a : ∀ n, K.obj n ⟶ X)
    (hg : ∀ n, finite_prefix_inclusion K n ≫ g (n + 1) = g n)
    (ha : ∀ n, finite_prefix_lastι K n ≫ g (n + 1) = a n) :
    ∀ n, finite_prefix_to_sigma K n ≫ Limits.Sigma.desc a = g n := by
  intro n
  induction n with
  | zero =>
      -- The zero-stage map is unique because the initial prefix object is zero.
      have h0 : IsZero (finite_prefix_obj K 0) := by
        simpa [finite_prefix_obj] using (isZero_zero 𝒜)
      exact h0.eq_of_src _ _
  | succ n ih =>
      -- The successor-stage map is determined by the previous prefix and the newest summand.
      apply biprod.hom_ext'
      · calc
          biprod.inl ≫ finite_prefix_to_sigma K (n + 1) ≫ Limits.Sigma.desc a =
            finite_prefix_to_sigma K n ≫ Limits.Sigma.desc a := by
              simp [finite_prefix_to_sigma, finite_prefix_inclusion, Category.assoc]
          _ = g n := ih
          _ = biprod.inl ≫ g (n + 1) := (hg n).symm
      · calc
          biprod.inr ≫ finite_prefix_to_sigma K (n + 1) ≫ Limits.Sigma.desc a =
            a n := by
              rw [finite_prefix_to_sigma, biprod.inr_desc_assoc, Limits.Sigma.ι_desc]
          _ = biprod.inr ≫ g (n + 1) := (ha n).symm

/-- Helper for Lemma 13.33.6: the coproduct map built from the newest summands recovers any cocone
on the left finite-prefix system. -/
theorem finite_prefix_left_desc_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K)) :
    ∀ n,
      finite_prefix_to_sigma K n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) =
        s.ι.app n := by
  intro n
  -- Route correction: instead of a second ad hoc induction, reconstruct the cocone from the
  -- old branch and newest summand through the generic finite-prefix descent lemma.
  simpa using finite_prefix_desc_eq_sigma_desc_of_branches (K := K)
    (g := fun i ↦ s.ι.app i)
    (a := fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1))
    (hg := fun i ↦ by
      -- Cocone naturality identifies the old branch with the previous cocone leg.
      simpa [finite_prefix_left_functor, Functor.ofSequence_map_homOfLE_succ] using
        s.w (homOfLE (Nat.le_succ i)))
    (ha := fun i ↦ rfl) n

/-- Helper for Lemma 13.33.6: the explicit descendant from the countable coproduct satisfies the
left finite-prefix cocone equations. -/
theorem finite_prefix_left_cocone_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K)) :
    ∀ n,
      (finite_prefix_left_cocone K).ι.app n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) =
        s.ι.app n := by
  intro n
  -- The explicit cocone is defined from the same finite-prefix maps.
  simpa [finite_prefix_left_cocone] using finite_prefix_left_desc_fac K s n

/-- Helper for Lemma 13.33.6: the descendant from the countable coproduct is unique for cocones on
the left finite-prefix system. -/
theorem finite_prefix_left_cocone_uniq [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_left_functor K))
    (m : (finite_prefix_left_cocone K).pt ⟶ s.pt)
    (hm : ∀ n, (finite_prefix_left_cocone K).ι.app n ≫ m = s.ι.app n) :
    m = Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)) := by
  -- Compare both maps on each coproduct summand using the cocone equation at stage `i + 1`.
  apply Limits.Sigma.hom_ext
  intro i
  have hi := congrArg (fun t ↦ finite_prefix_lastι K i ≫ t) (hm (i + 1))
  have hleft' :
      finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    simpa [finite_prefix_left_cocone, Category.assoc] using hi
  have hsigma := congrArg (fun t ↦ t ≫ m) (finite_prefix_lastι_comp_to_sigma (K := K) i).symm
  have hleft'' :
      (finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1)) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    simpa [Category.assoc] using hleft'
  have hleft : Sigma.ι K.obj i ≫ m = finite_prefix_lastι K i ≫ s.ι.app (i + 1) := by
    exact hsigma.trans hleft''
  have hright :
      finite_prefix_lastι K i ≫ s.ι.app (i + 1) =
        Sigma.ι K.obj i ≫
          Limits.Sigma.desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app (j + 1)) := by
    simpa using
      (CategoryTheory.Limits.Sigma.ι_desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app (j + 1)) i).symm
  exact hleft.trans hright

/-- Helper for Lemma 13.33.6: the left finite-prefix cocone is colimit, because any cocone is
determined by its values on the newly added summands. -/
noncomputable def finite_prefix_left_isColimit [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    IsColimit (finite_prefix_left_cocone K) :=
  IsColimit.mk
    (fun s ↦ Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app (i + 1)))
    (fun s n ↦ finite_prefix_left_cocone_fac K s n)
    (fun s m hm ↦ finite_prefix_left_cocone_uniq K s m hm)

/-- Helper for Lemma 13.33.6: the coproduct map built from the newest summands also recovers any
cocone on the shifted finite-prefix system. -/
theorem finite_prefix_middle_desc_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K)) :
    ∀ n,
      finite_prefix_to_sigma K (n + 1) ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) =
        s.ι.app n := by
  intro n
  -- The shifted cocone uses the same reconstruction lemma after padding the zero stage.
  simpa using finite_prefix_desc_eq_sigma_desc_of_branches (K := K)
    (g := fun
      | 0 => 0
      | i + 1 => s.ι.app i)
    (a := fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i)
    (hg := fun
      | 0 => by
          -- The padded zero stage is forced by the zero object.
          have h0 : IsZero (finite_prefix_obj K 0) := by
            simpa [finite_prefix_obj] using (isZero_zero 𝒜)
          exact h0.eq_of_src _ _
      | i + 1 => by
          -- Cocone naturality handles each genuine successor stage.
          simpa [finite_prefix_middle_functor, Functor.ofSequence_map_homOfLE_succ] using
            s.w (homOfLE (Nat.le_succ i)))
    (ha := fun i ↦ rfl) (n + 1)

/-- Helper for Lemma 13.33.6: the explicit descendant from the countable coproduct satisfies the
shifted finite-prefix cocone equations. -/
theorem finite_prefix_middle_cocone_fac [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K)) :
    ∀ n,
      (finite_prefix_middle_cocone K).ι.app n ≫
          Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) =
        s.ι.app n := by
  intro n
  -- The shifted explicit cocone uses the same finite-prefix maps with one index shift.
  simpa [finite_prefix_middle_cocone] using finite_prefix_middle_desc_fac K s n

/-- Helper for Lemma 13.33.6: the descendant from the countable coproduct is unique for cocones on
the shifted finite-prefix system. -/
theorem finite_prefix_middle_cocone_uniq [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] (s : Cocone (finite_prefix_middle_functor K))
    (m : (finite_prefix_middle_cocone K).pt ⟶ s.pt)
    (hm : ∀ n, (finite_prefix_middle_cocone K).ι.app n ≫ m = s.ι.app n) :
    m = Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i) := by
  -- The shifted cocone has the same summandwise uniqueness after precomposing with `lastι`.
  apply Limits.Sigma.hom_ext
  intro i
  have hi := congrArg (fun t ↦ finite_prefix_lastι K i ≫ t) (hm i)
  have hleft' :
      finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app i := by
    simpa [finite_prefix_middle_cocone, Category.assoc] using hi
  have hsigma := congrArg (fun t ↦ t ≫ m) (finite_prefix_lastι_comp_to_sigma (K := K) i).symm
  have hleft'' :
      (finite_prefix_lastι K i ≫ finite_prefix_to_sigma K (i + 1)) ≫ m =
        finite_prefix_lastι K i ≫ s.ι.app i := by
    simpa [Category.assoc] using hleft'
  have hleft : Sigma.ι K.obj i ≫ m = finite_prefix_lastι K i ≫ s.ι.app i := by
    exact hsigma.trans hleft''
  have hright :
      finite_prefix_lastι K i ≫ s.ι.app i =
        Sigma.ι K.obj i ≫ Limits.Sigma.desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app j) := by
    simpa using
      (CategoryTheory.Limits.Sigma.ι_desc (fun j ↦ finite_prefix_lastι K j ≫ s.ι.app j) i).symm
  exact hleft.trans hright

/-- Helper for Lemma 13.33.6: the shifted finite-prefix cocone is also colimit, using the same
summandwise reconstruction one stage earlier. -/
noncomputable def finite_prefix_middle_isColimit [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜)
    [HasCoproduct K.obj] :
    IsColimit (finite_prefix_middle_cocone K) :=
  IsColimit.mk
    (fun s ↦ Limits.Sigma.desc (fun i ↦ finite_prefix_lastι K i ≫ s.ι.app i))
    (fun s n ↦ finite_prefix_middle_cocone_fac K s n)
    (fun s m hm ↦ finite_prefix_middle_cocone_uniq K s m hm)

/-- Helper for Lemma 13.33.6: the explicit finite-prefix cocones are compatible with the global
telescope map. -/
theorem finite_prefix_cocone_compat [HasFiniteBiproducts 𝒜] (K : ℕ ⥤ 𝒜) [HasCoproduct K.obj] :
    ∀ n,
      (finite_prefix_left_cocone K).ι.app n ≫ sequentialTelescopeMap K =
        (finite_prefix_stage_natTrans K).app n ≫ (finite_prefix_middle_cocone K).ι.app n :=
  by
    intro n
    -- This is exactly the finite-stage compatibility, rewritten through the explicit cocone data.
    simpa [finite_prefix_left_cocone, finite_prefix_middle_cocone, finite_prefix_stage_natTrans] using
      finite_prefix_stage_map_comp_to_sigma K n

-- Proof sketch: apply part (1) to obtain exact countable coproducts. Then express the direct sum
-- as the sequential colimit of the finite partial sums and apply exactness of sequential colimits
-- to the standard short exact sequences
-- `0 ⟶ A₀ ⨿ ⋯ ⨿ Aₙ₋₁ ⟶ A₀ ⨿ ⋯ ⨿ Aₙ ⟶ Aₙ ⟶ 0`, whose colimit identifies with the telescope
-- short complex.
/-- Lemma 13.33.6: for a sequential diagram in an abelian category with exact colimits over `ℕ`,
the telescope map on the countable direct sum fits into a short exact sequence
`0 ⟶ ⨿ Kₙ ⟶ ⨿ Kₙ ⟶ colim K ⟶ 0`. -/
theorem sequentialTelescope_shortExact [HasExactColimitsOfShape ℕ 𝒜] (K : ℕ ⥤ 𝒜) :
    (ShortComplex.mk (sequentialTelescopeMap K)
      (Limits.Sigma.desc (colimit.ι K))
      (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
        fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))).ShortExact :=
  by
    -- Exactness follows once the canonical map to the sequential colimit is identified as the
    -- cokernel of the telescope map.
    have hExact :
        (ShortComplex.mk (sequentialTelescopeMap K)
          (Limits.Sigma.desc (colimit.ι K))
          (sequentialTelescopeMap_comp_sigmaDesc K (colimit.ι K)
            fun n ↦ colimit.w K (homOfLE (Nat.le_succ n)))).Exact := by
      exact ShortComplex.exact_of_g_is_cokernel _
        (Classical.choice <|
          sigma_desc_cokernelCofork_nonempty_of_sequentialTelescope K)
    let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
    let _ : CountableAB4 𝒜 := CountableAB4.of_countableAB5 𝒜
    -- The mono statement comes from the source-faithful finite-prefix telescope systems: each
    -- finite-stage map is split mono, and the global telescope map is their colimit.
    have hMonoNat : Mono (finite_prefix_stage_natTrans K) := by
      -- Each component is mono by the finite split-mono calculation above.
      have : ∀ n, Mono ((finite_prefix_stage_natTrans K).app n) := by
        intro n
        change Mono (finite_prefix_stage_map K n)
        exact finite_prefix_stage_mono K n
      exact NatTrans.mono_of_mono_app (finite_prefix_stage_natTrans K)
    have hMono : Mono (sequentialTelescopeMap K) := by
      let _ : Mono (finite_prefix_stage_natTrans K) := hMonoNat
      exact Limits.colim.map_mono' (finite_prefix_stage_natTrans K)
        (finite_prefix_left_isColimit K) (finite_prefix_middle_isColimit K)
        (sequentialTelescopeMap K) (finite_prefix_cocone_compat K)
    exact ShortComplex.ShortExact.mk' hExact hMono inferInstance

end

end CategoryTheory
