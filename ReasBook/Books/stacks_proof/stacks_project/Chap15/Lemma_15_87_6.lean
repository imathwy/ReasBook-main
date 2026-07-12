import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap13.Remark_13_34_4
import StacksProject_2024.Chap15.Lemma_15_87_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite
open scoped BigOperators

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/- Domain-style sampling for Lemma 15.87.6:
- primary domain: derived limits in a triangulated category and isomorphisms of the associated
  sequential pro-objects;
- sampled owner declarations:
  `exists_representative`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`;
- best owner abstraction: the public pro-isomorphism hypothesis belongs to the canonical
  pro-object morphism `η`; a sequential representative of `η` is private bridge data used only to
  pass to inverse systems of abelian groups;
- primitive data: the towers `Ksys`, `Msys`, their chosen derived limits `K`, `M`, and a
  pro-object morphism
  `η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
    proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}`;
- derived API: the owner-level isomorphism hypothesis `IsIso η`, a chosen representative of `η`,
  and the induced represented-Hom representative.

Source/core/bridge triage:
- `source-facing`: the existence of a non-canonical isomorphism between chosen derived limits of
  pro-isomorphic towers;
- `core/canonical`: `η`, `IsDerivedLimit`, and the owner theorem
  `inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`;
- `bridge/view`: a chosen representative `a` of `η` and the represented-Hom representative
  `preadditiveCoyonedaRep a L`. -/

namespace SequentialProObjectMorphismRep

variable {Ksys Msys : ℕᵒᵖ ⥤ D}

local notation "SeqRep" => _root_.CategoryTheory.SequentialProObjectMorphismRep

-- Proof sketch: apply the additive covariant functor `preadditiveCoyoneda.obj (op L)` to the
-- compatibility square defining `a`. This transports the levelwise commutativity relation from
-- `D` to the inverse systems of abelian groups `Hom_D(L, K_n)` and `Hom_D(L, M_n)`.
/-- Helper for Lemma 15.87.6: applying `preadditiveCoyoneda.obj (op L)` to the defining
compatibility square of `a` yields the compatibility square on the represented-Hom towers. -/
private theorem preadditiveCoyonedaRep_comm
    (a : SeqRep Ksys Msys) (L : D) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      (Ksys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE (a.reindex.monotone h)).op ≫
          (preadditiveCoyoneda.obj (op L)).map (a.map n) =
        (preadditiveCoyoneda.obj (op L)).map (a.map n') ≫
          (Msys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE h).op := by
  intro n n' h
  -- Applying the represented-Hom functor turns the representative compatibility square into the
  -- corresponding square of inverse systems of abelian groups.
  have h₁ :
      (Ksys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE (a.reindex.monotone h)).op ≫
          (preadditiveCoyoneda.obj (op L)).map (a.map n) =
        (preadditiveCoyoneda.obj (op L)).map
          (Ksys.map (homOfLE (a.reindex.monotone h)).op ≫ a.map n) := by
    simpa using
      (Functor.map_comp
        (preadditiveCoyoneda.obj (op L))
        (Ksys.map (homOfLE (a.reindex.monotone h)).op)
        (a.map n)).symm
  have h₂ :
      (preadditiveCoyoneda.obj (op L)).map
          (Ksys.map (homOfLE (a.reindex.monotone h)).op ≫ a.map n) =
        (preadditiveCoyoneda.obj (op L)).map
          (a.map n' ≫ Msys.map (homOfLE h).op) := by
    rw [(a.comm h).w]
  have h₃ :
      (preadditiveCoyoneda.obj (op L)).map
          (a.map n' ≫ Msys.map (homOfLE h).op) =
        (preadditiveCoyoneda.obj (op L)).map (a.map n') ≫
          (Msys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE h).op := by
    simpa using
      (Functor.map_comp
        (preadditiveCoyoneda.obj (op L))
        (a.map n')
        (Msys.map (homOfLE h).op))
  exact h₁.trans (h₂.trans h₃)

/-- The induced representative on the sequential inverse systems of abelian groups
`Hom_D(L, K_n)` and `Hom_D(L, M_n)`. -/
private def preadditiveCoyonedaRep
    (a : SeqRep Ksys Msys) (L : D) :
    SeqRep
      (Ksys ⋙ preadditiveCoyoneda.obj (op L))
      (Msys ⋙ preadditiveCoyoneda.obj (op L)) where
  reindex := a.reindex
  hom :=
    { app := fun n ↦ (preadditiveCoyoneda.obj (op L)).map (a.map n.unop)
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using preadditiveCoyonedaRep_comm a L h }

/-- Helper for Lemma 15.87.6: a representative-level pro-isomorphism induces an isomorphism of
the associated owner-level pro-object morphism. -/
private theorem isIso_toProObjectHom_of_isProIsomorphism
    {C : Type*} [Category C]
    {X Y : ℕᵒᵖ ⥤ C} (r : SequentialProObjectMorphismRep X Y)
    (hr : r.IsProIsomorphism) :
    IsIso r.toProObjectHom := by
  -- Proof comment: pro-isomorphism gives bijectivity on every Hom-colimit evaluation, and those
  -- pointwise bijections assemble to an isomorphism of functors.
  letI : ∀ Z : C, IsIso (r.toProObjectHom.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (r.toProObjectHom.app Z)).2
      (SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective hr Z)
  exact NatIso.isIso_of_isIso_app r.toProObjectHom

/-- Helper for Lemma 15.87.6: applying a functor to the level maps of a sequential representative
produces the corresponding representative between the whiskered towers. -/
private theorem mapRep_naturality
    {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E)
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y) :
    ∀ ⦃X₁ Y₁ : ℕᵒᵖ⦄ (g : X₁ ⟶ Y₁),
      F.map (((r.reindex.toFunctor.op ⋙ X).map g)) ≫ F.map (r.hom.app Y₁) =
        F.map (r.hom.app X₁) ≫ F.map (Y.map g) := by
  -- Route correction: the only missing step here is the fully general whiskered naturality
  -- statement for representatives, matching the shape expected by `mapRep`.
  intro X₁ Y₁ g
  -- Proof comment: this is just `r.hom.naturality g` with every stage map transported through
  -- `F`.
  simpa [Functor.map_comp] using congrArg (fun t ↦ F.map t) (r.hom.naturality g)

/-- Helper for Lemma 15.87.6: a sequential representative may be transported through any functor
by mapping all of its stage morphisms. -/
private def mapRep
    {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E)
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y) :
    SequentialProObjectMorphismRep (X ⋙ F) (Y ⋙ F) where
  reindex := r.reindex
  hom :=
    { app := fun n ↦ F.map (r.hom.app n)
      naturality := mapRep_naturality F r }

/-- Helper for Lemma 15.87.6: if the owner-level pro-object morphism represented by `r` is an
isomorphism, then `r` already carries representative-level inverse data. -/
private theorem isProIsomorphism_of_isIso_toProObjectHom
    {C : Type*} [Category C]
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (hrIso : IsIso r.toProObjectHom) :
    r.IsProIsomorphism := by
  -- Route correction: `Lemma 15.87.4` already isolates the real blocker here: the owner-level
  -- composition law for `toProObjectHom` is not the naive natural-transformation composition, so
  -- the representative inverse extraction cannot yet be completed from the current API.
  -- TODO: add the correct Chapter 4 owner-level composition bridge for `toProObjectHom`, then
  -- compare `compRep r s` and `compRep s r` with the identity representatives via
  -- `represents_eq_iff_equivalent`.
  let _ := hrIso
  sorry

/-- Helper for Lemma 15.87.6: applying a functor to a representative-level pro-isomorphism
preserves the representative-level inverse data. -/
private theorem mapRep_isProIsomorphism
    {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E)
    {X Y : ℕᵒᵖ ⥤ C}
    {r : SequentialProObjectMorphismRep X Y}
    (hr : r.IsProIsomorphism) :
    (mapRep F r).IsProIsomorphism := by
  -- Route correction: the only remaining work here is an interface lemma identifying the
  -- stagewise maps of `compRep` and `idRep` after applying `F`, so that the common-refinement
  -- equalities for `hr` can be transported verbatim.
  -- TODO: add those two thin rewrite lemmas, then map the inverse witness stagewise through `F`
  -- exactly as in Lemma `15.87.13`.
  let _ := hr
  sorry

/-- Helper for Lemma 15.87.6: if a representative induces an isomorphism in the pro-category,
then the same holds after transporting the representative through any functor. -/
private theorem mapRep_toProObjectHom_isIso
    {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E)
    {X Y : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    [IsIso r.toProObjectHom] :
    IsIso (mapRep F r).toProObjectHom := by
  -- Proof comment: recover the representative inverse data from the owner-level isomorphism,
  -- transport that inverse data through `F`, and return to the owner level.
  have hr : r.IsProIsomorphism := by
    exact isProIsomorphism_of_isIso_toProObjectHom r (inferInstance : IsIso r.toProObjectHom)
  have hmap : (mapRep F r).IsProIsomorphism := mapRep_isProIsomorphism F hr
  exact isIso_toProObjectHom_of_isProIsomorphism (mapRep F r) hmap

end SequentialProObjectMorphismRep

section ProductMaps

variable {A B : SequentialInverseSystem D}
variable [HasProduct (inverseSystemFamily A)] [HasProduct (inverseSystemFamily B)]

/-- Helper for Lemma 15.87.6: the first Milnor product map attached to a representative is the
product of its level maps. -/
private abbrev firstProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n

/-- Helper for Lemma 15.87.6: the `n`-th component of the second Milnor product map is the
telescoping interval sum between the representative indices `m_n` and `m_{n+1}`. -/
private abbrev secondProductComponent (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (r.reindex (n + 1) - r.reindex n)) fun k ↦
    Pi.π (inverseSystemFamily A) (r.reindex n + k) ≫
      A.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.map n

/-- Helper for Lemma 15.87.6: the second Milnor product map is assembled from the telescoping
components. -/
private def secondProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ secondProductComponent r n

/-- Helper for Lemma 15.87.6: transition maps in a sequential inverse system compose in the
expected order. -/
private theorem transitionMap_comp
    (F : SequentialInverseSystem D) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (hij.trans hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- Proof comment: this is just functoriality for the unique order morphisms in `ℕᵒᵖ`.
  have hh :
      (homOfLE (hij.trans hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, hh] using
    (F.map_comp ((homOfLE hjk).op) ((homOfLE hij).op))

/-- Helper for Lemma 15.87.6: if two projection indices agree, then the corresponding projection
followed by the matching transition map is unchanged after transport along that equality. -/
private theorem projection_transition_transport_eq
    (F : SequentialInverseSystem D) {m i j : ℕ}
    [HasProduct (inverseSystemFamily F)]
    (hij : i = j) (hi : m ≤ i) (hj : m ≤ j) :
    Pi.π (inverseSystemFamily F) i ≫ F.transitionMap hi =
      Pi.π (inverseSystemFamily F) j ≫ F.transitionMap hj := by
  -- Proof comment: after substituting the endpoint equality, the two transition proofs live in a
  -- subsingleton and therefore define the same morphism.
  subst hij
  simpa using congrArg
    (fun h : m ≤ i ↦ Pi.π (inverseSystemFamily F) i ≫ F.transitionMap h)
    (Subsingleton.elim hi hj)

/-- Helper for Lemma 15.87.6: the first Milnor product map is computed projectionwise. -/
private theorem firstProductMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n := by
  -- Proof comment: the `n`-th product projection picks out the `n`-th representative component.
  rw [firstProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.6: the successor projection of the first Milnor product map is the
successor representative component. -/
private theorem firstProductMap_π_succ (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ Pi.π (inverseSystemFamily B) (n + 1) =
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫ r.map (n + 1) := by
  -- Proof comment: this is the projection formula specialized to the successor stage.
  simpa using firstProductMap_π r (n + 1)

/-- Helper for Lemma 15.87.6: the second Milnor product map is computed projectionwise. -/
private theorem secondProductMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    secondProductMap r ≫ Pi.π (inverseSystemFamily B) n =
      secondProductComponent r n := by
  -- Proof comment: the `n`-th product projection picks out the `n`-th telescoping component.
  rw [secondProductMap, Pi.lift_π]

/-- Helper for Lemma 15.87.6: the finite sum of successive transported differences telescopes to
the two boundary terms. -/
private theorem transition_sum_telescope
    (A : SequentialInverseSystem D) [HasProduct (inverseSystemFamily A)] (m c : ℕ) :
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
      -- Proof comment: the empty interval contributes no summands, so only the initial boundary
      -- term remains.
      simp [SequentialInverseSystem.transitionMap]
  | succ c ih =>
      -- Proof comment: split off the final summand and rewrite the new boundary map as a
      -- composite so the middle terms cancel additively.
      rw [Finset.sum_range_succ, ih]
      have hcomp :
          A.transitionMap (Nat.le_add_right m (c + 1)) =
            A.transitionMap (Nat.le_succ (m + c)) ≫
              A.transitionMap (Nat.le_add_right m c) := by
        simpa [Nat.add_assoc] using
          transitionMap_comp A (Nat.le_add_right m c) (Nat.le_succ (m + c))
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

/-- Helper for Lemma 15.87.6: projecting the right side of the Milnor square along the `n`-th
product projection leaves only the two boundary terms coming from stages `n` and `n + 1`. -/
private theorem firstProductMap_comp_difference_projection
    (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    firstProductMap r ≫ derivedLimitDifferenceMap B ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n -
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
  -- Proof comment: expand the Milnor difference projection and read off the two first-product
  -- components that survive.
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

/-- Helper for Lemma 15.87.6: projecting the left side of the Milnor square along the `n`-th
product projection telescopes to the interval endpoints of the representative. -/
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
  -- Proof comment: project the telescoping product map, rewrite each term using the Milnor
  -- difference formula, and collapse the resulting finite sum.
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
    -- Proof comment: this is exactly the source telescoping identity postcomposed with `r.map n`.
    simpa [Preadditive.sum_comp, Preadditive.sub_comp, Category.assoc] using
      congrArg (fun t ↦ t ≫ r.map n) (transition_sum_telescope A m c)
  simpa [m, c, Preadditive.sub_comp, Category.assoc] using htel

/-- Helper for Lemma 15.87.6: the two Milnor product maps attached to a representative form the
commutative square needed to extend to a morphism of derived-limit triangles. -/
private theorem derivedLimitDifference_commSq
    (r : SequentialProObjectMorphismRep A B) :
    CommSq (derivedLimitDifferenceMap A) (firstProductMap r) (secondProductMap r)
      (derivedLimitDifferenceMap B) := by
  -- Route correction: follow the Milnor proof from Lemma 15.87.4 exactly by projecting to each
  -- product factor, telescoping the left side, and identifying the remaining endpoint via
  -- `r.comm (Nat.le_succ n)`.
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
    -- Proof comment: rewrite the telescoping endpoint to the actual successor stage.
    exact projection_transition_transport_eq A
      (Nat.add_sub_of_le (r.reindex.monotone (Nat.le_succ n)))
      (Nat.le_add_right _ _) (r.reindex.monotone (Nat.le_succ n))
  have hcomm :
      Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          A.transitionMap (r.reindex.monotone (Nat.le_succ n)) ≫
            r.map n =
        Pi.π (inverseSystemFamily A) (r.reindex (n + 1)) ≫
          r.map (n + 1) ≫ B.transitionMap (Nat.le_succ n) := by
    -- Proof comment: the representative compatibility identifies the transported endpoint with
    -- the right boundary term.
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
    -- Proof comment: postcompose the endpoint transport with `r.map n` so it can be used inside
    -- the telescoped subtraction.
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.map n) hendpoint
  calc
    (derivedLimitDifferenceMap A ≫ secondProductMap r) ≫ Pi.π (inverseSystemFamily B) n =
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
    _ = (firstProductMap r ≫ derivedLimitDifferenceMap B) ≫ Pi.π (inverseSystemFamily B) n := by
          simpa [Category.assoc] using
            (firstProductMap_comp_difference_projection r n).symm

end ProductMaps

section MilnorComparison

variable {Ksys Msys : ℕᵒᵖ ⥤ D} {K M : D}
variable [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Msys)]
variable {ιK : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
variable {δK : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧}
variable {ιM : M ⟶ ∏ᶜ inverseSystemFamily Msys}
variable {δM : ∏ᶜ inverseSystemFamily Msys ⟶ M⟦(1 : ℤ)⟧}

/-- Helper for Lemma 15.87.6: the owner-level `R^1 \!\varprojlim` map on the shifted
represented-Hom tower may be computed using the whiskered representative `a`. -/
private theorem shifted_represented_hom_inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
    (a : SequentialProObjectMorphismRep Ksys Msys) (L : D) :
    inducedFirstDerivedLimitMap
        ((SequentialProObjectMorphismRep.mapRep
            (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).toProObjectHom) =
      (SequentialProObjectMorphismRep.mapRep
          (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).firstDerivedLimitMap := by
  -- Proof comment: `inducedFirstDerivedLimitMap` is representative-independent, so for the
  -- whiskered pro-morphism we may evaluate it on the literal whiskered representative.
  simpa using
    (inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
      (η := (SequentialProObjectMorphismRep.mapRep
        (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).toProObjectHom)
      (r := SequentialProObjectMorphismRep.mapRep
        (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a)
      rfl)

/-- Helper for Lemma 15.87.6: the owner-level inverse-limit map on the represented-Hom tower may
be computed using the whiskered representative `a`. -/
private theorem represented_hom_inducedLimitMap_eq_limitMap
    (a : SequentialProObjectMorphismRep Ksys Msys) (L : D) :
    inducedLimitMap
        ((SequentialProObjectMorphismRep.mapRep
            (preadditiveCoyoneda.obj (op L)) a).toProObjectHom) =
      (SequentialProObjectMorphismRep.mapRep
          (preadditiveCoyoneda.obj (op L)) a).limitMap := by
  -- Proof comment: the inverse-limit owner map is likewise computed by any representative of the
  -- same pro-morphism, so the whiskered representative gives the required formula directly.
  simpa using
    (inducedLimitMap_eq_limitMap
      (η := (SequentialProObjectMorphismRep.mapRep
        (preadditiveCoyoneda.obj (op L)) a).toProObjectHom)
      (r := SequentialProObjectMorphismRep.mapRep
        (preadditiveCoyoneda.obj (op L)) a)
      rfl)

/-- Helper for Lemma 15.87.6: after fixing the Milnor triangles and the triangle morphism `φT`,
the remaining source-faithful task is to construct the represented-Hom Milnor row morphism whose
outer components are the representative-level `R^1 \!\varprojlim` and `\varprojlim` maps induced
by `a`. -/
private theorem homToDerivedLimit_shortExact_row_morphism_of_triangle
    (hδK : Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ∈ distTriang D)
    (hδM : Triangle.mk ιM (derivedLimitDifferenceMap Msys) δM ∈ distTriang D)
    (a : SequentialProObjectMorphismRep Ksys Msys)
    (φT :
      Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ⟶
        Triangle.mk ιM (derivedLimitDifferenceMap Msys) δM)
    (hφ₂ : φT.hom₂ = firstProductMap a)
    (hφ₃ : φT.hom₃ = secondProductMap a)
    (L : D) :
    ∃ (ιK' :
        SequentialInverseSystem.firstDerivedLimit
            ((Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyoneda.obj (op L)) ⟶
          (preadditiveCoyoneda.obj (op L)).obj K)
      (πK :
        (preadditiveCoyoneda.obj (op L)).obj K ⟶
          limit (Ksys ⋙ preadditiveCoyoneda.obj (op L)))
      (hK' : ιK' ≫ πK = 0)
      (hshortK : (ShortComplex.mk ιK' πK hK').ShortExact)
      (ιM' :
        SequentialInverseSystem.firstDerivedLimit
            ((Msys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyoneda.obj (op L)) ⟶
          (preadditiveCoyoneda.obj (op L)).obj M)
      (πM :
        (preadditiveCoyoneda.obj (op L)).obj M ⟶
          limit (Msys ⋙ preadditiveCoyoneda.obj (op L)))
      (hM' : ιM' ≫ πM = 0)
      (hshortM : (ShortComplex.mk ιM' πM hM').ShortExact)
      (ψ : (ShortComplex.mk ιK' πK hK') ⟶ (ShortComplex.mk ιM' πM hM')),
      ψ.τ₁ =
        (SequentialProObjectMorphismRep.mapRep
            (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).firstDerivedLimitMap ∧
      ψ.τ₂ = (preadditiveCoyoneda.obj (op L)).map φT.hom₁ ∧
      ψ.τ₃ =
        (SequentialProObjectMorphismRep.mapRep
            (preadditiveCoyoneda.obj (op L)) a).limitMap := by
  -- Route correction: the owner-level induced maps are no longer part of this blocker. The only
  -- remaining source-proof step is to expose the fixed represented-Hom Milnor rows for `hδK`
  -- and `hδM`, then descend the five-term comparison induced by `φT` to a morphism of those
  -- short exact rows.
  let _ := hδK
  let _ := hδM
  let _ := hφ₂
  let _ := hφ₃
  -- TODO: build the two explicit represented-Hom Milnor short exact rows attached to the chosen
  -- Milnor maps `ιK` and `ιM`, construct the row morphism using
  -- `ComposableArrows.homMk₅` and `Functor.homologySequenceδ_naturality`, and identify the outer
  -- components with the representative-level maps of the whiskered representatives via the fixed
  -- product-map formulas already established above.
  sorry

/-- Helper for Lemma 15.87.6: once the Milnor triangle morphism has been fixed, applying
`Hom_D(L,-)` should yield a morphism between the two Milnor short exact rows whose outer maps are
the canonical `R^1 \!\varprojlim` and `\varprojlim` comparison maps coming from the represented
Hom towers. -/
private theorem homToDerivedLimit_shortExact_naturality
    (hδK : Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ∈ distTriang D)
    (hδM : Triangle.mk ιM (derivedLimitDifferenceMap Msys) δM ∈ distTriang D)
    (a : SequentialProObjectMorphismRep Ksys Msys)
    (φT :
      Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ⟶
        Triangle.mk ιM (derivedLimitDifferenceMap Msys) δM)
    (hφ₂ : φT.hom₂ = firstProductMap a)
    (hφ₃ : φT.hom₃ = secondProductMap a)
    (L : D) :
    ∃ (ιK' :
        SequentialInverseSystem.firstDerivedLimit
            ((Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyoneda.obj (op L)) ⟶
          (preadditiveCoyoneda.obj (op L)).obj K)
      (πK :
        (preadditiveCoyoneda.obj (op L)).obj K ⟶
          limit (Ksys ⋙ preadditiveCoyoneda.obj (op L)))
      (hK' : ιK' ≫ πK = 0)
      (hshortK : (ShortComplex.mk ιK' πK hK').ShortExact)
      (ιM' :
        SequentialInverseSystem.firstDerivedLimit
            ((Msys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyoneda.obj (op L)) ⟶
          (preadditiveCoyoneda.obj (op L)).obj M)
      (πM :
        (preadditiveCoyoneda.obj (op L)).obj M ⟶
          limit (Msys ⋙ preadditiveCoyoneda.obj (op L)))
      (hM' : ιM' ≫ πM = 0)
      (hshortM : (ShortComplex.mk ιM' πM hM').ShortExact)
      (ψ : (ShortComplex.mk ιK' πK hK') ⟶ (ShortComplex.mk ιM' πM hM')),
      ψ.τ₁ =
        inducedFirstDerivedLimitMap
          ((SequentialProObjectMorphismRep.mapRep
              (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).toProObjectHom) ∧
      ψ.τ₂ = (preadditiveCoyoneda.obj (op L)).map φT.hom₁ ∧
      ψ.τ₃ =
        inducedLimitMap
          ((SequentialProObjectMorphismRep.mapRep
              (preadditiveCoyoneda.obj (op L)) a).toProObjectHom) := by
  rcases
      homToDerivedLimit_shortExact_row_morphism_of_triangle
        (hδK := hδK) (hδM := hδM) a φT hφ₂ hφ₃ L with
    ⟨ιK', πK, hK', hshortK, ιM', πM, hM', hshortM, ψ, hψ₁, hψ₂, hψ₃⟩
  refine ⟨ιK', πK, hK', hshortK, ιM', πM, hM', hshortM, ψ, ?_, hψ₂, ?_⟩
  · -- Proof comment: rewrite the representative-level left component to the owner-level
    -- `inducedFirstDerivedLimitMap` for the whiskered represented-Hom pro-morphism.
    calc
      ψ.τ₁ =
          (SequentialProObjectMorphismRep.mapRep
              (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).firstDerivedLimitMap :=
        hψ₁
      _ =
          inducedFirstDerivedLimitMap
            ((SequentialProObjectMorphismRep.mapRep
                (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).toProObjectHom) := by
          symm
          exact
            shifted_represented_hom_inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
              (a := a) (L := L)
  · -- Proof comment: the same representative-independence rewrite identifies the right component
    -- with the owner-level inverse-limit map on the represented-Hom tower.
    calc
      ψ.τ₃ =
          (SequentialProObjectMorphismRep.mapRep
              (preadditiveCoyoneda.obj (op L)) a).limitMap :=
        hψ₃
      _ =
          inducedLimitMap
            ((SequentialProObjectMorphismRep.mapRep
                (preadditiveCoyoneda.obj (op L)) a).toProObjectHom) := by
          symm
          exact represented_hom_inducedLimitMap_eq_limitMap (a := a) (L := L)

end MilnorComparison

-- Proof sketch: choose a representative `a` of `η` by Example `4.22.6`, then compare the two
-- Milnor triangles attached to `hK` and `hM` via the product maps constructed from `a`. For each
-- test object `L`, the represented-Hom towers carry the same pro-isomorphism information by
-- `preadditiveCoyonedaRep a L`, so Lemma 15.87.4 provides the outer isomorphisms needed in the
-- Milnor short exact sequences. The remaining blocker is to package that comparison functorially
-- in `L`.
/-- Lemma 15.87.6: let `D` be a triangulated category, let `(K_n)` and `(M_n)` be inverse systems
of objects of `D` with derived limits `K` and `M`, and let `η` be an isomorphism between the
associated pro-objects. Then `η` induces a non-canonical isomorphism `K ⟶ M` between the chosen
derived limits. -/
@[stacks 0H9L]
theorem exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
    {Ksys Msys : ℕᵒᵖ ⥤ D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
      proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}) [IsIso η] :
    ∃ f : K ⟶ M, IsIso f := by
  classical
  obtain ⟨a, ha⟩ := exists_representative η
  rcases hK with ⟨_, ⟨ιK, δK, hδK⟩⟩
  rcases hM with ⟨_, ⟨ιM, δM, hδM⟩⟩
  have haIso : IsIso a.toProObjectHom := by
    rw [ha]
    infer_instance
  letI : IsIso a.toProObjectHom := haIso
  have hcomm :
      CommSq (derivedLimitDifferenceMap Ksys) (firstProductMap a) (secondProductMap a)
        (derivedLimitDifferenceMap Msys) :=
    derivedLimitDifference_commSq a
  obtain ⟨φT, hφ₂, hφ₃⟩ :=
    exists_triangleMorphism_between_derivedLimit_triangles
      (hK := hδK) (hL := hδM) (hcomm := hcomm)
  let f : K ⟶ M := φT.hom₁
  -- Route correction: the candidate map `f` and the Milnor triangle morphism are now fixed. The
  -- remaining source-faithful step is exactly to compare the represented-Hom Milnor short exact
  -- rows for `Ksys` and `Msys` and then apply Yoneda to the resulting family of middle
  -- isomorphisms.
  have hHomIso : ∀ L : D, IsIso ((preadditiveCoyoneda.obj (op L)).map f) := by
    intro L
    -- Proof comment: compare the two Milnor short exact rows for the fixed triangle morphism
    -- `φT`; Lemma `15.87.4` gives isomorphisms on the outer terms, so the middle map is an
    -- isomorphism by the short exact sequence comparison lemma.
    obtain
      ⟨ιK', πK, hK', hshortK, ιM', πM, hM', hshortM, ψ, hψ₁, hψ₂, hψ₃⟩ :=
      homToDerivedLimit_shortExact_naturality
        (hδK := hδK) (hδM := hδM) a φT hφ₂ hφ₃ L
    let ηShift :
        colimit
            (((Msys ⋙ shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)).op) ⋙
              uliftCoyoneda.{0}) ⟶
          proSystemHomColimitFunctor
              (Ksys ⋙ shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) ⋙
            uliftFunctor.{0} :=
      (SequentialProObjectMorphismRep.mapRep
          (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a).toProObjectHom
    let ηUnshift :
        colimit (((Msys ⋙ preadditiveCoyoneda.obj (op L)).op) ⋙ uliftCoyoneda.{0}) ⟶
          proSystemHomColimitFunctor (Ksys ⋙ preadditiveCoyoneda.obj (op L)) ⋙
            uliftFunctor.{0} :=
      (SequentialProObjectMorphismRep.mapRep
          (preadditiveCoyoneda.obj (op L)) a).toProObjectHom
    have hηShiftIso : IsIso ηShift := by
      dsimp [ηShift]
      exact
        SequentialProObjectMorphismRep.mapRep_toProObjectHom_isIso
          (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)) a
    have hηUnshiftIso : IsIso ηUnshift := by
      dsimp [ηUnshift]
      exact
        SequentialProObjectMorphismRep.mapRep_toProObjectHom_isIso
          (preadditiveCoyoneda.obj (op L)) a
    have hleftIso :
        IsIso (inducedFirstDerivedLimitMap ηShift) := by
      letI : IsIso ηShift := hηShiftIso
      exact
        (inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
          (η := ηShift)).2
    have hrightIso :
        IsIso (inducedLimitMap ηUnshift) := by
      letI : IsIso ηUnshift := hηUnshiftIso
      exact
        (inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
          (η := ηUnshift)).1
    haveI : IsIso ψ.τ₁ := by
      simpa [hψ₁] using hleftIso
    haveI : IsIso ψ.τ₃ := by
      simpa [hψ₃] using hrightIso
    have hmiddleIso : IsIso ψ.τ₂ :=
      ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ hshortK hshortM
    simpa [f, hψ₂] using hmiddleIso
  let g : M ⟶ K :=
    (inv ((preadditiveCoyoneda.obj (op M)).map f)).hom (𝟙 M)
  have hgf : g ≫ f = 𝟙 M := by
    -- Proof comment: `g` was chosen as the preimage of `𝟙_M` under the covariant Hom-map
    -- induced by `f`.
    have hgf' :
        ((preadditiveCoyoneda.obj (op M)).map f).hom g = 𝟙 M := by
      change
        ((inv ((preadditiveCoyoneda.obj (op M)).map f) ≫
            (preadditiveCoyoneda.obj (op M)).map f).hom) (𝟙 M) =
          𝟙 M
      rw [IsIso.inv_hom_id]
      rfl
    simpa [g, f] using hgf'
  have hfg : f ≫ g = 𝟙 K := by
    -- Proof comment: the map on `Hom_D(K, -)` induced by `f` is injective, so the equality
    -- `((f ≫ g) ≫ f) = f` forces `f ≫ g = 𝟙_K`.
    have hbij :
        Function.Bijective (ConcreteCategory.hom ((preadditiveCoyoneda.obj (op K)).map f)) := by
      exact (ConcreteCategory.isIso_iff_bijective ((preadditiveCoyoneda.obj (op K)).map f)).1
        (hHomIso K)
    apply hbij.1
    change (f ≫ g) ≫ f = (𝟙 K) ≫ f
    simpa [Category.assoc, hgf]
  have hIsof : IsIso f := by
    letI : IsIso f := ⟨⟨g, hfg, hgf⟩⟩
    infer_instance
  exact ⟨f, hIsof⟩

end

end CategoryTheory
