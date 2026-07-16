import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_14_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex ChainComplex

universe v u

noncomputable section

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-- Helper for Lemma 12.14.3: the chain-to-cochain bridge is the canonical equivalence functor. -/
private abbrev chainToCochain :
    ChainComplex V ℤ ⥤ PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ) :=
  (ChainComplex.cochainComplexEquivalence V).functor

/-- Helper for Lemma 12.14.3: the inverse cochain-to-chain bridge. -/
private abbrev cochainToChain :
    PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ) ⥤ ChainComplex V ℤ :=
  (ChainComplex.cochainComplexEquivalence V).inverse

/-- Helper for Lemma 12.14.3: the chain shift is transported from the cochain shift along the
canonical chain/cochain equivalence. -/
private abbrev chain_shift_aux (k : ℤ) :
    ChainComplex V ℤ ⥤ ChainComplex V ℤ :=
  chainToCochain ⋙ shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k ⋙
    cochainToChain

/-- Helper for Lemma 12.14.3: the counit comparison is natural for the transported shift. -/
private theorem chain_shift_aux_iso_hom_naturality (k : ℤ) {K L : ChainComplex V ℤ} (φ : K ⟶ L) :
    ((chain_shift_aux (V := V) k ⋙ chainToCochain (V := V)).map φ) ≫
        ((ChainComplex.cochainComplexEquivalence V).counitIso.app
          ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k).obj
            ((chainToCochain (V := V)).obj L))).hom =
      ((ChainComplex.cochainComplexEquivalence V).counitIso.app
          ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k).obj
            ((chainToCochain (V := V)).obj K))).hom ≫
        (((chainToCochain (V := V)) ⋙
            shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k).map φ) := by
  -- Compare both sides degreewise and use naturality of the counit morphism.
  convert ((ChainComplex.cochainComplexEquivalence V).counitIso.hom.naturality
    ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k).map
      ((chainToCochain (V := V)).map φ))) using 1

/-- Helper for Lemma 12.14.3: the transported shift identifies the chain shift with the cochain
shift under `chainToCochain`. -/
private noncomputable abbrev chain_shift_aux_iso (k : ℤ) :
    chain_shift_aux (V := V) k ⋙ chainToCochain (V := V) ≅
      chainToCochain (V := V) ⋙
        shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k :=
  NatIso.ofComponents
    (fun K ↦
      (ChainComplex.cochainComplexEquivalence V).counitIso.app
        ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ)) k).obj
          ((chainToCochain (V := V)).obj K)))
    (chain_shift_aux_iso_hom_naturality (V := V) k)

/-- Helper for Lemma 12.14.3: the chain-complex category inherits the integer shift transported
from cochain complexes. -/
private noncomputable instance instHasShiftChainComplex :
    HasShift (ChainComplex V ℤ) ℤ :=
  Functor.FullyFaithful.hasShift
    (Functor.FullyFaithful.ofFullyFaithful (chainToCochain (V := V)))
    (chain_shift_aux (V := V))
    (chain_shift_aux_iso (V := V))

/-- Helper for Lemma 12.14.3: after transporting the shift, `chainToCochain` commutes with
integer shifts. -/
private noncomputable abbrev chain_to_cochain_commShift :
    (chainToCochain (V := V)).CommShift ℤ :=
  by
    -- Reuse the fully faithful transport of the shift from the cochain side.
    let hF : (chainToCochain (V := V)).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
    exact Functor.CommShift.ofHasShiftOfFullyFaithful hF
      (chain_shift_aux (V := V)) (chain_shift_aux_iso (V := V))

local instance : (chainToCochain (V := V)).CommShift ℤ := chain_to_cochain_commShift (V := V)

/- Source/core/bridge triage:
- source-facing:
  `chainComplex_self_homotopy_equiv_hom_to_shift`.
- core/canonical owner declarations in this domain:
  `CategoryTheory.Functor.mapHomotopy`,
  `ChainComplex.chainToCochain V`,
  `cochainComplex_self_homotopy_equiv_hom_to_shift` from `Lemma_12_14_9`,
  and the ambient equivalence `cochainComplexEquivalence V`.
- target item here: a chain-complex bridge/view obtained by transporting those owner
  equivalences across `cochainComplexEquivalence V`.

Primitive data:
- the canonical bridge `ChainComplex.chainToCochain V`,
- the induced entrywise transport of homotopies across that equivalence,
- the induced equivalence on shifted morphisms from full faithfulness and the canonical
  commutation isomorphism `((ChainComplex.chainToCochain V).commShiftIso (1)).app B`.

Derived API:
- `homotopyEquivSelf`,
- `homotopy_isEmpty_or_nonempty_equiv`,
- `chainToCochainHomotopyEquiv`,
- `chainComplex_self_homotopy_equiv_hom_to_shift`,
- `chainComplex_homotopy_isEmpty_or_exists_hom_to_shift_bijection`.
-/

/-- Helper for Lemma 12.14.3: a chain homotopy transports to a cochain homotopy by negating the
indices. -/
private def chain_to_cochain_homotopy_forward_hom {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    (p q : ℤ) →
      ((chainToCochain (V := V)).obj A).X p ⟶ ((chainToCochain (V := V)).obj B).X q :=
  fun p q ↦ h.hom (-p) (-q)

/-- Helper for Lemma 12.14.3: the forward transport still vanishes away from adjacent degrees. -/
private theorem chain_to_cochain_homotopy_forward_zero {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    ∀ p q : ℤ, ¬(ComplexShape.up ℤ).Rel q p →
      chain_to_cochain_homotopy_forward_hom (V := V) h p q = 0 := by
  intro p q hpq
  dsimp [chain_to_cochain_homotopy_forward_hom]
  rw [h.zero (-p) (-q)]
  · rfl
  · dsimp at hpq ⊢
    omega

/-- Helper for Lemma 12.14.3: the forward transport satisfies the cochain homotopy identity. -/
private theorem chain_to_cochain_homotopy_forward_comm {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    ∀ n : ℤ,
      ((chainToCochain (V := V)).map a).f n =
        (dNext n) (chain_to_cochain_homotopy_forward_hom (V := V) h) +
          (prevD n) (chain_to_cochain_homotopy_forward_hom (V := V) h) +
            ((chainToCochain (V := V)).map b).f n := by
  intro n
  -- TODO: normalize the remaining `dFrom`/`dTo` transport in `h.comm (-n)` to the cochain-side
  -- `dNext`/`prevD` formula by explicit restriction-by-negation rewrites, following the source
  -- proof pattern used in `CochainComplex.homotopyOp`.
  sorry

/-- Helper for Lemma 12.14.3: a chain homotopy transports to a cochain homotopy by negating the
indices. -/
private def chain_to_cochain_homotopy_forward {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b) :=
  Homotopy.mk
    (chain_to_cochain_homotopy_forward_hom (V := V) h)
    (chain_to_cochain_homotopy_forward_zero (V := V) h)
    (chain_to_cochain_homotopy_forward_comm (V := V) h)

/-- Helper for Lemma 12.14.3: a transported cochain homotopy pulls back to a chain homotopy by
undoing the negated indexing with the canonical `XIsoOfEq` comparison isomorphisms. -/
private def chain_to_cochain_homotopy_backward_hom {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    (i j : ℤ) → A.X i ⟶ B.X j :=
  fun i j ↦
    (A.XIsoOfEq (by simp)).hom ≫ h.hom (-i) (-j) ≫ (B.XIsoOfEq (by simp)).hom

/-- Helper for Lemma 12.14.3: the backward transport still vanishes away from adjacent degrees. -/
private theorem chain_to_cochain_homotopy_backward_zero {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    ∀ i j : ℤ, ¬(ComplexShape.down ℤ).Rel j i →
      chain_to_cochain_homotopy_backward_hom (V := V) h i j = 0 := by
  intro i j hij
  -- TODO: transport `h.zero (-i) (-j)` across the two `XIsoOfEq` comparison maps and then
  -- close the resulting zero-composition equality explicitly.
  sorry

/-- Helper for Lemma 12.14.3: the backward transport satisfies the chain homotopy identity. -/
private theorem chain_to_cochain_homotopy_backward_comm {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    ∀ n : ℤ,
      a.f n =
        (dNext n) (chain_to_cochain_homotopy_backward_hom (V := V) h) +
          (prevD n) (chain_to_cochain_homotopy_backward_hom (V := V) h) + b.f n := by
  intro n
  -- Route correction: rewrite the chain-side degree `n` as `-m`, then conjugate `h.comm m`
  -- through the `XIsoOfEq` comparisons to identify the two summands with `dNext` and `prevD`.
  -- The remaining blocker is the exact normalization of the negated predecessor/successor indices.
  sorry

/-- Helper for Lemma 12.14.3: a transported cochain homotopy pulls back to a chain homotopy by
undoing the negated indexing with the canonical `XIsoOfEq` comparison isomorphisms. -/
private def chain_to_cochain_homotopy_backward {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    Homotopy a b :=
  Homotopy.mk
    (chain_to_cochain_homotopy_backward_hom (V := V) h)
    (chain_to_cochain_homotopy_backward_zero (V := V) h)
    (chain_to_cochain_homotopy_backward_comm (V := V) h)

/-- Helper for Lemma 12.14.3: transporting a chain homotopy to cochains and back recovers the
original homotopy. -/
private theorem chain_to_cochain_homotopy_forward_backward {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    chain_to_cochain_homotopy_backward (V := V) (chain_to_cochain_homotopy_forward (V := V) h) =
      h := by
  -- The round trip only inserts and cancels the canonical double-negation comparison isomorphisms.
  -- TODO: after the backward transport normalization lemmas are in place, this should reduce by
  -- `Homotopy.ext` and cancellation of the inserted `XIsoOfEq` morphisms.
  sorry

/-- Helper for Lemma 12.14.3: transporting a cochain homotopy to chains and forward again
recovers the original cochain homotopy. -/
private theorem chain_to_cochain_homotopy_backward_forward {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    chain_to_cochain_homotopy_forward (V := V) (chain_to_cochain_homotopy_backward (V := V) h) =
      h := by
  -- The reverse round trip cancels the same comparison isomorphisms on the cochain side.
  -- TODO: once the backward component formula is normalized, this is the same `Homotopy.ext`
  -- cancellation argument as the forward-backward round trip.
  sorry

/- Bridge/view owner: `chainToCochain V` transports homotopies in both directions. -/
def chainToCochainHomotopyEquiv {A B : ChainComplex V ℤ} {a b : A ⟶ B} :
    Homotopy a b ≃
      Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b) :=
  { toFun := chain_to_cochain_homotopy_forward (V := V)
    invFun := chain_to_cochain_homotopy_backward (V := V)
    left_inv := chain_to_cochain_homotopy_forward_backward (V := V)
    right_inv := chain_to_cochain_homotopy_backward_forward (V := V) }

variable {A B : ChainComplex V ℤ}

/- Bridge/view owner: under `chainToCochain V`, a morphism into the cochain `[-1]` shift is
exactly a morphism into the chain `[1]`-shift. -/
private noncomputable abbrev chainToCochainShiftHomEquiv (A B : ChainComplex V ℤ) :
    (((cochainComplexEquivalence V).functor.obj A) ⟶
      ((cochainComplexEquivalence V).functor.obj B)⟦(-1 : ℤ)⟧) ≃
        (A ⟶ B⟦(1 : ℤ)⟧) :=
  let F : ChainComplex V ℤ ⥤ PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ) :=
    chainToCochain (V := V)
  let e :
      (cochainComplexEquivalence V).functor.obj (B⟦(1 : ℤ)⟧) ≅
        ((cochainComplexEquivalence V).functor.obj B)⟦(-1 : ℤ)⟧ :=
    (show F.obj (B⟦(1 : ℤ)⟧) ≅
        ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ))
          (1 : ℤ)).obj (F.obj B)) from
        (F.commShiftIso (1 : ℤ)).app B) ≪≫
      (pullbackShiftIso (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ) (1 : ℤ) (-1 : ℤ)
        (by simp)).app (F.obj B)
  (((cochainComplexEquivalence V).fullyFaithfulFunctor.homEquiv).trans
    ((Iso.refl _).homCongr e)).symm

/-- Lemma 12.14.3: for a chain map `a : A_• ⟶ B_•`, there is a bijection between the
self-homotopies of `a` and the morphisms `A_• ⟶ B[1]_•`. -/
noncomputable def chainComplex_self_homotopy_equiv_hom_to_shift (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(1 : ℤ)⟧) :=
  chainToCochainHomotopyEquiv.trans
    ((cochainComplex_self_homotopy_equiv_hom_to_shift
        ((chainToCochain (V := V)).map a)).trans
      (chainToCochainShiftHomEquiv A B))

-- Proof sketch: if `Homotopy a b` is empty we are done. Otherwise choose a homotopy
-- `h : Homotopy a b`; translating by `h` with `homotopyEquivSelf h` and then applying
-- `chainComplex_self_homotopy_equiv_hom_to_shift a` gives the required bijection with
-- `A_• ⟶ B[1]_•`.
/-- Lemma 12.14.3: for chain maps `a, b : A_• ⟶ B_•`, the homotopies from `a` to `b` are either
empty or nonempty together with an induced equivalence to the morphisms `A_• ⟶ B[1]_•`. -/
theorem chainComplex_homotopy_isEmpty_or_exists_hom_to_shift_bijection (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (Homotopy a b ≃ (A ⟶ B⟦(1 : ℤ)⟧)) := by
  simpa using homotopy_isEmpty_or_nonempty_equiv a b
    (chainComplex_self_homotopy_equiv_hom_to_shift a)
