import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap12.Lemma_12_14_9

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

/-- Helper for Lemma 12.14.3: `chainToCochain` evaluates a chain-map component in degree `n` as
the original component in degree `-n`. -/
private theorem chainToCochainMapComponent {A B : ChainComplex V ℤ} (a : A ⟶ B) (n : ℤ) :
    ((chainToCochain (V := V)).map a).f n = a.f (-n) := by
  -- The chain-to-cochain functor is the restriction along `m ↦ -m`, so degree `n` becomes `-n`.
  change (HomologicalComplex.restrictionMap a ComplexShape.embeddingUpIntDownInt).f n = a.f (-n)
  rw [HomologicalComplex.restrictionMap_f'
    (K := A) (L := B) (φ := a) (e := ComplexShape.embeddingUpIntDownInt)
    (i := n) (i' := -n) (show -n = -n by rfl)]
  simpa [HomologicalComplex.restrictionXIso]

/-- Helper for Lemma 12.14.3: `chainToCochain` evaluates a chain differential in degrees `i, j`
as the original differential in degrees `-i, -j`. -/
private theorem chainToCochainDifferentialComponent (A : ChainComplex V ℤ) (i j : ℤ) :
    ((chainToCochain (V := V)).obj A).d i j = A.d (-i) (-j) := by
  -- The restriction differential is just the original differential after negating the indices.
  change (HomologicalComplex.restriction A ComplexShape.embeddingUpIntDownInt).d i j = A.d (-i) (-j)
  rw [HomologicalComplex.restriction_d_eq
    (K := A) (e := ComplexShape.embeddingUpIntDownInt)
    (i := i) (j := j) (i' := -i) (j' := -j)
    (show -i = -i by rfl) (show -j = -j by rfl)]
  simpa [HomologicalComplex.restrictionXIso]

/-- Helper for Lemma 12.14.3: in degree `-n`, the transported map component is the original chain
component conjugated by the double-negation comparison isomorphisms. -/
private theorem chainToCochainMapComponentNeg {A B : ChainComplex V ℤ} (a : A ⟶ B) (n : ℤ) :
    ((chainToCochain (V := V)).map a).f (-n) =
      (A.XIsoOfEq (by simp)).inv ≫ a.f n ≫ (B.XIsoOfEq (by simp)).hom := by
  -- This is the same restriction formula, now spelled at degree `-n`.
  change (HomologicalComplex.restrictionMap a ComplexShape.embeddingUpIntDownInt).f (-n) =
    (A.XIsoOfEq (by simp)).inv ≫ a.f n ≫ (B.XIsoOfEq (by simp)).hom
  rw [HomologicalComplex.restrictionMap_f'
    (K := A) (L := B) (φ := a) (e := ComplexShape.embeddingUpIntDownInt)
    (i := -n) (i' := n) (show -(-n) = n by simp)]
  simpa [HomologicalComplex.restrictionXIso, HomologicalComplex.XIsoOfEq]

/-- Helper for Lemma 12.14.3: in degrees `-i, -j`, the transported differential is the original
chain differential conjugated by the double-negation comparison isomorphisms. -/
private theorem chainToCochainDifferentialComponentNeg (A : ChainComplex V ℤ) (i j : ℤ) :
    ((chainToCochain (V := V)).obj A).d (-i) (-j) =
      (A.XIsoOfEq (by simp)).inv ≫ A.d i j ≫ (A.XIsoOfEq (by simp)).hom := by
  -- Restriction in degree `-i` identifies with the original degree `i` through double negation.
  change (HomologicalComplex.restriction A ComplexShape.embeddingUpIntDownInt).d (-i) (-j) =
    (A.XIsoOfEq (by simp)).inv ≫ A.d i j ≫ (A.XIsoOfEq (by simp)).hom
  rw [HomologicalComplex.restriction_d_eq
    (K := A) (e := ComplexShape.embeddingUpIntDownInt)
    (i := -i) (j := -j) (i' := i) (j' := j)
    (show -(-i) = i by simp) (show -(-j) = j by simp)]
  simpa [HomologicalComplex.restrictionXIso, HomologicalComplex.XIsoOfEq]

/-- Helper for Lemma 12.14.3: conjugating the degree `-n` transported component recovers the
original chain-map component in degree `n`. -/
private theorem chainToCochainMapComponentConj {A B : ChainComplex V ℤ} (a : A ⟶ B) (n : ℤ) :
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ ((chainToCochain (V := V)).map a).f (-n) ≫
      (B.XIsoOfEq (show -(-n) = n by simp)).hom = a.f n := by
  -- Rewrite the transported component at `-n` as the original degree `-(-n)` component.
  rw [chainToCochainMapComponent (V := V) a (-n)]
  -- Naturality identifies the inserted comparison maps with the original component.
  have hnat :=
    HomologicalComplex.XIsoOfEq_hom_naturality (φ := a) (h := (show n = -(-n) by simp))
  have hnat' :=
    congrArg (fun t ↦ t ≫ (B.XIsoOfEq (show -(-n) = n by simp)).hom) hnat.symm
  calc
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ a.f (-(-n)) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      a.f n ≫ (B.XIsoOfEq (show n = -(-n) by simp)).hom ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        simpa [Category.assoc] using hnat'
    _ = a.f n := by
      simp

/-- Helper for Lemma 12.14.3: the forward transport satisfies the cochain homotopy identity. -/
private theorem chain_to_cochain_homotopy_forward_comm {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy a b) :
    ∀ n : ℤ,
      ((chainToCochain (V := V)).map a).f n =
        (dNext n) (chain_to_cochain_homotopy_forward_hom (V := V) h) +
          (prevD n) (chain_to_cochain_homotopy_forward_hom (V := V) h) +
            ((chainToCochain (V := V)).map b).f n := by
  intro n
  -- Rewrite the cochain-side components as the chain-side components at degree `-n`.
  rw [chainToCochainMapComponent (V := V) a n, chainToCochainMapComponent (V := V) b n]
  dsimp [dNext, prevD, chain_to_cochain_homotopy_forward_hom]
  rw [chainToCochainDifferentialComponent (V := V) A n ((ComplexShape.up ℤ).next n)]
  rw [chainToCochainDifferentialComponent (V := V) B ((ComplexShape.up ℤ).prev n) n]
  -- The remaining arithmetic is exactly the chain homotopy identity at degree `-n`.
  have hcomm := h.comm (-n)
  rw [dNext_eq h.hom (show (ComplexShape.down ℤ).Rel (-n) ((ComplexShape.down ℤ).next (-n)) by simp),
    prevD_eq h.hom (show (ComplexShape.down ℤ).Rel ((ComplexShape.down ℤ).prev (-n)) (-n) by simp)]
    at hcomm
  rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel (-n) (-n - 1) by simp),
    (ComplexShape.down ℤ).prev_eq' (show (ComplexShape.down ℤ).Rel (-n + 1) (-n) by simp)] at hcomm
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    (ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
  have h₁ : -n - 1 = -(n + 1) := by ring
  have h₂ : -n + 1 = -(n - 1) := by ring
  rw [h₁, h₂] at hcomm
  simpa [add_assoc, add_left_comm, add_comm] using hcomm

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
  -- Transport the cochain-side vanishing statement back through the double-negation comparisons.
  dsimp [chain_to_cochain_homotopy_backward_hom]
  have hzero : h.hom (-i) (-j) = 0 := by
    exact h.zero (-i) (-j) (by
      dsimp at hij ⊢
      omega)
  rw [hzero]
  simp
  rfl

/-- Helper for Lemma 12.14.3: the backward transport satisfies the chain homotopy identity. -/
private theorem chainToCochainBackwardCommDNext {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b))
    (n : ℤ) :
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ (dNext (-n)) h.hom ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      (dNext n) (chain_to_cochain_homotopy_backward_hom (V := V) h) := by
  -- Rewrite both sides in the explicit adjacent-degree form used by chain homotopies.
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel (-n) ((ComplexShape.up ℤ).next (-n)) by simp)]
  rw [dNext_eq (chain_to_cochain_homotopy_backward_hom (V := V) h)
    (show (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) by simp)]
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (-n) (-n + 1) by simp)]
  rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel n (n - 1) by simp)]
  -- Convert the transported cochain differential into the original chain differential.
  rw [show -n + 1 = -(n - 1) by ring]
  rw [chainToCochainDifferentialComponent (V := V) A (-n) (-(n - 1))]
  -- Unfold the transported homotopy component and cancel the inserted comparison maps.
  dsimp [chain_to_cochain_homotopy_backward_hom]
  calc
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫
        (A.d (- -n) (- -(n - 1)) ≫ h.hom (-(n - 1)) (-n)) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ A.d (- -n) (- -(n - 1))) ≫
        h.hom (-(n - 1)) (-n) ≫ (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        simp [Category.assoc]
    _ = A.d n (- -(n - 1)) ≫ h.hom (-(n - 1)) (-n) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
    _ = A.d n (n - 1) ≫ (A.XIsoOfEq (show n - 1 = -(-(n - 1)) by simp)).hom ≫
        h.hom (-(n - 1)) (-n) ≫ (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        simp

/-- Helper for Lemma 12.14.3: transport the right boundary `d ≫ XIso` in the backward `prevD`
branch to the chain-side normal form. -/
private theorem chainToCochainBackwardCommPrevDRightTransport {B : ChainComplex V ℤ} {X : V}
    (n : ℤ) (g : X ⟶ B.X (-(-(n + 1)))) :
    g ≫ ((chainToCochain (V := V)).obj B).d (-(n + 1)) (-n) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      g ≫ (B.XIsoOfEq (show -(-(n + 1)) = n + 1 by simp)).hom ≫ B.d (n + 1) n := by
  -- Route correction: compare both sides to the same chain differential before rebuilding the
  -- whole `prevD` summand, so the terminal `XIsoOfEq` transport is solved once and for all.
  have hnegN : -(-n) = n := by simp
  have hnegSucc : -(-(n + 1)) = n + 1 := by simp
  -- Normalize the transported cochain differential to the chain differential at negated indices.
  calc
    g ≫ ((chainToCochain (V := V)).obj B).d (-(n + 1)) (-n) ≫ (B.XIsoOfEq hnegN).hom =
      g ≫ B.d (-(-(n + 1))) (-(-n)) ≫ (B.XIsoOfEq hnegN).hom := by
        rw [chainToCochainDifferentialComponent (V := V) B (-(n + 1)) (-n)]
        rfl
    -- Move the right comparison map across the differential using the owner transport API.
    _ = g ≫ B.d (-(-(n + 1))) n := by
        rw [HomologicalComplex.d_comp_XIsoOfEq_hom (K := B) (h := hnegN)
          (p₁ := -(-(n + 1)))]
    -- Rewrite the same chain differential back into the target comparison-map normal form.
    _ = g ≫ (B.XIsoOfEq hnegSucc).hom ≫ B.d (n + 1) n := by
        rw [← HomologicalComplex.XIsoOfEq_hom_comp_d (K := B) (h := hnegSucc) (p₃ := n)]

/-- Helper for Lemma 12.14.3: the conjugated cochain `prevD` summand is exactly the chain
`prevD` summand of the transported homotopy. -/
private theorem chainToCochainBackwardCommPrevD {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b))
    (n : ℤ) :
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ (prevD (-n)) h.hom ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      (prevD n) (chain_to_cochain_homotopy_backward_hom (V := V) h) := by
  -- Route correction: rewrite the whole summand only after the B-side differential/XIso boundary
  -- has been normalized by the dedicated transport adapter above.
  rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-(n + 1)) (-n) by simp)]
  rw [prevD_eq (chain_to_cochain_homotopy_backward_hom (V := V) h)
    (show (ComplexShape.down ℤ).Rel (n + 1) n by simp)]
  -- Expose the transported component once, then apply the exact right-transport bridge.
  dsimp [chain_to_cochain_homotopy_backward_hom]
  have htransport :
      (((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ h.hom (-n) (-(n + 1))) :
          A.X n ⟶ B.X (-(-(n + 1)))) ≫
          ((chainToCochain (V := V)).obj B).d (-(n + 1)) (-n) ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom =
        (((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ h.hom (-n) (-(n + 1))) :
          A.X n ⟶ B.X (-(-(n + 1)))) ≫
          (B.XIsoOfEq (show -(-(n + 1)) = n + 1 by simp)).hom ≫ B.d (n + 1) n := by
    exact chainToCochainBackwardCommPrevDRightTransport (V := V) n
      (((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ h.hom (-n) (-(n + 1))) :
        A.X n ⟶ B.X (-(-(n + 1))))
  calc
    (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫
        (h.hom (-n) (-(n + 1)) ≫
          ((chainToCochain (V := V)).obj B).d (-(n + 1)) (-n)) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom =
      ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ h.hom (-n) (-(n + 1))) ≫
          ((chainToCochain (V := V)).obj B).d (-(n + 1)) (-n) ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        simp [Category.assoc]
    _ = ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ h.hom (-n) (-(n + 1))) ≫
          (B.XIsoOfEq (show -(-(n + 1)) = n + 1 by simp)).hom ≫
          B.d (n + 1) n := by
        exact htransport
    _ = chain_to_cochain_homotopy_backward_hom (V := V) h n (n + 1) ≫ B.d (n + 1) n := by
      simp [chain_to_cochain_homotopy_backward_hom, Category.assoc]

/-- Helper for Lemma 12.14.3: whiskering distributes over a three-term sum in associated form. -/
private theorem whiskerThreeSummands {W X Y Z : V} (l : W ⟶ X) (x y z : X ⟶ Y) (r : Y ⟶ Z) :
    l ≫ (x + y + z) ≫ r = (l ≫ x ≫ r) + (l ≫ y ≫ r) + (l ≫ z ≫ r) := by
  -- Expand both whiskerings and reassociate the resulting sum once.
  simp [Preadditive.comp_add, Preadditive.add_comp, add_assoc]

/-- Helper for Lemma 12.14.3: the backward transport satisfies the chain homotopy identity. -/
private theorem chain_to_cochain_homotopy_backward_comm {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    ∀ n : ℤ,
      a.f n =
        (dNext n) (chain_to_cochain_homotopy_backward_hom (V := V) h) +
          (prevD n) (chain_to_cochain_homotopy_backward_hom (V := V) h) + b.f n := by
  intro n
  -- Route correction: conjugate the already-known cochain homotopy identity at degree `-n`
  -- once, and rewrite each transported summand directly into the chain-side normal form.
  have hcomm :=
    congrArg
      (fun t ↦
        (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ t ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom)
      (h.comm (-n))
  calc
    a.f n =
      (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ ((chainToCochain (V := V)).map a).f (-n) ≫
        (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        symm
        exact chainToCochainMapComponentConj (V := V) a n
    _ = (A.XIsoOfEq (show n = -(-n) by simp)).hom ≫
          ((dNext (-n)) h.hom + (prevD (-n)) h.hom +
            ((chainToCochain (V := V)).map b).f (-n)) ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom := by
        simpa using hcomm
    _ = ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ (dNext (-n)) h.hom ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom) +
        ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ (prevD (-n)) h.hom ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom) +
        ((A.XIsoOfEq (show n = -(-n) by simp)).hom ≫ ((chainToCochain (V := V)).map b).f (-n) ≫
          (B.XIsoOfEq (show -(-n) = n by simp)).hom) := by
        exact whiskerThreeSummands
          (A.XIsoOfEq (show n = -(-n) by simp)).hom
          ((dNext (-n)) h.hom) ((prevD (-n)) h.hom) (((chainToCochain (V := V)).map b).f (-n))
          (B.XIsoOfEq (show -(-n) = n by simp)).hom
    _ = (dNext n) (chain_to_cochain_homotopy_backward_hom (V := V) h) +
          (prevD n) (chain_to_cochain_homotopy_backward_hom (V := V) h) + b.f n := by
        rw [chainToCochainBackwardCommDNext (V := V) h n,
          chainToCochainBackwardCommPrevD (V := V) h n,
          chainToCochainMapComponentConj (V := V) b n]

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
  -- Relabeling across definitional equalities only inserts identity comparison maps.
  have H (p q p' q' : ℤ) (hp : p = p') (hq : q = q') :
      (A.XIsoOfEq hp).hom ≫ h.hom p' q' ≫ (B.XIsoOfEq hq.symm).hom = h.hom p q := by
    subst hp hq
    simp
  -- The round trip only inserts and cancels the canonical double-negation comparison isomorphisms.
  ext i j
  -- Unfold the component formulas and simplify the double-negation comparisons.
  dsimp [chain_to_cochain_homotopy_backward, chain_to_cochain_homotopy_forward,
    chain_to_cochain_homotopy_backward_hom, chain_to_cochain_homotopy_forward_hom]
  have hi : i = -(-i) := by simp
  have hj : j = -(-j) := by simp
  rw [hi, hj]
  simpa using H (-(-i)) (-(-j)) (-(-(-(-i)))) (-(-(-(-j)))) (by simp) (by simp)

/-- Helper for Lemma 12.14.3: transporting a cochain homotopy to chains and forward again
recovers the original cochain homotopy. -/
private theorem chain_to_cochain_homotopy_backward_forward {A B : ChainComplex V ℤ} {a b : A ⟶ B}
    (h : Homotopy ((chainToCochain (V := V)).map a) ((chainToCochain (V := V)).map b)) :
    chain_to_cochain_homotopy_forward (V := V) (chain_to_cochain_homotopy_backward (V := V) h) =
      h := by
  -- Relabeling across definitional equalities only inserts identity comparison maps.
  have H (p q p' q' : ℤ) (hp : p = p') (hq : q = q') :
      (((chainToCochain (V := V)).obj A).XIsoOfEq hp).hom ≫ h.hom p' q' ≫
        (((chainToCochain (V := V)).obj B).XIsoOfEq hq.symm).hom = h.hom p q := by
    subst hp hq
    simp
  -- The reverse round trip cancels the same comparison isomorphisms on the cochain side.
  ext i j
  -- Unfold the component formulas and cancel the inserted `XIsoOfEq` comparisons.
  dsimp [chain_to_cochain_homotopy_backward, chain_to_cochain_homotopy_forward,
    chain_to_cochain_homotopy_backward_hom, chain_to_cochain_homotopy_forward_hom]
  have hi : i = -(-i) := by simp
  have hj : j = -(-j) := by simp
  rw [hi, hj]
  simpa using H (-(-i)) (-(-j)) (-(-(-(-i)))) (-(-(-(-j)))) (by simp) (by simp)

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
@[stacks 011C]
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
@[stacks 011C]
theorem chainComplex_homotopy_isEmpty_or_exists_hom_to_shift_bijection (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (Homotopy a b ≃ (A ⟶ B⟦(1 : ℤ)⟧)) := by
  simpa using homotopy_isEmpty_or_nonempty_equiv a b
    (chainComplex_self_homotopy_equiv_hom_to_shift a)
