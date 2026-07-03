import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_14_1 (from Chap12) -/
open CategoryTheory HomologicalComplex

universe v u

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

noncomputable section

/-
Domain-style sampling:
- primary domain: the canonical shift on chain complexes indexed by `ℤ`;
- sampled owner declarations:
  `CochainComplex.shiftFunctor`,
  `CochainComplex.shiftFunctorObjXIso`,
  `CategoryTheory.PullbackShift`,
  `Functor.CommShift.commShiftIso`.

Owner abstraction:
- `core/canonical`: the cochain-complex shift owner from mathlib;
- `source-facing`: the induced shift on `ChainComplex C ℤ`, transported across
  `ChainComplex.cochainComplexEquivalence`;
- `bridge/view`: the generic shift-commutation isomorphism on
  `ChainComplex.cochainComplexEquivalence`.

Primitive data are only the pulled-back cochain shift and the chain/cochain equivalence. The
degree formulas and comparison isomorphisms are derived API. -/
private abbrev cochainShiftPullback (C : Type u) [Category.{v} C] [Preadditive C] :=
  PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ)

private abbrev chainCochainEquivalence : ChainComplex C ℤ ≌ cochainShiftPullback C :=
  ChainComplex.cochainComplexEquivalence C

/- Bridge/view owner: the canonical chain-to-cochain transport, viewed in the pullback-shift
owner category where the shift parameter is preserved. -/
abbrev chainToCochain :
    ChainComplex C ℤ ⥤ PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) :=
  (chainCochainEquivalence C).functor

private abbrev cochainToChain : cochainShiftPullback C ⥤ ChainComplex C ℤ :=
  (chainCochainEquivalence C).inverse

private abbrev shiftFunctorAux (k : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ :=
  chainToCochain C ⋙ shiftFunctor (cochainShiftPullback C) k ⋙ cochainToChain C

-- Proof sketch: unfold `shiftFunctorAux`, rewrite through
-- `ChainComplex.cochainComplexEquivalence`, and simplify the transported indexing along
-- `n ↦ -n` together with the cochain-shift formula.
private theorem shiftFunctorAux_obj_X (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    ((shiftFunctorAux C k).obj K).X n = K.X (n + k) := sorry

-- Proof sketch: unfold `shiftFunctorAux`, compute the transported cochain differential, and
-- simplify the indexing conversion through `n ↦ -n`.
private theorem shiftFunctorAux_obj_d (k : ℤ) (K : ChainComplex C ℤ) (i j : ℤ) :
    ((shiftFunctorAux C k).obj K).d i j =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow • K.d (i + k) (j + k)) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm := sorry

-- Proof sketch: unfold `shiftFunctorAux`, pass through the cochain-equivalence transport, and
-- read off the component in translated degree `n + k`.
private theorem shiftFunctorAux_map_f (k : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    ((shiftFunctorAux C k).map φ).f n =
      eqToHom (shiftFunctorAux_obj_X C k K n) ≫
        φ.f (n + k) ≫
        eqToHom (shiftFunctorAux_obj_X C k L n).symm := sorry

private def shiftFunctorAuxIso (k : ℤ) :
    shiftFunctorAux C k ⋙ chainToCochain C ≅
      chainToCochain C ⋙ shiftFunctor (cochainShiftPullback C) k :=
  NatIso.ofComponents
    (fun K ↦
      (chainCochainEquivalence C).counitIso.app
        ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K)))
    (by
      intro K L φ
      exact hom_ext _ _ fun n ↦ by
        simp [chainToCochain, cochainToChain, shiftFunctorAux])

/- Definition 12.14.1: chain complexes indexed by `ℤ` carry the canonical shift,
obtained by pulling back the cochain-complex shift along integer negation and transporting it
across `ChainComplex.cochainComplexEquivalence C`. -/
noncomputable instance instHasShift : HasShift (ChainComplex C ℤ) ℤ :=
  Functor.FullyFaithful.hasShift
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun k ↦ shiftFunctorAux C k)
    (fun k ↦ shiftFunctorAuxIso C k)

noncomputable instance instChainToCochainCommShift :
    (chainToCochain C).CommShift ℤ := by
  let hF : (chainToCochain C).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  letI : HasShift (ChainComplex C ℤ) ℤ :=
    Functor.FullyFaithful.hasShift hF (shiftFunctorAux C) (shiftFunctorAuxIso C)
  exact Functor.CommShift.ofHasShiftOfFullyFaithful hF (shiftFunctorAux C) (shiftFunctorAuxIso C)

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Proof sketch: unfold `shiftFunctor`, rewrite through
-- `ChainComplex.cochainComplexEquivalence`, and simplify the transported indexing along
-- `n ↦ -n` together with the cochain-shift formula.
/-- The degree-`n` term of the shifted chain complex is the degree-`n + k` term of the
original complex. -/
theorem shiftFunctor_obj_X (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦k⟧).X n = K.X (n + k) := by
  simpa using shiftFunctorAux_obj_X C k K n

/-- The canonical degree isomorphism from `(K⟦k⟧).X i` to `K.X j` when `j = i + k`. -/
@[simp] def shiftFunctorObjXIso (K : ChainComplex C ℤ) (k i j : ℤ) (h : j = i + k) :
    (K⟦k⟧).X i ≅ K.X j :=
  eqToIso ((shiftFunctor_obj_X k K i).trans (by rw [h]))

-- Proof sketch: rewrite the shifted differential through the canonical degree isomorphisms and
-- simplify the transported cochain-shift formula.
/-- Via the canonical degree identifications, the differential on `K⟦k⟧` is
`(-1)^k` times the translated differential of `K`. -/
theorem shiftFunctor_obj_d (k : ℤ) (K : ChainComplex C ℤ) (i j : ℤ) :
    (K.shiftFunctorObjXIso k i (i + k) rfl).inv ≫ (K⟦k⟧).d i j =
      (k.negOnePow • K.d (i + k) (j + k)) ≫
        (K.shiftFunctorObjXIso k j (j + k) rfl).inv := by
  sorry

-- Proof sketch: rewrite the shifted component through the canonical degree isomorphisms and
-- simplify the transported cochain-shift formula.
/-- Via the canonical degree identifications, the degree-`n` component of the shifted morphism is
the degree-`n + k` component of the original morphism. -/
theorem shiftFunctor_map_f (k : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    (K.shiftFunctorObjXIso k n (n + k) rfl).inv ≫
        ((shiftFunctor (ChainComplex C ℤ) k).map φ).f n =
      φ.f (n + k) ≫ (L.shiftFunctorObjXIso k n (n + k) rfl).inv := by
  sorry

/-- The canonical degree isomorphism from `K⟦-1⟧` in degree `n` to `K` in degree `n - 1`. -/
abbrev shiftMinusOneXIso (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X n ≅ K.X (n - 1) :=
  K.shiftFunctorObjXIso (-1) n (n - 1) (by omega)

/-- The canonical degree isomorphism from `K⟦-1⟧` in degree `n + 1` to `K` in degree `n`. -/
abbrev shiftMinusOneSuccXIso (K : ChainComplex C ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X (n + 1) ≅ K.X n :=
  shiftMinusOneXIso K (n + 1) ≪≫ K.XIsoOfEq (show n + 1 - 1 = n by omega)

end

end ChainComplex

/-! ### Definition_12_14_2 (from Chap12) -/
open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

noncomputable section

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Domain-style sampling: the primary domain is homological algebra for shifts of chain homology.
Relevant owner declarations in the surrounding ecosystem are:
- `ChainComplex.cochainComplexEquivalence`,
- `CategoryTheory.PullbackShift` together with `pullbackShiftIso`,
- `Functor.CommShift.commShiftIso`,
- `CochainComplex.ShiftSequence.shiftIso`,
- `CategoryTheory.Functor.ShiftSequence.shiftIso`.

Source/core/bridge triage:
- `core/canonical`: the Chapter 12 shift owner on `ChainComplex`, built in
  `Definition_12_14_1` from `PullbackShift`, together with the cochain owner
  `CochainComplex.ShiftSequence.shiftIso`;
- `bridge/view`: this file transports that owner to chain homology.

Primitive data:
- the chain/cochain equivalence viewed in the pullback-shift owner category;
- the comparison isomorphisms from pullbacked cochain homology to chain homology.

Derived API:
- the owner shift-sequence instance on `(homologyFunctor C (down ℤ) 0)`;
- the public comparison morphism `(homologyFunctor C (down ℤ) 0).shiftIso`.
-/
private abbrev cochainShiftPullback :=
  PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ)

private abbrev pullbackHomologyFunctor (i : ℤ) : cochainShiftPullback C ⥤ C :=
  homologyFunctor C (up ℤ) (-i)

private noncomputable instance : (pullbackHomologyFunctor C 0).ShiftSequence ℤ where
  sequence i := pullbackHomologyFunctor C i
  isoZero := Iso.refl _
  shiftIso k i i' hi' :=
    Functor.isoWhiskerRight
      (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) k (-k) (by simp))
      (homologyFunctor C (up ℤ) (-i)) ≪≫
    (show shiftFunctor (CochainComplex C ℤ) (-k : ℤ) ⋙ homologyFunctor C (up ℤ) (-i) ≅
        pullbackHomologyFunctor C i' from
      CochainComplex.ShiftSequence.shiftIso C (-k) (-i) (-i') (by omega))
  shiftIso_zero i := by
    sorry
  shiftIso_add k l i i' i'' hi' hi'' := by
    sorry

private def homologyFunctorFactorsApp (A : ChainComplex C ℤ) (i : ℤ) :
    (pullbackHomologyFunctor C i).obj ((ChainComplex.cochainComplexEquivalence C).functor.obj A) ≅
      (homologyFunctor C (down ℤ) i).obj A :=
  ((((ChainComplex.cochainComplexEquivalence C).functor.obj A).restrictionHomologyIso
      embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
      (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
        change -(i + 1) = -i - 1
        omega)
      (show embeddingDownIntUpInt.f i = -i by simp)
      (show embeddingDownIntUpInt.f (i - 1) = -i + 1 by
        change -(i - 1) = -i + 1
        omega)
      (show (up ℤ).prev (-i) = -i - 1 by simp)
      (show (up ℤ).next (-i) = -i + 1 by simp)).symm) ≪≫
    (homologyFunctor C (down ℤ) i).mapIso
      (((ChainComplex.cochainComplexEquivalence C).unitIso.app A).symm)

private def homologyFunctorFactors (i : ℤ) :
    chainToCochain C ⋙ pullbackHomologyFunctor C i ≅
      homologyFunctor C (down ℤ) i :=
  NatIso.ofComponents
    (fun A ↦ homologyFunctorFactorsApp C A i)
    (by
      intro A B f
      sorry)

noncomputable instance :
    (homologyFunctor C (down ℤ) 0).ShiftSequence ℤ where
  sequence i := homologyFunctor C (down ℤ) i
  isoZero := Iso.refl _
  shiftIso k i i' hi' :=
    Functor.isoWhiskerLeft (shiftFunctor (ChainComplex C ℤ) k) (homologyFunctorFactors C i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((chainToCochain C).commShiftIso k) (pullbackHomologyFunctor C i) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (chainToCochain C)
              ((pullbackHomologyFunctor C 0).shiftIso k i i' hi') ≪≫
              homologyFunctorFactors C i'
  shiftIso_zero i := by
    sorry
  shiftIso_add k l i i' i'' hi' hi'' := by
    sorry

end ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Definition 12.14.2: after transporting the cochain owner
`CochainComplex.ShiftSequence.shiftIso` through the Chapter 12 pullback-shift owner on
`ChainComplex`, the canonical functorial identification `H_{i + k}(A) ≅ H_i(A[k])` is expressed
by the generic owner morphism `(homologyFunctor C (down ℤ) 0).shiftIso`. Its source is the
degreewise equality `A_{i + k} = A[k]_i` from Definition `12.14.1`. -/
#check (homologyFunctor C (down ℤ) 0).shiftIso

variable (A : ChainComplex C ℤ) (k : ℤ)

/- Companion recall: the underlying shifted chain complex is the canonical shift object `A⟦k⟧`. -/
#check A⟦k⟧

/-! ### Lemma_12_14_3 (from Chap12) -/
open CategoryTheory HomologicalComplex ChainComplex

universe v u

noncomputable section

variable {V : Type u} [Category.{v} V] [Preadditive V]

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

/- Bridge/view owner: `chainToCochain V` transports homotopies in both directions. -/
def chainToCochainHomotopyEquiv {A B : ChainComplex V ℤ} {a b : A ⟶ B} :
    Homotopy a b ≃
      Homotopy ((chainToCochain V).map a) ((chainToCochain V).map b) where
  toFun h := by
    refine
      { hom := fun p q ↦ h.hom (-p) (-q)
        zero := ?_
        comm := ?_ }
    · intro p q hpq
      rw [h.zero (-p) (-q)]
      · rfl
      · dsimp at hpq ⊢
        lia
    · intro n
      sorry
  invFun h := by
    refine
      { hom := fun i j ↦
          (A.XIsoOfEq (by simp)).hom ≫ h.hom (-i) (-j) ≫ (B.XIsoOfEq (by simp)).hom
        zero := ?_
        comm := ?_ }
    · intro i j hij
      rw [h.zero (-i) (-j)]
      · sorry
      · dsimp at hij ⊢
        lia
    · intro n
      sorry
  left_inv h := by
    sorry
  right_inv h := by
    sorry

variable {A B : ChainComplex V ℤ}

/- Bridge/view owner: under `chainToCochain V`, a morphism into the cochain `[-1]` shift is
exactly a morphism into the chain `[1]`-shift. -/
private noncomputable abbrev chainToCochainShiftHomEquiv (A B : ChainComplex V ℤ) :
    (((cochainComplexEquivalence V).functor.obj A) ⟶
      ((cochainComplexEquivalence V).functor.obj B)⟦(-1 : ℤ)⟧) ≃
        (A ⟶ B⟦(1 : ℤ)⟧) :=
  let F := chainToCochain V
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
        ((chainToCochain V).map a)).trans
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

/-! ### Lemma_12_14_4 (from Chap12) -/
open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

/- Source-facing primitive datum for Lemmas 12.14.4–12.14.6: the short complex in degree `n`
obtained by evaluating a short complex of chain complexes. -/
abbrev degreewiseShortComplex (S : ShortComplex (ChainComplex 𝒜 ℤ)) (n : ℤ) :=
  S.map (eval 𝒜 (ComplexShape.down ℤ) n)

noncomputable section

/- Source/core/bridge triage:
- core/canonical owner: `CochainComplex.homOfDegreewiseSplit`
- target item here: a chain-complex bridge/view obtained by transporting that owner construction
  across `cochainComplexEquivalence 𝒜`.
- primitive data: the degreewise split short complex `degreewiseShortComplex S n`.
- derived bridge data: the mapped short complex under `(cochainComplexEquivalence 𝒜).functor`
  and the canonical shift comparison from the pullback-shift owner. -/
/- Internal bridge/view: the chain-level connecting morphism is the preimage, under
`cochainComplexEquivalence 𝒜`, of the owner construction
`CochainComplex.homOfDegreewiseSplit` composed with the canonical shift comparison. -/
/-- Lemma 12.14.4: for a degreewise split short complex of chain complexes, the morphisms
`π_{n-1} ∘ d_{B,n} ∘ s_n` assemble to a chain map `C_• ⟶ A[-1]_•`. -/
def homOfDegreewiseSplit
    (S : ShortComplex (ChainComplex 𝒜 ℤ))
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    : S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧ :=
  let F : ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
      (negAddMonoidHom : ℤ →+ ℤ) :=
    show ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
        (negAddMonoidHom : ℤ →+ ℤ) from
      (cochainComplexEquivalence 𝒜).functor
  let T := ((cochainComplexEquivalence 𝒜).functor).mapShortComplex.obj S
  let τ : ∀ m : ℤ, (T.map (eval 𝒜 (up ℤ) m)).Splitting :=
    fun m ↦ show (T.map (eval 𝒜 (up ℤ) m)).Splitting from σ (-m)
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj (F.obj S.X₁) :=
    rfl
  let e :
      (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
        (cochainComplexEquivalence 𝒜).functor.obj (S.X₁⟦(-1 : ℤ)⟧) :=
    eqToHom hEq ≫
      ((show shiftFunctor (ChainComplex 𝒜 ℤ) (-1 : ℤ) ⋙ F ≅
          F ⋙
            shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ)
              (negAddMonoidHom : ℤ →+ ℤ)) (-1 : ℤ)
        from
          F.commShiftIso (-1 : ℤ)).app S.X₁).symm.hom
  ((cochainComplexEquivalence 𝒜).functor).preimage <|
    (show T.X₃ ⟶ (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) from
      CochainComplex.homOfDegreewiseSplit T τ) ≫ e

-- Proof sketch: transport `CochainComplex.homOfDegreewiseSplit_f` across
-- `ChainComplex.cochainComplexEquivalence`. The auxiliary shift comparison identifies the
-- cochain shift `[1]` with the chain shift `[-1]`.
/-- After identifying `(A⟦-1⟧).X n` with `A.X (n - 1)`, the degree-`n` component of
`homOfDegreewiseSplit` is `π_{n-1} ∘ d_{B,n} ∘ s_n`. -/
@[simp]
theorem homOfDegreewiseSplit_f
    (S : ShortComplex (ChainComplex 𝒜 ℤ))
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n ≫
        (S.X₁.shiftMinusOneXIso n).hom =
      (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r := by
  sorry

end

end ChainComplex

/-! ### Lemma_12_14_5 (from Chap12) -/
open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable (S : ShortComplex (ChainComplex 𝒜 ℤ)) (hS : S.ShortExact)

/- Domain-style sampling in the chain-complex long-exact-sequence API:
- core/canonical owner boundary: `ShortComplex.ShortExact.δ`
- core/canonical owner shifted homology map:
  `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap`
- source-facing bridge datum: `homOfDegreewiseSplit` from Lemma `12.14.4`

This item is a `bridge/view`: it compares the explicit chain-level connecting morphism from
Lemma `12.14.4` with the owner boundary map in the long exact homology sequence, using the owner
`Functor.ShiftSequence.shiftMap` interface on chain homology.
-/

variable (σ : ∀ n : ℤ, (ChainComplex.degreewiseShortComplex S n).Splitting)

-- Proof sketch: compare the explicit chain map `homOfDegreewiseSplit S σ` from
-- Lemma `12.14.4` with the canonical boundary map in the snake-lemma construction of
-- the homology long exact sequence; the identification `H_i(A[-1]) ≅ H_{i-1}(A)` is the owner
-- shift-map construction `(homologyFunctor 𝒜 (ComplexShape.down ℤ) 0).shiftMap` specialized to
-- `k = -1`.
/-- Lemma 12.14.5: after identifying `H_i(A[-1]_•)` with `H_{i-1}(A_•)`, the homology map
induced by the explicit chain map `δ(σ) : C_• ⟶ A[-1]_•` of Lemma 12.14.4 is exactly the
connecting morphism occurring in the long exact homology sequence of the short exact sequence of
chain complexes. -/
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    (homologyFunctor 𝒜 (down ℤ) 0).shiftMap (homOfDegreewiseSplit S σ) i (i - 1) (by omega) =
      hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) := by
  sorry

end ChainComplex

/-! ### Lemma_12_14_6 (from Chap12) -/
open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable (S : ShortComplex (ChainComplex 𝒜 ℤ))
variable (σ σ' : ∀ n : ℤ, (ChainComplex.degreewiseShortComplex S n).Splitting)
variable
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

/-
Domain-style sampling for degreewise-split connecting morphisms:
- primary domain: homotopies between connecting morphisms attached to degreewise split short
  complexes.
- owner declarations inspected:
  `CochainComplex.homOfDegreewiseSplit` and `CochainComplex.homOfDegreewiseSplit_f` from mathlib,
  `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference` and its degreewise
  companion theorem from `Lemma_12_14_12`,
  `chainToCochainHomotopyEquiv` from `Lemma_12_14_3`,
  `ChainComplex.homOfDegreewiseSplit` and `chainToCochain` from `Lemma_12_14_4` and
  `Definition_12_14_1`.
- best owner abstraction: the cochain-side homotopy theorem, transported through the chapter
  owner functor `chainToCochain 𝒜`.
- primitive data here: the correction family `h n : C_n ⟶ A_n` and the section-difference
  identity `hs_eq`.
- derived API here: the transported chain homotopy and its degreewise component formula.
-/

noncomputable section

private abbrev transportedShortComplex :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  (chainToCochain 𝒜).mapShortComplex.obj S

private abbrev transportedSplitting
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting) :
    ∀ n : ℤ, ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting :=
  fun n ↦ show ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting from σ (-n)

private abbrev transportedCorrection :
    ∀ n : ℤ, ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₃ ⟶
      ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₁ :=
  fun n ↦ show ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₃ ⟶
      ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₁ from -h (-n)

private def shiftMinusOneComparison :
    (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
      (chainToCochain 𝒜).obj (S.X₁⟦(-1 : ℤ)⟧) :=
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj ((chainToCochain 𝒜).obj S.X₁) :=
    rfl
  eqToHom hEq ≫ (((chainToCochain 𝒜).commShiftIso (-1 : ℤ)).app S.X₁).symm.hom

private theorem transportedSectionDifference
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    : CochainComplex.sectionDifference
        (transportedShortComplex S)
        (transportedSplitting S σ')
        (transportedSplitting S σ)
        (transportedCorrection S h) := by
  sorry

-- Proof sketch: write the difference of the two connecting morphisms using the identities
-- `(σ' n).s = (σ n).s + h_n ≫ i_n` and `(σ' n).r = (σ n).r - q_n ≫ h_n`. After expanding
-- degreewise, the cross-term vanishes
-- because `S.f ≫ S.g = 0`, and the remaining terms are exactly the null-homotopic expression
-- determined by the family `h_n : C_n ⟶ A_n`, viewed as maps into the canonical shift `A⟦-1⟧`.
/- Source/core/bridge triage:
- core/canonical owner in this chapter: `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference`
  from `Lemma_12_14_12`
- target item here: a `bridge/view`, transporting that owner statement along
  `cochainComplexEquivalence 𝒜`. -/
/-- Lemma 12.14.6: if a second degreewise splitting differs from the first by maps
`h_n : C_n ⟶ A_n`, then these maps, viewed as morphisms `C_n ⟶ A[-1]_{n + 1}`, give a chain
homotopy between the associated connecting morphisms. -/
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f) :
    Homotopy
      (homOfDegreewiseSplit S σ)
      (homOfDegreewiseSplit S σ') := by
  let T := transportedShortComplex S
  let τ := transportedSplitting S σ
  let τ' := transportedSplitting S σ'
  let e := shiftMinusOneComparison S
  let hs : CochainComplex.sectionDifference T τ' τ (transportedCorrection S h) :=
    transportedSectionDifference S σ σ' h hs_eq
  let H :
      Homotopy
        (CochainComplex.homOfDegreewiseSplit T τ)
        (CochainComplex.homOfDegreewiseSplit T τ') :=
    CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference
      T τ' τ (transportedCorrection S h) hs
  have H' :
      Homotopy
        ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ))
        ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ')) := by
    simpa [e, homOfDegreewiseSplit, T, τ, τ'] using H.compRight e
  exact
    (chainToCochainHomotopyEquiv :
      Homotopy (homOfDegreewiseSplit S σ) (homOfDegreewiseSplit S σ') ≃
        Homotopy
          ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ))
          ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ'))).symm H'

private theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom_comp_shiftMinusOneXIso
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (S.X₁.shiftMinusOneXIso (n + 1)).hom =
      (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
        simpa using h n) := by
  sorry

private theorem correction_comp_shiftIndexIso (n : ℤ) :
    (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
      simpa using h n) ≫
        (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom =
      h n := by
  have e : n + 1 - 1 = n := by omega
  change
    cast (congrArg (fun W : 𝒜 ↦ S.X₃.X n ⟶ W) (congrArg (fun i ↦ S.X₁.X i) e).symm) (h n) ≫
        eqToHom (congrArg (fun i ↦ S.X₁.X i) e) =
      h n
  have hcast := congrArg_cast_hom_right (h n) (congrArg (fun i ↦ S.X₁.X i) e)
  have hpost := congrArg (fun k ↦ k ≫ eqToHom (congrArg (fun i ↦ S.X₁.X i) e)) hcast
  simpa [Category.assoc] using hpost

/-- The homotopy of Lemma 12.14.6 has degree-`n` component given by the correction map
`h_n : C_n ⟶ A_n`, viewed in the shifted target `A[-1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (shiftMinusOneSuccXIso S.X₁ n).hom =
      h n := by
  have hcomp :=
    congrArg
      (fun k ↦ k ≫ (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom)
      (homOfDegreewiseSplit_homotopy_of_splitting_difference_hom_comp_shiftMinusOneXIso
        S σ σ' h hs_eq n)
  calc
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (shiftMinusOneSuccXIso S.X₁ n).hom =
      (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
        simpa using h n) ≫
          (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom := by
        simpa [shiftMinusOneSuccXIso, Category.assoc] using hcomp
    _ = h n := correction_comp_shiftIndexIso S h n

end

end ChainComplex

/-! ### Definition_12_14_7 (from Chap12) -/
/- Domain-style sampling:
- primary domain: shifts of cochain complexes in a preadditive category;
- sampled owner declarations:
  `CochainComplex.shiftFunctor`,
  `CochainComplex.shiftFunctor_obj_X'`,
  `CochainComplex.shiftFunctor_obj_d'`,
  `CochainComplex.shiftFunctor_map_f'`.

Source/core/bridge triage:
- `core/canonical`: `CochainComplex.shiftFunctor`;
- `source-facing`: the shifted cochain complex `A⟦k⟧`;
- `bridge/view`: the degreewise object, differential, and morphism formulas supplied by the
  sampled companion lemmas.

Primitive data are only the owner functor. The formulas
`(A⟦k⟧).X n = A.X (n + k)`, `d = (-1)^k • A.d (n + k) (n + k + 1)`, and
`((shiftFunctor _ k).map f).f n = f.f (n + k)` are derived API, so this file should remain a
canonical recall item rather than reintroducing a parallel local shift definition.

Definition 12.14.7: the source-facing shift construction on cochain complexes is the canonical
owner functor `CochainComplex.shiftFunctor`. -/
recall CochainComplex.shiftFunctor

/-! ### Definition_12_14_8 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: cohomology of shifted cochain complexes in a category with homology;
- sampled owner declarations:
  `CochainComplex.ShiftSequence.shiftIso`,
  `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso`,
  `CategoryTheory.Functor.ShiftSequence.shiftIso`;
- best owner abstraction for this file: the cochain-complex owner
  `CochainComplex.ShiftSequence.shiftIso`, whose underlying generic interface is
  `CategoryTheory.Functor.ShiftSequence.shiftIso`.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.ShiftSequence.shiftIso`;
- `core/canonical`: `CategoryTheory.Functor.ShiftSequence.shiftIso`;
- `bridge/view`: the inherited shift-sequence morphism
  `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso`.

Primitive data in this domain are the cochain-complex shift/cohomology comparison encoded by
`CochainComplex.ShiftSequence.shiftIso`; the generic functor-level shift-sequence interface and
the specialized morphism `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso` are derived API.

Definition 12.14.8 is a source-facing recall item: for a cochain complex `A` and any shift
`k : ℤ`, the canonical cohomology-shift identification is exactly
`CochainComplex.ShiftSequence.shiftIso`, and its inverse identifies `H^(i + k)(A)` with
`H^i(A⟦k⟧)`. -/
recall CochainComplex.ShiftSequence.shiftIso

end CategoryTheory

/-! ### Lemma_12_14_9 (from Chap12) -/
open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open CochainComplex.HomComplex.Cocycle

universe v u

noncomputable section

variable {ι : Type*} {c : ComplexShape ι}
variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {K L : HomologicalComplex D c} {f g : K ⟶ L}

/-- Translating by a fixed homotopy `h : Homotopy f g` identifies the homotopies from `f` to `g`
with the self-homotopies of `f`. -/
private def homotopyEquivSelf (h : Homotopy f g) : Homotopy f g ≃ Homotopy f f where
  toFun k := k.trans h.symm
  invFun k := k.trans h
  left_inv k := by
    ext i j
    simp [Homotopy.trans, Homotopy.symm, add_assoc]
  right_inv k := by
    ext i j
    simp [Homotopy.trans, Homotopy.symm, add_assoc]

/-- If self-homotopies of `a` are identified with a type `α`, then the homotopies from `a` to `b`
are either empty or identified with `α` after choosing one homotopy `a ⟶ b`. -/
theorem homotopy_isEmpty_or_nonempty_equiv {A B : HomologicalComplex D c} (a b : A ⟶ B)
    {α : Type*} (e : Homotopy a a ≃ α) :
    IsEmpty (Homotopy a b) ∨ Nonempty (Homotopy a b ≃ α) := by
  by_cases h : Nonempty (Homotopy a b)
  · right
    rcases h with ⟨h⟩
    exact ⟨(homotopyEquivSelf h).trans e⟩
  · left
    exact ⟨fun k ↦ h ⟨k⟩⟩

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : CochainComplex C ℤ}

/- Source/core/bridge triage:
- primary domain: homotopies of cochain-complex maps and the associated hom-complex.
- core/canonical owner declarations:
  `homotopyEquivSelf`,
  `homotopy_isEmpty_or_nonempty_equiv`,
  `Homotopy.equivSubZero`,
  `Cochain.equivHomotopy`,
  `Cocycle.equivHomShift`.
- target items here: bridge/view declarations packaging that owner chain into the source-facing
  bijection between homotopies and morphisms into the `(-1)`-shift.

Primitive data:
- a homotopy `h : Homotopy a b`,
- the owner hom-complex cochain and cocycle descriptions.

Derived API:
- `cochainComplex_self_homotopy_equiv_hom_to_shift`,
- `cochainComplex_homotopyTranslateToShiftNegOne`,
- `homotopy_isEmpty_or_exists_shiftNegOne_bijection`.
-/
private noncomputable def zeroHomotopyEquivCocycle :
    Homotopy (0 : A ⟶ B) 0 ≃ Cocycle A B (-1) :=
  (Cochain.equivHomotopy (0 : A ⟶ B) 0).trans <|
    Equiv.subtypeEquivRight fun z ↦ by
      rw [Cocycle.mem_iff (-1) 0 (neg_add_cancel 1) z]
      simp
      simpa using (eq_comm : 0 = δ (-1) 0 z ↔ δ (-1) 0 z = 0)

/-- Lemma 12.14.9: for a cochain map `a : A^• ⟶ B^•`, self-homotopies of `a` are in bijection
with morphisms `A^• ⟶ B^•[-1]`. -/
noncomputable def cochainComplex_self_homotopy_equiv_hom_to_shift (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  Homotopy.equivSubZero.trans <|
    by simpa using zeroHomotopyEquivCocycle.trans equivHomShift.symm.toEquiv

-- Proof sketch: use `cochainComplex_self_homotopy_equiv_hom_to_shift` to transport the additive
-- group structure on `A ⟶ B⟦(-1 : ℤ)⟧` to self-homotopies of `a`, and let these act on
-- `Homotopy a b` by composition with a chosen homotopy.
/-- Translating by a chosen homotopy `h : Homotopy a b` sends any other homotopy from `a` to `b`
to the corresponding morphism `A^• ⟶ B^•[-1]`. -/
private noncomputable def cochainComplex_homotopyTranslateToShiftNegOne {a b : A ⟶ B}
    (h : Homotopy a b) :
    Homotopy a b ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  (homotopyEquivSelf h).trans (cochainComplex_self_homotopy_equiv_hom_to_shift a)

-- Proof sketch: if `Homotopy a b` is empty we are done. Otherwise choose a homotopy `h : Homotopy
-- a b`; translation by `h` gives the required bijection with `A ⟶ B⟦-1⟧`, which is the
-- principal-homogeneous-space description of the nonempty case without packaging it as
-- existential torsor data.
/-- Companion statement: for cochain maps `a, b : A^• ⟶ B^•`, the homotopies from `a` to `b` are
either empty or nonempty together with an induced equivalence to the morphisms
`A^• ⟶ B^•[-1]`. -/
theorem homotopy_isEmpty_or_exists_shiftNegOne_bijection (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (Homotopy a b ≃ (A ⟶ B⟦(-1 : ℤ)⟧)) := by
  simpa [cochainComplex_homotopyTranslateToShiftNegOne] using
    homotopy_isEmpty_or_nonempty_equiv a b
      (cochainComplex_self_homotopy_equiv_hom_to_shift a)

/-! ### Lemma_12_14_10 (from Chap12) -/
/- Source/core/bridge triage for Lemma 12.14.10:
- primary domain: degreewise split short exact sequences of cochain complexes and their canonical
  connecting morphisms in the homotopy-category package.
- inspected owner declarations:
  `CochainComplex.cocycleOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit_f`,
  `CochainComplex.triangleOfDegreewiseSplit`.
- best owner abstraction: the canonical owner morphism
  `CochainComplex.homOfDegreewiseSplit`.
- layer: `core/canonical`; this numbered item is a direct recall of the owner morphism and its
  degreewise component formula, not a source-facing new construction.
- primitive data: a short complex `S` of cochain complexes together with a degreewise splitting
  family `σ`.
- derived API: the cocycle description, the component formula, and the associated triangle remain
  upstream and are reused directly here.
-/

/- Lemma 12.14.10: for a degreewise split short complex
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of cochain complexes in an additive category, the family of
components `s^n ≫ d_B^n ≫ π^{n + 1} : C^n ⟶ A^{n + 1}` assembles into the canonical morphism
`C^• ⟶ A^•[1]`. -/
recall CochainComplex.homOfDegreewiseSplit

/- Companion recall: the degree-`n` component of
`CochainComplex.homOfDegreewiseSplit` is `s^n ≫ d_B^n ≫ π^{n + 1}`. -/
recall CochainComplex.homOfDegreewiseSplit_f

/-! ### Lemma_12_14_11 (from Chap12) -/
open ComplexShape HomologicalComplex

universe u v

noncomputable section

namespace CategoryTheory.ShortComplex

variable {V : Type u} [Category.{v} V] [Abelian V]
variable {S : ShortComplex (CochainComplex V ℤ)}
variable (hS : S.ShortExact)
variable (spl : ∀ n : ℤ, (S.map (HomologicalComplex.eval V (up ℤ) n)).Splitting)

/-
Domain-style sampling in the cohomology-boundary owner API:
- primitive split datum: `CochainComplex.homOfDegreewiseSplit`
- degreewise companion formula: `CochainComplex.homOfDegreewiseSplit_f`
- owner short-exact boundary: `ShortComplex.ShortExact.δ`
- owner triangle boundary: `CochainComplex.homologyδOfTriangle`

Lemma 12.14.11 is a `bridge/view`: it identifies the triangle-level boundary map attached to the
degreewise split triangle with the short-exact-sequence boundary map `hS.δ`.
-/

-- Proof sketch: use the owner triangle boundary
-- `CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)` for the
-- cohomology map induced by `CochainComplex.homOfDegreewiseSplit S spl`, then compare it with the
-- snake-lemma boundary `hS.δ` using `CochainComplex.homOfDegreewiseSplit_f` and the description of
-- `ShortComplex.ShortExact.δ`.
/-- Lemma 12.14.11: for a degreewise splitting of a short exact sequence
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0`, the cohomology boundary map of the degreewise split triangle, i.e. of
the canonical connecting morphism `CochainComplex.homOfDegreewiseSplit S spl : C^• ⟶ A^•[1]`, is
the connecting morphism in the associated long exact cohomology sequence. -/
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl) i (i + 1)
      rfl = hS.δ i (i + 1) rfl := by
  sorry

end CategoryTheory.ShortComplex

/-! ### Lemma_12_14_12 (from Chap12) -/
open ComplexShape HomologicalComplex

universe u v

namespace CategoryTheory
namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (S : ShortComplex (CochainComplex V ℤ))

/- Domain-style sampling:
- primary domain: degreewise split short complexes of cochain complexes and the homotopies
  comparing the owner connecting morphisms `CochainComplex.homOfDegreewiseSplit`.
- inspected owner declarations: `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit_f`,
  `CochainComplex.shiftFunctorObjXIso`,
  `ChainComplex.degreewiseShortComplex` from `Lemma_12_14_4`.
- best owner abstraction: `CochainComplex.homOfDegreewiseSplit`.
- primitive data in this file: the degreewise short complex, two degreewise splittings, and the
  section-difference family `h`.
- derived API in this file: the induced homotopy between the two owner connecting morphisms and
  its degreewise component formula. -/

/-- The short complex obtained by evaluating a short complex of cochain complexes in degree `n`.
-/
abbrev degreewiseShortComplex (S : ShortComplex (CochainComplex V ℤ)) (n : ℤ) :=
  S.map (HomologicalComplex.eval V (up ℤ) n)

variable
  (spl spl' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

/-- The second degreewise splitting differs from the first by the section corrections `h^n`. -/
abbrev sectionDifference : Prop :=
  ∀ n : ℤ, (spl' n).s = (spl n).s + h n ≫ (degreewiseShortComplex S n).f

private theorem retraction_eq_sub_section_correction
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (spl' n).r = (spl n).r - (degreewiseShortComplex S n).g ≫ h n := by
  sorry

-- Proof sketch: use that each degreewise splitting satisfies `r ≫ s = 0`. Expanding
-- `(spl' n).r = (spl n).r + g^n ≫ q^n` and the derived formula
-- `(spl' n).r = (spl n).r - q^n ≫ h^n` coming from `ShortComplex.Splitting.ext_s`, then precompose
-- with `(spl n).s`. The identities `(spl n).s ≫ (spl n).r = 0` and `(spl n).s ≫ q^n = 𝟙`
-- leave exactly `g^n + h^n = 0`.
/-- Lemma 12.14.12 (1): if a second degreewise splitting differs from the first one by correction
maps `h^n` on the section side and `g^n` on the retraction side, then these corrections satisfy
`g^n = -h^n` in every degree. -/
theorem retraction_correction_eq_neg_section_correction
    (k : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)
    (hs : sectionDifference S spl spl' h)
    (hr' : ∀ n : ℤ,
      (spl' n).r = (spl n).r + (degreewiseShortComplex S n).g ≫ k n)
    (n : ℤ) :
    k n = -h n := by
  sorry

-- Proof sketch: the retraction correction is canonically `-h^n`, so these maps, viewed in the
-- shifted target `A^•[1]`, form the degreewise components of a homotopy from the connecting
-- morphism attached to `spl'` to the one attached to `spl`. The homotopy relation is exactly the
-- standard textbook identity for the two connecting morphisms.
/- Source/core/bridge triage:
- source-facing: correction maps comparing two degreewise splittings of the same short complex.
- core/canonical owner: `homOfDegreewiseSplit`.
- target item here: a bridge/view giving the induced homotopy between the two owner maps. -/
/-- Lemma 12.14.12: the correction maps between two degreewise splittings define a homotopy from
the connecting morphism attached to `spl'` to the one attached to `spl`. -/
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs : sectionDifference S spl spl' h) :
    Homotopy
      (CochainComplex.homOfDegreewiseSplit S spl')
      (CochainComplex.homOfDegreewiseSplit S spl) where
  hom i j :=
    if hij : (up ℤ).Rel j i then
      (-h i) ≫
        (S.X₁.shiftFunctorObjXIso 1 (i - 1) i (Int.sub_add_cancel i 1).symm).inv ≫
          ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (by
            have hij' : j + 1 = i := by simpa [up_Rel] using hij
            omega)).hom
    else
      0
  zero i j hij := by
    dsimp
    split_ifs with hrel
    · exact (hij hrel).elim
    · rfl
  comm n := by
    sorry

/-- The degree-`n` component of the homotopy from Lemma 12.14.12 is the correction map
`-h^n : C^n ⟶ A^n`, viewed inside the shifted target `A^•[1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference S spl spl' h hs).hom n (n - 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).hom =
      -h n := by
  sorry

end

end CochainComplex
end CategoryTheory
