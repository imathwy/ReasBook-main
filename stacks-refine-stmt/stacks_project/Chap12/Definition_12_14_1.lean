import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
