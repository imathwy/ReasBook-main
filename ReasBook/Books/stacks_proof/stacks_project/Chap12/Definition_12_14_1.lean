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

omit [Preadditive C] in
/-- Helper for Definition 12.14.1: `eqToHom` does not depend on the chosen equality proof. -/
private theorem eqToHom_proof_irrel {X Y : C} (p q : X = Y) : eqToHom p = eqToHom q := by
  cases p
  cases q
  rfl

/-- Helper for Definition 12.14.1: on the pullback-shift owner, shifting by `k` is the ordinary
cochain shift by `-k` on objects. -/
private theorem pullback_shift_obj_X_neg (k : ℤ) (Y : cochainShiftPullback C) (n : ℤ) :
    ((shiftFunctor (cochainShiftPullback C) k).obj Y).X n = Y.X (n - k) := by
  -- Read the pullback shift as the cochain shift with parameter `-k`.
  rfl

/-- Helper for Definition 12.14.1: on the pullback-shift owner, the shifted differential is the
cochain differential in translated degrees with the standard sign `(-1)^k`. -/
private theorem pullback_shift_obj_d_neg (k : ℤ) (Y : cochainShiftPullback C) (i j : ℤ) :
    ((shiftFunctor (cochainShiftPullback C) k).obj Y).d i j =
      k.negOnePow • Y.d (i - k) (j - k) := by
  -- Read the pullback shift as the cochain shift with parameter `-k`.
  change (-k).negOnePow • Y.d (i - k) (j - k) = k.negOnePow • Y.d (i - k) (j - k)
  simp [Int.negOnePow_neg]

/-- Helper for Definition 12.14.1: on the pullback-shift owner, the shifted morphism component in
degree `n` is the original component in degree `n - k`. -/
private theorem pullback_shift_map_f_neg (k : ℤ) {Y Z : cochainShiftPullback C}
    (ψ : Y ⟶ Z) (n : ℤ) :
    ((shiftFunctor (cochainShiftPullback C) k).map ψ).f n = ψ.f (n - k) := by
  -- Read the pullback shift as the cochain shift with parameter `-k`.
  rfl

-- Proof sketch: unfold `shiftFunctorAux`, rewrite through
-- `ChainComplex.cochainComplexEquivalence`, and simplify the transported indexing along
-- `n ↦ -n` together with the cochain-shift formula.
-- TODO: evaluate the cochain shift in degree `-n` and simplify `-(-n + -k) = n + k`.
private theorem shiftFunctorAux_obj_X (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    ((shiftFunctorAux C k).obj K).X n = K.X (n + k) := by
  -- Route correction: evaluate the inverse negation restriction at degree `n`, then compute the
  -- pullback-shifted cochain object at degree `-n`.
  change
    ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K)).X (-n) =
      K.X (n + k)
  rw [pullback_shift_obj_X_neg]
  change K.X (-(-n - k)) = K.X (n + k)
  congr 1
  omega

/-- Helper for Definition 12.14.1: the chain-to-cochain `restrictionXIso` is exactly the
transport appearing in `shiftFunctorAux_obj_X`. -/
private theorem chainToCochain_restrictionXIso_hom_eq_shiftFunctorAux_obj_X
    (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    (K.restrictionXIso ComplexShape.embeddingUpIntDownInt
        (show -(-n - k) = n + k by omega)).hom =
      eqToHom (shiftFunctorAux_obj_X C k K n) := by
  -- Both morphisms transport along the same arithmetic identification of the degree `n + k`.
  change
    eqToHom (congrArg K.X (show -(-n - k) = n + k by omega)) =
      eqToHom (shiftFunctorAux_obj_X C k K n)
  exact eqToHom_proof_irrel C _ _

/-- Helper for Definition 12.14.1: the inverse chain-to-cochain `restrictionXIso` is the inverse
transport appearing in `shiftFunctorAux_obj_X`. -/
private theorem chainToCochain_restrictionXIso_inv_eq_shiftFunctorAux_obj_X
    (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    (K.restrictionXIso ComplexShape.embeddingUpIntDownInt
        (show -(-n - k) = n + k by omega)).inv =
      eqToHom (shiftFunctorAux_obj_X C k K n).symm := by
  -- The inverse comparison map is the inverse transport along the same degree equality.
  change
    eqToHom (congrArg K.X (show n + k = -(-n - k) by omega)) =
      eqToHom (shiftFunctorAux_obj_X C k K n).symm
  exact eqToHom_proof_irrel C _ _

-- Proof sketch: unfold `shiftFunctorAux`, compute the transported cochain differential, and
-- simplify the indexing conversion through `n ↦ -n`.
-- TODO: rewrite the pullback shift differential as the cochain differential in degrees
-- `-i` and `-j`, then simplify the transported indices and comparison maps.
private theorem shiftFunctorAux_obj_d (k : ℤ) (K : ChainComplex C ℤ) (i j : ℤ) :
    ((shiftFunctorAux C k).obj K).d i j =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow • K.d (i + k) (j + k)) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm := by
  -- Route correction: compute the differential inside the cochain world at degrees `-i` and
  -- `-j`, then simplify the negation transport back to the chain convention.
  change
    ((shiftFunctor (cochainShiftPullback C) k).obj ((chainToCochain C).obj K)).d (-i) (-j) =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow • K.d (i + k) (j + k)) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm
  rw [pullback_shift_obj_d_neg]
  -- Identify the chain-to-cochain differential with the restriction differential.
  change
    k.negOnePow • (restriction K ComplexShape.embeddingUpIntDownInt).d (-i - k) (-j - k) =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow • K.d (i + k) (j + k)) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm
  rw [HomologicalComplex.restriction_d_eq
    (K := K) (e := ComplexShape.embeddingUpIntDownInt)
    (i := -i - k) (j := -j - k) (i' := i + k) (j' := j + k)
    (show -(-i - k) = i + k by omega) (show -(-j - k) = j + k by omega)]
  rw [chainToCochain_restrictionXIso_hom_eq_shiftFunctorAux_obj_X
    (C := C) k K i]
  rw [chainToCochain_restrictionXIso_inv_eq_shiftFunctorAux_obj_X
    (C := C) k K j]
  -- Reassociate once and move the unit scalar through the two comparison isomorphisms.
  calc
    k.negOnePow • eqToHom (shiftFunctorAux_obj_X C k K i) ≫ K.d (i + k) (j + k) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm =
      k.negOnePow •
          (eqToHom (shiftFunctorAux_obj_X C k K i) ≫ K.d (i + k) (j + k)) ≫
        eqToHom (shiftFunctorAux_obj_X C k K j).symm := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ eqToHom (shiftFunctorAux_obj_X C k K j).symm)
              (CategoryTheory.Linear.units_smul_comp (R := ℤ) k.negOnePow
                (eqToHom (shiftFunctorAux_obj_X C k K i))
                (K.d (i + k) (j + k)))
    _ =
      k.negOnePow •
          ((eqToHom (shiftFunctorAux_obj_X C k K i) ≫ K.d (i + k) (j + k)) ≫
            eqToHom (shiftFunctorAux_obj_X C k K j).symm) := by
          simpa using
            (CategoryTheory.Linear.units_smul_comp (R := ℤ) k.negOnePow
              (eqToHom (shiftFunctorAux_obj_X C k K i) ≫ K.d (i + k) (j + k))
              (eqToHom (shiftFunctorAux_obj_X C k K j).symm))
    _ =
      k.negOnePow •
          (eqToHom (shiftFunctorAux_obj_X C k K i) ≫
            (K.d (i + k) (j + k) ≫
              eqToHom (shiftFunctorAux_obj_X C k K j).symm)) := by
          rw [Category.assoc]
    _ =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow •
          (K.d (i + k) (j + k) ≫
            eqToHom (shiftFunctorAux_obj_X C k K j).symm)) := by
          rw [← Linear.comp_units_smul]
    _ =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        ((k.negOnePow • K.d (i + k) (j + k)) ≫
          eqToHom (shiftFunctorAux_obj_X C k K j).symm) := by
          rw [Linear.units_smul_comp]
    _ =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        ((k.negOnePow • K.d (i + k) (j + k)) ≫
          eqToHom (shiftFunctorAux_obj_X C k K j).symm) := by
          rfl
    _ =
      eqToHom (shiftFunctorAux_obj_X C k K i) ≫
        (k.negOnePow • K.d (i + k) (j + k)) ≫
          eqToHom (shiftFunctorAux_obj_X C k K j).symm := by
          simp

-- Proof sketch: unfold `shiftFunctorAux`, pass through the cochain-equivalence transport, and
-- read off the component in translated degree `n + k`.
-- TODO: rewrite the pullback shift map component as the cochain map component in degree `-n`,
-- then simplify the transported source and target identifications.
private theorem shiftFunctorAux_map_f (k : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    ((shiftFunctorAux C k).map φ).f n =
      eqToHom (shiftFunctorAux_obj_X C k K n) ≫
        φ.f (n + k) ≫
        eqToHom (shiftFunctorAux_obj_X C k L n).symm := by
  -- Route correction: compute the shifted cochain-map component at degree `-n`, then simplify
  -- the negation transport on source and target degrees.
  change
    ((shiftFunctor (cochainShiftPullback C) k).map ((chainToCochain C).map φ)).f (-n) =
      eqToHom (shiftFunctorAux_obj_X C k K n) ≫
        φ.f (n + k) ≫
        eqToHom (shiftFunctorAux_obj_X C k L n).symm
  rw [pullback_shift_map_f_neg]
  -- Identify the chain-to-cochain component with the restriction-map component.
  change
    (restrictionMap φ ComplexShape.embeddingUpIntDownInt).f (-n - k) =
      eqToHom (shiftFunctorAux_obj_X C k K n) ≫
        φ.f (n + k) ≫
        eqToHom (shiftFunctorAux_obj_X C k L n).symm
  rw [HomologicalComplex.restrictionMap_f'
    (K := K) (L := L) (φ := φ) (e := ComplexShape.embeddingUpIntDownInt)
    (i := -n - k) (i' := n + k) (show -(-n - k) = n + k by omega)]
  rw [chainToCochain_restrictionXIso_hom_eq_shiftFunctorAux_obj_X
    (C := C) k K n]
  rw [chainToCochain_restrictionXIso_inv_eq_shiftFunctorAux_obj_X
    (C := C) k L n]
  -- The remaining comparison maps are now exactly the transports from `shiftFunctorAux_obj_X`.
  rfl

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

/-- Helper for Definition 12.14.1: the displayed inverse degree isomorphism is the inverse
transport from `shiftFunctor_obj_X`. -/
private theorem shiftFunctorObjXIso_inv_eq_eqToHom
    (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    (K.shiftFunctorObjXIso k n (n + k) rfl).inv =
      eqToHom (shiftFunctor_obj_X k K n).symm := by
  -- Unfold the displayed degree isomorphism; for the witness `rfl` it is just an `eqToIso`.
  simp [shiftFunctorObjXIso]

/-- Helper for Definition 12.14.1: the auxiliary and public degree identifications induce the same
forward transport. -/
private theorem shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom
    (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    eqToHom (shiftFunctorAux_obj_X C k K n) = eqToHom (shiftFunctor_obj_X k K n) := by
  exact eqToHom_proof_irrel C _ _

/-- Helper for Definition 12.14.1: the auxiliary and public degree identifications induce the same
inverse transport. -/
private theorem shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom_symm
    (k : ℤ) (K : ChainComplex C ℤ) (n : ℤ) :
    eqToHom (shiftFunctorAux_obj_X C k K n).symm =
      eqToHom (shiftFunctor_obj_X k K n).symm := by
  exact eqToHom_proof_irrel C _ _

-- Proof sketch: rewrite the shifted differential through the canonical degree isomorphisms and
-- simplify the transported cochain-shift formula.
/-- Via the canonical degree identifications, the differential on `K⟦k⟧` is
`(-1)^k` times the translated differential of `K`. -/
theorem shiftFunctor_obj_d (k : ℤ) (K : ChainComplex C ℤ) (i j : ℤ) :
    (K.shiftFunctorObjXIso k i (i + k) rfl).inv ≫ (K⟦k⟧).d i j =
      (k.negOnePow • K.d (i + k) (j + k)) ≫
        (K.shiftFunctorObjXIso k j (j + k) rfl).inv := by
  -- Identify the generated shift functor with the auxiliary one used to define it.
  rw [shiftFunctorObjXIso_inv_eq_eqToHom]
  rw [shiftFunctorObjXIso_inv_eq_eqToHom (k := k) (K := K) (n := j)]
  -- Normalize the public shift back to the auxiliary model used to define the instance.
  change
    eqToHom (shiftFunctor_obj_X k K i).symm ≫ ((shiftFunctorAux C k).obj K).d i j =
      (k.negOnePow • K.d (i + k) (j + k)) ≫ eqToHom (shiftFunctor_obj_X k K j).symm
  -- Rewrite the shifted differential by the auxiliary transport formula and cancel the left pair
  -- of consecutive `eqToHom` morphisms.
  rw [shiftFunctorAux_obj_d (C := C)]
  rw [shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom (C := C)]
  rw [shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom_symm (C := C)]
  let p : (K⟦k⟧).X i = K.X (i + k) := shiftFunctor_obj_X k K i
  have hp : p.symm.trans p = rfl := by
    apply Subsingleton.elim
  change eqToHom p.symm ≫ eqToHom p ≫ (k.negOnePow • K.d (i + k) (j + k)) ≫
      eqToHom (shiftFunctor_obj_X k K j).symm =
    (k.negOnePow • K.d (i + k) (j + k)) ≫ eqToHom (shiftFunctor_obj_X k K j).symm
  rw [CategoryTheory.eqToHom_trans_assoc, hp]
  simp

-- Proof sketch: rewrite the shifted component through the canonical degree isomorphisms and
-- simplify the transported cochain-shift formula.
/-- Via the canonical degree identifications, the degree-`n` component of the shifted morphism is
the degree-`n + k` component of the original morphism. -/
theorem shiftFunctor_map_f (k : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    (K.shiftFunctorObjXIso k n (n + k) rfl).inv ≫
        ((shiftFunctor (ChainComplex C ℤ) k).map φ).f n =
      φ.f (n + k) ≫ (L.shiftFunctorObjXIso k n (n + k) rfl).inv := by
  -- Identify the generated shift functor with the auxiliary one used to define it.
  rw [shiftFunctorObjXIso_inv_eq_eqToHom]
  rw [shiftFunctorObjXIso_inv_eq_eqToHom (k := k) (K := L) (n := n)]
  -- Normalize the public shift back to the auxiliary model used to define the instance.
  change
    eqToHom (shiftFunctor_obj_X k K n).symm ≫ ((shiftFunctorAux C k).map φ).f n =
      φ.f (n + k) ≫ eqToHom (shiftFunctor_obj_X k L n).symm
  -- Rewrite the shifted component by the auxiliary transport formula and cancel the left pair of
  -- consecutive `eqToHom` morphisms.
  rw [shiftFunctorAux_map_f (C := C)]
  rw [shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom (C := C)]
  rw [shiftFunctorAux_obj_X_eq_shiftFunctor_obj_X_eqToHom_symm (C := C)]
  let p : (K⟦k⟧).X n = K.X (n + k) := shiftFunctor_obj_X k K n
  have hp : p.symm.trans p = rfl := by
    apply Subsingleton.elim
  change eqToHom p.symm ≫ eqToHom p ≫ φ.f (n + k) ≫
      eqToHom (shiftFunctor_obj_X k L n).symm =
    φ.f (n + k) ≫ eqToHom (shiftFunctor_obj_X k L n).symm
  rw [CategoryTheory.eqToHom_trans_assoc, hp]
  simp

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
