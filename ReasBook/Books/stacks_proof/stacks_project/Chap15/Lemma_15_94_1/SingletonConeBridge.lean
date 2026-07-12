import Mathlib

noncomputable section

open CategoryTheory
open ComplexShape

universe u

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.94.1: positive cochain degrees of the extended homotopy cofiber vanish,
so the remaining cone-bridge work only has to compare degrees `0` and `-1`. -/
private theorem extend_homotopyCofiber_isZero_pos
    {C : ChainComplex (ModuleCat A) ℕ} (φ : C ⟶ C) (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X (m + 1 : ℤ)) := by
  -- Positive integers are not in the image of `n ↦ -n`, so extension by zero kills these terms.
  change CategoryTheory.Limits.IsZero (((HomologicalComplex.homotopyCofiber φ).extend
      ComplexShape.embeddingDownNat).X (m + 1 : ℤ))
  apply (HomologicalComplex.homotopyCofiber φ).isZero_extend_X
    ComplexShape.embeddingDownNat (m + 1 : ℤ)
  intro i hi
  dsimp [ComplexShape.embeddingDownNat] at hi
  omega

/-- Helper for Lemma 15.94.1: if the extension of `C` is concentrated in degree `0`, then every
negative degree `-(m + 1)` of the extended cochain complex vanishes. -/
private theorem singleton_extend_isZero_neg_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C).X
        (-((m + 1 : ℕ) : ℤ))) := by
  -- Transport the vanishing from the degree-zero single complex along the chosen comparison `e`.
  have hsingle :
      CategoryTheory.Limits.IsZero
        ((((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).X
          (-((m + 1 : ℕ) : ℤ)))) := by
    apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (0 : ℤ) M (-((m + 1 : ℕ) : ℤ)))
    omega
  exact hsingle.of_iso
    ((HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) (-((m + 1 : ℕ) : ℤ))).mapIso e)

/-- Helper for Lemma 15.94.1: under a degree-zero single-complex identification, every positive
chain degree of `C` vanishes. -/
private theorem singleton_chain_isZero_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))
    (m : ℕ) :
    CategoryTheory.Limits.IsZero (C.X (m + 1)) := by
  -- Degree `m + 1` of the chain complex becomes cochain degree `-(m + 1)` after extension.
  exact
    (singleton_extend_isZero_neg_succ (e := e) m).of_iso
      ((C.extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (m + 1) = -((m + 1 : ℕ) : ℤ) by rfl)).symm)

/-- Helper for Lemma 15.94.1: if the left summand is zero, then the projection
`X ⊞ Y ⟶ Y` is an isomorphism in `ModuleCat A`. -/
private theorem biprod_snd_isIso_of_isZero_left
    {X Y : ModuleCat A} [CategoryTheory.Limits.HasBinaryBiproduct X Y]
    (hX : CategoryTheory.Limits.IsZero X) :
    IsIso (Limits.biprod.snd : X ⊞ Y ⟶ Y) := by
  letI : CategoryTheory.Limits.IsZero X := hX
  have hfst_zero : (Limits.biprod.fst : X ⊞ Y ⟶ X) = 0 := by
    exact hX.eq_of_tgt _ _
  -- Use `biprod.inr` as the inverse and collapse the vanished left summand.
  refine ⟨⟨Limits.biprod.inr, ?_, ?_⟩⟩
  · -- Compare both endomorphisms of the biproduct through their two projections.
    apply Limits.biprod.hom_ext
    · simpa [Category.assoc, hfst_zero]
    · simp [Category.assoc]
  · simp

/-- Helper for Lemma 15.94.1: if the right summand is zero, then the projection
`X ⊞ Y ⟶ X` is an isomorphism in `ModuleCat A`. -/
private theorem biprod_fst_isIso_of_isZero_right
    {X Y : ModuleCat A} [CategoryTheory.Limits.HasBinaryBiproduct X Y]
    (hY : CategoryTheory.Limits.IsZero Y) :
    IsIso (Limits.biprod.fst : X ⊞ Y ⟶ X) := by
  letI : CategoryTheory.Limits.IsZero Y := hY
  have hsnd_zero : (Limits.biprod.snd : X ⊞ Y ⟶ Y) = 0 := by
    exact hY.eq_of_tgt _ _
  -- Use `biprod.inl` as the inverse and collapse the vanished right summand.
  refine ⟨⟨Limits.biprod.inl, ?_, ?_⟩⟩
  · -- Compare both endomorphisms of the biproduct through their two projections.
    apply Limits.biprod.hom_ext
    · simp [Category.assoc]
    · simpa [Category.assoc, hsnd_zero]
  · simp

/-- Helper for Lemma 15.94.1: once `C` is concentrated in degree `0`, the extended homotopy
cofiber has no terms below degree `-1`. -/
private theorem singleton_homotopyCofiber_isZero_neg_two_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X (-((m + 2 : ℕ) : ℤ))) := by
  -- Route correction: the needed owner vanishing is obtained by transporting the explicit
  -- biproduct description of `homotopyCofiber φ` in degree `m + 2`.
  have hleft : CategoryTheory.Limits.IsZero (C.X (m + 1)) := by
    exact singleton_chain_isZero_succ (e := e) m
  have hright : CategoryTheory.Limits.IsZero (C.X (m + 2)) := by
    exact singleton_chain_isZero_succ (e := e) (m := m + 1)
  letI :
      IsIso (Limits.biprod.snd : C.X (m + 1) ⊞ C.X (m + 2) ⟶ C.X (m + 2)) := by
    -- The left summand already vanishes, so projection to the right summand is invertible.
    simpa using biprod_snd_isIso_of_isZero_left
      (X := C.X (m + 1)) (Y := C.X (m + 2)) hleft
  have hcone_biprod : CategoryTheory.Limits.IsZero (C.X (m + 1) ⊞ C.X (m + 2)) := by
    -- Identify the biproduct with the zero right summand through the invertible projection.
    exact hright.of_iso
      (asIso (Limits.biprod.snd : C.X (m + 1) ⊞ C.X (m + 2) ⟶ C.X (m + 2)))
  have hchain : CategoryTheory.Limits.IsZero ((HomologicalComplex.homotopyCofiber φ).X (m + 2)) := by
    -- In chain degree `m + 2`, `XIsoBiprod` is exactly the cone decomposition
    -- `C.X (m + 1) ⊞ C.X (m + 2)`.
    exact hcone_biprod.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ (m + 2) (m + 1)
        (by simp [ComplexShape.down]))
  exact hchain.of_iso
    ((HomologicalComplex.homotopyCofiber φ).extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (m + 2) = -((m + 2 : ℕ) : ℤ) by rfl))

/-- Helper for Lemma 15.94.1: the literal mapping cone of a degree-zero single-complex self-map
is supported only in degrees `0` and `-1`. -/
private theorem single_map_mappingCone_isZero_outside
    {M : ModuleCat A} (g : M ⟶ M) {i : ℤ} (hi0 : i ≠ 0) (hiNegOne : i ≠ -1) :
    CategoryTheory.Limits.IsZero
      ((CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g)).X i) := by
  -- Rewrite the cone term as the biproduct of the two neighboring single-complex terms, both of
  -- which are zero away from the window `{0, -1}`.
  have hleft :
      CategoryTheory.Limits.IsZero
        ((((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).X (i + 1))) := by
    apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (0 : ℤ) M (i + 1))
    intro hi
    apply hiNegOne
    linarith
  have hright :
      CategoryTheory.Limits.IsZero
        ((((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).X i)) := by
    apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (0 : ℤ) M i)
    exact hi0
  exact
    (CochainComplex.mappingCone.isZero_X_iff
      (φ := ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g)) i).2
      ⟨hleft, hright⟩

/-- Helper for Lemma 15.94.1: if an extended chain complex is identified with the degree-zero
single complex on `M` and the transported endomorphism is conjugate to `(singleFunctor _ 0).map g`,
then the extended homotopy cofiber should identify with the literal mapping cone of that
single-complex map. -/
noncomputable abbrev extend_homotopyCofiber_conjugate_single_map_iso_mappingCone
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C) (g : M ⟶ M)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)
    (hconj :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map φ) =
        e.hom ≫
          (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g ≫
            e.inv) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber φ)) ≅
        CochainComplex.mappingCone
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g) := by
  -- Route correction: isolate the transport/coercion blocker here, before returning to the
  -- one-generator Koszul stage. The support bookkeeping is now closed by
  -- `extend_homotopyCofiber_isZero_pos`,
  -- `singleton_homotopyCofiber_isZero_neg_two_succ`, and
  -- `single_map_mappingCone_isZero_outside`, so only the degree `0/-1` components and their
  -- unique differential still need to be compared using `hconj`.
  sorry

end

end CategoryTheory
