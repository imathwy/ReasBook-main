import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_6
import StacksProject_2024.Chap10.Lemma_10_52_11
import StacksProject_2024.Chap15.Lemma_15_121_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing Module.End

universe u v w

section

/-
Domain triage:
- primary domain: finite-length determinants of scalar-multiplication endomorphisms after
  restricting scalars along a local homomorphism;
- sampled owner API:
  `Module.End.finiteLengthDeterminant`,
  `Module.End.finiteLengthDeterminant_eq_mul_of_shortExact`,
  `isFiniteLength_iff_exists_compositionSeries`,
  `CompositionSeries.factor_isSimpleModule`,
  `Module.length_compositionSeries`;
- core/canonical owner: `Module.End.finiteLengthDeterminant` on the restricted-scalar endomorphism
  `Algebra.lsmul R R' R M' u`;
- source-facing layer: Lemma `15.121.2`, expressing that determinant by the residue-field norm
  formula;
- bridge/view layer: an `R'`-composition series is an internal proof device for the
  restricted-scalar finite-length hypothesis and the factorwise reduction, but it is not part of
  the public determinant statement;
- primitive data: the local map `R → R'`, the scalar `u : R'`, and the finite-length owner
  hypothesis `IsFiniteLength R' M'`;
- derived API: restricted-scalar finite length, an internally chosen composition series, and the
  simple-factor norm computation.
-/

variable {R : Type u} {R' : Type v} {M' : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

local notation "κ" => IsLocalRing.ResidueField R
local notation "κ'" => IsLocalRing.ResidueField R'

local noncomputable instance residueFieldModule : Module R' κ' :=
  Module.compHom κ' (IsLocalRing.residue R')

/-- Helper for Lemma 15.121.2: the quotient by the maximal ideal of a local ring is the canonical
local residue field. -/
private noncomputable abbrev maximalIdeal_quotient_residueField_equiv :
    (R' ⧸ maximalIdeal R') ≃+* κ' :=
  RingEquiv.ofBijective (algebraMap (R' ⧸ maximalIdeal R') κ')
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R'))

/-- Helper for Lemma 15.121.2: the quotient-to-residue-field identification is linear over the
local ring itself. -/
private noncomputable abbrev maximalIdeal_quotient_linearEquiv_residueField :
    (R' ⧸ maximalIdeal R') ≃ₗ[R'] κ' :=
  { toFun := maximalIdeal_quotient_residueField_equiv (R' := R')
    invFun := (maximalIdeal_quotient_residueField_equiv (R' := R')).symm
    left_inv := (maximalIdeal_quotient_residueField_equiv (R' := R')).left_inv
    right_inv := (maximalIdeal_quotient_residueField_equiv (R' := R')).right_inv
    map_add' := (maximalIdeal_quotient_residueField_equiv (R' := R')).map_add
    map_smul' := by
      intro a x
      -- Both scalar actions are multiplication by the image of `a` in the quotient/residue field.
      change
        maximalIdeal_quotient_residueField_equiv (R' := R')
            (((Ideal.Quotient.mk (maximalIdeal R')) a) * x) =
          (IsLocalRing.residue R' a) *
            maximalIdeal_quotient_residueField_equiv (R' := R') x
      rw [(maximalIdeal_quotient_residueField_equiv (R' := R')).map_mul]
      rfl }

/-- Helper for Lemma 15.121.2: if `K ≤ L` are `R'`-submodules, their carrier types are linearly
equivalent over the restricted scalar ring `R` to the corresponding `submoduleOf` view. -/
private noncomputable def submoduleOf_restrictScalars_linearEquiv
    {K L : Submodule R' M'} (hKL : K ≤ L) :
    K ≃ₗ[R] K.submoduleOf L :=
  { toFun := fun x ↦ ⟨⟨x.1, hKL x.2⟩, x.2⟩
    invFun := fun x ↦ ⟨x.1.1, x.2⟩
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro x
      ext
      rfl
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro a x
      rfl }

/-- Helper for Lemma 15.121.2: the top `R'`-submodule is canonically the ambient restricted-scalar
`R`-module. -/
private noncomputable def top_restrictScalars_linearEquiv :
    (⊤ : Submodule R' M') ≃ₗ[R] M' :=
  { toFun := fun x ↦ x.1
    invFun := fun x ↦ ⟨x, by simp⟩
    left_inv := by
      intro x
      ext
      rfl
    right_inv := by
      intro x
      rfl
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro a x
      rfl }

/-- A simple `R'`-module has finite length after restricting scalars along a local homomorphism
with finite residue-field extension. -/
private theorem isFiniteLength_restrictScalars_of_simple [Module.Finite κ κ']
    (N : Type*) [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    [IsSimpleModule R' N] :
    IsFiniteLength R N := by
  let _ : Module R' κ' := Module.compHom κ' (IsLocalRing.residue R')
  let _ : Algebra R κ := (IsLocalRing.residue R).toAlgebra
  let _ : Algebra κ κ' := (IsLocalRing.ResidueField.map (algebraMap R R')).toAlgebra
  let _ : Algebra R κ' := ((IsLocalRing.residue R').comp (algebraMap R R')).toAlgebra
  let _ : IsScalarTower R κ κ' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    -- The scalar action through `κ` is the canonical residue-field map of the local homomorphism.
    simpa using (IsLocalRing.ResidueField.map_residue (algebraMap R R') a).symm
  obtain ⟨I, hImax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule R' N)
  have hI : I = maximalIdeal R' := IsLocalRing.eq_maximalIdeal hImax
  let eκ' : N ≃ₗ[R'] κ' :=
    e.trans <|
      (Submodule.quotEquivOfEq _ _ hI.symm).trans
        (maximalIdeal_quotient_linearEquiv_residueField (R' := R'))
  let eR :
      let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
      N ≃ₗ[R] κ' :=
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    { toFun := eκ'
      invFun := eκ'.symm
      left_inv := eκ'.left_inv
      right_inv := eκ'.right_inv
      map_add' := eκ'.map_add
      map_smul' := by
        intro a x
        -- Restrict scalar linearity along `R → R'` and then through the residue map on `κ'`.
        change eκ' (((algebraMap R R') a) • x) =
          (((IsLocalRing.residue R').comp (algebraMap R R')) a) • eκ' x
        exact eκ'.map_smulₛₗ ((algebraMap R R') a) x }
  have htorsκ' : Module.IsTorsionBySet R κ' (maximalIdeal R) := by
    intro x a ha
    have hnonunit : ¬ IsUnit a := by
      rw [← IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact ha
    have hmap_mem : algebraMap R R' a ∈ maximalIdeal R' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact IsLocalHom.map_nonunit a hnonunit
    have hzero : IsLocalRing.residue R' (algebraMap R R' a) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmap_mem
    -- Elements of the source maximal ideal act trivially after passing to the target residue field.
    simpa [hzero]
  have htors : Module.IsTorsionBySet R N (maximalIdeal R) := by
    intro x a ha
    apply eR.injective
    -- Transport the torsion statement across the restricted-scalar equivalence with `κ'`.
    simpa using htorsκ' (eR x) a ha
  have hfiniteκ' : Module.Finite R κ' := Module.Finite.of_restrictScalars_finite R κ κ'
  have hfiniteN : Module.Finite R N := (Module.Finite.equiv_iff eR).2 hfiniteκ'
  -- Once the source maximal ideal acts by zero, Lemma `10.52.6` turns finite generation into
  -- finite length.
  exact (isFiniteLength_iff_finite_of_isTorsionBySet htors).2 hfiniteN

/-- An `R'`-composition series from `⊥` to `⊤` yields finite length for the underlying
`R`-module. -/
private theorem isFiniteLength_restrictScalars_of_compositionSeries
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
    IsFiniteLength R M' := by
  -- Route correction: the packaged semilocal bridge is unavailable in this environment, so we
  -- rebuild the restricted-scalar finite-length proof by climbing the chosen `R'`-composition
  -- series one simple factor at a time.
  have hstage :
      ∀ n, ∀ hn : n ≤ s.length, IsFiniteLength R ↥(s ⟨n, Nat.lt_succ_of_le hn⟩) := by
    intro n
    induction n with
    | zero =>
        intro hn
        -- The initial stage is `⊥`, hence its carrier is a subsingleton module.
        simpa [h₀] using (IsFiniteLength.of_subsingleton (R := R)
          (M := ↥(⊥ : Submodule R' M')))
    | succ n ihn =>
        intro hn
        let i : Fin s.length := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
        have hprev : IsFiniteLength R ↥(s i.castSucc) := by
          simpa [i] using ihn (Nat.le_of_succ_le hn)
        have hprev_submodule : IsFiniteLength R ↥((s i.castSucc).submoduleOf (s i.succ)) := by
          rw [Module.length_ne_top_iff] at hprev ⊢
          -- Reinterpret the previous stage as a submodule of the current stage.
          simpa using
            (show Module.length R ↥((s i.castSucc).submoduleOf (s i.succ)) ≠ ⊤ from by
              rw [LinearEquiv.length_eq
                ((submoduleOf_restrictScalars_linearEquiv (R := R) (R' := R')
                    (M' := M') (CovBy.le (s.step i))).symm :
                  ↥((s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[R] ↥(s i.castSucc))]
              exact hprev)
        have hsimple : IsSimpleModule R' (s.factor i) := s.factor_isSimpleModule i
        have hfactor : IsFiniteLength R (s.factor i) := by
          exact @isFiniteLength_restrictScalars_of_simple R R' _ _ _ _ _ _ _
            (s.factor i) _ _ _ _ hsimple
        have hcurr : IsFiniteLength R ↥(s i.succ) := by
          -- Finite length is equivalent to being both Noetherian and Artinian, and both owners
          -- are stable under passage from a submodule and its quotient to the ambient module.
          rw [isFiniteLength_iff_isNoetherian_isArtinian]
          exact
            ⟨(isNoetherian_iff_submodule_quotient ((s i.castSucc).submoduleOf (s i.succ))).mpr
                ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hprev_submodule).1,
                  (isFiniteLength_iff_isNoetherian_isArtinian.mp hfactor).1⟩,
              (isArtinian_iff_submodule_quotient ((s i.castSucc).submoduleOf (s i.succ))).mpr
                ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hprev_submodule).2,
                  (isFiniteLength_iff_isNoetherian_isArtinian.mp hfactor).2⟩⟩
        simpa [i] using hcurr
  have htop : IsFiniteLength R ↥(⊤ : Submodule R' M') := by
    simpa [h₁] using hstage s.length le_rfl
  rw [Module.length_ne_top_iff] at htop ⊢
  -- Identify the last stage `⊤` with the ambient module `M'`.
  simpa using
    (show Module.length R ↥(⊤ : Submodule R' M') ≠ ⊤ from by
      rw [LinearEquiv.length_eq (top_restrictScalars_linearEquiv (R := R) (R' := R')
        (M' := M'))]
      exact htop)

/-- A finite-length `R'`-module has finite length after restricting scalars along a local
homomorphism with finite residue-field extension. -/
private theorem isFiniteLength_restrictScalars [Module.Finite κ κ']
    (hM' : IsFiniteLength R' M') :
    IsFiniteLength R M' := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM'
  exact isFiniteLength_restrictScalars_of_compositionSeries s h₀ h₁

/-- Each simple `R'`-factor in a composition series has finite length over the restricted scalar
ring `R`. -/
private theorem factor_isFiniteLength_restrictScalars [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    IsFiniteLength R (s.factor i) := by
  have hsimple : IsSimpleModule R' (s.factor i) := s.factor_isSimpleModule i
  exact @isFiniteLength_restrictScalars_of_simple R R' _ _ _ _ _ _ _ (s.factor i) _ _ _ _ hsimple

/-- Helper for Lemma 15.121.2: every simple factor in an `R'`-composition series is linearly
equivalent to the target residue field. -/
private theorem factor_linearEquiv_residueField
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    Nonempty (s.factor i ≃ₗ[R'] κ') := by
  have hAnn :
      Module.annihilator R' (s.factor i) = maximalIdeal R' := by
    let _ : IsSimpleModule R' (s.factor i) := s.factor_isSimpleModule i
    exact IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  obtain ⟨e⟩ :=
    CompositionSeries.factor_isomorphic_quotient_annihilator (R := R') (M := M') s i
  -- Identify the quotient by the annihilator with the quotient by the maximal ideal, then with
  -- the canonical residue field.
  exact ⟨e.trans <|
    (Submodule.quotEquivOfEq _ _ hAnn.symm).trans
      (maximalIdeal_quotient_linearEquiv_residueField (R' := R'))⟩

/-- Helper for Lemma 15.121.2: after restricting scalars along `R → R'`, each simple
`R'`-composition factor is annihilated by `maximalIdeal R`. -/
private theorem factor_isTorsionBySet_maximalIdeal
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    Module.IsTorsionBySet R (s.factor i) (maximalIdeal R) := by
  let _ : Module R' κ' := Module.compHom κ' (IsLocalRing.residue R')
  let _ : Algebra R κ := (IsLocalRing.residue R).toAlgebra
  let _ : Algebra κ κ' := (IsLocalRing.ResidueField.map (algebraMap R R')).toAlgebra
  let _ : Algebra R κ' := ((IsLocalRing.residue R').comp (algebraMap R R')).toAlgebra
  let _ : IsScalarTower R κ κ' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    -- The scalar action through `κ` is the residue-field map induced by the local homomorphism.
    simpa using (IsLocalRing.ResidueField.map_residue (algebraMap R R') a).symm
  obtain ⟨e⟩ := factor_linearEquiv_residueField (R := R) (R' := R') (M' := M') s i
  let eR :
      let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
      s.factor i ≃ₗ[R] κ' :=
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        -- Restrict scalar linearity from `R'` to `R` and then pass to the residue field of `R'`.
        change e (((algebraMap R R') a) • x) =
          (((IsLocalRing.residue R').comp (algebraMap R R')) a) • e x
        exact e.map_smulₛₗ ((algebraMap R R') a) x }
  have htorsκ' : Module.IsTorsionBySet R κ' (maximalIdeal R) := by
    intro x a ha
    have hnonunit : ¬ IsUnit a := by
      rw [← IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact ha
    have hmap_mem : algebraMap R R' a ∈ maximalIdeal R' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact IsLocalHom.map_nonunit a hnonunit
    have hzero : IsLocalRing.residue R' (algebraMap R R' a) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmap_mem
    -- Elements from the source maximal ideal act by zero on the target residue field.
    simpa [hzero]
  intro x a ha
  apply eR.injective
  -- Transport the annihilation statement back across the restricted-scalar equivalence.
  simpa using htorsκ' (eR x) a ha

/-- Helper for Lemma 15.121.2: if `maximalIdeal R` acts trivially on `N`, then the residue-field
tensor model used by `finiteLengthDeterminant` collapses back to `N` itself. -/
private noncomputable def residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
    {N : Type*} [AddCommGroup N] [Module R N]
    (htors : Module.IsTorsionBySet R N (maximalIdeal R)) :
    let _ : Module κ N := htors.module
    κ ⊗[R] N ≃ₗ[κ] N := by
  let _ : Algebra R κ := (IsLocalRing.residue R).toAlgebra
  let _ : Module κ N := htors.module
  -- Once the action factors through `κ = R ⧸ maximalIdeal R`, the left tensor unit collapses.
  exact (Algebra.TensorProduct.lidOfCompatibleSMul R κ N).toLinearEquiv

/-- Helper for Lemma 15.121.2: after restricting scalars along `R → R'`, the target residue field
is annihilated by the maximal ideal of `R`. -/
private theorem residueField_isTorsionBySet_maximalIdeal :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    Module.IsTorsionBySet R κ' (maximalIdeal R) := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  intro x a ha
  have hnonunit : ¬ IsUnit a := by
    rw [← IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ha
  have hmap_mem : algebraMap R R' a ∈ maximalIdeal R' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact IsLocalHom.map_nonunit a hnonunit
  have hzero : IsLocalRing.residue R' (algebraMap R R' a) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmap_mem
  -- The source maximal ideal acts by zero after passing to the target residue field.
  simpa [hzero]

/-- Helper for Lemma 15.121.2: after restricting scalars from `R'` to `R`, each simple factor in
an `R'`-composition series identifies with the target residue field. -/
private noncomputable def factor_restrictScalars_linearEquiv_residueField
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    s.factor i ≃ₗ[R] κ' := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  obtain ⟨e⟩ := factor_linearEquiv_residueField (R := R) (R' := R') (M' := M') s i
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        -- Restrict scalar linearity from `R'` to `R` and then pass to the residue class in `κ'`.
        change e (((algebraMap R R') a) • x) =
          (((IsLocalRing.residue R').comp (algebraMap R R')) a) • e x
        exact e.map_smulₛₗ ((algebraMap R R') a) x }

/-- Helper for Lemma 15.121.2: the restricted-scalar identification of a simple factor with `κ'`
intertwines multiplication by `u` with multiplication by the residue class of `u`. -/
private theorem factor_restrictScalars_linearEquiv_residueField_map_lsmul
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R')
    (x : s.factor i) :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    factor_restrictScalars_linearEquiv_residueField (R := R) (R' := R') (M' := M') s i (u • x) =
      (IsLocalRing.residue R' u) *
        factor_restrictScalars_linearEquiv_residueField
          (R := R) (R' := R') (M' := M') s i x := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  obtain ⟨e⟩ := factor_linearEquiv_residueField (R := R) (R' := R') (M' := M') s i
  -- Read the restricted-scalar equivalence as the original `R'`-linear equivalence.
  change e (u • x) = (IsLocalRing.residue R' u) * e x
  simpa [Algebra.smul_def] using e.map_smulₛₗ u x

/-- Helper for Lemma 15.121.2: after restricting scalars, the factor-to-residue-field
identification conjugates multiplication by `u` on a simple factor to multiplication by the
residue class of `u` on `κ'`. -/
private theorem factor_restrictScalars_linearEquiv_residueField_conj_lsmul
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R') :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    Algebra.lsmul R κ' κ' (IsLocalRing.residue R' u) =
      (factor_restrictScalars_linearEquiv_residueField
          (R := R) (R' := R') (M' := M') s i).toLinearMap ∘ₗ
        Algebra.lsmul R R (s.factor i) u ∘ₗ
          (factor_restrictScalars_linearEquiv_residueField
            (R := R) (R' := R') (M' := M') s i).symm.toLinearMap := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  -- Evaluate both endomorphisms on a residue-field element and use the pointwise intertwining
  -- statement from the factor equivalence.
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  simpa using
    factor_restrictScalars_linearEquiv_residueField_map_lsmul
      (R := R) (R' := R') (M' := M') s i u
      ((factor_restrictScalars_linearEquiv_residueField
          (R := R) (R' := R') (M' := M') s i).symm x)

/-- Helper for Lemma 15.121.2: when `maximalIdeal R` acts trivially on `N`, any `R`-linear
endomorphism of `N` descends to a `κ`-linear endomorphism with the same underlying function. -/
private noncomputable def endHom_over_residueField_of_isTorsionBySet_maximalIdeal
    {N : Type*} [AddCommGroup N] [Module R N]
    (htors : Module.IsTorsionBySet R N (maximalIdeal R))
    (φ : Module.End R N) :
    let _ : Module κ N := htors.module
    Module.End κ N := by
  let _ : Module κ N := htors.module
  -- The descended endomorphism keeps the same additive map; only the scalar owner changes.
  exact
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro a x
        rfl }

/-- Helper for Lemma 15.121.2: after descending the restricted-scalar endomorphism on `κ'` along
the maximal-ideal torsion action, one recovers the ordinary `κ`-linear scalar-multiplication map. -/
private theorem residueField_descended_lsmul_eq
    (u : R') :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    let _ : Module κ κ' := residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R').module
    endHom_over_residueField_of_isTorsionBySet_maximalIdeal
        (R := R) (N := κ') (residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R'))
        (Algebra.lsmul R κ' κ' (IsLocalRing.residue R' u)) =
      Algebra.lsmul κ κ κ' (IsLocalRing.residue R' u) := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  let _ : Module κ κ' := residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R').module
  -- Both descended endomorphisms are definitionally the same scalar-multiplication map on `κ'`.
  rfl

/-- Helper for Lemma 15.121.2: the ordinary `κ`-determinant of the descended scalar-multiplication
endomorphism on `κ'` is the field norm. -/
private theorem residueField_descended_det_eq_norm
    [Module.Finite κ κ']
    (u : R') :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    let _ : Module κ κ' := residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R').module
    LinearMap.det
      (endHom_over_residueField_of_isTorsionBySet_maximalIdeal
        (R := R) (N := κ') (residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R'))
        (Algebra.lsmul R κ' κ' (IsLocalRing.residue R' u))) =
      Algebra.norm κ (IsLocalRing.residue R' u) := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  let _ : Module κ κ' := residueField_isTorsionBySet_maximalIdeal (R := R) (R' := R').module
  -- First rewrite the descended endomorphism as ordinary `κ`-linear scalar multiplication.
  rw [residueField_descended_lsmul_eq (R := R) (R' := R') u]
  -- The field norm is defined as the determinant of multiplication by the scalar.
  simpa using Algebra.norm_apply κ (IsLocalRing.residue R' u)

/-- Helper for Lemma 15.121.2: when `maximalIdeal R` acts trivially on `N`, the tensor-collapse
equivalence conjugates the residue-field base change of an `R`-linear endomorphism to its
descended `κ`-linear endomorphism. -/
private theorem residueFieldTensor_linearEquiv_conj_descended_endomorphism
    {N : Type*} [AddCommGroup N] [Module R N]
    (htors : Module.IsTorsionBySet R N (maximalIdeal R))
    (φ : Module.End R N) :
    let _ : Module κ N := htors.module
    endHom_over_residueField_of_isTorsionBySet_maximalIdeal
        (R := R) (N := N) htors φ =
      (residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
          (R := R) (N := N) htors).toLinearMap ∘ₗ
        φ.baseChange κ ∘ₗ
          (residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
            (R := R) (N := N) htors).symm.toLinearMap := by
  let _ : Module κ N := htors.module
  let e := residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
    (R := R) (N := N) htors
  let ψ :=
    endHom_over_residueField_of_isTorsionBySet_maximalIdeal
      (R := R) (N := N) htors φ
  -- First compare the two sides after precomposing with the tensor-collapse equivalence.
  have hintertwine :
      ψ ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ φ.baseChange κ := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · rfl
    · intro a x
      -- On pure tensors, both sides reduce to scalar multiplication by `a` after applying `φ`.
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul]
      change φ (a • x) = a • φ x
      exact φ.map_smulₛₗ a x
    · intro z₁ z₂ hz₁ hz₂
      calc
        (ψ ∘ₗ e.toLinearMap) (z₁ + z₂)
            = (ψ ∘ₗ e.toLinearMap) z₁ + (ψ ∘ₗ e.toLinearMap) z₂ := by
                simp
        _ = (e.toLinearMap ∘ₗ φ.baseChange κ) z₁
              + (e.toLinearMap ∘ₗ φ.baseChange κ) z₂ := by
              rw [hz₁, hz₂]
        _ = (e.toLinearMap ∘ₗ φ.baseChange κ) (z₁ + z₂) := by
              simp
  -- Evaluate the intertwining identity on `e.symm y` to isolate the conjugacy formula.
  apply LinearMap.ext
  intro y
  have hy :=
    congrArg
      (fun f : κ ⊗[R] N →ₗ[κ] N => f (e.symm y))
      hintertwine
  simpa [LinearMap.comp_apply] using hy

/-- Helper for Lemma 15.121.2: on a finite-length `R`-module annihilated by `maximalIdeal R`, the
canonical finite-length determinant agrees with the ordinary determinant of the descended
`κ`-linear endomorphism. -/
private theorem finiteLengthDeterminant_eq_det_of_isTorsionBySet_maximalIdeal
    {N : Type*} [AddCommGroup N] [Module R N]
    (htors : Module.IsTorsionBySet R N (maximalIdeal R))
    (φ : Module.End R N) (hN : IsFiniteLength R N) :
    let _ : Module κ N := htors.module
    let _ : Module.Finite R N :=
      (isFiniteLength_iff_finite_of_isTorsionBySet
        (R := R) (m := maximalIdeal R) htors).1 hN
    let _ : Module.Finite κ N := Module.Finite.of_restrictScalars_finite R κ N
    let _ : FiniteDimensional κ N := FiniteDimensional.of_finite κ N
    φ.finiteLengthDeterminant hN =
      LinearMap.det
        (endHom_over_residueField_of_isTorsionBySet_maximalIdeal
          (R := R) (N := N) htors φ) := sorry

/-- Helper for Lemma 15.121.2: the tensor owner `κ ⊗[R] s.factor i` collapses to `κ'` by first
transporting the factor to `κ'` and then using the canonical tensor-unit identification. -/
private noncomputable def factor_residueFieldTensor_linearEquiv
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    κ ⊗[R] s.factor i ≃ₗ[κ] κ' := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  let eR :=
    factor_restrictScalars_linearEquiv_residueField
      (R := R) (R' := R') (M' := M') s i
  let eκ : κ ⊗[R] s.factor i ≃ₗ[κ] κ ⊗[R] κ' :=
    LinearEquiv.baseChange R κ (s.factor i) κ' eR
  -- First base change the factor equivalence, then collapse `κ ⊗[R] κ'` back to `κ'`.
  exact eκ.trans <|
    residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
      (R := R) (N := κ') residueField_isTorsionBySet_maximalIdeal

/-- Helper for Lemma 15.121.2: the tensor-to-residue-field identification sends pure tensors to
the expected scalar multiples in `κ'`. -/
private theorem factor_residueFieldTensor_linearEquiv_apply_tmul
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length)
    (a : κ) (x : s.factor i) :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    factor_residueFieldTensor_linearEquiv (R := R) (R' := R') (M' := M') s i (a ⊗ₜ[R] x) =
      a • factor_restrictScalars_linearEquiv_residueField
        (R := R) (R' := R') (M' := M') s i x := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  -- The base-change equivalence preserves pure tensors, and the tensor unit collapses by
  -- `lidOfCompatibleSMul`.
  simp [factor_residueFieldTensor_linearEquiv,
    residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal,
    factor_restrictScalars_linearEquiv_residueField,
    Algebra.TensorProduct.lidOfCompatibleSMul_tmul]

/-- Helper for Lemma 15.121.2: on pure tensors, the base-changed scalar-multiplication map on a
simple factor becomes multiplication by the residue class of `u` under the tensor collapse
equivalence. -/
private theorem factor_residueFieldTensor_linearEquiv_map_baseChange_lsmul_tmul
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R')
    (a : κ) (x : s.factor i) :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    factor_residueFieldTensor_linearEquiv (R := R) (R' := R') (M' := M') s i
      (((Algebra.lsmul R R (s.factor i) u).baseChange κ) (a ⊗ₜ[R] x)) =
        (IsLocalRing.residue R' u) *
          factor_residueFieldTensor_linearEquiv
            (R := R) (R' := R') (M' := M') s i (a ⊗ₜ[R] x) := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  -- Normalize the base-changed map on pure tensors before transporting the `u`-action through
  -- the factor-to-residue-field equivalence.
  rw [LinearMap.baseChange_tmul, factor_residueFieldTensor_linearEquiv_apply_tmul,
    factor_restrictScalars_linearEquiv_residueField_map_lsmul]
  calc
    a •
        ((IsLocalRing.residue R' u) *
          factor_restrictScalars_linearEquiv_residueField
            (R := R) (R' := R') (M' := M') s i x)
        = (IsLocalRing.residue R' u) *
            (a • factor_restrictScalars_linearEquiv_residueField
              (R := R) (R' := R') (M' := M') s i x) := by
              simp [mul_assoc]
    _ = (IsLocalRing.residue R' u) *
          factor_residueFieldTensor_linearEquiv
            (R := R) (R' := R') (M' := M') s i (a ⊗ₜ[R] x) := by
              rw [factor_residueFieldTensor_linearEquiv_apply_tmul]

/-- Helper for Lemma 15.121.2: conjugate `κ`-linear endomorphisms have the same determinant. -/
private theorem det_eq_of_linearEquiv_conj
    {V : Type*} {W : Type*}
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    [AddCommGroup W] [Module κ W] [FiniteDimensional κ W]
    (f : V →ₗ[κ] V) (g : W →ₗ[κ] W) (e : V ≃ₗ[κ] W)
    (hconj : g = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) :
    LinearMap.det g = LinearMap.det f := by
  classical
  let ι := Module.Free.ChooseBasisIndex κ V
  let b : Module.Basis ι κ V := Module.Free.chooseBasis κ V
  -- Transport a basis along `e` so the conjugate map has the same matrix as the original map.
  have hmatrix : LinearMap.toMatrix (b.map e) (b.map e) g = LinearMap.toMatrix b b f := by
    rw [hconj]
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.map_apply]
  -- Equal matrices in transported bases yield equal determinants.
  rw [← LinearMap.det_toMatrix (b.map e) g, hmatrix, LinearMap.det_toMatrix b f]

/-- Helper for Lemma 15.121.2: the tensor-collapse equivalence conjugates the full base-changed
scalar-multiplication endomorphism on a simple factor to ordinary multiplication by the residue
class of `u` on `κ'`. -/
private theorem factor_residueFieldTensor_linearEquiv_conj_baseChange_lsmul
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R') :
    let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
    Algebra.lsmul κ κ κ' (IsLocalRing.residue R' u) =
      (factor_residueFieldTensor_linearEquiv
          (R := R) (R' := R') (M' := M') s i).toLinearMap ∘ₗ
        (Algebra.lsmul R R (s.factor i) u).baseChange κ ∘ₗ
          (factor_residueFieldTensor_linearEquiv
            (R := R) (R' := R') (M' := M') s i).symm.toLinearMap := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  let eκ :=
    factor_residueFieldTensor_linearEquiv (R := R) (R' := R') (M' := M') s i
  let f := (Algebra.lsmul R R (s.factor i) u).baseChange κ
  let g := Algebra.lsmul κ κ κ' (IsLocalRing.residue R' u)
  have hintertwine : g ∘ₗ eκ.toLinearMap = eκ.toLinearMap ∘ₗ f := by
    -- Both sides are `κ`-linear, so it suffices to compare them on pure tensors.
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [f, g]
    · intro a x
      -- Normalize the tensor-owner action on pure tensors before transporting across `eκ`.
      change
        (IsLocalRing.residue R' u) *
            eκ (a ⊗ₜ[R] x) =
          eκ (f (a ⊗ₜ[R] x))
      simpa [eκ, f, g] using
        (factor_residueFieldTensor_linearEquiv_map_baseChange_lsmul_tmul
          (R := R) (R' := R') (M' := M') s i u a x).symm
    · intro z₁ z₂ hz₁ hz₂
      calc
        (g ∘ₗ eκ.toLinearMap) (z₁ + z₂)
            = (g ∘ₗ eκ.toLinearMap) z₁ + (g ∘ₗ eκ.toLinearMap) z₂ := by
                simp
        _ = (eκ.toLinearMap ∘ₗ f) z₁ + (eκ.toLinearMap ∘ₗ f) z₂ := by
              rw [hz₁, hz₂]
        _ = (eκ.toLinearMap ∘ₗ f) (z₁ + z₂) := by
              simp
  -- Evaluate the intertwining identity on `eκ.symm y` to isolate the conjugacy formula.
  apply LinearMap.ext
  intro y
  have hy :=
    congrArg
      (fun h :
        κ ⊗[R] s.factor i →ₗ[κ] κ' =>
          h (eκ.symm y))
      hintertwine
  simpa [eκ, f, g, LinearMap.comp_apply] using hy

/-- Helper for Lemma 15.121.2: the determinant of the base-changed scalar-multiplication map on a
simple factor is the norm of the residue class of `u`. -/
private theorem factor_baseChange_lsmul_det_eq_norm_residue
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R') :
    LinearMap.det ((Algebra.lsmul R R (s.factor i) u).baseChange κ) =
      Algebra.norm κ (IsLocalRing.residue R' u) := by
  let _ : Module R κ' := Module.compHom κ' ((IsLocalRing.residue R').comp (algebraMap R R'))
  let eκ :=
    factor_residueFieldTensor_linearEquiv (R := R) (R' := R') (M' := M') s i
  have hconj :=
    factor_residueFieldTensor_linearEquiv_conj_baseChange_lsmul
      (R := R) (R' := R') (M' := M') s i u
  -- Transport the determinant computation to the canonical owner `κ'`.
  calc
    LinearMap.det ((Algebra.lsmul R R (s.factor i) u).baseChange κ)
        = LinearMap.det (Algebra.lsmul κ κ κ' (IsLocalRing.residue R' u)) := by
            symm
            exact det_eq_of_linearEquiv_conj
              (f := (Algebra.lsmul R R (s.factor i) u).baseChange κ)
              (g := Algebra.lsmul κ κ κ' (IsLocalRing.residue R' u))
              (e := eκ)
              hconj
    _ = Algebra.norm κ (IsLocalRing.residue R' u) := by
          simpa using Algebra.norm_apply κ (IsLocalRing.residue R' u)

/-- On a simple `R'`-composition factor, the canonical finite-length determinant of multiplication
by `u` over `R` is the norm of `u mod maximalIdeal R'`. -/
private theorem factor_finiteLengthDeterminant_eq_norm_residue
    [Module.Finite κ κ']
    (s : CompositionSeries (Submodule R' M')) (i : Fin s.length) (u : R') :
    (Algebra.lsmul R R (s.factor i) u).finiteLengthDeterminant
        (factor_isFiniteLength_restrictScalars s i) =
      Algebra.norm κ (IsLocalRing.residue R' u) := by
  let htors :=
    factor_isTorsionBySet_maximalIdeal (R := R) (R' := R') (M' := M') s i
  let _ : Module κ (s.factor i) := htors.module
  let _ : Module.Finite R (s.factor i) :=
    (isFiniteLength_iff_finite_of_isTorsionBySet
      (R := R) (m := maximalIdeal R) htors).1
      (factor_isFiniteLength_restrictScalars (R := R) (R' := R') (M' := M') s i)
  let _ : Module.Finite κ (s.factor i) := Module.Finite.of_restrictScalars_finite R κ (s.factor i)
  let _ : FiniteDimensional κ (s.factor i) := FiniteDimensional.of_finite κ (s.factor i)
  have hbridge :
      (Algebra.lsmul R R (s.factor i) u).finiteLengthDeterminant
          (factor_isFiniteLength_restrictScalars (R := R) (R' := R') (M' := M') s i) =
        LinearMap.det
          (endHom_over_residueField_of_isTorsionBySet_maximalIdeal
            (R := R) (N := s.factor i) htors
            (Algebra.lsmul R R (s.factor i) u)) :=
    finiteLengthDeterminant_eq_det_of_isTorsionBySet_maximalIdeal
      (R := R) (N := s.factor i) htors
      (Algebra.lsmul R R (s.factor i) u)
      (factor_isFiniteLength_restrictScalars (R := R) (R' := R') (M' := M') s i)
  have hconj :=
    residueFieldTensor_linearEquiv_conj_descended_endomorphism
      (R := R) (N := s.factor i) htors (Algebra.lsmul R R (s.factor i) u)
  have hdet :
      LinearMap.det ((Algebra.lsmul R R (s.factor i) u).baseChange κ) =
        Algebra.norm κ (IsLocalRing.residue R' u) :=
    factor_baseChange_lsmul_det_eq_norm_residue
      (R := R) (R' := R') (M' := M') s i u
  -- First rewrite the canonical finite-length determinant through the descended `κ`-linear owner,
  -- then transport that ordinary determinant back to the tensor owner computed above.
  calc
    (Algebra.lsmul R R (s.factor i) u).finiteLengthDeterminant
        (factor_isFiniteLength_restrictScalars (R := R) (R' := R') (M' := M') s i)
      = LinearMap.det
          (endHom_over_residueField_of_isTorsionBySet_maximalIdeal
            (R := R) (N := s.factor i) htors
            (Algebra.lsmul R R (s.factor i) u)) := hbridge
    _ = LinearMap.det ((Algebra.lsmul R R (s.factor i) u).baseChange κ) := by
          exact det_eq_of_linearEquiv_conj
            (f := (Algebra.lsmul R R (s.factor i) u).baseChange κ)
            (g := endHom_over_residueField_of_isTorsionBySet_maximalIdeal
              (R := R) (N := s.factor i) htors
              (Algebra.lsmul R R (s.factor i) u))
            (e := residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
              (R := R) (N := s.factor i) htors)
            hconj
    _ = Algebra.norm κ (IsLocalRing.residue R' u) := hdet

-- Proof sketch: derive an internal composition series of the finite-length `R'`-module `M'` from
-- `isFiniteLength_iff_exists_compositionSeries`, use it to build the restricted-scalar
-- finite-length hypothesis on `M'`, and then apply multiplicativity of
-- `Module.End.finiteLengthDeterminant` along the successive short exact sequences. Each simple
-- factor contributes the same norm term by `factor_finiteLengthDeterminant_eq_norm_residue`, and
-- `Module.length_compositionSeries` identifies the number of factors with `length_{R'}(M')`.
/-- Lemma 15.121.2: for a local homomorphism `(R, 𝔪, κ) → (R', 𝔪', κ')` with finite residue-field
extension and a finite-length `R'`-module `M'`, the canonical finite-length determinant over `κ`
of multiplication by `u` on the restricted-scalar `R`-module underlying `M'` is
`Norm_{κ'/κ}(u mod 𝔪') ^ length_{R'}(M')`. -/
theorem finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length
    [Module.Finite κ κ']
    (u : R') (hM' : IsFiniteLength R' M') :
    (Algebra.lsmul R R M' u).finiteLengthDeterminant
        (isFiniteLength_restrictScalars hM') =
      Algebra.norm κ (IsLocalRing.residue R' u) ^ (Module.length R' M').toNat := by
  -- TODO: choose an `R'`-composition series of `M'`, use
  -- `Module.End.finiteLengthDeterminant_eq_mul_of_shortExact` along the successive quotient rows,
  -- and apply `factor_finiteLengthDeterminant_eq_norm_residue` to each simple factor.
  sorry

end
