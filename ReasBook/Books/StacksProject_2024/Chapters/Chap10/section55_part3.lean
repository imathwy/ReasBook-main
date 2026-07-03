import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.HopkinsLevitzki

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_55_7 (from Chap10) -/
noncomputable section

universe u

section FiniteGrothendieckGroup

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]

/-- Helper for Lemma 10.55.7: the zero module is finitely generated. -/
private theorem isFG_zero :
    ModuleCat.isFG R (ModuleCat.of R PUnit) := by
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Lemma 10.55.7: a finite-length module is finitely generated. -/
private theorem isFG_of_isFiniteLength {M : Type u} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) :
    ModuleCat.isFG R (ModuleCat.of R M) := by
  have hNoeth : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Lemma 10.55.7: a finite module defines an object of `FGModuleCat`. -/
private theorem isFG_of_finite {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ModuleCat.isFG R (ModuleCat.of R M) := by
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Lemma 10.55.7: the residue field is finitely generated as an `R`-module. -/
private theorem isFG_residueField :
    ModuleCat.isFG R (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  have hsimple : IsSimpleModule R (IsLocalRing.ResidueField R) := by
    refine isSimpleModule_iff_quot_maximal.mpr ?_
    refine ⟨IsLocalRing.maximalIdeal R, inferInstance, ?_⟩
    refine ⟨?_⟩
    simpa [IsLocalRing.ResidueField] using
      (LinearEquiv.refl R (R ⧸ IsLocalRing.maximalIdeal R))
  have hfinite : IsFiniteLength R (IsLocalRing.ResidueField R) := by
    exact (Module.length_ne_top_iff).mp <| by
      simpa using (Module.length_eq_one_iff.mpr hsimple)
  exact isFG_of_isFiniteLength (R := R) hfinite

/-- Helper for Lemma 10.55.7: a short exact sequence gives the defining Grothendieck-group
relation. -/
private theorem modulePropertyK0_of_shortExact {P : ObjectProperty (ModuleCat R)}
    (S : ShortComplex P.FullSubcategory) (hS : (S.map P.ι).ShortExact) :
    ModulePropertyK0.of R P S.X₂ =
      ModulePropertyK0.of R P S.X₁ + ModulePropertyK0.of R P S.X₃ := by
  -- Rewrite the quotient equality as membership in the subgroup of short-exact relations.
  change
    QuotientAddGroup.mk' (modulePropertyK0Relations R P) (FreeAbelianGroup.of S.X₂) =
      QuotientAddGroup.mk' (modulePropertyK0Relations R P)
        (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨-(FreeAbelianGroup.of S.X₂ - (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)),
    ?_, by abel_nf⟩
  refine AddSubgroup.neg_mem _ ?_
  simpa [modulePropertyK0Relations, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (AddSubgroup.subset_closure <|
      Set.mem_range.2 ⟨⟨S, hS⟩, rfl⟩ :
        FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃ ∈
          modulePropertyK0Relations R P)

/-- Helper for Lemma 10.55.7: the zero object has trivial Grothendieck class. -/
private theorem modulePropertyK0_of_zero {P : ObjectProperty (ModuleCat R)}
    (h0 : P (ModuleCat.of R PUnit)) :
    ModulePropertyK0.of R P ⟨ModuleCat.of R PUnit, h0⟩ = 0 := by
  let Z : P.FullSubcategory := ⟨ModuleCat.of R PUnit, h0⟩
  let S : ShortComplex P.FullSubcategory :=
    { X₁ := Z
      X₂ := Z
      X₃ := Z
      f := 0
      g := 0
      zero := by
        apply ObjectProperty.hom_ext
        simp }
  have hS : (S.map P.ι).ShortExact := by
    -- The split exact sequence `0 → 0 → 0 → 0` yields `[0] = [0] + [0]`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro z
      constructor
      · intro hz
        refine ⟨0, ?_⟩
        cases z
        rfl
      · rintro ⟨z, hz⟩
        cases z
        rfl
    · intro z₁ z₂ hz
      cases z₁
      cases z₂
      rfl
    · intro z
      refine ⟨0, ?_⟩
      cases z
      rfl
  have hzero :
      ModulePropertyK0.of R P Z =
        ModulePropertyK0.of R P Z + ModulePropertyK0.of R P Z := by
    simpa [S, Z] using modulePropertyK0_of_shortExact (R := R) (P := P) S hS
  have hcancel' :
      -ModulePropertyK0.of R P Z + ModulePropertyK0.of R P Z =
        -ModulePropertyK0.of R P Z +
          (ModulePropertyK0.of R P Z + ModulePropertyK0.of R P Z) := by
    exact congrArg (fun t : ModulePropertyK0 R P => -ModulePropertyK0.of R P Z + t) hzero
  have hcancel : (0 : ModulePropertyK0 R P) = ModulePropertyK0.of R P Z := by
    simpa [add_assoc] using hcancel'
  -- Cancel the common summand to conclude that the zero object has zero class.
  simpa [Z] using hcancel.symm

/-- Helper for Lemma 10.55.7: isomorphic objects have the same Grothendieck class. -/
private theorem modulePropertyK0_of_iso {P : ObjectProperty (ModuleCat R)}
    (h0 : P (ModuleCat.of R PUnit)) {M N : P.FullSubcategory} (e : M ≅ N) :
    ModulePropertyK0.of R P M = ModulePropertyK0.of R P N := by
  let Z : P.FullSubcategory := ⟨ModuleCat.of R PUnit, h0⟩
  let S : ShortComplex P.FullSubcategory :=
    { X₁ := M
      X₂ := N
      X₃ := Z
      f := e.hom
      g := 0
      zero := by
        apply ObjectProperty.hom_ext
        simp }
  have hS : (S.map P.ι).ShortExact := by
    -- Package the standard exact sequence `0 → M --e--> N → 0`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro n
      constructor
      · intro _
        refine ⟨e.inv.hom n, ?_⟩
        change (e.inv.hom ≫ e.hom.hom) n = n
        rw [ObjectProperty.isoInv_hom_id_hom (P := P) e]
        rfl
      · rintro ⟨m, hm⟩
        rfl
    · intro m₁ m₂ hm
      have hm' : e.inv.hom (e.hom.hom m₁) = e.inv.hom (e.hom.hom m₂) := by
        simpa using congrArg e.inv.hom hm
      change (e.hom.hom ≫ e.inv.hom) m₁ = (e.hom.hom ≫ e.inv.hom) m₂ at hm'
      rw [ObjectProperty.isoHom_inv_id_hom (P := P) e] at hm'
      simpa using hm'
    · intro z
      refine ⟨0, ?_⟩
      cases z
      rfl
  -- The short exact relation for `0 → M → N → 0` reduces to `[N] = [M]`.
  simpa [S, Z, modulePropertyK0_of_zero (R := R) (P := P) h0] using
    (modulePropertyK0_of_shortExact (R := R) (P := P) S hS).symm

/-- Helper for Lemma 10.55.7: the class of a finite module is the sum of the class of a
submodule and the class of its quotient. -/
private theorem finiteGrothendieckGroupOf_eq_submodule_add_quotient
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R M) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R N) +
        finiteGrothendieckGroupOf R (FGModuleCat.of R (M ⧸ N)) := by
  let S : ShortComplex (FGModuleCat R) :=
    { X₁ := FGModuleCat.of R N
      X₂ := FGModuleCat.of R M
      X₃ := FGModuleCat.of R (M ⧸ N)
      f := FGModuleCat.ofHom N.subtype
      g := FGModuleCat.ofHom N.mkQ
      zero := by
        ext x
        change N.mkQ (N.subtype x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact x.2 }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
    -- Package `0 → N → M → M ⧸ N → 0` as a short exact sequence in `ModuleCat`.
    refine ModuleCat.shortComplex_shortExact (S.map (ModuleCat.isFG R).ι)
      (LinearMap.exact_subtype_mkQ N) Subtype.val_injective (Submodule.mkQ_surjective N)
  -- Apply the defining Grothendieck relation to this short exact sequence.
  simpa [finiteGrothendieckGroupOf, S] using
    modulePropertyK0_of_shortExact (R := R) (P := ModuleCat.isFG R) S hS

/-- Helper for Lemma 10.55.7: every simple finite module over an Artinian local ring has the same
Grothendieck class as the residue field. -/
private theorem simple_module_class_eq_residue_field_class
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsSimpleModule R M] :
    finiteGrothendieckGroupOf R (FGModuleCat.of R M) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
  obtain ⟨I, hImax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R M)
  have hI : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hImax
  subst hI
  -- Replace the simple module by the quotient by the unique maximal ideal.
  simpa [finiteGrothendieckGroupOf, IsLocalRing.ResidueField] using
    modulePropertyK0_of_iso (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))
      (e.toFGModuleCatIso)

/-- Helper for Lemma 10.55.7: pulling a submodule back along the inclusion of a larger submodule
does not change its Grothendieck class. -/
private theorem submodule_comap_class_eq
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (A B : Submodule R M) (hAB : A ≤ B) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (Submodule.comap B.subtype A)) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R A) := by
  let e₀ := (Submodule.comap B.subtype A).equivMapOfInjective
    B.subtype (Submodule.injective_subtype _)
  have hmap : (Submodule.comap B.subtype A).map B.subtype = A := by
    -- Mapping the pulled-back submodule back into `M` recovers the original smaller stage.
    rw [Submodule.map_comap_subtype, inf_of_le_right hAB]
  let e : Submodule.comap B.subtype A ≃ₗ[R] A := e₀.trans <| LinearEquiv.ofEq _ _ hmap
  -- Grothendieck classes are invariant under the canonical identification of these submodules.
  simpa [finiteGrothendieckGroupOf] using
    modulePropertyK0_of_iso (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))
      e.toFGModuleCatIso

/-- Helper for Lemma 10.55.7: the bottom submodule contributes the zero Grothendieck class. -/
private theorem bot_submodule_class_eq_zero
    {M : FGModuleCat R} :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (⊥ : Submodule R M.obj)) = 0 := by
  -- Identify the bottom submodule with the zero module and use the defining zero relation.
  calc
    finiteGrothendieckGroupOf R (FGModuleCat.of R (⊥ : Submodule R M.obj)) =
        ModulePropertyK0.of R (ModuleCat.isFG R)
          ⟨ModuleCat.of R PUnit, isFG_zero (R := R)⟩ := by
      simpa [finiteGrothendieckGroupOf] using
        modulePropertyK0_of_iso (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))
          (Submodule.botEquivPUnit.toFGModuleCatIso)
    _ = 0 := modulePropertyK0_of_zero (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))

/-- Helper for Lemma 10.55.7: the top submodule has the same Grothendieck class as the ambient
module. -/
private theorem top_submodule_class_eq
    (M : FGModuleCat R) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (⊤ : Submodule R M.obj)) =
      finiteGrothendieckGroupOf R M := by
  -- The top submodule is canonically linearly equivalent to the ambient module.
  simpa [finiteGrothendieckGroupOf] using
    modulePropertyK0_of_iso (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))
      ((Submodule.topEquiv : (⊤ : Submodule R M.obj) ≃ₗ[R] M.obj).toFGModuleCatIso)

/-- Helper for Lemma 10.55.7: each stage of a composition series contributes one residue-field
class in the finite Grothendieck group. -/
private theorem composition_series_index_class_eq_zsmul_residue_field_class
    (M : FGModuleCat R) (s : CompositionSeries (Submodule R M.obj)) (hs0 : s.head = ⊥)
    (i : Fin (s.length + 1)) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (s i)) =
      ((i : ℕ) : ℤ) •
        finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
  let η : finiteGrothendieckGroup R :=
    finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R))
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ s.length,
        finiteGrothendieckGroupOf R
            (FGModuleCat.of R (s ⟨n, Nat.lt_succ_of_le hn⟩)) =
          (n : ℤ) • η := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hsZero : s ⟨0, Nat.lt_succ_of_le hn⟩ = ⊥ := by
          simpa using hs0
        -- The composition series starts at the zero submodule.
        rw [hsZero]
        simpa [η] using (bot_submodule_class_eq_zero (R := R) (M := M))
    | succ n ih =>
        intro hn
        let j : Fin s.length := ⟨n, Nat.lt_of_succ_le hn⟩
        let N : Submodule R (s j.succ) := Submodule.comap (s j.succ).subtype (s j.castSucc)
        have hquotSimple : IsSimpleModule R (s j.succ ⧸ N) := by
          -- The successive quotient attached to a cover in a composition series is simple.
          simpa [N] using
            (covBy_iff_quot_is_simple (CovBy.le (s.step j))).mp (s.step j)
        have hdecomp :
            finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.succ)) =
              finiteGrothendieckGroupOf R (FGModuleCat.of R N) +
                finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.succ ⧸ N)) := by
          -- Apply the Grothendieck relation to the short exact sequence
          -- `0 → N → s j.succ → (s j.succ) ⧸ N → 0`.
          simpa [N] using
            finiteGrothendieckGroupOf_eq_submodule_add_quotient (R := R) (M := s j.succ) N
        have hpred :
            finiteGrothendieckGroupOf R (FGModuleCat.of R N) =
              finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.castSucc)) := by
          -- The pulled-back predecessor is canonically the predecessor itself.
          simpa [N] using
            submodule_comap_class_eq (R := R) (A := s j.castSucc) (B := s j.succ)
              (CovBy.le (s.step j))
        have hquot :
            finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.succ ⧸ N)) = η := by
          -- Over a local ring every simple factor has the residue-field class.
          let _ : IsSimpleModule R (s j.succ ⧸ N) := hquotSimple
          simpa [η, N] using
            simple_module_class_eq_residue_field_class (R := R) (M := s j.succ ⧸ N)
        calc
          finiteGrothendieckGroupOf R
              (FGModuleCat.of R (s ⟨n.succ, Nat.lt_succ_of_le hn⟩)) =
              finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.succ)) := by
            rfl
          _ = finiteGrothendieckGroupOf R (FGModuleCat.of R N) +
                finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.succ ⧸ N)) := hdecomp
          _ = finiteGrothendieckGroupOf R (FGModuleCat.of R (s j.castSucc)) + η := by
            rw [hpred, hquot]
          _ = (n : ℤ) • η + η := by
            simpa [j, η] using ih (Nat.le_of_succ_le hn)
          _ = (n.succ : ℤ) • η := by
            simpa [one_zsmul] using (add_zsmul η (n : ℤ) 1).symm
  -- Specialize the nat-indexed prefix statement to the requested stage.
  simpa [η] using hprefix i.1 (Nat.le_of_lt_succ i.2)

/-- Helper for Lemma 10.55.7: the Grothendieck class of a finite module is its length times the
residue-field class. -/
private theorem finite_module_class_eq_length_zsmul_residue_field_class
    (M : FGModuleCat R) :
    finiteGrothendieckGroupOf R M =
      ((Module.length R M.obj).toNat : ℤ) •
        finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
  -- Route correction: stay inside one ambient finitely generated module and read off the class
  -- from a composition series of submodules, rather than recursing through changing carriers.
  have hFiniteLength : IsFiniteLength R M := by
    exact (Module.length_ne_top_iff).mp (Module.length_ne_top (R := R) (M := M))
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hFiniteLength
  have hlast : s (Fin.last s.length) = (⊤ : Submodule R M.obj) := by
    simpa using hs1
  have hstage :
      finiteGrothendieckGroupOf R (FGModuleCat.of R (s (Fin.last s.length))) =
        (s.length : ℤ) •
          finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
    exact composition_series_index_class_eq_zsmul_residue_field_class (R := R) (M := M) s hs0
      (Fin.last s.length)
  have hlastClass :
      finiteGrothendieckGroupOf R (FGModuleCat.of R (s (Fin.last s.length))) =
        finiteGrothendieckGroupOf R (FGModuleCat.of R (⊤ : Submodule R M.obj)) := by
    -- Replace the last stage by the top submodule via the canonical equality-induced isomorphism.
    simpa [finiteGrothendieckGroupOf] using
      modulePropertyK0_of_iso (R := R) (P := ModuleCat.isFG R) (isFG_zero (R := R))
        ((LinearEquiv.ofEq _ _ hlast).toFGModuleCatIso)
  have htop :
      finiteGrothendieckGroupOf R (FGModuleCat.of R (⊤ : Submodule R M.obj)) =
        (s.length : ℤ) •
          finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
    -- The last stage of the composition series is the whole module.
    calc
      finiteGrothendieckGroupOf R (FGModuleCat.of R (⊤ : Submodule R M.obj)) =
          finiteGrothendieckGroupOf R (FGModuleCat.of R (s (Fin.last s.length))) := by
        simpa using hlastClass.symm
      _ = (s.length : ℤ) •
            finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := hstage
  have hlengthNat : s.length = (Module.length R M.obj).toNat := by
    -- Convert the canonical length formula for a composition series to a natural-number identity.
    simpa using congrArg ENat.toNat (Module.length_compositionSeries (R := R) s hs0 hs1)
  calc
    finiteGrothendieckGroupOf R M =
        finiteGrothendieckGroupOf R (FGModuleCat.of R (⊤ : Submodule R M.obj)) := by
      simpa using (top_submodule_class_eq (R := R) M).symm
    _ = (s.length : ℤ) •
          finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := htop
    _ = ((Module.length R M.obj).toNat : ℤ) •
          finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R)) := by
      rw [hlengthNat]

/-- Helper for Lemma 10.55.7: the length map sends the residue-field class to `1`. -/
private theorem lengthMap_residue_field_class_eq_one :
    finiteGrothendieckGroup_lengthMap R
        (finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R))) = 1 := by
  -- Evaluate the length map on the distinguished residue-field generator.
  have hsimple : IsSimpleModule R (IsLocalRing.ResidueField R) := by
    refine isSimpleModule_iff_quot_maximal.mpr ?_
    refine ⟨IsLocalRing.maximalIdeal R, inferInstance, ?_⟩
    refine ⟨?_⟩
    simpa [IsLocalRing.ResidueField] using
      (LinearEquiv.refl R (R ⧸ IsLocalRing.maximalIdeal R))
  rw [finiteGrothendieckGroup_lengthMap_apply_of]
  simpa using (Module.length_eq_one_iff.mpr hsimple)

-- Proof sketch: let `k = R ⧸ maximalIdeal R`. Every finite `R`-module has finite length, so its
-- class in `K'_0(R)` is the sum of the classes of the successive simple quotients in a composition
-- series. Since `R` is local, each simple quotient is isomorphic to `k`, so `K'_0(R)` is
-- generated by `[k]`; injectivity follows because the length map sends `[k]` to `1`.
/-- Lemma 10.55.7 (1): for an Artinian local ring `R`, the length homomorphism on `K'_0(R)` is
bijective. -/
theorem finiteGrothendieckGroup_lengthMap_bijective :
    Function.Bijective
      ((finiteGrothendieckGroup_lengthMap R) : finiteGrothendieckGroup.{u, u} R → ℤ) := by
  let η : finiteGrothendieckGroup R :=
    finiteGrothendieckGroupOf R (FGModuleCat.of R (IsLocalRing.ResidueField R))
  let σ : ℤ →+ finiteGrothendieckGroup R := zmultiplesHom _ η
  have hright :
      (finiteGrothendieckGroup_lengthMap R).comp σ = AddMonoidHom.id ℤ := by
    apply AddMonoidHom.ext_int
    -- The candidate section sends `1` to the residue-field class, whose length is `1`.
    calc
      ((finiteGrothendieckGroup_lengthMap R).comp σ) 1 =
          finiteGrothendieckGroup_lengthMap R η := by
        simp [AddMonoidHom.comp_apply, σ]
      _ = 1 := by
        simpa [η] using lengthMap_residue_field_class_eq_one (R := R)
  have hleft :
      σ.comp (finiteGrothendieckGroup_lengthMap R) =
        AddMonoidHom.id (finiteGrothendieckGroup R) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro M
    -- Every generator class is determined by its module length and the residue-field class.
    calc
      (σ.comp (finiteGrothendieckGroup_lengthMap R))
          (finiteGrothendieckGroupOf R M) =
          σ ((Module.length R M.obj).toNat : ℤ) := by
        rw [AddMonoidHom.comp_apply, finiteGrothendieckGroup_lengthMap_apply_of]
      _ = ((Module.length R M.obj).toNat : ℤ) • η := by
        simp [σ]
      _ = finiteGrothendieckGroupOf R M := by
        symm
        simpa [η] using finite_module_class_eq_length_zsmul_residue_field_class (R := R) M
  have hrightInv :
      Function.RightInverse σ
        ((finiteGrothendieckGroup_lengthMap R) : finiteGrothendieckGroup.{u, u} R → ℤ) := by
    intro z
    exact DFunLike.congr_fun hright z
  have hleftInv :
      Function.LeftInverse σ
        ((finiteGrothendieckGroup_lengthMap R) : finiteGrothendieckGroup.{u, u} R → ℤ) := by
    intro x
    exact DFunLike.congr_fun hleft x
  have hf :
      Function.Bijective
        ((finiteGrothendieckGroup_lengthMap R) : finiteGrothendieckGroup.{u, u} R → ℤ) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hσxy :
          σ ((finiteGrothendieckGroup_lengthMap R) x) =
            σ ((finiteGrothendieckGroup_lengthMap R) y) := by
        simpa using congrArg σ hxy
      calc
        x = σ ((finiteGrothendieckGroup_lengthMap R) x) := by
          symm
          exact hleftInv x
        _ = σ ((finiteGrothendieckGroup_lengthMap R) y) := hσxy
        _ = y := hleftInv y
    · intro z
      exact ⟨σ z, hrightInv z⟩
  exact hf

/-- Lemma 10.55.7 (2): for an Artinian local ring `R`, the length map identifies `K'_0(R)` with
`ℤ`. -/
noncomputable def finiteGrothendieckGroup_lengthEquiv :
    finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (finiteGrothendieckGroup_lengthMap R)
    (finiteGrothendieckGroup_lengthMap_bijective R)

-- Proof sketch: `finiteGrothendieckGroup_lengthEquiv` is defined by `AddEquiv.ofBijective` from
-- the length homomorphism, so its underlying function is exactly `finiteGrothendieckGroup_lengthMap`.
/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the canonical length map. -/
theorem finiteGrothendieckGroup_lengthEquiv_apply
    (x : finiteGrothendieckGroup R) :
    finiteGrothendieckGroup_lengthEquiv R x =
      finiteGrothendieckGroup_lengthMap R x := by
  -- This equivalence is defined from the length map, so it acts by that map.
  rfl

end FiniteGrothendieckGroup

/-! ### Lemma_10_55_8 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

universe u v

section ProjectiveGrothendieckGroup

variable (R : Type u) [CommRing R]

variable [IsLocalRing R]

/-- Helper for Lemma 10.55.8: the finite projective subcategory in the same universe as `R`. -/
private abbrev finite_projective_module_cat_same_universe :=
  FiniteProjectiveModuleCat.{u, u} R

/-- Helper for Lemma 10.55.8: the Grothendieck group of same-universe finite projective modules.
-/
private abbrev projective_grothendieck_group_same_universe :=
  projectiveGrothendieckGroup.{u, u} R

/-- The integer-valued rank of a finitely generated projective `R`-module. -/
private abbrev projectiveGrothendieckGroup_rank (M : FiniteProjectiveModuleCat R) : ℤ :=
  (Module.finrank R M.obj : ℤ)

-- Proof sketch: projective modules are flat, and `Module.free_of_flat_of_isLocalRing` upgrades a
-- finite flat module over a local ring to a free module.
/-- Lemma 10.55.8 (1): every finite projective module over a local ring is free. -/
theorem finite_projective_module_free_of_isLocalRing
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Free R M := by
  -- Projective modules are flat, and finite flat modules over a local ring are free.
  let _ : Module.Flat R M := inferInstance
  exact Module.free_of_flat_of_isLocalRing

-- Proof sketch: apply `Module.free_of_flat_of_isLocalRing` to identify the terms of the short
-- exact sequence with finite free modules, then use additivity of `Module.finrank` on split short
-- exact sequences.
/-- Rank is additive on short exact sequences of finitely generated projective modules. -/
private theorem projectiveGrothendieckGroup_rank_respects_shortExact
    (S : ShortComplex (FiniteProjectiveModuleCat R))
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    projectiveGrothendieckGroup_rank R S.X₂ =
      projectiveGrothendieckGroup_rank R S.X₁ + projectiveGrothendieckGroup_rank R S.X₃ := by
  let T : ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  have hT : T.ShortExact := by
    simpa [T] using hS
  let _ : Module.Finite R T.X₁ := by
    simpa [T] using (inferInstance : Module.Finite R S.X₁.obj)
  let _ : Module.Finite R T.X₃ := by
    simpa [T] using (inferInstance : Module.Finite R S.X₃.obj)
  let _ : Module.Projective R T.X₁ := by
    simpa [T] using (inferInstance : Module.Projective R S.X₁.obj)
  let _ : Module.Projective R T.X₃ := by
    simpa [T] using (inferInstance : Module.Projective R S.X₃.obj)
  let _ : Module.Free R T.X₁ := finite_projective_module_free_of_isLocalRing (R := R)
  let _ : Module.Free R T.X₃ := finite_projective_module_free_of_isLocalRing (R := R)
  have hfinrank :
      Module.finrank R T.X₂ = Module.finrank R T.X₁ + Module.finrank R T.X₃ := by
    simpa [T] using
      (ModuleCat.free_shortExact_finrank_add (R := R) (S := T) hT rfl rfl)
  -- Cast the finite-rank equality from `ℕ` to `ℤ` to match the generator-level invariant.
  simpa [projectiveGrothendieckGroup_rank, T, Nat.cast_add] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfinrank

-- Proof sketch: a generator of `modulePropertyK0Relations` comes from a short exact sequence of
-- finite projective modules, and `projectiveGrothendieckGroup_rank_respects_shortExact` sends the
-- corresponding Grothendieck relation to zero. Closure gives the kernel inclusion.
/-- The Grothendieck relations for finite projective modules lie in the kernel of rank. -/
private theorem projectiveGrothendieckGroup_relations_le_ker_rank :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (projectiveGrothendieckGroup_rank R)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (projectiveGrothendieckGroup_rank R)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  have hrank :
      projectiveGrothendieckGroup_rank R S.X₂ =
        projectiveGrothendieckGroup_rank R S.X₁ + projectiveGrothendieckGroup_rank R S.X₃ :=
    projectiveGrothendieckGroup_rank_respects_shortExact (R := R) S hS
  -- Rewrite by rank additivity and normalize the resulting integer identity.
  rw [hrank]
  abel

/-- Lemma 10.55.8 (2): the rank function on finitely generated projective `R`-modules descends to
a well-defined homomorphism `K₀(R) → ℤ`. -/
def projectiveGrothendieckGroup_rankMap :
    projectiveGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (projectiveGrothendieckGroup_rank R)
    (projectiveGrothendieckGroup_relations_le_ker_rank R)

-- Proof sketch: `projectiveGrothendieckGroup_rankMap` is the canonical `ModulePropertyK0.lift` of
-- `projectiveGrothendieckGroup_rank`, so on a generator class it evaluates to the rank of that
-- finite projective module.
/-- The rank map sends the class of a finite projective module to its rank. -/
theorem projectiveGrothendieckGroup_rankMap_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_rankMap R
        (projectiveGrothendieckGroupOf R M) =
      (Module.finrank R M.obj : ℤ) := by
  -- The descended map agrees with the original generator-level rank functional.
  simpa [projectiveGrothendieckGroup_rank] using
    ModulePropertyK0.lift_of R
      (projectiveGrothendieckGroup_rank R)
      (projectiveGrothendieckGroup_relations_le_ker_rank R)
      M

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the zero module is finitely generated and projective. -/
private theorem finite_projective_module_property_zero :
    finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
  exact ⟨inferInstance, inferInstance⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the direct product of two finitely generated projective modules is
again finitely generated and projective. -/
private theorem finite_projective_module_property_prod
    (M N : ModuleCat R)
    (hM : finiteProjectiveModuleProperty R M)
    (hN : finiteProjectiveModuleProperty R N) :
    finiteProjectiveModuleProperty R (ModuleCat.of R (M × N)) := by
  let _ : Module.Finite R M := hM.1
  let _ : Module.Projective R M := hM.2
  let _ : Module.Finite R N := hN.1
  let _ : Module.Projective R N := hN.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 10.55.8: the rank-one free module as an object of the finite projective
subcategory. -/
private abbrev rank_one_finite_projective_module :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R R, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 10.55.8: the standard free module of rank `n` as an object of the finite
projective subcategory. -/
private abbrev standard_free_finite_projective_module (n : ℕ) :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R (Fin n → R), ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 10.55.8: the direct product of two finite projective modules as an object of
the finite projective subcategory. -/
private abbrev prod_finite_projective_module
    (M N : finite_projective_module_cat_same_universe (R := R)) :
    finite_projective_module_cat_same_universe (R := R) :=
  ⟨ModuleCat.of R (M.obj × N.obj),
    finite_projective_module_property_prod (R := R) M.obj N.obj M.property N.property⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the rank-zero standard free module has trivial Grothendieck class. -/
private theorem standard_free_zero_class_eq_zero :
    projectiveGrothendieckGroupOf R
      (standard_free_finite_projective_module (R := R) 0) = 0 := by
  haveI : Subsingleton (Fin 0 → R) := inferInstance
  -- The rank-zero free module is subsingleton, so its class agrees with the zero object.
  simpa using
    (ModulePropertyK0.of_subsingleton (R := R) (P := finiteProjectiveModuleProperty R)
      (finite_projective_module_property_zero (R := R))
      (standard_free_finite_projective_module (R := R) 0))

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: `R ⊕ R^n` is canonically the standard free module of rank `n + 1`.
-/
private def standard_free_succ_iso_prod (n : ℕ) :
    prod_finite_projective_module (R := R)
      (rank_one_finite_projective_module (R := R))
      (standard_free_finite_projective_module (R := R) n) ≅
        standard_free_finite_projective_module (R := R) n.succ :=
  ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
    (LinearEquiv.toModuleIso (Fin.consLinearEquiv R (fun _ : Fin n.succ ↦ R)))

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the Grothendieck class of a product of finite projective modules is
the sum of the classes of its two factors. -/
private theorem projectiveGrothendieckGroupOf_prod
    (M N : finite_projective_module_cat_same_universe (R := R)) :
    projectiveGrothendieckGroupOf R (prod_finite_projective_module (R := R) M N) =
      projectiveGrothendieckGroupOf R M + projectiveGrothendieckGroupOf R N := by
  let P := finiteProjectiveModuleProperty R
  let S : ShortComplex P.FullSubcategory :=
    { X₁ := M
      X₂ := prod_finite_projective_module (R := R) M N
      X₃ := N
      f := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl R M.obj N.obj))
      g := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd R M.obj N.obj))
      zero := by
        apply ObjectProperty.hom_ext
        ext x
        rfl }
  let T : ShortComplex (ModuleCat R) :=
    { X₁ := M.obj
      X₂ := ModuleCat.of R (M.obj × N.obj)
      X₃ := N.obj
      f := ModuleCat.ofHom (LinearMap.inl R M.obj N.obj)
      g := ModuleCat.ofHom (LinearMap.snd R M.obj N.obj)
      zero := by
        ext x
        rfl }
  have hT : T.ShortExact := by
    -- The standard split sequence `0 → M → M × N → N → 0` is short exact in `ModuleCat`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        ext
        · rfl
        · simpa using hx.symm
      · rintro ⟨m, rfl⟩
        rfl
    · intro m m' hmm'
      exact congrArg Prod.fst hmm'
    · intro n
      refine ⟨(0, n), ?_⟩
      rfl
  have hS : (S.map P.ι).ShortExact := by
    -- Forgetting the full-subcategory structure recovers the split short exact sequence above.
    simpa [S, T, prod_finite_projective_module] using hT
  -- Apply the defining short exact sequence relation in `K₀(R)`.
  simpa [S, prod_finite_projective_module] using
    ModulePropertyK0.of_shortExact (R := R) (P := P) S hS

omit [IsLocalRing R] in
/-- Helper for Lemma 10.55.8: the class of the standard free module of rank `n` is `n` times the
class of the rank-one free module. -/
private theorem free_fin_class_eq_zsmul_rank_one (n : ℕ) :
    projectiveGrothendieckGroupOf R
      ((standard_free_finite_projective_module (R := R) n :
        finite_projective_module_cat_same_universe (R := R))) =
        n •
          (projectiveGrothendieckGroupOf R
            ((rank_one_finite_projective_module (R := R) :
              finite_projective_module_cat_same_universe (R := R))) :
            projective_grothendieck_group_same_universe (R := R)) := by
  -- Route correction: follow the source proof via the split sequence
  -- `0 → R → R ⊕ R^n → R^n → 0`, rather than hiding the successor step in ad hoc rewriting.
  let η : projective_grothendieck_group_same_universe (R := R) :=
    projectiveGrothendieckGroupOf R
      ((rank_one_finite_projective_module (R := R) :
        finite_projective_module_cat_same_universe (R := R)))
  induction n with
  | zero =>
      -- Start the recursion with the trivial class of the zero free module.
      simpa [η] using standard_free_zero_class_eq_zero (R := R)
  | succ n ih =>
      have hcons :
          projectiveGrothendieckGroupOf R
              ((prod_finite_projective_module (R := R)
                (rank_one_finite_projective_module (R := R))
                (standard_free_finite_projective_module (R := R) n) :
                  finite_projective_module_cat_same_universe (R := R))) =
            projectiveGrothendieckGroupOf R
              ((standard_free_finite_projective_module (R := R) n.succ :
                finite_projective_module_cat_same_universe (R := R))) := by
        -- Transport the product decomposition across the canonical free-module isomorphism.
        exact ModulePropertyK0.of_iso (R := R) (P := finiteProjectiveModuleProperty R)
          (finite_projective_module_property_zero (R := R))
          (standard_free_succ_iso_prod (R := R) n)
      calc
        projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) n.succ :
              finite_projective_module_cat_same_universe (R := R))) =
            projectiveGrothendieckGroupOf R
              ((prod_finite_projective_module (R := R)
                (rank_one_finite_projective_module (R := R))
                (standard_free_finite_projective_module (R := R) n) :
                  finite_projective_module_cat_same_universe (R := R))) := by
          simpa using hcons.symm
        _ = projectiveGrothendieckGroupOf R
              ((rank_one_finite_projective_module (R := R) :
                finite_projective_module_cat_same_universe (R := R))) +
              projectiveGrothendieckGroupOf R
                ((standard_free_finite_projective_module (R := R) n :
                  finite_projective_module_cat_same_universe (R := R))) := by
          exact projectiveGrothendieckGroupOf_prod (R := R)
            ((rank_one_finite_projective_module (R := R) :
              finite_projective_module_cat_same_universe (R := R)))
            ((standard_free_finite_projective_module (R := R) n :
              finite_projective_module_cat_same_universe (R := R)))
        _ = η + (n : ℤ) • η := by
          simpa [η, natCast_zsmul] using congrArg
            (fun x : projective_grothendieck_group_same_universe (R := R) ↦ η + x) ih
        _ = n.succ • η := by
          rw [succ_nsmul, natCast_zsmul, add_comm]

-- Proof sketch: surjectivity comes from the rank-one free module. Injectivity follows because
-- `finite_projective_module_free_of_isLocalRing` identifies every finite projective module with a
-- finite free module, so its `K₀`-class is determined by its rank.
/-- Lemma 10.55.8 (3): for a local ring, the rank map identifies `K₀(R)` with `ℤ`. -/
theorem projectiveGrothendieckGroup_rankMap_bijective :
    Function.Bijective (projectiveGrothendieckGroup_rankMap.{u, u} R) := by
  let η : projective_grothendieck_group_same_universe (R := R) :=
    projectiveGrothendieckGroupOf R
      ((rank_one_finite_projective_module (R := R) :
        finite_projective_module_cat_same_universe (R := R)))
  let σ : ℤ →+ projective_grothendieck_group_same_universe (R := R) := zmultiplesHom _ η
  have hright :
      (projectiveGrothendieckGroup_rankMap R).comp σ = AddMonoidHom.id ℤ := by
    apply AddMonoidHom.ext_int
    -- On `1`, the inverse candidate picks the class of the rank-one free module.
    simpa [AddMonoidHom.comp_apply, σ, η] using
      (projectiveGrothendieckGroup_rankMap_apply_of (R := R)
        (rank_one_finite_projective_module (R := R)))
  have hleft :
      σ.comp (projectiveGrothendieckGroup_rankMap R) =
        AddMonoidHom.id (projective_grothendieck_group_same_universe (R := R)) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro M
    let _ : Module.Free R M.obj := finite_projective_module_free_of_isLocalRing (R := R)
    let e : M.obj ≃ₗ[R] (Fin (Module.finrank R M.obj) → R) :=
      LinearEquiv.ofFinrankEq (R := R) M.obj (Fin (Module.finrank R M.obj) → R) (by simp)
    have hclass :
        projectiveGrothendieckGroupOf R M =
          projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) (Module.finrank R M.obj) :
              finite_projective_module_cat_same_universe (R := R))) := by
      -- Every finite projective module over a local ring is isomorphic to a standard free module
      -- of the same rank.
      exact ModulePropertyK0.of_iso (R := R) (P := finiteProjectiveModuleProperty R)
        (finite_projective_module_property_zero (R := R))
        (ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
          (LinearEquiv.toModuleIso e))
    calc
      (σ.comp (projectiveGrothendieckGroup_rankMap R))
          (projectiveGrothendieckGroupOf R M) =
          σ (Module.finrank R M.obj : ℤ) := by
        rw [AddMonoidHom.comp_apply, projectiveGrothendieckGroup_rankMap_apply_of]
      _ = (Module.finrank R M.obj : ℤ) • η := by
        simp [σ]
      _ = projectiveGrothendieckGroupOf R
            ((standard_free_finite_projective_module (R := R) (Module.finrank R M.obj) :
              finite_projective_module_cat_same_universe (R := R))) := by
        symm
        simpa [η, natCast_zsmul] using
          (free_fin_class_eq_zsmul_rank_one (R := R) (Module.finrank R M.obj))
      _ = projectiveGrothendieckGroupOf R M := by
        simpa using hclass.symm
  constructor
  · intro x y hxy
    have hx : σ (projectiveGrothendieckGroup_rankMap R x) = x := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft x
    have hy : σ (projectiveGrothendieckGroup_rankMap R y) = y := by
      simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hleft y
    rw [← hx, ← hy, hxy]
  · intro z
    refine ⟨σ z, ?_⟩
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hright z

end ProjectiveGrothendieckGroup

/-! ### Lemma_10_55_9 (from Chap10) -/
noncomputable section

universe u v

section Comparison

variable (R : Type u) [CommRing R]

/-- Helper for Lemma 10.55.9: a finite projective module over a local Artinian ring has length
equal to its rank times the length of the ring. -/
private theorem finiteProjective_length_eq_rank_mul_ring_length [IsArtinianRing R]
    [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ((Module.length R M).toNat : ℤ) =
      ((Module.length R R).toNat : ℤ) * Module.finrank R M := by
  -- Use Lemma 10.55.8 to replace the finite projective module by a finite free module.
  let _ : Module.Free R M := finite_projective_module_free_of_isLocalRing (R := R)
  -- Convert the `ℕ∞`-valued free-length formula into the integer-valued statement used here.
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_of_free_of_finite R M)

/-- Helper for Lemma 10.55.9: the left composite of the comparison square sends a generator of
`K₀(R)` to the length of the underlying finite module. -/
private theorem comparison_length_on_generator [IsArtinianRing R]
    (M : FiniteProjectiveModuleCat R) :
    ((finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)))
      (projectiveGrothendieckGroupOf R M) =
        ((Module.length R M.obj).toNat : ℤ) := by
  -- The comparison map preserves generator classes, and the inclusion into finitely generated
  -- modules does not change the underlying module whose length is measured.
  rw [AddMonoidHom.comp_apply, ModulePropertyK0.map_of, finiteGrothendieckGroup_lengthMap_apply_of]
  rfl

/-- Helper for Lemma 10.55.9: the right composite of the comparison square sends a generator of
`K₀(R)` to `length_R(R)` times the rank of that generator. -/
private theorem comparison_rank_on_generator [IsArtinianRing R] [IsLocalRing R]
    (M : FiniteProjectiveModuleCat R) :
    ((AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R))
      (projectiveGrothendieckGroupOf R M) =
        ((Module.length R R).toNat : ℤ) * Module.finrank R M.obj := by
  -- The rank map evaluates on a generator by the rank of the corresponding projective module.
  rw [AddMonoidHom.comp_apply, projectiveGrothendieckGroup_rankMap_apply_of]
  rfl

/-- Lemma 10.55.9: for a local Artinian ring `R`, the canonical comparison map `K₀(R) → K'_0(R)`
fits into the commutative square with vertical maps `rank_R` and `length_R`, where the lower
horizontal map is multiplication by `length_R(R)`. -/
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length
    [IsArtinianRing R] [IsLocalRing R] :
    (finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)) =
      (AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro M
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  -- Both composites are determined on generator classes, and the source proof reduces exactly to
  -- the free-module length computation from the previous helper.
  calc
    ((finiteGrothendieckGroup_lengthMap R).comp
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)))
        (projectiveGrothendieckGroupOf R M) =
          ((Module.length R M.obj).toNat : ℤ) := by
      exact comparison_length_on_generator (R := R) M
    _ = ((Module.length R R).toNat : ℤ) * Module.finrank R M.obj := by
      exact finiteProjective_length_eq_rank_mul_ring_length (R := R) M.obj
    _ = ((AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (projectiveGrothendieckGroup_rankMap R))
        (projectiveGrothendieckGroupOf R M) := by
      simpa using (comparison_rank_on_generator (R := R) M).symm

/-- On an element of `K₀(R)`, Lemma 10.55.9 says that taking length after comparison to `K'_0(R)`
agrees with multiplying rank by `length_R(R)`. -/
@[simp]
theorem projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply
    [IsArtinianRing R] [IsLocalRing R] (x : projectiveGrothendieckGroup R) :
    finiteGrothendieckGroup_lengthMap R
        (ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R) x) =
      ((Module.length R R).toNat : ℤ) * projectiveGrothendieckGroup_rankMap R x := by
  -- Evaluate the homomorphism identity from Lemma 10.55.9 at the chosen class `x`.
  simpa using DFunLike.congr_fun
    (projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length R) x

end Comparison
