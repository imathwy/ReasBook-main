import StacksProject_2024.Chap10.Lemma_10_55_1
import Mathlib.RingTheory.HopkinsLevitzki

-- Declarations for this item will be appended below by the statement pipeline.

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
