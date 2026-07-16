import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_3
import stacks_proof.stacks_project.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

noncomputable section

namespace RingPairCat

section

/- Domain-style sampling for Lemma 15.12.4:
- primary domain: henselization of ring pairs and the canonical comparison from henselization to
  adic completion in Noetherian commutative algebra;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.toHenselization`,
  `RingPairCat.henselizationRing`,
  `AdicCompletion.map`;
- best owner abstraction: the source-facing map to adic completion is derived from the canonical
  pair-henselization adjunction of Lemma `15.12.1`, not from any new local wrapper or additional
  public adjunction data;
- primitive data: a ring pair `X` and the Noetherian hypothesis on `X.ring`;
- derived API: the comparison map `A^h → A^∧` and the flatness / faithful-flatness statements
  attached to it.

Source/core/bridge triage:
- `source-facing`: the canonical map from the henselization of `(A, I)` to its `I`-adic
  completion and its properties in Lemma `15.12.4`;
- `core/canonical`: the adjunction owner `henselianPairInclusion` from Lemma `15.12.1`;
- `bridge/view`: the comparison morphism obtained by applying the adjunction universal property to
  the henselian completion pair. -/

variable (X : RingPairCat.{u})
variable [IsNoetherianRing X.ring]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: both composites are induced by the same ring map `X.ring → AdicCompletion X.ideal
-- X.ring`, and the lower horizontal arrow is exactly the quotient map obtained from that ring map
-- by functoriality of quotients.
omit [IsNoetherianRing X.ring] in
/-- The quotient square defining the canonical morphism from `X` to its adic completion pair. -/
private lemma toAdicCompletionPair_w :
    CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)) ≫
        CommRingCat.ofHom
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map) := by
  -- Proof comment: this is exactly the canonical quotient square for the algebra map from `A`
  -- to its adic completion, with target ideal the extended ideal `IA^∧`.
  simpa using
    pairOfIdeal_hom_square
      (A := X.ring)
      (B := AdicCompletion X.ideal X.ring)
      X.ideal
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
      (Ideal.le_comap_map :
        X.ideal ≤
          Ideal.comap (algebraMap X.ring (AdicCompletion X.ideal X.ring))
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal))

-- Proof sketch: the completion ring is complete for the extended ideal, hence henselian by the
-- canonical complete-pair instance. The Noetherian hypothesis ensures the completion is complete
-- for that extended ideal in the ring-theoretic sense used by `HenselianRing`.
/-- The `I`-adic completion pair of a Noetherian pair is henselian. -/
private theorem adicCompletion_henselian :
    HenselianRing
      (AdicCompletion X.ideal X.ring)
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) := by
  let hComplete :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := by
    exact
      (IsAdicComplete.map_algebraMap_iff X.ideal (AdicCompletion X.ideal X.ring)).2
        (AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing X.ideal))
  letI :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := hComplete
  exact
    @IsAdicComplete.henselianRing
      (AdicCompletion X.ideal X.ring)
      inferInstance
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
      hComplete

/-- The canonical ring map from the henselization ring `A^h` to the `I`-adic completion `A^∧`. -/
def henselizationToAdicCompletion :
    henselizationRing X →+* AdicCompletion X.ideal X.ring :=
  let completionMap :
      X ⟶ pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) :=
    InducedCategory.homMk <|
      Arrow.homMk
        (CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)))
        (CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map))
        (toAdicCompletionPair_w X)
  let comparison :=
    ((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
      ⟨pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal),
        adicCompletion_henselian X⟩).symm
      completionMap
  ringHom comparison.hom

/-- Helper for Lemma 15.12.4: the canonical map from the henselization to the adic completion
extends the original map `A → A^∧`. -/
private theorem henselizationToAdicCompletion_comp_toHenselization :
    (henselizationToAdicCompletion X).comp (toHenselization X) =
      algebraMap X.ring (AdicCompletion X.ideal X.ring) := by
  -- TODO: normalize the arrow-level adjunction unit identity for the explicit morphism used in
  -- `henselizationToAdicCompletion` until it becomes the ring-hom equality above.
  sorry

/-- Helper for Lemma 15.12.4: the special-fiber ideal quotient of `A^h` is canonically the same as
the module quotient by `I A^h`. -/
private noncomputable abbrev henselizationIdeal_quotient_equiv_module_quotient :
    (henselizationRing X ⧸ Ideal.map (toHenselization X) X.ideal) ≃ₗ[X.ring]
      henselizationRing X ⧸ ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
        Submodule X.ring (henselizationRing X)) :=
  (Submodule.Quotient.restrictScalarsEquiv X.ring
      (Ideal.map (toHenselization X) X.ideal)).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars X.ring
        (Ideal.map (toHenselization X) X.ideal : Submodule (henselizationRing X)
          (henselizationRing X)))
      ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
        Submodule X.ring (henselizationRing X))
      (Ideal.smul_top_eq_map X.ideal).symm)

/-- Helper for Lemma 15.12.4: on the source ring `A`, quotienting by the ideal `I` is the same as
quotienting the `A`-module `A` by `I • A`. -/
private noncomputable abbrev sourceIdeal_quotient_equiv_module_quotient :
    (X.ring ⧸ X.ideal) ≃ₗ[X.ring]
      X.ring ⧸ ((X.ideal • (⊤ : Submodule X.ring X.ring)) :
        Submodule X.ring X.ring) :=
  Submodule.quotEquivOfEq
    (X.ideal : Submodule X.ring X.ring)
    ((X.ideal • (⊤ : Submodule X.ring X.ring)) : Submodule X.ring X.ring)
    (by simp)

/-- Helper for Lemma 15.12.4: the inverse source quotient-model bridge sends a module quotient
class back to the corresponding ideal quotient class. -/
private theorem sourceIdeal_quotient_equiv_module_quotient_symm_mkQ (x : X.ring) :
    (sourceIdeal_quotient_equiv_module_quotient (X := X)).symm
        (((X.ideal • (⊤ : Submodule X.ring X.ring)) :
          Submodule X.ring X.ring).mkQ x) =
      (Ideal.Quotient.mk X.ideal) x := by
  -- Proof comment: apply the forward quotient bridge and use its explicit formula on
  -- representatives.
  apply (sourceIdeal_quotient_equiv_module_quotient (X := X)).injective
  simpa [sourceIdeal_quotient_equiv_module_quotient] using
    (Submodule.quotEquivOfEq_mk
      (X.ideal : Submodule X.ring X.ring)
      ((X.ideal • (⊤ : Submodule X.ring X.ring)) : Submodule X.ring X.ring)
      (by simp : (X.ideal : Submodule X.ring X.ring) =
        ((X.ideal • (⊤ : Submodule X.ring X.ring)) :
          Submodule X.ring X.ring))
      x)

/-- Helper for Lemma 15.12.4: the quotient-model bridge sends an ideal-quotient class of `A^h`
to the corresponding module-quotient class. -/
private theorem henselizationIdeal_quotient_equiv_module_quotient_mk (x : henselizationRing X) :
    henselizationIdeal_quotient_equiv_module_quotient (X := X)
        ((Ideal.Quotient.mk (Ideal.map (toHenselization X) X.ideal)) x) =
      (((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
          Submodule X.ring (henselizationRing X)).mkQ x) := by
  have hrestrict :
      (Submodule.Quotient.restrictScalarsEquiv X.ring
          (Ideal.map (toHenselization X) X.ideal)).symm
          ((Ideal.Quotient.mk (Ideal.map (toHenselization X) X.ideal)) x) =
        Submodule.Quotient.mk x := by
    -- Proof comment: restricting scalars does not change the quotient generator.
    apply (Submodule.Quotient.restrictScalarsEquiv X.ring
      (Ideal.map (toHenselization X) X.ideal)).injective
    simpa [Ideal.Quotient.mk_eq_mk] using
      (Submodule.Quotient.restrictScalarsEquiv_mk X.ring
        (Ideal.map (toHenselization X) X.ideal) x)
  -- Proof comment: compute through the restriction-of-scalars equivalence and then the quotient
  -- transport induced by `I • ⊤ = I A^h`.
  calc
    henselizationIdeal_quotient_equiv_module_quotient (X := X)
        ((Ideal.Quotient.mk (Ideal.map (toHenselization X) X.ideal)) x)
      = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars X.ring
            (Ideal.map (toHenselization X) X.ideal : Submodule (henselizationRing X)
              (henselizationRing X)))
          ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
            Submodule X.ring (henselizationRing X))
          (Ideal.smul_top_eq_map X.ideal).symm)
          ((Submodule.Quotient.restrictScalarsEquiv X.ring
            (Ideal.map (toHenselization X) X.ideal)).symm
            ((Ideal.Quotient.mk (Ideal.map (toHenselization X) X.ideal)) x)) := by
            rfl
    _ = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars X.ring
            (Ideal.map (toHenselization X) X.ideal : Submodule (henselizationRing X)
              (henselizationRing X)))
          ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
            Submodule X.ring (henselizationRing X))
          (Ideal.smul_top_eq_map X.ideal).symm)
          (Submodule.Quotient.mk x) := by
            rw [hrestrict]
    _ = (((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
          Submodule X.ring (henselizationRing X)).mkQ x) := by
            simpa using
              (Submodule.quotEquivOfEq_mk
                (Submodule.restrictScalars X.ring
                  (Ideal.map (toHenselization X) X.ideal : Submodule (henselizationRing X)
                    (henselizationRing X)))
                ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
                  Submodule X.ring (henselizationRing X))
                (Ideal.smul_top_eq_map X.ideal).symm x)

/-- Helper for Lemma 15.12.4: the `n = 1` quotient comparison from Lemma `15.12.2` matches the
module-quotient map required by the completion-surjectivity API. -/
private theorem toHenselization_quotientMapByIdeal_bijective :
    Function.Bijective
      ((Algebra.linearMap X.ring (henselizationRing X)).quotientMapByIdeal X.ideal) := by
  let qRing :
      X.ring ⧸ X.ideal →+* henselizationRing X ⧸ Ideal.map (toHenselization X) X.ideal :=
    Ideal.quotientMap
      (Ideal.map (toHenselization X) X.ideal)
      (toHenselization X)
      Ideal.le_comap_map
  let eRing :
      (X.ring ⧸ X.ideal) ≃+* henselizationRing X ⧸ Ideal.map (toHenselization X) X.ideal :=
    RingEquiv.ofBijective qRing <| by
      -- Proof comment: this is exactly the `n = 1` quotient comparison from Lemma `15.12.2`,
      -- rewritten using `I^h = I A^h`.
      simpa [pow_one, henselizationIdeal_eq_map (X := X)] using
        quotientPowToHenselization_bijective (X := X) 1
  let e :
      X.ring ⧸ ((X.ideal • (⊤ : Submodule X.ring X.ring)) : Submodule X.ring X.ring) ≃ₗ[X.ring]
        henselizationRing X ⧸ ((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
          Submodule X.ring (henselizationRing X)) :=
    (sourceIdeal_quotient_equiv_module_quotient (X := X)).symm.trans
      (LinearEquiv.restrictScalars X.ring eRing.toLinearEquiv).trans
      (henselizationIdeal_quotient_equiv_module_quotient (X := X))
  have hmap :
      (Algebra.linearMap X.ring (henselizationRing X)).quotientMapByIdeal X.ideal =
        e.toLinearMap := by
    -- Proof comment: both quotient maps send the class of `x : A` to the class of its image in
    -- `A^h`, and the two quotient-model bridges only transport between ideal and module quotients.
    apply DFunLike.ext
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      ((X.ideal • (⊤ : Submodule X.ring X.ring)) : Submodule X.ring X.ring) q
    calc
      (Algebra.linearMap X.ring (henselizationRing X)).quotientMapByIdeal X.ideal
          (((X.ideal • (⊤ : Submodule X.ring X.ring)) :
            Submodule X.ring X.ring).mkQ x)
        = (((X.ideal • (⊤ : Submodule X.ring (henselizationRing X))) :
            Submodule X.ring (henselizationRing X)).mkQ ((toHenselization X) x)) := by
              simp [LinearMap.quotientMapByIdeal]
      _ = henselizationIdeal_quotient_equiv_module_quotient (X := X)
            ((Ideal.Quotient.mk (Ideal.map (toHenselization X) X.ideal))
              ((toHenselization X) x)) := by
              simpa using
                (henselizationIdeal_quotient_equiv_module_quotient_mk
                  (X := X) ((toHenselization X) x)).symm
      _ = henselizationIdeal_quotient_equiv_module_quotient (X := X)
            (eRing ((Ideal.Quotient.mk X.ideal) x)) := by
              rfl
      _ = henselizationIdeal_quotient_equiv_module_quotient (X := X)
            ((LinearEquiv.restrictScalars X.ring eRing.toLinearEquiv)
              ((sourceIdeal_quotient_equiv_module_quotient (X := X)).symm
                (((X.ideal • (⊤ : Submodule X.ring X.ring)) :
                  Submodule X.ring X.ring).mkQ x))) := by
              rw [sourceIdeal_quotient_equiv_module_quotient_symm_mkQ (X := X) x]
      _ = e.toLinearMap
            (((X.ideal • (⊤ : Submodule X.ring X.ring)) :
              Submodule X.ring X.ring).mkQ x) := by
              rfl
  simpa [hmap] using e.bijective

/-- Helper for Lemma 15.12.4: the `n`th quotient of the adic completion agrees with the `n`th
quotient of the original ring. -/
private theorem adicCompletion_quotientPow_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) (X.ideal ^ n))
        (algebraMap X.ring (AdicCompletion X.ideal X.ring))
        Ideal.le_comap_map) := by
  let e :
      (AdicCompletion X.ideal X.ring ⧸
          Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) (X.ideal ^ n)) ≃ₐ[X.ring]
        (X.ring ⧸ X.ideal ^ n) :=
    (Ideal.quotientEquivAlgOfEq X.ring
      (completionIdeal_pow_eq_ker_evalₐ (I := X.ideal)
        (Ideal.fg_of_isNoetherianRing (X.ideal)) n)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := AdicCompletion.evalₐ X.ideal n)
        (AdicCompletion.surjective_evalₐ X.ideal n))
  have hq :
      Ideal.quotientMap
          (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) (X.ideal ^ n))
          (algebraMap X.ring (AdicCompletion X.ideal X.ring))
          Ideal.le_comap_map =
        e.symm.toRingHom := by
    -- Proof comment: both maps send the class of `r : A` to the class of its canonical image in
    -- the completion quotient.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [e]
    change
      Ideal.Quotient.mk
          (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) (X.ideal ^ n))
          ((algebraMap X.ring (AdicCompletion X.ideal X.ring)) r) =
        (Ideal.quotientEquivAlgOfEq X.ring
          (completionIdeal_pow_eq_ker_evalₐ (I := X.ideal)
            (Ideal.fg_of_isNoetherianRing (X.ideal)) n).symm)
          ((Ideal.quotientKerAlgEquivOfSurjective
              (f := AdicCompletion.evalₐ X.ideal n)
              (AdicCompletion.surjective_evalₐ X.ideal n)).symm
            ((Ideal.Quotient.mk (X.ideal ^ n)) r))
    rw [← AdicCompletion.evalₐ_of (I := X.ideal) n r]
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply
      (hf := AdicCompletion.surjective_evalₐ X.ideal n)
      (a := AdicCompletion.of X.ideal X.ring r)]
    rfl
  rw [hq]
  exact e.symm.bijective

/-- Helper for Lemma 15.12.4: the induced map from the completion of `A` to the completion of
`A^h` is surjective. -/
private theorem adicCompletion_map_toHenselization_surjective :
    Function.Surjective
      (AdicCompletion.map X.ideal (Algebra.linearMap X.ring (henselizationRing X))) := by
  -- Proof comment: after transporting the `n = 1` quotient comparison into module-quotient form,
  -- we can apply the standard completion-surjectivity criterion directly.
  apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
  intro y
  obtain ⟨x, hx⟩ := (toHenselization_quotientMapByIdeal_bijective (X := X)).2 y
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
    ((X.ideal • (⊤ : Submodule X.ring X.ring)) : Submodule X.ring X.ring) x
  exact ⟨m, by simpa [LinearMap.quotientMapByIdeal] using hx⟩

-- Proof sketch: Lemma `15.12.2` identifies every quotient
-- `X.ring ⧸ X.ideal ^ n → henselizationRing X ⧸ (X.ideal)^n henselizationRing X` as a bijection.
-- Passing to inverse limits gives a bijection on the induced map of `X.ideal`-adic completions.
/-- Lemma 15.12.4 (1): the map on `I`-adic completions induced by `A → A^h`, formalized as the
map from the `I`-adic completion of `A` to the `I`-adic completion of the `A`-module `A^h`, is
bijective. -/
@[stacks 0AGV]
theorem adicCompletion_map_toHenselization_bijective :
    Function.Bijective
      (AdicCompletion.map X.ideal (Algebra.linearMap X.ring (henselizationRing X))) := by
  refine ⟨?_, adicCompletion_map_toHenselization_surjective X⟩
  -- Proof comment: the remaining injectivity step should identify the comparison map with the
  -- inverse-limit map built from the quotientwise bijections for all `I ^ n`.
  -- TODO: prove injectivity by comparing all quotient stages using
  -- `henselizationToAdicCompletion_comp_toHenselization`, `adicCompletion_quotientPow_bijective`,
  -- and `quotientPowToHenselization_bijective`, then conclude by the Hausdorff/extensionality API
  -- for adic completion.
  sorry

-- Proof sketch: once `A^h → A^∧` is known faithfully flat and `A^∧` is Noetherian by the standard
-- noetherianity theorem for adic completions of Noetherian rings, Noetherianity descends along
-- faithfully flat maps.
/-- Lemma 15.12.4 (2): the henselization ring `A^h` of a Noetherian pair `(A, I)` is Noetherian. -/
@[stacks 0AGV]
theorem henselizationRing_isNoetherian :
    IsNoetherianRing (henselizationRing X) := sorry

-- Proof sketch: this is exactly Lemma `15.12.2 (1)` recalled in the Noetherian setting.
/- Lemma 15.12.4 (3): the canonical map `A → A^h` is flat. -/
recall toHenselization_flat

-- Proof sketch: the completion map `A → A^∧` is flat for Noetherian rings, and the canonical map
-- `A^h → A^∧` is the comparison morphism from the henselization into that flat completion target.
-- Flatness follows from the quotientwise identification with the completion of `A`.
/-- Lemma 15.12.4 (4): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is flat. -/
@[stacks 0AGV]
theorem henselizationToAdicCompletion_flat :
    RingHom.Flat (henselizationToAdicCompletion X) := sorry

-- Proof sketch: `I^h = IA^h` lies in the Jacobson radical of the henselization pair, and the map
-- `A^h → A^∧` induces the identity on the special fiber `A^h / I^h ≅ A / I`. Together with the
-- previous flatness statement, the standard Jacobson-radical criterion upgrades flatness to
-- faithful flatness.
/-- Lemma 15.12.4 (5): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is faithfully flat. -/
@[stacks 0AGV]
theorem henselizationToAdicCompletion_faithfullyFlat :
    RingHom.FaithfullyFlat (henselizationToAdicCompletion X) := sorry

end

end RingPairCat
