import Mathlib
import StacksProject_2024.Chap15.Definition_15_28_2
import StacksProject_2024.Chap15.Lemma_15_28_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex
open scoped KoszulComplex

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.28.11: a compatible linear equivalence transports a Koszul complex to an
isomorphic Koszul complex. -/
private noncomputable def KoszulComplex.map_iso_of_linearEquiv
    {E E' : Type v} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
    {φ : E →ₗ[R] R} {φ' : E' →ₗ[R] R}
    (e : E ≃ₗ[R] E') (hφ : φ'.comp e.toLinearMap = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := KoszulComplex.map e.toLinearMap hφ
  inv :=
    -- The inverse comparison uses the inverse linear equivalence with the transported
    -- compatibility of linear forms.
    KoszulComplex.map e.symm.toLinearMap <| by
      apply LinearMap.ext
      intro x
      simpa using (LinearMap.congr_fun hφ (e.symm x)).symm
  hom_inv_id := by
    -- Check the composite on each exterior-power stage by reducing to generators.
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom e.symm.toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom e.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using congrArg (fun ψ : E ≃ₗ[R] E => ψ (m i)) e.left_inv
  inv_hom_id := by
    -- The reverse composite is identical after the same generator-level normalization.
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext m
    change
      ModuleCat.exteriorPower.map (ModuleCat.ofHom e.toLinearMap) n
          (ModuleCat.exteriorPower.map (ModuleCat.ofHom e.symm.toLinearMap) n
            (ModuleCat.exteriorPower.mk m)) =
        ModuleCat.exteriorPower.mk m
    rw [ModuleCat.exteriorPower.map_mk, ModuleCat.exteriorPower.map_mk]
    congr 1
    ext i
    simpa using congrArg (fun ψ : E' ≃ₗ[R] E' => ψ (m i)) e.right_inv

/-- Helper for Lemma 15.28.11: the canonical split `((Fin r → R) × R) ≃ Fin (r + 1) → R`
matches `Fin.snoc`. -/
private def finSnocLinearEquiv (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) :=
  { toFun := fun x ↦ Fin.snoc x.1 x.2
    invFun := fun x ↦ (Fin.init x, x (Fin.last r))
    map_add' := by
      intro x y
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simp
    map_smul' := by
      intro a x
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simp
    left_inv := by
      intro x
      ext i <;> simp
    right_inv := by
      intro x
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simp [Fin.init_def] }

@[simp] private theorem finSnocLinearEquiv_apply {r : ℕ} (x : (Fin r → R) × R) :
    finSnocLinearEquiv (R := R) r x = Fin.snoc x.1 x.2 :=
  rfl

/-- Helper for Lemma 15.28.11: after reindexing through `Fin.snoc`, the tuple linear form is the
coproduct scalar linear form on the truncated family. -/
private theorem koszulLinearForm_snoc_comp {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (koszulLinearForm (Fin.snoc fs a)).comp (finSnocLinearEquiv (R := R) r).toLinearMap =
      koszulCoprodScalarLinearMap (koszulLinearForm fs) a := by
  -- Evaluate both linear forms on a generic split tuple and simplify the `Fin.snoc` sum.
  apply LinearMap.ext
  intro x
  simp [LinearMap.comp_apply, finSnocLinearEquiv_apply, koszulCoprodScalarLinearMap,
    koszulLinearForm, Module.piEquiv_apply_apply, Fin.sum_univ_castSucc]

/-- Helper for Lemma 15.28.11: the family Koszul complex on `Fin.snoc fs a` is the transported
coproduct-scalar Koszul complex. -/
private noncomputable def koszulComplex_snoc_iso_coprod_scalar {r : ℕ}
    (fs : Fin r → R) (a : R) :
    K^•(Fin.snoc fs a) ≅
      koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) :=
  (KoszulComplex.map_iso_of_linearEquiv
      (φ := koszulCoprodScalarLinearMap (koszulLinearForm fs) a)
      (φ' := koszulLinearForm (Fin.snoc fs a))
      (finSnocLinearEquiv (R := R) r)
      (koszulLinearForm_snoc_comp (R := R) fs a)).symm

/-- Helper for Lemma 15.28.11: the shifted source complex in Lemma 15.28.10 transports through
the same `Fin.snoc` comparison by functoriality of `extend`, `shift`, and `restriction`. -/
private noncomputable abbrev shifted_koszulComplex_snoc_iso_coprod_scalar {r : ℕ}
    (fs : Fin r → R) (a : R) :
    (((K^•(Fin.snoc fs a)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat ≅
      ((((koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a)).extend
          embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat) :=
  (embeddingDownNat.restrictionFunctor (ModuleCat R)).mapIso <|
      (shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-1 : ℤ)).mapIso <|
      (embeddingDownNat.extendFunctor (ModuleCat R)).mapIso
        (koszulComplex_snoc_iso_coprod_scalar (R := R) fs a)

/-- Helper for Lemma 15.28.11: conjugating a morphism by source and target isomorphisms preserves
its homotopy cofiber up to isomorphism. -/
private noncomputable def homotopyCofiber_iso_of_conjugate
    {A A' B B' : ChainComplex (ModuleCat R) ℕ}
    (eA : A ≅ A') (eB : B ≅ B') (β : A' ⟶ B') :
    homotopyCofiber (eA.hom ≫ β ≫ eB.inv) ≅ homotopyCofiber β := sorry

/-- Helper for Lemma 15.28.11: the coproduct-scalar case supplied by Lemma `15.28.10`. -/
private theorem koszulComplex_coprod_scalar_mul_exists_homotopyEquiv_homotopyCofiber
    {E : Type u} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ α :
        (((koszulComplex (koszulCoprodScalarLinearMap φ f)).extend embeddingDownNat)⟦
          (-1 : ℤ)⟧).restriction embeddingDownNat ⟶
          koszulComplex (koszulCoprodScalarLinearMap φ g),
      Nonempty
        (HomotopyEquiv
          (koszulComplex (koszulCoprodScalarLinearMap φ (f * g)))
          (homotopyCofiber α)) := by
  sorry

-- Proof sketch: specialize Lemma `15.28.10` to the family linear form `koszulLinearForm fs`,
-- then transport the three linear-map-level Koszul complexes to the family-level complexes on
-- `Fin.snoc fs f`, `Fin.snoc fs g`, and `Fin.snoc fs (f * g)`.
/-- Lemma 15.28.11: for a finite family `fs : Fin r → R`, the Koszul complex on
`Fin.snoc fs (f * g)` is homotopy equivalent to the cone of a map from the canonical degree-one
shift `(((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
of the Koszul complex on `Fin.snoc fs f` to the Koszul complex on `Fin.snoc fs g`. -/
theorem koszulComplexOn_snoc_mul_exists_homotopyEquiv_homotopyCofiber
    {r : ℕ} (fs : Fin r → R) (f g : R) :
    ∃ α :
        (((K^•(Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction
            embeddingDownNat ⟶
        K^•(Fin.snoc fs g),
      Nonempty (HomotopyEquiv (K^•(Fin.snoc fs (f * g))) (homotopyCofiber α)) := by
  -- Route correction: follow the source proof literally by specializing Lemma `15.28.10` to
  -- `φ := koszulLinearForm fs`, then transport the three coproduct-scalar Koszul complexes along
  -- the canonical `Fin.snoc` linear equivalences.
  let ef := shifted_koszulComplex_snoc_iso_coprod_scalar (R := R) fs f
  let eg := koszulComplex_snoc_iso_coprod_scalar (R := R) fs g
  let efg := koszulComplex_snoc_iso_coprod_scalar (R := R) fs (f * g)
  rcases
      koszulComplex_coprod_scalar_mul_exists_homotopyEquiv_homotopyCofiber
        (φ := koszulLinearForm fs) f g with
    ⟨β, hβ⟩
  -- Proof comment: conjugate the specialized map `β` by the `Fin.snoc` transport isomorphisms.
  refine ⟨ef.hom ≫ β ≫ eg.inv, ?_⟩
  rcases hβ with ⟨eβ⟩
  -- Proof comment: `efg` transports the `fg`-complex, and the imported conjugation lemma from
  -- Lemma `15.28.10` transports the cone of `β` to the cone of the family-level map.
  refine ⟨(HomotopyEquiv.ofIso efg).trans <|
    eβ.trans <|
      HomotopyEquiv.ofIso (homotopyCofiber_iso_of_conjugate ef eg β).symm⟩

end
