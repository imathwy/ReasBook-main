import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_28_1
import stacks_proof.stacks_project.Chap15.Lemma_15_28_7
import stacks_proof.stacks_project.Chap15.Lemma_15_28_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory ComplexShape HomologicalComplex

/- Domain-style sampling:
- primary domain: degree shifts of `ℕ`-indexed chain complexes, expressed canonically through the
  cochain-complex shift on `ℤ` together with complex-shape embeddings;
- sampled owner declarations:
  `HomologicalComplex.extend`,
  `HomologicalComplex.restriction`,
  `ComplexShape.embeddingDownNat`,
  `CategoryTheory.shiftFunctor` on `CochainComplex C ℤ`;
- best owner abstraction: for an `ℕ`-indexed chain complex `K`, the source-facing degree-one
  shifted complex is the bridge/view
  `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`;
- primitive data: the chain complex `K` and the canonical embedding `embeddingDownNat`;
- derived API: any `ℕ`-indexed reformulation of that shifted complex.

Source/core/bridge triage:
- `source-facing`: the existence statement for the Koszul complexes in Lemma 15.28.10;
- `core/canonical`: `extend`, `restriction`, `embeddingDownNat`, and the canonical cochain shift;
- `bridge/view`: the `ℕ`-indexed shifted-chain source object obtained by extending to `ℤ`,
  shifting by `-1`, and restricting back. This file should therefore use that owner expression
  directly rather than keep a parallel local shift definition. -/

section

variable {R : Type u} [CommRing R]
variable {E : Type u} [AddCommGroup E] [Module R E]

/-- Helper for Lemma 15.28.10: extending the comparison from Lemma `15.28.7` identifies the
augmented Koszul complex with the extended scalar homotopy cofiber in the ambient `ℤ`-indexed
cochain category. -/
noncomputable def extended_koszul_coprod_scalar_iso_homotopyCofiber
    (φ : E →ₗ[R] R) (a : R) :
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).obj
        (koszulComplex (koszulCoprodScalarLinearMap φ a)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).obj
        (homotopyCofiber (a • 𝟙 (koszulComplex φ))) :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).mapIso
    (koszulComplex_coprod_scalar_iso_homotopyCofiber (φ := φ) a)

/-- Helper for Lemma 15.28.10: extending a scalar homotopy cofiber along `embeddingDownNat`
matches the homotopy cofiber of the extended scalar endomorphism. -/
noncomputable def extend_homotopyCofiber_scalar_iso
    (K : ChainComplex (ModuleCat R) ℕ) (a : R) :
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).obj
        (homotopyCofiber (a • 𝟙 K)) ≅
      homotopyCofiber
        (a • 𝟙 ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat R)).obj K)) :=
  sorry

/-- Helper for Lemma 15.28.10: the source-side comparison from Lemma `15.28.7` can be transported
through `extend`, the cochain shift by `-1`, and restriction back to `ℕ`. -/
noncomputable abbrev shifted_koszul_coprod_scalar_iso_homotopyCofiber
    (φ : E →ₗ[R] R) (a : R) :
    HomologicalComplex.restriction
        (((koszulComplex (koszulCoprodScalarLinearMap φ a)).extend embeddingDownNat)⟦(-1 : ℤ)⟧)
        embeddingDownNat ≅
      HomologicalComplex.restriction
        (((homotopyCofiber (a • 𝟙 (koszulComplex φ))).extend embeddingDownNat)⟦(-1 : ℤ)⟧)
        embeddingDownNat :=
  -- Proof comment: this is the thin adapter promised by the source proof; only the source object
  -- of the final cone map needs the shifted `extend`/`restriction` transport.
  (embeddingDownNat.restrictionFunctor (ModuleCat R)).mapIso <|
    (shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-1 : ℤ)).mapIso <|
      (embeddingDownNat.extendFunctor (ModuleCat R)).mapIso
        (koszulComplex_coprod_scalar_iso_homotopyCofiber (φ := φ) a)

/-- Helper for Lemma 15.28.10: Lemma `15.28.9` repackaged directly in the target file's
`extend`/shift/`restriction` language. -/
theorem restricted_homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber
    (K : ChainComplex (ModuleCat R) ℕ) (f g : R) :
    ∃ β :
        HomologicalComplex.restriction
            (((homotopyCofiber (f • 𝟙 K)).extend embeddingDownNat)⟦(-1 : ℤ)⟧)
            embeddingDownNat ⟶
          homotopyCofiber (g • 𝟙 K),
      Nonempty
        (HomotopyEquiv
          (homotopyCofiber ((f * g) • 𝟙 K))
          (homotopyCofiber β)) :=
  sorry

/-- Helper for Lemma 15.28.10: every degree in `ComplexShape.down ℕ` has the expected
predecessor, so the owner `homotopyCofiber.desc` constructor applies without any extra transport
work. -/
private lemma chain_down_exists_nat (j : ℕ) : ∃ i, (ComplexShape.down ℕ).Rel i j := by
  refine ⟨j + 1, ?_⟩
  simp [ComplexShape.down]

/-- Helper for Lemma 15.28.10: applying `descEquiv.symm` after postcomposition records
postcomposition on the owner descent data. -/
private theorem homotopyCofiber_descEquiv_symm_comp
    {A B K L : ChainComplex (ModuleCat R) ℕ} (φ : A ⟶ B)
    (g : K ⟶ L) (f : homotopyCofiber φ ⟶ K) :
    ((HomologicalComplex.homotopyCofiber.descEquiv
      (φ := φ) L chain_down_exists_nat).symm (f ≫ g)) =
      ⟨(((HomologicalComplex.homotopyCofiber.descEquiv
          (φ := φ) K chain_down_exists_nat).symm f).1 ≫ g),
        (Homotopy.ofEq (by simp [Category.assoc])).trans <|
          ((((HomologicalComplex.homotopyCofiber.descEquiv
              (φ := φ) K chain_down_exists_nat).symm f).2).compRight g).trans
            (Homotopy.ofEq (by simp))⟩ := by
  -- Unfold the owner inverse once and compare the resulting sigma data componentwise.
  rw [HomologicalComplex.homotopyCofiber.descSigma_ext_iff]
  constructor
  · change HomologicalComplex.homotopyCofiber.inr φ ≫ (f ≫ g) =
      (HomologicalComplex.homotopyCofiber.inr φ ≫ f) ≫ g
    simp [Category.assoc]
  · intro i j hij
    -- On the homotopy field, `descEquiv.symm` is defined by `inrCompHomotopy.compRight`, so the
    -- postcomposition formula is literal after reassociation.
    simp [HomologicalComplex.homotopyCofiber.descEquiv, Category.assoc]

/-- Helper for Lemma 15.28.10: `descEquiv.symm` sends an actual descended map back to the
descent datum used to define it. -/
private theorem homotopyCofiber_descEquiv_symm_desc
    {A B K : ChainComplex (ModuleCat R) ℕ} (φ : A ⟶ B)
    (α : B ⟶ K) (hα : Homotopy (φ ≫ α) 0) :
    ((HomologicalComplex.homotopyCofiber.descEquiv
      (φ := φ) K chain_down_exists_nat).symm (homotopyCofiber.desc φ α hα)) =
      ⟨α, hα⟩ := by
  -- This is the owner left-inverse of `descEquiv`; we expose it as a rewrite lemma for the two
  -- inverse checks in the cone-conjugation isomorphism below.
  simpa using
    (Equiv.symm_apply_apply
      (HomologicalComplex.homotopyCofiber.descEquiv
        (φ := φ) K chain_down_exists_nat) ⟨α, hα⟩)

/-- Helper for Lemma 15.28.10: conjugating a map by source and target isomorphisms preserves its
homotopy cofiber up to isomorphism. -/
noncomputable def homotopyCofiber_iso_of_conjugate
    {A A' B B' : ChainComplex (ModuleCat R) ℕ}
    (eA : A ≅ A') (eB : B ≅ B') (β : A' ⟶ B') :
    homotopyCofiber (eA.hom ≫ β ≫ eB.inv) ≅ homotopyCofiber β := by
  let hom :
      homotopyCofiber (eA.hom ≫ β ≫ eB.inv) ⟶ homotopyCofiber β :=
    -- Proof comment: descend from the target-side map `eB.hom ≫ inr β`; after reassociating,
    -- the null-homotopy is exactly `inrCompHomotopy β` precomposed by `eA.hom`.
    homotopyCofiber.desc (eA.hom ≫ β ≫ eB.inv)
      (eB.hom ≫ homotopyCofiber.inr β)
      ((Homotopy.ofEq (by simp [Category.assoc])).trans <|
        (homotopyCofiber.inrCompHomotopy β chain_down_exists_nat).compLeft eA.hom)
  let inv :
      homotopyCofiber β ⟶ homotopyCofiber (eA.hom ≫ β ≫ eB.inv) :=
    -- Proof comment: descend in the reverse direction from `eB.inv ≫ inr (eA.hom ≫ β ≫ eB.inv)`;
    -- this is the same source-faithful conjugation argument with `eA.inv` on the left.
    homotopyCofiber.desc β
      (eB.inv ≫ homotopyCofiber.inr (eA.hom ≫ β ≫ eB.inv))
      ((Homotopy.ofEq (by simp [Category.assoc])).trans <|
        (homotopyCofiber.inrCompHomotopy (eA.hom ≫ β ≫ eB.inv) chain_down_exists_nat).compLeft
          eA.inv)
  refine ⟨hom, inv, ?_, ?_⟩
  · -- Compare the forward-then-backward composite through `descEquiv.symm`; both sides encode
    -- the same map `inr` together with the same owner null-homotopy.
    let φ' := eA.hom ≫ β ≫ eB.inv
    have h_id :
        (𝟙 (homotopyCofiber φ')) =
          homotopyCofiber.desc φ'
            (homotopyCofiber.inr φ')
            (homotopyCofiber.inrCompHomotopy φ' chain_down_exists_nat) := by
      -- The identity is the descended map attached to the canonical `inr` null-homotopy.
      simpa using
        (HomologicalComplex.homotopyCofiber.eq_desc
          (φ := φ') (f := 𝟙 (homotopyCofiber φ')) chain_down_exists_nat).symm
    apply
      ((HomologicalComplex.homotopyCofiber.descEquiv
        (φ := φ') (homotopyCofiber φ') chain_down_exists_nat).symm.injective)
    rw [homotopyCofiber_descEquiv_symm_comp, h_id, homotopyCofiber_descEquiv_symm_desc,
      homotopyCofiber_descEquiv_symm_desc]
    rw [HomologicalComplex.homotopyCofiber.descSigma_ext_iff]
    constructor
    · -- The descended target map is literally `inr φ'` after canceling `eB.hom ≫ eB.inv`.
      simp [φ', hom, inv, Category.assoc]
    · intro i j hij
      -- Evaluate the reverse descent datum on the owner left summand, then cancel
      -- `eA.hom ≫ eA.inv = 𝟙`.
      have h_inv :
          homotopyCofiber.inlX β i j hij ≫ inv.f j =
            eA.inv.f i ≫ homotopyCofiber.inlX φ' i j hij := by
        -- `inlX_desc_f` exposes the homotopy field used to define `inv`.
        simpa [φ', inv, Category.assoc, homotopyCofiber.inrCompHomotopy_hom,
          hij] using
          (HomologicalComplex.homotopyCofiber.inlX_desc_f
            (φ := β)
            (α := eB.inv ≫ homotopyCofiber.inr φ')
            (hα := (Homotopy.ofEq (by simp [Category.assoc])).trans <|
              (homotopyCofiber.inrCompHomotopy φ' chain_down_exists_nat).compLeft eA.inv)
            i j hij)
      -- After the previous normalization, the remaining homotopy component is exactly the owner
      -- `inrCompHomotopy` for `φ'`.
      simpa [φ', hom, inv, Category.assoc, h_inv, homotopyCofiber.inrCompHomotopy_hom, hij] using
        (eA.hom_inv_id_assoc (homotopyCofiber.inlX φ' i j hij))
  · -- The reverse composite is symmetric: compare its descended data to the canonical identity
    -- data on `homotopyCofiber β`.
    have h_id :
        (𝟙 (homotopyCofiber β)) =
          homotopyCofiber.desc β
            (homotopyCofiber.inr β)
            (homotopyCofiber.inrCompHomotopy β chain_down_exists_nat) := by
      -- As above, `eq_desc` identifies the identity with the canonical descended `inr`.
      simpa using
        (HomologicalComplex.homotopyCofiber.eq_desc
          (φ := β) (f := 𝟙 (homotopyCofiber β)) chain_down_exists_nat).symm
    apply
      ((HomologicalComplex.homotopyCofiber.descEquiv
        (φ := β) (homotopyCofiber β) chain_down_exists_nat).symm.injective)
    rw [homotopyCofiber_descEquiv_symm_comp, h_id, homotopyCofiber_descEquiv_symm_desc,
      homotopyCofiber_descEquiv_symm_desc]
    rw [HomologicalComplex.homotopyCofiber.descSigma_ext_iff]
    constructor
    · -- This time `eB.inv ≫ eB.hom = 𝟙` gives the target `inr β`.
      simp [hom, inv, Category.assoc]
    · intro i j hij
      let φ' := eA.hom ≫ β ≫ eB.inv
      have h_hom :
          homotopyCofiber.inlX φ' i j hij ≫ hom.f j =
            eA.hom.f i ≫ homotopyCofiber.inlX β i j hij := by
        -- `inlX_desc_f` now exposes the homotopy field used to define `hom`.
        simpa [φ', hom, Category.assoc, homotopyCofiber.inrCompHomotopy_hom,
          hij] using
          (HomologicalComplex.homotopyCofiber.inlX_desc_f
            (φ := φ')
            (α := eB.hom ≫ homotopyCofiber.inr β)
            (hα := (Homotopy.ofEq (by simp [Category.assoc])).trans <|
              (homotopyCofiber.inrCompHomotopy β chain_down_exists_nat).compLeft eA.hom)
            i j hij)
      -- Cancel `eA.inv ≫ eA.hom = 𝟙` to recover the owner `inrCompHomotopy` for `β`.
      simpa [φ', hom, inv, Category.assoc, h_hom, homotopyCofiber.inrCompHomotopy_hom, hij] using
        (eA.inv_hom_id_assoc (homotopyCofiber.inlX β i j hij))

-- Proof sketch: identify the three Koszul complexes attached to
-- `koszulCoprodScalarLinearMap φ f`, `koszulCoprodScalarLinearMap φ g`, and
-- `koszulCoprodScalarLinearMap φ (f * g)` with the corresponding homotopy cofibers from
-- Lemma 15.28.7; interpret the degree-one shift of the first complex via the canonical bridge
-- `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`; then apply
-- `homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber` to the scalar endomorphisms
-- of `koszulComplex φ`.
/-- Lemma 15.28.10: if `φ'_f`, `φ'_g`, and `φ'_{fg}` are the linear forms on `E ⊕ R`, realized in
Lean as `E × R`, obtained from `φ` by adjoining multiplication by `f`, `g`, and `f * g` on the
`R`-summand, then the Koszul complex of `φ'_{fg}` is homotopy equivalent to the cone of a map
from the canonical degree-one shift
`((K(φ'_f).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
to `K(φ'_g)`. -/
@[stacks 062B]
theorem koszulComplex_coprod_scalar_mul_exists_homotopyEquiv_homotopyCofiber
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ α :
        (((koszulComplex (koszulCoprodScalarLinearMap φ f)).extend embeddingDownNat)⟦
          (-1 : ℤ)⟧).restriction embeddingDownNat ⟶
          koszulComplex (koszulCoprodScalarLinearMap φ g),
      Nonempty
        (HomotopyEquiv
          (koszulComplex (koszulCoprodScalarLinearMap φ (f * g)))
          (homotopyCofiber α)) := by
  let K := koszulComplex φ
  let ef := shifted_koszul_coprod_scalar_iso_homotopyCofiber (φ := φ) f
  let eg := koszulComplex_coprod_scalar_iso_homotopyCofiber (φ := φ) g
  let efg := koszulComplex_coprod_scalar_iso_homotopyCofiber (φ := φ) (f * g)
  rcases
      restricted_homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber
        (K := K) f g with
    ⟨β, hβ⟩
  refine ⟨ef.hom ≫ β ≫ eg.inv, ?_⟩
  rcases hβ with ⟨eβ⟩
  -- Route correction: only the source comparison is shifted. The `g` and `f * g` transports stay
  -- on the plain `ℕ`-indexed side, so the endgame is a single conjugation of `β`.
  refine ⟨(HomotopyEquiv.ofIso efg).trans <|
    eβ.trans <|
      HomotopyEquiv.ofIso (homotopyCofiber_iso_of_conjugate ef eg β).symm⟩

end
