import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_15_1 (from Chap09) -/
/- Domain-style sampling for Definition 9.15.1:
- primary domain: normal algebraic field extensions and their splitting criteria;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `Normal.splits`,
  `Normal.of_algEquiv`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `Normal F E`;
- primitive data: none locally, since the source notion and its pointwise splitting
  characterization are already owned upstream;
- derived API: `normal_iff` exposes the source-style criterion, while `Normal.splits` and
  `Normal.of_algEquiv` supply standard consequences and transport.

Source/core/bridge triage:
- `source-facing`: the textbook notion that an algebraic field extension is normal;
- `core/canonical`: `Normal`;
- `bridge/view`: the splitting criterion `normal_iff`.

This file should therefore remain a pure recall surface. A local theorem restating `normal_iff`
under an ambient algebraicity hypothesis would only duplicate the canonical owner API. -/

/- Definition 9.15.1: for an algebraic field extension `E/F`, the textbook notion that `E` is
normal over `F` is the canonical mathlib typeclass `Normal F E`, which already packages the
algebraicity of the extension. -/
recall Normal

/- Companion recall for Definition 9.15.1: `normal_iff` is the canonical source-facing
characterization of normality by splitting of minimal polynomials; under an ambient algebraicity
hypothesis, its integrality clause is automatic. -/
recall normal_iff

/-! ### Lemma_9_15_2 (from Chap09) -/
/- Domain-style sampling for Lemma 9.15.2:
- primary domain: normality in towers of algebraic field extensions;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `Normal.tower_top_of_normal`,
  `IntermediateField.normal`;
- best owner abstraction: the canonical owner is the mathlib typeclass `Normal` together with its
  tower theorem `Normal.tower_top_of_normal`;
- primitive data: none locally beyond the ambient field tower and the normality instance on the top
  extension;
- derived API: `Normal.tower_top_of_normal` is the theorem-level owner, and
  `IntermediateField.normal` is its intermediate-field specialization.

Source/core/bridge triage:
- `source-facing`: normality ascends from the base field to the middle field in a tower
  `F → E → K`;
- `core/canonical`: `Normal.tower_top_of_normal`;
- `bridge/view`: `IntermediateField.normal`.

This item adds no new mathematics beyond the canonical theorem, so the refined file should remain a
pure recall surface rather than introducing a redundant local wrapper theorem. -/

/- Lemma 9.15.2: in a tower of algebraic field extensions `K/E/F`, if `K` is normal over `F`,
then `K` is normal over `E`; this is the canonical theorem `Normal.tower_top_of_normal`. -/
recall Normal.tower_top_of_normal

/-! ### Lemma_9_15_3 (from Chap09) -/
/- Domain-style sampling for Lemma 9.15.3:
- primary domain: normality of algebraic intermediate-field extensions under lattice operations;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `IntermediateField.normal_iInf`,
  `IntermediateField.normal_inf`;
- best owner abstraction: the canonical owner is the mathlib typeclass `Normal`, with
  `IntermediateField.normal_iInf` as the intermediate-field lattice theorem owning the source
  construction;
- primitive data: a nonempty family `E : ι → IntermediateField F K` together with the pointwise
  normality instances `Normal F (E i)`;
- derived API: binary intersections are the special case `IntermediateField.normal_inf`, derived
  from the general intersection theorem.

Source/core/bridge triage:
- `source-facing`: the intersection of a nonempty family of normal intermediate extensions is
  normal;
- `core/canonical`: `IntermediateField.normal_iInf`;
- `bridge/view`: `IntermediateField.normal_inf` as the two-factor specialization.

This item adds no new mathematics beyond the canonical owner theorem, so the refined file should
remain a pure recall surface instead of introducing a parallel local lemma. -/

/- Lemma 9.15.3: for a nonempty family `E : ι → IntermediateField F K`, if each `E i / F` is
normal, then the intersection `⨅ i, E i` is normal over `F`. This is exactly the canonical
mathlib instance `IntermediateField.normal_iInf`, tagged `[stacks 09HP]`; the nonemptiness
hypothesis is the faithful formalization of the intended statement, since the empty intersection is
`⊤`. -/
recall IntermediateField.normal_iInf

/-! ### Lemma_9_15_4 (from Chap09) -/
universe u v

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Normal F E]

/- Domain-style sampling for Lemma 9.15.4:
- primary domain: normal algebraic field extensions and the separable closure inside a normal
  extension;
- sampled owner declarations:
  `Normal`,
  `separableClosure`,
  `separableClosure.normalClosure_eq_self`,
  `separableClosure.isGalois`;
- best owner abstraction: the source-faithful main surface is the canonical typeclass
  `Normal F (separableClosure F E)`;
- primitive data: none locally beyond the ambient normal extension `E / F`;
- derived API: the stronger bundled owner `IsGalois F (separableClosure F E)`, whose normality
  component gives the source statement.

Source/core/bridge triage:
- `source-facing`: normality of the intermediate field `separableClosure F E` over `F`;
- `core/canonical`: the owner typeclass `Normal`;
- `bridge/view`: the stronger instance `separableClosure.isGalois`.

This item should therefore remain a pure owner check surface. Replacing the main entry by a recall
of `separableClosure.isGalois` would strengthen the source statement from normality to Galoisness,
so the faithful refined form keeps the `Normal` conclusion as the main entry and treats the Galois
instance only as upstream support. -/
/- Lemma 9.15.4: if `E / F` is a normal algebraic field extension, then the subextension
`E / separableClosure F E / F` from Lemma 9.14.6 is normal; equivalently, the intermediate field
`separableClosure F E` is normal over `F`. In mathlib this is the normality component of the
canonical instance `separableClosure.isGalois`. -/
#check (inferInstance : Normal F (separableClosure F E))

/-! ### Lemma_9_15_5 (from Chap09) -/
universe u v

open IntermediateField

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.15.5:
- primary domain: normal algebraic field extensions, detected by the image fields of embeddings
  into an algebraic closure;
- sampled owner declarations:
  `IntermediateField.normal_iff_forall_fieldRange_eq`,
  `AlgHom.fieldRange_of_normal`,
  `AlgHom.map_fieldRange`,
  `AlgEquiv.transfer_normal`;
- best owner abstraction: the canonical owner is
  `IntermediateField.normal_iff_forall_fieldRange_eq`, applied to the intermediate field
  `ι.fieldRange` cut out by a chosen embedding `ι : E →ₐ[F] AlgebraicClosure F`;
- primitive data vs. derived API:
  primitive data is just that chosen embedding `ι`;
  derived API is the induced equivalence `AlgEquiv.ofInjectiveField ι : E ≃ₐ[F] ι.fieldRange`,
  transport of normality along this equivalence, and the field-range comparison obtained from
  `AlgHom.map_fieldRange`.

Source/core/bridge triage:
- `source-facing`: the textbook statement quantifying over pairs of embeddings
  `E →ₐ[F] AlgebraicClosure F`;
- `core/canonical`: `IntermediateField.normal_iff_forall_fieldRange_eq`;
- `bridge/view`: identify the abstract extension `E/F` with the concrete intermediate field
  `ι.fieldRange ⊆ AlgebraicClosure F`.

This file should therefore keep only the source-facing bridge theorem, while routing the proof
directly through the owner theorem instead of maintaining a parallel local normality criterion.
-/

/- Companion recall: the canonical owner theorem is the intermediate-field statement inside a
normal ambient extension. -/
recall IntermediateField.normal_iff_forall_fieldRange_eq

/-- Lemma 9.15.5: for an algebraic extension `E/F`, the extension is normal if and only if any
two `F`-algebra embeddings of `E` into `AlgebraicClosure F` have the same image subfield. -/
theorem normal_iff_forall_algHom_fieldRange_eq :
    Normal F E ↔
      ∀ σ σ' : E →ₐ[F] AlgebraicClosure F, σ.fieldRange = σ'.fieldRange := by
  let ι : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let e : E ≃ₐ[F] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  constructor
  · intro h σ σ'
    have hι (τ : E →ₐ[F] AlgebraicClosure F) : τ.fieldRange = ι.fieldRange := by
      letI : Normal F ι.fieldRange := e.transfer_normal.1 h
      have hcomp :
          IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) =
            (τ.comp e.symm.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.symm.toAlgHom τ
      have htop : (e.symm : ι.fieldRange →ₐ[F] E).fieldRange = ⊤ :=
        AlgEquiv.fieldRange_eq_top e.symm
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) := by
          rw [htop]
        _ = (τ.comp e.symm.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := AlgHom.fieldRange_of_normal (τ.comp e.symm.toAlgHom)
    exact (hι σ).trans (hι σ').symm
  · intro h
    have hfieldRange (τ : ι.fieldRange →ₐ[F] AlgebraicClosure F) :
        τ.fieldRange = ι.fieldRange := by
      have hcomp :
          IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) =
            (τ.comp e.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.toAlgHom τ
      have htop : (e : E →ₐ[F] ι.fieldRange).fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top e
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) := by rw [htop]
        _ = (τ.comp e.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := h (τ.comp e.toAlgHom) ι
    exact e.transfer_normal.2 <| normal_iff_forall_fieldRange_eq.2 hfieldRange

/-! ### Lemma_9_15_6 (from Chap09) -/
universe u v w

open IntermediateField

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E]

/-- Helper for Lemma 9.15.6: the intermediate field generated by integral generators is algebraic
over the base field. -/
lemma adjoin_range_isAlgebraic {I : Type w} (α : I → E)
    (hint : ∀ i : I, IsIntegral F (α i)) :
    Algebra.IsAlgebraic F (adjoin F (Set.range α)) := by
  -- Rewrite the indexed integrality hypothesis as a statement on the generating set.
  refine isAlgebraic_adjoin ?_
  intro y hy
  rcases hy with ⟨i, rfl⟩
  exact hint i

/-- Helper for Lemma 9.15.6: the indexed splitting hypothesis induces the set-based data required
for elements of `Set.range α`. -/
lemma range_generator_splitting_data {I : Type w} (α : I → E)
    (hint : ∀ i : I, IsIntegral F (α i))
    (hsplit : ∀ i : I, ((minpoly F (α i)).map (algebraMap F E)).Splits) :
    ∀ y ∈ Set.range α, IsIntegral F y ∧ ((minpoly F y).map (algebraMap F E)).Splits := by
  -- Unpack range membership to recover the original generator.
  intro y hy
  rcases hy with ⟨i, rfl⟩
  exact ⟨hint i, hsplit i⟩

/-- Helper for Lemma 9.15.6: every element of the field generated by the family `α` is integral
over the base field. -/
lemma isIntegral_of_mem_adjoin_range {I : Type w} (α : I → E)
    (hint : ∀ i : I, IsIntegral F (α i)) {x : E}
    (hx : x ∈ adjoin F (Set.range α)) :
    IsIntegral F x := by
  let K : IntermediateField F E := adjoin F (Set.range α)
  have halg : Algebra.IsAlgebraic F K := adjoin_range_isAlgebraic (F := F) α hint
  let xK : K := ⟨x, hx⟩
  have hxK_alg : IsAlgebraic F xK := by
    -- Algebraicity of the adjoin applies to the subtype element corresponding to `x`.
    exact @Algebra.IsAlgebraic.isAlgebraic F K _ _ _ halg xK
  have hxK_int : IsIntegral F xK := hxK_alg.isIntegral
  -- The inclusion of the adjoin into `E` preserves integrality.
  simpa [K, xK] using IsIntegral.map K.val hxK_int

/-- Lemma 9.15.6: if an algebraic extension `E/F` is generated by a family `α : I → E` and the
minimal polynomial of each generator `α i` over `F` splits completely in `E`, then `E/F` is
normal. -/
-- Domain style:
-- * sampled owner declarations: `Normal`, `normal_iff`, `IntermediateField.splits_of_mem_adjoin`,
--   `IntermediateField.isAlgebraic_adjoin`
-- * core owner: `Normal F E`
-- * primitive data here: the generating family `α`, the generatorwise integrality hypothesis, and
--   the generatorwise splitting hypothesis
-- * derived API: `IntermediateField.isAlgebraic_adjoin` upgrades generatorwise integrality to
--   algebraicity of the generated intermediate field, and `splits_of_mem_adjoin` upgrades the
--   splitting hypothesis from the generators to the whole generated intermediate field
--
-- This theorem is therefore a source-facing family-indexed bridge to the canonical owner, not a
-- second local notion of normality.
-- Proof sketch: apply `normal_iff`; generatorwise integrality makes `adjoin F (Set.range α)`
-- algebraic over `F`, hence every `x : E` is integral once `hgen` puts `x` in that adjoin; then
-- `splits_of_mem_adjoin` promotes splitting from the generating range to all of `E`.
@[stacks 0BR3 "second part"]
theorem normal_of_adjoin_range_minpoly_splits {I : Type w} (α : I → E)
    (hgen : adjoin F (Set.range α) = ⊤)
    (hint : ∀ i : I, IsIntegral F (α i))
    (hsplit : ∀ i : I, ((minpoly F (α i)).map (algebraMap F E)).Splits) :
    Normal F E := by
  -- Use the standard criterion for normality in terms of integrality and splitting.
  rw [normal_iff]
  intro x
  have hx : x ∈ adjoin F (Set.range α) := by
    -- The generation hypothesis identifies every element of `E` with an element of the adjoin.
    rw [hgen]
    exact mem_top
  have hx_integral : IsIntegral F x := isIntegral_of_mem_adjoin_range (F := F) α hint hx
  have hrange :
      ∀ y ∈ Set.range α, IsIntegral F y ∧ ((minpoly F y).map (algebraMap F E)).Splits :=
    range_generator_splitting_data (F := F) α hint hsplit
  have hx_splits : ((minpoly F x).map (algebraMap F E)).Splits :=
    splits_of_mem_adjoin F E hrange hx
  -- Combine the two propagated properties to finish the `normal_iff` criterion.
  exact ⟨hx_integral, hx_splits⟩

/-! ### Lemma_9_15_7 (from Chap09) -/
universe u v w

variable {K : Type u} {M : Type v} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

/- If `M/K` is normal, then any `K`-automorphism `τ` of `L` induces the canonical restricted
`K`-automorphism `τ.restrictNormal M` of `M`. -/
recall AlgEquiv.restrictNormal

/-
The canonical owner of the extension construction into a normal extension is `AlgHom.liftNormal`.
-/
recall AlgHom.liftNormal

/- For a normal target, the lifted endomorphism is bijective by `AlgHom.normal_bijective`. -/
recall AlgHom.normal_bijective

/-- Lemma 9.15.7: if `L/K` is normal, then any `K`-algebra map `σ : M →ₐ[K] L` extends to a
`K`-algebra automorphism of `L`. This source-facing bridge packages the canonical lift
`σ.liftNormal L` into an element of `Gal(L / K)`. -/
lemma exists_gal_extending_algHom [Normal K L] (σ : M →ₐ[K] L) :
    ∃ τ : Gal(L/K), τ.toAlgHom.comp (IsScalarTower.toAlgHom K M L) = σ := by
  refine ⟨AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _), ?_⟩
  ext x
  exact σ.liftNormal_commutes L x

/-! ### Definition_9_15_8 (from Chap09) -/
universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.15.8:
- primary domain: automorphism groups of field extensions in Galois theory;
- sampled canonical declarations:
  `Gal(E / F)`,
  `(inferInstance : Group Gal(E / F))`,
  `AlgEquiv.restrictNormalHom`,
  `IsGalois.card_aut_eq_finrank`;
- best owner abstraction: `Gal(E / F)`, the canonical type of `F`-algebra automorphisms of `E`.

Layer triage:
- `core/canonical`: `Gal(E / F)`;
- `bridge/view`: restriction morphisms such as `AlgEquiv.restrictNormalHom` and later cardinality
  theorems such as `IsGalois.card_aut_eq_finrank`.

Primitive data are only the field extension `E/F` and its `F`-algebra structure. The group
structure and later restriction/counting API are derived from this owner, so this file should not
introduce a parallel local `Aut(E/F)` alias or wrapper.
-/

/- Definition 9.15.8: for a field extension `E/F`, the automorphism group `Aut(E/F)` is the
canonical mathlib owner `Gal(E / F)`, i.e. the type of `F`-algebra automorphisms of `E`. -/
#check Gal(E / F)

/- Companion check: `Gal(E / F)` carries the canonical group structure induced by composition. -/
#check (inferInstance : Group Gal(E / F))

end

/-! ### Lemma_9_15_9 (from Chap09) -/
universe u v

open IntermediateField

private noncomputable def galToEmb
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Gal(E/F) → Field.Emb F E :=
  fun σ ↦ (IsScalarTower.toAlgHom F E (AlgebraicClosure E)).comp σ.toAlgHom

private theorem galToEmb_injective
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Function.Injective (galToEmb F E) := by
  intro σ τ hστ
  ext x
  exact (IsScalarTower.toAlgHom F E (AlgebraicClosure E)).injective <| DFunLike.congr_fun hστ x

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- For a finite extension `E/F`, the number of `F`-automorphisms of `E` is bounded by the finite
separable degree `[E : F]_s`. -/
theorem natCard_gal_le_finSepDegree :
    Nat.card Gal(E/F) ≤ Field.finSepDegree F E := by
  simpa [Field.finSepDegree, galToEmb] using
    Nat.card_le_card_of_injective (galToEmb F E) (galToEmb_injective F E)

/-- For a finite extension `E/F`, equality in the bound
`Nat.card Gal(E/F) ≤ Field.finSepDegree F E` is equivalent to normality. -/
theorem natCard_gal_eq_finSepDegree_iff_normal :
    Nat.card Gal(E/F) = Field.finSepDegree F E ↔ Normal F E := by
  constructor
  · intro h
    have hcard : Nat.card (Field.Emb F E) ≤ Nat.card Gal(E/F) := by
      exact le_of_eq <| calc
        Nat.card (Field.Emb F E) = Field.finSepDegree F E := rfl
        _ = Nat.card Gal(E/F) := h.symm
    have hbij : Function.Bijective (galToEmb F E) :=
      (galToEmb_injective F E).bijective_of_nat_card_le hcard
    let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E (AlgebraicClosure E)
    let e : E ≃ₐ[F] τ.fieldRange := AlgEquiv.ofInjectiveField τ
    have hfieldRange : ∀ ψ : τ.fieldRange →ₐ[F] AlgebraicClosure E, ψ.fieldRange = τ.fieldRange := by
      intro ψ
      rcases hbij.2 (ψ.comp e.toAlgHom) with ⟨σ, hσ⟩
      have hσtop : σ.toAlgHom.fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top σ
      have hetop : e.toAlgHom.fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top e
      have hcomp : (ψ.comp e.toAlgHom).fieldRange = τ.fieldRange := by
        calc
          (ψ.comp e.toAlgHom).fieldRange = ((galToEmb F E) σ).fieldRange := by
            simpa [galToEmb] using congrArg AlgHom.fieldRange hσ.symm
          _ = τ.fieldRange := by
            change (τ.comp σ.toAlgHom).fieldRange = τ.fieldRange
            rw [← AlgHom.map_fieldRange σ.toAlgHom τ, hσtop, ← AlgHom.fieldRange_eq_map τ]
      calc
        ψ.fieldRange = (ψ.comp e.toAlgHom).fieldRange := by
          rw [← AlgHom.map_fieldRange e.toAlgHom ψ, hetop, ← AlgHom.fieldRange_eq_map ψ]
        _ = τ.fieldRange := hcomp
    letI : Normal F τ.fieldRange := (normal_iff_forall_fieldRange_eq).2 hfieldRange
    exact Normal.of_algEquiv e.symm
  · intro h
    letI : Normal F E := h
    simpa [Field.finSepDegree] using
      (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-- Lemma 9.15.9: for a finite extension `E/F`, the number of `F`-automorphisms of `E` is at most
the finite separable degree `[E : F]_s`, and equality holds exactly when `E/F` is normal. -/
theorem natCard_gal_le_finSepDegree_and_eq_iff_normal :
    Nat.card Gal(E/F) ≤ Field.finSepDegree F E ∧
      (Nat.card Gal(E/F) = Field.finSepDegree F E ↔ Normal F E) :=
  ⟨natCard_gal_le_finSepDegree, natCard_gal_eq_finSepDegree_iff_normal⟩

end

/-! ### Lemma_9_15_10 (from Chap09) -/
/- Domain-style sampling for Lemma 9.15.2:
- primary domain: normality in towers of algebraic field extensions;
- sampled owner declarations:
  `Normal`,
  `normal_iff`,
  `Normal.tower_top_of_normal`,
  `IntermediateField.normal`;
- best owner abstraction: the canonical owner is the mathlib typeclass `Normal` together with its
  tower theorem `Normal.tower_top_of_normal`;
- primitive data: none locally beyond the ambient field tower and the normality instance on the top
  extension;
- derived API: `Normal.tower_top_of_normal` is the theorem-level owner, and
  `IntermediateField.normal` is its intermediate-field specialization.

Source/core/bridge triage:
- `source-facing`: normality ascends from the base field to the middle field in a tower
  `F → E → K`;
- `core/canonical`: `Normal.tower_top_of_normal`;
- `bridge/view`: `IntermediateField.normal`.

This item adds no new mathematics beyond the canonical theorem, so the file remains a pure recall
surface rather than introducing a redundant local wrapper theorem. -/

/- Lemma 9.15.2: let `K/E/F` be a tower of algebraic field extensions. If `K` is normal over `F`,
then `K` is normal over `E`; this is the canonical theorem `Normal.tower_top_of_normal`. -/
recall Normal.tower_top_of_normal
