import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField

universe u v

/- Domain-style sampling for Lemma 9.27.3:
- primary domain: algebraic / normal field extensions, relative separable closures, purely
  inseparable intermediate fields, and fixed fields of automorphism groups;
- sampled canonical owners:
  `perfectClosure`,
  `perfectClosure.isPurelyInseparable`,
  `separableClosure.isGalois`,
  `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`;
- best owner abstraction: the canonical intermediate fields `separableClosure F E` and
  `perfectClosure F E`, with `Normal F E` as the ambient normal-case owner and the fixed-field
  presentation demoted to a companion bridge theorem;
- primitive data: none locally beyond the ambient field extension hypotheses, with algebraicity
  already part of `Normal F E` on the normal side;
- derived API: the normal-case bridge to `fixedField (⊤ : Subgroup Gal(E/F))`, the Galois
  structure of `E / perfectClosure F E`, and the final decomposition statement.

Source/core/bridge triage:
- `source-facing`: the normal algebraic decomposition into separable and purely inseparable parts;
- `core/canonical`: `separableClosure`, `perfectClosure`, `IsPurelyInseparable`,
  `IsGalois`, and `LinearDisjoint`;
- `bridge/view`: the theorem identifying `perfectClosure F E` with the fixed field of the full
  automorphism group. -/

section AlgebraicPart

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [Algebra.IsAlgebraic F E]

/- For any algebraic extension `E / F`, the ambient extension is purely inseparable over the
canonical intermediate field `separableClosure F E`. This is exactly the owner instance
`separableClosure.isPurelyInseparable`. -/
recall separableClosure.isPurelyInseparable

/- In particular, for the algebraic extensions considered here, the canonical purely inseparable
part over `F` is the owner instance `perfectClosure.isPurelyInseparable`. -/
recall perfectClosure.isPurelyInseparable

end AlgebraicPart

section NormalAlgebraicPart

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [Normal F E]

/- In the normal case, the separable closure inside `E` is already Galois over `F`. This is the
canonical owner instance `separableClosure.isGalois`. -/
recall separableClosure.isGalois

/-- Helper for Lemma 9.27.3: in a normal algebraic extension, an element lies in the relative
perfect closure exactly when every `F`-automorphism fixes it. -/
lemma mem_perfectClosure_iff_fixed_by_all_aut {x : E} :
    x ∈ perfectClosure F E ↔ ∀ σ : Gal(E/F), σ x = x := by
  classical
  let S : Finset E := ((minpoly F x).aroots E).toFinset
  have hsplits : ((minpoly F x).map (algebraMap F E)).Splits := Normal.splits' x
  have hx_root : x ∈ (minpoly F x).rootSet E := by
    exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).mem_rootSet.2 (minpoly.aeval F x)
  have hxS : x ∈ S := by
    simpa [S, Polynomial.rootSet_def] using hx_root
  constructor
  · intro hx σ
    -- The perfect-closure hypothesis forces the minimal polynomial to have a unique distinct root.
    have hsep : (minpoly F x).natSepDegree = 1 :=
      (mem_perfectClosure_iff_natSepDegree_eq_one (F := F) (E := E)).1 hx
    have hS : S.card = 1 := by
      have hnat := Polynomial.natSepDegree_eq_of_splits (f := minpoly F x) (E := E) hsplits
      rw [hsep] at hnat
      exact hnat.symm
    have hσ_root : Polynomial.aeval (σ x) (minpoly F x) = 0 := by
      simpa [minpoly.algEquiv_eq σ x] using (minpoly.aeval F (σ x))
    have hσS : σ x ∈ S := by
      have hroot : σ x ∈ (minpoly F x).rootSet E := by
        exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).mem_rootSet.2 hσ_root
      simpa [S, Polynomial.rootSet_def] using hroot
    rcases Finset.card_eq_one.mp hS with ⟨y, hy⟩
    have hxeq : x = y := by
      simpa [hy] using hxS
    have hσeq : σ x = y := by
      simpa [hy] using hσS
    exact hσeq.trans hxeq.symm
  · intro hfix
    -- If every automorphism fixes `x`, every root of its minimal polynomial must already equal `x`.
    have hroot_eq : ∀ y, y ∈ S → y = x := by
      intro y hy
      have hy_root : y ∈ (minpoly F x).rootSet E := by
        simpa [S, Polynomial.rootSet_def] using hy
      have hyaeval : Polynomial.aeval y (minpoly F x) = 0 := by
        exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).mem_rootSet.1 hy_root
      have hymin : minpoly F x = minpoly F y := by
        exact minpoly.eq_of_irreducible_of_monic
          (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)) hyaeval
          (minpoly.monic (Algebra.IsIntegral.isIntegral x))
      have hyorbit : y ∈ MulAction.orbit Gal(E/F) x :=
        (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := E)).mp hymin.symm
      rcases hyorbit with ⟨σ, rfl⟩
      simpa using hfix σ
    have hS : S.card = 1 := by
      refine Finset.card_eq_one.mpr ?_
      refine ⟨x, Finset.ext fun y ↦ ?_⟩
      constructor
      · intro hy
        simp [hroot_eq y hy]
      · intro hy
        rcases Finset.mem_singleton.mp hy with rfl
        exact hxS
    -- Counting distinct roots now identifies the separable degree with `1`.
    have hnat : (minpoly F x).natSepDegree = 1 := by
      rw [Polynomial.natSepDegree_eq_of_splits (f := minpoly F x) (E := E) hsplits, hS]
    exact (mem_perfectClosure_iff_natSepDegree_eq_one (F := F) (E := E)).2 hnat

-- Proof sketch: the canonical purely inseparable intermediate field `perfectClosure F E` is
-- pointwise fixed by every `F`-automorphism of `E`, while the maximality theorem
-- `le_perfectClosure_iff` identifies any purely inseparable intermediate field with a subfield of
-- `perfectClosure F E`.
/-- In a normal algebraic extension, the fixed field of the full automorphism group is exactly the
canonical purely inseparable part `perfectClosure F E`. -/
theorem perfectClosure_eq_fixedField_top_of_normal_algebraic :
    perfectClosure F E = fixedField (⊤ : Subgroup Gal(E/F)) := by
  ext x
  rw [IntermediateField.mem_fixedField_iff, mem_perfectClosure_iff_fixed_by_all_aut]
  constructor
  · intro hx σ _
    exact hx σ
  · intro hx σ
    exact hx σ (Subgroup.mem_top _)

/-- Helper for Lemma 9.27.3: there is no further purely inseparable part above the canonical
perfect closure. -/
lemma perfectClosure_eq_bot_over_perfectClosure :
    perfectClosure (perfectClosure F E) E = ⊥ := by
  let K := perfectClosure F E
  apply bot_unique
  intro x hx
  -- Any element purely inseparable over `K` is still purely inseparable over `F`, hence already
  -- lies in `K`.
  have hle :
      (perfectClosure K E).restrictScalars F ≤ perfectClosure F E := by
    letI : IsPurelyInseparable F ↥((perfectClosure K E).restrictScalars F) := by
      change IsPurelyInseparable F ↥(perfectClosure K E)
      exact IsPurelyInseparable.trans (F := F) (E := K) (K := perfectClosure K E)
    exact le_perfectClosure F E ((perfectClosure K E).restrictScalars F)
  have hxK : x ∈ perfectClosure F E := hle hx
  exact IntermediateField.mem_bot.mpr ⟨⟨x, hxK⟩, rfl⟩

-- Proof sketch: first identify the purely inseparable part with the fixed field of the full
-- automorphism group, then transport the standard fixed-field Galois statement across that
-- equality.
/-- In a normal algebraic extension, the ambient field is Galois over its canonical purely
inseparable part `perfectClosure F E`. -/
theorem isGalois_over_perfectClosure_of_normal_algebraic :
    IsGalois (perfectClosure F E) E := by
  let K := perfectClosure F E
  letI : Normal K E := Normal.tower_top_of_normal F K E
  have hbot : perfectClosure K E = ⊥ :=
    perfectClosure_eq_bot_over_perfectClosure (F := F) (E := E)
  have hsep : Algebra.IsSeparable K E := by
    refine ⟨fun x ↦ ?_⟩
    let L : IntermediateField K E := normalClosure K K⟮x⟯ E
    have hx_alg : IsAlgebraic K x :=
      IsAlgebraic.tower_top K (Algebra.IsAlgebraic.isAlgebraic (R := F) x)
    letI : FiniteDimensional K K⟮x⟯ :=
      IntermediateField.adjoin.finiteDimensional hx_alg.isIntegral
    letI : FiniteDimensional K L :=
      normalClosure.is_finiteDimensional K K⟮x⟯ E
    have hLbot : perfectClosure K L = ⊥ := by
      apply bot_unique
      intro y hy
      have hyE : (y : E) ∈ perfectClosure K E := by
        exact (map_mem_perfectClosure_iff (F := K) (E := L) (K := E) L.val).2 hy
      rw [hbot] at hyE
      obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hyE
      refine IntermediateField.mem_bot.mpr ?_
      use z
      apply Subtype.val_injective
      simpa using hz
    -- The finite normal closure of `K⟮x⟯` is Galois once its own perfect closure is trivial.
    have hLfixed : IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) = ⊥ := by
      have hperfect :=
        perfectClosure_eq_fixedField_top_of_normal_algebraic (F := K) (E := L)
      rw [hLbot] at hperfect
      simpa using hperfect.symm
    have hLGal : IsGalois K L :=
      IsGalois.of_fixedField_eq_bot (F := K) (E := L) hLfixed
    have hxL : x ∈ L := by
      show x ∈ normalClosure K K⟮x⟯ E
      exact IntermediateField.le_normalClosure K⟮x⟯
        (IntermediateField.mem_adjoin_simple_self K x)
    exact IntermediateField.isSeparable_of_mem_isSeparable K E hxL
  exact { to_isSeparable := hsep, to_normal := inferInstance }

-- Proof sketch: combine the canonical purely inseparable owner `perfectClosure F E` with the
-- canonical separable owner `separableClosure F E`; linear disjointness comes from the
-- purely-inseparable/separable criterion, and the normal-case Galois theorem over
-- `perfectClosure F E` yields that their compositum is all of `E`. The fixed-field description is
-- then recovered from `perfectClosure_eq_fixedField_top_of_normal_algebraic`.
/-- Lemma 9.27.3: for a normal algebraic extension `E/F`, the canonical separable part
`separableClosure F E` and the canonical purely inseparable part `perfectClosure F E` are
linearly disjoint over `F` and generate all of `E`; equivalently, `E` is the tensor product of
its separable and purely inseparable parts over `F`. -/
@[stacks 030M]
theorem normal_algebraic_separable_inseparable_decomposition :
    (separableClosure F E).LinearDisjoint (perfectClosure F E) ∧
      separableClosure F E ⊔ perfectClosure F E = ⊤ := by
  let K := perfectClosure F E
  constructor
  · -- The separable and purely inseparable parts are linearly disjoint by the standard criterion.
    exact (separableClosure F E).linearDisjoint_of_isPurelyInseparable_of_isSeparable K
  · have hGal : IsGalois K E :=
      isGalois_over_perfectClosure_of_normal_algebraic (F := F) (E := E)
    have hsepTop : separableClosure K E = ⊤ :=
      (separableClosure.eq_top_iff (F := K) (E := E)).2 hGal.to_isSeparable
    -- Over `K`, adjoining the original separable closure produces all of `E`.
    have hadjoin : adjoin K (separableClosure F E : Set E) = ⊤ := by
      rw [separableClosure.adjoin_eq_of_isAlgebraic (F := F) (E := K) (K := E), hsepTop]
    -- Rewriting the adjoin over `K` as a supremum gives the claimed compositum identity.
    have hsup :
        K ⊔ separableClosure F E = ⊤ := by
      have hsup' :
          restrictScalars F (adjoin K (separableClosure F E : Set E)) =
            K ⊔ separableClosure F E := by
        simpa using
          (IntermediateField.restrictScalars_adjoin_eq_sup (F := F) (E := E) K
            (separableClosure F E : Set E))
      rw [hadjoin] at hsup'
      simpa using hsup'.symm
    simpa [K, sup_comm] using hsup

end NormalAlgebraicPart
