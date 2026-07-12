import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_2
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SimpleAscends
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.HomBaseChange
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.SimpleClassBridge
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6.Bases

/-!
# Field independence of simple modular representations over algebraically closed fields

For algebraically closed fields `L ⊆ E` of characteristic `p` and a finite group `G`, every simple
`E[G]`-representation `T` is, up to isomorphism, the scalar extension of a simple
`L[G]`-representation.

The argument is the *modular Wedderburn count*.  Pick complete pairwise nonisomorphic families
`πL` (over `L`) and `πE` (over `E`) of simple representations.  By Corollary 18-18.2-5 each family
has index cardinality equal to the (field-independent) number of `p`-regular conjugacy classes of
`G`, so the two index types have equal cardinality and are finite.  Scalar-extending the `L`-family
gives `π' i := FDRep.scalarExtension (πL i)`, which is again simple (Brick 1', modular) and pairwise
nonisomorphic (the intertwiner dimensions are preserved by Hom base change, and Schur over the
algebraically closed fields turns non-isomorphism into vanishing intertwiner dimension).  Matching
each `π' i` to an index of `πE` produces an injective map `ιL → ιE`, which is surjective by the
cardinality equality.  Hence every simple `E`-representation — in particular `T` — is isomorphic to
some `π' i`, i.e. to the scalar extension of a simple `L`-representation.

This is the characteristic-`p` analogue of `FieldIndependence/Surjectivity.lean` (which uses the
semisimple identity `∑ dᵢ² = |G|` in place of `|simple| = |p-regular classes|`).
-/

noncomputable section

universe u

open scoped TensorProduct Representation

open CategoryTheory

namespace Representation

variable {p : ℕ} [hp : Fact p.Prime]
variable {L : Type u} [Field L] [IsAlgClosed L] [hL : CharP L p]
variable {E : Type u} [Field E] [IsAlgClosed E] [Algebra L E]
variable {G : Type u} [Group G] [Finite G]

omit [Fact p.Prime] in
/-- The index type of a complete pairwise-nonisomorphic simple family over an arbitrary field is
finite: the Grothendieck classes of the family form a basis of the finitely generated `ℤ`-module
`R₀[k](G)`. -/
private theorem finite_index_of_complete_family {k : Type u} [Field k] [IsAlgClosed k]
    [CharP k p] {ι : Type (u + 1)} (π : ι → FDRep k G)
    (hpw : PairwiseNonisomorphic π) (hc : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  let bR := simple_finiteRep_classes_basis_of_complete_family π hpw hc
  letI : Module.Finite ℤ (R₀[k](G)) :=
    (cartan_source_target_free_and_finite_support (k := k) (G := G)).2.2.2
  exact Module.Finite.finite_basis bR

omit [IsAlgClosed L] [IsAlgClosed E] in
/-- The `E`-dimension of the intertwiners between scalar extensions of two finite-dimensional
`L`-representations equals the `L`-dimension of the intertwiners between the originals, packaged at
the `FDRep`-Hom level (i.e. `dim_E (V_E ⟶ W_E) = dim_L (V ⟶ W)`). -/
private theorem finrank_hom_scalarExtension_eq (V W : FDRep L G) :
    Module.finrank E (FDRep.scalarExtension (k := E) V ⟶ FDRep.scalarExtension (k := E) W)
      = Module.finrank L (V ⟶ W) := by
  -- Bridge each `FDRep`-Hom space to the corresponding intertwiner space.
  have hbridgeE :
      Module.finrank E (FDRep.scalarExtension (k := E) V ⟶ FDRep.scalarExtension (k := E) W)
        = Module.finrank E (Representation.IntertwiningMap
            (Representation.scalarExtension (k := E) V.ρ)
            (Representation.scalarExtension (k := E) W.ρ)) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom
          (FDRep.scalarExtension (k := E) V) (FDRep.scalarExtension (k := E) W)).symm.trans
        (Representation.invariantsEquivIntertwiningMap
          (FDRep.scalarExtension (k := E) V).ρ (FDRep.scalarExtension (k := E) W).ρ))
  have hbridgeL :
      Module.finrank L (V ⟶ W)
        = Module.finrank L (Representation.IntertwiningMap V.ρ W.ρ) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom V W).symm.trans
        (Representation.invariantsEquivIntertwiningMap V.ρ W.ρ))
  rw [hbridgeE, hbridgeL]
  exact Representation.finrank_intertwiningMap_eq_baseChange_hom V.ρ W.ρ

include hp hL in
/-- **Char-`p` modular field independence.**  Over algebraically closed fields `L ⊆ E` of
characteristic `p` and a finite group `G`, every simple `E[G]`-representation is isomorphic to the
scalar extension of a simple `L[G]`-representation. -/
theorem exists_simple_isScalarExtension_of_isAlgClosed_modular
    (T : FDRep E G) [Simple T] :
    ∃ (S : FDRep L G), Simple S ∧ Nonempty (T ≅ FDRep.scalarExtension S) := by
  classical
  -- Characteristic `p` passes from `L` to `E` along the injective coefficient embedding.
  haveI : CharP E p := charP_of_injective_algebraMap (algebraMap L E).injective p
  -- Step 1: complete pairwise nonisomorphic simple families over `L` and over `E`.
  obtain ⟨ιL, πL, hπL_pw, hπL_comp⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field (F := L) (H := G)
  obtain ⟨ιE, πE, hπE_pw, hπE_comp⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field (F := E) (H := G)
  haveI : Finite ιL := finite_index_of_complete_family (p := p) πL hπL_pw hπL_comp
  haveI : Finite ιE := finite_index_of_complete_family (p := p) πE hπE_pw hπE_comp
  -- Step 2: the two index types have equal cardinality (both count `p`-regular classes).
  have hcardL : Nat.card ιL = Nat.card (PRegularConjClass G p) :=
    card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
      (p := p) πL hπL_pw hπL_comp
  have hcardE : Nat.card ιE = Nat.card (PRegularConjClass G p) :=
    card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
      (p := p) πE hπE_pw hπE_comp
  have hcard : Nat.card ιL = Nat.card ιE := hcardL.trans hcardE.symm
  -- Step 3: scalar-extend the `L`-family; each member stays simple.
  let π' : ιL → FDRep E G := fun i ↦ FDRep.scalarExtension (πL i)
  have hπ'_simple : ∀ i, Simple (π' i) := by
    intro i
    letI : Simple (πL i) := hπL_comp.isSimple i
    letI hirr : Representation.IsIrreducible (πL i).ρ := FDRep.isIrreducible_of_simple (πL i)
    letI : Representation.IsIrreducible (π' i).ρ :=
      isIrreducible_scalarExtension_of_isAlgClosed_base_of_isAlgClosed (E := E) (πL i).ρ hirr
    exact FDRep.simple_of_isIrreducible (π' i)
  -- Step 4: the scalar-extended family is pairwise nonisomorphic.  Schur over `L` makes the
  -- intertwiner dimension vanish for non-isomorphic simples, and Hom base change carries that
  -- vanishing up to `E`, where (Schur over the algebraically closed `E`) it forbids isomorphism.
  have hπ'_pw : PairwiseNonisomorphic π' := by
    intro i j hij
    letI : Simple (πL i) := hπL_comp.isSimple i
    letI : Simple (πL j) := hπL_comp.isSimple j
    letI : Simple (π' i) := hπ'_simple i
    letI : Simple (π' j) := hπ'_simple j
    -- `dim_L (πL i ⟶ πL j) = 0` because `πL i ≇ πL j`.
    have hzeroL : Module.finrank L (πL i ⟶ πL j) = 0 := by
      rw [FDRep.finrank_hom_simple_simple (πL i) (πL j)]
      rw [if_neg]
      rintro ⟨e⟩
      exact hπL_pw hij ⟨e⟩
    -- Transport the vanishing to `E` via Hom base change.
    have hzeroE : Module.finrank E (π' i ⟶ π' j) = 0 := by
      rw [show π' i = FDRep.scalarExtension (k := E) (πL i) from rfl,
        show π' j = FDRep.scalarExtension (k := E) (πL j) from rfl,
        finrank_hom_scalarExtension_eq (πL i) (πL j), hzeroL]
    -- Over the algebraically closed `E`, vanishing intertwiner dimension forbids isomorphism.
    rw [FDRep.finrank_hom_simple_simple (π' i) (π' j)] at hzeroE
    intro he
    rw [if_pos he] at hzeroE
    exact one_ne_zero hzeroE
  -- Step 5: match each `π' i` to a representative in `πE`, giving an injective map `f : ιL → ιE`.
  have hf : ∀ i, ∃ j, Nonempty (π' i ≅ πE j) := fun i =>
    hπE_comp.exists_iso (π' i) (hπ'_simple i)
  let f : ιL → ιE := fun i ↦ (hf i).choose
  have hf_iso : ∀ i, Nonempty (π' i ≅ πE (f i)) := fun i => (hf i).choose_spec
  have hf_inj : Function.Injective f := by
    intro i i' hii'
    by_contra hne
    -- `π' i ≅ πE (f i) = πE (f i') ≅ π' i'`, contradicting pairwise nonisomorphism of `π'`.
    obtain ⟨ei⟩ := hf_iso i
    obtain ⟨ei'⟩ := hf_iso i'
    apply hπ'_pw hne
    exact ⟨ei.trans (eqToIso (congrArg πE hii')) |>.trans ei'.symm⟩
  -- Step 6: an injection between finite types of equal cardinality is surjective.
  have hf_surj : Function.Surjective f := by
    letI : Fintype ιL := Fintype.ofFinite ιL
    letI : Fintype ιE := Fintype.ofFinite ιE
    have hc : Fintype.card ιL = Fintype.card ιE := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard
    exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hc⟩).2
  -- Step 7: locate `T` in `πE`, then pull back to a `π' i = FDRep.scalarExtension (πL i)`.
  obtain ⟨j, ⟨eTj⟩⟩ := hπE_comp.exists_iso T inferInstance
  obtain ⟨i, hij⟩ := hf_surj j
  obtain ⟨eji⟩ := hf_iso i
  -- `T ≅ πE j = πE (f i) ≅ π' i = FDRep.scalarExtension (πL i)`.
  refine ⟨πL i, hπL_comp.isSimple i, ⟨?_⟩⟩
  exact eTj.trans ((eqToIso (congrArg πE hij.symm)).trans eji.symm)

end Representation
