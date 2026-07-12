import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Definition_18_32_6
import StacksProject_2024.Chap18.Definition_18_40_4
import StacksProject_2024.Chap21.Lemma_21_4_2
import StacksProject_2024.Chap21.Lemma_21_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped RingedSitePicard

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [IsLocallyRingedSite 𝒪]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget AddCommGrpCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasExt (Sheaf J AddCommGrpCat.{u})]
variable [MonoidalCategory (ringedSiteModuleCategory.{u, u, u} J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory.{u, u, u} J 𝒪)]

/- Lemma 21.6.1 is a source-facing existence statement about the comparison between
`H¹(C, 𝒪^*)` and `Pic(𝒪)`. The canonical owners already live upstream:
`ringedSiteUnitsAddSheaf`, `ringedSitePicardGroup`, and the torsor/H¹ bridge from
`abelianSheafTorsor_isoClasses_to_H1`. -/

/-- Helper for Lemma 21.6.1: if a map from `Pic(𝒪)` to isomorphism classes of `𝒪^*`-torsors
sends `0` to the trivial torsor class, then the induced map to `H¹(C, 𝒪^*)` also sends `0`
to `0`. -/
private theorem picardToH1OfTorsorIsoClasses_mapZero
    (f : Pic(𝒪) →
      Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪)))
    (hf_zero :
      f 0 =
        (_root_.Quotient.mk'' <|
          Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪)))) :
    abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f 0) = 0 := by
  -- Proof comment: rewrite the Picard zero class to the trivial torsor class and use the
  -- normalization of `abelianSheafTorsor_isoClasses_to_H1` on the trivial torsor.
  rw [hf_zero]
  simpa using abelianSheafTorsor_isoClasses_to_H1_trivial (ringedSiteUnitsAddSheaf 𝒪)

/-- Helper for Lemma 21.6.1: once the Picard-to-torsor comparison is additive after passing to
`H¹(C, 𝒪^*)`, has trivial kernel on the induced `H¹` map, and is surjective on torsor classes,
it yields the desired additive bijection `Pic(𝒪) → H¹(C, 𝒪^*)`. -/
private theorem picardGroupToUnitsSheafH1_ofKernelZeroAndSurjective
    (f : Pic(𝒪) →
      Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪)))
    (hf_zero :
      f 0 =
        (_root_.Quotient.mk'' <|
          Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))))
    (hf_add :
      ∀ x y : Pic(𝒪),
        abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f (x + y)) =
          abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f x) +
            abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f y))
    (hf_ker :
      ∀ x : Pic(𝒪),
        abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f x) = 0 → x = 0)
    (hf_surj : Function.Surjective f) :
    ∃ e : Pic(𝒪) →+ ((ringedSiteUnitsAddSheaf 𝒪).H 1), Function.Bijective e := by
  let e : Pic(𝒪) →+ ((ringedSiteUnitsAddSheaf 𝒪).H 1) :=
    { toFun := fun x ↦
        abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪) (f x)
      map_zero' := picardToH1OfTorsorIsoClasses_mapZero (J := J) (𝒪 := 𝒪) f hf_zero
      map_add' := hf_add }
  refine ⟨e, ?_⟩
  have htorsorH1 :
      Function.Bijective
        (abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)) :=
    abelianSheafTorsor_isoClasses_to_H1_bijective (ringedSiteUnitsAddSheaf 𝒪)
  constructor
  · intro x y hxy
    -- Proof comment: subtract the two classes and use the assumed kernel-zero property of the
    -- induced `H¹` comparison.
    have hzero : e (x - y) = 0 := by
      calc
        e (x - y) = e x - e y := by rw [map_sub]
        _ = 0 := sub_eq_zero.mpr hxy
    have hxy' : x - y = 0 := hf_ker (x - y) (by simpa [e] using hzero)
    exact sub_eq_zero.mp hxy'
  · intro z
    rcases htorsorH1.2 z with ⟨P, hP⟩
    rcases hf_surj P with ⟨x, rfl⟩
    -- Proof comment: surjectivity factors through the existing bijection from torsor classes to
    -- `H¹(C, 𝒪^*)`.
    exact ⟨x, by simpa [e] using hP⟩

/-- Helper for Lemma 21.6.1: `ringedSitePicardGroup.mk` recovers a Picard class from its chosen
representative. -/
private theorem picardGroup_mk_repr
    (x : Pic(𝒪)) :
    ringedSitePicardGroup.mk J 𝒪
        ((ringedSitePicardGroup.repr J 𝒪 x : ringedSiteModuleCategory.{u, u, u} J 𝒪)) = x := by
  let ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪 := ringedSitePicardGroup.repr J 𝒪 x
  -- Proof comment: `repr` is defined as a canonical representative of the given Picard class, so
  -- `eq_of_repr_iso` reduces the claim to the tautological isomorphism `repr (mk (repr x)) ≅ repr x`.
  have h :
      x = ringedSitePicardGroup.mk J 𝒪 ℒ := by
    apply ringedSitePicardGroup.eq_of_repr_iso J 𝒪
      (x := x) (y := ringedSitePicardGroup.mk J 𝒪 ℒ)
    rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 ℒ with ⟨e⟩
    exact ⟨e.symm⟩
  simpa [ℒ] using h.symm

/-- Helper for Lemma 21.6.1: the forward comparison torsor is the torsor of local sections whose
associated map from `unitModule` is an isomorphism. -/
private noncomputable def unitGeneratorTorsor
    (ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Sheaf.Torsor (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪)) := by
  -- Route correction: the forward bridge is now isolated as the textbook torsor of local
  -- unit-generating sections, rather than being bundled together with zero/additivity/surjectivity.
  -- TODO: define the carrier as the sheaf of sections `s` with `IsIso (ℒ.unitHomEquiv.symm s)`,
  -- use slice-local nonemptiness from the invertible-module cover, and prove the `𝒪^*`-action by
  -- transport through `unitHomEquiv` plus theorem-local terminal-value extensionality.
  sorry

/-- Helper for Lemma 21.6.1: the forward torsor depends only on the isomorphism class of the
invertible module. -/
private theorem unitGeneratorTorsorIsoOfIso
    {ℒ 𝒩 : ringedSiteModuleCategory.{u, u, u} J 𝒪}
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight 𝒩)]
    (e : ℒ ≅ 𝒩) :
    Nonempty
      (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ ≅
        unitGeneratorTorsor (J := J) (𝒪 := 𝒪) 𝒩) := by
  -- Proof comment: transporting a local generating section across `e` preserves the
  -- `unitHomEquiv.symm` isomorphism predicate and intertwines the units action.
  sorry

/-- Helper for Lemma 21.6.1: the forward torsor of the structure module is the trivial units
torsor. -/
private theorem unitGeneratorTorsor_unitModuleIsoTrivial :
    Nonempty
      (unitGeneratorTorsor (J := J) (𝒪 := 𝒪)
          ((unitModule J 𝒪 : ringedSiteModuleCategory.{u, u, u} J 𝒪)) ≅
        Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) := by
  -- Proof comment: the canonical generator `1` of `unitModule J 𝒪` gives the distinguished point
  -- of the trivial units torsor, and local multiplication identifies all other generators with units.
  sorry

/-- Helper for Lemma 21.6.1: a global section of the forward torsor is exactly a global
trivialization of the invertible module. -/
private theorem nonempty_globalSections_unitGeneratorTorsor_iff
    (ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Nonempty ((Sheaf.Γ J (Type u)).obj (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ).carrier) ↔
      Nonempty (((unitModule J 𝒪 : ringedSiteModuleCategory.{u, u, u} J 𝒪)) ≅ ℒ) := by
  -- Proof comment: a global section is a global generator, and `unitHomEquiv.symm` turns that
  -- generator into the corresponding global isomorphism from `unitModule J 𝒪`.
  sorry

/-- Helper for Lemma 21.6.1: tensoring local generators adds the corresponding torsor classes in
`H¹(C, 𝒪^*)`. -/
private theorem unitGeneratorTorsor_tensor_h1
    (ℒ 𝒩 : ringedSiteModuleCategory.{u, u, u} J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight 𝒩)]
    [Functor.IsEquivalence (tensorRight (ℒ ⊗ 𝒩))] :
    abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
        (_root_.Quotient.mk'' (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) (ℒ ⊗ 𝒩))) =
      abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
          (_root_.Quotient.mk'' (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ)) +
        abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
          (_root_.Quotient.mk'' (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) 𝒩)) := by
  -- Proof comment: on a common refinement, tensoring two local generators multiplies the units
  -- cocycles, so the torsor classes add after the existing torsor-to-`H¹` comparison.
  sorry

/-- Helper for Lemma 21.6.1: every units torsor comes from the forward torsor of an associated
invertible module. -/
private theorem associatedModuleOfUnitsTorsor_spec
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) :
    ∃ (ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪) (_hℒ : Functor.IsEquivalence (tensorRight ℒ)),
      Nonempty (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ ≅ P) := by
  -- Proof comment: the associated module is the sheafification of `(P × 𝒪)/𝒪^*`, and a chosen
  -- local section of `P` identifies it locally with `unitModule`, giving both invertibility and
  -- recovery of the original torsor.
  sorry

/-- Helper for Lemma 21.6.1: the Picard-to-torsor comparison is the isomorphism class of the
forward torsor attached to the canonical representative of a Picard class. -/
private noncomputable def picardToUnitsTorsorIsoClasses :
    Pic(𝒪) →
      Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪)) :=
  fun x ↦
    _root_.Quotient.mk'' <|
      unitGeneratorTorsor (J := J) (𝒪 := 𝒪)
        ((ringedSitePicardGroup.repr J 𝒪 x : ringedSiteModuleCategory.{u, u, u} J 𝒪))

/-- Helper for Lemma 21.6.1: the canonical Picard-to-units-torsor comparison sends the neutral
Picard class to the trivial units torsor class. -/
private theorem picardToUnitsTorsorIsoClasses_mapZero :
    picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) 0 =
      (_root_.Quotient.mk'' <|
        Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) := by
  let ℒ₀ : ringedSiteModuleCategory.{u, u, u} J 𝒪 := ringedSitePicardGroup.repr J 𝒪 0
  have hrepr0 :
      Nonempty (ℒ₀ ≅ (unitModule J 𝒪 : ringedSiteModuleCategory.{u, u, u} J 𝒪)) := by
    -- Proof comment: `repr 0` is the representative of the Picard class of `unitModule J 𝒪`.
    simpa [ringedSitePicardGroup.mk_unit J 𝒪] using
      (ringedSitePicardGroup.repr_mk_iso J 𝒪 (unitModule J 𝒪))
  rcases hrepr0 with ⟨e₀⟩
  rcases unitGeneratorTorsorIsoOfIso (J := J) (𝒪 := 𝒪) e₀ with ⟨eGen⟩
  rcases unitGeneratorTorsor_unitModuleIsoTrivial (J := J) (𝒪 := 𝒪) with ⟨eTriv⟩
  -- Proof comment: equality in torsor isomorphism classes is witnessed by the composite
  -- `unitGeneratorTorsor (repr 0) ≅ trivial`.
  exact Quotient.sound ⟨eGen ≪≫ eTriv⟩

/-- Helper for Lemma 21.6.1: after passing from units torsors to `H¹(C, 𝒪^*)`, the canonical
Picard-to-torsor comparison is additive. -/
private theorem picardToUnitsH1_mapAdd
    (x y : Pic(𝒪)) :
    abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
        (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) (x + y)) =
      abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
          (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) x) +
        abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
          (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) y) := by
  let ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪 := ringedSitePicardGroup.repr J 𝒪 x
  let 𝒩 : ringedSiteModuleCategory.{u, u, u} J 𝒪 := ringedSitePicardGroup.repr J 𝒪 y
  have hmkTensor : ringedSitePicardGroup.mk J 𝒪 (ℒ ⊗ 𝒩) = x + y := by
    -- Proof comment: Picard addition is induced by tensor product of representatives.
    rw [ringedSitePicardGroup.mk_tensor J 𝒪 ℒ 𝒩,
      picardGroup_mk_repr (J := J) (𝒪 := 𝒪) x,
      picardGroup_mk_repr (J := J) (𝒪 := 𝒪) y]
  have hreprTensor : Nonempty (ringedSitePicardGroup.repr J 𝒪 (x + y) ≅ ℒ ⊗ 𝒩) := by
    -- Proof comment: `repr (x + y)` is the representative of the tensor-product class.
    simpa [ℒ, 𝒩, hmkTensor] using
      (ringedSitePicardGroup.repr_mk_iso J 𝒪 (ℒ ⊗ 𝒩))
  rcases hreprTensor with ⟨eTensor⟩
  rcases unitGeneratorTorsorIsoOfIso (J := J) (𝒪 := 𝒪) eTensor with ⟨eGen⟩
  have hclass :
      picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) (x + y) =
        (_root_.Quotient.mk'' <| unitGeneratorTorsor (J := J) (𝒪 := 𝒪) (ℒ ⊗ 𝒩)) := by
    -- Proof comment: the quotient class only depends on the isomorphism type of the representative.
    exact Quotient.sound ⟨eGen⟩
  -- Route correction: the remaining additivity work is now isolated in the theorem-local helper
  -- `unitGeneratorTorsor_tensor_h1` on invertible modules.
  rw [hclass]
  exact unitGeneratorTorsor_tensor_h1 (J := J) (𝒪 := 𝒪) ℒ 𝒩

/-- Helper for Lemma 21.6.1: the induced Picard-to-`H¹` comparison has trivial kernel. -/
private theorem picardToUnitsH1_kernelZero
    (x : Pic(𝒪))
    (hx :
      abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
        (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) x) = 0) :
    x = 0 := by
  have hclass :
      picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) x =
        (_root_.Quotient.mk'' <|
          Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) := by
    -- Proof comment: the torsor class is trivial because the torsor-to-`H¹` comparison is injective.
    apply (abelianSheafTorsor_isoClasses_to_H1_bijective (ringedSiteUnitsAddSheaf 𝒪)).1
    calc
      abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
          (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪) x) = 0 := hx
      _ = abelianSheafTorsor_isoClasses_to_H1 (ringedSiteUnitsAddSheaf 𝒪)
            (_root_.Quotient.mk'' <|
              Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) := by
          symm
          exact abelianSheafTorsor_isoClasses_to_H1_trivial (ringedSiteUnitsAddSheaf 𝒪)
  let ℒ : ringedSiteModuleCategory.{u, u, u} J 𝒪 := ringedSitePicardGroup.repr J 𝒪 x
  have htriv :
      Nonempty
        (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ ≅
          Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups (ringedSiteUnitsAddSheaf 𝒪))) :=
    Quotient.exact hclass
  have hsections :
      Nonempty ((Sheaf.Γ J (Type u)).obj
        (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ).carrier) := by
    -- Proof comment: a torsor is trivial exactly when it has a global section.
    exact (Sheaf.Torsor.isTrivial_iff_nonempty_globalSections
      (unitGeneratorTorsor (J := J) (𝒪 := 𝒪) ℒ)).1 htriv
  have hreprUnit :
      Nonempty ((unitModule J 𝒪 : ringedSiteModuleCategory.{u, u, u} J 𝒪) ≅ ℒ) := by
    -- Proof comment: the forward torsor bridge turns a global generator into a global trivialization.
    exact (nonempty_globalSections_unitGeneratorTorsor_iff
      (J := J) (𝒪 := 𝒪) ℒ).1 hsections
  have hreprZero : ringedSitePicardGroup.mk J 𝒪 ℒ = 0 := by
    -- Proof comment: a representative is zero in Picard exactly when it is isomorphic to `unitModule`.
    exact (ringedSitePicardGroup.mk_eq_zero_iff J 𝒪 ℒ).2 <| by
      rcases hreprUnit with ⟨e⟩
      exact ⟨e.symm⟩
  -- Proof comment: `ringedSitePicardGroup.mk` of the chosen representative recovers the original class.
  simpa [picardGroup_mk_repr (J := J) (𝒪 := 𝒪) x, ℒ] using hreprZero

/-- Helper for Lemma 21.6.1: the canonical Picard-to-units-torsor comparison is surjective on
isomorphism classes of units torsors. -/
private theorem picardToUnitsTorsorIsoClasses_surjective :
    Function.Surjective (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪)) := by
  intro c
  refine _root_.Quotient.inductionOn c ?_
  intro P
  rcases associatedModuleOfUnitsTorsor_spec (J := J) (𝒪 := 𝒪) P with ⟨ℒ, hℒ, hP⟩
  let _ : Functor.IsEquivalence (tensorRight ℒ) := hℒ
  rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 ℒ with ⟨eRepr⟩
  rcases unitGeneratorTorsorIsoOfIso (J := J) (𝒪 := 𝒪) eRepr with ⟨eGen⟩
  rcases hP with ⟨eP⟩
  -- Proof comment: the associated module produces a representative whose forward torsor is
  -- isomorphic to `P`, so their quotient classes agree.
  refine ⟨ringedSitePicardGroup.mk J 𝒪 ℒ, ?_⟩
  exact Quotient.sound ⟨eGen ≪≫ eP⟩

/-- Helper for Lemma 21.6.1: the missing source-faithful bridge is an additive comparison from
`Pic(𝒪)` to `H¹(C, 𝒪^*)`, built from the units torsor attached to an invertible module. -/
theorem picardGroupToUnitsSheafH1 :
    ∃ e : Pic(𝒪) →+ ((ringedSiteUnitsAddSheaf 𝒪).H 1), Function.Bijective e := by
  -- Proof comment: the final reduction now asks only for zero normalization, additivity, kernel
  -- zero on the induced `H¹` map, and surjectivity on torsor classes.
  refine picardGroupToUnitsSheafH1_ofKernelZeroAndSurjective (J := J) (𝒪 := 𝒪)
    (picardToUnitsTorsorIsoClasses (J := J) (𝒪 := 𝒪))
    (picardToUnitsTorsorIsoClasses_mapZero (J := J) (𝒪 := 𝒪))
    (picardToUnitsH1_mapAdd (J := J) (𝒪 := 𝒪))
    (picardToUnitsH1_kernelZero (J := J) (𝒪 := 𝒪))
    (picardToUnitsTorsorIsoClasses_surjective (J := J) (𝒪 := 𝒪))

/-- Lemma 21.6.1: for a locally ringed site `(C, 𝒪)`, there exists a bijective additive
comparison map from the first cohomology of the units sheaf `𝒪^*` to the Picard group
`Pic(𝒪)`. -/
@[stacks 040E]
theorem ringedSiteUnitsSheaf_H1_equiv_picardGroup :
    ∃ e : ((ringedSiteUnitsAddSheaf 𝒪).H 1) →+ Pic(𝒪), Function.Bijective e := by
  rcases picardGroupToUnitsSheafH1 (J := J) (𝒪 := 𝒪) with ⟨ePic, hePic⟩
  let ePic' : Pic(𝒪) ≃+ ((ringedSiteUnitsAddSheaf 𝒪).H 1) :=
    AddEquiv.ofBijective ePic hePic
  -- Proof comment: invert the additive equivalence coming from the Picard-to-`H¹` comparison.
  refine ⟨ePic'.symm.toAddMonoidHom, ?_⟩
  exact ePic'.symm.bijective

end
