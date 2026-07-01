import Mathlib.RingTheory.Ideal.Cotangent
import stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing

section

/-
Layering for this item:
* source-facing statement: a finite local ring homomorphism is surjective once the induced maps on
  residue fields and cotangent spaces are surjective and the target maximal ideal is finitely
  generated.
* core/canonical owners: `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `ResidueField.map`, and `Ideal.mapCotangent`.
* bridge/view: the residue-field and cotangent-space maps are the quotient maps to which the owner
  Nakayama criterion is applied.
-/

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- Helper for Lemma 10.20.3: the image of the maximal ideal of the source local ring lies in the
maximal ideal of the target local ring. -/
private theorem map_maximalIdeal_le_maximalIdeal :
    Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
  -- A local homomorphism pulls back the target maximal ideal to the source maximal ideal.
  rw [Ideal.map_le_iff_le_comap]
  simpa using le_of_eq (maximalIdeal_comap (algebraMap A B)).symm

/-- Helper for Lemma 10.20.3: cotangent-space surjectivity gives surjectivity of the quotient map
for the inclusion `Ideal.map (algebraMap A B) (maximalIdeal A) ↪ maximalIdeal B`. -/
private theorem map_maximalIdeal_subtype_quotient_surjective_of_cotangent_surjective
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Function.Surjective
      ((Submodule.inclusion (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))).quotientMapByIdeal
        (maximalIdeal B)) := by
  intro x
  obtain ⟨y, hy⟩ := hcot x
  obtain ⟨a, rfl⟩ := (maximalIdeal A).toCotangent_surjective y
  let aI : Ideal.map (algebraMap A B) (maximalIdeal A) :=
    ⟨algebraMap A B a, Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
  refine ⟨Submodule.Quotient.mk aI, ?_⟩
  -- The quotient map is the same canonical cotangent map on representatives.
  have himage :
      (maximalIdeal B).toCotangent
          ⟨algebraMap A B a, map_maximalIdeal_le_maximalIdeal (A := A) (B := B) aI.2⟩ = x := by
    simpa [aI] using
      (Ideal.mapCotangent_toCotangent (I₁ := maximalIdeal A) (I₂ := maximalIdeal B)
        (f := Algebra.ofId A B) (h := (maximalIdeal_comap (algebraMap A B)).symm.le) a).trans hy
  simpa [LinearMap.quotientMapByIdeal, aI] using himage

/-- Helper for Lemma 10.20.3: the cotangent-space hypothesis forces the image of the source
maximal ideal to equal the target maximal ideal. -/
private theorem map_maximalIdeal_eq_maximalIdeal_of_cotangent_surjective
    (hfg : (maximalIdeal B).FG)
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  let ι : Ideal.map (algebraMap A B) (maximalIdeal A) →ₗ[B] maximalIdeal B :=
    Submodule.inclusion (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))
  have hquot : Function.Surjective (ι.quotientMapByIdeal (maximalIdeal B)) :=
    map_maximalIdeal_subtype_quotient_surjective_of_cotangent_surjective
      (A := A) (B := B) hcot
  letI : Module.Finite B (maximalIdeal B) := Module.Finite.of_fg hfg
  have hsurj : Function.Surjective ι := by
    -- Apply Nakayama over `B` to the inclusion of the mapped maximal ideal.
    refine surjective_of_quotientMap_surjective_of_le_ring_jacobson
      (R := B) (I := maximalIdeal B) ι hquot ?_
    simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
      (show maximalIdeal B ≤ maximalIdeal B from le_rfl)
  apply le_antisymm (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  -- Surjectivity of the inclusion means every element of `maximalIdeal B` already comes from the
  -- mapped ideal.
  have hy_val : y.1 = x := congrArg Subtype.val hy
  simpa [hy_val] using y.2

/-- Helper for Lemma 10.20.3: once the mapped maximal ideal is the target maximal ideal, the
quotient map induced by `algebraMap A B` is exactly the residue-field map. -/
private theorem algebraMap_quotient_surjective_of_residueField_surjective_of_map_maximalIdeal_eq
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A B) =
        Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    simp [Ideal.smul_top_eq_map]
  let e₁ :
      (B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) :=
    Submodule.quotEquivOfEq _ _ hsmul
  let e₂ :
      B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) →
        ResidueField B :=
    Ideal.quotEquivOfEq hmap
  have he₂inj : Function.Injective e₂ := (Ideal.quotEquivOfEq hmap).injective
  intro x
  obtain ⟨y, hy⟩ := hres (e₂ (e₁ x))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hquotientMap :
      ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) := by
    rfl
  have htransport :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
    rw [hquotientMap]
    simpa [e₁] using
      (Submodule.quotEquivOfEq_mk hsmul (algebraMap A B a))
  have hleft :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        ResidueField.map (algebraMap A B) (residue A a) := by
    rw [htransport]
    calc
      e₂ (Submodule.Quotient.mk (algebraMap A B a))
        = residue B (algebraMap A B a) := by
            simpa [e₂, IsLocalRing.ResidueField] using
              (Ideal.quotEquivOfEq_mk hmap (algebraMap A B a))
      _ = ResidueField.map (algebraMap A B) (residue A a) := by
            symm
            exact IsLocalRing.ResidueField.map_residue (algebraMap A B) a
  have hy' :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        e₂ (e₁ x) :=
    hleft.trans hy
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  have hquot :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        e₁ x :=
    he₂inj hy'
  -- After transporting the codomain quotient to the residue field of `B`, the induced quotient
  -- map becomes the canonical residue-field map.
  exact e₁.injective hquot

/-- Lemma 10.20.3: a finite local ring homomorphism is surjective if the target maximal ideal is
finitely generated, the induced map on residue fields is surjective, and the induced map on
cotangent spaces `CotangentSpace A → CotangentSpace B`, given by the canonical map
`mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
  (maximalIdeal_comap (algebraMap A B)).symm.le`, is surjective. -/
-- Proof sketch: apply
-- `surjective_of_quotientMap_surjective_of_le_ring_jacobson` from Lemma `10.20.1` to the
-- `A`-linear map `algebraMap A B`; surjectivity on residue fields identifies the needed quotient
-- map with `ResidueField.map (algebraMap A B)`. Apply the same owner theorem again to the induced
-- map `maximalIdeal A →ₗ[A] maximalIdeal B`; the quotient map in this second step is exactly the
-- canonical cotangent map `mapCotangent ...`, and `hfg` supplies the finite-generation input for
-- `maximalIdeal B`.
theorem surjective_of_localHom_finite_surjective_residueFieldMap_surjective_maximalIdealCotangentMap
    (hf : Module.Finite A B) (hfg : (maximalIdeal B).FG)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Function.Surjective (algebraMap A B) := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    map_maximalIdeal_eq_maximalIdeal_of_cotangent_surjective
      (A := A) (B := B) hfg hcot
  have hquot :
      Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) :=
    algebraMap_quotient_surjective_of_residueField_surjective_of_map_maximalIdeal_eq
      (A := A) (B := B) hres hmap
  -- Apply Nakayama over `A` to the structural map `A → B`.
  refine surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (R := A) (I := maximalIdeal A) (Algebra.linearMap A B) hquot ?_
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (show maximalIdeal A ≤ maximalIdeal A from le_rfl)

end
