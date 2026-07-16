import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_127_3
import stacks_proof.stacks_project.Chap10.Lemma_10_143_8
import stacks_proof.stacks_project.Chap15.Lemma_15_105_4
import stacks_proof.stacks_project.Chap15.Lemma_15_105_5
import stacks_proof.stacks_project.Chap15.Lemma_15_105_15
import stacks_proof.stacks_project.Chap15.Lemma_15_105_16
import stacks_proof.stacks_project.Chap15.Lemma_15_106_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open CategoryTheory
open CategoryTheory.Limits

section

open scoped IntermediateField
open scoped TensorProduct
open scoped MaximalWeaklyEtaleSubalgebraNotation

variable {K : Type u} [Field K]
variable {A' : Type v} [CommRing A'] [Algebra K A']
variable {A : Type w} [CommRing A] [Algebra K A]

local notation "A_red" => A ⧸ nilradical A
local notation "B_red" => B_max(A_red⁄K)

/-- Helper for Lemma 15.106.3: transporting an algebra across an equivalence identifies the
tensor-square multiplication map with the transported multiplication on the target. -/
theorem tensorSquareMul_eq_of_algEquiv
    {B : Type*} [CommRing B] [Algebra K B]
    {C : Type*} [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C) :
    let eTensor : C ⊗[K] C ≃ₐ[K] B ⊗[K] B := Algebra.TensorProduct.congr e.symm e.symm
    ((e.toAlgHom).comp
        ((Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).comp eTensor.toAlgHom)).toRingHom =
      (Algebra.TensorProduct.lmul' K : C ⊗[K] C →ₐ[K] C).toRingHom := by
  let eTensor : C ⊗[K] C ≃ₐ[K] B ⊗[K] B := Algebra.TensorProduct.congr e.symm e.symm
  let g : C ⊗[K] C →ₐ[K] C :=
    (e.toAlgHom).comp ((Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).comp eTensor.toAlgHom)
  -- The transported multiplication agrees with the canonical one on the left tensor generators.
  have hleft :
      g.comp (Algebra.TensorProduct.includeLeft : C →ₐ[K] C ⊗[K] C) =
        (Algebra.TensorProduct.lmul' K : C ⊗[K] C →ₐ[K] C).comp
          (Algebra.TensorProduct.includeLeft : C →ₐ[K] C ⊗[K] C) := by
    ext x
    simp [g, eTensor]
  -- The same comparison on the right tensor generators identifies the full map.
  have hright :
      (AlgHom.restrictScalars K g).comp (Algebra.TensorProduct.includeRight : C →ₐ[K] C ⊗[K] C) =
        (AlgHom.restrictScalars K (Algebra.TensorProduct.lmul' K : C ⊗[K] C →ₐ[K] C)).comp
          (Algebra.TensorProduct.includeRight : C →ₐ[K] C ⊗[K] C) := by
    ext x
    simp [g, eTensor]
  have hg :
      g = (Algebra.TensorProduct.lmul' K : C ⊗[K] C →ₐ[K] C) :=
    Algebra.TensorProduct.ext hleft hright
  simpa [g] using congrArg AlgHom.toRingHom hg

/-- Helper for Lemma 15.106.3: weak étaleness is preserved by `K`-algebra equivalences. -/
theorem isWeaklyEtale_of_algEquiv
    {B : Type*} [CommRing B] [Algebra K B]
    {C : Type*} [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C)
    (hB : Algebra.IsWeaklyEtale K B) :
    Algebra.IsWeaklyEtale K C := by
  refine
    { moduleFlat := by
        -- Flatness of the structure map transports along the underlying linear equivalence.
        exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
      flat_tensorSquareMultiplication := by
        let eTensor : C ⊗[K] C ≃ₐ[K] B ⊗[K] B := Algebra.TensorProduct.congr e.symm e.symm
        let g : C ⊗[K] C →ₐ[K] C :=
          (e.toAlgHom).comp
            ((Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).comp eTensor.toAlgHom)
        -- Transport flatness first across the tensor-square equivalence and then across `e`.
        have heTensorFlat : eTensor.toRingHom.Flat := RingHom.Flat.of_bijective eTensor.bijective
        have hmulFlat :
            ((Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).toRingHom).Flat :=
          hB.flat_tensorSquareMultiplication
        have heFlat : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
        have hgFlat : g.toRingHom.Flat := by
          have hcomp₁ :
              (((Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).toRingHom).comp
                eTensor.toRingHom).Flat :=
            RingHom.Flat.comp heTensorFlat hmulFlat
          simpa [g] using RingHom.Flat.comp hcomp₁ heFlat
        have hg :
            g.toRingHom =
              (Algebra.TensorProduct.lmul' K : C ⊗[K] C →ₐ[K] C).toRingHom := by
          simpa [g, eTensor] using tensorSquareMul_eq_of_algEquiv (K := K) e
        rw [hg] at hgFlat
        simpa [RingHom.algebraMap_toAlgebra] using hgFlat }

/-- Helper for Lemma 15.106.3: an injective map from a weakly étale `K`-algebra has weakly étale
range. -/
theorem isWeaklyEtale_range_of_injective
    {B : Type*} [CommRing B] [Algebra K B]
    {C : Type*} [CommRing C] [Algebra K C]
    (f : B →ₐ[K] C)
    (hf : Function.Injective f)
    (hB : Algebra.IsWeaklyEtale K B) :
    Algebra.IsWeaklyEtale K f.range := by
  let e : B ≃ₐ[K] f.range :=
    AlgEquiv.ofBijective f.rangeRestrict
      ⟨fun x y hxy ↦ hf (congrArg Subtype.val hxy), fun y ↦ by
        rcases y with ⟨y, hy⟩
        rcases hy with ⟨x, rfl⟩
        exact ⟨x, rfl⟩⟩
  -- The range is algebra-isomorphic to the source, so weak étaleness transfers across `e`.
  simpa [e] using isWeaklyEtale_of_algEquiv (K := K) e hB

/-- Helper for Lemma 15.106.3: every étale `K`-algebra is weakly étale over `K`. -/
theorem isWeaklyEtale_of_etale
    {B : Type*} [CommRing B] [Algebra K B]
    [Algebra.Etale K B] :
    Algebra.IsWeaklyEtale K B := by
  refine
    { moduleFlat := by
        infer_instance
      flat_tensorSquareMultiplication := by
        let _ : Algebra B (B ⊗[K] B) := Algebra.TensorProduct.leftAlgebra
        let _ : Algebra K (B ⊗[K] B) := Algebra.TensorProduct.leftAlgebra
        let _ : Algebra.Etale B (B ⊗[K] B) := inferInstance
        let _ : Algebra.Etale K (B ⊗[K] B) :=
          Algebra.Etale.comp (R := K) (A := B) (B := B ⊗[K] B)
        let _ : Algebra (B ⊗[K] B) B := (Algebra.TensorProduct.lmul' K).toAlgebra
        let _ : Algebra.Etale (B ⊗[K] B) B := Algebra.etale_of_etale_over_common_base
        have halg : (algebraMap (B ⊗[K] B) B).Flat := by
          exact RingHom.flat_algebraMap_iff.mpr inferInstance
        simpa [RingHom.algebraMap_toAlgebra] using halg }

/-- Helper for Lemma 15.106.3: over a field, quotients of étale algebras are again étale. -/
theorem etale_quotient_of_etale_over_field
    {S : Type*} [CommRing S] [Algebra K S]
    [Algebra.Etale K S] (I : Ideal S) :
    Algebra.Etale K (S ⧸ I) := by
  let _ : Algebra.FiniteType K S := inferInstance
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  let _ : Algebra.FormallyUnramified K (S ⧸ I) := inferInstance
  let _ : Algebra.FinitePresentation K (S ⧸ I) :=
    Algebra.FinitePresentation.quotient hIfg
  -- Route correction: package the same source quotient-step through the canonical mathlib owners
  -- `FormallyUnramified` and `FinitePresentation` over the field `K`.
  exact Algebra.Etale.of_formallyUnramified_of_flat

/- Domain-style sampling for Lemma 15.106.3:
- primary domain: functoriality and permanence of the owner subalgebra `B_max(A⁄K)` under
  `K`-algebra maps, filtered colimits, reduction, and finite products;
- sampled owner declarations:
  `maximalWeaklyEtaleSubalgebra`,
  `le_maximalWeaklyEtaleSubalgebra`,
  `CommAlgCat`,
  `PreservesFilteredColimits`,
  `Subalgebra.map`,
  `Subalgebra.comap`,
  `Algebra.IsSeparable`,
  `Algebra.IsSeparable.isAlgebraic`;
- best owner abstraction: `B_max(A⁄K)` from `Lemma_15_106_2` is the primitive source-facing
  object, and the filtered-colimit clause `(3)` is best expressed by the induced endofunctor on
  `CommAlgCat K`; the directed-union equality inside a fixed ambient algebra is a bridge/view
  specialization of that owner-level statement;
- layer triage:
  part `(1)` is `bridge/view`,
  part `(3)` is `source-facing` at the functorial filtered-colimit level and only secondarily a
  directed-subalgebra specialization,
  parts `(2)` and `(4)` through `(7)` remain source-facing consequences about the same owner;
- primitive vs. derived:
  the primitive data here is still only the owner subalgebra `B_max`; containment of its image,
  the induced `CommAlgCat` endofunctor, its filtered-colimit preservation, reduction maps, and
  field/separability consequences are derived API.

This file should therefore keep the image statement as the owner-level subalgebra inequality,
package it into the canonical endofunctor on `CommAlgCat K`, and state filtered-colimit
compatibility through `PreservesFilteredColimits` before specializing to directed unions inside a
fixed ambient algebra.
-/

namespace AlgHom

-- Proof sketch: control the image of a singleton-generated étale stage inside `B_max(A')`,
-- pass to its kernel quotient and then to its range in `A`, and use maximality of `B_max(A)` on
-- that weakly étale range stage.
/-- The image of the maximal weakly étale `K`-subalgebra under a `K`-algebra map is contained in
the maximal weakly étale `K`-subalgebra of the target. -/
theorem map_maximalWeaklyEtaleSubalgebra_le
    (f : A' →ₐ[K] A) :
    (B_max(A'⁄K)).map f ≤ B_max(A⁄K) := by
  let _ : Algebra.IsWeaklyEtale K B_max(A'⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A')
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  let x' : B_max(A'⁄K) := ⟨x, hx⟩
  let S : Subalgebra K B_max(A'⁄K) := Algebra.adjoin K ({x'} : Set B_max(A'⁄K))
  let xS : S := ⟨x', Algebra.subset_adjoin (by simp)⟩
  have hSfg : S.FG := by
    rw [Subalgebra.fg_iff_finiteType S]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x')
  -- The source-faithful controlled object is the singleton-generated stage inside `B_max(A')`.
  have hSet : Algebra.Etale K S :=
    etale_of_fg_subalgebra_of_isWeaklyEtale S hSfg
  let g₀ : B_max(A'⁄K) →ₐ[K] A := f.comp B_max(A'⁄K).val
  let g : S →ₐ[K] A := g₀.comp S.val
  have hquot : Algebra.Etale K (S ⧸ RingHom.ker g.toRingHom) :=
    etale_quotient_of_etale_over_field (K := K) (S := S) (RingHom.ker g.toRingHom)
  have hrangeWeak : Algebra.IsWeaklyEtale K g.range := by
    let e : (S ⧸ RingHom.ker g.toRingHom) ≃ₐ[K] g.range := Ideal.quotientKerEquivRange g
    let _ : Algebra.Etale K (S ⧸ RingHom.ker g.toRingHom) := hquot
    have hquotWeak : Algebra.IsWeaklyEtale K (S ⧸ RingHom.ker g.toRingHom) :=
      isWeaklyEtale_of_etale (K := K)
    -- The quotient-to-range bridge is exactly the first isomorphism theorem for `g`.
    exact isWeaklyEtale_of_algEquiv (K := K) e hquotWeak
  have hle : g.range ≤ B_max(A⁄K) :=
    le_maximalWeaklyEtaleSubalgebra (K := K) (A := A) g.range hrangeWeak
  -- The chosen generator lands in the weakly étale range stage, hence in `B_max(A)`.
  change g xS ∈ B_max(A⁄K)
  exact hle ⟨xS, rfl⟩

/-- An element of `B_max(A'/K)` maps into `B_max(A/K)` under any `K`-algebra map `A' → A`. -/
theorem map_maximalWeaklyEtaleSubalgebra_mem
    (f : A' →ₐ[K] A) (x : B_max(A'⁄K)) :
    f x ∈ B_max(A⁄K) :=
  map_maximalWeaklyEtaleSubalgebra_le f <|
    show f x ∈ (B_max(A'⁄K)).map f from ⟨x, x.2, rfl⟩

/-- Lemma 15.106.3 (1): any `K`-algebra map `A' → A` induces a `K`-algebra map
`B_max(A') → B_max(A)`. -/
@[stacks 0CKT]
def maximalWeaklyEtaleSubalgebraMap
    (f : A' →ₐ[K] A) :
    B_max(A'⁄K) →ₐ[K] B_max(A⁄K) :=
  (f.comp B_max(A'⁄K).val).codRestrict B_max(A⁄K)
    (map_maximalWeaklyEtaleSubalgebra_mem f)

/-- The induced map on maximal weakly étale subalgebras agrees with the ambient algebra map. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraMap_apply
    (f : A' →ₐ[K] A) (x : B_max(A'⁄K)) :
    ↑(maximalWeaklyEtaleSubalgebraMap f x) = f x := rfl

end AlgHom

/-- The maximal weakly étale subalgebra construction as an endofunctor on `K`-algebras. -/
def maximalWeaklyEtaleSubalgebraFunctor (K : Type u) [Field K] :
    CommAlgCat K ⥤ CommAlgCat K where
  obj A := CommAlgCat.of K B_max(A⁄K)
  map f := CommAlgCat.ofHom <| AlgHom.maximalWeaklyEtaleSubalgebraMap f.hom
  map_id A := by
    apply CommAlgCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    ext x
    rfl

-- Proof sketch: the inclusion `A' ↪ A` gives the forward containment by part `(1)`. For the
-- reverse containment, the preimage `(B_max(A)).comap i` is weakly étale over `K`, so maximality
-- of `B_max(A')` forces equality.
/-- Lemma 15.106.3 (2): if `A'` is identified with a `K`-subalgebra of `A`, then `B_max(A')`
is the intersection `B_max(A) ∩ A'`, written as a comap. -/
@[stacks 0CKT]
theorem maximalWeaklyEtaleSubalgebra_comap_of_injective
    (i : A' →ₐ[K] A) (hi : Function.Injective i) :
    B_max(A'⁄K) = (B_max(A⁄K)).comap i := by
  let hsource' : Algebra.IsWeaklyEtale K B_max(A'⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A')
  let hsource : Algebra.IsWeaklyEtale K B_max(A⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A)
  apply le_antisymm
  · intro x hx
    let g : B_max(A'⁄K) →ₐ[K] A := i.comp B_max(A'⁄K).val
    have hg_inj : Function.Injective g := by
      intro x y hxy
      exact Subtype.ext <| hi hxy
    -- The injective image of `B_max(A')` is weakly étale, so maximality places it in `B_max(A)`.
    have hrange : Algebra.IsWeaklyEtale K g.range :=
      isWeaklyEtale_range_of_injective (K := K) g hg_inj hsource'
    have hle : g.range ≤ B_max(A⁄K) :=
      le_maximalWeaklyEtaleSubalgebra (K := K) (A := A) g.range hrange
    change i x ∈ B_max(A⁄K)
    exact hle ⟨⟨x, hx⟩, rfl⟩
  · intro y hy
    let S : Subalgebra K A' := Algebra.adjoin K ({y} : Set A')
    let T : Subalgebra K A := Algebra.adjoin K ({i y} : Set A)
    let T' : Subalgebra K B_max(A⁄K) := Algebra.adjoin K ({⟨i y, hy⟩} : Set B_max(A⁄K))
    have hyS : y ∈ S := by
      exact Algebra.subset_adjoin (by simp)
    have hT'fg : T'.FG := by
      rw [Subalgebra.fg_iff_finiteType T']
      exact Algebra.FiniteType.adjoin_of_finite
        (Set.finite_singleton (⟨i y, hy⟩ : B_max(A⁄K)))
    -- The singleton-generated stage inside `B_max(A)` is étale by the finite-stage theorem.
    have hT'et : Algebra.Etale K T' :=
      etale_of_fg_subalgebra_of_isWeaklyEtale T' hT'fg
    have hT'map : T'.map B_max(A⁄K).val = T := by
      simpa [T', T] using
        (AlgHom.map_adjoin_singleton (R := K) (e := B_max(A⁄K).val) ⟨i y, hy⟩)
    have eT : T' ≃ₐ[K] T := by
      let eT₀ : T' ≃ₐ[K] T'.map B_max(A⁄K).val :=
        Subalgebra.equivMapOfInjective T' B_max(A⁄K).val Subtype.val_injective
      exact hT'map ▸ eT₀
    have hTet : Algebra.Etale K T := by
      let _ : Algebra.Etale K T' := hT'et
      -- Forgetting from `B_max(A)` to `A` does not change the singleton-generated stage.
      exact Algebra.Etale.of_equiv eT
    have hSmap : S.map i = T := by
      simpa [S, T] using (AlgHom.map_adjoin_singleton (R := K) (e := i) y)
    have eS : S ≃ₐ[K] T := by
      let eS₀ : S ≃ₐ[K] S.map i := Subalgebra.equivMapOfInjective S i hi
      exact hSmap ▸ eS₀
    have hSet : Algebra.Etale K S := by
      let _ : Algebra.Etale K T := hTet
      -- Route correction: pull étaleness back from the image stage instead of asking for a
      -- general weakly-étale subalgebra permanence theorem.
      exact Algebra.Etale.of_equiv eS.symm
    have hSweak : Algebra.IsWeaklyEtale K S := by
      let _ : Algebra.Etale K S := hSet
      exact isWeaklyEtale_of_etale (K := K)
    -- Maximality of `B_max(A')` now applies to the singleton-generated weakly étale stage.
    exact le_maximalWeaklyEtaleSubalgebra (K := K) (A := A') S hSweak hyS

/-- Helper for Lemma 15.106.3: over a field, a weakly étale algebra is absolutely flat. -/
lemma isAbsolutelyFlatRing_of_isWeaklyEtale_over_field
    {B : Type v} [CommRing B] [Algebra K B]
    (hKB : Algebra.IsWeaklyEtale K B) :
    IsAbsolutelyFlatRing B := by
  letI : HasWeakDimensionLE K 0 := hasWeakDimensionLEZero_of_isAbsolutelyFlatRing K
  letI : HasWeakDimensionLE B 0 := hasWeakDimensionLE_of_isWeaklyEtale K B 0 hKB
  -- Weak dimension `≤ 0` is the chapter-level criterion for absolute flatness.
  exact isAbsolutelyFlatRing_of_hasWeakDimensionLEZero B

/-- Helper for Lemma 15.106.3: an absolutely flat ring with only trivial idempotents is a field. -/
lemma isField_of_idempotents_trivial_of_isAbsolutelyFlatRing
    {R : Type v} [CommRing R] [Nontrivial R] [IsAbsolutelyFlatRing R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField R := by
  let hlocal : IsLocalRing R := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    obtain ⟨b, hx⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) x
    have he : IsIdempotentElem (x * b) := by
      calc
        (x * b) * (x * b) = (x ^ 2 * b) * b := by ring
        _ = x * b := by rw [← hx]
    rcases hidem (x * b) he with hxb0 | hxb1
    · right
      have hx0 : x = 0 := by
        calc
          x = x ^ 2 * b := hx
          _ = x * (x * b) := by ring
          _ = 0 := by simp [hxb0]
      simp [hx0]
    · left
      exact ⟨⟨x, b, hxb1, by simpa [mul_comm] using hxb1⟩, rfl⟩
  let _ : IsLocalRing R := hlocal
  -- The local absolutely-flat criterion upgrades the factorization axiom to a field structure.
  exact isField_of_localRing_exists_factor (R := R) fun r ↦
    IsAbsolutelyFlatRing.exists_factor (A := R) r

/-- Helper for Lemma 15.106.3: flat tensor-square multiplication over a field implies
separability, without requiring the base field and the extension to live in the same universe. -/
lemma isSeparable_of_flat_tensorSquareMultiplication_aux
    {L : Type w} [Field L] [Algebra K L]
    (hflat : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).Flat) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x ↦ ?_⟩
  let M : IntermediateField K L := K⟮x⟯
  letI : Algebra M L := M.val.toAlgebra
  letI : IsScalarTower K M L := inferInstance
  have hML : (algebraMap M L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMflat : (Algebra.TensorProduct.lmul' K : M ⊗[K] M →ₐ[K] M).Flat :=
    Algebra.tensorSquareMul_flat_of_faithfullyFlat hML hflat
  letI : Algebra.FormallyUnramified K M :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hMflat
  letI : Algebra.EssFiniteType K M := (IntermediateField.essFiniteType_iff).2 <| by
    simpa [M] using IntermediateField.fg_adjoin_finset ({x} : Finset L)
  have hsep : Algebra.IsSeparable K M := Algebra.FormallyUnramified.isSeparable K M
  -- The simple intermediate field `K⟮x⟯` captures separability of the chosen element.
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
    (F := K) (E := L) (x := x)).mp <| by
    simpa [M] using hsep

/-- Helper for Lemma 15.106.3: the stagewise inclusion `B_max(F.obj j) → c.pt` attached to a
`CommAlgCat K` cocone. -/
def maximalWeaklyEtaleSubalgebraToAmbient
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (j : J) :
    B_max(F.obj j⁄K) →ₐ[K] c.pt :=
  (c.ι.app j).hom.comp (B_max(F.obj j⁄K)).val

/-- Helper for Lemma 15.106.3: the stagewise map `B_max(F.obj j) → B_max(c.pt)` induced by the
ambient cocone leg. -/
def maximalWeaklyEtaleSubalgebraComparisonStageMap
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (j : J) :
    B_max(F.obj j⁄K) →ₐ[K] B_max(c.pt⁄K) :=
  AlgHom.maximalWeaklyEtaleSubalgebraMap ((c.ι.app j).hom)

/-- Helper for Lemma 15.106.3: the ambient stage map is the underlying inclusion of the induced
stagewise comparison map into `B_max(c.pt)`. -/
theorem maximalWeaklyEtaleSubalgebraToAmbient_eq_val_comp_stageComparison
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (j : J) :
    maximalWeaklyEtaleSubalgebraToAmbient (K := K) F c j =
      (B_max(c.pt⁄K)).val.comp
        (maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j) := by
  rfl

/-- Helper for Lemma 15.106.3: the ambient stage maps satisfy the cocone naturality relation after
applying the `B_max` functor. -/
theorem maximalWeaklyEtaleSubalgebraToAmbient_naturality
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F)
    {j j' : J} (f : j ⟶ j') :
    (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K).map f ≫
        CommAlgCat.ofHom (maximalWeaklyEtaleSubalgebraToAmbient (K := K) F c j') =
      CommAlgCat.ofHom (maximalWeaklyEtaleSubalgebraToAmbient (K := K) F c j) := by
  -- Evaluate the two morphisms on an element and reduce to the cocone relation in `F`.
  apply CommAlgCat.hom_ext
  ext x
  change ((c.ι.app j').hom) (((F.map f).hom) x.1) = ((c.ι.app j).hom) x.1
  exact congrArg (fun g : F.obj j ⟶ c.pt ↦ g.hom x.1) (c.w f)

/-- Helper for Lemma 15.106.3: the induced stagewise maps to `B_max(c.pt)` satisfy the cocone
naturality relation. -/
theorem maximalWeaklyEtaleSubalgebraComparisonStageMap_naturality
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F)
    {j j' : J} (f : j ⟶ j') :
    (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K).map f ≫
        CommAlgCat.ofHom
          (maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j') =
      CommAlgCat.ofHom
        (maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j) := by
  -- Compare the two maps after composing with the inclusion into the ambient colimit point.
  apply CommAlgCat.hom_ext
  ext x
  change ((c.ι.app j').hom) (((F.map f).hom) x.1) = ((c.ι.app j).hom) x.1
  exact congrArg (fun g : F.obj j ⟶ c.pt ↦ g.hom x.1) (c.w f)

/-- Helper for Lemma 15.106.3: the stagewise inclusions into the ambient cocone assemble to a
cocone on the `B_max` diagram. -/
def maximalWeaklyEtaleSubalgebraAmbientCocone
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) :
    Cocone (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K) where
  pt := c.pt
  ι :=
    { app := fun j ↦
        CommAlgCat.ofHom (maximalWeaklyEtaleSubalgebraToAmbient (K := K) F c j)
      naturality := by
        intro X Y f
        simpa using
          maximalWeaklyEtaleSubalgebraToAmbient_naturality (K := K) F c f }

/-- Helper for Lemma 15.106.3: the stagewise maps into `B_max(c.pt)` assemble to the comparison
cocone used in the filtered-colimit argument. -/
def maximalWeaklyEtaleSubalgebraComparisonCocone
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) :
    Cocone (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K) where
  pt := CommAlgCat.of K B_max(c.pt⁄K)
  ι :=
    { app := fun j ↦
        CommAlgCat.ofHom
          (maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j)
      naturality := by
        intro X Y f
        simpa using
          maximalWeaklyEtaleSubalgebraComparisonStageMap_naturality (K := K) F c f }

/-- Helper for Lemma 15.106.3: the canonical comparison morphism from the abstract colimit of the
stagewise `B_max` algebras to `B_max` of the ambient cocone point. -/
noncomputable def maximalWeaklyEtaleSubalgebraColimitComparison
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) [HasColimit (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)] :
    colimit (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K) ⟶
      (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c).pt :=
  colimit.desc (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)
    (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c)

/-- Helper for Lemma 15.106.3: a finitely generated `K`-subalgebra of `B_max(c.pt)` factors
through some stage of a filtered colimit diagram, and the factored stage map lands in the stagewise
maximal weakly étale subalgebra. -/
theorem fg_subalgebra_factors_through_stage_of_filtered_colimit
    {J : Type x} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (hc : IsColimit c)
    (S : Subalgebra K B_max(c.pt⁄K)) (hSfg : S.FG) :
    ∃ j, ∃ g : S →ₐ[K] B_max(F.obj j⁄K),
      AlgHom.maximalWeaklyEtaleSubalgebraMap ((c.ι.app j).hom).comp g = S.val := by
  let _ : Algebra.IsWeaklyEtale K B_max(c.pt⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := c.pt)
  have hSet : Algebra.Etale K S :=
    etale_of_fg_subalgebra_of_isWeaklyEtale S hSfg
  have hSfp : (algebraMap K S).FinitePresentation := by
    -- Finite generation over the field `K` upgrades the controlled stage `S` to finite
    -- presentation, so the standard filtered-colimit factorization theorem applies.
    simpa [RingHom.finitePresentation_algebraMap] using
      (Algebra.FinitePresentation.of_finiteType).mp ((Subalgebra.fg_iff_finiteType S).mp hSfg)
  let E := commAlgCatEquivUnder (CommRingCat.of K)
  let G : J ⥤ Under (CommRingCat.of K) := F ⋙ E.functor
  let cUnder : Cocone G := E.functor.mapCocone c
  have hcUnder : IsColimit cUnder := isColimitOfPreserves E.functor hc
  have hpres :
      PreservesFilteredColimits
        (coyoneda.obj (.op (CommRingCat.mkUnder (CommRingCat.of K) S))) := by
    -- The represented functor `Hom_K(S, -)` preserves filtered colimits because `S/K` is finitely
    -- presented.
    simpa using
      CommRingCat.preservesFilteredColimits_coyoneda
        (CommRingCat.of K) (CommRingCat.mkUnder (CommRingCat.of K) S) hSfp
  let gToAmbient : CommRingCat.mkUnder (CommRingCat.of K) S ⟶ cUnder.pt := S.val.toUnder
  obtain ⟨j, gStageRaw, hgStageRaw⟩ :=
    factorsThroughStage_of_preservesFilteredColimits_coyoneda
      (algebraMap K S) hpres G cUnder hcUnder gToAmbient
  have gStage :
      CommRingCat.mkUnder (CommRingCat.of K) S ⟶
        CommRingCat.mkUnder (CommRingCat.of K) (F.obj j) := by
    simpa [G, E] using gStageRaw
  have ιj : CommRingCat.mkUnder (CommRingCat.of K) (F.obj j) ⟶ cUnder.pt := by
    simpa [G, E] using cUnder.ι.app j
  have hgStage : gToAmbient = gStage ≫ ιj := by
    dsimp [gStage, ιj]
    simpa [gToAmbient, G, E] using hgStageRaw
  have hφ_commutes :
      ∀ x : K,
        ((CommRingCat.Hom.hom gStage.right).comp (algebraMap K S)) x =
          (algebraMap K (F.obj j)) x := by
    -- The under-morphism condition on `gStage` is exactly the algebra-map compatibility needed
    -- to view the underlying ring map as a `K`-algebra morphism.
    intro x
    have hw := CommRingCat.hom_ext_iff.mp (Under.w gStage)
    change ((CommRingCat.Hom.hom gStage.right).comp (algebraMap K S)) x =
      (algebraMap K (F.obj j)) x
    simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x
  let φ : S →ₐ[K] F.obj j :=
    { __ := gStage.right.hom
      commutes' := hφ_commutes }
  have hfac : ∀ x : S, (c.ι.app j).hom (φ x) = S.val x := by
    -- Evaluating the factored under-morphism identity on `x` recovers the original inclusion of
    -- `S` into the ambient colimit point.
    intro x
    have hw := CommRingCat.hom_ext_iff.mp (congrArg (fun f ↦ f.right) hgStage)
    simpa [gToAmbient, φ, CommRingCat.hom_comp] using (DFunLike.congr_fun hw x).symm
  have hφ_injective : Function.Injective φ := by
    -- The stage factor is injective because its composite with the ambient cocone leg is the
    -- subtype inclusion `S ↪ B_max(c.pt)`.
    intro x y hxy
    exact Subtype.ext <| by
      change S.val x = S.val y
      rw [← hfac x, ← hfac y, hxy]
  have hSweak : Algebra.IsWeaklyEtale K S := by
    let _ : Algebra.Etale K S := hSet
    exact isWeaklyEtale_of_etale (K := K)
  have hrangeWeak : Algebra.IsWeaklyEtale K φ.range :=
    isWeaklyEtale_range_of_injective (K := K) φ hφ_injective hSweak
  have hRangeLe : φ.range ≤ B_max(F.obj j⁄K) :=
    le_maximalWeaklyEtaleSubalgebra (K := K) (A := F.obj j) φ.range hrangeWeak
  have hStageMem : ∀ x : S, φ x ∈ B_max(F.obj j⁄K) := fun x ↦ hRangeLe ⟨x, rfl⟩
  let gStageMax : S →ₐ[K] B_max(F.obj j⁄K) :=
    φ.codRestrict _ hStageMem
  refine ⟨j, gStageMax, ?_⟩
  -- After codrestricting the stage factor into `B_max(F.obj j)`, the original inclusion of `S`
  -- is recovered by the induced map on maximal weakly étale subalgebras.
  ext x
  exact Subtype.ext (hfac x)

/-- Helper for Lemma 15.106.3: the ambient descended map from the abstract colimit of the stagewise
`B_max` algebras is the comparison map followed by the inclusion into the ambient cocone point. -/
theorem maximalWeaklyEtaleSubalgebraColimitToAmbient_eq_val_comp_comparison
    {J : Type x} [Category J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F)
    [HasColimit (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)] :
    colimit.desc (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)
        (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c) =
      maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c ≫
        CommAlgCat.ofHom (B_max(c.pt⁄K)).val := by
  -- Both descended morphisms are determined by their values on the stagewise colimit legs.
  refine colimit.hom_ext (fun j ↦ ?_)
  rw [colimit.ι_desc, colimit.ι_desc]
  simpa [maximalWeaklyEtaleSubalgebraColimitComparison] using
    maximalWeaklyEtaleSubalgebraToAmbient_eq_val_comp_stageComparison (K := K) F c j

/-- Helper for Lemma 15.106.3: the abstract colimit of the stagewise `B_max` algebras embeds into
the ambient filtered colimit through the descended ambient cocone map. -/
theorem injective_maximalWeaklyEtaleSubalgebra_colimitToAmbient
    {J : Type x} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (hc : IsColimit c)
    [HasColimit (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)] :
    Function.Injective
      (colimit.desc (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)
        (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom := by
  let D := F ⋙ maximalWeaklyEtaleSubalgebraFunctor K
  let t : Cocone (D ⋙ forget (CommAlgCat K)) :=
    (forget (CommAlgCat K)).mapCocone (colimit.cocone D)
  let s : Cocone (F ⋙ forget (CommAlgCat K)) := (forget (CommAlgCat K)).mapCocone c
  have ht : IsColimit t := by
    dsimp [t]
    exact isColimitOfPreserves (forget (CommAlgCat K)) (colimit.isColimit D)
  have hs : IsColimit s := by
    dsimp [s]
    exact isColimitOfPreserves (forget (CommAlgCat K)) hc
  intro x y hxy
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit ht x
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit ht y
  have hx_desc :
      (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom x =
        (c.ι.app i).hom xi.1 := by
    rw [← hxi]
    -- Evaluate the descended ambient map on the chosen stage representative.
    have hleg := congrArg CommAlgCat.Hom.hom
      (colimit.ι_desc (F := D)
        (c := maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c) (j := i))
    simpa [D, maximalWeaklyEtaleSubalgebraAmbientCocone,
      maximalWeaklyEtaleSubalgebraToAmbient] using DFunLike.congr_fun hleg xi
  have hy_desc :
      (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom y =
        (c.ι.app j).hom yj.1 := by
    rw [← hyj]
    -- The same colimit-leg evaluation for the second representative.
    have hleg := congrArg CommAlgCat.Hom.hom
      (colimit.ι_desc (F := D)
        (c := maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c) (j := j))
    simpa [D, maximalWeaklyEtaleSubalgebraAmbientCocone,
      maximalWeaklyEtaleSubalgebraToAmbient] using DFunLike.congr_fun hleg yj
  have hambient :
      (c.ι.app i).hom xi.1 = (c.ι.app j).hom yj.1 := by
    -- Equality after descending to the ambient colimit point comes from the hypothesis `hxy`.
    calc
      (c.ι.app i).hom xi.1
          = (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom x :=
            hx_desc.symm
      _ = (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom y := hxy
      _ = (c.ι.app j).hom yj.1 := hy_desc
  obtain ⟨k, f, g, hfg⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (F := F ⋙ forget (CommAlgCat K)) (ht := hs) xi.1 yj.1).mp hambient
  have hstage :
      ((D ⋙ forget (CommAlgCat K)).map f) xi =
        ((D ⋙ forget (CommAlgCat K)).map g) yj := by
    -- Push the common-stage equality back through the stagewise `B_max` maps.
    apply Subtype.ext
    simpa [D, maximalWeaklyEtaleSubalgebraFunctor,
      AlgHom.maximalWeaklyEtaleSubalgebraMap_apply] using hfg
  have hcolim :
      t.ι.app i xi = t.ι.app j yj := by
    -- Equality in the forgotten `B_max` colimit follows from equality at a common stage.
    exact
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (F := D ⋙ forget (CommAlgCat K)) (ht := ht) xi yj).mpr ⟨k, f, g, hstage⟩
  calc
    x = t.ι.app i xi := hxi.symm
    _ = t.ι.app j yj := hcolim
    _ = y := hyj

/-- Helper for Lemma 15.106.3: every element of `B_max` of the ambient filtered colimit comes from
the abstract colimit of the stagewise `B_max` algebras. -/
theorem surjective_maximalWeaklyEtaleSubalgebraColimitComparison
    {J : Type x} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (hc : IsColimit c)
    [HasColimit (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)] :
    Function.Surjective (maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom := by
  intro x
  let S : Subalgebra K B_max(c.pt⁄K) := Algebra.adjoin K ({x} : Set B_max(c.pt⁄K))
  let xS : S := ⟨x, Algebra.subset_adjoin (by simp)⟩
  have hSfg : S.FG := by
    rw [Subalgebra.fg_iff_finiteType S]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  obtain ⟨j, g, hg⟩ :=
    fg_subalgebra_factors_through_stage_of_filtered_colimit (K := K) F c hc S hSfg
  refine ⟨(colimit.ι (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K) j).hom (g xS), ?_⟩
  have hleg := congrArg CommAlgCat.Hom.hom
    (colimit.ι_desc (F := F ⋙ maximalWeaklyEtaleSubalgebraFunctor K)
      (c := maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c) (j := j))
  have hfactor :
      maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j (g xS) = x := by
    -- Evaluate the stage factorization on the distinguished generator of `S`.
    have hx := congrArg (fun φ : S →ₐ[K] B_max(c.pt⁄K) ↦ φ xS) hg
    simpa [xS, maximalWeaklyEtaleSubalgebraComparisonStageMap] using hx
  calc
    (maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom
        ((colimit.ι (F ⋙ maximalWeaklyEtaleSubalgebraFunctor K) j).hom (g xS))
        = maximalWeaklyEtaleSubalgebraComparisonStageMap (K := K) F c j (g xS) := by
          -- The comparison morphism is defined by the universal property of the colimit.
          simpa [maximalWeaklyEtaleSubalgebraColimitComparison,
            maximalWeaklyEtaleSubalgebraComparisonCocone] using DFunLike.congr_fun hleg (g xS)
    _ = x := hfactor

/-- Helper for Lemma 15.106.3: applying `B_max` to a filtered colimit cocone again yields a
colimiting cocone. -/
theorem isColimit_mappedCocone_of_filtered_colimit
    {J : Type x} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) (hc : IsColimit c) :
    IsColimit (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c) := by
  let D := F ⋙ maximalWeaklyEtaleSubalgebraFunctor K
  have hambient_inj :
      Function.Injective
        (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom :=
    injective_maximalWeaklyEtaleSubalgebra_colimitToAmbient (K := K) F c hc
  have hcomparison_inj :
      Function.Injective (maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom := by
    intro x y hxy
    apply hambient_inj
    -- Compose with the subtype inclusion into the ambient colimit point to recover the ambient
    -- descended map, then use injectivity there.
    have hx := DFunLike.congr_fun
      (congrArg CommAlgCat.Hom.hom
        (maximalWeaklyEtaleSubalgebraColimitToAmbient_eq_val_comp_comparison
          (K := K) F c)) x
    have hy := DFunLike.congr_fun
      (congrArg CommAlgCat.Hom.hom
        (maximalWeaklyEtaleSubalgebraColimitToAmbient_eq_val_comp_comparison
          (K := K) F c)) y
    calc
      (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom x
          = (B_max(c.pt⁄K)).val
              ((maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom x) := by
                simpa using hx
      _ = (B_max(c.pt⁄K)).val
            ((maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom y) := by
              simpa [hxy]
      _ = (colimit.desc D (maximalWeaklyEtaleSubalgebraAmbientCocone (K := K) F c)).hom y := by
            simpa using hy.symm
  have hcomparison_surj :
      Function.Surjective (maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom :=
    surjective_maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c hc
  let e : colimit D ≃ₐ[K] B_max(c.pt⁄K) :=
    AlgEquiv.ofBijective
      (maximalWeaklyEtaleSubalgebraColimitComparison (K := K) F c).hom
      ⟨hcomparison_inj, hcomparison_surj⟩
  let eIso : colimit D ≅ (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c).pt :=
    { hom := CommAlgCat.ofHom e.toAlgHom
      inv := CommAlgCat.ofHom e.symm.toAlgHom
      hom_inv_id := by
        apply CommAlgCat.hom_ext
        ext x
        simpa using e.left_inv x
      inv_hom_id := by
        apply CommAlgCat.hom_ext
        ext x
        simpa using e.apply_symm_apply x }
  letI :
      IsIso ((colimit.isColimit D).desc
        (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c)) := by
    have hdesc :
        (colimit.isColimit D).desc
            (maximalWeaklyEtaleSubalgebraComparisonCocone (K := K) F c) = eIso.hom := by
      apply CommAlgCat.hom_ext
      ext x
      rfl
    simpa [hdesc] using eIso.isIso_hom
  -- The canonical colimit cocone for `D` transports across the comparison isomorphism.
  exact IsColimit.ofPointIso (colimit.isColimit D)

-- Proof sketch: view `B_max` as the functor `maximalWeaklyEtaleSubalgebraFunctor K` on
-- `CommAlgCat K`. For a filtered diagram `F`, each finitely presented weakly étale `K`-subalgebra
-- of the colimit algebra factors through some stage by Lemma `10.127.3`, while part `(1)` gives
-- the forward maps from the stagewise `B_max`; this identifies the mapped cocone as colimiting.
/-- Lemma 15.106.3 (3): the maximal weakly étale subalgebra construction commutes with filtered
colimits, expressed canonically as preservation of filtered colimits by the endofunctor
`maximalWeaklyEtaleSubalgebraFunctor K` on `CommAlgCat K`. -/
@[stacks 0CKT]
theorem maximalWeaklyEtaleSubalgebra_preservesFilteredColimits
    (K : Type u) [Field K] :
    PreservesFilteredColimits (maximalWeaklyEtaleSubalgebraFunctor K) := by
  refine ⟨fun J _ _ ↦ ?_⟩
  refine ⟨fun F ↦ ?_⟩
  refine ⟨?_⟩
  -- Route correction: first show the mapped cocone is colimiting, then package that as filtered
  -- colimit preservation for the owner functor `B_max`.
  change IsColimit ((maximalWeaklyEtaleSubalgebraFunctor K).mapCocone (colimit.cocone F))
  simpa [maximalWeaklyEtaleSubalgebraFunctor, maximalWeaklyEtaleSubalgebraComparisonCocone,
    maximalWeaklyEtaleSubalgebraComparisonStageMap] using
    isColimit_mappedCocone_of_filtered_colimit (K := K) F (colimit.cocone F)
      (colimit.isColimit F)

-- Proof sketch: this is the directed-union specialization of the filtered-colimit owner theorem
-- above, after identifying a directed family of `K`-subalgebras of `A` with a filtered diagram in
-- `CommAlgCat K` whose colimit is `A`.
/-- Directed-union specialization of Lemma 15.106.3 (3): for a directed union presentation
`A = colim Aᵢ` by `K`-subalgebras, `B_max(A)` is the directed supremum of the images of the
stagewise maximal weakly étale subalgebras `B_max(Aᵢ)`. -/
theorem maximalWeaklyEtaleSubalgebra_eq_sSup_of_directed
    {ι : Type x} (Aᵢ : ι → Subalgebra K A)
    (hdir : Directed (· ≤ ·) Aᵢ) (hA : sSup (Set.range Aᵢ) = ⊤) :
    B_max(A⁄K) =
      sSup (Set.range fun i ↦
        (B_max(Aᵢ i⁄K)).map (Aᵢ i).val) := sorry

/-- The canonical map from `B_max(A)` to the maximal weakly étale subalgebra of the reduction of
`A`. -/
def maximalWeaklyEtaleSubalgebraReductionMap
    (K : Type u) [Field K] (A : Type w) [CommRing A] [Algebra K A] :
    B_max(A⁄K) →ₐ[K] B_max(A ⧸ nilradical A⁄K) :=
  (Ideal.Quotient.mkₐ K (nilradical A)).maximalWeaklyEtaleSubalgebraMap

-- Proof sketch: write `B_max(A_red)` as a filtered colimit of étale `K`-algebras and lift each
-- étale stage across `A → A_red`; maximality makes the induced map surjective. Its kernel is made
-- of nilpotents, but `B_max(A_red)` is reduced by Lemma `15.106.1 (1)`, so the kernel vanishes.
/-- Lemma 15.106.3 (4): the canonical map `B_max(A) → B_max(A_red)` is an isomorphism, expressed
as bijectivity of the induced algebra map to the quotient by the nilradical. -/
@[stacks 0CKT]
theorem bijective_maximalWeaklyEtaleSubalgebraReductionMap :
    Function.Bijective (maximalWeaklyEtaleSubalgebraReductionMap K A) := sorry

-- Proof sketch: each projection from a finite product to one factor and each diagonal inclusion of
-- a factor into the product gives maps between the corresponding `B_max`. Using part `(1)`, these
-- maps identify the maximal weakly étale subalgebra of the product with the product of the
-- stagewise maximal weakly étale subalgebras.
/-- Lemma 15.106.3 (5): for a finite family of `K`-algebras, the maximal weakly étale subalgebra
of the product is the product of the maximal weakly étale subalgebras of the factors. -/
@[stacks 0CKT]
theorem maximalWeaklyEtaleSubalgebra_pi
    {ι : Type x} [Finite ι] (Aᵢ : ι → Type v)
    [∀ i, CommRing (Aᵢ i)] [∀ i, Algebra K (Aᵢ i)] :
    B_max(((i : ι) → Aᵢ i)⁄K) = Subalgebra.pi Set.univ (fun i ↦ B_max(Aᵢ i⁄K)) := sorry

-- Proof sketch: `B_max(A)` is weakly étale over `K` by Lemma `15.106.2`, so Lemma `15.106.1 (4)`
-- applies directly. The hypothesis on idempotents of `A` forces the same condition on the
-- subalgebra `B_max(A)`.
/-- Lemma 15.106.3 (6): if `A` has no nontrivial idempotents, then `B_max(A)` is a field. -/
@[stacks 0CKT]
theorem isField_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField B_max(A⁄K) := by
  let hweak : Algebra.IsWeaklyEtale K B_max(A⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A)
  let _ : IsAbsolutelyFlatRing B_max(A⁄K) :=
    isAbsolutelyFlatRing_of_isWeaklyEtale_over_field (K := K) hweak
  -- Restrict the ambient idempotent hypothesis to the maximal weakly étale subalgebra.
  refine isField_of_idempotents_trivial_of_isAbsolutelyFlatRing (R := B_max(A⁄K)) ?_
  intro e he
  have hcoe : IsIdempotentElem (e : A) := by
    simpa using congrArg Subtype.val he
  rcases hA (e : A) hcoe with h0 | h1
  · left
    ext
    exact h0
  · right
    ext
    exact h1

-- Proof sketch: part `(6)` makes `B_max(A)` a field, and Lemma `15.106.1 (5)` then gives the
-- canonical owner `Algebra.IsSeparable K B_max(A⁄K)`. Algebraicity is a derived consequence via
-- `Algebra.IsSeparable.isAlgebraic`.
/-- Lemma 15.106.3 (7): if `A` has no nontrivial idempotents, then `B_max(A)` is a separable
algebraic extension of `K`, expressed through the canonical owner `Algebra.IsSeparable`. -/
@[stacks 0CKT]
theorem isSeparable_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsSeparable K B_max(A⁄K) := by
  let hfield : IsField B_max(A⁄K) :=
    isField_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
      (K := K) (A := A) hA
  let _ : Algebra.IsWeaklyEtale K B_max(A⁄K) :=
    isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A)
  let _ : Field B_max(A⁄K) := hfield.toField
  -- Once `B_max(A)` is known to be a field, separability is the chapter-level weakly étale
  -- consequence over the base field `K`.
  exact isSeparable_of_flat_tensorSquareMultiplication_aux
    (K := K) (L := B_max(A⁄K))
    (inferInstance : Algebra.IsWeaklyEtale K B_max(A⁄K)).flat_tensorSquareMultiplication

/-- Under the hypotheses of part `(7)`, `B_max(A)` is algebraic over `K`. -/
theorem isAlgebraic_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsAlgebraic K B_max(A⁄K) := by
  let _ : Algebra.IsSeparable K B_max(A⁄K) :=
    isSeparable_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one hA
  infer_instance

end
