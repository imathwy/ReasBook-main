import Mathlib
import Mathlib.RingTheory.Ideal.Pure
import stacks_proof.stacks_project.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

open CategoryTheory
open HomologicalComplex
open scoped KoszulComplex

/- Domain triage:
* primary domain: finite `H₁`-regular sequences in a quotient ring and the induced equality
  `I ⊓ J = I * J` for the owner ideal `J = Ideal.ofList (List.ofFn g)`;
* sampled owner API:
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `Ideal.ofList`,
  `injective_lTensor_quotient_iff_inf_eq_mul`;
* `source-facing`: the public ideal `Ideal.span (Set.range g)`;
* `core/canonical`: the finite-family owner ideal `Ideal.ofList (List.ofFn g)`;
* `bridge/view`: rewrite the owner ideal to `Ideal.span (Set.range g)` only at the public
  theorem boundary.
-/

/-- Helper for Lemma 15.30.8: the owner ideal of a finite family is the source-facing span of its
range. -/
private theorem ofList_ofFn_eq_span_range_local {m : ℕ} (g : Fin m → A) :
    Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) := by
  -- Proof comment: unfold `Ideal.ofList` and identify `List.ofFn g` with the same generating set
  -- indexed by `Fin m`.
  ext x
  simp [Ideal.ofList, List.mem_ofFn', Set.range]

/-- Helper for Lemma 15.30.8: the map on quotients modulo `I` induced by an `A`-linear map. -/
private abbrev quotientMapByIdeal_local
    {M M' : Type u} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (f : M →ₗ[A] M') (I : Ideal A) :
    M ⧸ (I • (⊤ : Submodule A M)) →ₗ[A] M' ⧸ (I • (⊤ : Submodule A M')) :=
  (I • (⊤ : Submodule A M)).mapQ (I • (⊤ : Submodule A M')) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- Helper for Lemma 15.30.8: after the standard quotient-tensor identifications, tensoring the
owner inclusion `J ↪ A` with `A ⧸ I` is exactly the quotient map `J / IJ → A / I`. -/
private theorem subtype_quotientMapByIdeal_lTensor_naturality_local
    (I J : Ideal A) :
    quotientMapByIdeal_local J.subtype I ∘ₗ
        (TensorProduct.quotTensorEquivQuotSMul J I).toLinearMap =
      (TensorProduct.quotTensorEquivQuotSMul A I).toLinearMap ∘ₗ
        J.subtype.lTensor (A ⧸ I) := by
  -- Proof comment: compare the tensor-side and quotient-side maps on pure tensors, where both
  -- quotient-tensor equivalences have their defining closed form.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [smul_eq_mul, quotientMapByIdeal_local, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    Submodule.Quotient.mk_smul, map_smul, Submodule.mapQ_apply, Submodule.subtype_apply,
    Ideal.Quotient.mk_eq_mk, LinearMap.lTensor_tmul]
  rfl

/-- Helper for Lemma 15.30.8: injectivity of the explicit quotient map `J / IJ → A / I` implies
injectivity of the tensor map `J ⊗[A] (A ⧸ I) → A ⊗[A] (A ⧸ I)`. -/
private theorem injective_lTensor_of_injective_quotientMapByIdeal_local
    (I J : Ideal A) (hJ : Function.Injective (quotientMapByIdeal_local J.subtype I)) :
    Function.Injective (J.subtype.lTensor (A ⧸ I)) := by
  -- Proof comment: transport equality across the quotient-tensor equivalences and then use the
  -- assumed injectivity of the concrete quotient map.
  let eJ := TensorProduct.quotTensorEquivQuotSMul J I
  let eA := TensorProduct.quotTensorEquivQuotSMul A I
  intro x y hxy
  apply eJ.injective
  have hx :
      quotientMapByIdeal_local J.subtype I (eJ x) =
        eA (J.subtype.lTensor (A ⧸ I) x) := by
    simpa [eJ, eA] using
      LinearMap.congr_fun (subtype_quotientMapByIdeal_lTensor_naturality_local (A := A) I J) x
  have hy :
      quotientMapByIdeal_local J.subtype I (eJ y) =
        eA (J.subtype.lTensor (A ⧸ I) y) := by
    simpa [eJ, eA] using
      LinearMap.congr_fun (subtype_quotientMapByIdeal_lTensor_naturality_local (A := A) I J) y
  apply hJ
  calc
    quotientMapByIdeal_local J.subtype I (eJ x) = eA (J.subtype.lTensor (A ⧸ I) x) := hx
    _ = eA (J.subtype.lTensor (A ⧸ I) y) := by rw [hxy]
    _ = quotientMapByIdeal_local J.subtype I (eJ y) := hy.symm

/-- Helper for Lemma 15.30.8: in a short complex of `A`-modules, a homology class vanishes
exactly when its cycle representative comes from the previous differential. -/
private theorem shortComplex_homologyπ_eq_zero_iff_exists_boundary_local
    (S : ShortComplex (ModuleCat A)) [S.HasHomology] (q : S.cycles) :
    S.homologyπ.hom q = 0 ↔
      ∃ b : S.X₁, S.moduleCatToCycles b = S.moduleCatCyclesIso.hom q := by
  have hcomm :
      S.homologyπ ≫ S.moduleCatHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Proof comment: compare abstract homology with the concrete quotient of cycles by
    -- boundaries.
    simpa using S.π_moduleCatCyclesIso_hom
  constructor
  · intro hq
    -- Proof comment: evaluate the comparison square at the chosen cycle and rewrite vanishing in
    -- abstract homology as vanishing in the concrete quotient of cycles by boundaries.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hπ' : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := hπ.symm
    have hmem : S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ'
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- Proof comment: a concrete boundary class is zero in the quotient-of-cycles presentation,
    -- hence also zero after transporting back to abstract homology.
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1 inferInstance
    have h0 : 0 = S.moduleCatHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.30.8: in degree `i` of a chain complex of `A`-modules, a homology class
vanishes exactly when its cycle representative is a boundary from the previous degree. -/
private theorem homologyπ_eq_zero_iff_exists_boundary_local
    (K : ChainComplex (ModuleCat A) ℕ) (i : ℕ) (q : K.cycles i) :
    (K.homologyπ i).hom q = 0 ↔
      ∃ b : (K.sc i).X₁, (K.sc i).moduleCatToCycles b = (K.sc i).moduleCatCyclesIso.hom q := by
  -- Proof comment: rewrite degree-`i` homology through the canonical short complex `K.sc i`.
  simpa [HomologicalComplex.homologyπ, ShortComplex.homologyπ] using
    shortComplex_homologyπ_eq_zero_iff_exists_boundary_local (S := K.sc i) q

/-- Helper for Lemma 15.30.8: the quotient-side `H₁`-regularity hypothesis should force
injectivity of the tensor map attached to the owner ideal `Ideal.ofList (List.ofFn g)`. -/
private theorem injective_lTensor_of_ofList_quotient_h1_regular {m : ℕ} (I : Ideal A)
    (g : Fin m → A) (hreg : IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk I (g i))) :
    Function.Injective ((Ideal.ofList (List.ofFn g)).subtype.lTensor (A ⧸ I)) := by
  let J : Ideal A := Ideal.ofList (List.ofFn g)
  have hquot :
      Function.Injective (quotientMapByIdeal_local J.subtype I) := by
    -- Route correction: the file can no longer rely on `Lemma_15_30_6`, so the remaining source
    -- proof core has to be carried out locally as the degree-`2 → 1 → 0` Koszul diagram chase.
    -- Proof comment: the generic boundary-extraction lemma above now isolates the homological
    -- bookkeeping, so the only missing work is the explicit quotient-Koszul cycle construction
    -- and the boundary-to-`IJ` descent.
    -- TODO(Lemma 15.30.8): use `hreg`, via `isH1RegularSequence_iff` on the quotient family
    -- `qg i = Ideal.Quotient.mk I (g i)`, to show that every relation among the classes `qg i`
    -- is a trivial Koszul relation. Then apply that to any `x : J` whose image in `A ⧸ I`
    -- vanishes, rewriting a representative `x = ∑ i, g i * a i` and concluding that `x ∈ I * J`.
    let B : Type u := A ⧸ I
    let qg : Fin m → B := fun i ↦ Ideal.Quotient.mk I (g i)
    have hzero : CategoryTheory.Limits.IsZero ((K^•(qg)).homology 1) := by
      -- Proof comment: normalize the source hypothesis to vanishing of degree-one quotient Koszul
      -- homology so the remaining boundary witness can be extracted from `homologyπ`.
      exact (isH1RegularSequence_iff qg).mp hreg
    let _ := hzero
    sorry
  -- Proof comment: once the quotient-side injectivity is known, the tensor statement follows by
  -- the standard quotient-tensor equivalence.
  simpa [J] using
    injective_lTensor_of_injective_quotientMapByIdeal_local (A := A) I J hquot

-- Proof sketch: rewrite the public span ideal to the canonical owner `Ideal.ofList (List.ofFn g)`,
-- then apply the owner criterion `injective_lTensor_quotient_iff_inf_eq_mul`. The remaining input
-- is exactly the source-faithful tensor-injectivity statement above.
/-- Lemma 15.30.8: if the image of a finite family `g` in `A ⧸ I` is `H_1`-regular, then the
intersection of `I` with the ideal generated by `g` is the product `I * (g_1, \ldots, g_m)`. -/
@[stacks 0665]
theorem ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient {m : ℕ} (I : Ideal A)
    (g : Fin m → A) (hreg : IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk I (g i))) :
    I ⊓ Ideal.span (Set.range g) = I * Ideal.span (Set.range g) := by
  -- Proof comment: first move from the source-facing span ideal to the canonical owner ideal.
  rw [← ofList_ofFn_eq_span_range_local g]
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  -- Proof comment: after the owner rewrite, the statement is exactly the tensor injectivity from
  -- the source-proof route.
  exact injective_lTensor_of_ofList_quotient_h1_regular I g hreg

end RingTheory.Sequence
