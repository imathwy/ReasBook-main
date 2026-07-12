import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped Representation.ExternalTensor
open MonoidHom

universe u v w w'

namespace Subgroup

section

variable {G : Type v} [Group G]

/- The direct-product bridge attached to complementary commuting subgroups. This is a
`bridge/view` declaration: the primitive data are the complement proof and the commuting
hypothesis, and the resulting `MulEquiv` is the canonical owner for the multiplication
identification `H × K ≃* G`. -/
/-- If complementary subgroups `H` and `K` commute elementwise, multiplication identifies the
direct product `H × K` with `G`. -/
noncomputable def IsComplement'.prodMulEquiv
    {H K : Subgroup G} (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    H × K ≃* G :=
  MulEquiv.ofBijective
    (H.subtype.noncommCoprod K.subtype hcomm)
    (by simpa [noncommCoprod_apply] using hHK)

end

end Subgroup

namespace Representation

section

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable (H K : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type w'} [AddCommGroup W] [Module k W]

/-- Helper for Exercise 3-3.3-7: under the direct-product identification `H × K ≃* G`, left
multiplication by an element of `H` only changes the `H`-coordinate. -/
private lemma prodMulEquiv_symm_subtype
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) :
    (hHK.prodMulEquiv hcomm).symm (h : G) = (h, 1) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- Compare both sides after transporting them back to `G` through the direct-product
  -- identification.
  apply eHK.injective
  rw [eHK.apply_symm_apply]
  change ↑h = (H.subtype.noncommCoprod K.subtype hcomm) (h, 1)
  simp [noncommCoprod_apply]

/-- Helper for Exercise 3-3.3-7: under the direct-product identification `H × K ≃* G`, left
multiplication by an element of `H` only changes the `H`-coordinate. -/
private lemma prodMulEquiv_symm_subtype_mul
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) (g : G) :
    (hHK.prodMulEquiv hcomm).symm ((h : G) * g) =
      (h * ((hHK.prodMulEquiv hcomm).symm g).1, ((hHK.prodMulEquiv hcomm).symm g).2) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- The direct-product coordinates turn left multiplication by `h` into multiplication on the
  -- `H`-coordinate only.
  rw [eHK.symm.map_mul, prodMulEquiv_symm_subtype H K hHK hcomm h]
  rcases eHK.symm g with ⟨hg, kg⟩
  simp

/-- Helper for Exercise 3-3.3-7: right translation by `u⁻¹` in `G` becomes componentwise
multiplication by the inverse coordinates of `u` in `H × K`. -/
private lemma prodMulEquiv_symm_mul_inv
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g u : G) :
    (hHK.prodMulEquiv hcomm).symm (g * u⁻¹) =
      (((hHK.prodMulEquiv hcomm).symm g).1 * ((hHK.prodMulEquiv hcomm).symm u).1⁻¹,
        ((hHK.prodMulEquiv hcomm).symm g).2 * ((hHK.prodMulEquiv hcomm).symm u).2⁻¹) := by
  let eHK := hHK.prodMulEquiv hcomm
  -- The direct-product coordinates respect multiplication and inversion.
  change eHK.symm (g * u⁻¹) = eHK.symm g * (eHK.symm u)⁻¹
  simpa using eHK.symm.map_mul g u⁻¹

/-- Helper for Exercise 3-3.3-7: the raw map on `k[G] ⊗ W` that sends the basis vector `g` to the
`K`-basis vector indexed by the `K`-coordinate of `g`, while twisting `W` by the inverse
`H`-coordinate. -/
private noncomputable def induced_to_externalTensor_raw
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    (G →₀ k) ⊗[k] W →ₗ[k] W ⊗[k] (K →₀ k) :=
  let eHK := hHK.prodMulEquiv hcomm
  TensorProduct.lift <|
    Finsupp.lift (W →ₗ[k] W ⊗[k] (K →₀ k)) k G fun g ↦
      ((TensorProduct.mk k W (K →₀ k)).flip (Finsupp.single ((eHK.symm g).2)⁻¹ 1)) ∘ₗ
        θ ((eHK.symm g).1)⁻¹

/-- Helper for Exercise 3-3.3-7: the raw tensor formula is well defined on the induced
coinvariants. -/
private lemma induced_to_externalTensor_descends
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (h : H) :
    induced_to_externalTensor_raw H K θ hHK hcomm ∘ₗ
        Representation.tprod ((leftRegular k G).comp H.subtype) θ h =
      induced_to_externalTensor_raw H K θ hHK hcomm := by
  -- It suffices to compare both sides on the pure tensors `single g 1 ⊗ w`.
  refine TensorProduct.ext ?_
  refine Finsupp.lhom_ext' fun g ↦ ?_
  ext w
  simp [induced_to_externalTensor_raw, Representation.tprod_apply, Finsupp.lift_apply,
    prodMulEquiv_symm_subtype_mul]

/-- Helper for Exercise 3-3.3-7: the descended map from the induced model to the external tensor
model. -/
private noncomputable def induced_to_externalTensor
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    IndV H.subtype θ →ₗ[k] W ⊗[k] (K →₀ k) :=
  Coinvariants.lift _ (induced_to_externalTensor_raw H K θ hHK hcomm)
    (induced_to_externalTensor_descends H K θ hHK hcomm)

/-- Helper for Exercise 3-3.3-7: on the standard generator `IndV.mk g w`, the descended map reads
off the direct-product coordinates of `g`. -/
private lemma induced_to_externalTensor_apply_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) (w : W) :
    induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ g w) =
      θ (((hHK.prodMulEquiv hcomm).symm g).1)⁻¹ w ⊗ₜ[k]
        Finsupp.single (((hHK.prodMulEquiv hcomm).symm g).2)⁻¹ 1 := by
  -- Unfolding the quotient lift reduces immediately to the defining tensor formula.
  simp [induced_to_externalTensor, induced_to_externalTensor_raw, Finsupp.lift_apply]

/-- Helper for Exercise 3-3.3-7: the inverse candidate from `W ⊗ k[K]` back to the induced
representation sends `w ⊗ δ_k` to the induced generator supported at the element `(1, k⁻¹)`. -/
private noncomputable def externalTensor_to_induced_linear
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    W ⊗[k] (K →₀ k) →ₗ[k] IndV H.subtype θ :=
  TensorProduct.lift <|
    LinearMap.flip <|
      Finsupp.lift (W →ₗ[k] IndV H.subtype θ) k K fun k' ↦
        Representation.IndV.mk H.subtype θ ((hHK.prodMulEquiv hcomm) (1, k'⁻¹))

/-- Helper for Exercise 3-3.3-7: the inverse candidate is explicit on pure tensors with a single
`K`-basis vector. -/
private lemma externalTensor_to_induced_linear_apply_single
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (w : W) (k' : K) (r : k) :
    externalTensor_to_induced_linear H K θ hHK hcomm (w ⊗ₜ[k] Finsupp.single k' r) =
      r • Representation.IndV.mk H.subtype θ ((hHK.prodMulEquiv hcomm) (1, k'⁻¹)) w := by
  -- The `Finsupp.lift` linear-combination formula collapses on a single basis vector.
  simp [externalTensor_to_induced_linear, Finsupp.lift_apply]

/-- Helper for Exercise 3-3.3-7: the coordinate formula for `induced_to_externalTensor` respects
the `G`-action on the standard induced generators. -/
private lemma induced_to_externalTensor_intertwines_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g u : G) (w : W) :
    induced_to_externalTensor H K θ hHK hcomm
        ((ind H.subtype θ) g (Representation.IndV.mk H.subtype θ u w)) =
      (((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) g)
        (induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ u w)) := by
  let eHK := hHK.prodMulEquiv hcomm
  rcases hg : eHK.symm g with ⟨gH, gK⟩
  rcases hu : eHK.symm u with ⟨uH, uK⟩
  -- Expand the induced action on the standard generator and read off its direct-product
  -- coordinates.
  rw [Representation.ind_mk, induced_to_externalTensor_apply_mk]
  have hu_mul :
      eHK.symm (u * g⁻¹) = (uH * gH⁻¹, uK * gK⁻¹) := by
    simpa [hg, hu] using prodMulEquiv_symm_mul_inv H K hHK hcomm u g
  rw [hu_mul]
  -- Evaluate the target tensor-product action on the same generator.
  rw [induced_to_externalTensor_apply_mk]
  have hg' : (hHK.prodMulEquiv hcomm).symm g = (gH, gK) := by
    simpa [eHK] using hg
  have hu' : (hHK.prodMulEquiv hcomm).symm u = (uH, uK) := by
    simpa [eHK] using hu
  have hleftRegular :
      leftRegular k K gK (Finsupp.single uK⁻¹ (1 : k)) =
        Finsupp.single (gK * uK⁻¹) 1 := by
    simpa using
      (Representation.ofMulAction_single (k := k) (G := K) (H := K) gK uK⁻¹ (1 : k))
  -- The `H`-coordinate multiplies on the left, while the `K`-basis vector translates by
  -- left-regular multiplication.
  simpa [MonoidHom.coe_comp, Function.comp_apply, Representation.tprod_apply,
    TensorProduct.map_tmul, hg', hu', hleftRegular, Module.End.mul_apply, map_mul]

/-- Helper for Exercise 3-3.3-7: the explicit inverse sends the image of each induced generator
back to that same generator. -/
private lemma externalTensor_to_induced_left_inverse_mk
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) (w : W) :
    externalTensor_to_induced_linear H K θ hHK hcomm
        (induced_to_externalTensor H K θ hHK hcomm (Representation.IndV.mk H.subtype θ g w)) =
      Representation.IndV.mk H.subtype θ g w := by
  let eHK := hHK.prodMulEquiv hcomm
  rcases hcoords : eHK.symm g with ⟨gH, gK⟩
  -- Expand the forward map on the generator `IndV.mk g w`.
  rw [induced_to_externalTensor_apply_mk]
  rw [show (hHK.prodMulEquiv hcomm).symm g = (gH, gK) by simpa [eHK, hcoords]]
  -- Apply the inverse candidate to the resulting basis tensor.
  rw [externalTensor_to_induced_linear_apply_single]
  simp only [one_smul, inv_inv]
  have hk_eval : eHK (1, gK) = (gK : G) := by
    simp [eHK, Subgroup.IsComplement'.prodMulEquiv, noncommCoprod_apply]
  have hg_eval : eHK (gH, gK) = (gH : G) * (gK : G) := by
    simp [eHK, Subgroup.IsComplement'.prodMulEquiv, noncommCoprod_apply]
  have hg_decomp : g = (gH : G) * (gK : G) := by
    calc
      g = eHK (gH, gK) := by simpa [eHK, hcoords] using (eHK.apply_symm_apply g).symm
      _ = (gH : G) * (gK : G) := hg_eval
  rw [hk_eval, hg_decomp]
  -- Move the `H`-factor from the `G`-coordinate of the induced generator into the coefficient
  -- vector using the coinvariant relation.
  have hmk :
      Representation.IndV.mk H.subtype θ ((gH : G) * (gK : G)) w =
        Representation.IndV.mk H.subtype θ (gK : G) (θ gH⁻¹ w) := by
    simpa [Representation.IndV.mk, Representation.ofMulAction_single] using
      (Representation.Coinvariants.mk_inv_tmul
        (ρ := (leftRegular k G).comp H.subtype)
        (τ := θ)
        (x := Finsupp.single (gK : G) (1 : k))
        (y := w)
        (g := gH⁻¹))
  exact hmk.symm

/-- Helper for Exercise 3-3.3-7: the coordinate map recovers a pure tensor supported on a single
`K`-basis vector after applying the explicit inverse candidate. -/
private lemma induced_to_externalTensor_right_inverse_single
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (w : W) (k' : K) (r : k) :
    induced_to_externalTensor H K θ hHK hcomm
        (externalTensor_to_induced_linear H K θ hHK hcomm
          (w ⊗ₜ[k] Finsupp.single k' r)) =
      w ⊗ₜ[k] Finsupp.single k' r := by
  let eHK := hHK.prodMulEquiv hcomm
  -- Expand the inverse candidate on the chosen `K`-basis tensor.
  rw [externalTensor_to_induced_linear_apply_single, map_smul]
  -- The forward map then reads off the trivial `H`-coordinate and the chosen `K`-coordinate.
  rw [induced_to_externalTensor_apply_mk]
  have hcoords : eHK.symm (eHK (1, k'⁻¹)) = (1, k'⁻¹) := by
    simp [eHK]
  rw [hcoords]
  -- After simplifying the coordinates, only the original pure tensor remains.
  simpa [inv_one, ← TensorProduct.tmul_smul]

/-- Helper for Exercise 3-3.3-7: the explicit coordinate map intertwines the induced `G`-action
with the pulled-back tensor-product action. -/
private lemma induced_to_externalTensor_isIntertwining
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G))
    (g : G) :
    induced_to_externalTensor H K θ hHK hcomm ∘ₗ (ind H.subtype θ) g =
      (((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) g) ∘ₗ
        induced_to_externalTensor H K θ hHK hcomm := by
  -- Check equivariance on the canonical induced generators `IndV.mk g w`.
  apply Representation.IndV.hom_ext (φ := H.subtype) (ρ := θ)
  intro u
  ext w
  simpa [LinearMap.comp_apply] using
    induced_to_externalTensor_intertwines_mk H K θ hHK hcomm g u w

/-- Helper for Exercise 3-3.3-7: the inverse candidate is a left inverse to the coordinate map on
the whole induced module. -/
private lemma externalTensor_to_induced_left_inverse
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    externalTensor_to_induced_linear H K θ hHK hcomm ∘ₗ
        induced_to_externalTensor H K θ hHK hcomm =
      (LinearMap.id : IndV H.subtype θ →ₗ[k] IndV H.subtype θ) := by
  -- The induced model is generated by the images of `IndV.mk`, so the generator identity
  -- upgrades to a map identity by `IndV.hom_ext`.
  apply Representation.IndV.hom_ext (φ := H.subtype) (ρ := θ)
  intro g
  ext w
  simpa [LinearMap.comp_apply] using
    externalTensor_to_induced_left_inverse_mk H K θ hHK hcomm g w

/-- Helper for Exercise 3-3.3-7: the coordinate map is a right inverse to the explicit inverse on
the tensor-product model. -/
private lemma induced_to_externalTensor_right_inverse
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    induced_to_externalTensor H K θ hHK hcomm ∘ₗ
        externalTensor_to_induced_linear H K θ hHK hcomm =
      (LinearMap.id : W ⊗[k] (K →₀ k) →ₗ[k] W ⊗[k] (K →₀ k)) := by
  -- Check the identity on pure tensors `w ⊗ single k' 1`; tensor and `Finsupp` extensionality
  -- then promote it to all tensors.
  refine TensorProduct.ext ?_
  ext w k'
  simpa [LinearMap.comp_apply] using
    induced_to_externalTensor_right_inverse_single H K θ hHK hcomm w k' (1 : k)

/-- Helper for Exercise 3-3.3-7: the standard induced model is equivariantly isomorphic to the
external tensor product `θ ⊠ r_K` transported along the direct-product identification `H × K ≃ G`.
-/
private noncomputable abbrev ind_equiv_externalTensor_leftRegular_of_direct_product
    (θ : Representation k H W)
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    (ind H.subtype θ).Equiv ((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) :=
  -- Route correction: the explicit coordinate map already gives the right model; the remaining
  -- task is to package its generator-level equivariance and inverse formulas into a linear
  -- equivalence of representations.
  Representation.Equiv.mk
    (LinearEquiv.ofLinear
      (induced_to_externalTensor H K θ hHK hcomm)
      (externalTensor_to_induced_linear H K θ hHK hcomm)
      (induced_to_externalTensor_right_inverse H K θ hHK hcomm)
      (externalTensor_to_induced_left_inverse H K θ hHK hcomm))
    (induced_to_externalTensor_isIntertwining H K θ hHK hcomm)

/- Source/core/bridge triage:
* source-facing: the exercise identifies an induced `G`-representation with the pullback of
  `θ ⊗ r_K` along the product decomposition `H × K ≃ G`.
* core/canonical: `Representation.ind`, the external tensor-product owner
  `(θ.comp (fst H K)).tprod ((leftRegular k K).comp (snd H K))`, and
  `Representation.leftRegular`.
* bridge/view: `Subgroup.IsComplement'.prodMulEquiv` packages the subgroup product identification
  obtained from `H.IsComplement' K` and the commutation hypothesis.

Primitive data are the induced equivalence `hρ` and the direct-product hypotheses `hHK`, `hcomm`.
The product-group equivalence is a bridge derived from the direct-product hypotheses, while the
tensor-product model is the canonical source-facing notation `θ ⊠ leftRegular k K` for that owner,
rather than a separate local wrapper definition.
-/
/-- Exercise 3-3.3-7: if `G` is the direct product of its subgroups `H` and `K`, and `ρ` is a
representation of `G` induced by a representation `θ` of `H`, then `ρ` is isomorphic to the
pullback along the multiplication identification `H × K ≃ G` of the external tensor product
`θ ⊠ r_K`, where `r_K` is the regular representation of `K`. -/
-- Proof sketch: the direct-product hypothesis is encoded by the canonical complement owner
-- `H.IsComplement' K` together with pairwise commutation of elements of `H` and `K`. These data
-- recover the multiplication isomorphism `H × K ≃* G`, after which one compares the standard
-- induced model with the external tensor-product model `θ ⊠ r_K` on `W ⊗[k] (K →₀ k)` and
-- composes with
-- the given equivalence `ρ ≃ ind H.subtype θ`.
noncomputable def isomorphic_to_externalTensor_left_regular_of_induced_of_direct_product
    (ρ : Representation k G V) (θ : Representation k H W)
    (hρ : ρ.Equiv (ind H.subtype θ))
    (hHK : H.IsComplement' K)
    (hcomm : ∀ h : H, ∀ k' : K, Commute (h : G) (k' : G)) :
    ρ.Equiv ((θ ⊠ leftRegular k K).comp (hHK.prodMulEquiv hcomm).symm.toMonoidHom) :=
  -- The target comparison is the given induced equivalence followed by the explicit direct-product
  -- model for the induced representation.
  hρ.trans (ind_equiv_externalTensor_leftRegular_of_direct_product H K θ hHK hcomm)

end

end Representation
