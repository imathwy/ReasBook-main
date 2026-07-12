import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped Pointwise Representation

noncomputable section

universe u v w

namespace Representation

section

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

private abbrev mackeyConjMap (K : Subgroup G) (s : G) : K →* G :=
  (MulAut.conj s⁻¹).toMonoidHom.comp K.subtype

/-- The Mackey subgroup `K ∩ sHs⁻¹`, viewed as a subgroup of `K`. -/
abbrev mackeySubgroup (K H : Subgroup G) (s : G) : Subgroup K :=
  H.comap (mackeyConjMap K s)

/-- The canonical conjugation homomorphism `K ∩ sHs⁻¹ → H` used in Mackey's decomposition. -/
private abbrev mackeyConjHom (K H : Subgroup G) (s : G) : mackeySubgroup K H s →* H :=
  ((mackeyConjMap K s).restrict (mackeySubgroup K H s)).codRestrict H fun x ↦ x.2

/-- The twist `W^s` of `W` along the canonical conjugation homomorphism
`K ∩ sHs⁻¹ → H`. -/
noncomputable abbrev mackeyTwist
    (K H : Subgroup G) (W : Rep k H) (s : G) :
    Rep k (mackeySubgroup K H s) :=
  Rep.res (mackeyConjHom K H s) W

section Normal

variable {W : Type w} [AddCommGroup W] [Module k W]

/-- The conjugate representation `ρ ^ s` of a representation `ρ` of a normal subgroup `H`.
This is the normal-subgroup specialization of the Mackey twist. -/
scoped instance {H : Subgroup G} [H.Normal] : Pow (Representation k H W) G where
  pow ρ s := ρ.comp (MulAut.conjNormal s⁻¹).toMonoidHom

@[simp] theorem pow_apply {H : Subgroup G} [H.Normal] (ρ : Representation k H W) (s : G)
    (h : H) :
    (ρ ^ s) h = ρ ((MulAut.conjNormal s⁻¹) h) :=
  rfl

end Normal

/-- The Mackey summand `Ind^K_{K ∩ sHs⁻¹}(W^s)` attached to a representative `s : G`. -/
noncomputable abbrev mackeySummand
    (K H : Subgroup G) (W : Rep k H) (s : G) :
    Rep k K :=
  Rep.ind (mackeySubgroup K H s).subtype (mackeyTwist K H W s)

/-- Helper for Proposition 7-7.3-1: the unit-coset generator
`IndV.mk H.subtype W.ρ 1` is injective, so its range is a faithful copy of `W`. -/
private noncomputable def inducedIdentityCopyProjectionAux
    (H : Subgroup G) (W : Rep.{w} k H) :
    (G →₀ k) →ₗ[k] W.V →ₗ[k] W.V :=
  Finsupp.lift _ _ _ fun g ↦
    @dite _ (g ∈ H) ((Classical.decPred fun x : G ↦ x ∈ H) g) (fun hg ↦ W.ρ ⟨g, hg⟩⁻¹)
      (fun _ ↦ 0)

/-- Helper for Proposition 7-7.3-1: the basiswise projection to the unit-coset copy is constant on
the `H`-coinvariant relations defining `Ind_H^G(W)`. -/
private theorem induced_identity_copy_projectionAux_respects
    (H : Subgroup G) (W : Rep.{w} k H) :
    ∀ h : H,
      TensorProduct.lift (inducedIdentityCopyProjectionAux H W) ∘ₗ
          (Representation.tprod ((leftRegular k G).comp H.subtype) W.ρ) h =
        TensorProduct.lift (inducedIdentityCopyProjectionAux H W) := by
  classical
  intro h
  -- Check the coinvariant relation on a basis tensor `δ_g ⊗ w`.
  ext g w
  by_cases hg : g ∈ H
  · have hhg : ((h : G) * g) ∈ H := H.mul_mem h.property hg
    have hmul : W.ρ ⟨(h : G) * g, hhg⟩⁻¹ ((W.ρ h) w) = W.ρ ⟨g, hg⟩⁻¹ w := by
      have hsub : ((⟨(h : G) * g, hhg⟩⁻¹ : H) * h) = ⟨g, hg⟩⁻¹ := by
        ext
        simp [mul_assoc]
      calc
        W.ρ ⟨(h : G) * g, hhg⟩⁻¹ ((W.ρ h) w)
          = W.ρ (((⟨(h : G) * g, hhg⟩⁻¹ : H) * h)) w := by
              simp [Module.End.mul_apply, map_mul]
        _ = W.ρ ⟨g, hg⟩⁻¹ w := by
              rw [hsub]
    -- On the `H`-summand, the projection exactly cancels the extra translate.
    simpa [inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul, hg, hhg] using hmul
  · have hnhg : ((h : G) * g) ∉ H := by
      intro hmem
      have htmp : ((h : G)⁻¹ * ((h : G) * g)) ∈ H :=
        H.mul_mem (H.inv_mem h.property) hmem
      have hg' : g ∈ H := by
        simpa [mul_assoc] using htmp
      exact hg hg'
    -- Outside the unit double-coset fiber, both sides project to zero.
    rw [inducedIdentityCopyProjectionAux]
    simp [TensorProduct.lift.tmul, hg, hnhg]

/-- Helper for Proposition 7-7.3-1: projection from `Ind_H^G(W)` back to the unit-coset copy. -/
private noncomputable def inducedIdentityCopyProjection
    (H : Subgroup G) (W : Rep.{w} k H) :
    Representation.IndV H.subtype W.ρ →ₗ[k] W.V :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift (inducedIdentityCopyProjectionAux H W))
    (induced_identity_copy_projectionAux_respects H W)

/-- Helper for Proposition 7-7.3-1: the projection recovers the original vector on the
unit-coset generator `IndV.mk ... 1`. -/
private theorem induced_identity_copy_projection_apply_mk_one
    (H : Subgroup G) (W : Rep.{w} k H) (w : W.V) :
    inducedIdentityCopyProjection H W (Representation.IndV.mk H.subtype W.ρ 1 w) = w := by
  classical
  have hone : (1 : G) ∈ H := H.one_mem
  have hbase : W.ρ ⟨1, hone⟩⁻¹ w = w := by
    have hsub : ((⟨1, hone⟩ : H)⁻¹) = 1 := by
      ext
      simp
    rw [hsub]
    exact LinearMap.congr_fun W.ρ.map_one w
  -- Evaluating the quotient lift at the unit basis vector reduces to the identity on `W`.
  simpa [inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul,
    hone] using hbase

/-- Helper for Proposition 7-7.3-1: the unit-coset generator
`IndV.mk H.subtype W.ρ 1` is injective, so its range is a faithful copy of `W`. -/
private theorem induced_identity_copy_mk_one_injective
    (H : Subgroup G) (W : Rep.{w} k H) :
    Function.Injective (Representation.IndV.mk H.subtype W.ρ 1) := by
  intro x y hxy
  -- Apply the explicit projection back to `W`; it is a left inverse on the unit-coset copy.
  have hproj := congrArg (inducedIdentityCopyProjection H W) hxy
  calc
    x = inducedIdentityCopyProjection H W (Representation.IndV.mk H.subtype W.ρ 1 x) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one H W x
    _ = inducedIdentityCopyProjection H W (Representation.IndV.mk H.subtype W.ρ 1 y) := hproj
    _ = y := induced_identity_copy_projection_apply_mk_one H W y

/-- Helper for Proposition 7-7.3-1: the range of `IndV.mk` at the unit coset is stable under the
restricted `H`-action on `Ind_H^G(W)`. -/
private theorem induced_identity_copy_apply_mem
    (H : Subgroup G) (W : Rep.{w} k H) (h : H)
    {x : Representation.IndV H.subtype W.ρ}
    (hx : x ∈ LinearMap.range (Representation.IndV.mk H.subtype W.ρ 1)) :
    ((Rep.ind H.subtype W).ρ.comp H.subtype) h x ∈
      LinearMap.range (Representation.IndV.mk H.subtype W.ρ 1) := by
  rcases hx with ⟨w, rfl⟩
  -- Rewrite the translate of the unit-coset copy back into the unit-coset copy.
  refine ⟨W.ρ h w, ?_⟩
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Proposition 7-7.3-1: the copy of `W` sitting in `Ind_H^G(W)` at the unit coset. -/
private def inducedIdentityCopySubrepresentation
    (H : Subgroup G) (W : Rep.{w} k H) :
    Subrepresentation ((Rep.ind H.subtype W).ρ.comp H.subtype) :=
  { toSubmodule := LinearMap.range (Representation.IndV.mk H.subtype W.ρ 1)
    apply_mem_toSubmodule := induced_identity_copy_apply_mem H W }

/-- Helper for Proposition 7-7.3-1: the unit-coset copy intertwines the original `H`-action on
`W` with the restricted action on its image inside `Ind_H^G(W)`. -/
private noncomputable def inducedIdentityCopyLinearEquiv
    (H : Subgroup G) (W : Rep.{w} k H) :
    W.V ≃ₗ[k] (inducedIdentityCopySubrepresentation H W).toSubmodule :=
  LinearEquiv.ofInjective
    (Representation.IndV.mk H.subtype W.ρ 1)
    (induced_identity_copy_mk_one_injective H W)

/-- Helper for Proposition 7-7.3-1: the unit-coset copy intertwines the original `H`-action on
`W` with the restricted action on its image inside `Ind_H^G(W)`. -/
private theorem induced_identity_copy_linearEquiv_intertwines
    (H : Subgroup G) (W : Rep.{w} k H) :
    ∀ h,
      (inducedIdentityCopyLinearEquiv H W).toLinearMap ∘ₗ W.ρ h =
        (inducedIdentityCopySubrepresentation H W).toRepresentation h ∘ₗ
          (inducedIdentityCopyLinearEquiv H W).toLinearMap := by
  intro h
  -- Both sides are the same vector in `Ind_H^G(W)` after transporting along the unit-coset copy.
  ext w
  -- After forgetting the range witness, both sides are the standard `IndV.mk` identity.
  change Representation.IndV.mk H.subtype W.ρ 1 (W.ρ h w) =
    ((Rep.ind H.subtype W).ρ.comp H.subtype) h (Representation.IndV.mk H.subtype W.ρ 1 w)
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Proposition 7-7.3-1: `W` is `H`-equivariantly equivalent to its unit-coset copy
inside `Ind_H^G(W)`. -/
private noncomputable def inducedIdentityCopyEquiv
    (H : Subgroup G) (W : Rep.{w} k H) :
    W.ρ.Equiv (inducedIdentityCopySubrepresentation H W).toRepresentation :=
  Representation.Equiv.mk
    (inducedIdentityCopyLinearEquiv H W)
    (induced_identity_copy_linearEquiv_intertwines H W)

/-- Helper for Proposition 7-7.3-1: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft
    {Γ : Type*} [Group Γ]
    {V' V'' U : Type*}
    [AddCommGroup V'] [Module k V']
    [AddCommGroup V''] [Module k V'']
    [AddCommGroup U] [Module k U]
    {ρ : Representation k Γ V'} {σ : Representation k Γ V''}
    (e : ρ.Equiv σ) (τ : Representation k Γ U) :
    σ.IntertwiningMap τ ≃ₗ[k] ρ.IntertwiningMap τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      ext x
      simp
    right_inv := by
      intro f
      ext x
      simp
    map_add' := by
      intro f g
      rfl
    map_smul' := by
      intro a f
      rfl }

/-- Helper for Proposition 7-7.3-1: every vector in the unit-coset copy is the unit-coset
generator attached to its preimage under the explicit equivalence with `W`. -/
private theorem induced_identity_copy_eq_mk_one_symm
    (H : Subgroup G) (W : Rep.{w} k H)
    (u : (inducedIdentityCopySubrepresentation H W).toSubmodule) :
    (u : Representation.IndV H.subtype W.ρ) =
      Representation.IndV.mk H.subtype W.ρ 1 ((inducedIdentityCopyEquiv H W).symm u) := by
  -- The explicit copy equivalence is defined by the unit-coset embedding `IndV.mk ... 1`.
  have hmk (w : W.V) :
      (((inducedIdentityCopyLinearEquiv H W) w :
          (inducedIdentityCopySubrepresentation H W).toSubmodule) :
        Representation.IndV H.subtype W.ρ) =
        Representation.IndV.mk H.subtype W.ρ 1 w := by
    rfl
  have hEq :
      inducedIdentityCopyLinearEquiv H W ((inducedIdentityCopyEquiv H W).symm u) = u := by
    exact (inducedIdentityCopyEquiv H W).toLinearEquiv.apply_symm_apply u
  have hEq_coe :
      (u : Representation.IndV H.subtype W.ρ) =
        (((inducedIdentityCopyLinearEquiv H W) ((inducedIdentityCopyEquiv H W).symm u) :
            (inducedIdentityCopySubrepresentation H W).toSubmodule) :
          Representation.IndV H.subtype W.ρ) := by
    simpa using
      congrArg
        (fun z : (inducedIdentityCopySubrepresentation H W).toSubmodule ↦
          (z : Representation.IndV H.subtype W.ρ))
        hEq.symm
  calc
    (u : Representation.IndV H.subtype W.ρ) =
        (((inducedIdentityCopyLinearEquiv H W) ((inducedIdentityCopyEquiv H W).symm u) :
            (inducedIdentityCopySubrepresentation H W).toSubmodule) :
          Representation.IndV H.subtype W.ρ) :=
      hEq_coe
    _ = Representation.IndV.mk H.subtype W.ρ 1 ((inducedIdentityCopyEquiv H W).symm u) :=
      hmk _

/-- Helper for Proposition 7-7.3-1: the ambient `G / H`-indexed family coming from the unit-coset
copy of `W` inside `Ind_H^G(W)`. -/
private abbrev inducedLeftCosetFamily
    (H : Subgroup G) (W : Rep.{w} k H) :
    G ⧸ H → Submodule k (Representation.IndV H.subtype W.ρ) :=
  ((Rep.ind H.subtype W).ρ).leftQuotientSubmodule H (inducedIdentityCopySubrepresentation H W)

/-- Helper for Proposition 7-7.3-1: after transporting the unit-coset copy back to `W`,
restriction of intertwiners is exactly Frobenius reciprocity, hence bijective. -/
private theorem induced_identity_copy_restrictIntertwiningMap_bijective
    (H : Subgroup G) (W : Rep.{w} k H) (ρ' : Rep.{max (max u v) w} k G) :
    Function.Bijective
      (restrictIntertwiningMap ((Rep.ind H.subtype W).ρ) H
        (inducedIdentityCopySubrepresentation H W) ρ'.ρ) := by
  let e :
      ((inducedIdentityCopySubrepresentation H W).toRepresentation.IntertwiningMap
          (ρ'.ρ.comp H.subtype)) ≃ₗ[k]
        W.ρ.IntertwiningMap (ρ'.ρ.comp H.subtype) :=
    intertwiningMapCongrLeft (inducedIdentityCopyEquiv H W) (ρ'.ρ.comp H.subtype)
  let L :
      ((Rep.ind H.subtype W).ρ).IntertwiningMap ρ'.ρ →
        W.ρ.IntertwiningMap (ρ'.ρ.comp H.subtype) :=
    fun F ↦
      (F.toLinearMap.comp
        (Representation.IndV.mk H.subtype W.ρ 1)).intertwiningMap_of_isIntertwiningMap
        W.ρ (ρ'.ρ.comp H.subtype) fun h x ↦ by
          have hcomm :
              F.toLinearMap (((Rep.ind H.subtype W).ρ.comp H.subtype) h
                  (Representation.IndV.mk H.subtype W.ρ 1 x)) =
                (ρ'.ρ.comp H.subtype) h
                  (F.toLinearMap (Representation.IndV.mk H.subtype W.ρ 1 x)) := by
            simpa using congr($(F.isIntertwining' h) (Representation.IndV.mk H.subtype W.ρ 1 x))
          simpa [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul] using hcomm
  have hrestrict :
      ∀ F : ((Rep.ind H.subtype W).ρ).IntertwiningMap ρ'.ρ,
        e (restrictIntertwiningMap ((Rep.ind H.subtype W).ρ) H
          (inducedIdentityCopySubrepresentation H W) ρ'.ρ F) = L F := by
    intro F
    -- Transporting along `inducedIdentityCopyEquiv` rewrites restriction to evaluation on
    -- `IndV.mk ... 1`.
    ext w
    rfl
  let extend :
      W.ρ.IntertwiningMap (ρ'.ρ.comp H.subtype) →
        ((Rep.ind H.subtype W).ρ).IntertwiningMap ρ'.ρ :=
    fun f ↦
      { toLinearMap := Representation.Coinvariants.lift _
          (TensorProduct.lift <| Finsupp.lift _ _ _ fun h => ρ'.ρ h⁻¹ ∘ₗ f.toLinearMap)
          fun g ↦ by
            simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
              TensorProduct.lift_comp_map]
            congr 1
            ext
            simp [Representation.IntertwiningMap.isIntertwining]
        isIntertwining' := fun g ↦ by
          ext
          simp }
  have hleft : Function.LeftInverse extend L := by
    intro F
    -- Equality on the induced representation is checked on the standard generators `IndV.mk`.
    ext h a
    have hcomm :=
      congr($(F.isIntertwining' h⁻¹) (Representation.IndV.mk H.subtype W.ρ 1 a))
    simpa [L, extend, Representation.IndV.mk] using hcomm.symm
  have hright : Function.RightInverse extend L := by
    intro f
    -- Evaluating the explicit extension at the unit generator recovers the original intertwiner.
    ext a
    simp [L, extend]
  have hL : Function.Bijective L := ⟨hleft.injective, hright.surjective⟩
  constructor
  · intro F F' hFF'
    apply hL.1
    simpa [hrestrict F, hrestrict F'] using congrArg e hFF'
  · intro f
    obtain ⟨F, hF⟩ := hL.2 (e f)
    refine ⟨F, ?_⟩
    apply e.injective
    simpa [hrestrict F] using hF

/-- Helper for Proposition 7-7.3-1: `Ind_H^G(W)` is induced from the unit-coset copy of `W`. -/
theorem induced_identity_copy_is_induced
    (H : Subgroup G) (W : Rep.{w} k H) :
    ((Rep.ind H.subtype W).ρ).IsInducedFromSubrepresentation
      H (inducedIdentityCopySubrepresentation H W) := by
  -- Route correction: instead of rebundling the unit-coset copy into a larger owner with awkward
  -- universes, the right remaining statement is a representation-level bridge lemma:
  -- identify `restrictIntertwiningMap` for the unit-coset copy with Frobenius reciprocity
  -- transported along `inducedIdentityCopyEquiv H W`, without rebundling `W` and `U₁`
  -- as objects of the same `Rep` universe.
  -- Proposition `7-7.1-1` turns the transported Frobenius bijection into the internal-family
  -- statement needed for inducedness.
  exact
    isInducedFromSubrepresentation_of_bijective_restrictIntertwiningMap
      (ρ := (Rep.ind H.subtype W).ρ)
      (H := H)
      (W := inducedIdentityCopySubrepresentation H W)
      (fun ρ' ↦ induced_identity_copy_restrictIntertwiningMap_bijective H W ρ')

/-- Helper for Proposition 7-7.3-1: after restricting to `K`, the ambient left-coset summand
indexed by `q` is sent onto the summand indexed by `k • q`. -/
theorem induced_leftCoset_family_map
    (H : Subgroup G) (W : Rep.{w} k H) (g : G) (q : G ⧸ H) :
    (inducedLeftCosetFamily H W q).map ((Rep.ind H.subtype W).ρ g) =
      inducedLeftCosetFamily H W (g • q) := by
  -- This is the tautological identity `g · (xW) = (gx)W` for the ambient induced family.
  unfold inducedLeftCosetFamily
  exact
    (Representation.leftQuotientSubmodule_map
      (ρ := (Rep.ind H.subtype W).ρ)
      (H := H)
      (W := inducedIdentityCopySubrepresentation H W)
      g q)

/-- Helper for Proposition 7-7.3-1: the block attached to a double coset is the supremum of the
ambient left-coset summands lying above that double coset. -/
private def doubleCosetBlock
    (K H : Subgroup G) (W : Rep.{w} k H) (d : DoubleCoset.Quotient (K : Set G) H) :
    Submodule k (Representation.IndV H.subtype W.ρ) :=
  ⨆ q : {q : G ⧸ H // DoubleCoset.mk K H q.out = d}, inducedLeftCosetFamily H W q.1

/-- Helper for Proposition 7-7.3-1: regrouping the ambient `G / H`-family by double-coset fibers
does not change its total span. -/
theorem doubleCoset_blocks_iSup_eq_top
    (K H : Subgroup G) (W : Rep.{w} k H) :
    iSup (doubleCosetBlock K H W) = ⊤ := by
  classical
  -- First compare the regrouped supremum with the original `G / H`-indexed supremum.
  calc
    iSup (doubleCosetBlock K H W) = iSup (inducedLeftCosetFamily H W) := by
      apply le_antisymm
      · refine iSup_le ?_
        intro d
        refine iSup_le ?_
        intro q
        exact le_iSup_of_le q.1 le_rfl
      · refine iSup_le ?_
        intro q
        exact
          le_iSup_of_le (DoubleCoset.mk K H q.out) <|
            le_iSup_of_le ⟨q, rfl⟩ le_rfl
    _ = ⊤ := by
      -- The ambient family already spans because it exhibits `Ind_H^G(W)` as induced from `U₁`.
      let ℳ : G ⧸ H → Submodule k (Representation.IndV H.subtype W.ρ) := inducedLeftCosetFamily H W
      letI : DecidableEq (G ⧸ H) := Classical.decEq _
      have hInternal : DirectSum.IsInternal ℳ := by
        simpa [ℳ, inducedLeftCosetFamily, Representation.IsInducedFromSubrepresentation] using
          induced_identity_copy_is_induced H W
      exact hInternal.submodule_iSup_eq_top

/-- Helper for Proposition 7-7.3-1: regrouping the ambient `G / H`-family by double-coset fibers
preserves internality, so the quotient-indexed double-coset blocks are independent and span the
restricted induced representation. -/
private theorem doubleCoset_blocks_is_internal
    (K H : Subgroup G) (W : Rep.{w} k H)
    [DecidableEq (DoubleCoset.Quotient (K : Set G) H)] :
    DirectSum.IsInternal (doubleCosetBlock K H W) := by
  classical
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  let ℳ : G ⧸ H → Submodule k (Representation.IndV H.subtype W.ρ) := inducedLeftCosetFamily H W
  let f : G ⧸ H → DoubleCoset.Quotient (K : Set G) H := fun q ↦ DoubleCoset.mk K H q.out
  have hAmbient : DirectSum.IsInternal ℳ := by
    -- The ambient left-coset family is already the internal family coming from Proposition 7-7.1-1.
    simpa [ℳ, inducedLeftCosetFamily, Representation.IsInducedFromSubrepresentation] using
      induced_identity_copy_is_induced H W
  have hAmbientIndep : iSupIndep ℳ := hAmbient.submodule_iSupIndep
  have hBlock :
      ∀ d : DoubleCoset.Quotient (K : Set G) H,
        doubleCosetBlock K H W d = ⨆ q ∈ {q : G ⧸ H | f q = d}, ℳ q := by
    intro d
    simp [doubleCosetBlock, ℳ, f, iSup_subtype]
  have hRest :
      ∀ d : DoubleCoset.Quotient (K : Set G) H,
        (⨆ e, ⨆ _ : e ≠ d, doubleCosetBlock K H W e) =
          ⨆ q ∈ {q : G ⧸ H | f q ≠ d}, ℳ q := by
    intro d
    apply le_antisymm
    · refine iSup_le ?_
      intro e
      refine iSup_le ?_
      intro hed
      change (⨆ q : {q : G ⧸ H // f q = e}, ℳ q.1) ≤
        ⨆ q ∈ {q : G ⧸ H | f q ≠ d}, ℳ q
      refine iSup_le ?_
      intro q
      exact le_iSup_of_le q.1 <| le_iSup_of_le (by simpa [f] using q.2.trans_ne hed) le_rfl
    · refine iSup_le ?_
      intro q
      refine iSup_le ?_
      intro hqd
      exact
        le_iSup_of_le (f q) <|
          le_iSup_of_le hqd <|
            by
              rw [hBlock (f q)]
              exact le_iSup_of_le q <| le_iSup_of_le (by simp [f]) le_rfl
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    -- Distinct double-coset fibers are disjoint because the ambient `G / H`-family is independent.
    rw [hBlock, hRest]
    exact hAmbientIndep.disjoint_biSup_biSup <| by
      rw [Set.disjoint_left]
      intro q hq_left hq_right
      exact hq_right hq_left
  · exact doubleCoset_blocks_iSup_eq_top K H W

/-- Helper for Proposition 7-7.3-1: after reindexing the quotient-indexed block decomposition along
the chosen representatives `s`, the selected double-coset blocks still form an internal direct
sum. -/
private theorem selected_doubleCosetBlocks_is_internal
    {ι : Type*} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    DirectSum.IsInternal (fun i ↦ doubleCosetBlock K H W (DoubleCoset.mk K H (s i))) := by
  classical
  let ehs : ι ≃ DoubleCoset.Quotient (K : Set G) H :=
    Equiv.ofBijective (fun i ↦ DoubleCoset.mk K H (s i)) hs
  have hBlocks : DirectSum.IsInternal (doubleCosetBlock K H W) :=
    doubleCoset_blocks_is_internal K H W
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · -- Independence is preserved by reindexing along the representative equivalence.
    simpa [ehs, Function.comp] using hBlocks.submodule_iSupIndep.comp ehs.injective
  · -- The regrouped blocks still span because `ehs` hits every double coset exactly once.
    calc
      iSup (fun i ↦ doubleCosetBlock K H W (DoubleCoset.mk K H (s i))) =
          iSup (doubleCosetBlock K H W ∘ ehs) := by
            rfl
      _ = iSup (doubleCosetBlock K H W) := by
            simpa [Function.comp] using (ehs.iSup_comp (g := doubleCosetBlock K H W))
      _ = ⊤ := hBlocks.submodule_iSup_eq_top

/-- Helper for Proposition 7-7.3-1: the Mackey subgroup consists exactly of the elements of `K`
that fix the left coset `sH`. -/
private theorem mackey_subgroup_iff_fix_leftCoset
    (K H : Subgroup G) (s : G) (x : K) :
    x ∈ mackeySubgroup K H s ↔ (((x : K) : G) * s : G ⧸ H) = (s : G ⧸ H) := by
  constructor
  · intro hx
    -- Membership in `K ∩ sHs⁻¹` says `s⁻¹ x s ∈ H`, which is the left-coset equality criterion.
    rw [QuotientGroup.eq]
    simpa [mackeySubgroup, mackeyConjMap, mul_assoc] using H.inv_mem hx
  · intro hx
    -- Conversely, fixing `sH` means the relative element `s⁻¹ x s` lies in `H`.
    have hx' : s⁻¹ * ((x : K) : G)⁻¹ * s ∈ H := by
      rw [QuotientGroup.eq] at hx
      simpa [mul_assoc] using hx
    have hx'' : s⁻¹ * ((x : K) : G) * s ∈ H := by
      simpa [mul_assoc] using H.inv_mem hx'
    simpa [mackeySubgroup, mackeyConjMap, mul_assoc] using hx''

/-- Helper for Proposition 7-7.3-1: translating the unit-coset projection by `s⁻¹` recovers the
vector used to build the `sH`-summand. -/
private noncomputable def seedLeftCosetProjection
    (H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Representation.IndV H.subtype W.ρ →ₗ[k] W.V :=
  inducedIdentityCopyProjection H W ∘ₗ (Rep.ind H.subtype W).ρ s⁻¹

/-- Helper for Proposition 7-7.3-1: the translated projection is a left inverse to the seed map
`w ↦ IndV.mk ... s⁻¹ w`. -/
private theorem seedLeftCosetProjection_apply_mk
    (H : Subgroup G) (W : Rep.{w} k H) (s : G) (w : W.V) :
    seedLeftCosetProjection H W s (Representation.IndV.mk H.subtype W.ρ s⁻¹ w) = w := by
  -- Moving the `sH`-generator back by `s⁻¹` returns the unit-coset generator, where the explicit
  -- projection from earlier is already known to be the identity.
  calc
    seedLeftCosetProjection H W s (Representation.IndV.mk H.subtype W.ρ s⁻¹ w) =
        inducedIdentityCopyProjection H W
          (((Rep.ind H.subtype W).ρ s⁻¹) (Representation.IndV.mk H.subtype W.ρ s⁻¹ w)) := by
            rfl
    _ = inducedIdentityCopyProjection H W (Representation.IndV.mk H.subtype W.ρ 1 w) := by
          simp [Representation.IndV.mk]
    _ = w := induced_identity_copy_projection_apply_mk_one H W w

/-- Helper for Proposition 7-7.3-1: the seed translate `w ↦ IndV.mk ... s⁻¹ w` is injective. -/
private theorem seedLeftCoset_mk_injective
    (H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Function.Injective (Representation.IndV.mk H.subtype W.ρ s⁻¹) := by
  intro x y hxy
  -- Apply the translated projection, which is a left inverse on the `sH`-summand.
  have hproj := congrArg (seedLeftCosetProjection H W s) hxy
  calc
    x = seedLeftCosetProjection H W s (Representation.IndV.mk H.subtype W.ρ s⁻¹ x) := by
          symm
          exact seedLeftCosetProjection_apply_mk H W s x
    _ = seedLeftCosetProjection H W s (Representation.IndV.mk H.subtype W.ρ s⁻¹ y) := hproj
    _ = y := seedLeftCosetProjection_apply_mk H W s y

/-- Helper for Proposition 7-7.3-1: the left-coset summand indexed by `sH` is exactly the range of
`w ↦ IndV.mk ... s⁻¹ w`. -/
private theorem seedLeftCosetFamily_eq_range
    (H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    inducedLeftCosetFamily H W (s : G ⧸ H) =
      LinearMap.range (Representation.IndV.mk H.subtype W.ρ s⁻¹) := by
  -- Use the representative `s` itself when unfolding the left-quotient family, so the target
  -- summand is visibly the image of the unit-coset copy under the translate by `s`.
  unfold inducedLeftCosetFamily
  rw [Representation.leftQuotientSubmodule_mk]
  change
    (LinearMap.range (Representation.IndV.mk H.subtype W.ρ 1)).map ((Rep.ind H.subtype W).ρ s) =
      LinearMap.range (Representation.IndV.mk H.subtype W.ρ s⁻¹)
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨w, rfl⟩
    exact ⟨w, by simp [Representation.IndV.mk]⟩
  · intro hx
    rcases hx with ⟨w, rfl⟩
    refine Submodule.mem_map.mpr ?_
    refine ⟨Representation.IndV.mk H.subtype W.ρ 1 w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · simp [Representation.IndV.mk]

/-- Helper for Proposition 7-7.3-1: the seed left-coset summand is stable under the Mackey
subgroup, so it forms a subrepresentation of the restricted induced representation. -/
private def seedLeftCosetSubrepresentation
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Subrepresentation
      (((Rep.res K.subtype (Rep.ind H.subtype W)).ρ).comp (mackeySubgroup K H s).subtype) :=
  { toSubmodule := inducedLeftCosetFamily H W (s : G ⧸ H)
    apply_mem_toSubmodule := by
      intro x v hv
      -- An element of `K ∩ sHs⁻¹` fixes the coset `sH`, so the translate of the seed summand
      -- stays inside the same summand.
      have hfix :
          (((x : K) : G) * s : G ⧸ H) = (s : G ⧸ H) :=
        (mackey_subgroup_iff_fix_leftCoset K H s (x : K)).mp x.property
      have hmap :
          (inducedLeftCosetFamily H W (s : G ⧸ H)).map
              ((((Rep.res K.subtype (Rep.ind H.subtype W)).ρ).comp
                  (mackeySubgroup K H s).subtype) x) =
            inducedLeftCosetFamily H W (s : G ⧸ H) := by
        calc
          (inducedLeftCosetFamily H W (s : G ⧸ H)).map
              ((((Rep.res K.subtype (Rep.ind H.subtype W)).ρ).comp
                  (mackeySubgroup K H s).subtype) x) =
            inducedLeftCosetFamily H W ((((x : K) : G) * s : G ⧸ H)) := by
              simpa using
                induced_leftCoset_family_map H W (((x : K) : G))
                  (s : G ⧸ H)
          _ = inducedLeftCosetFamily H W (s : G ⧸ H) := by
              simpa [hfix]
      rw [← hmap]
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    }

/-- Helper for Proposition 7-7.3-1: the seed translate `w ↦ IndV.mk ... s⁻¹ w` gives a linear
equivalence from `W` onto the `sH`-summand. -/
private noncomputable def seedLeftCosetLinearEquiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    W.V ≃ₗ[k] (seedLeftCosetSubrepresentation K H W s).toSubmodule := by
  let eRange :
      W.V ≃ₗ[k] LinearMap.range (Representation.IndV.mk H.subtype W.ρ s⁻¹) :=
    LinearEquiv.ofInjective (Representation.IndV.mk H.subtype W.ρ s⁻¹)
      (seedLeftCoset_mk_injective H W s)
  let eSub :
      LinearMap.range (Representation.IndV.mk H.subtype W.ρ s⁻¹) ≃ₗ[k]
        (seedLeftCosetSubrepresentation K H W s).toSubmodule :=
    LinearEquiv.ofEq _ _ (seedLeftCosetFamily_eq_range H W s).symm
  exact eRange.trans eSub

/-- Helper for Proposition 7-7.3-1: after forgetting the submodule witness, the seed equivalence
is the translate map `w ↦ IndV.mk ... s⁻¹ w`. -/
private theorem seedLeftCosetLinearEquiv_apply
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) (w : W.V) :
    ((seedLeftCosetLinearEquiv K H W s w :
        (seedLeftCosetSubrepresentation K H W s).toSubmodule) :
      Representation.IndV H.subtype W.ρ) =
      Representation.IndV.mk H.subtype W.ρ s⁻¹ w := by
  -- The range-based equivalence was chosen precisely so that its underlying ambient vector is the
  -- original seed translate.
  simp [seedLeftCosetLinearEquiv, seedLeftCosetFamily_eq_range]

/-- Helper for Proposition 7-7.3-1: the seed equivalence intertwines the Mackey twist action with
the restricted induced action on the `sH`-summand. -/
private theorem seedLeftCosetLinearEquiv_intertwines
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    ∀ x,
      (seedLeftCosetLinearEquiv K H W s).toLinearMap ∘ₗ (mackeyTwist K H W s).ρ x =
        (seedLeftCosetSubrepresentation K H W s).toRepresentation x ∘ₗ
          (seedLeftCosetLinearEquiv K H W s).toLinearMap := by
  intro x
  -- On the ambient induced module, both sides are the standard identity
  -- `x · IndV.mk s w = IndV.mk s ((s⁻¹xs) · w)`.
  ext w
  change
    Representation.IndV.mk H.subtype W.ρ s⁻¹ ((mackeyTwist K H W s).ρ x w) =
      (((Rep.res K.subtype (Rep.ind H.subtype W)).ρ).comp (mackeySubgroup K H s).subtype) x
        (((seedLeftCosetLinearEquiv K H W s w :
            (seedLeftCosetSubrepresentation K H W s).toSubmodule) :
          Representation.IndV H.subtype W.ρ)) at *
  rw [seedLeftCosetLinearEquiv_apply]
  simpa [mackeyTwist, mackeyConjHom, mackeyConjMap, Representation.IndV.mk,
    Module.End.mul_apply, map_mul, mul_assoc, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Proposition 7-7.3-1: the seed left-coset summand is equivariantly isomorphic to the
Mackey twist `W^s`. -/
private noncomputable def seedLeftCosetEquiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (mackeyTwist K H W s).ρ.Equiv (seedLeftCosetSubrepresentation K H W s).toRepresentation :=
  Representation.Equiv.mk
    (seedLeftCosetLinearEquiv K H W s)
    (seedLeftCosetLinearEquiv_intertwines K H W s)

/-- Helper for Proposition 7-7.3-1: two elements of `G` in the same left `H`-coset determine the
same `K \ G / H` double coset. -/
private theorem doubleCoset_mk_eq_of_leftRel
    (K H : Subgroup G) {a b : G}
    (hab : QuotientGroup.leftRel H a b) :
    DoubleCoset.mk K H a = DoubleCoset.mk K H b := by
  rw [QuotientGroup.leftRel_apply] at hab
  let h : H := ⟨a⁻¹ * b, hab⟩
  exact (DoubleCoset.eq K H a b).2 ⟨1, K.one_mem, h, h.property, by simp [h]⟩

/-- Helper for Proposition 7-7.3-1: left multiplication by an element of `K` does not change the
double-coset label of a left `H`-coset. -/
private theorem doubleCoset_mk_smul_leftCoset
    (K H : Subgroup G) (x : K) (q : G ⧸ H) :
    DoubleCoset.mk K H (((x : K) • q).out) = DoubleCoset.mk K H q.out := by
  have hleft :
      (((x : K) • q).out : G ⧸ H) = (((x : K) : G) * q.out : G ⧸ H) := by
    calc
      (((x : K) • q).out : G ⧸ H) = (x : K) • q := Quotient.out_eq' ((x : K) • q)
      _ = (x : K) • (q.out : G ⧸ H) := by
            exact (congrArg (fun z : G ⧸ H ↦ (x : K) • z) (Quotient.out_eq' q)).symm
      _ = (((x : K) : G) * q.out : G ⧸ H) := rfl
  have hleftRel :
      QuotientGroup.leftRel H (((x : K) : G) * q.out) (((x : K) • q).out) := by
    exact Quotient.exact' hleft.symm
  calc
    DoubleCoset.mk K H (((x : K) • q).out) =
        DoubleCoset.mk K H (((x : K) : G) * q.out) := by
          symm
          exact doubleCoset_mk_eq_of_leftRel K H hleftRel
    _ = DoubleCoset.mk K H q.out := by
          symm
          exact (DoubleCoset.eq K H q.out (((x : K) : G) * q.out)).2
            ⟨x, x.property, 1, H.one_mem, by simp⟩

/-- Helper for Proposition 7-7.3-1: each double-coset block is stable under the restricted
`K`-action on `Ind_H^G(W)`. -/
private theorem doubleCosetBlock_apply_mem
    (K H : Subgroup G) (W : Rep.{w} k H)
    (d : DoubleCoset.Quotient (K : Set G) H)
    (x : K)
    {v : Representation.IndV H.subtype W.ρ}
    (hv : v ∈ doubleCosetBlock K H W d) :
    ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ x) v ∈ doubleCosetBlock K H W d := by
  classical
  have hmap :
      (doubleCosetBlock K H W d).map ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ x) ≤
        doubleCosetBlock K H W d := by
    -- Transport each left-coset summand separately; the double-coset fiber is unchanged by `x`.
    unfold doubleCosetBlock
    rw [Submodule.map_iSup]
    refine iSup_le ?_
    intro q
    have hq :
        DoubleCoset.mk K H (((x : K) • q.1).out) = d := by
      calc
        DoubleCoset.mk K H (((x : K) • q.1).out) = DoubleCoset.mk K H q.1.out :=
          doubleCoset_mk_smul_leftCoset K H x q.1
        _ = d := q.2
    calc
      (inducedLeftCosetFamily H W q.1).map ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ x) =
          inducedLeftCosetFamily H W ((x : K) • q.1) := by
            simpa using induced_leftCoset_family_map H W ((x : K) : G) q.1
      _ ≤ ⨆ q : {q : G ⧸ H // DoubleCoset.mk K H q.out = d}, inducedLeftCosetFamily H W q.1 :=
          le_iSup_of_le ⟨(x : K) • q.1, hq⟩ le_rfl
  exact hmap <| Submodule.mem_map.mpr ⟨v, hv, rfl⟩

/-- Helper for Proposition 7-7.3-1: the block over a fixed double coset is a
`K`-subrepresentation of the restricted induced representation. -/
private def doubleCosetBlockSubrepresentation
    (K H : Subgroup G) (W : Rep.{w} k H)
    (d : DoubleCoset.Quotient (K : Set G) H) :
    Subrepresentation ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ) :=
  { toSubmodule := doubleCosetBlock K H W d
    apply_mem_toSubmodule := doubleCosetBlock_apply_mem K H W d }

/-- Helper for Proposition 7-7.3-1: once the selected blocks are known to be internal, the
restricted induced representation is explicitly identified with the external direct sum of those
block subrepresentations. -/
private noncomputable def restriction_induced_selectedDoubleCosetBlocks_iso
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    Rep.res K.subtype (Rep.ind H.subtype W) ≅
      Rep.of (directSum fun i ↦
        (doubleCosetBlockSubrepresentation K H W
          (DoubleCoset.mk K H (s i))).toRepresentation) := by
  let σ : ι → Subrepresentation ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ) :=
    fun i ↦ doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H (s i))
  have hσ_internal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) := by
    -- Route correction: convert the proved submodule-level internality into the bundled
    -- subrepresentation family before asking for the external direct-sum equivalence.
    simpa [σ, doubleCosetBlockSubrepresentation] using
      selected_doubleCosetBlocks_is_internal K H W s hs
  letI := DirectSum.IsInternal.chooseDecomposition (fun i ↦ (σ i).toSubmodule) hσ_internal
  refine Rep.mkIso <| (Representation.Equiv.mk ?_ ?_).symm
  · exact (DirectSum.decomposeLinearEquiv (fun i ↦ (σ i).toSubmodule)).symm
  · intro x
    -- The decomposition map is `K`-equivariant because each summand is a `K`-subrepresentation.
    ext i v
    simp [Representation.directSum, σ, LinearMap.comp_assoc]
    rfl

/-- Helper for Proposition 7-7.3-1: once the selected blocks are known to be internal, the
restricted induced representation is the external direct sum of those block subrepresentations. -/
private theorem restriction_induced_isomorphic_selectedDoubleCosetBlocks
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    IsIsomorphic
      (Rep.res K.subtype (Rep.ind H.subtype W))
      (Rep.of (directSum fun i ↦
        (doubleCosetBlockSubrepresentation K H W
          (DoubleCoset.mk K H (s i))).toRepresentation)) := by
  classical
  exact ⟨restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs⟩

/-- Helper for Proposition 7-7.3-1: the selected-block decomposition sends a translated seed
to the corresponding block coordinate. -/
private theorem restriction_induced_selectedDoubleCosetBlocks_iso_hom_apply_seed
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i))
    (i : ι) (x : mackeyTwist K H W (s i))
    (hx : Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x ∈
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H (s i))).toSubmodule) :
    ((restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs).hom.hom :
        Representation.IndV H.subtype W.ρ →ₗ[k]
          DirectSum ι
            (fun j ↦
              (doubleCosetBlockSubrepresentation K H W
                (DoubleCoset.mk K H (s j))).toSubmodule))
      (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x) =
      DirectSum.lof k _
        (fun j ↦
          (doubleCosetBlockSubrepresentation K H W
            (DoubleCoset.mk K H (s j))).toSubmodule)
        i
        (⟨Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x, hx⟩ :
          (doubleCosetBlockSubrepresentation K H W
            (DoubleCoset.mk K H (s i))).toSubmodule) := by
  let ℳ : ι → Submodule k (Representation.IndV H.subtype W.ρ) :=
    fun j ↦
      (doubleCosetBlockSubrepresentation K H W
        (DoubleCoset.mk K H (s j))).toSubmodule
  let y : ℳ i :=
    ⟨Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x, hx⟩
  have hℳ_internal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, doubleCosetBlockSubrepresentation] using
      selected_doubleCosetBlocks_is_internal K H W s hs
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hℳ_internal
  have hdecomp :
      DirectSum.decomposeLinearEquiv ℳ y =
        DirectSum.lof k ι (fun j ↦ ℳ j) i y :=
    DirectSum.decomposeLinearEquiv_apply_coe ℳ i y
  simpa [restriction_induced_selectedDoubleCosetBlocks_iso, ℳ, y] using hdecomp

/-- Helper for Proposition 7-7.3-1: the direct sum of componentwise representation equivalences is
again an equivalence of representations. -/
theorem directSum_componentwise_intertwines
    {ι : Type*}
    {V W : ι → Type*}
    [(i : ι) → AddCommGroup (V i)] [(i : ι) → Module k (V i)]
    [(i : ι) → AddCommGroup (W i)] [(i : ι) → Module k (W i)]
    (ρ : ∀ i, Representation k G (V i))
    (σ : ∀ i, Representation k G (W i))
    (e : ∀ i, (ρ i).Equiv (σ i)) :
    ∀ g,
      (LinearEquiv.ofLinear
          (DirectSum.lmap fun i ↦ (e i).toLinearEquiv.toLinearMap)
          (DirectSum.lmap fun i ↦ (e i).symm.toLinearEquiv.toLinearMap)
          (by
            ext x i
            simp)
          (by
            ext x i
            simp)).toLinearMap ∘ₗ directSum ρ g =
        directSum σ g ∘ₗ
          (LinearEquiv.ofLinear
            (DirectSum.lmap fun i ↦ (e i).toLinearEquiv.toLinearMap)
            (DirectSum.lmap fun i ↦ (e i).symm.toLinearEquiv.toLinearMap)
            (by
              ext x i
              simp)
            (by
              ext x i
              simp)).toLinearMap := by
  intro g
  -- Check equivariance coordinatewise: each component intertwines by construction.
  ext x i
  exact LinearMap.congr_fun ((e i).toIntertwiningMap.2 g) (x i)

/-- Helper for Proposition 7-7.3-1: componentwise representation isomorphisms induce an
explicit isomorphism of external direct sums. -/
noncomputable def directSum_iso_of_componentwise
    {ι : Type*}
    (ρ σ : ι → Rep k G)
    (e : ∀ i, ρ i ≅ σ i) :
    Rep.of (directSum fun i ↦ (ρ i).ρ) ≅
      Rep.of (directSum fun i ↦ (σ i).ρ) := by
  classical
  let η : ∀ i, (ρ i).ρ.Equiv (σ i).ρ :=
    fun i ↦ Representation.equivOfIso (e i)
  refine Rep.mkIso <| Representation.Equiv.mk ?_ ?_
  · exact
      LinearEquiv.ofLinear
        (DirectSum.lmap fun i ↦ (η i).toLinearEquiv.toLinearMap)
        (DirectSum.lmap fun i ↦ (η i).symm.toLinearEquiv.toLinearMap)
        (by
          ext x i
          simp)
        (by
          ext x i
          simp)
  · exact directSum_componentwise_intertwines (fun i ↦ (ρ i).ρ) (fun i ↦ (σ i).ρ) η

/-- Helper for Proposition 7-7.3-1: the componentwise direct-sum isomorphism acts on each
external summand by the corresponding component isomorphism. -/
theorem directSum_iso_of_componentwise_hom_apply_lof
    {ι : Type*} [DecidableEq ι]
    (ρ σ : ι → Rep k G)
    (e : ∀ i, ρ i ≅ σ i)
    (i : ι) (x : (ρ i).V) :
    ((directSum_iso_of_componentwise ρ σ e).hom.hom :
        DirectSum ι (fun i ↦ (ρ i).V) →ₗ[k] DirectSum ι (fun i ↦ (σ i).V))
      (DirectSum.lof k ι (fun i ↦ (ρ i).V) i x) =
      DirectSum.lof k ι (fun i ↦ (σ i).V) i ((e i).hom.hom x) := by
  simp [directSum_iso_of_componentwise, Representation.equivOfIso]

/-- Helper for Proposition 7-7.3-1: componentwise isomorphisms of the Mackey blocks induce an
isomorphism of the corresponding external direct sums. -/
theorem directSum_isomorphic_of_componentwise
    {ι : Type*}
    (ρ σ : ι → Rep k G)
    (h : ∀ i, IsIsomorphic (ρ i) (σ i)) :
    IsIsomorphic
      (Rep.of (directSum fun i ↦ (ρ i).ρ))
      (Rep.of (directSum fun i ↦ (σ i).ρ)) := by
  classical
  exact ⟨directSum_iso_of_componentwise ρ σ (fun i ↦ Classical.choice (h i))⟩

/-- Helper for Proposition 7-7.3-1: the seed summand `sW` belongs to the unique block labeled by
the double coset of `s`. -/
private theorem seed_left_coset_subrepresentation_le_block
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    inducedLeftCosetFamily H W (s : G ⧸ H) ≤
      doubleCosetBlock K H W (DoubleCoset.mk K H s) := by
  have hs_out :
      DoubleCoset.mk K H (Quotient.out (s : G ⧸ H)) = DoubleCoset.mk K H s := by
    exact
      doubleCoset_mk_eq_of_leftRel K H
        (Quotient.exact' (Quotient.out_eq' (s : G ⧸ H)))
  exact le_iSup_of_le ⟨(s : G ⧸ H), hs_out⟩ le_rfl

/-- Helper for Proposition 7-7.3-1: the seed summand `sW` rebundled as a subrepresentation of the
single double-coset block `V(s)`. -/
private def seed_left_coset_subrepresentation_in_block
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Subrepresentation
      (((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation).comp
        (mackeySubgroup K H s).subtype) :=
  { toSubmodule :=
      (inducedLeftCosetFamily H W (s : G ⧸ H)).comap
        (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro x v hv
      -- The ambient seed summand is already stable under `K ∩ sHs⁻¹`; restricting to the block
      -- just records that the same translated vector still lies in `V(s)`.
      exact (seedLeftCosetSubrepresentation K H W s).apply_mem_toSubmodule x hv }

/-- Helper for Proposition 7-7.3-1: the left-coset summands inside one block, viewed as
submodules of that block. -/
private def doubleCosetBlockFiberFamily
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    {q : G ⧸ H // DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} →
      Submodule k
        ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :=
  fun q ↦
    (inducedLeftCosetFamily H W q.1).comap
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule.subtype

/-- Helper for Proposition 7-7.3-1: any representative of the left coset `sH` determines the
same double-coset label as `s`. -/
private theorem doubleCoset_mk_out_leftCoset_eq
    (K H : Subgroup G) (s : G) :
    DoubleCoset.mk K H (Quotient.out (s : G ⧸ H)) = DoubleCoset.mk K H s := by
  exact
    doubleCoset_mk_eq_of_leftRel K H
      (Quotient.exact' (Quotient.out_eq' (s : G ⧸ H)))

/-- Helper for Proposition 7-7.3-1: a left coset of `mackeySubgroup K H s` in `K` determines the
corresponding ambient left `H`-coset inside the block over `KsH`. -/
private noncomputable def mackey_left_coset_to_fiber
    (K H : Subgroup G) (s : G) :
    K ⧸ mackeySubgroup K H s →
      {q : G ⧸ H // DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} :=
  fun q ↦
    ⟨(q.out : K) • (s : G ⧸ H),
      (doubleCoset_mk_smul_leftCoset K H q.out (s : G ⧸ H)).trans
        (doubleCoset_mk_out_leftCoset_eq K H s)⟩

/-- Helper for Proposition 7-7.3-1: two `K / H_s`-cosets with the same ambient fiber point are
equal. -/
private theorem mackey_left_coset_to_fiber_injective
    (K H : Subgroup G) (s : G) :
    Function.Injective (mackey_left_coset_to_fiber K H s) := by
  intro q₁ q₂ hq
  -- Compare the underlying fiber points and move both sides back to the seed coset `sH`.
  have hsubtype :
      (((q₁.out : K) : G) • (s : G ⧸ H)) = (((q₂.out : K) : G) • (s : G ⧸ H)) := by
    simpa [mackey_left_coset_to_fiber] using congrArg Subtype.val hq
  have hfix :
      (((((q₂.out : K)⁻¹ * q₁.out : K) : K) : G) • (s : G ⧸ H)) = (s : G ⧸ H) := by
    calc
      (((((q₂.out : K)⁻¹ * q₁.out : K) : K) : G) • (s : G ⧸ H)) =
          (((q₂.out : K) : G)⁻¹) • ((((q₁.out : K) : G) • (s : G ⧸ H))) := by
            simp [mul_smul]
      _ = (((q₂.out : K) : G)⁻¹) • ((((q₂.out : K) : G) • (s : G ⧸ H))) := by
            rw [hsubtype]
      _ = (s : G ⧸ H) := by
            simp
  have hmem : ((q₂.out : K)⁻¹ * q₁.out) ∈ mackeySubgroup K H s := by
    exact (mackey_subgroup_iff_fix_leftCoset K H s ((q₂.out : K)⁻¹ * q₁.out)).2 hfix
  have hmem' : q₁.out⁻¹ * q₂.out ∈ mackeySubgroup K H s := by
    simpa using (mackeySubgroup K H s).inv_mem hmem
  -- Quotient equality in `K / (K ∩ sHs⁻¹)` is encoded by the defining setoid relation.
  calc
    q₁ = Quotient.mk'' q₁.out := (Quotient.out_eq' q₁).symm
    _ = Quotient.mk'' q₂.out := by
          apply Quotient.sound
          simpa [QuotientGroup.leftRel_apply] using hmem'
    _ = q₂ := Quotient.out_eq' q₂

/-- Helper for Proposition 7-7.3-1: every ambient left `H`-coset inside the block over `KsH`
comes from some left coset of `mackeySubgroup K H s` in `K`. -/
private theorem mackey_left_coset_to_fiber_surjective
    (K H : Subgroup G) (s : G) :
    Function.Surjective (mackey_left_coset_to_fiber K H s) := by
  intro q
  -- Choose the `K`-part of a witness that `q` lies in the double coset `KsH`.
  rcases (DoubleCoset.eq K H s q.1.out).1 q.2.symm with ⟨x, hxK, h, hhH, hq_out⟩
  let qx : K ⧸ mackeySubgroup K H s := Quotient.mk'' ⟨x, hxK⟩
  refine ⟨qx, ?_⟩
  apply Subtype.ext
  change (((qx.out : K) : G) • (s : G ⧸ H)) = q.1
  have hout_rel :
      QuotientGroup.leftRel (mackeySubgroup K H s)
        qx.out
        ⟨x, hxK⟩ := by
    apply Quotient.exact'
    simpa [qx] using (Quotient.out_eq' qx)
  rw [QuotientGroup.leftRel_apply] at hout_rel
  have hfix :
      (((((qx.out : K)⁻¹ * ⟨x, hxK⟩ : K) : K) : G) • (s : G ⧸ H)) = (s : G ⧸ H) := by
    exact
      (mackey_subgroup_iff_fix_leftCoset K H s ((qx.out : K)⁻¹ * ⟨x, hxK⟩)).1 hout_rel
  have hseed :
      (((qx.out : K) : G) • (s : G ⧸ H)) =
        (x : G) • (s : G ⧸ H) := by
    let t : K := (qx.out : K)⁻¹ * ⟨x, hxK⟩
    have ht : (((t : K) : G) • (s : G ⧸ H)) = (s : G ⧸ H) := by
      simpa [t] using hfix
    calc
      (((qx.out : K) : G) • (s : G ⧸ H)) =
          (((qx.out : K) : G) • (((t : K) : G) • (s : G ⧸ H))) := by
            rw [ht]
      _ = ((((qx.out : K) * t : K) : K) : G) • (s : G ⧸ H) := by
            simp [mul_smul]
      _ = (x : G) • (s : G ⧸ H) := by
            simp [t]
  -- The `H`-component of the double-coset witness disappears in `G / H`.
  calc
    ((((Quotient.mk'' ⟨x, hxK⟩ : K ⧸ mackeySubgroup K H s).out : K) : G) • (s : G ⧸ H)) =
        (x : G) • (s : G ⧸ H) := hseed
    _ = q.1 := by
      calc
        (x : G) • (s : G ⧸ H) = (x * s : G ⧸ H) := rfl
        _ = (x * s * h : G ⧸ H) := by
            apply QuotientGroup.eq.mpr
            simpa [mul_assoc] using hhH
        _ = (q.1.out : G ⧸ H) := by
            rw [hq_out]
        _ = q.1 := Quotient.out_eq' q.1

/-- Helper for Proposition 7-7.3-1: the fiber of `G / H` above the double coset `KsH` is
parametrized by the left cosets of `mackeySubgroup K H s` in `K`. -/
private noncomputable def mackey_left_coset_fiber_equiv
    (K H : Subgroup G) (s : G) :
    K ⧸ mackeySubgroup K H s ≃
      {q : G ⧸ H // DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} := by
  classical
  exact Equiv.ofBijective
    (mackey_left_coset_to_fiber K H s)
    ⟨mackey_left_coset_to_fiber_injective K H s,
      mackey_left_coset_to_fiber_surjective K H s⟩

/-- Helper for Proposition 7-7.3-1: the `K / H_s`-translate of the seed inside the block is the
ambient left-coset summand lying over the corresponding point of the fiber. -/
private theorem doubleCosetBlock_leftQuotientSubmodule_eq
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G)
    (q : K ⧸ mackeySubgroup K H s) :
    Representation.leftQuotientSubmodule
        ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
        (mackeySubgroup K H s)
        (seed_left_coset_subrepresentation_in_block K H W s) q =
      doubleCosetBlockFiberFamily K H W s (mackey_left_coset_fiber_equiv K H s q) := by
  -- Route correction: `toRepresentation` is built from `LinearMap.restrict`, so the stable proof
  -- is to compare membership in the two submodules through the ambient `Ind_H^G(W)` action.
  rw [Representation.leftQuotientSubmodule_out]
  ext v
  constructor
  · intro hv
    rcases Submodule.mem_map.mp hv with ⟨y, hy, rfl⟩
    -- Forgetting the block witness reduces the left side to the ambient translate of `sW`.
    change
      ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ (q.out)
          ((y :
            (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
            Representation.IndV H.subtype W.ρ)) ∈
        inducedLeftCosetFamily H W ((mackey_left_coset_fiber_equiv K H s q).1)
    have hmap :
        (inducedLeftCosetFamily H W (s : G ⧸ H)).map
            ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ (q.out)) =
          inducedLeftCosetFamily H W ((mackey_left_coset_fiber_equiv K H s q).1) := by
      have hfiber :
          ((mackey_left_coset_fiber_equiv K H s q).1 : G ⧸ H) =
            (((q.out : K) : G) • (s : G ⧸ H)) := by
        simp [mackey_left_coset_fiber_equiv, Equiv.ofBijective_apply,
          mackey_left_coset_to_fiber]
        change (((q.out : K) : G) • (s : G ⧸ H)) =
          ((((q.out : K) : G) * s : G) : G ⧸ H)
        rfl
      rw [hfiber]
      exact induced_leftCoset_family_map H W (((q.out : K) : G)) (s : G ⧸ H)
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨_, hy, rfl⟩
  · intro hv
    -- Conversely, every vector in the target fiber summand comes from a seed vector in the block.
    change
      ((v :
        (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
        Representation.IndV H.subtype W.ρ) ∈
        inducedLeftCosetFamily H W ((mackey_left_coset_fiber_equiv K H s q).1) at hv
    have hmap :
        (inducedLeftCosetFamily H W (s : G ⧸ H)).map
            ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ (q.out)) =
          inducedLeftCosetFamily H W ((mackey_left_coset_fiber_equiv K H s q).1) := by
      have hfiber :
          ((mackey_left_coset_fiber_equiv K H s q).1 : G ⧸ H) =
            (((q.out : K) : G) • (s : G ⧸ H)) := by
        simp [mackey_left_coset_fiber_equiv, Equiv.ofBijective_apply,
          mackey_left_coset_to_fiber]
        change (((q.out : K) : G) • (s : G ⧸ H)) =
          ((((q.out : K) : G) * s : G) : G ⧸ H)
        rfl
      rw [hfiber]
      exact induced_leftCoset_family_map H W (((q.out : K) : G)) (s : G ⧸ H)
    rw [← hmap] at hv
    rcases Submodule.mem_map.mp hv with ⟨y, hy, hyv⟩
    refine Submodule.mem_map.mpr ?_
    refine ⟨⟨y, seed_left_coset_subrepresentation_le_block K H W s hy⟩, hy, ?_⟩
    apply Subtype.ext
    change ((Rep.res K.subtype (Rep.ind H.subtype W)).ρ (q.out) y :
        Representation.IndV H.subtype W.ρ) = v
    exact hyv

/-- Helper for Proposition 7-7.3-1: decidable equality on the ambient left-coset quotient, so
fiber subtypes use Lean's standard `Subtype.instDecidableEq`. -/
private noncomputable instance leftQuotientDecidableEq (H : Subgroup G) :
    DecidableEq (G ⧸ H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.3-1: restricting the ambient `G / H`-indexed internal family to
the fiber over the double coset `KsH` yields an internal decomposition of the block `V(s)`. -/
private theorem doubleCosetBlockFiberFamily_is_internal
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    DirectSum.IsInternal (doubleCosetBlockFiberFamily K H W s) := by
  classical
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  let A : G ⧸ H → Submodule k (Representation.IndV H.subtype W.ρ) := inducedLeftCosetFamily H W
  have hAmbient : DirectSum.IsInternal A := by
    -- The full `G / H`-family is already the internal induced decomposition from Proposition `7-7.1-1`.
    simpa [A, inducedLeftCosetFamily, Representation.IsInducedFromSubrepresentation] using
      induced_identity_copy_is_induced H W
  have hFiberIndep :
      iSupIndep
        (fun q : {q : G ⧸ H // DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} ↦ A q) := by
    -- Restrict independence to the left-coset summands lying above the fixed double-coset fiber.
    exact hAmbient.submodule_iSupIndep.comp Subtype.coe_injective
  have hblock :
      doubleCosetBlock K H W (DoubleCoset.mk K H s) =
        ⨆ q ∈ {q : G ⧸ H | DoubleCoset.mk K H q.out = DoubleCoset.mk K H s}, A q := by
    -- The block over `KsH` is, by definition, the supremum of exactly the left-coset summands in
    -- that fiber.
    simpa [A, doubleCosetBlock] using
      (iSup_subtype''
        {q : G ⧸ H | DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} A)
  have hRestricted := by
    -- Mathlib already proves that any independent subfamily remains internal inside its `biSup`.
    exact
      DirectSum.isInternal_biSup_submodule_of_iSupIndep
        {q : G ⧸ H | DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} hFiberIndep
  have hblock' :
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule =
        ⨆ q ∈ {q : G ⧸ H | DoubleCoset.mk K H q.out = DoubleCoset.mk K H s}, A q := by
    simpa [doubleCosetBlockSubrepresentation] using hblock
  have hfamily :
      doubleCosetBlockFiberFamily K H W s =
        (fun q : {q : G ⧸ H // DoubleCoset.mk K H q.out = DoubleCoset.mk K H s} ↦
          Submodule.comap
            ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule.subtype)
            (A q)) := by
    funext q
    rfl
  -- Identifying the `biSup` carrier with the concrete block turns the standard restricted family
  -- into `doubleCosetBlockFiberFamily K H W s`.
  rw [hfamily]
  rw [hblock']
  exact hRestricted

/-- Helper for Proposition 7-7.3-1: one block `V(s)` is induced from its seed translate `sW`
with stabilizer `K ∩ sHs⁻¹`. -/
private theorem doubleCosetBlock_is_induced_from_seed
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Representation.IsInducedFromSubrepresentation
      ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
      (mackeySubgroup K H s)
      (seed_left_coset_subrepresentation_in_block K H W s) := by
  classical
  letI : DecidableEq (K ⧸ mackeySubgroup K H s) := Classical.decEq _
  let e := mackey_left_coset_fiber_equiv K H s
  have hfiber_internal : DirectSum.IsInternal (doubleCosetBlockFiberFamily K H W s) := by
    -- The block is the internal sum of the ambient left-coset summands lying over `KsH`.
    exact doubleCosetBlockFiberFamily_is_internal K H W s
  have hleft_fun :
      Representation.leftQuotientSubmodule
          ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
          (mackeySubgroup K H s)
          (seed_left_coset_subrepresentation_in_block K H W s) =
        doubleCosetBlockFiberFamily K H W s ∘ e := by
    -- Reindex the block owner's translate family by the explicit orbit-stabilizer equivalence.
    funext q
    simpa [e, Function.comp] using doubleCosetBlock_leftQuotientSubmodule_eq K H W s q
  have hindep :
      iSupIndep
        (Representation.leftQuotientSubmodule
          ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
          (mackeySubgroup K H s)
          (seed_left_coset_subrepresentation_in_block K H W s)) := by
    rw [hleft_fun]
    exact hfiber_internal.submodule_iSupIndep.comp e.injective
  have hspan :
      iSup
        (Representation.leftQuotientSubmodule
          ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
          (mackeySubgroup K H s)
          (seed_left_coset_subrepresentation_in_block K H W s)) =
        ⊤ := by
    -- The same reindexing carries the spanning statement from the fiber family to the block owner.
    calc
      iSup
          (Representation.leftQuotientSubmodule
            ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
            (mackeySubgroup K H s)
            (seed_left_coset_subrepresentation_in_block K H W s)) =
          iSup (doubleCosetBlockFiberFamily K H W s ∘ e) := by
            rw [hleft_fun]
      _ = iSup (doubleCosetBlockFiberFamily K H W s) := by
            simpa [Function.comp] using
              (Equiv.iSup_comp (g := doubleCosetBlockFiberFamily K H W s) e)
      _ = ⊤ := hfiber_internal.submodule_iSup_eq_top
  -- Package the transported independence and spanning statements as inducedness.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Proposition 7-7.3-1: forgetting that the seed lies inside one block recovers the
ambient seed summand `sW`. -/
private noncomputable def seed_left_coset_subrepresentation_in_block_linearEquiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (seed_left_coset_subrepresentation_in_block K H W s).toSubmodule ≃ₗ[k]
      (seedLeftCosetSubrepresentation K H W s).toSubmodule :=
  Submodule.comapSubtypeEquivOfLe (seed_left_coset_subrepresentation_le_block K H W s)

/-- Helper for Proposition 7-7.3-1: the block-seed copy and the ambient seed copy carry the same
`K ∩ sHs⁻¹`-action. -/
private theorem seed_left_coset_subrepresentation_in_block_linearEquiv_intertwines
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    ∀ x,
      (seed_left_coset_subrepresentation_in_block_linearEquiv K H W s).toLinearMap ∘ₗ
          (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation x =
        (seedLeftCosetSubrepresentation K H W s).toRepresentation x ∘ₗ
          (seed_left_coset_subrepresentation_in_block_linearEquiv K H W s).toLinearMap := by
  intro x
  -- Both representations are just codomain restrictions of the same ambient action.
  ext v
  rfl

/-- Helper for Proposition 7-7.3-1: the seed inside the block is equivariantly the same as the
ambient seed summand `sW`. -/
private noncomputable def seed_left_coset_subrepresentation_in_block_equiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation.Equiv
      (seedLeftCosetSubrepresentation K H W s).toRepresentation :=
  Representation.Equiv.mk
    (seed_left_coset_subrepresentation_in_block_linearEquiv K H W s)
    (seed_left_coset_subrepresentation_in_block_linearEquiv_intertwines K H W s)

/-- Helper for Proposition 7-7.3-1: the seed inside the block is identified with the
conjugate-twist source of the Mackey summand. -/
private noncomputable def mackey_block_source_equiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation.Equiv
      (mackeyTwist K H W s).ρ :=
  (seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
    (seedLeftCosetEquiv K H W s).symm

/-- Helper for Proposition 7-7.3-1: the induced map obtained from the source equivalence. -/
private noncomputable def mackey_block_inducedSourceHom
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (Representation.ind (mackeySubgroup K H s).subtype
        (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation).IntertwiningMap
      (Representation.ind (mackeySubgroup K H s).subtype (mackeyTwist K H W s).ρ) :=
  let eSource := mackey_block_source_equiv K H W s
  { toLinearMap := Representation.Coinvariants.map _ _
      (eSource.toLinearMap.lTensor _)
      (by
        simp [LinearMap.lTensor_comp_map, eSource.toIntertwiningMap.2,
          LinearMap.map_comp_lTensor])
    isIntertwining' := by
      intro g
      ext h a
      simp [Representation.ind_mk] }

/-- Helper for Proposition 7-7.3-1: inverse induced map obtained from the source equivalence. -/
private noncomputable def mackey_block_inducedSourceInv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (Representation.ind (mackeySubgroup K H s).subtype (mackeyTwist K H W s).ρ).IntertwiningMap
      (Representation.ind (mackeySubgroup K H s).subtype
        (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation) :=
  let eSource := mackey_block_source_equiv K H W s
  { toLinearMap := Representation.Coinvariants.map _ _
      (eSource.symm.toLinearMap.lTensor _)
      (by
        intro g
        ext x y
        simpa using
          congrArg
            (fun z ↦ (Finsupp.single (↑g * x) (1 : k)) ⊗ₜ[k] z)
            (LinearMap.congr_fun (eSource.symm.toIntertwiningMap.2 g) y))
    isIntertwining' := by
      intro g
      ext h a
      simp }

private theorem mackey_block_inducedSource_inv_hom
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (mackey_block_inducedSourceInv K H W s).toLinearMap ∘ₗ
        (mackey_block_inducedSourceHom K H W s).toLinearMap = LinearMap.id := by
  apply Representation.IndV.hom_ext
  intro h
  ext a
  simp [mackey_block_inducedSourceHom, mackey_block_inducedSourceInv]

private theorem mackey_block_inducedSource_hom_inv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (mackey_block_inducedSourceHom K H W s).toLinearMap ∘ₗ
        (mackey_block_inducedSourceInv K H W s).toLinearMap = LinearMap.id := by
  apply Representation.IndV.hom_ext
  intro h
  ext a
  simp [mackey_block_inducedSourceHom, mackey_block_inducedSourceInv]

/-- Helper for Proposition 7-7.3-1: the induced source equivalence between the block seed
model and the conjugate-twist model. -/
private noncomputable def mackey_block_inducedSourceEquiv
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    (Representation.ind (mackeySubgroup K H s).subtype
        (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation).Equiv
      (Representation.ind (mackeySubgroup K H s).subtype (mackeyTwist K H W s).ρ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear
      (mackey_block_inducedSourceHom K H W s).toLinearMap
      (mackey_block_inducedSourceInv K H W s).toLinearMap
      (mackey_block_inducedSource_hom_inv K H W s)
      (mackey_block_inducedSource_inv_hom K H W s))
    (mackey_block_inducedSourceHom K H W s).isIntertwining'

/-- Helper for Proposition 7-7.3-1: the block `V(s)` is explicitly identified with the Mackey
summand `Ind_{K ∩ sHs⁻¹}^K(W^s)`. -/
private noncomputable def doubleCosetBlock_mackeySummand_iso
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    Rep.of ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation) ≅
      mackeySummand K H W s := by
  let ρblock := (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation
  let U := seed_left_coset_subrepresentation_in_block K H W s
  have hInduced : ρblock.IsInducedFromSubrepresentation (mackeySubgroup K H s) U := by
    -- The previous theorem has already identified the single block `V(s)` as induced from `sW`.
    simpa [ρblock, U] using doubleCosetBlock_is_induced_from_seed K H W s
  have hIsoHom : IsIso (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U) := by
    -- Proposition `7-7.1-1` converts inducedness into invertibility of the universal induction map.
    exact
      (Representation.isInducedFromSubrepresentation_iff_isIso_inducedFromSubrepresentationHom
        ρblock (mackeySubgroup K H s) U).1 hInduced
  letI : IsIso (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U) := hIsoHom
  -- Replace the inducing source `sW` inside the block by the conjugate-twist model `W^s`.
  simpa [mackeySummand, ρblock, U] using
    ((CategoryTheory.asIso (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U)).symm ≪≫
      Rep.mkIso (mackey_block_inducedSourceEquiv K H W s))

/-- Helper for Proposition 7-7.3-1: the source equivalence inverse sends a Mackey coefficient
back to the same ambient translated seed inside the block seed subrepresentation. -/
private theorem mackey_block_source_equiv_symm_apply_seed
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G)
    (x : mackeyTwist K H W s) :
    let U := seed_left_coset_subrepresentation_in_block K H W s
    let eSource : U.toRepresentation.Equiv (mackeyTwist K H W s).ρ :=
      (seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
        (seedLeftCosetEquiv K H W s).symm
    (((eSource.symm.toLinearMap x : U.toSubmodule) :
        (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
      Representation.IndV H.subtype W.ρ) =
      Representation.IndV.mk H.subtype W.ρ s⁻¹ x := by
  classical
  dsimp
  change
    ((((seed_left_coset_subrepresentation_in_block_linearEquiv K H W s).symm
        ((seedLeftCosetLinearEquiv K H W s) x) :
      (seed_left_coset_subrepresentation_in_block K H W s).toSubmodule) :
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
      Representation.IndV H.subtype W.ρ) =
      Representation.IndV.mk H.subtype W.ρ s⁻¹ x
  simpa [seed_left_coset_subrepresentation_in_block_linearEquiv] using
    seedLeftCosetLinearEquiv_apply K H W s x

/-- Helper for Proposition 7-7.3-1: the induced-from-subrepresentation comparison map sends
the unit source seed back to the original block seed. -/
private theorem mackey_block_inducedFromSubrepresentationHom_apply_source_seed
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G)
    (x : mackeyTwist K H W s)
    (hx : Representation.IndV.mk H.subtype W.ρ s⁻¹ x ∈
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
    let ρblock := (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation
    let U := seed_left_coset_subrepresentation_in_block K H W s
    let eSource : U.toRepresentation.Equiv (mackeyTwist K H W s).ρ :=
      (seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
        (seedLeftCosetEquiv K H W s).symm
    (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U).hom
        (Representation.IndV.mk (mackeySubgroup K H s).subtype U.toRepresentation 1
          (eSource.symm.toLinearMap x)) =
      (⟨Representation.IndV.mk H.subtype W.ρ s⁻¹ x, hx⟩ :
        (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) := by
  classical
  dsimp
  have hsource := mackey_block_source_equiv_symm_apply_seed K H W s x
  calc
    (Rep.Hom.hom
        (((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation).inducedFromSubrepresentationHom
          (mackeySubgroup K H s) (seed_left_coset_subrepresentation_in_block K H W s)))
        (Representation.IndV.mk (mackeySubgroup K H s).subtype
          (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation 1
          (((seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
            (seedLeftCosetEquiv K H W s).symm).symm.toLinearMap x))
        = ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation 1⁻¹)
            (((seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
              (seedLeftCosetEquiv K H W s).symm).symm.toLinearMap x) := by
          exact Representation.inducedFromSubrepresentationHom_mk
            ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation)
            (mackeySubgroup K H s)
            (seed_left_coset_subrepresentation_in_block K H W s)
            (1 : K)
            (((seed_left_coset_subrepresentation_in_block_equiv K H W s).trans
              (seedLeftCosetEquiv K H W s).symm).symm.toLinearMap x)
    _ = (⟨Representation.IndV.mk H.subtype W.ρ s⁻¹ x, hx⟩ :
        (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) := by
          ext
          simpa using hsource


/-- Helper for Proposition 7-7.3-1: the named induced source map sends the unit seed to the
unit seed with the transported coefficient. -/
private theorem mackey_block_inducedSourceHom_apply_source_seed
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G)
    (x : mackeyTwist K H W s) :
    (mackey_block_inducedSourceHom K H W s).toLinearMap
        (Representation.IndV.mk (mackeySubgroup K H s).subtype
          (seed_left_coset_subrepresentation_in_block K H W s).toRepresentation 1
          ((mackey_block_source_equiv K H W s).symm.toLinearMap x)) =
      Representation.IndV.mk
        (mackeySubgroup K H s).subtype
        ((mackeyTwist K H W s).ρ)
        1 x := by
  simpa [mackey_block_inducedSourceHom] using
    congrArg
      (fun y ↦
        Representation.IndV.mk
          (mackeySubgroup K H s).subtype
          ((mackeyTwist K H W s).ρ)
          1 y)
      ((mackey_block_source_equiv K H W s).toLinearEquiv.apply_symm_apply x)

/-- Helper for Proposition 7-7.3-1: the block-to-Mackey isomorphism sends the block seed to
the standard induced seed in the Mackey summand. -/
private theorem doubleCosetBlock_mackeySummand_iso_hom_apply_seed
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G)
    (x : mackeyTwist K H W s)
    (hx : Representation.IndV.mk H.subtype W.ρ s⁻¹ x ∈
      (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule) :
    (doubleCosetBlock_mackeySummand_iso K H W s).hom.hom
        (⟨Representation.IndV.mk H.subtype W.ρ s⁻¹ x, hx⟩ :
          (doubleCosetBlockSubrepresentation K H W
            (DoubleCoset.mk K H s)).toSubmodule) =
      Representation.IndV.mk
        (mackeySubgroup K H s).subtype
        ((mackeyTwist K H W s).ρ)
        1 x := by
  classical
  let ρblock := (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation
  let U := seed_left_coset_subrepresentation_in_block K H W s
  have hInduced : ρblock.IsInducedFromSubrepresentation (mackeySubgroup K H s) U := by
    simpa [ρblock, U] using doubleCosetBlock_is_induced_from_seed K H W s
  have hIsoHom : IsIso (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U) := by
    exact
      (Representation.isInducedFromSubrepresentation_iff_isIso_inducedFromSubrepresentationHom
        ρblock (mackeySubgroup K H s) U).1 hInduced
  letI : IsIso (ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U) := hIsoHom
  let eSource : U.toRepresentation.Equiv (mackeyTwist K H W s).ρ :=
    mackey_block_source_equiv K H W s
  let f := ρblock.inducedFromSubrepresentationHom (mackeySubgroup K H s) U
  let sourceSeed :=
    Representation.IndV.mk (mackeySubgroup K H s).subtype U.toRepresentation 1
      (eSource.symm.toLinearMap x)
  let yBlock : (doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toSubmodule :=
    ⟨Representation.IndV.mk H.subtype W.ρ s⁻¹ x, hx⟩
  have hpreimage : f.hom sourceSeed = yBlock := by
    simpa [f, sourceSeed, eSource, yBlock, ρblock, U] using
      mackey_block_inducedFromSubrepresentationHom_apply_source_seed K H W s x hx
  have hinv_pre : (CategoryTheory.asIso f).inv.hom (f.hom sourceSeed) = sourceSeed := by
    exact Iso.hom_inv_id_apply (CategoryTheory.asIso f) sourceSeed
  have hinv : (CategoryTheory.asIso f).inv.hom yBlock = sourceSeed := by
    exact hpreimage ▸ hinv_pre
  change
    (mackey_block_inducedSourceHom K H W s).toLinearMap
        ((CategoryTheory.asIso f).inv.hom yBlock) =
      Representation.IndV.mk
        (mackeySubgroup K H s).subtype
        ((mackeyTwist K H W s).ρ)
        1 x
  rw [hinv]
  simpa [sourceSeed, eSource, U] using
    mackey_block_inducedSourceHom_apply_source_seed K H W s x

/-- Helper for Proposition 7-7.3-1: the block `V(s)` is `K`-isomorphic to the Mackey summand
`Ind_{K ∩ sHs⁻¹}^K(W^s)`. -/
private theorem doubleCosetBlock_isomorphic_mackeySummand
    (K H : Subgroup G) (W : Rep.{w} k H) (s : G) :
    IsIsomorphic
      (Rep.of ((doubleCosetBlockSubrepresentation K H W (DoubleCoset.mk K H s)).toRepresentation))
      (mackeySummand K H W s) := by
  exact ⟨doubleCosetBlock_mackeySummand_iso K H W s⟩

-- Proof sketch: decompose the underlying induced module as the direct sum of the `K`-stable
-- subspaces coming from the double cosets `K * s i * H`, identify each summand with the
-- induction from `mackeySubgroup K H (s i)`, and then pass to an isomorphism in
-- `Rep k K`.
/-- Proposition 7-7.3-1: if `s : ι → G` is a system of representatives for `K \ G / H`, then the
restriction of `Ind_H^G(W)` to `K` is isomorphic to the direct sum of the induced
representations `Ind_{K ∩ s(i)Hs(i)⁻¹}^K(W^{s(i)})`. -/
noncomputable def restriction_induced_mackeyDirectSum_iso
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    Rep.res K.subtype (Rep.ind H.subtype W) ≅
      Rep.of (directSum fun i ↦ (mackeySummand K H W (s i)).ρ) := by
  exact
    restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs ≪≫
      directSum_iso_of_componentwise
        (fun i ↦
          Rep.of
            ((doubleCosetBlockSubrepresentation K H W
              (DoubleCoset.mk K H (s i))).toRepresentation))
        (fun i ↦ mackeySummand K H W (s i))
        (fun i ↦ doubleCosetBlock_mackeySummand_iso K H W (s i))

theorem restriction_induced_isomorphic_mackeyDirectSum
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    IsIsomorphic
      (Rep.res K.subtype (Rep.ind H.subtype W))
      (Rep.of (directSum fun i ↦ (mackeySummand K H W (s i)).ρ)) := by
  classical
  exact ⟨restriction_induced_mackeyDirectSum_iso K H W s hs⟩

/-- Helper for Proposition 7-7.3-1: the underlying vector-space family of the Mackey direct sum. -/
private abbrev mackeyDirectSumVFamily
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G) (j : ι) :=
  Representation.IndV
    (mackeySubgroup K H (s j)).subtype
    ((mackeyTwist K H W (s j)).ρ)

/-- Helper for Proposition 7-7.3-1: the target vector space of the explicit Mackey direct sum. -/
private abbrev mackeyDirectSumV
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G) :=
  DirectSum ι (mackeyDirectSumVFamily K H W s)

/-- Helper for Proposition 7-7.3-1: the concrete linear map underlying the Mackey direct-sum
isomorphism.  Naming it keeps later seed-computation statements small enough for elaboration. -/
@[irreducible]
private noncomputable def restrictionInducedMackeyDirectSumLinearMap
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i)) :
    Representation.IndV H.subtype W.ρ →ₗ[k] mackeyDirectSumV K H W s :=
  (restriction_induced_mackeyDirectSum_iso
    (k := k) (K := K) (H := H) (W := W) (s := s) hs).hom.hom

/-- Helper for Proposition 7-7.3-1: the translated seed in `Ind_H^G W`. -/
@[irreducible]
private noncomputable def restrictionInducedTranslatedSeed
    {ι : Type w} (H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    (i : ι) (x : mackeyTwist K H W (s i)) :
    Representation.IndV H.subtype W.ρ :=
  Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x

/-- Helper for Proposition 7-7.3-1: the corresponding seed in the `i`-th Mackey summand. -/
@[irreducible]
private noncomputable def mackeyDirectSumSeed
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι] (i : ι) (x : mackeyTwist K H W (s i)) :
    mackeyDirectSumV K H W s :=
  DirectSum.lof k _
    (mackeyDirectSumVFamily K H W s)
    i
    (Representation.IndV.mk
      (mackeySubgroup K H (s i)).subtype
      ((mackeyTwist K H W (s i)).ρ)
      1 x)

-- The seed-computation statement still expands a selected-block iso followed by a componentwise
-- Mackey direct-sum iso; the proof below keeps those expansions localized.
/-- Helper for Proposition 7-7.3-1: the explicit Mackey direct-sum isomorphism sends the
translated generator `IndV.mk ... (s i)⁻¹ x` to the `i`-th Mackey seed `DirectSum.lof ... 1 x`. -/
theorem restriction_induced_isomorphic_mackeyDirectSum_hom_apply_translated_seed
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i))
    (i : ι) (x : mackeyTwist K H W (s i)) :
    restrictionInducedMackeyDirectSumLinearMap K H W s hs
      (restrictionInducedTranslatedSeed (K := K) H W s i x) =
    mackeyDirectSumSeed K H W s i x := by
  classical
  unfold restrictionInducedMackeyDirectSumLinearMap
    restrictionInducedTranslatedSeed mackeyDirectSumSeed
  change
    (restriction_induced_mackeyDirectSum_iso
      (k := k) (K := K) (H := H) (W := W) (s := s) hs).hom.hom
      (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x) =
      DirectSum.lof k _
        (mackeyDirectSumVFamily K H W s)
        i
        (Representation.IndV.mk
          (mackeySubgroup K H (s i)).subtype
          ((mackeyTwist K H W (s i)).ρ)
          1 x)
  let seed : Representation.IndV H.subtype W.ρ :=
    Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x
  let ℳ : ι → Submodule k (Representation.IndV H.subtype W.ρ) :=
    fun j ↦
      (doubleCosetBlockSubrepresentation K H W
        (DoubleCoset.mk K H (s j))).toSubmodule
  have hseedMem : seed ∈ inducedLeftCosetFamily H W (s i : G ⧸ H) := by
    rw [seedLeftCosetFamily_eq_range]
    exact ⟨x, rfl⟩
  have hblockMem : seed ∈ ℳ i := by
    exact seed_left_coset_subrepresentation_le_block K H W (s i) hseedMem
  let y : ℳ i := ⟨seed, hblockMem⟩
  have hfirst :
      ((restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs).hom.hom :
          Representation.IndV H.subtype W.ρ →ₗ[k]
            DirectSum ι
              (fun j ↦
                (doubleCosetBlockSubrepresentation K H W
                  (DoubleCoset.mk K H (s j))).toSubmodule))
        seed = DirectSum.lof k _
          (fun j ↦
            (doubleCosetBlockSubrepresentation K H W
              (DoubleCoset.mk K H (s j))).toSubmodule)
          i y := by
    simpa [ℳ, y, seed] using
      restriction_induced_selectedDoubleCosetBlocks_iso_hom_apply_seed K H W s hs i x hblockMem
  have hcomponent :
      (doubleCosetBlock_mackeySummand_iso K H W (s i)).hom.hom
          (y : (doubleCosetBlockSubrepresentation K H W
            (DoubleCoset.mk K H (s i))).toSubmodule) =
        Representation.IndV.mk
          (mackeySubgroup K H (s i)).subtype
          ((mackeyTwist K H W (s i)).ρ)
          1 x := by
    simpa [ℳ, y, seed] using
      doubleCosetBlock_mackeySummand_iso_hom_apply_seed K H W (s i) x hblockMem
  have hfirst' :
      ((restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs).hom.hom :
          Representation.IndV H.subtype W.ρ →ₗ[k]
            DirectSum ι
              (fun j ↦
                (doubleCosetBlockSubrepresentation K H W
                  (DoubleCoset.mk K H (s j))).toSubmodule))
        (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x) =
        DirectSum.lof k _
          (fun j ↦
            (doubleCosetBlockSubrepresentation K H W
              (DoubleCoset.mk K H (s j))).toSubmodule)
          i y := by
    simpa [seed] using hfirst
  let ρblock : ι → Rep k K :=
    fun j ↦
      Rep.of
        ((doubleCosetBlockSubrepresentation K H W
          (DoubleCoset.mk K H (s j))).toRepresentation)
  let σmackey : ι → Rep k K := fun j ↦ mackeySummand K H W (s j)
  let ecomp : ∀ j, ρblock j ≅ σmackey j :=
    fun j ↦ doubleCosetBlock_mackeySummand_iso K H W (s j)
  let compIso := directSum_iso_of_componentwise ρblock σmackey ecomp
  have hcompLof :
      (compIso.hom.hom :
          DirectSum ι (fun j ↦ (ρblock j).V) →ₗ[k]
            DirectSum ι (fun j ↦ (σmackey j).V))
        (DirectSum.lof k ι (fun j ↦ (ρblock j).V) i
          (y : (ρblock i).V)) =
        DirectSum.lof k ι (fun j ↦ (σmackey j).V) i
          ((ecomp i).hom.hom (y : (ρblock i).V)) := by
    exact directSum_iso_of_componentwise_hom_apply_lof ρblock σmackey ecomp i
      (y : (ρblock i).V)
  calc
    (restriction_induced_mackeyDirectSum_iso
      (k := k) (K := K) (H := H) (W := W) (s := s) hs).hom.hom
      (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x) =
        compIso.hom.hom
          (((restriction_induced_selectedDoubleCosetBlocks_iso K H W s hs).hom.hom :
              Representation.IndV H.subtype W.ρ →ₗ[k]
                DirectSum ι (fun j ↦ (ρblock j).V))
            (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x)) := by
      simp [restriction_induced_mackeyDirectSum_iso, compIso, ρblock, σmackey, ecomp]
    _ = compIso.hom.hom
        (DirectSum.lof k ι (fun j ↦ (ρblock j).V) i
          (y : (ρblock i).V)) := by
      exact congrArg compIso.hom.hom (by simpa [ρblock] using hfirst')
    _ = DirectSum.lof k ι (fun j ↦ (σmackey j).V) i
          ((ecomp i).hom.hom (y : (ρblock i).V)) := hcompLof
    _ = DirectSum.lof k _
          (mackeyDirectSumVFamily K H W s)
          i
          (Representation.IndV.mk
            (mackeySubgroup K H (s i)).subtype
            ((mackeyTwist K H W (s i)).ρ)
            1 x) := by
      simpa [σmackey, ecomp, ρblock, mackeySummand, mackeyDirectSumVFamily] using
        congrArg
          (DirectSum.lof k ι (fun j ↦ (σmackey j).V) i)
          hcomponent

/-- Helper for Proposition 7-7.3-1: the Mackey direct-sum isomorphism sends the translated
generator `IndV.mk ... (s i)⁻¹ x` to the explicit `i`-th summand seed. -/
theorem restriction_induced_mackeyDirectSum_iso_hom_apply_translated_seed
    {ι : Type w} (K H : Subgroup G) (W : Rep.{w} k H) (s : ι → G)
    [DecidableEq ι]
    (hs : Function.Bijective fun i ↦ DoubleCoset.mk K H (s i))
    (i : ι) (x : mackeyTwist K H W (s i)) :
    ((restriction_induced_mackeyDirectSum_iso
        (k := k) (K := K) (H := H) (W := W) (s := s) hs).hom.hom
      (Representation.IndV.mk H.subtype W.ρ (s i)⁻¹ x)) =
      DirectSum.lof k _
        (fun j ↦
          Representation.IndV
            (mackeySubgroup K H (s j)).subtype
            ((mackeyTwist K H W (s j)).ρ))
        i
        (Representation.IndV.mk
          (mackeySubgroup K H (s i)).subtype
          ((mackeyTwist K H W (s i)).ρ)
          1 x) := by
  -- The previous seed theorem is stated through local abbreviations; unfold them here so later
  -- files can use the explicit public map without depending on private names.
  simpa [restrictionInducedMackeyDirectSumLinearMap, restrictionInducedTranslatedSeed,
    mackeyDirectSumSeed] using
    restriction_induced_isomorphic_mackeyDirectSum_hom_apply_translated_seed
      (k := k) K H W s hs i x

end

section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {W : Type w} [AddCommGroup W] [Module k W]

private def conjugateSubrepresentationOrderIso
    {H : Subgroup G} [H.Normal] (ρ : Representation k H W) (s : G) :
    Subrepresentation (ρ ^ s) ≃o Subrepresentation ρ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule g x hx := by
        rcases (MulAut.conjNormal s⁻¹).surjective g with ⟨h, rfl⟩
        exact U.apply_mem_toSubmodule h hx }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule g x hx := by
        exact U.apply_mem_toSubmodule ((MulAut.conjNormal s⁻¹) g) hx }
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv U := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro U V
    rfl

namespace IsIrreducible

-- Proof sketch: conjugation by `s` acts on `H` through the automorphism
-- `MulAut.conjNormal s⁻¹ : H ≃* H`, and the invariant-subspace lattice of `ρ ^ s` is therefore
-- order-isomorphic to that of `ρ` via the identity submodule on `W`.
/-- Conjugating a representation of a normal subgroup preserves irreducibility. -/
theorem pow {H : Subgroup G} [H.Normal]
    (ρ : Representation k H W) [ρ.IsIrreducible] (s : G) :
    (ρ ^ s).IsIrreducible := by
  exact (conjugateSubrepresentationOrderIso ρ s).isSimpleOrder_iff.mpr inferInstance

end IsIrreducible

end

end Representation
