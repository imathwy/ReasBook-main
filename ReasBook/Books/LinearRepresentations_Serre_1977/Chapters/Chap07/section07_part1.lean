import Mathlib
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Induced

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_7_7_1_1 (from Chap07) -/
open CategoryTheory Rep

universe u v w

namespace Representation

section

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {V : Type (max u v w)} [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V) (H : Subgroup G)
variable (W : Subrepresentation (ρ.comp H.subtype))

-- Source/core/bridge triage for Proposition 7-7.1-1:
-- * source-facing: LinearRepresentations_Serre_1977's criterion that `ρ` is induced from the `H`-stable subrepresentation
--   `W` exactly when the canonical comparison `Ind_H^G(W) ⟶ ρ` is an isomorphism.
-- * core/canonical owners sampled in the induction domain:
--   `Representation.IsInducedFromSubrepresentation`, `Rep.ind`, `Rep.indResHomEquiv`, and
--   `CategoryTheory.ConcreteCategory.isIso_iff_bijective`.
-- * primitive data: `ρ`, `H`, `W`, and the inclusion `W ↪ Res_H^G(ρ)`.
-- * derived API: the comparison morphism obtained by transporting that inclusion across
--   Frobenius reciprocity.

-- Proposition 7-7.1-1: a representation `ρ` is induced by the `H`-stable subrepresentation `W`
-- if and only if the canonical adjunction morphism from `Ind_H^G(W)` to `ρ` is an isomorphism.
-- Proof sketch: first identify postcomposition with the canonical adjunction morphism with the
-- Chapter 3 restriction map on intertwining spaces. Then `isIso_iff_coyoneda_map_bijective`
-- turns the isomorphism condition into bijectivity of all those restriction maps. The forward
-- implication is exactly Lemma `3-3.3-2`; the reverse structural converse is isolated below.
/-- Helper for Proposition 7-7.1-1: under Frobenius reciprocity, postcomposition with the
canonical map `Ind_H^G(W) ⟶ ρ` is exactly the Chapter 3 restriction map on intertwining spaces. -/
theorem postcompose_inducedFromSubrepresentationHom_eq_restrictIntertwiningMap
    {V' : Type (max u v w)} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V') (F : ρ.IntertwiningMap ρ') :
    (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
        (inducedFromSubrepresentationHom ρ H W ≫
          (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F) =
      Rep.ofHom (restrictIntertwiningMap ρ H W ρ' F) := by
  -- Evaluate the Frobenius-reciprocity image at the unit coset generator.
  ext w
  change
    ((inducedFromSubrepresentationHom ρ H W ≫
        (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F).hom
      (IndV.mk H.subtype W.toRepresentation 1 w) = F w)
  simp [inducedFromSubrepresentationHom]
  rfl

/-- Helper for Proposition 7-7.1-1: rebundling the `IntertwiningMap` produced from
`indResHomEquiv` recovers the original categorical morphism. -/
theorem ofHom_homLinearEquiv_indResHomEquiv
    {V' : Type (max u v w)} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V')
    (f : Rep.ind H.subtype (Rep.of W.toRepresentation) ⟶ Rep.of ρ') :
    Rep.ofHom
        (Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ'))
          ((Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) f)) =
      (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) f := by
  rfl

/-- Helper for Proposition 7-7.1-1: the categorical postcomposition map associated with
`inducedFromSubrepresentationHom` is bijective exactly when the Chapter 3 restriction map is. -/
theorem bijective_postcompose_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap
    {V' : Type (max u v w)} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V') :
    Function.Bijective
        (fun (g : Rep.of ρ ⟶ Rep.of ρ') ↦ inducedFromSubrepresentationHom ρ H W ≫ g) ↔
      Function.Bijective (restrictIntertwiningMap ρ H W ρ') := by
  constructor
  · intro h
    constructor
    · intro F F' hFF'
      -- Transport equality of restrictions back through Frobenius reciprocity.
      have hpostEq :
          (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
              (inducedFromSubrepresentationHom ρ H W ≫
                (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F) =
            (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
              (inducedFromSubrepresentationHom ρ H W ≫
                (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F') := by
        calc
          (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
              (inducedFromSubrepresentationHom ρ H W ≫
                (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F) =
              Rep.ofHom (restrictIntertwiningMap ρ H W ρ' F) := by
                simpa using
                  postcompose_inducedFromSubrepresentationHom_eq_restrictIntertwiningMap
                    (ρ := ρ) (H := H) (W := W) ρ' F
          _ = Rep.ofHom (restrictIntertwiningMap ρ H W ρ' F') := by
                simp [hFF']
          _ = (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
                (inducedFromSubrepresentationHom ρ H W ≫
                  (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F') := by
                simpa using
                  (postcompose_inducedFromSubrepresentationHom_eq_restrictIntertwiningMap
                    (ρ := ρ) (H := H) (W := W) ρ' F').symm
      have hpost :
          inducedFromSubrepresentationHom ρ H W ≫
              (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F =
            inducedFromSubrepresentationHom ρ H W ≫
              (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F' :=
        (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')).injective hpostEq
      have hg :
          (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F =
            (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F' := h.1 hpost
      simpa using congrArg (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')) hg
    · intro f
      -- Use surjectivity of postcomposition, then read the resulting map back as an intertwiner.
      obtain ⟨g, hg⟩ := h.2 <|
        (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')).symm
          (Rep.ofHom f)
      refine ⟨(Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')) g, ?_⟩
      ext w
      have hcomp := congrArg
        (fun z : Rep.ind H.subtype (Rep.of W.toRepresentation) ⟶ Rep.of ρ' ↦
          (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) z)
        hg
      have hw := congrArg (fun z => z.hom w) hcomp
      simpa using hw
  · intro h
    constructor
    · intro g g' hgg'
      -- Compare the two morphisms after transporting them to restriction maps.
      have hrestrictEq := congrArg
        (fun z : Rep.ind H.subtype (Rep.of W.toRepresentation) ⟶ Rep.of ρ' ↦
          (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) z)
        hgg'
      have hrestrict :
          restrictIntertwiningMap ρ H W ρ'
              ((Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')) g) =
            restrictIntertwiningMap ρ H W ρ'
              ((Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')) g') := by
        ext w
        have hw := congrArg (fun z => z.hom w) hrestrictEq
        simpa
          [postcompose_inducedFromSubrepresentationHom_eq_restrictIntertwiningMap]
          using hw
      have hmaps := h.1 hrestrict
      exact (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).injective hmaps
    · intro f
      -- First view `f` as an `H`-equivariant map on `W`, then extend it using the bijective
      -- restriction map.
      let f' : W.toRepresentation.IntertwiningMap (ρ'.comp H.subtype) :=
        Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ'))
          ((Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) f)
      obtain ⟨F, hF⟩ := h.2 f'
      refine ⟨(Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F, ?_⟩
      apply (Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')).injective
      apply (Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ'))).injective
      have hpost :
          (Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ')))
              ((Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
                (inducedFromSubrepresentationHom ρ H W ≫
                  (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F)) =
            restrictIntertwiningMap ρ H W ρ' F := by
        ext w
        change
          ((inducedFromSubrepresentationHom ρ H W ≫
              (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F).hom
            (IndV.mk H.subtype W.toRepresentation 1 w) = F w)
        simp [inducedFromSubrepresentationHom]
        rfl
      calc
        (Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ')))
            ((Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ'))
              (inducedFromSubrepresentationHom ρ H W ≫
                (Rep.homLinearEquiv (Rep.of ρ) (Rep.of ρ')).symm F)) =
            restrictIntertwiningMap ρ H W ρ' F :=
          hpost
        _ = f' := hF
        _ = (Rep.homLinearEquiv (Rep.of W.toRepresentation) (Rep.res H.subtype (Rep.of ρ')))
              ((Rep.indResHomEquiv H.subtype (Rep.of W.toRepresentation) (Rep.of ρ')) f) := by
              rfl

/-- Helper for Proposition 7-7.1-1: the canonical comparison morphism is an isomorphism exactly
when every Chapter 3 restriction map is bijective. -/
theorem isIso_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap :
    IsIso (inducedFromSubrepresentationHom ρ H W) ↔
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ) := by
  -- `coyoneda` rewrites isomorphy into bijectivity of postcomposition on every target.
  rw [CategoryTheory.isIso_iff_coyoneda_map_bijective]
  constructor
  · intro hIso ρ'
    simpa using
      (bijective_postcompose_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) (ρ' := ρ'.ρ)).mp
        (hIso ρ')
  · intro hIso ρ'
    simpa using
      (bijective_postcompose_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) (ρ' := ρ'.ρ)).mpr
        (hIso ρ')

/-- Helper for Proposition 7-7.1-1: two representatives of the same left coset transport `W`
to the same translated submodule of `V`. -/
theorem translate_eq_of_leftRel {s t : G}
    (hst : QuotientGroup.leftRel H s t) :
    W.toSubmodule.map (ρ s) = W.toSubmodule.map (ρ t) := by
  -- Compare the two translates by rewriting `t` as `s * h` for a suitable `h ∈ H`.
  rw [le_antisymm_iff]
  constructor
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h⁻¹ w, W.apply_mem_toSubmodule h⁻¹ hw, ?_⟩
    change ρ t (ρ h⁻¹ w) = ρ s w
    calc
      ρ t (ρ h⁻¹ w) = ρ (s * h) (ρ h⁻¹ w) := by
        congr 1
        simp [h]
      _ = ρ s (ρ h (ρ h⁻¹ w)) := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ s w := by simp
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    rw [QuotientGroup.leftRel_apply] at hst
    let h : H := ⟨s⁻¹ * t, hst⟩
    refine Submodule.mem_map.mpr ?_
    refine ⟨ρ h w, W.apply_mem_toSubmodule h hw, ?_⟩
    change ρ s (ρ h w) = ρ t w
    calc
      ρ s (ρ h w) = ρ (s * h) w := by
        simp [Module.End.mul_apply, map_mul]
      _ = ρ t w := by
        congr 1
        simp [h]

/-- Helper for Proposition 7-7.1-1: acting by `s` transports the `q`-indexed translate of `W`
onto the `(s • q)`-indexed translate. -/
theorem leftQuotientSubmodule_map (s : G) (q : G ⧸ H) :
    (ρ.leftQuotientSubmodule H W q).map (ρ s) =
      ρ.leftQuotientSubmodule H W (s • q) := by
  -- First move from the chosen representative `q.out` to the explicit translate `s * q.out`.
  have hmap :
      (ρ.leftQuotientSubmodule H W q).map (ρ s) =
        W.toSubmodule.map (ρ (s * q.out)) := by
    rw [ρ.leftQuotientSubmodule_out H W q]
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Submodule.mem_map.mp hy with ⟨w, hw, rfl⟩
      exact Submodule.mem_map.mpr ⟨w, hw, by
        change ρ (s * q.out) w = ρ s (ρ q.out w)
        simp [Module.End.mul_apply, map_mul]
      ⟩
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
      refine Submodule.mem_map.mpr ⟨ρ q.out w, ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      · change ρ s (ρ q.out w) = ρ (s * q.out) w
        simp [Module.End.mul_apply, map_mul]
  -- Then replace `s * q.out` by the chosen representative of the target coset.
  have hq : QuotientGroup.leftRel H ((s • q).out) (s * q.out) := by
    apply Quotient.exact'
    calc
      ((s • q).out : G ⧸ H) = s • q := Quotient.out_eq' (s • q)
      _ = s • (q.out : G ⧸ H) := by
        exact congrArg (fun z : G ⧸ H ↦ s • z) (Quotient.out_eq' q).symm
      _ = (s * q.out : G ⧸ H) := rfl
  rw [ρ.leftQuotientSubmodule_out H W (s • q)]
  exact hmap.trans ((translate_eq_of_leftRel (ρ := ρ) (H := H) (W := W) hq).symm)

/-- Helper for Proposition 7-7.1-1: universal bijectivity of the restriction map forces the
coset translates of `W` to span all of `V`. -/
theorem leftQuotientSubmodule_iSup_eq_top_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    iSup (ρ.leftQuotientSubmodule H W) = ⊤ := by
  classical
  let U : Submodule k V := iSup (ρ.leftQuotientSubmodule H W)
  -- Route correction: the span half is handled first by quotienting out the span `U`, rather than
  -- trying to recover the whole internal direct-sum structure in one step.
  have hU_stable : ∀ g : G, U ≤ U.comap (ρ g) := by
    intro g x hx
    change ρ g x ∈ U
    refine Submodule.iSup_induction (p := ρ.leftQuotientSubmodule H W)
      (motive := fun z : V ↦ ρ g z ∈ U) hx ?_ ?_ ?_
    · intro q z hz
      -- Each individual translate is carried to the corresponding translated summand.
      have hz' : ρ g z ∈ ρ.leftQuotientSubmodule H W (g • q) := by
        rw [← leftQuotientSubmodule_map (ρ := ρ) (H := H) (W := W) g q]
        exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩
      exact Submodule.mem_iSup_of_mem (g • q) hz'
    · simp
    · intro x y hx hy
      simpa [map_add] using Submodule.add_mem U hx hy
  let ρquot : Representation k G (V ⧸ U) := ρ.quotient U hU_stable
  let Fq : ρ.IntertwiningMap ρquot :=
    (Submodule.mkQ U).intertwiningMap_of_isIntertwiningMap ρ ρquot (by
      intro g v
      rfl)
  have hwU (w : W.toSubmodule) : (w : V) ∈ U := by
    -- The original subrepresentation `W` is the translate indexed by the identity coset.
    refine Submodule.mem_iSup_of_mem ((1 : G) : G ⧸ H) ?_
    rw [ρ.leftQuotientSubmodule_mk H W (1 : G)]
    exact Submodule.mem_map.mpr ⟨w, w.property, by simp⟩
  have hrestrict_zero : restrictIntertwiningMap ρ H W ρquot Fq = 0 := by
    -- The quotient map vanishes on `W` because `W ≤ U`.
    ext w
    change (Submodule.mkQ U : V →ₗ[k] V ⧸ U) w = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hwU w
  have hFq_zero : Fq = 0 := (hbij (Rep.of ρquot)).1 hrestrict_zero
  have hmkQ_zero : (Submodule.mkQ U : V →ₗ[k] V ⧸ U) = 0 := by
    -- Injectivity forces the quotient intertwiner itself to be the zero map.
    ext x
    exact congrArg (fun f : ρ.IntertwiningMap ρquot ↦ f x) hFq_zero
  -- A quotient map that is identically zero can only come from the top submodule.
  apply top_unique
  intro x _
  have hx : (Submodule.mkQ U : V →ₗ[k] V ⧸ U) x = 0 := by
    simp [hmkQ_zero]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  exact hx

/-- Helper for Proposition 7-7.1-1: the subgroup-supported function attached to `w` in the
coinduced model of `W`. -/
noncomputable def supported_coinduced_function_fun (w : W.toSubmodule) : G → W.toSubmodule :=
  let _ : DecidablePred (fun g : G ↦ g ∈ H) := Classical.decPred _
  fun g ↦ if hg : g ∈ H then W.toRepresentation ⟨g, hg⟩ w else 0

/-- Helper for Proposition 7-7.1-1: the subgroup-supported function lies in the canonical
coinduced-function model. -/
theorem supported_coinduced_function_fun_mem_coindV (w : W.toSubmodule) :
    supported_coinduced_function_fun (ρ := ρ) (H := H) (W := W) w ∈
      (W.toRepresentation).coindV H.subtype := by
  -- The defining covariance relation is checked by splitting on whether the evaluation point lies
  -- in the subgroup.
  rw [Representation.mem_coindV]
  intro h g
  dsimp [supported_coinduced_function_fun]
  by_cases hgh : ((h : G) * g) ∈ H
  · have hg : g ∈ H := by
      simpa [mul_assoc] using H.mul_mem (H.inv_mem h.2) hgh
    simp [hgh, hg, Subrepresentation.toRepresentation, map_mul]
    rfl
  · have hg : g ∉ H := by
      intro hg
      exact hgh (H.mul_mem h.2 hg)
    simp [hgh, hg]

/-- Helper for Proposition 7-7.1-1: the subgroup-supported functions depend linearly on the input
vector in `W`. -/
noncomputable def supported_coinduced_linear :
    W.toSubmodule →ₗ[k] (W.toRepresentation).coindV H.subtype :=
  { toFun := fun w ↦
      ⟨supported_coinduced_function_fun (ρ := ρ) (H := H) (W := W) w,
        supported_coinduced_function_fun_mem_coindV (ρ := ρ) (H := H) (W := W) w⟩
    map_add' := by
      intro x y
      ext g
      dsimp [supported_coinduced_function_fun]
      by_cases hg : g ∈ H
      · simp [hg, map_add]
      · simp [hg]
    map_smul' := by
      intro a x
      ext g
      dsimp [supported_coinduced_function_fun]
      by_cases hg : g ∈ H
      · simp [hg]
      · simp [hg] }

/-- Helper for Proposition 7-7.1-1: the subgroup-supported map intertwines the `H`-action on `W`
with the restricted coinduced action. -/
theorem supported_coinduced_linear_isIntertwining :
    ∀ h : H, ∀ w : W.toSubmodule,
      supported_coinduced_linear (ρ := ρ) (H := H) (W := W) (W.toRepresentation h w) =
        (((W.toRepresentation).coind H.subtype).comp H.subtype) h
          (supported_coinduced_linear (ρ := ρ) (H := H) (W := W) w) := by
  intro h w
  -- Evaluate both coinduced functions pointwise and compare their subgroup-support formulas.
  ext g
  simp only [supported_coinduced_linear, MonoidHom.coe_comp, Subgroup.coe_subtype,
    Function.comp_apply, Representation.coind_apply, LinearMap.restrict_coe_apply,
    LinearMap.funLeft_apply, SetLike.coe_eq_coe]
  dsimp [supported_coinduced_function_fun]
  by_cases hg : g ∈ H
  · have hgh : g * h ∈ H := H.mul_mem hg h.2
    simp [hg, hgh, Subrepresentation.toRepresentation, map_mul]
    rfl
  · have hgh : g * h ∉ H := by
      intro hmem
      exact hg (by simpa [mul_assoc] using H.mul_mem hmem (H.inv_mem h.2))
    simp [hg, hgh]

/-- Helper for Proposition 7-7.1-1: the subgroup-supported construction is an `H`-equivariant map
from `W` into the restricted coinduced representation. -/
noncomputable def supported_coinduced_restrict_map :
    W.toRepresentation.IntertwiningMap (((W.toRepresentation).coind H.subtype).comp H.subtype) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap W.toRepresentation
    (((W.toRepresentation).coind H.subtype).comp H.subtype)
    (supported_coinduced_linear (ρ := ρ) (H := H) (W := W))
    (supported_coinduced_linear_isIntertwining (ρ := ρ) (H := H) (W := W))

/-- Helper for Proposition 7-7.1-1: the subgroup-supported coinduced function evaluates to `w` at
the identity element. -/
theorem supported_coinduced_restrict_map_apply_one (w : W.toSubmodule) :
    (((supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w :
        (W.toRepresentation).coindV H.subtype) : G → W.toSubmodule) 1) = w := by
  -- At the identity, the supported function reduces to the identity action of `H` on `W`.
  simp [supported_coinduced_restrict_map, supported_coinduced_linear,
    supported_coinduced_function_fun]
  exact congrArg (fun f : W.toSubmodule →ₗ[k] W.toSubmodule => f w) W.toRepresentation.map_one'

/-- Helper for Proposition 7-7.1-1: away from the subgroup, the subgroup-supported coinduced
function vanishes. -/
theorem supported_coinduced_restrict_map_apply_of_not_mem (w : W.toSubmodule) {g : G}
    (hg : g ∉ H) :
    (((supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w :
        (W.toRepresentation).coindV H.subtype) : G → W.toSubmodule) g) = 0 := by
  -- Outside `H`, the subgroup-supported function is definitionally zero.
  simp [supported_coinduced_restrict_map, supported_coinduced_linear,
    supported_coinduced_function_fun, hg]

/-- Helper for Proposition 7-7.1-1: after acting by `g` on the subgroup-supported coinduced
function, evaluation at `1` is evaluation of the original function at `g`. -/
theorem supported_coinduced_eval_one_after_action (w : W.toSubmodule) (g : G) :
    (((((W.toRepresentation).coind H.subtype) g)
        (supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w) :
          (W.toRepresentation).coindV H.subtype) : G → W.toSubmodule) 1 =
      (((supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w :
          (W.toRepresentation).coindV H.subtype) : G → W.toSubmodule) g) := by
  -- The coinduced action is right translation on the argument of the function.
  simp only [Representation.coind_apply, LinearMap.restrict_coe_apply, LinearMap.funLeft_apply,
    one_mul]

/-- Helper for Proposition 7-7.1-1: universal bijectivity supplies the coinduced extension whose
evaluation at `1` extracts the identity-coset component. -/
noncomputable def identity_coset_extension_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    ρ.IntertwiningMap ((W.toRepresentation).coind H.subtype) :=
  Classical.choose <|
    (hbij (Rep.of ((W.toRepresentation).coind H.subtype))).2
      (supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W))

/-- Helper for Proposition 7-7.1-1: the chosen coinduced extension restricts to the
subgroup-supported map on `W`. -/
theorem identity_coset_extension_of_bijective_restrictIntertwiningMap_spec
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    restrictIntertwiningMap ρ H W ((W.toRepresentation).coind H.subtype)
        (identity_coset_extension_of_bijective_restrictIntertwiningMap
          (ρ := ρ) (H := H) (W := W) hbij) =
      supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) :=
  Classical.choose_spec <|
    (hbij (Rep.of ((W.toRepresentation).coind H.subtype))).2
      (supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W))

/-- Helper for Proposition 7-7.1-1: evaluation at `1` after the chosen coinduced extension gives a
linear projection onto the identity-coset copy of `W`. -/
noncomputable def identity_coset_projection_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    V →ₗ[k] W.toSubmodule :=
  (LinearMap.proj (R := k) (i := (1 : G))) ∘ₗ
    ((W.toRepresentation).coindV H.subtype).subtype ∘ₗ
      (identity_coset_extension_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij).toLinearMap

/-- Helper for Proposition 7-7.1-1: the identity-coset projection is the identity on `W`. -/
theorem identity_coset_projection_of_bijective_restrictIntertwiningMap_apply_self
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ))
    (w : W.toSubmodule) :
    identity_coset_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij w = w := by
  -- Restricting the chosen extension to `W` recovers the subgroup-supported coinduced map.
  have hw :
      identity_coset_extension_of_bijective_restrictIntertwiningMap
          (ρ := ρ) (H := H) (W := W) hbij w =
        supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w := by
    simpa [Representation.restrictIntertwiningMap_apply] using
      congrArg (fun f => f w)
        (identity_coset_extension_of_bijective_restrictIntertwiningMap_spec
          (ρ := ρ) (H := H) (W := W) hbij)
  have hEval := congrArg
    (fun f : (W.toRepresentation).coindV H.subtype =>
      ((f : G → W.toSubmodule) 1))
    hw
  simpa [identity_coset_projection_of_bijective_restrictIntertwiningMap] using
    hEval.trans (supported_coinduced_restrict_map_apply_one
      (ρ := ρ) (H := H) (W := W) w)

/-- Helper for Proposition 7-7.1-1: the identity-coset projection annihilates translates whose
representative does not lie in `H`. -/
theorem identity_coset_projection_of_bijective_restrictIntertwiningMap_apply_translate
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ))
    (g : G) (w : W.toSubmodule) (hg : g ∉ H) :
    identity_coset_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij (ρ g w) = 0 := by
  -- Intertwining transports evaluation at `1` after action by `g` to evaluation at `g`.
  have hw :
      identity_coset_extension_of_bijective_restrictIntertwiningMap
          (ρ := ρ) (H := H) (W := W) hbij w =
        supported_coinduced_restrict_map (ρ := ρ) (H := H) (W := W) w := by
    simpa [Representation.restrictIntertwiningMap_apply] using
      congrArg (fun f => f w)
        (identity_coset_extension_of_bijective_restrictIntertwiningMap_spec
          (ρ := ρ) (H := H) (W := W) hbij)
  change
    ((((identity_coset_extension_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij) (ρ g w) :
          (W.toRepresentation).coindV H.subtype) : G → W.toSubmodule) 1) = 0
  rw [Representation.IntertwiningMap.isIntertwining
    (f := identity_coset_extension_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W) hbij) (g := g) (v := w)]
  rw [hw]
  rw [supported_coinduced_eval_one_after_action (ρ := ρ) (H := H) (W := W) w g]
  exact supported_coinduced_restrict_map_apply_of_not_mem (ρ := ρ) (H := H) (W := W) w hg

/-- Helper for Proposition 7-7.1-1: transport the identity-coset projection to the `q`-indexed
summand. -/
noncomputable def translate_projection_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ))
    (q : G ⧸ H) :
    V →ₗ[k] ρ.leftQuotientSubmodule H W q :=
  (ρ.leftQuotientSubmoduleEquiv H W q).toLinearMap ∘ₗ
    (identity_coset_projection_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W) hbij) ∘ₗ
    (ρ q.out⁻¹)

/-- Helper for Proposition 7-7.1-1: the transported projection is the identity on the `q`-indexed
translate of `W`. -/
theorem translate_projection_of_bijective_restrictIntertwiningMap_apply_self
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ))
    (q : G ⧸ H) (x : ρ.leftQuotientSubmodule H W q) :
    translate_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij q x = x := by
  -- Pull back to `W`, apply the identity-coset projection there, then transport forward again.
  let w : W.toSubmodule := (ρ.leftQuotientSubmoduleEquiv H W q).symm x
  have hw :
      ρ q.out⁻¹ x = w := by
    simpa [w] using leftQuotientSubmoduleEquiv_symm_apply (ρ := ρ) (H := H) (W := W) q x
  ext
  calc
    ((translate_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij q x : ρ.leftQuotientSubmodule H W q) : V) =
        ρ q.out
          (identity_coset_projection_of_bijective_restrictIntertwiningMap
            (ρ := ρ) (H := H) (W := W) hbij (ρ q.out⁻¹ x)) := by
          simp [translate_projection_of_bijective_restrictIntertwiningMap,
            leftQuotientSubmoduleEquiv_apply]
    _ = ρ q.out w := by
          rw [hw, identity_coset_projection_of_bijective_restrictIntertwiningMap_apply_self]
    _ = x := by
          simpa [w] using
            (leftQuotientSubmoduleEquiv_apply (ρ := ρ) (H := H) (W := W) q w).symm

/-- Helper for Proposition 7-7.1-1: the transported projection vanishes on every distinct coset
translate. -/
theorem translate_projection_of_bijective_restrictIntertwiningMap_apply_other
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ))
    {q r : G ⧸ H} (hqr : r ≠ q) (y : ρ.leftQuotientSubmodule H W r) :
    translate_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij q y = 0 := by
  -- After pulling back by `q.out⁻¹`, a distinct `r`-summand becomes a translate by an element
  -- outside `H`, so the identity-coset projection kills it.
  let w : W.toSubmodule := (ρ.leftQuotientSubmoduleEquiv H W r).symm y
  have hw :
      ρ q.out⁻¹ y = ρ (q.out⁻¹ * r.out) w := by
    calc
      ρ q.out⁻¹ y = ρ q.out⁻¹ (ρ r.out w) := by
        congr 1
        simpa [w] using
          (leftQuotientSubmoduleEquiv_apply (ρ := ρ) (H := H) (W := W) r w).symm
      _ = ρ (q.out⁻¹ * r.out) w := by
        simp [Module.End.mul_apply, map_mul]
  have hnot_mem : q.out⁻¹ * r.out ∉ H := by
    intro hmem
    have hEq : q = r := by
      calc
        q = (q.out : G ⧸ H) := (Quotient.out_eq' q).symm
        _ = (r.out : G ⧸ H) := by
          apply Quotient.sound'
          simpa [QuotientGroup.leftRel_apply] using hmem
        _ = r := Quotient.out_eq' r
    exact hqr hEq.symm
  ext
  calc
    ((translate_projection_of_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W) hbij q y : ρ.leftQuotientSubmodule H W q) : V) =
        ρ q.out
          (identity_coset_projection_of_bijective_restrictIntertwiningMap
            (ρ := ρ) (H := H) (W := W) hbij (ρ q.out⁻¹ y)) := by
          simp [translate_projection_of_bijective_restrictIntertwiningMap,
            leftQuotientSubmoduleEquiv_apply]
    _ = ρ q.out
          (identity_coset_projection_of_bijective_restrictIntertwiningMap
            (ρ := ρ) (H := H) (W := W) hbij (ρ (q.out⁻¹ * r.out) w)) := by
          rw [hw]
    _ = ρ q.out ((0 : W.toSubmodule) : V) := by
          rw [identity_coset_projection_of_bijective_restrictIntertwiningMap_apply_translate
            (ρ := ρ) (H := H) (W := W) hbij (q.out⁻¹ * r.out) w hnot_mem]
    _ = 0 := by simpa using LinearMap.map_zero (ρ q.out)

/-- Helper for Proposition 7-7.1-1: universal bijectivity of the restriction map forces the coset
translates of `W` to be pairwise disjoint, hence independent. -/
theorem leftQuotientSubmodule_iSupIndep_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    iSupIndep (ρ.leftQuotientSubmodule H W) := by
  -- The transported projections kill every summand except the chosen one, so they separate the
  -- `q`-indexed translate from the supremum of all others.
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro x hxq hxrest
  let πq :=
    translate_projection_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W) hbij q
  let xq : ρ.leftQuotientSubmodule H W q := ⟨x, hxq⟩
  have hself : πq x = xq := by
    simpa [πq, xq] using
      translate_projection_of_bijective_restrictIntertwiningMap_apply_self
        (ρ := ρ) (H := H) (W := W) hbij q xq
  have hzero : πq x = 0 := by
    refine Submodule.iSup_induction
        (p := fun r ↦ ⨆ (_ : r ≠ q), ρ.leftQuotientSubmodule H W r)
        (motive := fun z : V ↦ πq z = 0) hxrest ?_ ?_ ?_
    · intro r z hz
      refine Submodule.iSup_induction
          (p := fun _ : r ≠ q ↦ ρ.leftQuotientSubmodule H W r)
          (motive := fun t : V ↦ πq t = 0) hz ?_ ?_ ?_
      · intro hr t ht
        let tr : ρ.leftQuotientSubmodule H W r := ⟨t, ht⟩
        simpa [πq, tr] using
          translate_projection_of_bijective_restrictIntertwiningMap_apply_other
            (ρ := ρ) (H := H) (W := W) hbij (q := q) (r := r) hr tr
      · simp
      · intro y z hy hz
        simp [hy, hz]
    · simp
    · intro y z hy hz
      simp [hy, hz]
  have hxq_zero : xq = 0 := hself.symm.trans hzero
  simpa [xq] using congrArg (fun z : ρ.leftQuotientSubmodule H W q ↦ (z : V)) hxq_zero

/-- Helper for Proposition 7-7.1-1: if every Chapter 3 restriction map is bijective, then the
coset translates of `W` form the internal direct-sum decomposition required by
`IsInducedFromSubrepresentation`. -/
theorem isInducedFromSubrepresentation_of_bijective_restrictIntertwiningMap
    (hbij :
      ∀ (ρ' : Rep k G), Function.Bijective (restrictIntertwiningMap ρ H W ρ'.ρ)) :
    ρ.IsInducedFromSubrepresentation H W := by
  classical
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  -- Route correction: the quotient argument above already proves that the translates span `V`.
  have hspan :
      iSup (ρ.leftQuotientSubmodule H W) = ⊤ :=
    leftQuotientSubmodule_iSup_eq_top_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W) hbij
  -- The coinduced projection construction separates distinct coset translates, giving
  -- independence; together with the span statement above, this yields the required internal sum.
  have hindep :
      iSupIndep (ρ.leftQuotientSubmodule H W) :=
    leftQuotientSubmodule_iSupIndep_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W) hbij
  change DirectSum.IsInternal (ρ.leftQuotientSubmodule H W)
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Proposition 7-7.1-1: a representation `ρ` is induced by the `H`-stable subrepresentation `W`
if and only if the canonical adjunction morphism from `Ind_H^G(W)` to `ρ` is an isomorphism. -/
theorem isInducedFromSubrepresentation_iff_isIso_inducedFromSubrepresentationHom
    :
    ρ.IsInducedFromSubrepresentation H W ↔
      IsIso (inducedFromSubrepresentationHom ρ H W) := by
  constructor
  · intro hρ
    -- The inducedness hypothesis gives the Chapter 3 bijectivity statement for every target.
    refine
      (isIso_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W)).2 ?_
    intro ρ'
    exact bijective_restrictIntertwiningMap_of_isInducedFromSubrepresentation ρ H W hρ ρ'.ρ
  · intro hIso
    -- Convert the isomorphism into universal bijectivity, then invoke the structural converse.
    exact isInducedFromSubrepresentation_of_bijective_restrictIntertwiningMap
      (ρ := ρ) (H := H) (W := W)
      ((isIso_inducedFromSubrepresentationHom_iff_bijective_restrictIntertwiningMap
        (ρ := ρ) (H := H) (W := W)).1 hIso)

/-- Companion form of Proposition 7-7.1-1 on the underlying function of the canonical morphism. -/
-- Proof sketch: the main proposition identifies the canonical adjunction morphism as an
-- isomorphism; in the concrete category `Rep k G`, this is equivalent to bijectivity of the
-- underlying linear map.
theorem isInducedFromSubrepresentation_iff_bijective_inducedFromSubrepresentationHom
    :
    ρ.IsInducedFromSubrepresentation H W ↔
      Function.Bijective (inducedFromSubrepresentationHom ρ H W) := by
  simpa using
    (isInducedFromSubrepresentation_iff_isIso_inducedFromSubrepresentationHom ρ H W).trans
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (inducedFromSubrepresentationHom ρ H W))

end

end Representation

/-! ### Proposition_7_7_1_3 (from Chap07) -/
universe u v w x

namespace Representation

section Stabilizer

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]

/-- Bridge/view: the action underlying a representation. -/
private abbrev toDistribMulAction (ρ : Representation k G V) : DistribMulAction G V where
  smul g v := ρ g v
  one_smul v := by
    change ρ 1 v = v
    exact LinearMap.congr_fun ρ.map_one v
  mul_smul g h v := by
    change ρ (g * h) v = ρ g (ρ h v)
    exact LinearMap.congr_fun (ρ.map_mul g h) v
  smul_zero g := map_zero (ρ g)
  smul_add g x y := map_add (ρ g) x y

/-- Bridge/view: scalar commutation for the pointwise action on submodules induced by `ρ`. -/
private abbrev smulCommClass (ρ : Representation k G V) :
    let _ : DistribMulAction G V := ρ.toDistribMulAction
    SMulCommClass G k V := by
  letI := ρ.toDistribMulAction
  exact ⟨fun g a v ↦ (ρ g).map_smul a v⟩

/-- The stabilizer subgroup of a submodule for the action induced by `ρ`. -/
def submoduleStabilizer (ρ : Representation k G V) (W : Submodule k V) : Subgroup G := by
  letI := ρ.toDistribMulAction
  letI : SMulCommClass G k V := ρ.smulCommClass
  letI : DistribMulAction G (Submodule k V) := Submodule.pointwiseDistribMulAction
  exact MulAction.stabilizer G W

/-- Membership in `ρ.submoduleStabilizer W` is equivalent to preserving `W` under `ρ`. -/
theorem mem_submoduleStabilizer_iff_map_eq
    (ρ : Representation k G V) (W : Submodule k V) {g : G} :
    g ∈ ρ.submoduleStabilizer W ↔ W.map (ρ g) = W := by
  letI := ρ.toDistribMulAction
  letI : SMulCommClass G k V := ρ.smulCommClass
  letI : DistribMulAction G (Submodule k V) := Submodule.pointwiseDistribMulAction
  simpa [submoduleStabilizer] using
    (show g ∈ MulAction.stabilizer G W ↔ W.map (DistribSMul.toLinearMap k V g) = W from
      Submodule.mem_stabilizer_submodule_iff_map_eq)

/-- An element of the stabilizer sends every vector of `W` back into `W`. -/
-- Proof sketch: if `h` stabilizes `W` for the induced action on submodules, then `h • v` lies in
-- `h • W = W` for every `v ∈ W`.
private theorem submoduleStabilizer_apply_mem
    (ρ : Representation k G V) (W : Submodule k V) (h : ρ.submoduleStabilizer W)
    {v : V} (hv : v ∈ W) :
    ρ h v ∈ W := by
  have hh : W.map (ρ h) = W := by
    exact (mem_submoduleStabilizer_iff_map_eq ρ W).mp h.property
  simpa [hh] using (Submodule.mem_map.mpr ⟨v, hv, rfl⟩ : ρ h v ∈ W.map (ρ h))

/-- The restricted subrepresentation carried by a submodule inside its stabilizer subgroup. -/
def stabilizedSubrepresentation
    (ρ : Representation k G V) (W : Submodule k V) :
    Subrepresentation (ρ.comp (ρ.submoduleStabilizer W).subtype) where
  toSubmodule := W
  apply_mem_toSubmodule := submoduleStabilizer_apply_mem ρ W

end Stabilizer

section TransitiveSummands

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable {I : Type x}

variable [MulAction G I] [MulAction.IsPretransitive G I]

/-- A family of submodules is permuted by `ρ` if each group element carries `W i` onto `W (g • i)`.
-/
def PermutesSubmoduleFamily (ρ : Representation k G V) (W : I → Submodule k V) : Prop :=
  ∀ g : G, ∀ i : I, (W i).map (ρ g) = W (g • i)

end TransitiveSummands

section TransitiveSummands

variable {k : Type u} [Ring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {I : Type x}

variable [MulAction G I] [MulAction.IsPretransitive G I]

-- Source/core/bridge triage for Proposition 7-7.1-3:
-- * source-facing: LinearRepresentations_Serre_1977's stabilizer of a chosen summand and the associated stabilizer
--   subrepresentation from which `ρ` is induced, for a family of submodules permuted by `ρ`.
-- * core/canonical owners sampled in the representation-theoretic domain:
--   `Representation.IsInducedFromSubrepresentation`, `DirectSum.iSupIndep`, and
--   `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`.
-- * primitive data: the representation `ρ`, a family of submodules `W`, the canonical internal
--   direct-sum data `iSupIndep W` and `iSup W = ⊤`, the permutation property
--   `ρ.PermutesSubmoduleFamily W`, and the chosen index `i0`.
-- * bridge/view: `ρ.submoduleStabilizer (W i0)` packages the induced `MulAction.stabilizer`
--   subgroup without leaking its implementation instances into theorem statements; the local
--   internal direct-sum owner is recovered canonically from `hindep` and `hspan`.
-- * derived API: the stabilizer subgroup `ρ.submoduleStabilizer (W i0)` and the induced
--   stabilizer subrepresentation `ρ.stabilizedSubrepresentation (W i0)`.

noncomputable section

/-- Helper for Proposition 7-7.1-3: an element lies in the stabilizer of the chosen summand exactly
when it carries that summand onto itself in the permuted family. -/
private theorem submoduleStabilizer_iff_translated_summand_eq
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hperm : ρ.PermutesSubmoduleFamily W)
    {g : G} :
    g ∈ ρ.submoduleStabilizer (W i0) ↔ W (g • i0) = W i0 := by
  -- The stabilizer condition is exactly the equality supplied by the permutation hypothesis.
  rw [mem_submoduleStabilizer_iff_map_eq]
  constructor
  · intro hg
    calc
      W (g • i0) = (W i0).map (ρ g) := (hperm g i0).symm
      _ = W i0 := hg
  · intro hg
    calc
      (W i0).map (ρ g) = W (g • i0) := hperm g i0
      _ = W i0 := hg

/-- Helper for Proposition 7-7.1-3: if the chosen summand is zero, then transitivity forces every
summand in the permuted family to be zero. -/
private theorem all_summands_eq_bot_of_chosen_eq_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hbot : W i0 = ⊥) :
    ∀ i : I, W i = ⊥ := by
  intro i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i0 i
  -- Transitivity writes `i` as a translate of `i0`, so equivariance transports the zero summand.
  rw [← hg, ← hperm g i0]
  simp [hbot]

/-- Helper for Proposition 7-7.1-3: when the chosen summand is nonzero, stabilizing that summand
is equivalent to fixing its index. -/
private theorem mem_submoduleStabilizer_iff_fix_index_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    g ∈ ρ.submoduleStabilizer (W i0) ↔ g • i0 = i0 := by
  constructor
  · intro hg
    have hEq : W (g • i0) = W i0 :=
      (submoduleStabilizer_iff_translated_summand_eq ρ W i0 hperm).mp hg
    by_contra hne_fix
    have hdisj_top : Disjoint (W i0) (⨆ (j) (_ : j ≠ i0), W j) :=
      (iSupIndep_def.mp hindep) i0
    have hle : W (g • i0) ≤ ⨆ (j) (_ : j ≠ i0), W j := by
      exact le_iSup_of_le (g • i0) <| le_iSup_of_le hne_fix le_rfl
    -- Independence makes the chosen summand disjoint from any distinct translate.
    have hdisj : Disjoint (W i0) (W (g • i0)) :=
      hdisj_top.mono_right hle
    have hself : Disjoint (W i0) (W i0) := by
      simpa [hEq] using hdisj
    exact hne (disjoint_self.mp hself)
  · intro hfix
    -- If `g` fixes the chosen index, the equivariant family equality is exactly the stabilizer
    -- condition.
    exact (submoduleStabilizer_iff_translated_summand_eq ρ W i0 hperm).mpr <| by
      simp [hfix]

/-- Helper for Proposition 7-7.1-3: the quotient-to-index map is well defined once the
submodule stabilizer agrees with the index stabilizer on the nonzero branch. -/
private theorem submoduleStabilizerQuotientToIndex_wellDefined_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    {g₁ g₂ : G}
    (hrel : QuotientGroup.leftRel (ρ.submoduleStabilizer (W i0)) g₁ g₂) :
    g₁ • i0 = g₂ • i0 := by
  have hmem : g₁⁻¹ * g₂ ∈ ρ.submoduleStabilizer (W i0) :=
    QuotientGroup.leftRel_apply.mp hrel
  have hfix : (g₁⁻¹ * g₂) • i0 = i0 :=
    (mem_submoduleStabilizer_iff_fix_index_of_ne_bot ρ W i0 hindep hperm hne (g₁⁻¹ * g₂)).mp hmem
  -- Two representatives of the same left coset differ by an element fixing `i0`.
  calc
    g₁ • i0 = g₁ • ((g₁⁻¹ * g₂) • i0) := by rw [hfix]
    _ = g₂ • i0 := by simp [mul_smul]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, a left coset of the stabilizer is sent
to the corresponding translated index. -/
private def submoduleStabilizerQuotientToIndex_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    G ⧸ ρ.submoduleStabilizer (W i0) → I :=
  Quotient.lift
    (fun g : G ↦ g • i0)
    (fun _ _ hab ↦
      submoduleStabilizerQuotientToIndex_wellDefined_of_ne_bot ρ W i0 hindep hperm hne hab)

@[simp] private theorem submoduleStabilizerQuotientToIndex_of_ne_bot_mk
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne
        (g : G ⧸ ρ.submoduleStabilizer (W i0)) =
      g • i0 :=
  by
    simp [submoduleStabilizerQuotientToIndex_of_ne_bot]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, the quotient-to-index map is injective
because equal translates differ by an element fixing the chosen index. -/
private theorem submoduleStabilizerQuotientToIndex_injective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Injective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) := by
  intro q₁ q₂ hq
  revert hq
  refine Quotient.inductionOn₂' q₁ q₂ ?_
  intro g₁ g₂ hq_mk
  apply QuotientGroup.eq.mpr
  have hq_smul : g₁ • i0 = g₂ • i0 := by
    simpa using hq_mk
  have hfix : (g₁⁻¹ * g₂) • i0 = i0 := by
    -- Equal images in the quotient map mean the relative element fixes `i0`.
    calc
      (g₁⁻¹ * g₂) • i0 = g₁⁻¹ • (g₂ • i0) := by rw [mul_smul]
      _ = g₁⁻¹ • (g₁ • i0) := by rw [← hq_smul]
      _ = i0 := by simp
  exact
    (mem_submoduleStabilizer_iff_fix_index_of_ne_bot ρ W i0 hindep hperm hne (g₁⁻¹ * g₂)).mpr
      hfix

/-- Helper for Proposition 7-7.1-3: pretransitivity makes the quotient-to-index map surjective. -/
private theorem submoduleStabilizerQuotientToIndex_surjective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Surjective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) := by
  intro i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i0 i
  -- Every index is a translate of `i0`, so it has a quotient representative.
  refine ⟨(g : G ⧸ ρ.submoduleStabilizer (W i0)), ?_⟩
  simpa using hg

/-- Helper for Proposition 7-7.1-3: the quotient by the stabilizer of a nonzero chosen summand is
equivalent to the index set. -/
private theorem submoduleStabilizerQuotientToIndex_bijective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Bijective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) :=
  ⟨submoduleStabilizerQuotientToIndex_injective_of_ne_bot ρ W i0 hindep hperm hne,
    submoduleStabilizerQuotientToIndex_surjective_of_ne_bot ρ W i0 hindep hperm hne⟩

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, quotient cosets of the stabilizer
reindex the family of summands. -/
private noncomputable def submoduleStabilizerQuotientEquivIndex_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    G ⧸ ρ.submoduleStabilizer (W i0) ≃ I :=
  Equiv.ofBijective
    (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne)
    (submoduleStabilizerQuotientToIndex_bijective_of_ne_bot ρ W i0 hindep hperm hne)

@[simp] private theorem submoduleStabilizerQuotientEquivIndex_of_ne_bot_mk
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hne
        (g : G ⧸ ρ.submoduleStabilizer (W i0)) =
      g • i0 :=
  by
    simp [submoduleStabilizerQuotientEquivIndex_of_ne_bot]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, each left-coset translate of the
stabilized summand agrees with the corresponding original summand. -/
private theorem leftQuotientSubmodule_eq_reindexed_family_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (q : G ⧸ ρ.submoduleStabilizer (W i0)) :
    ρ.leftQuotientSubmodule
        (ρ.submoduleStabilizer (W i0))
        (ρ.stabilizedSubrepresentation (W i0))
        q =
      W (submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hne q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- The translate indexed by `gH` is just the image of `W i0` under `ρ g`, hence `W (g • i0)`.
  rw [ρ.leftQuotientSubmodule_mk]
  simpa using hperm g i0

/-- Proposition 7-7.1-3: if the submodules `W i` are independent, span `V`, and are permuted
transitively by `G`, then the chosen summand `W i0` is stable under its stabilizer subgroup, and
`ρ` is induced from the corresponding stabilizer subrepresentation. Equivalently, `V` is an
internal direct sum of the `W i`, and the family of left-coset translates of `W i0` gives that
decomposition. -/
-- Proof sketch: identify the left cosets of the stabilizer of `W i0` with the index set `I` via
-- transitivity, compare the transported copies of `W i0` with the equivariant family `W`, and
-- then transfer the internal direct-sum decomposition along that identification.
theorem
    isInducedFromSubrepresentation_submoduleStabilizer_of_indep_span_of_permuted_family
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hspan : iSup W = ⊤)
    (hperm : ρ.PermutesSubmoduleFamily W) :
    ρ.IsInducedFromSubrepresentation
      (ρ.submoduleStabilizer (W i0))
      (ρ.stabilizedSubrepresentation (W i0)) := by
  classical
  let _ : DecidableEq (G ⧸ ρ.submoduleStabilizer (W i0)) := Classical.decEq _
  have hInternal :
      DirectSum.IsInternal
        (ρ.leftQuotientSubmodule
          (ρ.submoduleStabilizer (W i0))
          (ρ.stabilizedSubrepresentation (W i0))) := by
    by_cases hbot : W i0 = ⊥
    · -- In the degenerate branch, transitivity forces every original summand and every quotient
      -- translate to be zero.
      have hall : ∀ i : I, W i = ⊥ :=
        all_summands_eq_bot_of_chosen_eq_bot ρ W i0 hperm hbot
      have hleftbot :
          ∀ q : G ⧸ ρ.submoduleStabilizer (W i0),
            ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))
                q =
              ⊥ := by
        intro q
        refine Quotient.inductionOn' q ?_
        intro g
        rw [ρ.leftQuotientSubmodule_mk]
        change Submodule.map (ρ g) (W i0) = ⊥
        rw [hbot]
        exact Submodule.map_bot (ρ g)
      have hleftbot_fun :
          (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) =
            fun _ : G ⧸ ρ.submoduleStabilizer (W i0) ↦ (⊥ : Submodule k V) := by
        funext q
        exact hleftbot q
      have hindep_left :
          iSupIndep
            (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) := by
        -- A family of zero submodules is independent.
        rw [iSupIndep_def]
        intro q
        rw [hleftbot q]
        exact disjoint_bot_left
      have hspan_bot : iSup W = ⊥ := by
        simp [hall]
      have htopbot : (⊥ : Submodule k V) = ⊤ := by
        -- The original spanning hypothesis collapses `V` in the zero-summand branch.
        calc
          (⊥ : Submodule k V) = iSup W := hspan_bot.symm
          _ = ⊤ := hspan
      have hspan_left :
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
            ⊤ := by
        calc
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
              ⊥ := by
              rw [hleftbot_fun]
              simp
          _ = ⊤ := htopbot
      exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep_left hspan_left
    · -- On the nonzero branch, orbit-stabilizer identifies the quotient translates with the
      -- original family `W`.
      let e :=
        submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hbot
      have hleft :
          ∀ q : G ⧸ ρ.submoduleStabilizer (W i0),
            ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))
                q =
              W (e q) := by
        intro q
        simpa [e] using
          leftQuotientSubmodule_eq_reindexed_family_of_ne_bot ρ W i0 hindep hperm hbot q
      have hleft_fun :
          (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) =
            W ∘ e := by
        funext q
        exact hleft q
      have hindep_left :
          iSupIndep
            (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) := by
        -- Reindex the original independent family along the quotient-index equivalence.
        rw [hleft_fun]
        exact hindep.comp e.injective
      have hspan_left :
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
            ⊤ := by
        calc
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
              iSup (W ∘ e) := by
              rw [hleft_fun]
          _ = iSup W := by
              simpa [Function.comp] using (Equiv.iSup_comp (g := W) e)
          _ = ⊤ := hspan
      exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep_left hspan_left
  unfold Representation.IsInducedFromSubrepresentation
  simpa using hInternal

end

end TransitiveSummands

end Representation

/-! ### Remark_7_7_1_2 (from Chap07) -/
open CategoryTheory Rep

noncomputable section

universe u v

section ExistenceAndAdjunction

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

variable (H : Subgroup G) (W : Rep k H)

-- Source/core/bridge triage for Remark 7-7.1-2:
-- * source-facing: existence of the induced representation, Frobenius reciprocity, and
--   transitivity of induction.
-- * core/canonical owners sampled in the induction domain:
--   `Rep.ind`, `Rep.indResHomEquiv`, `Rep.indResAdjunction`, and
--   `CategoryTheory.Adjunction.leftAdjointCompIso`.
-- * primitive data: a subgroup inclusion or group homomorphisms together with the source
--   representation.
-- * derived API: the transitivity isomorphism, obtained by specializing adjunction composition to
--   `indResAdjunction`.
/- Remark 7-7.1-2 (1): the induced representation of `W` along the subgroup inclusion `H ≤ G`
is the canonical mathlib object `ind H.subtype W`, so existence is built into the owner
declaration and uniqueness is up to the usual isomorphism notion in `Rep k G`. -/
#check (Rep.ind H.subtype W : Rep k G)

variable (E : Rep k G)

/- Frobenius reciprocity identifies the `H`-equivariant maps
`W ⟶ res H.subtype E` with the `G`-equivariant maps `ind H.subtype W ⟶ E`; this is the
canonical linear equivalence `indResHomEquiv H.subtype W E`. -/
#check
  (Rep.indResHomEquiv H.subtype W E :
    (Rep.ind H.subtype W ⟶ E) ≃ₗ[k] (W ⟶ Rep.res H.subtype E))

end ExistenceAndAdjunction

section Transitivity

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type v} [Group H]
variable {K : Type v} [Group K]
variable (φ : G →* H) (ψ : H →* K)

/- Remark 7-7.1-2 (2): induction is transitive. For homomorphisms `φ : G →* H` and
`ψ : H →* K`, the canonical transitivity isomorphism
`indFunctor k φ ⋙ indFunctor k ψ ≅ indFunctor k (ψ.comp φ)` is exactly the
specialization of the adjunction composition isomorphism to `Rep.indResAdjunction`. -/
#check
  ((indResAdjunction k φ).leftAdjointCompIso
    (indResAdjunction k ψ)
    (indResAdjunction k (ψ.comp φ))
    (eqToIso rfl) :
      indFunctor k φ ⋙ indFunctor k ψ ≅ indFunctor k (ψ.comp φ))

end Transitivity

/-! ### Remark_7_7_1_4 (from Chap07) -/
universe u v w x

namespace Representation

namespace IsIrreducible

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {I : Type x} [MulAction G I]

section PermutedInternalSummands

/-- Remark 7-7.1-4: for an irreducible representation written as an internal direct sum of
nonzero submodules `W i`, the pretransitivity conclusion only needs the independence and
permutation data; the spanning hypothesis is redundant. -/
-- Proof sketch: for any orbit `O ⊆ I`, the supremum of the summands `W i` with `i ∈ O` is stable
-- under `ρ` because the family is permuted by `G`. Irreducibility forces this orbit submodule to
-- be either `⊥` or `⊤`. The nonzero hypothesis rules out `⊥` for every nonempty orbit, so there
-- can be only one orbit.
theorem isPretransitive_of_permuted_internalSummands
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (W : I → Submodule k V)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : ∀ i, W i ≠ ⊥) :
    MulAction.IsPretransitive G I := by
  classical
  by_cases hI : Nonempty I
  · let orbitSubmodule : I → Submodule k V := fun i ↦ ⨆ j ∈ MulAction.orbit G i, W j
    have hstable : ∀ i g, (orbitSubmodule i).map (ρ g) ≤ orbitSubmodule i := by
      intro i g
      dsimp [orbitSubmodule]
      rw [Submodule.map_iSup, iSup_le_iff]
      intro j
      rw [Submodule.map_iSup, iSup_le_iff]
      intro hj
      have hgj : (W j).map (ρ g) = W (g • j) := hperm g j
      rw [hgj]
      exact le_iSup_of_le (g • j) <|
        le_iSup_of_le (MulAction.mem_orbit_of_mem_orbit g hj) le_rfl
    let U : I → Subrepresentation ρ := fun i ↦
      { toSubmodule := orbitSubmodule i
        apply_mem_toSubmodule := by
          intro g v hv
          exact hstable i g <| Submodule.mem_map.mpr ⟨v, hv, rfl⟩ }
    have hU_top : ∀ i, U i = ⊤ := by
      intro i
      have hWi_le : W i ≤ (U i).toSubmodule := by
        exact le_iSup_of_le i <| le_iSup_of_le (MulAction.mem_orbit_self i) le_rfl
      have hU_ne_bot : U i ≠ ⊥ := by
        intro hU_bot
        have hbot : (U i).toSubmodule = ⊥ := by
          simpa using congrArg Subrepresentation.toSubmodule hU_bot
        exact hne i <| le_bot_iff.mp <| hbot ▸ hWi_le
      exact (IsSimpleOrder.eq_bot_or_eq_top (U i)).resolve_left hU_ne_bot
    have horbit_eq_univ : ∀ i, MulAction.orbit G i = (Set.univ : Set I) := by
      intro i
      apply Set.eq_univ_of_forall
      intro j
      have horbitSubmodule_top : orbitSubmodule i = ⊤ := by
        simpa [U, orbitSubmodule] using congrArg Subrepresentation.toSubmodule (hU_top i)
      exact hindep.mem_of_biSup_eq_top (by simpa [orbitSubmodule] using horbitSubmodule_top) (hne j)
    rcases hI with ⟨i0⟩
    exact (MulAction.isPretransitive_iff_orbit_eq_univ i0).2 (horbit_eq_univ i0)
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    infer_instance

/-- Under the hypotheses of Remark 7-7.1-4, Proposition 7-7.1-3 applies to any chosen summand:
`ρ` is induced from the stabilizer of `W i0` acting on that summand. -/
theorem isInducedFromStabilizer_of_permuted_internalSummands
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (W : I → Submodule k V) (i0 : I)
    (hindep : iSupIndep W) (hspan : iSup W = ⊤)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : ∀ i, W i ≠ ⊥) :
    ρ.IsInducedFromSubrepresentation
      (ρ.submoduleStabilizer (W i0))
      (ρ.stabilizedSubrepresentation (W i0)) := by
  letI : MulAction.IsPretransitive G I :=
    isPretransitive_of_permuted_internalSummands ρ W hindep hperm hne
  simpa using
    isInducedFromSubrepresentation_submoduleStabilizer_of_indep_span_of_permuted_family
      ρ W i0 hindep hspan hperm

end PermutedInternalSummands

end IsIrreducible

end Representation
