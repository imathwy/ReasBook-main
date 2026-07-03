import Mathlib
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Induced

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_7_7_3_2 (from Chap07) -/
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable (K H : Subgroup G) (W : Rep k H)

-- Source/core/bridge triage for Remark 7-7.3-2:
-- * source-facing: the Mackey summand attached to a representative depends only on its image in
--   `K \ G / H`.
-- * core/canonical owners sampled in this domain: `Representation.mackeySummand`,
--   `DoubleCoset.eq`, `Rep.mkIso`, and `Rep.indFunctor`.
-- * primitive data: the summand owner `mackeySummand K H W s`.
-- * derived API: right translation by `H` and left translation by `K` both preserve the Mackey
--   summand up to canonical isomorphism.
-- * bridge/view: extract `t = a * s * b` from `DoubleCoset.eq`, then combine the two transport
--   lemmas below.

/-- Helper for Remark 7-7.3-2: right multiplication by an element of `H` leaves the Mackey
subgroup `K ∩ sHs⁻¹` unchanged. -/
theorem mackeySubgroup_mul_right_eq
    {s b : G} (hb : b ∈ H) :
    mackeySubgroup K H (s * b) = mackeySubgroup K H s := by
  -- Rewrite the membership condition by canceling the right `H`-translate.
  ext x
  constructor
  · intro hx
    have hx' : b⁻¹ * (s⁻¹ * (((x : K) : G) * s) * b) ∈ H := by
      simpa [mackeySubgroup, mul_assoc] using hx
    have hxmul : b * (b⁻¹ * (s⁻¹ * (((x : K) : G) * s) * b)) ∈ H := by
      exact H.mul_mem hb hx'
    have hx'' : s⁻¹ * (((x : K) : G) * s) * b ∈ H := by
      simpa [mul_assoc] using hxmul
    have hxmul' : (s⁻¹ * (((x : K) : G) * s) * b) * b⁻¹ ∈ H := by
      exact H.mul_mem hx'' (H.inv_mem hb)
    have hxH : s⁻¹ * (((x : K) : G) * s) ∈ H := by
      simpa [mul_assoc] using hxmul'
    simpa [mackeySubgroup, mul_assoc] using hxH
  · intro hx
    have hxH : s⁻¹ * (((x : K) : G) * s) ∈ H := by
      simpa [mackeySubgroup, mul_assoc] using hx
    have hx' : (s⁻¹ * (((x : K) : G) * s)) * b ∈ H := by
      exact H.mul_mem hxH hb
    have hx'' : b⁻¹ * ((s⁻¹ * (((x : K) : G) * s)) * b) ∈ H := by
      exact H.mul_mem (H.inv_mem hb) hx'
    simpa [mackeySubgroup, mul_assoc] using hx''

/-- Helper for Remark 7-7.3-2: an equivalence of source representations induces an equivalence of
the induced ambient representations. -/
noncomputable def induced_representation_equiv
    {S : Type*} [Group S]
    {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    (f : S →* K)
    {ρ : Representation k S V} {σ : Representation k S V'}
    (e : ρ.Equiv σ) :
    (Rep.ind f (Rep.of ρ)).ρ.Equiv (Rep.ind f (Rep.of σ)).ρ := by
  let inducedHom :
      (Rep.ind f (Rep.of ρ)).ρ.IntertwiningMap (Rep.ind f (Rep.of σ)).ρ :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        -- The induced action commutes with the transported source map on standard generators.
        intro g
        ext h a
        simp }
  let inducedInv :
      (Rep.ind f (Rep.of σ)).ρ.IntertwiningMap (Rep.ind f (Rep.of ρ)).ρ :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg (fun z ↦ (Finsupp.single (f g * x) (1 : k)) ⊗ₜ[k] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        -- The same generator computation gives the inverse intertwining map.
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedInv.toLinearMap ∘ₗ inducedHom.toLinearMap = LinearMap.id := by
    -- The induced maps are inverse because they agree with `e` and `e.symm` on each generator.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedHom, inducedInv]
  have hinduced_hom_inv :
      inducedHom.toLinearMap ∘ₗ inducedInv.toLinearMap = LinearMap.id := by
    -- The same generator test proves the inverse identity in the opposite order.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedHom, inducedInv]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedHom.toLinearMap inducedInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedHom.isIntertwining'

/-- Helper for Remark 7-7.3-2: induction along a source-group equivalence is the same induced
representation after reindexing the subgroup inclusion. -/
private noncomputable def ind_equiv_of_comp_equiv_local
    {S T : Type*} [Group S] [Group T]
    {V : Type*} [AddCommGroup V] [Module k V]
    (e : S ≃* T) (f : T →* K) (ρ : Representation k T V) :
    (Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).Equiv
      (Representation.ind f ρ) := by
  let ρcomp : Representation k S (TensorProduct k (K →₀ k) V) :=
    Representation.tprod ((Representation.leftRegular k K).comp (f.comp e.toMonoidHom))
      (ρ.comp e.toMonoidHom)
  let ρbase : Representation k T (TensorProduct k (K →₀ k) V) :=
    Representation.tprod ((Representation.leftRegular k K).comp f) ρ
  have hker :
      Representation.Coinvariants.ker ρcomp = Representation.Coinvariants.ker ρbase := by
    -- Reindexing the source group only renames the same family of coinvariant relations.
    unfold Representation.Coinvariants.ker
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with ⟨⟨g, v⟩, rfl⟩
      exact Submodule.subset_span ⟨(e g, v), by simp [ρcomp, ρbase]⟩
    · refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with ⟨⟨g, v⟩, rfl⟩
      exact Submodule.subset_span ⟨(e.symm g, v), by simp [ρcomp, ρbase]⟩
  refine Representation.Equiv.mk
      (Submodule.quotEquivOfEq _ _ hker) ?_
  intro k
  -- The quotient equivalence acts identically on the standard generators `IndV.mk`.
  apply Representation.IndV.hom_ext
  intro k'
  ext v
  change (Submodule.quotEquivOfEq _ _ hker)
      (((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) k)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) k') v)) =
    ((Representation.ind f ρ) k)
      ((Submodule.quotEquivOfEq _ _ hker)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) k') v))
  have hleft :
      ((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) k)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) k') v) =
      (Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (k' * k⁻¹)) v := by
    exact Representation.ind_mk (φ := f.comp e.toMonoidHom) (ρ := ρ.comp e.toMonoidHom) k k' v
  have hright :
      ((Representation.ind f ρ) k)
        ((Representation.IndV.mk f ρ k') v) =
      (Representation.IndV.mk f ρ (k' * k⁻¹)) v := by
    exact Representation.ind_mk (φ := f) (ρ := ρ) k k' v
  have hsource :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker ρcomp)
          (Representation.Coinvariants.ker ρbase)
          hker)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) k') v) =
      (Representation.IndV.mk f ρ k') v := by
    exact Submodule.quotEquivOfEq_mk _ _ hker _
  have hsource' :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker ρcomp)
          (Representation.Coinvariants.ker ρbase)
          hker)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (k' * k⁻¹)) v) =
      (Representation.IndV.mk f ρ (k' * k⁻¹)) v := by
    exact Submodule.quotEquivOfEq_mk _ _ hker _
  rw [hleft, hsource', hsource, hright]

/-- Helper for Remark 7-7.3-2: the unchanged subgroup under right multiplication can be viewed as
an explicit multiplicative equivalence rather than by transport. -/
private noncomputable def mackeySubgroup_mul_right_mulEquiv
    {s b : G} (hb : b ∈ H) :
    mackeySubgroup K H s ≃* mackeySubgroup K H (s * b) where
  toFun x := by
    rcases x with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [mackeySubgroup_mul_right_eq (K := K) (H := H) (s := s) (b := b) hb] using hx
  invFun x := by
    rcases x with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [mackeySubgroup_mul_right_eq (K := K) (H := H) (s := s) (b := b) hb] using hx
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    rfl
  map_mul' x y := rfl

/-- Helper for Remark 7-7.3-2: the right-translation subgroup equivalence acts by the identity on
the underlying subgroup element of `K`. -/
@[simp] private theorem mackeySubgroup_mul_right_mulEquiv_apply
    {s b : G} (hb : b ∈ H) {x : mackeySubgroup K H s} :
    ((mackeySubgroup_mul_right_mulEquiv (K := K) (H := H) hb) x : K) = x :=
  rfl

/-- Helper for Remark 7-7.3-2: right multiplication by `b ∈ H` changes the source twist only by
the automorphism `W.ρ b⁻¹` of `W`. -/
private noncomputable def mackeyTwist_mul_right_source_equiv
    {s b : G} (hb : b ∈ H) :
    (mackeyTwist K H W s).ρ.Equiv
      ((mackeyTwist K H W (s * b)).ρ.comp
        (mackeySubgroup_mul_right_mulEquiv (K := K) (H := H) hb).toMonoidHom) := by
  let eW : W.V ≃ₗ[k] W.V :=
    LinearEquiv.ofLinear (W.ρ ⟨b, hb⟩⁻¹) (W.ρ ⟨b, hb⟩)
      (by
        ext w
        simp)
      (by
        ext w
        simp)
  refine Representation.Equiv.mk eW ?_
  intro x
  ext w
  rcases x with ⟨x, hx⟩
  let gx : H := ⟨s⁻¹ * (↑x * s), by simpa [mackeySubgroup, mul_assoc] using hx⟩
  have hconj_mem : b⁻¹ * (s⁻¹ * (↑x * (s * b))) ∈ H := by
    -- The right translate contributes a conjugation by `b` inside `H`.
    simpa [gx, mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem hb) gx.property) hb
  let gx' : H := ⟨b⁻¹ * (s⁻¹ * (↑x * (s * b))), hconj_mem⟩
  have hconj : gx' = (⟨b, hb⟩ : H)⁻¹ * gx * ⟨b, hb⟩ := by
    -- Both subgroup elements are the same element of `H`, written in two conjugate forms.
    ext
    simp [gx', gx, mul_assoc]
  calc
    eW ((mackeyTwist K H W s).ρ ⟨x, hx⟩ w) = eW (W.ρ gx w) := by
      simp [mackeyTwist, gx, mackeySubgroup, mul_assoc]
    _ = W.ρ ((⟨b, hb⟩ : H)⁻¹ * gx) w := by
      simp [eW, gx, map_mul]
    _ = W.ρ (gx' * (⟨b, hb⟩ : H)⁻¹) w := by
      rw [hconj]
      simp [mul_assoc]
    _ = W.ρ gx' (eW w) := by
      simp [eW, gx', map_mul]
    _ = (((mackeyTwist K H W (s * b)).ρ.comp
          (mackeySubgroup_mul_right_mulEquiv (K := K) (H := H) hb).toMonoidHom) ⟨x, hx⟩)
          (eW w) := by
      simp [mackeyTwist, gx', mackeySubgroup_mul_right_mulEquiv_apply, mackeySubgroup,
        mul_assoc]

/-- Helper for Remark 7-7.3-2: left translation on the ambient `K`-coordinate identifies the
induced models for `f` and for a conjugate homomorphism `f'`. -/
private noncomputable def ind_equiv_of_left_translation_local
    {S : Type*} [Group S]
    {V : Type*} [AddCommGroup V] [Module k V]
    (a : K) (f f' : S →* K) (ρ : Representation k S V)
    (hconj : ∀ x, f' x = a * f x * a⁻¹) :
    (Representation.ind f ρ).Equiv (Representation.ind f' ρ) := by
  let shift : (K →₀ k) ≃ₗ[k] K →₀ k := Finsupp.domLCongr (Equiv.mulLeft a)
  let inducedHom :
      (Representation.ind f ρ).IntertwiningMap (Representation.ind f' ρ) :=
    { toLinearMap := Representation.Coinvariants.map _ _ (shift.toLinearMap.rTensor V) (by
        -- Left translation on `K` turns the `f`-relations into the `f'`-relations.
        intro x
        ext g v
        simp [Representation.tprod_apply, shift, hconj, mul_assoc])
      isIntertwining' := by
        -- The ambient `K`-action commutes with the same left translation on generators.
        intro k
        apply Representation.IndV.hom_ext
        intro k'
        ext v
        simp [shift, mul_assoc] }
  have hconj_symm : ∀ x, f x = a⁻¹ * f' x * a := by
    intro x
    rw [hconj x]
    simp [mul_assoc]
  let inducedInv :
      (Representation.ind f' ρ).IntertwiningMap (Representation.ind f ρ) :=
    { toLinearMap := Representation.Coinvariants.map _ _ (shift.symm.toLinearMap.rTensor V) (by
        -- Translating back by `a⁻¹` recovers the original family of source relations.
        intro x
        ext g v
        simp [Representation.tprod_apply, shift, hconj_symm, mul_assoc])
      isIntertwining' := by
        -- The same generator computation gives the inverse intertwining map.
        intro k
        apply Representation.IndV.hom_ext
        intro k'
        ext v
        simp [shift, mul_assoc] }
  have hinduced_inv_hom :
      inducedInv.toLinearMap ∘ₗ inducedHom.toLinearMap = LinearMap.id := by
    -- Both composites are the identity because the ambient translation and its inverse cancel on
    -- every standard generator `IndV.mk`.
    apply Representation.IndV.hom_ext
    intro k
    ext v
    simp [inducedHom, inducedInv, shift]
  have hinduced_hom_inv :
      inducedHom.toLinearMap ∘ₗ inducedInv.toLinearMap = LinearMap.id := by
    -- The same generator check proves the inverse identity in the opposite order.
    apply Representation.IndV.hom_ext
    intro k
    ext v
    simp [inducedHom, inducedInv, shift]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedHom.toLinearMap inducedInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedHom.isIntertwining'

/-- Helper for Remark 7-7.3-2: left multiplication by an element of `K` conjugates the Mackey
subgroup inside `K`. -/
private noncomputable def mackeySubgroup_mul_left_mulEquiv
    {s a : G} (ha : a ∈ K) :
    mackeySubgroup K H s ≃* mackeySubgroup K H (a * s) where
  toFun x := by
    rcases x with ⟨x, hx⟩
    refine ⟨(⟨a, ha⟩ : K) * x * (⟨a, ha⟩ : K)⁻¹, ?_⟩
    -- Conjugating `x` by `a` preserves the Mackey condition because `(a * s)⁻¹ (a x a⁻¹) (a * s)
    -- = s⁻¹ x s`.
    simpa [mackeySubgroup, mul_assoc] using hx
  invFun x := by
    rcases x with ⟨x, hx⟩
    refine ⟨(⟨a, ha⟩ : K)⁻¹ * x * (⟨a, ha⟩ : K), ?_⟩
    -- The inverse conjugation recovers the original subgroup element.
    simpa [mackeySubgroup, mul_assoc] using hx
  left_inv x := by
    rcases x with ⟨x, hx⟩
    ext
    simp [mul_assoc]
  right_inv x := by
    rcases x with ⟨x, hx⟩
    ext
    simp [mul_assoc]
  map_mul' x y := by
    ext
    simp [mul_assoc]

/-- Helper for Remark 7-7.3-2: after left translation, the subgroup equivalence is literally
conjugation by `a` inside `K`. -/
@[simp] private theorem mackeySubgroup_mul_left_mulEquiv_apply
    {s a : G} (ha : a ∈ K) {x : mackeySubgroup K H s} :
    ((mackeySubgroup_mul_left_mulEquiv (K := K) (H := H) (s := s) (a := a) ha) x : K) =
      (⟨a, ha⟩ : K) * x * (⟨a, ha⟩ : K)⁻¹ :=
  rfl

/-- Helper for Remark 7-7.3-2: the source twists for `s` and `a * s` agree after transporting the
source subgroup by conjugation inside `K`. -/
private noncomputable def mackeyTwist_mul_left_source_equiv
    {s a : G} (ha : a ∈ K) :
    (mackeyTwist K H W s).ρ.Equiv
      ((mackeyTwist K H W (a * s)).ρ.comp
        (mackeySubgroup_mul_left_mulEquiv (K := K) (H := H) (s := s) (a := a) ha).toMonoidHom) := by
  refine Representation.Equiv.mk (LinearEquiv.refl k W.V) ?_
  intro x
  ext w
  rcases x with ⟨x, hx⟩
  -- The source action is unchanged because `(a * s)⁻¹ (a x a⁻¹) (a * s) = s⁻¹ x s`.
  simp [mackeyTwist, mackeySubgroup, mul_assoc] at hx ⊢

-- Right multiplication by `H` fixes the subgroup and changes the source twist only by the
-- automorphism `W.ρ b`, so induction carries that source equivalence to the ambient summand.
/-- Helper for Remark 7-7.3-2: right multiplication by an element of `H` preserves the Mackey
summand up to isomorphism. -/
theorem mackeySummand_isomorphic_mul_right
    {s b : G} (hb : b ∈ H) :
    IsIsomorphic (mackeySummand K H W s) (mackeySummand K H W (s * b)) := by
  let eSub := mackeySubgroup_mul_right_mulEquiv (K := K) (H := H) (s := s) (b := b) hb
  let eSource :=
    mackeyTwist_mul_right_source_equiv (K := K) (H := H) (W := W) (s := s) (b := b) hb
  let eInducedSource :=
    induced_representation_equiv (k := k) (K := K)
      (V := W.V) (V' := W.V)
      (f := ((mackeySubgroup K H (s * b)).subtype).comp eSub.toMonoidHom)
      eSource
  let eReindex :=
    ind_equiv_of_comp_equiv_local (K := K) eSub
      (V := W.V)
      (f := (mackeySubgroup K H (s * b)).subtype)
      (ρ := (mackeyTwist K H W (s * b)).ρ)
  -- First transport the source twist for the fixed subgroup, then remove the reindexing of the
  -- subgroup inclusion.
  exact ⟨Rep.mkIso (eInducedSource.trans eReindex)⟩

-- Left multiplication by `K` conjugates the Mackey subgroup inside `K`; this changes the source
-- representation only up to the canonical conjugation equivalence, and induction preserves that
-- equivalence.
/-- Left multiplication by an element of `K` transports the Mackey summand to an isomorphic one. -/
theorem mackeySummand_isomorphic_mul_left
    {s a : G} (ha : a ∈ K) :
    IsIsomorphic (mackeySummand K H W s) (mackeySummand K H W (a * s)) := by
  -- Route correction: the old plan tried to force literal equality under left translation, but the
  -- correct route is to compare the two summands through subgroup conjugation inside `K`.
  let aK : K := ⟨a, ha⟩
  let eSub := mackeySubgroup_mul_left_mulEquiv (K := K) (H := H) (s := s) (a := a) ha
  let eAmbient :=
    ind_equiv_of_left_translation_local (k := k)
      (K := K) (S := mackeySubgroup K H s) (V := W.V) aK
      (f := (mackeySubgroup K H s).subtype)
      (f' := ((mackeySubgroup K H (a * s)).subtype).comp eSub.toMonoidHom)
      (ρ := (mackeyTwist K H W s).ρ)
      (by
        intro x
        rfl)
  let eSource := mackeyTwist_mul_left_source_equiv (K := K) (H := H) (W := W) (s := s) (a := a) ha
  let eInducedSource :=
    induced_representation_equiv (k := k) (K := K)
      (V := W.V) (V' := W.V)
      (f := ((mackeySubgroup K H (a * s)).subtype).comp eSub.toMonoidHom)
      eSource
  let eReindex :=
    ind_equiv_of_comp_equiv_local (K := K) eSub
      (V := W.V)
      (f := (mackeySubgroup K H (a * s)).subtype)
      (ρ := (mackeyTwist K H W (a * s)).ρ)
  -- The left translate is the composition of ambient translation, source identification, and the
  -- final source-group reindexing.
  exact ⟨Rep.mkIso ((eAmbient.trans eInducedSource).trans eReindex)⟩

/-- Remark 7-7.3-2: if `s` and `t` have the same image in `K \ G / H`, then the Mackey summands
`Ind_{K ∩ sHs⁻¹}^K(W^s)` and `Ind_{K ∩ tHt⁻¹}^K(W^t)` are isomorphic. In particular, the summand
attached to a representative depends only on its double coset. -/
theorem mackeySummand_isomorphic_of_same_doubleCoset
    {s t : G}
    (hst : DoubleCoset.mk K H s = DoubleCoset.mk K H t) :
    IsIsomorphic (mackeySummand K H W s) (mackeySummand K H W t) := by
  rcases (DoubleCoset.eq K H s t).1 hst with ⟨a, ha, b, hb, rfl⟩
  rcases mackeySummand_isomorphic_mul_left K H W ha with ⟨eLeft⟩
  rcases mackeySummand_isomorphic_mul_right K H W hb with ⟨eRight⟩
  -- Compose the two canonical transports `s ↦ a * s` and `a * s ↦ a * s * b`.
  exact ⟨eLeft ≪≫ eRight⟩

end

end Representation

/-! ### Corollary_7_7_4_2 (from Chap07) -/
open scoped Representation

noncomputable section

universe u v

namespace Representation

section

open Rep (of)

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {W : Type v} [AddCommGroup W] [Module k W]

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's normal-subgroup form of Mackey's irreducibility criterion.
-- * core/canonical owners: `Rep.ind`, `Rep.of`, `Representation.IsIrreducible`,
--   `Representation.Equiv`, and the Chapter 7 conjugation owner `ρ ^ s`.
-- * bridge/view: this corollary keeps the source-facing ordinary representation `ρ`, but phrases
--   induction through the bundled owner `Rep.ind H.subtype (of ρ)` rather than a parallel raw
--   induced-representation surface. The irreducibility transport for conjugates already lives on
--   the owner file `Proposition_7_7_3_1.lean`, so this corollary reuses it rather than
--   redefining it.
-- * primitive data: a normal subgroup `H ≤ G` and a representation `ρ : Representation k H W`.
-- * derived API: irreducibility of the induced owner, irreducibility of conjugates via
--   `Representation.IsIrreducible.pow`, and nonisomorphism with conjugates.

-- Proof sketch: apply Proposition `7-7.4-1`. When `H` is normal, the Mackey subgroup `H_s`
-- is canonically the whole subgroup, and the Mackey twist is restriction of `Rep.of ρ` along the
-- conjugation automorphism `MulAut.conjNormal s⁻¹ : H ≃* H`, so the disjointness condition
-- becomes the nonexistence of an equivalence between `ρ` and its conjugate `ρ^s`; the owner
-- theorem `Representation.IsIrreducible.pow` supplies the corresponding irreducibility transport.
-- The same field, algebraic-closure, and Maschke nonvanishing hypotheses are inherited from
-- Proposition `7-7.4-1`.
/-- Helper for Corollary 7-7.4-2: if `H` is normal, then the Mackey subgroup `H_s` attached to
`H` and `s` is all of `H`. -/
theorem mackeySubgroup_self_eq_top_of_normal
    (H : Subgroup G) [H.Normal] (s : G) :
    mackeySubgroup H H s = ⊤ := by
  -- Normality makes the conjugation condition defining `H_s` automatic for every `h ∈ H`.
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    simpa [mackeySubgroup, mul_assoc] using
      (Subgroup.Normal.conj_mem' inferInstance (x : G) x.2 s)

/-- Helper for Corollary 7-7.4-2: an irreducible representation has a nontrivial carrier space. -/
theorem irreducible_nontrivial_for_normal_corollary
    {H : Subgroup G} (ρ : Representation k H W) [ρ.IsIrreducible] : Nontrivial W := by
  -- If the carrier were subsingleton, the zero and whole subrepresentations would coincide.
  classical
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  exact bot_ne_top hbot_top

/-- Helper for Corollary 7-7.4-2: forgetting the `Rep` packaging in the normal Mackey coordinate
produces an intertwiner from `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_intertwining_to_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) →ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) where
  toFun f := by
    refine
      { toLinearMap := f.toLinearMap
        isIntertwining' := ?_ }
    intro h
    ext w
    have hhK_mem : h ∈ mackeySubgroup H H s := by
      simpa [mackeySubgroup, mul_assoc] using
        (Subgroup.Normal.conj_mem' inferInstance (h : G) h.2 s)
    let hK : mackeySubgroup H H s := ⟨h, hhK_mem⟩
    have hcomm := Representation.IntertwiningMap.isIntertwining (f := f) (g := hK) (v := w)
    have hhconj_mem : s⁻¹ * ↑h * s ∈ H := by
      simpa [mackeySubgroup] using hhK_mem
    have hconj_eq :
        ((MulAut.conjNormal s).symm h) = ⟨s⁻¹ * ↑h * s, hhconj_mem⟩ := by
      ext
      simp [MulAut.conjNormal_symm_apply, mul_assoc]
    simpa [Representation.pow_apply, hK, mackeyTwist, Rep.res_obj_ρ, hconj_eq] using hcomm
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: an intertwiner `ρ ^ s → ρ` restricts to the normal-case Mackey
coordinate map. -/
noncomputable def normal_mackey_intertwining_from_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((ρ ^ s).IntertwiningMap ρ) →ₗ[k]
      ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) where
  toFun g := by
    refine LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := (mackeyTwist H H (of ρ) s).ρ)
      (σ := (Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ)
      g.toLinearMap ?_
    intro x w
    have hconj_mem : s⁻¹ * ↑x.1 * s ∈ H := by
      simpa [mul_assoc] using (Subgroup.Normal.conj_mem' inferInstance (x.1 : G) x.1.2 s)
    have hconj_eq :
        ((MulAut.conjNormal s).symm x.1) = ⟨s⁻¹ * ↑x.1 * s, hconj_mem⟩ := by
      ext
      simp [MulAut.conjNormal_symm_apply, mul_assoc]
    simpa [Representation.pow_apply, mackeyTwist, Rep.res_obj_ρ, hconj_eq] using
      (Representation.IntertwiningMap.isIntertwining (f := g) (g := x.1) (v := w))
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: after forgetting the `Rep` packaging, the normal-case Mackey
coordinate maps are exactly the intertwining maps from `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_intertwining_equiv_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    ((mackeyTwist H H (of ρ) s).ρ).IntertwiningMap
        ((Rep.res (mackeySubgroup H H s).subtype (of ρ)).ρ) ≃ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) where
  __ := normal_mackey_intertwining_to_conjugate (H := H) ρ s
  invFun := normal_mackey_intertwining_from_conjugate (H := H) ρ s
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  right_inv g := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- Helper for Corollary 7-7.4-2: in the normal-subgroup case, the Mackey-coordinate morphisms are
exactly the intertwining maps from the conjugate representation `ρ ^ s` to `ρ`. -/
noncomputable def normal_mackey_hom_equiv_conjugate
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) (s : G) :
    (mackeyTwist H H (of ρ) s ⟶ Rep.res (mackeySubgroup H H s).subtype (of ρ)) ≃ₗ[k]
      ((ρ ^ s).IntertwiningMap ρ) :=
  (Rep.homLinearEquiv _ _) ≪≫ₗ normal_mackey_intertwining_equiv_conjugate (H := H) ρ s

/-- Helper for Corollary 7-7.4-2: under irreducibility, Mackey disjointness in the normal case is
exactly nonisomorphism with the conjugate representation. -/
theorem normal_mackey_disjoint_iff_not_isomorphic
    (H : Subgroup G) [H.Normal] (ρ : Representation k H W) [ρ.IsIrreducible] (s : G) :
    (∀ f : mackeyTwist H H (of ρ) s ⟶ Rep.res (mackeySubgroup H H s).subtype (of ρ), f = 0) ↔
      ¬ Nonempty ((ρ ^ s).Equiv ρ) := by
  constructor
  · intro h hiso
    rcases hiso with ⟨e⟩
    let eHom := normal_mackey_hom_equiv_conjugate (H := H) ρ s
    have hmackey_zero : eHom.symm e.toIntertwiningMap = 0 := h (eHom.symm e.toIntertwiningMap)
    have hzero : e.toIntertwiningMap = 0 := by
      simpa using congrArg eHom hmackey_zero
    letI : Nontrivial W := irreducible_nontrivial_for_normal_corollary ρ
    have hnot_bijective_zero : ¬ Function.Bijective (0 : (ρ ^ s).IntertwiningMap ρ) := by
      intro hzero_bij
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      exact hx <| hzero_bij.injective (by simp)
    exact hnot_bijective_zero <| by simpa [hzero] using e.bijective
  · intro h f
    let eHom := normal_mackey_hom_equiv_conjugate (H := H) ρ s
    have hpow : (ρ ^ s).IsIrreducible := Representation.IsIrreducible.pow ρ s
    letI : (ρ ^ s).IsIrreducible := hpow
    by_contra hf
    have hne : eHom f ≠ 0 := by
      intro hzero
      exact hf (eHom.injective hzero)
    rcases Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := ρ ^ s) (σ := ρ) (f := eHom f) with hbij | hzero
    · exact h ⟨(eHom f).ofBijective hbij⟩
    · exact hne hzero

/-- Corollary 7-7.4-2: if `H` is normal in `G`, then the induced representation `Ind_H^G(ρ)` is
irreducible if and only if `ρ` is irreducible and, for every `s ∉ H`, the conjugate
representation `ρ^s` is not isomorphic to `ρ`. -/
theorem ind_isIrreducible_iff_isIrreducible_and_not_isomorphic_to_conjugates
    [IsAlgClosed k] (H : Subgroup G) [H.Normal] (ρ : Representation k H W) :
    (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible ↔
      ρ.IsIrreducible ∧
        ∀ s : G, s ∉ H →
          ¬ Nonempty ((ρ ^ s).Equiv ρ) := by
  -- Route correction: specialize the Mackey criterion and rewrite each Mackey-coordinate vanishing
  -- condition as the absence of an equivalence `ρ ^ s ≃ ρ`.
  refine (ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint (H := H) (ρ := ρ)).trans ?_
  constructor
  · rintro ⟨hρ, hmackey⟩
    refine ⟨hρ, ?_⟩
    intro s hs
    letI : ρ.IsIrreducible := hρ
    exact (normal_mackey_disjoint_iff_not_isomorphic (H := H) ρ s).1 (hmackey s hs)
  · rintro ⟨hρ, hconj⟩
    refine ⟨hρ, ?_⟩
    intro s hs f
    letI : ρ.IsIrreducible := hρ
    exact (normal_mackey_disjoint_iff_not_isomorphic (H := H) ρ s).2 (hconj s hs) f

end

end Representation

/-! ### Exercise_7_7_4_3 (from Chap07) -/
open Matrix
open scoped MatrixGroups

noncomputable section

universe u

section UpperTriangularSubgroup

variable (k : Type u) [CommRing k]

-- Source/core/bridge triage for Exercise 7-7.4-3:
-- * source-facing: the subgroup `H ≤ SL(2, k)` of upper triangular matrices and its linear
--   character `χ_ω`.
-- * core/canonical owners sampled in this domain: `Matrix.BlockTriangular` for the upper
--   triangular condition, `MonoidHom.toRepresentation` for the degree-one representation,
--   `Rep.of`/`Rep.ind` for the bundled Chapter 7 induction owner, and
--   `Representation.ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint` for the Mackey
--   irreducibility criterion phrased through that owner.
-- * bridge/view: the subgroup-owner map `sl2UpperTriangularSubgroup.topLeft k` extracting the
--   top-left unit, from which `χ_ω` is obtained by composition with `ω`.
-- * primitive data: the subgroup `sl2UpperTriangularSubgroup k` and its source-facing character
--   `sl2UpperTriangularSubgroup.character k ω`.
-- * derived API: the induced irreducibility statement, which should be expressed through the
--   bundled owner `Rep.ind ... (Rep.of ...)`.

local notation "M₂" => Matrix (Fin 2) (Fin 2) k

/-- The subgroup `H ≤ SL(2, k)` of upper triangular matrices, namely the matrices
`[[a, b], [0, d]]`. -/
def sl2UpperTriangularSubgroup : Subgroup (SL(2, k)) where
  carrier := { g | (g : M₂).BlockTriangular id }
  one_mem' := by
    simpa using (Matrix.blockTriangular_one :
      Matrix.BlockTriangular (1 : M₂) id)
  mul_mem' := by
    intro g h hg hh
    exact hg.mul hh
  inv_mem' := by
    intro g hg
    have hdet : IsUnit (((g : M₂)).det) := by
      simp [g.det_coe]
    change (((g⁻¹ : SL(2, k)) : M₂).BlockTriangular id)
    rw [show ((g⁻¹ : SL(2, k)) : M₂) = ((g : M₂)⁻¹) by
      rw [Matrix.SpecialLinearGroup.coe_inv,
        Matrix.nonsing_inv_apply (g : M₂) hdet]
      simp [g.det_coe]]
    let _ : Invertible (g : M₂) := Matrix.invertibleOfIsUnitDet (g : M₂) hdet
    simpa using Matrix.blockTriangular_inv_of_blockTriangular hg

namespace sl2UpperTriangularSubgroup

/-- Membership in `sl2UpperTriangularSubgroup` is exactly the canonical upper-triangular
predicate on the underlying `2 × 2` matrix. -/
@[simp] theorem mem_iff (g : SL(2, k)) :
    g ∈ sl2UpperTriangularSubgroup k ↔ ((g : M₂).BlockTriangular id) :=
  Iff.rfl

/-- An upper triangular element of `SL(2, k)` has vanishing lower-left entry. -/
private theorem apply_one_zero (g : sl2UpperTriangularSubgroup k) :
    ((g : SL(2, k)) 1 0) = 0 := by
  simpa using g.2 (show (0 : Fin 2) < 1 by decide)

/-- For an upper triangular element of `SL(2, k)`, the diagonal entries multiply to `1`. -/
private theorem topLeft_mul_bottomRight (h : sl2UpperTriangularSubgroup k) :
    ((h : SL(2, k)) 0 0) * ((h : SL(2, k)) 1 1) = 1 := by
  have hdet : (((h : SL(2, k)) : M₂).det) = 1 := (h : SL(2, k)).det_coe
  rw [Matrix.det_of_upperTriangular h.2, Fin.prod_univ_two] at hdet
  exact hdet

/-- The canonical monoid hom sending an upper triangular element of `SL(2, k)` to its top-left
unit. -/
def topLeft : sl2UpperTriangularSubgroup k →* kˣ where
  toFun h :=
    ⟨((h : SL(2, k)) 0 0), ((h : SL(2, k)) 1 1),
      topLeft_mul_bottomRight k h,
      by simpa [mul_comm] using topLeft_mul_bottomRight k h⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' h h' := by
    apply Units.ext
    change ((h * h' : sl2UpperTriangularSubgroup k) : SL(2, k)) 0 0 =
      ((h : SL(2, k)) 0 0) * ((h' : SL(2, k)) 0 0)
    simp [Matrix.mul_apply, Fin.sum_univ_two, apply_one_zero k h']

/-- The underlying value of `topLeft h` is the top-left entry of `h`. -/
@[simp] theorem topLeft_val (h : sl2UpperTriangularSubgroup k) :
    ((topLeft k h : kˣ) : k) = ((h : SL(2, k)) 0 0) :=
  rfl

/-- The degree-one character `χ_ω` of the upper triangular subgroup of `SL(2, k)`, defined by
`χ_ω([[a, b], [0, d]]) = ω(a)`. -/
def character (ω : kˣ →* ℂˣ) : sl2UpperTriangularSubgroup k →* ℂˣ :=
  ω.comp (topLeft k)

end sl2UpperTriangularSubgroup

end UpperTriangularSubgroup

section Irreducibility

variable (k : Type) [Field k] [Finite k]

open Rep (of)

local notation "M₂" => Matrix (Fin 2) (Fin 2) k
local notation "H" => sl2UpperTriangularSubgroup k

/-- Helper for Exercise 7-7.4-3: an element of `SL(2, k)` outside the upper triangular subgroup
has nonzero lower-left entry. -/
lemma lower_left_ne_zero_of_not_mem_upperTriangular
    {s : SL(2, k)} (hs : s ∉ H) : ((s : M₂) 1 0) ≠ 0 := by
  -- The only obstruction to upper triangularity in size `2` is the `(1,0)` entry.
  intro h10
  apply hs
  show ((s : M₂).BlockTriangular id)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  simpa using h10

/-- Helper for Exercise 7-7.4-3: the Mackey conjugation map
`H ∩ sHs⁻¹ → H`, written explicitly for the upper triangular subgroup of `SL(2, k)`. -/
noncomputable def sl2_upper_triangular_mackey_conj_hom (s : SL(2, k)) :
    Representation.mackeySubgroup H H s →* H :=
  (((MulAut.conj s⁻¹).toMonoidHom.comp (sl2UpperTriangularSubgroup k).subtype).restrict
      (Representation.mackeySubgroup H H s)).codRestrict H fun x ↦ x.2

/-- Helper for Exercise 7-7.4-3: every element outside the upper triangular subgroup yields a
Mackey-subgroup element whose top-left entry is `u` and whose conjugate top-left entry is
`u⁻¹`. -/
lemma exists_mackey_test_element_with_topLeft_values
    {s : SL(2, k)} (hs : s ∉ H) (u : kˣ) :
    ∃ x : Representation.mackeySubgroup H H s,
      sl2UpperTriangularSubgroup.topLeft k x.1 = u ∧
        sl2UpperTriangularSubgroup.topLeft k (sl2_upper_triangular_mackey_conj_hom (k := k) s x) =
          u⁻¹ := by
  let a : k := (s : M₂) 0 0
  let c : k := (s : M₂) 1 0
  have hc : c ≠ 0 := by
    -- The off-Borel hypothesis is exactly the denominator nonvanishing needed below.
    simpa [c] using lower_left_ne_zero_of_not_mem_upperTriangular (k := k) hs
  let t : k := a * (((u⁻¹ : kˣ) : k) - (u : k)) / c
  let xM : M₂ := !![(u : k), t; 0, ((u⁻¹ : kˣ) : k)]
  have hxM_det : xM.det = 1 := by
    -- The witness matrix already has determinant `u * u⁻¹ = 1`.
    rw [show xM = !![(u : k), t; 0, ((u⁻¹ : kˣ) : k)] by rfl, Matrix.det_fin_two]
    simp [xM, t]
  let xSL : SL(2, k) := ⟨xM, hxM_det⟩
  have hxH_mem : xSL ∈ H := by
    -- The witness is visibly upper triangular.
    show ((xSL : M₂).BlockTriangular id)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [xSL, xM] at hij ⊢
  let xH : H := ⟨xSL, hxH_mem⟩
  have hx_conj_mem : xH ∈ Representation.mackeySubgroup H H s := by
    -- Conjugating by `s` cancels the lower-left entry by the chosen value of `t`.
    have hx_conj_triangular : ((((s⁻¹ : SL(2, k)) : M₂) * xM) * (s : M₂)).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      have hsdet : ((s : M₂) 0 0) * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 = 1 := by
        have hsdet0 := s.det_coe
        rwa [Matrix.det_fin_two] at hsdet0
      rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp [xM]
      dsimp [t, a, c] at *
      field_simp [hc]
      ring_nf
      simp
    change (((MulAut.conj s⁻¹).toMonoidHom.comp (sl2UpperTriangularSubgroup k).subtype) xH) ∈ H
    rw [sl2UpperTriangularSubgroup.mem_iff]
    simpa [MulAut.conj, xH, xSL, Matrix.mul_assoc] using hx_conj_triangular
  let x : Representation.mackeySubgroup H H s := ⟨xH, hx_conj_mem⟩
  refine ⟨x, ?_, ?_⟩
  · -- The first top-left value is built into the witness matrix.
    apply Units.ext
    simp [sl2UpperTriangularSubgroup.topLeft_val, x, xH, xSL, xM]
  · -- The conjugated top-left entry becomes `u⁻¹` by the determinant-one identity of `s`.
    apply Units.ext
    have hsdet : ((s : M₂) 0 0) * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 = 1 := by
      have hsdet0 := s.det_coe
      rwa [Matrix.det_fin_two] at hsdet0
    have hc : ((s : M₂) 1 0) ≠ 0 := by
      exact lower_left_ne_zero_of_not_mem_upperTriangular (k := k) hs
    have htopLeftAdj :
        (((s : M₂).adjugate * xM * (s : M₂)) 0 0) = ((u⁻¹ : kˣ) : k) := by
      rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      simp [xM]
      dsimp [t, a, c] at *
      field_simp [hc]
      ring_nf
      have hmul :
          (s : M₂) 1 1 * (u : k) * (s : M₂) 0 0 * ((u⁻¹ : kˣ) : k) -
              (s : M₂) 1 0 * (s : M₂) 0 1
            = (s : M₂) 0 0 * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 := by
        calc
          (s : M₂) 1 1 * (u : k) * (s : M₂) 0 0 * ((u⁻¹ : kˣ) : k) - (s : M₂) 1 0 * (s : M₂) 0 1
              = (s : M₂) 0 0 * (s : M₂) 1 1 * ((u : k) * ((u⁻¹ : kˣ) : k)) -
                  (s : M₂) 0 1 * (s : M₂) 1 0 := by
                    ring
          _ = (s : M₂) 0 0 * (s : M₂) 1 1 - (s : M₂) 0 1 * (s : M₂) 1 0 := by
                simp
      exact hmul.trans hsdet
    simpa [sl2_upper_triangular_mackey_conj_hom, sl2UpperTriangularSubgroup.topLeft_val,
      MulAut.conj, x, xH, xSL, Matrix.mul_assoc, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.nonsing_inv_apply, s.det_coe] using htopLeftAdj

/-- Helper for Exercise 7-7.4-3: a complex linear endomorphism of the one-dimensional space `ℂ`
is determined by its value at `1`. -/
lemma complex_linear_apply_eq_mul_apply_one (T : ℂ →ₗ[ℂ] ℂ) (z : ℂ) :
    T z = z * T 1 := by
  -- Write `z` as `z • 1` and then use linearity.
  calc
    T z = T (z • (1 : ℂ)) := by simp
    _ = z • T 1 := by rw [LinearMap.map_smul]
    _ = z * T 1 := by simp [smul_eq_mul]

/-- Helper for Exercise 7-7.4-3: if two representations on the line `ℂ` act differently on some
group element, then every intertwiner between them is zero. -/
lemma hom_zero_of_action_on_one_mismatch
    {Γ : Type*} [Group Γ] {ρ σ : Representation ℂ Γ ℂ}
    (h : ∃ g : Γ, (ρ g) 1 ≠ (σ g) 1) :
    ∀ f : Rep.of ρ ⟶ Rep.of σ, f = 0 := by
  intro f
  rcases h with ⟨g, hg⟩
  have hscalar : (ρ g) 1 * Rep.Hom.hom f 1 = (σ g) 1 * Rep.Hom.hom f 1 := by
    -- Evaluate the intertwining relation at `1` and rewrite each linear map by its value on `1`.
    calc
      (ρ g) 1 * Rep.Hom.hom f 1 = Rep.Hom.hom f ((ρ g) 1) := by
        symm
        simpa using complex_linear_apply_eq_mul_apply_one (Rep.Hom.hom f) ((ρ g) 1)
      _ = (σ g) (Rep.Hom.hom f 1) := by
        simpa using Representation.IntertwiningMap.isIntertwining ρ σ (Rep.Hom.hom f) g (1 : ℂ)
      _ = (σ g) 1 * Rep.Hom.hom f 1 := by
        simpa using complex_linear_apply_eq_mul_apply_one (σ g) (Rep.Hom.hom f 1)
  have hFone : Rep.Hom.hom f 1 = 0 := by
    -- A nonzero value at `1` would force the two scalar actions to coincide.
    by_contra hFone
    exact hg (mul_right_cancel₀ hFone hscalar)
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  -- Once the map kills `1`, linearity forces it to vanish everywhere.
  have hz : (Rep.Hom.hom f) z = z * Rep.Hom.hom f 1 := by
    simpa using complex_linear_apply_eq_mul_apply_one (Rep.Hom.hom f) z
  simp [hz, hFone]

/-- Helper for Exercise 7-7.4-3: if `ω²` is nontrivial, then some unit `u` satisfies
`(ω u)^2 ≠ 1`. -/
lemma exists_unit_sq_ne_one_of_character_sq_ne_one
    (ω : kˣ →* ℂˣ) (hω : (ω ^ 2 : kˣ →* ℂˣ) ≠ 1) :
    ∃ u : kˣ, (ω u) ^ 2 ≠ 1 := by
  -- Otherwise every value of `ω²` would be `1`, forcing `ω² = 1`.
  by_contra h
  apply hω
  ext u
  push Not at h
  simpa [pow_two] using congrArg (fun z : ℂˣ => (z : ℂ)) (h u)

-- Proof sketch: apply Mackey's irreducibility criterion to the pair
-- `(SL(2, k), sl2UpperTriangularSubgroup)` and the bundled induced owner
-- `Rep.ind (sl2UpperTriangularSubgroup k).subtype
--   (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)`.
-- The unique nontrivial double-coset representative is the Weyl element, and the resulting
-- intertwining space is zero exactly when `ω^2` is nontrivial.
/-- Exercise 7-7.4-3: if `k` is a finite field and `ω : kˣ →* ℂˣ` satisfies `ω^2 ≠ 1`, then the
representation of `SL(2, k)` induced from the degree-one character `χ_ω` of the upper triangular
subgroup `H = {[[a, b], [0, d]]}` is irreducible. -/
theorem sl2UpperTriangularCharacter_induced_isIrreducible_of_sq_ne_one
    (ω : kˣ →* ℂˣ) (hω : (ω ^ 2 : kˣ →* ℂˣ) ≠ 1) :
    (Rep.ind (sl2UpperTriangularSubgroup k).subtype
      (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ.IsIrreducible := by
  let hcard_nat : Nat.card (SL(2, k)) ≠ 0 :=
    (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  letI : NeZero (Nat.card (SL(2, k)) : ℂ) := ⟨by
    exact_mod_cast hcard_nat⟩
  -- Route correction: rather than passing to a global Bruhat representative, use Proposition
  -- `7-7.4-1` exactly as stated and kill each off-Borel Mackey intertwiner by an explicit
  -- witness in `H ∩ sHs⁻¹`.
  have hcriterion :=
    Representation.ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
      (k := ℂ) (V := ℂ)
      (sl2UpperTriangularSubgroup k)
      (sl2UpperTriangularSubgroup.character k ω).toRepresentation
  refine hcriterion.2 ?_
  constructor
  · -- A character line is already irreducible.
    simpa using MonoidHom.toRepresentation_isIrreducible (sl2UpperTriangularSubgroup.character k ω)
  · intro s hs f
    obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_of_character_sq_ne_one (k := k) ω hω
    obtain ⟨x, hx_top, hx_conj_top⟩ :=
      exists_mackey_test_element_with_topLeft_values (k := k) hs u
    have hω_units_ne : ω u ≠ ω u⁻¹ := by
      -- Equality of the two character values would force `(ω u)^2 = 1`.
      intro hEq
      apply hu
      calc
        (ω u) ^ 2 = ω u * ω u := by simp [pow_two]
        _ = ω u * ω u⁻¹ := by rw [hEq]
        _ = ω (u * u⁻¹) := by rw [← map_mul]
        _ = 1 := by simp
    have hω_ne : (ω u : ℂ) ≠ (ω u⁻¹ : ℂ) := by
      intro hEq
      apply hω_units_ne
      exact Units.ext hEq
    have hsource :
        (((Representation.mackeyTwist H H
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ x) (1 : ℂ)) =
          (ω u⁻¹ : ℂ) := by
      -- On the twisted side, the explicit conjugation map sends the witness top-left entry to
      -- `u⁻¹`.
      change (((sl2UpperTriangularSubgroup.character k ω).toRepresentation
          (sl2_upper_triangular_mackey_conj_hom (k := k) s x)) (1 : ℂ)) = (ω u⁻¹ : ℂ)
      simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, sl2UpperTriangularSubgroup.character,
        hx_conj_top]
    have htarget :
        (((Rep.res (Representation.mackeySubgroup H H s).subtype
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ x) (1 : ℂ)) =
          (ω u : ℂ) := by
      -- On the restricted side, the same witness still has top-left entry `u`.
      change (((sl2UpperTriangularSubgroup.character k ω).toRepresentation x.1) (1 : ℂ)) =
        (ω u : ℂ)
      simp [MonoidHom.toRepresentation, LinearMap.lsmul_apply, sl2UpperTriangularSubgroup.character,
        hx_top]
    have hsource_target_ne :
        (((Representation.mackeyTwist H H
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ x) (1 : ℂ)) ≠
          (((Rep.res (Representation.mackeySubgroup H H s).subtype
            (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ x) (1 : ℂ)) := by
      rw [hsource, htarget]
      exact hω_ne.symm
    exact hom_zero_of_action_on_one_mismatch
      (ρ := (Representation.mackeyTwist H H
        (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation) s).ρ)
      (σ := (Rep.res (Representation.mackeySubgroup H H s).subtype
        (of (sl2UpperTriangularSubgroup.character k ω).toRepresentation)).ρ)
      ⟨x, hsource_target_ne⟩ f

end Irreducibility

/-! ### Proposition_7_7_4_1 (from Chap07) -/
noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientMainProposition7741 (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

omit [Finite G] [NeZero (Nat.card G : k)] in
/-- Helper for Proposition 7-7.4-1: transporting a Mackey coordinate along an equality of double
cosets preserves and reflects vanishing. -/
theorem mackey_coordinate_equiv_of_same_doubleCoset_eq_zero_iff
    (H : Subgroup G) (ρ : Representation k H V)
    {s t : G}
    (hst : DoubleCoset.mk H H s = DoubleCoset.mk H H t)
    (f : mackeyTwist H H (of ρ) s ⟶
      Rep.res (mackeySubgroup H H s).subtype (of ρ)) :
    (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
      (s := s) (t := t) hst f = 0) ↔ f = 0 := by
  constructor
  · intro hf
    -- The same-double-coset transport is a linear equivalence, so its image can vanish only when
    -- the original coordinate already vanishes.
    exact
      (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
        (s := s) (t := t) hst).injective <| by
          simpa using hf
  · intro hf
    -- Conversely, the transport sends the zero coordinate to zero.
    rw [hf]
    simp

theorem ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
    [IsAlgClosed k] (H : Subgroup G) (ρ : Representation k H V) :
    (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible ↔
      ρ.IsIrreducible ∧
        ∀ s ∉ H,
          ∀ f : mackeyTwist H H (of ρ) s ⟶
              Rep.res (mackeySubgroup H H s).subtype (of ρ),
            f = 0 := by
  -- Follow LinearRepresentations_Serre_1977's Schur step over an algebraically closed field: global endomorphisms of an
  -- irreducible induced representation are scalar, while an off-identity Mackey singleton has zero
  -- identity coordinate.
  constructor
  · intro hInd
    have hρ : ρ.IsIrreducible := isIrreducible_of_ind_isIrreducible H ρ hInd
    refine ⟨hρ, ?_⟩
    intro s hs f
    letI : ρ.IsIrreducible := hρ
    let q : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H s
    have hq : q ≠ DoubleCoset.mk H H (1 : G) :=
      doubleCoset_ne_identity_of_not_mem H hs
    have hrep_not_mem : doubleCosetRepresentative H q ∉ H :=
      doubleCosetRepresentative_not_mem_of_ne_identity H hq
    -- Package the contradiction at the representative-indexed Mackey coordinate used by the global
    -- coordinate equivalence.
    let fq :
        mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
          Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ) :=
      (mackey_coordinate_equiv_of_same_doubleCoset (k := k) H ρ
        (s := s) (t := doubleCosetRepresentative H q)
        (by
          calc
            DoubleCoset.mk H H s = q := rfl
            _ = DoubleCoset.mk H H (doubleCosetRepresentative H q) := by
              symm
              exact doubleCosetRepresentative_spec H q)) f
    have hf_zero_of_fq_zero : fq = 0 → f = 0 := by
      -- Reuse the new transport lemma to pull vanishing back across the double-coset
      -- identification instead of re-proving injectivity inline.
      intro hfq
      exact
        (mackey_coordinate_equiv_of_same_doubleCoset_eq_zero_iff
          (k := k) H ρ
          (s := s) (t := doubleCosetRepresentative H q)
          (by
            calc
              DoubleCoset.mk H H s = q := rfl
              _ = DoubleCoset.mk H H (doubleCosetRepresentative H q) := by
                symm
                exact doubleCosetRepresentative_spec H q)
          f).1 <| by
            simpa [fq] using hfq
    let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
    let xi := singleton_mackey_coordinate_family (k := k) H ρ q fq
    let F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ) := e.symm xi
    have hF_coordinates : e F = xi := by
      simp [F, e]
    by_cases hfq : fq = 0
    · exact hf_zero_of_fq_zero hfq
    have hF_bij : Function.Bijective F.hom :=
      bijective_of_singleton_coordinate_nonzero_of_ind_isIrreducible (k := k) H ρ
        hInd q fq F hF_coordinates hfq
    have hidentity_coordinate_zero :
        (e F) (DoubleCoset.mk H H (1 : G)) = 0 := by
      -- Package the singleton-support computation at the identity double coset into a reusable
      -- coordinate vanishing lemma.
      exact singleton_off_identity_identity_coordinate_eq_zero H ρ hq fq F
        hF_coordinates
    let gF : Rep.of ρ ⟶ Rep.of ρ :=
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e F) (DoubleCoset.mk H H (1 : G)))
    have hgF_zero : gF = 0 := by
      -- The new identity-coordinate helper upgrades the zero coordinate directly to the zero
      -- self-intertwiner of `ρ`.
      simpa [gF] using
        singleton_off_identity_identity_self_hom_eq_zero H ρ hq fq F hF_coordinates
    have hproj_unit_zero :
        ∀ v : V,
          inducedIdentityCopyProjection H ρ
            (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) = 0 := by
      -- The identity Mackey coordinate of the singleton family vanishes, so the transported
      -- endomorphism has zero unit-copy projection on the unit generators.
      intro v
      exact singleton_off_identity_family_projection_eq_zero (k := k) H ρ hq fq F
        hF_coordinates v
    have hrestricted_identity_block_zero :
        ∀ h : H, ∀ v : V,
          (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom
            (Representation.IndV.mk H.subtype ρ (h : G) v)).down = 0 := by
      -- The corrected frontier extends the vanishing from the unit generator to the entire
      -- identity Mackey block viewed through the restricted Frobenius map.
      intro h v
      exact singleton_off_identity_restricted_hom_identity_block_eq_zero (k := k) H ρ
        hq fq F hF_coordinates h v
    have hF_not_bijective : ¬ Function.Bijective F.hom := by
      exact off_identity_singleton_not_bijective_of_ind_isIrreducible
        (k := k) H ρ hInd hq fq hfq F hF_coordinates
    exact False.elim (hF_not_bijective hF_bij)
  · rintro ⟨hρ, hdisjoint⟩
    letI : ρ.IsIrreducible := hρ
    letI : Nontrivial V := irreducible_nontrivial ρ
    letI : Nontrivial (Representation.IndV H.subtype ρ) := by
      -- The unit-coset copy embeds the nontrivial space `V` into the induced representation.
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine ⟨⟨Representation.IndV.mk H.subtype ρ 1 v, 0, ?_⟩⟩
      intro hEq
      have hEq' : Representation.IndV.mk H.subtype ρ 1 v =
          Representation.IndV.mk H.subtype ρ 1 (0 : V) := by
        simpa using hEq
      have := induced_unit_generator_injective (k := k) H ρ hEq'
      exact hv this
    -- It suffices to show that every nonzero endomorphism of the induced representation is
    -- bijective; the coordinate equivalence reduces such an endomorphism to its identity block.
    refine isIrreducible_of_semisimple_and_nonzero_endomorphisms_bijective
      (τ := (Rep.ind H.subtype (of ρ)).ρ) ?_
    intro F hF_ne
    let τ : Rep k G := Rep.ind H.subtype (of ρ)
    let Fhom : τ ⟶ τ := (Rep.homLinearEquiv τ τ).symm F
    let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
    let g : Rep.of ρ ⟶ Rep.of ρ :=
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e Fhom) (DoubleCoset.mk H H (1 : G)))
    have hsupport :
        ∀ q : DoubleCoset.Quotient (H : Set G) H,
          q ≠ DoubleCoset.mk H H (1 : G) → (e Fhom) q = 0 := by
      intro q hq
      -- Every off-identity coordinate is one of the disjoint Mackey intertwining spaces.
      have hnotmem : doubleCosetRepresentative H q ∉ H :=
        doubleCosetRepresentative_not_mem_of_ne_identity H hq
      exact hdisjoint (doubleCosetRepresentative H q) hnotmem ((e Fhom) q)
    have hFhom_eq :
        Fhom = Rep.indMap H.subtype g :=
      endomorphism_eq_indMap_of_identity_supported (k := k) H ρ Fhom hsupport
    have hF_eq :
        F = (Rep.indMap H.subtype g).hom := by
      have := congrArg (Rep.homLinearEquiv τ τ) hFhom_eq
      simpa [Fhom] using this
    have hg_ne : g ≠ 0 := by
      intro hg
      apply hF_ne
      rw [hF_eq, hg]
      ext x
      simp [Rep.indMap]
    have hg_bij : Function.Bijective g.hom := by
      -- A nonzero endomorphism of the irreducible `H`-representation `ρ` is bijective.
      exact
        (Representation.IsIrreducible.bijective_or_eq_zero
          (ρ := ρ) (σ := ρ) (f := g.hom)).resolve_right <| by
            intro hg_zero
            exact hg_ne (Rep.hom_ext hg_zero)
    -- The previous induction lemma transports bijectivity from `g` to the global endomorphism `F`.
    simpa [hF_eq] using
      (induced_map_bijective_iff_self_hom_bijective (k := k) H ρ g).2 hg_bij
end MackeyIrreducibilityCriterion
#print axioms  ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
end Representation
