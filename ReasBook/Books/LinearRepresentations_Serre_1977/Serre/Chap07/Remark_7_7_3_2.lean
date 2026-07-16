import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_3_1

-- Declarations for this item will be appended below by the statement pipeline.

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
