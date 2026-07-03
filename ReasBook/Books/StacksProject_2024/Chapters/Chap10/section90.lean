import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_90_1 (from Chap10) -/
universe u v

namespace Module

/-- Definition 10.90.1 (1): an `R`-module is coherent if it is finitely generated and every
finitely generated submodule is finitely presented over `R`. -/
class Coherent (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] : Prop
    extends Module.Finite R M where
  finitePresentation_submodule :
    ∀ (N : Submodule R M), Module.Finite R N → Module.FinitePresentation R N

end Module

/-- Definition 10.90.1 (2): a commutative ring is coherent if it is coherent as a module over
itself. -/
class IsCoherentRing (R : Type u) [CommRing R] : Prop extends Module.Coherent R R

/-! ### Example_10_90_2 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/-- Example 10.90.2: a valuation ring is coherent. The owner abstraction is
`IsCoherentRing`; finite presentation of finitely generated ideals is derived from this instance. -/
instance valuationRing_isCoherentRing : IsCoherentRing A where
  toCoherent :=
    { toFinite := by infer_instance
      finitePresentation_submodule := by
        intro I hI
        have hI' : I.FG := by
          simpa [Module.Finite.iff_fg] using hI
        letI : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hI'
        by_cases h : I = ⊥
        · subst h
          infer_instance
        · exact Module.FinitePresentation.of_equiv (Ideal.isoBaseOfIsPrincipal h) }

end

/-! ### Lemma_10_90_3 (from Chap10) -/
universe u v w

open CategoryTheory Module.Finite

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A coherent module is finitely presented. -/
instance finitePresentation_of_coherent [Module.Coherent R M] :
    Module.FinitePresentation R M := by
  letI : Module.FinitePresentation R (⊤ : Submodule R M) :=
    (inferInstance : Module.Coherent R M).finitePresentation_submodule ⊤ inferInstance
  exact Module.FinitePresentation.of_equiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)

attribute [instance 100] finitePresentation_of_coherent

-- Proof sketch: if `Q ≤ P` is finite, then `Q` is also a finite submodule of `M`, so coherence of
-- `M` makes `Q` finitely presented; together with finiteness of `P`, this shows `P` is coherent.
/-- Lemma 10.90.3: a finite submodule of a coherent `R`-module is coherent. -/
instance coherent_submodule_of_finite {P : Submodule R M}
    [Module.Coherent R M] [Module.Finite R P] :
    Module.Coherent R P where
  toFinite := inferInstance
  finitePresentation_submodule Q hQ := by
    let e : Q ≃ₗ[R] Q.map P.subtype :=
      Q.equivMapOfInjective P.subtype P.subtype_injective
    letI : Module.Finite R (Q.map P.subtype) := Module.Finite.of_fg
      ((iff_fg.mp hQ).map P.subtype)
    letI : Module.FinitePresentation R (Q.map P.subtype) :=
      (inferInstance : Module.Coherent R M).finitePresentation_submodule (Q.map P.subtype)
        inferInstance
    exact Module.FinitePresentation.of_equiv e.symm

attribute [instance 100] coherent_submodule_of_finite

-- Proof sketch: pull a finite submodule back along the equivalence, use coherence on the source
-- side, and transport finite presentation back across the induced equivalence on submodules.
/-- Helper for Lemma 10.90.3: coherence is preserved by linear equivalences. -/
theorem coherent_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') [hM : Module.Coherent R M] :
    Module.Coherent R M' where
  toFinite := Module.Finite.of_surjective e.toLinearMap e.surjective
  finitePresentation_submodule P hP := by
    -- Pull the finite submodule back to the coherent source, where coherence gives finite
    -- presentation directly.
    let eP := (P.comap e.toLinearMap).equivMapOfInjective e.toLinearMap e.injective
    have hmap : (P.comap e.toLinearMap).map e.toLinearMap = P :=
      Submodule.map_comap_eq_of_surjective e.surjective P
    letI : Module.Finite R ((P.comap e.toLinearMap).map e.toLinearMap) := by
      rw [hmap]
      exact hP
    letI : Module.Finite R (P.comap e.toLinearMap) := Module.Finite.equiv eP.symm
    letI : Module.FinitePresentation R (P.comap e.toLinearMap) :=
      hM.finitePresentation_submodule (P.comap e.toLinearMap) inferInstance
    exact Module.FinitePresentation.of_equiv
      (eP.trans (LinearEquiv.ofEq _ _ hmap))

-- Proof sketch: the image is a finite module because it is a quotient of the finite domain. The
-- short exact sequence `0 → ker φ → N → range φ → 0` and the finite presentation of the coherent
-- image then give finite generation of the kernel by Lemma `10.5.3`.
/-- The kernel of a map from a finite module to a coherent module is finite. -/
theorem ker_finite_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Finite R (LinearMap.ker φ) := by
  have hExact : Function.Exact (LinearMap.ker φ).subtype φ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  letI : Module.FinitePresentation R (LinearMap.range φ) := inferInstance
  exact Module.Finite.of_exact_of_finitePresentation (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict hExact

-- Proof sketch: `range φ` is a finite submodule of the coherent codomain because it is a quotient
-- of the finite domain, so the previous clause applies to this finite submodule.
/-- The image of a map from a finite module to a coherent module is coherent. -/
theorem range_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (LinearMap.range φ) := by
  letI : Module.Finite R (LinearMap.range φ) := Module.Finite.of_fg (Submodule.fg_range φ)
  infer_instance

-- Proof sketch: for a finite submodule of the quotient `M ⧸ range φ`, pull it back to a finite
-- submodule of `M`; coherence of `M` and Lemma `10.5.3` on the induced short exact sequence yield
-- finite presentation downstairs.
/-- The cokernel of a map from a finite module to a coherent module is coherent. -/
theorem cokernel_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) where
  toFinite := inferInstance
  finitePresentation_submodule E hE := by
    let q : M →ₗ[R] M ⧸ LinearMap.range φ := Submodule.mkQ (LinearMap.range φ)
    let E' : Submodule R M := E.comap q
    let ι : LinearMap.range φ →ₗ[R] E' :=
      LinearMap.codRestrict E' (LinearMap.range φ).subtype fun x => by
        change q x.1 ∈ E
        have hx0 : q x.1 = 0 := by
          simpa [q, Submodule.Quotient.mk_eq_zero] using x.2
        simpa [hx0] using E.zero_mem
    let π : E' →ₗ[R] E :=
      LinearMap.codRestrict E (q.comp E'.subtype) fun x => x.2
    have hπ_surj : Function.Surjective π := by
      -- Surjectivity is by taking each element of `E` as its own lift in the pullback.
      intro y
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (LinearMap.range φ) y.1
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change q x ∈ E
        exact hx ▸ y.2
      apply Subtype.ext
      simpa [π, q, hx, LinearMap.comp_apply, LinearMap.codRestrict_apply]
    have hExact : Function.Exact ι π := by
      -- This is the pulled-back short exact sequence `0 → range φ → E' → E → 0`.
      rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        have hx' : π x = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have hx0q : (π x : M ⧸ LinearMap.range φ) = 0 := congrArg Subtype.val hx'
        have hx0 : q x.1 = 0 := by
          simpa [π, q, LinearMap.comp_apply, LinearMap.codRestrict_apply] using hx0q
        have hxrange : x.1 ∈ LinearMap.range φ := by
          simpa [q, Submodule.Quotient.mk_eq_zero] using hx0
        exact ⟨⟨x.1, hxrange⟩, Subtype.ext rfl⟩
      · intro hx
        rcases hx with ⟨y, hy⟩
        have hxy : x.1 = (ι y).1 := congrArg Subtype.val hy.symm
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        have hy0 : q y.1 = 0 := by
          simpa [q, Submodule.Quotient.mk_eq_zero] using y.2
        simpa [π, ι, q, LinearMap.comp_apply, LinearMap.codRestrict_apply, hxy]
          using hy0
    -- Exactness first shows the pullback is finite, so coherence of `M` upgrades it to finite
    -- presentation.
    letI : Module.Finite R E' := Module.Finite.of_exact hExact hπ_surj
    letI : Module.FinitePresentation R E' :=
      (inferInstance : Module.Coherent R M).finitePresentation_submodule E' inferInstance
    -- A finitely presented pullback and a finite kernel give finite presentation downstairs.
    exact Module.finitePresentation_of_surjective_of_exact ι π hπ_surj hExact

-- Proof sketch: a coherent source is finite, so the preceding kernel-finiteness statement applies;
-- then the kernel is a finite submodule of the coherent source and hence coherent by the first
-- clause.
/-- The kernel of a morphism of coherent modules is coherent. -/
theorem ker_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N] [Module.Coherent R M] :
    Module.Coherent R (LinearMap.ker φ) := by
  letI : Module.Finite R (LinearMap.ker φ) := ker_finite_of_finite_of_coherent φ
  infer_instance

-- Proof sketch: a coherent source is finite, so the previous cokernel statement applies directly
-- to the map `φ`.
/-- The cokernel of a morphism of coherent modules is coherent. -/
theorem cokernel_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) :=
  cokernel_coherent_of_finite_of_coherent φ

end

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: first identify the source with the range of `S.f`, then use exactness to replace
-- that range by the kernel of `S.g`.
/-- Helper for Lemma 10.90.3: in a short exact sequence, the left term identifies with the kernel
of the right map. -/
noncomputable def source_equiv_ker_of_shortExact (hS : S.ShortExact) :
    S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom :=
  (LinearEquiv.ofInjective S.f.hom hS.moduleCat_injective_f).trans
    (LinearEquiv.ofEq _ _ hS.exact.moduleCat_range_eq_ker)

-- Proof sketch: rewrite the cokernel by exactness as a quotient by `ker S.g`, then use the
-- canonical quotient-by-kernel equivalence of the surjective map `S.g`.
/-- Helper for Lemma 10.90.3: in a short exact sequence, the quotient by the image of `S.f`
identifies with the target of `S.g`. -/
noncomputable def quotient_range_equiv_target_of_shortExact (hS : S.ShortExact) :
    (S.X₂ ⧸ LinearMap.range S.f.hom) ≃ₗ[R] S.X₃ :=
  (Submodule.quotEquivOfEq _ _ hS.exact.moduleCat_range_eq_ker).trans
    (LinearMap.quotKerEquivOfSurjective S.g.hom hS.moduleCat_surjective_g)

-- Proof sketch: for a finite submodule `P ≤ S.X₂`, take its image in `S.X₃` and its inverse image
-- in `S.X₁`; the resulting short exact sequence on submodules has coherent outer terms, so Lemma
-- `10.5.3` promotes finite generation of `P` to finite presentation.
/-- In a short exact sequence of `R`-modules, if the left and right terms are coherent, then the
middle term is coherent. -/
theorem coherent_X2_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₂ where
  toFinite := by
    -- The middle term is finite because both endpoints are coherent, hence finite.
    let hExact : Function.Exact S.f.hom S.g.hom :=
      (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    exact Module.Finite.of_exact hExact hS.moduleCat_surjective_g
  finitePresentation_submodule P hP := by
    let P₁ : Submodule R S.X₁ := P.comap S.f.hom
    let P₃ : Submodule R S.X₃ := P.map S.g.hom
    let fP : P₁ →ₗ[R] P :=
      LinearMap.codRestrict P (S.f.hom.comp P₁.subtype) fun x => x.2
    let gP : P →ₗ[R] P₃ :=
      LinearMap.codRestrict P₃ (S.g.hom.comp P.subtype) fun x =>
        ⟨x.1, x.2, rfl⟩
    have hfP : Function.Injective fP := by
      -- Injectivity comes from injectivity of the original left map.
      intro x y hxy
      apply Subtype.ext
      exact hS.moduleCat_injective_f (congrArg Subtype.val hxy)
    have hgP : Function.Surjective gP := by
      -- Surjectivity is the defining property of the mapped submodule `P₃`.
      intro z
      rcases z.2 with ⟨x, hx, hxg⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxg
    have hExactS : Function.Exact S.f.hom S.g.hom :=
      (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    have hExactP : Function.Exact fP gP := by
      -- Exactness is inherited by restricting the ambient short exact sequence to `P`.
      have hker_range : LinearMap.ker S.g.hom = LinearMap.range S.f.hom :=
        LinearMap.exact_iff.mp hExactS
      rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        have hx' : gP x = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have hx0 : S.g.hom x.1 = 0 := by
          simpa [gP, LinearMap.comp_apply, LinearMap.codRestrict_apply] using congrArg Subtype.val hx'
        have hxker : x.1 ∈ LinearMap.ker S.g.hom := by
          rw [LinearMap.mem_ker]
          exact hx0
        have hxrange : x.1 ∈ LinearMap.range S.f.hom := by
          exact hker_range ▸ hxker
        rw [LinearMap.mem_range] at hxrange
        rcases hxrange with ⟨y, hyEq⟩
        have hy : y ∈ P₁ := by
          change S.f.hom y ∈ P
          simpa [hyEq] using x.2
        refine ⟨⟨y, hy⟩, ?_⟩
        apply Subtype.ext
        simpa [fP, LinearMap.comp_apply, LinearMap.codRestrict_apply] using hyEq
      · intro hx
        rcases hx with ⟨y, hy⟩
        have hxy : x.1 = (fP y).1 := congrArg Subtype.val hy.symm
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        simp [fP, gP, S.moduleCat_zero_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply, hxy]
    letI : Module.Finite R P₃ := Module.Finite.of_surjective gP hgP
    letI : Module.FinitePresentation R P₃ :=
      (inferInstance : Module.Coherent R S.X₃).finitePresentation_submodule P₃ inferInstance
    letI : Module.Finite R P₁ := Module.Finite.of_exact_of_finitePresentation fP gP hfP hgP hExactP
    letI : Module.FinitePresentation R P₁ :=
      (inferInstance : Module.Coherent R S.X₁).finitePresentation_submodule P₁ inferInstance
    -- Apply Lemma `10.5.3` to the restricted exact sequence on the finite submodule `P`.
    exact Module.finitePresentation_of_exact fP gP hfP hgP hExactP

-- Proof sketch: identify `S.X₁` with the kernel of `S.g`; since `S.X₂` and `S.X₃` are coherent,
-- the kernel of the map `S.g` is coherent by the kernel statement above.
/-- In a short exact sequence of `R`-modules, if the middle and right terms are coherent, then the
left term is coherent. -/
theorem coherent_X1_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₂]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₁ := by
  -- Transport coherence from the kernel model back to the source object.
  let e : S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom := source_equiv_ker_of_shortExact hS
  letI : Module.Coherent R (LinearMap.ker S.g.hom) := ker_coherent_of_coherent S.g.hom
  exact coherent_of_linearEquiv e.symm

-- Proof sketch: identify `S.X₃` with the cokernel of `S.f`; since `S.X₁` and `S.X₂` are
-- coherent, the cokernel of `S.f` is coherent by the cokernel statement above.
/-- In a short exact sequence of `R`-modules, if the left and middle terms are coherent, then the
right term is coherent. -/
theorem coherent_X3_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₂] :
    Module.Coherent R S.X₃ := by
  -- Transport coherence from the cokernel model to the target object.
  let e : (S.X₂ ⧸ LinearMap.range S.f.hom) ≃ₗ[R] S.X₃ :=
    quotient_range_equiv_target_of_shortExact hS
  letI : Module.Coherent R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
    cokernel_coherent_of_coherent S.f.hom
  exact coherent_of_linearEquiv e

end

end CategoryTheory.ShortComplex

/-! ### Lemma_10_90_4 (from Chap10) -/
universe u v w

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Coherent R R]

omit [Module.Coherent R R] in
private theorem coherent_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [hM : Module.Coherent R M] :
    Module.Coherent R N where
  toFinite := Module.Finite.of_surjective e.toLinearMap e.surjective
  finitePresentation_submodule P hP := by
    let eP := (P.comap e.toLinearMap).equivMapOfInjective e.toLinearMap e.injective
    have hmap : (P.comap e.toLinearMap).map e.toLinearMap = P :=
      Submodule.map_comap_eq_of_surjective e.surjective P
    letI : Module.Finite R ((P.comap e.toLinearMap).map e.toLinearMap) := by
      rw [hmap]
      exact hP
    letI : Module.Finite R (P.comap e.toLinearMap) := Module.Finite.equiv eP.symm
    letI : Module.FinitePresentation R (P.comap e.toLinearMap) :=
      hM.finitePresentation_submodule (P.comap e.toLinearMap) inferInstance
    exact Module.FinitePresentation.of_equiv
      (eP.trans (LinearEquiv.ofEq _ _ hmap))

private theorem coherent_fin_zero : Module.Coherent R (Fin 0 → R) where
  toFinite := inferInstance
  finitePresentation_submodule P _ := by
    have hP : P = ⊤ := Subsingleton.elim _ _
    subst hP
    exact Module.FinitePresentation.of_equiv
      (Submodule.topEquiv : (⊤ : Submodule R (Fin 0 → R)) ≃ₗ[R] (Fin 0 → R)).symm

private theorem coherent_prod_left {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Coherent R N] :
    Module.Coherent R (R × N) where
  toFinite := inferInstance
  finitePresentation_submodule P hP := by
    let sndP : P →ₗ[R] N := (LinearMap.snd R R N).comp P.subtype
    let fstKer : LinearMap.ker sndP →ₗ[R] R :=
      (LinearMap.fst R R N).comp (P.subtype.comp (LinearMap.ker sndP).subtype)
    letI : Module.Finite R (LinearMap.range sndP) := Module.Finite.of_fg (Submodule.fg_range sndP)
    letI : Module.Coherent R (LinearMap.range sndP) := inferInstance
    have hExact : Function.Exact (LinearMap.ker sndP).subtype sndP.rangeRestrict := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    letI : Module.Finite R (LinearMap.ker sndP) :=
      Module.Finite.of_fg <|
        by
          simpa [LinearMap.ker_rangeRestrict] using
            (Module.FinitePresentation.fg_ker sndP.rangeRestrict sndP.surjective_rangeRestrict)
    have hfstKer : Function.Injective fstKer := by
      intro x y hxy
      apply Subtype.ext
      apply P.subtype_injective
      ext
      · simpa [fstKer] using hxy
      ·
        have hx0' : (LinearMap.snd R R N) (P.subtype x.1) = 0 := by
          change sndP x.1 = 0
          exact x.2
        have hy0' : (LinearMap.snd R R N) (P.subtype y.1) = 0 := by
          change sndP y.1 = 0
          exact y.2
        simpa using hx0'.trans hy0'.symm
    let eKer := LinearEquiv.ofInjective fstKer hfstKer
    letI : Module.Finite R (LinearMap.range fstKer) :=
      Module.Finite.of_fg (Submodule.fg_range fstKer)
    letI : Module.Coherent R (LinearMap.range fstKer) := inferInstance
    letI : Module.FinitePresentation R (LinearMap.ker sndP) :=
      by
        letI : Module.FinitePresentation R (LinearMap.range fstKer) := inferInstance
        let eKer' : LinearMap.range fstKer ≃ₗ[R] LinearMap.ker sndP := eKer.symm
        let f : LinearMap.range fstKer →ₗ[R] LinearMap.ker sndP := eKer'.toLinearMap
        have hf : Function.Surjective f := eKer'.surjective
        have hker : LinearMap.ker f = ⊥ := by
          rw [show f = eKer'.toLinearMap by rfl, LinearEquiv.ker]
        show Module.FinitePresentation R (LinearMap.ker sndP)
        exact @Module.finitePresentation_of_surjective R (LinearMap.range fstKer)
          (LinearMap.ker sndP) _ _ _ _ _ inferInstance f hf <| by
          show (LinearMap.ker f).FG
          simpa [hker] using (Submodule.fg_bot : (⊥ : Submodule R (LinearMap.range fstKer)).FG)
    letI : Module.FinitePresentation R (LinearMap.ker sndP.rangeRestrict) := by
      rw [LinearMap.ker_rangeRestrict]
      infer_instance
    exact Module.finitePresentation_of_ker sndP.rangeRestrict sndP.surjective_rangeRestrict

private theorem coherent_fin : ∀ n : ℕ, Module.Coherent R (Fin n → R)
  | 0 => by
      exact coherent_fin_zero
  | n + 1 => by
      letI : Module.Coherent R (Fin n → R) := coherent_fin n
      letI : Module.Coherent R (R × (Fin n → R)) := coherent_prod_left
      let e₁ : (Fin (n + 1) → R) ≃ₗ[R] Option (Fin n) → R :=
        LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) ↦ R) (finSuccEquiv n)
      let e₂ : (Option (Fin n) → R) ≃ₗ[R] R × (Fin n → R) :=
        LinearEquiv.piOptionEquivProd R
      exact coherent_of_equiv (e₁ ≪≫ₗ e₂).symm

private theorem coherent_finite_free {ι : Type*} [Finite ι] :
    Module.Coherent R (ι → R) := by
  classical
  cases nonempty_fintype ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  letI : Module.Coherent R (Fin (Fintype.card ι) → R) := coherent_fin (Fintype.card ι)
  exact coherent_of_equiv
    (LinearEquiv.piCongrLeft R (fun _ : Fin (Fintype.card ι) ↦ R) e).symm

-- Proof sketch: one direction is Lemma `10.90.3`, which makes every coherent module finitely
-- presented. For the converse, choose a finite presentation of `M` as a cokernel of a map
-- `R^m → R^n`; the free modules `R^m` and `R^n` are coherent because `R` is coherent, and then
-- Lemma `10.90.3` shows the cokernel is coherent.
/-- Lemma 10.90.4: over a coherent ring, an `R`-module is coherent if and only if it is finitely
presented. -/
lemma module_coherent_iff_finitePresentation :
    Module.Coherent R M ↔ Module.FinitePresentation R M := by
  constructor
  · intro
    infer_instance
  · intro hM
    letI : Module.FinitePresentation R M := hM
    obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
    letI : Module.Finite R K := Module.Finite.of_fg hK
    letI : Module.Coherent R (Fin n → R) := coherent_finite_free
    letI : Module.Coherent R K := inferInstance
    letI : Module.Coherent R ((Fin n → R) ⧸ K.subtype.range) :=
      cokernel_coherent_of_coherent K.subtype
    letI : Module.Coherent R ((Fin n → R) ⧸ K) :=
      coherent_of_equiv (Submodule.quotEquivOfEq K.subtype.range K (Submodule.range_subtype K))
    exact coherent_of_equiv e.symm

end

/-! ### Lemma_10_90_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

variable [IsNoetherianRing R]

-- Proof sketch: by Lemma 10.31.4, every finite `R`-module over a Noetherian ring is finitely
-- presented; apply this to any finite ideal `I` of `R`.
/-- Lemma 10.90.5: a Noetherian ring is a coherent ring. -/
instance noetherianRing_isCoherentRing : IsCoherentRing R where
  toCoherent :=
    { toFinite := inferInstance
      finitePresentation_submodule := fun I _ ↦ Module.finitePresentation_of_finite R I }

end

/-! ### Proposition_10_90_6 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]

open scoped TensorProduct

/- Domain triage: this proposition relates coherence of a commutative ring to flatness of
arbitrary products.
- `source-facing`: the TFAE comparing the Stacks ideal-theoretic coherence condition with flatness
  of products.
- `core/canonical`: the chapter owner predicate `IsCoherentRing R`.
- `bridge/view`: the textbook clause "every finitely generated ideal is finitely presented" is a
  source-facing reformulation of `IsCoherentRing R`, not a separate owner abstraction.
Primitive data are only the ring and the chosen family of modules; finite presentation of ideals is
derived API of the owner predicate. -/

-- Proof sketch: `(1) → (2)` uses the ideal-theoretic flatness criterion from Lemma `10.39.5`.
-- For a finitely generated ideal `I`, coherence gives finite presentation, so Proposition
-- `10.89.3` identifies `I ⊗[R] ∏ Mₐ` with `∏ (I ⊗[R] Mₐ)`, and injectivity follows
-- componentwise from the flatness of each factor. `(2) → (3)` is the specialization to the
-- constant family with each factor equal to `R`. For `(3) → (1)`, Proposition `10.89.2`
-- identifies the image of `I ⊗[R] R^A → R^A` with `I^A`, and Proposition `10.89.3` then forces
-- each finitely generated ideal `I` to be finitely presented, i.e. the canonical owner predicate
-- `IsCoherentRing R` holds.
/-- Helper for Proposition 10.90.6: the flatness test map into a product is the canonical
comparison map `TensorProduct.piRightHom` followed by the coordinatewise flatness test maps. -/
lemma ideal_lift_pi_eq_pi_comp_piRightHom {A : Type (max u v)}
    {M : A → Type (max u w)} [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)] (I : Ideal R) :
    TensorProduct.lift ((LinearMap.lsmul R (∀ a, M a)).comp I.subtype) =
      (LinearMap.piMap fun a ↦ TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) ∘ₗ
        TensorProduct.piRightHom R R I M := by
  -- Compute both linear maps on pure tensors; they agree coordinatewise.
  ext x f a
  simp [TensorProduct.piRightHom_tmul]

/-- Helper for Proposition 10.90.6: if a finitely generated ideal `I` is finitely presented, then
the ideal-test map into a product of flat modules is injective. -/
lemma ideal_lift_pi_injective_of_finitePresentation {A : Type (max u v)}
    {M : A → Type (max u w)} [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)] (I : Ideal R)
    (hIfg : I.FG) (hI : Module.FinitePresentation R I) (hM : ∀ a, Module.Flat R (M a)) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R (∀ a, M a)).comp I.subtype)) := by
  letI : Module.FinitePresentation R I := hI
  have hpi :
      Function.Bijective (TensorProduct.piRightHom R R I M) := by
    have hiff :
        Module.FinitePresentation R I ↔
          ∀ (B : Type (max u v)) (Q : B → Type (max u w))
            [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)],
            Function.Bijective (TensorProduct.piRightHom R R I Q) :=
      show
        Module.FinitePresentation R I ↔
          ∀ (B : Type (max u v)) (Q : B → Type (max u w))
            [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)],
            Function.Bijective (TensorProduct.piRightHom R R I Q)
      from
        module_finitePresentation_tfae_tensorProduct_pi_bijective.{u, u, v, w}
          (R := R) (M := I) |>.out 0 1
    exact hiff.1 hI A M
  have hcoord :
      Function.Injective
        (LinearMap.piMap fun a ↦
          TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) := by
    -- Each coordinate is injective by the flatness criterion on the same finitely generated ideal.
    intro t₁ t₂ hEq
    ext a
    have ha :
        Function.Injective
          (TensorProduct.lift ((LinearMap.lsmul R (M a)).comp I.subtype)) := by
      exact (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hM a)) (I := I) hIfg
    exact ha (congrFun hEq a)
  -- Rewrite the product map through `piRightHom` and combine the injective factors.
  rw [ideal_lift_pi_eq_pi_comp_piRightHom (R := R) (M := M) I]
  exact hcoord.comp hpi.1

/-- Helper for Proposition 10.90.6: the flatness test map into `R^A` factors through the scalar
comparison map `TensorProduct.piScalarRightHom`. -/
lemma ideal_lift_scalar_eq_pi_subtype_comp_piScalarRightHom (I : Ideal R)
    (A : Type (max u v)) :
    TensorProduct.lift ((LinearMap.lsmul R (A → R)).comp I.subtype) =
      (LinearMap.piMap fun _ : A ↦ I.subtype) ∘ₗ TensorProduct.piScalarRightHom R R I A := by
  -- On pure tensors the scalar comparison map records the pointwise scalar multiples in `I`.
  ext x f a
  simp [TensorProduct.piScalarRightHom_tmul, mul_comm]

/-- Helper for Proposition 10.90.6: if every scalar product `R^A` is flat, then every finitely
generated ideal of `R` is finitely presented. -/
lemma finitePresentation_of_fg_ideal_of_flat_scalar_pi (I : Ideal R) (hIfg : I.FG)
    (hflat : ∀ A : Type (max u v), Module.Flat R (A → R)) :
    Module.FinitePresentation R I := by
  letI : Module.Finite R I := Module.Finite.of_fg hIfg
  have hsurj :
      ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A) := by
    have hiff :
        Module.Finite R I ↔
          ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A) :=
      show
        Module.Finite R I ↔
          ∀ A : Type (max u v), Function.Surjective (TensorProduct.piScalarRightHom R R I A)
      from
        module_finite_tfae_tensorProduct_pi_surjective.{u, u, v, v}
          (R := R) (M := I) |>.out 0 3
    exact hiff.1 inferInstance
  have hbij :
      ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A) := by
    intro A
    have hlift :
        Function.Injective
          (TensorProduct.lift ((LinearMap.lsmul R (A → R)).comp I.subtype)) := by
      exact (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hflat A)) (I := I) hIfg
    have hpi :
        Function.Injective
          ((LinearMap.piMap fun _ : A ↦ I.subtype) ∘ TensorProduct.piScalarRightHom R R I A) := by
      simpa [LinearMap.comp_apply,
        ideal_lift_scalar_eq_pi_subtype_comp_piScalarRightHom (R := R) I A] using hlift
    have hinj :
        Function.Injective (TensorProduct.piScalarRightHom R R I A) := hpi.of_comp
    exact ⟨hinj, hsurj A⟩
  -- Proposition `10.89.3` converts bijectivity of the scalar comparison maps into finite
  -- presentation of `I`.
  have hiff :
      Module.FinitePresentation R I ↔
        ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A) :=
    show
      Module.FinitePresentation R I ↔
        ∀ A : Type (max u v), Function.Bijective (TensorProduct.piScalarRightHom R R I A)
    from
      module_finitePresentation_tfae_tensorProduct_pi_bijective.{u, u, v, v}
        (R := R) (M := I) |>.out 0 3
  exact hiff.2 hbij

/-- Proposition 10.90.6: the following are equivalent for a commutative ring `R`: `R` is coherent
(expressed by the owner predicate `IsCoherentRing R`), arbitrary products of flat `R`-modules are
flat, and for every set `A` the product module `A → R` is flat. -/
theorem coherent_tfae_flat_products :
    List.TFAE
      [ IsCoherentRing R,
        ∀ (A : Type (max u v)) (M : A → Type (max u w))
          [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)],
          (∀ a, Module.Flat R (M a)) → Module.Flat R (∀ a, M a),
        ∀ A : Type (max u v), Module.Flat R (A → R) ] := by
  -- Route correction: enlarge the quantified index universe so the reverse implication can test
  -- clause `(3)` on arbitrary ideal-indexed products, exactly as in the source proof.
  tfae_have 1 → 2 := by
    intro hcoh A M _ _ hM
    -- Follow Lemma `10.39.5`: test flatness of the product on finitely generated ideals.
    rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hIfg
    -- Coherence makes every finitely generated ideal finitely presented.
    have hI : Module.FinitePresentation R I := by
      exact hcoh.finitePresentation_submodule I (Module.Finite.of_fg hIfg)
    -- Proposition `10.89.3` identifies the tensor with the product of the tensors.
    exact ideal_lift_pi_injective_of_finitePresentation (R := R) (M := M) I hIfg hI hM
  tfae_have 2 → 3 := by
    intro h A
    -- Specialize to the constant family `ULift R` and transport flatness back along the product
    -- equivalence with `A → R`.
    have hULift : Module.Flat R (A → ULift.{max u w} R) := by
      simpa using
        h A (fun _ : A ↦ ULift.{max u w} R)
          (fun _ ↦ (inferInstance : Module.Flat R (ULift.{max u w} R)))
    exact Module.Flat.of_linearEquiv
      (LinearEquiv.piCongrRight fun _ : A ↦ ULift.moduleEquiv.symm)
  tfae_have 3 → 1 := by
    intro hflat
    refine
      { toCoherent :=
          { toFinite := inferInstance
            finitePresentation_submodule := ?_ } }
    intro I hI
    -- Convert finite generation of the ideal into finite presentation via the scalar products.
    exact finitePresentation_of_fg_ideal_of_flat_scalar_pi (R := R) I Submodule.FG.of_finite hflat
  tfae_finish

end
