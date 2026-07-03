import StacksProject_2024.Chap10.Definition_10_90_1
import StacksProject_2024.Chap10.Lemma_10_5_3

-- Declarations for this item will be appended below by the statement pipeline.

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
