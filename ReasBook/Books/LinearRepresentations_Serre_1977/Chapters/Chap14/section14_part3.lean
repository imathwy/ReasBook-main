import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_14_14_3_2 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w x y

section

variable {R : Type u} [Ring R]

/-- Helper for Corollary 14-14.3-2: a simple product module forces one factor to be
subsingleton. -/
private theorem simple_prod_right_or_left_subsingleton
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (h : IsSimpleModule R (M × N)) : Subsingleton M ∨ Subsingleton N := by
  classical
  by_contra hcontra
  have hM : Nontrivial M := (not_subsingleton_iff_nontrivial).mp (by
    intro hSub
    exact hcontra (Or.inl hSub))
  have hN : Nontrivial N := (not_subsingleton_iff_nontrivial).mp (by
    intro hSub
    exact hcontra (Or.inr hSub))
  let S : Submodule R (M × N) := (⊤ : Submodule R M).prod (⊥ : Submodule R N)
  have hSbot : S ≠ ⊥ := by
    -- The left-axis submodule is nonzero because the left factor is nontrivial.
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    intro hEq
    have hmS : (m, 0) ∈ S := by
      simp [S]
    have hmBot : (m, 0) ∈ (⊥ : Submodule R (M × N)) := hEq ▸ hmS
    exact hm (by simpa using hmBot)
  have hStop : S ≠ ⊤ := by
    -- The same submodule is proper because it misses a nonzero vector in the right factor.
    obtain ⟨n, hn⟩ := exists_ne (0 : N)
    intro hEq
    have hnTop : (0, n) ∈ S := by
      simp [hEq]
    simp [S, hn] at hnTop
  have hSimpleOrder : IsSimpleOrder (Submodule R (M × N)) := (isSimpleModule_iff R (M × N)).mp h
  rcases hSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · exact hSbot hS
  · exact hStop hS

/-- Helper for Corollary 14-14.3-2: a simple largest semisimple quotient rules out any nontrivial
binary decomposition of the projective Artinian source. -/
private theorem simple_largestSemisimpleQuotient_implies_indecomposable
    {P : ModuleCat R} [Module.Projective R P] [IsArtinianRing R] [IsArtinian R P]
    (hSimple : IsSimpleModule R (P ⧸ Module.jacobson R P)) : Indecomposable P := by
  refine ⟨?_, ?_⟩
  · -- A zero source would force the quotient to be subsingleton, contradicting simplicity.
    intro hZero
    have hSub : Subsingleton P := (ModuleCat.isZero_iff_subsingleton).1 hZero
    letI : Subsingleton P := hSub
    have hQSub : Subsingleton (P ⧸ Module.jacobson R P) :=
      (Module.jacobson R P).mkQ_surjective.subsingleton
    letI : Subsingleton (P ⧸ Module.jacobson R P) := hQSub
    exact (not_nontrivial (P ⧸ Module.jacobson R P))
      (IsSimpleModule.nontrivial R (P ⧸ Module.jacobson R P))
  · intro Y Z e
    -- Transport a hypothetical biproduct decomposition of `P` to a product decomposition of its
    -- largest semisimple quotient, then use simplicity of that quotient.
    let iY : Y ⟶ P := biprod.inl ≫ e.inv
    let pY : P ⟶ Y := e.hom ≫ biprod.fst
    have hpYiY : pY.hom.comp iY.hom = LinearMap.id := by
      have hcat : iY ≫ pY = 𝟙 Y := by
        simp [iY, pY]
      ext y
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) y
    have hYproj : Module.Projective R Y := Module.Projective.of_split iY.hom pY.hom hpYiY
    have hpYsurj : Function.Surjective pY.hom := by
      intro y
      exact ⟨iY.hom y, LinearMap.congr_fun hpYiY y⟩
    have hYart : IsArtinian R Y := isArtinian_of_surjective _ pY.hom hpYsurj
    let iZ : Z ⟶ P := biprod.inr ≫ e.inv
    let pZ : P ⟶ Z := e.hom ≫ biprod.snd
    have hpZiZ : pZ.hom.comp iZ.hom = LinearMap.id := by
      have hcat : iZ ≫ pZ = 𝟙 Z := by
        simp [iZ, pZ]
      ext z
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) z
    have hZproj : Module.Projective R Z := Module.Projective.of_split iZ.hom pZ.hom hpZiZ
    have hpZsurj : Function.Surjective pZ.hom := by
      intro z
      exact ⟨iZ.hom z, LinearMap.congr_fun hpZiZ z⟩
    have hZart : IsArtinian R Z := isArtinian_of_surjective _ pZ.hom hpZsurj
    let eProd : P ≃ₗ[R] (Y × Z) := (e ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
    have hQuotIso : Nonempty ((P ⧸ Module.jacobson R P) ≃ₗ[R]
        ((Y × Z) ⧸ Module.jacobson R (Y × Z))) := by
      refine ⟨Submodule.Quotient.equiv (Module.jacobson R P)
        (Module.jacobson R (Y × Z)) eProd ?_⟩
      have hmapJac :
          Submodule.map eProd.toLinearMap (Module.jacobson R P) =
            Module.jacobson R (Y × Z) :=
        Module.map_jacobson_of_bijective eProd.bijective
      simpa [eProd] using hmapJac
    obtain ⟨eQuot⟩ := hQuotIso
    have hSemiprod :
        Nonempty (((Y × Z) ⧸ Module.jacobson R (Y × Z)) ≃ₗ[R]
          (Y ⧸ Module.jacobson R Y) × (Z ⧸ Module.jacobson R Z)) :=
      largestSemisimpleQuotient_prod_linearEquiv
    obtain ⟨eSemiprod⟩ := hSemiprod
    have hSimpleFactors :
        IsSimpleModule R ((Y ⧸ Module.jacobson R Y) × (Z ⧸ Module.jacobson R Z)) := by
      exact IsSimpleModule.congr (eSemiprod.symm.trans eQuot.symm)
    rcases simple_prod_right_or_left_subsingleton hSimpleFactors with hYsub | hZsub
    · left
      letI : Subsingleton (Y ⧸ Module.jacobson R Y) := hYsub
      have hqY :
          ((Module.jacobson R Y).mkQ : Y →ₗ[R] Y ⧸ Module.jacobson R Y).IsProjectiveEnvelope := by
        simpa using
          (show ((Module.jacobson R Y).mkQ : Y →ₗ[R] Y ⧸ Module.jacobson R Y).IsProjectiveEnvelope
            from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
      obtain ⟨eY⟩ := hqY.nonempty_linearEquiv_target
      exact (ModuleCat.isZero_iff_subsingleton).2 eY.injective.subsingleton
    · right
      letI : Subsingleton (Z ⧸ Module.jacobson R Z) := hZsub
      have hqZ :
          ((Module.jacobson R Z).mkQ : Z →ₗ[R] Z ⧸ Module.jacobson R Z).IsProjectiveEnvelope := by
        simpa using
          (show ((Module.jacobson R Z).mkQ : Z →ₗ[R] Z ⧸ Module.jacobson R Z).IsProjectiveEnvelope
            from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
      obtain ⟨eZ⟩ := hqZ.nonempty_linearEquiv_target
      exact (ModuleCat.isZero_iff_subsingleton).2 eZ.injective.subsingleton

/-- Helper for Corollary 14-14.3-2: linear equivalences preserve indecomposability. -/
private theorem indecomposable_iff_linearEquiv
    {P Q : ModuleCat.{v} R} (e : P ≃ₗ[R] Q) :
    Indecomposable P ↔ Indecomposable Q := by
  constructor
  · intro hP
    refine ⟨?_, ?_⟩
    · -- Zero objects are preserved by isomorphism, so the nonzero condition transports.
      intro hQzero
      exact hP.1 (IsZero.of_iso hQzero e.toModuleIso)
    · intro Y Z i
      -- Pull the decomposition of `Q` back across `e`.
      exact hP.2 Y Z (e.toModuleIso ≪≫ i)
  · intro hQ
    refine ⟨?_, ?_⟩
    · -- Zero objects are preserved by isomorphism in the opposite direction as well.
      intro hPzero
      exact hQ.1 (IsZero.of_iso hPzero e.toModuleIso.symm)
    · intro Y Z i
      -- Push the decomposition of `P` forward across `e`.
      exact hQ.2 Y Z (e.toModuleIso.symm ≪≫ i)

/-- Helper for Corollary 14-14.3-2: a semisimple indecomposable module is simple. -/
private theorem isSimpleModule_of_isSemisimple_of_indecomposable
    {M : ModuleCat.{v} R} [IsSemisimpleModule R M] (hM : Indecomposable M) :
    IsSimpleModule R M := by
  classical
  have hM_nontrivial : Nontrivial M := by
    -- An indecomposable object is nonzero, hence its carrier cannot be subsingleton.
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hSub
    exact hM.1 ((ModuleCat.isZero_iff_subsingleton).2 hSub)
  letI : Nontrivial M := hM_nontrivial
  by_contra hNotSimple
  have hExists :
      ∃ S : Submodule R M, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra hNo
    have hAll : ∀ S : Submodule R M, S = ⊥ ∨ S = ⊤ := by
      intro S
      by_cases hSbot : S = ⊥
      · exact Or.inl hSbot
      · by_cases hStop : S = ⊤
        · exact Or.inr hStop
        · exact False.elim (hNo ⟨S, hSbot, hStop⟩)
    have hSimple : IsSimpleModule R M := by
      exact (isSimpleModule_iff R M).2
        { toNontrivial := inferInstance, eq_bot_or_eq_top := hAll }
    exact hNotSimple hSimple
  rcases hExists with ⟨S, hSbot, hStop⟩
  obtain ⟨T, hCompl⟩ := exists_isCompl S
  have hTbot : T ≠ ⊥ := by
    -- If the complement vanished, the chosen submodule would already be the whole space.
    intro hT
    apply hStop
    simpa [hT] using hCompl.sup_eq_top
  let eProd : M ≃ₗ[R] S × T := (S.prodEquivOfIsCompl T hCompl).symm
  have hDecomp :
      M ≅ (ModuleCat.of R S) ⊞ (ModuleCat.of R T) := by
    -- Translate the internal direct-sum decomposition into the categorical biproduct form.
    exact eProd.toModuleIso ≪≫ (ModuleCat.biprodIsoProd (ModuleCat.of R S) (ModuleCat.of R T)).symm
  rcases hM.2 (ModuleCat.of R S) (ModuleCat.of R T) hDecomp with hSzero | hTzero
  · have hSsub : Subsingleton S := (ModuleCat.isZero_iff_subsingleton).1 hSzero
    have hSnontrivial : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hSbot
    exact not_nontrivial S hSnontrivial
  · have hTsub : Subsingleton T := (ModuleCat.isZero_iff_subsingleton).1 hTzero
    have hTnontrivial : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hTbot
    exact not_nontrivial T hTnontrivial

/-- Helper for Corollary 14-14.3-2: the source of a projective envelope of a simple module is
indecomposable. -/
private theorem indecomposable_of_projectiveEnvelope_simple_target
    {P S : ModuleCat.{v} R} {f : P ⟶ S} (hf : f.hom.IsProjectiveEnvelope)
    [IsSimpleModule R S] :
    Indecomposable P := by
  refine ⟨?_, ?_⟩
  · -- A zero source would force the simple target to be subsingleton.
    intro hPzero
    have hPsub : Subsingleton P := (ModuleCat.isZero_iff_subsingleton).1 hPzero
    letI : Subsingleton P := hPsub
    have hSsub : Subsingleton S := hf.surjective.subsingleton
    letI : Subsingleton S := hSsub
    exact (not_nontrivial S) (IsSimpleModule.nontrivial R S)
  · intro Y Z e
    -- Route correction: work directly with the essential map to the simple target, rather than
    -- first passing through the Jacobson quotient of `P`.
    let eProd : P ≃ₗ[R] (Y × Z) := (e ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
    let g : Y × Z →ₗ[R] S := f.hom.comp eProd.symm.toLinearMap
    have hg : g.IsEssential := by
      simpa [g, eProd] using
        (LinearMap.isEssential_iff_conj eProd (LinearEquiv.refl R S)).2
          hf.toIsEssential
    have hgsurj : Function.Surjective g := by
      intro s
      rcases hf.surjective s with ⟨p, hp⟩
      exact ⟨eProd p, by simpa [g] using hp⟩
    have hcoprod :
        LinearMap.coprod (g.comp (LinearMap.inl R Y Z)) (g.comp (LinearMap.inr R Y Z)) = g := by
      ext yz <;> simp [g]
    have hRangeTop : LinearMap.range g = ⊤ := LinearMap.range_eq_top.2 hgsurj
    have hLeftSimple : LinearMap.range (g.comp (LinearMap.inl R Y Z)) = ⊥ ∨
        LinearMap.range (g.comp (LinearMap.inl R Y Z)) = ⊤ := by
      exact (isSimpleModule_iff R S).1 inferInstance |>.eq_bot_or_eq_top _
    rcases hLeftSimple with hLeftBot | hLeftTop
    · left
      have hRangeRight : LinearMap.range (g.comp (LinearMap.inr R Y Z)) = ⊤ := by
        rw [← hcoprod, LinearMap.range_coprod, hLeftBot, bot_sup_eq] at hRangeTop
        exact hRangeTop
      have hAxisTop :
          ((⊥ : Submodule R Y).prod (⊤ : Submodule R Z)).map g = ⊤ := by
        calc
          ((⊥ : Submodule R Y).prod (⊤ : Submodule R Z)).map g
              = ((⊥ : Submodule R Y).map (g.comp (LinearMap.inl R Y Z))) ⊔
                  ((⊤ : Submodule R Z).map (g.comp (LinearMap.inr R Y Z))) := by
                rw [← hcoprod]
                rw [LinearMap.map_coprod_prod]
                simp
          _ = LinearMap.range (g.comp (LinearMap.inr R Y Z)) := by
                rw [Submodule.map_bot, bot_sup_eq, LinearMap.range_eq_map]
          _ = ⊤ := hRangeRight
      have hAxisEqTop : ((⊥ : Submodule R Y).prod (⊤ : Submodule R Z)) = ⊤ :=
        hg.eq_top_of_map_eq_top _ hAxisTop
      have hYsub : Subsingleton Y := by
        refine ⟨fun y y' ↦ ?_⟩
        have hy : (y - y', 0) ∈ ((⊥ : Submodule R Y).prod (⊤ : Submodule R Z)) := by
          simp [hAxisEqTop]
        exact sub_eq_zero.mp (by simpa using hy.1)
      exact (ModuleCat.isZero_iff_subsingleton).2 hYsub
    · right
      have hAxisTop :
          ((⊤ : Submodule R Y).prod (⊥ : Submodule R Z)).map g = ⊤ := by
        calc
          ((⊤ : Submodule R Y).prod (⊥ : Submodule R Z)).map g
              = ((⊤ : Submodule R Y).map (g.comp (LinearMap.inl R Y Z))) ⊔
                  ((⊥ : Submodule R Z).map (g.comp (LinearMap.inr R Y Z))) := by
                rw [← hcoprod]
                rw [LinearMap.map_coprod_prod]
                simp
          _ = LinearMap.range (g.comp (LinearMap.inl R Y Z)) := by
                rw [Submodule.map_bot, sup_bot_eq, LinearMap.range_eq_map]
          _ = ⊤ := hLeftTop
      have hAxisEqTop : ((⊤ : Submodule R Y).prod (⊥ : Submodule R Z)) = ⊤ :=
        hg.eq_top_of_map_eq_top _ hAxisTop
      have hZsub : Subsingleton Z := by
        refine ⟨fun z z' ↦ ?_⟩
        have hz : (0, z - z') ∈ ((⊤ : Submodule R Y).prod (⊥ : Submodule R Z)) := by
          simp [hAxisEqTop]
        exact sub_eq_zero.mp (by simpa using hz.2)
      exact (ModuleCat.isZero_iff_subsingleton).2 hZsub

section FiniteProjectiveGroupAlgebra

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
local notation "kG" => MonoidAlgebra k G
variable {M : ModuleCat (MonoidAlgebra k G)}
variable [Module.Finite (MonoidAlgebra k G) M] [Module.Projective (MonoidAlgebra k G) M]

-- Source-faithful public surface: LinearRepresentations_Serre_1977 states this corollary for finite projective `k[G]`-modules.
/-- Corollary 14-14.3-2 (1): every finite projective `k[G]`-module is isomorphic to a finite
direct sum of finite projective indecomposable `k[G]`-modules, realized here as a finite biproduct
in `ModuleCat`. -/
theorem finite_projective_module_exists_indecomposable_decomposition
    :
    ∃ (ι : Type w) (_ : Finite ι) (P : ι → ModuleCat kG) (_ : M ≅ ⨁ P),
      ∀ i, Module.Finite kG (P i) ∧ Module.Projective kG (P i) ∧ Indecomposable (P i) := by
  classical
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  let Q : ModuleCat kG := ModuleCat.of kG (M ⧸ Module.jacobson kG M)
  let q : M →ₗ[kG] Q := (Module.jacobson kG M).mkQ
  have hQsemisimple : IsSemisimpleModule kG Q := by
    -- The canonical Jacobson quotient is semisimple for finite `k[G]`-modules.
    simpa [Q] using
      (show IsSemisimpleModule kG (M ⧸ Module.jacobson kG M)
        from largestSemisimpleQuotient_isSemisimple)
  letI : IsSemisimpleModule kG Q := hQsemisimple
  have hQfinite : Module.Finite kG Q := by
    infer_instance
  obtain ⟨n, S, eQ, hSsimple⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp kG Q
  choose E f hf using
    fun i : Fin n ↦ exists_isProjectiveEnvelope (ModuleCat.of kG (S i))
  let g₀ : (Π₀ i : Fin n, E i) →ₗ[kG] (Π₀ i : Fin n, S i) :=
    DirectSum.lmap fun i ↦ (f i).hom
  have hg₀ : g₀.IsProjectiveEnvelope := by
    -- Assemble the chosen projective envelopes of the simple quotient summands.
    simpa [g₀] using DirectSum.lmap_isProjectiveEnvelope (fun i ↦ (f i).hom) hf
  let g : (Π₀ i : Fin n, E i) →ₗ[kG] Q := eQ.symm.toLinearMap ∘ₗ g₀
  have hg : g.IsProjectiveEnvelope := by
      -- Conjugate the direct-sum envelope along the quotient decomposition.
    simpa [g, g₀] using
      (LinearMap.isProjectiveEnvelope_iff_conj
        (LinearEquiv.refl kG (Π₀ i : Fin n, E i)) eQ.symm).2 hg₀
  have hq : q.IsProjectiveEnvelope := by
    -- The canonical Jacobson-quotient map of the projective source is the reference envelope.
    simpa [q, Q] using
      (show ((Module.jacobson kG M).mkQ : M →ₗ[kG] M ⧸ Module.jacobson kG M).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hq hg
  let eBiprod : M ≅ ⨁ E :=
    (eSrc.trans DFinsupp.linearEquivFunOnFintype).toModuleIso ≪≫ (ModuleCat.biproductIsoPi E).symm
  let ι : Type w := ULift (Fin n)
  let P : ι → ModuleCat kG := fun i ↦ E i.down
  let eReindex : (⨁ E) ≅ ⨁ P :=
    biproduct.whiskerEquiv Equiv.ulift.symm (fun i ↦ by simpa [P] using Iso.refl (E i))
  refine ⟨ι, inferInstance, P, eBiprod ≪≫ eReindex, ?_⟩
  intro i
  have hsumFinite : Module.Finite kG (Π₀ j : Fin n, E j) :=
    Module.Finite.of_surjective eSrc.toLinearMap eSrc.surjective
  have hPiFinite : Module.Finite kG (P i) := by
    -- Each summand injects into the finite direct sum via its singleton inclusion.
    have hPiFinite' : Module.Finite kG (E i.down) := by
      let l : E i.down →ₗ[kG] (Π₀ j : Fin n, E j) :=
        DirectSum.lof kG (Fin n) (fun j ↦ E j) i.down
      refine Module.Finite.of_injective l ?_
      intro x y hxy
      have hxy' := congrArg (DirectSum.component kG (Fin n) (fun j ↦ E j) i.down) hxy
      have hx : DirectSum.component kG (Fin n) (fun j ↦ E j) i.down (l x) = x := by
        change (DFinsupp.single i.down x : Π₀ j : Fin n, E j) i.down = x
        exact DFinsupp.single_eq_same
      have hy : DirectSum.component kG (Fin n) (fun j ↦ E j) i.down (l y) = y := by
        change (DFinsupp.single i.down y : Π₀ j : Fin n, E j) i.down = y
        exact DFinsupp.single_eq_same
      calc
        x = DirectSum.component kG (Fin n) (fun j ↦ E j) i.down (l x) := hx.symm
        _ = DirectSum.component kG (Fin n) (fun j ↦ E j) i.down (l y) := hxy'
        _ = y := hy
    simpa [P] using hPiFinite'
  have hPiProjective : Module.Projective kG (P i) := by
    -- Projectivity is part of the chosen projective-envelope structure.
    letI : (f i.down).hom.IsProjectiveEnvelope := hf i.down
    infer_instance
  have hSimpleTarget : IsSimpleModule kG (ModuleCat.of kG (S i.down)) := by
    simpa using hSsimple i.down
  have hPiIndecomp : Indecomposable (P i) := by
    -- A projective envelope of a simple target has indecomposable source.
    let fi : E i.down ⟶ ModuleCat.of kG (S i.down) := f i.down
    have hfi : fi.hom.IsProjectiveEnvelope := hf i.down
    simpa [P] using
      indecomposable_of_projectiveEnvelope_simple_target hfi
  exact ⟨hPiFinite, hPiProjective, hPiIndecomp⟩

/-- Helper for Corollary 14-14.3-2: every summand in a finite biproduct decomposition of a finite
projective `k[G]`-module is again finite and projective. -/
private theorem finite_projective_of_biproduct_summand
    {ι : Type w} [Finite ι] {P : ι → ModuleCat kG} (e : M ≅ ⨁ P) (i : ι) :
    Module.Finite kG (P i) ∧ Module.Projective kG (P i) := by
  let iP : P i ⟶ M := biproduct.ι P i ≫ e.inv
  let pP : M ⟶ P i := e.hom ≫ biproduct.π P i
  have hpPiP : pP.hom.comp iP.hom = LinearMap.id := by
    -- The biproduct projection splits the inclusion of the chosen summand.
    have hcat : iP ≫ pP = 𝟙 (P i) := by
      simp [iP, pP]
    ext x
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcat) x
  have hpPsurj : Function.Surjective pP.hom := by
    -- A split epimorphism from the finite module `M` preserves finite generation.
    intro y
    exact ⟨iP.hom y, LinearMap.congr_fun hpPiP y⟩
  have hPiFinite : Module.Finite kG (P i) := Module.Finite.of_surjective pP.hom hpPsurj
  have hPiProjective : Module.Projective kG (P i) :=
    Module.Projective.of_split iP.hom pP.hom hpPiP
  exact ⟨hPiFinite, hPiProjective⟩

/-- Helper for Corollary 14-14.3-2: an indecomposable finite projective `k[G]`-module has simple
largest semisimple quotient. -/
private theorem largestSemisimpleQuotient_isSimple_of_indecomposable
    {P : ModuleCat kG} [Module.Finite kG P] [Module.Projective kG P]
    (hP : Indecomposable P) :
    IsSimpleModule kG (P ⧸ Module.jacobson kG P) := by
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  let _ : IsArtinian kG P := by
    infer_instance
  let Q : ModuleCat kG := ModuleCat.of kG (P ⧸ Module.jacobson kG P)
  have hQsemisimple : IsSemisimpleModule kG Q := by
    -- The Jacobson quotient is the common semisimple invariant attached to `P`.
    simpa [Q] using
      (show IsSemisimpleModule kG (P ⧸ Module.jacobson kG P)
        from largestSemisimpleQuotient_isSemisimple)
  let _ : IsSemisimpleModule kG Q := hQsemisimple
  let q : P →ₗ[kG] Q := (Module.jacobson kG P).mkQ
  have hq : q.IsProjectiveEnvelope := by
    -- The canonical Jacobson-quotient map is the reference projective envelope of `P`.
    simpa [q, Q] using
      (show ((Module.jacobson kG P).mkQ :
          P →ₗ[kG] P ⧸ Module.jacobson kG P).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  have hQnontrivial : Nontrivial Q := by
    -- If the quotient vanished, essentiality of `q` would already force `P` to vanish.
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hQsub
    letI : Subsingleton Q := hQsub
    have hbotmap : (⊥ : Submodule kG P).map q = ⊤ := by
      exact Subsingleton.elim _ _
    have hPbot : (⊥ : Submodule kG P) = ⊤ :=
      hq.toIsEssential.eq_top_of_map_eq_top _ hbotmap
    have hPsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      have hxy : x - y ∈ (⊥ : Submodule kG P) := by
        rw [hPbot]
        simp
      exact sub_eq_zero.mp (by simpa using hxy)
    exact hP.1 ((ModuleCat.isZero_iff_subsingleton).2 hPsub)
  let _ : Nontrivial Q := hQnontrivial
  by_contra hNotSimple
  have hExists :
      ∃ S : Submodule kG Q, S ≠ ⊥ ∧ S ≠ ⊤ := by
    -- Failure of simplicity gives a proper nonzero submodule in the semisimple quotient.
    by_contra hNo
    have hAll : ∀ S : Submodule kG Q, S = ⊥ ∨ S = ⊤ := by
      intro S
      by_cases hSbot : S = ⊥
      · exact Or.inl hSbot
      · by_cases hStop : S = ⊤
        · exact Or.inr hStop
        · exact False.elim (hNo ⟨S, hSbot, hStop⟩)
    have hSimple : IsSimpleModule kG Q := by
      exact (isSimpleModule_iff kG Q).2
        { toNontrivial := inferInstance, eq_bot_or_eq_top := hAll }
    exact hNotSimple hSimple
  rcases hExists with ⟨S, hSbot, hStop⟩
  obtain ⟨T, hCompl⟩ := exists_isCompl S
  have hTbot : T ≠ ⊥ := by
    -- A zero complement would make `S` equal to the whole semisimple quotient.
    intro hT
    have hsup : S ⊔ T = ⊤ := hCompl.sup_eq_top
    rw [hT, sup_bot_eq] at hsup
    exact hStop hsup
  have hSnontrivial : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hSbot
  have hTnontrivial : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hTbot
  let eProd : Q ≃ₗ[kG] S × T := (S.prodEquivOfIsCompl T hCompl).symm
  obtain ⟨ES, fS, hfS⟩ := exists_isProjectiveEnvelope (k := k) (G := G) (ModuleCat.of kG S)
  obtain ⟨ET, fT, hfT⟩ := exists_isProjectiveEnvelope (k := k) (G := G) (ModuleCat.of kG T)
  let gProd : ES × ET →ₗ[kG] S × T := fS.hom.prodMap fT.hom
  have hgProd : gProd.IsProjectiveEnvelope := by
    -- The two projective envelopes combine into a projective envelope of the product quotient.
    simpa [gProd] using LinearMap.prodMap_isProjectiveEnvelope hfS hfT
  let g : ES × ET →ₗ[kG] Q := eProd.symm.toLinearMap.comp gProd
  have hg : g.IsProjectiveEnvelope := by
    -- Transport the product envelope back across the semisimple splitting of `Q`.
    simpa [g, gProd] using
      (LinearMap.isProjectiveEnvelope_iff_conj
        (R := kG) (LinearEquiv.refl kG (ES × ET)) eProd.symm).2 hgProd
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hq hg
  rcases ((indecomposable_iff_linearEquiv eSrc).1 hP).2 ES ET
      (ModuleCat.biprodIsoProd ES ET).symm with hESzero | hETzero
  · -- A zero left envelope would force the nonzero left quotient summand to vanish as well.
    have hESsub : Subsingleton ES := (ModuleCat.isZero_iff_subsingleton).1 hESzero
    letI : Subsingleton ES := hESsub
    have hSsub : Subsingleton S := hfS.surjective.subsingleton
    letI : Subsingleton S := hSsub
    exact not_nontrivial S hSnontrivial
  · -- The same contradiction appears on the right summand.
    have hETsub : Subsingleton ET := (ModuleCat.isZero_iff_subsingleton).1 hETzero
    letI : Subsingleton ET := hETsub
    have hTsub : Subsingleton T := hfT.surjective.subsingleton
    letI : Subsingleton T := hTsub
    exact not_nontrivial T hTnontrivial

/-- Helper for Corollary 14-14.3-2: an indecomposable summand in a finite biproduct decomposition
has simple largest semisimple quotient. -/
private theorem summand_largestSemisimpleQuotient_isSimple
    {ι : Type w} [Finite ι] {P : ι → ModuleCat kG}
    (e : M ≅ ⨁ P) (hP : ∀ i, Indecomposable (P i)) (i : ι) :
    IsSimpleModule kG (P i ⧸ Module.jacobson kG (P i)) := by
  -- First recover finiteness and projectivity of the chosen summand from the biproduct
  -- decomposition, then apply the indecomposable-projective criterion already proved above.
  let _ : Module.Finite kG (P i) := (finite_projective_of_biproduct_summand e i).1
  let _ : Module.Projective kG (P i) := (finite_projective_of_biproduct_summand e i).2
  exact largestSemisimpleQuotient_isSimple_of_indecomposable (k := k) (G := G) (hP i)

/-- Helper for Corollary 14-14.3-2: the largest semisimple quotient determines a finite projective
module up to isomorphism. -/
private theorem projective_iso_of_largestSemisimpleQuotient_iso
    {P Q : ModuleCat kG} [Module.Finite kG P] [Module.Projective kG P]
    [Module.Finite kG Q] [Module.Projective kG Q]
    (hIso : Nonempty (ModuleCat.of kG (P ⧸ Module.jacobson kG P) ≅
      ModuleCat.of kG (Q ⧸ Module.jacobson kG Q))) :
    Nonempty (P ≅ Q) := by
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  let _ : IsArtinian kG P := by
    infer_instance
  let _ : IsArtinian kG Q := by
    infer_instance
  obtain ⟨eQuot⟩ := hIso
  let qP : P →ₗ[kG] (P ⧸ Module.jacobson kG P) := (Module.jacobson kG P).mkQ
  let qQ : Q →ₗ[kG] (Q ⧸ Module.jacobson kG Q) := (Module.jacobson kG Q).mkQ
  have hqP : qP.IsProjectiveEnvelope := by
    -- The canonical Jacobson-quotient map is the reference envelope for each projective source.
    simpa [qP] using
      (show ((Module.jacobson kG P).mkQ : P →ₗ[kG] P ⧸ Module.jacobson kG P).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  have hqQ : qQ.IsProjectiveEnvelope := by
    simpa [qQ] using
      (show ((Module.jacobson kG Q).mkQ : Q →ₗ[kG] Q ⧸ Module.jacobson kG Q).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  let qQ' : Q →ₗ[kG] (P ⧸ Module.jacobson kG P) :=
    eQuot.symm.toLinearEquiv.toLinearMap.comp qQ
  have hqQ' : qQ'.IsProjectiveEnvelope := by
    -- Transport the second envelope so both projective envelopes land in the same quotient.
    simpa [qQ', qQ] using
      (LinearMap.isProjectiveEnvelope_iff_conj (R := kG)
        (LinearEquiv.refl kG Q) eQuot.symm.toLinearEquiv).2 hqQ
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hqP hqQ'
  exact ⟨eSrc.toModuleIso⟩

/-- Helper for Corollary 14-14.3-2: after reindexing a finite family to `Fin n`, the largest
semisimple quotient of the finite product identifies with the product of the largest semisimple
quotients of the factors. -/
private theorem largestSemisimpleQuotient_fin_pi_linearEquiv
    {n : ℕ} (P : Fin n → ModuleCat kG)
    [∀ i, Module.Finite kG (P i)] [∀ i, Module.Projective kG (P i)] :
    Nonempty ((((i : Fin n) → P i) ⧸ Module.jacobson kG ((i : Fin n) → P i)) ≃ₗ[kG]
      (i : Fin n) → (P i ⧸ Module.jacobson kG (P i))) := by
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  induction n with
  | zero =>
      let hLeft :
          Subsingleton (((i : Fin 0) → P i) ⧸ Module.jacobson kG ((i : Fin 0) → P i)) := by
        infer_instance
      let hRight : Subsingleton ((i : Fin 0) → (P i ⧸ Module.jacobson kG (P i))) := by
        infer_instance
      letI := hLeft
      letI := hRight
      -- Both sides are the zero module for the empty product.
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | succ n ih =>
      let Pnone : ModuleCat kG := P ((finSuccEquiv n).symm none)
      let Ptail : Fin n → ModuleCat kG := fun i ↦ P ((finSuccEquiv n).symm (some i))
      let eSplit : ((i : Fin (n + 1)) → P i) ≃ₗ[kG] (Pnone × ((i : Fin n) → Ptail i)) := by
        -- Rewrite the `Fin (n + 1)`-indexed product as a head factor and a tail product.
        let eReindex : ((o : Option (Fin n)) → P ((finSuccEquiv n).symm o)) ≃ₗ[kG]
            ((i : Fin (n + 1)) → P i) :=
          LinearEquiv.piCongrLeft kG (fun i ↦ P i) (finSuccEquiv n).symm
        simpa [Pnone, Ptail] using eReindex.symm.trans (LinearEquiv.piOptionEquivProd kG)
      have hmapJac :
          Submodule.map eSplit.toLinearMap (Module.jacobson kG ((i : Fin (n + 1)) → P i)) =
            Module.jacobson kG (Pnone × ((i : Fin n) → Ptail i)) := by
        -- The product splitting preserves the Jacobson radical because it is a linear equivalence.
        simpa [eSplit] using
          (Module.map_jacobson_of_bijective (R := kG) (f := eSplit.toLinearMap) eSplit.bijective)
      obtain ⟨eQuotSplit⟩ :
          Nonempty ((((i : Fin (n + 1)) → P i) ⧸ Module.jacobson kG ((i : Fin (n + 1)) → P i))
            ≃ₗ[kG]
              ((Pnone × ((i : Fin n) → Ptail i)) ⧸
                Module.jacobson kG (Pnone × ((i : Fin n) → Ptail i)))) := by
        exact ⟨Submodule.Quotient.equiv _ _ eSplit hmapJac⟩
      have hTailProj : Module.Projective kG ((i : Fin n) → Ptail i) := by
        -- Convert the finite product to a finite direct sum, where projectivity is already
        -- available componentwise.
        let _ : Module.Projective kG (Π₀ i : Fin n, Ptail i) := by
          infer_instance
        exact Module.Projective.of_equiv
          (DFinsupp.linearEquivFunOnFintype :
            (Π₀ i : Fin n, Ptail i) ≃ₗ[kG] ((i : Fin n) → Ptail i))
      let _ : Module.Projective kG ((i : Fin n) → Ptail i) := hTailProj
      let _ : Module.Finite kG ((i : Fin n) → Ptail i) := by
        infer_instance
      let _ : IsArtinian kG Pnone := by
        infer_instance
      let _ : IsArtinian kG ((i : Fin n) → Ptail i) := by
        infer_instance
      obtain ⟨eProd⟩ :=
        largestSemisimpleQuotient_prod_linearEquiv
          (R := kG) (P := Pnone) (Q := (i : Fin n) → Ptail i)
      obtain ⟨eTail⟩ := ih Ptail
      let eProdTail :
          (((Pnone ⧸ Module.jacobson kG Pnone) ×
              (((i : Fin n) → Ptail i) ⧸ Module.jacobson kG ((i : Fin n) → Ptail i))) ≃ₗ[kG]
            ((Pnone ⧸ Module.jacobson kG Pnone) ×
              ((i : Fin n) → Ptail i ⧸ Module.jacobson kG (Ptail i)))) :=
        LinearEquiv.prodCongr
          (LinearEquiv.refl kG (Pnone ⧸ Module.jacobson kG Pnone)) eTail
      let eAsOption :
          (((o : Option (Fin n)) → P ((finSuccEquiv n).symm o) ⧸
                Module.jacobson kG (P ((finSuccEquiv n).symm o))) ≃ₗ[kG]
            ((Pnone ⧸ Module.jacobson kG Pnone) ×
              ((i : Fin n) → Ptail i ⧸ Module.jacobson kG (Ptail i)))) := by
        -- Package the head quotient and the tail quotients back into an `Option`-indexed product.
        simpa [Pnone, Ptail] using
          (LinearEquiv.piOptionEquivProd kG :
            ((o : Option (Fin n)) → P ((finSuccEquiv n).symm o) ⧸
                Module.jacobson kG (P ((finSuccEquiv n).symm o))) ≃ₗ[kG]
              ((P ((finSuccEquiv n).symm none) ⧸
                    Module.jacobson kG (P ((finSuccEquiv n).symm none))) ×
                ((i : Fin n) → P ((finSuccEquiv n).symm (some i)) ⧸
                    Module.jacobson kG (P ((finSuccEquiv n).symm (some i))))))
      let eQuotReindex :
          (((o : Option (Fin n)) → P ((finSuccEquiv n).symm o) ⧸
                Module.jacobson kG (P ((finSuccEquiv n).symm o))) ≃ₗ[kG]
            ((i : Fin (n + 1)) → P i ⧸ Module.jacobson kG (P i))) :=
        LinearEquiv.piCongrLeft kG (fun i ↦ P i ⧸ Module.jacobson kG (P i))
          (finSuccEquiv n).symm
      -- Compose the head-tail product bridge with the inductive bridge for the tail.
      exact ⟨eQuotSplit.trans (eProd.trans (eProdTail.trans (eAsOption.symm.trans eQuotReindex)))⟩

/-- Helper for Corollary 14-14.3-2: once the head component of a product equivalence is already a
linear equivalence, the remaining tail components are linearly equivalent as well. -/
private theorem tail_linearEquiv_of_head_linearEquiv
    {A : Type v} [AddCommGroup A] [Module kG A]
    {B : Type w} [AddCommGroup B] [Module kG B]
    {C : Type x} [AddCommGroup C] [Module kG C]
    {D : Type y} [AddCommGroup D] [Module kG D]
    (e : (A × B) ≃ₗ[kG] (C × D)) (a : A ≃ₗ[kG] C)
    (ha : (((LinearMap.fst kG C D).comp e.toLinearMap).comp (LinearMap.inl kG A B)) =
      (a : A →ₗ[kG] C)) :
    Nonempty (B ≃ₗ[kG] D) := by
  let b : B →ₗ[kG] C := ((LinearMap.fst kG C D).comp e.toLinearMap).comp (LinearMap.inr kG A B)
  let c : A →ₗ[kG] D := ((LinearMap.snd kG C D).comp e.toLinearMap).comp (LinearMap.inl kG A B)
  let d : B →ₗ[kG] D := ((LinearMap.snd kG C D).comp e.toLinearMap).comp (LinearMap.inr kG A B)
  let tail : B →ₗ[kG] D := d - (c.comp a.symm.toLinearMap).comp b
  have happly (x : A × B) : e x = ((a : A →ₗ[kG] C) x.1 + b x.2, c x.1 + d x.2) := by
    rcases x with ⟨x1, x2⟩
    -- Expand the product map into its head and tail blocks.
    have hsum : e (x1, x2) = e (x1, 0) + e (0, x2) := by
      have hx : (x1, x2) = (x1, 0) + (0, x2) := by
        ext <;> simp
      rw [hx, map_add]
    ext
    · have hfst1 : (e (x1, 0)).1 = a x1 := by
        simpa using LinearMap.congr_fun ha x1
      have hfst2 : (e (0, x2)).1 = b x2 := by
        simp [b]
      calc
        (e (x1, x2)).1 = (e (x1, 0)).1 + (e (0, x2)).1 := by
          simpa using congrArg Prod.fst hsum
        _ = a x1 + b x2 := by
          rw [hfst1, hfst2]
    · have hsnd1 : (e (x1, 0)).2 = c x1 := by
        simp [c]
      have hsnd2 : (e (0, x2)).2 = d x2 := by
        simp [d]
      calc
        (e (x1, x2)).2 = (e (x1, 0)).2 + (e (0, x2)).2 := by
          simpa using congrArg Prod.snd hsum
        _ = c x1 + d x2 := by
          rw [hsnd1, hsnd2]
  have htail_apply (x : B) : e (-a.symm (b x), x) = (0, tail x) := by
    -- Kill the head coordinate to isolate the residual tail map.
    rw [happly]
    ext <;> simp [tail, sub_eq_add_neg, add_comm]
  let g : D →ₗ[kG] B := ((LinearMap.snd kG A B).comp e.symm.toLinearMap).comp (LinearMap.inr kG C D)
  have hleft : g.comp tail = LinearMap.id := by
    -- Apply `e⁻¹` to the normalized block form.
    ext x
    have hx : e.symm (0, tail x) = (-a.symm (b x), x) := by
      apply e.injective
      calc
        e (e.symm (0, tail x)) = (0, tail x) := e.apply_symm_apply _
        _ = e (-a.symm (b x), x) := (htail_apply x).symm
    simpa [g] using congrArg Prod.snd hx
  have hright : tail.comp g = LinearMap.id := by
    -- Conversely, every pure-tail vector comes from the normalized preimage.
    ext y
    let x : A × B := e.symm (0, y)
    have hx : e x = (0, y) := by
      simp [x]
    have hx1 : x.1 = -a.symm (b x.2) := by
      apply a.injective
      have hfst : (a : A →ₗ[kG] C) x.1 + b x.2 = 0 := by
        simpa [x, happly] using congrArg Prod.fst hx
      have hfst' : (a : A →ₗ[kG] C) x.1 = -(b x.2) := eq_neg_of_add_eq_zero_left hfst
      simpa [hfst']
    have hsnd : c x.1 + d x.2 = y := by
      simpa [x, happly] using congrArg Prod.snd hx
    have hsnd' : tail x.2 = y := by
      rw [hx1] at hsnd
      simpa [tail, sub_eq_add_neg, add_comm] using hsnd
    simpa [g, x] using hsnd'
  exact ⟨LinearEquiv.ofLinear tail g hright hleft⟩

/-- Helper for Corollary 14-14.3-2: a linear equivalence between finite products of simple
modules reindexes the simple factors. -/
private theorem simple_fin_pi_reindex_of_linearEquiv
    {n m : ℕ}
    (S : Fin n → Type v) [∀ i, AddCommGroup (S i)] [∀ i, Module kG (S i)]
    (T : Fin m → Type w) [∀ j, AddCommGroup (T j)] [∀ j, Module kG (T j)]
    (hS : ∀ i, IsSimpleModule kG (S i)) (hT : ∀ j, IsSimpleModule kG (T j))
    (e : ((i : Fin n) → S i) ≃ₗ[kG] ((j : Fin m) → T j)) :
    ∃ eIdx : Fin n ≃ Fin m, ∀ i, Nonempty (S i ≃ₗ[kG] T (eIdx i)) := by
  classical
  induction n generalizing m with
  | zero =>
      cases m with
      | zero =>
          refine ⟨Equiv.refl _, ?_⟩
          intro i
          exact Fin.elim0 i
      | succ m =>
          -- A nonempty product of simple modules cannot be linearly equivalent to the zero module.
          let j : Fin (m + 1) := 0
          letI : Subsingleton ((i : Fin 0) → S i) := by
            infer_instance
          letI : Nontrivial (T j) := IsSimpleModule.nontrivial kG (T j)
          letI : Nontrivial ((j : Fin (m + 1)) → T j) := by
            infer_instance
          have : Subsingleton ((j : Fin (m + 1)) → T j) := e.surjective.subsingleton
          exact False.elim ((not_nontrivial ((j : Fin (m + 1)) → T j)) inferInstance)
  | succ n ih =>
      cases m with
      | zero =>
          -- Symmetrically, the left product cannot be nonempty here either.
          let i : Fin (n + 1) := 0
          letI : Nontrivial (S i) := IsSimpleModule.nontrivial kG (S i)
          letI : Nontrivial ((i : Fin (n + 1)) → S i) := by
            infer_instance
          have : Subsingleton ((i : Fin (n + 1)) → S i) := e.injective.subsingleton
          exact False.elim ((not_nontrivial ((i : Fin (n + 1)) → S i)) inferInstance)
      | succ m =>
          let Shead : Type v := S 0
          let Stail : Fin n → Type v := fun i ↦ S i.succ
          let eSreindex : ((o : Option (Fin n)) → S ((finSuccEquiv n).symm o)) ≃ₗ[kG]
              ((i : Fin (n + 1)) → S i) :=
            LinearEquiv.piCongrLeft kG (fun i ↦ S i) (finSuccEquiv n).symm
          let eSsplit :
              (((i : Fin (n + 1)) → S i) ≃ₗ[kG] (Shead × ((i : Fin n) → Stail i))) :=
            eSreindex.symm.trans (LinearEquiv.piOptionEquivProd kG)
          let eLeft :
              ((Shead × ((i : Fin n) → Stail i)) ≃ₗ[kG] ((j : Fin (m + 1)) → T j)) :=
            eSsplit.symm.trans e
          let f : Shead →ₗ[kG] ((j : Fin (m + 1)) → T j) :=
            eLeft.toLinearMap.comp (LinearMap.inl kG Shead ((i : Fin n) → Stail i))
          have hShead : IsSimpleModule kG Shead := by
            simpa [Shead] using hS 0
          letI : Nontrivial Shead := by
            simpa [Shead] using IsSimpleModule.nontrivial kG Shead
          have hf_inj : Function.Injective f :=
            eLeft.injective.comp (LinearMap.inl_injective (R := kG))
          have hf_ne_zero : f ≠ 0 := by
            -- The head summand embeds nontrivially into the whole product.
            intro hf0
            obtain ⟨x, hx⟩ := exists_ne (0 : Shead)
            exact hx (hf_inj (by simpa [f, hf0]))
          have hcoord : ∃ j : Fin (m + 1), ((LinearMap.proj j).comp f) ≠ 0 := by
            -- A nonzero vector in a finite product has a nonzero coordinate.
            by_contra hNo
            apply hf_ne_zero
            ext x j
            have hj0 : ((LinearMap.proj j).comp f) = 0 := by
              simpa using (not_exists.mp hNo) j
            exact LinearMap.congr_fun hj0 x
          rcases hcoord with ⟨j, hj⟩
          let Thead : Type w := T j
          let Ttail : Fin m → Type w := fun i ↦ T ((finSuccEquiv' j).symm (some i))
          let eTreindex : ((o : Option (Fin m)) → T ((finSuccEquiv' j).symm o)) ≃ₗ[kG]
              ((k : Fin (m + 1)) → T k) :=
            LinearEquiv.piCongrLeft kG (fun k ↦ T k) (finSuccEquiv' j).symm
          let eTsplit :
              (((k : Fin (m + 1)) → T k) ≃ₗ[kG] (Thead × ((i : Fin m) → Ttail i))) :=
            eTreindex.symm.trans (LinearEquiv.piOptionEquivProd kG)
          let eMid :
              ((Shead × ((i : Fin n) → Stail i)) ≃ₗ[kG] (Thead × ((i : Fin m) → Ttail i))) :=
            eLeft.trans eTsplit
          let headMap : Shead →ₗ[kG] Thead :=
            ((LinearMap.fst kG Thead ((i : Fin m) → Ttail i)).comp eMid.toLinearMap).comp
              (LinearMap.inl kG Shead ((i : Fin n) → Stail i))
          have hheadMap : headMap = (LinearMap.proj j).comp f := by
            ext x
            rfl
          have hhead_ne_zero : headMap ≠ 0 := by
            rw [hheadMap]
            exact hj
          have hThead : IsSimpleModule kG Thead := by
            simpa [Thead] using hT j
          let aHead : Shead ≃ₗ[kG] Thead :=
            LinearEquiv.ofBijective headMap (LinearMap.bijective_of_ne_zero hhead_ne_zero)
          have haHead :
              (((LinearMap.fst kG Thead ((i : Fin m) → Ttail i)).comp eMid.toLinearMap).comp
                (LinearMap.inl kG Shead ((i : Fin n) → Stail i))) =
                (aHead : Shead →ₗ[kG] Thead) := by
            ext x
            rfl
          obtain ⟨eTail⟩ :=
            tail_linearEquiv_of_head_linearEquiv
              (A := Shead) (B := ((i : Fin n) → Stail i))
              (C := Thead) (D := ((i : Fin m) → Ttail i))
              eMid aHead haHead
          have hS_tail : ∀ i, IsSimpleModule kG (Stail i) := by
            intro i
            simpa [Stail] using hS i.succ
          have hT_tail : ∀ i, IsSimpleModule kG (Ttail i) := by
            intro i
            simpa [Ttail] using hT ((finSuccEquiv' j).symm (some i))
          -- Peel off the matched head simple and recurse on the tails.
          obtain ⟨eTailIdx, hTailIdx⟩ := ih Stail Ttail hS_tail hT_tail eTail
          let eIdx : Fin (n + 1) ≃ Fin (m + 1) :=
            (finSuccEquiv n).trans (Equiv.optionCongr eTailIdx) |>.trans (finSuccEquiv' j).symm
          refine ⟨eIdx, ?_⟩
          intro i
          refine Fin.cases ?_ ?_ i
          · simpa [eIdx, Shead, Thead] using
              (show Nonempty (Shead ≃ₗ[kG] Thead) from ⟨aHead⟩)
          · intro i
            simpa [eIdx, Stail, Ttail] using hTailIdx i

-- Proof sketch: the source only asserts uniqueness up to isomorphism classes of the
-- indecomposable summands. We therefore keep the public theorem at that level instead of
-- strengthening it to an equality between biproduct presentations.
/-- Corollary 14-14.3-2 (2): for a finite projective `k[G]`-module, any two finite biproduct
decompositions into indecomposable modules are unique up to reindexing and summand isomorphism. -/
theorem finite_projective_module_indecomposable_decomposition_unique
    {ι : Type w} [Finite ι] {P : ι → ModuleCat kG}
    {κ : Type x} [Finite κ] {Q : κ → ModuleCat kG}
    (hP : ∀ i, Indecomposable (P i))
    (hQ : ∀ j, Indecomposable (Q j))
    (eP : M ≅ ⨁ P) (eQ : M ≅ ⨁ Q) :
    ∃ (e : ι ≃ κ), ∀ i, Nonempty (P i ≅ Q (e i)) := by
  classical
  -- Route correction: reindex both decompositions to `Fin n` and `Fin m` first, so the remaining
  -- semisimple comparison can work with ordinary finite products instead of arbitrary finite
  -- biproducts.
  obtain ⟨n, ⟨eι⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨m, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  let Pfin : Fin n → ModuleCat kG := fun i ↦ P (eι.symm i)
  let Qfin : Fin m → ModuleCat kG := fun j ↦ Q (eκ.symm j)
  have hPwhisker (i : ι) : Pfin (eι i) ≅ P i := by
    simpa [Pfin] using Iso.refl (P i)
  have hQwhisker (j : κ) : Qfin (eκ j) ≅ Q j := by
    simpa [Qfin] using Iso.refl (Q j)
  let ePfin : M ≅ ⨁ Pfin := eP ≪≫ biproduct.whiskerEquiv eι hPwhisker
  let eQfin : M ≅ ⨁ Qfin := eQ ≪≫ biproduct.whiskerEquiv eκ hQwhisker
  have hPfin : ∀ i, Indecomposable (Pfin i) := by
    intro i
    simpa [Pfin] using hP (eι.symm i)
  have hQfin : ∀ j, Indecomposable (Qfin j) := by
    intro j
    simpa [Qfin] using hQ (eκ.symm j)
  have hPfinSimple : ∀ i, IsSimpleModule kG (Pfin i ⧸ Module.jacobson kG (Pfin i)) := by
    -- This verifies the first semisimple-side ingredient of the `Fin n` skeleton.
    intro i
    exact summand_largestSemisimpleQuotient_isSimple ePfin hPfin i
  have hQfinSimple : ∀ j, IsSimpleModule kG (Qfin j ⧸ Module.jacobson kG (Qfin j)) := by
    intro j
    exact summand_largestSemisimpleQuotient_isSimple eQfin hQfin j
  let _ : ∀ i, Module.Finite kG (Pfin i) := fun i ↦ (finite_projective_of_biproduct_summand ePfin i).1
  let _ : ∀ i, Module.Projective kG (Pfin i) :=
    fun i ↦ (finite_projective_of_biproduct_summand ePfin i).2
  let _ : ∀ j, Module.Finite kG (Qfin j) := fun j ↦ (finite_projective_of_biproduct_summand eQfin j).1
  let _ : ∀ j, Module.Projective kG (Qfin j) :=
    fun j ↦ (finite_projective_of_biproduct_summand eQfin j).2
  let ePpi : M ≅ ModuleCat.of kG ((i : Fin n) → Pfin i) := ePfin ≪≫ ModuleCat.biproductIsoPi Pfin
  let eQpi : M ≅ ModuleCat.of kG ((j : Fin m) → Qfin j) := eQfin ≪≫ ModuleCat.biproductIsoPi Qfin
  have hPjac :
      Submodule.map ePpi.toLinearEquiv.toLinearMap (Module.jacobson kG M) =
        Module.jacobson kG ((i : Fin n) → Pfin i) := by
    -- The biproduct decomposition rewrites the Jacobson radical of `M` as that of the product.
    simpa [ePpi] using
      (Module.map_jacobson_of_bijective (R := kG)
        (f := ePpi.toLinearEquiv.toLinearMap) ePpi.toLinearEquiv.bijective)
  have hQjac :
      Submodule.map eQpi.toLinearEquiv.toLinearMap (Module.jacobson kG M) =
        Module.jacobson kG ((j : Fin m) → Qfin j) := by
    simpa [eQpi] using
      (Module.map_jacobson_of_bijective (R := kG)
        (f := eQpi.toLinearEquiv.toLinearMap) eQpi.toLinearEquiv.bijective)
  let ePquot :
      (M ⧸ Module.jacobson kG M) ≃ₗ[kG]
        (((i : Fin n) → Pfin i) ⧸ Module.jacobson kG ((i : Fin n) → Pfin i)) :=
    Submodule.Quotient.equiv _ _ ePpi.toLinearEquiv hPjac
  let eQquot :
      (M ⧸ Module.jacobson kG M) ≃ₗ[kG]
        (((j : Fin m) → Qfin j) ⧸ Module.jacobson kG ((j : Fin m) → Qfin j)) :=
    Submodule.Quotient.equiv _ _ eQpi.toLinearEquiv hQjac
  obtain ⟨ePfinSemisimple⟩ := largestSemisimpleQuotient_fin_pi_linearEquiv (k := k) (G := G) Pfin
  obtain ⟨eQfinSemisimple⟩ := largestSemisimpleQuotient_fin_pi_linearEquiv (k := k) (G := G) Qfin
  let ePsimple :
      (M ⧸ Module.jacobson kG M) ≃ₗ[kG]
        ((i : Fin n) → (Pfin i ⧸ Module.jacobson kG (Pfin i))) :=
    ePquot.trans ePfinSemisimple
  let eQsimple :
      (M ⧸ Module.jacobson kG M) ≃ₗ[kG]
        ((j : Fin m) → (Qfin j ⧸ Module.jacobson kG (Qfin j))) :=
    eQquot.trans eQfinSemisimple
  let eSimpleProducts :
      ((i : Fin n) → (Pfin i ⧸ Module.jacobson kG (Pfin i))) ≃ₗ[kG]
        ((j : Fin m) → (Qfin j ⧸ Module.jacobson kG (Qfin j))) :=
    ePsimple.symm.trans eQsimple
  -- Compare the simple quotient factors directly and then lift each matched quotient isomorphism
  -- back to the corresponding indecomposable projective summands.
  obtain ⟨eSimpleIdx, hSimpleIdx⟩ :=
    simple_fin_pi_reindex_of_linearEquiv
      (S := fun i ↦ Pfin i ⧸ Module.jacobson kG (Pfin i))
      (T := fun j ↦ Qfin j ⧸ Module.jacobson kG (Qfin j))
      hPfinSimple hQfinSimple eSimpleProducts
  let eOut : ι ≃ κ := (eι.trans eSimpleIdx).trans eκ.symm
  refine ⟨eOut, ?_⟩
  intro i
  have hQuotLinear :
      Nonempty ((Pfin (eι i) ⧸ Module.jacobson kG (Pfin (eι i))) ≃ₗ[kG]
        (Qfin (eSimpleIdx (eι i)) ⧸ Module.jacobson kG (Qfin (eSimpleIdx (eι i))))) :=
    hSimpleIdx (eι i)
  have hQuotIso :
      Nonempty
        (ModuleCat.of kG (Pfin (eι i) ⧸ Module.jacobson kG (Pfin (eι i))) ≅
          ModuleCat.of kG
            (Qfin (eSimpleIdx (eι i)) ⧸
              Module.jacobson kG (Qfin (eSimpleIdx (eι i))))) := by
    rcases hQuotLinear with ⟨eQuot⟩
    exact ⟨eQuot.toModuleIso⟩
  have hSummandIso :
      Nonempty (Pfin (eι i) ≅ Qfin (eSimpleIdx (eι i))) :=
    projective_iso_of_largestSemisimpleQuotient_iso (k := k) (G := G) hQuotIso
  rcases hSummandIso with ⟨eSummand⟩
  have hLeft : P i ≅ Pfin (eι i) := (hPwhisker i).symm
  have hRight : Qfin (eSimpleIdx (eι i)) ≅ Q (eOut i) := by
    simpa [eOut] using hQwhisker (eOut i)
  exact ⟨hLeft ≪≫ eSummand ≪≫ hRight⟩

end FiniteProjectiveGroupAlgebra

-- Proof sketch: if `P` is indecomposable projective, its largest semisimple quotient is simple;
-- conversely, if the largest semisimple quotient were not simple then `P` would admit a
-- corresponding nontrivial decomposition. The helper infrastructure remains ring-theoretic, but
-- the public corollary is kept in the `k[G]` setting of the source.
/-- Corollary 14-14.3-2 (3): a projective `k[G]`-module is indecomposable if and only if its
largest semisimple quotient is simple. -/
theorem indecomposable_projective_module_iff_simple_largestSemisimpleQuotient
    {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]
    {P : ModuleCat (MonoidAlgebra k G)}
    [Module.Projective (MonoidAlgebra k G) P] [Module.Finite (MonoidAlgebra k G) P] :
    Indecomposable P ↔
      IsSimpleModule (MonoidAlgebra k G) (P ⧸ Module.jacobson (MonoidAlgebra k G) P) := by
  let _ : Module.Finite k (MonoidAlgebra k G) := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing (MonoidAlgebra k G) := IsArtinianRing.of_finite k (MonoidAlgebra k G)
  let _ : IsArtinian (MonoidAlgebra k G) P := by
    infer_instance
  constructor
  · intro hP
    -- Compare the canonical envelope of `P` with envelopes of the two factors of any semisimple
    -- decomposition of its quotient; indecomposability rules out a nontrivial split quotient.
    exact largestSemisimpleQuotient_isSimple_of_indecomposable (k := k) (G := G) hP
  · -- A nontrivial decomposition of `P` would force a nontrivial decomposition of its largest
    -- semisimple quotient, contradicting simplicity.
    exact simple_largestSemisimpleQuotient_implies_indecomposable

end
