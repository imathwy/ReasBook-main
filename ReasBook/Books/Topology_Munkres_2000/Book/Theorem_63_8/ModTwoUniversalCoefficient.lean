module

public import Topology_Munkres_2000.Book.Theorem_63_8.ModTwoSingularCohomology
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory

universe u

variable {K Cplus C Cminus : Type u} [Field K]
variable [AddCommGroup Cplus] [Module K Cplus]
variable [AddCommGroup C] [Module K C]
variable [AddCommGroup Cminus] [Module K Cminus]

/-- Helper for Theorem 63.8: a square-zero first differential takes values in
the cycles of the second differential. -/
lemma boundary_mem_cycles (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus)
    (hfg : g.comp f = 0) (x : Cplus) : f x ∈ LinearMap.ker g := by
  -- Evaluate the square-zero identity on the chosen chain.
  rw [LinearMap.mem_ker]
  have hx := LinearMap.congr_fun hfg x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx

/-- Helper for Theorem 63.8: the boundary map corestricted to the cycle
subspace. -/
def boundaryToCycles (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus)
    (hfg : g.comp f = 0) : Cplus →ₗ[K] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (boundary_mem_cycles f g hfg)

/-- Helper for Theorem 63.8: dualizing a square-zero pair makes every
coboundary a cocycle. -/
lemma dualBoundary_mem_cocycles (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus)
    (hfg : g.comp f = 0) (φ : Module.Dual K Cminus) :
    g.dualMap φ ∈ LinearMap.ker f.dualMap := by
  -- Evaluate the dual composite on a chain and use the primal square-zero law.
  rw [LinearMap.mem_ker]
  ext x
  have hx := LinearMap.congr_fun hfg x
  simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero] using congrArg φ hx

/-- Helper for Theorem 63.8: the dual of the second differential corestricted
to the cocycle subspace. -/
def coboundaryToCocycles (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus)
    (hfg : g.comp f = 0) :
    Module.Dual K Cminus →ₗ[K] LinearMap.ker f.dualMap :=
  g.dualMap.codRestrict (LinearMap.ker f.dualMap)
    (dualBoundary_mem_cocycles f g hfg)

/-- Helper for Theorem 63.8: restricting a cocycle to cycles annihilates the
boundary subspace. -/
lemma cocycleRestriction_mem_boundaryAnnihilator
    (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus) (hfg : g.comp f = 0)
    (φ : LinearMap.ker f.dualMap) :
    (LinearMap.ker g).dualRestrict φ.1 ∈
      (LinearMap.range (boundaryToCycles f g hfg)).dualAnnihilator := by
  -- A boundary evaluates to zero because the original functional is a cocycle.
  rw [Submodule.mem_dualAnnihilator]
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  have hx := LinearMap.congr_fun φ.2 x
  simpa only [boundaryToCycles, Submodule.dualRestrict_apply,
    LinearMap.codRestrict_apply, LinearMap.dualMap_apply,
    LinearMap.zero_apply] using hx

/-- Helper for Theorem 63.8: restriction sends cocycles to functionals on
cycles that vanish on boundaries. -/
def cocycleRestriction (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus)
    (hfg : g.comp f = 0) :
    LinearMap.ker f.dualMap →ₗ[K]
      (LinearMap.range (boundaryToCycles f g hfg)).dualAnnihilator :=
  (((LinearMap.ker g).dualRestrict.comp
      (LinearMap.ker f.dualMap).subtype).codRestrict
    (LinearMap.range (boundaryToCycles f g hfg)).dualAnnihilator
    (cocycleRestriction_mem_boundaryAnnihilator f g hfg))

/-- Helper for Theorem 63.8: every functional on cycles vanishing on
boundaries extends to a cocycle on all chains. -/
lemma cocycleRestriction_surjective
    (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus) (hfg : g.comp f = 0) :
    Function.Surjective (cocycleRestriction f g hfg) := by
  -- Extend a functional from the cycle subspace to the full chain group.
  intro ψ
  let extension : Module.Dual K C :=
    Subspace.dualLift (LinearMap.ker g) ψ.1
  have extensionCocycle : extension ∈ LinearMap.ker f.dualMap := by
    rw [LinearMap.mem_ker]
    ext x
    have hBoundary : boundaryToCycles f g hfg x ∈
        LinearMap.range (boundaryToCycles f g hfg) :=
      LinearMap.mem_range_self (boundaryToCycles f g hfg) x
    have hψ := (Submodule.mem_dualAnnihilator ψ.1).mp ψ.2
      (boundaryToCycles f g hfg x) hBoundary
    calc
      extension (f x) =
          extension (boundaryToCycles f g hfg x) := by
        simp only [boundaryToCycles, LinearMap.codRestrict_apply]
      _ = ψ.1 (boundaryToCycles f g hfg x) :=
        Subspace.dualLift_of_subtype (boundaryToCycles f g hfg x)
      _ = 0 := hψ
  refine ⟨⟨extension, extensionCocycle⟩, ?_⟩
  -- Restriction cancels the chosen extension on the cycle subspace.
  apply Subtype.ext
  ext z
  exact Subspace.dualLift_of_subtype z

/-- Helper for Theorem 63.8: the cocycles restricting trivially to cycles are
exactly the coboundaries. -/
lemma range_coboundaryToCocycles_eq_ker_cocycleRestriction
    (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus) (hfg : g.comp f = 0) :
    LinearMap.range (coboundaryToCocycles f g hfg) =
      LinearMap.ker (cocycleRestriction f g hfg) := by
  apply le_antisymm
  · -- A coboundary vanishes after restriction to the kernel of `g`.
    rintro φ ⟨η, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    ext z
    calc
      _ = η (g z.1) := rfl
      _ = 0 := by simpa only [map_zero] using congrArg η z.2
      _ = _ := rfl
  · -- A cocycle vanishing on all cycles lies in the range of the dual of `g`.
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ
    have hRestriction : (LinearMap.ker g).dualRestrict φ.1 = 0 := by
      exact congrArg Subtype.val hφ
    have hAnnihilator : φ.1 ∈ (LinearMap.ker g).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro z hz
      have hzValue := LinearMap.congr_fun hRestriction ⟨z, hz⟩
      simpa only [Submodule.dualRestrict_apply, LinearMap.zero_apply] using hzValue
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker g] at hAnnihilator
    obtain ⟨η, hη⟩ := hAnnihilator
    refine ⟨η, ?_⟩
    exact Subtype.ext hη

/-- Helper for Theorem 63.8: cohomology of the dual of a square-zero pair is
canonically the dual of its homology quotient. -/
noncomputable def dualHomologyQuotientEquiv
    (f : Cplus →ₗ[K] C) (g : C →ₗ[K] Cminus) (hfg : g.comp f = 0) :
    (LinearMap.ker f.dualMap ⧸
        LinearMap.range (coboundaryToCocycles f g hfg)) ≃ₗ[K]
      Module.Dual K
        (LinearMap.ker g ⧸ LinearMap.range (boundaryToCycles f g hfg)) :=
  (Submodule.quotEquivOfEq _ _
      (range_coboundaryToCocycles_eq_ker_cocycleRestriction f g hfg)).trans
    ((cocycleRestriction f g hfg).quotKerEquivOfSurjective
      (cocycleRestriction_surjective f g hfg)) |>.trans
        ((LinearMap.range (boundaryToCycles f g hfg)).dualQuotEquivDualAnnihilator.symm)

/-- Helper for Theorem 63.8: the underlying linear maps of a module-valued
short complex compose to zero. -/
lemma shortComplex_comp_zero (S : ShortComplex (ModuleCat.{u} K)) :
    S.g.hom.comp S.f.hom = 0 := by
  -- Forget the categorical square-zero law once, retaining its linear-map spelling.
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg ModuleCat.Hom.hom S.zero

/-- Helper for Theorem 63.8: dualizing the arrows of a short complex preserves
the square-zero law, with their order reversed. -/
lemma dualShortComplex_zero (S : ShortComplex (ModuleCat.{u} K)) :
    S.f.hom.dualMap.comp S.g.hom.dualMap = 0 := by
  -- Evaluate a dual functional on the original square-zero composite.
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (shortComplex_comp_zero S) x
  simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply,
    LinearMap.zero_apply, map_zero] using congrArg φ hx

/-- Helper for Theorem 63.8: the dual of a module-valued short complex reverses
its arrows and takes the linear dual in every degree. -/
@[expose]
def dualShortComplex (S : ShortComplex (ModuleCat.{u} K)) :
    ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap
    (dualShortComplex_zero S)

/-- Helper for Theorem 63.8: the first arrow of the dual short complex is the
dual of the original second arrow. -/
lemma dualShortComplex_f_hom (S : ShortComplex (ModuleCat.{u} K)) :
    (dualShortComplex S).f.hom = S.g.hom.dualMap := by
  -- Expose the first projection without unfolding the construction downstream.
  rfl

/-- Helper for Theorem 63.8: the second arrow of the dual short complex is the
dual of the original first arrow. -/
lemma dualShortComplex_g_hom (S : ShortComplex (ModuleCat.{u} K)) :
    (dualShortComplex S).g.hom = S.f.hom.dualMap := by
  -- Expose the second projection without unfolding the construction downstream.
  rfl

/-- Helper for Theorem 63.8: dualizing the right square of a short-complex
isomorphism gives the left square between the dual complexes. -/
lemma dualShortComplexIso_comm₁₂ {S T : ShortComplex (ModuleCat.{u} K)}
    (e : S ≅ T) :
    ((ShortComplex.π₃.mapIso e).toLinearEquiv.dualMap.toModuleIso).hom ≫
        (dualShortComplex S).f =
      (dualShortComplex T).f ≫
        ((ShortComplex.π₂.mapIso e).toLinearEquiv.dualMap.toModuleIso).hom := by
  -- Evaluate the dual square and invoke the original right commutative square.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have h := congrArg ModuleCat.Hom.hom e.hom.comm₂₃
  have hx := LinearMap.congr_fun h x
  change φ (e.hom.τ₃ (S.g x)) = φ (T.g (e.hom.τ₂ x))
  exact congrArg φ hx.symm

/-- Helper for Theorem 63.8: dualizing the left square of a short-complex
isomorphism gives the right square between the dual complexes. -/
lemma dualShortComplexIso_comm₂₃ {S T : ShortComplex (ModuleCat.{u} K)}
    (e : S ≅ T) :
    ((ShortComplex.π₂.mapIso e).toLinearEquiv.dualMap.toModuleIso).hom ≫
        (dualShortComplex S).g =
      (dualShortComplex T).g ≫
        ((ShortComplex.π₁.mapIso e).toLinearEquiv.dualMap.toModuleIso).hom := by
  -- Evaluate the dual square and invoke the original left commutative square.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have h := congrArg ModuleCat.Hom.hom e.hom.comm₁₂
  have hx := LinearMap.congr_fun h x
  change φ (e.hom.τ₂ (S.f x)) = φ (T.f (e.hom.τ₁ x))
  exact congrArg φ hx.symm

/-- Helper for Theorem 63.8: an isomorphism of short complexes dualizes
contravariantly to an isomorphism of their dual short complexes. -/
noncomputable def dualShortComplexIso {S T : ShortComplex (ModuleCat.{u} K)}
    (e : S ≅ T) : dualShortComplex T ≅ dualShortComplex S :=
  ShortComplex.isoMk
    ((ShortComplex.π₃.mapIso e).toLinearEquiv.dualMap.toModuleIso)
    ((ShortComplex.π₂.mapIso e).toLinearEquiv.dualMap.toModuleIso)
    ((ShortComplex.π₁.mapIso e).toLinearEquiv.dualMap.toModuleIso)
    (dualShortComplexIso_comm₁₂ e) (dualShortComplexIso_comm₂₃ e)

/-- Helper for Theorem 63.8: homology of the dual short complex is linearly
equivalent to the dual of the original homology. -/
noncomputable def dualShortComplexHomologyLinearEquiv
    (S : ShortComplex (ModuleCat.{u} K)) :
    (dualShortComplex S).homology ≃ₗ[K] Module.Dual K S.homology :=
  (dualShortComplex S).moduleCatHomologyIso.toLinearEquiv |>.trans
    (dualHomologyQuotientEquiv S.f.hom S.g.hom
      (shortComplex_comp_zero S)) |>.trans
        S.moduleCatHomologyIso.toLinearEquiv.dualMap

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Theorem 63.8: the degreewise singular cochain short complex is
isomorphic to the dual of the corresponding singular chain short complex. -/
lemma nonempty_modTwoSingularCochainScIsoDualChainSc
    (X : TopCat) (n : ℕ) :
    Nonempty
      ((modTwoSingularCochainComplex X).sc n ≅
        dualShortComplex (K := ZMod 2)
          ((modTwoSingularChainComplex X).sc n)) := by
  -- Split off degree zero, where both predecessor indices are normalized to zero.
  cases n with
  | zero =>
      let eC :
          (modTwoSingularCochainComplex X).sc 0 ≅
            (modTwoSingularCochainComplex X).sc' 0 0 1 :=
        (modTwoSingularCochainComplex X).isoSc' 0 0 1
          CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)
      let eD :
          (modTwoSingularChainComplex X).sc 0 ≅
            (modTwoSingularChainComplex X).sc' 1 0 0 :=
        (modTwoSingularChainComplex X).isoSc' 1 0 0
          (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero
      have eM :
          (modTwoSingularCochainComplex X).sc' 0 0 1 ≅
            dualShortComplex (K := ZMod 2)
              ((modTwoSingularChainComplex X).sc' 1 0 0) := by
        let e1 :
            ((modTwoSingularCochainComplex X).sc' 0 0 1).X₁ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' 1 0 0)).X₁ :=
          eqToIso (by rfl)
        let e2 :
            ((modTwoSingularCochainComplex X).sc' 0 0 1).X₂ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' 1 0 0)).X₂ :=
          eqToIso (by rfl)
        let e3 :
            ((modTwoSingularCochainComplex X).sc' 0 0 1).X₃ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' 1 0 0)).X₃ :=
          eqToIso (by rfl)
        refine ShortComplex.isoMk e1 e2 e3 ?_ ?_
        · dsimp only [e1, e2]
          simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
          apply ModuleCat.hom_ext
          rw [dualShortComplex_f_hom]
          apply LinearMap.ext
          intro φ
          apply LinearMap.ext
          intro x
          simp
          change (0 : ZMod 2) = 0
          rfl
        · dsimp only [e2, e3]
          simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
          apply ModuleCat.hom_ext
          rw [dualShortComplex_g_hom]
          exact ((congrArg ModuleCat.Hom.hom
            (modTwoSingularCochainComplex_d X 0)).trans
              (modTwoSingularCoboundary_hom X 0)).symm
      -- Pass to explicit neighboring indices, dualize there, and return contravariantly.
      exact ⟨eC ≪≫ eM ≪≫ dualShortComplexIso eD⟩
  | succ n =>
      let eC :
          (modTwoSingularCochainComplex X).sc (n + 1) ≅
            (modTwoSingularCochainComplex X).sc' n (n + 1) (n + 1 + 1) :=
        (modTwoSingularCochainComplex X).isoSc' n (n + 1) (n + 1 + 1)
          (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))
      let eD :
          (modTwoSingularChainComplex X).sc (n + 1) ≅
            (modTwoSingularChainComplex X).sc' (n + 1 + 1) (n + 1) n :=
        (modTwoSingularChainComplex X).isoSc' (n + 1 + 1) (n + 1) n
          (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)
      have eM :
          (modTwoSingularCochainComplex X).sc' n (n + 1) (n + 1 + 1) ≅
            dualShortComplex (K := ZMod 2)
              ((modTwoSingularChainComplex X).sc' (n + 1 + 1) (n + 1) n) := by
        let e1 :
            ((modTwoSingularCochainComplex X).sc' n (n + 1) (n + 1 + 1)).X₁ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' (n + 1 + 1) (n + 1) n)).X₁ :=
          eqToIso (by rfl)
        let e2 :
            ((modTwoSingularCochainComplex X).sc' n (n + 1) (n + 1 + 1)).X₂ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' (n + 1 + 1) (n + 1) n)).X₂ :=
          eqToIso (by rfl)
        let e3 :
            ((modTwoSingularCochainComplex X).sc' n (n + 1) (n + 1 + 1)).X₃ ≅
              (dualShortComplex (K := ZMod 2)
                ((modTwoSingularChainComplex X).sc' (n + 1 + 1) (n + 1) n)).X₃ :=
          eqToIso (by rfl)
        refine ShortComplex.isoMk e1 e2 e3 ?_ ?_
        · dsimp only [e1, e2]
          simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
          apply ModuleCat.hom_ext
          rw [dualShortComplex_f_hom]
          exact ((congrArg ModuleCat.Hom.hom
            (modTwoSingularCochainComplex_d X n)).trans
              (modTwoSingularCoboundary_hom X n)).symm
        · dsimp only [e2, e3]
          simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
          apply ModuleCat.hom_ext
          rw [dualShortComplex_g_hom]
          exact ((congrArg ModuleCat.Hom.hom
            (modTwoSingularCochainComplex_d X (n + 1))).trans
              (modTwoSingularCoboundary_hom X (n + 1))).symm
      -- Positive degrees have honest predecessor and successor indices on both sides.
      exact ⟨eC ≪≫ eM ≪≫ dualShortComplexIso eD⟩

-- Route correction: the duality bridge is obtained from mathlib's explicit
-- homology quotient, without any finite-dimensionality assumption.
/-- Helper for Theorem 63.8: mod-two singular cohomology is the linear dual of
mod-two singular homology in the same degree. -/
lemma nonempty_modTwoSingularCohomologyDualHomologyLinearEquiv
    (X : TopCat) (n : ℕ) :
    Nonempty
      (ModTwoSingularCohomology X n ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) ((modTwoSingularChainComplex X).homology n)) :=
  by
    -- Transport cohomology to the dual chain short complex, then apply universal coefficients.
    obtain ⟨e⟩ := nonempty_modTwoSingularCochainScIsoDualChainSc X n
    exact ⟨(ShortComplex.homologyMapIso e).toLinearEquiv.trans
      (dualShortComplexHomologyLinearEquiv
        ((modTwoSingularChainComplex X).sc n))⟩

end AlgebraicTopology

end

end
