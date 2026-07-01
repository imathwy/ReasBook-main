import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open ShortComplex

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {L M N : I ⥤ ModuleCat R}
variable {φ : L ⟶ M} {ψ : M ⟶ N}

-- Proof sketch: use `NatTrans.ext` and check equality objectwise; the hypothesis says exactly that
-- each component of `φ ≫ ψ` is zero.
private theorem module_system_comp_eq_zero
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    φ ≫ ψ = 0 := sorry

/-- The short complex in the functor category attached to the composable system
`L ⟶ M ⟶ N`. This is the owner object from which the stagewise short complexes and their
homology are derived. -/
noncomputable def module_system_shortComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    ShortComplex (I ⥤ ModuleCat R) :=
  .mk φ ψ (module_system_comp_eq_zero hcomp)

/-- Lemma 10.8.8 (1): if each stage `L_i ⟶ M_i ⟶ N_i` is a complex, then their homology modules
assemble into a system over `I`; in the directed case this is the system from the statement of
the lemma. -/
noncomputable def module_system_homology
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ModuleCat R :=
  (ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp) ⋙
    homologyFunctor (ModuleCat R)

-- Proof sketch: first rewrite `colim.map φ ≫ colim.map ψ` as `colim.map (φ ≫ ψ)` using
-- `colim.map_comp`, then substitute the vanishing natural transformation from
-- `module_system_comp_eq_zero`.
/-- Lemma 10.8.8 (2): the induced sequence on colimits
`colim L_i ⟶ colim M_i ⟶ colim N_i` is again a complex. -/
theorem colimit_module_system_isComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    colim.map φ ≫ colim.map ψ = 0 := by
  have h :=
    congrArg (fun α ↦ colim.map α)
      (module_system_comp_eq_zero hcomp)
  simpa only [Functor.map_comp, Functor.map_zero] using h

/-- The canonical comparison morphism from the colimit of the stagewise homology system to the
homology of the colimit short complex attached to `L ⟶ M ⟶ N`. -/
noncomputable def module_system_homology_comparison
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :=
  colimit.post
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
    (homologyFunctor (ModuleCat R))

-- Proof sketch: identify the stagewise homology system with the homology object of the short
-- complex system `i ↦ (L_i ⟶ M_i ⟶ N_i)`, observe that the canonical map
-- `colimit.post _ (homologyFunctor (ModuleCat R))` is the universal comparison morphism from the
-- colimit of the functor `i ↦ H_i` to the homology of the colimit short complex, and prove this
-- comparison is an isomorphism using exactness of filtered colimits of `R`-modules.
variable [IsDirectedOrder I]

/-- Lemma 10.8.8 (3): the canonical comparison morphism from the colimit of the stagewise homology
modules `H_i` to the homology of the colimit complex is an isomorphism. This formalizes the
textbook equality `H = colim_i H_i`. -/
theorem module_system_homology_comparison_isIso
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := sorry

noncomputable instance (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) :=
  module_system_homology_comparison_isIso hcomp

end
