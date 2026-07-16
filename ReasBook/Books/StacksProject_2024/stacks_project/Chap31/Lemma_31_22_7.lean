import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_28_4
import StacksProject_2024.stacks_project.Chap31.Lemma_31_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners `Flat` and
-- `LocallyOfFinitePresentation`; local Chapter 31 precedent fixes closed subschemes as
-- `Scheme.IdealSheafData`, fibre restrictions by `IdealSheafData.comap`, absolute quasi-regular
-- immersions by `IsQuasiRegularImmersion`, and relative quasi-regular immersions by
-- `RelativeQuasiRegularImmersion`.

/-- Lemma 31.22.7 (1): let `f : X ⟶ S` be flat and locally of finite presentation, let
`T ⊆ X` be a closed subscheme, and let `x : T`. If the fibre `T_s ⊆ X_s`, with
`s = f(T.subschemeι x)`, is a quasi-regular immersion in a neighbourhood of `x`, then after
shrinking to an open neighbourhood `U` of `x` there is a relative quasi-regular immersion
`Z ⊆ U` such that `Z_s = (T ∩ U)_s` and `T ∩ U ⊆ Z`. The regular-immersion conclusion for
`Z ⟶ U` is included as the final clause from the lemma. -/
@[stacks 063W]
theorem exists_open_relativeQuasiRegularImmersion_le_fiber_eq_of_fiber_quasiRegular_near
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              ∃ _ : T.comap U.ι ≤ Z,
                (T.comap U.ι).comap
                    (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))) =
                  Z.comap (Scheme.Hom.fiberι (U.ι ≫ f) (f (T.subschemeι x))) := sorry

/-- Lemma 31.22.7 (2): under the hypotheses of part (1), if `T ⟶ X` is of finite presentation
and `T ⟶ S` is flat at `x`, then the open neighbourhood and relative quasi-regular immersion may
be chosen so that `T ∩ U = Z`. The regular-immersion conclusion for `Z ⟶ U` is included. -/
@[stacks 063W]
theorem exists_open_relativeQuasiRegularImmersion_eq_of_finitePresentation_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.FinitePresentation T.subschemeι]
    (hTflat : Scheme.Hom.flatAt (T.subschemeι ≫ f) x)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z := sorry

/-- Lemma 31.22.7 (3): under the hypotheses of part (1), if near `x` the closed subscheme `T` is
cut out by `c` equations and `c` is the codimension of `T_s` in `X_s` at `x`, expressed by
`dim_x X_s = dim_x T_s + c`, then the open neighbourhood and relative quasi-regular immersion may
be chosen so that `T ∩ U = Z`. The regular-immersion conclusion for `Z ⟶ U` is included. -/
@[stacks 063W]
theorem exists_open_relativeQuasiRegularImmersion_eq_of_cutOutBy_expectedCodimension
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData) (x : T.subscheme)
    [Flat f] [LocallyOfFinitePresentation f] (c : ℕ)
    (V : X.affineOpens) (hV : T.subschemeι x ∈ (V : Set X))
    (g : Fin c → Γ(X, V)) (hcut : T.ideal V = Ideal.span (Set.range g))
    (hdim :
      f.fiberDimensionAt (T.subschemeι x) =
        (T.subschemeι ≫ f).fiberDimensionAt x + (c : WithBot ℕ∞))
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (T.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (T.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (T.subschemeι x)))) ∧
          IsQuasiRegularImmersion
            (((T.comap (Scheme.Hom.fiberι f (f (T.subschemeι x)))).comap W.ι).subschemeι)) :
    ∃ U : X.Opens,
      ∃ _ : T.subschemeι x ∈ (U : Set X),
        ∃ Z : U.toScheme.IdealSheafData,
          ∃ _ : RelativeQuasiRegularImmersion (U.ι ≫ f) Z.subschemeι,
            ∃ _ : IsRegularImmersion Z.subschemeι,
              T.comap U.ι = Z := sorry

/-- Lemma 31.22.7 (4): in particular, if `T ⟶ S` is locally of finite presentation and flat, and
every fibre `T_s ⊆ X_s` is a quasi-regular immersion, then `T ⟶ X` is a relative quasi-regular
immersion. -/
@[stacks 063W]
theorem relativeQuasiRegularImmersion_of_flat_locallyOfFinitePresentation_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (T : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (T.subschemeι ≫ f)] [Flat (T.subschemeι ≫ f)]
    (hfibers : ∀ s : S,
      IsQuasiRegularImmersion ((T.comap (Scheme.Hom.fiberι f s)).subschemeι)) :
    RelativeQuasiRegularImmersion f T.subschemeι := sorry

end AlgebraicGeometry
