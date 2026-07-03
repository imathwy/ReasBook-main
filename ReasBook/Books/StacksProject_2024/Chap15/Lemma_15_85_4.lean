import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open DerivedCategory
open CategoryTheory.Limits
open HomologicalComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.4:
- primary domain: comparison between homotopy-category and derived-category morphisms from
  bounded-above complexes, together with maps to shifted single complexes encoded by cocycles in
  `HomComplex`;
- inspected owner declarations:
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `DerivedCategory.Qh.map`,
  `CochainComplex.HomComplex.Cocycle.toSingleMk`,
  `CochainComplex.HomComplex.Cocycle.equivHomShift`;
- best owner abstraction: the comparison map of part `(1)` is the canonical localization map
  `DerivedCategory.Qh.map` on homotopy-category morphisms, while the primitive source datum in
  parts `(3)` and `(4)` is a degree `-2` cocycle `a : M.X (-2) ⟶ X` with
  `M.d (-3) (-2) ≫ a = 0`, owned by `Cocycle.toSingleMk`; the derived morphism to `X[2]` is a
  bridge/view obtained by applying `ShiftedHom.map` along `DerivedCategory.Q`;
- primitive data vs. derived API:
  the primitive data is the support/projectivity hypotheses together with the cocycle condition in
  degree `-2`, while the derived morphisms `M^• ⟶ X[2]` and `K^• ⟶ K^{-2}[2]` are bridge
  constructions and should not be stored as independent primitive wrapper data.

Source/core/bridge triage:
- `source-facing`: the four theorem statements below;
- `core/canonical`: `DerivedCategory.Qh.map` and the cocycle owners
  `Cocycle.toSingleMk` / `Cocycle.equivHomShift`;
- `bridge/view`: the derived morphisms obtained from those cocycles via `ShiftedHom.map`. -/

abbrev negTwoCocycleToShift {M K : Cpx}
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0) :=
  Q.map
    (equivHomShift.symm (toSingleMk a (by omega) (-3) (by omega) ha))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

abbrev negTwoProjection (K : Cpx) (hK : K.IsStrictlyGE (-2)) :=
  let _ : K.IsStrictlyGE (-2) := hK
  Q.map
    (equivHomShift.symm
      (toSingleMk
        (𝟙 (K.X (-2)))
        (by omega)
        (-3)
        (by omega)
        (by
          simpa using
            (K.isZero_of_isStrictlyGE (-2) (-3) (by omega)).eq_of_src (K.d (-3) (-2)) 0)))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

-- Proof sketch: replace `M^•` by a projective resolution `F^• → M^•` whose terms are
-- projective and which is termwise surjective. Since `K^i = 0` for `i ≤ -2`, every morphism
-- `F^• ⟶ K^•` and every homotopy factors uniquely through `M^•`, so the localization map from
-- `K(R)` to `D(R)` is bijective on morphisms out of `M^•`.
/-- Lemma 15.85.4 (1): if `M^•` is zero in positive degrees with `M^0` projective, and `K^•` is
zero in degrees `≤ -2`, then the canonical comparison
`Hom_{K(R)}(M^•, K^•) → Hom_{D(R)}(M^•, K^•)` is bijective. -/
theorem homotopyCategory_to_derived_bijective_of_projective_degree_zero
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-1)) :
    Function.Bijective (Qh.map : ((KQ).obj M ⟶ (KQ).obj K) → _) := sorry

-- Proof sketch: if `a^{-1} + h^0 d_M^{-1} = 0`, modify `a^•` by the homotopy with only
-- degree-zero component `h^0` to kill degree `-1`; then every map `K^• ⟶ N[1]` is homotopic to
-- one vanishing in degree `0`, so the induced `Ext^1` map is zero. Conversely, test against the
-- canonical class in `Ext^1_R(K^•, K^{-1})` and use part `(1)` to recover the required `h^0`.
/-- Lemma 15.85.4 (2): assume `K^•` is zero outside degrees `-1` and `0`, and `K^0` is
projective. For a map of complexes `a^• : M^• ⟶ K^•`, the induced maps
`Ext^1_R(K^•, N) → Ext^1_R(M^•, N)` vanish for all `R`-modules `N` if and only if there exists
`h^0 : M^0 ⟶ K^{-1}` with `a^{-1} + h^0 ∘ d_M^{-1} = 0`. -/
theorem inducesZeroOnModuleExt1_iff_exists_degree_zero_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hKge : K.IsStrictlyGE (-1))
    (hKle : K.IsStrictlyLE 0)
    (hK0 : Projective (K.X 0))
    (a : M ⟶ K) :
    (∀ (N : ModuleCat R) (e : ShiftedHom (Q.obj K) ((single₀).obj N) (1 : ℤ)),
      Q.map a ≫ e = 0) ↔
      ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0 := sorry

-- Proof sketch: choose a projective resolution `F^• → M^•` as in the proof of part `(1)` and a
-- representative `b^• : F^• ⟶ K^•` of `α`. The hypothesis on the composition with the canonical
-- projection to `K^{-2}[2]` lets one modify `b^•` by a homotopy so that its degree `-2`
-- component is exactly `a ∘ p^{-2}`; the support assumptions on `M^•` and `K^•` then force the
-- remaining components to factor through `M^•`, yielding a representative `a^• : M^• ⟶ K^•`
-- with prescribed degree `-2` term.
/-- Lemma 15.85.4 (3): assume `K^•` is zero in degrees `≤ -3`. Let
`α : Hom_{D(R)}(M^•, K^•)`. If the composite of `α` with the canonical projection
`K^• → K^{-2}[2]` comes from a module map `a : M^{-2} ⟶ K^{-2}` satisfying
`a ∘ d_M^{-3} = 0`, then `α` is represented by a map of complexes
`a^• : M^• ⟶ K^•` whose degree `-2` component is `a`. -/
theorem exists_representative_with_prescribed_degree_negTwo
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    (α : Q.obj M ⟶ Q.obj K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ negTwoProjection K hK = negTwoCocycleToShift a ha) :
    ∃ aMap : M ⟶ K, Q.map aMap = α ∧ aMap.f (-2) = a := sorry

-- Proof sketch: a homotopy between two representatives with the same image in `D(R)` can be
-- chosen on a projective resolution of `M^•`; arguing as in part `(3)`, it factors through
-- `M^•`. If the degree `-2` components already agree, then the support assumptions on `K^•`
-- force the remaining homotopy to have only degree `-1` and degree `0` components, giving
-- exactly the displayed formulas.
/-- Lemma 15.85.4 (4): under the hypotheses of part `(3)`, any two representatives of the same
derived morphism with the same degree `-2` component differ by homotopy components
`h^{-1} : M^{-1} ⟶ K^{-2}` and `h^0 : M^0 ⟶ K^{-1}` satisfying the usual degree `-1` and degree
`0` homotopy formulas. -/
theorem representative_difference_controlled_by_two_step_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    {aMap aMap' : M ⟶ K}
    (hQ : Q.map aMap = Q.map aMap')
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) :
    ∃ h : Homotopy aMap' aMap,
      M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
        aMap'.f (-1) =
          aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h.hom 0 (-1) ∧
        aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := sorry

end

end CategoryTheory
