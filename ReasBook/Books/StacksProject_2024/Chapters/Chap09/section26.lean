import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_26_1 (from Chap09) -/
universe u v

open IntermediateField
open IntermediateField.AdjoinSimple

/-- The textbook notation `k(x_i)` for the rational function field in variables indexed by `ι`. -/
scoped[MvRatFunc] notation:max k "⟮X_" ι "⟯" => FractionRing (MvPolynomial ι k)

open scoped MvRatFunc

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Source/core/bridge triage for Definition 9.26.1:
- `source-facing`: purely transcendental field extensions `K / k`
- `core/canonical`: the transcendence-basis predicate `IsTranscendenceBasis k x` together with the
  multivariable rational function field type `k⟮X_ι⟯ = FractionRing (MvPolynomial ι k)`
- `bridge/view`: the transcendence-basis and algebraically independent generating-family
  formulations obtained from the source-facing rational-function-field isomorphism via
  `AlgebraicIndependent.aevalEquivField` and
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`
- `layer`: `source-facing`

Primitive data are the source-facing `k`-algebra isomorphism from a multivariable rational
function field `k⟮X_ι⟯` onto `K`. The transcendence-basis and algebraically independent generating
family presentations are derived bridge API from the canonical owners above.
-/

/- Companion recall: the textbook notion that a family of elements of `K` is algebraically
independent over `k` is the canonical mathlib predicate `AlgebraicIndependent`. -/
recall AlgebraicIndependent

/- Companion recall: the textbook notion of a transcendence basis is the canonical mathlib
predicate `IsTranscendenceBasis`. -/
recall IsTranscendenceBasis

/- Companion recall: an algebraically independent family identifies the generated intermediate
field with the rational function field on the corresponding indeterminates. -/
recall AlgebraicIndependent.aevalEquivField

/- Companion recall: an algebraically independent generating family is a transcendence basis
exactly when the ambient field is algebraic over the generated intermediate field. -/
recall AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic

/-- Definition 9.26.1: a purely transcendental extension of `k` is a field extension `K/k`
`k`-isomorphic to a multivariable rational function field `k(x_i)`. The transcendence-basis and
algebraically independent generating-family formulations are recorded below as companion bridge
theorems. -/
def IsPurelyTranscendental (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ (ι : Type v), Nonempty (k⟮X_ι⟯ ≃ₐ[k] K)

/-- Companion bridge: a purely transcendental extension admits a transcendence basis generating the
whole field. -/
theorem isPurelyTranscendental_iff_exists_isTranscendenceBasis :
    IsPurelyTranscendental k K ↔
    ∃ (ι : Type v) (x : ι → K),
      IsTranscendenceBasis k x ∧ adjoin k (Set.range x) = ⊤ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ι, ⟨e⟩⟩
    let y : ι → k⟮X_ι⟯ := fun i ↦ algebraMap (MvPolynomial ι k) k⟮X_ι⟯ (MvPolynomial.X i)
    have hy_basis : IsTranscendenceBasis k y := by
      let _ : Algebra.IsAlgebraic (MvPolynomial ι k) k⟮X_ι⟯ := by
        exact
          IsFractionRing.comap_isAlgebraic_iff.mpr
            (inferInstance : Algebra.IsAlgebraic k⟮X_ι⟯ k⟮X_ι⟯)
      simpa [y, Function.comp] using
        (IsTranscendenceBasis.mvPolynomial ι k).algebraMap_comp
    have hy_top : adjoin k (Set.range y) = ⊤ := by
      have hy_aeval (p : MvPolynomial ι k) :
          MvPolynomial.aeval y p = algebraMap (MvPolynomial ι k) k⟮X_ι⟯ p := by
        induction p using MvPolynomial.induction_on with
        | C a =>
            rw [MvPolynomial.aeval_C]
            simpa using
              (show algebraMap k k⟮X_ι⟯ a =
                  algebraMap (MvPolynomial ι k) k⟮X_ι⟯ (algebraMap k (MvPolynomial ι k) a) from by
                rw [IsScalarTower.algebraMap_eq k (MvPolynomial ι k) k⟮X_ι⟯]
                simp)
        | add p q hp hq =>
            simp [hp, hq]
        | mul_X p i hp =>
            simp [y, hp, map_mul]
      apply eq_top_iff.mpr
      intro z _
      rw [mem_adjoin_range_iff k y]
      obtain ⟨p, q, hq, hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι k) z
      refine ⟨p, q, ?_⟩
      rw [hy_aeval p, hy_aeval q]
      exact hz.symm
    refine ⟨ι, e ∘ y, e.isTranscendenceBasis hy_basis, ?_⟩
    apply eq_top_iff.mpr
    intro z _
    rcases e.surjective z with ⟨w, rfl⟩
    have hw : w ∈ adjoin k (Set.range y) := by
      rw [hy_top]
      trivial
    have hw' : e w ∈ (adjoin k (Set.range y)).map e.toAlgHom := by
      exact ⟨w, hw, rfl⟩
    rw [adjoin_map, ← Set.range_comp] at hw'
    exact hw'
  · rintro ⟨ι, x, hx, hx_top⟩
    exact ⟨ι, ⟨hx.1.aevalEquivField.trans ((equivOfEq hx_top).trans topEquiv)⟩⟩

/-- Companion source-facing reformulation: a purely transcendental extension is generated by an
algebraically independent family. -/
theorem isPurelyTranscendental_iff_exists_algebraicIndependent :
    IsPurelyTranscendental k K ↔
    ∃ (ι : Type v) (x : ι → K),
      AlgebraicIndependent k x ∧ adjoin k (Set.range x) = ⊤ := by
  rw [isPurelyTranscendental_iff_exists_isTranscendenceBasis]
  refine ⟨?_, ?_⟩
  · rintro ⟨ι, x, hx, hx_top⟩
    exact ⟨ι, x, hx.1, hx_top⟩
  · rintro ⟨ι, x, hx_ind, hx_top⟩
    have hx_alg : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K := by
      rw [← isAlgebraic_adjoin_iff_top, hx_top, Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surjective topEquiv.surjective
    exact ⟨ι, x, hx_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hx_alg, hx_top⟩

/-- A simple extension generated by a transcendental element is purely transcendental. -/
theorem isPurelyTranscendental_adjoin_simple_of_transcendental {t : K}
    (ht : Transcendental k t) :
    IsPurelyTranscendental k k⟮t⟯ := by
  let L := k⟮t⟯
  let g : L := gen k t
  let x : PUnit.{v + 1} → L := fun _ ↦ g
  have hx_range : Set.range x = ({g} : Set L) := by
    simp [x]
  have hg_trans : Transcendental k g := by
    rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective L K)]
    simpa [L, g] using ht
  have hx_ind : AlgebraicIndependent k x := by
    rw [algebraicIndependent_singleton_iff PUnit.unit]
    simpa [x] using hg_trans
  have hx_top : adjoin k (Set.range x) = ⊤ := by
    apply lift_injective L
    calc
      lift (adjoin k (Set.range x)) = lift (k⟮g⟯) := by rw [hx_range]
      _ = k⟮t⟯ := by simp [L, g]
      _ = lift (⊤ : IntermediateField k L) := by simp [L]
  exact isPurelyTranscendental_iff_exists_algebraicIndependent.mpr
    ⟨PUnit.{v + 1}, x, hx_ind, hx_top⟩

/- The source-facing owner `IsPurelyTranscendental` now keeps the textbook rational-function-field
presentation as primitive data. The transcendence-basis and algebraically independent generating
family views remain thin bridge theorems via the canonical owners `IsTranscendenceBasis` and
`AlgebraicIndependent.aevalEquivField`. -/

/-! ### Example_9_26_2 (from Chap09) -/
open IntermediateField
open IntermediateField.AdjoinSimple
open scoped RatFunc

/- Domain-style sampling for Example 9.26.2:
- primary domain: simple transcendental field extensions;
- sampled owner declarations:
  `IsPurelyTranscendental`,
  `isPurelyTranscendental_adjoin_simple_of_transcendental`,
  `RatFunc.algEquivOfTranscendental`,
  `transcendental_algebraMap_iff`;
- best owner abstraction: the chapter owner `IsPurelyTranscendental`;
- primitive data: transcendence of `π` over `ℚ`;
- derived API: pure transcendence of `ℚ⟮π⟯` via the upstream simple-extension owner theorem, and
  the resulting rational-function equivalence via `RatFunc.algEquivOfTranscendental`.
-/

/-- The real number `π` is transcendental over `ℚ`. -/
-- Proof sketch: this is the classical transcendence theorem for `π`, for example from
-- Lindemann-Weierstrass.
-- TODO: supply the upstream transcendence theorem `Transcendental ℚ Real.pi`; the rest of this
-- file already reduces the textbook example to that single input.
theorem real_pi_transcendental : Transcendental ℚ Real.pi := sorry

/-- Example 9.26.2: the simple extension `ℚ(π)` is purely transcendental over `ℚ`. -/
-- Proof sketch: since `π` is transcendental over `ℚ`, the distinguished generator of `ℚ⟮π⟯`
-- yields the canonical owner theorem for simple transcendental extensions.
theorem rat_adjoin_pi_isPurelyTranscendental :
    IsPurelyTranscendental ℚ ℚ⟮Real.pi⟯ :=
  isPurelyTranscendental_adjoin_simple_of_transcendental real_pi_transcendental

noncomputable section

section

local instance ratFuncRatAlgebra : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Helper for Example 9.26.2: the canonical rational-function-field model of `ℚ(π)`. -/
-- Route correction: `RatFunc.algEquivOfTranscendental` is structure-valued, so this helper is a
-- `def` under the polynomial-induced `ℚ`-algebra instance on `RatFunc ℚ`.
-- Proof sketch: once `π` is known transcendental, the standard `RatFunc` equivalence specializes
-- directly to the simple extension `ℚ⟮π⟯`.
noncomputable def rat_adjoin_pi_algEquiv_ratFunc :
    RatFunc ℚ ≃ₐ[ℚ] ℚ⟮Real.pi⟯ :=
  RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

/- In particular, `ℚ(π)` is `ℚ`-isomorphic to the one-variable rational function field `ℚ(x)`;
this is the canonical specialization of `RatFunc.algEquivOfTranscendental`. -/
#check RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

end

/-! ### Lemma_9_26_3 (from Chap09) -/
universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Lemma 9.26.3:
- primary domain: transcendence bases for field extensions;
- sampled owner declarations:
  `IsTranscendenceBasis`,
  `exists_isTranscendenceBasis`,
  `exists_isTranscendenceBasis'`,
  `IsTranscendenceBasis.cardinalMk_eq`;
- best owner abstraction: `IsTranscendenceBasis`;
- primitive data: the field extension `F ⟶ E`;
- derived API: existence of a transcendence basis and invariance of the cardinality of any two
  transcendence bases.

Source/core/bridge triage:
- `source-facing`: existence of a transcendence basis of `E/F` and equality of the cardinalities
  of any two transcendence bases;
- `core/canonical`: the owner predicate `IsTranscendenceBasis F x`;
- `bridge/view`: the type-indexed variant `exists_isTranscendenceBasis'`;
- `layer`: `source-facing`.

The source lemma adds no new owner object beyond the canonical predicate
`IsTranscendenceBasis`, so the file should recall the exact existence and uniqueness-of-cardinality
theorems rather than a local wrapper or a type-indexed surrogate.
-/

/- Lemma 9.26.3 (1): for a field extension `E/F`, a transcendence basis exists. This is the
canonical source-facing mathlib theorem `exists_isTranscendenceBasis`. -/
recall exists_isTranscendenceBasis

/- Lemma 9.26.3 (2): any two transcendence bases of `E/F` have the same cardinality. This is the
canonical mathlib theorem `IsTranscendenceBasis.cardinalMk_eq`. -/
recall IsTranscendenceBasis.cardinalMk_eq

/-! ### Definition_9_26_4 (from Chap09) -/
universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
variable {ι : Type v} {x : ι → K}

/- Source/core/bridge triage for Definition 9.26.4:
- sampled owner declarations: `IsTranscendenceBasis`, `exists_isTranscendenceBasis`,
  `Algebra.trdeg`, `IsTranscendenceBasis.cardinalMk_eq_trdeg`;
- `source-facing`: the transcendence degree of a field extension `K/k`
- `core/canonical`: `Algebra.trdeg k K`
- `bridge/view`: `IsTranscendenceBasis.cardinalMk_eq_trdeg`, identifying the cardinality of any
  transcendence basis with that invariant
- `layer`: `core/canonical`

Primitive data are only the field extension and its canonical `k`-algebra structure on `K`. A
choice of transcendence basis and the equality between its cardinality and the invariant are
derived API, so the owner file should recall `Algebra.trdeg` directly and keep the basis
cardinality statement as a companion.
-/

/- Definition 9.26.4: for a field extension `K / k`, the transcendence degree of `K` over `k`
is the canonical mathlib cardinal-valued invariant `Algebra.trdeg k K`. -/
recall Algebra.trdeg

/- Companion recall: `IsTranscendenceBasis.cardinalMk_eq_trdeg` identifies the cardinality of any
transcendence basis with `Algebra.trdeg`. -/
recall IsTranscendenceBasis.cardinalMk_eq_trdeg

/-! ### Lemma_9_26_5 (from Chap09) -/
universe u v

/-
Source/core/bridge triage for Lemma 9.26.5:
- primary domain: transcendence degree in towers of algebra extensions;
- sampled owner declarations: `Algebra.trdeg`, `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `lift_trdeg_add_eq`, and `trdeg_add_eq`;
- best owner abstraction: `Algebra.trdeg`, with `trdeg_add_eq` as the canonical tower formula;
- primitive data: a tower `R → S → A` of commutative rings equipped with the faithful-scalar and
  no-zero-divisor hypotheses needed for the canonical additivity theorem;
- derived API: the Stacks field-extension statement is obtained from `trdeg_add_eq` by typeclass
  specialization;
- `source-facing`: additivity of transcendence degree in a tower of field extensions;
- `core/canonical`: `Algebra.trdeg` and its tower theorem `trdeg_add_eq`;
- `bridge/view`: the field-specialization of `trdeg_add_eq`;
- `layer`: `core/canonical`.

The source lemma adds no new mathematics beyond the canonical tower formula, so the file should
recall `trdeg_add_eq` directly instead of introducing a parallel local field-only wrapper.
-/

/-
Lemma 9.26.5: transcendence degree is additive in a tower. The Stacks field-extension statement is
the field specialization of the canonical mathlib theorem `trdeg_add_eq`.
-/
recall trdeg_add_eq (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K]
    [Nontrivial k] {L : Type v} [CommRing L] [NoZeroDivisors L] [Algebra k L] [Algebra K L]
    [FaithfulSMul k K] [FaithfulSMul K L] [IsScalarTower k K L] :
    Algebra.trdeg k K + Algebra.trdeg K L = Algebra.trdeg k L

/-! ### Example_9_26_6 (from Chap09) -/
open IntermediateField
open Cardinal
open IntermediateField.AdjoinPair
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

section

/- Domain-style sampling for Example 9.26.6:
- primary domain: transcendence degree of finitely generated field extensions;
- sampled owner declarations:
  `Algebra.trdeg`,
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`,
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `IntermediateField.AdjoinPair.gen₁` / `IntermediateField.AdjoinPair.gen₂`;
- best owner abstraction: the transcendence-degree owner `Algebra.trdeg` of the intermediate field
  `ℚ⟮Real.exp 1, Real.pi⟯`.

Primitive data are the two generators `Real.exp 1` and `Real.pi` and the intermediate field they
generate. The `Fin 2` family in `K` is only bridge/view API into the canonical owner
`IsTranscendenceBasis` and the resulting invariant `Algebra.trdeg`.

Source/core/bridge triage:
- `source-facing`: the concrete field `ℚ(e, π)` and the question whether its transcendence degree
  is `1` or `2`;
- `core/canonical`: `Algebra.trdeg ℚ K`;
- `bridge/view`: the two-generator family in `K`, used only to invoke
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic` and then
  `IsTranscendenceBasis.cardinalMk_eq_trdeg`;
- `layer`: `source-facing`.
-/

local notation "K" => ℚ⟮Real.exp 1, Real.pi⟯

-- Proof sketch: exhibit a transcendental element of `K` over `ℚ` and then apply the canonical
-- owner lemma `trdeg_pos`, converting `0 < Algebra.trdeg ℚ K` into the equivalent lower bound
-- `1 ≤ Algebra.trdeg ℚ K`.
/-- Example 9.26.6: the field `ℚ(e, π)` has transcendence degree at least `1` over `ℚ`. -/
theorem rat_e_pi_field_trdeg_one_le :
    1 ≤ Algebra.trdeg ℚ K := by
  let πK : K := gen₂ ℚ (Real.exp 1) Real.pi
  have hπK : Transcendental ℚ πK := by
    rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective K ℝ)]
    simpa [πK] using real_pi_transcendental
  haveI : Algebra.Transcendental ℚ K := ⟨⟨πK, hπK⟩⟩
  simpa [Cardinal.one_le_iff_pos] using (trdeg_pos ℚ K)

-- Proof sketch: transport algebraic independence of `![Real.exp 1, Real.pi]` to the canonical
-- two-generator family in `K`, show that `K` is algebraic over the intermediate field generated
-- by that family, and conclude that this family is a transcendence basis. The equality
-- `Algebra.trdeg ℚ K = 2` is then the canonical basis-cardinality formula
-- `IsTranscendenceBasis.cardinalMk_eq_trdeg`.
/-- If `e` and `π` are algebraically independent over `ℚ`, then `ℚ(e, π)` has transcendence
degree `2` over `ℚ`. -/
theorem rat_e_pi_field_trdeg_eq_two_of_algebraicIndependent
    (h_alg : AlgebraicIndependent ℚ (![Real.exp 1, Real.pi] : Fin 2 → ℝ)) :
    Algebra.trdeg ℚ K = 2 := by
  let x : Fin 2 → K :=
    ![gen₁ ℚ (Real.exp 1) Real.pi, gen₂ ℚ (Real.exp 1) Real.pi]
  have hx_ind : AlgebraicIndependent ℚ x := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom ℚ K ℝ)
    convert h_alg using 1
    ext i
    fin_cases i
    · simpa [x] using (AdjoinPair.algebraMap_gen₁ ℚ (Real.exp 1) Real.pi : _)
    · simpa [x] using (AdjoinPair.algebraMap_gen₂ ℚ (Real.exp 1) Real.pi : _)
  have hx_top : IntermediateField.adjoin ℚ (Set.range x) = (⊤ : IntermediateField ℚ K) := by
    let L : IntermediateField ℚ ℝ := K
    apply IntermediateField.lift_injective L
    have hx_image : Subtype.val '' Set.range x = ({Real.exp 1, Real.pi} : Set ℝ) := by
      ext z
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨x 0, ⟨0, rfl⟩, rfl⟩
        · exact ⟨x 1, ⟨1, rfl⟩, rfl⟩
    calc
      IntermediateField.lift (IntermediateField.adjoin ℚ (Set.range x)) = L := by
        rw [IntermediateField.lift_adjoin, hx_image]
      _ = IntermediateField.lift (⊤ : IntermediateField ℚ K) := by
        ext z
        constructor
        · intro hz
          let zL : L := ⟨z, hz⟩
          exact (IntermediateField.mem_lift zL).2 (by trivial)
        · rintro ⟨zL, -, rfl⟩
          exact zL.2
  have hK_alg_if : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range x)) K := by
    rw [hx_top, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  have hK_alg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range x)) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp hK_alg_if
  have hbasis : IsTranscendenceBasis ℚ x :=
    hx_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hK_alg
  simpa using hbasis.cardinalMk_eq_trdeg.symm

/- Stacks Example 9.26.6 also records the meta-mathematical third point: it is currently unknown
whether `e` and `π` are algebraically independent over `ℚ`, so the exact value of
`Algebra.trdeg ℚ ℚ⟮Real.exp 1, Real.pi⟯` remains an open problem. -/

end

/-! ### Example_9_26_7 (from Chap09) -/
open IntermediateField
open IntermediateField.AdjoinSimple
open Polynomial

universe u v

section

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Example 9.26.7:
- primary domain: transcendence bases in simple transcendental field extensions;
- sampled owner declarations:
  `IsTranscendenceBasis`,
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`,
  `IntermediateField.isAlgebraic_adjoin_iff_top`,
  `IntermediateField.isAlgebraic_adjoin_simple`;
- best owner abstraction: `IsTranscendenceBasis F x`;
- primitive data: the simple extension `K := F⟮t⟯`, its distinguished generator `g := gen F t`,
  and the integral relation of `g` over `F⟮g ^ 2⟯`;
- derived API: the two singleton-family basis statements, obtained by combining algebraic
  independence with the corresponding algebraicity-over-adjoin claims.

Source/core/bridge triage:
- `source-facing`: the concrete singleton families generated by `t` and `t^2` inside `F(t)`;
- `core/canonical`: the owner predicate `IsTranscendenceBasis F x`;
- `bridge/view`: the algebraicity-over-adjoin facts used to invoke
  `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`;
- `layer`: `source-facing`.

The source-facing statement is retained, but the proof is phrased directly through the canonical
owners instead of spelling out duplicate singleton-range and top-extension boilerplate.
-/
/-- Helper for Example 9.26.7: the distinguished generator of `F⟮t⟯` already generates the whole
simple extension as an intermediate field over `F`. -/
lemma simple_extension_generator_adjoin_eq_top {t : E} :
    F⟮(gen F t : F⟮t⟯)⟯ = (⊤ : IntermediateField F F⟮t⟯) := by
  -- Compare the two intermediate fields after lifting them into the ambient extension `E`.
  apply IntermediateField.lift_injective (F⟮t⟯)
  calc
    IntermediateField.lift (F⟮(gen F t : F⟮t⟯)⟯) = F⟮t⟯ := by
      simpa using
        (IntermediateField.lift_adjoin_simple (F⟮t⟯) (gen F t : F⟮t⟯))
    _ = IntermediateField.lift (⊤ : IntermediateField F F⟮t⟯) := by
      simp

/-- Helper for Example 9.26.7: the generator `g` of `F⟮t⟯` is integral over the subfield
generated by `g²`. -/
lemma simple_extension_generator_isIntegral_over_square {t : E} :
    IsIntegral (F⟮((gen F t : F⟮t⟯) ^ 2)⟯) (gen F t : F⟮t⟯) := by
  let K := F⟮t⟯
  let g : K := gen F t
  let K₂ : IntermediateField F K := F⟮g ^ 2⟯
  let g₂ : K₂ := gen F (g ^ 2)
  have htwo_ne_zero : (2 : ℕ) ≠ 0 := by
    decide
  -- The quadratic relation `g² - g² = 0` gives a monic polynomial over `K₂`.
  refine ⟨X ^ 2 - C g₂, monic_X_pow_sub_C g₂ htwo_ne_zero, ?_⟩
  simp [K, g, K₂, g₂, pow_two]

/-- Helper for Example 9.26.7: the whole simple extension `F⟮t⟯` is algebraic over the subfield
generated by the square of its distinguished generator. -/
lemma simple_extension_isAlgebraic_over_square_generator {t : E} :
    Algebra.IsAlgebraic (F⟮((gen F t : F⟮t⟯) ^ 2)⟯) F⟮t⟯ := by
  let K := F⟮t⟯
  let g : K := gen F t
  let K₂ : IntermediateField F K := F⟮g ^ 2⟯
  have hFg_top : F⟮g⟯ = (⊤ : IntermediateField F K) := by
    simpa [K, g] using (simple_extension_generator_adjoin_eq_top (F := F) (t := t))
  have hK₂g_top : IntermediateField.adjoin K₂ ({g} : Set K) = ⊤ := by
    -- Once `g` generates `K` over `F`, it also generates `K` over the larger base field `K₂`.
    exact IntermediateField.adjoin_eq_top_of_adjoin_eq_top F hFg_top
  have htop : Algebra.IsAlgebraic K₂ (⊤ : IntermediateField K₂ K) := by
    -- Algebraicity of the simple adjoin over `K₂` transfers to the top intermediate field.
    rw [← hK₂g_top]
    simpa [K, g, K₂] using
      (IntermediateField.isAlgebraic_adjoin_simple
        (simple_extension_generator_isIntegral_over_square (F := F) (t := t)))
  let _ : Algebra.IsAlgebraic K₂ (⊤ : IntermediateField K₂ K) := htop
  -- The top intermediate field is canonically isomorphic to the ambient field `K`.
  simpa [K, K₂] using
    ((IntermediateField.topEquiv : (⊤ : IntermediateField K₂ K) ≃ₐ[K₂] K).isAlgebraic)

-- Proof sketch: let `K := F⟮t⟯` and `g := gen F t`. The canonical owner for both claims is
-- `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`. For `g`, transcendence descends
-- from `t` via `transcendental_algebraMap_iff`, and `K` is algebraic over the corresponding
-- polynomial subalgebra because it is the simple field extension generated by `g`. For `g^2`,
-- `Transcendental.pow` gives algebraic independence, and `g` is integral over `F⟮g^2⟯` as a root
-- of `X^2 - C (g^2)`, so `K/F⟮g^2⟯` is algebraic; `IntermediateField.isAlgebraic_adjoin_iff_top`
-- then converts this to the required `Algebra.adjoin`-based statement.
/-- Example 9.26.7: if `t` is transcendental over `F`, then inside the simple extension `F(t)`,
both the singleton family generated by `t` and the singleton family generated by `t²` are
transcendence bases. In particular, the algebraic/purely transcendental decomposition is not
unique. -/
theorem simple_extension_singleton_and_square_are_transcendence_bases {t : E}
    (ht : Transcendental F t) :
    IsTranscendenceBasis F (fun _ : Unit ↦ gen F t) ∧
    IsTranscendenceBasis F (fun _ : Unit ↦ (gen F t) ^ 2) := by
  let K := F⟮t⟯
  let g : K := gen F t
  let x : Unit → K := fun _ ↦ g
  let y : Unit → K := fun _ ↦ g ^ 2
  have hx_adjoin : IntermediateField.adjoin F (Set.range x) = F⟮g⟯ := by
    -- The singleton family `x` generates exactly the simple field `F⟮g⟯`.
    simp [x]
  have hy_adjoin : IntermediateField.adjoin F (Set.range y) = F⟮g ^ 2⟯ := by
    -- The same singleton-range rewrite identifies the square-generated field.
    simp [y]
  have hg_trans : Transcendental F g := by
    -- Transport transcendence of `t` through the faithful algebra map `K → E`.
    rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective K E)]
    simpa [K, g] using ht
  have hx_ind : AlgebraicIndependent F x := by
    -- Algebraic independence of a singleton is exactly transcendence of its value.
    rw [algebraicIndependent_singleton_iff Unit.unit]
    simpa [x] using hg_trans
  have hFg_top : F⟮g⟯ = (⊤ : IntermediateField F K) := by
    -- The previous helper identifies the simple adjoin with the whole extension.
    simpa [K, g] using (simple_extension_generator_adjoin_eq_top (F := F) (t := t))
  have hKx_alg : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range x)) K := by
    -- Rewrite the generated intermediate field to `⊤` and use surjectivity of `topEquiv`.
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hx_adjoin, hFg_top,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  have hx_basis : IsTranscendenceBasis F x := by
    -- The canonical criterion turns algebraic independence plus algebraicity into a basis.
    exact hx_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hKx_alg
  have hy_trans : Transcendental F (g ^ 2) :=
    hg_trans.pow (by decide : 0 < (2 : ℕ))
  have hy_ind : AlgebraicIndependent F y := by
    -- Again reduce singleton algebraic independence to transcendence of the value.
    rw [algebraicIndependent_singleton_iff Unit.unit]
    simpa [y] using hy_trans
  have hKy_alg_if : Algebra.IsAlgebraic (IntermediateField.adjoin F (Set.range y)) K := by
    -- The dedicated helper packages the quadratic algebraicity argument over `F⟮g²⟯`.
    rw [hy_adjoin]
    simpa [K, g] using
      (simple_extension_isAlgebraic_over_square_generator (F := F) (t := t))
  have hKy_alg : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range y)) K := by
    -- Convert from the intermediate-field version to the `Algebra.adjoin` owner.
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp hKy_alg_if
  have hy_basis : IsTranscendenceBasis F y := by
    -- Apply the same transcendence-basis criterion to the square-generated singleton.
    exact hy_ind.isTranscendenceBasis_iff_isAlgebraic.mpr hKy_alg
  have hx_basis' : IsTranscendenceBasis F (fun _ : Unit ↦ gen F t) := by
    simpa [x, g] using hx_basis
  have hy_basis' : IsTranscendenceBasis F (fun _ : Unit ↦ (gen F t) ^ 2) := by
    simpa [y, g] using hy_basis
  exact ⟨hx_basis', hy_basis'⟩

end

/-! ### Example_9_26_8 (from Chap09) -/
open scoped Manifold Topology
open CategoryTheory AlgebraicGeometry
open Set

noncomputable section

universe u v

section

set_option autoImplicit false

/-- A compact connected Riemann surface, modeled as a Hausdorff second-countable complex
one-manifold. The nontriviality needed for the category of nonconstant holomorphic maps is a
derived fact, not part of the object data. -/
structure CompactRiemannSurface where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) 1 carrier]
  [compactSpace : CompactSpace carrier]
  [connectedSpace : ConnectedSpace carrier]

attribute [instance] CompactRiemannSurface.topologicalSpace CompactRiemannSurface.t2Space
  CompactRiemannSurface.secondCountableTopology CompactRiemannSurface.chartedSpace
  CompactRiemannSurface.isManifold CompactRiemannSurface.compactSpace
  CompactRiemannSurface.connectedSpace

instance : CoeSort CompactRiemannSurface (Type u) := ⟨CompactRiemannSurface.carrier⟩

/-- Helper for Example 9.26.8: a compact Riemann surface has two distinct points. -/
lemma CompactRiemannSurface.exists_pair_ne (X : CompactRiemannSurface.{u}) :
    ∃ x y : X, x ≠ y := by
  letI : Nonempty X := inferInstance
  obtain ⟨x⟩ := ‹Nonempty X›
  let z : ℂ := extChartAt 𝓘(ℂ) x x
  -- Work in a chart around `x` and choose a second complex point in the punctured target.
  have hz_mem : z ∈ (extChartAt 𝓘(ℂ) x).target := by
    simpa [z] using mem_extChartAt_target (I := 𝓘(ℂ)) x
  have htarget : (extChartAt 𝓘(ℂ) x).target ∈ nhds z :=
    (isOpen_extChartAt_target (I := 𝓘(ℂ)) x).mem_nhds hz_mem
  have hpunct : (nhdsWithin z ({z}ᶜ : Set ℂ)).NeBot := inferInstance
  have hdiff : ((extChartAt 𝓘(ℂ) x).target \ {z} : Set ℂ).Nonempty := by
    refine hpunct.nonempty_of_mem ?_
    simpa using diff_mem_nhdsWithin_compl htarget ({z} : Set ℂ)
  rcases hdiff with ⟨w, hw_target, hw_ne⟩
  refine ⟨x, (extChartAt 𝓘(ℂ) x).symm w, ?_⟩
  intro h_eq
  -- Apply the chart to the supposed equality to contradict `w ≠ z`.
  have hchart :
      extChartAt 𝓘(ℂ) x x = extChartAt 𝓘(ℂ) x ((extChartAt 𝓘(ℂ) x).symm w) :=
    congrArg (extChartAt 𝓘(ℂ) x) h_eq
  have hw_eq : z = w := by
    calc
      z = extChartAt 𝓘(ℂ) x x := by
        rfl
      _ = extChartAt 𝓘(ℂ) x ((extChartAt 𝓘(ℂ) x).symm w) := hchart
      _ = w := PartialEquiv.right_inv (extChartAt 𝓘(ℂ) x) hw_target
  exact hw_ne hw_eq.symm

instance (X : CompactRiemannSurface.{u}) : Nontrivial X := by
  -- The chart argument above supplies the two distinct points needed for `Nontrivial`.
  obtain ⟨x, y, hxy⟩ := CompactRiemannSurface.exists_pair_ne X
  exact ⟨x, y, hxy⟩

/-- A holomorphic map of compact Riemann surfaces, formalized as a complex
manifold-differentiable map. -/
structure CompactRiemannSurfaceHom (X Y : CompactRiemannSurface.{u}) where
  toFun : X → Y
  mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun

instance (X Y : CompactRiemannSurface.{u}) : FunLike (CompactRiemannSurfaceHom X Y) X Y where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

@[ext]
lemma CompactRiemannSurfaceHom.ext {X Y : CompactRiemannSurface.{u}}
    {f g : CompactRiemannSurfaceHom X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

instance : Category CompactRiemannSurface where
  Hom X Y := CompactRiemannSurfaceHom X Y
  id X :=
    { toFun := id
      mdifferentiable := by
        simpa using
          (mdifferentiable_id : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X ↦ x)) }
  comp f g :=
    { toFun := g ∘ f
      mdifferentiable := g.mdifferentiable.comp f.mdifferentiable }
  id_comp f := by
    ext x
    rfl
  comp_id f := by
    ext x
    rfl
  assoc f g h := by
    ext x
    rfl

/-- A holomorphic map of compact Riemann surfaces is nonconstant if it separates two points. -/
def CompactRiemannSurfaceHom.IsNonconstant {X Y : CompactRiemannSurface.{u}}
    (f : CompactRiemannSurfaceHom X Y) : Prop :=
  ∃ x y, f x ≠ f y

/-- The morphism property cutting out nonconstant holomorphic maps of compact Riemann surfaces. -/
def CompactRiemannSurface.nonconstantHom :
    MorphismProperty CompactRiemannSurface :=
  fun _ _ f ↦ f.IsNonconstant

/-- Helper for Example 9.26.8: the chart expression of a holomorphic map is analytic at the chart
base point. -/
lemma CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X) :
    AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) := by
  let s : Set X := (extChartAt 𝓘(ℂ) x).source ∩ f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source
  -- Work on the chart neighborhood where both the source chart and the target chart of `f x`
  -- are valid, so the manifold differentiability statement becomes ordinary differentiability.
  have hs_mem : s ∈ 𝓝 x := by
    refine Filter.inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x) ?_
    exact (f.mdifferentiable x).continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) (f x))
  have hs_subset : s ⊆ (extChartAt 𝓘(ℂ) x).source := Set.inter_subset_left
  have hs_maps : Set.MapsTo f s (extChartAt 𝓘(ℂ) (f x)).source := by
    intro y hy
    exact hy.2
  have hmdiffOn : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f s := by
    intro y hy
    exact (f.mdifferentiable y).mdifferentiableWithinAt
  have hdiffOn :
      DifferentiableOn ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x '' s) := by
    exact
      (mdifferentiableOn_iff_of_subset_source' (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (x := x) (y := f x) (s := s) (f := f) hs_subset hs_maps).1 hmdiffOn
  have himage_mem : extChartAt 𝓘(ℂ) x '' s ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    exact extChartAt_image_nhds_mem_nhds_of_boundaryless (I := 𝓘(ℂ)) hs_mem
  -- Complex differentiability on a chart neighborhood upgrades to analyticity at the base point.
  exact hdiffOn.analyticAt himage_mem

/-- Helper for Example 9.26.8: once a holomorphic map is known to be open, compactness and
connectedness force surjectivity. -/
lemma CompactRiemannSurfaceHom.surjective_of_isOpenMap {X Y : CompactRiemannSurface.{u}}
    (f : CompactRiemannSurfaceHom X Y) (hf_open : IsOpenMap f.toFun) :
    Function.Surjective f := by
  -- Compactness of the source makes the range closed in the Hausdorff target.
  have hcont : Continuous f := f.mdifferentiable.continuous
  have hclosed : IsClosed (Set.range f) := by
    have hclosedMap : IsClosedMap f := hcont.isClosedMap
    simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ
  -- Openness gives the complementary half of the clopen range argument.
  have hopen : IsOpen (Set.range f) := hf_open.isOpen_range
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  letI : Nonempty X := inferInstance
  have hnonempty : (Set.range f).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨f x, ⟨x, rfl⟩⟩
  -- Connectedness of the target rules out a nonempty proper clopen subset.
  have hconnected :=
    (connectedSpace_iff_clopen (α := Y)).1 (inferInstance : ConnectedSpace Y)
  have hrange : Set.range f = Set.univ := by
    exact (hconnected.2 (Set.range f) hclopen).resolve_left <| by
      intro hempty
      exact hnonempty.ne_empty hempty
  exact Set.range_eq_univ.mp hrange

/-- Helper for Example 9.26.8: surjectivity of the first map lets one pull back nonconstant
witnesses through composition. -/
lemma CompactRiemannSurfaceHom.nonconstantCompositeWitnesses
    {X Y Z : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (g : CompactRiemannSurfaceHom Y Z) (hf : Function.Surjective f) (hg : g.IsNonconstant) :
    ∃ x y : X, g (f x) ≠ g (f y) := by
  -- Pull the distinct witness pair for `g` back along the surjective `f`.
  rcases hg with ⟨y₁, y₂, hy⟩
  rcases hf y₁ with ⟨x₁, rfl⟩
  rcases hf y₂ with ⟨x₂, rfl⟩
  exact ⟨x₁, x₂, hy⟩

/-- Helper for Example 9.26.8: a complex-analytic function that is constant on a nonempty open
subset of a preconnected domain is constant on the whole domain. -/
lemma analytic_eq_const_of_eqOn_nonempty_open {V W : Set ℂ} {g : ℂ → ℂ} {c : ℂ}
    (hg : AnalyticOnNhd ℂ g V) (hV : IsPreconnected V) (hWV : W ⊆ V) (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) (hW_const : Set.EqOn g (fun _ ↦ c) W) :
    Set.EqOn g (fun _ ↦ c) V := by
  rcases hW_nonempty with ⟨z₀, hz₀W⟩
  have hz₀V : z₀ ∈ V := hWV hz₀W
  -- Use the open patch to upgrade pointwise constancy near `z₀` to eventual equality.
  have hEventually : g =ᶠ[𝓝 z₀] fun _ ↦ c := by
    filter_upwards [hW_open.mem_nhds hz₀W] with z hz
    exact hW_const hz
  exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hV hz₀V hEventually

/-- Helper for Example 9.26.8: near the base chart point, the chart representative of a
holomorphic map is defined on the actual source/target validity domain. -/
lemma CompactRiemannSurfaceHom.chartValidity_eventuallyEq
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X) :
    (Set.univ : Set ℂ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ) x x)]
      ((extChartAt 𝓘(ℂ) x).target ∩
        (extChartAt 𝓘(ℂ) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source) : Set ℂ) := by
  -- Normalize the ambient neighborhood to the exact chart-validity set from the ext-chart API.
  simpa using
    (ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
      (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (s := Set.univ) (f := f) (x := x)
      (f.mdifferentiable x).continuousWithinAt)

/-- Helper for Example 9.26.8: if the chart representative of `f` is eventually constant at `x`,
then `f` is constant on an open neighborhood of `x`. -/
lemma CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (x : X)
    (hconst :
      ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ) x x),
        writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f z = extChartAt 𝓘(ℂ) (f x) (f x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.EqOn f (fun _ ↦ f x) U := by
  let validity : Set ℂ :=
    (extChartAt 𝓘(ℂ) x).target ∩
      (extChartAt 𝓘(ℂ) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ) (f x)).source)
  have hvalid : validity ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    have hvalid' : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ) x x), z ∈ validity := by
      filter_upwards [CompactRiemannSurfaceHom.chartValidity_eventuallyEq f x] with z hz
      exact hz.mp trivial
    exact hvalid'
  let eqSet : Set ℂ :=
    {z | writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f z = extChartAt 𝓘(ℂ) (f x) (f x)}
  have hmem : validity ∩ eqSet ∈ 𝓝 (extChartAt 𝓘(ℂ) x x) := by
    exact Filter.inter_mem hvalid (by simpa [eqSet] using hconst)
  rcases mem_nhds_iff.mp hmem with ⟨s, hs_sub, hs_open, hx_mem_s⟩
  let U : Set X := (chartAt ℂ x).source ∩ extChartAt 𝓘(ℂ) x ⁻¹' s
  refine ⟨U, ?_, ?_, ?_⟩
  · -- Pull the chart-open neighborhood back to the manifold.
    simpa [U] using isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x hs_open
  · -- The chart center belongs to the chosen neighborhood.
    exact ⟨mem_chart_source _ x, hx_mem_s⟩
  · intro y hy
    have hy_s : extChartAt 𝓘(ℂ) x y ∈ s := hy.2
    have hy_mem : extChartAt 𝓘(ℂ) x y ∈ validity ∩ eqSet := hs_sub hy_s
    have hy_targetSource :
        f ((extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y)) ∈
          (extChartAt 𝓘(ℂ) (f x)).source := hy_mem.1.2
    have hy_eqChart :
        writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f (extChartAt 𝓘(ℂ) x y) =
          extChartAt 𝓘(ℂ) (f x) (f x) := hy_mem.2
    have hy_source : y ∈ (extChartAt 𝓘(ℂ) x).source := by
      simpa [extChartAt_source] using hy.1
    have hy_symm :
        (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) = y :=
      PartialEquiv.left_inv (extChartAt 𝓘(ℂ) x) hy_source
    have hy_chart_symm :
        (chartAt ℂ x).symm ((chartAt ℂ x) y) = y := by
      simpa using hy_symm
    have hy_fx_source : f y ∈ (extChartAt 𝓘(ℂ) (f x)).source := by
      simpa [hy_chart_symm] using hy_targetSource
    have hchart_eq : extChartAt 𝓘(ℂ) (f x) (f y) = extChartAt 𝓘(ℂ) (f x) (f x) := by
      -- Rewrite the chart equality back to the actual target values.
      simpa [writtenInExtChartAt, Function.comp, hy_chart_symm] using hy_eqChart
    have hfy_eq : f y = f x := by
      have hfy_eq' := congrArg (fun z => (extChartAt 𝓘(ℂ) (f x)).symm z) hchart_eq
      calc
        f y = (extChartAt 𝓘(ℂ) (f x)).symm (extChartAt 𝓘(ℂ) (f x) (f y)) := by
          symm
          exact PartialEquiv.left_inv (extChartAt 𝓘(ℂ) (f x)) hy_fx_source
        _ = (extChartAt 𝓘(ℂ) (f x)).symm (extChartAt 𝓘(ℂ) (f x) (f x)) := hfy_eq'
        _ = f x := PartialEquiv.left_inv (extChartAt 𝓘(ℂ) (f x))
          (mem_extChartAt_source (I := 𝓘(ℂ)) (f x))
    simpa using hfy_eq

/-- Helper for Example 9.26.8: the local constancy locus of value `c` for `f`. -/
def CompactRiemannSurfaceHom.localConstancyLocus
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) (c : Y) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.EqOn f (fun _ ↦ c) U}

/-- Helper for Example 9.26.8: a chart sends an open subset of its source to an open subset of the
model space. -/
lemma CompactRiemannSurface.isOpen_image_chartAt
    {X : CompactRiemannSurface.{u}} (x : X) {U : Set X} (hU : IsOpen U)
    (hU_source : U ⊆ (chartAt ℂ x).source) :
    IsOpen (chartAt ℂ x '' U) := by
  -- Use the local homeomorphism property of the chart pointwise on the image.
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro z ⟨y, hy, rfl⟩
  exact (chartAt ℂ x).image_mem_nhds (hU_source hy) (hU.mem_nhds hy)

/-- Helper for Example 9.26.8: the local constancy locus is stable under taking closure. -/
lemma CompactRiemannSurfaceHom.mem_localConstancyLocus_of_mem_closure
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) {c : Y} {x : X}
    (hx :
      x ∈ closure (CompactRiemannSurfaceHom.localConstancyLocus f c)) :
    x ∈ CompactRiemannSurfaceHom.localConstancyLocus f c := by
  let eX := extChartAt 𝓘(ℂ) x
  let eY := extChartAt 𝓘(ℂ) (f x)
  let z0 : ℂ := eX x
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  have hfiber_subset :
      CompactRiemannSurfaceHom.localConstancyLocus f c ⊆ f ⁻¹' ({c} : Set Y) := by
    intro y hy
    rcases hy with ⟨U, _, hyU, hUconst⟩
    simpa using hUconst hyU
  have hxFiber : x ∈ closure (f ⁻¹' ({c} : Set Y)) :=
    closure_mono hfiber_subset hx
  have hfx : f x = c := by
    -- First pin down the value at the closure point using continuity and the closed fiber.
    exact ContinuousWithinAt.eq_const_of_mem_closure
      (f.mdifferentiable.continuous.continuousAt.continuousWithinAt) hxFiber
      (by intro y hy; simpa using hy)
  have hanalytic := CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt f x
  obtain ⟨r, hr, hBallAnalytic⟩ := hanalytic.exists_ball_analyticOnNhd
  let chartBall : Set X := (chartAt ℂ x).source ∩ eX ⁻¹' (Metric.ball z0 r)
  have hchartBall_open : IsOpen chartBall := by
    -- Work inside one genuine chart ball around the closure point.
    simpa [chartBall, eX] using
      isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x Metric.isOpen_ball
  have hxChartBall : x ∈ chartBall := by
    refine ⟨mem_chart_source _ x, ?_⟩
    exact (show z0 ∈ Metric.ball z0 r from Metric.mem_ball_self hr)
  obtain ⟨y, hyChartBall, hyLocus⟩ :=
    (mem_closure_iff_nhds.mp hx) chartBall (hchartBall_open.mem_nhds hxChartBall)
  rcases hyLocus with ⟨U, hU_open, hyU, hUconst⟩
  let patch : Set X := (((chartAt ℂ x).source ∩ U) ∩ eX ⁻¹' (Metric.ball z0 r))
  have hpatch_open : IsOpen patch := by
    -- Intersect the constancy patch with the chosen chart ball.
    simpa [patch, eX, extChartAt_source, inter_assoc, inter_left_comm, inter_comm] using
      hU_open.inter (isOpen_extChartAt_preimage (I := 𝓘(ℂ)) x Metric.isOpen_ball)
  have hyPatch : y ∈ patch := by
    exact ⟨⟨hyChartBall.1, hyU⟩, hyChartBall.2⟩
  let chartPatch : Set ℂ := chartAt ℂ x '' patch
  have hchartPatch_open : IsOpen chartPatch := by
    -- The chart sends the source patch to an open subset of the model space.
    exact CompactRiemannSurface.isOpen_image_chartAt x hpatch_open fun y hy ↦ hy.1.1
  have hchartPatch_nonempty : chartPatch.Nonempty := ⟨chartAt ℂ x y, ⟨y, hyPatch, rfl⟩⟩
  have hchartPatch_subset : chartPatch ⊆ Metric.ball z0 r := by
    rintro z ⟨w, hw, rfl⟩
    simpa [z0, eX, extChartAt_coe] using hw.2
  have hchartPatch_const :
      Set.EqOn g (fun _ ↦ eY (f x)) chartPatch := by
    -- On the transported open patch, the chart representative is literally constant.
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw_source : w ∈ (chartAt ℂ x).source := hw.1.1
    have hw_eq : f w = f x := by
      calc
        f w = c := hUconst hw.1.2
        _ = f x := hfx.symm
    have hw_chart_symm : (chartAt ℂ x).symm ((chartAt ℂ x) w) = w :=
      (chartAt ℂ x).left_inv hw_source
    simpa [g, eX, eY, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      Function.comp, hw_chart_symm, hw_eq]
  have hball_preconnected : IsPreconnected (Metric.ball z0 r) :=
    (convex_ball z0 r).isPreconnected
  rcases hBallAnalytic.is_constant_or_isOpen hball_preconnected with hconstBall | hopenBall
  · rcases hconstBall with ⟨w, hw⟩
    have hw0 : w = eY (f x) := by
      -- Normalize the constant by evaluating at the chart center.
      have hz0 : z0 ∈ Metric.ball z0 r := Metric.mem_ball_self hr
      have hz0_eval : g z0 = eY (f x) := by
        simp [g, z0, eX, eY, writtenInExtChartAt]
      exact (hw z0 hz0).symm.trans hz0_eval
    have hEventually :
        ∀ᶠ z in 𝓝 z0, g z = eY (f x) := by
      filter_upwards [Metric.ball_mem_nhds z0 hr] with z hz
      simpa [hw0] using hw z hz
    -- Turn chart constancy on a whole ball back into a manifold neighborhood of constancy.
    simpa [CompactRiemannSurfaceHom.localConstancyLocus, hfx, z0, g, eY] using
      CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt f x hEventually
  · have himage :
        g '' chartPatch = ({eY (f x)} : Set ℂ) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [hchartPatch_const hw]
      · intro hz
        rcases hchartPatch_nonempty with ⟨w, hw⟩
        have hz' : z = eY (f x) := by simpa using hz
        refine ⟨w, hw, ?_⟩
        have hw_const := hchartPatch_const hw
        simpa [hz'] using hw_const
    have hopenImage : IsOpen (g '' chartPatch) := by
      simpa [g, eX, eY, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
        Function.comp] using hopenBall chartPatch hchartPatch_subset hchartPatch_open
    have hsingletonOpen : IsOpen ({eY (f x)} : Set ℂ) := by
      simpa [himage] using hopenImage
    exact False.elim <| (not_isOpen_singleton (eY (f x))) hsingletonOpen

/-- Helper for Example 9.26.8: constancy on one nonempty open patch forces global constancy. -/
lemma CompactRiemannSurfaceHom.eq_const_of_eqOn_nonempty_open
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y) {c : Y} {U : Set X}
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) (hUconst : Set.EqOn f (fun _ ↦ c) U) :
    ∀ z : X, f z = c := by
  let S := CompactRiemannSurfaceHom.localConstancyLocus f c
  have hS_open : IsOpen S := by
    -- Any witness neighborhood at one point witnesses openness of the whole locus nearby.
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    rcases hx with ⟨V, hV_open, hxV, hVconst⟩
    exact Filter.mem_of_superset (hV_open.mem_nhds hxV) fun y hyV ↦
      ⟨V, hV_open, hyV, hVconst⟩
  have hS_closed : IsClosed S := by
    -- Closure stability from the chart-ball argument makes the locus closed.
    rw [← closure_eq_iff_isClosed]
    exact Set.Subset.antisymm
      (fun x hx ↦ CompactRiemannSurfaceHom.mem_localConstancyLocus_of_mem_closure f hx)
      subset_closure
  have hS_nonempty : S.Nonempty := by
    rcases hU_nonempty with ⟨x, hxU⟩
    exact ⟨x, U, hU_open, hxU, hUconst⟩
  have hS_univ : S = Set.univ := by
    let hconnected :=
      (connectedSpace_iff_clopen (α := X)).1 (inferInstance : ConnectedSpace X)
    exact (hconnected.2 S ⟨hS_closed, hS_open⟩).resolve_left <| by
      intro hS_empty
      exact hS_nonempty.ne_empty hS_empty
  intro z
  have hzS : z ∈ S := by simpa [hS_univ]
  rcases hzS with ⟨V, _, hzV, hVconst⟩
  exact hVconst hzV

/-- Helper for Example 9.26.8: a nonconstant holomorphic map satisfies the neighborhood
criterion for openness at every point. -/
lemma CompactRiemannSurfaceHom.nhdsLeMapAt_of_isNonconstant
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (hf : f.IsNonconstant) (x : X) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  let eX := extChartAt 𝓘(ℂ) x
  let eY := extChartAt 𝓘(ℂ) (f x)
  let z0 : ℂ := eX x
  let w0 : ℂ := eY (f x)
  let g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f
  rcases AnalyticAt.eventually_constant_or_nhds_le_map_nhds
      (CompactRiemannSurfaceHom.analyticAt_writtenInExtChartAt f x) with hconst | hmap
  · have hconst' :
        ∀ᶠ z in 𝓝 z0, g z = w0 := by
      have hz0_eval : g z0 = w0 := by
        simp [g, z0, w0, eX, eY, writtenInExtChartAt]
      filter_upwards [hconst] with z hz
      exact hz.trans hz0_eval
    rcases CompactRiemannSurfaceHom.eq_const_on_open_of_eventuallyEq_writtenInExtChartAt f x hconst'
      with ⟨U, hU_open, hxU, hUconst⟩
    -- Route correction: once the chart branch is locally constant, the new rigidity lemma
    -- upgrades that to global constancy and contradicts `hf`.
    have hglobal : ∀ z : X, f z = f x :=
      CompactRiemannSurfaceHom.eq_const_of_eqOn_nonempty_open f hU_open ⟨x, hxU⟩ hUconst
    rcases hf with ⟨a, b, hab⟩
    exact (hab ((hglobal a).trans (hglobal b).symm)).elim
  · have hmap' :
        Filter.map eY.symm (𝓝 w0) ≤ Filter.map (eY.symm ∘ g) (𝓝 z0) :=
      by
        change Filter.map eY.symm (𝓝 w0) ≤ Filter.map eY.symm (Filter.map g (𝓝 z0))
        simpa [Filter.map_map] using Filter.map_mono (m := eY.symm) hmap
    have hleft : Filter.map eY.symm (𝓝 w0) = 𝓝 (f x) := by
      simpa [eY, w0, extChartAt_coe, extChartAt_coe_symm] using
        (chartAt ℂ (f x)).symm_map_nhds_eq (mem_chart_source _ (f x))
    have hcongr :
        (eY.symm ∘ g) =ᶠ[𝓝 z0] (f ∘ eX.symm) := by
      -- On the chart-validity neighborhood, the target chart inverse cancels back to `f`.
      filter_upwards [CompactRiemannSurfaceHom.chartValidity_eventuallyEq f x] with z hz
      have hz' :
          z ∈ (eX.target ∩ eX.symm ⁻¹' (f ⁻¹' eY.source) : Set ℂ) := hz.mp trivial
      have hz_source : f (eX.symm z) ∈ eY.source := hz'.2
      have hz_source' : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f x)).source := by
        simpa [eX, eY, extChartAt_source, extChartAt_coe_symm, Function.comp] using hz_source
      have hz_cancel :
          (chartAt ℂ (f x)).symm ((chartAt ℂ (f x)) (f ((chartAt ℂ x).symm z))) =
            f ((chartAt ℂ x).symm z) :=
        (chartAt ℂ (f x)).left_inv hz_source'
      simpa [eX, eY, g, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
        Function.comp, hz_cancel]
    have hright :
        Filter.map (eY.symm ∘ g) (𝓝 z0) = Filter.map (f ∘ eX.symm) (𝓝 z0) :=
      Filter.map_congr hcongr
    have hsource : Filter.map (f ∘ eX.symm) (𝓝 z0) = Filter.map f (𝓝 x) := by
      change Filter.map f (Filter.map eX.symm (𝓝 z0)) = Filter.map f (𝓝 x)
      congr 1
      simpa [eX, z0, extChartAt_coe, extChartAt_coe_symm] using
        (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source _ x)
    -- Transport the complex open-mapping neighborhood inequality back through the source and
    -- target charts.
    calc
      𝓝 (f x) = Filter.map eY.symm (𝓝 w0) := hleft.symm
      _ ≤ Filter.map (eY.symm ∘ g) (𝓝 z0) := hmap'
      _ = Filter.map (f ∘ eX.symm) (𝓝 z0) := hright
      _ = Filter.map f (𝓝 x) := hsource

/-- Example 9.26.8: a nonconstant holomorphic map of compact Riemann surfaces is open. -/
lemma CompactRiemannSurfaceHom.isOpenMap_of_isNonconstant
    {X Y : CompactRiemannSurface.{u}} (f : CompactRiemannSurfaceHom X Y)
    (hf : f.IsNonconstant) : IsOpenMap f.toFun := by
  -- Route correction: the missing step was global rigidity from one open constancy patch.
  -- With that in place, the complex open-mapping dichotomy reduces pointwise to `nhds ≤ map nhds`.
  exact isOpenMap_iff_nhds_le.2 fun x ↦
    CompactRiemannSurfaceHom.nhdsLeMapAt_of_isNonconstant f hf x

instance : CompactRiemannSurface.nonconstantHom.IsMultiplicative where
  id_mem X := by
    -- The identity map is nonconstant because the object itself is nontrivial.
    obtain ⟨x, y, hxy⟩ := CompactRiemannSurface.exists_pair_ne X
    exact ⟨x, y, hxy⟩
  comp_mem f g hf hg := by
    -- Route correction: witness chasing is insufficient here, so first upgrade `f` to an open map.
    have hf_open : IsOpenMap f.toFun :=
      CompactRiemannSurfaceHom.isOpenMap_of_isNonconstant f hf
    -- Once `f` is open, compactness and connectedness force surjectivity, so the witness pair
    -- for `g` can be pulled back along `f`.
    simpa [CompactRiemannSurfaceHom.IsNonconstant] using
      CompactRiemannSurfaceHom.nonconstantCompositeWitnesses f g
        (CompactRiemannSurfaceHom.surjective_of_isOpenMap f hf_open) hg

/-- The category of compact Riemann surfaces with nonconstant holomorphic maps, realized as the
wide subcategory of holomorphic maps cut out by the nonconstancy property. -/
abbrev CompactRiemannSurfaceCat :=
  WideSubcategory CompactRiemannSurface.nonconstantHom

end

/-! ### Definition_9_26_9 (from Chap09) -/
-- Definition 9.26.9 currently reuses the purely transcendental extension API from Definition 9.26.1.

/-! ### Lemma_9_26_10 (from Chap09) -/
universe u v

section

variable {k : Type u} {k' : Type v}
variable [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] FractionRing.isScalarTower_liftAlgebra

open scoped MvRatFunc

/- Domain-style sampling for Lemma 9.26.10:
- primary domain: algebraic field extensions and the induced extension on rational function fields;
- sampled owner declarations:
  `MvPolynomial.algebraMvPolynomial`,
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial`;
- owner abstraction: the induced fraction-field algebra coming from the canonical algebra
  `MvPolynomial (Fin r) k →ₐ[k] MvPolynomial (Fin r) k'`, together with the mathlib owner theorem
  `rank_fractionRing_mvPolynomial`;
- primitive data: only the finite extension `k'/k` and the number of variables `r`;
- derived API: the finite-dimensional degree equality below.

Source/core/bridge triage:
- `source-facing`: the equality of degrees of rational function field extensions in `r` variables;
- `core/canonical`: `rank_fractionRing_mvPolynomial` plus the canonical `FractionRing.liftAlgebra`
  interface;
- `bridge/view`: the passage from rank to `finrank` by `Cardinal.toNat`.

The refined file keeps the public statement directly on the canonical owner theorem and uses only a
local module instance for elaboration support. -/

open Algebra.IsAlgebraic

noncomputable local instance (r : ℕ) : Module k⟮X_(Fin r)⟯ k'⟮X_(Fin r)⟯ :=
  (FractionRing.liftAlgebra (MvPolynomial (Fin r) k) k'⟮X_(Fin r)⟯).toModule

/-- Lemma 9.26.10: for a finite field extension `k'/k`, the induced extension of rational
function fields in `r` variables has degree `[k' : k]`, hence is finite. The source-facing
statement is derived from the canonical owner theorem `rank_fractionRing_mvPolynomial`, using the
standard induced fraction-field algebra `FractionRing.liftAlgebra`. -/
lemma finrank_fractionRing_mvPolynomial_eq_finrank (r : ℕ) :
    Module.finrank k⟮X_(Fin r)⟯ k'⟮X_(Fin r)⟯ = Module.finrank k k' := by
  simpa only [Module.finrank, Cardinal.toNat_lift] using
    congrArg Cardinal.toNat (rank_fractionRing_mvPolynomial (Fin r))

end

/-! ### Lemma_9_26_11 (from Chap09) -/
universe u v

section

open IntermediateField
open scoped algebraAdjoinAdjoin

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 9.26.11:
- primary domain: finitely generated field extensions and their relative algebraic closures;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `fg_top_iff`,
  `algebraicClosure`,
  `mem_algebraicClosure_iff`;
- owner abstraction: `Algebra.EssFiniteType k K` for finite generation, together with the
  canonical intermediate field `algebraicClosure k K`;
- primitive data: no new local data, since the theorem is about the existing owner object
  `algebraicClosure k K`;
- derived API: only the source-facing finite-dimensionality statement below.

Source/core/bridge triage:
- `source-facing`: Lemma 9.26.11 itself, asserting that the relative algebraic closure is finite
  over the base field for finitely generated extensions;
- `core/canonical`: the owner hypothesis `Algebra.EssFiniteType k K` and the canonical relative
  algebraic closure `algebraicClosure k K`;
- `bridge/view`: the identification of the textbook `FG` formulation with the owner hypothesis via
  `fg_top_iff`, already provided upstream.

The refined file keeps the theorem directly on `algebraicClosure k K`, without introducing any
parallel local wrapper for the same intermediate field, and reuses the upstream bridge from
`(⊤ : IntermediateField k K).FG` to `Algebra.EssFiniteType k K`. -/

/-- Helper for Lemma 9.26.11: a finitely generated field extension admits a finite
transcendence basis whose generated intermediate field has finite residual degree in `K`. -/
lemma exists_finTranscendenceBasis_finiteDimensional_over_adjoin
    [Algebra.EssFiniteType k K] :
    ∃ r, ∃ x : Fin r → K, IsTranscendenceBasis k x ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K := by
  classical
  obtain ⟨s, hs_fin, hs_top⟩ :=
    (IntermediateField.fg_def (S := (⊤ : IntermediateField k K))).mp
      (IntermediateField.fg_top k K)
  have hs_alg_field : Algebra.IsAlgebraic (IntermediateField.adjoin k s) K := by
    exact ⟨fun x ↦ by
      have hx_mem : x ∈ IntermediateField.adjoin k s := by
        simpa [hs_top] using (show x ∈ (⊤ : IntermediateField k K) from trivial)
      simpa using isAlgebraic_algebraMap (⟨x, hx_mem⟩ : IntermediateField.adjoin k s)⟩
  have hs_alg_ring : Algebra.IsAlgebraic (Algebra.adjoin k s) K := by
    exact
      (IntermediateField.isAlgebraic_adjoin_iff_top (F := k) (s := s)).mp hs_alg_field
  letI : Algebra.IsAlgebraic (Algebra.adjoin k s) K := hs_alg_ring
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) s
  have ht_fin : t.Finite := hs_fin.subset hts
  letI : Fintype t := ht_fin.fintype
  let r := Fintype.card t
  let e : Fin r ≃ t := (Fintype.equivFin t).symm
  let x : Fin r → K := fun i ↦ (e i : K)
  have hx : IsTranscendenceBasis k x := by
    -- Reindex the finite transcendence basis by `Fin r` once and keep that spelling.
    simpa [x, Function.comp] using
      ((isTranscendenceBasis_equiv e (f := ((↑) : t → K))).2 ht)
  have hx_range : Set.range x = t := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      simp [x]
  have hx_alg : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := by
    simpa [hx_range] using hx.isAlgebraic_field
  letI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := hx_alg
  letI : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (Set.range x)) K
  letI : Module.Finite (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨r, x, hx, ?_⟩
  -- Finite generation plus algebraicity over the basis field upgrades to finite-dimensionality.
  infer_instance

/-- Helper for Lemma 9.26.11: constant polynomials attached to a `k`-basis of `L` remain
linearly independent over the polynomial ring in the transcendence variables. -/
lemma constantBasisLinearIndependentOverPolynomial
    {L : Type v} [Field L] [Algebra k L] {r : ℕ} {ι : Type*} (b : Module.Basis ι k L) :
    LinearIndependent (MvPolynomial (Fin r) k)
      (fun i ↦ (MvPolynomial.C (b i) : MvPolynomial (Fin r) L)) := by
  classical
  -- Apply coefficient extraction monomial-by-monomial to reduce polynomial relations to
  -- coefficient relations in the original `k`-basis of `L`.
  rw [linearIndependent_iff]
  intro l hl
  ext i d
  have hcoeff :
      Finsupp.linearCombination k b
        (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)) = 0 := by
    have hcoeff := congrArg (MvPolynomial.coeff d) hl
    rw [Finsupp.linearCombination_apply] at hcoeff
    simp only [Finsupp.sum, Algebra.smul_def, mul_comm] at hcoeff
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
    simp only [MvPolynomial.coeff_C_mul] at hcoeff
    have hcoeff' : l.sum (fun a b_1 ↦ MvPolynomial.coeff d b_1 • b a) = 0 := by
      simpa [Finsupp.sum, Algebra.smul_def, mul_comm] using hcoeff
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      (show (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)).sum (fun x a ↦ a • b x) = 0 by
        rw [Finsupp.sum_mapRange_index]
        · exact hcoeff'
        · intro a
          simp)
  have hzero := (linearIndependent_iff.mp b.linearIndependent)
    (l.mapRange (fun p ↦ MvPolynomial.coeff d p) (by simp)) hcoeff
  exact congrArg (fun f => f i) hzero

/-- Lemma 9.26.11: the basis field generated by a transcendence basis is linearly disjoint from a
finite algebraic coefficient field. This is the bridge used by the final finite-dimensionality
argument in the same file. -/
lemma basisFieldLinearDisjointOfAlgebraic
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K} (hx : IsTranscendenceBasis k x) :
    (IntermediateField.adjoin k (Set.range x)).LinearDisjoint L := by
  classical
  let kX := FractionRing (MvPolynomial (Fin r) k)
  let LX := FractionRing (MvPolynomial (Fin r) L)
  letI : Algebra kX LX := FractionRing.liftAlgebra (MvPolynomial (Fin r) k) LX
  letI : Module kX LX := (FractionRing.liftAlgebra (MvPolynomial (Fin r) k) LX).toModule
  let b := Module.finBasis k L
  let hxL : IsTranscendenceBasis L x :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_iff (R := k) (S := L) (x := x)).mp hx
  -- Route correction: transport only the basis-independence witness from `L(X)` into `K`,
  -- and compute the image of `k(X)` once at the end.
  have hconst : LinearIndependent kX (fun i ↦ algebraMap L LX (b i)) := by
    -- Localize the polynomial-basis independence from `k[X]` to the rational function field.
    simpa [kX, LX] using
      (LinearIndependent.localization_localization
        (R := MvPolynomial (Fin r) k)
        (A := MvPolynomial (Fin r) L)
        (Rₛ := kX)
        (Aₛ := LX)
        (S := nonZeroDivisors (MvPolynomial (Fin r) k))
        (v := fun i ↦ (MvPolynomial.C (b i) : MvPolynomial (Fin r) L))
        (constantBasisLinearIndependentOverPolynomial (k := k) (L := L) (r := r) b))
  let eL : LX →ₐ[L] ↥(IntermediateField.adjoin L (Set.range x)) :=
    hxL.1.aevalEquivField.toAlgHom
  let jLt : LX →ₐ[L] ↥(⊤ : IntermediateField L K) :=
    (IntermediateField.inclusion (show IntermediateField.adjoin L (Set.range x) ≤ ⊤ by
      exact le_top)).comp eL
  let jL : LX →ₐ[L] K := IntermediateField.topEquiv.toAlgHom.comp jLt
  let j : kX →ₐ[k] K :=
    (jL.restrictScalars k).comp (IsScalarTower.toAlgHom k kX LX)
  let ej := AlgEquiv.ofInjectiveField j
  have hfrac (q : MvPolynomial (Fin r) k) :
      (algebraMap kX LX) ((algebraMap (MvPolynomial (Fin r) k) kX) q) =
        algebraMap (MvPolynomial (Fin r) k) LX q := by
    -- Rewrite the `k(X) -> L(X)` map as the canonical fraction-ring lift on `k[X]`.
    rw [FractionRing.algebraMap_liftAlgebra (R := MvPolynomial (Fin r) k) (K := LX)]
    simpa [kX, LX] using
      (IsFractionRing.lift_algebraMap
        (A := MvPolynomial (Fin r) k)
        (K := kX)
        (L := LX)
        (g := algebraMap (MvPolynomial (Fin r) k) LX)
        (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin r) k) LX) q)
  have hpolyMap :
      algebraMap (MvPolynomial (Fin r) k) LX =
        ((algebraMap (MvPolynomial (Fin r) L) LX).comp
          (MvPolynomial.map (algebraMap k L))) := by
    -- Identify the polynomial coefficient extension `k[X] -> L[X] -> L(X)`.
    apply MvPolynomial.ringHom_ext
    · intro a
      rfl
    · intro i
      rfl
  have hmapAeval (p : MvPolynomial (Fin r) k) :
      jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
          (MvPolynomial.map (algebraMap k L))) p) =
        (MvPolynomial.aeval x) p := by
    -- Push the coefficient-extended polynomial through the `L`-based `aevalEquivField`,
    -- then collapse the coefficient extension by the tower `k -> L -> K`.
    let q : MvPolynomial (Fin r) L := MvPolynomial.map (algebraMap k L) p
    have hq :
        (((algebraMap (MvPolynomial (Fin r) L) LX).comp
            (MvPolynomial.map (algebraMap k L))) p) =
          algebraMap (MvPolynomial (Fin r) L) LX q := by
      rfl
    rw [hq]
    calc
      jL ((algebraMap (MvPolynomial (Fin r) L) LX) q) = (MvPolynomial.aeval x) q := by
        -- Unfold the composite `L(X) -> K` only once, down to the computation rule for
        -- `aevalEquivField` on coefficient-extended polynomials.
        change ↑(hxL.1.aevalEquivField ((algebraMap (MvPolynomial (Fin r) L) LX) q)) =
          (MvPolynomial.aeval x) q
        exact AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe (hx := hxL.1) (a := q)
      _ = (MvPolynomial.aeval x) p := by
        simpa [q] using (MvPolynomial.aeval_map_algebraMap (A := L) (x := x) p)
  have hj :
      RingHom.comp (j : kX →+* K) (algebraMap (MvPolynomial (Fin r) k) kX) =
        ((MvPolynomial.aeval x : MvPolynomial (Fin r) k →ₐ[k] K) :
          MvPolynomial (Fin r) k →+* K) := by
    -- Compare the two fraction-field lifts by reducing both to the same polynomial map.
    apply MvPolynomial.ringHom_ext
    · intro a
      calc
        j ((algebraMap (MvPolynomial (Fin r) k) kX) (MvPolynomial.C a))
            = jL ((algebraMap (MvPolynomial (Fin r) k) LX) (MvPolynomial.C a)) := by
                simp [j, hfrac (MvPolynomial.C a)]
        _ = jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
              (MvPolynomial.map (algebraMap k L))) (MvPolynomial.C a)) := by
                rw [hpolyMap]
        _ = (MvPolynomial.aeval x) (MvPolynomial.C a) := by
          exact hmapAeval (MvPolynomial.C a)
    · intro i
      calc
        j ((algebraMap (MvPolynomial (Fin r) k) kX) (MvPolynomial.X i))
            = jL ((algebraMap (MvPolynomial (Fin r) k) LX) (MvPolynomial.X i)) := by
                simp [j, hfrac (MvPolynomial.X i)]
        _ = jL (((algebraMap (MvPolynomial (Fin r) L) LX).comp
              (MvPolynomial.map (algebraMap k L))) (MvPolynomial.X i)) := by
                rw [hpolyMap]
        _ = (MvPolynomial.aeval x) (MvPolynomial.X i) := by
          exact hmapAeval (MvPolynomial.X i)
  have hjRange : j.fieldRange = IntermediateField.adjoin k (Set.range x) := by
    -- Compute the image of `k(X)` in `K` from the polynomial map `aeval x`.
    exact IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (f := j) (g := MvPolynomial.aeval x) hj
      (Algebra.adjoin_range_eq_range_aeval k x).symm
  have hmap :
      LinearIndependent j.fieldRange
        (jL.toRingHom.toAddMonoidHom ∘ fun i ↦ algebraMap L LX (b i)) := by
    -- Change scalars from `k(X)` to the actual image field `j.fieldRange`.
    refine LinearIndependent.map_of_injective_injectiveₛ hconst ej.symm
      jL.toRingHom.toAddMonoidHom ej.symm.injective jL.injective ?_
    intro z m
    change jL ((algebraMap kX LX (ej.symm z)) * m) = z * jL m
    rw [map_mul]
    have hz : jL (algebraMap kX LX (ej.symm z)) = z := by
      change j (ej.symm z) = ↑z
      exact congrArg Subtype.val (ej.apply_symm_apply z)
    simpa [Algebra.smul_def, hz]
  have hK : LinearIndependent (IntermediateField.adjoin k (Set.range x)) (algebraMap L K ∘ b) := by
    -- The transported family is exactly the image of the original `k`-basis of `L` inside `K`.
    rw [← hjRange]
    convert hmap using 1
    ext i
    exact (jL.commutes (b i)).symm
  -- The basis criterion now closes linear disjointness over the actual basis field `k(x)`.
  exact IntermediateField.LinearDisjoint.of_basis_right' b hK

/-- Helper for Lemma 9.26.11: once the basis field is linearly disjoint from `L`, the standard
adjoin-rank formula bounds `[L : k]` by the residual degree over the basis field. -/
lemma finrankLeOfBasisFieldLinearDisjoint
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K}
    [FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K]
    (hld : (IntermediateField.adjoin k (Set.range x)).LinearDisjoint L) :
    Module.finrank k L ≤ Module.finrank (IntermediateField.adjoin k (Set.range x)) K := by
  let F := IntermediateField.adjoin k (Set.range x)
  let G : IntermediateField F K :=
    IntermediateField.extendScalars
      (show F ≤ (IntermediateField.adjoin L (F : Set K)).restrictScalars k from
        IntermediateField.subset_adjoin L (F : Set K))
  -- Convert linear disjointness into an exact rank computation for the adjoined coefficient field.
  have hG_rank : Module.rank F G = Module.rank k L := by
    simpa [F, G] using
      IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_right_of_isAlgebraic_right
        (A := F) (E := K) (L := L) hld
  have hG_finrank : Module.finrank F G = Module.finrank k L := by
    apply Nat.cast_injective (R := Cardinal)
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact hG_rank
  -- The tower law then bounds the degree of `L / k` by the residual degree of `K / F`.
  have : FiniteDimensional G K := FiniteDimensional.right F G K
  have hmul : Module.finrank F G * Module.finrank G K = Module.finrank F K :=
    Module.finrank_mul_finrank F G K
  have hpos : 0 < Module.finrank G K := Module.finrank_pos
  have hle : Module.finrank F G ≤ Module.finrank F K := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_right _ hpos
  simpa [F] using hG_finrank ▸ hle

/-- Helper for Lemma 9.26.11: after adjoining a finite transcendence basis, every finite
algebraic extension of `k` acting on `K` has degree bounded by the residual degree of `K` over the
basis field. -/
lemma finrank_algebraicField_le_finrank_over_basis
    {L : Type v} [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K]
    [FiniteDimensional k L] [Algebra.IsAlgebraic k L]
    {r : ℕ} {x : Fin r → K} (hx : IsTranscendenceBasis k x)
    [FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K] :
    Module.finrank k L ≤ Module.finrank (IntermediateField.adjoin k (Set.range x)) K := by
  -- Reduce the source statement to the single remaining linearly disjointness bridge.
  exact finrankLeOfBasisFieldLinearDisjoint
    (k := k) (K := K) (L := L) (x := x)
    (basisFieldLinearDisjointOfAlgebraic (k := k) (K := K) (L := L) hx)

/-- Final conclusion for Lemma 9.26.11: if `K/k` is a finitely generated field extension, then the
relative algebraic closure of `k` in `K` is finite over `k`. The source-facing theorem uses the
canonical owner `[Algebra.EssFiniteType k K]` for finite generation. -/
-- Proof sketch: choose a transcendence basis of `K/k`; then Lemma 9.26.10 identifies every finite
-- subextension of `algebraicClosure k K` with a finite extension of the corresponding rational
-- function field of uniformly bounded degree. This bounds the degrees of all finite intermediate
-- subextensions of `algebraicClosure k K / k`, from which finite-dimensionality follows.
lemma finiteDimensional_algebraicClosure [Algebra.EssFiniteType k K] :
    FiniteDimensional k (algebraicClosure k K) := by
  classical
  obtain ⟨r, x, hx, hfdK⟩ :=
    exists_finTranscendenceBasis_finiteDimensional_over_adjoin (k := k) (K := K)
  let F := IntermediateField.adjoin k (Set.range x)
  by_contra hnfd
  letI : Algebra.IsAlgebraic k ↥(algebraicClosure k K) := algebraicClosure.isAlgebraic k K
  obtain ⟨L0, hL0fd, hL0gt⟩ :=
    IntermediateField.exists_lt_finrank_of_infinite_dimensional
      (F := k) (E := ↥(algebraicClosure k K)) hnfd (Module.finrank F K)
  let f0 : ↥L0 →ₐ[k] ↥(⊤ : IntermediateField k ↥(algebraicClosure k K)) :=
    IntermediateField.inclusion (show L0 ≤ ⊤ by exact le_top)
  let f1 : ↥(⊤ : IntermediateField k ↥(algebraicClosure k K)) →ₐ[k] ↥(algebraicClosure k K) :=
    IntermediateField.topEquiv.toAlgHom
  let f2 : ↥(algebraicClosure k K) →ₐ[k] ↥(⊤ : IntermediateField k K) :=
    IntermediateField.inclusion (show algebraicClosure k K ≤ ⊤ by exact le_top)
  let f3 : ↥(⊤ : IntermediateField k K) →ₐ[k] K := IntermediateField.topEquiv.toAlgHom
  let f : ↥L0 →ₐ[k] K := f3.comp (f2.comp (f1.comp f0))
  letI : Algebra ↥L0 K := f.toAlgebra
  letI : IsScalarTower k ↥L0 K := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro a
    rfl
  letI : FiniteDimensional k ↥L0 := hL0fd
  have hbound :
      Module.finrank k ↥L0 ≤ Module.finrank F K := by
    -- Route correction: once the finite algebraic witness is viewed inside `K`,
    -- the source proof reduces to the single bounded-degree lemma above.
    simpa [F] using
      finrank_algebraicField_le_finrank_over_basis
        (k := k) (K := K) (L := ↥L0) (x := x) hx
  exact (not_lt_of_ge hbound) hL0gt

end
