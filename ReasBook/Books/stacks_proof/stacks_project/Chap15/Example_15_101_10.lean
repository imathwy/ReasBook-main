import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_90_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open MvPowerSeries

universe u

attribute [local instance] CategoryTheory.HasExt.standard

namespace IadicFiniteModuleSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The quotient ring `A / I^n` at stage `n`. This local copy avoids importing the later remark
file while keeping the stage notation used by Example `15.101.10`. -/
abbrev stageRing (n : ℕ+) :=
  A ⧸ I ^ (n : ℕ)

end IadicFiniteModuleSystem

section

/- Domain-style sampling for Example 15.101.10:
- primary domain: commutative algebra of the nodal complete local ring, its `I`-power quotients,
  the induced quotient modules, and the resulting `Ext²` groups in `ModuleCat`;
- sampled owner declarations:
  `MvPowerSeries`,
  `IadicFiniteModuleSystem.stageRing`,
  `ModuleCat.of`,
  `CategoryTheory.Abelian.Ext`;
- best owner abstraction:
  `source-facing`: the nodal ring `A = k[[x,y]] / (xy)`, the ideal `I = (x)`, the module
    `M = N = A / (y)`, and the reduced modules `M_n = N_n = M / I^n M`;
  `core/canonical`: quotient rings via ideals, quotient modules via submodules, the chapter owner
    `stageRing`, and the ambient `Ext`;
  `bridge/view`: the stagewise quotient module over `A_n`, which should be expressed directly from
    `stageRing` rather than via a parallel local stage-ring owner;
- primitive data: the nodal ring, its generators `x, y`, the ideals `(x)` and `(y)`, and the
  quotient module `A / (y)`;
- derived API: the reduced stage modules and the ambient/stagewise `Ext²` groups appearing in the
  counterexample theorem. -/

/-- The two-variable formal power series ring `k[[x,y]]`. -/
abbrev nodalPowerSeriesRing (k : Type u) [Field k] : Type u :=
  MvPowerSeries (Fin 2) k

/-- The nodal relation `xy` inside `k[[x,y]]`. -/
abbrev nodalRelation (k : Type u) [Field k] : nodalPowerSeriesRing k :=
  X (0 : Fin 2) * X (1 : Fin 2)

/-- The nodal complete local ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalRing (k : Type u) [Field k] : Type u :=
  nodalPowerSeriesRing k ⧸
    Ideal.span ({ nodalRelation k } : Set (nodalPowerSeriesRing k))

/-- The image of `x` in the quotient ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalX (k : Type u) [Field k] : nodalRing k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2))

/-- The image of `y` in the quotient ring `A = k[[x,y]] / (xy)`. -/
abbrev nodalY (k : Type u) [Field k] : nodalRing k :=
  Ideal.Quotient.mk _ (X (1 : Fin 2))

/-- The ideal `I = (x)` in the nodal ring `A`. -/
abbrev nodalIdealX (k : Type u) [Field k] : Ideal (nodalRing k) :=
  Ideal.span ({ nodalX k } : Set (nodalRing k))

/-- The ideal `(y)` in the nodal ring `A`. -/
abbrev nodalIdealY (k : Type u) [Field k] : Ideal (nodalRing k) :=
  Ideal.span ({ nodalY k } : Set (nodalRing k))

/-- The module `M = N = A / (y)` used in the counterexample. -/
abbrev nodalQuotientModule (k : Type u) [Field k] : ModuleCat (nodalRing k) :=
  ModuleCat.of (nodalRing k) ((nodalRing k) ⧸ nodalIdealY k)

/-- Helper for Example 15.101.10: the companion quotient module `A / (x)` appearing in the
alternating two-step resolution. -/
abbrev nodalXQuotientModule (k : Type u) [Field k] : ModuleCat (nodalRing k) :=
  ModuleCat.of (nodalRing k) ((nodalRing k) ⧸ nodalIdealX k)

/-- The reduced stage `M_n = N_n = M / I^n M`, viewed as a module over `A_n = A / I^n`. -/
abbrev nodalStageModule (k : Type u) [Field k] (n : ℕ+) :
    ModuleCat (IadicFiniteModuleSystem.stageRing (nodalRing k) (nodalIdealX k) n) :=
  ModuleCat.of (IadicFiniteModuleSystem.stageRing (nodalRing k) (nodalIdealX k) n) <|
    (nodalQuotientModule k) ⧸
      (((nodalIdealX k) ^ (n : ℕ)) • (⊤ : Submodule (nodalRing k) (nodalQuotientModule k)))

variable (k : Type u) [Field k]

/-- Helper for Example 15.101.10: the nodal relation forces `xy = 0` in the quotient ring
`A = k[[x,y]] / (xy)`. -/
theorem nodal_x_mul_nodal_y :
    nodalX k * nodalY k = (0 : nodalRing k) := by
  -- Unfold the quotient generators so the goal is the defining relation of the quotient ring.
  change
    Ideal.Quotient.mk (Ideal.span ({nodalRelation k} : Set (nodalPowerSeriesRing k)))
      ((X (0 : Fin 2)) * (X (1 : Fin 2))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  -- The product `X 0 * X 1` is exactly the chosen generator of the relation ideal.
  exact Ideal.subset_span rfl

/-- Helper for Example 15.101.10: the class of `y` annihilates the quotient module
`M = A / (y)`. -/
theorem nodal_y_smul_eq_zero_on_quotient (z : nodalQuotientModule k) :
    (nodalY k) • z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Reduce to the statement that every multiple of `y` lies in the ideal `(y)`.
  change Ideal.Quotient.mk (nodalIdealY k) (nodalY k * a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simpa [mul_comm] using
    (Ideal.mul_mem_left (nodalIdealY k) a
      (Ideal.subset_span (by simp : nodalY k ∈ ({nodalY k} : Set (nodalRing k)))))

/-- Helper for Example 15.101.10: the image of multiplication by `y` on the nodal ring is the
principal ideal `(y)`. -/
theorem nodal_mulRight_y_range_eq_idealY :
    LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k)) = nodalIdealY k := by
  -- Identify the range with the principal-ideal multiple `yA` and then unfold the principal ideal.
  ext z
  constructor
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨a, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · intro hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨a, rfl⟩
    refine LinearMap.mem_range.mpr ⟨a, ?_⟩
    simp [LinearMap.mulRight_apply, mul_comm]

/-- Helper for Example 15.101.10: the image of multiplication by `x` on the nodal ring is the
principal ideal `(x)`. -/
theorem nodal_mulRight_x_range_eq_idealX :
    LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalX k)) = nodalIdealX k := by
  -- The same principal-ideal computation works for the `x`-row of the periodic resolution.
  ext z
  constructor
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨a, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · intro hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨a, rfl⟩
    refine LinearMap.mem_range.mpr ⟨a, ?_⟩
    simp [LinearMap.mulRight_apply, mul_comm]

/-- Helper for Example 15.101.10: the quotient map `A → A / (y)` has kernel `(y)`. -/
theorem nodal_quotient_by_y_ker :
    LinearMap.ker ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap) =
      nodalIdealY k := by
  -- The linear kernel is the usual quotient kernel expressed in module language.
  ext z
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Helper for Example 15.101.10: the quotient map `A → A / (x)` has kernel `(x)`. -/
theorem nodal_quotient_by_x_ker :
    LinearMap.ker ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealX k)).toLinearMap) =
      nodalIdealX k := by
  -- The linear kernel is again the defining ideal of the quotient module.
  ext z
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Helper for Example 15.101.10: the source row `A --y→ A → A/(y) → 0` is exact. -/
theorem nodal_y_quotient_row_exact :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.mulRight (nodalRing k) (nodalY k)))
      (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap))
      (by
        -- The quotient map kills every `y`-multiple because those lie in `(y)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun a ↦ by
          change Ideal.Quotient.mk (nodalIdealY k) (a * nodalY k) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))).Exact := by
  let S : ShortComplex (ModuleCat (nodalRing k)) :=
    ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.mulRight (nodalRing k) (nodalY k)))
      (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap))
      (by
        -- Package the compositional zero relation into the canonical short-complex owner.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun a ↦ by
          change Ideal.Quotient.mk (nodalIdealY k) (a * nodalY k) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  change S.Exact
  -- Exactness reduces to the concrete equality `range(* y) = ker(A → A/(y))`.
  rw [S.moduleCat_exact_iff_range_eq_ker]
  simpa [S] using
    (nodal_mulRight_y_range_eq_idealY (k := k)).trans (nodal_quotient_by_y_ker (k := k)).symm

/-- Helper for Example 15.101.10: the companion row `A --x→ A → A/(x) → 0` is exact. -/
theorem nodal_x_quotient_row_exact :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.mulRight (nodalRing k) (nodalX k)))
      (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealX k)).toLinearMap))
      (by
        -- The quotient map kills every `x`-multiple because those lie in `(x)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun a ↦ by
          change Ideal.Quotient.mk (nodalIdealX k) (a * nodalX k) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))).Exact := by
  let S : ShortComplex (ModuleCat (nodalRing k)) :=
    ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.mulRight (nodalRing k) (nodalX k)))
      (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealX k)).toLinearMap))
      (by
        -- Package the compositional zero relation into the canonical short-complex owner.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun a ↦ by
          change Ideal.Quotient.mk (nodalIdealX k) (a * nodalX k) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  change S.Exact
  -- Exactness reduces to the concrete equality `range(* x) = ker(A → A/(x))`.
  rw [S.moduleCat_exact_iff_range_eq_ker]
  simpa [S] using
    (nodal_mulRight_x_range_eq_idealX (k := k)).trans (nodal_quotient_by_x_ker (k := k)).symm

/-- Helper for Example 15.101.10: the ambient variables `X 0` and `X 1` are nonzero in the
two-variable formal power series ring before passing to the nodal quotient. -/
private theorem nodal_powerSeries_variable_ne_zero (i : Fin 2) :
    (X i : nodalPowerSeriesRing k) ≠ 0 := by
  -- Compare the coefficient of the unique degree-one monomial supported at `i`.
  intro hzero
  have hcoeff := congrArg (fun f : nodalPowerSeriesRing k ↦ coeff (Finsupp.single i 1) f) hzero
  simpa using hcoeff

/-- Helper for Example 15.101.10: multiplication by `y` on the nodal ring has kernel equal to the
image of multiplication by `x`. This is the source middle exactness for
`0 → A/(x) → A --y→ A → A/(y) → 0`. -/
theorem nodal_mulRight_y_ker_eq_range_x :
    LinearMap.ker (LinearMap.mulRight (nodalRing k) (nodalY k)) =
      LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalX k)) := by
  let I : Ideal (nodalPowerSeriesRing k) :=
    Ideal.span ({nodalRelation k} : Set (nodalPowerSeriesRing k))
  ext z
  constructor
  · intro hz
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    -- Work upstairs in `k[[x,y]]`: the quotient condition means `f * Y` lies in `(XY)`.
    change (LinearMap.mulRight (nodalRing k) (nodalY k)) (Ideal.Quotient.mk I f) = 0 at hz
    change Ideal.Quotient.mk I (f * X (1 : Fin 2)) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨g, hg⟩
    -- Cancel the nonzero factor `Y` in the ambient domain to recover divisibility by `X`.
    have hmul : (f - g * X (0 : Fin 2)) * X (1 : Fin 2) = 0 := by
      rw [sub_mul, hg]
      simp [nodalRelation, mul_assoc, mul_left_comm, mul_comm]
    have hcancel : f - g * X (0 : Fin 2) = 0 := by
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · exact hzero
      · exact (nodal_powerSeries_variable_ne_zero (k := k) (1 : Fin 2) hzero).elim
    have hf : f = g * X (0 : Fin 2) := sub_eq_zero.mp hcancel
    refine LinearMap.mem_range.mpr ⟨Ideal.Quotient.mk I g, ?_⟩
    -- Descend the recovered `X`-divisibility to the quotient ring.
    change Ideal.Quotient.mk I (g * X (0 : Fin 2)) = Ideal.Quotient.mk I f
    simpa [hf]
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨a, rfl⟩
    -- Every `x`-multiple is killed by `y` because `xy = 0` in the nodal quotient.
    change (LinearMap.mulRight (nodalRing k) (nodalY k))
        ((LinearMap.mulRight (nodalRing k) (nodalX k)) a) = 0
    simp [LinearMap.mulRight_apply, mul_assoc, nodal_x_mul_nodal_y]

/-- Helper for Example 15.101.10: multiplication by `x` on the nodal ring has kernel equal to the
image of multiplication by `y`. This is the companion middle exactness for
`0 → A/(y) → A --x→ A → A/(x) → 0`. -/
theorem nodal_mulRight_x_ker_eq_range_y :
    LinearMap.ker (LinearMap.mulRight (nodalRing k) (nodalX k)) =
      LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k)) := by
  let I : Ideal (nodalPowerSeriesRing k) :=
    Ideal.span ({nodalRelation k} : Set (nodalPowerSeriesRing k))
  ext z
  constructor
  · intro hz
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    -- Work upstairs in `k[[x,y]]`: the quotient condition means `f * X` lies in `(XY)`.
    change (LinearMap.mulRight (nodalRing k) (nodalX k)) (Ideal.Quotient.mk I f) = 0 at hz
    change Ideal.Quotient.mk I (f * X (0 : Fin 2)) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨g, hg⟩
    -- Cancel the nonzero factor `X` in the ambient domain to recover divisibility by `Y`.
    have hmul : (f - g * X (1 : Fin 2)) * X (0 : Fin 2) = 0 := by
      rw [sub_mul, hg]
      simp [nodalRelation, mul_assoc, mul_left_comm, mul_comm]
    have hcancel : f - g * X (1 : Fin 2) = 0 := by
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · exact hzero
      · exact (nodal_powerSeries_variable_ne_zero (k := k) (0 : Fin 2) hzero).elim
    have hf : f = g * X (1 : Fin 2) := sub_eq_zero.mp hcancel
    refine LinearMap.mem_range.mpr ⟨Ideal.Quotient.mk I g, ?_⟩
    -- Descend the recovered `Y`-divisibility to the quotient ring.
    change Ideal.Quotient.mk I (g * X (1 : Fin 2)) = Ideal.Quotient.mk I f
    simpa [hf]
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨a, rfl⟩
    -- Every `y`-multiple is killed by `x` because `xy = 0` in the nodal quotient.
    rw [LinearMap.mem_ker]
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    calc
      (a * nodalY k) * nodalX k = a * (nodalX k * nodalY k) := by
        rw [mul_assoc, mul_comm (nodalY k) (nodalX k), ← mul_assoc]
      _ = a * 0 := by rw [nodal_x_mul_nodal_y]
      _ = 0 := by simp

/-- Helper for Example 15.101.10: the source row `0 → range(* y) → A → A / (y) → 0` is short
exact. This packages the source first syzygy before transporting it back to `A / (x)`. -/
theorem nodal_range_shortExact_y :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k))).subtype)
      (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap))
      (by
        -- Elements in the range are `y`-multiples, hence they vanish in the quotient by `(y)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun z ↦ by
          change Ideal.Quotient.mk (nodalIdealY k) z.1 = 0
          have hzIdeal : z.1 ∈ nodalIdealY k := by
            rw [← nodal_mulRight_y_range_eq_idealY (k := k)]
            exact z.2
          exact (Ideal.Quotient.eq_zero_iff_mem).2 hzIdeal)).ShortExact := by
  -- Route correction: use the range-form source row first, then identify `range(* y)` with `A/(x)`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · let S : ShortComplex (ModuleCat (nodalRing k)) :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k))).subtype)
        (ModuleCat.ofHom ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap))
        (by
          -- The range inclusion lands in the quotient kernel because its elements already lie in `(y)`.
          apply ModuleCat.hom_ext
          exact LinearMap.ext fun z ↦ by
            change Ideal.Quotient.mk (nodalIdealY k) z.1 = 0
            have hzIdeal : z.1 ∈ nodalIdealY k := by
              rw [← nodal_mulRight_y_range_eq_idealY (k := k)]
              exact z.2
            exact (Ideal.Quotient.eq_zero_iff_mem).2 hzIdeal)
    change S.Exact
    -- Exactness is the concrete identity `range(range-subtype) = ker(A → A/(y))`.
    rw [S.moduleCat_exact_iff_range_eq_ker]
    change
      LinearMap.range
          ((ModuleCat.ofHom
              (LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k))).subtype : _).hom) =
        LinearMap.ker ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap)
    rw [nodal_quotient_by_y_ker]
    simpa [S, Submodule.range_subtype] using nodal_mulRight_y_range_eq_idealY (k := k)
  · -- The range inclusion is injective by construction.
    exact (ModuleCat.mono_iff_injective _).2 fun a b h => Subtype.ext h
  · -- The quotient map is surjective by the universal quotient construction.
    exact (ModuleCat.epi_iff_surjective _).2
      (Ideal.Quotient.mkₐ_surjective (nodalRing k) (nodalIdealY k))

/-- Helper for Example 15.101.10: quotienting by `(x)` identifies `A / (x)` with the source
syzygy `range(* y)`. -/
noncomputable def nodal_quotient_by_x_equiv_range_mul_y :
    ((nodalRing k) ⧸ nodalIdealX k) ≃ₗ[nodalRing k]
      LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k)) := by
  -- Follow the source route: first quotient by `ker(* y) = range(* x)`, then pass to the image.
  exact
    (Submodule.quotEquivOfEq
      (nodalIdealX k)
      (LinearMap.ker (LinearMap.mulRight (nodalRing k) (nodalY k)))
      ((nodal_mulRight_x_range_eq_idealX (k := k)).symm.trans
        (nodal_mulRight_y_ker_eq_range_x (k := k)).symm)).trans
      ((LinearMap.mulRight (nodalRing k) (nodalY k)).quotKerEquivRange)

/-- Helper for Example 15.101.10: quotienting by `(x)` identifies `A / (x)` with the kernel of the
quotient map `A → A / (y)`. This is the precise source term needed for the ambient boundary map. -/
noncomputable def nodal_xQuotientModuleIso_kernel_quotientByY :
    nodalXQuotientModule k ≅
      ModuleCat.of (nodalRing k)
        (LinearMap.ker ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap)) := by
  let hRangeKer :
      LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalY k)) =
        LinearMap.ker ((Ideal.Quotient.mkₐ (nodalRing k) (nodalIdealY k)).toLinearMap) :=
    (nodal_mulRight_y_range_eq_idealY (k := k)).trans (nodal_quotient_by_y_ker (k := k)).symm
  -- First identify `A / (x)` with `range(* y)`, then rewrite the range as the quotient kernel.
  exact
    (nodal_quotient_by_x_equiv_range_mul_y (k := k)).toModuleIso ≪≫
      (LinearEquiv.ofEq _ _ hRangeKer).toModuleIso

/-- Helper for Example 15.101.10: in a short exact sequence with projective middle term, the
contravariant boundary map is a linear equivalence in positive degree. -/
noncomputable def shortExact_boundary_linearEquiv_ext_succ
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (N : ModuleCat R) [CategoryTheory.Projective S.X₂] (q : ℕ) :
    Ext S.X₁ N (q + 1) ≃ₗ[R] Ext S.X₃ N (q + 2) := by
  let δ : Ext S.X₁ N (q + 1) →ₗ[R] Ext S.X₃ N (q + 2) :=
    hS.extClass.precompOfLinear R N (Nat.add_comm 1 (q + 1))
  have hsurj : Function.Surjective δ := by
    intro e
    -- Exactness at the right-hand `Ext` term lifts every class across the boundary map.
    exact Ext.contravariant_sequence_exact₃ hS N e (Ext.eq_zero_of_projective _)
      (Nat.add_comm 1 (q + 1))
  have hinj : Function.Injective δ := by
    intro x y hxy
    have hsub : δ (x - y) = 0 := by
      rw [LinearMap.map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS N (x - y)
      (Nat.add_comm 1 (q + 1)) hsub
    have hzero : z = 0 := by
      exact z.eq_zero_of_projective
    have hxy' : x - y = 0 := by
      simpa [δ, hzero] using hz.symm
    exact sub_eq_zero.mp hxy'
  -- The long exact sequence is exact on both sides because the middle term is projective.
  exact LinearEquiv.ofBijective δ ⟨hinj, hsurj⟩

/-- Helper for Example 15.101.10: precomposing `Ext` classes by an isomorphism on the source is a
linear equivalence. -/
noncomputable def ext_precomp_linearEquiv_of_iso
    {R : Type u} [CommRing R] {X Y N : ModuleCat R} (i : ℕ) (e : X ≅ Y) :
    Ext Y N i ≃ₗ[R] Ext X N i := by
  -- TODO: package the source-side isomorphism transport on `Ext` without triggering the current
  -- `precompOfLinear` elaboration timeout.
  sorry

/-- Helper for Example 15.101.10: the canonical kernel row for `A → A / (y)` shifts the ambient
`Ext²_A(M, M)` computation to `Ext¹_A(A / (x), M)`. -/
noncomputable def nodal_ambient_ext2_linearEquiv_ext1_xQuotient :
    Ext (nodalXQuotientModule k) (nodalQuotientModule k) 1 ≃ₗ[nodalRing k]
      Ext (nodalQuotientModule k) (nodalQuotientModule k) 2 := by
  -- TODO: reuse the short exact row `0 → A/(x) → A → A/(y) → 0` through the stabilized source
  -- syzygy identification without re-triggering the current `Ext` transport timeout.
  sorry

/-- Helper for Example 15.101.10: for a singleton family indexed by `Fin 1`, quotienting by the
generated ideal agrees with quotienting by the principal ideal `(x)`. -/
noncomputable def singleton_span_quotient_moduleIso
    {R : Type u} [CommRing R] (x : R) :
    ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun _ : Fin 1 ↦ x))) ≅
      ModuleCat.of R (R ⧸ Ideal.span ({x} : Set R)) := by
  -- TODO: transport the quotient module across the equality `Ideal.span (range (const x)) = (x)`.
  sorry

/-- Helper for Example 15.101.10: the singleton `Fin 1`-family with value `x` spans the ideal
`(x)` in the nodal ring. -/
private theorem nodal_x_singleton_span_eq_idealX :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ nodalX k)) = nodalIdealX k := by
  -- The range of a constant `Fin 1`-family is the singleton `{x}`.
  have hset : Set.range (fun _ : Fin 1 ↦ nodalX k) = ({nodalX k} : Set (nodalRing k)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      simp
    · intro hz
      simp at hz
      rcases hz with rfl
      exact ⟨0, rfl⟩
  simpa [nodalIdealX, hset]

/-- Helper for Example 15.101.10: specializing the quotient-row presentation from
Lemma `15.90.6` to the singleton generator `x` identifies `Ext¹_A(A/(x), M)` with the quotient
of `Hom_A((x), M)` by the image of the scalar-action map `M → Hom_A((x), M)`. -/
noncomputable def nodal_ext1_xQuotient_linearEquiv_hom_quotient :
    ((((Ideal.span (Set.range (fun _ : Fin 1 ↦ nodalX k))) →ₗ[nodalRing k] nodalQuotientModule k) ⧸
        LinearMap.range
          (spanToIdealSpanHom (f := fun _ : Fin 1 ↦ nodalX k) (N := nodalQuotientModule k)))
      ≃ₗ[nodalRing k] Ext (nodalXQuotientModule k) (nodalQuotientModule k) 1) := by
  -- TODO: specialize Lemma `15.90.6` to the singleton generator `x`, then transport the source
  -- quotient object from the raw singleton-span quotient to the bundled module `A / (x)`.
  sorry

/-- Helper for Example 15.101.10: quotienting by `(y)` identifies `A / (y)` with the image of
multiplication by `x`. This is the companion syzygy needed to rewrite maps out of `(x)` as
endomorphisms of `M = A / (y)`. -/
noncomputable def nodal_quotient_by_y_equiv_range_mul_x :
    ((nodalRing k) ⧸ nodalIdealY k) ≃ₗ[nodalRing k]
      LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalX k)) := by
  -- Follow the source route: first quotient by `ker(* x) = range(* y)`, then pass to the image.
  exact
    (Submodule.quotEquivOfEq
      (nodalIdealY k)
      (LinearMap.ker (LinearMap.mulRight (nodalRing k) (nodalX k)))
      ((nodal_mulRight_y_range_eq_idealY (k := k)).symm.trans
        (nodal_mulRight_x_ker_eq_range_y (k := k)).symm)).trans
      ((LinearMap.mulRight (nodalRing k) (nodalX k)).quotKerEquivRange)

/-- Helper for Example 15.101.10: the ideal `(x)` is canonically the same `A`-module as
`M = A / (y)`. This packages the second source syzygy before turning `Hom_A((x), M)` into
endomorphisms of `M`. -/
noncomputable def nodalIdealX_linearEquiv_quotientByY :
    nodalIdealX k ≃ₗ[nodalRing k] nodalQuotientModule k := by
  -- Rewrite `(x)` as the image of multiplication by `x`, then use the companion quotient row.
  exact
    (LinearEquiv.ofEq
      (LinearMap.range (LinearMap.mulRight (nodalRing k) (nodalX k)))
      (nodalIdealX k)
      (nodal_mulRight_x_range_eq_idealX (k := k))).symm.trans
      (nodal_quotient_by_y_equiv_range_mul_x (k := k)).symm

/-- Helper for Example 15.101.10: an `A`-linear endomorphism of `M = A / (y)` is determined by
the image of `1`. This is the concrete owner-level replacement for the remaining ambient
`Hom_A((x), M)` quotient computation. -/
noncomputable def nodalQuotientModule_end_linearEquiv_self :
    (nodalQuotientModule k →ₗ[nodalRing k] nodalQuotientModule k) ≃ₗ[nodalRing k]
      nodalQuotientModule k := by
  -- TODO: evaluate an endomorphism of `M = A / (y)` at `1` and reconstruct it by multiplication
  -- by that value.
  sorry

/-- Helper for Example 15.101.10: precomposing with a linear equivalence transports linear maps on
the source. -/
noncomputable def precomposeLinearEquiv
    {R : Type u} [CommRing R] {M N P : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] N) :
    (N →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] P) := by
  let toLinear : (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) :=
    { toFun := fun φ ↦ φ.comp e.toLinearMap
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro a φ
        rfl }
  let invLinear : (M →ₗ[R] P) →ₗ[R] (N →ₗ[R] P) :=
    { toFun := fun φ ↦ φ.comp e.symm.toLinearMap
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro a φ
        rfl }
  -- Evaluate both composites on points so that the inverse identities for `e` close the proof.
  refine LinearEquiv.ofLinear toLinear invLinear ?_ ?_
  · ext φ x
    simp [toLinear, invLinear]
  · ext φ x
    simp [toLinear, invLinear]

/-- Helper for Example 15.101.10: multiplication by `x` on `M = A / (y)` as a linear map. -/
noncomputable def nodalQuotientModule_smulByX :
    nodalQuotientModule k →ₗ[nodalRing k] nodalQuotientModule k :=
  { toFun := fun z ↦ (nodalX k) • z
    map_add' := by
      intro z z'
      simp [smul_add]
    map_smul' := by
      intro a z
      simp [smul_smul, mul_comm] }

/-- Helper for Example 15.101.10: a linear equivalence transports quotient modules to the quotient
by the mapped submodule. -/
noncomputable def quotientBySubmoduleLinearEquiv
    {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) :
    (M ⧸ P) ≃ₗ[R] (N ⧸ P.map e.toLinearMap) := by
  let toLinear :
      (M ⧸ P) →ₗ[R] (N ⧸ P.map e.toLinearMap) :=
    P.mapQ
      (P.map e.toLinearMap)
      e.toLinearMap
      (by
        intro x hx
        exact Submodule.mem_map_of_mem hx)
  let invLinear :
      (N ⧸ P.map e.toLinearMap) →ₗ[R] (M ⧸ P) :=
    (P.map e.toLinearMap).mapQ
      P
      e.symm.toLinearMap
      (by
        intro y hy
        rcases Submodule.mem_map.1 hy with ⟨x, hx, rfl⟩
        simpa using hx)
  -- Evaluate both composites on quotient representatives, where the ambient inverse identities
  -- for `e` become definitional equalities.
  refine LinearEquiv.ofLinear toLinear invLinear ?_ ?_
  · apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change toLinear (invLinear (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    simpa [toLinear, invLinear] using
      congrArg (Submodule.Quotient.mk (p := P.map e.toLinearMap))
        (e.apply_symm_apply x)
  · apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change invLinear (toLinear (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    simpa [toLinear, invLinear] using
      congrArg (Submodule.Quotient.mk (p := P))
        (e.symm_apply_apply x)

/-- Helper for Example 15.101.10: mapping a range through a linear map is the range of the
composite map. -/
theorem submodule_map_range_eq_range_comp
    {R : Type u} [CommRing R] {M N P : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (LinearMap.range f).map g = LinearMap.range (g.comp f) := by
  ext z
  constructor
  · intro hz
    rcases Submodule.mem_map.1 hz with ⟨y, hy, rfl⟩
    rcases LinearMap.mem_range.1 hy with ⟨x, rfl⟩
    exact LinearMap.mem_range.2 ⟨x, rfl⟩
  · intro hz
    rcases LinearMap.mem_range.1 hz with ⟨x, rfl⟩
    exact Submodule.mem_map.2 ⟨f x, LinearMap.mem_range.2 ⟨x, rfl⟩, rfl⟩

/-- Helper for Example 15.101.10: the ambient quotient description of
`Ext¹_A(A/(x), M)` descends to the concrete module quotient `M / xM`. -/
noncomputable def nodal_ext1_xQuotient_linearEquiv_mod_x_quotient :
    Ext (nodalXQuotientModule k) (nodalQuotientModule k) 1 ≃ₗ[nodalRing k]
      ((nodalQuotientModule k) ⧸
        LinearMap.range (nodalQuotientModule_smulByX (k := k))) := by
  -- TODO: descend the quotient presentation of `Ext¹_A(A/(x), M)` to `M / xM` by transporting the
  -- `Hom_A((x), M)` quotient through `nodalIdealX_linearEquiv_quotientByY`,
  -- `nodalQuotientModule_end_linearEquiv_self`, and `quotientBySubmoduleLinearEquiv`.
  sorry

/-- Helper for Example 15.101.10: the ambient `Ext²_A(M, M)` group is the field `k`. -/
noncomputable def nodal_ambient_ext2_linearEquiv_field :
    (Ext (nodalQuotientModule k) (nodalQuotientModule k) 2) ≃ₗ[k] k := by
  -- TODO: compose the boundary shift `Ext² ≃ Ext¹(A/(x), M)` with the concrete quotient
  -- computation `Ext¹(A/(x), M) ≃ M / xM ≃ k`.
  sorry

/-- Helper for Example 15.101.10: the ambient quotient `M / xM` is the coefficient field `k`. -/
noncomputable def nodal_quotient_mod_x_linearEquiv_field :
    ((nodalQuotientModule k) ⧸
      LinearMap.range (nodalQuotientModule_smulByX (k := k))) ≃ₗ[k] k := by
  -- TODO: identify `M = A / (y)` with `k[[x]]`, transport the quotient by `x`,
  -- and then use `PowerSeries.X_dvd_iff` to identify the quotient with `k`.
  sorry

/-- Helper for Example 15.101.10: the reduced stage `Ext²` groups vanish for the truncated nodal
modules `M_n`. -/
theorem nodal_stage_ext2_isZero_aux (n : ℕ+) :
    IsZero (Ext (nodalStageModule k n) (nodalStageModule k n) 2) := by
  -- TODO: package the stage `Ext²` term as the quotient `ker(x^(n-1)) / range(x)` from the
  -- textbook free resolution, then kill that quotient using exactness on `k[x] / (x^n)`.
  sorry

-- Proof sketch: compute `Ext^2_A(M, N)` from the periodic free resolution
-- `⋯ → A --y→ A --x→ A --y→ A → M → 0`; when `N = A / (y)`, this gives
-- `Ext^2_A(M, N) = N[y] / xN = N / xN ≃ k`. For each `n > 0`, use the reduced free resolution
-- `⋯ → A_n^⊕2 → A_n → A_n → A_n → M_n → 0` from the text to identify
-- `Ext^2_{A_n}(M_n, N_n)` with `N_n[x^(n - 1)] / xN_n`, and then use the exact sequence
-- `N_n --x→ N_n --x^(n - 1)→ N_n` for `N_n = k[x] / (x^n)` to deduce vanishing.
/-- Example 15.101.10: for the nodal ring `A = k[[x,y]] / (xy)` with `I = (x)` and
`M = N = A / (y)`, the ambient group `Ext^2_A(M, N)` is isomorphic to `k`, while for every
positive integer `n` the reduced group `Ext^2_{A_n}(M_n, N_n)` vanishes, where
`A_n = A / I^n` and `M_n = N_n = M / I^n M`. This is the explicit counterexample showing that the
`I`-power torsion term in Lemma `15.101.8` cannot be ignored. -/
@[stacks 0EH2]
theorem nodal_power_series_ext2_counterexample :
    ∃ e : (Ext (nodalQuotientModule k) (nodalQuotientModule k) 2) ≃ₗ[k] k,
      ∀ n : ℕ+, IsZero (Ext (nodalStageModule k n) (nodalStageModule k n) 2) := by
  -- Route correction: the ambient source proof does not use a single short exact row
  -- `0 → M → A → M → 0`; the correct alternating rows are
  -- `0 → A/(x) → A --→ M → 0` and `0 → M → A --→ A/(x) → 0`.
  refine ⟨?_, ?_⟩
  · -- Compose the ambient boundary shift with the concrete quotient computation `Ext¹ ≃ M / xM ≃ k`.
    exact nodal_ambient_ext2_linearEquiv_field (k := k)
  · intro n
    -- The remaining stage computation is isolated in a single truncated-resolution helper.
    exact nodal_stage_ext2_isZero_aux (k := k) n

/-- For every positive integer `n`, the reduced group `Ext^2_{A_n}(M_n, N_n)` vanishes in the
nodal counterexample from Example `15.101.10`. -/
theorem nodal_stage_ext2_isZero (n : ℕ+) :
    IsZero (Ext (nodalStageModule k n) (nodalStageModule k n) 2) := by
  rcases nodal_power_series_ext2_counterexample k with ⟨_, hzero⟩
  exact hzero n

end
