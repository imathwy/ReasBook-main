import Mathlib
import Mathlib.Algebra.Category.Ring.Limits
import stacks_proof.stacks_project.Chap10.Lemma_10_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped Polynomial

universe u v

section

variable {J : Type v} [Preorder J]
variable (F : Jᵒᵖ ⥤ CommRingCat.{u})
variable (I : ∀ j : Jᵒᵖ, Ideal (F.obj j))
variable [UnivLE.{v, u}]

/-- Helper for Lemma 15.11.12: the underlying commutative ring of the inverse limit. -/
noncomputable abbrev limitRing : Type u :=
  ((limit F : CommRingCat) : Type u)

/-- Helper for Lemma 15.11.12: the canonical inverse-limit ideal. -/
noncomputable abbrev limitIdeal : Ideal (limitRing (F := F)) :=
  ⨅ j, Ideal.comap ((limit.π F j).hom) (I j)

/- Domain-style sampling:
- primary domain: inverse limits of henselian pairs in commutative algebra;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `HenselianRing.is_henselian`,
  `henselianRing_pi_iff`,
  `directedSystem_directLimit_henselianRing`;
- best owner abstraction: the public conclusion should stay the canonical owner
  `HenselianRing ((limit F : CommRingCat.{u}) : Type u)
    (⨅ j, Ideal.comap ((limit.π F j).hom) (I j))`; there is no separate inverse-system wrapper
  notion to introduce here;
- primitive data: the inverse system `F`, the ideal family `I`, and the compatibility maps `hI`;
- derived API: the limit object is supplied canonically by the owner instance
  `CommRingCat.hasLimitsOfSize`, activated here by `[UnivLE.{v, u}]`, and the conclusion is the
  induced henselian-pair instance on that limit ring with the canonical inverse-limit ideal.

Source/core/bridge triage:
- `source-facing`: closure of compatible inverse systems of henselian pairs under inverse limits;
- `core/canonical`: the owner class `HenselianRing`;
- `bridge/view`: the inverse-limit ring `limit F` and the limit ideal
  `⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`.
-/

-- Proof sketch: realize the inverse limit as the ring of compatible sections. The Jacobson clause
-- is checked coordinatewise using the stagewise henselian Jacobson condition. For the Hensel
-- lifting clause, solve the simple-root problem at each stage, then use uniqueness of simple
-- lifts modulo a Jacobson ideal to prove compatibility of the stagewise roots and reassemble them
-- into a root in the inverse limit.
/-- Helper for Lemma 15.11.12: a point of the inverse limit ring determines the corresponding
compatible family in the underlying `Type`-valued diagram. -/
noncomputable def underlying_sections_of_limit (x : limitRing (F := F)) :
    (F ⋙ forget CommRingCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget CommRingCat) F).hom x)

/-- Helper for Lemma 15.11.12: a compatible family in the underlying `Type`-valued diagram defines
a point of the inverse limit ring. -/
noncomputable def limit_of_underlying_sections
    (s : (F ⋙ forget CommRingCat).sections) : limitRing (F := F) :=
  (preservesLimitIso (forget CommRingCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget CommRingCat)).symm s)

/-- Helper for Lemma 15.11.12: the compatible-family description of a limit point is injective. -/
lemma underlying_sections_of_limit_injective :
    Function.Injective (underlying_sections_of_limit (F := F)) := by
  intro x y hxy
  -- Proof comment: compare in the underlying `Type`-valued limit and invert the preserved-limit
  -- isomorphism.
  have hlimit :
      (preservesLimitIso (forget CommRingCat) F).hom x =
        (preservesLimitIso (forget CommRingCat) F).hom y := by
    exact (Types.limitEquivSections (F ⋙ forget CommRingCat)).injective hxy
  simpa using congrArg ((preservesLimitIso (forget CommRingCat) F).inv) hlimit

/-- Helper for Lemma 15.11.12: reading off the compatible family of a limit element recovers each
limit projection. -/
lemma limit_π_underlying_sections_of_limit (x : limitRing (F := F)) (j : Jᵒᵖ) :
    (limit.π F j).hom x = (underlying_sections_of_limit (F := F) x).val j := by
  -- Proof comment: first move to the underlying `Type`-valued limit, then use the explicit
  -- sections equivalence.
  let t : limit (F ⋙ forget CommRingCat) :=
    (preservesLimitIso (forget CommRingCat) F).hom x
  have hπ :
      limit.π (F ⋙ forget CommRingCat) j t = (limit.π F j).hom x := by
    exact congrArg (fun g => g x) (preservesLimitIso_hom_π (forget CommRingCat) F j)
  have ht :
      (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm
          (underlying_sections_of_limit (F := F) x) = t := by
    simpa [underlying_sections_of_limit, t] using
      (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm_apply_apply
        ((preservesLimitIso (forget CommRingCat) F).hom x)
  have hsections :
      limit.π (F ⋙ forget CommRingCat) j
          ((Types.limitEquivSections (F ⋙ forget CommRingCat)).symm
            (underlying_sections_of_limit (F := F) x)) =
        (underlying_sections_of_limit (F := F) x).val j := by
    simpa using
      Types.limitEquivSections_symm_apply (F ⋙ forget CommRingCat)
        (underlying_sections_of_limit (F := F) x) j
  exact hπ.symm.trans (ht ▸ hsections)

/-- Helper for Lemma 15.11.12: the limit point built from a compatible family has the expected
coordinate at every stage. -/
lemma limit_π_limit_of_underlying_sections
    (s : (F ⋙ forget CommRingCat).sections) (j : Jᵒᵖ) :
    (limit.π F j).hom (limit_of_underlying_sections (F := F) s) = s.val j := by
  -- Proof comment: again pass through the underlying `Type`-valued limit and read off the chosen
  -- section coordinate.
  let t : limit (F ⋙ forget CommRingCat) :=
    (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm s
  have hπ :
      (limit.π F j).hom ((preservesLimitIso (forget CommRingCat) F).inv t) =
        limit.π (F ⋙ forget CommRingCat) j t := by
    exact congrArg (fun g => g t) (preservesLimitIso_inv_π (forget CommRingCat) F j)
  simpa [limit_of_underlying_sections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget CommRingCat) s j)

omit [UnivLE.{v, u}] in
/-- Helper for Lemma 15.11.12: each stage ideal is contained in the Jacobson radical of its stage
ring. -/
lemma stage_le_ring_jacobson [∀ j, HenselianRing (F.obj j) (I j)] (j : Jᵒᵖ) :
    I j ≤ Ring.jacobson (F.obj j) := by
  -- Proof comment: this is the Jacobson field of the stagewise henselian owner, rewritten on the
  -- chapter surface `Ring.jacobson`.
  simpa [Ideal.jacobson_bot] using
    (show I j ≤ Ideal.jacobson (⊥ : Ideal (F.obj j)) from HenselianRing.jac (I := I j))

/-- Helper for Lemma 15.11.12: if an element is a unit after every projection from the inverse
limit, then it is already a unit in the limit ring. -/
lemma isUnit_of_projection_isUnit (x : limitRing (F := F))
    (hx : ∀ j : Jᵒᵖ, IsUnit ((limit.π F j).hom x)) :
    IsUnit x := by
  classical
  let u : ∀ j : Jᵒᵖ, Units (F.obj j) := fun j ↦ (hx j).unit
  have hu_spec : ∀ j : Jᵒᵖ, ((u j : Units (F.obj j)) : F.obj j) = (limit.π F j).hom x := by
    intro j
    exact IsUnit.unit_spec (hx j)
  have hu_compat : ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), Units.map (F.map f).hom (u j) = u k := by
    intro j k f
    apply Units.ext
    -- Proof comment: the chosen units are equal because their values are both the projected image
    -- of `x` at stage `k`.
    calc
      (((Units.map (F.map f).hom (u j) : Units (F.obj k)) : F.obj k)) =
          (F.map f).hom (((u j : Units (F.obj j)) : F.obj j)) := rfl
      _ = (F.map f).hom ((limit.π F j).hom x) := by rw [hu_spec j]
      _ = (limit.π F k).hom x := by
        simpa using congrArg (fun g => g x) (limit.w F f)
      _ = ((u k : Units (F.obj k)) : F.obj k) := by rw [hu_spec k]
  have huinv_compat :
      ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), (F.map f).hom ↑((u j)⁻¹) = ↑((u k)⁻¹) := by
    intro j k f
    -- Proof comment: once the units themselves are compatible, so are their inverses.
    simpa using
      congrArg (fun z : Units (F.obj k) => ((z⁻¹ : Units (F.obj k)) : F.obj k)) (hu_compat f)
  let s : (F ⋙ forget CommRingCat).sections :=
    ⟨fun j ↦ (((u j)⁻¹ : Units (F.obj j)) : F.obj j), fun {_ _} f ↦ huinv_compat f⟩
  let y : limitRing (F := F) := limit_of_underlying_sections (F := F) s
  have hxy : x * y = 1 := by
    apply underlying_sections_of_limit_injective (F := F)
    apply Subtype.ext
    funext j
    -- Proof comment: each projection multiplies `x` with the reassembled inverse to `1`.
    have hcoord :
        (underlying_sections_of_limit (F := F) (x * y)).val j =
          (limit.π F j).hom (1 : limitRing (F := F)) := by
      calc
        (underlying_sections_of_limit (F := F) (x * y)).val j = (limit.π F j).hom (x * y) := by
          exact (limit_π_underlying_sections_of_limit (F := F) (x := x * y) (j := j)).symm
        _ = (limit.π F j).hom x * (limit.π F j).hom y := by rw [map_mul]
        _ = (limit.π F j).hom x * (((u j)⁻¹ : Units (F.obj j)) : F.obj j) := by
          rw [limit_π_limit_of_underlying_sections]
        _ = (((u j : Units (F.obj j)) : F.obj j)) * (((u j)⁻¹ : Units (F.obj j)) : F.obj j) := by
          rw [hu_spec j]
        _ = 1 := by simp
        _ = (limit.π F j).hom (1 : limitRing (F := F)) := by rw [map_one]
    exact hcoord.trans (limit_π_underlying_sections_of_limit (F := F) (x := 1) (j := j))
  have hyx : y * x = 1 := by
    apply underlying_sections_of_limit_injective (F := F)
    apply Subtype.ext
    funext j
    -- Proof comment: the same coordinatewise inverse identity gives the opposite product.
    have hcoord :
        (underlying_sections_of_limit (F := F) (y * x)).val j =
          (limit.π F j).hom (1 : limitRing (F := F)) := by
      calc
        (underlying_sections_of_limit (F := F) (y * x)).val j = (limit.π F j).hom (y * x) := by
          exact (limit_π_underlying_sections_of_limit (F := F) (x := y * x) (j := j)).symm
        _ = (limit.π F j).hom y * (limit.π F j).hom x := by rw [map_mul]
        _ = (((u j)⁻¹ : Units (F.obj j)) : F.obj j) * (limit.π F j).hom x := by
          rw [limit_π_limit_of_underlying_sections]
        _ = (((u j)⁻¹ : Units (F.obj j)) : F.obj j) * (((u j : Units (F.obj j)) : F.obj j)) := by
          rw [hu_spec j]
        _ = 1 := by simp
        _ = (limit.π F j).hom (1 : limitRing (F := F)) := by rw [map_one]
    exact hcoord.trans (limit_π_underlying_sections_of_limit (F := F) (x := 1) (j := j))
  exact isUnit_iff_exists.mpr ⟨y, hxy, hyx⟩

/-- Helper for Lemma 15.11.12: every element of `1 +` the inverse-limit ideal is a unit in the
inverse limit ring. -/
lemma isUnit_one_add_of_mem_limit_ideal
    [∀ j, HenselianRing (F.obj j) (I j)]
    (x : limitRing (F := F)) (hx : x ∈ limitIdeal (F := F) (I := I)) :
    IsUnit (1 + x) := by
  -- Proof comment: use the Jacobson criterion at each stage, then reassemble the stage inverses in
  -- the inverse limit.
  refine isUnit_of_projection_isUnit (F := F) (x := 1 + x) fun j ↦ ?_
  have hmem : (limit.π F j).hom x ∈ I j := by
    rw [Ideal.mem_iInf] at hx
    exact Ideal.mem_comap.mp (hx j)
  have hJac : I j ≤ Ring.jacobson (F.obj j) := stage_le_ring_jacobson (F := F) (I := I) j
  simpa [map_add] using
    (ideal_le_ring_jacobson_iff_isUnit_one_add (R := F.obj j) (I := I j)).mp hJac
      ((limit.π F j).hom x) hmem

omit [UnivLE.{v, u}] in
/-- Helper for Lemma 15.11.12: in a Jacobson ideal, a simple root lift is unique inside a fixed
residue class modulo the ideal. -/
lemma eq_of_roots_of_sub_mem_ideal_and_derivative_isUnit_mod_ideal
    {A : Type u} [CommRing A] (J : Ideal A) (hJac : J ≤ Ring.jacobson A) {f : A[X]} {a b : A}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hd : b - a ∈ J)
    (hder : IsUnit ((Ideal.Quotient.mk J) (f.derivative.eval a))) :
    a = b := by
  let d := b - a
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion f a d
  have hfactor :
      f.derivative.eval a * d + c * d ^ 2 = (f.derivative.eval a + c * d) * d := by
    -- Proof comment: factor the linear and quadratic correction terms by the common difference.
    dsimp [d]
    ring
  have hsum : 0 = f.derivative.eval a * d + c * d ^ 2 := by
    -- Proof comment: the binomial expansion collapses because both evaluation endpoints are roots.
    simpa [d, ha.eq_zero, hb.eq_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  have hrootEq : (f.derivative.eval a + c * d) * d = 0 := by
    rw [hfactor] at hsum
    exact hsum.symm
  have hd' : d ∈ J := by
    simpa [d] using hd
  have hcd : c * d ∈ J := by
    simpa [mul_comm] using J.mul_mem_left c hd'
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    isLocalHom_of_le_jacobson_bot J (by simpa [Ideal.jacobson_bot] using hJac)
  have hunit : IsUnit (f.derivative.eval a + c * d) := by
    -- Proof comment: the quadratic correction term dies modulo `J`, so the derivative stays a
    -- unit after adding that correction.
    apply IsUnit.of_map (Ideal.Quotient.mk J)
    have hzero : (Ideal.Quotient.mk J) (c * d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcd
    rw [map_add, hzero, add_zero]
    exact hder
  have hd_zero : d = 0 := hunit.mul_right_eq_zero.mp hrootEq
  exact (sub_eq_zero.mp (by simpa [d] using hd_zero)).symm

/-- Lemma 15.11.12: if `F : Jᵒᵖ ⥤ CommRingCat` is an inverse system of commutative rings over a
preordered set and `I j` is a compatible inverse system of henselian ideals on the stages, then
the inverse-limit ring `limit F`, equipped with the limit ideal
`⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`, is a henselian pair. -/
@[stacks 0EM6]
instance inverseSystem_limit_henselianRing
    (hI : ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    [∀ j, HenselianRing (F.obj j) (I j)] :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (⨅ j, Ideal.comap ((limit.π F j).hom) (I j)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the Jacobson-radical clause is reduced to the stagewise unit criterion on
    -- `1 +` the limit ideal.
    simpa [Ideal.jacobson_bot] using
      (ideal_le_ring_jacobson_iff_isUnit_one_add
        (R := limitRing (F := F)) (I := limitIdeal (F := F) (I := I))).2
        (fun x hx ↦ isUnit_one_add_of_mem_limit_ideal (F := F) (I := I) x hx)
  · intro f hf a₀ ha₀ hderiv
    have ha₀_stage :
        ∀ j : Jᵒᵖ,
          (Polynomial.map ((limit.π F j).hom) f).eval ((limit.π F j).hom a₀) ∈ I j := by
      intro j
      have hmem : (limit.π F j).hom (Polynomial.eval a₀ f) ∈ I j := by
        rw [Ideal.mem_iInf] at ha₀
        exact Ideal.mem_comap.mp (ha₀ j)
      rw [← Polynomial.eval₂_at_apply ((limit.π F j).hom) a₀ (p := f)] at hmem
      simpa [Polynomial.eval₂_eq_eval_map] using hmem
    have hderiv_stage :
        ∀ j : Jᵒᵖ,
          IsUnit
            ((Ideal.Quotient.mk (I j))
              (((Polynomial.map ((limit.π F j).hom) f).derivative).eval
                ((limit.π F j).hom a₀))) := by
      intro j
      let qj : limitRing (F := F) ⧸ limitIdeal (F := F) (I := I) →+* F.obj j ⧸ I j :=
        Ideal.quotientMap (I j) ((limit.π F j).hom) (iInf_le _ j)
      have hmap : IsUnit (qj ((Ideal.Quotient.mk (limitIdeal (F := F) (I := I)))
          (f.derivative.eval a₀))) := IsUnit.map qj hderiv
      simpa [qj, Polynomial.derivative_map, Polynomial.eval₂_eq_eval_map,
        Polynomial.eval₂_at_apply] using hmap
    choose aStage hrootStage hmemStage using
      fun j ↦
        HenselianRing.is_henselian (I := I j) (Polynomial.map ((limit.π F j).hom) f)
          (by simpa using hf.map ((limit.π F j).hom))
          ((limit.π F j).hom a₀) (ha₀_stage j) (hderiv_stage j)
    have hcompat : ∀ ⦃j k : Jᵒᵖ⦄ (g : j ⟶ k), (F.map g).hom (aStage j) = aStage k := by
      intro j k g
      have hrootMap :
          (Polynomial.map ((limit.π F k).hom) f).IsRoot ((F.map g).hom (aStage j)) := by
        have hmap :
            (Polynomial.map (F.map g).hom (Polynomial.map ((limit.π F j).hom) f)).IsRoot
              ((F.map g).hom (aStage j)) :=
          Polynomial.IsRoot.map (f := (F.map g).hom) (h := hrootStage j)
        have hcomp :
            (F.map g).hom.comp ((limit.π F j).hom) = (limit.π F k).hom := by
          ext x
          simpa using congrArg (fun φ => φ x) (limit.w F g)
        rw [Polynomial.map_map, hcomp] at hmap
        simpa using hmap
      have hmemMap :
          (F.map g).hom (aStage j) - (limit.π F k).hom a₀ ∈ I k := by
        have hmem :
            (F.map g).hom (aStage j - (limit.π F j).hom a₀) ∈ I k := by
          exact (hI g) (Ideal.mem_map_of_mem _ (hmemStage j))
        simpa [map_sub] using hmem
      have hdiff :
          (F.map g).hom (aStage j) - aStage k ∈ I k := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (I k).sub_mem hmemMap (hmemStage k)
      have hderivAtRoot :
          IsUnit
            ((Ideal.Quotient.mk (I k))
              (((Polynomial.map ((limit.π F k).hom) f).derivative).eval (aStage k))) := by
        have hq :
            (Ideal.Quotient.mk (I k))
                (((Polynomial.map ((limit.π F k).hom) f).derivative).eval (aStage k)) =
              (Ideal.Quotient.mk (I k))
                (((Polynomial.map ((limit.π F k).hom) f).derivative).eval
                  ((limit.π F k).hom a₀)) := by
          rw [← Polynomial.eval₂_at_apply (Ideal.Quotient.mk (I k)) (aStage k)
              (p := (Polynomial.map ((limit.π F k).hom) f).derivative)]
          rw [← Polynomial.eval₂_at_apply (Ideal.Quotient.mk (I k)) ((limit.π F k).hom a₀)
              (p := (Polynomial.map ((limit.π F k).hom) f).derivative)]
          rw [show (Ideal.Quotient.mk (I k)) (aStage k) =
              (Ideal.Quotient.mk (I k)) ((limit.π F k).hom a₀) by
                rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
                exact hmemStage k]
        rw [hq]
        exact hderiv_stage k
      have hJac : I k ≤ Ring.jacobson (F.obj k) := stage_le_ring_jacobson (F := F) (I := I) k
      exact
        (eq_of_roots_of_sub_mem_ideal_and_derivative_isUnit_mod_ideal
          (J := I k) hJac (ha := hrootStage k) (hb := hrootMap) hdiff hderivAtRoot).symm
    let s : (F ⋙ forget CommRingCat).sections :=
      ⟨fun j ↦ aStage j, fun {_ _} g ↦ hcompat g⟩
    let a : limitRing (F := F) := limit_of_underlying_sections (F := F) s
    refine ⟨a, ?_, ?_⟩
    · -- Proof comment: the reassembled limit point is a root because every projection is a root.
      apply (Polynomial.IsRoot.def).2
      apply underlying_sections_of_limit_injective (F := F)
      apply Subtype.ext
      funext j
      have hproj_eval :
          (limit.π F j).hom (Polynomial.eval a f) = 0 := by
        rw [← Polynomial.eval₂_at_apply ((limit.π F j).hom) a (p := f)]
        rw [show (limit.π F j).hom a = aStage j by
              simpa [a, s] using limit_π_limit_of_underlying_sections (F := F) s j]
        simpa [Polynomial.eval₂_eq_eval_map, Polynomial.IsRoot] using hrootStage j
      have hcoord :
          (underlying_sections_of_limit (F := F) (Polynomial.eval a f)).val j =
            (limit.π F j).hom (0 : limitRing (F := F)) := by
        calc
          (underlying_sections_of_limit (F := F) (Polynomial.eval a f)).val j =
              (limit.π F j).hom (Polynomial.eval a f) := by
                exact
                  (limit_π_underlying_sections_of_limit (F := F)
                    (x := Polynomial.eval a f) (j := j)).symm
          _ = 0 := hproj_eval
          _ = (limit.π F j).hom (0 : limitRing (F := F)) := by rw [map_zero]
      exact hcoord.trans (limit_π_underlying_sections_of_limit (F := F) (x := 0) (j := j))
    · -- Proof comment: the lifted limit root stays congruent to the original approximate root
      -- because that congruence holds at every stage.
      rw [Ideal.mem_iInf]
      intro j
      rw [Ideal.mem_comap]
      rw [show (limit.π F j).hom (a - a₀) = aStage j - (limit.π F j).hom a₀ by
            rw [map_sub]
            simpa [a, s] using limit_π_limit_of_underlying_sections (F := F) s j]
      exact hmemStage j

end
