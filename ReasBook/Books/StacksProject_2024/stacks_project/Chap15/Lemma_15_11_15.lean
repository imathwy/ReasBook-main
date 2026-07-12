import Mathlib
import StacksProject_2024.Chap15.Lemma_15_11_10
import StacksProject_2024.Chap15.Lemma_15_11_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Polynomial

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: closure of henselian ideals in the complete lattice `Ideal A`;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `ideal_add_henselianRing`,
  `directedSystem_directLimit_henselianRing`,
  `Ideal.sSup_eq_iSup`;
- best owner abstraction: the public core object is the canonical supremum ideal
  `sSup {I : Ideal A | HenselianRing A I}`; henselianity and maximality are derived theorems about
  that ideal, not primitive data of a wrapper package.

Source/core/bridge triage:
- `source-facing`: the existence of a largest henselian ideal of `A`;
- `core/canonical`: the owner predicate `HenselianRing A I` on the complete lattice `Ideal A`;
- `bridge/view`: the supremum ideal of all henselian ideals together with its universal upper-bound
  property.

Primitive data is only the ambient ring `A` and the set of ideals carrying the owner predicate
`HenselianRing A`. The largest henselian ideal is therefore a canonical lattice construction, so
the file should expose that ideal directly and keep the existential statement only as a thin
source-facing consequence.
-/

/-- The supremum of all henselian ideals of `A`. -/
def largestHenselianIdeal : Ideal A :=
  sSup {I : Ideal A | HenselianRing A I}

local notation "HenselianIdealIndex" => {I : Ideal A // HenselianRing A I}
local notation "HenselianIdealConst" => fun _ : HenselianIdealIndex ↦ A
local notation "HenselianIdealTransition" =>
  fun _ _ _ ↦ (RingHom.id A : A →+* A)
local notation "HenselianIdealDirectLimit" =>
  Ring.DirectLimit HenselianIdealConst HenselianIdealTransition
local notation "HenselianIdealColimitIdeal" =>
  ⨆ J : HenselianIdealIndex,
    Ideal.map (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition J) (J : Ideal A)

/-- Helper for Lemma 15.11.15: the zero ideal is a henselian ideal. -/
instance ideal_bot_henselianRing : HenselianRing A (⊥ : Ideal A) := by
  refine ⟨bot_le, ?_⟩
  intro F hF a0 ha0 hderiv
  refine ⟨a0, ?_, ?_⟩
  · -- The approximate root condition modulo `⊥` is already an exact root equation.
    exact Polynomial.IsRoot.def.mpr (by simpa using ha0)
  · -- Choosing the same lift makes the difference vanish.
    simpa

/-- Helper for Lemma 15.11.15: the subtype of henselian ideals is nonempty. -/
instance henselianIdealIndex_nonempty : Nonempty HenselianIdealIndex :=
  ⟨⟨⊥, inferInstance⟩⟩

/-- Helper for Lemma 15.11.15: a surjective image of a Jacobson ideal is again Jacobson. -/
private theorem ideal_map_le_ring_jacobson_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    Ideal.map f I ≤ Ring.jacobson S := by
  -- Check the Jacobson criterion on `1 + y` after pulling `y` back along surjectivity.
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro y hy
  rcases (Ideal.mem_map_iff_of_surjective f hf).mp hy with ⟨x, hx, rfl⟩
  have hxUnit : IsUnit (1 + x) := by
    exact (ideal_le_ring_jacobson_iff_isUnit_one_add I).mp hI x hx
  simpa using IsUnit.map f hxUnit

/-- Helper for Lemma 15.11.15: henselian ideals are directed under inclusion by taking sums. -/
lemma henselian_ideal_subtype_directed :
    Directed (· ≤ ·) fun J : HenselianIdealIndex => (J : Ideal A) := by
  -- Route correction: use the canonical sum-closure instance from `Lemma_15_11_10` instead of
  -- rebuilding the two-step quotient transport locally in this file.
  intro I J
  let _ : HenselianRing A (I : Ideal A) := I.2
  let _ : HenselianRing A (J : Ideal A) := J.2
  let _ : HenselianRing A (I.1 + J.1) := inferInstance
  refine ⟨⟨I.1 + J.1, inferInstance⟩, ?_, ?_⟩
  · -- The first summand sits inside the sum ideal.
    exact le_sup_left
  · -- The second summand sits inside the sum ideal.
    exact le_sup_right

/-- Helper for Lemma 15.11.15: the henselian-ideal index type is directed. -/
instance henselianIdealIndex_isDirectedOrder : IsDirectedOrder HenselianIdealIndex where
  directed := henselian_ideal_subtype_directed (A := A)

/-- Helper for Lemma 15.11.15: the constant `A`-system over henselian ideals is a directed
system. -/
instance henselianIdealConst_directedSystem :
    DirectedSystem HenselianIdealConst HenselianIdealTransition where
  map_self := by
    intro J x
    rfl
  map_map := by
    intro J K L hJK hKL x
    rfl

/-- Helper for Lemma 15.11.15: moving a stage representative forward in the constant system does
not change its image in the direct limit. -/
lemma henselianIdealConst_of_f {I J : HenselianIdealIndex} (hIJ : I ≤ J) (x : A) :
    Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition J x =
      Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x := by
  -- The transition maps are identities, so `of_f` specializes to literal equality.
  simpa using
    (@Ring.DirectLimit.of_f HenselianIdealIndex _ HenselianIdealConst _ HenselianIdealTransition
      I J hIJ x)

/-- Helper for Lemma 15.11.15: the direct limit of the constant `A`-system indexed by henselian
ideals is canonically `A` again. -/
noncomputable def henselianIdealConstDirectLimitEquiv :
    HenselianIdealDirectLimit ≃+* A :=
  RingEquiv.ofRingHom
    (Ring.DirectLimit.lift HenselianIdealConst HenselianIdealTransition A
      (fun _ ↦ RingHom.id A) fun _ _ _ _ ↦ rfl)
    (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition (Classical.arbitrary HenselianIdealIndex))
    (by
      ext x
      simp only [Ring.DirectLimit.lift_of, RingHom.comp_apply, RingHom.id_apply])
    (by
      apply RingHom.ext
      intro z
      classical
      induction z using Ring.DirectLimit.induction_on with
      | ih I x =>
          let I₀ : HenselianIdealIndex := Classical.arbitrary HenselianIdealIndex
          rcases exists_ge_ge I I₀ with ⟨K, hIK, hI₀K⟩
          simpa only [RingHom.comp_apply, Ring.DirectLimit.lift_of, RingHom.id_apply] using
            (show
                Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I₀ x =
                  Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x from by
              calc
                Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I₀ x =
                    Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition K
                      ((RingHom.id A) x) := by
                        symm
                        exact henselianIdealConst_of_f (A := A) hI₀K x
                _ = Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition K x := rfl
                _ = Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x := by
                      exact henselianIdealConst_of_f (A := A) hIK x))

/-- Helper for Lemma 15.11.15: the inverse equivalence sends an element of `A` to any chosen stage
representative in the constant direct limit. -/
lemma henselianIdealConstDirectLimitEquiv_symm_of (I : HenselianIdealIndex) (x : A) :
    (henselianIdealConstDirectLimitEquiv (A := A)).symm x =
      Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x := by
  classical
  let I₀ : HenselianIdealIndex := Classical.arbitrary HenselianIdealIndex
  change
    Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I₀ x =
      Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x
  rcases exists_ge_ge I I₀ with ⟨K, hIK, hI₀K⟩
  calc
    Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I₀ x =
        Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition K ((RingHom.id A) x) := by
          symm
          exact henselianIdealConst_of_f (A := A) hI₀K x
    _ = Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition K x := rfl
    _ = Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x := by
          exact henselianIdealConst_of_f (A := A) hIK x

/-- Helper for Lemma 15.11.15: the constant-system equivalence evaluates a stage representative to
its underlying element of `A`. -/
lemma henselianIdealConstDirectLimitEquiv_apply_of (I : HenselianIdealIndex) (x : A) :
    henselianIdealConstDirectLimitEquiv (A := A)
      (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x) = x := by
  -- The forward map is the direct-limit lift whose stage maps are the identities on `A`.
  change
    Ring.DirectLimit.lift HenselianIdealConst HenselianIdealTransition A
      (fun _ ↦ RingHom.id A) (fun _ _ _ _ ↦ rfl)
      (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition I x) = x
  simpa using
    (Ring.DirectLimit.lift_of
      (G := HenselianIdealConst)
      (f := HenselianIdealTransition)
      (P := A)
      (g := fun _ ↦ RingHom.id A)
      (Hg := fun _ _ _ _ ↦ rfl)
      I x)

/-- Helper for Lemma 15.11.15: evaluating a polynomial after pulling both coefficients and point
back along a ring equivalence commutes with pushing forward again. -/
private theorem ringEquiv_map_symm_eval
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (F : S[X]) (a : S) :
    e.toRingHom ((Polynomial.map e.symm.toRingHom F).eval (e.symm a)) = F.eval a := by
  -- Compare the two evaluations via `eval₂` and simplify the double coefficient transport.
  calc
    e.toRingHom ((Polynomial.map e.symm.toRingHom F).eval (e.symm a)) =
        Polynomial.eval₂ e.toRingHom (e.toRingHom (e.symm a))
          (Polynomial.map e.symm.toRingHom F) := by
            rw [Polynomial.eval₂_at_apply]
    _ = Polynomial.eval (e.toRingHom (e.symm a))
          (Polynomial.map e.toRingHom (Polynomial.map e.symm.toRingHom F)) := by
            rw [← Polynomial.eval₂_eq_eval_map]
    _ = F.eval a := by
          simp [Polynomial.map_map]

/-- Helper for Lemma 15.11.15: ring equivalences transport henselian ideals to their mapped
ideals. -/
theorem henselianRing_map_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) [HenselianRing R I] :
    HenselianRing S (Ideal.map e.toRingHom I) := by
  refine ⟨?_, ?_⟩
  · -- Transport Jacobson-radical membership using the unit criterion and the ring equivalence.
    have hJac :
        I ≤ Ring.jacobson R := by
      simpa [Ideal.jacobson_bot] using
        (show I ≤ Ideal.jacobson (⊥ : Ideal R) from HenselianRing.jac (R := R) (I := I))
    have hMapJac :
        Ideal.map e.toRingHom I ≤ Ring.jacobson S := by
      exact ideal_map_le_ring_jacobson_of_surjective e.toRingHom e.surjective I hJac
    simpa [Ideal.jacobson_bot] using hMapJac
  · intro F hF a0 ha0 hderiv
    let G : R[X] := Polynomial.map e.symm.toRingHom F
    have hG_monic : G.Monic := by
      -- Monicity is preserved under coefficient transport along a ring equivalence.
      simpa [G] using hF.map e.symm.toRingHom
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp ha0 with ⟨x0, hx0, hx0eq⟩
    have hG_eval_eq : G.eval (e.symm a0) = x0 := by
      -- The pulled-back evaluation is the chosen preimage of the original error term.
      apply e.injective
      calc
        e.toRingHom (G.eval (e.symm a0)) = F.eval a0 := by
          simpa [G] using ringEquiv_map_symm_eval (e := e) (F := F) (a := a0)
        _ = e.toRingHom x0 := by
          simpa using hx0eq.symm
    have hG_eval : G.eval (e.symm a0) ∈ I := by
      simpa [hG_eval_eq] using hx0
    have hMapSymm : Ideal.map e.toRingHom I ≤ Ideal.comap e.symm.toRingHom I := by
      -- A mapped ideal element pulls back to its original representative under the inverse map.
      intro y hy
      rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hy with ⟨x, hx, rfl⟩
      simpa using hx
    let qMap : R ⧸ I →+* S ⧸ Ideal.map e.toRingHom I :=
      Ideal.quotientMap (Ideal.map e.toRingHom I) e.toRingHom Ideal.le_comap_map
    let qMapSymm : S ⧸ Ideal.map e.toRingHom I →+* R ⧸ I :=
      Ideal.quotientMap I e.symm.toRingHom hMapSymm
    have hqMapLeft :
        RingHom.comp qMap qMapSymm = RingHom.id (S ⧸ Ideal.map e.toRingHom I) := by
      -- The quotient maps induced by `e` and `e.symm` are inverse on quotient representatives.
      ext y
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
      simpa using congrArg (Ideal.Quotient.mk (Ideal.map e.toRingHom I)) (e.apply_symm_apply y)
    have hqMapRight :
        RingHom.comp qMapSymm qMap = RingHom.id (R ⧸ I) := by
      -- The same computation works in the opposite direction.
      ext x
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
      simpa using congrArg (Ideal.Quotient.mk I) (e.symm_apply_apply x)
    let qEquiv : R ⧸ I ≃+* S ⧸ Ideal.map e.toRingHom I :=
      RingEquiv.ofRingHom qMap qMapSymm hqMapLeft hqMapRight
    have hG_deriv_eval_map :
        qEquiv ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0))) =
          (Ideal.Quotient.mk (Ideal.map e.toRingHom I)) (F.derivative.eval a0) := by
      -- Identify the derivative classes by transporting the derivative polynomial itself.
      change qMap ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0))) = _
      rw [Ideal.quotientMap_mk]
      have hEvalDeriv :
          e.toRingHom (G.derivative.eval (e.symm a0)) = F.derivative.eval a0 := by
        calc
          e.toRingHom (G.derivative.eval (e.symm a0)) =
              e.toRingHom (((Polynomial.map e.symm.toRingHom F).derivative).eval (e.symm a0)) := by
                rfl
          _ = e.toRingHom ((Polynomial.map e.symm.toRingHom F.derivative).eval (e.symm a0)) := by
                rw [Polynomial.derivative_map]
          _ = F.derivative.eval a0 := by
                simpa using ringEquiv_map_symm_eval (e := e) (F := F.derivative) (a := a0)
      exact congrArg (Ideal.Quotient.mk (Ideal.map e.toRingHom I)) hEvalDeriv
    have hG_deriv_eval_pre :
        IsUnit ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0))) := by
      -- Pull the derivative unit back through the quotient equivalence.
      have hTarget :
          IsUnit (qEquiv ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0)))) := by
        rw [hG_deriv_eval_map]
        exact hderiv
      have hPre := IsUnit.map qEquiv.symm.toRingHom hTarget
      have hPreEq :
          qEquiv.symm (qEquiv ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0)))) =
            (Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0)) := by
        simpa using
          qEquiv.symm_apply_apply ((Ideal.Quotient.mk I) (G.derivative.eval (e.symm a0)))
      exact hPreEq ▸ hPre
    obtain ⟨a, ha_root, ha_mem⟩ :=
      HenselianRing.is_henselian (R := R) (I := I) G hG_monic (e.symm a0) hG_eval hG_deriv_eval_pre
    refine ⟨e a, ?_, ?_⟩
    · -- Push the root of the pulled-back polynomial forward to a root of the original one.
      apply Polynomial.IsRoot.def.mpr
      calc
        F.eval (e a) = e.toRingHom (G.eval a) := by
          symm
          simpa [G] using ringEquiv_map_symm_eval (e := e) (F := F) (a := e a)
        _ = 0 := by
          simpa [Polynomial.IsRoot.def.mp ha_root]
    · -- Push the congruence class forward to the mapped ideal.
      have hmemMapped : e.toRingHom (a - e.symm a0) ∈ Ideal.map e.toRingHom I :=
        Ideal.mem_map_of_mem e.toRingHom ha_mem
      simpa using hmemMapped

/-- Helper for Lemma 15.11.15: the stage ideals in the constant direct-limit system form a
directed family. -/
lemma henselian_ideal_directLimit_family_directed :
    Directed (· ≤ ·) fun J : HenselianIdealIndex =>
      Ideal.map (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition J) (J : Ideal A) := by
  -- The constant-system compatibility maps are identities, so Lemma `15.11.13` applies directly.
  exact directLimit_ideal_family_directed
    (A := HenselianIdealConst)
    (I := fun J : HenselianIdealIndex ↦ (J : Ideal A))
    (f := HenselianIdealTransition)
    (fun {_ _} h ↦ by simpa using h)

/-- Helper for Lemma 15.11.15: the supremum defining `largestHenselianIdeal` can be rewritten as
an indexed supremum over the subtype of henselian ideals. -/
lemma largestHenselianIdeal_eq_iSup_henselianIdeals :
    largestHenselianIdeal = ⨆ J : HenselianIdealIndex, (J : Ideal A) := by
  -- Compare the two ideals using their universal upper-bound properties in the ideal lattice.
  apply le_antisymm
  · refine sSup_le ?_
    intro I hI
    exact le_iSup (fun J : HenselianIdealIndex ↦ (J : Ideal A)) ⟨I, hI⟩
  · refine iSup_le ?_
    intro J
    exact le_sSup J.property

/-- Helper for Lemma 15.11.15: the colimit ideal from the constant system identifies with the
supremum of all henselian ideals of `A`. -/
lemma map_constant_directLimit_ideal_eq_largestHenselianIdeal :
    Ideal.map (henselianIdealConstDirectLimitEquiv (A := A)).toRingHom HenselianIdealColimitIdeal =
      largestHenselianIdeal := by
  -- Push the colimit ideal through the constant-system equivalence stagewise.
  calc
    Ideal.map (henselianIdealConstDirectLimitEquiv (A := A)).toRingHom HenselianIdealColimitIdeal =
        ⨆ J : HenselianIdealIndex,
          Ideal.map (henselianIdealConstDirectLimitEquiv (A := A)).toRingHom
            (Ideal.map (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition J)
              (J : Ideal A)) := by
            rw [Ideal.map_iSup]
    _ = ⨆ J : HenselianIdealIndex, (J : Ideal A) := by
          congr with J
          have hComp :
              RingHom.comp (henselianIdealConstDirectLimitEquiv (A := A)).toRingHom
                (Ring.DirectLimit.of HenselianIdealConst HenselianIdealTransition J) = RingHom.id A := by
            ext x
            exact henselianIdealConstDirectLimitEquiv_apply_of (A := A) J x
          rw [Ideal.map_map, hComp, Ideal.map_id]
    _ = largestHenselianIdeal := by
          rw [largestHenselianIdeal_eq_iSup_henselianIdeals (A := A)]

-- Proof sketch: henselian ideals are closed under finite sums by Lemma `15.11.10`, so the set of
-- henselian ideals is directed under inclusion after replacing any pair by their sum. Apply Lemma
-- `15.11.13` to the constant directed system indexed by henselian ideals with identity transition
-- maps. The resulting direct-limit ideal is exactly the supremum of all henselian ideals.
/-- The supremum of all henselian ideals of `A` is henselian. -/
instance largestHenselianIdeal_henselianRing :
    HenselianRing A largestHenselianIdeal := by
  have hCompat :
      ∀ ⦃J K : HenselianIdealIndex⦄ (h : J ≤ K),
        Ideal.map (HenselianIdealTransition J K h) (J : Ideal A) ≤ (K : Ideal A) := by
    intro J K h
    simpa using h
  have hColimit : HenselianRing HenselianIdealDirectLimit HenselianIdealColimitIdeal := by
    -- Lemma `15.11.13` applies to the constant system of henselian ideals.
    let _ : ∀ J : HenselianIdealIndex, HenselianRing A (J : Ideal A) := fun J ↦ J.2
    exact directedSystem_directLimit_henselianRing
      (A := HenselianIdealConst)
      (I := fun J : HenselianIdealIndex ↦ (J : Ideal A))
      (f := HenselianIdealTransition)
      hCompat
  have hMapped :
      HenselianRing A
        (Ideal.map (henselianIdealConstDirectLimitEquiv (A := A)).toRingHom HenselianIdealColimitIdeal) := by
    -- Transport the colimit henselian pair back to `A` along the constant-system equivalence.
    let _ : HenselianRing HenselianIdealDirectLimit HenselianIdealColimitIdeal := hColimit
    exact henselianRing_map_of_equiv
      (e := henselianIdealConstDirectLimitEquiv (A := A))
      HenselianIdealColimitIdeal
  -- Reidentify the transported ideal with the supremum used in the file-level definition.
  rw [map_constant_directLimit_ideal_eq_largestHenselianIdeal (A := A)] at hMapped
  exact hMapped

/-- Every henselian ideal of `A` is contained in the largest henselian ideal. -/
theorem le_largestHenselianIdeal (I : Ideal A) [HenselianRing A I] :
    I ≤ largestHenselianIdeal := by
  exact le_sSup (show HenselianRing A I from inferInstance)

/-- The largest henselian ideal is the greatest henselian ideal of `A`. -/
theorem isGreatest_largestHenselianIdeal :
    IsGreatest {I : Ideal A | HenselianRing A I} largestHenselianIdeal := by
  refine ⟨show HenselianRing A largestHenselianIdeal from inferInstance, ?_⟩
  intro I hI
  let _ : HenselianRing A I := hI
  exact le_largestHenselianIdeal I

/-- Lemma 15.11.15: in a commutative ring `A`, there exists a henselian ideal containing every
henselian ideal of `A`; equivalently, there is a largest ideal `I` such that `(A, I)` is a
henselian pair. -/
theorem exists_largest_henselianIdeal :
    ∃ I : Ideal A, HenselianRing A I ∧ ∀ J : Ideal A, HenselianRing A J → J ≤ I := by
  refine ⟨largestHenselianIdeal, inferInstance, ?_⟩
  intro J hJ
  let _ : HenselianRing A J := hJ
  exact le_largestHenselianIdeal J

end
