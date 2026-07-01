import stacks_project.Chap10.Lemma_10_106_8
import stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

/-
Domain-style sampling:
- primary domain: formal étaleness of commutative algebras and directed colimits of `R`-algebras;
- sampled owner API:
  `Algebra.FormallyEtale`,
  `RingHom.formallyEtale_algebraMap`,
  `RingHom.FormallyEtale`,
  `Ring.DirectLimit.of`,
  `Ring.DirectLimit.of_f`;
- source-facing: the textbook lemma that a directed colimit of formally étale `R`-algebras is
  again formally étale over `R`;
- core/canonical: formal étaleness is owned by `Algebra.FormallyEtale`, with the canonical
  structure-map view recovered through `RingHom.formallyEtale_algebraMap`;
- bridge/view: the canonical direct-limit map `R →+* S∞` is the owner from which the direct-limit
  `Algebra R S∞` structure should be derived publicly.

Primitive data are the stage `R`-algebras and the directed system of `R`-algebra maps. The
compatibility of transition maps with `algebraMap` is derived from `AlgHom.commutes`, so it should
not remain a separate public hypothesis. The direct-limit `R`-algebra structure is derived API
coming from the canonical map `R →+* S∞`.
-/
variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (S : I → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable (φ : ∀ i j, i ≤ j → S i →ₐ[R] S j)
variable [DirectedSystem S fun i j h ↦ (φ i j h : S i →+* S j)]

local notation "ρ" => (fun i j h ↦ (φ i j h : S i →+* S j))
local notation "S∞" => Ring.DirectLimit S ρ

namespace Ring.DirectLimit

local notation "Rconst" => fun _ : I ↦ R
local notation "ιR" => fun _ _ _ ↦ (RingHom.id R : R →+* R)
local notation "R∞" => Ring.DirectLimit Rconst ιR

local instance directedSystemConst : DirectedSystem Rconst ιR where
  map_self := by
    intro i x
    rfl
  map_map := by
    intro k j i hij hjk x
    rfl

omit [Nonempty I] [IsDirectedOrder I] in
private lemma ofConst_f {i j : I} (hij : i ≤ j) (r : R) :
    Ring.DirectLimit.of Rconst ιR j r = Ring.DirectLimit.of Rconst ιR i r := by
  simpa using (@Ring.DirectLimit.of_f I _ Rconst _ ιR i j hij r)

/-- The canonical map from the direct limit of the constant `R`-system to the direct limit of the
given system of `R`-algebras. -/
private noncomputable def fromConst : R∞ →+* S∞ :=
  Ring.DirectLimit.lift Rconst ιR S∞
    (fun i ↦ (Ring.DirectLimit.of S ρ i).comp (_root_.algebraMap R (S i)))
    fun i j hij r ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [show _root_.algebraMap R (S j) r = (φ i j hij) (_root_.algebraMap R (S i) r) from
        ((φ i j hij).commutes r).symm]
      exact Ring.DirectLimit.of_f hij (_root_.algebraMap R (S i) r)

/-- The direct limit of the constant `R`-system is canonically isomorphic to `R`. -/
private noncomputable def constEquiv : R∞ ≃+* R :=
  RingEquiv.ofRingHom
    (Ring.DirectLimit.lift Rconst ιR R (fun _ ↦ RingHom.id R) fun _ _ _ _ ↦ rfl)
    (Ring.DirectLimit.of Rconst ιR (Classical.arbitrary I))
    (by
      ext r
      simp only [Ring.DirectLimit.lift_of, RingHom.comp_apply, RingHom.id_apply])
    (by
      apply RingHom.ext
      intro z
      classical
      induction z using Ring.DirectLimit.induction_on with
      | ih i r =>
          let i₀ : I := Classical.arbitrary I
          rcases exists_ge_ge i i₀ with ⟨j, hij, hi₀j⟩
          simpa only [RingHom.comp_apply, Ring.DirectLimit.lift_of, RingHom.id_apply] using
            (show Ring.DirectLimit.of Rconst ιR i₀ r = Ring.DirectLimit.of Rconst ιR i r from by
              calc
                Ring.DirectLimit.of Rconst ιR i₀ r =
                    Ring.DirectLimit.of Rconst ιR j ((RingHom.id R) r) := by
                      symm
                      exact ofConst_f hi₀j r
                _ = Ring.DirectLimit.of Rconst ιR j r := rfl
                _ = Ring.DirectLimit.of Rconst ιR i r := by
                      exact ofConst_f hij r))

private lemma constEquiv_symm_of (i : I) (r : R) :
    constEquiv.symm r = Ring.DirectLimit.of Rconst ιR i r := by
  classical
  let i₀ : I := Classical.arbitrary I
  change Ring.DirectLimit.of Rconst ιR i₀ r = Ring.DirectLimit.of Rconst ιR i r
  rcases exists_ge_ge i i₀ with ⟨j, hij, hi₀j⟩
  calc
    Ring.DirectLimit.of Rconst ιR i₀ r =
        Ring.DirectLimit.of Rconst ιR j ((RingHom.id R) r) := by
          symm
          exact ofConst_f hi₀j r
    _ = Ring.DirectLimit.of Rconst ιR j r := rfl
    _ = Ring.DirectLimit.of Rconst ιR i r := by
          exact ofConst_f hij r

/-- The canonical map from `R` to the direct limit of a directed system of `R`-algebras. -/
noncomputable def algebraMap : R →+* S∞ :=
  (fromConst S φ).comp constEquiv.symm.toRingHom

/-- The directed colimit ring carries the canonical `R`-algebra structure induced from the stage
algebras. -/
noncomputable instance instAlgebra : Algebra R S∞ :=
  (Ring.DirectLimit.algebraMap S φ).toAlgebra

-- Proof sketch: identify `r : R` with its image in the direct limit of the constant `R`-system,
-- then evaluate the canonical lift on that stage representative.
omit [DirectedSystem S fun i j h ↦ (φ i j h : S i →+* S j)] in
theorem algebraMap_eq_of (i : I) (r : R) :
    _root_.algebraMap R S∞ r = Ring.DirectLimit.of S ρ i (_root_.algebraMap R (S i) r) := by
  change Ring.DirectLimit.algebraMap S φ r =
    Ring.DirectLimit.of S ρ i (_root_.algebraMap R (S i) r)
  rw [Ring.DirectLimit.algebraMap]
  change (fromConst S φ) (constEquiv.symm r) =
    Ring.DirectLimit.of S ρ i (_root_.algebraMap R (S i) r)
  rw [show constEquiv.symm r = Ring.DirectLimit.of Rconst ιR i r from constEquiv_symm_of i r]
  simp only [fromConst, RingHom.comp_apply, Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.150.4: the canonical map from a stage into the direct limit is an
`R`-algebra homomorphism. -/
theorem ofAlgHom_commutes (i : I) (r : R) :
    Ring.DirectLimit.of S ρ i (_root_.algebraMap R (S i) r) = _root_.algebraMap R S∞ r := by
  -- The direct-limit `R`-algebra structure was defined so that every stage map is `R`-linear.
  symm
  exact Ring.DirectLimit.algebraMap_eq_of S φ i r

/-- Helper for Lemma 10.150.4: the stage map into the direct limit as an `R`-algebra homomorphism.
-/
noncomputable def ofAlgHom (i : I) : S i →ₐ[R] S∞ :=
  { toRingHom := Ring.DirectLimit.of S ρ i
    commutes' := ofAlgHom_commutes S φ i }

/-- Helper for Lemma 10.150.4: the direct-limit stage embeddings respect the transition maps. -/
theorem ofAlgHom_comp_transition {i j : I} (hij : i ≤ j) :
    (ofAlgHom S φ j).comp (φ i j hij) = ofAlgHom S φ i := by
  -- This is the direct-limit relation `of_j ∘ φ_ij = of_i` rewritten at the `AlgHom` level.
  ext x
  exact Ring.DirectLimit.of_f hij x

/-- Helper for Lemma 10.150.4: the ring maps underlying a compatible family of stage algebra maps
respect the directed system. -/
theorem liftAlgHom_ring_compatible {A : Type*} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i) :
    ∀ i j hij x, g j (φ i j hij x) = g i x := by
  intro i j hij x
  exact DFunLike.congr_fun (hg i j hij) x

/-- Helper for Lemma 10.150.4: the universal-property lift of a compatible family of stage algebra
maps preserves the `R`-algebra structure. -/
theorem liftAlgHom_commutes {A : Type*} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i)
    (r : R) :
    Ring.DirectLimit.lift S ρ A (fun i ↦ (g i).toRingHom)
      (liftAlgHom_ring_compatible S φ g hg) (_root_.algebraMap R S∞ r) =
        _root_.algebraMap R A r := by
  classical
  let i : I := Classical.arbitrary I
  -- Evaluate the direct-limit lift on a stage representative of the scalar `r`.
  calc
    Ring.DirectLimit.lift S ρ A (fun i ↦ (g i).toRingHom)
        (liftAlgHom_ring_compatible S φ g hg) (_root_.algebraMap R S∞ r) =
      Ring.DirectLimit.lift S ρ A (fun i ↦ (g i).toRingHom)
        (liftAlgHom_ring_compatible S φ g hg)
          (Ring.DirectLimit.of S ρ i (_root_.algebraMap R (S i) r)) := by
            rw [Ring.DirectLimit.algebraMap_eq_of S φ i r]
    _ = (g i).toRingHom (_root_.algebraMap R (S i) r) := by
          simp only [Ring.DirectLimit.lift_of]
    _ = g i (_root_.algebraMap R (S i) r) := rfl
    _ = _root_.algebraMap R A r := by
          exact (g i).commutes r

/-- Helper for Lemma 10.150.4: a compatible family of stage algebra maps assembles to an algebra
map out of the direct limit. -/
noncomputable def liftAlgHom {A : Type*} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i) :
    S∞ →ₐ[R] A :=
  { toRingHom := Ring.DirectLimit.lift S ρ A (fun i ↦ (g i).toRingHom)
      (liftAlgHom_ring_compatible S φ g hg)
    commutes' := liftAlgHom_commutes S φ g hg }

/-- Helper for Lemma 10.150.4: the assembled direct-limit algebra map restricts to the prescribed
stage map. -/
theorem liftAlgHom_of {A : Type*} [CommRing A] [Algebra R A]
    (g : ∀ i, S i →ₐ[R] A)
    (hg : ∀ i j hij, (g j).comp (φ i j hij) = g i)
    (i : I) :
    (liftAlgHom S φ g hg).comp (ofAlgHom S φ i) = g i := by
  -- The assembled map was defined by the universal property of the direct limit.
  ext x
  change Ring.DirectLimit.lift S ρ A (fun j ↦ (g j).toRingHom)
      (liftAlgHom_ring_compatible S φ g hg) (Ring.DirectLimit.of S ρ i x) = g i x
  rw [Ring.DirectLimit.lift_of]
  rfl

/-- Helper for Lemma 10.150.4: algebra maps out of the direct limit are determined by their
restrictions to every stage. -/
theorem algHom_ext_of_stagewise {A : Type*} [CommRing A] [Algebra R A]
    {f g : S∞ →ₐ[R] A}
    (h : ∀ i, f.comp (ofAlgHom S φ i) = g.comp (ofAlgHom S φ i)) :
    f = g := by
  -- Every element of the direct limit comes from a stage, so stagewise agreement is enough.
  ext x
  induction x using Ring.DirectLimit.induction_on with
  | ih i x =>
      simpa only [ofAlgHom] using DFunLike.congr_fun (h i) x

/-- Helper for Lemma 10.150.4: a formally étale stage has the square-zero lifting bijection
against test rings living in the direct-limit universe. -/
theorem stage_comp_bijective {A : Type (max u v w)} [CommRing A] [Algebra R A]
    (i : I) (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (hEti : Algebra.FormallyEtale R (S i)) :
    Function.Bijective ((Ideal.Quotient.mkₐ R J).comp : (S i →ₐ[R] A) → S i →ₐ[R] A ⧸ J) := by
  -- Route correction: ULift the stage algebra to the direct-limit universe, apply the owner
  -- bijectivity theorem there, and transport the result back along the induced equivalences.
  let e : ULift.{v} (S i) ≃ₐ[R] S i := ULift.algEquiv (R := R) (A := S i)
  let domEquiv : (S i →ₐ[R] A) ≃ (ULift.{v} (S i) →ₐ[R] A) :=
    AlgEquiv.arrowCongr (R := R) e.symm (AlgEquiv.refl : A ≃ₐ[R] A)
  let codEquiv : (S i →ₐ[R] A ⧸ J) ≃ (ULift.{v} (S i) →ₐ[R] A ⧸ J) :=
    AlgEquiv.arrowCongr (R := R) e.symm (AlgEquiv.refl : (A ⧸ J) ≃ₐ[R] (A ⧸ J))
  have hEt_ulift : Algebra.FormallyEtale R (ULift.{v} (S i)) := by
    exact Algebra.FormallyEtale.of_equiv (A := S i) (B := ULift.{v} (S i)) e.symm
  have hbij_ulift :
      Function.Bijective
        ((Ideal.Quotient.mkₐ R J).comp :
          (ULift.{v} (S i) →ₐ[R] A) → ULift.{v} (S i) →ₐ[R] A ⧸ J) :=
    (Algebra.FormallyEtale.iff_comp_bijective.mp hEt_ulift) J hJ
  have hcomm :
      ∀ f : S i →ₐ[R] A,
        codEquiv ((Ideal.Quotient.mkₐ R J).comp f) =
          (Ideal.Quotient.mkₐ R J).comp (domEquiv f) := by
    intro f
    rfl
  refine ⟨?_, ?_⟩
  · intro f₁ f₂ h
    apply domEquiv.injective
    apply hbij_ulift.injective
    simpa [hcomm] using congrArg codEquiv h
  · intro g
    obtain ⟨g', hg'⟩ := hbij_ulift.surjective (codEquiv g)
    refine ⟨domEquiv.symm g', ?_⟩
    apply codEquiv.injective
    calc
      codEquiv ((Ideal.Quotient.mkₐ R J).comp (domEquiv.symm g')) =
          (Ideal.Quotient.mkₐ R J).comp (domEquiv (domEquiv.symm g')) := by
            simpa [hcomm] using hcomm (domEquiv.symm g')
      _ = (Ideal.Quotient.mkₐ R J).comp g' := by
            rw [domEquiv.apply_symm_apply]
      _ = codEquiv g := hg'

/-- Helper for Lemma 10.150.4: the uniquely chosen lifts on the stages are compatible with the
transition maps. -/
theorem stage_lifts_compatible {A : Type (max u v w)} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (g : S∞ →ₐ[R] A ⧸ J)
    (ℓ : ∀ i, S i →ₐ[R] A)
    (hℓ : ∀ i, (Ideal.Quotient.mkₐ R J).comp (ℓ i) = g.comp (ofAlgHom S φ i))
    (hEt : ∀ i, Algebra.FormallyEtale R (S i)) :
    ∀ i j hij, (ℓ j).comp (φ i j hij) = ℓ i := by
  intro i j hij
  have hbij :
      Function.Bijective
        ((Ideal.Quotient.mkₐ R J).comp : (S i →ₐ[R] A) → S i →ₐ[R] A ⧸ J) :=
    stage_comp_bijective (S := S) i J hJ (hEt i)
  have hcomp :
      (Ideal.Quotient.mkₐ R J).comp ((ℓ j).comp (φ i j hij)) = g.comp (ofAlgHom S φ i) := by
    -- Both candidate lifts factor through the same stage map into the quotient.
    calc
      (Ideal.Quotient.mkₐ R J).comp ((ℓ j).comp (φ i j hij)) =
          ((Ideal.Quotient.mkₐ R J).comp (ℓ j)).comp (φ i j hij) := by
            rw [AlgHom.comp_assoc]
      _ = (g.comp (ofAlgHom S φ j)).comp (φ i j hij) := by
            rw [hℓ j]
      _ = g.comp ((ofAlgHom S φ j).comp (φ i j hij)) := by
            rw [AlgHom.comp_assoc]
      _ = g.comp (ofAlgHom S φ i) := by
            rw [ofAlgHom_comp_transition (S := S) (φ := φ) hij]
  exact hbij.injective (hcomp.trans (hℓ i).symm)

section Local

variable [IsLocalRing R] [∀ i, IsLocalRing (S i)]
variable [∀ i, IsLocalHom (_root_.algebraMap R (S i))]
variable [∀ i j hij, IsLocalHom (φ i j hij : S i →+* S j)]

/-- The canonical map from the base ring `R` to the direct limit of a directed system of local
`R`-algebras is a local ring homomorphism. -/
instance algebraMap_isLocalHom : IsLocalHom (_root_.algebraMap R S∞) := by
  sorry

end Local

-- Proof sketch: formal étaleness is owned by `Algebra.FormallyEtale`, so the directed-colimit
-- statement is most canonically proved on the induced `R`-algebra structure on `S∞`; the
-- source-facing ring-hom statement is then recovered by
-- `RingHom.formallyEtale_algebraMap`.
/-- The directed colimit of formally étale `R`-algebras is formally étale over `R`. -/
theorem formallyEtale
    (hEt : ∀ i, Algebra.FormallyEtale R (S i)) :
    Algebra.FormallyEtale R S∞ := by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr ?_
  intro A _ _ J hJ
  refine ⟨?_, ?_⟩
  · intro lift₁ lift₂ hLift
    -- Uniqueness reduces to injectivity of the stagewise quotient maps.
    apply algHom_ext_of_stagewise S φ
    intro i
    have hbij :
        Function.Bijective
          ((Ideal.Quotient.mkₐ R J).comp : (S i →ₐ[R] A) → S i →ₐ[R] A ⧸ J) :=
      stage_comp_bijective (S := S) i J hJ (hEt i)
    exact hbij.injective (congrArg (fun f : S∞ →ₐ[R] A ⧸ J => f.comp (ofAlgHom S φ i)) hLift)
  · intro g
    have stageLift_exists :
        ∀ i, ∃ l : S i →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp l = g.comp (ofAlgHom S φ i) := by
      intro i
      -- Each stage is formally étale, so the quotient map is surjective on lifts from that stage.
      exact (stage_comp_bijective (S := S) i J hJ (hEt i)).surjective
        (g.comp (ofAlgHom S φ i))
    let stageLift : ∀ i, S i →ₐ[R] A := fun i ↦ (stageLift_exists i).choose
    have stageLift_spec :
        ∀ i, (Ideal.Quotient.mkₐ R J).comp (stageLift i) = g.comp (ofAlgHom S φ i) := by
      intro i
      exact (stageLift_exists i).choose_spec
    have stageLift_compatible :
        ∀ i j hij, (stageLift j).comp (φ i j hij) = stageLift i := by
      -- Compatibility follows because two candidate lifts of the same stage map are equal.
      exact stage_lifts_compatible (S := S) (φ := φ) J hJ g stageLift stageLift_spec hEt
    let lift : S∞ →ₐ[R] A := liftAlgHom S φ stageLift stageLift_compatible
    refine ⟨lift, ?_⟩
    -- The assembled map is a lift because it agrees with `g` on every stage.
    apply algHom_ext_of_stagewise S φ
    intro i
    change (Ideal.Quotient.mkₐ R J).comp (lift.comp (ofAlgHom S φ i)) = g.comp (ofAlgHom S φ i)
    rw [liftAlgHom_of]
    exact stageLift_spec i

end Ring.DirectLimit

-- Proof sketch: use the infinitesimal lifting criterion for formal étaleness. For a square-zero
-- extension `A → A ⧸ J`, every stage map `R → S i` admits a unique lift `S i → A`; the
-- compatibility hypothesis on the transition maps makes these lifts compatible, so the universal
-- property of `Ring.DirectLimit` gives a unique lift from the direct limit.
/-- Lemma 10.150.4: the canonical map from `R` to the direct limit of a directed system of
`R`-algebras is formally étale if each stage structure map is formally étale. -/
theorem directLimit_formallyEtale
    (hEt : ∀ i, (algebraMap R (S i)).FormallyEtale) :
    (algebraMap R S∞).FormallyEtale := by
  rw [RingHom.formallyEtale_algebraMap]
  exact Ring.DirectLimit.formallyEtale S φ fun i ↦
    (RingHom.formallyEtale_algebraMap).mp (hEt i)

namespace RingHom

/-- A ring map that is a filtered colimit of étale algebras is formally étale. -/
theorem formallyEtale_of_isFilteredColimitOfEtale
    {A : Type w} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) :
    (algebraMap R A).FormallyEtale := by
  sorry

end RingHom

end
