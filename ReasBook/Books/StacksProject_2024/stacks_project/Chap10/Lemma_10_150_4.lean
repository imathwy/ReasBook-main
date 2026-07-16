import StacksProject_2024.stacks_project.Chap10.Lemma_10_106_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

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
  sorry

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
