import StacksProject_2024.Chap10.Definition_10_141_1
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace RingHom

open IsLocalRing

/-
Domain-style sampling for Lemma 15.38.1:
- primary domain: infinitesimal lifting criteria for formal smoothness of local ring maps in
  maximal-ideal adic topology;
- inspected owner declarations of the same kind:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.FormallySmooth.exists_lift`,
  * `IsLocalRing.of_surjective'`,
  * `RingHom.IsSmallExtension.isLocalRingTarget`;
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner, while the local
  extension-map facts should be expressed through the canonical local-ring derivation owners
  `IsLocalRing.of_surjective'` and `IsSmallExtension.isLocalRingTarget`; in particular, the target
  local structure for a square-zero surjection or small extension is derived internally rather than
  stored as extra theorem-level data. The lift itself is the same derived payload as in
  `RingHom.FormallySmooth.exists_lift`;
- primitive data on the right-hand side: the chosen square-zero surjection or small extension
  `π : A' →+* A`, the local map `g : S →+* A`, the nilpotence of `maximalIdeal A'`, the
  residue-field bijectivity, and the commutative square;
- derived API: the existential lift payload, and the locality of any lift `S →+* A`, which should
  not be primitive public data in this bridge theorem.

Source/core/bridge triage:
- `source-facing`: the local lifting criteria against square-zero and small extensions;
- `core/canonical`: `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the equivalences below, which compare the owner predicate with those lifting
  criteria.
-/

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

private abbrev maximalIdealAdic_liftPayload
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (f : R →+* S) (π : A' →+* A) (g : S →+* A) (g0 : R →+* A') : Prop :=
  ∃ gLift : S →+* A', π.comp gLift = g ∧ gLift.comp f = g0

private theorem maximalIdealAdic_nontrivialTarget_of_squareZero
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsq : RingHom.ker π ^ 2 = ⊥) : Nontrivial A := by
  classical
  by_contra hA
  letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
  have hker : RingHom.ker π = ⊤ := by
    ext x
    simp [RingHom.mem_ker, Subsingleton.elim (π x) 0]
  have h1sq : (1 : A') ∈ RingHom.ker π ^ 2 := by
    rw [pow_two, hker]
    simpa using Ideal.mul_mem_mul (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
      (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
  have h1 : (1 : A') = 0 := by
    have hmem : (1 : A') ∈ (⊥ : Ideal A') := by
      exact hπsq ▸ h1sq
    exact hmem
  let _ : Nontrivial A' := IsLocalRing.toNontrivial
  exact one_ne_zero h1

private abbrev maximalIdealAdic_residueFieldMapBijective
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
  letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
  Function.Bijective (ResidueField.map g)

private theorem maximalIdealAdic_isLocalRingTargetOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [hπ : IsSmallExtension π] : IsLocalRing A := by
  let _ : Nontrivial A := hπ.instNontrivialTarget
  exact IsLocalRing.of_surjective' π hπ.surjective

private abbrev maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := inferInstance
  letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
  Function.Bijective (ResidueField.map g)

/-- The square-zero local lifting condition appearing in Lemma 15.38.1. The target local-ring
structure is derived canonically from the surjective map `π : A' → A`, so it is not part of the
public data of the condition. -/
abbrev maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (_ : IsNilpotent (maximalIdeal A')) (g : S →+* A),
      let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
      letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijective π hπsurj hπsq g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

/-- The small-extension local lifting condition appearing in the Noetherian refinement of Lemma
15.38.1. The target local-ring structure is derived canonically from the owner predicate
`IsSmallExtension π`, so only the actual extension and residue-field data remain visible. -/
abbrev maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A),
      letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension π g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

-- Proof sketch: use Lemma `15.37.2` to identify formal smoothness for the maximal-ideal-adic
-- topology with the discrete-source lifting property, then restrict the test objects to local
-- square-zero extensions with nilpotent maximal ideal and residue-field isomorphism. For the
-- converse, replace an arbitrary square-zero lifting problem by the inverse-image local subring
-- generated by the image of `S` in `A ⧸ J`, exactly as in the Stacks argument. The lifted ring
-- hom is automatically local because its composite with the quotient map is `g`.
/-- Lemma 15.38.1: a local homomorphism `f : R →+* S` is formally smooth for the maximal-ideal-adic
topology on `S` if and only if every square-zero lifting problem against a local ring `A` with
nilpotent maximal ideal and residue-field isomorphism `S → A ⧸ J` admits a lift
(hence automatically a local lift). -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_square_zero_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition f := sorry

-- Proof sketch: the forward implication is the main equivalence above. For the converse under the
-- Noetherian hypothesis on `S`, devissage through the filtration of `J` by one-dimensional
-- residue-field quotients reduces the square-zero criterion to the case where `A → A ⧸ J` is a
-- small extension, and then the assumed lifting property supplies the required lift, which is
-- again automatically local.
/-- The Noetherian refinement of the local lifting criterion: it is enough to test liftings only
against small extensions `A → A ⧸ J` with the same residue-field condition, asking only for a
lift in the conclusion since locality is derived. -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_smallExtension_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition f := sorry

end

end RingHom
