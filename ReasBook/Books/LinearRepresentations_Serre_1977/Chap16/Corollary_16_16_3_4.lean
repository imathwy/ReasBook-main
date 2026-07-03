import Mathlib
import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap16.Proposition_16_16_3_3
import Serre.Chap16.Theorem_16_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G))

/-- Helper for Corollary 16-16.3-4: the Chapter `16` character criterion for the range of Serre's
scalar-extension map, specialized to an actual finite-dimensional representation. -/
private theorem
    finiteRepClass_mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
    (V : FDRep K G) :
    [V]₀ ∈ (e).range ↔
      ∀ g : G, ¬ IsPRegular p g → V.character g = 0 := by
  -- Rewrite the Chapter `16` range criterion on the actual class `[V]₀`.
  simpa [finiteRepGrothendieckCharacter_class] using
    (mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
      (A := A) (K := K) (G := G) (p := p) [V]₀)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Corollary 16-16.3-4: the Grothendieck class of an actual finite-dimensional
`K[G]`-representation lies in Serre's positive subset `R_K^+(G)`. -/
private theorem finiteRepGrothendieckClass_mem_positiveSubset
    {K : Type u} [Field K] {G : Type u} [Group G] (V : FDRep K G) :
    [V]₀ ∈ R⁺[K](G) := by
  -- Unpack Serre's positive subset as the range of actual finite-dimensional representations.
  exact (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).2 ⟨V, rfl⟩

omit [IsFractionRing A K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Corollary 16-16.3-4: a lifted residue-field projective class maps to the scalar
extension class of some lift. -/
private theorem residueField_projective_class_has_scalarExtension_lift
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ = [Q.scalarExtension K]₀ := by
  -- First lift the projective residue-field module to an honest projective `A[G]`-module.
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) F
  refine ⟨Q, ?_⟩
  -- Convert the reduction isomorphism into equality of projective classes, then evaluate Serre's
  -- scalar-extension map on the resulting generator.
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [F]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [F]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred
  calc
    projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ =
        projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
    _ = [Q.scalarExtension K]₀ := by
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Corollary 16-16.3-4: Serre's reverse bridge turns actual range membership into an
actual projective `A[G]`-lift. -/
private theorem reverse_projectiveScalarExtensionClass_of_mem_range
    (hR : SatisfiesConditionR (R⁺[K](G)) A)
    (V : FDRep K G)
    (hmem : [V]₀ ∈ (e).range) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ := by
  -- Actual finite-dimensional representations lie in Serre's positive subset.
  have hactual : [V]₀ ∈ R⁺[K](G) :=
    finiteRepGrothendieckClass_mem_positiveSubset (K := K) (G := G) V
  have himage : [V]₀ ∈ e '' P⁺[k](G) := by
    have hinter : [V]₀ ∈ ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := ⟨hmem, hactual⟩
    -- Route correction: now that Proposition `16-16.3-3` is imported directly, use Serre's
    -- canonical image/range identity instead of the old local placeholder.
    rw [← SatisfiesConditionR.image_eq_range_inter_positive
      (A := A) (K := K) (G := G) hR] at hinter
    exact hinter
  rcases himage with ⟨x, hx, hxV⟩
  rcases (mem_projectivePositiveSubset_iff (A := k) (G := G)).1 hx with ⟨F, rfl⟩
  obtain ⟨Q, hQ⟩ :=
    residueField_projective_class_has_scalarExtension_lift
      (A := A) (K := K) (G := G) F
  refine ⟨Q, ?_⟩
  -- The residue-field projective witness now closes the original scalar-extension class.
  calc
    [Q.scalarExtension K]₀ =
        projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ := by
          simpa using hQ.symm
    _ = [V]₀ := hxV

/- 
Domain-style sampling for Corollary 16-16.3-4:
* primary domain: modular representation theory via the Grothendieck-group image of the canonical
  scalar-extension owner `projectiveGrothendieckScalarExtensionHom A K`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `SatisfiesConditionR.image_eq_range_inter_positive`,
  `mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular`,
  `FiniteProjectiveGroupAlgebraModule.exists_residueFieldReduction_iso`;
* best owner abstraction: membership of the actual class `[V]₀` in the canonical range `e.range`.

Source/core/bridge triage:
* source-facing: existence of a finite projective `A[G]`-module whose scalar-extension class in
  `R₀[K](G)` equals the actual Grothendieck class `[V]₀`;
* core/canonical: the range of `e` and the Chapter `16` character-vanishing criterion for that
  range;
* bridge/view: the companion theorem below, which identifies the source-facing lifting statement
  with the canonical range condition under Serre's hypothesis `(R)`.

Primitive data vs derived API:
* primitive data here: the actual finite-dimensional representation `V` and the condition
  `(R)` on `R⁺[K](G)`;
* derived API: the range-membership bridge and the final character criterion.
-/

-- Proof sketch: Proposition `16-16.3-3`, exposed as
-- `SatisfiesConditionR.image_eq_range_inter_positive`, identifies the actual projective image
-- `e '' P⁺[k](G)`
-- with the intersection `e.range ∩ R⁺[K](G)`. Since `[V]₀` is automatically actual, this turns
-- existence of a finite projective `A[G]`-module whose scalar-extension class equals `[V]₀` into
-- membership of `[V]₀` in `e.range`. Theorem `16-16.2-1` then rewrites that range condition as
-- vanishing of the ordinary character of `V` on `p`-singular elements; the reverse direction
-- additionally needs the Chapter `14` projective lifting theorem over a henselian local ring.
omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Under condition `(R)`, the Grothendieck class of an actual finite-dimensional
`K[G]`-representation is a projective scalar-extension class, meaning
`[V]₀ = [P.scalarExtension K]₀` for some finite projective `A[G]`-module `P`, exactly when
`[V]₀` lies in the range of Serre's canonical scalar-extension homomorphism
`e : P_k(G) → R_K(G)`. -/
theorem
    finiteRep_has_projectiveScalarExtensionClass_iff_mem_projectiveGrothendieckScalarExtension_range
    (hR : SatisfiesConditionR (R⁺[K](G)) A)
    (V : FDRep K G) :
    (∃ P : FiniteProjectiveGroupAlgebraModule A G, [P.scalarExtension K]₀ = [V]₀) ↔
      [V]₀ ∈ (e).range := by
  constructor
  · rintro ⟨P, hP⟩
    -- An actual lifted projective module gives an explicit witness in the range of `e`.
    refine ⟨projectiveGrothendieckReductionEquiv (A := A) (G := G) [P]ₚ₀, ?_⟩
    calc
      projectiveGrothendieckScalarExtensionHom A K
          ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [P]ₚ₀) =
          [P.scalarExtension K]₀ := by
            have hred :
                (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
                    ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [P]ₚ₀) = [P]ₚ₀ := by
              exact
                (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_apply [P]ₚ₀
            rw [projectiveGrothendieckScalarExtensionHom_apply]
            rw [hred]
            exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) P
      _ = [V]₀ := hP
  · intro hmem
    -- Route correction: use Serre's canonical
    -- `e.range ∩ R⁺[K](G) -> e '' P⁺[k](G) -> F -> Q`
    -- bridge rather than the old local placeholder chain.
    exact
      reverse_projectiveScalarExtensionClass_of_mem_range
        (A := A) (K := K) (G := G) (hR := hR) V hmem

/-- Corollary 16-16.3-4: if Serre's condition `(R)` holds for the actual positive subset
`R_K^+(G)`, then the Grothendieck class of a finite-dimensional `K`-representation of `G` is a
projective scalar-extension class, equivalently `[V]₀ = [P.scalarExtension K]₀` for some finite
projective `A[G]`-module `P`, if and only if its ordinary character vanishes on the
`p`-singular elements of `G`. -/
theorem finiteRep_has_projectiveScalarExtensionClass_iff_character_eq_zero_on_pSingular
    (hR : SatisfiesConditionR (R⁺[K](G)) A)
    (V : FDRep K G) :
    (∃ P : FiniteProjectiveGroupAlgebraModule A G,
      [P.scalarExtension K]₀ = [V]₀) ↔
      ∀ g : G, ¬ IsPRegular p g → V.character g = 0 := by
  constructor
  · intro hP
    -- Pass from an actual projective lift to range membership, then invoke the character test.
    have hrange :
        [V]₀ ∈ (e).range :=
      (finiteRep_has_projectiveScalarExtensionClass_iff_mem_projectiveGrothendieckScalarExtension_range
        (hR := hR) V).1 hP
    exact
      (finiteRepClass_mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
        (A := A) (K := K) (G := G) (p := p) V).1 hrange
  · intro hχ
    -- First rewrite the character vanishing hypothesis as membership in the scalar-extension
    -- range, then invoke the structural bridge proved just above.
    have hrange : [V]₀ ∈ (e).range :=
      (finiteRepClass_mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
        (A := A) (K := K) (G := G) (p := p) V).2 hχ
    exact
      (finiteRep_has_projectiveScalarExtensionClass_iff_mem_projectiveGrothendieckScalarExtension_range
        (hR := hR) V).2 hrange

end

end Representation
