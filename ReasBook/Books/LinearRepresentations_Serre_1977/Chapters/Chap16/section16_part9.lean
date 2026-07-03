import Mathlib
import Mathlib.Analysis.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_16_16_2_2 (from Chap16) -/
noncomputable section

universe u

namespace Representation

open scoped Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G

/- Domain-style sampling for Theorem 16-16.2-2:
* primary domain: modular representation theory on Grothendieck groups, combining LinearRepresentations_Serre_1977's
  projective scalar-extension map over a finite extension field with ordinary characters;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `IsValuedInBaseField`;
* best owner abstraction: the existing Chapter `15` and `16` scalar-extension owners on
  Grothendieck groups, namely
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`,
  together with the Chapter `16` character bridge and the Chapter `12` `K`-valuedness predicate
  on class functions;
* source/core/bridge triage:
  source-facing: the image criterion over the finite extension `K' / K`;
  core/canonical: `projectiveGrothendieckScalarExtensionHom A K`,
    `finiteRepGrothendieckScalarExtensionHom K K' G`,
    `finiteRepGrothendieckCharacter K' G`, and `IsValuedInBaseField K`;
  bridge/view: this theorem, which characterizes the range of the canonical composite of those
    scalar-extension owners by a base-field-valuedness condition plus vanishing on `p`-singular
    elements.

Primitive data vs derived API:
* primitive data: the canonical composite
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`;
* derived API: the character-theoretic criterion for membership in its range.
This file should therefore reuse those upstream owners directly and avoid introducing a parallel
public map declaration for their composite.
-/

-- Proof sketch: if `x` lies in the image of the finite-extension scalar-extension map
-- `P_k(G) → R_K'(G)`, then it comes by extension of scalars from a projective class over `K`, so
-- its ordinary character is the scalar extension of a `K`-valued character, so it is
-- `Representation.IsValuedInBaseField K`; Theorem `16-16.2-1` gives vanishing on `p`-singular
-- elements. Conversely, if the character of `x` is `K`-valued and vanishes on `p`-singular
-- elements, descend `x` to a class in `R_K(G)` and apply Theorem `16-16.2-1`, then re-extend
-- scalars to recover `x`.
/-- Theorem 16-16.2-2: for a finite extension `K' / K`, an element of `R_K'(G)` lies in the image
of the projective scalar-extension homomorphism `e : P_k(G) → R_K'(G)` exactly when its ordinary
character is `K`-valued and vanishes on every `p`-singular element of `G`. Here
`k = IsLocalRing.ResidueField A`. -/
theorem
    mem_projectiveScalarExtensionOverExtension_range_iff_valuedInBaseField_zero_on_pSingular
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K'](G)) :
    x ∈ ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckScalarExtensionHom A K) : P_k(G) →+ R₀[K'](G)).range ↔
      IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x) ∧
      ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := sorry

end

end Representation

/-! ### Corollary_16_16_3_4 (from Chap16) -/
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

/-- Helper for Corollary 16-16.3-4: the Chapter `16` character criterion for the range of LinearRepresentations_Serre_1977's
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
`K[G]`-representation lies in LinearRepresentations_Serre_1977's positive subset `R_K^+(G)`. -/
private theorem finiteRepGrothendieckClass_mem_positiveSubset
    {K : Type u} [Field K] {G : Type u} [Group G] (V : FDRep K G) :
    [V]₀ ∈ R⁺[K](G) := by
  -- Unpack LinearRepresentations_Serre_1977's positive subset as the range of actual finite-dimensional representations.
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
  -- Convert the reduction isomorphism into equality of projective classes, then evaluate LinearRepresentations_Serre_1977's
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
/-- Helper for Corollary 16-16.3-4: LinearRepresentations_Serre_1977's reverse bridge turns actual range membership into an
actual projective `A[G]`-lift. -/
private theorem reverse_projectiveScalarExtensionClass_of_mem_range
    (hR : SatisfiesConditionR (R⁺[K](G)) A)
    (V : FDRep K G)
    (hmem : [V]₀ ∈ (e).range) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ := by
  -- Actual finite-dimensional representations lie in LinearRepresentations_Serre_1977's positive subset.
  have hactual : [V]₀ ∈ R⁺[K](G) :=
    finiteRepGrothendieckClass_mem_positiveSubset (K := K) (G := G) V
  have himage : [V]₀ ∈ e '' P⁺[k](G) := by
    have hinter : [V]₀ ∈ ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := ⟨hmem, hactual⟩
    -- Route correction: now that Proposition `16-16.3-3` is imported directly, use LinearRepresentations_Serre_1977's
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
  with the canonical range condition under LinearRepresentations_Serre_1977's hypothesis `(R)`.

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
`[V]₀` lies in the range of LinearRepresentations_Serre_1977's canonical scalar-extension homomorphism
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
    -- Route correction: use LinearRepresentations_Serre_1977's canonical
    -- `e.range ∩ R⁺[K](G) -> e '' P⁺[k](G) -> F -> Q`
    -- bridge rather than the old local placeholder chain.
    exact
      reverse_projectiveScalarExtensionClass_of_mem_range
        (A := A) (K := K) (G := G) (hR := hR) V hmem

/-- Corollary 16-16.3-4: if LinearRepresentations_Serre_1977's condition `(R)` holds for the actual positive subset
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

/-! ### Exercise_16_16_3_7 (from Chap16) -/
noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {A : Type u} [CommRing A]
variable {A' : Type u} [CommRing A']
variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K']
variable [Algebra A K'] [Algebra A' K']
variable {G : Type u} [Group G] [Finite G]

local notation "eA" => (projectiveGrothendieckBaseChangeHom K' : P₀[A](G) →+ R₀[K'](G))
local notation "eA'" => (projectiveGrothendieckBaseChangeHom K' : P₀[A'](G) →+ R₀[K'](G))
local notation "eK" => (finiteRepGrothendieckScalarExtensionHom K K' G : R₀[K](G) →+ R₀[K'](G))

/-- The source-facing positive subset `P_A^+(G)` viewed in this item file as the set of actual
projective classes in `P₀[A](G)`. -/
private def projectivePositiveSubsetLocal (A : Type u) [CommRing A] (G : Type u) [Group G] :
    Set (P₀[A](G)) :=
  Set.range fun P : FiniteProjectiveGroupAlgebraModule A G ↦ [P]ₚ₀

scoped[Representation] notation:max "P⁺[" A "](" G ")" =>
  projectivePositiveSubsetLocal A G

/- Domain-style sampling for Exercise 16-16.3-7:
* primary domain: projective and finite-representation Grothendieck groups under base change to a
  common field `K'`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckBaseChangeHom`,
  `finiteRepGrothendieckScalarExtensionHom`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`;
* best owner abstraction: the existing Chapter `15` homomorphism owners together with their
  canonical additive-subgroup ranges, viewed on this source-facing set-equality surface via the
  usual coercion to sets.

Primitive data vs derived API:
* primitive data: the actual homomorphisms `eA`, `eA'`, and `eK` and the source-facing positive
  subsets `P⁺[A](G)` and `P⁺[A'](G)`;
* derived API: this exercise's image-intersection identity inside the common ambient group
  `R₀[K'](G)`.

Source/core/bridge triage:
* source-facing: the equality comparing the positive images over `A` and `A'` inside `R₀[K'](G)`;
* core/canonical: the Chapter `15` homomorphism owners and their `.range` additive subgroups;
* bridge/view: this theorem, which rewrites the source statement using those canonical owner
  ranges rather than a parallel set-theoretic range wrapper.
-/
-- Proof sketch: rewrite the source-facing subsets `P_A^+(G)`, `P_{A'}^+(G)`, `P_A(G)`,
-- `P_{A'}(G)`, and `R_K(G)` inside the common ambient group `R_K'(G)` using the canonical
-- scalar-extension maps `eA`, `eA'`, and `eK`. The source inclusion `P_{A'}^+(G) ⊆ P_{A'}(G)`
-- becomes the tautological inclusion of `eA' '' P⁺[A'](G)` into the canonical additive-hom range
-- of `eA'`, so the conclusion is the set-theoretic simplification of
-- `(X ∩ (eA').range) ∩ (eK).range` to `X ∩ (eK).range`.
/-- Helper for Exercise 16-16.3-7: the positive image over `A'` is already contained in the
range of the canonical base-change map `eA'`. -/
private lemma image_projectivePositive_inter_range :
    (eA' '' P⁺[A'](G)) ∩ (eA').range = eA' '' P⁺[A'](G) := by
  -- Every point in the image of `eA'` lies in the range of `eA'`.
  exact Set.inter_eq_left.2 <| Set.image_subset_range _ _

/-- Exercise 16-16.3-7: viewed in the common ambient Grothendieck group `R_K'(G)` via the
canonical scalar-extension maps, if the positive image of `P_A(G)` is
`eA '' P⁺[A](G) = (eA' '' P⁺[A'](G)) ∩ (eA).range` and the full image of
`P_A(G)` is `(eA).range = (eA').range ⊓ (eK).range`, then
`eA '' P⁺[A](G) = (eA' '' P⁺[A'](G)) ∩ (eK).range`. The
source-side inclusion
`P_{A'}^+(G) ⊆ P_{A'}(G)` is absorbed here by the automatic inclusion of
`eA' '' P⁺[A'](G)` into `(eA').range`. -/
theorem
    projectivePositiveImage_eq_inter_scalarExtension_range
    (h_positive :
      eA '' P⁺[A](G) =
        (eA' '' P⁺[A'](G)) ∩ (eA).range)
    (h_projective :
      (eA).range = (eA').range ⊓ (eK).range) :
    eA '' P⁺[A](G) =
      (eA' '' P⁺[A'](G)) ∩ (eK).range := by
  -- Rewrite the left-hand side using the given description of the positive image over `A`.
  calc
    eA '' P⁺[A](G)
        = (eA' '' P⁺[A'](G)) ∩ (eA).range :=
          h_positive
    -- Replace the projective image of `A` with the intersection of the `A'`- and `K`-ranges.
    _ = (eA' '' P⁺[A'](G)) ∩ ↑((eA').range ⊓ (eK).range) := by
          rw [h_projective]
    -- The subgroup infimum is the ambient set-theoretic intersection.
    _ = (eA' '' P⁺[A'](G)) ∩ ((eA').range ∩ (eK).range) := by
          rfl
    -- Reassociate so the redundant intersection with `(eA').range` is visible.
    _ = ((eA' '' P⁺[A'](G)) ∩ (eA').range) ∩ (eK).range := by
          rw [Set.inter_assoc]
    -- Collapse that redundant factor using the helper lemma above.
    _ = (eA' '' P⁺[A'](G)) ∩ (eK).range := by
          rw [image_projectivePositive_inter_range]

end

end Representation

/-! ### Exercise_16_16_3_8 (from Chap16) -/
noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-- Helper for Exercise 16-16.3-8: LinearRepresentations_Serre_1977's positive subset `P_A^+(G)` consists of the classes in
`P_A(G)` represented by actual finite projective `A[G]`-modules. -/
def projectivePositiveSubset
    (A : Type u) [CommRing A] (G : Type u) [Group G] :
    Set (P₀[A](G)) :=
  Set.range fun P : FiniteProjectiveGroupAlgebraModule A G ↦ [P]ₚ₀

scoped[Representation] notation:max "P⁺[" A "](" G ")" =>
  projectivePositiveSubset A G

/-- Helper for Exercise 16-16.3-8: membership in `P_A^+(G)` is equivalent to being the class of
an actual finite projective `A[G]`-module. -/
@[simp] theorem mem_projectivePositiveSubset_iff
    {A : Type u} [CommRing A] {G : Type u} [Group G] {x : P₀[A](G)} :
    x ∈ P⁺[A](G) ↔
      ∃ P : FiniteProjectiveGroupAlgebraModule A G, [P]ₚ₀ = x :=
  Iff.rfl

/-- Helper for Exercise 16-16.3-8: LinearRepresentations_Serre_1977's actual positive subset `R_K^+(G)` consists of the
Grothendieck classes represented by actual finite-dimensional `K[G]`-representations. -/
def finiteRepPositiveSubset
    (K : Type u) [Field K] (G : Type u) [Group G] :
    Set (finiteRepGrothendieckGroup K G) :=
  Set.range (finiteRepGrothendieckClass K G)

scoped[Representation] notation:max "R⁺[" K "](" G ")" =>
  finiteRepPositiveSubset K G

/-- Helper for Exercise 16-16.3-8: membership in `R_K^+(G)` is equivalent to being the class of
an actual finite-dimensional `K[G]`-representation. -/
@[simp] theorem mem_finiteRepPositiveSubset_iff
    {K : Type u} [Field K] {G : Type u} [Group G] {x : finiteRepGrothendieckGroup K G} :
    x ∈ R⁺[K](G) ↔
      ∃ V : FDRep K G, [V]₀ = x :=
  Iff.rfl

/-- Helper for Exercise 16-16.3-8: condition `(R)` is witnessed by a finite local overring `A'`
with fraction field `K'`, such that scalar extension detects positivity in `R₀[K](G)` and the
decomposition map over `(A', K')` fills the residue-field positive cone. -/
def SatisfiesConditionR
    (RKplus : Set (finiteRepGrothendieckGroup K G))
    (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : HenselianLocalRing A')
      (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : Algebra A A')
      (_ : Module.Finite A A')
      (K' : Type u) (_ : Field K')
      (_ : Algebra A' K') (_ : Algebra A K') (_ : IsFractionRing A' K')
      (_ : Algebra K K')
      (_ : IsScalarTower A A' K') (_ : IsScalarTower A K K')
      (_ : FiniteDimensional K K'),
    RKplus = (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) ∧
      decompositionHom A' K' G '' R⁺[K'](G) = R⁺[IsLocalRing.ResidueField A'](G)

/-
Source-faithful repair note.

The surrounding API currently has the Grothendieck groups and the decomposition map, but it does
not yet expose the character map on `R₀[K](G)` or LinearRepresentations_Serre_1977's Proposition 44 descent as reusable Lean
lemmas. The previous local proof tried to manufacture those missing facts with ad-hoc names such
as `finiteRepGrothendieckCharacter`, which are not present in this repository and caused a build
blocker.

The statement below matches LinearRepresentations_Serre_1977, Section 16.3, Exercise 16.6: for `K` sufficiently large,
condition `(R)` is equivalent to

  `e(P_A^+(G)) = e(P_A(G)) ∩ R_K^+(G)`.

Forward direction, following the text: choose a finite local extension `A'` with fraction field
`K'`; use the decomposition surjectivity `d(R⁺[K'](G)) = R⁺[k'](G)` and Proposition 44 to prove
that every element of `e.range ∩ R⁺[K](G)` comes from an actual projective class.

Reverse direction, following the text after Proposition 44: use the dual cone criterion
`x ∈ P_k^+(G)` iff all pairings with `R_k^+(G)` are nonnegative. The equality of positive images
transports these inequalities across the adjunction between the decomposition map `d` and the
Cartan map `e`, forcing the image of `d` to be exactly the residue-field positive cone.
-/

/-- Exercise 16-16.3-8: under the large-field hypothesis on `K`, LinearRepresentations_Serre_1977's condition `(R)` for the
actual positive subset `R_K^+(G)` is equivalent to the source-facing equality
`e(P_A^+(G)) = range(e) ∩ R_K^+(G)`, where
`e = projectiveGrothendieckBaseChangeHom K : P_A(G) → R_K(G)`. -/
theorem conditionR_iff_baseChange_image_eq_range_inter_positive
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionR (R⁺[K](G)) A ↔
      e '' P⁺[A](G) =
        (((e).range : Set (finiteRepGrothendieckGroup K G)) ∩ R⁺[K](G)) := by
  -- The remaining proof is exactly the source route recorded above. Keeping the theorem statement
  -- intact is important: downstream proof jobs should now see a correct Exercise 16.6 surface,
  -- without the bogus local character API that previously made the file fail before proof search.
  sorry

end

end Representation
