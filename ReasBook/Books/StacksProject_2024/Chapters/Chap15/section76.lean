import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_76_1 (from Chap15) -/
open CategoryTheory ComplexShape Limits

universe u

noncomputable section

variable {R : Type u} [CommRing R]

section

variable (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)

/- Domain-style sampling:
- primary domain: bounded-above acyclic cochain complexes of `R`-modules, together with reduction
  modulo `I` and the owner retract-stability/direct-summand condition on the allowed termwise
  module class;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.map`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`,
  `HomologicalComplex.Acyclic`,
  `ObjectProperty.IsStableUnderRetracts`;
- best owner abstraction: the bounded-above termwise-`PClass` owner
  `CochainComplex.MinusWithTermsIn PClass`, the reduced owner
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`, the canonical retract-stability owner
  `PClass.IsStableUnderRetracts` for the source direct-summand condition, and the reduction
  owner on cochain complexes `ReduceModI.mapHomologicalComplex (up ℤ)`;
- primitive data: the lifted complex `P : CochainComplex.MinusWithTermsIn PClass` and the target
  reduced complex `E : CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- derived API: the acyclicity of the underlying cochain complexes of `P` and `E`, and the
  existence of a reduction isomorphism
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`.

Source/core/bridge triage:
- `source-facing`: the existence statement of Lemma `15.76.1`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn PClass`, `HomologicalComplex.Acyclic`, and
  the reduction/base-change owners `ReduceModI`, `ReduceModI.mapHomologicalComplex (up ℤ)`,
  together with the chapter owner `PClass.IsStableUnderRetracts`;
- `bridge/view`: the comparison isomorphism
  `e : ((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: start above the top nonzero degree of `E` and descend inductively. At each step,
-- split the already constructed acyclic tail into cycles and boundaries, use the retract-stability
-- owner `PClass.IsStableUnderRetracts` for the source direct-summand condition to keep the cycle
-- objects inside `PClass`, lift the next differential from a projective module, and then upgrade
-- surjectivity modulo `I` to actual surjectivity by hypothesis.
/-- Lemma 15.76.1: under the stated projectivity, retract-stability (equivalently, direct-summand
closure in the module category), and surjectivity-modulo-`I` hypotheses on a class `PClass` of
`R`-modules, every bounded-above acyclic complex of
`(R ⧸ I)`-modules whose terms are reductions of objects of `PClass` lifts to a bounded-above
acyclic complex of `R`-modules with terms in `PClass`. -/
theorem exists_boundedAbove_acyclic_lift_of_module_class
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic) :
    ∃ (P : CochainComplex.MinusWithTermsIn PClass)
      (e :
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex (up ℤ)).obj
          (P : CpxR) ≅ (E : CpxRI)),
      (P : CpxR).Acyclic := sorry

end

end

/-! ### Lemma_15_76_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "DModRI" => DerivedCategory ModRI
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
variable (PClass : ObjectProperty ModR)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "PClassModI" => (PClass.map ReduceModI)

/- Domain-style sampling:
- primary domain: bounded-above derived representatives of module complexes, together with
  reduction modulo an ideal;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction: the chosen bounded-above cochain complex with terms in `PClass`
  `P : CochainComplex.MinusWithTermsIn PClass`, together with the chapter owners
  `PClass.IsClosedUnderBinaryCoproducts` and `PClass.IsStableUnderRetracts` for the direct-sum and
  direct-summand conditions; representation / reduction remain direct isomorphism data on that
  owner object, and the reduced complex is already owned by
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- primitive data: `P : CochainComplex.MinusWithTermsIn PClass`, an isomorphism
  `K ≅ DerivedCategory.Q.obj (P : CpxR)`, and the reduced owner
  `E : CochainComplex.MinusWithTermsIn PClassModI`;
- derived API: the bounded-above condition and termwise membership of `E`, plus existential
  theorems asserting that such a representative or lift exists.

Source/core/bridge triage:
- `source-facing`: existence of a bounded-above `PClass`-complex representing `K`, and of one whose
  reduction modulo `I` is a prescribed complex `E`;
- `core/canonical`: the chosen complex `P` together with owner-style predicates on `P`;
- `bridge/view`: the termwise reduction condition
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ E`. -/

-- Proof sketch: choose a bounded-above `PClass`-representative of `K`, identify its derived
-- reduction modulo `I` with the termwise scalar extension to `R ⧸ I`, compare that complex with
-- the underlying complex of the owner `E` in `D(R ⧸ I)`, and then lift the resulting acyclic cone
-- by the previous lifting lemma. The cokernel complex of the lifted map gives the desired
-- representative of `K` with prescribed reduction.
/-- Lemma 15.76.2: let `R` be a ring, let `I ⊆ R` be an ideal, and let `PClass` be a class of
`R`-modules satisfying the projectivity, direct-sum closure, retract-stability/direct-summand
closure, and surjectivity-modulo-`I` hypotheses. If `E^•` is a bounded-above complex of
`R/I`-modules representing `K ⊗_R^{\mathbf L} R/I`, and if `K` admits a bounded-above
representative with terms in `PClass`, then there exists a bounded-above complex `P^•` with terms
in `PClass` which represents `K` in `D(R)` and whose reduction modulo `I` is isomorphic to
`E^•`. -/
theorem exists_boundedAbove_representative_lifting_derivedReduction
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsClosedUnderBinaryCoproducts]
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective ((ReduceModI.map f).hom) →
      Function.Surjective f.hom)
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn PClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hKrep : ∃ P : CochainComplex.MinusWithTermsIn PClass,
      K ≅ DerivedCategory.Q.obj (P : CpxR)) :
    ∃ P : CochainComplex.MinusWithTermsIn PClass,
      (K ≅ DerivedCategory.Q.obj (P : CpxR)) ×
        (ReduceModI.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P : CpxR) ≅ (E : CpxRI) := sorry

end

end CategoryTheory

/-! ### Lemma_15_76_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CochainComplex
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ProjectiveMinusR" => CochainComplex.ProjectiveMinus ModR
local notation "ProjectiveMinusRI" => CochainComplex.ProjectiveMinus ModRI

/- Domain-style sampling:
- primary domain: lifting bounded-above projective derived representatives across quotient
  reduction modulo a nilpotent ideal;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `ModuleCat.extendScalars`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the bounded-above projective owners
  `CochainComplex.ProjectiveMinus ModR` and `CochainComplex.ProjectiveMinus ModRI`; the quotient
  representative should stay on the canonical owner `ProjectiveMinus`, while reduction remains the
  canonical cochain-level scalar-extension
  `(Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj`;
- primitive data: the derived object `K : D(R)`, the bounded-above projective quotient complex
  `E`, and the canonical reduction hypothesis that `E` represents `K ⊗[R]^L[(R ⧸ I)]`;
- derived API: existence of a bounded-above projective representative `P` of `K` together with
  the two resulting comparison isomorphism claims, exposed through the canonical Prop-level owner
  `CategoryTheory.IsIsomorphic` rather than through `Nonempty`.

Source/core/bridge triage:
- `source-facing`: the projective specialization of the lifting statement of Lemma `15.76.3`;
- `core/canonical`: `ProjectiveMinus`, `derivedTensorWithAlgebra`, and
  `CochainComplex.ProjectiveResolution`;
- `bridge/view`: the object-level comparison claims
  `IsIsomorphic K (DerivedCategory.Q.obj (P : CpxR))` and
  `IsIsomorphic
    ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj
      (P : CpxR))
    (E : CpxRI)`; the reduction hypothesis itself stays on the chapter owner
  `K ⊗[R]^L[(R ⧸ I)]`. -/

-- Proof sketch: start from the canonical derived reduction hypothesis
-- `(K ⊗[R]^L[(R ⧸ I)]).IsIsomorphic (Q(E))`, choose a K-projective model computing that derived
-- reduction,
-- truncate above using boundedness of `E`, lift each quotient-projective term across the nilpotent
-- ideal by Lemma `10.77.5`, and use K-projectivity to identify the resulting bounded-above lift
-- with `K`.
/-- Lemma 15.76.3: let `R` be a ring, let `I ⊆ R` be a nilpotent ideal, let `E^•` be a bounded-
above complex of projective `R / I`-modules, and let `K` be an object of `D(R)`. If a
derived reduction `K \otimes_R^{\mathbf L} (R / I)` is represented by `E^•`, then there exists a
bounded-above complex `P^•` of projective `R`-modules together with comparison isomorphisms
`K \cong Q(P^•)` and `P^•/IP^• \cong E^•`. -/
theorem exists_boundedAbove_projective_representative_lifting_mod_nilpotent
    (K : DModR) (E : ProjectiveMinusRI)
    (hErep : IsIsomorphic (K ⊗[R]^L[(R ⧸ I)]) (DerivedCategory.Q.obj (E : CpxRI)))
    (hInil : IsNilpotent I) :
    ∃ P : ProjectiveMinusR,
      IsIsomorphic K (DerivedCategory.Q.obj (P : CpxR)) ∧
        IsIsomorphic
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj
            (P : CpxR))
          (E : CpxRI) := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_76_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]

local notation "DModRPrime" => DerivedCategory (ModuleCat R')

/- Domain-style sampling for Lemma 15.76.4:
- primary domain: derived scalar extension on module derived categories and reflection of
  pseudo-coherence across nilpotent thickenings;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `exists_boundedAbove_projective_representative_lifting_mod_nilpotent`,
  `DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra R' R : D(R') ⥤ D(R)`, used on objects through the notation
  `K' ⊗[R']^L[R]`;
- primitive vs. derived:
  primitive data are the surjectivity and nilpotence hypotheses on `R' → R` and the object
  `K' : D(R')`;
  the pseudo-coherence equivalence is derived API over the existing owner and predicate;
- source/core/bridge triage:
  `source-facing`: pseudo-coherence is equivalent before and after base change along a nilpotent
  surjection;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPseudoCoherent`;
  `bridge/view`: the notation `K' ⊗[R']^L[R]` for applying the owner functor to `K'`.
- layer: this theorem is source-facing over canonical owners, so the public statement should use
  the existing notation layer rather than a raw functor application term. -/

-- Proof sketch: the implication `K'.IsPseudoCoherent → (K' ⊗[R']^L[R]).IsPseudoCoherent` is the
-- canonical preservation theorem `derivedTensorWithAlgebra_isPseudoCoherent` from Lemma
-- `15.65.12`. For the converse, choose a bounded-above finite-free representative of the base
-- change, lift it through Lemma `15.76.3` to a bounded-above projective representative over `R'`,
-- and then use Nakayama along the surjection with nilpotent kernel to show the lifted terms are
-- finite free.
/-- Lemma 15.76.4: for a surjective ring map `R' → R` with nilpotent kernel, an object `K'` of
`D(R')` is pseudo-coherent if and only if its derived base change
`K' \otimes_{R'}^{\mathbf L} R` is pseudo-coherent in `D(R)`. -/
theorem isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K' : DModRPrime) :
    (K' ⊗[R']^L[R]).IsPseudoCoherent ↔
      K'.IsPseudoCoherent := by
  constructor
  · intro hK
    sorry
  · intro hK
    simpa using derivedTensorWithAlgebra_isPseudoCoherent K' hK

end

end CategoryTheory

/-! ### Lemma_15_76_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "FiniteStablyFreeClass" => finiteStablyFreeModuleProperty R
local notation "FiniteStablyFreeClassModI" => finiteStablyFreeModuleProperty (R ⧸ I)

/- Domain-style sampling:
- primary domain: lifting bounded-above finite stably free derived representatives across
  reduction modulo an ideal inside the Jacobson radical;
- sampled owner declarations:
  `finiteStablyFreeModuleProperty`,
  `CochainComplex.MinusWithTermsIn`,
  `DerivedCategory.IsPseudoCoherent`,
  `exists_boundedAbove_representative_lifting_derivedReduction`,
  `Module.StablyFree`;
- best owner abstraction: the chosen representative should remain a bounded-above owner complex
  `P : CochainComplex.MinusWithTermsIn FiniteStablyFreeClass`, while the quotient-side input
  should use the direct owner `CochainComplex.MinusWithTermsIn FiniteStablyFreeClassModI`; the
  reduction comparison remains a bridge from `P` to `E`, and pseudo-coherence remains on the
  derived object `K`;
- primitive data: the quotient-side and source-side bounded-above finite-stably-free complexes
  `E` and `P`, together with the comparison isomorphisms in `D(R)` and after reduction modulo `I`;
- derived API: the existence of such a lift, plus the termwise freeness consequence.

Source/core/bridge triage:
- `source-facing`: the lifting existence statement of Lemma `15.76.5`;
- `core/canonical`: `finiteStablyFreeModuleProperty`, `CochainComplex.MinusWithTermsIn`,
  `K.IsPseudoCoherent`, and the owner predicates `Module.Finite` / `Module.StablyFree`;
- `bridge/view`: the reduction comparison
  `((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
      (ComplexShape.up ℤ)).obj (P : CpxR) ≅ (E : CpxRI))`. -/

-- Proof sketch: apply Lemma `15.76.2` with `PClass` equal to the class of finite stably free
-- `R`-modules. The closure conditions come from Lemma `15.3.2`, lifting termwise reductions comes
-- from Lemma `15.3.3`, the pseudo-coherent hypothesis provides a bounded-above finite free
-- representative of `K`, and Lemma `15.3.5` upgrades the lifted terms to free ones whenever the
-- corresponding term of `E` is free.
/-- Lemma 15.76.5: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above complex of finite stably free `R/I`-modules, and let `K` be an object of `D(R)`.
Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`I ⊆ \operatorname{Jac}(R)` (equivalently, every element of `1 + I` is invertible). Then there
exists a bounded-above complex `P^•` of finite stably free `R`-modules representing `K` whose
reduction modulo `I` is isomorphic to `E^•`; moreover, if `E^i` is free, then `P^i` is free. -/
theorem exists_boundedAbove_finiteStablyFree_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteStablyFreeClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent)
    (hI : I ≤ Ring.jacobson R) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteStablyFreeClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE :
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
              (ComplexShape.up ℤ)).obj (P : CpxR)) ≅ (E : CpxRI),
          ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := sorry

end

end CategoryTheory

/-! ### Lemma_15_76_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open IsLocalRing
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "κ" => ResidueField R
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "FiniteFreeClass" => (fun M : ModuleCat R ↦ Module.Free R M ∧ Module.Finite R M)
local notation "BoundedFiniteFreeCpx" => CochainComplex.MinusWithTermsIn FiniteFreeClass

/- Domain-style sampling for Lemma 15.76.6:
- primary domain: pseudo-coherent derived complexes over a local ring and bounded-above finite-free
  representatives controlled by residue-field homology;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`,
  `exists_boundedAbove_termwiseFiniteFree_quasiIso`;
- best owner abstraction: the bounded-above finite-free model should be carried by the existing
  owner `CochainComplex.MinusWithTermsIn FiniteFreeClass`, while the source-facing residue-field
  homology and prescribed rank function remain bridge data on top of that owner;
- primitive vs. derived:
  primitive data are the derived residue-field homology objects and the rank function `d : ℤ → ℕ`;
  derived API is the existence and uniqueness of owner-level bounded-above finite-free models with
  those prescribed ranks;
- source/core/bridge triage:
  `source-facing`: the three clauses of Lemma `15.76.6`;
  `core/canonical`: `K.IsPseudoCoherent`, `CochainComplex.MinusWithTermsIn`, and
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: `residueFieldDerivedHomology` and the pointwise rank condition on the owner
    complex terms.
-/

/-- The degree-`i` homology of the derived residue-field base change `K ⊗_R^L κ`. -/
abbrev residueFieldDerivedHomology (K : DModR) (i : ℤ) : ModuleCat κ :=
  (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj (K ⊗[R]^L[κ])

-- Proof sketch: apply pseudo-coherence preservation under derived tensoring with the residue field,
-- then use the standard characterization of pseudo-coherent derived complexes over the field `κ`,
-- where every pseudo-coherent object is represented by a bounded-above complex of finite free
-- `κ`-modules. Such a complex has finite-dimensional homology in each degree and vanishes in all
-- sufficiently large degrees.
/-- Lemma 15.76.6 (1): if `K` is pseudo-coherent over the local ring `R`, then the cohomology of
`K ⊗_R^L κ` is finite-dimensional over the residue field `κ` in every degree and vanishes in
sufficiently large degrees. -/
theorem residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
    (K : DModR) (hK : K.IsPseudoCoherent) :
    (∀ i : ℤ, FiniteDimensional κ (residueFieldDerivedHomology K i)) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (residueFieldDerivedHomology K i) := sorry

-- Proof sketch: combine part `(1)` with `hd` to deduce that `d i = 0` for all sufficiently large
-- `i`, then choose the zero-differential complex over `κ` with term `κ^{d i}` in degree `i` and
-- identify it with the derived residue-field base change of `K`. Apply the lifting statement of
-- Lemma `15.76.5` at the maximal ideal of the local ring to obtain a bounded-above free
-- `R`-complex representing `K` with the prescribed ranks.
/-- Lemma 15.76.6 (2): if `d i` is the dimension of the degree-`i` residue-field cohomology of
`K`, then `K` is represented by a bounded-above cochain complex whose degree-`i` term is free of
rank `d i`. -/
theorem exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
    (K : DModR) (hK : K.IsPseudoCoherent) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ))) :
    ∃ P : BoundedFiniteFreeCpx,
      (∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R))) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)) := sorry

-- Proof sketch: let `β : P ⟶ Q` be a morphism in the derived category representing the identity of
-- `K`. After tensoring with `κ`, the complexes `P ⊗_R κ` and `Q ⊗_R κ` have zero differentials
-- because their terms already realize the residue-field homology dimensions `d i`. Hence `β ⊗ 1`
-- is degreewise an isomorphism, so each component `β^i` is an isomorphism by Nakayama's lemma for
-- finite free modules over the local ring `R`.
/-- Lemma 15.76.6 (3): a bounded-above free representative of `K` whose degree-`i` term has rank
equal to the dimension of `H^i(K ⊗_R^L κ)` is unique up to isomorphism of complexes. -/
theorem boundedAbove_termwiseFree_representative_unique_of_residueFieldDerivedHomology
    (K : DModR) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ)))
    {P P' : BoundedFiniteFreeCpx}
    (hP : ∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hPK : Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)))
    (hP' : ∀ i : ℤ, Nonempty (((P' : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hP'K : Nonempty (K ≅ DerivedCategory.Q.obj (P' : CpxR))) :
    Nonempty ((P : CpxR) ≅ (P' : CpxR)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_76_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxAway[" f "]" => CochainComplex (ModuleCat (Localization.Away f)) ℤ
local notation "FiniteFreeClassAway[" f "]" =>
  (fun M : ModuleCat (Localization.Away f) ↦
    Module.Free (Localization.Away f) M ∧ Module.Finite (Localization.Away f) M)
local notation "BoundedFiniteFreeCpxAway[" f "]" =>
  CochainComplex.MinusWithTermsIn FiniteFreeClassAway[f]

/- Domain-style sampling for Lemma 15.76.7:
- primary domain: perfect derived complexes over a commutative ring, measured by residue-field
  fibers at a prime and represented after shrinking by finite-free localization complexes;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: `K.IsPerfect` remains the source-facing owner, while the explicit
  localized finite-free representative in part `(2)` should reuse the bounded-above owner
  `CochainComplex.MinusWithTermsIn`; the lower support bound is separate source-facing data, and
  upper boundedness stays inside that owner;
- primitive vs. derived:
  primitive data are the prime `p`, the perfect object `K`, the rank function `d`, and the
  localized owner complex;
  derived API is the finite-support residue-field homology conclusion in part `(1)` and the
  termwise rank identifications plus derived isomorphism in part `(2)`;
- source/core/bridge triage:
  `source-facing`: the two numbered clauses of Lemma `15.76.7`;
  `core/canonical`: `K.IsPerfect`, `CochainComplex.MinusWithTermsIn`, and the localized finite-
    free term property;
  `bridge/view`: `primeResidueFieldDerivedHomology` and the localized termwise rank condition on
    the chosen owner complex.
-/

/-- The degree-`i` homology of `K ⊗_R^L κ(𝔭)`. -/
abbrev primeResidueFieldDerivedHomology (p : PrimeSpectrum R) (K : DModR) (i : ℤ) :
    ModuleCat p.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat p.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[p.asIdeal.ResidueField])

-- Proof sketch: base change the perfect complex `K` from `R` to the residue field `κ(𝔭)` by
-- derived tensor product. Over a field, a perfect complex is represented by a bounded complex of
-- finite-dimensional vector spaces, so each homology group is finite-dimensional and only finitely
-- many degrees contribute nonzero homology.
/-- Lemma 15.76.7 (1): if `K` is perfect over `R`, then the homology of `K ⊗_R^L κ(𝔭)` is
finite-dimensional over `κ(𝔭)` in every degree and nonzero in only finitely many degrees. -/
theorem primeResidueFieldDerivedHomology_finiteDimensional_and_finiteSupport_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) :
    (∀ i : ℤ, FiniteDimensional p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i)) ∧
      Set.Finite {i : ℤ | ¬ IsZero (primeResidueFieldDerivedHomology p K i)} := sorry

-- Proof sketch: apply part `(1)` to see that each residue-field homology group
-- `H^i(K ⊗_R^L κ(𝔭))` is finite-dimensional. Localize `R` at `𝔭`, so that `K ⊗_R^L R_𝔭` is a
-- perfect complex over the local ring `R_𝔭`. Apply the local lifting statement to obtain a
-- bounded-above finite-free representative in the canonical owner
-- `CochainComplex.MinusWithTermsIn`, with those homology dimensions as termwise ranks, and then
-- descend that representative from `R_𝔭 = colim_{f ∉ 𝔭} R_f` to some away localization `R_f`,
-- keeping the lower support bound separate from the bounded-above owner data.
/-- Lemma 15.76.7 (2): if `d i = dim_{κ(𝔭)} H^i(K ⊗_R^L κ(𝔭))`, then after inverting some
`f ∉ 𝔭` the derived localization `K ⊗_R^L R_f` is represented by a bounded-above finite-free
complex with some lower support bound, whose degree-`i` term is free of rank `d i`. -/
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPerfect
    (p : PrimeSpectrum R) (K : DModR) (hK : K.IsPerfect) (d : ℤ → ℕ)
    (hd :
      ∀ i : ℤ,
        Module.finrank p.asIdeal.ResidueField (primeResidueFieldDerivedHomology p K i) = d i) :
    ∃ (f : R) (_ : f ∉ p.asIdeal) (a : ℤ) (P : BoundedFiniteFreeCpxAway[f]),
      (P : CpxAway[f]).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty (((P : CpxAway[f]).X i) ≃ₗ[Localization.Away f]
            (Fin (d i) → Localization.Away f))) ∧
        Nonempty ((K ⊗[R]^L[Localization.Away f]) ≅ DerivedCategory.Q.obj (P : CpxAway[f])) :=
  sorry

end

end CategoryTheory

/-! ### Lemma_15_76_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling:
- primary domain: localization of bounded finite-projective cochain complexes and comparison of
  quasi-isomorphic complexes after termwise scalar extension;
- sampled owner declarations:
  `ObjectProperty.ofObj`,
  `ObjectProperty.additiveClosure`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `(ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)`,
  `CochainComplex.mappingCone`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: the object property of the elementary contractible two-term localization-away
    complexes, the localization-away owner `localizationAwayComplex`, and the existence statement
    of Lemma `15.76.8`;
  `core/canonical`: the cochain-level scalar-extension owner
    `(ModuleCat.extendScalars (algebraMap R (Localization.Away f))).mapHomologicalComplex (up ℤ)`
    and the canonical cone owner `CochainComplex.mappingCone`;
  `bridge/view`: the owner-level additive closure expressing "finite direct sum of trivial
    complexes" via the Chapter 13 closure API, together with the source-facing localization owner
    built from the core scalar-extension functor;
- primitive data vs. derived API: the primitive local content is the object property generated by
  the elementary contractible two-term localization-away complexes. The finite-direct-sum and
  isomorphism closure is derived canonically as `additiveClosure`, and termwise localization of a
  complex should be exposed through a short source-facing owner rather than repeated raw functor
  syntax.

Source/core/bridge triage:
- `source-facing`: `localizationAwayComplex`,
  `localizationAwayElementaryTrivialComplexProperty`, and the main existence theorem below;
- `core/canonical`: cochain-level scalar extension and `CochainComplex.mappingCone`;
- `bridge/view`: `localizationAwayElementaryTrivialComplexProperty f` together with its canonical
  additive closure, plus the identification of complex localization with termwise scalar
  extension. -/

/-- Termwise localization of a cochain complex of `R`-modules away from `f`. -/
abbrev localizationAwayComplex (f : R) (M : CpxR) :
    CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).mapHomologicalComplex
    (up ℤ)).obj M

-- Proof sketch: unfold `localizationAwayComplex`; it is degreewise scalar extension along
-- `R → R_f`.
/-- The localization-away complex is obtained by degreewise extension of scalars to `R_f`. -/
theorem localizationAwayComplex_def (f : R) (M : CpxR) :
    localizationAwayComplex f M =
      ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).mapHomologicalComplex
        (up ℤ)).obj M :=
  rfl

/-- The elementary two-term contractible complex over `R_f` concentrated in degrees `n` and
`n + 1`. -/
abbrev localizationAwayElementaryTrivialComplex (f : R) (n : ℤ) :
    CochainComplex (ModuleCat (Localization.Away f)) ℤ :=
  CochainComplex.mappingCone
    (𝟙 ((CochainComplex.singleFunctor (ModuleCat (Localization.Away f)) (n + 1)).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))))

/-- The object property of the elementary contractible two-term complexes over `R_f`. -/
abbrev localizationAwayElementaryTrivialComplexProperty (f : R) :
    ObjectProperty (CochainComplex (ModuleCat (Localization.Away f)) ℤ) :=
  ObjectProperty.ofObj (localizationAwayElementaryTrivialComplex f)

-- Proof sketch: localize the given derived-category isomorphism at the prime `p`, use the
-- filtered-colimit description `R_p = colim_{f ∉ p} R_f` to descend an isomorphism of complexes
-- from the local ring `R_p` to some localization `R_f`, and in the local case split each bounded
-- finite-projective complex into its minimal summand plus a finite direct sum of elementary
-- contractible two-term complexes using Lemmas `15.76.6` and `10.102.2`.
/-- Lemma 15.76.8: if `M^•` and `N^•` are bounded complexes of finite projective `R`-modules
representing the same object of `D(R)`, then after localizing away from some element
`f ∉ 𝔭` there exist complexes `P^•` and `Q^•` in the additive closure of the elementary trivial
two-term complexes over `R_f` such that `M^•_f ⊞ P^•` and `N^•_f ⊞ Q^•` are isomorphic as
complexes. -/
theorem exists_localizationAway_iso_biproduct_trivialComplexes_of_same_derivedObject
    (p : PrimeSpectrum R) {M N : CpxR}
    (hM : M.IsBoundedFiniteProjective)
    (hN : N.IsBoundedFiniteProjective)
    (hMN : IsIsomorphic (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N)) :
    ∃ f : R, f ∉ p.asIdeal ∧
      ∃ P Q : CochainComplex (ModuleCat (Localization.Away f)) ℤ,
        (localizationAwayElementaryTrivialComplexProperty f).additiveClosure P ∧
        (localizationAwayElementaryTrivialComplexProperty f).additiveClosure Q ∧
          IsIsomorphic
            (localizationAwayComplex f M ⊞ P)
            (localizationAwayComplex f N ⊞ Q) := sorry

end

end CategoryTheory

/-! ### Lemma_15_76_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "FiniteProjectiveClass" => finiteProjectiveModuleProperty R
local notation "FiniteProjectiveClassModI" => finiteProjectiveModuleProperty (R ⧸ I)
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ))

/- Domain-style sampling:
- primary domain: lifting bounded-above finite-projective derived representatives across reduction
  modulo a henselian ideal;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `exists_finiteProjective_lift_of_henselianRing`,
  `CochainComplex.MinusWithTermsIn`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.extendScalars`;
- best owner abstraction: the chosen representative should remain a bounded-above owner complex
  `P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass`, while the quotient-side input should
  use the canonical owner `CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI`; the bridge
  from quotient-side finite projectives to reduction data for `Lemma 15.76.2` is proof-only, via
  `exists_finiteProjective_lift_of_henselianRing`; pseudo-coherence remains on the derived object
  `K`;
- primitive data: the quotient-side bounded-above finite-projective complex `E`, the lifted
  bounded-above finite-projective representative `P`, and the comparison data in `D(R)` and after
  reduction modulo `I`;
- derived API: the existence of such representatives, recorded by the explicit comparison
  isomorphisms supplied by the owner theorem
  `exists_boundedAbove_representative_lifting_derivedReduction`; since those isomorphisms are
  genuine data rather than propositions, the source-facing statement below exposes them as
  explicit existential binders together with the termwise freeness consequence.

Source/core/bridge triage:
- `source-facing`: the lifting-existence statement of Lemma `15.76.9`;
- `core/canonical`: `finiteProjectiveModuleProperty`, `CochainComplex.MinusWithTermsIn`, and
  `K.IsPseudoCoherent`;
- `bridge/view`: the explicit comparison isomorphisms
  `K ≅ DerivedCategory.Q.obj (P : CpxR)` and
  `(ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: apply Lemma `15.76.2` with `PClass` equal to the class of finite projective
-- `R`-modules. The henselian-pair hypothesis and Lemma `15.13.1` lift each finite projective
-- `R/I`-term of `E`, Nakayama's lemma supplies the surjectivity condition via Lemma `15.3.5`, and
-- pseudo-coherence gives a bounded-above finite-projective representative of `K` by Lemma
-- `15.65.5`.
/-- Lemma 15.76.9: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above cochain complex of finite projective `R/I`-modules, and let `K` be an object of
`D(R)`. Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`(R, I)` is a henselian pair. Then there exists a bounded-above cochain complex of finite
projective `R`-modules representing `K` whose reduction modulo `I` is isomorphic to `E^•`;
moreover, if `E^i` is free, then the lifted term `P^i` is free. -/
theorem exists_boundedAbove_finiteProjective_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE : (ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI),
        ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := sorry

end

end CategoryTheory
