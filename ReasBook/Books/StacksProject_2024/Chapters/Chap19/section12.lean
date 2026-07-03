import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_12_1 (from Chap19) -/
open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 19.12.1:
- primary domain: generators/strong generators in Grothendieck abelian categories, together with
  subobject-cardinality bounds;
- sampled owner declarations:
  `IsSeparator`,
  `isSeparator_iff_exists_not_factors_subobject`,
  `exists_epi_from_coproduct_of_generator_of_subobject_cardinal_le`,
  `Cardinal.mk (Subobject X)`;
- best owner abstraction: the generator input is canonically `IsSeparator U`, while the
  size parameter is the canonical owner `Cardinal.mk (Subobject N)` with its `w`-small model
  `Shrink.{w} (Subobject N)` rather than an auxiliary existential index type;
- primitive data: a separator `U`, an epimorphism `π : M ⟶ N`, and the proper subobjects of `N`;
- derived API: a subobject `M' : Subobject M` with `Epi (M'.arrow ≫ π)` and the induced
  subobject-cardinality bound coming from the canonical coproduct indexed by
  `Shrink.{w} (Subobject N)`.

Source/core/bridge triage:
- `source-facing`: the bounded subobject `M' ⊆ M` that still surjects onto `N`;
- `core/canonical`: `IsSeparator`, `Cardinal.mk (Subobject _)`, and the canonical small model
  `Shrink.{w} (Subobject _)`;
- `bridge/view`: this theorem, which converts the generator-side owner abstractions into the
  Stacks-project bounded-subobject statement. -/

/-- Lemma 19.12.1: if `π : M ⟶ N` is an epimorphism in a Grothendieck abelian category with
source-facing generator `U`, formalized by `IsSeparator U`, then some subobject `M' ⊆ M` still
surjects onto `N`, and `Subobject M'` is bounded in cardinality by the subobject lattice of the
coproduct of copies of `U` indexed by the canonical `w`-small model `Shrink.{w} (Subobject N)` of
the subobject lattice of `N`. -/
-- Proof sketch: use the separator/strong-generator criterion to choose, for each proper
-- subobject `N' ⊊ N`, a map `U ⟶ M` whose composite with `π` does not factor through `N'`.
-- Assemble these maps into a morphism from the canonical coproduct indexed by
-- `Shrink.{w} (Subobject N)`, let `M'` be its image in `M`, and then use the Chapter 19
-- subobject-cardinality lemmas for subobjects and quotients to bound
-- `Cardinal.mk (Subobject (M' : C))` by the corresponding coproduct bound.
theorem exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {U M N : C} (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
        Cardinal.mk (Subobject (M' : C)) ≤
          Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ U)) := sorry

end CategoryTheory

/-! ### Lemma_19_12_2 (from Chap19) -/
open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

section

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local notation "Cpx" => CochainComplex C ℤ

/- Domain-style sampling for Lemma 19.12.2:
- primary domain: acyclic cochain complexes in a Grothendieck abelian category, together with the
  canonical bounded-above predicate and termwise subobject-cardinality bounds;
- sampled owner declarations:
  `CochainComplex.Acyclic`,
  `CochainComplex.IsStrictlyLE`,
  `Cardinal.mk (Subobject (K.X n))`,
  `exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size`;
- best owner abstraction: the ambient owner is a cochain complex `K : CochainComplex C ℤ`, with
  boundedness expressed by `∃ b, K.IsStrictlyLE b`, acyclicity by `K.Acyclic`, and size by the
  canonical formula `∀ n, Cardinal.mk (Subobject (K.X n)) ≤ κ`;
- primitive data: a cochain complex, a cardinal `κ`, and the two source conclusions about a
  nonzero acyclic subcomplex and a coproduct presentation;
- derived API: later lemmas may consume those two conclusions as hypotheses, but they should not
  be repackaged as new public owner classes.

Source/core/bridge triage:
- `source-facing`: the existence of one cardinal `κ` controlling both the small nonzero acyclic
  subcomplexes and the coproduct presentations from the source lemma;
- `core/canonical`: `K.Acyclic`, `K.IsStrictlyLE b`, and `Cardinal.mk (Subobject (K.X n))`;
- `bridge/view`: none. The main entry should therefore remain the direct source-facing theorem,
  stated with the canonical owners rather than a bundled wrapper. -/

-- Proof sketch: choose a generator `U` of `C`, apply Lemma `19.12.1` in a descending induction to
-- every nonzero acyclic complex to obtain nonzero bounded-above acyclic subcomplexes with a
-- uniform termwise size bound, and then use these small subcomplexes through all morphisms
-- `U ⟶ M.X n` to assemble a coproduct of bounded-above acyclic small complexes surjecting onto
-- the original acyclic complex.
/-- Lemma 19.12.2: there is a cardinal `κ` such that every nonzero acyclic cochain complex has a
nonzero bounded-above acyclic subcomplex with termwise size at most `κ`, and every acyclic
cochain complex is a quotient of a coproduct of bounded-above acyclic complexes with the same
termwise size bound. -/
theorem exists_cardinal_for_small_acyclic_subcomplexes_and_coproduct_presentations :
    ∃ κ : Cardinal,
      (∀ (M : Cpx) (_ : M.Acyclic) (_ : ¬ IsZero M),
        ∃ N : Subobject M,
          ¬ IsZero (N : Cpx) ∧
            (∃ b : ℤ, (N : Cpx).IsStrictlyLE b) ∧
            (N : Cpx).Acyclic ∧
            ∀ n : ℤ, Cardinal.mk (Subobject ((N : Cpx).X n)) ≤ κ) ∧
      ∀ (M : Cpx) (_ : M.Acyclic),
        ∃ (ι : Type w) (Mi : ι → Cpx) (f : (∐ fun i : ι ↦ Mi i) ⟶ M),
          Epi f ∧
            ∀ i : ι,
              (∃ b : ℤ, (Mi i).IsStrictlyLE b) ∧
                (Mi i).Acyclic ∧
                ∀ n : ℤ, Cardinal.mk (Subobject ((Mi i).X n)) ≤ κ := sorry

end
end CategoryTheory

/-! ### Lemma_19_12_3 (from Chap19) -/
open CategoryTheory Limits
open ComplexShape
open HomotopyCategory

universe v u

namespace CategoryTheory
namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "Cpx" => CochainComplex C ℤ
/- Domain-style sampling for Lemma 19.12.3:
- primary domain: K-injective cochain complexes in an abelian category, detected by vanishing of
  morphisms from acyclic complexes in the homotopy category and refined here using the small
  bounded-above acyclic generators supplied abstractly by the first conclusion of
  Lemma `19.12.2`;
- sampled owner declarations:
  `CochainComplex.IsKInjective`,
  `CochainComplex.isKInjective_iff_rightOrthogonal`,
  `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero`,
  `CategoryTheory.IsBoundedAbove`;
- best owner abstraction: the canonical owner is the target complex `I : Cpx` with property
  `I.IsKInjective`; bounded-above acyclicity is expressed through the existing project owner
  `IsBoundedAbove`, and the termwise subobject-cardinality bound remains an auxiliary source-side
  hypothesis rather than a new packaged owner;
- primitive data: the cardinal `κ`, the bounded-above acyclic small-subcomplex conclusion of
  Lemma `19.12.2` for that `κ`, the complex `I`, and the termwise injectivity hypothesis
  `∀ j, Injective (I.X j)`;
- derived API: the vanishing statement in the homotopy category for bounded-above acyclic
  `κ`-small complexes, which is a source-facing bridge to the canonical owner `I.IsKInjective`.

Source/core/bridge triage:
- `source-facing`: the Stacks-style reduction criterion saying it suffices to test vanishing on the
  bounded-above acyclic `κ`-small complexes produced by the first conclusion of
  Lemma `19.12.2`;
- `core/canonical`: `CochainComplex.IsKInjective`;
- `bridge/view`: the homotopy-category vanishing condition
  `∀ f : (quotient C (up ℤ)).obj M ⟶ (quotient C (up ℤ)).obj I, f = 0` for the chosen source
  complexes.
-/

-- Proof sketch: use the nonzero bounded-above acyclic `κ`-small subcomplexes from the first
-- conclusion of Lemma `19.12.2` inside any nonzero acyclic complex. The termwise injectivity of
-- `I` lets one descend along these subcomplexes and force vanishing in the homotopy category,
-- contradicting the existence of a nonzero morphism from an acyclic source. The canonical owner
-- theorem `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero` then upgrades
-- this vanishing criterion to K-injectivity.
/-- Lemma 19.12.3: if `κ` satisfies the bounded-above acyclic small-subcomplex conclusion of
Lemma `19.12.2`, a cochain complex `I`
with injective terms is K-injective provided that every morphism in the homotopy category from a
bounded-above acyclic complex whose terms have at most `κ` subobjects to `I` is zero. -/
theorem isKInjective_of_termwise_injective_of_small_boundedAbove_acyclic_vanishing
    (κ : Cardinal)
    (hκ_sub :
      ∀ (M : Cpx) (_ : M.Acyclic) (_ : ¬ IsZero M),
        ∃ N : Subobject M,
          ¬ IsZero (N : Cpx) ∧
            IsBoundedAbove (N : Cpx) ∧
            (N : Cpx).Acyclic ∧
            ∀ n : ℤ, Cardinal.mk (Subobject ((N : Cpx).X n)) ≤ κ)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j))
    (hvanish :
      ∀ (M : Cpx)
        (hM_bounded : IsBoundedAbove M)
        (hM_acyclic : M.Acyclic)
        (hM_size : ∀ n : ℤ, Cardinal.mk (Subobject (M.X n)) ≤ κ)
        (f : (quotient C (up ℤ)).obj M ⟶ (quotient C (up ℤ)).obj I), f = 0) :
    I.IsKInjective := sorry

end

end CochainComplex
end CategoryTheory

/-! ### Lemma_19_12_4 (from Chap19) -/
open CategoryTheory

universe w v u

namespace CochainComplex

/-
Domain-style sampling for Lemma 19.12.4:
- primary domain: functorial cochain-complex approximations in a Grothendieck abelian category,
  used to kill maps from a chosen acyclic family up to homotopy and later upgraded to
  K-injective resolutions;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings`,
  `CochainComplex.ResolutionFunctor`,
  `CochainComplex.IsKInjective`,
  `NatTrans.mono_iff_mono_app`;
- best owner abstraction: this Chapter 19 construction is a cochain-complex-level generalization
  of the Chapter 13 `CochainComplex.ResolutionFunctor` owner family, so its
  primitive owner should also live in the `CochainComplex` namespace; the primitive data is a
  functorial approximation `FunctorialComplexApproximation C`, consisting of an endofunctor on
  `CochainComplex C ℤ`, a natural comparison map, and the facts that each comparison map is a
  monomorphism of cochain complexes and a quasi-isomorphism;
- primitive data: the functorial approximation itself;
- derived API: the null-homotopy killing property of Lemma 19.12.4 and the later injective-term
  and K-injective enhancements, together with the inherited degreewise monomorphism facts.

Source/core/bridge triage:
- `source-facing`: `AcyclicKillingResolutionFunctor K`;
- `core/canonical`: `FunctorialComplexApproximation C`;
- `bridge/view`: later specializations adding injective-subobject and K-injective target
  properties.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w}

/-- A functorial cochain-complex approximation by a monomorphic quasi-isomorphic enlargement.
This is the shared primitive owner for the Chapter 19 constructions built from such
approximations; the induced degreewise monomorphisms are derived from the complex-level mono
field. -/
structure FunctorialComplexApproximation (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying endofunctor on cochain complexes. -/
  toFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural comparison map from a complex to its chosen enlargement. -/
  ι : 𝟭 (CochainComplex C ℤ) ⟶ toFunctor
  /-- Each comparison map is a monomorphism of cochain complexes. -/
  mono_app (M : CochainComplex C ℤ) : Mono (ι.app M)
  /-- Each comparison map is a quasi-isomorphism. -/
  quasiIso_app (M : CochainComplex C ℤ) : QuasiIso (ι.app M)

namespace FunctorialComplexApproximation

variable {C : Type u} [Category.{v} C] [Abelian C]

instance (J : FunctorialComplexApproximation C) : Mono J.ι :=
  (NatTrans.mono_iff_mono_app J.ι).2 J.mono_app

end FunctorialComplexApproximation

/-- A functorial enlargement of cochain complexes that kills maps from a fixed family up to
homotopy. -/
structure AcyclicKillingResolutionFunctor (K : I → CochainComplex C ℤ)
    extends FunctorialComplexApproximation C where
  /-- Composing a map out of one of the chosen complexes with the comparison map is homotopic to
  zero. -/
  null_homotopy (i : I) (M : CochainComplex C ℤ) (w : K i ⟶ M) :
    Nonempty (Homotopy (w ≫ ι.app M) 0)

-- Proof sketch: for each acyclic `K i`, choose a termwise monomorphism `K i ⟶ L i` that is
-- homotopic to zero and whose target is quasi-isomorphic to zero, for instance the cone on the
-- identity. Form the pushout over the coproduct of all maps `K i ⟶ M`; this yields a functorial
-- monomorphism of cochain complexes `j_M : M ⟶ \mathbf M(M)`, hence a degreewise monomorphism,
-- with acyclic cokernel, hence a
-- quasi-isomorphism, and the universal property of the pushout makes every composite
-- `K i ⟶ M ⟶ \mathbf M(M)` homotopic to zero.
/-- Lemma 19.12.4: for a Grothendieck abelian category and a family of acyclic cochain complexes
`(K_i^\bullet)`, there exists a functorial degreewise monomorphic quasi-isomorphic enlargement
`j_{M^\bullet} : M^\bullet \to \mathbf M^\bullet(M^\bullet)` such that for every `i` and every
map `w : K_i^\bullet \to M^\bullet`, the composite `j_{M^\bullet} \circ w` is homotopic to zero. -/
theorem exists_acyclic_killing_resolution_functor [IsGrothendieckAbelian.{w} C]
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic) :
    Nonempty (AcyclicKillingResolutionFunctor K) := sorry

end

end CochainComplex

/-! ### Lemma_19_12_5 (from Chap19) -/
open CategoryTheory

universe w v u

namespace CochainComplex

/-
Domain-style sampling for Lemma 19.12.5:
- primary domain: functorial cochain-complex approximations in a Grothendieck abelian category,
  upgraded by degreewise factorization through injective subobjects;
- sampled owner declarations:
  `FunctorialComplexApproximation`,
  `HasFunctorialInjectiveEmbeddings`,
  `HasFunctorialInjectiveEmbeddings.under`,
  `InjectivePresentation`,
  `Subobject.Factors`;
- best owner abstraction: the core owner remains `FunctorialComplexApproximation C` from
  Lemma 19.12.4, while the injective-subobject factorization is derived theorem-level data about
  its degreewise comparison maps rather than a second packaged owner;
- primitive data: a functorial complex approximation;
- derived API: for each degreewise component `(J.ι.app M).f n`, an injective subobject of
  `(J.toFunctor.obj M).X n` together with the canonical factorization property
  `I.Factors ((J.ι.app M).f n)`.

Source/core/bridge triage:
- `source-facing`: the existence statement that the comparison maps factor through injective
  subobjects degreewise;
- `core/canonical`: `FunctorialComplexApproximation C`;
- `bridge/view`: the degreewise factorization witnesses for the comparison morphism.
-/

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Lemma 19.12.5: in a Grothendieck abelian category there exists a functorial cochain-complex
replacement `M ↦ N(M)` together with a natural map `j_M : M ⟶ N(M)` that is termwise injective
and a quasi-isomorphism, and whose degreewise components factor through injective subobjects of the
corresponding terms of `N(M)` in the canonical `Subobject.Factors` sense. -/
-- Proof sketch: apply Theorem 19.11.7 termwise to obtain functorial monomorphisms
-- `Mⁿ ⟶ I(Mⁿ)`, assemble these into the standard auxiliary complex `J(M)`, and form the shifted
-- mapping cone of the quotient map `J(M) ⟶ Q(M)`. The induced map `j_M : M ⟶ N(M)` is termwise
-- mono, each component lands in an injective subobject by construction, and the long exact
-- cohomology sequence for the defining short exact sequence gives that `j_M` is a quasi-isomorphism.
theorem exists_functorial_injective_subobject_complex_approximation :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (M : CochainComplex C ℤ) (n : ℤ),
        ∃ I : Subobject ((J.toFunctor.obj M).X n),
          Injective (I : C) ∧ I.Factors ((J.ι.app M).f n) := sorry

end CochainComplex

/-! ### Theorem_19_12_6 (from Chap19) -/
open CategoryTheory

universe w v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-
Domain-style sampling for Theorem 19.12.6:
- primary domain: functorial K-injective resolutions of cochain complexes in a Grothendieck
  abelian category;
- sampled owner declarations:
  `FunctorialComplexApproximation`,
  `CochainComplex.IsKInjective`,
  `CochainComplex.InjectiveResolution`,
  `ResolutionFunctor`;
- best owner abstraction: the core owner in this chapter is already
  `FunctorialComplexApproximation C`; the injective-term and K-injective conditions in
  Theorem 19.12.6 are derived properties of the chosen target complexes, not new primitive
  structure deserving a second public wrapper;
- primitive data: a functorial complex approximation `J : FunctorialComplexApproximation C`;
- derived API: the termwise injectivity and K-injectivity of `J.toFunctor.obj M`.

Source/core/bridge triage:
- `source-facing`: the existence of a functorial K-injective replacement for every cochain
  complex;
- `core/canonical`: `FunctorialComplexApproximation C` and `I.IsKInjective`;
- `bridge/view`: the extra injective-term and K-injective properties on the chosen approximation.
-/

-- Proof sketch: start from the functorial injective-subobject approximation of Lemma 19.12.5 and
-- iterate it transfinitely as in the proof of Theorem 19.11.7. Lemma 19.12.3 upgrades the limit
-- complex to a K-injective one once the stage has sufficiently large cofinality, while AB5 keeps
-- the transition colimit quasi-isomorphic to the original complex and preserves the degreewise
-- monomorphism and injective-term properties.
/-- Theorem 19.12.6: in a Grothendieck abelian category there exists a functorial assignment
`M^\bullet ↦ I^\bullet` together with a quasi-isomorphism `M^\bullet ⟶ I^\bullet` whose degreewise
components are monomorphisms, such that every term `I^n` is injective and the target complex is
K-injective. -/
theorem exists_functorial_kInjective_resolution (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      (∀ (M : CochainComplex C ℤ) (n : ℤ), Injective ((J.toFunctor.obj M).X n)) ∧
        ∀ M : CochainComplex C ℤ, (J.toFunctor.obj M).IsKInjective := sorry

end

end CochainComplex
