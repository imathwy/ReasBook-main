import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
