import Mathlib
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_13_1 (from Chap12) -/
open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Lemma 12.13.1:
- primary domain: homotopies of homological complexes in a preadditive category;
- sampled canonical owner declarations:
  `Homotopy`,
  `Homotopy.compLeft`,
  `Homotopy.compRight`,
  `Homotopy.comp`;
- best owner abstraction: `Homotopy` on `HomologicalComplex V c`;
- primitive data: the fields `hom`, `zero`, and `comm` of a homotopy;
- derived API: closure under precomposition and postcomposition, together with the degreewise
  component lemmas `Homotopy.compLeft_hom` and `Homotopy.compRight_hom`;
- source/core/bridge triage:
  `core/canonical`: `Homotopy` and its composition operations on `HomologicalComplex`.

This item is already owner-side mathematics, so the refined file should recall the canonical
declarations directly rather than introduce a chapter-local duplicate wrapper or alias.
-/

/- Lemma 12.13.1: the owner abstraction `Homotopy` is closed under precomposition and
postcomposition by morphisms of chain complexes, via the canonical operations
`Homotopy.compLeft` and `Homotopy.compRight`. -/
recall Homotopy.compLeft
recall Homotopy.compRight

/- The degreewise formulas for these owner operations are already the canonical component lemmas
`Homotopy.compLeft_hom` and `Homotopy.compRight_hom`. -/
recall Homotopy.compLeft_hom
recall Homotopy.compRight_hom

/-! ### Definition_12_13_2 (from Chap12) -/
universe v u

open CategoryTheory HomologicalComplex

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Definition 12.13.2:
- primary domain: homotopy equivalences of homological complexes in a preadditive category;
- sampled canonical declarations:
  `HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `HomotopyEquiv.ofIso`,
  `HomotopyEquiv.trans`;
- source/core/bridge triage:
  `core/canonical`: `HomotopyEquiv A B`,
  `bridge/view`: `homotopyEquivalences V c a`.

The primitive data are already owned by `HomotopyEquiv`: a forward map, a backward map, and the
two homotopies exhibiting the composites as homotopic to the identities. The morphism-property
formulation `homotopyEquivalences` is derived from that owner and should remain a bridge/view,
not a parallel chapter-local notion.
-/

/- Definition 12.13.2: the owner notion that two complexes in an additive category are homotopy
equivalent is the canonical structure `HomotopyEquiv`; the associated morphism property is
`homotopyEquivalences`. -/
recall HomotopyEquiv
recall HomologicalComplex.homotopyEquivalences

/-! ### Lemma_12_13_3 (from Chap12) -/
open CategoryTheory Limits HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 12.13.3:
- primary domain: homological complexes, with monomorphisms, epimorphisms, and exactness detected
  degreewise.
- sampled owner declarations in this domain:
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.exact_iff_degreewise_exact`,
  `HomologicalComplex.instAbelian`.
- owner abstraction: `ChainComplex A ℤ` is the source-facing specialization of
  `HomologicalComplex A (ComplexShape.down ℤ)`.
- primitive data: the degreewise components `φ.f i` of a morphism and the degreewise short
  complexes `S.map (eval A (ComplexShape.down ℤ) i)`.
- derived API: the source-facing degreewise bridge lemmas `(1)` and `(2)`.
- source/core/bridge triage:
  `(1)` and `(2)` are `source-facing` bridge declarations;
  the abelian instance and the exactness equivalence in `(3)` are `core/canonical` owner API
  already provided by `HomologicalComplex`, so this file should reuse them directly rather than
  keep parallel local wrappers. -/

section

variable [HasZeroMorphisms A] [HasPullbacks A]

/-- Lemma 12.13.3 (1): a morphism of chain complexes is monomorphic exactly when each degree
component is monomorphic. This is the chain-complex specialization of the canonical owner
construction `mono_of_mono_f`, with the forward implication coming from the owner evaluation
functors. -/
theorem chainComplex_mono_iff_degreewise_mono {K L : ChainComplex A ℤ} (φ : K ⟶ L) :
    Mono φ ↔ ∀ i : ℤ, Mono (φ.f i) := by
  constructor
  · intro hφ i
    letI : Mono φ := hφ
    have : Mono ((eval A (down ℤ) i).map φ) := inferInstance
    simpa using this
  · intro hφ
    exact mono_of_mono_f φ hφ

end

section

variable [HasZeroMorphisms A] [HasPushouts A]

/-- Lemma 12.13.3 (2): a morphism of chain complexes is epimorphic exactly when each degree
component is epimorphic. This is the chain-complex specialization of the canonical owner
construction `epi_of_epi_f`, with the forward implication coming from the owner evaluation
functors. -/
theorem chainComplex_epi_iff_degreewise_epi {K L : ChainComplex A ℤ} (φ : K ⟶ L) :
    Epi φ ↔ ∀ i : ℤ, Epi (φ.f i) := by
  constructor
  · intro hφ i
    letI : Epi φ := hφ
    have : Epi ((eval A (down ℤ) i).map φ) := inferInstance
    simpa using this
  · intro hφ
    exact epi_of_epi_f φ hφ

end

section

/- Lemma 12.13.3: if `A` is an abelian category, then the category of chain complexes in `A`
is abelian. -/
variable [Abelian A]

recall HomologicalComplex.instAbelian

section

variable (S : ShortComplex (ChainComplex A ℤ))

/- Lemma 12.13.3 (3): exactness for short complexes of chain complexes is exactly the canonical
degreewise exactness statement `HomologicalComplex.exact_iff_degreewise_exact`, specialized to the
shape `down ℤ`. -/
recall HomologicalComplex.exact_iff_degreewise_exact

end
end

/-! ### Definition_12_13_4 (from Chap12) -/
open CategoryTheory

/- Domain-style sampling for Definition 12.13.4:
- primary domain: quasi-isomorphisms and acyclic chain complexes;
- sampled canonical owner declarations:
  `QuasiIso`,
  `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`,
  `HomologicalComplex.Acyclic`,
  `HomologicalComplex.acyclic_iff`,
  `HomologicalComplex.exactAt_iff_isZero_homology`;
- source/core/bridge triage:
  `core/canonical`: `QuasiIso f` and `K.Acyclic`,
  `bridge/view`: the owner characterizations `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`, `HomologicalComplex.acyclic_iff`, and
  `HomologicalComplex.exactAt_iff_isZero_homology`.

Primitive data are already owned by `QuasiIso` and `HomologicalComplex.Acyclic`. The source-facing
criteria are therefore best exposed by direct recall of the owner predicates and their canonical
characterization lemmas, rather than by introducing a local recombination theorem.
-/

/- Definition 12.13.4 (1): a morphism of chain complexes is a quasi-isomorphism when it induces
isomorphisms on homology in every degree; this is the canonical mathlib predicate `QuasiIso`,
used in particular for chain complexes in an abelian category. -/
recall QuasiIso
recall quasiIso_iff
recall quasiIsoAt_iff_isIso_homologyMap

/- Definition 12.13.4 (2): a chain complex is acyclic when it is exact in every degree; mathlib
packages this canonical notion by `HomologicalComplex.Acyclic`, and in an abelian category this is
equivalent to vanishing of all homology objects. -/
recall HomologicalComplex.Acyclic
recall HomologicalComplex.acyclic_iff
recall HomologicalComplex.exactAt_iff_isZero_homology

/-! ### Lemma_12_13_5 (from Chap12) -/
open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Abelian V]

/- Domain-style sampling:
- primary domain: homotopy invariance and quasi-isomorphisms for homological complexes
- core/canonical owner abstraction: `Homotopy` and `HomotopyEquiv` on `HomologicalComplex`
- primitive data: a homotopy between morphisms, or a homotopy equivalence
- derived API: equality of induced homology maps, the canonical homology isomorphism of a
  homotopy equivalence, and the quasi-isomorphism consequence
- source-facing layer here: the `ChainComplex V ℤ` specialization
- bridge/view layer: rewriting the owner-side morphism-property statement via `mem_quasiIso_iff`
-/

/- Lemma 12.13.5: homotopic maps of chain complexes in an abelian category induce the same maps
on homology. This is exactly the owner theorem `Homotopy.homologyMap_eq`, specialized to
`ChainComplex V ℤ`. -/
recall Homotopy.homologyMap_eq
recall HomotopyEquiv.toHomologyIso

/- The quasi-isomorphism consequence for a homotopy equivalence is the owner-side comparison
`homotopyEquivalences_le_quasiIso`; for chain complexes, the source-facing `QuasiIso`
formulation is obtained by rewriting with `mem_quasiIso_iff`. -/
recall homotopyEquivalences_le_quasiIso
recall mem_quasiIso_iff

/-! ### Lemma_12_13_6 (from Chap12) -/
open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/-
Domain-style sampling in the homology-sequence owner API:
- primitive owner data: `ShortComplex.ShortExact.δ`
- owner sequence object: `HomologicalComplex.HomologySequence.composableArrows₅`
- derived exactness pieces: `ShortComplex.ShortExact.homology_exact₁`,
  `ShortComplex.ShortExact.homology_exact₂`, `ShortComplex.ShortExact.homology_exact₃`
- owner exact five-term segment: `HomologicalComplex.HomologySequence.composableArrows₅_exact`

Lemma 12.13.6 is `bridge/view`: the chain-complex `ComplexShape.down ℤ` specialization of that
owner theorem, so the main entry should be direct specialized use of the owner theorem rather than
a parallel chapter-local theorem.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/-
Lemma 12.13.6: a short exact sequence of chain complexes in an abelian category yields the
canonical exact homology segment
`H_i(A_•) ⟶ H_i(B_•) ⟶ H_i(C_•) ⟶ H_{i-1}(A_•) ⟶ H_{i-1}(B_•) ⟶ H_{i-1}(C_•)`,
with connecting morphism
`hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))`. This is exactly the owner theorem
`HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the chain-complex
shape `ComplexShape.down ℤ`. -/
#check (composableArrows₅_exact hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) :
    (composableArrows₅ hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))).Exact)

end CategoryTheory

/-! ### Lemma_12_13_7 (from Chap12) -/
open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

/- Domain-style sampling:
- primary domain: homotopies of homological complexes in a preadditive category
- sampled canonical owner declarations:
  `Homotopy`,
  `Homotopy.compLeft`,
  `Homotopy.compRight`,
  `Homotopy.compLeft_hom`,
  `Homotopy.compRight_hom`
- best owner abstraction: `Homotopy` on `HomologicalComplex V c`
- primitive data: the fields `hom`, `zero`, and `comm` of a homotopy
- derived API: closure under precomposition and postcomposition, together with the degreewise
  component lemmas `Homotopy.compLeft_hom` and `Homotopy.compRight_hom`
- source/core/bridge triage:
  `core/canonical`: `Homotopy` and its composition operations on `HomologicalComplex`,
  `bridge/view`: the cochain-complex whiskering statement obtained by combining
  `Homotopy.compLeft` and `Homotopy.compRight`

Lemma 12.13.7 is not just a recall of the separate owner operations: it is the thin cochain-side
bridge that packages both whiskerings into the specific homotopy with components
`a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1)`.
-/

namespace Homotopy

variable {A B C D : CochainComplex V ℤ} {a : A ⟶ B} {f g : B ⟶ C} {c : C ⟶ D}

/-- Lemma 12.13.7: if `h : Homotopy f g`, then whiskering `h` on the left by `a` and on the right
by `c` gives a homotopy from `((a ≫ f) ≫ c)` to `((a ≫ g) ≫ c)`, corresponding to the source
notation `c ∘ f ∘ a` and `c ∘ g ∘ a`. -/
def cochainWhisker (a : A ⟶ B) (h : Homotopy f g) (c : C ⟶ D) :
    Homotopy ((a ≫ f) ≫ c) ((a ≫ g) ≫ c) :=
  (h.compLeft a).compRight c

/-- The degree-`i` component of `cochainWhisker h` corresponds to the source formula
`c^{i - 1} ∘ h^i ∘ a^i`; in Lean this is
`a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1)`. -/
theorem cochainWhisker_hom (h : Homotopy f g) (i : ℤ) :
    (cochainWhisker a h c).hom i (i - 1) =
      a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1) := by
  simp [cochainWhisker]

end Homotopy

/-! ### Definition_12_13_8 (from Chap12) -/
open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type v} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/- Domain-style sampling for Definition 12.13.8:
- primary domain: homotopy equivalences of homological complexes in a preadditive category;
- sampled canonical declarations:
  `HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `HomotopyEquiv.ofIso`,
  `HomotopyEquiv.trans`;
- source/core/bridge triage:
  `core/canonical`: `HomotopyEquiv A B`,
  `bridge/view`: `homotopyEquivalences V c a`.

The primitive data are already owned by `HomotopyEquiv`: a forward map, a backward map, and the
two homotopies from the composites to the identities. The morphism-property formulation
`homotopyEquivalences` is derived API from that owner, so the present item should recall only that
canonical source-facing bridge rather than duplicating the owner entry from Definition 12.13.2.
-/

/- Definition 12.13.8: for complexes in an additive category, the property that a morphism is a
homotopy equivalence is the canonical morphism property
`HomologicalComplex.homotopyEquivalences`. -/
recall HomologicalComplex.homotopyEquivalences

/-! ### Lemma_12_13_9 (from Chap12) -/
open CategoryTheory Limits HomologicalComplex ComplexShape

universe u v

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 12.13.9:
- primary domain: homological complexes, with monomorphisms, epimorphisms, and exactness detected
  degreewise.
- sampled owner declarations in this domain:
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.exact_iff_degreewise_exact`,
  `HomologicalComplex.instAbelian`.
- owner abstraction: `CochainComplex A ℤ` is the source-facing specialization of
  `HomologicalComplex A (up ℤ)`.
- primitive data: the degreewise components `φ.f i` of a morphism and the degreewise short
  complexes `S.map (eval A (up ℤ) i)`.
- derived API: the source-facing degreewise bridge lemmas `(1)` and `(2)`.
- source/core/bridge triage:
  `(1)` and `(2)` are `source-facing` bridge declarations;
  the abelian instance and the exactness equivalence in `(3)` are `core/canonical` owner API
  already provided by `HomologicalComplex`, so this file should reuse them directly rather than
  keep parallel local wrappers. -/

section

variable [HasZeroMorphisms A] [HasPullbacks A]

/-- Lemma 12.13.9 (1): a morphism of cochain complexes is monomorphic exactly when each degree
component is monomorphic. This is the cochain-complex specialization of the canonical owner
construction `mono_of_mono_f`, and the forward implication only uses that evaluation preserves
pullbacks. -/
theorem cochainComplex_mono_iff_degreewise_mono {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    Mono φ ↔ ∀ i : ℤ, Mono (φ.f i) := by
  constructor
  · intro hφ i
    letI : Mono φ := hφ
    change Mono ((eval A (up ℤ) i).map φ)
    infer_instance
  · exact mono_of_mono_f φ

end

section

variable [HasZeroMorphisms A] [HasPushouts A]

/-- Lemma 12.13.9 (2): a morphism of cochain complexes is epimorphic exactly when each degree
component is epimorphic. This is the cochain-complex specialization of the canonical owner
construction `epi_of_epi_f`, and the forward implication only uses that evaluation preserves
pushouts. -/
theorem cochainComplex_epi_iff_degreewise_epi {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    Epi φ ↔ ∀ i : ℤ, Epi (φ.f i) := by
  constructor
  · intro hφ i
    letI : Epi φ := hφ
    change Epi ((eval A (up ℤ) i).map φ)
    infer_instance
  · exact epi_of_epi_f φ

end

section

/- Lemma 12.13.9: if `A` is an abelian category, then the category of cochain complexes in `A`
is abelian. -/
variable [Abelian A]

recall HomologicalComplex.instAbelian

section

variable (S : ShortComplex (CochainComplex A ℤ))

/- Lemma 12.13.9 (3): exactness for short complexes of cochain complexes is exactly the canonical
degreewise exactness statement `HomologicalComplex.exact_iff_degreewise_exact`, specialized to the
shape `up ℤ`. -/
recall HomologicalComplex.exact_iff_degreewise_exact

end
end

/-! ### Definition_12_13_10 (from Chap12) -/
open CategoryTheory

universe v u

variable {V : Type u} [Category.{v} V] [Abelian V]

/- Domain-style sampling for Definition 12.13.10:
- primary domain: quasi-isomorphisms and acyclic cochain complexes;
- sampled canonical owner declarations:
  `QuasiIso`,
  `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`,
  `HomologicalComplex.Acyclic`,
  `HomologicalComplex.acyclic_iff`,
  `HomologicalComplex.exactAt_iff_isZero_homology`;
- source/core/bridge triage:
  `core/canonical`: `QuasiIso f` and `K.Acyclic`,
  `bridge/view`: the owner characterizations `quasiIso_iff`,
  `quasiIsoAt_iff_isIso_homologyMap`, `HomologicalComplex.acyclic_iff`, and
  `HomologicalComplex.exactAt_iff_isZero_homology`.

Primitive data are already owned by `QuasiIso` and `HomologicalComplex.Acyclic`. The source-facing
criteria are therefore best exposed by direct recall of the owner predicates and their canonical
characterization lemmas, rather than by introducing a cochain-specific chapter-local wrapper.
-/

/- Definition 12.13.10 (1): a morphism of cochain complexes is a quasi-isomorphism exactly when it
satisfies the canonical predicate `QuasiIso`; equivalently, each induced cohomology map is an
isomorphism. -/
recall QuasiIso
recall quasiIso_iff
recall quasiIsoAt_iff_isIso_homologyMap

/- Definition 12.13.10 (2): a cochain complex is acyclic when it is exact in every degree; mathlib
packages this canonical notion by `HomologicalComplex.Acyclic`, and in an abelian category this is
equivalent to vanishing of all cohomology objects. -/
recall HomologicalComplex.Acyclic
recall HomologicalComplex.acyclic_iff
recall HomologicalComplex.exactAt_iff_isZero_homology

/-! ### Lemma_12_13_11 (from Chap12) -/
/- Domain-style sampling:
- primary domain: homotopy invariance and quasi-isomorphisms for homological complexes;
- sampled canonical declarations:
  `Homotopy.homologyMap_eq`,
  `HomotopyEquiv.toHomologyIso`,
  `homotopyEquivalences_le_quasiIso`,
  `HomologicalComplex.mem_quasiIso_iff`;
- best owner abstraction: `Homotopy` and `HomotopyEquiv` on `HomologicalComplex`;
- primitive data: a homotopy between two morphisms, or a homotopy equivalence;
- derived API: equality of the induced homology maps, the canonical homology isomorphism of a
  homotopy equivalence, and the resulting quasi-isomorphism property;
- source/core/bridge triage:
  `core/canonical`: `Homotopy`, `HomotopyEquiv`,
  `bridge/view`: the `QuasiIso` reformulation via `HomologicalComplex.mem_quasiIso_iff`.

No extra chapter-local wrapper is needed here: the mathematical content already lives on the
owner-side declarations for homotopies of homological complexes, and the quasi-isomorphism
statement is only a companion view.
-/

/- Lemma 12.13.11: if two morphisms of complexes in an abelian category are homotopic, then they
induce the same map on homology in every degree. The quasi-isomorphism consequence for a homotopy
equivalence is recalled below via the canonical owner-side comparison. -/
recall Homotopy.homologyMap_eq
recall HomotopyEquiv.toHomologyIso

/- The quasi-isomorphism consequence of a homotopy equivalence is the owner-side comparison
`homotopyEquivalences_le_quasiIso`; the source-facing `QuasiIso` formulation is obtained by
rewriting with `HomologicalComplex.mem_quasiIso_iff`. -/
recall homotopyEquivalences_le_quasiIso
recall HomologicalComplex.mem_quasiIso_iff

/-! ### Lemma_12_13_12 (from Chap12) -/
open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: cohomology exact sequences attached to short exact sequences of cochain
  complexes, together with the shift identifications relating neighboring degrees;
- sampled owner declarations:
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`,
  `HomologicalComplex.HomologySequence.mapComposableArrows₅`,
  `CochainComplex.ShiftSequence.shiftIso`;
- best owner abstraction for the main exactness statement: the generic homology-sequence owner
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`, with the textbook cochain
  statement obtained by specialization to `ComplexShape.up ℤ`.

Source/core/bridge triage:
- `source-facing`: the cochain exact segment
  `H^i(A^•) ⟶ H^i(B^•) ⟶ H^i(C^•) ⟶ H^(i + 1)(A^•) ⟶ H^(i + 1)(B^•) ⟶ H^(i + 1)(C^•)`;
- `core/canonical`: `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `bridge/view`: the `ComplexShape.up ℤ` specializations of
  `composableArrows₅_exact` and `mapComposableArrows₅`.

Primitive data are exactly the short exactness witness `hS : S.ShortExact`; the exact segment,
its functorial map under a morphism of short exact sequences, and the cochain shift comparison
are derived API from the owner declarations above.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/- Lemma 12.13.12: a short exact sequence of cochain complexes in an abelian category yields the
canonical exact cohomology segment
`H^i(A^•) ⟶ H^i(B^•) ⟶ H^i(C^•) ⟶ H^(i + 1)(A^•) ⟶ H^(i + 1)(B^•) ⟶ H^(i + 1)(C^•)`,
with connecting morphism `hS.δ i (i + 1) (up_mk i (i + 1) rfl)`. This is exactly the owner
theorem `HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the
cochain shape `ComplexShape.up ℤ`. -/
#check (HomologicalComplex.HomologySequence.composableArrows₅_exact hS i (i + 1)
  (up_mk i (i + 1) rfl) :
    (composableArrows₅ hS i (i + 1) (up_mk i (i + 1) rfl)).Exact)

/- Functoriality companion: a morphism of short exact sequences of cochain complexes induces a
morphism between the corresponding exact cohomology segments in degree `i`. This is the
`ComplexShape.up ℤ` specialization of the owner map `mapComposableArrows₅`. -/
variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
variable (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

#check (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1)
  (up_mk i (i + 1) rfl) :
    composableArrows₅ hS₁ i (i + 1) (up_mk i (i + 1) rfl) ⟶
      composableArrows₅ hS₂ i (i + 1) (up_mk i (i + 1) rfl))

/- Shift-compatibility companion: the cohomology functor on cochain complexes carries the
canonical shift isomorphisms `H^i(K⟦n⟧) ≅ H^(i + n)(K)` used to identify the long exact sequence
of a shifted short exact sequence with the shifted long exact sequence. This is the source-facing
cochain owner `CochainComplex.ShiftSequence.shiftIso`. -/
recall CochainComplex.ShiftSequence.shiftIso

end CategoryTheory
