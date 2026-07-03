import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_127_1 (from Chap15) -/
noncomputable section

open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.127.1:
- primary domain: the symmetric monoidal structure on `D(R)` together with the source-facing
  derived tensor product notation `⊗[R]^L`;
- sampled owner declarations:
  the anonymous `MonoidalCategory DMod` and `SymmetricCategory DMod` instances from Lemma
  `15.59.14`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`,
  `derivedTensorProduct_associator`,
  `derivedTensorProduct_comm`;
- best owner abstraction:
  `source-facing`: the tensor surface `⊗[R]^L` and its associativity/commutativity constraints;
  `core/canonical`: the ambient `MonoidalCategory DMod` and `SymmetricCategory DMod` instances;
  `bridge/view`: the comparison isomorphism identifying the owner tensor `K ⊗ L` with
  `K ⊗[R]^L L`;
- primitive vs. derived:
  the monoidal and symmetric structures on `D(R)` are the owner data; the comparison with
  `⊗[R]^L` and the displayed associator/commutor are derived API transported from that owner;
- layer: this file is a recall-only `core/canonical` item, so its main entry should recall the
  ambient monoidal and symmetric owners on `D(R)`, with the source-facing associator and
  commutor kept as companions.
-/

/- Lemma 15.127.1: the derived category `D(R)` carries the canonical monoidal structure obtained
by localizing tensor product on complexes. -/
#synth MonoidalCategory DMod

/- The same localized tensor product makes `D(R)` into a symmetric monoidal category. -/
#synth SymmetricCategory DMod

/- The owner tensor on `D(R)` is identified with the source-facing derived tensor product
notation `⊗[R]^L`. -/
section

variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

recall derivedCategory_tensorObj_iso_derivedTensorProduct
    (K L : DMod) :
    K ⊗ L ≅ K ⊗[R]^L L

/- The associativity constraint for `⊗[R]^L` is transported from the ambient monoidal owner on
`D(R)`. -/
recall derivedTensorProduct_associator
    (K L M : DMod) :
    ((K ⊗[R]^L L) ⊗[R]^L M) ≅ (K ⊗[R]^L (L ⊗[R]^L M))

end

end

section

/- The commutativity constraint for `⊗[R]^L` is transported from the ambient symmetric-monoidal
owner on `D(R)`. -/
#check derivedTensorProduct_comm

end

end CategoryTheory

/-! ### Lemma_15_127_2 (from Chap15) -/
open CategoryTheory

universe u

variable {R : Type u} [Ring R]
variable {ι : Type*} [Finite ι]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.127.2:
- primary domain: subcomplexes of a cochain complex of `R`-modules, together with the chapter
  owner for termwise finite-free complexes and the chapter style for arbitrary finite families;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `isMPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`;
- best owner abstraction:
  `source-facing`: a subcomplex `G ⊆ F` containing the chosen finite family of elements;
  `core/canonical`: the owner object `Subobject F`, with boundedness expressed by the ambient
    `IsStrictlyGE`/`IsStrictlyLE` predicates and finite freeness by
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: the inclusion morphism `G.arrow : (G : Cpx) ⟶ F`, whose degreewise components
    realize containment of the chosen elements;
- primitive vs. derived:
  the primitive datum is just the canonical subobject `G : Subobject F`;
  boundedness and termwise finite freeness are properties of the underlying complex and should not
  be repackaged as a parallel local structure, while the chosen finite family should be indexed by
  an arbitrary finite type `ι` rather than the coordinate model `Fin N`.
- layer: this file stays `source-facing`, but its theorem should quantify over `Subobject F`
  directly instead of introducing a duplicate wrapper owner, with the finite-family input kept at
  the weaker canonical `ι : Type*` / `[Finite ι]` abstraction level.
-/

-- Proof sketch: let `a` be the minimum of the finitely many prescribed degrees. Choose finitely
-- many basis vectors in degree `a` spanning the specified elements there, enlarge degree `a + 1`
-- by finitely many basis vectors containing their differentials, and then apply descending
-- induction on the lower bound to build a bounded finite free subcomplex containing every chosen
-- element.
/-- Lemma 15.127.2: a bounded above complex of free `R`-modules contains any finite family of
specified elements in a bounded finite free subcomplex. -/
theorem exists_bounded_finite_free_subcomplex_containing
    (F : Cpx)
    (hbounded : ∃ b : ℤ, F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i)) :
    ∃ G : Subobject F,
      (∃ a b : ℤ, (G : Cpx).IsStrictlyGE a ∧ (G : Cpx).IsStrictlyLE b) ∧
      (G : Cpx).IsTermwiseFiniteFree ∧
      ∀ i : ι,
        ∃ g : (G : Cpx).X (degrees i), G.arrow.f (degrees i) g = elements i :=
  sorry

/-! ### Lemma_15_127_3 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

/-
Domain-style sampling for Lemma 15.127.3:
- primary domain: rigid duality for perfect objects in the monoidal derived category `D(R)`;
- sampled owner declarations:
  `ExactPairing`,
  `HasLeftDual`,
  `derivedDualExactPairing`,
  `leftDualIso`,
  `DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the existence theorem that `M` admits a duality datum exactly when `M` is
    perfect, together with the identification of any chosen dual object with the canonical derived
    dual `Mᵛ⟮H⟯ = R\mathrm{Hom}_R(M, R[0])`;
  `core/canonical`: an arbitrary exact pairing `ExactPairing N M` and the chapter owner
    `DerivedCategory.IsPerfect`;
  `bridge/view`: the canonical pairing `derivedDualExactPairing` attached to a perfect object and
    the uniqueness isomorphism `leftDualIso` comparing any other left dual with it.

Primitive data are only the chosen derived-internal-Hom package `H`, the object `M`, and an
arbitrary exact pairing `ExactPairing N M`. The canonical dual `Mᵛ⟮H⟯` and the comparison from a
chosen dual object are derived API, so this file should recall `derivedDualExactPairing` for the
forward half, state the converse for arbitrary dual data, and keep the uniqueness isomorphism only
as a bridge to the canonical derived dual.
-/

variable (H : RHomPkg)

/- Lemma 15.127.3 (forward direction): for a perfect object of `D(R)`, the derived dual
`Mᵛ⟮H⟯ = R\mathrm{Hom}_R(M, R[0])` is canonically a left dual via the owner declaration
`derivedDualExactPairing`. -/
recall derivedDualExactPairing
    (H : RHomPkg) {M : DMod}
    (hM : DerivedCategory.IsPerfect M) :
    ExactPairing Mᵛ⟮H⟯ M

-- Proof sketch: choose the coevaluation from the assumed exact pairing `ExactPairing N M`, factor it
-- through a bounded finite free subcomplex by Lemma `15.127.2`, and apply the triangle identity
-- to show that `𝟙_M` factors through a perfect object. Since perfect objects are closed under
-- retracts, `M` itself is perfect.
/-- Lemma 15.127.3 (converse): if `M` admits a duality datum in the monoidal category `D(R)`,
then `M` is perfect. -/
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing N M) :
    DerivedCategory.IsPerfect M := by
  sorry

/- Bridge/view for Lemma `15.127.3`: uniqueness of left duals is already owned by
`leftDualIso`. For a chosen pairing `hpair : ExactPairing N M`, the textbook comparison
`N ≅ Mᵛ⟮H⟯` is obtained directly as
`leftDualIso hpair (derivedDualExactPairing H (exactPairing_isPerfect hpair))`,
so this file should not introduce a second wrapper around that owner declaration. -/
recall leftDualIso
    {C : Type _} [Category C] [MonoidalCategory C]
    {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    X₁ ≅ X₂

end

end CategoryTheory

/-! ### Lemma_15_127_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-
Domain-style sampling for Lemma 15.127.4:
- primary domain: invertible objects in the monoidal derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.tensorLeft_isEquivalence_iff_exists_tensor_inverse`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.exactPairing_isPerfect`,
  `CategoryTheory.ringSingle`,
  `CategoryTheory.derivedTensorWithAlgebra`;
- best owner abstraction:
  `source-facing`: the local criterion that an invertible object of `D(R)` becomes a shifted copy
    of the localized unit after derived base change to some `Localization.Away f`;
  `core/canonical`: the chapter owner `DerivedCategory.IsPerfect` for perfectness and the monoidal
    owner `ExactPairing N M` for left-dual data;
  `bridge/view`: chosen tensor-inverse data extracted from `(tensorLeft M).IsEquivalence`, used
    only internally to build an exact pairing and invoke `exactPairing_isPerfect`, together with
    the chapter notation `M ⊗[R]^L[Localization.Away f]` for derived localization.

Primitive data are only the invertibility witness `(tensorLeft M).IsEquivalence`, the localized
derived tensor product, and the shifted localized unit `ringSingleAway[f]⟦-n⟧`. The perfectness
conclusion is derived API via the existing chapter owner `exactPairing_isPerfect`, so this file
should keep only the source-facing local criterion and that thin canonical corollary.
-/

local notation "DModAway[" f "]" => DerivedCategory (ModuleCat (Localization.Away f))
local notation "ringSingleAway[" f "]" => (ringSingle : DModAway[f])

-- Proof sketch: for the forward implication, tensoring with the inverse of an invertible object
-- shows that after localization at every prime, the base change of `M` is still invertible over
-- the localized ring; over a local ring an invertible perfect object is a single shift of the
-- unit. For the reverse implication, apply the local criterion prime-by-prime to the evaluation
-- map from the derived dual tensor `M`, and conclude that it is an isomorphism globally because
-- isomorphisms in `D(R)` can be checked after localization.
/-- Lemma 15.127.4: an object `M` of `D(R)` is invertible if and only if for every prime ideal
`𝔭 ⊂ R` there exists an element `f ∉ 𝔭` such that the derived localization `M_f` is isomorphic to
`R_f[-n]` for some integer `n`. -/
theorem isInvertibleObject_iff_locally_isomorphic_to_shifted_localized_ring
    (M : DMod) :
    (tensorLeft M).IsEquivalence ↔
      ∀ p : PrimeSpectrum R,
        ∃ f : R, f ∉ p.asIdeal ∧ ∃ n : ℤ,
          IsIsomorphic (M ⊗[R]^L[Localization.Away f]) (ringSingleAway[f]⟦-n⟧) := sorry

/-
Proof sketch: once `M` is invertible, choose a tensor inverse `N` using
`tensorLeft_isEquivalence_iff_exists_tensor_inverse`. The isomorphisms `M ⊗ N ≅ 𝟙` and
`N ⊗ M ≅ 𝟙` provide an exact pairing `ExactPairing N M`, so the perfectness conclusion is the
canonical Chapter 15 consequence `exactPairing_isPerfect`.
-/
/-- An invertible object of `D(R)` is perfect. -/
theorem isPerfect_of_isInvertibleObject
    {M : DMod} (hM : (tensorLeft M).IsEquivalence) :
    M.IsPerfect := by
  rcases (tensorLeft_isEquivalence_iff_exists_tensor_inverse M).1 hM with
    ⟨N, ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  have hpair : ExactPairing N M := by
    letI : ExactPairing M N :=
      { coevaluation' := e₁.inv
        evaluation' := e₂.hom
        coevaluation_evaluation' := by
          sorry
        evaluation_coevaluation' := by
          sorry }
    exact BraidedCategory.exactPairing_swap M N
  simpa using exactPairing_isPerfect hpair

end

end CategoryTheory
