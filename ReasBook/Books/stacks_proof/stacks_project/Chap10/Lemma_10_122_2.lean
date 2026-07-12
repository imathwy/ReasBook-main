import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_122_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 122 2: the commutative ring structure on a residue field induced
by its field structure. -/
private noncomputable abbrev residueFieldFieldCommRing (p : PrimeSpectrum R) :
    CommRing p.asIdeal.ResidueField :=
  Field.toEuclideanDomain.toCommRing

attribute [local instance] residueFieldFieldCommRing

/-- Helper for Chap10 Lemma 10 122 2: the algebra structure on the residue field of a fiber prime
over the residue field of the base prime. -/
private noncomputable abbrev fiberPrimeResidueFieldAlgebra (p : PrimeSpectrum R)
    (qbar : PrimeSpectrum (p.asIdeal.Fiber S)) :
    Algebra p.asIdeal.ResidueField qbar.asIdeal.ResidueField :=
  IsLocalRing.ResidueField.algebra (Localization.AtPrime qbar.asIdeal)

attribute [local instance] fiberPrimeResidueFieldAlgebra

/-- Helper for Chap10 Lemma 10 122 2: the canonical fiber homeomorphism preserves singleton
openness. -/
private lemma isOpen_singleton_preimageEquivFiber_iff (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    IsOpen ({PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩} :
      Set (PrimeSpectrum (p.asIdeal.Fiber S))) ↔
    IsOpen ({(⟨q, hq⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})} :
      Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) := by
  -- Proof comment: rewrite the fiber-ring singleton as the image of the source singleton.
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← Set.image_singleton]
  exact e.isOpen_image

/-- Helper for Chap10 Lemma 10 122 2: an open singleton in the fiber is cut out by an ambient
basic open. -/
private lemma exists_basicOpen_fiber_eq_singleton_of_isOpen_singleton
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hopen : IsOpen ({(⟨q, hq⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})} :
      Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}))) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ((({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
        (D(g) : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) =
          ({q} : Set (PrimeSpectrum S))) := by
  -- Proof comment: lift the open singleton to an ambient open and shrink it to a basic open.
  rcases isOpen_induced_iff.mp hopen with ⟨U, hUopen, hUtrace⟩
  have hqU : q ∈ U := by
    have hx : (⟨q, hq⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ∈
        (Subtype.val ⁻¹' U : Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) := by
      rw [hUtrace]
      simp
    exact hx
  obtain ⟨V, ⟨g, hgV⟩, hqV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hUopen
  subst V
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g q).1 hqV, ?_⟩
  -- Proof comment: in the fiber, membership in this basic open forces membership in the trace.
  ext q'
  constructor
  · intro hq'
    rcases hq' with ⟨hq'fiber, hq'basic⟩
    let x' : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := ⟨q', hq'fiber⟩
    have hx'U : x' ∈
        (Subtype.val ⁻¹' U : Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) :=
      hVU hq'basic
    have hx'sing : x' ∈
        ({(⟨q, hq⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})} :
          Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) := by
      simpa [hUtrace] using hx'U
    have hx'eq : x' = ⟨q, hq⟩ := by
      simpa using hx'sing
    exact congrArg Subtype.val hx'eq
  · intro hq'eq
    subst q'
    exact ⟨hq, hqV⟩

/-- Helper for Chap10 Lemma 10 122 2: an ambient basic open cutting out the fiber point makes the
fiber singleton open. -/
private lemma isOpen_singleton_of_exists_basicOpen_fiber_eq_singleton
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hbasic : ∃ g : S, g ∉ q.asIdeal ∧
      ((({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
        (D(g) : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) =
          ({q} : Set (PrimeSpectrum S)))) :
    IsOpen ({(⟨q, hq⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})} :
      Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) := by
  -- Proof comment: realize the subtype singleton as the trace of the chosen basic open.
  rcases hbasic with ⟨g, hgq, hcut⟩
  rw [isOpen_induced_iff]
  refine ⟨(D(g) : Set (PrimeSpectrum S)), PrimeSpectrum.isOpen_basicOpen, ?_⟩
  ext x
  constructor
  · intro hx
    have hxcut : x.1 ∈ ((({q' : PrimeSpectrum S |
        PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
          (D(g) : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S))) :=
      ⟨x.2, hx⟩
    rw [hcut] at hxcut
    have hxval : x.1 = q := by
      simpa using hxcut
    exact Subtype.ext hxval
  · intro hx
    have hxeq : x = ⟨q, hq⟩ := by
      simpa using hx
    rw [hxeq]
    exact (PrimeSpectrum.mem_basicOpen g q).2 hgq

/-- Helper for Chap10 Lemma 10 122 2: fiber-ring singleton openness is equivalent to the textbook
ambient basic-open condition on the primes over `p`. -/
private lemma isOpen_preimageEquivFiber_singleton_iff_exists_basicOpen_fiber_eq_singleton
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    IsOpen ({PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩} :
      Set (PrimeSpectrum (p.asIdeal.Fiber S))) ↔
      ∃ g : S, g ∉ q.asIdeal ∧
      ((({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
        (D(g) : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) =
          ({q} : Set (PrimeSpectrum S))) := by
  -- Proof comment: combine homeomorphic transport with the basic-open description of fiber traces.
  rw [isOpen_singleton_preimageEquivFiber_iff p q hq]
  constructor
  · exact exists_basicOpen_fiber_eq_singleton_of_isOpen_singleton p q hq
  · exact isOpen_singleton_of_exists_basicOpen_fiber_eq_singleton p q hq

variable [Algebra.FiniteType R S]

/- Domain-style sampling for Lemma 10.122.2:
- primary domain: the fiber of `Spec S → Spec R` over a prime `p`, viewed through the canonical
  fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S`;
- sampled owner declarations:
  `PrimeSpectrum.preimageEquivFiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `isolatedPoint_tfae`,
  `topologicalKrullDimAt`;
- best owner abstraction: the canonical fiber-prime owner
  `PrimeSpectrum.preimageEquivFiber R S p`, with Lemma `10.122.1` supplying the derived
  isolated-point `List.TFAE` on the fiber ring;
- primitive data: `p : PrimeSpectrum R`, `q : PrimeSpectrum S`, and the lies-over witness
  `hq : PrimeSpectrum.comap (algebraMap R S) q = p`;
- derived API: the six equivalent fiberwise conditions.

Source/core/bridge triage:
- `source-facing`: `prime_over_isolated_point_in_fiber_tfae`;
- `core/canonical`: `PrimeSpectrum.preimageEquivFiber`, `PrimeSpectrum.preimageHomeomorphFiber`,
  and `isolatedPoint_tfae`;
- `bridge/view`: clause `(3)`, which keeps the textbook basic-open singleton condition on primes
  of `S` lying over `p` while the other clauses live directly on the fiber prime. -/

-- Proof sketch: identify the fiber of `Spec S → Spec R` over `p` with `Spec (κ(p) ⊗[R] S)` via
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under this correspondence, the point `q` becomes
-- `PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩`, and the six clauses are exactly the six
-- clauses of Lemma `10.122.1` for the finite type `κ(p)`-algebra `p.asIdeal.Fiber S`, with
-- clause `(3)` restated in the source-facing primes-over-`p` basic-open language.
/-- Chap10 Lemma 10 122 2: for a finite type ring map `R → S`, a prime `q` of `S` lying over `p`, and the
corresponding point `\bar q` of the fiber `Spec (κ(p) ⊗[R] S)`, the following are equivalent:
`\bar q` is an isolated point of the fiber; the local fiber ring at `\bar q` is finite over
`κ(p)`; there exists `g ∉ q` such that the primes of `S` lying over `p` inside `D(g)` are exactly
`{q}`; the local topological dimension of the fiber at `\bar q` is zero; `\bar q` is closed and
the local fiber ring has Krull dimension zero; and the residue field extension at `\bar q` is
finite over `κ(p)` while the local fiber ring has Krull dimension zero. -/
@[stacks 00PK]
theorem prime_over_isolated_point_in_fiber_tfae (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    let qbar : PrimeSpectrum (p.asIdeal.Fiber S) := PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩
    List.TFAE
      [ IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))
      , Module.Finite p.asIdeal.ResidueField (Localization.AtPrime qbar.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧
          ({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
            (D(g) : Set (PrimeSpectrum S)) = ({q} : Set (PrimeSpectrum S)))
      , topologicalKrullDimAt qbar = 0
      , IsClosed ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      , Module.Finite p.asIdeal.ResidueField qbar.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      ] := by
  -- Proof comment: name the fiber-ring prime and use the already proved fiber-ring TFAE.
  intro qbar
  have howner := isolatedPoint_tfae (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) qbar
  have hbridge : IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ↔
      ∃ g : S, g ∉ q.asIdeal ∧
        ((({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
          (D(g) : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) =
            ({q} : Set (PrimeSpectrum S))) := by
    simpa [qbar] using
      isOpen_preimageEquivFiber_singleton_iff_exists_basicOpen_fiber_eq_singleton p q hq
  -- Proof comment: the third clause is the bridge; the other clauses are the fiber-ring TFAE.
  tfae_have 1 ↔ 2 := howner.out 0 1
  tfae_have 1 ↔ 3 := by
    simpa using hbridge
  tfae_have 1 ↔ 5 := howner.out 0 4
  tfae_have 4 ↔ 5 := howner.out 3 4
  tfae_have 5 ↔ 6 := howner.out 4 5 (h₂ := by
    dsimp [residueFieldFieldCommRing, fiberPrimeResidueFieldAlgebra]
    simp)
  tfae_finish

end
