import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_125_1
import stacks_proof.stacks_project.Chap10.Definition_10_135_5
import stacks_proof.stacks_project.Chap10.Definition_10_136_1
import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Lemma_10_6_2
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_39_12
import stacks_proof.stacks_project.Chap10.Lemma_10_135_4
import stacks_proof.stacks_project.Chap10.Lemma_10_135_8
import stacks_proof.stacks_project.Chap10.Lemma_10_136_4
import stacks_proof.stacks_project.Chap10.Lemma_10_136_9
import stacks_proof.stacks_project.Chap10.Lemma_10_136_10
import stacks_proof.stacks_project.Chap10.Lemma_10_136_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 136 15: a directed implication cycle on three propositions
already gives the full `List.TFAE` statement. -/
private theorem tfae_three_of_cycle {A B C : Prop}
    (hAB : A → B) (hBC : B → C) (hCA : C → A) :
    List.TFAE [A, B, C] := by
  -- Proof comment: after unfolding `TFAE`, each pair of clauses is connected by the given
  -- directed cycle, so propositional reasoning closes the finite case split.
  rw [List.TFAE]
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  tauto

/-- The condition that some basic open neighbourhood of `q` is syntomic over `R`. -/
def SyntomicAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ (algebraMap R (Localization.Away g)).Syntomic

/-- The condition that some basic open neighbourhood of `q` is a relative global complete
intersection over `R`. -/
def RelativeGlobalCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsRelativeGlobalCompleteIntersection R (Localization.Away g)

/-- The local fiber ring at `q` is a complete intersection over the residue field of the
contracted prime `q ∩ R`. -/
def FiberCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  @IsCompleteIntersectionOver.{u, max u v, max u v}
    (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) inferInstance inferInstance
    (fiberLocalRingAtResidueFieldAlgebra R S q)

/-- Some basic open neighbourhood of `q` is of finite presentation over `R`, the local map
`R_(q ∩ R) → S_q` is flat, and the local fiber ring at `q` is a complete intersection over
`κ(q ∩ R)`. -/
def FinitePresentationFlatAndFiberCompleteIntersectionAtPrime (R : Type u) [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧
    FinitePresentation R (Localization.Away g) ∧
    (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat ∧
    FiberCompleteIntersectionAtPrime R q

/-- Helper for Chap10 Lemma 10 136 15: a prime avoiding an away parameter lifts to the away
localization. -/
private theorem exists_primeSpectrum_away_comap_eq_of_notMem
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal) :
    ∃ qg : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q := by
  -- Proof comment: the image of `Spec(S_g)` is the basic open `D(g)`, and `q` lies in that open
  -- exactly because `g` avoids the chosen prime.
  have hq_range :
      q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    simpa [PrimeSpectrum.mem_basicOpen] using hg
  exact Set.mem_range.mp hq_range

/-- Helper for Chap10 Lemma 10 136 15: localizing `S` at `q` agrees with localizing the away
chart `S_g` at any prime `qg` lying over `q`. -/
private noncomputable def localizationAwayAtPrimeAlgEquiv
    (q : PrimeSpectrum S) {g : S} (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q) :
    Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qg.asIdeal :=
  let eDomain : Localization.AtPrime q.asIdeal ≃ₐ[S]
      Localization.AtPrime (Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal) :=
    Localization.localAlgEquiv
      q.asIdeal
      (Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal)
      (AlgEquiv.refl (R := S) (A := S))
      (by simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg.symm)
  let eDouble :
      Localization.AtPrime (Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal) ≃ₐ[S]
        Localization.AtPrime qg.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g)
      qg.asIdeal
  -- Proof comment: first rewrite the contracted prime to the displayed away-chart prime, then use
  -- the standard iterated-localization equivalence for `S → S_g → (S_g)_(qg)`.
  (eDomain.trans eDouble).restrictScalars R

/-- Helper for Chap10 Lemma 10 136 15: the stalk comparison for `S_q ≃ (S_g)_{qg}` is compatible
with the localized base maps from `R_(q ∩ R)`. -/
private noncomputable def localizationAwayAtPrimeAlgEquivOverBasePrime
    (q : PrimeSpectrum S) {g : S} (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    Localization.AtPrime q.asIdeal ≃ₐ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime qg.asIdeal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hpqg :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) qg = p := by
    -- Proof comment: contracting `qg` along `R → S → S_g` is the same as first contracting to
    -- `q` and then to `R`.
    ext r
    simp [p, hqg]
  let hbase :
      p.asIdeal = Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpqg
  let eR :
      Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qg.asIdeal :=
    localizationAwayAtPrimeAlgEquiv (R := R) (S := S) q qg hqg
  let fq : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl
  let fqg : Localization.AtPrime p.asIdeal →+* Localization.AtPrime qg.asIdeal :=
    Localization.localRingHom p.asIdeal qg.asIdeal (algebraMap R (Localization.Away g)) hbase
  have hcomp : eR.toRingHom.comp fq = fqg := by
    -- Proof comment: both maps out of `R_(q ∩ R)` are the canonical local maps into the same
    -- target stalk, so uniqueness reduces the comparison to elements of `R`.
    apply Localization.localRingHom_unique
    intro r
    calc
      eR (algebraMap R (Localization.AtPrime q.asIdeal) r) =
          algebraMap R (Localization.AtPrime qg.asIdeal) r := eR.commutes r
      _ = fqg (algebraMap R (Localization.AtPrime p.asIdeal) r) := by
          rw [Localization.localRingHom_to_map]
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := fq.toAlgebra
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime qg.asIdeal) :=
    fqg.toAlgebra
  refine
    { __ := eR.toRingEquiv
      commutes' := ?_ }
  intro x
  -- Proof comment: compatibility of the `R_(q ∩ R)`-algebra structures is exactly the map
  -- equality proved above.
  exact congrArg (fun f : Localization.AtPrime p.asIdeal →+* Localization.AtPrime qg.asIdeal ↦ f x)
    hcomp

/-- Helper for Chap10 Lemma 10 136 15: localizing corresponding primes along an `R`-algebra
equivalence gives the induced `R`-algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- Proof comment: `Localization.localAlgEquiv` is the owner-level API for transporting a local
  -- ring across an algebra equivalence once the prime is rewritten as the contracted prime.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Chap10 Lemma 10 136 15: the fiber prime of `q` contracts to `q` along the
canonical inclusion of the fiber ring. -/
private theorem fiberPrimeAt_includeRight_comap
    (q : PrimeSpectrum S) :
    PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight :
          S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom)
        (fiberPrimeAt R S q) =
      q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hinv :
      ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) = q := by
    -- Proof comment: `fiberPrimeAt` is defined as the forward image of `q` under the fiber-prime
    -- equivalence, so the inverse equivalence returns the original ambient prime.
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
  calc
    PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight :
          S →ₐ[R] (p.asIdeal.Fiber S)).toRingHom)
        (fiberPrimeAt R S q) =
        ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) := by
          change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
              (fiberPrimeAt R S q) =
            ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q))
          rfl
    _ = q := hinv

/-- Helper for Chap10 Lemma 10 136 15: a finitely presented algebra admits a surjective
polynomial presentation. -/
private theorem finitePresentation_surjectivePolynomialPresentation
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] A, Function.Surjective π := by
  -- Proof comment: the owner API for finite presentation already returns a surjective polynomial
  -- chart, so only the chart itself should be kept here; the source codimension will be chosen
  -- later from the fiber-local complete-intersection data at the prime.
  obtain ⟨n, π, hπsurj, _hπkerfg⟩ :=
    (Algebra.FinitePresentation.out :
      ∃ (n : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective π ∧ (RingHom.ker π.toRingHom).FG)
  exact ⟨n, π, hπsurj⟩

/-- Helper for Chap10 Lemma 10 136 15: local flatness at `q` transports to the stalk of an away
chart prime `qA` lying over `q`. -/
private theorem exists_flat_localRingHom_localizationAway_comap
    (q : PrimeSpectrum S) {g : S} (qA : PrimeSpectrum (Localization.Away g))
    (hqA : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qA = q)
    (hflat : (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    ∃ hbase : p.asIdeal = Ideal.comap (algebraMap R (Localization.Away g)) qA.asIdeal,
      (Localization.localRingHom p.asIdeal qA.asIdeal (algebraMap R (Localization.Away g))
        hbase).Flat := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hpqA :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) qA = p := by
    -- Proof comment: contracting `qA` along `R → S → S_g` agrees with first contracting to `q`.
    ext r
    simp [p, hqA]
  have hbase : p.asIdeal = Ideal.comap (algebraMap R (Localization.Away g)) qA.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpqA
  let eStalk :
      Localization.AtPrime q.asIdeal ≃ₐ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime qA.asIdeal :=
    localizationAwayAtPrimeAlgEquivOverBasePrime (R := R) (S := S) q qA hqA
  let fq : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl
  let fqA : Localization.AtPrime p.asIdeal →+* Localization.AtPrime qA.asIdeal :=
    Localization.localRingHom p.asIdeal qA.asIdeal (algebraMap R (Localization.Away g)) hbase
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := fq.toAlgebra
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime qA.asIdeal) :=
    fqA.toAlgebra
  have hflatTargetModule :
      Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime qA.asIdeal) := by
    have hflatSourceModule :
        Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := by
      -- Proof comment: rewrite the source local map as the ambient algebra map and forget to the
      -- corresponding flat module structure.
      simpa [RingHom.algebraMap_toAlgebra] using
        (RingHom.flat_algebraMap_iff.mp
          (show (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal)).Flat by
            simpa [p, RingHom.algebraMap_toAlgebra] using hflat))
    letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      hflatSourceModule
    -- Proof comment: transport flatness across the canonical stalk equivalence
    -- `S_q ≃ (S_g)_(qA)`.
    exact Module.Flat.of_linearEquiv eStalk.symm.toLinearEquiv
  refine ⟨hbase, ?_⟩
  -- Proof comment: the target local map is again just the algebra map into the away-chart stalk.
  simpa [p, RingHom.algebraMap_toAlgebra] using
    (RingHom.flat_algebraMap_iff.mpr hflatTargetModule)

/-- Helper for Chap10 Lemma 10 136 15: after fixing the away chart `S_g₀` and one surjective
polynomial presentation of it, the remaining source-faithful step is to trim that presentation at
the lifted prime and produce a relative global complete-intersection neighbourhood on the away
chart. -/
private theorem existsAwayChartRgciNeighborhood_of_finitePresentationFlatAndFiberCompleteIntersectionPresentation
    (q : PrimeSpectrum S) {g0 : S} (hg0 : g0 ∉ q.asIdeal)
    (hfp : FinitePresentation R (Localization.Away g0))
    (hflat : (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiber : FiberCompleteIntersectionAtPrime R q)
    (qA : PrimeSpectrum (Localization.Away g0))
    (hqA : PrimeSpectrum.comap (algebraMap S (Localization.Away g0)) qA = q)
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g0)
    (hπsurj : Function.Surjective π) :
    ∃ u : Localization.Away g0,
      u ∉ qA.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away u) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  obtain ⟨hbase, hflatA⟩ :=
    exists_flat_localRingHom_localizationAway_comap
      (R := R) (S := S) q qA hqA hflat
  let a : p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g0
  have haqf : a ∉ (fiberPrimeAt R S q).asIdeal := by
    -- Proof comment: the fiber prime over `q` still avoids the away parameter `g₀`.
    simpa [a, PrimeSpectrum.comap_asIdeal,
      fiberPrimeAt_includeRight_comap (R := R) (S := S) q] using hg0
  -- Route correction: the previous proof tried to force `relativeDimensionAt = n - c` on an
  -- arbitrary quotient chart whose relation count `c` came from global kernel generators. The
  -- source proof instead trims the fixed surjective chart `π` at the lifted prime `qA`.
  -- Proof comment: the verified prefix now fixes the contracted base prime `p`, the transported
  -- local flatness on `(S_g₀)_(qA)`, and the fiber-side away parameter `a`; the remaining work is
  -- exactly the trimmed-presentation and Nakayama shrinking package from the source proof.
  -- TODO: first apply `localizationAtPrime_algEquiv_of_algEquiv` to
  -- `RingHom.fiber_localizationAway_algEquiv (R := R) (S := S) p g0` to identify the away-chart
  -- fiber local ring with the corresponding localization of `Localization.Away a`; then transport
  -- `hfiber` from `q` to `qA`, base-change `π` to the residue field of `q ∩ R`, extract the
  -- trimmed local relation family from `00SG/00SC`, prove the trimmed chart has the expected
  -- `relativeDimensionAt`, apply `00ST` on that trimmed chart, and finally use `hflatA` plus
  -- Nakayama to shrink away the comparison kernel back on `Localization.Away g0`.
  sorry

/-- Helper for Chap10 Lemma 10 136 15: a comap equality turns target-prime membership into the
corresponding source-prime membership test. -/
private theorem map_mem_asIdeal_iff_of_comap_eq
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hcomap : PrimeSpectrum.comap f q = p) (x : A) :
    f x ∈ q.asIdeal ↔ x ∈ p.asIdeal := by
  have hcomapIdeal : Ideal.comap f q.asIdeal = p.asIdeal := by
    -- Proof comment: rewrite the prime-spectrum comap equality at the ideal layer once.
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap
  -- Proof comment: membership in the contracted ideal is definitionally target membership.
  change x ∈ Ideal.comap f q.asIdeal ↔ x ∈ p.asIdeal
  simpa [hcomapIdeal]

/-- Helper for Chap10 Lemma 10 136 15: an RGCI neighborhood transports across an algebra
equivalence after rewriting the source prime in comap form. -/
private theorem existsLocalizedRgciNeighborhood_of_algEquivSourceNeighborhood
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (qA : PrimeSpectrum A) (qB : PrimeSpectrum B)
    (hqA : qA = PrimeSpectrum.comap e.toRingHom qB)
    (h :
      ∃ u : A,
        u ∉ qA.asIdeal ∧
          Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away u)) :
    ∃ v : B,
      v ∉ qB.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away v) := by
  -- Proof comment: rewrite the source prime to the comap spelling, push the chosen denominator
  -- through `e`, and transport the localized RGCI chart across the induced away equivalence.
  subst qA
  rcases h with ⟨u, huqA, huRGCI⟩
  let eAway : Localization.Away u ≃ₐ[R] Localization.Away (e u) :=
    IsLocalization.algEquivOfAlgEquiv
      (A := R)
      (S := Localization.Away u)
      (Q := Localization.Away (e u))
      e
      (Submonoid.map_powers e u)
  refine ⟨e u, ?_, ?_⟩
  · -- Proof comment: nonmembership is preserved because `qA` is exactly the comap of `qB`.
    intro heuq
    exact huqA (by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using heuq)
  · -- Proof comment: RGCI is intrinsic to the localized chart, so the away equivalence carries
    -- the property to the pushed-forward denominator.
    exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv huRGCI eAway

/-- Helper for Chap10 Lemma 10 136 15: an iterated away localization of a principal open is a
single principal open of the original ring after clearing one denominator. -/
private theorem singleOriginalAwayAlgEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    (g : A) (u : Localization.Away g) :
    let h : A := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[R] Localization.Away h) := by
  let a : A := (IsLocalization.Away.sec g u).1
  let h : A := g * a
  let hassoc :
      Associated (algebraMap A (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap A (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[R] Localization.Away (algebraMap A (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap A (Localization.Away g) a))).restrictScalars R
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap A (Localization.Away g) a)) := by
    -- Proof comment: once the cleared denominator is definitionally `g * a`, the common middle
    -- ring is also an away localization at that single original element.
    simpa [h] using
      (inferInstance :
        IsLocalization.Away h (Localization.Away (algebraMap A (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap A (Localization.Away g) a) ≃ₐ[R] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap A (Localization.Away g) a))).symm.restrictScalars R
  -- Proof comment: compare the iterated localization and the single cleared denominator through
  -- the common away localization at the lifted numerator.
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 136 15: clearing the denominator of an iterated away localization
keeps the resulting original-ring element outside the starting prime. -/
private theorem notMem_original_away_of_iterated_away
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) {g : A} (hg : g ∉ q.asIdeal)
    (qAway : PrimeSpectrum (Localization.Away g))
    (hqAway : PrimeSpectrum.comap (algebraMap A (Localization.Away g)) qAway = q)
    {u : Localization.Away g} (hu : u ∉ qAway.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  have hsec_not_mem_away :
      algebraMap A (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qAway.asIdeal := by
    -- Proof comment: if the numerator landed in the lifted prime, associatedness would force the
    -- localized element `u` into that prime as well.
    intro hsec_mem
    have hu_mem : u ∈ qAway.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    -- Proof comment: contract the previous nonmembership statement back along `A → A_g`.
    intro hsec_mem
    have hmap_mem :
        algebraMap A (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈ qAway.asIdeal := by
      exact
        (map_mem_asIdeal_iff_of_comap_eq
          (algebraMap A (Localization.Away g)) hqAway (IsLocalization.Away.sec g u).1).mpr
          hsec_mem
    exact hsec_not_mem_away hmap_mem
  -- Proof comment: both factors avoid the original prime, so their product does as well.
  exact q.2.mul_notMem hg hsec_not_mem

/-- Helper for Chap10 Lemma 10 136 15: a relative global complete-intersection neighborhood is
automatically syntomic on the same basic open. -/
private theorem syntomicAtPrime_of_relativeGlobalCompleteIntersectionAtPrime
    (q : PrimeSpectrum S) :
    RelativeGlobalCompleteIntersectionAtPrime R q → SyntomicAtPrime R q := by
  rintro ⟨g, hgq, hgci⟩
  -- Proof comment: reuse the same principal neighborhood and apply syntomicity of relative
  -- global complete intersections.
  exact ⟨g, hgq, Algebra.IsRelativeGlobalCompleteIntersection.syntomic hgci⟩

/-- Helper for Chap10 Lemma 10 136 15: a syntomic basic-open neighborhood should supply the
finite-presentation, local-flatness, and fiber complete-intersection package at `q`. -/
private theorem finitePresentationFlatAndFiberCompleteIntersectionAtPrime_of_syntomicAtPrime
    (q : PrimeSpectrum S) :
    SyntomicAtPrime R q → FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q := by
  intro hsyntomic
  rcases hsyntomic with ⟨g, hgq, hsg⟩
  obtain ⟨qg, hqg⟩ :=
    exists_primeSpectrum_away_comap_eq_of_notMem (R := R) (S := S) q hgq
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hpqg :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) qg = p := by
    -- Proof comment: the lifted away prime contracts to the same base prime as `q`.
    ext r
    simp [p, hqg]
  have hbase :
      p.asIdeal = Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpqg
  have hfinite : FinitePresentation R (Localization.Away g) :=
    RingHom.finitePresentation_algebraMap.mp hsg.finitePresentation
  have hflatAway :
      (Localization.localRingHom p.asIdeal qg.asIdeal (algebraMap R (Localization.Away g))
        hbase).Flat :=
    RingHom.Flat.localRingHom hsg.flat qg.asIdeal p.asIdeal hbase
  let eStalk :
      Localization.AtPrime q.asIdeal ≃ₐ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime qg.asIdeal :=
    localizationAwayAtPrimeAlgEquivOverBasePrime (R := R) (S := S) q qg hqg
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).toAlgebra
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime qg.asIdeal) :=
    (Localization.localRingHom p.asIdeal qg.asIdeal (algebraMap R (Localization.Away g))
      hbase).toAlgebra
  have hflatTargetModule :
      Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := by
    have hflatAwayModule :
        Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime qg.asIdeal) := by
      -- Proof comment: view the local map into the away-chart stalk as the algebra map from
      -- `R_(q ∩ R)` and then forget the ring-hom wrapper to its module-flat content.
      simpa [RingHom.algebraMap_toAlgebra] using
        (RingHom.flat_algebraMap_iff.mp
          (show (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime qg.asIdeal)).Flat by
            simpa [RingHom.algebraMap_toAlgebra] using hflatAway))
    letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime qg.asIdeal) :=
      hflatAwayModule
    -- Proof comment: transport flatness back along the canonical stalk equivalence.
    exact Module.Flat.of_linearEquiv eStalk.toLinearEquiv
  have hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat := by
    -- Proof comment: the target local map is the algebra map for the stalk `S_q`, so the module
    -- flatness just proved is exactly the desired ring-hom flatness.
    simpa [p, RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hflatTargetModule)
  -- Proof comment: the finite-presentation and local-flatness clauses are now in place on the
  -- original prime `q`; only the fiber complete-intersection transport remains.
  refine ⟨g, hgq, hfinite, hflat, ?_⟩
  have hFibers :
      (algebraMap R (Localization.Away g)).HasLocalCompleteIntersectionFibers :=
    hsg.hasLocalCompleteIntersectionFibers
  rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at hFibers
  have hlocalFiberAway :
      IsLocalCompleteIntersection p.asIdeal.ResidueField
        (p.asIdeal.Fiber (Localization.Away g)) := by
    -- Proof comment: specialize the syntomic fiber condition at the contracted base prime.
    simpa [p] using hFibers p
  let a : p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g
  have hlocalAwayFiber :
      IsLocalCompleteIntersection p.asIdeal.ResidueField (Localization.Away a) := by
    -- Proof comment: rewrite the away-chart fiber as the corresponding localization of the
    -- original fiber ring once, then keep the proof on that single chart.
    simpa [a] using
      fiber_localizationAway_isLocalCompleteIntersection_of_syntomic
        (R := R) (S := S) p g hlocalFiberAway
  let qf : PrimeSpectrum (p.asIdeal.Fiber S) := fiberPrimeAt R S q
  have haqf : a ∉ qf.asIdeal := by
    -- Proof comment: the fiber prime contracts to `q`, so the away parameter still avoids the
    -- chosen prime after passing to the fiber.
    simpa [a, PrimeSpectrum.comap_asIdeal,
      fiberPrimeAt_includeRight_comap (R := R) (S := S) q] using hgq
  obtain ⟨qfAway, hqfAway⟩ :=
    exists_primeSpectrum_away_comap_eq_of_notMem
      (R := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) qf haqf
  let eFiberLocal :
      Localization.AtPrime qf.asIdeal ≃ₐ[p.asIdeal.ResidueField]
        Localization.AtPrime qfAway.asIdeal :=
    localizationAwayAtPrimeAlgEquiv
      (R := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) qf qfAway hqfAway
  letI : Algebra.EssFiniteType p.asIdeal.ResidueField
      (Localization.AtPrime qfAway.asIdeal) := by
    -- Proof comment: the local ring on the fiber chart is a localization of a local complete
    -- intersection algebra, hence essentially of finite type over the residue field.
    exact Algebra.EssFiniteType.of_isLocalization
      (Localization.AtPrime qfAway.asIdeal) qfAway.asIdeal.primeCompl
  letI : Algebra.EssFiniteType p.asIdeal.ResidueField
      (Localization.AtPrime qf.asIdeal) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eFiberLocal).mpr inferInstance
  have hfiberLocalTFAE :=
    isCompleteIntersectionOver_tfae
      (k := p.asIdeal.ResidueField)
      (S := Localization.AtPrime qf.asIdeal)
  have hfiberModel :
      ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra p.asIdeal.ResidueField A)
          (a' : PrimeSpectrum A)
          (e : Localization.AtPrime qf.asIdeal ≃ₐ[p.asIdeal.ResidueField]
            Localization.AtPrime a'.asIdeal),
          IsLocalCompleteIntersection p.asIdeal.ResidueField A :=
    ⟨Localization.Away a, inferInstance, inferInstance, qfAway, eFiberLocal, hlocalAwayFiber⟩
  -- Proof comment: the local-ring TFAE converts the local-CI fiber chart into the complete-
  -- intersection owner predicate on the original fiber local ring at `q`.
  simpa [FiberCompleteIntersectionAtPrime, fiberLocalRingAt, qf] using
    (hfiberLocalTFAE.out 4 0 rfl rfl).mp hfiberModel

/-- Helper for Chap10 Lemma 10 136 15: the finite-presentation, local-flatness, and fiber
complete-intersection package should shrink to a relative global complete-intersection
neighborhood. -/
private theorem relativeGlobalCompleteIntersectionAtPrime_of_finitePresentationFlatAndFiberCompleteIntersectionAtPrime
    (q : PrimeSpectrum S) :
    FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q →
      RelativeGlobalCompleteIntersectionAtPrime R q := by
  intro hfiniteFlatFiber
  rcases hfiniteFlatFiber with ⟨g0, hg0, hfp, hflat, hfiber⟩
  obtain ⟨qA, hqA⟩ :=
    exists_primeSpectrum_away_comap_eq_of_notMem (R := R) (S := S) q hg0
  letI : Algebra.FinitePresentation R (Localization.Away g0) := hfp
  have hrgciAwayChart :
      ∃ u : Localization.Away g0,
        u ∉ qA.asIdeal ∧
          Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away u) := by
    -- Proof comment: once the fixed away chart is replaced by the trimmed presentation at `qA`,
    -- the source proof yields an RGCI principal neighbourhood directly on `Localization.Away g0`.
    obtain ⟨n, π, hπsurj⟩ :=
      finitePresentation_surjectivePolynomialPresentation (R := R) (A := Localization.Away g0)
    exact
      existsAwayChartRgciNeighborhood_of_finitePresentationFlatAndFiberCompleteIntersectionPresentation
        (R := R) (S := S) q hg0 hfp hflat hfiber qA hqA π hπsurj
  rcases hrgciAwayChart with ⟨u, huqA, huRGCI⟩
  obtain ⟨eSingle⟩ := singleOriginalAwayAlgEquiv (R := R) (g := g0) u
  let g : S := g0 * (IsLocalization.Away.sec g0 u).1
  have hgq :
      g ∉ q.asIdeal := by
    -- Proof comment: clearing the iterated-away denominator preserves nonmembership in the
    -- original prime.
    simpa [g] using
      notMem_original_away_of_iterated_away q hg0 qA hqA huqA
  have hgci :
      Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
    -- Proof comment: the iterated-away chart `((S_g0)_u)` is equivalent to the single away chart
    -- `S_g`, so the RGCI property transports across that equivalence.
    exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv huRGCI eSingle
  exact ⟨g, hgq, hgci⟩

/-- Chap10 Lemma 10 136 15: for a prime `q` of `S` with contracted prime `q ∩ R`, the following
are equivalent: some basic open neighbourhood of `q` is syntomic over `R`; some basic open
neighbourhood of `q` is a relative global complete intersection over `R`; and some basic open
neighbourhood of `q` is of finite presentation over `R`, the local map `R_(q ∩ R) → S_q` is
flat, and the local fiber ring at `q` is a complete intersection over `κ(q ∩ R)`. -/
@[stacks 00SY]
theorem syntomicAtPrime_tfae
    (q : PrimeSpectrum S) :
    List.TFAE
      [ SyntomicAtPrime R q
      , RelativeGlobalCompleteIntersectionAtPrime R q
      , FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q
      ] := by
  -- Proof comment: the theorem is organized as the standard three-arrow cycle
  -- `(2) → (1) → (3) → (2)`, so the propositional `TFAE` assembly is separated from the
  -- algebraic neighborhood constructions.
  exact tfae_three_of_cycle
    (syntomicAtPrime_of_relativeGlobalCompleteIntersectionAtPrime (R := R) (S := S) q)
    (finitePresentationFlatAndFiberCompleteIntersectionAtPrime_of_syntomicAtPrime
      (R := R) (S := S) q)
    (relativeGlobalCompleteIntersectionAtPrime_of_finitePresentationFlatAndFiberCompleteIntersectionAtPrime
      (R := R) (S := S) q)

end

end Algebra
