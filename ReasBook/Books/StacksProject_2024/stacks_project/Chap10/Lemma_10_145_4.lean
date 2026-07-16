import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_144_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_145_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps, étale neighborhoods, and residue-field
  control on the resulting fiber factors;
* sampled owner declarations:
  `exists_etale_liesOver_with_residueField_equiv`,
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`,
  `Ideal.primesOver`,
  `Ideal.ResidueField.mapₐ`;
* best owner abstraction:
  the chapter-local decomposition theorem
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`, with the fiber owner
  `Ideal.primesOver` and the canonical residue-field bridge supplied by the lies-over relation;
* layer triage:
  - `source-facing`: the present theorem, which keeps the decomposition from Lemma `10.145.3` and
    adds the purely inseparable residue-field conclusion;
  - `core/canonical`: `Ideal.primesOver` for the distinguished primes and the induced
    `κ(p')`-algebra structure on `κ(rᵢ)`;
  - `bridge/view`: `Ideal.ResidueField.mapₐ`, expressing the residue-field extension attached to a
    prime lying over `p'`;
* primitive data:
  a finite-type `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood `R → R'`, the finite family of finite factors indexed by a canonical
  finite type `ι`, their distinguished primes in `p'.primesOver (A i)`, the finite purely
  inseparable residue-field extensions over `κ(p')`, and the non-quasi-finite remainder over `p'`.
-/

-- Proof sketch: first enlarge the residue field at `p` by a finite separable extension using
-- Lemma `10.144.3` so that every quasi-finite prime in the fiber acquires purely inseparable
-- residue field over the new base point. Then apply the product decomposition of Lemma `10.145.3`
-- to the resulting étale neighborhood; the distinguished primes in the finite factors keep the
-- same residue fields, while the remaining factor is not quasi-finite over the chosen prime.
/-- Lemma 10.145.4: for a finite type ring map `R → S` and a prime `p ⊂ R`, there exists an étale
neighborhood `R → R'` with a prime `p'` over `p` such that `R' ⊗[R] S` decomposes as a finite
product of finite `R'`-algebras `Aᵢ` and a remainder `B`, where each `Aᵢ` comes with its unique
prime `rᵢ` over `p'`, the corresponding residue field extension over `κ(p')` is finite and purely
inseparable, and `R' → B` is not quasi-finite at any prime over `p'`. -/
theorem exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ e : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ hfinite : ∀ i, Module.Finite R' (A i),
      ∃ r : ∀ i, p'.primesOver (A i),
      ∃ hsubsingleton : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∃ hres :
        ∀ i,
          FiniteDimensional p'.ResidueField (r i).1.ResidueField ∧
            IsPurelyInseparable p'.ResidueField (r i).1.ResidueField,
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := sorry

end
