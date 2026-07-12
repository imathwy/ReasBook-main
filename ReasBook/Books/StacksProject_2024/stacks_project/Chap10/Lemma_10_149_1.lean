import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2

open Algebra
open Algebra.Extension

universe u v

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

-- Proof sketch: choose a polynomial presentation `P ↠ S`, split the conormal sequence
-- `J / J^2 → Ω[P⁄R] ⊗[P] S` using `Ω[S⁄R] = 0`, and let `S' = P / J'` for the complementary
-- summand `J' / J^2`. The resulting square-zero extension is an `Extension R S` whose defining
-- map has square-zero kernel and the stated initial lifting property.
/-- Lemma 10.149.1: if `R → S` is formally unramified, then there exists an `R`-algebra extension
`P → S` with square-zero kernel such that every map `S → A ⧸ I` to a square-zero quotient lifts
uniquely to an `R`-algebra map `P.Ring → A`. -/
theorem exists_universal_squareZeroThickening [Algebra.FormallyUnramified R S] :
    ∃ P : Extension R S, P.IsUniversalFirstOrderThickening := sorry
