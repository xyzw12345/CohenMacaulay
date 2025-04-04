import Mathlib.RingTheory.Ideal.AssociatedPrime

/-!
# Missing lemmas in Mathlib of Associated Prime
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem AssociatedPrimes.finite_of_noetherian [IsNoetherianRing R] :
    (associatedPrimes R M).Finite := sorry
