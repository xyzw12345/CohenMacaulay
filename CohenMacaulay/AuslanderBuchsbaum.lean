import CohenMacaulay.depth

universe u v w

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Classical

---Some conditions are redundant
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (h : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find h + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by sorry
