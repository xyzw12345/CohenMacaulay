import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.lemma212
import Mathlib

universe u v w

open RingTheory.Sequence Ideal CategoryTheory
set_option pp.universes true
variable {R : Type u} [CommRing R] {M N : ModuleCat.{v} R} {n : ℕ}
  [LocallySmall.{w} (ModuleCat.{max u v} R)]
  {rs : List R} (hr : IsWeaklyRegular M rs) (h : ∀ r : R, r ∈ rs → r ∈ Module.annihilator R N)

instance : EnoughProjectives (ModuleCat.{max u v} R) := inferInstance

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

/- def lemma_213 : (N →ₗ[R] M ⧸ (ofList rs • ⊤ : Submodule R M)) ≃ₗ[R] Ext R _ n M N := by
  sorry -/
