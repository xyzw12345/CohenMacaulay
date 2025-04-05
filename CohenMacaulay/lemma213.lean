import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.lemma212
import Mathlib

universe u v w

open RingTheory.Sequence Ideal CategoryTheory
set_option pp.universes true
variable {R : Type u} [CommRing R] {M N : ModuleCat.{v} R} {n : ℕ}
  [UnivLE.{max u v, w}]
  --[LocallySmall.{w} (ModuleCat.{max u v} R)]
  {rs : List R} (hr : IsWeaklyRegular M rs) (h : ∀ r : R, r ∈ rs → r ∈ Module.annihilator R N)

local instance : CategoryTheory.HasExt.{max u v + 1} (ModuleCat.{max u v} R) :=
  CategoryTheory.HasExt.standard (ModuleCat.{max u v} R)
  --CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

/- def lemma_213 : (N →ₗ[R] M ⧸ (ofList rs • ⊤ : Submodule R M)) ≃ₗ[R] Ext R _ n M N := by
  sorry -/
