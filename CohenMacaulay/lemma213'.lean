import CohenMacaulay.FromPR.HasEnoughProjectives
import CohenMacaulay.FromPR.Ext0

import CohenMacaulay.Dependency.SMulRegular
import CohenMacaulay.Dependency.CategoryLemma

import Mathlib.RingTheory.Regular.RegularSequence

universe u v w

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
variable {R : Type u} [CommRing R] {M N : ModuleCat.{max u v} R} {n : ℕ}
  [UnivLE.{max u v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

lemma ext_hom_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N)
    (reg : IsSMulRegular M r) (n : ℕ) :
    (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M r).f).postcomp N (add_zero n))) = 0 := by

  sorry
