import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Support

namespace Module

open Order

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

noncomputable def supportDim : WithBot ℕ∞ :=
  krullDim (Module.support R M)

lemma supportDim_eq_ringKrullDim_quotient_ann [Module.Finite R M] :
    supportDim R M = ringKrullDim (R ⧸ (Module.annihilator R M)) := by
  simp only [supportDim]
  rw [Module.support_eq_zeroLocus, ringKrullDim_quotient]

end Module
