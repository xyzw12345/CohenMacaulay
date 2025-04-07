import Mathlib.RingTheory.Regular.RegularSequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open RingTheory.Sequence

--surj regular move

--power regular

--take regular
lemma take_regular {rs : List R} (reg : IsRegular M rs) (k : ℕ) :
    IsRegular M (rs.take k) where
  regular_mod_prev i hi := by
    simp only [List.length_take, lt_inf_iff] at hi
    rw [List.getElem_take, List.take_take, min_eq_left_of_lt hi.1]
    exact reg.regular_mod_prev i hi.2
  top_ne_smul := by
    rw [ne_comm, ← lt_top_iff_ne_top]
    have := lt_top_iff_ne_top.mpr reg.top_ne_smul.symm
    exact gt_of_gt_of_ge (lt_top_iff_ne_top.mpr reg.top_ne_smul.symm)
      (Submodule.smul_mono_left (Ideal.span_mono (fun _ ↦ List.mem_of_mem_take)))
