import CohenMacaulay.lemma212
import CohenMacaulay.lemma213
--import CohenMacaulay.FromPR.HasEnoughProjectives
--import CohenMacaulay.FromPR.Ext0 --replace these two with above later
--import CohenMacaulay.Dependency.CategoryLemma
import CohenMacaulay.Dependency.SMulRegular

universe u v w

open IsLocalRing LinearMap
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
   [UnivLE.{max u v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{max u v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{max u v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{max u v} R)

set_option linter.unusedTactic false

open Pointwise

lemma lemma222_3_to_4 (I : Ideal R) (n : ℕ) : ∀ M : ModuleCat R, Nontrivial M → Module.Finite R M →
    I • (⊤ : Submodule R M) < ⊤ → (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) →
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs := by
  induction' n with n ih
  · intro M ntr M_fin smul_lt exist_N
    use []
    simp [isRegular_iff]
  · intro M ntrM M_fin smul_lt exist_N
    rcases exist_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    have : Subsingleton (N →ₗ[R] M) :=
      let _ := h_ext 0 n.zero_lt_succ
      let _ : Subsingleton (N ⟶ M) :=
        Equiv.subsingleton.symm (homEquiv₀_hom N M).toEquiv
      Equiv.subsingleton.symm (ModuleCat.homAddEquiv (M := N) (N := M)).toEquiv
    rcases lemma_212_b this with ⟨x, mem_ann, hx⟩
    have := Ideal.le_radical mem_ann
    rw [h_supp', Ideal.mem_radical_iff] at this
    rcases this with ⟨k, hk⟩
    have hxk := IsSMulRegular.pow k hx
    let M' := QuotSMulTop (x ^ k) M
    have le_smul : x ^ k • (⊤ : Submodule R M) ≤ I • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk))
    have ntr' : Nontrivial M' := by
      apply Submodule.Quotient.nontrivial_of_lt_top
      exact gt_of_gt_of_ge smul_lt le_smul
    have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
      rcases Set.not_top_subset.mp (not_subset_of_ssubset smul_lt) with ⟨m, hm⟩
      have : Submodule.mkQ ((x ^ k) • ⊤) m ∉ I • (⊤ : Submodule R M') := by
        have : (⊤ : Submodule R M') = Submodule.map (Submodule.mkQ ((x ^ k) • ⊤)) ⊤ := by simp
        rw [this, ← Submodule.map_smul'', ← Submodule.mem_comap, Submodule.comap_map_eq]
        simpa [le_smul] using hm
      rw [lt_top_iff_ne_top]
      by_contra h
      absurd this
      simp [h]
    have exist_N' : (∃ N : ModuleCat R, Nontrivial ↑N ∧ Module.Finite R ↑N ∧
        Module.support R ↑N = PrimeSpectrum.zeroLocus ↑I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R M') i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      have := subsingleton_of_subsingleton_subsingleton
        ((Ext.covariant_sequence_exact₃' N hxk.SMul_ShortComplex_exact) i (i + 1) rfl)
      exact this (h_ext i (Nat.lt_add_right 1 hi)) (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
    rcases ih (ModuleCat.of R M') ntr'
      (Module.Finite.quotient R _) smul_lt' exist_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simp only [List.length_cons, len, Nat.add_left_inj, List.mem_cons, forall_eq_or_imp, hk,
      true_and, isRegular_cons_iff]
    exact ⟨mem, hxk, reg⟩

lemma lemma222 (I : Ideal R) (n : ℕ) (M : ModuleCat R) (Mntr : Nontrivial M)
    (Mfin : Module.Finite R M) (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
  [∀ N : ModuleCat R, (Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N ⊆ PrimeSpectrum.zeroLocus I) → ∀ i < n, Subsingleton (Ext N M i),
   ∀ i < n, Subsingleton (Ext (ModuleCat.of R (ULift (R⧸I))) M i),
   ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
    ].TFAE := by
  have ntrQ : Nontrivial (R⧸I) := by
    apply Submodule.Quotient.nontrivial_of_lt_top _ (lt_top_iff_ne_top.mpr _)
    by_contra eq
    absurd smul_lt
    simp [eq]
  have suppQ : Module.support R (R⧸I) = PrimeSpectrum.zeroLocus I := by
    have : I = (I • (⊤ : Ideal R)) := by simp only [smul_eq_mul, mul_top]
    rw [this, Module.support_quotient]
    have : Module.annihilator R R = ⊥ := by
      rw [Module.annihilator_eq_bot]
      exact (faithfulSMul_iff_algebraMap_injective R R).mpr fun ⦃a₁ a₂⦄ a ↦ a
    simp [Module.support_eq_zeroLocus, this]
  tfae_have 1 → 2 := by
    intro h1 i hi
    apply h1 (ModuleCat.of R (ULift (R⧸I))) _ i hi
    simp only [ULift.nontrivial, Module.Finite.ulift, true_and]
    rw [LinearEquiv.support_eq ULift.moduleEquiv, suppQ]
  tfae_have 2 → 3 := by
    intro h2
    use (ModuleCat.of R (ULift.{v} (R⧸I)))
    simp only [ULift.nontrivial, Module.Finite.ulift, true_and]
    refine ⟨?_, h2⟩
    rw [LinearEquiv.support_eq ULift.moduleEquiv, suppQ]
  tfae_have 3 → 4 := lemma222_3_to_4 I n M Mntr Mfin smul_lt
  tfae_have 4 → 1 := by
    intro ⟨rs, len, mem, reg⟩ N ⟨Nntr, Nfin, Nsupp⟩ i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    have : ∀ r ∈ rs, ∃ k, r ^ k ∈ Module.annihilator R N :=
      fun r hr ↦ le_rad (mem r hr)
    choose pow hpow using this
    let rs' : List R := List.ofFn (fun i ↦ (rs.get i) ^ (pow _ (rs.get_mem i)))
    have mem' : ∀ x ∈ rs', x ∈ Module.annihilator R N := by
      intro x hx
      rcases List.mem_iff_get.mp hx with ⟨t, ht⟩
      simp only [← ht, List.get_eq_getElem, List.getElem_ofFn, rs']
      apply hpow
    have mem'' : ∀ x ∈ (rs'.take i), x ∈ Module.annihilator R N := by
      intro x hx
      exact mem' x (List.mem_of_mem_take hx)
    have reg' : IsRegular M rs' := by

      sorry
    have reg'' : IsRegular M (rs'.take i) := by

      sorry
    let e := lemma_213 reg''.toIsWeaklyRegular mem''
    have : (List.take i rs').length = i := by
      simpa [rs', len] using Nat.le_of_succ_le hi
    rw [this] at e
    have : Subsingleton (N →ₗ[R] M ⧸ ofList (List.take i rs') • (⊤ : Submodule R M)) := by
      have : i < rs'.length := by simpa [rs', len] using hi
      exact lemma_212_a (reg'.regular_mod_prev i this) (mem' _ (List.getElem_mem this))
    exact e.symm.subsingleton
  tfae_finish
