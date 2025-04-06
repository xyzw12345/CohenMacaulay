import CohenMacaulay.lemma212
import CohenMacaulay.lemma213
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
lemma lemma222_3_to_4 (I : Ideal R) (n : ℕ) : ∀ M : ModuleCat R, Nontrivial M → Module.Finite R M →
    I • (⊤ : Submodule R M) < ⊤ →
    (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧ Module.support R N = PrimeSpectrum.zeroLocus I ∧
    ∀ i < n, Subsingleton (Ext N M i)) → ∃ rs : List R, rs.length = n ∧
    (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs := by
  induction' n with n ih
  · intro M ntr M_fin smul_lt exist_N
    use []
    simp [isRegular_iff]
  · intro M ntr M_fin smul_lt exist_N
    rcases exist_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    have : Subsingleton (N →ₗ[R] M) :=
      let _ := h_ext 0 n.zero_lt_succ
      let _ : Subsingleton (N ⟶ M) :=
        Equiv.subsingleton.symm (homEquiv₀_hom N M).toEquiv
      Equiv.subsingleton.symm (ModuleCat.homAddEquiv (M := N) (N := M)).toEquiv
    rcases lemma_212_b this with ⟨x, mem_ann, hx⟩
    let M' := M ⧸ span {x} • (⊤ : Submodule R M)
    have ntr' : Nontrivial M' := by
      apply Submodule.Quotient.nontrivial_of_lt_top
      rw [Submodule.ideal_span_singleton_smul]
      have := Ideal.le_radical mem_ann
      rw [h_supp', Ideal.mem_radical_iff] at this
      rcases this with ⟨k, hk⟩
      have := IsSMulRegular.pow k hx
      sorry
    have smul_lt : I • (⊤ : Submodule R M') < ⊤ := by
      sorry
    let seq := Ext.covariantSequence N hx.SMul_ShortComplex_exact
    let seq_exact := Ext.covariantSequence_exact N hx.SMul_ShortComplex_exact
    #check CategoryTheory.ComposableArrows.sc

    have exist_N' : (∃ N : ModuleCat R, Nontrivial ↑N ∧ Module.Finite R ↑N ∧
        Module.support R ↑N = PrimeSpectrum.zeroLocus ↑I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R M') i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi

      sorry

    rcases ih (ModuleCat.of R (M ⧸ span {x} • (⊤ : Submodule R M))) ntr'
      (Module.Finite.quotient R _) smul_lt exist_N' with ⟨rs, len, mem, reg⟩
    -- x is only in the radical of I

    sorry

--lemma lemma222 (use TFAE)
