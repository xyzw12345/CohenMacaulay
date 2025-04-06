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

lemma lemma222_3_to_4 (I : Ideal R) (n : ℕ) (M : ModuleCat R) [Nontrivial M] [Module.Finite R M]
    (exist_mod : ∃ N : ModuleCat R, Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧
    ∀ i < n, Subsingleton (Ext N M i)) : ∃ rs : List R, rs.length = n ∧
    ∀ r ∈ rs, r ∈ I ∧ RingTheory.Sequence.IsRegular M rs := by
  induction' n with n ih
  · use []
    simp [isRegular_iff]
  · rcases exist_mod with ⟨N, fin, h_supp, h_ext⟩
    have : Subsingleton (N →ₗ[R] M) :=
      let _ := h_ext 0 n.zero_lt_succ
      let _ : Subsingleton (N ⟶ M) :=
        Equiv.subsingleton.symm (homEquiv₀_hom N M).toEquiv
      Equiv.subsingleton.symm (ModuleCat.homAddEquiv (M := N) (N := M)).toEquiv
    rcases lemma_212_b this with ⟨x, mem_ann, hx⟩
    let seq := Ext.covariantSequence N hx.SMul_ShortComplex_exact
    let seq_exact := Ext.covariantSequence_exact N hx.SMul_ShortComplex_exact

    sorry

--lemma lemma222 (use TFAE)
