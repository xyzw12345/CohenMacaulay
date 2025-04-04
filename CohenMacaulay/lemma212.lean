import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

open IsLocalRing LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/- Draft : (7.C) Lemma 7.1. Let $S$ be a multiplicative subset of A, and put

$A^{\prime}=S^{-1} A$, $M^{\prime}=S^{-1} M$. Then

$$
\operatorname{Ass}_A\left(M^{\prime}\right)=f\left(\operatorname{Ass}_{A^{\prime}}\left(M^{\prime}
\right)\right)=\operatorname{Ass}_A(M) \cap\{\mathfrak{p} \mid \mathfrak{p} \cap S=\varnothing\}
$$

where $f$ is the natural map $\operatorname{Spec}\left(A^{\prime}\right) \longrightarrow
\operatorname{Spec}(A)$.

Proof. Left to the reader. One must use the fact that any ideal of $A$ is finitely generated. -/


variable {p : Ideal R} [hp : p.IsPrime]

#check (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p).toFun

#check ((associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M)))

-- lemma s: ((associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M))) ⊆
-- { p_1 : Ideal (Localization.AtPrime p) // p_1.IsPrime } := sorry

-- #check (Set { p_1 // p_1.IsPrime } : Set (Ideal (Localization.AtPrime p)))

-- variable (p_1 : Ideal (Localization.AtPrime p))

-- #check p_1.IsPrime

-- #check (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p).toFun ''
--   ((associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) : Set { p_1 // p_1.IsPrime })

-- lemma mem_associatePrimes_localizedModule_iff1  :
--     (IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p).toFun '' (associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
--     = associatedPrimes R M ∩ {p_1 // (p_1 : Set ) ∩ p = ⊥}
--     := sorry


lemma mem_associatePrimes_localizedModule_iff {p : Ideal R} [hp : p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
    ↔ p ∈ associatedPrimes R M := by
  -- constructor
  -- · intro ⟨nhp, ⟨x, eq⟩⟩
  --   constructor
  --   · exact hp
  --   · unfold toSpanSingleton at *
  --     obtain ⟨⟨a, b⟩, ha⟩ := Quotient.exists_rep x
  --     rw [← ha] at eq
  --     -- have : (x : LocalizedModule p.primeCompl M) , ∃ LocalizedModule.mk = x:= sorry
  --     sorry
  -- · intro ⟨_, ⟨x, eq⟩⟩
  --   constructor
  --   · exact Ideal.IsMaximal.isPrime' (maximalIdeal (Localization.AtPrime p))
  --   · unfold toSpanSingleton at *
  --     -- #check LocalizedModule.mk (p.primeCompl) M
  --     #check LocalizedModule.mk
  --     sorry
  #check IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p

  sorry

lemma lemma_212_a {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this

lemma lemma_212_b [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  by_contra! h
  have : (Module.annihilator R N : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact fun r hr ↦ h r hr
  have : ∃ p ∈ associatedPrimes R M, (Module.annihilator R N : Set R) ⊆ (p : Set R) := by
    sorry
  rcases this with ⟨p, pass, hp⟩
  let _ := pass.isPrime
  let p' : PrimeSpectrum R := ⟨p, pass.isPrime⟩
  have loc_ne_zero : p' ∈ Module.support R N := Module.mem_support_iff_of_finite.mpr hp
  rw [Module.mem_support_iff] at loc_ne_zero
  let Rₚ := Localization.AtPrime p
  let Nₚ := LocalizedModule p'.asIdeal.primeCompl N
  let Mₚ := LocalizedModule p'.asIdeal.primeCompl M
  have : (⊤ : Submodule Rₚ Nₚ) ≠
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ) := by
    apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    exact IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator Rₚ Nₚ)
  let Nₚ' := Nₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
  let Mₚ' := Mₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Mₚ)
  let _ : Module p.ResidueField Nₚ' :=
    Module.instQuotientIdealSubmoduleHSMulTop Nₚ (maximalIdeal (Localization.AtPrime p))
  have := AssociatePrimes.mem_iff.mp (mem_associatePrimes_localizedModule_iff.mpr pass)
  rcases this.2 with ⟨x, hx⟩
  let to_res : Nₚ →ₗ[Rₚ] p.ResidueField := sorry
  --need surjective
  let i : p.ResidueField →ₗ[Rₚ] Mₚ := sorry
  --need injective
  let f := i.comp to_res
  have f_ne0 : f ≠ 0 := sorry
  absurd hom0
  rw [not_subsingleton_iff_nontrivial]
  --need iso
  sorry
