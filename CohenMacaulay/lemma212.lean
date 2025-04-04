import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

open IsLocalRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma mem_associatePrimes_LocalizedModule_iff {p : Ideal R} [hp : p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
    ↔ p ∈ associatedPrimes R M := by

  sorry

lemma lemma_212_a {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ LinearMap.ext fun x ↦ ?_)
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
  have : (⊤ : Submodule Rₚ Nₚ) ≠
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ) := by
    apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    exact IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator Rₚ Nₚ)
  let Nₚ' := Nₚ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
  let _ : Module p.ResidueField Nₚ' := by

    sorry

  sorry
