import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

open IsLocalRing LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma comap_localization_mem_associatePrimes_of_mem_associatePrimes (S : Submonoid R)
    (p : Ideal (Localization S)) [p.IsPrime]
    (ass : p ∈ associatedPrimes (Localization S) (LocalizedModule S M)) :
    p.comap (algebraMap R (Localization S)) ∈ associatedPrimes R M := by

  sorry

lemma mem_associatePrimes_of_mem_associatePrimes_comap_localization (S : Submonoid R)
    (p : Ideal (Localization S)) [p.IsPrime]
    (ass : p.comap (algebraMap R (Localization S)) ∈ associatedPrimes R M) :
    p ∈ associatedPrimes (Localization S) (LocalizedModule S M) := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · --may be able to remove `p.IsPrime`
    trivial
  · use LocalizedModule.mkLinearMap S M x
    ext t
    induction' t using Localization.induction_on with a
    simp only [LocalizedModule.mkLinearMap_apply, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one]
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · use 1
      simp only [← LinearMap.toSpanSingleton_apply, one_smul, ← LinearMap.mem_ker, ← hx,
        Ideal.mem_comap, ← Localization.mk_one_eq_algebraMap]
      have : Localization.mk a.1 1 = Localization.mk a.1 a.2 * Localization.mk a.2.1 (1 : S) := by
        simp only [Localization.mk_mul, mul_one, ← sub_eq_zero, Localization.sub_mk,
          one_mul, sub_zero]
        simp [mul_comm, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ h
    · rcases h with ⟨s, hs⟩
      have : s • a.1 • x = (s.1 * a.1) • x := smul_smul s.1 a.1 x
      rw [this, ← LinearMap.toSpanSingleton_apply, ← LinearMap.mem_ker, ← hx, Ideal.mem_comap,
        ← Localization.mk_one_eq_algebraMap] at hs
      have : Localization.mk a.1 a.2 =
        Localization.mk (s.1 * a.1) 1 * Localization.mk 1 (s * a.2) := by
        simp only [Localization.mk_mul, mul_one, one_mul, ← sub_eq_zero, Localization.sub_mk,
          Submonoid.coe_mul, sub_zero]
        simp [← mul_assoc, mul_comm s.1 a.2.1, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ hs

  /-
  refine ⟨fun h ↦ ?_, fun ⟨h, ass⟩ ↦ ?_⟩
  · constructor
    · rw [← IsLocalization.map_algebraMap_ne_top_iff_disjoint S (Localization S)]
      exact h.isPrime.ne_top
    ·
      sorry
  · rcases ass with ⟨hp, x, hx⟩
    /-
    let f : R ⧸ p →ₗ[R] M := p.liftQ (LinearMap.toSpanSingleton R M x) (le_of_eq hx)
    have inj1 : Function.Injective f :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
    let Sf := LocalizedModule.map S f
    have inj2 : Function.Injective Sf := LocalizedModule.map_injective S f inj1
    let iso'' : (Localization S) ≃ₗ[Localization S] (LocalizedModule S R) := sorry
    let iso' : ((Localization S) ⧸ (Ideal.map (algebraMap R (Localization S)) p)) ≃ₗ[Localization S] (LocalizedModule S R ⧸ Submodule.localized S p) := by

      sorry
    let iso := iso'.trans (localizedQuotientEquiv S p)
    refine ⟨IsLocalization.isPrime_of_isPrime_disjoint S (Localization S) p hp h, ?_⟩
    -/
    refine ⟨IsLocalization.isPrime_of_isPrime_disjoint S (Localization S) p hp h, ?_⟩
    use LocalizedModule.mkLinearMap S M x
    ext r
    simp only [LocalizedModule.mkLinearMap_apply, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply]

    sorry-/

lemma mem_associatePrimes_localizedModule_atPrime_iff {p : Ideal R} [p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
    ↔ p ∈ associatedPrimes R M := by

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
  have := AssociatePrimes.mem_iff.mp (mem_associatePrimes_localizedModule_atPrime_iff.mpr pass)
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
