import Mathlib.RingTheory.Regular.IsSMulRegular

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma lemma_212_a {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ (⊤ : Submodule R N).annihilator) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ LinearMap.ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Submodule.mem_annihilator.mp mem_ann x trivial, map_zero]
  simpa using reg this

lemma lemma_212_b [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ (⊤ : Submodule R N).annihilator, IsSMulRegular M r := by
  by_contra! h
  have : ((⊤ : Submodule R N).annihilator : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact fun r hr ↦ h r hr
  have : ∃ p ∈ associatedPrimes R M, ((⊤ : Submodule R N).annihilator : Set R) ⊆ (p : Set R) := by

    sorry

  sorry
