import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Submodule.Pointwise

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Ideal Pointwise

def SMul_ShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (M ⧸ (span {r} • (⊤ : Submodule R M) : Submodule R M))
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom ((span {r} • (⊤ : Submodule R M)).mkQ)
  zero := by
    ext m
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, Submodule.mkQ_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.smul_mem_smul (mem_span_singleton_self r) trivial

variable {M} in
lemma IsSMulRegular.SMul_ShortComplex_exact {r : R} (reg : IsSMulRegular M r) :
    (SMul_ShortComplex M r).ShortExact where
  exact := by
    simp only [SMul_ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
      ModuleCat.hom_ofHom]
    intro x
    simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.ideal_span_singleton_smul r ⊤,
      Submodule.mem_smul_pointwise_iff_exists]
  mono_f := by simpa [SMul_ShortComplex, ModuleCat.mono_iff_injective] using reg
  epi_g := by
    simpa [SMul_ShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _
