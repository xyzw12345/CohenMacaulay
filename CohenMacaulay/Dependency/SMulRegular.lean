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

variable {R : Type*} [CommRing R] (M : ModuleCat R)

open CategoryTheory Pointwise

def SMul_ShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (M ⧸ (r • (⊤ : Submodule R M) : Submodule R M))
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom ((r • (⊤ : Submodule R M)).mkQ)
  zero := by
    ext m
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, Submodule.mkQ_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul m r _ trivial

lemma IsSMulRegular.SMul_ShortComplex_exact {r : R} (reg : IsSMulRegular M r) :
    (SMul_ShortComplex M r).ShortExact where
  exact := by
    simp only [SMul_ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
      ModuleCat.hom_ofHom]
    intro x
    simp [Submodule.mem_smul_pointwise_iff_exists]
  mono_f := by simpa [SMul_ShortComplex, ModuleCat.mono_iff_injective] using reg
  epi_g := by
    simpa [SMul_ShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _
