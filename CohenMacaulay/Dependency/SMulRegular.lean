import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Homology.ShortComplex.Exact
variable {R : Type*} [CommRing R] (M : ModuleCat R)

open CategoryTheory

def SMul_ShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (M ⧸ (Ideal.span {r} • (⊤ : Submodule R M)))
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom (((Ideal.span {r} • (⊤ : Submodule R M))).mkQ)
  zero := by
    ext m
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, Submodule.mkQ_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) trivial

lemma IsSMulRegular.SMul_ShortComplex_exact {r : R} (reg : IsSMulRegular M r) :
    (SMul_ShortComplex M r).Exact :=
  sorry
