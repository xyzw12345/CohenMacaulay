import Mathlib.Algebra.Module.FinitePresentation

variable {R : Type*} (M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (S : Submonoid R) [Module.FinitePresentation R M]

noncomputable def Module.FinitePresentation.LinearEquiv_map :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (M →ₗ[R] N))
  (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N))

noncomputable def Module.FinitePresentation.LinearEquiv_mapExtendScalars :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (M →ₗ[R] N))
  (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N) (Localization S))
