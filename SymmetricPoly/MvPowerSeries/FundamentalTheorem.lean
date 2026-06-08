import SymmetricPoly.MvPowerSeries.SymmetricFun
import Mathlib.Algebra.MvPolynomial.Basic

namespace MvPowerSeries
variable (σ R) [CommSemiring R]
/-- The `R`-algebra homomorphism from $R[x_1,\dots,x_n]$ to the symmetric subalgebra of
  $R[\{x_i \mid i ∈ σ\}]$ sending $x_i$ to the $i$-th elementary symmetric polynomial. -/
noncomputable def esymmAlgHom :
    MvPolynomial ℕ R →ₐ[R] symmetricFunctions σ R :=
  MvPolynomial.aeval (fun i ↦ ⟨esymm σ R (i + 1), esymm_mem_symmetricFunctions⟩)

lemma esymmAlgHom_surjective : Function.Surjective (esymmAlgHom σ R) := by sorry

lemma esymmAlgHom_injective [Infinite σ] : Function.Injective (esymmAlgHom σ R) := by sorry

noncomputable def esymmAlgEquiv [Infinite σ] :
    MvPolynomial ℕ R ≃ₐ[R] symmetricFunctions σ R :=
  AlgEquiv.ofBijective (esymmAlgHom σ R)
    ⟨esymmAlgHom_injective σ R, esymmAlgHom_surjective σ R⟩

noncomputable def msymmHom : (Partition →₀ R) →ₗ[R] symmetricFunctions σ R :=
  Finsupp.linearCombination R (fun μ ↦ ⟨msymm σ R μ, msymm_mem_symmetricFunctions⟩)

end MvPowerSeries
