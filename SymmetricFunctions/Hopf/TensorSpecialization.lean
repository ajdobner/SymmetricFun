import SymmetricFunctions.Hopf.Alphabets
import SymmetricFunctions.BaseChange
import LambdaRing.UniversalPolynomials.TwoAlphabetBounds

/-! # Faithful specialization in two independent alphabets

The tensor polynomial presentation is purely algebraic. Elementary-generator
variables are not asserted to be line elements for any lambda structure.
-/

noncomputable section

namespace SymmetricFunction

open scoped TensorProduct

variable (R : Type*) [CommRing R]

/-- The two elementary-generator blocks present the tensor algebra. -/
def tensorPolynomialEquiv : (SymmetricFunction R ⊗[R] SymmetricFunction R) ≃ₐ[R]
    MvPolynomial (ℕ+ ⊕ ℕ+) R :=
  (Algebra.TensorProduct.congr (polynomialEquiv R) (polynomialEquiv R)).trans
    (MvPolynomial.tensorEquivSum R ℕ+ ℕ+ R)

@[simp] theorem tensorPolynomialEquiv_e_left (i : ℕ+) :
    tensorPolynomialEquiv R (e (i : ℕ) ⊗ₜ[R] 1) = MvPolynomial.X (Sum.inl i) := by
  simp [tensorPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

@[simp] theorem tensorPolynomialEquiv_e_right (i : ℕ+) :
    tensorPolynomialEquiv R (1 ⊗ₜ[R] e (i : ℕ)) = MvPolynomial.X (Sum.inr i) := by
  simp [tensorPolynomialEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]

/-- Finite alphabet evaluation of the tensor presentation is elementary substitution. -/
theorem tensorAlphabetSpecialization_eq_aeval (N M : ℕ)
    (x : SymmetricFunction R ⊗[R] SymmetricFunction R) :
    tensorAlphabetSpecialization R (Fin N) (Fin M) x =
      MvPolynomial.aeval (Sum.elim
        (fun i : ℕ+ => MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin N) R i))
        (fun j : ℕ+ => MvPolynomial.rename Sum.inr (MvPolynomial.esymm (Fin M) R j)))
        (tensorPolynomialEquiv R x) := by
  have he : tensorAlphabetSpecialization R (Fin N) (Fin M) =
      (MvPolynomial.aeval (Sum.elim
        (fun i : ℕ+ => MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin N) R i))
        (fun j : ℕ+ => MvPolynomial.rename Sum.inr (MvPolynomial.esymm (Fin M) R j)))).comp
        (tensorPolynomialEquiv R).toAlgHom := by
    apply Algebra.TensorProduct.ext
    · apply algHom_ext
      intro i
      simp
    · apply algHom_ext
      intro i
      simp
  exact DFunLike.congr_fun he x

/-- All finite pairs of independent alphabets jointly detect equality, over any ring. -/
theorem eq_of_tensorAlphabetSpecialization_eq
    {x y : SymmetricFunction R ⊗[R] SymmetricFunction R}
    (h : ∀ N M, tensorAlphabetSpecialization R (Fin N) (Fin M) x =
      tensorAlphabetSpecialization R (Fin N) (Fin M) y) : x = y := by
  classical
  apply (tensorPolynomialEquiv R).injective
  let q := tensorPolynomialEquiv R x
  let r := tensorPolynomialEquiv R y
  let s := q.vars ∪ r.vars
  let D := s.sup (Sum.elim PNat.val PNat.val)
  have hb (i : ℕ+ ⊕ ℕ+) (hi : i ∈ s) : Sum.elim PNat.val PNat.val i ≤ D :=
    Finset.le_sup hi
  apply LambdaRing.UniversalPolynomial.twoElementary_injective_of_vars_le R D D
  · intro i hi
    exact hb (Sum.inl i) (Finset.mem_union_left _ hi)
  · intro i hi
    exact hb (Sum.inr i) (Finset.mem_union_left _ hi)
  · intro i hi
    exact hb (Sum.inl i) (Finset.mem_union_right _ hi)
  · intro i hi
    exact hb (Sum.inr i) (Finset.mem_union_right _ hi)
  · simpa only [tensorAlphabetSpecialization_eq_aeval] using h D D

end SymmetricFunction
