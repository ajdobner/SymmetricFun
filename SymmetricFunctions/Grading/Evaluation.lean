import SymmetricFunctions.Grading

/-! # Evaluation respecting weighted degree -/

noncomputable section

namespace SymmetricFunctions

/-- Substituting homogeneous polynomials of the assigned variable weights preserves weight. -/
theorem weightedHomogeneous_aeval {σ τ R M : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {v : τ → M} {p : MvPolynomial σ R} {d : M}
    (hp : p.IsWeightedHomogeneous w d) (x : σ → MvPolynomial τ R)
    (hx : ∀ i, (x i).IsWeightedHomogeneous v (w i)) :
    (MvPolynomial.aeval x p).IsWeightedHomogeneous v d := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero R v d
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial a r ha =>
    rw [MvPolynomial.aeval_monomial]
    have hg := MvPolynomial.IsWeightedHomogeneous.prod a.support
      (fun i => x i ^ a i) (fun i => a i • w i) (fun i _ => (hx i).pow (a i))
    change (a.prod (fun i k => x i ^ k)).IsWeightedHomogeneous v (a.weight w) at hg
    rw [ha] at hg
    exact hg.C_mul r

end SymmetricFunctions

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- Public evaluation preserves homogeneous degree when the generator images do. -/
theorem isHomogeneous_eval (x : ℕ+ → SymmetricFunction R)
    (hx : ∀ i, IsHomogeneous (x i) i) {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous (eval x f) d := by
  unfold IsHomogeneous at *
  have he : polynomialEquiv R (eval x f) =
      MvPolynomial.aeval (fun i => polynomialEquiv R (x i)) (polynomialEquiv R f) := by
    exact MvPolynomial.comp_aeval_apply x (polynomialEquiv R).toAlgHom (polynomialEquiv R f)
  rw [he]
  exact SymmetricFunctions.weightedHomogeneous_aeval hf _ hx

end SymmetricFunction
