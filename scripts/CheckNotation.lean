import SymmetricFunctions

/-!
Notation regression checks outside the accepted library. Expected failures test
scope isolation and reject unsupported coefficient/target assumptions. Their
diagnostics are suppressed; an unexpectedly successful check still fails.
-/

noncomputable section

-- Importing the root does not activate any of the optional notation.
#guard_msgs (drop info) in
#check_failure Λ[ℤ]
#guard_msgs (drop info) in
#check_failure ω
#guard_msgs (drop info) in
#check_failure Ω

section

open SymmetricFunction
open scoped SymmetricFunctionNotation

-- No implicit extension of integral plethysm to rational coefficients.
#guard_msgs (drop info) in
#check_failure (fun f g : Λ[ℚ] => f⟦g⟧)

-- CommRing alone does not manufacture an exterior-power structure.
#guard_msgs (drop info) in
#check_failure (λ[2] (1 : ℚ))

/-- info: fun f g => f⟦g⟧ : Λ[ℤ] → Λ[ℤ] → Λ[ℤ] -/
#guard_msgs in
#check fun f g : Λ[ℤ] => f⟦g⟧

/-- trace: f g k : Λ[ℤ]
⊢ f⟦g⟧⟦k⟧ = f⟦g⟦k⟧⟧ -/
#guard_msgs in
example (f g k : Λ[ℤ]) : (f⟦g⟧)⟦k⟧ = f⟦g⟦k⟧⟧ := by
  trace_state
  exact plethysm_assoc f g k

/-- trace: f : Λ[ℤ]
⊢ ω (ω f) = f -/
#guard_msgs in
example (f : Λ[ℤ]) : ω (ω f) = f := by
  trace_state
  exact omega_omega f

/-- trace: f : Λ[ℤ]
n : ℕ
⊢ λ[n] f = λ[n] f -/
#guard_msgs in
example (f : Λ[ℤ]) (n : ℕ) : λ[n] f = LambdaRing.lambda n f := by
  trace_state
  rfl

end

-- Leaving the section also closes the notation scope.
#guard_msgs (drop info) in
#check_failure Λ[ℤ]
#guard_msgs (drop info) in
#check_failure ω

-- Descriptive declarations remain usable without any notation scope.
#check SymmetricFunction.plethysm_assoc
#check SymmetricFunction.elementaryCompleteInvolution
#print axioms SymmetricFunction.plethysm_assoc

section
open SymmetricFunction
open scoped SymmetricFunctionNotation

/-- trace: ⊢ DegreeCompletion.component ℤ Ω 2 = h 2 -/
#guard_msgs in
example : DegreeCompletion.component ℤ Ω 2 = h 2 := by
  trace_state
  simp

-- Uppercase Omega cannot inhabit the bounded ring or integral plethysm inputs.
#guard_msgs (drop info) in
#check_failure (Ω : Λ[ℤ])
#guard_msgs (drop info) in
#check_failure (Ω⟦e (R := ℤ) 1⟧)

example {R : Type*} [CommRing R] : (Ω : DegreeCompletion R) + Ω * Ω =
    completeSeries + completeSeries * completeSeries := rfl
end
