import LambdaRing.Preservation

/-! # Descent of lambda laws along surjective preserving ring maps -/

noncomputable section

namespace PreLambdaRing

variable {A B : Type*} [CommRing A] [PreLambdaRing A] [CommRing B]

/-- Operations on a surjective ring image inherit the pre-lambda laws
when preservation is proved. -/
@[instance_reducible] def ofSurjective (φ : A →+* B) (hφ : Function.Surjective φ) (op : ℕ → B → B)
    (hop : ∀ n a, φ (LambdaRing.lambda n a) = op n (φ a)) : PreLambdaRing B where
  lambdaOp := op
  lambda_zero b := by obtain ⟨a, rfl⟩ := hφ b; rw [← hop, LambdaRing.lambda_zero, map_one]
  lambda_one b := by obtain ⟨a, rfl⟩ := hφ b; rw [← hop, LambdaRing.lambda_one]
  lambda_add n b c := by
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨d, rfl⟩ := hφ c
    rw [← map_add, ← hop, LambdaRing.lambda_add, map_sum]
    simp only [map_mul, hop]

end PreLambdaRing

namespace SpecialLambdaRing

variable {A B : Type*} [CommRing A] [PreLambdaRing A] [SpecialLambdaRing A]
variable [CommRing B] [PreLambdaRing B]

/-- Both special identities descend along an actual surjective preserving ring map. -/
theorem ofSurjective (φ : A →+* B) (hφ : Function.Surjective φ)
    (hop : ∀ n a, φ (LambdaRing.lambda n a) = LambdaRing.lambda n (φ a)) :
    SpecialLambdaRing B where
  lambda_unit n := by
    rw [← map_one φ, ← hop, LambdaRing.lambda_unit]
    split <;> simp
  lambda_mul n b c := by
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨d, rfl⟩ := hφ c
    rw [← map_mul, ← hop, LambdaRing.lambda_mul,
      LambdaRing.Polynomial.map_int_aeval_sum φ]
    simp only [hop]
  lambda_iterate n m b := by
    obtain ⟨a, rfl⟩ := hφ b
    rw [← hop, ← hop, LambdaRing.lambda_iterate, LambdaRing.Polynomial.map_int_aeval φ]
    simp only [hop]

end SpecialLambdaRing
