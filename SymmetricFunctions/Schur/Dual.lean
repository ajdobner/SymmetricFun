import SymmetricFunctions.Schur.Column
import SymmetricFunctions.Schur.ComplementaryMinors
import SymmetricFunctions.Schur.BoundarySign

/-!
# Dual Jacobi–Trudi and conjugation

The finite h/e Toeplitz inverse, complementary minors, and the explicitly proved
Young diagram boundary sign give the dual determinant formula. Applying omega
then conjugates the shape. Every coefficient ring is an arbitrary CommRing.
-/

namespace SymmetricFunction

noncomputable section
open SymmetricFunctions SymmetricFunctions.Partition
open scoped BigOperators
variable {R : Type*} [CommRing R] {d : ℕ}

/-- Elementary functions at integer indices; negative indices are zero. -/
def elementaryInt (k : ℤ) : SymmetricFunction R := if 0 ≤ k then e k.toNat else 0

@[simp] theorem elementaryInt_natCast (n : ℕ) : elementaryInt (R := R) (n : ℤ) = e n := by
  simp [elementaryInt]

@[simp] theorem elementaryInt_zero : elementaryInt (R := R) 0 = 1 := by
  simpa using elementaryInt_natCast (R := R) 0

@[simp] theorem elementaryInt_of_neg {k : ℤ} (hk : k < 0) : elementaryInt (R := R) k = 0 := by
  simp [elementaryInt, not_le.mpr hk]

@[simp] theorem omega_completeInt (k : ℤ) : omega (completeInt (R := R) k) = elementaryInt k := by
  unfold completeInt elementaryInt
  split_ifs <;> simp

@[simp] theorem omega_elementaryInt (k : ℤ) : omega (elementaryInt (R := R) k) = completeInt k := by
  rw [← omega_completeInt, omega_omega]

/-- Elementary Jacobi–Trudi matrix indexed by the supplied shape.
The dual formula for a Schur function uses its conjugate shape here. -/
def elementaryJacobiTrudiMatrix (ξ : Nat.Partition d) (L : ℕ) :
    Matrix (Fin L) (Fin L) (SymmetricFunction R) :=
  fun i j => elementaryInt ((rowLength ξ i : ℤ) - (i : ℤ) + (j : ℤ))

theorem omega_det_jacobiTrudiMatrix (ξ : Nat.Partition d) (L : ℕ) :
    omega (jacobiTrudiMatrix (R := R) ξ L).det = (elementaryJacobiTrudiMatrix ξ L).det := by
  rw [AlgEquiv.map_det]
  congr 1
  funext i j
  exact omega_completeInt _

/-- Elementary determinants inherit the exact sufficient-padding bound. -/
theorem det_elementaryJacobiTrudiMatrix (ξ : Nat.Partition d) {L : ℕ}
    (hL : length ξ ≤ L) :
    (elementaryJacobiTrudiMatrix (R := R) ξ L).det = omega (schur ξ) := by
  rw [← omega_det_jacobiTrudiMatrix, det_jacobiTrudiMatrix ξ hL]

/-- Signed elementary coefficients, with signs split between the two matrix indices. -/
theorem upperToeplitz_signedElementary (N : ℕ) (i j : Fin N) :
    upperToeplitz N (PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R))) i j =
      (-1 : SymmetricFunction R) ^ i.val * (-1) ^ j.val *
        elementaryInt ((j : ℤ) - (i : ℤ)) := by
  by_cases hij : i ≤ j
  · rw [upperToeplitz_apply_le N _ hij, PowerSeries.coeff_rescale,
      coeff_elementaryGeneratingSeries]
    have hn : 0 ≤ (j : ℤ) - (i : ℤ) := by omega
    simp only [elementaryInt, hn, ite_true]
    have hnat : ((j : ℤ) - (i : ℤ)).toNat = j.val - i.val := by omega
    rw [hnat]
    have hs : (-1 : SymmetricFunction R) ^ (j.val - i.val) =
        (-1) ^ i.val * (-1) ^ j.val := by
      nth_rw 2 [← Nat.sub_add_cancel (show i.val ≤ j.val from hij)]
      rw [pow_add]
      calc
        _ = (-1 : SymmetricFunction R) ^ (j.val - i.val) *
            ((-1) ^ i.val * (-1) ^ i.val) := by rw [← mul_pow]; simp
        _ = _ := by ring
    rw [hs]
  · rw [upperToeplitz_apply_gt N _ (lt_of_not_ge hij), elementaryInt_of_neg (by omega)]
    simp

private theorem det_elementary_complement (ξ : Nat.Partition d) :
    (Matrix.of (fun i j : Fin (width ξ) =>
      elementaryInt (R := R) ((boundaryColumn ξ j : ℤ) - (i : ℤ)))).det =
      (elementaryJacobiTrudiMatrix ξ.conjugate (width ξ)).det := by
  let F : Matrix (Fin (width ξ)) (Fin (width ξ)) (SymmetricFunction R) :=
    fun i j => elementaryInt ((boundaryColumn ξ j : ℤ) - (i : ℤ))
  have he : F.transpose.submatrix Fin.revPerm Fin.revPerm =
      elementaryJacobiTrudiMatrix ξ.conjugate (width ξ) := by
    funext i j
    change elementaryInt ((boundaryColumn ξ (Fin.revPerm i) : ℤ) - (Fin.revPerm j : ℤ)) = _
    dsimp only [elementaryJacobiTrudiMatrix]
    rw [rowLength_conjugate]
    have hrev (k : Fin (width ξ)) : (Fin.revPerm k : ℤ) = (width ξ : ℤ) - 1 - (k : ℤ) := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    have hidx : width ξ - 1 - (Fin.revPerm i).val = i.val := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    change elementaryInt (((Fin.revPerm i).val +
      (YoungDiagram.ofPartition ξ).colLen (width ξ - 1 - (Fin.revPerm i).val) : ℕ) -
        (Fin.revPerm j : ℤ)) = _
    rw [Nat.cast_add, hidx, hrev, hrev]
    congr 1
    ring
  calc
    _ = F.det := rfl
    _ = (F.transpose.submatrix Fin.revPerm Fin.revPerm).det := by simp
    _ = _ := congrArg Matrix.det he

private theorem prod_complement_sign (ξ : Nat.Partition d) :
    (∏ i : Fin (width ξ), (-1 : SymmetricFunction R) ^ i.val) *
      (∏ j : Fin (width ξ), (-1 : SymmetricFunction R) ^ (boundaryColumn ξ j).val) =
        (-1 : SymmetricFunction R) ^ d := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    ← pow_add, sum_boundaryColumn]
  rw [show (∑ i : Fin (width ξ), i.val) + ((∑ i : Fin (width ξ), i.val) + d) =
    ((∑ i : Fin (width ξ), i.val) + (∑ i : Fin (width ξ), i.val)) + d by omega]
  rw [pow_add, pow_add, ← mul_pow]
  simp

/-- Dual Jacobi–Trudi at the number of columns, proved by complementary minors. -/
theorem schur_eq_det_elementary_conjugate (ξ : Nat.Partition d) :
    schur (R := R) ξ = (elementaryJacobiTrudiMatrix ξ.conjugate (width ξ)).det := by
  let N := length ξ + width ξ
  let H := upperToeplitz N (completeGeneratingSeries (R := R))
  let E := upperToeplitz N
    (PowerSeries.rescale (-1) (elementaryGeneratingSeries (R := R)))
  let r := boundaryEquiv ξ
  let c := tailEquiv (length ξ) (width ξ)
  have hinv : H * E = 1 := by
    rw [← upperToeplitz_mul, mul_comm, elementary_complete_series, upperToeplitz_one]
  have hleft : H.submatrix (r ∘ Sum.inl) (c ∘ Sum.inl) =
      jacobiTrudiMatrix (R := R) ξ (length ξ) := by
    funext i j
    dsimp only [Matrix.submatrix_apply, Function.comp_def, H, N]
    rw [upperToeplitz_complete]
    dsimp only [jacobiTrudiMatrix]
    congr 1
    change ((width ξ + j.val : ℕ) : ℤ) -
      ((width ξ - rowLength ξ i + i.val : ℕ) : ℤ) = _
    have := rowLength_le_width ξ i
    omega
  have hdet : (H.submatrix r c).det = (-1 : SymmetricFunction R) ^ d := by
    have he : H.submatrix r c = (H.submatrix c c).submatrix (r.trans c.symm) id := by
      funext i j
      simp
    rw [he, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    dsimp only [r, c]
    rw [sign_boundary_relative_tail]
    simp [H, det_upperToeplitz]
  have hright : (E.submatrix (c ∘ Sum.inr) (r ∘ Sum.inr)).det =
      (-1 : SymmetricFunction R) ^ d *
        (elementaryJacobiTrudiMatrix ξ.conjugate (width ξ)).det := by
    let F : Matrix (Fin (width ξ)) (Fin (width ξ)) (SymmetricFunction R) :=
      fun i j => elementaryInt ((boundaryColumn ξ j : ℤ) - (i : ℤ))
    have he : E.submatrix (c ∘ Sum.inr) (r ∘ Sum.inr) =
        Matrix.of (fun i j : Fin (width ξ) => (-1 : SymmetricFunction R) ^ i.val *
          ((-1) ^ (boundaryColumn ξ j).val * F i j)) := by
      funext i j
      dsimp only [Matrix.submatrix_apply, Function.comp_def, E, N]
      rw [upperToeplitz_signedElementary]
      change (-1 : SymmetricFunction R) ^ i.val * (-1) ^ (boundaryColumn ξ j).val *
        elementaryInt ((boundaryColumn ξ j : ℤ) - (i : ℤ)) = _
      exact mul_assoc _ _ _
    have hc := Matrix.det_mul_column
      (fun i : Fin (width ξ) => (-1 : SymmetricFunction R) ^ i.val)
      (Matrix.of (fun i j => (-1 : SymmetricFunction R) ^ (boundaryColumn ξ j).val * F i j))
    simp only [Matrix.of_apply] at hc
    rw [he, hc, Matrix.det_mul_row (fun j : Fin (width ξ) =>
      (-1 : SymmetricFunction R) ^ (boundaryColumn ξ j).val) F,
      ← mul_assoc, prod_complement_sign]
    congr 1
    exact det_elementary_complement ξ
  have hm := det_minor_eq_det_mul_complement H E hinv r c
  rw [hleft, hdet, hright, ← mul_assoc, ← mul_pow] at hm
  simpa only [schur, neg_mul_neg, one_mul, one_pow] using hm

/-- The elementary–complete involution conjugates Schur shapes. -/
@[simp] theorem omega_schur (ξ : Nat.Partition d) :
    omega (schur (R := R) ξ) = schur ξ.conjugate := by
  rw [schur_eq_det_elementary_conjugate, det_elementaryJacobiTrudiMatrix _
    (by simp [width]), omega_omega]

/-- Dual Jacobi–Trudi for every sufficient padding of the conjugate partition. -/
theorem dual_jacobiTrudi (ξ : Nat.Partition d) {L : ℕ} (hL : length ξ.conjugate ≤ L) :
    (elementaryJacobiTrudiMatrix (R := R) ξ.conjugate L).det = schur ξ := by
  rw [det_elementaryJacobiTrudiMatrix ξ.conjugate hL, omega_schur,
    Nat.Partition.conjugate_conjugate]

end
end SymmetricFunction
