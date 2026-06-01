import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import SymmetricPoly.DecomposableAddMonoid

/-! # Total Monoid Algebras
  `TotalAddMonoidAlgebra R M` is made up of of formal series `M → R`. If
  `M` is a `DecomposableAddMonoid` and `R` is a ring, then `TotalAddMonoidAlgebra R M`
  is an $R$-algebra. We use the notation `R[[M]]` for this structure. -/
@[ext]
structure TotalAddMonoidAlgebra (R M : Type*) [Semiring R] where
  /-- Construct a total formal series from its coefficients, which is a function `M → R`. -/
  ofCoeff :: coeff : M → R

namespace TotalAddMonoidAlgebra

noncomputable section

scoped syntax:max (priority := high) term noWs "[[" term "]]" : term

macro_rules | `($R[[$M]]) => `(TotalAddMonoidAlgebra $R $M)

@[scoped app_unexpander TotalAddMonoidAlgebra]
meta def unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $R $M) => `($R[[$M]])
  | _ => throw ()


variable {R M : Type*}

section Semiring

variable [Semiring R]

def coeffEquiv : R[[M]] ≃ (M → R) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

/-- Construct an element consisting of a single term. -/
@[simp]
def single (m : M) (r : R) : R[[M]] :=
  letI := Classical.decEq M
  .ofCoeff <| Pi.single m r

@[simp]
lemma coeff_single (m : M) (r : R) :
  (single m r).coeff = letI := Classical.decEq M; Pi.single m r := rfl

/-- Additive structure. -/
instance : Add R[[M]] where
  add f g := ofCoeff (f.coeff + g.coeff)

lemma single_add (m : M) (r₁ r₂ : R) : single m (r₁ + r₂) = single m r₁ + single m r₂ := by
  ext x
  letI := Classical.decEq M
  exact congr_fun (@Pi.single_add M (fun _ => R) _ _ m r₁ r₂) x

/-- The zero element has all coefficients zero. -/
instance : Zero R[[M]] where
  zero := ofCoeff 0

lemma single_zero (m : M) : (single m 0 : R[[M]]) = 0 := by simp [single]; rfl

instance instAddCommMonoid : AddCommMonoid R[[M]] := Equiv.addCommMonoid coeffEquiv

/-- The embedding of scalars in `R[[M]]` is a monoid homomorphism. -/
def singleAddHom (m : M) : R →+ R[[M]] where
  toFun := single m
  map_zero' := single_zero _
  map_add' := single_add _

section SMul
variable {A : Type*} [SMulZeroClass A R]

instance smulZeroClass : SMulZeroClass A R[[M]] := Equiv.smulZeroClass A coeffEquiv

end SMul

section DecomposableAddMonoid

variable [DecomposableAddMonoid M]

instance instOne : One R[[M]] where
  one := single 0 1

theorem one_def : (1 : R[[M]]) = single 0 1 := rfl

instance instMul : Mul R[[M]] where
  mul f g := ofCoeff (fun m =>
    ∑ p ∈ DecomposableAddMonoid.antidiagonal m, f.coeff p.1 * g.coeff p.2)




@[simp]
lemma coeff_mul (f g : R[[M]]) (m : M) :
  (f * g).coeff m = ∑ p ∈ DecomposableAddMonoid.antidiagonal m, f.coeff p.1 * g.coeff p.2 := rfl

-- @[simp]
-- lemma coeff_add (f g : R[[M]]) (m : M) :
--   (f + g).coeff m = f.coeff m + g.coeff m := rfl

lemma coeff_single_zero_mul (x : R[[M]]) (r : R) (m : M) : (single 0 r * x).coeff m =
  r * x.coeff m := by
  simp only [coeff_mul]
  exact Finset.sum_eq_single (0, m)
    (by
      rintro ⟨p1, p2⟩ hp hneq
      simp only [coeff_single, Pi.single_apply]
      split_ifs with h
      · exfalso; apply hneq
        have hp_add := DecomposableAddMonoid.mem_antidiagonal.mp hp
        rw [h, zero_add] at hp_add
        exact Prod.ext h hp_add
      · exact MulZeroClass.zero_mul _)
    (by
      intro hnot; exfalso; apply hnot
      exact DecomposableAddMonoid.mem_antidiagonal.mpr (zero_add m))
    |>.trans (by simp)

lemma coeff_mul_single_zero (x : R[[M]]) (r : R) (m : M) : (x * single 0 r).coeff m =
  x.coeff m * r := by
  simp only [coeff_mul]
  exact Finset.sum_eq_single (m, 0)
    (by
      rintro ⟨p1, p2⟩ hp hneq
      simp only [coeff_single, Pi.single_apply]
      split_ifs with h
      · exfalso; apply hneq
        have hp_add := DecomposableAddMonoid.mem_antidiagonal.mp hp
        rw [h, add_zero] at hp_add
        exact Prod.ext hp_add h
      · exact MulZeroClass.mul_zero _)
    (by
      intro hnot; exfalso; apply hnot
      exact DecomposableAddMonoid.mem_antidiagonal.mpr (add_zero m))
    |>.trans (by simp)


instance semiring : Semiring R[[M]] where
  zero_mul a := by
    ext m
    exact Finset.sum_eq_zero (fun p _ => MulZeroClass.zero_mul _)
  mul_zero a := by
    ext m
    exact Finset.sum_eq_zero (fun p _ => MulZeroClass.mul_zero _)
  left_distrib a b c := by
    ext m
    change ∑ p ∈ DecomposableAddMonoid.antidiagonal m, a.coeff p.1 * (b.coeff p.2 + c.coeff p.2) = _
    simp only [mul_add, Finset.sum_add_distrib]
    rfl
  right_distrib a b c := by
    ext m
    change ∑ p ∈ DecomposableAddMonoid.antidiagonal m, (a.coeff p.1 + b.coeff p.1) * c.coeff p.2 = _
    simp only [add_mul, Finset.sum_add_distrib]
    rfl
  one_mul a := by
    ext m
    rw [one_def, coeff_single_zero_mul]
    simp only [one_mul]
  mul_one a := by
    ext m
    rw [one_def, coeff_mul_single_zero]
    simp only [mul_one]
  /- The hard work for mul_assoc is done by DecomposableAddMonoid theorems. -/
  mul_assoc a b c := by
    ext m
    simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, ←mul_assoc]
    let f : M → M → M → R := fun x y z => a.coeff x * b.coeff y * c.coeff z
    have : DecidableEq M := Classical.decEq M
    rw [←DecomposableAddMonoid.antidoublediagonal_fst_sum f m]
    rw [←DecomposableAddMonoid.antidoublediagonal_snd_sum f m]


@[simp]
lemma single_mul_single (x y : R) : (single 0 (x * y) : R[[M]]) =
  single 0 x * single 0 y := by
  ext m
  rw [coeff_single_zero_mul]
  simp only [coeff_single, Pi.single_apply]
  split_ifs with h
  · rfl
  · rw [MulZeroClass.mul_zero]

/-- The embedding of scalars into `R[[M]]` is a ring homomorphism. -/
def singleZeroRingHom : R →+* R[[M]] where
  __ := singleAddHom 0
  map_one' := rfl
  map_mul' x y := by
    simp only [singleAddHom, single_mul_single]

end DecomposableAddMonoid
end Semiring

section Algebra
variable [CommSemiring R] [Semiring A] [Algebra R A]

instance instAlgebra [DecomposableAddMonoid M] : Algebra R A[[M]] where
  algebraMap := singleZeroRingHom.comp (algebraMap R A)
  commutes' r f := by
    ext m
    change (single 0 (algebraMap R A r) * f).coeff m = (f * single 0 (algebraMap R A r)).coeff m
    rw [coeff_single_zero_mul, coeff_mul_single_zero, Algebra.commutes]
  smul_def' r f := by
    ext m
    change r • f.coeff m = (single 0 (algebraMap R A r) * f).coeff m
    rw [coeff_single_zero_mul, Algebra.smul_def]

end Algebra

end

end TotalAddMonoidAlgebra
