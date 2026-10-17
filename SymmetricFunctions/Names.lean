import SymmetricFunctions.Omega
import SymmetricFunctions.PowerSum

/-!
# Descriptive names for classical symmetric functions

These aliases help declaration search and prose-like statements. The traditional
`e`, `h`, `p`, and `omega` names and their theorem API remain available unchanged.
-/

noncomputable section

namespace SymmetricFunction

/-- The elementary symmetric function; `elementary 0 = 1`. Alias of `e`. -/
abbrev elementary {R : Type*} [CommSemiring R] (n : ℕ) : SymmetricFunction R := e n

/-- The complete homogeneous symmetric function; `complete 0 = 1`. Alias of `h`. -/
abbrev complete {R : Type*} [CommRing R] (n : ℕ) : SymmetricFunction R := h n

/-- The positive-index power-sum symmetric function. Alias of `p`. -/
abbrev powerSum {R : Type*} [CommRing R] (n : ℕ+) : SymmetricFunction R := p n

/-- The elementary-complete involution, traditionally denoted by lowercase omega.
This is unrelated to the uppercase Omega series in the degree completion. -/
abbrev elementaryCompleteInvolution {R : Type*} [CommRing R] :
    SymmetricFunction R ≃ₐ[R] SymmetricFunction R := omega

end SymmetricFunction
