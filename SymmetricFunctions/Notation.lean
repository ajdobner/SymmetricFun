import SymmetricFunctions.Names
import SymmetricFunctions.Plethysm.Integral

/-!
# Optional symmetric-function notation

Activate with `open scoped SymmetricFunctionNotation`. Importing this module
alone does not activate the notation. All operations keep their named API.

* `Λ[R]`: bounded symmetric functions over R.
* `ω f`: the elementary-complete involution (`SymmetricFunction.omega`).
* `λ[n] a`: exterior powers (`LambdaRing.lambda`) on any pre-lambda ring.
* `f⟦g⟧`: integral plethysm (`SymmetricFunction.plethysm`), outer argument first.

Uppercase Omega is reserved for a future degree-completed series with justified
evaluation operations. See `docs/NOTATION.md` for alphabet and coefficient roles.
-/

scoped[SymmetricFunctionNotation] notation:max "Λ[" R "]" => SymmetricFunction R
scoped[SymmetricFunctionNotation] notation "ω" => SymmetricFunction.omega
scoped[SymmetricFunctionNotation] notation:max "λ[" n "] " a:arg => LambdaRing.lambda n a
scoped[SymmetricFunctionNotation] notation:max f:arg "⟦" g "⟧" => SymmetricFunction.plethysm f g
