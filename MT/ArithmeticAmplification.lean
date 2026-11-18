module

public import MT.Amplification
public import MT.Tower

/-! # Arithmetic amplification, Proposition 4.1
The absolute root-discriminant bound is fixed before every other parameter
and the degree. The construction then produces the actual finite sets.
-/

public section
namespace MT

/-- The complete arithmetic proposition, using Sawin's totally real tower
in the field-supply step. -/
theorem arithmeticAmplification : ArithmeticAmplification :=
  arithmeticAmplification_of_dyadic_fields 255255 (by decide) Tower.dyadic_totally_real_fields

end MT
