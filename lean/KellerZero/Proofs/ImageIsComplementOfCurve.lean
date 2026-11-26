import KellerZero.Open
import KellerZero.Structure

/-!
# O1: over the complex numbers the gadget misses the curve and nothing else

The work is in `KellerZero.Structure`: a target with `c ≠ 0` is a value exactly when the cubic
`m³ - 2 m² + b c m - 2 a c²` has a simple root, and over an algebraically closed field that
fails only when the cubic is `(m - 2/3)³`, which is the curve.
-/

theorem KellerZero.Proofs.ImageIsComplementOfCurve : KellerZero.Open.ImageIsComplementOfCurve :=
  fun a b c => KellerZero.image_complex a b c
