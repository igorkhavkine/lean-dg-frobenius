import Mathlib

variable
  {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup A] [NormedAddCommGroup B]
  [NormedAddCommGroup C] [Module 𝕜 A] [Module 𝕜 B] [Module 𝕜 C]

theorem fderiv_to_fst
  {f : A × B → C} {U : Set (A × B)} {x : A × B} {f' : A × B →L[𝕜] C}
  (hf : HasFDerivWithinAt f f' U x)
  : HasFDerivWithinAt (fun a => f (a, x.2)) (fun a => f' (a, 0)) (Prod.fst '' U) x.1
  := by
    sorry
