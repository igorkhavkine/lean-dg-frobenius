import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib

/-
NOTES:
------

Lemma 4:
  - Notation αⁱⱼ (Lᵢ u) is function application or multiplication?
  - Converse implication confusion if the former is function application.

Lemma 5:
  - Distribution D in proof not mentioned before.
  - Likewise for the neighborhood U; but that may be implicitly assumed around x₀.
  - Split sub-neighborhood not defined.

Lemma 7:
  - Formulation uses both Zʲ(ty,z) and Zʲ(t,y,z).
-/

abbrev E (dim: ℕ) := (EuclideanSpace ℝ (Fin dim))

abbrev SmoothManifold (M: Type) (dim: ℕ)
  [TopologicalSpace M] [ChartedSpace (E dim) M]
    := IsManifold (modelWithCornersSelf ℝ (E dim)) ⊤ M

abbrev SSmoothMap {X: Type} {dimX: ℕ} {Y: Type} {dimY: ℕ}
  [TopologicalSpace X] [ChartedSpace (E dimX) X] [SmoothManifold X dimX]
  [TopologicalSpace Y] [ChartedSpace (E dimY) Y] [SmoothManifold Y dimY]
    := ContMDiffMap
      (modelWithCornersSelf ℝ (E dimX))
      (modelWithCornersSelf ℝ (E dimY))
      X
      Y

-- FIXME: Can we suppress typeclass assumptions impied by other typeclasses
--  (e.g. SmoothManifold => TopologicalSpace)
--
abbrev STangentBundle (M: Type) {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim]
    := TangentBundle (modelWithCornersSelf ℝ (E dim)) M

abbrev SVectorBundle {B: Type} (F: Type) (V: B → Type)
  [(x:B) → AddCommMonoid (V x)] [(x:B) → Module ℝ (V x)]
  [(x:B) → TopologicalSpace (V x)] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V]
    := VectorBundle ℝ F V


#synth NormedAddCommGroup (E 4)

abbrev SSmoothSection {M: Type} {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim]
  (F: Type)
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V: M → Type)
  [TopologicalSpace F] [TopologicalSpace (Bundle.TotalSpace F V)]
  [(x:M) → TopologicalSpace (V x)] [FiberBundle F V] -- This assumption doesn't seem to satisfy the typechecker
    := ContMDiffSection (modelWithCornersSelf ℝ (E dim)) F ⊤ V

abbrev SVectorField {M: Type} {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim]
    := SSmoothSection (STangentBundle M)

-- TODO: Lie bracket
