import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
--import Mathlib

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
    TYPO FIXED: Zʲ(t,y,z) -> Zʲ(ty,z)
-/

open Nat Real Manifold

abbrev E (dim: ℕ) := (EuclideanSpace ℝ (Fin dim))

abbrev SmoothManifold (M: Type*) (dim: ℕ)
  [TopologicalSpace M] [ChartedSpace (E dim) M]
    := IsManifold (modelWithCornersSelf ℝ (E dim)) ⊤ M

abbrev SSmoothMap {X: Type*} {dimX: ℕ} {Y: Type*} {dimY: ℕ}
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
abbrev STangentBundle (M: Type*) {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim]
    := TangentBundle (modelWithCornersSelf ℝ (E dim)) M

abbrev SVectorBundle {B: Type*} (F: Type*) (V: B → Type*)
  [(x:B) → AddCommMonoid (V x)] [(x:B) → Module ℝ (V x)]
  [(x:B) → TopologicalSpace (V x)] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V]
    := VectorBundle ℝ F V


#synth NormedAddCommGroup (E 4)

-- For some reason ContMDiffSection induced a different type for its last hidden
-- argument differently than the default type given to fbFV by the typeclass resolver.
-- The default hidden argument to FiberBundle is tot_topF, while
-- ContMDiffSection expected UniformSpace.toTopologicalSpace in its place.
-- Is it a Mathlib bug, or is that intentional behavior?
abbrev SSmoothSection {M: Type*} {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim] -- base manifold
  (F: Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] -- bundle fiber type
  (V: M → Type*) -- total space of the bundle
  [tot_topF : TopologicalSpace F] [tot_topFV : TopologicalSpace (Bundle.TotalSpace F V)]
  [fib_topFV : (x:M) → TopologicalSpace (V x)] [fbFV : @FiberBundle _ F _ UniformSpace.toTopologicalSpace V _ _ ] -- This assumption doesn't seem to satisfy the typechecker
    := @ContMDiffSection _ _ _ _ _ _ _ (modelWithCornersSelf ℝ (E dim)) M _ _ F _ _ ⊤ V _ _ fbFV

abbrev SVectorField {M: Type} {dim: ℕ}
  [TopologicalSpace M] [ChartedSpace (E dim) M] [SmoothManifold M dim]
    := SSmoothSection (STangentBundle M)

-- TODO: Lie bracket

#min_imports
