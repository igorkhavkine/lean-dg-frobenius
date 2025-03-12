import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib


open Nat Real Manifold

abbrev E (dim: ℕ) := (EuclideanSpace ℝ (Fin dim))

class SmoothManifold (M: Type*) (dim: ℕ) extends
  TopologicalSpace M, ChartedSpace (E dim) M, IsManifold (modelWithCornersSelf ℝ (E dim)) ⊤ M

abbrev SSmoothMap (X: Type*) {dimX: ℕ} (Y: Type*) {dimY: ℕ} [SmoothManifold X dimX] [SmoothManifold Y dimY]
  := ContMDiffMap (modelWithCornersSelf ℝ (E dimX)) (modelWithCornersSelf ℝ (E dimY)) X Y ⊤



abbrev SVectorBundle {B: Type*} (F: Type*) (V: B → Type*)
  [(x:B) → AddCommMonoid (V x)] [(x:B) → Module ℝ (V x)]
  [(x:B) → TopologicalSpace (V x)] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V]
    := VectorBundle ℝ F V

-- For some reason ContMDiffSection induced a different type for its last hidden
-- argument differently than the default type given to fbFV by the typeclass resolver.
-- The default hidden argument to FiberBundle is tot_topF, while
-- ContMDiffSection expected UniformSpace.toTopologicalSpace in its place.
-- Is it a Mathlib bug, or is that intentional behavior?
abbrev SSmoothSection {M: Type*} {dim: ℕ}
  [SmoothManifold M dim] -- base manifold
  (F: Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] -- bundle fiber type
  (V: M → Type*) -- total space of the bundle
  [tot_topF : TopologicalSpace F] [tot_topFV : TopologicalSpace (Bundle.TotalSpace F V)]
  [fib_topFV : (x:M) → TopologicalSpace (V x)] [fbFV : @FiberBundle _ F _ UniformSpace.toTopologicalSpace V _ _ ] -- This assumption doesn't seem to satisfy the typechecker
    := @ContMDiffSection _ _ _ _ _ _ _ (modelWithCornersSelf ℝ (E dim)) M _ _ F _ _ ⊤ V _ _ fbFV


section TangentBundle

variable (M: Type*) {dim: ℕ} [SmoothManifold M dim]

abbrev STangentSpace (x: M)
  := TangentSpace (modelWithCornersSelf ℝ (E dim)) x


-- defn of the section of (vec) bundle
--
abbrev STangentBundle
    := TangentBundle (modelWithCornersSelf ℝ (E dim)) M

-- find bundle tot.sp. smooth manif
--
instance: SmoothManifold (@STangentBundle M dim _) (2*dim) :=
  sorry

abbrev SVectorField
  := @SSmoothMap M dim (@STangentBundle M dim _) (2*dim) _ _ -- use section

end TangentBundle

-- find global/inv definition, or *local coords*, or derivations
--
def lieBracket {M: Type*} {dim: ℕ} [SmoothManifold M dim]
  (X: @SVectorField M dim _) (Y: @SVectorField M dim _) : @SVectorField M dim _
  := X∘Y - Y∘X

#min_imports
