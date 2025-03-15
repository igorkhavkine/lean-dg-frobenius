import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField
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

open VectorField ContDiff

variable (M: Type*) {dim: ℕ} [SmoothManifold M dim]

abbrev STangentSpace (x: M)
  := TangentSpace (modelWithCornersSelf ℝ (E dim)) x

-- As of 06.03.2025, Mathlib has a definition of the Lie bracket of vector fields,
-- and a formalization of a bunch of its properties.
-- Here's a example: the Lie bracket of two smooth vector fields is a smooth vector field.

-- sections as dependent functions
variable (V W : Π (x: M), STangentSpace (dim := dim) M x)
#check mlieBracket (modelWithCornersSelf ℝ (E dim)) V W -- the Lie bracket is defined
-- Smoothness of sections is encoded as follows:
variable (hV : ∀ (x : M), ContMDiffAt
  𝓘(ℝ, E dim) --(modelWithCornersSelf ℝ (E dim))
  𝓘(ℝ, E dim).tangent
  ∞
  (fun y ↦ (V y : TangentBundle (modelWithCornersSelf ℝ (E dim)) M)) x)
variable (hW : ∀ (x : M), ContMDiffAt
  (modelWithCornersSelf ℝ (E dim))
  (modelWithCornersSelf ℝ (E dim)).tangent
  ∞
  (fun y ↦ (W y : TangentBundle (modelWithCornersSelf ℝ (E dim)) M)) x)
-- need to check that the original smoothness of V and W (∞) is at least
-- as big as 1 + the requested smoothness of their Lie bracket (∞ + 1)
theorem minSmoothness_inf_add_1_le_inf : (minSmoothness ℝ (∞ + 1)) ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  norm_num
-- the following proves that the Lie bracket [V,W] is smooth wen V and W are smooth
example := fun x ↦
  ContMDiffAt.mlieBracket_vectorField (hV x) (hW x) minSmoothness_inf_add_1_le_inf


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
