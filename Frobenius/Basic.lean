import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField
import Mathlib


open Nat Real Manifold

abbrev E (dim: ℕ) := (EuclideanSpace ℝ (Fin dim))
abbrev euclMod (dim: ℕ) := modelWithCornersSelf ℝ (E dim)

class SmoothManifold (M: Type*) (dim: ℕ) extends
  TopologicalSpace M, ChartedSpace (E dim) M, IsManifold (euclMod dim) ⊤ M

abbrev SSmoothMap (X: Type*) {dimX: ℕ} [SmoothManifold X dimX] (Y: Type*) {dimY: ℕ} [SmoothManifold Y dimY]
  := ContMDiffMap (euclMod dimX) (euclMod dimY) X Y ⊤



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
    := @ContMDiffSection _ _ _ _ _ _ _ (euclMod dim) M _ _ F _ _ ⊤ V _ _ fbFV


section TangentBundle

open VectorField ContDiff

variable (M: Type*) {dim: ℕ} [SmoothManifold M dim]

abbrev STangentSpace (x: M)
  := TangentSpace (euclMod dim) x

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
noncomputable def STangentBundle
    := tangentBundleCore (euclMod dim) M

-- find bundle tot.sp. smooth manif

-- FOUND: tangent bundle as derivations (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/DerivationBundle.html)
---- Didn't study in detail.

-- FOUND: vector fields as smooth maps (x:M) -> T_x M (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField.html#VectorField.mlieBracket)
---- Provides theorems about pullbacks and the Lie bracket.
---- Seems quite isolated from the rest of MathLib.

instance: SmoothManifold (@STangentBundle M dim _).TotalSpace (2*dim) :=
  sorry

abbrev SVectorField
  := @SSmoothMap M dim _ (@STangentBundle M dim _).TotalSpace (2*dim) _ --M → (@STangentBundle M dim _).TotalSpace

end TangentBundle

-- find global/inv definition, or *local coords*, or derivations
--
def lieBracket {M: Type*} {dim: ℕ} [SmoothManifold M dim]
  (X: @SVectorField M dim _) (Y: @SVectorField M dim _) : @SVectorField M dim _
  := sorry

section FrobLoc

open Function ContDiff

-- bundle ordinary real vector spaces
class oVectorSpace (V : Type*) (dim : ℕ) extends
  AddCommGroup V, Module ℝ V, FiniteDimensional ℝ V

class oNormedSpace (V : Type*) (dim : ℕ) extends
  NormedAddCommGroup V, NormedSpace ℝ V, FiniteDimensional ℝ V

abbrev SmoothFunction {B F : Type*} {dimB dimF : ℕ} [oNormedSpace B dimB] [oNormedSpace F dimF] (f : B → F)
  := ContDiff ℝ ∞ f

variable {B F : Type*} {dimB dimF : ℕ} [oNormedSpace B dimB] [oNormedSpace F dimF]

-- vector fields on a vector space, as vector valued functions
variable {v : B → F}
  (hv : SmoothFunction (dimB := dimB) (dimF := dimF) v)
variable {w : B → F}
  (hw : SmoothFunction (dimB := dimB) (dimF := dimF) w)

local instance : oNormedSpace (B × F) (dimB + dimF) := by
  constructor

noncomputable local instance : oNormedSpace (B →L[ℝ] F) (dimB * dimF) := by
  constructor

abbrev minSmoothness_nat_le_inf {n : ℕ} : minSmoothness ℝ n ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact ENat.LEInfty.out

-- should be made more general
theorem fderiv_congr (hvw : v = w) : fderiv ℝ v = fderiv ℝ w := by
  funext x
  rw [fderiv_def, fderiv_def]
  refine fderivWithin_congr ?_ (congr_fun hvw x)
  exact (Set.eqOn_univ v w).mpr hvw

theorem fderiv_compat_of_eq' {f : B × F → B →L[ℝ] F}
      (hv : SmoothFunction (dimB := dimB) (dimF := dimF) v)
      (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
      (hdvf_eq : ∀ x, fderiv ℝ v x = f (x, v x)) :
    ∀ (x : B) d1 d2, fderiv ℝ (fun x ↦ f (x, v x)) x d1 d2 = fderiv ℝ (fun x ↦ f (x, v x)) x d2 d1 := by
  intro x d1 d2
  rw [(funext hdvf_eq).symm]
  have y := v x
  have sym_fd := (hv.contDiffAt (x := x)).isSymmSndFDerivAt minSmoothness_nat_le_inf d1 d2
  exact sym_fd

omit v in
theorem fderiv_compat_of_eq {f : B × F → B →L[ℝ] F}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F)
      (hv : SmoothFunction (dimB := dimB) (dimF := dimF) v),
        v x0 = y ∧ (∀ x, fderiv ℝ v x = f (x, v x))) :
    ∀ x y d1 d2, (fderiv ℝ f (x, y) (d1, 0) d2 + (fderiv ℝ f (x, y)).comp (.prodMap (ContinuousLinearMap.id ℝ B) (f (x, y))) (d2, 0) d1
                = fderiv ℝ f (x, y) (d1, 0) d2 + (fderiv ℝ f (x, y)).comp (.prodMap (ContinuousLinearMap.id ℝ B) (f (x, y))) (d2, 0) d1) := by
  intro x0 y d1 d2
  obtain ⟨v, hv, hy, hf_eq⟩ := hf_eq x0 y
  have hf_ext_eq := (comp_def f _).symm ▸ funext hf_eq
  have hdf_ext_eq := fderiv_congr (dimB := dimB) (dimF := dimB * dimF) hf_ext_eq
  have hdf_eq := congr_fun hdf_ext_eq x0
  rw [fderiv_comp] at hdf_eq
  -- seems almost done
  sorry


end FrobLoc
