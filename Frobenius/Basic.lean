import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Prod

section FrobLoc

open Function ContDiff

-- bundle ordinary real vector spaces
class oVectorSpace (V : Type*) (dim : ℕ) extends
  AddCommGroup V, Module ℝ V, FiniteDimensional ℝ V

class oNormedSpace (V : Type*) (dim : ℕ) extends
  NormedAddCommGroup V, NormedSpace ℝ V, FiniteDimensional ℝ V

abbrev SmoothFunction {B F : Type*} {dimB dimF : ℕ} [oNormedSpace B dimB] [oNormedSpace F dimF] (f : B → F)
  := ContDiff ℝ ∞ f

abbrev SmoothFunctionOn {B F : Type*} {dimB dimF : ℕ} [oNormedSpace B dimB] [oNormedSpace F dimF] (f : B → F) (s : Set B)
  := ContDiffOn ℝ ∞ f s

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

-- Existence of a solution v of fderiv ℝ v x = f (x, v x)) with arbitrary
-- initial data v x0 = y at any point x0 (hypothesis could be weakened to existence
-- of local solution only) implies a differential compatibility condition
-- on f (x, y) ("vanishing curvature").
omit v in
theorem fderiv_compat_of_eq {f : B × F → B →L[ℝ] F}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F)
      (hv : SmoothFunction (dimB := dimB) (dimF := dimF) v),
        v x0 = y ∧ (∀ x, fderiv ℝ v x = f (x, v x))) :
    ∀ x y d1 d2, (fderiv ℝ f (x, y) (d1, 0) d2
                  + (fderiv ℝ f (x, y)) (0, f (x, y) d1) d2
                = fderiv ℝ f (x, y) (d2, 0) d1
                  + (fderiv ℝ f (x, y)) (0, f (x, y) d2) d1) := by
  intro x0 y d1 d2
  replace ⟨v, hv, hy, hf_eq⟩ := hf_eq x0 y
  unfold SmoothFunction at hf hv
  replace hf_eq := (comp_def f _).symm ▸ funext hf_eq
  replace hdf_eq := fderiv_congr (dimB := dimB) (dimF := dimB * dimF) hf_eq
  replace hdf_eq := (congr_fun hdf_eq x0)
  have hdf_left := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d2) d1
  have hdf_right := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d1) d2
  have sym_vdd := (hv.contDiffAt (x := x0)).isSymmSndFDerivAt minSmoothness_nat_le_inf d2 d1
  replace hdf_eq := calc
    _ = _ := hdf_left.symm
    _ = _ := sym_vdd
    _ = _ := hdf_right
  have hf_x0 := (hf.contDiffAt (x := (x0, v x0))).differentiableAt (by norm_num)
  have hidv_x0 := DifferentiableAt.prodMk (x := x0)
      differentiableAt_id'
      ((contDiffAt hv).differentiableAt (by norm_num))
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk, fderiv_id'] at hdf_eq
  case hg => exact hf_x0
  case hf => exact hidv_x0
  case hf₁ => exact differentiableAt_id'
  case hf₂ => exact hv.contDiffAt.differentiableAt (by norm_num)
  simp only [ContinuousLinearMap.coe_comp', comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq] at hdf_eq
  have d1_add : (d1, (fderiv ℝ v x0) d1) = (d1,0) + (0,(fderiv ℝ v x0) d1) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have d2_add : (d2, (fderiv ℝ v x0) d2) = (d2,0) + (0,(fderiv ℝ v x0) d2) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  replace hdf_eq := d1_add ▸ d2_add ▸ hdf_eq
  simp only [hf_eq, comp_def, hy, map_add, ContinuousLinearMap.add_apply] at hdf_eq
  exact hdf_eq.symm

-- Existence of a local solution v of fderiv ℝ v x = f (x, v x)) with arbitrary
-- initial data v x0 = y at any point x0 implies a differential compatibility condition
-- on f (x, y) ("vanishing curvature").
-- [to clean up and fill in the sorry-s]
omit v in
theorem fderiv_compat_of_eqOn {f : B × F → B →L[ℝ] F}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F) (s : Set B) (hs : s ∈ nhds x0)
      (hv : SmoothFunctionOn (dimB := dimB) (dimF := dimF) v s),
        v x0 = y ∧ (∀ x ∈ s, (fderivWithin ℝ v s) x = f (x, v x))) :
    ∀ x y d1 d2, (fderiv ℝ f (x, y) (d1, 0) d2
                  + (fderiv ℝ f (x, y)) (0, f (x, y) d1) d2
                = fderiv ℝ f (x, y) (d2, 0) d1
                  + (fderiv ℝ f (x, y)) (0, f (x, y) d2) d1) := by
  intro x0 y d1 d2
  replace ⟨v, s, hs, hv, hy, hf_eq⟩ := hf_eq x0 y
  have hx0 := mem_of_mem_nhds hs
  --have hx0y : (x0, y) ∈ s.prod Set.univ := by sorry
  unfold SmoothFunction at hf
  unfold SmoothFunctionOn at hv
  replace hf_eq : Set.EqOn (fderivWithin ℝ v s) (fun x ↦ f (x, v x)) s := by
    unfold Set.EqOn
    exact hf_eq
  replace hf_eq := (comp_def f _).symm ▸ hf_eq
  have hdf_eq := fderivWithin_congr (𝕜 := ℝ) hf_eq (hf_eq hx0)
  have hdf_left := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d2) d1
  have hdf_right := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d1) d2
  have sym_vdd := by
    apply (hv.contDiffWithinAt hx0).isSymmSndFDerivWithinAt minSmoothness_nat_le_inf ?_ ?_ hx0 d2 d1
    · sorry
    · have := mem_interior_iff_mem_nhds.mpr hs
      refine mem_closure_iff_clusterPt.mpr ?_
      unfold ClusterPt
      sorry
  replace hdf_eq := calc
    _ = _ := hdf_left.symm
    _ = _ := sym_vdd
    _ = _ := hdf_right
  have hf_x0 := (hf.contDiffAt (x := (x0, v x0))).differentiableAt (by norm_num)
  have hidv_x0 := DifferentiableAt.prodMk (x := x0)
      differentiableAt_id'
      ((hv.contDiffAt hs).differentiableAt (by norm_num))
  rw [fderivWithin_comp (t := s.prod Set.univ)] at hdf_eq
  rw [DifferentiableWithinAt.fderivWithin_prodMk, fderivWithin_id'] at hdf_eq
  -- extra hypotheses needed to apply the last rewritings
  case hg => sorry --exact hf_x0
  case hf => sorry --exact hidv_x0
  case hf₁ => sorry --exact differentiableAt_id'
  case hf₂ => sorry --exact (hv.contDiffAt hs).differentiableAt (by norm_num)
  case hxs => sorry
  case h => sorry
  case hxs => sorry
  swap; · sorry
  simp only [ContinuousLinearMap.coe_comp', comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq] at hdf_eq
  have d1_add : (d1, ((fderivWithin ℝ v s) x0) d1) = (d1,0) + (0,((fderivWithin ℝ v s) x0) d1) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have d2_add : (d2, (fderivWithin ℝ v s x0) d2) = (d2,0) + (0,(fderivWithin ℝ v s x0) d2) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  replace hdf_eq := d1_add ▸ d2_add ▸ hdf_eq
  simp only [hf_eq, comp_def, hy, map_add, ContinuousLinearMap.add_apply] at hdf_eq
  have hf_subset := fderivWithin_subset
    (𝕜 := ℝ) (f := f) (x := (x0, y))
    (s.prod Set.univ).subset_univ
    (uniqueDiffWithinAt_of_mem_nhds (prod_mem_nhds hs Filter.univ_mem))
    ((hf.contDiffAt (x := (x0, y))).differentiableWithinAt (by norm_num))

  rw [hf_subset, hf_eq hx0, comp_apply, hy] at hdf_eq
  simp only [fderiv_def]
  convert hdf_eq.symm

end FrobLoc
