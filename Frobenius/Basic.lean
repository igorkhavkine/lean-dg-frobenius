import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.ContinuousMap.Bounded.Basic

noncomputable section FrobLoc

open Classical Function ContDiff

theorem fderiv_congr
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {v w : E → F} (hvw : v = w) : fderiv 𝕜 v = fderiv 𝕜 w := by
  funext x
  rw [fderiv_def, fderiv_def]
  refine fderivWithin_congr ?_ (congr_fun hvw x)
  exact (Set.eqOn_univ v w).mpr hvw

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

abbrev TotalFderivCompat (f : B × F → B →L[ℝ] F) := ∀ x y d1 d2,
  (fderiv ℝ f (x, y) (d1, 0) d2 + (fderiv ℝ f (x, y)) (0, f (x, y) d1) d2
  = fderiv ℝ f (x, y) (d2, 0) d1 + (fderiv ℝ f (x, y)) (0, f (x, y) d2) d1)

theorem fderiv_compat_of_eq' {f : B × F → B →L[ℝ] F}
      (hv : SmoothFunction (dimB := dimB) (dimF := dimF) v)
      (_hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
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
      (_hv : SmoothFunction (dimB := dimB) (dimF := dimF) v),
        v x0 = y ∧ (∀ x, fderiv ℝ v x = f (x, v x))) :
    TotalFderivCompat f := by
  intro x0 y d1 d2
  replace ⟨v, hv, hy, hf_eq⟩ := hf_eq x0 y
  unfold SmoothFunction at hf hv
  replace hf_eq := (comp_def f _).symm ▸ funext hf_eq
  --have hdf_eq := fderiv_congr ℝ hf_eq
  have hdf_eq := Eq.refl (fderiv ℝ (fderiv ℝ v)); nth_rw 2 [hf_eq] at hdf_eq -- instead of fderiv_congr
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
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F) (s : Set B) (_hs : s ∈ nhds x0)
      (_hv : SmoothFunctionOn (dimB := dimB) (dimF := dimF) v (interior s)),
        v x0 = y ∧ (∀ x ∈ s, (fderivWithin ℝ v (interior s)) x = f (x, v x))) :
    TotalFderivCompat f := by
  intro x0 y d1 d2
  replace ⟨v, s, hs, hv, hy, hf_eq⟩ := hf_eq x0 y
  have hx0 := mem_of_mem_nhds hs
  have hx0i : x0 ∈ interior s := mem_interior_iff_mem_nhds.mpr hs
  have hsi : interior s ⊆ s := interior_subset
  have hudsi : UniqueDiffWithinAt ℝ (interior s) x0 := isOpen_interior.uniqueDiffWithinAt hx0i
  unfold SmoothFunction at hf
  unfold SmoothFunctionOn at hv
  -- prepare hf_eq for the application of the chain rule
  replace hf_eq : Set.EqOn (fderivWithin ℝ v (interior s)) (fun x ↦ f (x, v x)) (interior s) := by
    unfold Set.EqOn
    intro x hx
    exact hf_eq x (Set.mem_of_subset_of_mem hsi hx)
  replace hf_eq := (comp_def f _).symm ▸ hf_eq
  have hdf_eq := fderivWithin_congr (𝕜 := ℝ) hf_eq (hf_eq hx0i)
  -- prepare the hypotheses for and use the symmetry of the second derivatives
  have hdf_left := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d2) d1
  have hdf_right := DFunLike.congr_fun (DFunLike.congr_fun hdf_eq d1) d2
  have sym_vdd := by
    apply (hv.contDiffWithinAt hx0i).isSymmSndFDerivWithinAt
      minSmoothness_nat_le_inf
      isOpen_interior.uniqueDiffOn
      (by rw [interior_interior]; exact Set.mem_of_subset_of_mem subset_closure hx0i)
      hx0i d2 d1
  replace hdf_eq := calc
    _ = _ := hdf_left.symm
    _ = _ := sym_vdd
    _ = _ := hdf_right
  have hf_x0 := (hf.contDiffAt (x := (x0, v x0))).differentiableAt (by norm_num)
  have hidv_x0 := DifferentiableAt.prodMk (x := x0)
      differentiableAt_id'
      ((hv.contDiffAt (interior_mem_nhds.mpr hs)).differentiableAt (by norm_num))
  -- apply the chain rule, with simplifications
  rw [fderivWithin_comp (t := Set.univ) (hxs := hudsi)] at hdf_eq
  case hg => exact hf_x0.differentiableWithinAt
  case hf => exact hidv_x0.differentiableWithinAt
  case h => exact Set.mapsTo_univ _ _
  rw [DifferentiableWithinAt.fderivWithin_prodMk (hxs := hudsi)] at hdf_eq
  case hf₁ => exact differentiableWithinAt_id'
  case hf₂ => exact (hv.contDiffWithinAt hx0i).differentiableWithinAt (by norm_num)
  rw [fderivWithin_id' hudsi] at hdf_eq
  simp only [ContinuousLinearMap.coe_comp', comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq] at hdf_eq
  -- expand the chainrule in both arguments
  have d1_add : (d1, ((fderivWithin ℝ v (interior s)) x0) d1) = (d1,0) + (0,((fderivWithin ℝ v (interior s)) x0) d1) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have d2_add : (d2, (fderivWithin ℝ v (interior s) x0) d2) = (d2,0) + (0,(fderivWithin ℝ v (interior s) x0) d2) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  replace hdf_eq := d1_add ▸ d2_add ▸ hdf_eq
  simp only [hf_eq, comp_def, hy, map_add, ContinuousLinearMap.add_apply] at hdf_eq
  rw [hf_eq hx0i, comp_apply, hy] at hdf_eq
  simp only [fderiv_def]
  -- after simplifying the chain rule we have the exact result
  exact hdf_eq.symm


lemma unique_sol_of_fderiv_compat {f : B × F → B →L[ℝ] F}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hdf : TotalFderivCompat f) {x0 : B} {y : F} {s : Set B}
  {hs : s ∈ nhds x0} {v : B → F}
  (v_init : v x0 = y)
  (v_sol : ∀ x ∈ s, (fderivWithin ℝ v (interior s)) x = f (x, v x))
  : SmoothFunctionOn (dimB := dimB) (dimF := dimF) v (interior s)
  := sorry


lemma deriv_to_partial
  {v : ℝ → BoundedContinuousFunction B F} {t : ℝ}
  {v' : BoundedContinuousFunction B F} {D : Set ℝ}
  (hd : HasDerivWithinAt v v' D t)
  : ∀ x : B, HasDerivWithinAt (fun s => v s x) (v' x) D t
  := by
    intro x
    rw [hasDerivWithinAt_iff_isLittleO]
    rw [hasDerivWithinAt_iff_isLittleO] at hd

    have norm_littleo_sup
      : (fun s => v s x - v t x - (s-t) • (v' x)) =O[nhdsWithin t D] (fun s => v s - v t - (s-t) • v')
      := by
        rw [Asymptotics.isBigO_iff_isBigOWith]
        use 1
        rw [Asymptotics.IsBigOWith_def]
        apply eventually_nhdsWithin_of_forall
        intro s hs
        rw [one_mul]
        have apply_distr :
          v s x - v t x - (s-t) • (v' x) = (v s - v t - (s-t) • v') x
          := by simp
        rw [apply_distr]
        apply BoundedContinuousFunction.norm_coe_le_norm

    exact (Asymptotics.IsBigO.trans_isLittleO norm_littleo_sup hd)


lemma deriv_arg_swap
  (v : ℝ → BoundedContinuousFunction B F)
  (x : B) {t : ℝ} (ht : t ∈ Set.Icc (-1) 1)
  {v' : BoundedContinuousFunction B F}
  (hd : HasDerivWithinAt v v' (Set.Icc (-1) 1) t)
  : derivWithin v (Set.Icc (-1) 1) t x = derivWithin (fun s => v s x) (Set.Icc (-1) 1) t
  := by
    have hd' := deriv_to_partial hd x
    rw [hd.derivWithin]
    swap
    apply uniqueDiffOn_Icc
    linarith
    exact ht
    rw [hd'.derivWithin]
    apply uniqueDiffOn_Icc
    linarith
    exact ht

-- a try at proving the local existence theorem
omit v in
theorem exists_sol_of_fderiv_compat {f : B × F → B →L[ℝ] F}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hdf : TotalFderivCompat f) :
      ∀ (x0 : B) (y : F), ∃ (s : Set B) (_hs : s ∈ nhds x0) (v : B → F)
      (_hv : SmoothFunctionOn (dimB := dimB) (dimF := dimF) v (interior s)),
        v x0 = y ∧ (∀ x ∈ s, (fderivWithin ℝ v (interior s)) x = f (x, v x))
    := by
  intro x0 y
  -- use Picard-Lindelöf here
  -- set up candidate solution by integrating radially from x0
  have ex1 := fun (z : F → ℝ → F) x t => deriv (z y) t = (f (x0 + t • (x-x0), z y t)) x
  have ex2 := fun (v : B → F) (z : F → ℝ → F) (x : B) t => z y t = v (x0 + t • (x-x0))
  --let BtoF := B →ᵇ F -- XXX: →ᵇ notation not working for some reason
  let BtoF := BoundedContinuousFunction B F
  let ff (t' : ℝ) (y' : BtoF) : BtoF := by
    --unfold BtoF
    constructor; swap
    · constructor; swap
      · exact fun (x : B) => (f (x0 + t' • (x-x0), y' x)) (x-x0)
      sorry
    sorry
  have hpl : IsPicardLindelof ff (-1) 0 1 (.const _ y) ?L ?R ?C := sorry
  case L => sorry
  case R => sorry
  case C => sorry
  have ex3 := hpl.exists_forall_hasDerivWithinAt_Icc_eq
    (BoundedContinuousFunction.const B y)
  obtain ⟨v', hv'y, hv'⟩ := ex3
  --replace hv' := BAll.imp_right
  --  (fun t ht => HasDerivWithinAt.derivWithin
  --    (hxs := (uniqueDiffOn_Icc (by norm_num : -1 < (1:ℝ))).uniqueDiffWithinAt ht))
  --  hv'

  have v'_deriv_eq := fun t (ht : t ∈ _) => -- rewrite HasDerivWithinAt as equality
    HasDerivWithinAt.derivWithin
      (hv' t ht)
      (hxs := (uniqueDiffOn_Icc (by norm_num : -1 < (1:ℝ))).uniqueDiffWithinAt ht)

  let v := v' 1

  -- Avoid shadowing `v`, since this forgets the bounded continuous structure.
  --
  have ⟨⟨_, hvc⟩, ⟨vC,hvb⟩⟩ := v

  simp only at hvb
  have hs := Metric.closedBall_mem_nhds x0 (?hR : (0:ℝ) < ?R)
  set s := Metric.closedBall x0 ?R -- XXX: what radius R to use, same as in hpl?
  case R => sorry
  case hR => sorry
  use s, hs
  use v
  use ?hvsm -- XXX: delay proving that v is smooth
  case hvsm => sorry
  -- check that the candidate solution is indeed a solution
  constructor
  case left =>
    -- check initial condition from hv'y ?
    -- maybe need to do more, like get explicit constant solution for (x-x0)=0?
    have congr_bcf {a b : BtoF} (_ : a = b) : ∀ x, a.toFun x = b.toFun x := sorry
    have ex4 := fun t (ht : t ∈ _) => congr_bcf (v'_deriv_eq t ht)
    -- XXX: why is there no `ball_forall_swap`?
    replace ex4 := forall_swap.mp (fun t => imp_forall_iff.mp (ex4 t))
    unfold ff at ex4
    --simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap, zero_smul, add_zero] at ex4
    simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at ex4
    replace ex4 := ex4 x0
    simp only [sub_self, smul_zero, add_zero, and_imp, map_zero] at ex4
    have ex5 := fun t (ht : t ∈ Set.Icc (-1) 1) => ex4 t ht

    have ex6 := fun t (ht : t ∈ Set.Icc (-1) 1) => (deriv_arg_swap v' x0 ht (hv' t ht)) ▸ ex5 t ht
    have ex7 := constant_of_derivWithin_zero  ?v'diff (by
      intro t ht
      exact (ex6 t (Set.mem_Icc_of_Ico ht))
      )
    case v'diff => sorry
    have := calc
      v' 1 x0 = v' (-1:ℝ) x0 := by exact ex7 1 (by norm_num)
      _       = v' 0 x0 := by exact (ex7 0 (by norm_num)).symm
      _       = y := by rw [hv'y]; simp only [BoundedContinuousFunction.const_apply]
    convert this
  case right =>
    -- need a special argument here
    sorry

#check BoundedContinuousFunction
#check IsPicardLindelof
#check IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq
#check exists_isIntegralCurveAt_of_contMDiffAt

end FrobLoc
