import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Frobenius.Utils

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

local instance : oNormedSpace (ℝ × B × F) (1 + dimB + dimF) := by
  constructor

noncomputable local instance : oNormedSpace (B →L[ℝ] F) (dimB * dimF) := by
  constructor

local instance : oNormedSpace ℝ 1 := by
  constructor

local instance : oNormedSpace (BoundedContinuousFunction B F) (dimB * dimF) := by
  sorry

local instance : oNormedSpace ((BoundedContinuousFunction B F) → (BoundedContinuousFunction B F)) (dimB * dimF * dimB * dimF) := by
  sorry

abbrev minSmoothness_nat_le_inf {n : ℕ} : minSmoothness ℝ n ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact ENat.LEInfty.out


abbrev Curvature (g : B × F → B →L[ℝ] F) p d1 d2 :=
  (fderiv ℝ g p (d1, 0) d2 + (fderiv ℝ g p) (0, g p d1) d2
  - (fderiv ℝ g p (d2, 0) d1 + (fderiv ℝ g p) (0, g p d2) d1))

abbrev TotalFderivCompat (g : B × F → B →L[ℝ] F) (U : Set (B × F)) :=
  ∀ p ∈ U, ∀ d1 d2, Curvature g p d1 d2 = 0

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
theorem fderiv_compat_of_eq {f : B × F → B →L[ℝ] F} {U : Set (B × F)}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F)
      (_hv : SmoothFunction (dimB := dimB) (dimF := dimF) v),
        v x0 = y ∧ (∀ x, fderiv ℝ v x = f (x, v x))) :
    TotalFderivCompat f U := by
  intro p hp d1 d2
  replace ⟨x0, y⟩ := p
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
  unfold Curvature
  rw [sub_eq_zero]
  exact hdf_eq.symm

-- Existence of a local solution v of fderiv ℝ v x = f (x, v x)) with arbitrary
-- initial data v x0 = y at any point x0 implies a differential compatibility condition
-- on f (x, y) ("vanishing curvature").
-- [to clean up and fill in the sorry-s]
omit v in
theorem fderiv_compat_of_eqOn {f : B × F → B →L[ℝ] F} {U : Set (B × F)}
  (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
  (hf_eq : ∀ (x0 : B) (y : F), ∃ (v : B → F) (s : Set B) (_hs : s ∈ nhds x0)
      (_hv : SmoothFunctionOn (dimB := dimB) (dimF := dimF) v (interior s)),
        v x0 = y ∧ (∀ x ∈ s, (fderivWithin ℝ v (interior s)) x = f (x, v x))) :
    TotalFderivCompat f U := by
  intro p hp d1 d2
  replace ⟨x0, y⟩ := p
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
  rw [← fderiv_def] at hdf_eq
  unfold Curvature
  rw [sub_eq_zero]
  exact hdf_eq.symm


-- BLACKBOX FOR NOW
--
-- lemma smooth_picard_lindelof {f : B × F → B →L[ℝ] F}
--   (hf : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) f)
--   (hdf : TotalFderivCompat f) {x0 : B} {y : F} {s : Set B}
--   {hs : s ∈ nhds x0}
--   (D : Set ℝ)
--   : ∃ v : ℝ × B → F,
--     v (0, x0) = y
--   ∧ (∀ x ∈ s, ∀ t ∈ D, HasFDerivWithinAt (fun t => v (t, x)) (fun t => f (x, v (t, x))) D t)
--   ∧ SmoothFunctionOn (dimB := 1+dimB) (dimF := dimF) v (interior (s × D))
--   := sorry


lemma deriv_to_partial
  {v : ℝ → BoundedContinuousFunction B F} {t : ℝ}
  {ζ : BoundedContinuousFunction B F} {D : Set ℝ}
  (hd : HasDerivWithinAt v ζ D t)
  : ∀ x : B, HasDerivWithinAt (fun s => v s x) (ζ x) D t
  := by
    intro x
    rw [hasDerivWithinAt_iff_isLittleO]
    rw [hasDerivWithinAt_iff_isLittleO] at hd

    have norm_littleo_sup
      : (fun s => v s x - v t x - (s-t) • (ζ x)) =O[nhdsWithin t D] (fun s => v s - v t - (s-t) • ζ)
      := by
        rw [Asymptotics.isBigO_iff_isBigOWith]
        use 1
        rw [Asymptotics.IsBigOWith_def]
        apply eventually_nhdsWithin_of_forall
        intro s hs
        rw [one_mul]
        have apply_distr :
          v s x - v t x - (s-t) • (ζ x) = (v s - v t - (s-t) • ζ) x
          := by simp
        rw [apply_distr]
        apply BoundedContinuousFunction.norm_coe_le_norm

    exact (Asymptotics.IsBigO.trans_isLittleO norm_littleo_sup hd)


lemma deriv_arg_swap
  (v : ℝ → BoundedContinuousFunction B F)
  (x : B) {t : ℝ} {a b : ℝ} (lt : a < b) (ht : t ∈ Set.Icc a b)
  {ζ : BoundedContinuousFunction B F}
  (hd : HasDerivWithinAt v ζ (Set.Icc a b) t)
  : derivWithin v (Set.Icc a b) t x = derivWithin (fun s => v s x) (Set.Icc a b) t
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
theorem exists_sol_of_fderiv_compat {g : B × F → B →L[ℝ] F}
  (g_smooth : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) g)
  (g_compat : TotalFderivCompat g Set.univ) :
      ∀ (x0 : B) (z : F), ∃ (s : Set B) (hs : s ∈ nhds x0) (w : B → F)
      (w_smooth : SmoothFunctionOn (dimB := dimB) (dimF := dimF) w (interior s)),
        w x0 = z ∧ (∀ x ∈ s, (fderivWithin ℝ w (interior s)) x = g (x, w x))
    := by
  intro x0 y
  -- use Picard-Lindelöf here
  -- set up candidate solution by integrating radially from x0
  have ex1 := fun (z : F → ℝ → F) x t => deriv (z y) t = (g (x0 + t • (x-x0), z y t)) x
  have ex2 := fun (v : B → F) (z : F → ℝ → F) (x : B) t => z y t = v (x0 + t • (x-x0))
  --let BtoF := B →ᵇ F -- XXX: →ᵇ notation not working for some reason
  let BtoF := BoundedContinuousFunction B F
  let radial_g : ℝ → BtoF → BtoF := by
    intro t' y'
    constructor
    case toContinuousMap := by
      constructor
      case toFun := fun (x : B) => (g (x0 + t' • (x-x0), y' x)) (x-x0)
      sorry
    case map_bounded' := sorry

  have radial_g_smooth : SmoothFunction (dimB := 1) (dimF := dimB*dimF*dimB*dimF) radial_g := by
    sorry

  have radial_g_lipschitz :=
    ContDiffAt.exists_lipschitzOnWith (by
      unfold SmoothFunction at radial_g_smooth
      rw [contDiff_iff_contDiffAt] at radial_g_smooth
      have diff_at_0 := radial_g_smooth 0
      apply (ContDiffAt.of_le diff_at_0)
      norm_num
    )

  have hpl : IsPicardLindelof radial_g (-1) 0 1 (.const _ y) ?L ?R ?C := by
    -- constructor
    -- norm_num
    -- case hR := sorry
    sorry
  case L => sorry
  case R => sorry
  case C => sorry
  have ex3 := hpl.exists_forall_hasDerivWithinAt_Icc_eq
    (BoundedContinuousFunction.const B y)
  obtain ⟨ζ, hζy, hζ⟩ := ex3
  --replace hζ := BAll.imp_right
  --  (fun t ht => HasDerivWithinAt.derivWithin
  --    (hxs := (uniqueDiffOn_Icc (by norm_num : -1 < (1:ℝ))).uniqueDiffWithinAt ht))
  --  hζ

  have ζ_deriv_eq := fun t (ht : t ∈ _) => -- rewrite HasDerivWithinAt as equality
    HasDerivWithinAt.derivWithin
      (hζ t ht)
      (hxs := (uniqueDiffOn_Icc (by norm_num : -1 < (1:ℝ))).uniqueDiffWithinAt ht)

  let v := ζ 1

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
    -- check initial condition from hζy ?
    -- maybe need to do more, like get explicit constant solution for (x-x0)=0?
    have congr_bcf {a b : BtoF} (_ : a = b) : ∀ x, a.toFun x = b.toFun x := sorry
    have ex4 := fun t (ht : t ∈ _) => congr_bcf (ζ_deriv_eq t ht)
    -- XXX: why is there no `ball_forall_swap`?
    replace ex4 := forall_swap.mp (fun t => imp_forall_iff.mp (ex4 t))
    unfold radial_g at ex4
    --simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap, zero_smul, add_zero] at ex4
    simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at ex4
    replace ex4 := ex4 x0
    simp only [sub_self, smul_zero, add_zero, and_imp, map_zero] at ex4
    have ex5 := fun t (ht : t ∈ Set.Icc (-1) 1) => ex4 t ht

    have ex6 := fun t (ht : t ∈ Set.Icc (-1) 1) => (deriv_arg_swap ζ x0 (by linarith) ht (hζ t ht)) ▸ ex5 t ht
    have ex7 := constant_of_derivWithin_zero  ?ζdiff (by
      intro t ht
      exact (ex6 t (Set.mem_Icc_of_Ico ht))
      )
    case ζdiff => sorry
    have := calc
      ζ 1 x0 = ζ (-1:ℝ) x0 := by exact ex7 1 (by norm_num)
      _       = ζ 0 x0 := by exact (ex7 0 (by norm_num)).symm
      _       = y := by rw [hζy]; simp only [BoundedContinuousFunction.const_apply]
    convert this
  case right =>
    intro x hx
    unfold radial_g at ζ_deriv_eq
    -- have ζ_deriv_at_1 := ζ_deriv_eq 1 (by norm_num)
    -- have ζ_deriv_swap := (deriv_arg_swap ζ x (by norm_num) (hζ 1 (by norm_num)))

    -- TODO: can we do this more nicely?
    --
    -- let coerce (f: BtoF) := f.toFun
    -- apply (congr_arg coerce) at ζ_deriv_at_1
    -- unfold coerce at ζ_deriv_at_1
    -- simp at ζ_deriv_at_1

    have extra_smoothness : ∀ s, @SmoothFunction B F dimB dimF _ _ (ζ s) := by sorry

    -- TODO: figure out domains of diff'ability
    --
    let η (t: ℝ) (b: B) := (fderiv ℝ (ζ t) b) - (t • g (x0 + t • (x - x0), ζ t b))

    /-
    \frac{\partial}{\partial t} \eta_a^c(t,y,z)
   = \left. \eta_a^{c'}(t,y,z) y^{a'} \frac{\partial}{\partial z^{c'}} g_{a'}^c(ty,z) \right|_{z=\zeta(t,y,z)}
   -/

    -- TODO: z argument + calc
    --
    have η_eq : ∀ t b a, derivWithin η (Set.Icc (-1) 1) t b a = fderiv ℝ (fun z => g (x0 + t • (x-x0), z) b) (ζ t b) (η t b a)
      := by sorry

    sorry


lemma η_unique
    {η : ℝ × B × F → B →L[ℝ] F} {g : B × F → B →L[ℝ] F} {sb : Set B} {sf : Set F} {y0 : B}
    (hy0 : y0 ∈ sb)
    {ζ : ℝ × B × F → F} {ε : ℝ} (hε : ε > 0)
    {u : Set ℝ} (hu : Set.Icc (-ε) (1+ε) ⊆ u) (u_open : IsOpen u)
    (ζ_init : ∀ y z, ζ (0, y, z) = z)
    (ζ_eq : ∀ y ∈ sb, ∀ z ∈ sf, ∀ t ∈ Set.Icc (-ε) (1+ε), HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
    (η_init : ∀ y ∈ sb, ∀ z ∈ sf, η (0, y, z) = 0)
    (η_eq : ∀ t ∈ Set.Icc (-ε) (1+ε), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, HasDerivAt (fun s => η (s, y, z) b) (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z)) (η (t, y, z) b)) t)
    : ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, Set.EqOn (η ⟨·, y, z⟩ b) (fun x => 0) (Set.Icc (-ε) (1+ε))
    := by
  intro y hy z hz b

  have zero_in_set : 0 ∈ Set.Ioo (-ε) (1+ε) := by
    simp only [Set.mem_Ioo, Left.neg_neg_iff]
    constructor
    · exact hε
    · rw [← add_zero (a := 0)]
      exact add_lt_add_of_le_of_lt (by exact zero_le_one' ℝ) hε

  let lip_bounds (t : ℝ) := ‖(fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z)))‖
  have lip_bounds_cont : ContinuousOn lip_bounds (Set.Icc (-ε) (1+ε)) := by
    have : ContDiff ℝ 1 (uncurry fun (t:ℝ) z' => g (y0 + t • (y-y0), z') y) := sorry
    unfold lip_bounds
    apply ContinuousOn.norm
    apply Continuous.continuousOn
    apply Continuous.fderiv this _ (by trivial)   -- XXX: how to do this?
    exact HasDerivAt.continuousOn (ζ_eq y hy z hz)
  have icc01_cpt : IsCompact (Set.Icc (-ε) (1+ε)) := isCompact_Icc
  have total_bound := exists_nonneg_bound_of_continuousOn (f := lip_bounds) (E := ℝ) icc01_cpt lip_bounds_cont

  apply ODE_solution_unique_of_mem_Icc (v := fun t => (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z)))) (t₀ := 0) (s := fun _ => Set.univ)
  · intro t ht
    have := (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z))).lipschitz
    let K := Classical.choose total_bound
    let h := Classical.choose_spec total_bound
    replace h := h t (Set.mem_Icc_of_Ioo ht)
    unfold lip_bounds at h
    simp only [norm_norm] at h

    rw [lipschitzOnWith_univ]
    · unfold LipschitzWith
      unfold LipschitzWith at this
      intro a b
      replace this := this a b
      calc
        edist ((fderiv ℝ (fun z' ↦ (g (y0 + t • (y - y0), z')) y) (ζ (t, y, z))) a) ((fderiv ℝ (fun z' ↦ (g (y0 + t • (y - y0), z')) y) (ζ (t, y, z))) b)
          ≤ ↑‖fderiv ℝ (fun z' ↦ (g (y0 + t • (y - y0), z')) y) (ζ (t, y, z))‖₊ * edist a b := this
        _ ≤ K * edist a b := by
          have : 0 ≤ edist a b := sorry
          apply mul_le_mul_of_nonneg_right
          · rw [← coe_nnnorm] at h
            exact h -- ???
          · trivial
  · exact zero_in_set
  · exact HasDerivAt.continuousOn (by
      intro t ht
      exact η_eq t ht y hy z hz b)
  · intro t ht
    exact η_eq t (Set.mem_Icc_of_Ioo ht) y hy z hz b
  · exact fun t a ↦ trivial
  · exact continuousOn_const
  · intro t ht
    simp only [ContinuousLinearMap.map_zero]
    exact hasDerivAt_const t 0
  · exact fun t a ↦ trivial
  · have := η_init y hy z hz
    simp only [this, ContinuousLinearMap.zero_apply]

lemma exchange_deriv
   {X : Type*} {dimX : ℕ} [oNormedSpace X dimX]
   {f : ℝ × B → X} {sb : Set B} {sf : Set ℝ}
   (f_smooth : SmoothFunctionOn (dimB := 1+dimB) (dimF := dimX) f (sf ×ˢ sb))
   {q : B} {r : ℝ} (hq : q ∈ sb) (hr : r ∈ sf)
  : deriv (fun s => fderiv ℝ (fun x => f (s, x)) q) r = fderiv ℝ (fun x => deriv (fun s => f (s, x)) r) q
  := by sorry

-- use this if @[fun_prop] attribute is not included for some theorem in Mathlib
attribute [fun_prop] ContDiffOn.comp

/-
lemma calc9b
    {g : B × F → B →L[ℝ] F} {sb : Set B} {sf : Set F} {y0 : B}
    {ζ : ℝ × B × F → F} {η : ℝ × B × F → B →L[ℝ] F}
    (sb_open : IsOpen sb) (sf_open : IsOpen sf) (hy0 : y0 ∈ sb)
    (g_smooth : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) g)
    (g_compat : TotalFderivCompat g (sb ×ˢ sf))
    {u : Set ℝ} (hu : (Set.Icc 0 1) ⊆ u) (u_open : IsOpen u)
    (ζ_eq : ∀ t ∈ (Set.Icc 0 1), ∀ y ∈ sb, ∀ z ∈ sf, HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
    (η_eq : ∀ t y z, η ⟨t, y, z⟩ = (fderiv ℝ (fun x => ζ (t, x, z)) y) - t • g (y0 + t • (y - y0), ζ (t, y, z)))
    : ∀ r ∈ u, ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, deriv (fun s => (η (s, y, z)) b) r = (fderiv ℝ (fun z' ↦ (g (y0 + r • (y - y0), z')) y) (ζ (r, y, z))) ((η (r, y, z)) b)
    := by
  intro r hr y hy z hz b

  have ζ_smooth : SmoothFunctionOn (dimB := 1+dimB+dimF) (dimF := dimF) ζ (u ×ˢ sb ×ˢ sf) := by
      sorry

  let shift (x:B) (s:ℝ) := y0 + s • (x-y0)
  have shift_deriv : ∀ s ∈ u, (derivWithin (shift y) u s) = y - y0 := by sorry
    -- intro s hs
    -- unfold shift
    -- rw [
    --   derivWithin_const_add, derivWithin_smul_const differentiableWithinAt_id,
    --   derivWithin_id' _ _ (u_open.uniqueDiffWithinAt hs), one_smul
    -- ]

  unfold SmoothFunction at g_smooth

  have u_uniq : UniqueDiffWithinAt ℝ u r := u_open.uniqueDiffWithinAt hr

  have ζ_diff : DifferentiableWithinAt ℝ ζ (u ×ˢ sb ×ˢ sf) (r, y, z) := by sorry
    -- refine ζ_smooth.differentiableOn (by norm_num) (r, y, z) ?_
    -- simp [hr, hy, hz]

  have ζfst_diff : DifferentiableWithinAt ℝ (fun s => ζ ⟨s, y, z⟩) u r := by sorry
    -- apply ζ_diff.comp r
    -- · fun_prop
    -- · unfold Set.MapsTo
    --   simp [hy, hz]

  have g_diff : Differentiable ℝ g := g_smooth.differentiable (by norm_num)

  calc
    deriv (fun s => (η (s, y, z)) b) r =
    deriv (fun s => (fderiv ℝ (fun x => ζ ⟨s, x, z⟩) y) b - s • g ⟨shift y s, ζ ⟨s, y, z⟩⟩ b) r
      := rfl
    _ = (deriv (fun s => (fderiv ℝ (fun x => ζ ⟨s, x, z⟩) y) b) r)
      - (deriv (fun s => s • g ⟨shift y s, ζ ⟨s, y, z⟩⟩ b) r)
      := by
        stop
        rw [deriv_sub]
        · sorry
        · apply DifferentiableAt.smul
          · exact differentiableAt_id
          · -- fun_prop not working
            -- (stuck at `DifferentiableAt ℝ (fun s => ζ ⟨s, y, z⟩) r`, since it tries
            -- to prov `DifferentiableAt ℝ ζ (r, y, z)`)
            apply DifferentiableWithinAt.clm_apply
            apply DifferentiableWithinAt.comp
            swap
            apply DifferentiableWithinAt.prodMk
            · fun_prop
            · exact ζfst_diff
            · exact differentiableWithinAt_univ.mpr (g_smooth.differentiable (by norm_num) (shift y r, ζ (r, y, z)))
            · unfold Set.MapsTo
              simp only [Set.mem_univ, implies_true]
            · exact differentiableWithinAt_const b
    _ = (fderivWithin ℝ (fun x => derivWithin (fun s => ζ ⟨s, x, z⟩) u r) sb y b)
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩
      + r • (derivWithin (fun s => g ⟨shift y s, ζ ⟨s, y, z⟩⟩) u r)) b
      := by stop
        congr
        · have : SmoothFunctionOn (dimB := 1+dimB) (dimF := dimF) (fun (s,y) => ζ ⟨s, y, z⟩) (u ×ˢ sb) := by
            unfold SmoothFunctionOn
            apply ContDiffOn.comp ζ_smooth (by fun_prop)
            unfold Set.MapsTo
            simp only [Set.mem_prod, hz, and_true, imp_self, implies_true]
          apply exchange_deriv this hy hr
        · rw [derivWithin_smul, derivWithin_id', derivWithin_clm_apply, derivWithin_fun_const, add_comm]
          simp only [one_smul, Pi.zero_apply, map_zero, add_zero,
            ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
          have g'_diff : DifferentiableWithinAt ℝ (fun s ↦ (g (shift y s, ζ (s, y, z)))) u r := by
            apply DifferentiableWithinAt.comp r (differentiableWithinAt_univ.mpr (g_diff (shift y r, ζ (r, y, z))))
            · apply DifferentiableWithinAt.prodMk
              · fun_prop
              · exact ζfst_diff
            · unfold Set.MapsTo
              simp only [Set.mem_univ, implies_true]
          · exact g'_diff
          · apply differentiableWithinAt_const
          · exact u_uniq
          · exact differentiableWithinAt_id'
          -- XXX: `have` hypotheses get lost between "dots" ?!
          have g'_diff : DifferentiableWithinAt ℝ (fun s ↦ (g (shift y s, ζ (s, y, z)))) u r := sorry
          · apply DifferentiableWithinAt.clm_apply g'_diff (differentiableWithinAt_const b)
    _ = (fderivWithin ℝ (fun x => derivWithin (fun s => ζ ⟨s, x, z⟩) u r) sb y b)
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩
      + r • (fderiv ℝ g (shift y r, ζ ⟨r, y, z⟩) (derivWithin (fun s => (shift y s, ζ ⟨s, y, z⟩)) u r))) b
      := by stop
        congr
        rw [
          fderivWithin_comp'_derivWithin (differentiableWithinAt_univ.mpr (g_diff (shift y r, ζ (r, y, z)))),
          fderivWithin_univ
        ]
        · apply DifferentiableWithinAt.prodMk
          · fun_prop
          · exact ζfst_diff
        · unfold Set.MapsTo
          simp only [Set.mem_univ, implies_true]

    _ = (fderivWithin ℝ (fun x => derivWithin (fun s => ζ ⟨s, x, z⟩) u r) sb y b)
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩
      + r • (
        fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (fun s => (shift y s, ζ ⟨s, y, z⟩)) u r).1
        + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (derivWithin (fun s => (shift y s, ζ ⟨s, y, z⟩)) u r).2)) b
      := by stop
        congr
        sorry
    _ = (fderivWithin ℝ (fun x => derivWithin (fun s => ζ ⟨s, x, z⟩) u r) sb y b)
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩
      + r • (
        fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (shift y) u r)
        + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (derivWithin (fun s => ζ ⟨s, y, z⟩) u r))) b
      := by stop
        congr
        · rw [
            ← fderivWithin_derivWithin,
            DifferentiableWithinAt.fderivWithin_prodMk _ _ u_uniq
          ]
          simp only [ContinuousLinearMap.prod_apply]
          rw [fderivWithin_derivWithin]
          · fun_prop
          · sorry
        sorry
    _ = (fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z)) (x-y0)) sb y b)
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩
      + r • (
        fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (shift y) u r)
        + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) (y-y0)))) b
      := by  stop
        congr
        · sorry -- XXX: congr forgot the assumption x ∈ sb
        · exact (ζ_eq r hr y hy z hz).derivWithin u_uniq

    _ = (g (y0 + r • (y - y0), ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (shift y) u r) b
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) (y - y0)) b)) := by
      -- congr
      -- rw [fderivWithin_clm_apply]
      -- simp
      -- rw [fderivWithin_sub, fderivWithin_const_apply, fderivWithin_id']
      -- simp only [sub_zero, ContinuousLinearMap.coe_id', id_eq]
      repeat sorry

    _ = (g (y0 + r • (y - y0), ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (shift y) u r) b
          - (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r)))
          + (fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) (y - y0)) b
          - fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0)
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0)))) := by sorry
            -- congr
            -- · abel
            -- · abel

    _ = (g (y0 + r • (y - y0), ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          ((fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0))
          -- curvature
          + (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) (derivWithin (shift y) u r) b
          - (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) (y - y0)) b
          - fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0)))) := by
            sorry

    _ = (g (y0 + r • (y - y0), ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          ((fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0))
          -- curvature
          + (Curvature g ((shift y r), ζ ⟨r, y, z⟩) (derivWithin (shift y) u r) b))) := by
            -- congr 4
            -- unfold Curvature
            -- repeat rw [fderiv_partials]
            -- simp only [map_zero,
            --   add_zero, zero_add]
            -- repeat rw [deriv_shift]
            -- abel
            repeat sorry

    _ = (g (y0 + r • (y - y0), ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          ((fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (y0 + r • (y - y0), ζ (r, y, z)) b) (y - y0))
          -- curvature
          + (0))) := by
      -- unfold TotalFderivCompat at g_compat
      -- congr
      -- refine g_compat (shift y r, ζ (r, y, z)) ?_ (derivWithin (shift y) u r) b
      sorry

    _ = (g (shift y r, ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          ((fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0))
          -- curvature
          + (0))) := by sorry--rfl

    _ = (g (shift y r, ζ (r, y, z)) b + ((fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))))
      - (g ⟨shift y r, ζ ⟨r, y, z⟩⟩ b
        + r • (
          ((fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)))) := by
      sorry
      -- rw [add_zero]

    _ = fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0)
      - r • (
          (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (derivWithin (shift y) u r))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)) := by
      sorry
      -- abel

    _ = (fderivWithin ℝ (fun x => g (y0 + r • (x - y0), ζ (r, x, z))) sb y b (y-y0))
      - r • (
          (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (y - y0))
          + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)) := by
      sorry
      -- repeat rw [shift_deriv]
      -- exact hr

    _ = (
      fderivWithin ℝ g Set.univ (shift y r, ζ (r, y, z)) (r • b, fderivWithin ℝ (fun x => ζ ⟨r, x, z⟩) sb y b) (y-y0)
    )
    - r • (
        (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (y - y0))
        + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)) := by
      sorry
      -- congr
      -- rw [fderivWithin_comp' y (differentiableWithinAt_univ.mpr (g_diff (shift y r, ζ (r, y, z))))]
      -- rw [DifferentiableWithinAt.fderivWithin_prodMk]

    _ = (
      (fderiv ℝ (fun x' => g ⟨x', ζ ⟨r, y, z⟩⟩) (shift y r) (r • b) (y-y0))
      + (fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) (fderivWithin ℝ (fun x => ζ ⟨r, x, z⟩) sb y b) (y-y0))
    )
    - r • (
        (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (y - y0))
        + fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)) := by
        sorry

    _ = (
      r • (fderiv ℝ (fun x' => g ⟨x', ζ ⟨r, y, z⟩⟩) (shift y r) b (y-y0))
      + (fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) (fderivWithin ℝ (fun x => ζ ⟨r, x, z⟩) sb y b) (y-y0))
    )
    - (
        r • (fderiv ℝ (fun x' => g (x', ζ ⟨r, y, z⟩)) (shift y r) b (y - y0))
        + r • fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0)) := by
      sorry
      -- congr
      -- · simp only [map_smul]
      --   rfl
      -- · apply smul_add

    -- _ = (fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) (fderiv ℝ (fun x => ζ ⟨r, x, z⟩) y b) (y-y0))
    -- - r • fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (g (shift y r, ζ (r, y, z)) b) (y - y0) := by

    _ = (fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) (fderiv ℝ (fun x => ζ ⟨r, x, z⟩) y b) (y-y0))
    - fderiv ℝ (fun z' => g (shift y r, z')) (ζ ⟨r, y, z⟩) (r • g (shift y r, ζ (r, y, z)) b) (y - y0) := by
      abel
      congr
      exact
        Eq.symm
          (ContinuousLinearMap.map_smul₂ (fderiv ℝ (fun z' ↦ g (shift y r, z')) (ζ (r, y, z)))
            r ((g (shift y r, ζ (r, y, z))) b) (y - y0))

    _ = (fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) ((fderiv ℝ (fun x => ζ ⟨r, x, z⟩) y b) - r • g (shift y r, ζ (r, y, z)) b) (y-y0)) := by
      exact
        Eq.symm
          (ContinuousLinearMap.map_sub₂ (fderiv ℝ (fun z' ↦ g (shift y r, z')) (ζ (r, y, z)))
            ((fderiv ℝ (fun x ↦ ζ (r, x, z)) y) b)
            (r • (g (shift y r, ζ (r, y, z))) b) (y - y0))

    _ = fderiv ℝ (fun z' => g ⟨shift y r, z'⟩) (ζ ⟨r, y, z⟩) (η ⟨r, y, z⟩ b) (y-y0) := by rfl
-/

set_option maxHeartbeats 1000000 in
lemma Lemma9b
  {g : B × F → B →L[ℝ] F} {sb : Set B} {sf : Set F} {y0 : B}
  (sb_open : IsOpen sb) (sf_open : IsOpen sf) (hy0 : y0 ∈ sb)
  (g_smooth : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) g)
  (g_compat : TotalFderivCompat g (sb ×ˢ sf))
  {ζ : ℝ × B × F → F} {u : Set ℝ} (hu : (Set.Icc 0 1) ⊆ u) (u_open : IsOpen u)
  (ζ_init : ∀ y z, ζ (0, y, z) = z)
  (ζ_eq : ∀ t ∈ (Set.Icc 0 1), ∀ y ∈ sb, ∀ z ∈ sf, HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
  : ∀ t ∈ Set.Icc 0 1, ∀ y ∈ sb, ∀ z ∈ sf, fderiv ℝ (fun y' => ζ (t, y', z)) y = t • g (y0 + t • (y-y0), ζ (t, y, z)) := by
    intro t ht y hy z hz

    let η : ℝ × B × F → B →L[ℝ] F := by
      intro ⟨t, y, z⟩
      exact (fderiv ℝ (fun x => ζ (t, x, z)) y) - t • g (y0 + t • (y - y0), ζ (t, y, z))

    have η_deriv_eq : ∀ r ∈ (Set.Icc 0 1), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, deriv (fun s => η (s, y, z) b) r = (fderiv ℝ (fun z' => g (y0 + r • (y-y0), z') y) (ζ (r, y, z)) (η (r, y, z) b))
      := by
        intro r hr y hy z hz b

        have hru := Set.mem_of_subset_of_mem hu hr

        calc
          deriv (fun s => (η (s, y, z)) b) r
          = (deriv (fun s => fderiv ℝ (fun x => ζ (s, x, z)) y) r - g (y0 + r • (y - y0), ζ (r, y, z)) - r • deriv (fun s => g (y0 + s • (y - y0), ζ (s, y, z))) r) b := by
            rw [deriv_clm_apply _ (differentiableAt_const b), deriv_const, ContinuousLinearMap.map_zero, add_zero]
            congr
            unfold η
            simp only
            rw [deriv_sub _ _, deriv_smul differentiableAt_id _]
            simp only [deriv_id'', one_smul, sub_add_eq_sub_sub_swap]
            repeat sorry

          _ = (fderiv ℝ (fun x => deriv (ζ ⟨·, x, z⟩) r) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • (fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) (deriv (fun s => (y0 + s • (y - y0), ζ (s, y, z))) r))) b := by
            congr
            · sorry
            · rw [fderiv_comp'_deriv]
              · sorry
              · sorry

          _ = (fderiv ℝ (fun x => deriv (ζ ⟨·, x, z⟩) r) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), deriv (ζ ⟨·, y, z⟩) r)) b := by
            congr
            rw [← fderiv_deriv, DifferentiableAt.fderiv_prodMk]
            simp only [fderiv_const_add, ContinuousLinearMap.prod_apply, fderiv_eq_smul_deriv,
              one_smul, Prod.mk.injEq, and_true]
            simp only [differentiableAt_id', deriv_smul_const, deriv_id'', one_smul]
            · fun_prop
            · sorry

          _ = (fderiv ℝ (fun x => (g (y0 + r • (x - y0), ζ (r, x, z))) (x - y0)) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), (g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0))) b := by
            rw [← fderivWithin_eq_fderiv (s:=sb), ← fderivWithin_eq_fderiv (s:=sb) (x:=y)]
            have : ∀ x ∈ sb, deriv (ζ ⟨·, x, z⟩) r = (g (y0 + r • (x - y0), ζ (r, x, z))) (x - y0) := by
              intro x hx
              exact (ζ_eq r hr x hx z hz).deriv
            -- fderiv congr
            · exact (ζ_eq r hr y hy z hz).deriv

          _ = ((g (y0 + r • (y-y0), ζ (r,y,z)) + (fderiv ℝ (fun x => g (y0 + r • (x-y0), ζ (r,x,z))) y).flip (y-y0))
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), (g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0))) b := by
            congr
            rw [
              fderiv_clm_apply _ (by fun_prop), fderiv_sub_const, fderiv_id'
            ]
            simp only [ContinuousLinearMap.comp_id, map_sub, add_right_inj]
            · sorry

          _ = ((fderiv ℝ (fun x => g (y0 + r • (x-y0), ζ (r,x,z))) y).flip (y-y0)
            - r • (fderiv ℝ (fun x' => g (x', ζ (r, y, z))) (y0 + r • (y-y0)) (y-y0) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r, y, z)) ((g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0)))) b := by
            congr
            · abel
            · apply fderiv_partials
              sorry

          _ = ((fderiv ℝ (fun x' => g (x', ζ (r,y,z))) (y0 + r • (y-y0)) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r,y,z))).flip (y-y0)
            - r • (fderiv ℝ (fun x' => g (x', ζ (r, y, z))) (y0 + r • (y-y0)) (y-y0) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r, y, z)) ((g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0)))) b := by
            congr

    have η_diff : ∀ r ∈ Set.Icc 0 1, ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, ∃ η', HasDerivAt (η ⟨·, y, z⟩ b) η' r
      := by
        intro r hr y hy z hz b
        have hru := Set.mem_of_subset_of_mem hu hr

        have : DifferentiableOn ℝ (η ⟨·, y, z⟩ b) u := sorry
        have := this.hasDerivAt (isOpen_iff_mem_nhds.mp u_open r hru)
        use (deriv (fun x ↦ (η (x, y, z)) b) r)

    have η_ode : ∀ t ∈ (Set.Icc 0 1), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, HasDerivAt (η ⟨·, y, z⟩ b) (fderiv ℝ (g ⟨y0 + t • (y-y0), ·⟩ y) (ζ (t, y, z)) (η (t, y, z) b)) t := by
      intro t ht y hy z hz b
      have htu := Set.mem_of_subset_of_mem hu ht
      have ⟨η', hη'⟩ := η_diff t ht y hy z hz b
      have deriv_1 := hη'.deriv.symm
      have deriv_2 := η_deriv_eq t ht y hy z hz b
      have := deriv_1.trans deriv_2
      rw [this] at hη'
      exact hη'

    have η_init : ∀ y ∈ sb, ∀ z ∈ sf, η (0, y, z) = 0 := by
      intro y hy z hz
      unfold η
      simp
      simp only [ζ_init]
      exact fderiv_const_apply z

    have := η_unique hy0 hu u_open ζ_init ζ_eq η_init η_ode t ht y hy z hz
    unfold η at this
    simp at this
    rw [sub_eq_iff_eq_add, zero_add] at this
    exact this


#check BoundedContinuousFunction
#check IsPicardLindelof
#check IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq
#check exists_isIntegralCurveAt_of_contMDiffAt

end FrobLoc
