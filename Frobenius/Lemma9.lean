import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Frobenius.Utils

open Classical Function ContDiff

set_option trace.Meta.Tactic.fun_prop true


noncomputable section FrobLoc

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

abbrev Curvature (g : B × F → B →L[ℝ] F) p d1 d2 :=
  (fderiv ℝ g p (d1, 0) d2 + (fderiv ℝ g p) (0, g p d1) d2
  - (fderiv ℝ g p (d2, 0) d1 + (fderiv ℝ g p) (0, g p d2) d1))

abbrev TotalFderivCompat (g : B × F → B →L[ℝ] F) (U : Set (B × F)) :=
  ∀ p ∈ U, ∀ d1 d2, Curvature g p d1 d2 = 0


lemma η_unique
    {η : ℝ × B × F → B →L[ℝ] F} {g : B × F → B →L[ℝ] F} {sb : Set B} {sf : Set F} {y0 : B}
    (hy0 : y0 ∈ sb)
    {ζ : ℝ × B × F → F} {ε : ℝ} (hε : ε > 0)
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
    have : Differentiable ℝ g := sorry
    have foo : ContinuousOn (fderiv ℝ g) Set.univ := sorry
    unfold lip_bounds
    apply ContinuousOn.norm
    have : ∀ t, DifferentiableAt ℝ (fun z' ↦ g (y0 + t • (y - y0), z')) (ζ (t, y, z)) := by fun_prop
    conv =>
      arg 1
      intro t
      rw [fderiv_clm_apply (this t) (differentiableAt_const y)]
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add]
    have hg' : ContDiffOn ℝ 10 (fun ⟨t,z'⟩ => g (y0 + t • (y-y0), z')) ((Set.Icc (-ε) (1+ε)) ×ˢ Set.univ) := sorry
    have hζ' : ContinuousOn (ζ ⟨·, y, z⟩) (Set.Icc (-ε) (1+ε)) := sorry
    apply ContinuousOn.clm_apply
    apply ContinuousOn.comp'
    · sorry
    apply continuousOn_fderiv hg' hζ'
    · norm_num
    · sorry
    · use Set.univ
    · exact continuousOn_const

  have icc01_cpt : IsCompact (Set.Icc (-ε) (1+ε)) := isCompact_Icc
  have total_bound := exists_nonneg_bound_of_continuousOn (f := lip_bounds) (E := ℝ) icc01_cpt lip_bounds_cont

  let h := Classical.choose_spec total_bound
  set K := Classical.choose total_bound

  apply ODE_solution_unique_of_mem_Icc (K := K) (v := fun t => (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z)))) (t₀ := 0) (s := fun _ => Set.univ)
  · intro t ht
    have := (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z))).lipschitz

    replace h := h t (Set.mem_Icc_of_Ioo ht)
    unfold lip_bounds at h
    rw [norm_norm] at h

    rw [lipschitzOnWith_univ]
    exact this.weaken h
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

set_option maxHeartbeats 1000000 in
lemma Lemma9b
  {g : B × F → B →L[ℝ] F} {sb : Set B} {sf : Set F} {y0 : B}
  (sb_open : IsOpen sb) (sf_open : IsOpen sf) (hy0 : y0 ∈ sb)
  (g_smooth : SmoothFunction (dimB := dimB + dimF) (dimF := dimB * dimF) g)
  (g_compat : TotalFderivCompat g (sb ×ˢ sf))
  {ζ : ℝ × B × F → F} {ε : ℝ} (hε : ε > 0)
  (ζ_init : ∀ y z, ζ (0, y, z) = z)
  (ζ_eq : ∀ y ∈ sb, ∀ z ∈ sf, ∀ t ∈ (Set.Icc (-ε) (1+ε)), HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
  : ∀ t ∈ Set.Icc 0 1, ∀ y ∈ sb, ∀ z ∈ sf, fderiv ℝ (fun y' => ζ (t, y', z)) y = t • g (y0 + t • (y-y0), ζ (t, y, z)) := by
    intro t ht y hy z hz

    let η : ℝ × B × F → B →L[ℝ] F := by
      intro ⟨t, y, z⟩
      exact (fderiv ℝ (fun x => ζ (t, x, z)) y) - t • g (y0 + t • (y - y0), ζ (t, y, z))

    have η_deriv_eq : ∀ r ∈ (Set.Icc (-ε) (1+ε)), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, deriv (fun s => η (s, y, z) b) r = (fderiv ℝ (fun z' => g (y0 + r • (y-y0), z') y) (ζ (r, y, z)) (η (r, y, z) b))
      := by sorry
        /-intro r hr y hy z hz b

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
              exact (ζ_eq x hx z hz r hr).deriv
            -- fderiv congr
            · exact (ζ_eq y hy z hz r hr).deriv

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
            congr-/

    have η_diff : ∀ r ∈ Set.Icc (-ε) (1+ε), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, ∃ η', HasDerivAt (η ⟨·, y, z⟩ b) η' r
      := by
        intro r hr y hy z hz b

        use (deriv (fun x ↦ (η (x, y, z)) b) r)
        simp only [hasDerivAt_deriv_iff]
        unfold η
        simp only
        have : Differentiable ℝ ζ := sorry
        have : Differentiable ℝ g := by
          unfold SmoothFunction at g_smooth
          exact g_smooth.differentiable (by norm_num)
        -- XXX: fun_prop not working
        --
        apply DifferentiableAt.clm_apply
        · apply DifferentiableAt.sub
          · apply ContDiffAt.differentiableAt_iteratedFDeriv
          · fun_prop
        · exact differentiableAt_const b

    have η_ode : ∀ t ∈ (Set.Icc (-ε) (1+ε)), ∀ y ∈ sb, ∀ z ∈ sf, ∀ b, HasDerivAt (η ⟨·, y, z⟩ b) (fderiv ℝ (g ⟨y0 + t • (y-y0), ·⟩ y) (ζ (t, y, z)) (η (t, y, z) b)) t := by
      intro t ht y hy z hz b
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

    have : ∀ t ∈ Set.Icc (-ε) (1+ε), ∀ b, fderiv ℝ (fun y' ↦ ζ (t, y', z)) y b = t • g (y0 + t • (y - y0), ζ (t, y, z)) b := by
      intro t ht b
      have := η_unique hy0 hε ζ_init ζ_eq η_init η_ode y hy z hz b
      unfold Set.EqOn at this
      unfold η at this
      simp only at this
      replace := this ht
      rw [ContinuousLinearMap.sub_apply, sub_eq_iff_eq_add, zero_add] at this
      exact this
    have htε : t ∈ Set.Icc (-ε) (1+ε) := by
      have : Set.Icc 0 1 ⊆ Set.Icc (-ε) (1+ε) := by
        rw [← zero_sub]
        exact (subset_of_le hε.gt (a := 0) (b := 1)).trans Set.Ioo_subset_Icc_self
      exact this ht
    replace := this t htε
    -- XXX: how to apply funext here?
    rw [← funext_iff] at this
    -- XXX
