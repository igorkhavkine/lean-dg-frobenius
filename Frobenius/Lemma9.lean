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
    (ζ_eq : ∀ {t y z}, t ∈ Set.Icc (-ε) (1+ε) → y ∈ sb → z ∈ sf → HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
    (η_init : ∀ {y z}, y ∈ sb → z ∈ sf → η (0, y, z) = 0)
    (η_eq : ∀ {t y z b}, t ∈ Set.Icc (-ε) (1+ε) → y ∈ sb → z ∈ sf → HasDerivAt (fun s => η (s, y, z) b) (fderiv ℝ (fun z' => g (y0 + t • (y-y0), z') y) (ζ (t, y, z)) (η (t, y, z) b)) t)
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
    have : ContDiff ℝ 1 g := sorry
    have : Differentiable ℝ g := sorry
    -- have foo : ContinuousOn (fderiv ℝ g) Set.univ := sorry
    unfold lip_bounds
    apply ContinuousOn.norm
    have : ∀ t, DifferentiableAt ℝ (fun z' ↦ g (y0 + t • (y - y0), z')) (ζ (t, y, z)) := by fun_prop
    conv =>
      arg 1
      intro t
      rw [fderiv_clm_apply (this t) (differentiableAt_const y)]
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add]
    have hg' : ContDiffOn ℝ 1 (fun ⟨t,z'⟩ => g (y0 + t • (y-y0), z')) ((Set.Icc (-ε) (1+ε)) ×ˢ Set.univ) := by fun_prop
    have hζ' : ContinuousOn (ζ ⟨·, y, z⟩) (Set.Icc (-ε) (1+ε)) := sorry
    have : Continuous (fun t ↦ (fderiv ℝ (fun z' ↦ g (y0 + t • (y - y0), z')) (ζ (t, y, z))).flip y) := by -- TODO: lemma for continuity of flip
      fun_prop
      --apply LinearMap.continuous_of_finiteDimensional
      sorry
    exact this.continuousOn

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
      exact η_eq ht hy hz)
  · intro t ht
    exact η_eq (Set.mem_Icc_of_Ioo ht) hy hz
  · exact fun t a ↦ trivial
  · exact continuousOn_const
  · intro t ht
    simp only [ContinuousLinearMap.map_zero]
    exact hasDerivAt_const t 0
  · exact fun t a ↦ trivial
  · have := η_init hy hz
    simp only [this, ContinuousLinearMap.zero_apply]

lemma exchange_deriv
    {X : Type*} {dimX : ℕ} [oNormedSpace X dimX]
    {f : ℝ × B → X} {sb : Set B} {sf : Set ℝ} {q : B} {r : ℝ}
    (f_smooth : SmoothFunctionOn (dimB := 1+dimB) (dimF := dimX) f (sf ×ˢ sb))
    (sb_open : IsOpen sb) (sf_open : IsOpen sf) (hq : q ∈ sb) (hr : r ∈ sf)
    : deriv (fun s => fderiv ℝ (fun x => f (s, x)) q) r = fderiv ℝ (fun x => deriv (fun s => f (s, x)) r) q := by
  have : ∀ b, ∀ {s}, s ∈ sf → fderiv ℝ (fun x ↦ f (s, x)) q b = fderiv ℝ f (s,q) (0,b) := by
    intro b s hs
    have pt : (s, q) ∈ sf ×ˢ sb := Set.mk_mem_prod hs hq
    have nh : sf ×ˢ sb ∈ nhds (s, q) := prod_mem_nhds_iff.mpr ⟨IsOpen.mem_nhds sf_open hs, IsOpen.mem_nhds sb_open hq⟩
    rw [fderiv_partials ((f_smooth.differentiableOn ENat.LEInfty.out (s, q) pt).differentiableAt nh)]
    simp only [fderiv_eq_smul_deriv, zero_smul, zero_add]

  rw [← fderiv_deriv, ← fderivWithin_eq_fderiv (s := sf)]
  · have : ∀ b, (fderivWithin ℝ (fun s ↦ (fderiv ℝ (fun x ↦ f (s, x)) q) b) sf r) 1 = (fderivWithin ℝ (fun s ↦ fderiv ℝ f (s,q) (0,b)) sf r) 1 := by
      intro b
      congr 1
      apply fderivWithin_congr
      · unfold Set.EqOn
        intro s hs
        simp only
        exact this b hs
      · exact this b hr
    rw [this, fderivWithin_eq_fderiv]
    have : (fderiv ℝ (fun s ↦ (fderiv ℝ f (s, q)) (0, b)) r) 1 = fderiv ℝ (fun x => fderiv ℝ f x (0, b)) (r,q) (1,0) := by
      rw [fderiv_partials]
      simp only [fderiv_eq_smul_deriv, one_smul, map_zero, add_zero]
      sorry
    · rw [this]
      sorry
    · exact IsOpen.uniqueDiffWithinAt sf_open hr
    · sorry
  · exact IsOpen.uniqueDiffWithinAt sf_open hr
  · sorry


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
  (ζ_eq : ∀ {t y z}, t ∈ (Set.Icc (-ε) (1+ε)) → y ∈ sb → z ∈ sf → HasDerivAt (fun s => ζ (s, y, z)) (g (y0 + t • (y - y0), ζ (t, y, z)) (y - y0)) t)
  : ∀ t ∈ Set.Icc 0 1, ∀ y ∈ sb, ∀ z ∈ sf, fderiv ℝ (fun y' => ζ (t, y', z)) y = t • g (y0 + t • (y-y0), ζ (t, y, z)) := by
    intro t ht

    let η : ℝ × B × F → B →L[ℝ] F := by
      intro ⟨t, y, z⟩
      exact (fderiv ℝ (fun x => ζ (t, x, z)) y) - t • g (y0 + t • (y - y0), ζ (t, y, z))

    unfold SmoothFunction at g_smooth
    have g_diff : Differentiable ℝ g := g_smooth.differentiable ENat.LEInfty.out

    have ζ_smooth : SmoothFunction (dimB := 1+dimB+dimF) (dimF := dimF) ζ := sorry
    have ζ_diff : ∀ {r y z}, r ∈ (Set.Icc (-ε) (1+ε)) → y ∈ sb → z ∈ sf → DifferentiableAt ℝ ζ (r, y, z) := sorry

    have η_deriv_eq : ∀ {r y z b}, r ∈ (Set.Ioo (-ε) (1+ε)) → y ∈ sb → z ∈ sf → deriv (fun s => η (s, y, z) b) r = (fderiv ℝ (fun z' => g (y0 + r • (y-y0), z') (y-y0)) (ζ (r, y, z)) (η (r, y, z) b))
      := by
        intro r y z b hro hy hz

        have hr : r ∈ Set.Icc (-ε) (1+ε) := Set.mem_Icc_of_Ioo hro

        calc
          deriv (fun s => (η (s, y, z)) b) r
          = (deriv (fun s => fderiv ℝ (fun x => ζ (s, x, z)) y) r - g (y0 + r • (y - y0), ζ (r, y, z)) - r • deriv (fun s => g (y0 + s • (y - y0), ζ (s, y, z))) r) b := by
            rw [deriv_clm_apply _ (differentiableAt_const b), deriv_const, ContinuousLinearMap.map_zero, add_zero]
            · congr
              unfold η
              simp only
              rw [deriv_fun_sub _ _, deriv_fun_smul differentiableAt_id _]
              simp only [deriv_id'', one_smul, sub_add_eq_sub_sub_swap]
              · have : DifferentiableAt ℝ ζ (r, y, z) := ζ_diff hr hy hz
                fun_prop
              · sorry
              · have : DifferentiableAt ℝ ζ (r, y, z) := ζ_diff hr hy hz
                fun_prop
            · sorry
          _ = (fderiv ℝ (fun x => deriv (ζ ⟨·, x, z⟩) r) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • (fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) (deriv (fun s => (y0 + s • (y - y0), ζ (s, y, z))) r))) b := by
            congr
            · rw [exchange_deriv (f := fun p => ζ (p.1, p.2, z)) _ sb_open isOpen_Ioo hy hro]
              unfold SmoothFunctionOn
              fun_prop
            · rw [fderiv_comp'_deriv]
              · fun_prop
              · have : DifferentiableAt ℝ ζ (r, y, z) := ζ_diff hr hy hz
                fun_prop

          _ = (fderiv ℝ (fun x => deriv (ζ ⟨·, x, z⟩) r) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), deriv (ζ ⟨·, y, z⟩) r)) b := by
            congr
            rw [← fderiv_deriv, DifferentiableAt.fderiv_prodMk]
            simp only [fderiv_const_add, ContinuousLinearMap.prod_apply, fderiv_eq_smul_deriv,
              one_smul, Prod.mk.injEq, and_true]
            simp only [differentiableAt_fun_id, deriv_smul_const, deriv_id'', one_smul]
            · fun_prop
            · have : DifferentiableAt ℝ ζ (r,y,z) := ζ_diff hr hy hz
              fun_prop

          _ = (fderiv ℝ (fun x => (g (y0 + r • (x - y0), ζ (r, x, z))) (x - y0)) y
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), (g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0))) b := by
            congr 2
            · congr 1
              rw [← fderivWithin_eq_fderiv (s := sb), ← fderivWithin_eq_fderiv (s := sb)]
              apply fderivWithin_congr
              repeat sorry
            · congr
              exact (ζ_eq hr hy hz).deriv

          _ = ((g (y0 + r • (y-y0), ζ (r,y,z)) + (fderiv ℝ (fun x => g (y0 + r • (x-y0), ζ (r,x,z))) y).flip (y-y0))
            - g (y0 + r • (y - y0), ζ (r, y, z))
            - r • fderiv ℝ g (y0 + r • (y-y0), ζ (r, y, z)) ((y - y0), (g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0))) b := by
            congr
            rw [
              fderiv_clm_apply _ (by fun_prop), fderiv_sub_const, fderiv_id'
            ]
            · simp only [ContinuousLinearMap.comp_id, map_sub]
            · have : DifferentiableAt ℝ ζ (r, y, z) := ζ_diff hr hy hz
              fun_prop

          _ = ((fderiv ℝ (fun x => g (y0 + r • (x-y0), ζ (r,x,z))) y).flip (y-y0)
            - r • (fderiv ℝ (fun x' => g (x', ζ (r, y, z))) (y0 + r • (y-y0)) (y-y0) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r, y, z)) ((g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0)))) b := by
            congr
            · abel
            · apply fderiv_partials
              fun_prop

          _ = fderiv ℝ (fun x => g (y0 + r • (x-y0), ζ (r,x,z))) y b (y-y0)
            - r • (fderiv ℝ (fun x' => g (x', ζ (r, y, z))) (y0 + r • (y-y0)) (y-y0) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r, y, z)) ((g (y0 + r • (y - y0), ζ (r, y, z))) (y - y0))) b := by
            congr


          _ = fderiv ℝ (fun x' => g (x', ζ (r,y,z))) (y0 + r • (y-y0)) b (r • (y-y0)) + (fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r,y,z))) (fderiv ℝ (fun x => ζ (r,x,z)) y b) (y-y0)
            - (fderiv ℝ (fun x' => g (x', ζ (r, y, z))) (y0 + r • (y-y0)) (r • (y-y0)) + fderiv ℝ (fun z' => g (y0 + r • (y-y0), z')) (ζ (r, y, z)) ((g (y0 + r • (y - y0), ζ (r, y, z))) (r • (y - y0)))) b := by
            congr
            rw [
              fderiv_comp' y (by fun_prop) _, DifferentiableAt.fderiv_prodMk (by fun_prop) _,
              ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply
            ]
            simp only [fderiv_const_add,
              fderiv_fun_const_smul (DifferentiableAt.sub_const differentiableAt_fun_id y0) r,
              fderiv_sub_const, fderiv_id', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq, map_smul]
            rw [fderiv_partials, ContinuousLinearMap.add_apply, map_smul, ContinuousLinearMap.smul_apply]
            · fun_prop
            · have : DifferentiableAt ℝ ζ (r,y,z) := ζ_diff hr hy hz
              fun_prop
            · have : DifferentiableAt ℝ ζ (r,y,z) := ζ_diff hr hy hz
              fun_prop
            · rw [← ContinuousLinearMap.smul_apply, smul_add, ← map_smul, ← map_smul, ← map_smul]

          _ = -(Curvature g (y0 + r • (y-y0), ζ (r,y,z)) (r • (y-y0)) b) + (fderiv ℝ (fun z' ↦ (g (y0 + r • (y - y0), z')) (y-y0)) (ζ (r, y, z))) ((η (r, y, z)) b) := by
            unfold Curvature
            unfold η
            simp only
            rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.map_sub _ ((fderiv ℝ (fun x ↦ ζ (r, x, z)) y) b)]

            have : DifferentiableAt ℝ g (y0 + r • (y - y0), ζ (r, y, z)) := g_diff (y0 + r • (y - y0), ζ (r, y, z))
            rw [fderiv_partials this, fderiv_partials this, fderiv_partials this, fderiv_partials this]

            simp only [ContinuousLinearMap.add_apply, map_zero, add_zero, zero_add,
              ContinuousLinearMap.coe_smul', Pi.smul_apply]
            rw [fderiv_clm_apply _ (differentiableAt_const (y - y0))]
            · simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero,
                zero_add, ContinuousLinearMap.flip_apply]
              set dy := r • (y-y0) with hdy
              set Z := ζ (r,y,z)
              set gx := (fun x' ↦ g (x', Z))
              set gz := (fun z' ↦ (g (y0 + dy, z')))
              set gzy := (fun z' ↦ (g (y0 + dy, z')) y)
              rw [
                ContinuousLinearMap.map_smul (fderiv ℝ gz Z), ContinuousLinearMap.smul_apply,
                ← ContinuousLinearMap.map_smul ((fderiv ℝ gz Z) ((g (y0 + dy, Z)) b)) r, ← hdy
              ]
              abel
            · fun_prop

          _ = (fderiv ℝ (fun z' ↦ (g (y0 + r • (y - y0), z')) (y-y0)) (ζ (r, y, z))) ((η (r, y, z)) b) := by
            unfold TotalFderivCompat at g_compat
            rw [g_compat (y0 + r • (y - y0), ζ (r, y, z)) _ (r • (y - y0)) b]
            · simp only [neg_zero, map_sub, zero_add]
            · sorry

    have η_diff : ∀ {r y z b}, r ∈ Set.Icc (-ε) (1+ε) → y ∈ sb → z ∈ sf → ∃ η', HasDerivAt (η ⟨·, y, z⟩ b) η' r
      := by
        intro r y z b hr hy hz

        use (deriv (fun x ↦ (η (x, y, z)) b) r)
        simp only [hasDerivAt_deriv_iff]
        unfold η
        simp only
        have ζ_diff : Differentiable ℝ ζ := ζ_smooth.differentiable ENat.LEInfty.out
        have : Differentiable ℝ g := by
          exact g_smooth.differentiable (by norm_num)
        -- XXX: fun_prop not working
        --
        conv =>
          arg 2
          intro t
          calc
            (fderiv ℝ (fun x ↦ ζ (t, x, z)) y - t • g (y0 + t • (y - y0), ζ (t, y, z))) b = fderiv ℝ (fun x ↦ ζ (t, x, z)) y b - t • g (y0 + t • (y - y0), ζ (t, y, z)) b
              := by apply ContinuousLinearMap.sub_apply
            _ = fderiv ℝ (ζ ∘ fun x ↦ (t, x, z)) y b - t • g (y0 + t • (y - y0), ζ (t, y, z)) b := by congr
            _ = fderiv ℝ ζ (t, y, z) (fderiv ℝ (fun x ↦ (t, x, z)) y b) - t • g (y0 + t • (y - y0), ζ (t, y, z)) b := by
              congr
              rw [fderiv_comp]
              · simp only [ContinuousLinearMap.coe_comp', comp_apply]
              · exact ζ_diff (t, y, z)
              · exact DifferentiableAt.prodMk (differentiableAt_const t) (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const z))
            _ = fderiv ℝ ζ (t, y, z) (0, b, 0) - t • g (y0 + t • (y - y0), ζ (t, y, z)) b := by
              congr
              simp only [differentiableAt_const, differentiableAt_fun_id, DifferentiableAt.prodMk,
                DifferentiableAt.fderiv_prodMk, fderiv_fun_const, Pi.zero_apply, fderiv_id',
                ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
                ContinuousLinearMap.coe_id', id_eq]
            _ = iteratedFDeriv ℝ 1 ζ (t, y, z) (fun _ => (0, b, 0)) - t • g (y0 + t • (y - y0), ζ (t, y, z)) b := sorry
        apply DifferentiableAt.sub
        · apply ContDiffAt.differentiableAt_iteratedFDeriv -- TODO: workout on paper
        · fun_prop

    have η_ode : ∀ {t y z b}, t ∈ (Set.Icc (-ε) (1+ε)) → y ∈ sb → z ∈ sf → HasDerivAt (η ⟨·, y, z⟩ b) (fderiv ℝ (g ⟨y0 + t • (y-y0), ·⟩ y) (ζ (t, y, z)) (η (t, y, z) b)) t := by
      intro _ _ _ _ ht hy hz
      have ⟨η', hη'⟩ := η_diff ht hy hz
      have deriv_1 := hη'.deriv.symm
      have deriv_2 := η_deriv_eq ht hy hz
      have := deriv_1.trans deriv_2
      rw [this] at hη'
      exact hη'

    have η_init : ∀ {y z}, y ∈ sb → z ∈ sf → η (0, y, z) = 0 := by
      intro y z hy hz
      unfold η
      simp
      simp only [ζ_init]
      exact fderiv_const_apply z

    intro y hy z hz

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

    ext b
    exact this b
