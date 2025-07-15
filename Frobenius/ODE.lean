import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.LineDeriv.Basic

open Set Function Real NNReal Metric --ODE

section PLCont
/- Temporary copy of code from Winston Yin's PR
   https://github.com/leanprover-community/mathlib4/pull/26392

   Once merged into Mathlib, remove the final `L` from `IsPicardLindelofL`.
-/

/-- Prop structure holding the assumptions of the Picard-Lindelöf theorem.
`IsPicardLindelof f t₀ x₀ a r L K` means that the time-dependent vector field `f` satisfies the
conditions to admit an integral curve `α : ℝ → E` to `f` defined on `Icc tmin tmax` with the
initial condition `α t₀ = x`, where `‖x - x₀‖ ≤ r`. Note that the initial point `x` is allowed
to differ from the point `x₀` about which the conditions on `f` are stated. -/
structure IsPicardLindelofL {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz in with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

-- XXX: probably this could return some weak pointwise bounds (which should already be
-- available from the function space that Picard iteraction acts on):
-- ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a

open Classical in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the intial point. -/
theorem IsPicardLindelofL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelofL f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  sorry

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is continuous on its domain as a (partial) map `E × ℝ → E`. -/
theorem IsPicardLindelofL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelofL f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  sorry
  -- prove using the following lemma together with `exists_..._lipschitzOnWith`
#check continuousOn_prod_of_continuousOn_lipschitzOnWith

omit x in
theorem IsPicardLindelofL.mem_closedBall
  (hf : IsPicardLindelofL f t₀ x₀ a r L K)
  {α : ℝ → E}
  (hα₀ : α t₀ ∈ closedBall x₀ r)
  (hα : ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) :
    ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a := by
  sorry
#check PicardLindelof.FunSpace.mem_closedBall --see this proof for inspiration

end PLCont

section Util -- some helpful lemmas

section ContinuousOnCurry

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem ContinuousOn.uncurry_left {f : X → Y → Z} {s : Set X } {t : Set Y}
  (h : ContinuousOn (uncurry f) (s ×ˢ t)) (x : X) (hx : x ∈ s) :
    ContinuousOn (f x) t := by
  have : MapsTo (x, ·) t (s ×ˢ t) := fun ⦃y⦄ hy => mem_prod.mp ⟨hx, hy⟩
  fun_prop (disch:=assumption)

theorem ContinuousOn.uncurry_right {f : X → Y → Z} {s : Set X } {t : Set Y}
  (h : ContinuousOn (uncurry f) (s ×ˢ t)) (y : Y) (hy : y ∈ t) :
    ContinuousOn (f · y) s := by
  have : MapsTo (·, y) s (s ×ˢ t) := fun ⦃x⦄ hx => mem_prod.mp ⟨hx, hy⟩
  fun_prop (disch:=assumption)

theorem continuousOn_curry {g : X × Y → Z} {s : Set X } {t : Set Y}
  (h : ContinuousOn g (s ×ˢ t)) (x : X) (hx : x ∈ s):
    ContinuousOn (curry g x) t := by
  refine ContinuousOn.uncurry_left ?_ x hx
  simp only [uncurry_curry]
  exact h

end ContinuousOnCurry

section Hadamard --Hadamard lemma

open Topology MeasureTheory in
theorem intervalIntegral.continuousOn_parametric_primitive_of_continuousOn
  {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
  {μ : Measure ℝ} [NoAtoms μ] [IsLocallyFiniteMeasure μ]
  {f : X → ℝ → E} {a₀ b₀ : ℝ} {s : Set X}
  (hf : ContinuousOn (Function.uncurry f) (s ×ˢ uIcc a₀ b₀)) :
    ContinuousOn (fun p : X ↦ ∫ (t : ℝ) in a₀..b₀, f p t ∂μ) s := by
  sorry

-- Hadamard lemma for Lipschitz-continuously differentiable functions
open AffineMap Topology in
theorem hadamard_div
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {f : F × E → G} {f' : F × E → E →L[ℝ] G} {v : Set F} {u : Set E}
  (huv : IsOpen u ∧ IsOpen v ∧ Convex ℝ u ∧ Convex ℝ v)
  (hf : ∀ y ∈ v, ∀ z ∈ u,
      ContinuousAt f' (y, z) ∧ HasFDerivAt (f ⟨y, ·⟩) (f' (y, z)) z) :
    ∃ g : F × E × E → E →L[ℝ] G,
      ∀ y ∈ v, (({C : ℝ≥0} → LipschitzOnWith C (f' ⟨y, ·⟩) u →
            LipschitzOnWith (2*C) (g ⟨y, ·⟩) (u ×ˢ u))
          ∧ ({C : ℝ≥0} → (∀ x ∈ u, ‖f' ⟨y, x⟩‖ ≤ C) → ∀ z ∈ u, ∀ x ∈ u, ‖g ⟨y, ⟨z, x⟩⟩‖ ≤ C))
        ∧ ContinuousOn g (v ×ˢ u ×ˢ u)
        ∧ (∀ x ∈ u, g (y,x,x) = f' (y,x) ∧ ∀ z ∈ u, f (y,z) - f (y,x) = g (y,z,x) (z - x)) := by
  sorry

end Hadamard

section ExtendLinear

-- extend LinearMap from neighborhood of zero
noncomputable def extend_linearMap_of_nhd_zero {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] -- XXX: actually hypotheses don't need any norm structure
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {U : Set V} (hU : U ∈ nhds 0) (f : V → W) --(hf : ContinuousOn f U)
  (hfadd : ∀ x ∈ U, ∀ y ∈ U, x + y ∈ U → f (x + y) = f x + f y)
  (hfsmul : ∀ c : ℝ, ∀ x ∈ U, c • x ∈ U → f (c • x) = c • f x) :
    V →ₗ[ℝ] W := by
  sorry

-- apply linear extension to get original function on neighborhood of zero
theorem extend_linearMap_of_nhd_zero_apply
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {U : Set V} {hU : U ∈ nhds 0}
  {f : V → W} {hfadd hfsmul} :
    ∀ x ∈ U, extend_linearMap_of_nhd_zero hU f hfadd hfsmul x = f x := by
  sorry

-- extend ContinuousLinearMap from neighborhood of zero
noncomputable def extend_continuousLinearMap_of_nhd_zero {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {U : Set V} (hU : U ∈ nhds 0) (f : V → W) (hf : ContinuousOn f U)
  (hfadd : ∀ x ∈ U, ∀ y ∈ U, x + y ∈ U → f (x + y) = f x + f y)
  (hfsmul : ∀ c : ℝ, ∀ x ∈ U, c • x ∈ U → f (c • x) = c • f x) :
    V →L[ℝ] W := by
  sorry

-- apply linear extension to get original function on neighborhood of zero
theorem extend_continuousLinearMap_of_nhd_zero_apply
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {U : Set V} {hU : U ∈ nhds 0}
  {f : V → W} {hf hfadd hfsmul} :
    ∀ x ∈ U, extend_continuousLinearMap_of_nhd_zero hU f hf hfadd hfsmul x = f x := by
  sorry

end ExtendLinear

section DiffThroughApply

-- differentiate through applying linear map to vector
theorem hasDerivAt_iff_hasDerivAt_apply_on_nhd_zero
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E} {B : ℝ → E →L[ℝ] E} (hB : Continuous B)
  {I : Set ℝ} (hI : Convex ℝ I) (hIo : IsOpen I)
  {U : Set E} (hU : U ∈ nhds 0) :
    (∀ t ∈ I, ∀ v ∈ U, HasDerivAt (fun s => (A s) v) ((B t) v) t)
      ↔ ∀ t ∈ I, HasDerivAt A (B t) t := by
  sorry

end DiffThroughApply

section GateauxFrechet

-- Sufficient conditions for the existence of Fréchet derivativefrom the existence
-- of Gâteaux derivative at a point (cf. Proposition 3.2.15 in Drábek & Milota (2007)).
theorem hasFDerivAt_of_hasLineDerivAt_continuous_on_nhd
  --{𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {x : E} (hU : U ∈ nhds x)
  (f : E → F) (f' : E → E →L[ℝ] F)
  (hf : ∀ y ∈ U, ∀ v, HasLineDerivAt ℝ f (f' y v) y v)
  (hf' : ContinuousWithinAt f' U x):
    HasFDerivAt f (f' x) x
  := sorry
end GateauxFrechet

end Util

section PLWithParam

-- XXX: remove the extra `L` after Winston Yin's PR mentioned above is merged

-- PL hypotheses that will guarantee regular dependence on ODE parameters
structure IsPicardLindelofWithParamL {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℝ → F × E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    (z₀ : F) (x₀ : E) (a r L K : ℝ≥0) : Prop where
  /-- The vector field at any time is Lipschitz in with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall (z₀, x₀) a)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ zx ∈ closedBall (z₀, x₀) a, ContinuousOn (f · zx) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ zx ∈ closedBall (z₀, x₀) a, ‖f t zx‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

-- for fixed parameters we recovere the standard PL hypotheses
theorem IsPicardLindelofWithParamL.isPicardLindelofL
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → F × E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)}
  {x₀ : E} {z₀ : F} {a r L K : ℝ≥0} (hf : IsPicardLindelofWithParamL f t₀ z₀ x₀ a r L K) :
    IsPicardLindelofL (fun t zx => (0, f t zx)) t₀ (z₀, x₀) a r L K := by
  obtain ⟨hfl, hfc, hle, hmle⟩ := hf
  constructor
  case lipschitzOnWith =>
    intro t ht
    rw [show K = max 0 K by simp only [zero_le, sup_of_le_right]]
    apply LipschitzOnWith.prodMk (LipschitzWith.const 0).lipschitzOnWith (hfl t ht)
  case continuousOn =>
    intro zx hzx
    apply ContinuousOn.prodMk continuousOn_const (hfc zx hzx)
  case norm_le =>
    intro t ht zx hzx
    calc
      _ = _ := Prod.norm_def ((0:F), f t zx)
      _ = ‖f t zx‖ := by simp only [norm_zero, max_eq_right_iff, norm_nonneg]
      _ ≤ _ := hle t ht zx hzx
  case mul_max_le =>
    exact hmle

-- Picard-Lindelöf ODE existance with parameters
-- XXX: see earlier remark about returning weak pointwise bounds on solution
theorem IsPicardLindelofWithParamL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → F × E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} (ht₀ : tmin < t₀ ∧ t₀ < tmax)
  --(hminmax : tmin < tmax)
  {x₀ : E} {z₀ : F} {a r L K : ℝ≥0} (hf : IsPicardLindelofWithParamL f t₀ z₀ x₀ a r L K) :
    ∃ α : (F × E) × ℝ → E, (∀ zx ∈ closedBall (z₀, x₀) r, α ⟨zx, t₀⟩ = zx.2 ∧
      ∀ t ∈ Ioo tmin tmax,
        --HasDerivWithinAt (α ⟨zx, ·⟩) (f t ⟨zx.1, α ⟨zx, t⟩⟩) (Icc tmin tmax) t)
        HasDerivAt (α ⟨zx, ·⟩) (f t ⟨zx.1, α ⟨zx, t⟩⟩) t)
        ∧ ContinuousOn α (closedBall (z₀, x₀) r ×ˢ Icc tmin tmax) := by
  have hminmax := ht₀.1.trans ht₀.2
  have h0f := hf.isPicardLindelofL
  obtain ⟨α, hα, hαc⟩ := h0f.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  use Prod.snd ∘ α
  constructor
  · intro zx hzx
    replace ⟨hα0, hα⟩ := hα zx hzx
    have hα_fst : ∀ t ∈ Icc tmin tmax, (α (zx,t)).1 = zx.1 := by
      replace hα0 := congr_arg Prod.fst hα0
      simp only [← hα0]
      replace hα := fun t ht => (((hasFDerivWithinAt_fst (s := univ)).comp t (hα t ht)
        (by exact fun ⦃_⦄ _ ↦ trivial)).hasDerivWithinAt)
      have (t) (ht : t ∈ Ico tmin tmax) := (hα t (mem_Icc_of_Ico ht)).derivWithin
        ((uniqueDiffOn_Icc hminmax).uniqueDiffWithinAt (mem_Icc_of_Ico ht))
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', comp_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] at this
      have := constant_of_derivWithin_zero ?_ this
      swap
      · unfold DifferentiableOn; intro t ht
        exact (hα t ht).differentiableWithinAt
      intro t ht
      calc
        _ = _ := (this t ht)
        _ = _ := (this t₀ t₀.prop).symm
        _ = _ := hα0
      exact hα0.symm --XXX: why this last line?
    constructor
    · exact congr_arg Prod.snd hα0
    · intro t ht
      replace hα := (hα t (mem_Icc_of_Ioo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      --convert (hasFDerivWithinAt_snd (s := univ)).comp t hα _
      convert (hasFDerivAt_snd).comp t hα
      · apply congr_arg₂
        · ext zx
          simp only [comp_apply]
        · simp only [comp_apply]
          congr 1
          rw [← hα_fst t (mem_Icc_of_Ioo ht)]
      --· exact fun ⦃x⦄ a ↦ trivial
  · apply (continuousOn_snd (s := univ)).comp hαc (fun _ _ => trivial)

end PLWithParam

section PLJointDiff
-- Joint differentiability in time and initial conditions from sufficient
-- regularity of the driving function

-- derivative of ODE solution, solves the differentiated ODE
theorem PL_deviation
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} (hminmax : tmin < tmax)
  {x₀ : E} {a r L K : ℝ≥0} (hr : 0 < r)
  (α : E × ℝ → E)
  (hf : (∀ t ∈ Icc tmin tmax, ContDiffOn ℝ 1 (f t) (closedBall x₀ a))
    ∧ IsPicardLindelofL f t₀ x₀ a r L K)
  (hfl : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (fderiv ℝ (f t)) (closedBall x₀ a))
  (hαl : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L (α ⟨·,t⟩) (closedBall x₀ r))
  (hα : ∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x
      ∧ ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t) :
    ∃ β : E × ℝ → E →L[ℝ] E, ∀ x ∈ closedBall x₀ r,
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (β ⟨x, ·⟩)
          ((fderiv ℝ (f t) (α (x, t))).comp (β ⟨x, t⟩)) (Icc tmin tmax) t
        ∧ HasFDerivWithinAt (α ⟨·, t⟩) (β ⟨x, t⟩) (closedBall x₀ r) x := by
  -- first start with some housekeeping
  have ha : 0 < a := sorry -- use hf.2.mul_max_le, hr and hminmax
  have hfc : ContinuousOn ↿f (Icc tmin tmax ×ˢ closedBall x₀ a) := sorry -- uniform Lipschitz
  have hf'c : ContinuousOn ↿(fun t x => fderiv ℝ (f t) x) (Icc tmin tmax ×ˢ closedBall x₀ a) :=
    sorry -- uniform Lipschitz
  -- define α deformation and find its differential equation
  -- change it to a linear equation using the Hadamard lemma
  -- prove IsPicardLindelofParamL for the deformation equation
  -- obtain solution γ with appropriate initial data, use its continuity and Lipschitz-ness
  -- use ODE uniqueness to show that γ coincides with deformation when ε ≠ 0
  -- set ε = 0 in γ and show that it is locally linear in initial data
  -- use the local linearity to extract the corresponding β linear map
  -- use β for the ∃ goal
  -- split the goal into the ODE for β and into relating β to the derivative of α
  -- first, simplify the deformation ODE to satisfy the ODE goal
  -- second, convert FDeriv into LineDeriv for α, rewrite using ε → 0 quotient limit
  -- take advantage of the ε ≠ 0 condition to rewrite the limit in terms of β, use continuity
  sorry

-- solution of ODE is jointly continuously differentiable, when driving function
-- is sufficiently regular
-- theorem ...

end PLJointDiff
