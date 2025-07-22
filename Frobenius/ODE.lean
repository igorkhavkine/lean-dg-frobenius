import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.Partial

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

omit x in
theorem IsPicardLindelofL.mem_closedBall' -- with weaker hypothesis on existence time
  (hf : IsPicardLindelofL f t₀ x₀ a r L K)
  {α : ℝ → E}
  (hα₀ : α t₀ ∈ closedBall x₀ r)
  (hα : ∀ t ∈ Ioo tmin tmax, HasDerivAt α (f t (α t)) t) :
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
  {f : F × E → G} {f' : F × E → E →L[ℝ] G} {v : Set F} {u : Set E} (huc : Convex ℝ u)
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

section LipschitzLinear

--XXX: should be available in a newer version of Mathlib
theorem ContinuousLinearMap.opNorm_le_iff_lipschitz {𝕜 𝕜₂ E F : Type*}
[SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
[NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
[NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
{f : E →SL[σ₁₂] F} {K : NNReal} :
  ‖f‖ ≤ ↑K ↔ LipschitzWith K ⇑f :=
sorry

end LipschitzLinear

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

section PartialFDeriv

-- this is from PR #26300
--   https://github.com/leanprover-community/mathlib4/pull/26300
/-- If a function `f : E × F → G` has partial derivative `f'x` or `f'y` continuous
on an open set `u`, then `f` is continously differentiable on this set, with
the derivative given by `f' = f'x.coprod f'y`.
-/
theorem hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  --NB: [NormedSpace ℝ E] is not needed because the proof eventually applies
  --    the Mean Value Theorem only in the F direction. But it could have been
  --    the other way around and it is odd to not have symmetry in the hypotheses
  {E : Type*} [NormedAddCommGroup E] /-[NormedSpace ℝ E]-/ [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {u : Set (E × F)} (hu : IsOpen u)
  {f'x : E × F → E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'x_cont : ContinuousOn f'x u) (hf'y_cont : ContinuousOn f'y u)
  (hf'x : ∀ z ∈ u, HasFDerivAt (f ∘ (·, z.2)) (f'x z) z.1)
  (hf'y : ∀ z ∈ u, HasFDerivAt (f ∘ (z.1, ·)) (f'y z) z.2) :
    ContinuousOn (fun z => (f'x z).coprod (f'y z)) u
    ∧ ∀ z ∈ u, HasFDerivAt f ((f'x z).coprod (f'y z)) z := by
  sorry

end PartialFDeriv

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

-- with parameters as dynamical variables we recover the standard PL hypotheses
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

-- for fixed parameters we recover the standard PL hypotheses
theorem IsPicardLindelofWithParamL.isPicardLindelofL'
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → F × E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)}
  {x₀ : E} {z₀ z : F} {a r L K : ℝ≥0}
  (hf : IsPicardLindelofWithParamL f t₀ z₀ x₀ a r L K) (hz : z ∈ closedBall z₀ a) :
    IsPicardLindelofL (fun t x => f t (z,x)) t₀ x₀ a r L K := by
  sorry


-- Picard-Lindelöf ODE existance with parameters (cont in time, Lipschitz in init data and params)
theorem IsPicardLindelofWithParamL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → F × E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} (ht₀ : tmin < t₀ ∧ t₀ < tmax)
  --(hminmax : tmin < tmax)
  {x₀ : E} {z₀ : F} {a r L K : ℝ≥0} (hf : IsPicardLindelofWithParamL f t₀ z₀ x₀ a r L K) :
    ∃ α : (F × E) → ℝ → E, (∀ zx ∈ closedBall (z₀, x₀) r, α zx t₀ = zx.2 ∧
      ∀ t ∈ Ioo tmin tmax, HasDerivAt (α zx) (f t ⟨zx.1, α zx t⟩) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall (z₀, x₀) r) := by
  sorry

-- Picard-Lindelöf ODE existance with parameters (jointly continuous version)
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
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Ioo tmin tmax)} --(hminmax : tmin < tmax)
  {x₀ : E} {a r L K : ℝ≥0} (hr : 0 < r)
  (α : E × ℝ → E)
  --(hfpl : let t₀' : Icc tmin tmax := ⟨t₀, mem_Icc_of_Ioo t₀.prop⟩;
  --    IsPicardLindelofL f t₀' x₀ a r L K)
  {f' : ℝ → E → E →L[ℝ] E}
  (hf'pl : let t₀' : Icc tmin tmax := ⟨t₀, mem_Icc_of_Ioo t₀.prop⟩;
      IsPicardLindelofL
        (fun t (⟨x,X⟩ : E × E) => (f t x, f' t x X))
        t₀' (x₀,0) a r L K)
  (hfd : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a,
    HasFDerivWithinAt (f t) (f' t x) (closedBall x₀ a) x)
  (hfdc : ∀ x ∈ (closedBall x₀ a), ContinuousOn (f · x) (Icc tmin tmax))
  (hfdl : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f' t) (closedBall x₀ a))
  (hαl : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith L (α ⟨·,t⟩) (ball x₀ r))
  (hα : ∀ x ∈ ball x₀ r, α ⟨x, t₀⟩ = x
      ∧ ∀ t ∈ Ioo tmin tmax, HasDerivAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) t) :
    ∃ β : E × ℝ → E →L[ℝ] E, ∀ x ∈ ball x₀ r,
      ∀ t ∈ Ioo tmin tmax, HasDerivAt (β ⟨x, ·⟩) ((f' t (α (x, t))).comp (β ⟨x, t⟩)) t
        ∧ HasFDerivAt (α ⟨·, t⟩) (β ⟨x, t⟩) x := by
  -- first start with some housekeeping
  let t₀' : Icc tmin tmax := ⟨t₀, mem_Icc_of_Ioo t₀.prop⟩
  have ha : 0 < a := sorry -- use hf.2.mul_max_le, hr and hminmax
  have ha' : (0:ℝ) < a := sorry -- use hf.2.mul_max_le, hr and hminmax
  have hra : r < a := sorry
  have hra' : r.toReal < a.toReal := sorry
  have hfc : ContinuousOn ↿f (Icc tmin tmax ×ˢ closedBall x₀ a) := sorry -- uniform Lipschitz
  have hfdc : ContinuousOn ↿f' (Icc tmin tmax ×ˢ closedBall x₀ a) :=
    sorry -- uniform Lipschitz
  have huncurryf' : uncurry f' = ↿f' := rfl
  -- XXX: basically the properties of f' could be packaged into its own IsPicardLindelof structure
  -- define α deformation and find its differential equation
  have hdef ⦃ε : ℝ⦄ (hε : ε ≠ 0) (Δ : E) ⦃x : E⦄
    (hx : x ∈ ball x₀ r) (hxεΔ : x + ε • Δ ∈ ball x₀ r)
    ⦃t⦄ (ht : t ∈ Ioo tmin tmax) :
      HasDerivAt
        (fun s => ε⁻¹ • (α ⟨x + ε • Δ, s⟩ - α ⟨x, s⟩))
        (ε⁻¹ • (f t (α ⟨x + ε • Δ, t⟩) - f t (α ⟨x, t⟩)))
        t
    := ((hα _ hxεΔ |>.2 _ ht).sub (hα _ hx |>.2 _ ht) |>.const_smul ε⁻¹)
  -- change it to a linear equation using the Hadamard lemma
  obtain ⟨g, hg⟩ := hadamard_div
    (f := ↿f)
    (f' := ↿f')
    --(C := K)
    (v := Ioo tmin tmax)
    --⟨Metric.isOpen_ball (x := x₀) (ε := a), isOpen_Ioo (a := tmin) (b := tmax), convex_ball x₀ a, convex_Ioo tmin tmax⟩
    (convex_ball x₀ a)
    (by
      intro t ht x hx
      constructor
      · exact hfdc.continuousAt sorry
      · exact (hfd t (mem_Icc_of_Ioo ht) x (mem_of_mem_of_subset hx ball_subset_closedBall)).hasFDerivAt sorry
      )
  -- prove IsPicardLindelofParamL for the deformation equation
  have hfpl : IsPicardLindelofL f t₀' x₀ a r L K := {
    lipschitzOnWith := fun t ht => by -- XXX: fun_prop?
      have := (LipschitzWith.prod_fst).comp_lipschitzOnWith (hf'pl.lipschitzOnWith t ht)
      have := this.comp <| (LipschitzWith.prodMk_right (0:E)).lipschitzOnWith
        (s := closedBall x₀ a)
      simp only [← closedBall_prod_same, one_mul, mul_one, comp_def] at this
      exact this (fun x hx => ⟨hx, mem_closedBall_self a.prop⟩)
    continuousOn := fun x hx => by
      have : MapsTo (fun s ↦ (s, x)) (Icc tmin tmax) (Icc tmin tmax ×ˢ closedBall x₀ ↑a)
        := fun s hs => ⟨hs,hx⟩
      fun_prop (disch:=assumption)
    norm_le := fun t ht x hx => by
      have := (hf'pl.norm_le t ht ⟨x,0⟩)
      simp only [← closedBall_prod_same] at this
      have := this ⟨hx, mem_closedBall_self a.prop⟩
      simp only [Prod.norm_mk, map_zero, norm_zero, norm_nonneg, sup_of_le_left] at this
      exact this
    mul_max_le := hf'pl.mul_max_le
  }
  -- the manipulations with `this` that go on until invoking `hg` could go into a helper lemma
  have := fun t ht x X hx =>
    (hf'pl.norm_le t ht ⟨x,X⟩ hx)
  simp only [Prod.norm_mk, sup_le_iff, ← closedBall_prod_same, mem_prod, and_imp] at this
  conv at this =>
    intro t ht x
    rw [forall_comm]
    ext hx X
    rw [mem_closedBall_zero_iff]
  replace this := fun t ht x hx X (hX : ‖(a:ℝ)⁻¹ • X‖ = 1) => by
    have := (this t ht x hx X)
    rw [norm_smul, norm_inv, norm_eq_abs, abs_eq, inv_mul_eq_one₀ ha'.ne.symm] at hX
    replace this := (mul_le_mul_left (show 0 < (a:ℝ)⁻¹ by sorry)).mpr (this hX.symm.le).2
    nth_rw 1 [← abs_of_nonneg (show 0 ≤ (a:ℝ)⁻¹ by sorry), ← norm_eq_abs,
      ← norm_smul, ← map_smul] at this
    nth_rw 2 [← NNReal.coe_inv a] at this
    rw [← NNReal.coe_mul] at this
    exact this
  replace this := fun t ht x hx X => this t ht x hx ((a:ℝ) • X)
  simp only [smul_smul, inv_mul_cancel₀ ha'.ne.symm, one_smul] at this
  replace this := fun t ht x (hx : x ∈ ball x₀ ↑a) => ContinuousLinearMap.opNorm_le_of_unit_norm
    (sorry) (this t ht x (mem_of_mem_of_subset hx ball_subset_closedBall))
  simp only [← uncurry_apply_pair f', huncurryf'] at this
  replace this := fun t (ht : t ∈ Icc tmin tmax) =>
    --XXX fix later: mismatch between t ∈ Icc and t ∈ Ioo
    (hg t sorry).1.2 (this t ht)
  --XXX: these commented lines could help prove hgpl.lipschitzOnWith below
  --     but need to sort out `ball` vs `closeBall` domain issues
  --have := fun t ht =>
  --  (hf'pl.lipschitzOnWith t ht)
  --simp only [← closedBall_prod_same, lipschitzOnWith_iff_norm_sub_le, mem_prod,
  --  dist_zero_right, Prod.mk_sub_mk, Prod.norm_mk, sup_le_iff, and_imp,
  --  Prod.forall] at this
  --have := fun t ht x hx X hX =>
  --  (this t ht x X hx hX x 0 hx (mem_closedBall_self a.prop)).2
  --simp only [map_zero, sub_zero, sub_self, norm_zero, norm_nonneg, sup_of_le_right] at this
  --have := fun t ht x (hx : x ∈ ball x₀ a) X (hX : X ∈ ball 0 a) =>
  --  (this t ht x (mem_of_mem_of_subset hx ball_subset_closedBall))
  --    X (mem_of_mem_of_subset hX ball_subset_closedBall)
  --have := fun t ht x hx => ContinuousLinearMap.opNorm_le_of_ball ha K.prop (this t ht x hx)
  --have hf'b := fun t ht x hx => (hg t ht).1.2 (C := K) (this t (mem_Icc_of_Ioo ht)) x hx
  have hr2 : r / 2 < r := sorry
  have hr2' : (r / 2).toReal < r.toReal := sorry
  have hr22' : (r / 2 / 2).toReal < (r / 2).toReal := sorry
  have hr22'pos : 0 < (r / 2 / 2).toReal := sorry
  have hgpl :
      IsPicardLindelofWithParamL (fun t (b : (ℝ × E × E) × E) => let ((ε, Δ, x), A) := b;
          (g (t, α (x + ε • Δ, t), α (x, t))) A)
        t₀' (0,0,x₀) 0 (r / 2) (r / 2 / 2) L (2*K) := {
    lipschitzOnWith := sorry
    continuousOn := sorry
    norm_le := fun t ht ⟨⟨ε,Δ,x⟩,A⟩ h => by
      simp only [← closedBall_prod_same] at h
      simp only [mem_prod] at h
      obtain ⟨⟨hε, hΔ, hx⟩, hA⟩ := h
      simp only [← Function.curry_apply α] at hα
      have hαx0 : curry α x t₀ ∈ closedBall x₀ (r / 2).toReal := by
        convert hx
        exact (hα x (mem_of_mem_of_subset hx (closedBall_subset_ball (x:=x₀) hr2'))).1
      have hαx := (hα x
        (mem_of_mem_of_subset hx (closedBall_subset_ball (x:=x₀) hr2'))).2
      have hαx_mem := hfpl.mem_closedBall'
        (mem_of_mem_of_subset hαx0 (closedBall_subset_closedBall hr2'.le))
        hαx
      have hxε : x + ε • Δ ∈ closedBall x₀ (r / 2).toReal := by
        sorry -- maybe need ε < 1
      have hαxε0 : curry α (x + ε • Δ) t₀ ∈ closedBall x₀ (r / 2) := by
        convert hxε
        exact (hα (x + ε • Δ) (mem_of_mem_of_subset hxε (closedBall_subset_ball (x:=x₀) hr2'))).1
      have hαxε := (hα (x + ε • Δ)
        (mem_of_mem_of_subset hxε (closedBall_subset_ball (x:=x₀) hr2'))).2
      have hαxε_mem := hfpl.mem_closedBall'
        (mem_of_mem_of_subset hαxε0 (closedBall_subset_closedBall hr2'.le))
        hαxε
      simp only
      calc
        _ ≤ _ := ContinuousLinearMap.le_opNorm _ A
        _ ≤ ↑(a⁻¹ * L) * a := by
          gcongr
          --XXX: conflict between `ball _ a` and `closedBall _ a`
          --     possibly need to allow shrinking of domain
          · sorry --exact this t ht _ (hαx_mem t ht) _ (hαxε_mem t ht)
          · simp only [mem_closedBall_zero_iff] at hA
            apply hA.trans _
            sorry
        _ = _ := by
          rw [NNReal.coe_mul, mul_comm _ (a.toReal), ← mul_assoc]
          rw [NNReal.coe_inv a, mul_inv_cancel₀ ha'.ne.symm, one_mul]
    mul_max_le := sorry
  }
  -- obtain solution γ with appropriate initial data, use its continuity and Lipschitz-ness
  obtain ⟨γ, hγ⟩ :=
    hgpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith (mem_Ioo.mp t₀.prop)
  have hγcont : ContinuousOn ↿γ
      (closedBall ((0, 0, x₀), 0) (r / 2 / 2).toReal ×ˢ Ioo tmin tmax) := by
    sorry --use uniform Lipschitz-ness
  -- use ODE uniqueness to show that γ coincides with deformation when ε ≠ 0
  have hinit ⦃ε : ℝ⦄ (hε : ε ≠ 0) (Δ : E) ⦃x : E⦄
    (hx : x ∈ ball x₀ r) (hxεΔ : x + ε • Δ ∈ ball x₀ r) :
      ε⁻¹ • (α ⟨x + ε • Δ, t₀⟩ - α ⟨x, t₀⟩) = Δ := by
    sorry
  have hαγ : ∀ εΔx : ℝ × E × E, let ⟨ε,Δ,x⟩ := εΔx;
    (((ε,Δ,x),Δ) ∈ closedBall ((0, 0, x₀), 0) (r / 2 / 2).toReal) → ε ≠ 0 → ∀ t ∈ Ioo tmin tmax,
      γ ((ε,Δ,x),Δ) t = ε⁻¹ • (α (x + ε • Δ, t) - α (x, t)) := by
    intro ⟨ε,Δ,x⟩ hball hε
    change EqOn _ _ _
    --have xxx A hA := hγ.1 ⟨⟨ε,Δ,x⟩,A⟩ hA
    apply ODE_solution_unique_of_mem_Ioo (t₀ := t₀) (s := fun t => univ) (K := K)
      _
      t₀.prop
      (fun t ht => by
        refine ⟨(hγ.1 ⟨⟨ε,Δ,x⟩,Δ⟩ sorry).2 t ht, mem_univ _⟩
        )
      (fun t ht => by
        -- forgot to change f - f into g in `hdef`
        --refine ⟨hdef hε Δ (x:=x) sorry sorry ht, mem_univ _⟩
        refine ⟨?_, mem_univ _⟩
        sorry
        )
      ((hγ.1 _ hball).1.trans (hinit (ε:=ε) sorry Δ (x:=x) sorry sorry).symm)
    sorry
  -- set ε = 0 in γ and show that it is locally linear in initial data, use linearity of ODE
  have hβcont : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ closedBall x₀ (r / 2 / 2).toReal,
      ContinuousOn (fun Δ ↦ γ ((0, Δ, x), Δ) t) (closedBall 0 (r / 2 / 2).toReal) :=
    sorry
  have hβadd : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ closedBall x₀ (r / 2 / 2).toReal,
    ∀ z ∈ closedBall (0:E) (r / 2 / 2).toReal, ∀ y ∈ closedBall (0:E) (r / 2 / 2).toReal,
    z + y ∈ closedBall 0 (r / 2 / 2).toReal →
      (fun Δ ↦ γ ((0, Δ, x), Δ) t) (z + y) =
        (fun Δ ↦ γ ((0, Δ, x), Δ) t) z + (fun Δ ↦ γ ((0, Δ, x), Δ) t) y :=
    sorry
  have hβsmul : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ closedBall x₀ (r / 2 / 2).toReal,
    ∀ c : ℝ, ∀ y ∈ closedBall (0:E) (r / 2 / 2).toReal, c • y ∈ closedBall 0 (r / 2 / 2).toReal →
      (fun Δ ↦ γ ((0, Δ, x), Δ) t) (c • y) = c • (fun Δ ↦ γ ((0, Δ, x), Δ) t) y :=
    sorry
  -- use the local linearity to extract the corresponding β linear map
  have hβγ t (ht : t ∈ Ioo tmin tmax) x (hx : x ∈ closedBall x₀ (r / 2 / 2).toReal) :=
    extend_continuousLinearMap_of_nhd_zero_apply
      (hU := closedBall_mem_nhds 0 hr22'pos)
      (f := fun Δ => γ ((0, Δ, x), Δ) t)
      (hf := hβcont t ht x hx)
      (hfadd := hβadd t ht x hx)
      (hfsmul := hβsmul t ht x hx)
  letI βsub : (closedBall x₀ (r / 2 / 2).toReal) ×ˢ (Ioo tmin tmax) → E →L[ℝ] E :=
    fun ⟨⟨x,t⟩, ⟨hx,ht⟩⟩ => extend_continuousLinearMap_of_nhd_zero
      (hU := closedBall_mem_nhds 0 hr22'pos)
      (f := fun Δ => γ ((0, Δ, x), Δ) t)
      (hf := hβcont t ht x hx)
      (hfadd := hβadd t ht x hx)
      (hfsmul := hβsmul t ht x hx)
  have βext := Function.Injective.extend_apply (Subtype.val_injective) βsub 0
  replace hβγ t (ht : t ∈ Ioo tmin tmax) x (hx : x ∈ closedBall x₀ (r / 2 / 2).toReal)
      Δ (hΔ : Δ ∈ closedBall (0:E) (r / 2 / 2).toReal) := by
    have := congr_arg (fun m => m Δ) (βext ⟨⟨x,t⟩, ⟨hx,ht⟩⟩)
    simp only at this
    exact this.trans (hβγ t ht x hx Δ hΔ)
  have hγ0 (x : E) (hx : x ∈ closedBall x₀ (r / 2 / 2).toReal)
    t (ht : t ∈ Ioo tmin tmax)
    (Δ : E) (hΔ : Δ ∈ closedBall 0 (r / 2 / 2).toReal)
      := by
    have := (hγ.1 ((0,Δ,x), Δ) sorry).2 t ht
    simp only at this
    simp only [← hβγ t ht x sorry Δ sorry] at this
    have this := this.congr_of_eventuallyEq
      (Set.EqOn.eventuallyEq_of_mem (fun t ht => hβγ t ht x sorry Δ sorry)
        (Ioo_mem_nhds ht.1 ht.2))
    simp only [zero_smul, add_zero, ← ContinuousLinearMap.comp_apply] at this
    simp only [((hg t ht).2.2 (α (x, t)) sorry).1] at this
    exact this
  set β := extend Subtype.val βsub 0
  replace hγ0 (x : E) (hx : x ∈ closedBall x₀ (r / 2 / 2).toReal) :=
    (hasDerivAt_iff_hasDerivAt_apply_on_nhd_zero
      (I := Ioo tmin tmax)
      sorry
      (convex_Ioo tmin tmax)
      (isOpen_Ioo)
      (closedBall_mem_nhds 0 hr22'pos)).mp (hγ0 x hx)
  -- use β for the ∃ goal
  use β
  intro x hx t ht
  -- split the goal into the ODE for β and into relating β to the derivative of α
  refine ⟨?ode, ?fderiv⟩
  case ode =>
    -- first, simplify the deformation ODE to satisfy the ODE goal
    -- XXX: mismatch on the hypothesis hx, the neighborhood to which x belongs
    exact hγ0 x sorry t ht
  case fderiv =>
    -- second, convert FDeriv into LineDeriv for α, rewrite using ε → 0 quotient limit
    apply hasFDerivAt_of_hasLineDerivAt_continuous_on_nhd
      (f' := fun y => β (y, t))
      ((isOpen_ball (x:=x₀) (ε:=(r / 2 / 2).toReal)).mem_nhds sorry)
      (fun x ↦ α (x, t))
      _
      sorry
    intro y hy Δ
    -- it is sufficient to deal with Δ in a neighborhood of 0
    suffices Δ ∈ closedBall 0 (r / 2 / 2).toReal →
        HasLineDerivAt ℝ (fun x ↦ α (x, t)) (((fun y ↦ β (y, t)) y) Δ) y Δ by
      -- rescale Δ to meet goal, use HasLineDerivAt.smul or hasLineDerivAt_smul_iff
      sorry
    intro hΔ
    -- rewrite LineDeriv as limit on punctured neighborhood
    simp only [hasLineDerivAt_iff_tendsto_slope_zero]
    -- rewrite punctured neighborhood limit as limit on subset
    set NZ : Set ℝ := {0}ᶜ
    let NZtoR : NZ → ℝ := Subtype.val
    rw [← Subtype.range_val (s := NZ), show Subtype.val = NZtoR by rfl]
    rw [← Filter.tendsto_comap'_iff self_mem_nhdsWithin]
    rw [comap_nhdsWithin_range NZtoR 0]
    -- simplify fraction formula and show that it is equal to g on subset
    set F := (fun ε:ℝ => ε⁻¹ • (α (y + ε • Δ, t) - α (y, t)))
    have heq : F ∘ NZtoR = (fun ε => γ ((ε, Δ, y), Δ) t) ∘ NZtoR := by sorry
    simp only [heq]
    -- take advantage of the ε ≠ 0 condition to rewrite the limit in terms of β, use continuity
    have hy' := mem_of_mem_of_subset hy (ball_subset_closedBall)
    simp only [hβγ t ht y hy' Δ hΔ]
    apply Filter.Tendsto.comp _ Filter.tendsto_map
    apply Filter.Tendsto.mono_left _ Filter.map_comap_le
    apply ContinuousAt.tendsto
    apply ContinuousOn.continuousAt
      _ (closedBall_mem_nhds 0 hr22'pos)
    rw [show ↿γ = (fun Xt => γ Xt.1 Xt.2) from rfl] at hγcont
    --fun_prop --XXX: doesn't work, even after the rw in hγcont
    apply hγcont.comp (f := fun ε => (((ε, Δ, y), Δ), t)) (by fun_prop) _
    unfold MapsTo; intro ε hε
    simp only [mem_prod, ht, and_true, ← closedBall_prod_same]
    exact ⟨⟨hε, hΔ, hy'⟩, hΔ⟩

-- solution of ODE is jointly continuously differentiable, when driving function
-- is sufficiently regular
-- theorem ...

theorem PL_joint_diff
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Ioo tmin tmax)}
  {x₀ : E} {a r L K : ℝ≥0} (hr : 0 < r)
  (α : E × ℝ → E)
  {f' : ℝ → E → E →L[ℝ] E}
  (hf'pl : let t₀' : Icc tmin tmax := ⟨t₀, mem_Icc_of_Ioo t₀.prop⟩;
      IsPicardLindelofL
        (fun t (⟨x,X⟩ : E × E) => (f t x, f' t x X))
        t₀' (x₀,0) a r L K)
  (hfd : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a,
    HasFDerivWithinAt (f t) (f' t x) (closedBall x₀ a) x)
  (hfdc : ∀ x ∈ (closedBall x₀ a), ContinuousOn (f · x) (Icc tmin tmax))
  (hfdl : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f' t) (closedBall x₀ a))
  (hα : ∀ x ∈ ball x₀ r, α ⟨x, t₀⟩ = x
      ∧ ∀ t ∈ Ioo tmin tmax, HasDerivAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) t) :
    ∃ α' : E × ℝ → E × ℝ →L[ℝ] E,
      ContinuousOn α' (ball x₀ r ×ˢ Ioo tmin tmax)
      ∧ ∀ x ∈ ball x₀ r, --XXX: probably need to shrink r
        ∀ t ∈ Ioo tmin tmax,
          HasFDerivAt α (α' ⟨x,t⟩) ⟨x,t⟩ := by
  -- get partial derivatives of α from ODE and from `PL_deviation`
  -- each one is continuous on the existence domain so then use
  --   `hasFDerivWithinAt_continuousOn_of_partial_continuousOn_open`
  -- to get joint continuous differentiability
  sorry

end PLJointDiff

#check IsCompact.exists_bound_of_continuousOn
