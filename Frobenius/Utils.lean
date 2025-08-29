/-
Copyright (c) 2025 Jan Růžička. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Růžička, Igor Khavkine
-/
import Mathlib

section

variable
  {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup A] [NormedAddCommGroup B]
  [NormedAddCommGroup C] [NormedSpace 𝕜 A] [NormedSpace 𝕜 B] [NormedSpace 𝕜 C]

theorem fderiv_to_fst
  {f : A × B → C} {x : A × B} {f' : A × B →L[𝕜] C} (hf : HasFDerivAt f f' x)
  : HasFDerivAt (f ⟨·, x.2⟩) (f'.comp (ContinuousLinearMap.inl 𝕜 A B)) x.1
  := by
    have : (f ⟨·, x.2⟩) = f ∘ ((ContinuousMap.id A).prodMk (ContinuousMap.const A x.2))
      := by rfl
    rw [this]
    have hg : HasFDerivAt ((ContinuousMap.id A).prodMk (ContinuousMap.const A x.2)) (ContinuousLinearMap.inl 𝕜 A B) x.1 := by
      apply HasFDerivAt.prodMk
      apply hasFDerivAt_id
      apply hasFDerivAt_const
    apply HasFDerivAt.comp
    exact hf
    exact hg

end

section

lemma subset_of_le {a b ε : ℝ} (hε : 0 < ε) : Set.Icc a b ⊆ Set.Ioo (a-ε) (b+ε) := sorry

-- `f = g` and `f x = g x` implies `deriv f x = deriv g x`
--
theorem deriv_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f g : 𝕜 → F} {x : 𝕜} (h : ∀ y, f y = g y) (hx : f x = g x) : deriv f x = deriv g x := by
  repeat rw [← derivWithin_univ]
  apply derivWithin_congr ((Set.eqOn_univ f g).mpr (funext h)) hx

-- chain rule for `f : 𝕜 → F` and `g : F → E`
--
theorem fderiv_comp'_deriv {𝕜 F E : Type*} [NontriviallyNormedField 𝕜]
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      {g : F → E} {f : 𝕜 → F} {x : 𝕜}
      (hg : DifferentiableAt 𝕜 g (f x))
      (hf : DifferentiableAt 𝕜 f x)
      : deriv (fun x' => g (f x')) x = (fderiv 𝕜 g (f x) : F → E) (deriv f x) := by
    have : ∀ x', g (f x') = (g ∘ f) x' := by
      intro x'
      rfl
    rw [deriv_congr this rfl, fderiv_comp_deriv x hg hf]

-- continuous function on a compact set has a non-negative bound
--
theorem exists_nonneg_bound_of_continuousOn {α : Type*} {E : Type*} [SeminormedAddGroup E]
    [TopologicalSpace α] {s : Set α} (hs : IsCompact s) {f : α → E} (hf : ContinuousOn f s)
    : ∃ C : NNReal, ∀ x ∈ s, ‖f x‖ ≤ C := by
  have ⟨C, h⟩ := hs.exists_bound_of_continuousOn hf
  use ‖C‖₊
  intro x hx
  have : C ≤ ‖C‖₊ := by
    simp only [coe_nnnorm, Real.norm_eq_abs]
    exact le_abs_self C
  exact (h x hx).trans this

-- differentiability of the function `x ↦ fderiv 𝕜 (f x) (g x)` on a set
--
theorem contDiffWithinAt_fderiv {𝕜 E F G} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F → G} {g : E → F} {m n : WithTop ℕ∞} {x₀ : E} {s : Set E} (hx₀ : x₀ ∈ s)
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ Set.univ) (x₀, g x₀)) (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (hmn : m + 1 ≤ n) : ContDiffWithinAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) s x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf hg uniqueDiffOn_univ
    hmn hx₀ ?_)
  simp only [Set.preimage_univ, Set.subset_univ]

-- extensionality for `ContDiffOn`
--
theorem contDiffOn_iff_contDiffWithinAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {n : WithTop ℕ∞} {s : Set E}
    : ContDiffOn 𝕜 n f s ↔ ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x := sorry

-- differentiability of the function `x ↦ fderiv 𝕜 (f x) (g x)`
--
theorem contDiffOn_fderiv {𝕜 E F G} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F → G} {g : E → F} {m n : WithTop ℕ∞} {s : Set E}
    (hf : ContDiffOn 𝕜 m (Function.uncurry f) (s ×ˢ Set.univ)) (hg : ContDiffOn 𝕜 n g s) (hnm : n + 1 ≤ m) :
    ContDiffOn 𝕜 n (fun x => fderiv 𝕜 (f x) (g x)) s := by
  have : ∀ x ∈ s, ContDiffWithinAt 𝕜 n (fun x => fderiv 𝕜 (f x) (g x)) s x := by
    intro x hx
    have hx' : (x, g x) ∈ s ×ˢ Set.univ := Set.mk_mem_prod hx trivial
    apply contDiffWithinAt_fderiv hx (hf.contDiffWithinAt hx') (hg.contDiffWithinAt hx) hnm
  exact contDiffOn_iff_contDiffWithinAt.mpr this

-- continuity of partial derivative
--
@[fun_prop]
theorem continuousOn_fderiv {𝕜 E F G} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} {g : E → F} {n : WithTop ℕ∞} {s : Set E}
    (hf : ContDiffOn 𝕜 n f (s ×ˢ Set.univ)) (hg : ContinuousOn g s) (hn : 1 ≤ n) :
    ContinuousOn (fun x => fderiv 𝕜 (fun y' => f (x, y')) (g x)) s :=
  (contDiffOn_fderiv hf (contDiffOn_zero.mpr hg) hn).continuousOn

end

section Partials

-- PR #25304

-- total derivative as a sum of partial derivatives (on a set)
--
theorem fderivWithin_partials
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {x dx : E} {y dy : F}
  (hf : DifferentiableWithinAt 𝕜 f (s ×ˢ t) (x, y))
  (hx : x ∈ s) (hy : y ∈ t) (hs : IsOpen s) (ht : IsOpen t) :
    fderivWithin 𝕜 f (s ×ˢ t) (x, y) (dx, dy)
    = fderivWithin 𝕜 (fun x' => f ⟨x', y⟩) s x dx + fderivWithin 𝕜 (fun y' => f ⟨x, y'⟩) t y dy := by
    have hinl : DifferentiableWithinAt 𝕜 (fun x' => (x', y)) s x
      := DifferentiableWithinAt.prodMk differentiableWithinAt_id' (differentiableWithinAt_const y)
    have hinr : DifferentiableWithinAt 𝕜 (fun y' => (x, y')) t y
      := DifferentiableWithinAt.prodMk (differentiableWithinAt_const x) differentiableWithinAt_id'

    rw [
      fderivWithin_comp' hf hinl _ (hs.uniqueDiffWithinAt hx) (t := s ×ˢ t) (x := x),
      fderivWithin_comp' hf hinr _ (ht.uniqueDiffWithinAt hy) (t := s ×ˢ t) (x := y),
      DifferentiableWithinAt.fderivWithin_prodMk differentiableWithinAt_id' (differentiableWithinAt_const y) (hs.uniqueDiffWithinAt hx),
      DifferentiableWithinAt.fderivWithin_prodMk (differentiableWithinAt_const x) differentiableWithinAt_id' (ht.uniqueDiffWithinAt hy),
      fderivWithin_id' (hs.uniqueDiffWithinAt hx), fderivWithin_id' (ht.uniqueDiffWithinAt hy)
    ]
    simp
    rw [← ContinuousLinearMap.map_add, Prod.mk_add_mk, add_zero, zero_add]

    · unfold Set.MapsTo
      intro y' hy'
      simp
      exact ⟨hx, hy'⟩
    · unfold Set.MapsTo
      intro x' hx'
      simp
      exact ⟨hx', hy⟩


-- total derivative as a sum of partial derivatives
--
theorem fderiv_partials
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {x dx : E} {y dy : F}
  (hf : DifferentiableAt 𝕜 f (x, y)) :
    fderiv 𝕜 f (x, y) (dx, dy)
    = fderiv 𝕜 (fun x' => f ⟨x', y⟩) x dx + fderiv 𝕜 (fun y' => f ⟨x, y'⟩) y dy
  := by
    rw [← fderivWithin_univ, ← Set.univ_prod_univ, ← fderivWithin_univ, ← fderivWithin_univ]
    exact fderivWithin_partials hf.differentiableWithinAt (Set.mem_univ x) (Set.mem_univ y) isOpen_univ isOpen_univ


/-- If a function `f : E × F → G` has a first partial derivative (within set `s`) `f'xz` at `z`
and has a second partial derivative (within open set `t`) `f'y` continuous on `s ×ˢ t`,
then `f` has a derivative at `z`, with the derivative given by `f'z = f'xz.coprod (f'y z)`.
See `hasFDerivWithinAt_of_partial_fst_continuousOn_prod_open` for the order of derivatives swapped.
-/
theorem hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (ht : IsOpen t)
  {f'xz : E →L[𝕜] G} {f'y : E × F → F →L[𝕜] G}
  (hf'y_cont : ContinuousOn f'y (s ×ˢ t))
  (hf'xz : HasFDerivWithinAt (f ∘ (·, z.2)) f'xz s z.1)
  (hf'y : ∀ z' ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (z'.1, ·)) (f'y z') t z'.2) :
    HasFDerivWithinAt f (f'xz.coprod (f'y z)) (s ×ˢ t) z := sorry

/-- If a function `f : E × F → G` has a second partial derivative (within set `t`) `f'yz` at `z`
and has a first partial derivative (within open set `s`) `f'x` continuous on `s ×ˢ t`,
then `f` has a derivative at `z`, with the derivative given by `f'z = (f'x z).coprod f'yz`.
See `hasFDerivWithinAt_of_partial_snd_continuousOn_prod_open` for the order of derivatives swapped.
-/
theorem hasFDerivWithinAt_of_partial_fst_continuousOn_prod_open
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E × F → G} {s : Set E} {t : Set F} {z : E × F}
  (hz : z ∈ s ×ˢ t) (hs : IsOpen s)
  {f'x : E × F → E →L[𝕜] G} {f'yz : F →L[𝕜] G}
  (hf'x_cont : ContinuousOn f'x (s ×ˢ t))
  (hf'x : ∀ z' ∈ s ×ˢ t, HasFDerivWithinAt (f ∘ (·, z'.2)) (f'x z') s z'.1)
  (hf'yz : HasFDerivWithinAt (f ∘ (z.1, ·)) f'yz t z.2) :
    HasFDerivWithinAt f ((f'x z).coprod f'yz) (s ×ˢ t) z := sorry

end Partials

section PicardLindelof -- Assume we have the machinery from the PR #21777.

-- PR#25304 - cont partials => total deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax} {x₀ : E} {a r L K : NNReal}

-- TODO: prove 3.1 from Hartman

-- NOTE: Uses a different `IsPicardLindelof` structure than the PR.
--
-- theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
--     (hf : IsPicardLindelof f tmin t₀ tmax x₀ K a L) :
--     ∃ α : E × ℝ → E, (∀ x ∈ Metric.closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
--       ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Set.Icc tmin tmax) t) ∧
--       ContinuousOn α (Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax) := by sorry

end PicardLindelof
