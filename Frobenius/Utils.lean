import Mathlib

section

variable
  {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup A] [NormedAddCommGroup B]
  [NormedAddCommGroup C] [NormedSpace 𝕜 A] [NormedSpace 𝕜 B] [NormedSpace 𝕜 C]

theorem fderiv_to_fst
  {f : A × B → C} {U : Set A} {V : Set B} {x : A × B} {f' : A × B →L[𝕜] C}
  (hx : x ∈ (U ×ˢ V)) (hf : HasFDerivWithinAt f f' (U ×ˢ V) x)
  : HasFDerivWithinAt (f ⟨·, x.2⟩) (f'.comp (ContinuousLinearMap.inl 𝕜 A B)) U x.1
  := by
    have : (f ⟨·, x.2⟩) = f ∘ ((ContinuousMap.id A).prodMk (ContinuousMap.const A x.2))
      := by rfl
    rw [this]
    have hg : HasFDerivWithinAt ((ContinuousMap.id A).prodMk (ContinuousMap.const A x.2)) (ContinuousLinearMap.inl 𝕜 A B) U x.1 := by
      apply HasFDerivWithinAt.prodMk
      apply hasFDerivWithinAt_id
      apply hasFDerivWithinAt_const
    apply HasFDerivWithinAt.comp
    exact hf
    exact hg
    unfold Set.MapsTo
    intro a ha
    simp
    constructor
    exact ha
    rw [Set.mem_prod] at hx
    exact hx.right

end

section PicardLindelof -- Assume we have the machinery from the PR #21777.

-- PR#25304 - cont partials => total deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax} {x₀ : E} {a r L K : NNReal}

-- NOTE: Uses a different `IsPicardLindelof` structure than the PR.
--
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelof f tmin t₀ tmax x₀ K a L) :
    ∃ α : E × ℝ → E, (∀ x ∈ Metric.closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Set.Icc tmin tmax) t) ∧
      ContinuousOn α (Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax) := by sorry

end PicardLindelof
