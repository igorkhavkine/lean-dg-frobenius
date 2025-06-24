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

section

theorem add_eq_add_left_iff {G : Type*} [AddGroup G] {a b c : G} : a+b = a+c ↔ b = c := by simp
theorem add_eq_add_right_iff {G : Type*} [AddGroup G] {a b c : G} : b+a = c+a ↔ b = c := by simp

theorem fderivWithin_comp'_derivWithin {𝕜 F E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {t : Set F} {s : Set 𝕜} {g : F → E} {f : 𝕜 → F} {x : 𝕜}
    (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : Set.MapsTo f s t) :
    derivWithin (fun x' => g (f x')) s x = (fderivWithin 𝕜 g t (f x) : F → E) (derivWithin f s x) :=
    sorry

end

section Partials

-- PR #25304

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
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelof f tmin t₀ tmax x₀ K a L) :
    ∃ α : E × ℝ → E, (∀ x ∈ Metric.closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Set.Icc tmin tmax) t) ∧
      ContinuousOn α (Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax) := by sorry

end PicardLindelof
