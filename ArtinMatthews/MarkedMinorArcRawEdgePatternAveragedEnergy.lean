module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternSymmetrized


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy and Schur for the genuine source-slot averaged rows.
The two sides may have different bounds, as required for pure-store and
pure-promotion sectors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgePatternReverseEnergy_nonneg
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) :
    0 ≤ markedRawEdgePatternReverseEnergy ν δ γ hZ A v₀ f s := by
  unfold markedRawEdgePatternReverseEnergy
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (norm_nonneg _) (div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le
      (markedRawMemorySchurWeight_pos hv₀ _).le)) (sq_nonneg _))

theorem markedRawSlotAverageReal_nonneg
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : MarkedRawState P M B Z → ℝ) (hF : ∀ s, 0 ≤ F s) (s : MarkedRawState P M B Z) :
    0 ≤ markedRawSlotAverageReal F s := by
  unfold markedRawSlotAverageReal
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => hF _))

theorem markedRawEdgePattern_source_average_cauchy
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) :
    ‖markedRawSlotAverage (markedRawEdgePatternApply ν δ γ hZ A f) s‖ ^ 2 ≤
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ A v₀) s *
        markedRawSlotAverageReal (markedRawEdgePatternReverseEnergy ν δ γ hZ A v₀ f) s := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let Slots := (j : J) → Equiv.Perm (Fin (pads+1))
  let Choice := Σ σ : Slots, MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s)
  let N := Fintype.card Slots
  let coeff := fun c : Choice =>
    markedRawEdgeChoiceCharge δ γ hZ (markedRawSlotEquiv c.1 s) c.2 *
      markedRawEdgeChoiceFreshMass ν hZ (markedRawSlotEquiv c.1 s) c.2 *
      A (markedRawEdgeChoicePromoted c.2) c.2.store (markedRawSlotEquiv c.1 s)
        (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2)
  have h := markedGhostChoice_finite_cauchy coeff
    (fun c => f (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2))
    (fun c => markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv c.1 s) c.2) /
      markedRawMemorySchurWeight v₀ (markedRawSlotEquiv c.1 s).2.2)
    (fun _ => div_pos (markedRawMemorySchurWeight_pos hv₀ _) (markedRawMemorySchurWeight_pos hv₀ _))
  have hh : ‖∑ σ : Slots, markedRawEdgePatternApply ν δ γ hZ A f (markedRawSlotEquiv σ s)‖ ^ 2 ≤
      (∑ σ : Slots, markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ (markedRawSlotEquiv σ s)) *
      (∑ σ : Slots, markedRawEdgePatternReverseEnergy ν δ γ hZ A v₀ f (markedRawSlotEquiv σ s)) := by
    simp only [Choice, Fintype.sum_sigma] at h
    dsimp only [coeff] at h
    unfold markedRawEdgePatternApply markedRawEdgePatternWeightedRow markedRawEdgePatternReverseEnergy
    convert h using 1
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro c _
    field_simp [(markedRawMemorySchurWeight_pos hv₀ (markedRawSlotEquiv σ s).2.2).ne',
      (markedRawMemorySchurWeight_pos hv₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c)).ne']
  calc
    _ = ((N : ℝ)⁻¹) ^ 2 *
        ‖∑ σ : Slots, markedRawEdgePatternApply ν δ γ hZ A f (markedRawSlotEquiv σ s)‖ ^ 2 := by
      simp only [markedRawSlotAverage, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
      rfl
    _ ≤ ((N : ℝ)⁻¹) ^ 2 *
        ((∑ σ : Slots, markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ (markedRawSlotEquiv σ s)) *
          (∑ σ : Slots, markedRawEdgePatternReverseEnergy ν δ γ hZ A v₀ f (markedRawSlotEquiv σ s))) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by unfold markedRawSlotAverageReal; change _ = (N:ℝ)⁻¹ * _ * ((N:ℝ)⁻¹ * _); ring

theorem markedRawEdgePatternSymmetrized_energy_le_of_rows
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hδ : ∀ j, 0 ≤ δ j) (hγ : ∀ j, 0 ≤ γ j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m))))
    {v₀ R C : ℝ} (hv₀ : 0 < v₀) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ s, markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A v₀) s ≤ R)
    (hcol : ∀ s, markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => (γ j : ℂ)) (fun j => (δ j : ℂ)) hZ
        (markedRawEdgePatternReverse A) v₀) s ≤ C)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) :
    (∑ s, markedRawStateMass ν s *
      ‖markedRawEdgePatternSymmetrized ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A f s‖ ^ 2) ≤
      R * C * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 := by
  classical
  let g := markedRawSlotAverage f
  let back := markedRawEdgePatternWeightedRow ν (fun j => (γ j : ℂ)) (fun j => (δ j : ℂ)) hZ
    (markedRawEdgePatternReverse A) v₀
  have hg : ∀ z a, MarkedRawMemorySymmetric (fun m => g (z,(a,m))) := markedRawSlotAverage_symmetric f hf
  have hginv : ∀ σ s, ‖g (markedRawSlotEquiv σ s)‖ ^ 2 = ‖g s‖ ^ 2 := by
    intro σ s
    dsimp only [g]
    rw [markedRawSlotAverage_slots]
  calc
    _ ≤ R * ∑ s, markedRawStateMass ν s * markedRawSlotAverageReal
        (markedRawEdgePatternReverseEnergy ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A v₀ g) s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      change markedRawStateMass ν s *
        ‖markedRawSlotAverage (markedRawEdgePatternApply ν (fun j => (δ j : ℂ))
          (fun j => (γ j : ℂ)) hZ A g) s‖ ^ 2 ≤ _
      have hp := markedRawEdgePattern_source_average_cauchy ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ))
        hZ A hv₀ g s
      have he := markedRawSlotAverageReal_nonneg _
        (markedRawEdgePatternReverseEnergy_nonneg ν (fun j => (δ j : ℂ))
          (fun j => (γ j : ℂ)) hZ A hv₀ g) s
      exact (mul_le_mul_of_nonneg_left hp (markedRawStateMass_nonneg ν hν s)).trans
        ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrow s) he)
          (markedRawStateMass_nonneg ν hν s)).trans_eq (by ring))
    _ = R * ∑ s, markedRawStateMass ν s * ‖g s‖ ^ 2 * back s := by
      rw [markedRawSlotAverageReal_integral,
        markedRawEdgePatternReverseEnergy_column ν δ γ hν hδ hγ hZ A hAl hAr hv₀ g hg]
    _ = R * ∑ s, markedRawStateMass ν s * ‖g s‖ ^ 2 * markedRawSlotAverageReal back s := by
      rw [markedRawSlotAverage_weighted_invariant ν _ back hginv]
    _ ≤ R * (C * ∑ s, markedRawStateMass ν s * ‖g s‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      exact (mul_le_mul_of_nonneg_left (hcol s)
        (mul_nonneg (markedRawStateMass_nonneg ν hν s) (sq_nonneg _))).trans_eq (by ring)
    _ ≤ _ := by
      have he := markedRawSlotAverage_energy_le ν hν f
      calc
        _ = (R*C) * ∑ s, markedRawStateMass ν s * ‖g s‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hR hC)

end
end ArtinMatthews
