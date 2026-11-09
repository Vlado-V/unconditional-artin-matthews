module

public import ArtinMatthews.MarkedMajorArcHighPrime
public import ArtinMatthews.MarkedMajorArcPrimeNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual high-frequency prime term with the `1/H` normalization used
by the determinant long coefficient. -/
namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_major_high_prime_normalized (A η τ P : ℝ)
    (hA : 0 ≤ A) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (t H u v : ℝ),
      L^B₀ ≤ |t| → |t| ≤ Real.exp (2*L) →
      Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
      ‖markedMajorNormalizedPrimeSum χ t H u v‖ ≤ 5*L^(-P) := by
  obtain ⟨B₀,hB₀,hprime⟩ := marked_major_high_prime_cancellation A η τ P hA hη hτ hP
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hprime,eventually_gt_atTop (0:ℝ)] with L hprime hLp
  intro q _ hq χ t H u v htlo hthi hHlo hHu huv hvH hvhi
  have hH : 0 < H := (Real.exp_pos _).trans_le hHlo
  apply marked_major_prime_normalization χ t hH hHu huv hvH (Real.rpow_nonneg hLp.le _)
  intro w hw
  exact hprime q hq χ t u w htlo hthi (hHlo.trans hHu) hw.1
    (by linarith [hw.2]) (hw.2.trans hvhi)

end ArtinMatthews
