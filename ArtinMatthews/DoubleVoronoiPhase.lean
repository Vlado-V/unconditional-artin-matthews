module

public import ArtinMatthews.KloostermanWeightedStationary


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ring algebra of the dual additive phase. The first transformed
numerator contains the actual square-zero correction from the congruence
average. -/

namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R]

theorem doubleVoronoi_reciprocal_coefficient (m₃ m₄ : Rˣ) (k₁ k₂ : R) :
    (↑(m₃*m₄)⁻¹ : R)*((m₄ : R)*k₂-(m₃ : R)*k₁) =
      (↑m₃⁻¹ : R)*k₂-(↑m₄⁻¹ : R)*k₁ := by
  have h₃ : (m₃*m₄)⁻¹*m₄ = m₃⁻¹ := by
    rw [mul_inv_rev, mul_right_comm, inv_mul_cancel, one_mul]
  have h₄ : (m₃*m₄)⁻¹*m₃ = m₄⁻¹ := by group
  have h₃' := congrArg (fun v : Rˣ => (v : R)) h₃
  have h₄' := congrArg (fun v : Rˣ => (v : R)) h₄
  simp only [Units.val_mul] at h₃' h₄'
  rw [mul_sub, ← mul_assoc, h₃', ← mul_assoc, h₄']

/-- The complete dual phase splits into the ordinary Kloosterman phase
and the linear congruence phase, with all signs preserved. -/
theorem doubleVoronoi_phase_identity (m₃ m₄ a : Rˣ) (k₁ k₂ h : R) (hh : h^2=0) :
    ((m₃ : R)-(m₄ : R))*(a : R) - h*(m₄ : R)*(a : R) -
        k₁*(↑(m₄*a*shiftUnit 1 h hh)⁻¹ : R) -
        k₂*(↑(-(m₃*a))⁻¹ : R) =
      ((m₃ : R)-(m₄ : R))*(a : R) +
        (↑(m₃*m₄)⁻¹ : R)*((m₄ : R)*k₂-(m₃ : R)*k₁)*(↑a⁻¹ : R) +
        h*(k₁*(↑(m₄*a)⁻¹ : R)-(m₄ : R)*(a : R)) := by
  rw [doubleVoronoi_reciprocal_coefficient]
  have hn : (↑(-(m₃*a))⁻¹ : R) = -(↑(m₃*a)⁻¹ : R) := rfl
  rw [hn]
  simp only [mul_inv_rev, Units.val_mul,
    shiftUnit_inv_val, inv_one, Units.val_one, one_pow, mul_one]
  ring

end ArtinMatthews
