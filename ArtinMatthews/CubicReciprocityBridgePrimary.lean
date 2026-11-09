module

public import ArtinMatthews.CubicReciprocityNonprincipalModel
public import ArtinMatthews.CubicReciprocityBridgeFrobenius


set_option backward.privateInPublic true
@[expose] public section

/-! Compatible primary generators in the two actual Eisenstein models. -/
noncomputable section

namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic

/-- Every Eisenstein prime away from three has a nonzero generator primary
in the concrete complex model used by the cubic numerator character. -/
theorem exists_cubicMoment_primary_generator (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ p ≠ 0 ∧
      CubicFirstMoment.primary (heckeIntegersEquivCubicEisenstein p) := by
  obtain ⟨p, hP, hp, _⟩ := cubicJacobi_exists_primary_generator P hg
  have hp0 : p ≠ 0 := by
    intro hzero
    have hP0 : P ≠ 0 := NeZero.ne P
    apply hP0
    rw [hP, hzero, Ideal.span_singleton_eq_bot.mpr rfl]
    rfl
  have h3lambda : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    change (omega - 1) ^ 2 = 3 * -omega
    linear_combination omega_sq_for_norm
  have h3 : (3 : O) ∣ p - 1 := h3lambda.trans hp
  refine ⟨p, hP, hp0, ?_⟩
  change (3 : CubicFirstMoment.Eisenstein) ∣ heckeIntegersEquivCubicEisenstein p - 1
  simpa only [map_ofNat, map_sub, map_one] using
    map_dvd heckeIntegersEquivCubicEisenstein h3

end ArtinMatthews
