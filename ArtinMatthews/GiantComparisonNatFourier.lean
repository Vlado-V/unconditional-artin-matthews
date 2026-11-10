module

public import ArtinMatthews.MarkedMinorArcProductFourier
public import ArtinMatthews.MarkedMajorArcCircleSource
public import ArtinMatthews.MarkedMinorArcEndpoints


set_option backward.privateInPublic true
@[expose] public section

/-! The natural endpoint polynomial uses the same normalized circle and
positive phase as the finite product-shift pairing. -/
namespace ArtinMatthews
open MeasureTheory AddCircle
open scoped BigOperators
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
local notation "Circle1" => AddCircle (1:ℝ)
local notation "e" => OAI.Problem337.RealPhase.phase

def giantComparisonNatFourier (S : Finset ℕ) (a : ℕ → ℂ) : C(Circle1, ℂ) :=
  markedProductFourierPolynomial (S.map Nat.castEmbedding) (fun n => a n.val.toNat)

theorem giantComparisonNatFourier_apply (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    giantComparisonNatFourier S a (t:Circle1) = ∑ n ∈ S, a n*e (t*(n:ℝ)) := by
  unfold giantComparisonNatFourier
  simp only [markedProductFourierPolynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul,markedMajor_fourier_phase]
  rw [Finset.sum_coe_sort (S.map Nat.castEmbedding) (fun n : ℤ => a n.toNat*e (t*(n:ℝ))),
    Finset.sum_map]
  simp

theorem giantComparisonNatFourier_parseval (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ θ : Circle1, ‖giantComparisonNatFourier S a θ‖^2 ∂AddCircle.haarAddCircle) =
      ∑ n ∈ S, ‖a n‖^2 := by
  unfold giantComparisonNatFourier
  rw [markedProductFourierPolynomial_parseval,
    Finset.sum_coe_sort (S.map Nat.castEmbedding) (fun n : ℤ => ‖a n.toNat‖^2), Finset.sum_map]
  simp

end
end ArtinMatthews
