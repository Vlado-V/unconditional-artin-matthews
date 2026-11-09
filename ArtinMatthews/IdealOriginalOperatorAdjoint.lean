module

public import ArtinMatthews.IdealOriginalPatternAdjoint
public import ArtinMatthews.IdealSlotPairing
public import ArtinMatthews.IdealOperatorPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The two original slot averages transport the pattern adjoint to the
literal ideal operator and preserve its all-test energy bound. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealOperator_reverse_pairing {I G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (patterns : Finset I) (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (f g : MarkedPhysicalMarking P (k + ell) → ℂ) :
    idealLabelPairing P f (idealOperator patterns C (-Θ) (-ζ)
      (fun i a b aux => star (K i b a aux)) g) =
      star (idealLabelPairing P g (idealOperator patterns C Θ ζ K f)) := by
  unfold idealOperator idealOperatorWithLaws
  simp_rw [idealSlotAverage_pairing, idealLabelPairing_sum_right, star_sum]
  exact sum_congr rfl (fun i _ =>
    idealPattern_reverse_pairing P hV (C i) Θ ζ (K i) (idealSlotAverage f) (idealSlotAverage g))

theorem idealOperator_reverse_energy_le {I G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (patterns : Finset I) (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) (U : ℝ)
    (hForward : ∀ f, idealLabelEnergy P (k + ell) (idealOperator patterns C Θ ζ K f) ≤
      U ^ 2 * idealLabelEnergy P (k + ell) f)
    (g : MarkedPhysicalMarking P (k + ell) → ℂ) :
    idealLabelEnergy P (k + ell) (idealOperator patterns C (-Θ) (-ζ)
      (fun i a b aux => star (K i b a aux)) g) ≤ U ^ 2 * idealLabelEnergy P (k + ell) g := by
  let E := idealLabelEnergy P (k + ell)
  let F := idealOperator patterns C Θ ζ K
  let v := idealOperator patterns C (-Θ) (-ζ) (fun i a b aux => star (K i b a aux)) g
  have hE (u : MarkedPhysicalMarking P (k + ell) → ℂ) : 0 ≤ E u := by
    change 0 ≤ idealLabelEnergy P (k + ell) u
    rw [← idealLabelNorm_sq P hV u]
    exact sq_nonneg _
  have hpair : idealLabelPairing P v v = star (idealLabelPairing P g (F v)) :=
    idealOperator_reverse_pairing P hV patterns C Θ ζ K v g
  have hnorm : E v ≤ idealLabelNorm P g * idealLabelNorm P (F v) := by
    change idealLabelEnergy P (k + ell) v ≤ _
    rw [← idealLabelPairing_self_norm P hV v, hpair]
    simpa only [Complex.star_def, Complex.norm_conj] using
      idealLabelPairing_norm_le P hV g (F v)
  have hsquared : E v ^ 2 ≤ E g * E (F v) := by
    simpa only [E, mul_pow, idealLabelNorm_sq P hV] using
      pow_le_pow_left₀ (hE v) hnorm 2
  have hbound : E v ^ 2 ≤ E g * (U ^ 2 * E v) :=
    hsquared.trans (mul_le_mul_of_nonneg_left (hForward v) (hE g))
  change E v ≤ U ^ 2 * E g
  by_cases hzero : E v = 0
  · rw [hzero]
    exact mul_nonneg (sq_nonneg U) (hE g)
  · have hv : 0 < E v := lt_of_le_of_ne (hE v) (Ne.symm hzero)
    apply le_of_mul_le_mul_right ?_ hv
    calc
      E v * E v = E v ^ 2 := (pow_two _).symm
      _ ≤ E g * (U ^ 2 * E v) := hbound
      _ = (U ^ 2 * E g) * E v := by ring

end
end ArtinMatthews
