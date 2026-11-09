module

public import ArtinMatthews.MarkedArrayAsymptotic
public import ArtinMatthews.MarkedArrayBandStructure
public import ArtinMatthews.MarkedActualArrayMass


set_option backward.privateInPublic true
@[expose] public section

/-! All-logarithmic progression estimates for the literal marking bands
from the paper. Every structural band and coefficient hypothesis is
proved using Mertens, disjoint exponents, and exact represented masses. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

/-- The actual single-, cross-, or repeated-array weight has negligible
summed predecessor-progression discrepancy. The Euler mean is its exact
finite independent divisor model; no distribution hypothesis remains. -/
theorem marked_actual_array_progression_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (a : ι → ℕ) (ha : ∀ i, a i = 1 ∨ a i = 2)
    (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedArrayProgressionDiscrepancy
      (fun i => markedLogPowerBand (e i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) a Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have he0 : ∀ i, 0 < e i := fun i => lt_trans (by norm_num) (he i).1
  have hapos : ∀ i, 0 < a i := by
    intro i
    rcases ha i with h | h <;> omega
  have hband : ∀ᶠ x : ℝ in atTop, MarkedArrayAsymptoticBounds
      (fun i => markedLogPowerBand (e i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) a
      (1 / 10) (1 / 5) (Real.log 2 / 2) (Fintype.card ι)
      (markedArrayReciprocalConstant (Fintype.card ι)) x := by
    filter_upwards [marked_actual_band_structure_eventually e he0 hinj
      (fun i => (he i).1.le) (fun i => (he i).2.le),
      marked_actual_array_reciprocal_mass_eventually e he0 hinj a ha] with x hs hm
    exact {
      disjoint := hs.1
      prime := fun i p hp => (hs.2.1 i p hp).1
      lower := fun i p hp => (hs.2.1 i p hp).2.1
      upper := fun i p hp => (hs.2.1 i p hp).2.2
      normalizer := hs.2.2.1
      primeMass := hs.2.2.2
      coefficientMass := hm }
  exact marked_array_progression_all_log_isLittleO
    (fun x i => markedLogPowerBand (e i) x)
    (fun x i => bandReciprocalMass (markedLogPowerBand (e i) x)) a hapos
    (1 / 10) (1 / 5) (1 / 4) c (Real.log 2 / 2) (Fintype.card ι)
    (markedArrayReciprocalConstant (Fintype.card ι)) A
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc0 hc1
    (by positivity) (Nat.cast_nonneg _) (markedArrayReciprocalConstant_pos _).le
    hband Φ hT hΦ hderiv hΦT hΦ0

end ArtinMatthews
