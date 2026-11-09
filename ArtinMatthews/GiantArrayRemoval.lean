module

public import ArtinMatthews.GiantBoundedProgression
public import ArtinMatthews.MarkedCorrelationLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Positive-sieve removal of the actual marking arrays from the fixed-
residue giant-factor sum. The variance and prime-mass estimates are already
proved; only a subsequent bound on each marked prime sum is analytic input. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology

def giantFixedProgressionPrimeSum {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T : ℝ) : ℝ → ℂ :=
  markedPrimeCorrelation Φ T (giantFixedResidueLiteralCoefficient U ε)

def giantFixedProgressionArrayPrimeSum {M : ℕ} (U : Finset (ZMod M)ˣ)
    {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℝ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T : ℝ) : ℝ → ℂ :=
  markedPrimeSingleArrayCorrelation e Φ T (giantFixedResidueLiteralCoefficient U ε)

theorem giant_fixed_progression_prime_eq_bounded {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε T : ℝ) (hε : ε ≤ 1/4) (hT : 0 ≤ T)
    (Φ : ℝ → ℝ) (hΦzero : Φ 0 = 0) :
    ∀ᶠ x : ℝ in atTop, giantFixedProgressionPrimeSum U ε Φ T x =
      markedPrimeCorrelation Φ T (giantFixedResidueCenteredCoefficient U ε) x := by
  filter_upwards [giant_fixed_residue_test_eq U ε T hε hT Φ hΦzero] with x hx
  unfold giantFixedProgressionPrimeSum markedPrimeCorrelation
  apply Finset.sum_congr rfl
  intro u hu
  exact hx u (Finset.mem_filter.mp hu).1

theorem giant_fixed_progression_array_eq_bounded {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε T : ℝ) (hε : ε ≤ 1/4) (hT : 0 ≤ T)
    (Φ : ℝ → ℝ) (hΦzero : Φ 0 = 0) :
    ∀ᶠ x : ℝ in atTop, ∀ {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℝ),
      giantFixedProgressionArrayPrimeSum U e ε Φ T x =
        markedPrimeSingleArrayCorrelation e Φ T (giantFixedResidueCenteredCoefficient U ε) x := by
  filter_upwards [giant_fixed_residue_test_eq U ε T hε hT Φ hΦzero] with x hx
  intro I _ _ e
  unfold giantFixedProgressionArrayPrimeSum markedPrimeSingleArrayCorrelation
  apply Finset.sum_congr rfl
  intro u hu
  rw [hx u (Finset.mem_filter.mp hu).1]

/-- Unconditional positive-sieve comparison for the actual uncapped giant
statistic and any fixed family of disjoint admissible marking arrays. -/
theorem giant_fixed_progression_deweighting {M : ℕ} (U : Finset (ZMod M)ˣ)
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1/10 : ℝ)<e j i ∧ e j i<1/5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0<Fintype.card J)
    (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0≤T) (ha : 0<a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0)
    (hΦ0 : ∀ t, 0≤Φ t) (hlow : ∀ t<a, Φ t=0) :
    ∀ᶠ x : ℝ in atTop,
      ‖∑ u ∈ (Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime),
        (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u *
          (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
            (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ)‖ ≤
      (markedPrimeDeweightingConstant (Fintype.card I) (1/960048) 20000 Φ T /
        Real.sqrt (Fintype.card J)) * x / Real.log x := by
  have hzero : Φ 0=0 := hlow 0 ha
  have hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u+1).Prime →
      ‖giantFixedResidueCenteredCoefficient U ε x u‖ ≤ 1 :=
    (giant_fixed_residue_coefficient_bound U hε hεq).mono (fun _ hx u _ => hx u)
  have hbound := marked_actual_prime_deweighting_canonical e he hinj hJ
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow (giantFixedResidueCenteredCoefficient U ε)
    (by norm_num : (0 : ℝ)≤1) hF
  filter_upwards [hbound,giant_fixed_residue_test_eq U ε T hεq.le hT Φ hzero] with x hx htest
  have heq : (∑ u ∈ (Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime),
        (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u *
          (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
            (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ)) =
      ∑ u ∈ (Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime),
        (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueCenteredCoefficient U ε x u *
          (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
            (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [htest u (Finset.mem_filter.mp hu).1]
  rw [heq]
  simpa only [one_mul] using hx

/-- The unweighted original sum is controlled by the average of the genuine
single-array sums plus the proved b^(-1/2) positive-sieve error. -/
theorem giant_fixed_progression_average_bound {M : ℕ} (U : Finset (ZMod M)ˣ)
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1/10 : ℝ)<e j i ∧ e j i<1/5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0<Fintype.card J)
    (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0≤T) (ha : 0<a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0)
    (hΦ0 : ∀ t, 0≤Φ t) (hlow : ∀ t<a, Φ t=0) :
    ∀ᶠ x : ℝ in atTop,
      ‖giantFixedProgressionPrimeSum U ε Φ T x‖ ≤
        (∑ j, ‖giantFixedProgressionArrayPrimeSum U (e j) ε Φ T x‖) / Fintype.card J +
        (markedPrimeDeweightingConstant (Fintype.card I) (1/960048) 20000 Φ T /
          Real.sqrt (Fintype.card J)) * x / Real.log x := by
  filter_upwards [giant_fixed_progression_deweighting U e he hinj hJ ε hε hεq
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow] with x hx
  have havg := marked_average_norm_bound
    ((Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime))
    (fun u => (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u)
    (fun j u => divisorWeight Finset.univ (fun i => markedLogPowerBand (e j i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u /
        independentArrayMean (fun i => markedLogPowerBand (e j i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x))) hJ
  exact havg.trans (add_le_add le_rfl hx)

end
end ArtinMatthews
