module

public import ArtinMatthews.MarkedArrayProgressions
public import ArtinMatthews.MarkedArrayCoefficientMass
public import ArtinMatthews.MarkedProgressionEnvelope


set_option backward.privateInPublic true
@[expose] public section

/-! Actual marking-array progression asymptotics. Structural bounds on the
prime bands and their two coefficient masses imply all-logarithmic saving;
no progression remainder is supplied as an assumption. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

/-- The actual summed progression discrepancy for a finite marking array. -/
noncomputable def markedArrayProgressionDiscrepancy {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
        Φ ((u : ℝ) / x) * ∏ i, (bandWeight (P i) (W i) u) ^ a i) -
      ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * representedArrayEulerMean P W a|

theorem markedArrayProgressionDiscrepancy_nonneg {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : 0 ≤ markedArrayProgressionDiscrepancy P W a Φ T x R := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- A finite, explicit domination by the analytic envelope. -/
theorem marked_array_progression_envelope_bound {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hP : ∀ i p, p ∈ P i → p.Prime)
    (α β δ c v V C x : ℝ) (hx : 1 < x) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hmin : ∀ i p, p ∈ P i → Real.exp ((Real.log x) ^ α) ≤ (p : ℝ))
    (hmax : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ β))
    (hW : ∀ i, v ≤ W i)
    (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ V)
    (hrecip : (∑ t ∈ representedArrayChoices P a,
      |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) ≤ C)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    markedArrayProgressionDiscrepancy P W a Φ T x ⌊x ^ c⌋₊ ≤
      ((3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) / v ^ (∑ i, a i) +
        (∫ t in Set.Ioc 0 T, Φ t) * C) *
      markedProgressionEnvelope x α β δ c (∑ i, a i) V (∑ i, a i) := by
  classical
  let m := ⌊(Real.log x) ^ δ⌋₊
  let s := ∑ i, a i
  let Z := Real.exp (2 * (Real.log x) ^ β)
  let N := max 1 ((Finset.univ.biUnion P).card : ℝ)
  let I := ∫ t in Set.Ioc 0 T, Φ t
  let J := ∫ t in Set.Ioc 0 T, |deriv Φ t|
  let D := 3 * J / v ^ s
  let H := I * C
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hI : 0 ≤ I := integral_nonneg hΦ0
  have hJ : 0 ≤ J := integral_nonneg (fun _ => abs_nonneg _)
  have hD : 0 ≤ D := div_nonneg (by positivity) (pow_nonneg hv.le _)
  have hH : 0 ≤ H := mul_nonneg hI hC
  have hZ : 1 ≤ Z := Real.one_le_exp_iff.mpr (by positivity)
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hN0 : 0 ≤ N := le_trans zero_le_one (le_max_left _ _)
  have hNZ : N ≤ Z := by
    apply max_le hZ
    have hprimeQ : ∀ p ∈ Finset.univ.biUnion P, p.Prime := by
      intro p hp
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      exact hP i p hi
    apply marked_prime_set_card_le (Finset.univ.biUnion P) hprimeQ hZ0
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hmax i p hi
  have hcoef : (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) ≤
      (Z / v) ^ s := by
    apply representedArrayCoefficient_mass_le P W a hv hZ0 hW
    intro i
    exact marked_prime_set_card_le (P i) (hP i) hZ0 (hmax i)
  have hR : (⌊x ^ c⌋₊ : ℝ) ≤ x ^ c := Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hHar : (harmonic ⌊x ^ c⌋₊ : ℝ) ≤ 1 + Real.log x := by
    apply (harmonic_floor_le_one_add_log (x ^ c) (Real.one_le_rpow hx.le hc0)).trans
    rw [Real.log_rpow hx0]
    nlinarith
  have hp0 : N ^ (2 * m) ≤ Z ^ (2 * m + 1) := by
    exact (pow_le_pow_left₀ hN0 hNZ _).trans (pow_le_pow_right₀ hZ (by omega))
  have hp1 : N ^ (2 * m + 1) ≤ Z ^ (2 * m + 1) := pow_le_pow_left₀ hN0 hNZ _
  have hround : ((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1) ≤
      ((2 * m + 2 : ℕ) : ℝ) * Z ^ (2 * m + 1) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hp0
      (Nat.cast_nonneg (2 * m + 1) : (0 : ℝ) ≤ (2 * m + 1 : ℕ))) hp1
    convert h using 1
    push_cast
    ring
  let L := (((s + 2 * m : ℕ) : ℝ) / Real.exp ((Real.log x) ^ α)) * Real.exp V +
    2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let E₁ := x ^ c * ((2 * m + 2 : ℕ) : ℝ) * Z ^ (2 * m + 1 + s)
  let E₂ := x * (1 + Real.log x) * L
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hfirst : ((⌊x ^ c⌋₊ : ℝ) * (3 * J) *
      (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1))) *
      (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) ≤ D * E₁ := by
    calc
      _ ≤ (x ^ c * (3 * J) * (((2 * m + 2 : ℕ) : ℝ) * Z ^ (2 * m + 1))) *
          (Z / v) ^ s := by gcongr
      _ = _ := by dsimp [D, E₁]; simp only [div_pow, pow_add]; ring
  have hsecond : (((x * I) * (harmonic ⌊x ^ c⌋₊ : ℝ)) * L) *
      (∑ t ∈ representedArrayChoices P a,
        |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) ≤ H * E₂ := by
    calc
      _ ≤ (((x * I) * (1 + Real.log x)) * L) * C := by gcongr
      _ = _ := by dsimp [H, E₂]; ring
  have herror := marked_array_progression_error P W a ha hdis hP m ⌊x ^ c⌋₊
    (Real.exp_pos _) hmin hV hmass Φ hx0 hT hΦ hderiv hΦT hΦ0
  change markedArrayProgressionDiscrepancy P W a Φ T x ⌊x ^ c⌋₊ ≤ _ at herror
  calc
    _ ≤ D * E₁ + H * E₂ := herror.trans (add_le_add hfirst hsecond)
    _ ≤ (D + H) * (E₁ + E₂) := by
      nlinarith [mul_nonneg hD hE₂, mul_nonneg hH hE₁]
    _ = _ := by
      dsimp only [D, H, E₁, E₂, L, I, J, m, s, Z, markedProgressionEnvelope, markedFactorialTail]
      push_cast
      ring

/-- Only structural bounds on the finite prime bands and normalized tuple
coefficients enter the asymptotic theorem. -/
structure MarkedArrayAsymptoticBounds {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ)
    (α β v V C x : ℝ) : Prop where
  disjoint : Pairwise fun i j => Disjoint (P i) (P j)
  prime : ∀ i p, p ∈ P i → p.Prime
  lower : ∀ i p, p ∈ P i → Real.exp ((Real.log x) ^ α) ≤ (p : ℝ)
  upper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ β)
  normalizer : ∀ i, v ≤ W i
  primeMass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ V
  coefficientMass : (∑ t ∈ representedArrayChoices P a,
    |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) ≤ C

/-- The actual array discrepancy saves every logarithmic power under
eventual structural band bounds, uniformly through `floor(x^c)`. -/
theorem marked_array_progression_all_log_tendsto {ι : Type*} [Fintype ι]
    (P : ℝ → ι → Finset ℕ) (W : ℝ → ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (α β δ c v V C A : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hband : ∀ᶠ x : ℝ in atTop, MarkedArrayAsymptoticBounds (P x) (W x) a α β v V C x)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / x *
      markedArrayProgressionDiscrepancy (P x) (W x) a Φ T x ⌊x ^ c⌋₊) atTop (𝓝 0) := by
  let B := ((3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) / v ^ (∑ i, a i) +
    (∫ t in Set.Ioc 0 T, Φ t) * C)
  have hlimit := (markedProgressionEnvelope_tendsto α β δ c (∑ i, a i) V A
    (∑ i, a i) hα hβ hδ hsum hc1 hV).const_mul B
  simp only [mul_zero] at hlimit
  apply squeeze_zero' _ _ hlimit
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _)
      (by linarith)) (markedArrayProgressionDiscrepancy_nonneg _ _ _ _ _ _ _)
  · filter_upwards [hband, eventually_gt_atTop (1 : ℝ)] with x hb hx
    have hbound := marked_array_progression_envelope_bound (P x) (W x) a ha hb.disjoint
      hb.prime α β δ c v V C x hx hc0 hc1.le hv hV hC hb.lower hb.upper hb.normalizer
      hb.primeMass hb.coefficientMass Φ hT hΦ hderiv hΦT hΦ0
    have h := mul_le_mul_of_nonneg_left hbound
      (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le A) (show 0 ≤ x by linarith))
    convert h using 1
    ring

/-- The usual unnormalized form: the actual progression discrepancy is
`o(x * (log x)^(-A))`, with its Euler mean defined by the marking array. -/
theorem marked_array_progression_all_log_isLittleO {ι : Type*} [Fintype ι]
    (P : ℝ → ι → Finset ℕ) (W : ℝ → ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (α β δ c v V C A : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hband : ∀ᶠ x : ℝ in atTop, MarkedArrayAsymptoticBounds (P x) (W x) a α β v V C x)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedArrayProgressionDiscrepancy (P x) (W x) a Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (mul_pos (by linarith : 0 < x)
      (Real.rpow_pos_of_pos (Real.log_pos hx) (-A))).ne' h |>.elim
  · apply (marked_array_progression_all_log_tendsto P W a ha α β δ c v V C A
      hα hβ hδ hsum hc0 hc1 hv hV hC hband Φ hT hΦ hderiv hΦT hΦ0).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le]
    field_simp

end ArtinMatthews
