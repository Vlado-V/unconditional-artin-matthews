module

public import ArtinMatthews.GiantMarkedResidual
public import ArtinMatthews.MarkedArrayEulerModel
public import ArtinMatthews.MarkedProgressionEnvelope
public import ArtinMatthews.GiantMarkedArray
public import ArtinMatthews.MarkedArrayCoefficientMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual marking-array progression asymptotics. Structural bounds on the
prime bands and their two coefficient masses imply all-logarithmic saving;
no progression remainder is supplied as an assumption. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

/-- The actual summed progression discrepancy for a finite marking array. -/
noncomputable def giantMarkedArrayProgressionDiscrepancy {ι : Type*} [Fintype ι]
    (G : Finset ℕ) (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
        Φ ((u : ℝ) / x) * (giantWindowDivisorCount G u * ∏ i, (bandWeight (P i) (W i) u) ^ a i)) -
      ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * ((∑ ell ∈ G, 1 / (ell : ℝ)) * representedArrayEulerMean P W a)|

theorem giantMarkedArrayProgressionDiscrepancy_nonneg {ι : Type*} [Fintype ι]
    (G : Finset ℕ) (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : 0 ≤ giantMarkedArrayProgressionDiscrepancy G P W a Φ T x R := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- A finite, explicit domination by the analytic envelope. -/
theorem giant_marked_array_progression_envelope_bound {ι : Type*} [Fintype ι]
    (G : Finset ℕ) (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hP : ∀ i p, p ∈ P i → p.Prime)
    (α β δ c v V C x gexp : ℝ) (hx : 1 < x) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hmin : ∀ i p, p ∈ P i → Real.exp ((Real.log x) ^ α) ≤ (p : ℝ))
    (hmax : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ β))
    (hW : ∀ i, v ≤ W i)
    (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ V)
    (hrecip : (∑ t ∈ representedArrayChoices P a,
      |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) ≤ C)
    (hG : ∀ ell ∈ G, ell.Prime) (hGP : Disjoint G (Finset.univ.biUnion P))
    (hGmin : ∀ ell ∈ G, Real.exp ((Real.log x) ^ α) ≤ (ell : ℝ))
    (hGcard : (G.card : ℝ) ≤ x ^ gexp) (hGmass : (∑ ell ∈ G, 1 / (ell : ℝ)) ≤ 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    giantMarkedArrayProgressionDiscrepancy G P W a Φ T x ⌊x ^ c⌋₊ ≤
      ((3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) / v ^ (∑ i, a i) +
        (∫ t in Set.Ioc 0 T, Φ t) * C) *
      markedProgressionEnvelope x α β δ (c + gexp) (((∑ i, a i : ℕ) : ℝ) + 1) V (∑ i, a i) := by
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
  let L := (((s + 1 + 2 * m : ℕ) : ℝ) / Real.exp ((Real.log x) ^ α)) * Real.exp V +
    2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let E₁ := x ^ (c + gexp) * ((2 * m + 2 : ℕ) : ℝ) * Z ^ (2 * m + 1 + s)
  let E₂ := x * (1 + Real.log x) * L
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hfirst : (((⌊x ^ c⌋₊ : ℝ) * (3 * J) *
      (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1))) * G.card) *
      (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) ≤ D * E₁ := by
    calc
      _ ≤ ((x ^ c * (3 * J) * (((2 * m + 2 : ℕ) : ℝ) * Z ^ (2 * m + 1))) * x ^ gexp) *
          (Z / v) ^ s := by gcongr
      _ = _ := by dsimp [D, E₁]; rw [Real.rpow_add hx0]; simp only [div_pow, pow_add]; ring
  have hsecond : ((((x * I) * (harmonic ⌊x ^ c⌋₊ : ℝ)) * L) *
      (∑ ell ∈ G, 1 / (ell : ℝ))) *
      (∑ t ∈ representedArrayChoices P a,
        |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) ≤ H * E₂ := by
    calc
      _ ≤ ((((x * I) * (1 + Real.log x)) * L) * 1) * C := by gcongr
      _ = _ := by dsimp [H, E₂]; ring
  have herror := giant_marked_array_progression_error G P W a ha hdis hP m ⌊x ^ c⌋₊
    hG hGP (Real.exp_pos _) hmin hGmin hV hmass Φ hx0 hT hΦ hderiv hΦT hΦ0
  change giantMarkedArrayProgressionDiscrepancy G P W a Φ T x ⌊x ^ c⌋₊ ≤ _ at herror
  calc
    _ ≤ D * E₁ + H * E₂ := herror.trans (add_le_add hfirst hsecond)
    _ ≤ (D + H) * (E₁ + E₂) := by
      nlinarith [mul_nonneg hD hE₂, mul_nonneg hH hE₁]
    _ = _ := by
      dsimp only [D, H, E₁, E₂, L, I, J, m, s, Z, markedProgressionEnvelope, markedFactorialTail]
      push_cast
      ring


end ArtinMatthews
