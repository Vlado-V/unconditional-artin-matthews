module

public import ArtinMatthews.MarkedMemoryTiltActual
public import ArtinMatthews.MarkedRawBoundary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Uniform convergence of the literal tilted boundary energy to one,
including the true growing active-list length and every memory cutoff. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ArtinMatthews

private theorem abs_prod_sub_one_le {I : Type*} (s : Finset I) (f : I → ℝ) :
    |(∏ i ∈ s, f i)-1| ≤ (∏ i ∈ s, (1+|f i-1|))-1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hv : |∏ i ∈ s, f i| ≤ 1+|(∏ i ∈ s, f i)-1| := by
      calc
        _ = |((∏ i ∈ s, f i)-1)+1| := by congr 1; ring
        _ ≤ |(∏ i ∈ s, f i)-1|+|1| := abs_add_le _ _
        _ = _ := by rw [abs_one]; ring
    calc
      _ = |(f a-1)*(∏ i ∈ s, f i)+((∏ i ∈ s, f i)-1)| := by congr 1; ring
      _ ≤ |f a-1| * |∏ i ∈ s, f i|+|(∏ i ∈ s, f i)-1| := by
        simpa only [abs_mul] using abs_add_le ((f a-1)*(∏ i ∈ s, f i)) ((∏ i ∈ s, f i)-1)
      _ ≤ (1+|f a-1|)*(1+|(∏ i ∈ s, f i)-1|)-1 := by
        nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg (f a-1))]
      _ ≤ _ := by
        have hh : 1+|(∏ i ∈ s, f i)-1| ≤ ∏ i ∈ s, (1+|f i-1|) := by linarith
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hh (by positivity)) 1

theorem markedRawBoundaryEnergy_error_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (M B : ℕ) {Z : Finset (ℤ × ℤ)} (z₀ : Z) {ε : ℝ}
    (hs : ∀ j, |(∑ p : ↥(P j), ν j p)-1| ≤ ε) :
    |markedRawBoundaryEnergy ν M B z₀-1| ≤ Real.exp (Fintype.card J * (M : ℝ) * ε)-1 := by
  classical
  let f : J × Fin M → ℝ := fun i => ∑ p : ↥(P i.1), ν i.1 p
  have heq : markedRawBoundaryEnergy ν M B z₀ = ∏ i : J × Fin M, f i := by
    rw [markedRawBoundaryEnergy_eq, Fintype.prod_prod_type]
    change (∏ j, (∑ p : ↥(P j), ν j p)^M) =
      ∏ j, ∏ _k : Fin M, (∑ p : ↥(P j), ν j p)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [heq]
  apply (abs_prod_sub_one_le Finset.univ f).trans
  apply sub_le_sub_right
  calc
    _ ≤ ∏ _i : J × Fin M, Real.exp ε := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro i _
      dsimp only [f]
      linarith [hs i.1, Real.add_one_le_exp ε]
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        ← Real.exp_nat_mul, Nat.cast_mul]

theorem markedRawBoundary_actual_energy_error {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      |markedRawBoundaryEnergy (markedRawActualPrimeAtom e q x) (markedPadSlots x) B z₀-1| ≤
        Real.exp (markedMemoryBoundaryEnvelope (Fintype.card J) x)-1 := by
  filter_upwards [markedMemory_actual_tilt_mass_error e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hmass hlog
  intro q hq₀ hq₁ B Z z₀
  exact (markedRawBoundaryEnergy_error_le_exp _ _ B z₀ (hmass q hq₀ hq₁)).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (markedMemory_boundary_exponent_le (Fintype.card J) hlog)) 1)

/-- Exact uniform 1+o(1) boundary norm squared from PD04. The quantifiers
include arbitrary q in [0,1], the root, and every memory truncation. -/
theorem markedRawBoundary_actual_energy_uniform_one {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      |markedRawBoundaryEnergy (markedRawActualPrimeAtom e q x) (markedPadSlots x) B z₀-1| < ε := by
  have ht : Tendsto (fun x => Real.exp (markedMemoryBoundaryEnvelope (Fintype.card J) x)-1)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.exp_zero, sub_self] using
      (((Real.continuous_exp.tendsto 0).comp
        (markedMemoryBoundaryEnvelope_tendsto (Fintype.card J))).sub_const 1)
  filter_upwards [markedRawBoundary_actual_energy_error e he, ht.eventually (Iio_mem_nhds hε)] with x hx hεx
  intro q hq₀ hq₁ B Z z₀
  exact (hx q hq₀ hq₁ B Z z₀).trans_lt hεx

end ArtinMatthews
