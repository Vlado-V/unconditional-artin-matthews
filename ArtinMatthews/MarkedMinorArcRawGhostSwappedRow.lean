module

public import ArtinMatthews.MarkedMinorArcRawGhostSwapped
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedMinorArcRawGhostFullRow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The swapped-charge rule has the same cutoff-independent absolute row
bound as the original ghost.  The argument keeps its actual tilted atoms;
only the elementary bound `0 ≤ V_i ≤ 1` is used for the charge comparison. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators

/-- Unit-V row estimate for the literal finite ghost choices.  The atom
mass hypothesis is an elementary finite sum, not a cancellation premise. -/
theorem markedRawGhost_unit_weighted_row {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hs : ∀ j, (∑ p : P j, ν j p) ≤ 2)
    {q ρ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ)
    (hgap : Real.sqrt q < ρ^2) {qStage : ℝ} (hqs₀ : 0 ≤ qStage)
    (hqs : qStage ≤ Real.sqrt q) {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawGhostWeightedAbsRow ν (fun _ => 1) qStage ρ
      (markedRawGhostSchurParameter q ρ) m z hz ≤
        Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  classical
  let v₀ := markedRawGhostSchurParameter q ρ
  have hv₀ : 0 < v₀ := (by norm_num : (0:ℝ)<1).trans_le
    (markedRawGhostSchurParameter_ge_one q ρ)
  have hsqrt : Real.sqrt q ≤ 1 := by
    nlinarith [Real.sq_sqrt hq₀,Real.sqrt_nonneg q]
  have hqs₁ : qStage ≤ 1 := hqs.trans hsqrt
  have hpol : ∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^
      (markedRawGroupHitIndices m j z hz).card ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j _
      exact pow_nonneg (add_nonneg (div_nonneg hqs₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqs₁) (mul_pos hρ hv₀).le)) _
    · intro j _
      exact pow_le_one₀ (add_nonneg (div_nonneg hqs₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqs₁) (mul_pos hρ hv₀).le))
        (markedRawGhostSchurParameter_survival hρ hgap hqs₀ hqs)
  have hExp : (∏ j, Real.exp ((v₀*(1-qStage)*1/ρ)*(∑ p : P j,ν j p))) ≤
      Real.exp ((Fintype.card J : ℝ)*(2*v₀/ρ)) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (2*v₀/ρ) := by
        apply Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
        intro j _
        apply Real.exp_le_exp.mpr
        have hs₀ : 0 ≤ ∑ p : P j,ν j p := Finset.sum_nonneg (fun p _ => hν j p)
        have hc₀ : 0 ≤ v₀*(1-qStage)*1/ρ := by positivity
        have hc₁ : v₀*(1-qStage)*1/ρ ≤ v₀/ρ := by
          apply div_le_div_of_nonneg_right _ hρ.le
          nlinarith
        calc
          _ ≤ (v₀/ρ)*2 := mul_le_mul hc₁ (hs j) hs₀ (div_nonneg hv₀.le hρ.le)
          _ = _ := by ring
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
  exact (markedRawGhost_actual_weighted_row ν hν (fun _ => 1) (by intro j; norm_num)
    hqs₀ hqs₁ hρ hv₀ m z hz).trans
      ((mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le)) hpol).trans hExp)

/-- Genuine swapped-charge row bound in the actual bands, with a threshold
independent of the path stage and the memory cutoff. -/
theorem markedRawGhostSwapped_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (B : ℕ) (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
        (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2),
      markedRawGhostSwappedWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
        (markedRawGhostSchurParameter q ρ) m z hz ≤
        Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  classical
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hV,marked_actual_tilted_atom_comparison_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hV hν hs
  intro qStage hqs₀ hqs B m z hz
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hVp : ∀ j, 0 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    fun j => ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le
  have hv₀ : 0 < markedRawGhostSchurParameter q ρ :=
    (by norm_num : (0:ℝ)<1).trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  exact (markedRawGhostSwappedWeightedAbsRow_le_one _ _ hVp (fun j => (hV j).2.le)
    qStage ρ hv₀ m z hz).trans
      (markedRawGhost_unit_weighted_row _ hνpos (hs q hq₀ hq₁) hq₀ hq₁ hρ hgap hqs₀ hqs m z hz)

end ArtinMatthews
