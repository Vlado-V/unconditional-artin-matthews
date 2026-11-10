module

public import ArtinMatthews.MarkedMinorArcBanRawEntry
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcBanRawDecay
public import ArtinMatthews.MarkedMinorArcRawCleanGlobal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Restoration of the literal cross-edge ban in the actual clean rule.
The error estimate and the clean estimate are both proved for the same
physical state and tilted measure, then combined with a fixed log margin. -/
namespace ArtinMatthews
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator

/-- Exact difference of counting conjugates for the actual cross-edge ban. -/
theorem markedRawBannedCleanKernel_counting_eq_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B) :
    markedWeightedCountingMatrix (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2)
      (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) bg)=
    markedWeightedCountingMatrix (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2)
      (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg)-
    markedWeightedCountingMatrix (fun u : MarkedRawCleanFiber P Z => markedRawLastMass ν u.2)
      (markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg) := by
  ext u v
  change (Real.sqrt (markedRawLastMass ν u.2) : ℂ)*
      markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) bg u v*
      (Real.sqrt (markedRawLastMass ν v.2) : ℂ)=_
  rw [markedRawBanErrorKernel_eq_difference]
  change _=(Real.sqrt (markedRawLastMass ν u.2) : ℂ)*markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg u v*
      (Real.sqrt (markedRawLastMass ν v.2) : ℂ)-
    (Real.sqrt (markedRawLastMass ν u.2) : ℂ)*
      (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg u v-
        markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ) bg u v)*
      (Real.sqrt (markedRawLastMass ν v.2) : ℂ)
  ring

set_option maxHeartbeats 1500000 in
/-- Actual physical clean norm with the full literal cross-edge ban restored,
at the genuine growing active-slot count. A0=G+6 is independent of the band
exponents. The global tau-ratio premise is the original fixed source box. -/
theorem marked_minor_actual_raw_banned_clean_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L K : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop, ∀ (B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) ⌊(Real.log x)^(1/100:ℝ)⌋₊ B),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s, ‖χ s‖ ≤ 1) →
      ‖markedWeightedCountingMatrix
        (fun u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z =>
          markedRawLastMass (markedRawActualPrimeAtom e q x) u.2)
        (markedRawBannedCleanKernel
          (markedRawCleanKernel hZ ψ η d₀ Y ((Real.log x)^(G+6)) ρ
            (markedRawFirstGoodCutoff r d₀ Y w χ)) bg)‖ ≤ (Real.log x)^(-G) := by
  classical
  let W := (SchwartzMap.seminorm ℝ 0 0) ψ
  have hW : 0 ≤ W := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hWbound : ∀ t, ‖ψ t‖ ≤ W := ψ.norm_le_seminorm ℝ
  have hsupport : ∀ t, ψ t ≠ 0 → |t| ≤ K := fun t ht => abs_le.mpr (hψ ht)
  have hclean := marked_minor_actual_raw_clean_opNorm e he hinj ψ η hη hηnorm
    (show 0<G+1 by linarith) hH hc hL hK hψ
  simp only [show (G+1)+5=G+6 by ring] at hclean
  filter_upwards [hclean,
    markedRawBanErrorKernel_uniform_log_saving e he hinj ψ η 1 K W (G+6) (G+1)
      (by norm_num) hK hW (by linarith) hηnorm hWbound hsupport,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x hx hb hlog
  intro B Z hZ q r d₀ Y ρ w χ bg hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hratio hχ
  have hlogp : 0 < Real.log x := by linarith
  have hY : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg hlogp.le _)).trans hYlo
  have hτnz : ∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0 :=
    fun z => abs_pos.mp (hc.trans_le (hτ _ z.2).1)
  have hepb := markedRawFirstGoodCutoff_norm_le r d₀ Y w χ hχ
  have hbase := hx ⌊(Real.log x)^(1/100:ℝ)⌋₊ B Z hZ q r d₀ Y ρ w χ bg
    hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ
  have herr := hb B Z q r hZ d₀ Y ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
    hq₀ hq₁ hρ₀ hρ₁ hepb hτnz hratio hY bg
  rw [markedRawBannedCleanKernel_counting_eq_sub]
  have hr : (Real.log x)^(-(G+1))=(Real.log x)^(-G)*(Real.log x)⁻¹ := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hlogp]
    congr 1
    ring
  calc
    _ ≤ _+_ := norm_sub_le _ _
    _ ≤ (Real.log x)^(-(G+1))+(Real.log x)^(-(G+1)) := add_le_add hbase herr
    _ = (2/(Real.log x))*(Real.log x)^(-G) := by rw [hr]; ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg hlogp.le _) ((div_le_one hlogp).mpr hlog)

end ArtinMatthews
