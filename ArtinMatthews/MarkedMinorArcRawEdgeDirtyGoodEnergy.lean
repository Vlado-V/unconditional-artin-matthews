module

public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcRawEdgeActualPartition
public import ArtinMatthews.MarkedMinorArcDirtyEnergyBudget
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
public import ArtinMatthews.MarkedMinorArcDirtySectorActual
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic energy saving for the literal dirty subtype sum, with
all nonempty-promotion and pure-store choices present. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdge_dirty_good_actual_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (v₀ c T A H W ρ A₀ G : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hA₀ : 0 ≤ A₀) (hG : 0 ≤ G)
    (hdepth : 100*(2*G+3*A₀+5)<(Fintype.card J:ℝ))
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
      (r d₀ Y q : ℝ) (w : Z → ℤ × ℤ)
      (χ f : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → 0 ≤ q → q ≤ 1 →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) →
      (∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m)))) →
      (∀ z a,MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) →
      (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawEdgeDirtySymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y
          ((Real.log x)^A₀) ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ) f s‖^2) ≤
        ((Real.log x)^(-G))^2 * ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  have hdepth' : 100*(2*(G+1)+3*A₀+3)<(Fintype.card J:ℝ) := by nlinarith
  filter_upwards [markedRawEdge_dirty_sector_actual_energy e he hinj ψ η v₀ c T A H W ρ A₀ (G+1)
      hv₀ hc hT hA hH hW hρ₀ hρ₁ hA₀ (by linarith) hdepth' hη hψ hsupp,
    markedDirty_actual_band_transfer_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3:ℝ))]
    with x hsector htransfer hlog
  intro Z hZ r d₀ Y q w χ f hY hq₀ hq₁ hw hτ hbox hχ hχsym hf
  let ν := markedRawActualPrimeAtom e q x
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let χg := markedRawDirtyGoodCutoff e x r d₀ Y w χ
  let K := fun (_ _ : J → Bool) => markedRawEdgeJointCoefficient hZ ψ η d₀ Y ((Real.log x)^A₀) ρ χg
  let Fp := markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
    (markedRawEdgePromotedKernel K) f
  let Fs := markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
    (markedRawEdgeStoreOnlyKernel K) f
  let E : ℝ := ∑ s,markedRawStateMass ν s*‖f s‖^2
  let ε : ℝ := (Real.log x)^(-(G+1))
  have ht := htransfer q hq₀ hq₁
  have hμ : ∀ s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z,
      0 ≤ markedRawStateMass ν s := markedRawStateMass_nonneg ν ht.1
  have hE : 0 ≤ E := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hsectors := hsector Z hZ r d₀ Y q w χ f hY hq₀ hq₁ hw hτ hbox hχ hχsym hf
  have hp : (∑ s,markedRawStateMass ν s*‖Fp s‖^2) ≤ ε^2*E := hsectors.1
  have hs : (∑ s,markedRawStateMass ν s*‖Fs s‖^2) ≤ ε^2*E := hsectors.2
  have hsplit : markedRawEdgeDirtySymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^A₀) ρ χg f = Fp+Fs := by
    exact (markedRawEdgeDirtySymmetrized_eq_pattern ν V hZ ψ η d₀ Y ((Real.log x)^A₀) ρ χg f).trans
      (markedRawEdgeDirtySymmetrized_eq_promoted_add_storeOnly ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ K f)
  have hthree := markedDirty_weighted_three_energy_le (markedRawStateMass ν) hμ Fp Fs (fun _ => 0)
  simp only [add_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,Finset.sum_const_zero] at hthree
  change (∑ s,markedRawStateMass ν s *
    ‖markedRawEdgeDirtySymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^A₀) ρ χg f s‖^2) ≤ _
  rw [hsplit]
  calc
    _ ≤ 3*((∑ s,markedRawStateMass ν s*‖Fp s‖^2)+(∑ s,markedRawStateMass ν s*‖Fs s‖^2)) := hthree
    _ ≤ 3*(ε^2*E+ε^2*E) := by gcongr
    _ ≤ (9*ε^2)*E := by nlinarith [mul_nonneg (sq_nonneg ε) hE]
    _ ≤ ((Real.log x)^(-G))^2*E :=
      mul_le_mul_of_nonneg_right (markedDirty_three_log_budget hlog) hE

end
end ArtinMatthews
