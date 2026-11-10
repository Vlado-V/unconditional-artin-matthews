module

public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcRawEdgePatternPartition
public import ArtinMatthews.MarkedMinorArcDirtyEnergyBudget
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
public import ArtinMatthews.MarkedMinorArcDirtyPatternRowActual
public import ArtinMatthews.MarkedMinorArcDirtyPatternSwap
public import ArtinMatthews.MarkedMinorArcRawEdgeDirtySectorEnergy
public import ArtinMatthews.MarkedMinorArcRawProductMass
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

/-! Actual arithmetic discharge of both asymmetric dirty-sector rows.
The promoted sector includes every store pattern; the remaining sector
has no promotions and at least one store. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdge_dirty_sector_actual_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (v₀ c T A H W ρ A₀ G : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hA₀ : 0 ≤ A₀) (hG : 0 ≤ G)
    (hdepth : 100*(2*G+3*A₀+3)<(Fintype.card J:ℝ))
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
        ‖markedRawEdgePatternSymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) (fun _ => 1) hZ
          (markedRawEdgePromotedKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y
            ((Real.log x)^A₀) ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ))) f s‖^2) ≤
          ((Real.log x)^(-G))^2 * ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 ∧
      (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawEdgePatternSymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) (fun _ => 1) hZ
          (markedRawEdgeStoreOnlyKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y
            ((Real.log x)^A₀) ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ))) f s‖^2) ≤
          ((Real.log x)^(-G))^2 * ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  let Λ : ℝ := (2/Real.log 2)^(Fintype.card J)
  let S : ℝ := 2*G+3*A₀+1
  let C₀ : ℝ := markedRawEdgeNoPromotionConstant (Fintype.card J) v₀ H W A Λ
  have hΛ : 1 ≤ Λ := one_le_pow₀ markedDirty_transfer_constant_one_le
  have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
  have hv₀₀ : 0 ≤ v₀ := zero_le_one.trans hv₀
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀,markedRawEdgeNoPromotionConstant]
    positivity
  have hdepthS : 100*(S+2)<(Fintype.card J:ℝ) := by dsimp [S]; linarith
  have hsuppAbs : ∀ t,ψ t ≠ 0 → |t| ≤ A := by
    intro t ht
    exact abs_le.mpr (hsupp ht)
  have hreflect := markedRawEdgeReflectedCutoff_bounds ψ hψ hsuppAbs
  have hsuppR : Function.support (markedRawEdgeReflectedCutoff ψ) ⊆ Set.Icc (-A) A := by
    intro t ht
    exact abs_le.mp (hreflect.2 t ht)
  filter_upwards [markedDirty_pattern_promoted_row_log_saving e he hinj ψ η v₀ c T A H W ρ Λ A₀ S
      hv₀ hc hT hH hW hρ₀ hρ₁ hΛ₀ hdepthS hη hψ hsupp,
    markedDirty_pattern_promoted_row_log_saving e he hinj (markedRawEdgeReflectedCutoff ψ) η v₀ c T A H W ρ Λ A₀ S
      hv₀ hc hT hH hW hρ₀ hρ₁ hΛ₀ hdepthS hη hreflect.1 hsuppR,
    markedDirty_pattern_noPromotion_row_crude e he,
    markedRawEdgeFlagChargeSwap_actual_bound_eventually e he,
    markedDirty_actual_band_transfer_eventually e he,
    markedRawActualPrimeBand_disjoint_eventually e hinj,
    markedDirty_asymmetric_energy_eventually hC₀ hG hA₀,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hprom hpromR hnop hswap htransfer hdisj hbudget hlog
  intro Z hZ r d₀ Y q w χ f hY hq₀ hq₁ hw hτ hbox hχ hχsym hf
  let ν := markedRawActualPrimeAtom e q x
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let χg := markedRawDirtyGoodCutoff e x r d₀ Y w χ
  let ε : ℝ := (Real.log x)^(-S)
  let C : ℝ := C₀*((Real.log x)^A₀)^3
  have ht := htransfer q hq₀ hq₁
  have hε : 0 ≤ ε := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hC : 0 ≤ C := mul_nonneg hC₀ (pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hlog) _) _)
  have hY₁ : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  have hQ : 1 ≤ (Real.log x)^A₀ := Real.one_le_rpow hlog hA₀
  have hχg : ∀ s,‖χg s‖ ≤ 1 := markedRawDirtyGoodCutoff_norm_le e x r d₀ Y w χ hχ
  have hχgsym : ∀ z a,MarkedRawMemorySymmetric (fun m => χg (z,(a,m))) :=
    markedRawDirtyGoodCutoff_symmetric e x r d₀ Y w χ hχsym
  have hτne : ∀ z : Z,markedMinorIntegerTau r z.1 ≠ 0 := by
    intro z hz
    have hh := (hτ z.1 z.2).1
    rw [hz,abs_zero] at hh
    exact (not_le_of_gt hc) hh
  have hr := markedRawEdge_dirty_sector_energy_of_rows ν V ht.1 (fun j => (ht.2.1 j).1)
    hdisj hZ ψ η d₀ Y ((Real.log x)^A₀) ρ v₀ Λ ε C χg hχgsym
    (zero_lt_one.trans_le hv₀) hΛ hε hC (hswap q hq₀ hq₁)
    (by
      intro β hβ s
      exact hprom Z hZ r d₀ Y q w χ β s hY hq₀ hq₁ hw hτ hbox hχ hβ)
    (by
      intro β hβ s
      exact hnop ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) Z hZ ψ η
        r d₀ Y ((Real.log x)^A₀) q ρ H W A v₀ Λ χg β s (w s.1)
        hY₁ hQ hq₀ hq₁ hρ₀ hρ₁.le hH hW hA hv₀ hΛ₀ hη hψ hsuppAbs hχg hβ
        (hw s.1) (hτne s.1) (fun z hz => hbox s.1 ⟨z,hz⟩))
    (by
      intro β hβ s
      exact hpromR Z hZ r d₀ Y q w χ β s hY hq₀ hq₁ hw hτ hbox hχ hβ)
    (by
      intro β hβ s
      exact hnop ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) Z hZ (markedRawEdgeReflectedCutoff ψ) η
        r d₀ Y ((Real.log x)^A₀) q ρ H W A v₀ Λ χg β s (w s.1)
        hY₁ hQ hq₀ hq₁ hρ₀ hρ₁.le hH hW hA hv₀ hΛ₀ hη hreflect.1 hreflect.2 hχg hβ
        (hw s.1) (hτne s.1) (fun z hz => hbox s.1 ⟨z,hz⟩)) f hf
  have hmass : 0 ≤ ∑ s,markedRawStateMass ν s*‖f s‖^2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (markedRawStateMass_nonneg ν ht.1 s) (sq_nonneg _))
  have hbudget' : ε*(ε+C) ≤ ((Real.log x)^(-G))^2 := hbudget
  have hstoreBudget : C*ε ≤ ((Real.log x)^(-G))^2 := by
    apply le_trans _ hbudget'
    nlinarith [sq_nonneg ε]
  exact ⟨hr.1.trans (mul_le_mul_of_nonneg_right hbudget' hmass),
    hr.2.trans (mul_le_mul_of_nonneg_right hstoreBudget hmass)⟩

end
end ArtinMatthews
