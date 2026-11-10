module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import ArtinMatthews.FiniteIsotropyCounting
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! A separated finite-isotropy slice has its exact stabilizer multiplicity. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ENNReal Pointwise Classical
noncomputable section

variable {Γ X : Type*} [Group Γ] [Countable Γ] [MulAction Γ X]
    [MeasurableSpace X] [MeasurableConstSMul Γ X]
    (μ : Measure X) [SMulInvariantMeasure Γ X μ]
    (ν : Measure (Quotient (MulAction.orbitRel Γ X)))
    [QuotientMeasureEqMeasurePreimage (G := Γ) μ ν]

theorem sourceFiniteSlice_measure (H : Subgroup Γ) [Finite H]
    {F : Set X} (hF : IsFundamentalDomain Γ F μ) (E : Set X) (hE : MeasurableSet E)
    (himage : MeasurableSet (Quotient.mk (MulAction.orbitRel Γ X) '' E))
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H) :
    μ E = (Nat.card H : ℝ≥0∞) * ν (Quotient.mk (MulAction.orbitRel Γ X) '' E) := by
  let f : X → ℝ≥0∞ := E.indicator (fun _ => 1)
  let T : Set (Quotient (MulAction.orbitRel Γ X)) :=
    Quotient.mk (MulAction.orbitRel Γ X) '' E
  have hf : Measurable f := measurable_const.indicator hE
  have hT : MeasurableSet T := himage
  have hsum (x : X) : (∑' γ : Γ, f (γ • x)) =
      (Nat.card H : ℝ≥0∞) * T.indicator (fun _ => 1) (Quotient.mk _ x) := by
    rw [sourceFiniteSlice_indicator_tsum H E hstable hsep x]
    change (if Quotient.mk (MulAction.orbitRel Γ X) x ∈ T then (Nat.card H : ℝ≥0∞) else 0) = _
    by_cases hx : Quotient.mk (MulAction.orbitRel Γ X) x ∈ T
    · rw [ite_eq_left hx, Set.indicator_of_mem hx, mul_one]
    · rw [ite_eq_right hx, Set.indicator_of_notMem hx, mul_zero]
  calc
    μ E = ∫⁻ x, f x ∂μ := (lintegral_indicator_one hE).symm
    _ = ∑' γ : Γ, ∫⁻ x in F, f (γ • x) ∂μ := hF.lintegral_eq_tsum'' f
    _ = ∫⁻ x in F, ∑' γ : Γ, f (γ • x) ∂μ :=
      (lintegral_tsum (fun γ => (hf.comp (measurable_const_smul γ)).aemeasurable)).symm
    _ = ∫⁻ x in F, (Nat.card H : ℝ≥0∞) * T.indicator (fun _ => 1) (Quotient.mk _ x) ∂μ := by
      exact lintegral_congr hsum
    _ = (Nat.card H : ℝ≥0∞) * ∫⁻ x in F, T.indicator (fun _ => 1) (Quotient.mk _ x) ∂μ :=
      lintegral_const_mul _ ((measurable_const.indicator hT).comp
        (measurable_quotient_mk' (s := MulAction.orbitRel Γ X)))
    _ = (Nat.card H : ℝ≥0∞) * ν T := by
      rw [(hF.measurePreserving_quotient_mk ν).lintegral_comp
        (measurable_const.indicator hT)]
      congr 1
      simpa only [one_mul] using (lintegral_indicator_const hT (1 : ℝ≥0∞))

theorem sourceFiniteSlice_quotient_measure (H : Subgroup Γ) [Finite H]
    {F : Set X} (hF : IsFundamentalDomain Γ F μ) (E : Set X) (hE : MeasurableSet E)
    (himage : MeasurableSet (Quotient.mk (MulAction.orbitRel Γ X) '' E))
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H) :
    ν (Quotient.mk (MulAction.orbitRel Γ X) '' E) = (Nat.card H : ℝ≥0∞)⁻¹ * μ E := by
  have hcard : (Nat.card H : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card H ≠ 0)
  rw [sourceFiniteSlice_measure μ ν H hF E hE himage hstable hsep,
    ← mul_assoc, ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

end
end ArtinMatthews
