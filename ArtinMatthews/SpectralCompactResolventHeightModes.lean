module

public import ArtinMatthews.SpectralEisensteinFiniteCusps
public import ArtinMatthews.SpectralEisensteinOutgoingEnergy
public import ArtinMatthews.SpectralEisensteinOutgoingModes
public import ArtinMatthews.SpectralGamma0TruncatedPseudoResolvent
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralEisensteinEquivalentMeans
public import ArtinMatthews.SpectralEisensteinMatchingModes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
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

/-! Genuine true-width outgoing tails in the actual truncated form at
every cutoff above the minimum matching height. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0TruncatedFormData_mem_iff_cusp_representatives (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (u : gamma0EnergySpace N) :
    u∈(gamma0TruncatedFormData N Y hY).subspace ↔
      ∀ i : Gamma0EisensteinCuspClasses N,
        gamma0CuspConstantTerm N (gamma0EisensteinCuspClassRepresentative N i) Y hY
          (gamma0EnergyInclusion N u)=0 := by
  change u∈gamma0TruncatedMeanZeroEnergy N Y hY ↔ _
  rw [mem_gamma0TruncatedMeanZeroEnergy_iff]
  refine ⟨fun h i => h _,fun h r => ?_⟩
  rw [gamma0CuspConstantTerm_equivalent N r _
    (gamma0EisensteinCuspClassRepresentative_equivalent N r) Y hY]
  exact h (gamma0EisensteinCuspClass N r)

def gamma0CuspOutgoingTailAt (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (q : ℂ)
    (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y) : CuspVerticalL2 (N:ℝ) Y :=
  gamma0CuspConstantTerm N r Y hY (gamma0CuspOutgoingCutoffMass N r q hq)

theorem gamma0CuspOutgoingTailAt_ae (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (q : ℂ)
    (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y) (hh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspOutgoingTailAt N r q hq Y hY
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
        fun y => ((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q := by
  have h := gamma0CuspOutgoingCutoffMass_constant_mode N r r q hq Y hY hh
  simpa only [gamma0CuspOutgoingTailAt,gamma0CuspEisensteinIndicator,
    gamma0EisensteinCuspsEquivalent_refl N r,ite_true,one_mul] using h

theorem gamma0CuspOutgoingTailAt_ne_zero (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (q : ℂ)
    (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y) (hh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspOutgoingTailAt N r q hq Y hY≠0 := by
  intro h
  have hc := gamma0CuspOutgoingTailAt_ae N r q hq Y hY hh
  rw [h] at hc
  have hz : (fun y => ((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^q)
      =ᵐ[volume.restrict (Ioi Y)] (fun _ => 0) :=
    (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (hc.symm.trans (Lp.coeFn_zero ℂ 2 _))
  have hμ : volume.restrict (Ioi Y)≠0 := by
    intro hν
    have he := congrArg (fun μ : Measure ℝ => μ univ) hν
    simp [Real.volume_Ioi] at he
  let _ : NeBot (ae (volume.restrict (Ioi Y))) := ae_neBot.mpr hμ
  obtain ⟨y,hy,hyY⟩ := (hz.and (ae_restrict_mem measurableSet_Ioi)).exists
  have hp : 0<y/(gamma0CuspTrueWidth N r:ℝ) :=
    div_pos (hY.trans hyY) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hp.ne'))) hy

theorem gamma0CuspOutgoingCutoffMass_atHeight_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (Y : ℝ) (hY : 0<Y)
    (hh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0CuspOutgoingCutoffMass N a q hq)=
      gamma0CuspEisensteinIndicator N r a • gamma0CuspOutgoingTailAt N r q hq Y hY := by
  apply Lp.ext
  filter_upwards [gamma0CuspOutgoingCutoffMass_constant_mode N r a q hq Y hY hh,
    gamma0CuspOutgoingTailAt_ae N r q hq Y hY hh,
    Lp.coeFn_smul (gamma0CuspEisensteinIndicator N r a) (gamma0CuspOutgoingTailAt N r q hq Y hY)]
      with y hy ht hs
  rw [hy,hs,Pi.smul_apply,ht,smul_eq_mul]

theorem gamma0CuspOutgoingCutoffEnergy_sum_atHeight_mode (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (c : Gamma0EisensteinCuspClasses N → ℂ)
    (Y : ℝ) (hY : 0<Y) (hh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N
        (∑ i,c i • gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i) q hq))=
      c (gamma0EisensteinCuspClass N r) • gamma0CuspOutgoingTailAt N r q hq Y hY := by
  simp only [map_sum,map_smul,gamma0CuspOutgoingCutoffEnergy_mass,
    gamma0CuspOutgoingCutoffMass_atHeight_mode N r _ q hq Y hY hh,smul_smul,
    gamma0CuspEisensteinIndicator_eq_cuspClass,gamma0EisensteinCuspClassRepresentative_class]
  rw [Finset.sum_eq_single (gamma0EisensteinCuspClass N r)]
  · simp
  · intro i _ hi
    simp only [ite_eq_right hi.symm,mul_zero,zero_smul]
  · simp

theorem gamma0CuspOutgoingCutoffEnergy_sum_mem_atHeight_imp_zero (N : ℕ) [NeZero N]
    (q : ℂ) (hq : q.re<1/2) (c : Gamma0EisensteinCuspClasses N → ℂ)
    (Y : ℝ) (hY : 0<Y) (hh : gamma0EisensteinMatchingHeight N≤Y)
    (hc : (∑ i,c i • gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i) q hq)
      ∈ (gamma0TruncatedFormData N Y hY).subspace) : c=0 := by
  funext i
  let r := gamma0EisensteinCuspClassRepresentative N i
  have hr := (gamma0EisensteinMatchingHeight_high N r).trans hh
  have he := (gamma0TruncatedFormData_mem_iff_cusp_representatives N Y hY _).mp hc i
  change gamma0CuspConstantTerm N r Y hY _=0 at he
  rw [gamma0CuspOutgoingCutoffEnergy_sum_atHeight_mode N r q hq c Y hY hr] at he
  have hclass : gamma0EisensteinCuspClass N r=i := gamma0EisensteinCuspClassRepresentative_class N i
  rw [hclass] at he
  exact (smul_eq_zero.mp he).resolve_right (gamma0CuspOutgoingTailAt_ne_zero N r q hq Y hY hr)

end ArtinMatthews
