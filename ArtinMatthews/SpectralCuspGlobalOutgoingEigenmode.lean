module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralGamma0AmbientResolvent
public import ArtinMatthews.SpectralCompactResolventOutgoingMode
public import ArtinMatthews.SpectralCuspWeightedGluing
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

/-! A subcritical full-energy eigenvector has one genuine outgoing
constant-mode power on the whole positive-height ray at each cusp. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspComplexPower_multiplier_eq_of_ae {Y : ℝ} (hY : 0<Y)
    (p A B : ℂ) (he : (fun y : ℝ => A*(y:ℂ)^p)=ᵐ[volume.restrict (Ioi Y)]
      (fun y => B*(y:ℂ)^p)) : A=B := by
  have hm : (volume.restrict (Ioi Y):Measure ℝ)≠0 := by
    intro hz
    have h := congrArg (fun μ : Measure ℝ => μ univ) hz
    simp [Real.volume_Ioi] at h
  let _ : (ae (volume.restrict (Ioi Y))).NeBot := ae_neBot.mpr hm
  obtain ⟨y,heq,hy⟩ := (he.and (ae_restrict_mem (μ:=volume) measurableSet_Ioi)).exists
  exact mul_right_cancel₀ (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (hY.trans hy).ne'))) heq

theorem gamma0EnergyMass_global_outgoing_eigenmode (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (s : ℂ) (hs : (1/2:ℝ)<s.re)
    (u : gamma0EnergySpace N) (hu : gamma0EnergyResolventPencil N (s*(1-s)) u=0) :
    ∃ B : ℂ,gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)=ᵐ[volume.restrict (Ioi 0)]
      fun y => B*(y:ℂ)^(1-s) := by
  have hp : gamma0EnergyResolventPencil N (s*(1-s)) u=gamma0EnergyMassAdjoint N 0 := by
    simpa only [map_zero] using hu
  have hZero (Y : ℝ) (hY : 0<Y) := gamma0EnergyMass_outgoing_global_mode_of_pencil N r s hs
    u 0 hp Y hY (fun ψ _ => inner_zero_right _)
  obtain ⟨B,hB⟩ := hZero 1 zero_lt_one
  refine ⟨B,?_⟩
  apply spectralCuspWeightedGluing_unique (w:=(N:ℝ)) (Nat.cast_pos.mpr (NeZero.pos N))
  intro n
  let Y := spectralCuspGluingHeight n
  have hY : 0<Y := spectralCuspGluingHeight_pos n
  obtain ⟨A,hA⟩ := hZero Y hY
  have hAB : A=B := by
    have h1 : gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
        =ᵐ[volume.restrict (Ioi (max 1 Y))] fun y => A*(y:ℂ)^(1-s) :=
      ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi (le_max_right 1 Y)) hA
    have h2 : gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
        =ᵐ[volume.restrict (Ioi (max 1 Y))] fun y => B*(y:ℂ)^(1-s) :=
      ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi (le_max_left 1 Y)) hB
    exact cuspComplexPower_multiplier_eq_of_ae (lt_max_of_lt_left zero_lt_one) (1-s) A B
      (h1.symm.trans h2)
  rw [hAB] at hA
  exact (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mpr hA

theorem gamma0SubcriticalEigen_parameter {l : ℝ} (_hl : 0≤l) (hc : l<1/4) :
    let s : ℂ := ((1/2+Real.sqrt (1/4-l):ℝ):ℂ)
    (1/2:ℝ)<s.re ∧ s*(1-s)=(l:ℂ) := by
  dsimp only
  have hs : 0<Real.sqrt (1/4-l) := Real.sqrt_pos.mpr (sub_pos.mpr hc)
  have he := Real.sq_sqrt (sub_nonneg.mpr hc.le)
  constructor
  · rw [Complex.ofReal_re]
    linarith
  · norm_cast
    nlinarith

end ArtinMatthews
