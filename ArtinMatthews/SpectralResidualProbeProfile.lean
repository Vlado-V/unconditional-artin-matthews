module

public import ArtinMatthews.SpectralCompactResolventCuspSupport
public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspFourierTestSeed
public import ArtinMatthews.SpectralResidualProbeCutoff
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed nonnegative compact height profile detects every real
outgoing constant power without depending on its exponent. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def gamma0ResidualProbeBump : ContDiffBump (2:ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem gamma0ResidualProbeBump_tsupport : tsupport gamma0ResidualProbeBump⊆Ioi (1:ℝ) := by
  intro y hy
  rw [gamma0ResidualProbeBump.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hy
  change |y-2|≤1/2 at hy
  have h := (abs_le.mp hy).1
  change (1:ℝ)<y
  linarith

theorem gamma0ResidualProbeBump_two : gamma0ResidualProbeBump 2=1 := by
  apply gamma0ResidualProbeBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_self]
  exact gamma0ResidualProbeBump.rIn_pos.le

def gamma0ResidualProbeWeight (q : ℝ) (y : ℝ) : ℝ :=
  gamma0ResidualProbeBump y*(max y 1)^(q-2)

theorem gamma0ResidualProbeWeight_continuous (q : ℝ) : Continuous (gamma0ResidualProbeWeight q) := by
  unfold gamma0ResidualProbeWeight
  apply gamma0ResidualProbeBump.continuous.mul
  apply (continuous_id.max continuous_const).rpow_const
  intro y
  left
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right y 1))

theorem gamma0ResidualProbeWeight_compact (q : ℝ) : HasCompactSupport (gamma0ResidualProbeWeight q) :=
  gamma0ResidualProbeBump.hasCompactSupport.mul_right

theorem gamma0ResidualProbeWeight_tsupport (q : ℝ) : tsupport (gamma0ResidualProbeWeight q)⊆Ioi (1:ℝ) :=
  tsupport_mul_subset_left.trans gamma0ResidualProbeBump_tsupport

theorem gamma0ResidualProbeWeight_pos_integral (q : ℝ) : 0<∫ y,gamma0ResidualProbeWeight q y := by
  apply (gamma0ResidualProbeWeight_continuous q).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (gamma0ResidualProbeWeight_compact q)
    (fun y => mul_nonneg gamma0ResidualProbeBump.nonneg
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right y 1)) _))
  change gamma0ResidualProbeBump 2*(max (2:ℝ) 1)^(q-2)≠0
  rw [gamma0ResidualProbeBump_two,one_mul,max_eq_left (by norm_num)]
  exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)

theorem gamma0ResidualProbe_power_integral (q : ℝ) (B : ℂ) :
    (∫ y in Ioi (1:ℝ),(gamma0ResidualProbeBump y/y^2) • (B*(y:ℂ)^(q:ℂ)))=
      B*((∫ y,gamma0ResidualProbeWeight q y):ℝ) := by
  have he (y : ℝ) (hy : y∈Ioi (1:ℝ)) :
      (gamma0ResidualProbeBump y/y^2) • (B*(y:ℂ)^(q:ℂ))=
        B*(gamma0ResidualProbeWeight q y:ℂ) := by
    have hy0 : 0<y := zero_lt_one.trans hy
    rw [gamma0ResidualProbeWeight,max_eq_left hy.le,Real.rpow_sub hy0,Real.rpow_two,
      ← Complex.ofReal_cpow hy0.le q]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  calc
    _ = ∫ y in Ioi (1:ℝ),B*(gamma0ResidualProbeWeight q y:ℂ) :=
      integral_congr_ae ((ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono he)
    _ = B*(∫ y in Ioi (1:ℝ),(gamma0ResidualProbeWeight q y:ℂ)) := integral_const_mul _ _
    _ = _ := by
      congr 1
      have hSet : (∫ y in Ioi (1:ℝ),gamma0ResidualProbeWeight q y)=
          ∫ y,gamma0ResidualProbeWeight q y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy =>
          image_eq_zero_of_notMem_tsupport (fun h => hy (gamma0ResidualProbeWeight_tsupport q h)))
      calc
        _ = (((∫ y in Ioi (1:ℝ),gamma0ResidualProbeWeight q y):ℝ):ℂ) := integral_ofReal
        _ = _ := congrArg Complex.ofReal hSet

def gamma0ResidualProbeSeed (N : ℕ) [NeZero N] : h2SmoothCompactSeeds :=
  cuspFourierTestSeed (N:ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) 0 gamma0ResidualProbeBump
    gamma0ResidualProbeBump.contDiff gamma0ResidualProbeBump.hasCompactSupport
    (gamma0ResidualProbeBump_tsupport.trans (Ioi_subset_Ioi zero_le_one))

def gamma0ResidualProbeMass (N : ℕ) [NeZero N] (r : SL(2,ℤ)) : Gamma0RegionL2 N :=
  gamma0SmoothSeedMass N (modularTranslateSmoothSeed r (gamma0ResidualProbeSeed N))

def gamma0ResidualProbeCutoff (N : ℕ) [NeZero N] : Gamma0CompactResolventCutoff N (gamma0ResidualProbeSeed N) :=
  gamma0CompactResolventCutoff N (gamma0ResidualProbeSeed N)

theorem gamma0ResidualProbeMass_detects_real_mode (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (f : Gamma0RegionL2 N) (q : ℝ) (B : ℂ)
    (hmode : gamma0GlobalCuspConstantTerm N r f=ᵐ[volume.restrict (Ioi 0)]
      fun y => B*(y:ℂ)^(q:ℂ)) :
    inner ℂ (gamma0ResidualProbeMass N r) f=
      (2*(N:ℂ))*B*((∫ y,gamma0ResidualProbeWeight q y):ℝ) := by
  have hpair := gamma0ZeroModeProbe_pairing N r 1 zero_lt_one gamma0ResidualProbeBump
    gamma0ResidualProbeBump.contDiff gamma0ResidualProbeBump.hasCompactSupport
    (gamma0ResidualProbeBump_tsupport.trans (Ioi_subset_Ioi zero_le_one))
    gamma0ResidualProbeBump_tsupport f
  change inner ℂ (gamma0ResidualProbeMass N r) f=_ at hpair
  rw [hpair]
  have he : (∫ y in Ioi (1:ℝ),(gamma0ResidualProbeBump y/y^2) •
      gamma0GlobalCuspConstantTerm N r f y)=
      ∫ y in Ioi (1:ℝ),(gamma0ResidualProbeBump y/y^2) • (B*(y:ℂ)^(q:ℂ)) :=
    integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) hmode).mono
      (fun y hy => congrArg (fun z : ℂ => (gamma0ResidualProbeBump y/y^2) • z) hy))
  rw [he,gamma0ResidualProbe_power_integral]
  ring

theorem gamma0ResidualProbeMass_mode_zero (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (f : Gamma0RegionL2 N) (q : ℝ) (B : ℂ)
    (hmode : gamma0GlobalCuspConstantTerm N r f=ᵐ[volume.restrict (Ioi 0)]
      fun y => B*(y:ℂ)^(q:ℂ)) (hzero : inner ℂ (gamma0ResidualProbeMass N r) f=0) : B=0 := by
  rw [gamma0ResidualProbeMass_detects_real_mode N r f q B hmode] at hzero
  have hN : 2*(N:ℂ)≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne N)
  have hM : (((∫ y,gamma0ResidualProbeWeight q y):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (gamma0ResidualProbeWeight_pos_integral q).ne'
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hM)).resolve_left hN

end ArtinMatthews
