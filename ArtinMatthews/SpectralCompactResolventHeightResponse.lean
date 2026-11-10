module

public import ArtinMatthews.SpectralClosedFormEnergyResolvent
public import ArtinMatthews.SpectralGamma0AmbientResolvent
public import ArtinMatthews.SpectralGamma0TruncatedPseudoResolvent
public import ArtinMatthews.SpectralEisensteinMatchingDefects
public import ArtinMatthews.SpectralMeromorphicFormMaps
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

/-! The actual energy-valued compact pseudo-resolvent and full weak
defect for an arbitrary cutoff and an arbitrary genuine mass forcing. -/
noncomputable section
open Set
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0HeightMatchingResponse (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) (s : ℂ) :
    Gamma0RegionL2 N →L[ℂ] gamma0EnergySpace N :=
  (gamma0TruncatedFormData N Y hY).energyResolvent (s*(1-s))

def gamma0HeightMatchingDefect (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) (s : ℂ) :
    Gamma0RegionL2 N →L[ℂ] gamma0EnergySpace N :=
  (gamma0EnergyResolventPencil N (s*(1-s))).comp (gamma0HeightMatchingResponse N Y hY s)-
    gamma0EnergyMassAdjoint N

theorem gamma0HeightMatchingResponse_mem (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) (s : ℂ)
    (F : Gamma0RegionL2 N) :
    gamma0HeightMatchingResponse N Y hY s F∈(gamma0TruncatedFormData N Y hY).subspace :=
  (gamma0TruncatedFormData N Y hY).energyResolvent_mem _ _

theorem gamma0HeightMatchingResponse_reflect (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) :
    gamma0HeightMatchingResponse N Y hY (1-s)=gamma0HeightMatchingResponse N Y hY s := by
  rw [gamma0HeightMatchingResponse,gamma0HeightMatchingResponse,gamma0Eisenstein_reflect_parameter]

theorem gamma0HeightMatchingDefect_reflect (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) :
    gamma0HeightMatchingDefect N Y hY (1-s)=gamma0HeightMatchingDefect N Y hY s := by
  rw [gamma0HeightMatchingDefect,gamma0HeightMatchingDefect,gamma0Eisenstein_reflect_parameter,
    gamma0HeightMatchingResponse_reflect]

theorem gamma0HeightMatchingResponse_meromorphic (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y) :
    Meromorphic (gamma0HeightMatchingResponse N Y hY) := by
  intro s
  exact ((gamma0TruncatedFormData N Y hY).energyResolvent_meromorphic (s*(1-s))).comp_analyticAt
    (g := fun w : ℂ => w*(1-w)) (x:=s) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))

theorem gamma0HeightMatchingResponse_analyticAt (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0<Y)
    (s : ℂ) (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional) :
    AnalyticAt ℂ (gamma0HeightMatchingResponse N Y hY) s :=
  ((gamma0TruncatedFormData N Y hY).energyResolvent_analyticAt (s*(1-s)) hs).comp
    (f:=fun w : ℂ => w*(1-w)) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))

theorem gamma0HeightMatchingDefect_apply_meromorphicAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ) (hF : AnalyticAt ℂ F s) :
    MeromorphicAt (fun w => gamma0HeightMatchingDefect N Y hY w (F w)) s := by
  let B := (gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)
  have hU := spectralMeromorphicAt_clmApply _ F s (gamma0HeightMatchingResponse_meromorphic N Y hY s) hF
  have hB := spectralMeromorphicAt_comp_clm B hU
  have hscalar : AnalyticAt ℂ (fun w : ℂ => w*(1-w)+1) s :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).add analyticAt_const
  have hJF := spectralMeromorphicAt_comp_clm (gamma0EnergyMassAdjoint N) hF.meromorphicAt
  exact (hU.sub (hscalar.meromorphicAt.smul hB)).sub hJF

theorem gamma0HeightMatchingDefect_apply_analyticAt (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (F : ℂ → Gamma0RegionL2 N) (s : ℂ)
    (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional) (hF : AnalyticAt ℂ F s) :
    AnalyticAt ℂ (fun w => gamma0HeightMatchingDefect N Y hY w (F w)) s := by
  let B := (gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)
  have hU := spectralAnalytic_clmApply _ F s (gamma0HeightMatchingResponse_analyticAt N Y hY s hs) hF
  have hB := (B.analyticAt _).comp hU
  have hscalar : AnalyticAt ℂ (fun w : ℂ => w*(1-w)+1) s :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).add analyticAt_const
  have hJF := ((gamma0EnergyMassAdjoint N).analyticAt _).comp hF
  exact (hU.sub (hscalar.smul hB)).sub hJF

theorem gamma0HeightMatchingForm_not_exceptional (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (z : ℂ) (hz : z.re<‖z‖) :
    z∉(gamma0TruncatedFormData N Y hY).exceptional := by
  intro h
  obtain ⟨x,hx,he⟩ := (gamma0TruncatedFormData N Y hY).exceptional_nonnegative z h
  rw [he,Complex.ofReal_re,Complex.norm_real,Real.norm_of_nonneg hx] at hz
  exact (lt_irrefl _ hz)

theorem gamma0HeightMatchingResponse_unique_of_pencil (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (s : ℂ) (hs : s*(1-s)∉(gamma0TruncatedFormData N Y hY).exceptional)
    (F : Gamma0RegionL2 N) (u : gamma0EnergySpace N)
    (hu : u∈(gamma0TruncatedFormData N Y hY).subspace)
    (hp : gamma0EnergyResolventPencil N (s*(1-s)) u=gamma0EnergyMassAdjoint N F) :
    u=gamma0HeightMatchingResponse N Y hY s F := by
  apply (gamma0TruncatedFormData N Y hY).energyResolvent_unique _ hs _ _ hu
  intro v _
  have he := congrArg (fun w : gamma0EnergySpace N => inner ℂ v w) hp
  change inner ℂ v (gamma0EnergyResolventPencil N (s*(1-s)) u)=
    inner ℂ v (gamma0EnergyMassAdjoint N F) at he
  rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner] at he
  change inner ℂ v u-(s*(1-s)+1)*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u)=
    inner ℂ (gamma0EnergyInclusion N v) F
  rw [gamma0FormEnergy_inner]
  linear_combination he

end ArtinMatthews
