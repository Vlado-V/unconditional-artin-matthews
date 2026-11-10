module

public import ArtinMatthews.SpectralClosedFormEnergyResolvent
public import ArtinMatthews.SpectralGamma0TruncatedPseudoResolvent
public import ArtinMatthews.SpectralEisensteinOutgoingModes
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralEisensteinOutgoingEnergy
public import ArtinMatthews.SpectralGamma0AmbientResolvent
public import ArtinMatthews.SpectralEisensteinContinuation
public import ArtinMatthews.SpectralEisensteinForcingAnalytic
public import ArtinMatthews.SpectralEisensteinOutgoingForcing
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

/-! The actual truncated energy response and its full weak defect. The
defect vanishes on the truncated test domain, but is retained as an actual
ambient energy vector to enforce the omitted equations. -/
noncomputable section
open Set
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinMatchingForm (N : ℕ) [NeZero N] :
    SpectralClosedFormData (gamma0EnergySpace N) (Gamma0RegionL2 N) :=
  gamma0TruncatedFormData N (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)

theorem gamma0EisensteinMatchingForm_not_exceptional (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re<‖z‖) : z∉(gamma0EisensteinMatchingForm N).exceptional := by
  intro h
  obtain ⟨x,hx,he⟩ := (gamma0EisensteinMatchingForm N).exceptional_nonnegative z h
  rw [he,Complex.ofReal_re,Complex.norm_real,Real.norm_of_nonneg hx] at hz
  exact (lt_irrefl _ hz)

def gamma0EisensteinMatchingResponse (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EnergySpace N :=
  (gamma0EisensteinMatchingForm N).energyResolvent (s*(1-s))
    (gamma0CuspEisensteinCompactForcingMass N a s)

theorem gamma0EisensteinMatchingResponse_mem (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EisensteinMatchingResponse N a s ∈ (gamma0EisensteinMatchingForm N).subspace :=
  (gamma0EisensteinMatchingForm N).energyResolvent_mem _ _

theorem gamma0EisensteinMatchingResponse_meromorphic (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Meromorphic (gamma0EisensteinMatchingResponse N a) := by
  intro s
  let A := (gamma0EisensteinMatchingForm N).energyResolvent
  have hA : MeromorphicAt (fun w : ℂ => A (w*(1-w))) s :=
    ((gamma0EisensteinMatchingForm N).energyResolvent_meromorphic (s*(1-s))).comp_analyticAt
      (g := fun w : ℂ => w*(1-w)) (x := s) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
  exact spectralMeromorphicAt_clmApply _ _ s hA (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s)

theorem gamma0EisensteinMatchingResponse_analyticAt (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : (s*(1-s)).re<‖s*(1-s)‖) : AnalyticAt ℂ (gamma0EisensteinMatchingResponse N a) s := by
  let A := (gamma0EisensteinMatchingForm N).energyResolvent
  have hA : AnalyticAt ℂ (fun w : ℂ => A (w*(1-w))) s :=
    ((gamma0EisensteinMatchingForm N).energyResolvent_analyticAt (s*(1-s))
      (gamma0EisensteinMatchingForm_not_exceptional N _ hs)).comp
        (f := fun w : ℂ => w*(1-w)) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
  exact spectralAnalytic_clmApply _ _ s hA (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s)

def gamma0EisensteinMatchingDefect (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    gamma0EnergySpace N :=
  gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinMatchingResponse N a s)-
    gamma0EnergyMassAdjoint N (gamma0CuspEisensteinCompactForcingMass N a s)

theorem gamma0EisensteinMatchingDefect_meromorphic (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Meromorphic (gamma0EisensteinMatchingDefect N a) := by
  intro s
  let B := (gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)
  have hU := gamma0EisensteinMatchingResponse_meromorphic N a s
  have hB := spectralMeromorphicAt_comp_clm B hU
  have hscalar : AnalyticAt ℂ (fun w : ℂ => w*(1-w)+1) s :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).add analyticAt_const
  have hF := spectralMeromorphicAt_comp_clm (gamma0EnergyMassAdjoint N)
    (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s).meromorphicAt
  exact (hU.sub (hscalar.meromorphicAt.smul hB)).sub hF

theorem gamma0EisensteinMatchingDefect_analyticAt (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : (s*(1-s)).re<‖s*(1-s)‖) : AnalyticAt ℂ (gamma0EisensteinMatchingDefect N a) s := by
  let B := (gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)
  have hU := gamma0EisensteinMatchingResponse_analyticAt N a s hs
  have hB := (B.analyticAt _).comp hU
  have hscalar : AnalyticAt ℂ (fun w : ℂ => w*(1-w)+1) s :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).add analyticAt_const
  have hF := ((gamma0EnergyMassAdjoint N).analyticAt _).comp
    (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s)
  exact (hU.sub (hscalar.smul hB)).sub hF

theorem gamma0EisensteinMatchingDefect_truncated (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : (s*(1-s)).re<‖s*(1-s)‖) (v : gamma0EnergySpace N)
    (hv : v∈(gamma0EisensteinMatchingForm N).subspace) :
    inner ℂ v (gamma0EisensteinMatchingDefect N a s)=0 := by
  have he := (gamma0EisensteinMatchingForm N).energyResolvent_equation (s*(1-s))
    (gamma0EisensteinMatchingForm_not_exceptional N _ hs)
    (gamma0CuspEisensteinCompactForcingMass N a s) v hv
  change inner ℂ v (gamma0EisensteinMatchingResponse N a s)-
    (s*(1-s)+1)*inner ℂ (gamma0EnergyInclusion N v)
      (gamma0EnergyInclusion N (gamma0EisensteinMatchingResponse N a s))=
    inner ℂ (gamma0EnergyInclusion N v) (gamma0CuspEisensteinCompactForcingMass N a s) at he
  rw [gamma0EisensteinMatchingDefect,inner_sub_right (𝕜 := ℂ) (E := gamma0EnergySpace N),
    gamma0EnergyResolventPencil_inner,
    gamma0EnergyMassAdjoint_inner]
  rw [gamma0FormEnergy_inner] at he
  linear_combination he

theorem gamma0CuspOutgoingCutoffEnergy_pencil (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) :
    gamma0EnergyResolventPencil N (q*(1-q)) (gamma0CuspOutgoingCutoffEnergy N a q hq)=
      gamma0EnergyMassAdjoint N (gamma0CuspEisensteinCompactForcingMass N a q) := by
  apply ext_inner_left ℂ
  intro v
  rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner,gamma0CuspOutgoingCutoffEnergy_mass]
  exact gamma0CuspOutgoingCutoffEnergy_forcing N a q hq v

theorem gamma0EisensteinMatchingPencil_injective (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re<‖z‖) :
    Function.Injective (gamma0EnergyResolventPencil N z) := by
  intro u v h
  apply (gamma0EnergyRotatedEquiv N z hz).injective
  change spectralResolventRotation z • gamma0EnergyResolventPencil N z u=
    spectralResolventRotation z • gamma0EnergyResolventPencil N z v
  rw [h]

end ArtinMatthews
