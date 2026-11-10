module

public import ArtinMatthews.SpectralGamma0AmbientResolventAnalytic
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralEisensteinRemainderL2
public import ArtinMatthews.SpectralGamma0FormOperator
public import ArtinMatthews.SpectralAmbientResolventOperator
public import ArtinMatthews.SpectralEisensteinForcingAnalytic
public import ArtinMatthews.SpectralEisensteinWeakForcing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Genuine holomorphic continuation of the truncated Eisenstein mass on
the right component of the ambient resolvent region, with proved agreement
with the original Re(s)>1 series. Crossing the spectral cut is separate. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

section Bilinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem spectralAnalytic_clmApply (A : ℂ → E →L[ℂ] F) (u : ℂ → E) (s : ℂ)
    (hA : AnalyticAt ℂ A s) (hu : AnalyticAt ℂ u s) :
    AnalyticAt ℂ (fun w => A w (u w)) s := by
  let B : (E →L[ℂ] F) →L[ℂ] E →L[ℂ] F := ContinuousLinearMap.id ℂ (E →L[ℂ] F)
  exact (B.analyticAt_bilinear (A s,u s)).comp₂ hA hu

end Bilinear

def gamma0EisensteinContinuationDomain : Set ℂ :=
  {s | (1/2:ℝ) < s.re ∧ (s*(1-s)).re < ‖s*(1-s)‖}

theorem complex_re_lt_norm_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) : z.re < ‖z‖ := by
  have hre := Complex.re_le_norm z
  have hsq := Complex.sq_norm z
  rw [Complex.normSq_apply] at hsq
  by_contra hn
  have he : ‖z‖=z.re := le_antisymm (not_lt.mp hn) hre
  rw [he] at hsq
  nlinarith [sq_pos_of_ne_zero hz]

theorem gamma0EisensteinContinuationDomain_nonreal (s : ℂ)
    (hs : (1/2:ℝ)<s.re) (hi : s.im ≠ 0) : s ∈ gamma0EisensteinContinuationDomain := by
  refine ⟨hs,complex_re_lt_norm_of_im_ne_zero _ ?_⟩
  have he : (s*(1-s)).im=s.im*(1-2*s.re) := by
    simp only [Complex.mul_im,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im]
    ring
  rw [he]
  exact mul_ne_zero hi (by linarith)

def gamma0CuspEisensteinContinuedRemainder (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0RegionL2 N :=
  gamma0AmbientResolventFamily N (s*(1-s)) (-gamma0CuspEisensteinCompactForcingMass N a s)

theorem gamma0CuspEisensteinContinuedRemainder_analyticAt (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    AnalyticAt ℂ (gamma0CuspEisensteinContinuedRemainder N a) s := by
  have hR : AnalyticAt ℂ (fun w => gamma0AmbientResolventFamily N (w*(1-w))) s :=
    (gamma0AmbientResolventFamily_analyticAt N (s*(1-s)) hs.2).comp
      (f := fun w : ℂ => w*(1-w)) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
  exact spectralAnalytic_clmApply _ _ s hR
    (gamma0CuspEisensteinCompactForcingMass_analyticAt N a s).neg

theorem gamma0CuspEisensteinContinuedRemainder_analyticOn (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    AnalyticOnNhd ℂ (gamma0CuspEisensteinContinuedRemainder N a) gamma0EisensteinContinuationDomain :=
  fun s hs => gamma0CuspEisensteinContinuedRemainder_analyticAt N a s hs

theorem gamma0CuspEisensteinContinuedRemainder_operator_graph (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    (gamma0CuspEisensteinContinuedRemainder N a s,
      -gamma0CuspEisensteinCompactForcingMass N a s+
        (s*(1-s)+1) • gamma0CuspEisensteinContinuedRemainder N a s)
      ∈ (gamma0MassEnergyOperator N).graph :=
  gamma0AmbientResolventFamily_operator_graph N (s*(1-s)) hs.2
    (-gamma0CuspEisensteinCompactForcingMass N a s)

theorem gamma0EisensteinContinuationDomain_initial (s : ℂ) (hs : 1 < s.re) :
    s ∈ gamma0EisensteinContinuationDomain :=
  ⟨by linarith,eisensteinSpectralParameter_off_nonnegative_ray s hs⟩

theorem gamma0CuspEisensteinContinuedRemainder_initial (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspEisensteinContinuedRemainder N a s=gamma0CuspEisensteinRemainderMass N a s hs := by
  rw [gamma0CuspEisensteinContinuedRemainder,
    gamma0AmbientResolventFamily_eq N (s*(1-s)) (eisensteinSpectralParameter_off_nonnegative_ray s hs)]
  exact (gamma0CuspEisensteinRemainderMass_resolvent N a s hs).symm

theorem gamma0CuspEisensteinContinuedRemainder_series_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    ∀ᵐ z ∂volume.restrict ModularGroup.fd,
      gamma0CuspEisenstein N a s (q.out⁻¹ • z)=
        gamma0CuspEisensteinCutoff N a s (q.out⁻¹ • z)+
          (gamma0CuspEisensteinContinuedRemainder N a s q) z := by
  rw [gamma0CuspEisensteinContinuedRemainder_initial N a s hs]
  have he := gamma0CuspEisensteinRemainderMass_ae N a s hs q
  filter_upwards [he] with z hz
  change (gamma0CuspEisensteinRemainderMass N a s hs q) z=
    gamma0CuspEisenstein N a s (q.out⁻¹ • z)-gamma0CuspEisensteinCutoff N a s (q.out⁻¹ • z) at hz
  linear_combination -hz

end ArtinMatthews
