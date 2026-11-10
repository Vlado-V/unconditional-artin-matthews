module

public import ArtinMatthews.SpectralCompactResolventMatchingCoefficient
public import ArtinMatthews.SpectralEisensteinReflectionScattering
public import ArtinMatthews.SpectralEisensteinRegularGerms
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! For each true cutoff, the actual compact matching parameters are
regular in a punctured neighborhood of every complex point. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

theorem gamma0HeightMatchingRegular_eventually (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, gamma0HeightMatchingRegular N Y hY w := by
  let ζ (w : ℂ) := w*(1-w)
  let E : Set ℂ := {z | z∈(gamma0TruncatedFormData N Y hY).exceptional ∧ ‖z‖≤‖ζ s‖+1}
  have hfinite : E.Finite :=
    (gamma0TruncatedFormData N Y hY).exceptional_finite_norm_le (‖ζ s‖+1) (by positivity)
  have hc : Continuous ζ := by unfold ζ;fun_prop
  have hnζ : Tendsto ζ (𝓝 s) (𝓝 (ζ s)) := hc.continuousAt
  have hnn : Tendsto (fun w => ‖ζ w‖) (𝓝 s) (𝓝 ‖ζ s‖) := hnζ.norm
  have hcut : (E\{ζ s})ᶜ∈𝓝 (ζ s) :=
    (hfinite.sdiff.isClosed.isOpen_compl).mem_nhds (by simp)
  have hcut' : ∀ᶠ w in 𝓝 s, ζ w∉E\{ζ s} := hnζ.eventually hcut
  have hnorm : ∀ᶠ w in 𝓝 s, ‖ζ w‖<‖ζ s‖+1 :=
    hnn.eventually (eventually_lt_nhds (by linarith : ‖ζ s‖<‖ζ s‖+1))
  have hreflect : ∀ᶠ w in 𝓝[≠] s,w≠1-s := by
    by_cases he : s=1-s
    · filter_upwards [(self_mem_nhdsWithin : ({s}:Set ℂ)ᶜ∈𝓝[≠] s)] with w hw
      intro h
      exact hw (mem_singleton_iff.mpr (h.trans he.symm))
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by simpa only [mem_compl_iff,mem_singleton_iff] using he))
  filter_upwards [nhdsWithin_le_nhds hcut',nhdsWithin_le_nhds hnorm,
    (self_mem_nhdsWithin : ({s}:Set ℂ)ᶜ∈𝓝[≠] s),hreflect,
    gamma0HeightMatchingMatrix_det_eventually_ne_zero N Y hY hmin s] with w hw hn hws hwr hd
  refine ⟨?_,hd⟩
  intro he
  have hmem : ζ w∈E := ⟨he,hn.le⟩
  have heq : ζ w=ζ s := by
    by_contra h
    exact hw ⟨hmem,by simpa only [mem_singleton_iff] using h⟩
  exact (eisensteinSpectralParameter_eq_iff w s).mp heq |>.elim
    (fun h => hws (mem_singleton_iff.mpr h)) hwr


theorem gamma0HeightMatchingRegular_reflected_eventually (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0<Y) (hmin : gamma0EisensteinMatchingHeight N≤Y) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0HeightMatchingRegular N Y hY w ∧ gamma0HeightMatchingRegular N Y hY (1-w) :=
  (gamma0HeightMatchingRegular_eventually N Y hY hmin s).and
    ((eisensteinParameterReflect_tendsto_punctured s).eventually
      (gamma0HeightMatchingRegular_eventually N Y hY hmin (1-s)))

end ArtinMatthews
