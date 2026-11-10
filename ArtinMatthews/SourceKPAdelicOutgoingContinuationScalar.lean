module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationAnalytic
public import ArtinMatthews.SourceArchIntertwinerProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! The literal finite-window formula and archimedean product give the
canonical scalar continuation of the measured outgoing operator. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourceArchJacquet Filter
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "I" => sourceKPAdelicTraceIntertwiner K hζ
local notation "H" => SourceKPAdelicOutgoingInitial K
local notation "arch" => sourceArchSphericalProduct K hζ
local notation "V" => sourceKPFiniteFiberScatteringRegularized K hζ
local notation "C" => sourceKPFiniteFiberScatteringContinuation K hζ

def sourceKPAdelicOutgoingScatteringWindow (g : Gf) : Finset Pr :=
  Classical.choose (sourceKPFiniteFiberScatteringContinuation_exists K hζ g ∅)

local notation "S₀" => sourceKPAdelicOutgoingScatteringWindow K hζ

theorem sourceKPAdelicOutgoingScatteringWindow_matches (g : Gf) (s : ℂ) (hs : H s) :
    I s (1,g) = C g (S₀ g) s :=
  (Classical.choose_spec (sourceKPFiniteFiberScatteringContinuation_exists K hζ g ∅)).2.2.2.1 s hs

theorem sourceKPAdelicOutgoingTrace_arch {s : ℂ} (hs : 0 < s.re) (g : G) :
    I s g = arch (-s) g.1 * I s (1,g.2) := by
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs g,
    sourceKPAdelicTraceIntertwiner_at_finite K hζ hs g.2]
  ring

def sourceKPAdelicOutgoingRegularizedScalar (s : ℂ) (g : G) : ℂ :=
  arch (-s) g.1 * V g.2 (S₀ g.2) s

local notation "R" => sourceKPAdelicOutgoingRegularizedScalar K hζ

theorem sourceKPAdelicOutgoingRegularizedScalar_analyticOnNhd (g : G) :
    AnalyticOnNhd ℂ (fun s => R s g) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (sourceKPAdelicOutgoingArchProduct_analyticAt K hζ g.1 s).mul
    (sourceKPAdelicOutgoingFiniteRegularized_analyticAt K hζ g.2 (S₀ g.2) hs)

theorem sourceKPAdelicOutgoingRegularizedScalar_initial (s : ℂ) (hs : H s) (g : G) :
    R s g = (s-1/6)*I s g := by
  have hp := zero_lt_one.trans_le (sourceKPAdelicOutgoingInitial_re_one_le K hs)
  have hn := sourceKPAdelicOutgoingInitial_ne_exceptional K hs
  rw [sourceKPAdelicOutgoingRegularizedScalar,
    sourceKPFiniteFiberScatteringRegularized_eq K hζ g.2 (S₀ g.2) hn,
    ← sourceKPAdelicOutgoingScatteringWindow_matches K hζ g.2 s hs,
    sourceKPAdelicOutgoingTrace_arch K hζ hp g]
  ring

theorem sourceKPAdelicOutgoingRegularizedScalar_eq_window (g : G) (S : Finset Pr)
    (hS : ∀ s, H s → I s (1,g.2) = C g.2 S s) {s : ℂ} (hs : 0 < s.re) :
    R s g = arch (-s) g.1 * V g.2 S s := by
  apply sourceKPAdelicOutgoingAnalytic_eqOn_of_initial K
    (sourceKPAdelicOutgoingRegularizedScalar_analyticOnNhd K hζ g)
    (fun z hz => (sourceKPAdelicOutgoingArchProduct_analyticAt K hζ g.1 z).mul
      (sourceKPAdelicOutgoingFiniteRegularized_analyticAt K hζ g.2 S hz)) _ hs
  intro z hz
  change R z g = arch (-z) g.1 * V g.2 S z
  have hp := zero_lt_one.trans_le (sourceKPAdelicOutgoingInitial_re_one_le K hz)
  rw [sourceKPAdelicOutgoingRegularizedScalar_initial K hζ z hz g,
    sourceKPAdelicOutgoingTrace_arch K hζ hp g, hS z hz,
    sourceKPFiniteFiberScatteringRegularized_eq K hζ g.2 S
      (sourceKPAdelicOutgoingInitial_ne_exceptional K hz)]
  ring

theorem sourceKPAdelicOutgoingRegularizedScalar_residue (g : G) (S : Finset Pr)
    (hS : ∀ s, H s → I s (1,g.2) = C g.2 S s) :
    R (1/6) g = arch (- (1/6 : ℂ)) g.1 * sourceKPFiniteFiberScatteringResidue K hζ g.2 S := by
  rw [sourceKPAdelicOutgoingRegularizedScalar_eq_window K hζ g S hS
    (by norm_num : 0 < (1/6 : ℂ).re),
    sourceKPFiniteFiberScatteringRegularized_value]

def sourceKPAdelicOutgoingContinuationScalar (s : ℂ) (g : G) : ℂ :=
  R s g / (s-1/6)

local notation "M" => sourceKPAdelicOutgoingContinuationScalar K hζ

theorem sourceKPAdelicOutgoingContinuationScalar_initial (s : ℂ) (hs : H s) (g : G) :
    M s g = I s g := by
  rw [sourceKPAdelicOutgoingContinuationScalar,
    sourceKPAdelicOutgoingRegularizedScalar_initial K hζ s hs g]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (sourceKPAdelicOutgoingInitial_ne_exceptional K hs))

theorem sourceKPAdelicOutgoingContinuationScalar_meromorphicOn (g : G) :
    MeromorphicOn (fun s => M s g) {s : ℂ | 0 < s.re} := by
  intro s hs
  have h : AnalyticAt ℂ (fun z : ℂ => z-1/6) s := analyticAt_id.sub analyticAt_const
  exact (sourceKPAdelicOutgoingRegularizedScalar_analyticOnNhd K hζ g s hs).meromorphicAt.div h.meromorphicAt

theorem sourceKPAdelicOutgoingContinuationScalar_residue_tendsto (g : G) :
    Tendsto (fun s => (s-1/6)*M s g) (𝓝[≠] (1/6 : ℂ)) (𝓝 (R (1/6) g)) := by
  have ha := sourceKPAdelicOutgoingRegularizedScalar_analyticOnNhd K hζ g (1/6)
    (by norm_num : 0 < (1/6 : ℂ).re)
  have ht := ha.continuousAt.tendsto.mono_left
    (show 𝓝[≠] (1/6 : ℂ) ≤ 𝓝 (1/6 : ℂ) from nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs₀ : s ≠ (1/6 : ℂ) := hs
  unfold sourceKPAdelicOutgoingContinuationScalar
  exact (mul_div_cancel₀ _ (sub_ne_zero.mpr hs₀)).symm

end
end ArtinMatthews
