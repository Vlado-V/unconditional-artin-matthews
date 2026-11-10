module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuation
public import ArtinMatthews.VaryingKummerAnalyticMixedInverseGammaOrderZero
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine continued Dedekind zeta with its removable value at zero
restored, and its exact order r₁+r₂−1 there. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

private theorem inverseDiscriminant_entire :
    Differentiable ℂ (fun z : ℂ => ((mixedDiscriminantScale K : ℂ)^z)⁻¹) := by
  apply Differentiable.inv
  · exact differentiable_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  · intro z
    exact cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))

/-- The entire numerator after the archimedean zero at zero cancels the
extraneous division by s in the raw completion formula. -/
def mixedDedekindEntireNumerator (s : ℂ) : ℂ :=
  mixedCompletedDedekindXi K s * ((mixedDiscriminantScale K : ℂ)^s)⁻¹ *
    s^(Fintype.card (InfinitePlace K)-1) * mixedInverseGammaUnit K s

theorem mixedDedekindEntireNumerator_entire :
    Differentiable ℂ (mixedDedekindEntireNumerator K) := by
  exact (((mixedCompletedDedekindXi_entire K).mul (inverseDiscriminant_entire K)).mul
    (differentiable_id.pow _)).mul (mixedInverseGammaUnit_entire K)

theorem mixedDedekindEntireNumerator_eq_regularized {s : ℂ} (hs : s ≠ 0) :
    mixedDedekindEntireNumerator K s = mixedRegularizedDedekindZeta K s := by
  have hc : 1 ≤ Fintype.card (InfinitePlace K) := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt Fintype.card_pos)
  have hp : s^Fintype.card (InfinitePlace K) = s^(Fintype.card (InfinitePlace K)-1)*s := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  unfold mixedDedekindEntireNumerator mixedRegularizedDedekindZeta
  rw [mixedInverseGammaFactor_factorization, hp]
  field_simp

/-- The canonical continuation, including the analytic value at zero. -/
def mixedDedekindZeta (s : ℂ) : ℂ := mixedDedekindEntireNumerator K s / (s-1)

theorem mixedDedekindZeta_analyticAt {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mixedDedekindZeta K) s :=
  ((mixedDedekindEntireNumerator_entire K).analyticAt s).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

theorem mixedDedekindZeta_meromorphic : Meromorphic (mixedDedekindZeta K) := by
  intro s
  exact ((mixedDedekindEntireNumerator_entire K).analyticAt s).meromorphicAt.div
    (analyticAt_id.sub analyticAt_const).meromorphicAt

theorem mixedDedekindZeta_eq_continuation {s : ℂ} (hs : s ≠ 0) :
    mixedDedekindZeta K s = mixedDedekindZetaContinuation K s := by
  unfold mixedDedekindZeta mixedDedekindZetaContinuation
  rw [mixedDedekindEntireNumerator_eq_regularized K hs]

theorem mixedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    mixedDedekindZeta K s = NumberField.dedekindZeta K s := by
  rw [mixedDedekindZeta_eq_continuation K (by intro h; norm_num [h] at hs)]
  exact mixedDedekindZetaContinuation_eq K hs

/-- Exact vanishing order at zero, retaining both real and complex places. -/
theorem mixedDedekindZeta_analyticOrder_zero :
    analyticOrderAt (mixedDedekindZeta K) 0 =
      ((Fintype.card (InfinitePlace K)-1 : ℕ) : ℕ∞) := by
  let U : ℂ → ℂ := fun s => mixedCompletedDedekindXi K s *
    ((mixedDiscriminantScale K : ℂ)^s)⁻¹ * mixedInverseGammaUnit K s / (s-1)
  have hU : AnalyticAt ℂ U 0 :=
    ((((mixedCompletedDedekindXi_entire K).analyticAt 0).mul
      ((inverseDiscriminant_entire K).analyticAt 0)).mul
      ((mixedInverseGammaUnit_entire K).analyticAt 0)).div
      (analyticAt_id.sub analyticAt_const) (by norm_num)
  have hU0 : U 0 ≠ 0 := by
    dsimp [U]
    simp only [cpow_zero,inv_one,mul_one,zero_sub]
    exact div_ne_zero (mul_ne_zero (mixedCompletedDedekindXi_zero_ne_zero K)
      (mixedInverseGammaUnit_zero_ne K)) (by norm_num)
  apply (mixedDedekindZeta_analyticAt K (s := 0) (by norm_num)).analyticOrderAt_eq_natCast.mpr
  refine ⟨U,hU,hU0,Filter.Eventually.of_forall ?_⟩
  intro s
  simp only [sub_zero,smul_eq_mul,mixedDedekindZeta,mixedDedekindEntireNumerator,U]
  ring

theorem mixedDedekindZeta_meromorphicOrder_zero :
    meromorphicOrderAt (mixedDedekindZeta K) 0 =
      ((InfinitePlace.nrRealPlaces K : ℤ) + InfinitePlace.nrComplexPlaces K - 1) := by
  rw [(mixedDedekindZeta_analyticAt K (s := 0) (by norm_num)).meromorphicOrderAt_eq,
    mixedDedekindZeta_analyticOrder_zero, ENat.map_natCast]
  have hc : 1 ≤ Fintype.card (InfinitePlace K) := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt Fintype.card_pos)
  rw [← WithTop.coe_natCast, Nat.cast_sub hc]
  simp [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]


theorem mixedDedekindZeta_eventually_eq_continuation {s : ℂ} (hs : s ≠ 0) :
    mixedDedekindZeta K =ᶠ[𝓝 s] mixedDedekindZetaContinuation K := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  exact mixedDedekindZeta_eq_continuation K hz

theorem mixedDedekindZeta_logDeriv_eq_continuation {s : ℂ} (hs : s ≠ 0) :
    logDeriv (mixedDedekindZeta K) s = logDeriv (mixedDedekindZetaContinuation K) s :=
  (logDeriv_congr_nhds (mixedDedekindZeta_eventually_eq_continuation K hs)).eq_of_nhds

theorem mixedDedekindZeta_order_one : meromorphicOrderAt (mixedDedekindZeta K) 1 = -1 := by
  rw [meromorphicOrderAt_congr
    ((mixedDedekindZeta_eventually_eq_continuation K (s := 1) one_ne_zero).filter_mono
      nhdsWithin_le_nhds)]
  exact mixedDedekindZetaContinuation_order_one K

theorem mixedDedekindZeta_residue :
    Tendsto (fun s : ℂ => (s-1)*mixedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  apply (mixedDedekindZetaContinuation_residue K).congr'
  filter_upwards [(mixedDedekindZeta_eventually_eq_continuation K
    (s := 1) one_ne_zero).filter_mono nhdsWithin_le_nhds] with s hs
  rw [hs]

end
end ArtinMatthews.VaryingKummerAnalytic
