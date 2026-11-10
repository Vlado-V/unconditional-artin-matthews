module

public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverage
public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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

/-! Actual unit periodicity of the mixed ideal theta and its continuation.
This prepares the change of fundamental domain in the trace-dual functional
equation. -/
namespace ArtinMatthews.ReusedTheta
open MeasureTheory Set
open scoped Classical BigOperators
noncomputable section

/-- Generic theta uniqueness argument extracted from OpenAI PrimePackets /
IdealThetaXi.lean. -/
theorem thetaMellinXi_congr_of_normalizedTheta {ι : Type*} [Fintype ι]
    (B C : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hBC : ∀ t : ℝ, normalizedTheta B t = normalizedTheta C t) :
    thetaMellinXi B = thetaMellinXi C := by
  have H : ∀ s : ℂ, (Fintype.card ι : ℝ)/2 < s.re → thetaMellinXi B s = thetaMellinXi C s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro he
      simp only [he, Complex.zero_re] at hs
      have : (0 : ℝ) ≤ (Fintype.card ι : ℝ)/2 := by positivity
      linarith
    have hsa : s ≠ (Fintype.card ι : ℂ)/2 := by
      intro he
      simp [he] at hs
    rw [thetaMellinXi_eq B hs0 hsa, thetaMellinXi_eq C hs0 hsa,
      ← (normalizedTheta_hasMellin B hs).2, ← (normalizedTheta_hasMellin C hs).2]
    simp_rw [hBC]
  apply ((thetaMellinXi_differentiable B).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    ((thetaMellinXi_differentiable C).differentiableOn.analyticOnNhd isOpen_univ)
    (z₀ := (Fintype.card ι : ℂ)/2+1)
  have hx : (Fintype.card ι : ℝ)/2 < ((Fintype.card ι : ℂ)/2+1).re := by simp
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with s hs
  exact H s hs
end
end ArtinMatthews.ReusedTheta

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedIdealFlowTheta_unit_periodic (z : (𝓞 K)ˣ) (u : logSpace K) (t : ℝ) :
    mixedIdealFlowTheta K I (logEmbedding K (Additive.ofMul z) + u) t =
      mixedIdealFlowTheta K I u t := by
  let e : I.1 ≃ I.1 := MulAction.toPerm z
  have he (a : I.1) : ((e a : I.1) : K) = (z : K) * (a : K) := rfl
  unfold mixedIdealFlowTheta
  simp_rw [← Complex.ofReal_pow, mixedIdealFlow_norm_sq]
  have hx (a : I.1) :
      ∑ w : InfinitePlace K,
        (mixedPlaceWeight K (logEmbedding K (Additive.ofMul z) + u) w * w (a : K))^2 =
      ∑ w : InfinitePlace K, (mixedPlaceWeight K u w * w ((e a : I.1) : K))^2 := by
    simp only [he, map_mul, mixedPlaceWeight_add, mixedPlaceWeight_unit]
    apply Finset.sum_congr rfl
    intro w _
    ring
  simp_rw [hx]
  exact e.tsum_eq (fun a : I.1 => Complex.exp
    (-((Real.pi*t : ℝ) : ℂ) *
      ((∑ w : InfinitePlace K, (mixedPlaceWeight K u w * w (a : K))^2 : ℝ) : ℂ)))

theorem mixedIdealFlowXi_unit_periodic (z : (𝓞 K)ˣ) (u : logSpace K) (s : ℂ) :
    thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
      (mixedIdealLogScale K I (logEmbedding K (Additive.ofMul z) + u))) s =
    thetaMellinXi (logScaledLattice (mixedIdealMatrix K I)
      (mixedIdealLogScale K I u)) s := by
  apply congrFun (thetaMellinXi_congr_of_normalizedTheta _ _ ?_) s
  intro t
  simp_rw [← mixedIdealFlowTheta_eq_normalizedTheta]
  exact mixedIdealFlowTheta_unit_periodic K I z u t

end
end ArtinMatthews.VaryingKummerAnalytic
