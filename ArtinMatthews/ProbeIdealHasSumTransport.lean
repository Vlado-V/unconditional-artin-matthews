module

public import ArtinMatthews.ProbeIdealRawSeries
public import ArtinMatthews.ProbePrimeRawWeights
public import ArtinMatthews.ProbeIdealRawWeights
public import ArtinMatthews.ProbeIdealSurvivorIndex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Structural transport of a convergent survivor sum back to the actual
raw local index. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdeal_hasSum_transport (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (f : ProbeLocalRawIndex → ℂ) (s : ℂ)
    (hzero : ∀ i, probeIdealLocalCoefficient K P χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0 → f i = 0)
    (hs : HasSum (fun j : ProbeLocalSurvivor => f (probeLocalSurvivorIndex j)) s) :
    HasSum f s := by
  apply (probeLocalSurvivorIndex_injective.hasSum_iff ?_).mp hs
  intro i hi
  apply hzero
  by_contra hc
  exact hi (probeIdealCoefficient_support K P χ hχ hminus i hc)

theorem probeIdealRaw_survivor_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) :
    (fun j : ProbeLocalSurvivor =>
      probeIdealRawTerm K P χ η θ a b V (probeLocalSurvivorIndex j)) =
      probeLocalSurvivorValue (Ideal.absNorm (P.asIdeal))
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6)
        (θ * b) (η * θ⁻¹ * a) V := by
  funext j
  exact probeIdealRawTerm_survivor K P χ hχ hminus hchar η θ a b V hθ j

end

end ArtinMatthews.VaryingKummerAnalytic
