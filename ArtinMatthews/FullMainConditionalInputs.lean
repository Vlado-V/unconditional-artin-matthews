module

public import ArtinMatthews.VerifiedResults
public import ArtinMatthews.CubicGaloisFourier
public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantPrimeExtractionArithmetic
public import ArtinMatthews.KummerAngularSourceBounds
public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.GiantActualTupleMean
public import ArtinMatthews.PositiveDensityAngularInputs
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

/-! Three explicit analytic inputs imply the original full target.
The finite and real-cutoff conclusions use the existing obstruction
and density theorems. -/
namespace ArtinMatthews

open Filter MeasureTheory VaryingKummerAnalytic
open scoped Topology BigOperators Asymptotics ContDiff

noncomputable section

/-- Cancellation for the literal composite tuple sums in the source
order of sieve depth, array count and large real parameter. -/
def GiantOrdinaryTupleCancellationInput (ε : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
    ∀ (M : ℕ) [NeZero M], ∀ m ≥ 20000, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5) → Function.Injective e →
      ∀ (χ : DirichletCharacter ℂ M) j,
        j ∈ Finset.Icc 2 ⌈2 / markedSieveExponent (ε / 4) m⌉₊ →
        giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ
          (T + 1) (markedSieveExponent (ε / 4) m) j
            =o[atTop] (fun x : ℝ => x / Real.log x)

/-- The cubic-selected finite prime mean needed in the unobstructed
case, with the original cubic density and prime-factor statistic. -/
def GiantCubicSelectedMeanInput (ε : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ S : Finset ℤ, AdmissibleBases S → ¬ ObstructionA S → ¬ ObstructionB S →
    ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
      ∀ (M : ℕ) [NeZero M] (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ),
        (∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1) →
        Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
          giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x) atTop
          (𝓝 (((U.card : ℝ) / Nat.totient M *
            (cubicConditionDensity S * (giantPrimeConstant ε *
              ∫ t : ℝ, Φ t)) : ℝ) : ℂ))

/-- The growing-prime twelfth-angular estimates used by the Kummer
zero-region theorem. -/
def GiantAngularSourceInput : Prop :=
  ∀ (q : ℕ) [NeZero q], q.Prime → 2 < q → TwelfthAngularSourceBounds q

theorem GiantOrdinaryTupleCancellationInput.finite_mean
    {ε : ℝ} {Φ : ℝ → ℝ} (htuple : GiantOrdinaryTupleCancellationInput ε Φ)
    (hε : 0 < ε) (hεq : ε < 1 / 4)
    (hΦsmooth : ContDiff ℝ ∞ Φ) (hcompact : HasCompactSupport Φ)
    (hΦ0 : ∀ t, 0 ≤ Φ t) {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2)
    (hsupp : Function.support Φ ⊆ Set.Ioo 1 T)
    (M : ℕ) [NeZero M] (U : Finset (ZMod M)ˣ) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantUncenteredPrimeTest U ε Φ T x) atTop
      (𝓝 (((U.card : ℝ) / M.totient * giantPrimeConstant ε *
        ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  apply giant_uncentered_prime_mean_of_actual_tuples U ε hε hεq Φ
    (by norm_num : (0 : ℝ) < 1) hT₁.le
    (hΦsmooth.differentiable (by simp)) (hΦsmooth.continuous_deriv (by simp))
    hcompact hsupp hΦ0 (ε / 4) (by positivity) (by linarith)
  exact htuple T hT₁ hT₂ hsupp M

theorem fullMainStatement_of_actual_tuple_cubic_angular_inputs
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < 1 / 1000000)
    (Φ : ℝ → ℝ) (hΦsmooth : ContDiff ℝ ∞ Φ)
    (hΦcompact : HasCompactSupport Φ) (hΦsupport : tsupport Φ ⊆ Set.Ioo (1 : ℝ) 2)
    (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) (hΦnonzero : ∃ t, Φ t ≠ 0)
    (htuple : GiantOrdinaryTupleCancellationInput ε Φ)
    (hcubic : GiantCubicSelectedMeanInput ε Φ)
    (hsource : GiantAngularSourceInput) :
    FullMainStatement := by
  intro S hS
  refine ⟨?_, fun h => finite_of_obstruction h⟩
  rintro ⟨hA, hB⟩
  have hεq : ε < 1 / 4 := hεδ.trans (by norm_num)
  obtain ⟨hdyadic, _, hreal⟩ :=
    positive_density_of_smooth_mean_laws_and_angular_sources hS hA hB
      hε hεδ Φ hΦsmooth hΦcompact hΦsupport hΦrange hΦnonzero
      hsource (by
        intro T hT₁ hT₂ hs M _ U
        simpa only [mul_assoc] using
          htuple.finite_mean hε hεq hΦsmooth hΦcompact
            (fun t => (hΦrange t).1) hT₁ hT₂ hs M U) (hcubic S hS hA hB)
  exact ⟨hdyadic, hreal⟩

end
end ArtinMatthews
