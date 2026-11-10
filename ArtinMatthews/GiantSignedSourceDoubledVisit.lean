module

public import ArtinMatthews.GiantSignedSourceVisitEnergy
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

/-! The actual absolute ghost visit with doubled birth weight has the
same source memory-weight choice as the signed visit. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

def giantSignedSourceDoubledVisit (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) : GiantSignedState PS PB M → ℂ :=
  giantSignedStateGhostApply PS ν (fun _ => (|qi / ρ ^ 2| : ℝ))
    (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f

theorem giantSignedSourceDoubledVisit_energy
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (V : B → ℝ) {Vmax qi ρ v C₀ L : ℝ}
    (hVmax : 0 ≤ Vmax) (hV0 : ∀ g, 0 ≤ V g) (hV : ∀ g, V g ≤ Vmax)
    (hVS : ∀ g, 0 < bandReciprocalMass (PS g))
    (hρ : 0 < ρ) (hv : 0 < v) (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1)
    (hL : 0 < L) (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (hrow : |qi / ρ ^ 2| + |-(1-qi) / ρ| / v ≤ 1)
    (hcol : ∀ g, |qi / ρ ^ 2| + 2 * |-(1-qi) * V g / ρ| / v ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m)))
    (U u : ℝ) (hU : 0 ≤ U) (hu : 0 < u)
    (hf : ∀ s a m, ‖f (s,a,m)‖ ≤ U * u ^ (∑ g, m.1 g)) :
    giantSignedStateEnergy PS ν (giantSignedSourceDoubledVisit PS ν V qi ρ f) ≤
      ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ (2 * Vmax) ρ v) *
        giantSignedStateEnergy PS ν f := by
  let A : B → ℂ := fun _ => (|qi / ρ ^ 2| : ℝ)
  let C : B → ℂ := fun g => (2 * |-(1-qi) * V g / ρ| : ℝ)
  let D : B → ℂ := fun _ => (|-(1-qi) / ρ| : ℝ)
  have hA (g : B) : ‖A g‖ = |qi / ρ ^ 2| := by
    simp only [A, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have hC (g : B) : ‖C g‖ = 2 * |-(1-qi) * V g / ρ| := by
    change ‖((2 * |-(1-qi) * V g / ρ| : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hD (g : B) : ‖D g‖ = |-(1-qi) / ρ| := by
    simp only [D, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have he := giantSignedStateGhostApply_energy PS hVS ν hν A C D v hv
    (fun g => by rw [hA g, hD g]; exact hrow) (fun g => by rw [hA g, hC g]; exact hcol g)
    f hsym U u hU hu hf
  simp only [hC, hD] at he
  refine he.trans (mul_le_mul_left ?_ _)
  have hfactor := giantSignedSourceVisitFactor_le PB ν hν hMass (fun g => 2 * V g)
    (mul_nonneg (by norm_num) hVmax) (fun g => mul_nonneg (by norm_num) (hV0 g))
    (fun g => mul_le_mul_of_nonneg_left (hV g) (by norm_num)) hρ hv.le hqi0 hqi1 hL hgroups
  have hscale (g : B) : |-(1-qi) * (2 * V g) / ρ| = 2 * |-(1-qi) * V g / ρ| := by
    rw [show -(1-qi) * (2 * V g) / ρ = 2 * (-(1-qi) * V g / ρ) by ring,
      abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  simpa only [hscale] using hfactor

end
end ArtinMatthews
