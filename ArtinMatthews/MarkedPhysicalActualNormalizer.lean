module

public import ArtinMatthews.MarkedPhysicalCoordinateCopyBounds
public import ArtinMatthews.MarkedEstimateMertensBands
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

/-! The literal physical mass and coordinate-edge normalizer are bounded
using the actual finite-band reciprocal mass theorem. No normalized
physical measure or tilted-memory adjoint is substituted. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def markedPhysicalBandInverseBound : ℝ := (Real.log 2/2)⁻¹

theorem markedPhysicalBandInverseBound_pos : 0 < markedPhysicalBandInverseBound := by
  unfold markedPhysicalBandInverseBound
  positivity

def markedPhysicalActualEdgeBound (groups : ℕ) (etaBound psiBound : ℝ) : ℝ :=
  5*markedPhysicalBandInverseBound^groups*etaBound^2*psiBound

theorem markedPhysicalActualEdgeBound_nonneg (groups : ℕ) {etaBound psiBound : ℝ}
    (hpsi : 0 ≤ psiBound) :
    0 ≤ markedPhysicalActualEdgeBound groups etaBound psiBound := by
  unfold markedPhysicalActualEdgeBound
  have hc := markedPhysicalBandInverseBound_pos
  positivity

theorem markedPhysicalActualNormalizer_bounds {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,0 < e j) (etaBound psiBound : ℝ)
    (hpsi : 0 ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop,
      (∀ M : ℕ,0 ≤ markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M ∧
        markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) M ≤
          Real.exp (markedPhysicalBandInverseBound*(Fintype.card J:ℝ)*M)) ∧
      markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) etaBound psiBound ≤
        markedPhysicalActualEdgeBound (Fintype.card J) etaBound psiBound := by
  have hm := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he j))
  filter_upwards [hm] with x hx
  have hV (j : J) : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) := by
    exact (show 0 < Real.log 2/2 by positivity).trans (hx j).1
  have hinv (j : J) : (bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹ ≤ markedPhysicalBandInverseBound := by
    exact (inv_le_inv₀ (hV j) (by positivity : 0 < Real.log 2/2)).mpr (hx j).1.le
  have hc : 0 ≤ markedPhysicalBandInverseBound := markedPhysicalBandInverseBound_pos.le
  have hce : markedPhysicalBandInverseBound ≤ Real.exp markedPhysicalBandInverseBound := by
    linarith [Real.add_one_le_exp markedPhysicalBandInverseBound]
  constructor
  · intro M
    constructor
    · exact markedPhysicalMass_nonneg _ M (fun j => (hV j).le)
    · calc
        _ ≤ ∏ _j : J,(Real.exp markedPhysicalBandInverseBound)^M :=
          Finset.prod_le_prod₀ (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) M)
            (fun j _ => pow_le_pow_left₀ (inv_nonneg.mpr (hV j).le) ((hinv j).trans hce) M)
        _ = _ := by
          simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
          congr 1
          ring
  · have hp0 : 0 ≤ ∏ j,(bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹ :=
      Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (hV j).le)
    have hp : (∏ j,(bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹) ≤
        markedPhysicalBandInverseBound^(Fintype.card J) := by
      calc
        _ ≤ ∏ _j : J,markedPhysicalBandInverseBound :=
          Finset.prod_le_prod₀ (fun j _ => inv_nonneg.mpr (hV j).le) (fun j _ => hinv j)
        _ = _ := by simp
    unfold markedPhysicalCoordinateEdgeBound markedPhysicalActualEdgeBound
    rw [abs_of_nonneg hp0]
    gcongr

end
end ArtinMatthews
