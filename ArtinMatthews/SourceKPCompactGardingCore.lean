module

public import ArtinMatthews.SourceKPCompactExhaustionCore
public import ArtinMatthews.SourceKPCompactHeightMass
public import ArtinMatthews.SourceKPActualExteriorHardy
public import ArtinMatthews.SourceKPCompactCoreMassNorm
public import ArtinMatthews.SourceKPCompactEnergyRegularity
public import ArtinMatthews.SourceKPCompactTrigEnergy
public import ArtinMatthews.SourceKPCompactTrigMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual compact test core retains the full exterior Hardy threshold. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactCore_garding (n : ℕ) (f : T) (C : ℝ)
    (hC : ∀ y : Y, sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ (n+1)) y ≤ C) :
    (InfinitePlace.nrComplexPlaces K : ℝ) * ‖sourceKPCompactCoreMass K hζ 2 f‖^2 ≤
      (∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μ) +
        ((InfinitePlace.nrComplexPlaces K : ℝ) + (Real.pi/2)^2*C) *
          ‖sourceKPCompactH1LocalizedMass K hζ (Real.exp (((n+1 : ℕ) : ℝ)+2))
            (sourceKPCompactH1Core K hζ ⟨f⟩)‖^2 := by
  let r : ℝ := InfinitePlace.nrComplexPlaces K
  let c := Real.pi/2
  let R := Real.exp (((n+1 : ℕ) : ℝ)+2)
  let A := sourceKPCompactExhaustionCos K hζ (n+1) f
  let B := sourceKPCompactExhaustionSin K hζ (n+1) f
  let η := sourceKPCompactExhaustionC2 K hζ (n+1)
  let E (g : T) := ∫ y, sourceKPCompactCoreEnergy K hζ g y ∂μ
  let N (g : T) := ∫ y, ‖g.val y‖^2 ∂μ
  let L := ∫ y in {y : Y | sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R}, ‖f.val y‖^2 ∂μ
  let J := ∫ y, ‖f.val y‖^2 * sourceKPCompactCoreEnergy K hζ η y ∂μ
  have hr : 0 ≤ r := by positivity
  have hA : N A ≤ L := sourceKPCompactExhaustionCos_mass_le K hζ (n+1) f
  have hE0 : 0 ≤ E A := integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ A)
  have hJ : J ≤ C*L := sourceKPCompactExhaustion_energyMass_le K hζ (n+1) f C hC
  have hB : r*N B ≤ E B := sourceKPExteriorCore_hardy K hζ B
    (Real.exp ((n : ℝ)+1)) (Real.one_lt_exp_iff.mpr (by positivity))
    (sourceKPCompactExhaustionSin_tsupport_high K hζ n f)
  have hN : N f = N A + N B := by
    change (∫ y, ‖f.val y‖^2 ∂μ) =
      (∫ y, ‖A.val y‖^2 ∂μ) + ∫ y, ‖B.val y‖^2 ∂μ
    rw [← integral_add (sourceKPCompactCore_norm_sq_integrable K hζ A)
      (sourceKPCompactCore_norm_sq_integrable K hζ B)]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      (sourceKPCompactExhaustionTrigMass_partition K hζ (n+1) f y).symm)
  have hE : E A + E B = E f + c^2*J := by
    have hAint := sourceKPCompactCoreEnergy_integrable K hζ A
    have hBint := sourceKPCompactCoreEnergy_integrable K hζ B
    have hfint := sourceKPCompactCoreEnergy_integrable K hζ f
    have hJint := sourceKPCompactExhaustion_energyMass_integrable K hζ (n+1) f
    change (∫ y, sourceKPCompactCoreEnergy K hζ A y ∂μ) +
        (∫ y, sourceKPCompactCoreEnergy K hζ B y ∂μ) =
      (∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μ) +
        c^2 * ∫ y, ‖f.val y‖^2 * sourceKPCompactCoreEnergy K hζ η y ∂μ
    rw [← integral_add hAint hBint,← integral_const_mul,
      ← integral_add hfint (hJint.const_mul (c^2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      simpa only [mul_assoc,c] using sourceKPCompactExhaustion_trig_energy K hζ (n+1) f y
  rw [sourceKPCompactCoreMass_norm_sq,sourceKPCompactH1LocalizedMass_core_norm_sq_value]
  change r*N f ≤ E f+(r+c^2*C)*L
  calc
    _ = r*N A+r*N B := by rw [hN,mul_add]
    _ ≤ r*L+E B := add_le_add (mul_le_mul_of_nonneg_left hA hr) hB
    _ ≤ r*L+(E A+E B) := add_le_add (le_refl _) (le_add_of_nonneg_left hE0)
    _ = E f+(r*L+c^2*J) := by rw [hE]; ring
    _ ≤ E f+(r*L+c^2*(C*L)) := add_le_add (le_refl _)
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hJ (sq_nonneg _)))
    _ = _ := by ring

end
end ArtinMatthews
