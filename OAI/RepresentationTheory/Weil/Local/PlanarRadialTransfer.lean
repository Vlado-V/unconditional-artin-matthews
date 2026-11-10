module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact
public import OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools


set_option backward.privateInPublic true
@[expose] public section

/-! # Planar Radial Transfer -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer.Construction

noncomputable section

/-! Moving the planar quadratic phase's Laplacian to a radial amplitude. -/

open _root_.MeasureTheory

def planarRadialTransferIntegrable (b : ℝ) (F F' F'' : ℝ → ℂ) : Prop :=
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialX F' * PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialXX F' F'' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialX F' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialY F' * PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialYY F' F'' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadial F * PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) ∧
  Integrable (PlanarRadialCompact.Construction.planarRadialY F' * PlanarQuadraticPhase.Construction.planarQuadraticPhase b)

theorem planar_radial_quadratic_integral_transfer
    (b : ℝ) (F F' F'' : ℝ → ℂ)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t)
    (hF' : ∀ t, 0 ≤ t → HasDerivAt F' (F'' t) t)
    (hI : planarRadialTransferIntegrable b F F' F'') :
    -(b : ℂ) ^ 2 * (∫ z, (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F (PlanarRadialCompact.Construction.planarRadiusSquared z) *
      PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) =
      ∫ z, ((PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F'' (PlanarRadialCompact.Construction.planarRadiusSquared z) +
        F' (PlanarRadialCompact.Construction.planarRadiusSquared z)) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hI
  have hx := OscillatoryTailTools.Construction.integral_planar_second_derivative_transfer
    (PlanarRadialCompact.Construction.planarRadial F) (PlanarRadialCompact.Construction.planarRadialX F') (PlanarRadialCompact.Construction.planarRadialXX F' F'')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseX b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b)
    (PlanarRadialCompact.Construction.planarRadial_hasDerivAt_x F F' hF) (PlanarRadialCompact.Construction.planarRadialX_hasDerivAt_x F' F'' hF')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase_hasDerivAt_x b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseX_hasDerivAt_x b)
    h1 h2 h3 h4 h5
  have hy := OscillatoryTailTools.Construction.integral_planar_second_derivative_transfer_right
    (PlanarRadialCompact.Construction.planarRadial F) (PlanarRadialCompact.Construction.planarRadialY F') (PlanarRadialCompact.Construction.planarRadialYY F' F'')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseY b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b)
    (PlanarRadialCompact.Construction.planarRadial_hasDerivAt_y F F' hF) (PlanarRadialCompact.Construction.planarRadialY_hasDerivAt_y F' F'' hF')
    (PlanarQuadraticPhase.Construction.planarQuadraticPhase_hasDerivAt_y b) (PlanarQuadraticPhase.Construction.planarQuadraticPhaseY_hasDerivAt_y b)
    h6 h7 h8 h9 h10
  have hsum : (∫ z, PlanarRadialCompact.Construction.planarRadial F z *
      (PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b z + PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b z)) =
      ∫ z, (PlanarRadialCompact.Construction.planarRadialXX F' F'' z + PlanarRadialCompact.Construction.planarRadialYY F' F'' z) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
    simp_rw [mul_add, add_mul]
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadial F z * PlanarQuadraticPhase.Construction.planarQuadraticPhaseXX b z) at h1
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadial F z * PlanarQuadraticPhase.Construction.planarQuadraticPhaseYY b z) at h6
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadialXX F' F'' z * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) at h3
    change Integrable (fun z => PlanarRadialCompact.Construction.planarRadialYY F' F'' z * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) at h8
    rw [integral_add h1 h6, integral_add h3 h8, hx, hy]
  simp_rw [PlanarQuadraticPhase.Construction.planarQuadraticPhase_laplacian, PlanarRadialCompact.Construction.planarRadial_laplacian] at hsum
  have heq : (-4 * (b : ℂ) ^ 2) *
      (∫ z, (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F (PlanarRadialCompact.Construction.planarRadiusSquared z) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) =
      4 * ∫ z, ((PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * F'' (PlanarRadialCompact.Construction.planarRadiusSquared z) +
        F' (PlanarRadialCompact.Construction.planarRadiusSquared z)) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
    convert hsum using 1
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold PlanarRadialCompact.Construction.planarRadial PlanarRadialCompact.Construction.planarRadiusSquared
        push_cast
        ring
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
  linear_combination (1 / 4 : ℂ) * heq

end

end OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer.Construction
