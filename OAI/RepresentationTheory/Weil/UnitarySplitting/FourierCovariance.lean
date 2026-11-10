module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Fourier Covariance -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance.Construction

noncomputable section

/-! Fourier covariance with the Weyl operators, before Fourier inversion
or unitarity has been established. -/

open _root_.MeasureTheory
open scoped BigOperators

def phasePosition {F : Type} {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.Position F d :=
  fun i => v (Sum.inl i)

def phaseMomentum {F : Type} {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.Position F d :=
  fun i => v (Sum.inr i)

def fourierPhaseRotation {F : Type} [Neg F] {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.PhaseSpace F d :=
  Sum.elim (phaseMomentum v) (-phasePosition v)

theorem heisenbergFunction_dot {F : Type} [Field F] {d : ℕ}
    (ψ : AddChar F ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x = ψ (Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v)
      (x - (2 : F)⁻¹ • phasePosition v)) * f (x - phasePosition v) := by
  unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction Local.FunctionsMetaplectic.Construction.dot phasePosition phaseMomentum
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm (2 : F)⁻¹]

theorem fourierIntegral_heisenberg
    {F : Type} [NormedField F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (fourierPhaseRotation v) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  funext x
  rw [heisenbergFunction_dot]
  change _ = ψ (Local.FunctionsMetaplectic.Construction.dot (-phasePosition v) (x - (2 : F)⁻¹ • phaseMomentum v)) *
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (x - phaseMomentum v)
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_add_right_eq_self
    (fun y => Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) (phasePosition v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [heisenbergFunction_dot, add_sub_cancel_right]
    have hphase : Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v) (y + phasePosition v - (2 : F)⁻¹ • phasePosition v) -
        Local.FunctionsMetaplectic.Construction.dot x (y + phasePosition v) =
      Local.FunctionsMetaplectic.Construction.dot (-phasePosition v) (x - (2 : F)⁻¹ • phaseMomentum v) - Local.FunctionsMetaplectic.Construction.dot (x - phaseMomentum v) y := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = ψ (Local.FunctionsMetaplectic.Construction.dot (phaseMomentum v)
          (y + phasePosition v - (2 : F)⁻¹ • phasePosition v) - Local.FunctionsMetaplectic.Construction.dot x (y + phasePosition v)) * f y := by
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring
      _ = _ := by
        rw [hphase]
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance.Construction
