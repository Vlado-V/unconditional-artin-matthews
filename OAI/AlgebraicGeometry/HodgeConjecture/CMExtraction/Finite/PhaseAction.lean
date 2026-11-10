module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Phase Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

noncomputable section

/-! The actual symplectic action on momentum and position coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def finiteMomentum (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => (g.val *ᵥ Sum.elim p q) (Sum.inl i)

def finitePosition (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => (g.val *ᵥ Sum.elim p q) (Sum.inr i)

theorem finitePhase_elim (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (finiteMomentum g p q) (finitePosition g p q) = g.val *ᵥ Sum.elim p q := by
  funext i
  cases i <;> rfl

theorem finiteMomentum_cancel (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    finiteMomentum g (finiteMomentum g⁻¹ p q) (finitePosition g⁻¹ p q) = p := by
  change (fun i => (g.val *ᵥ Sum.elim (finiteMomentum g⁻¹ p q)
    (finitePosition g⁻¹ p q)) (Sum.inl i)) = p
  rw [finitePhase_elim, Matrix.mulVec_mulVec]
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [h, Matrix.one_mulVec]
  rfl

theorem finitePosition_cancel (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    finitePosition g (finiteMomentum g⁻¹ p q) (finitePosition g⁻¹ p q) = q := by
  change (fun i => (g.val *ᵥ Sum.elim (finiteMomentum g⁻¹ p q)
    (finitePosition g⁻¹ p q)) (Sum.inr i)) = q
  rw [finitePhase_elim, Matrix.mulVec_mulVec]
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [h, Matrix.one_mulVec]
  rfl

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_intertwines_inverse_input (m : MpF) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hh : ∀ x, h.val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
      (finiteMomentum (D.finite.project m)⁻¹ p q)
      (finitePosition (D.finite.project m)⁻¹ p q) f.val x) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action m h).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (D.finite.action m f).val x := by
  have ht := D.finite.intertwines m _ _ f h hh x
  change (D.finite.action m h).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
    (finiteMomentum (D.finite.project m)
      (finiteMomentum (D.finite.project m)⁻¹ p q) (finitePosition (D.finite.project m)⁻¹ p q))
    (finitePosition (D.finite.project m)
      (finiteMomentum (D.finite.project m)⁻¹ p q) (finitePosition (D.finite.project m)⁻¹ p q))
    (D.finite.action m f).val x at ht
  simpa only [finiteMomentum_cancel, finitePosition_cancel] using ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport
