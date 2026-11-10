module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot
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

/-! # Subring Big Cell Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant.CM

noncomputable section

/-! Exact determinant comparison between an integral symplectic matrix
and its image in the ambient field, including inverse integrality. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

variable {I K : Type*} [Fintype I] [CommRing K]

theorem determinant_map (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S)
    (B : Matrix I I S) :
    S.subtype (((Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic S g hg).val.toBlocks₁₁ +
      B * (Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic S g hg).val.toBlocks₂₁).det) =
      (g.val.toBlocks₁₁ + B.map S.subtype * g.val.toBlocks₂₁).det := by
  rw [RingHom.map_det, map_add, map_mul]
  rfl

theorem inverse_mem {K : Type*} [Field K] (S : Subring K) (x : S) (hx : IsUnit x) :
    (x.val)⁻¹ ∈ S := by
  obtain ⟨u, rfl⟩ := hx
  have he : ((u.val : S) : K)⁻¹ = (((u⁻¹).val : S) : K) := by
    exact (Units.val_inv_eq_inv_val (Units.map S.subtype.toMonoidHom u)).symm
  rw [he]
  exact (u⁻¹).val.property

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant.CM
