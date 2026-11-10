module

public import ArtinMatthews.SourceKPCubicCenterAction
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

/-! The cubic center preserves each archimedean stabilizer and transports
the actual component embeddings through the identity archimedean map. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCenter_rationalStabilizer (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPRationalFiniteStabilizer K hζ (z • b) = sourceKPRationalFiniteStabilizer K hζ b :=
  MulAction.stabilizer_smul_eq_right (G := PGL(2, K)) z b

theorem sourceKPCubicCenter_archSubgroup (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPArchComponentSubgroup K hζ (z • b) = sourceKPArchComponentSubgroup K hζ b := by
  simp only [sourceKPArchComponentSubgroup, sourceKPCubicCenter_rationalStabilizer]

theorem sourceKPCubicCenter_component_point (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    z • sourceKPArchComponentPoint K hζ b a = sourceKPArchComponentPoint K hζ (z • b) a := by
  change (Quotient.mk _ (z • (a, b)) : SourceKPAutomorphicLevel K hζ) = Quotient.mk _ (a, z • b)
  rw [sourceKPCubicCenter_finiteLevel_pair]

def sourceKPCubicCenterComponentHomeomorph (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b)) ≃ₜ
      Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ (z • b))) where
  toEquiv := Quotient.congr (Equiv.refl _) (by
    intro a c
    rw [sourceKPCubicCenter_archSubgroup]
    rfl)
  continuous_toFun := continuous_quot_mk.quotient_lift _
  continuous_invFun := continuous_quot_mk.quotient_lift _

theorem sourceKPCubicCenterComponentHomeomorph_mk (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPCubicCenterComponentHomeomorph K hζ z b (Quotient.mk _ a) = Quotient.mk _ a := rfl

theorem sourceKPCubicCenter_component_embedding (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ)
    (x : Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) :
    z • sourceKPArchComponentEmbedding K hζ b x =
      sourceKPArchComponentEmbedding K hζ (z • b) (sourceKPCubicCenterComponentHomeomorph K hζ z b x) := by
  induction x using Quotient.inductionOn with
  | _ a => exact sourceKPCubicCenter_component_point K hζ z b a

theorem sourceKPCubicCenter_inverse_eval
    (F : SourceKPAutomorphicLevel K hζ → ℂ)
    (hF : ∀ (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicLevel K hζ),
      F (z • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ) * F x)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicLevel K hζ) :
    F (z⁻¹ • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ * F x := by
  simpa only [map_inv, Units.val_inv_eq_inv_val] using hF z⁻¹ x

end
end ArtinMatthews
