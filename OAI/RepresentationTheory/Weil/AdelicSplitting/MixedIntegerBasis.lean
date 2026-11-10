module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis
public import OAI.RepresentationTheory.Weil.AdelicSplitting.MixedFiniteDuality
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

/-! # Mixed Integer Basis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.MixedIntegerBasis.Construction

noncomputable section

/-! A real basis for the scaled integer position lattice, with an exact
identification between integer coordinates and tuples of algebraic integers. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

abbrev MixedPositionIndex := Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)

def integerPositionCoordinates : (Fin N → 𝓞 F) ≃ₗ[ℤ] (MixedPositionIndex F N → ℤ) :=
  PositionBasis.LocalAnalysis.positionBasisCoordinates N (RingOfIntegers.basis F)

def scaledMixedScalarBasis (M : ℕ) (hM : 0 < M) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (mixedEmbedding.mixedSpace F) :=
  (mixedEmbedding.latticeBasis F).unitsSMul (fun _ => Units.mk0 (M : ℝ) (by exact_mod_cast hM.ne'))

def mixedIntegerPositionBasis (M : ℕ) (hM : 0 < M) :
    Module.Basis (MixedPositionIndex F N) ℝ (Fin N → mixedEmbedding.mixedSpace F) :=
  PositionBasis.LocalAnalysis.positionBasis N (scaledMixedScalarBasis F M hM)

theorem integer_lattice_coordinates (r : 𝓞 F) :
    (mixedEmbedding.latticeBasis F).equivFun (mixedEmbedding F (algebraMap (𝓞 F) F r)) =
      fun j => ((RingOfIntegers.basis F).equivFun r j : ℝ) := by
  funext j
  simp only [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply,
    integralBasis_repr_apply, eq_intCast, Rat.cast_intCast]

theorem scaledMixedScalarBasis_integer_symm (M : ℕ) (hM : 0 < M)
    (n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) :
    (scaledMixedScalarBasis F M hM).equivFun.symm (fun j => (n j : ℝ)) =
      mixedEmbedding F ((M : F) * algebraMap (𝓞 F) F ((RingOfIntegers.basis F).equivFun.symm n)) := by
  have hb : (mixedEmbedding.latticeBasis F).equivFun.symm (fun j => (n j : ℝ)) =
      mixedEmbedding F (algebraMap (𝓞 F) F ((RingOfIntegers.basis F).equivFun.symm n)) := by
    apply (mixedEmbedding.latticeBasis F).equivFun.injective
    rw [(mixedEmbedding.latticeBasis F).equivFun.apply_symm_apply, integer_lattice_coordinates]
    simp only [(RingOfIntegers.basis F).equivFun.apply_symm_apply]
  calc
    _ = (M : ℝ) • (mixedEmbedding.latticeBasis F).equivFun.symm (fun j => (n j : ℝ)) := by
      rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [scaledMixedScalarBasis, Module.Basis.unitsSMul_apply, smul_smul, mul_comm]
    _ = _ := by
      rw [hb, map_mul, map_natCast]
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem mixedIntegerPositionBasis_integer_symm (M : ℕ) (hM : 0 < M)
    (n : MixedPositionIndex F N → ℤ) :
    (mixedIntegerPositionBasis F N M hM).equivFun.symm (fun p => (n p : ℝ)) =
      MixedFiniteDuality.Construction.mixedScalarIntegerPosition F N (M : F) ((integerPositionCoordinates F N).symm n) := by
  funext i
  rw [mixedIntegerPositionBasis, PositionBasis.LocalAnalysis.positionBasis_equivFun_symm]
  exact scaledMixedScalarBasis_integer_symm F M hM (fun j => n (i, j))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.MixedIntegerBasis.Construction
