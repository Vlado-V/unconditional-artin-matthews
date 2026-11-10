module

public import ArtinMatthews.SLocalWholePowerClasses
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual S-local logarithm uses the square of the complex modulus
and the norm-normalized finite-place absolute values. Its diagonal
S-unit restriction is the genuine full logarithmic lattice. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sLocalLog (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (SWholeUnits K S) →+ FullLogSpace (K := K) S where
  toFun x p := match p with
    | Sum.inl w => w.mult * Real.log ‖(x.toMul.1 w : w.Completion)‖
    | Sum.inr v => Real.log ‖(x.toMul.2 v : v.1.adicCompletion K)‖
  map_zero' := by ext p; cases p <;> simp
  map_add' x y := by
    ext p
    cases p <;> simp [norm_mul, Real.log_mul, mul_add]

theorem sLocalLog_diagonal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) S) :
    sLocalLog K S (Additive.ofMul (sWholeDiagonal K S (u : Kˣ))) =
      fullLogAmbient (K := K) S (Additive.ofMul u) := by
  ext p
  cases p with
  | inl w =>
    have hw := InfiniteIdeleGroup.norm_infiniteComponent_principalIdele (u : Kˣ) w
    change ‖algebraMap K w.Completion ((u : Kˣ) : K)‖ = w ((u : Kˣ) : K) at hw
    exact congrArg (fun r : ℝ => (w.mult : ℝ) * Real.log r) hw
  | inr v =>
    change Real.log ‖FinitePlace.embedding v.1 (((u : Kˣ) : K))‖ = _
    rw [FinitePlace.norm_embedding]
    rfl

def sLocalLogSum (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (SWholeUnits K S) →+ ℝ :=
  (coordinateSum (K := K) S).toAddMonoidHom.comp (sLocalLog K S)

def sLocalNorm (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SWholeUnits K S) : ℝ :=
  Real.exp (sLocalLogSum K S (Additive.ofMul y))

theorem sLocalNorm_pos (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SWholeUnits K S) :
    0 < sLocalNorm K S y := Real.exp_pos _

theorem sLocalNorm_eq_prod (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SWholeUnits K S) :
    sLocalNorm K S y =
      (∏ w : InfinitePlace K, ‖(y.1 w : w.Completion)‖ ^ w.mult) *
        ∏ v : S, ‖(y.2 v : v.1.adicCompletion K)‖ := by
  unfold sLocalNorm sLocalLogSum
  change Real.exp (∑ p : LogPlace (K := K) S,
    sLocalLog K S (Additive.ofMul y) p) = _
  rw [Fintype.sum_sum_type, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    change Real.exp (w.mult * Real.log ‖(y.1 w : w.Completion)‖) = _
    rw [Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr (y.1 w).ne_zero)]
  · apply Finset.prod_congr rfl
    intro v _
    exact Real.exp_log (norm_pos_iff.mpr (y.2 v).ne_zero)

@[simp] theorem sLocalNorm_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : SWholeUnits K S) :
    sLocalNorm K S (x * y) = sLocalNorm K S x * sLocalNorm K S y := by
  change Real.exp (sLocalLogSum K S
    (Additive.ofMul x + Additive.ofMul y)) = _
  rw [map_add, Real.exp_add]
  rfl

@[simp] theorem sLocalNorm_sUnit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) S) : sLocalNorm K S (sWholeDiagonal K S (u : Kˣ)) = 1 := by
  change Real.exp (coordinateSum (K := K) S
    (sLocalLog K S (Additive.ofMul (sWholeDiagonal K S (u : Kˣ))))) = 1
  rw [sLocalLog_diagonal, fullLogAmbient_mem_logHyperplane, Real.exp_zero]

theorem continuous_sLocalLog (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (fun y : SWholeUnits K S => sLocalLog K S (Additive.ofMul y)) := by
  apply continuous_pi
  intro p
  cases p with
  | inl w =>
    change Continuous (fun y : SWholeUnits K S =>
      (w.mult : ℝ) * Real.log ‖(y.1 w : w.Completion)‖)
    exact continuous_const.mul ((Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)).norm.log
      (fun y => norm_ne_zero_iff.mpr (y.1 w).ne_zero))
  | inr v =>
    change Continuous (fun y : SWholeUnits K S => Real.log ‖(y.2 v : v.1.adicCompletion K)‖)
    exact ((Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)).norm.log
      (fun y => norm_ne_zero_iff.mpr (y.2 v).ne_zero))

theorem continuous_sLocalLogSum (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (fun y : SWholeUnits K S => sLocalLogSum K S (Additive.ofMul y)) :=
  (coordinateSum (K := K) S).continuous_of_finiteDimensional.comp (continuous_sLocalLog K S)

theorem sLocalNorm_eq_one_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SWholeUnits K S) :
    sLocalNorm K S y = 1 ↔ sLocalLogSum K S (Additive.ofMul y) = 0 :=
  Real.exp_eq_one_iff _

end
end ArtinMatthews
