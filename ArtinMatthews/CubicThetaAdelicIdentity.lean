module

public import ArtinMatthews.CubicThetaFiniteTest
public import ArtinMatthews.CubicThetaSiegelData
public import ArtinMatthews.CubicTheta
public import ArtinMatthews.CubicThetaTransform
public import ArtinMatthews.CubicThetaHolomorphicLattice
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The finite-adelic theta series is literally the actual weighted Eisenstein ideal theta. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM
open OAI OAI.SevenEighths Complex UpperHalfPlane

/-- An exact support reindexing, from rational points to integral points. -/
theorem theta_finiteResidueTest_eq_integer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} [NeZero N] (w : (ι → ZMod N) → ℂ) (Z : SiegelMatrix ι) (z : ι → ℂ) :
    theta (finiteResidueTest w) Z z =
      ∑' m : ι → ℤ, w (fun i => (m i : ZMod N)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          siegelMatrixForm Z.matrix (fun i => (m i : ℝ)) (fun i => (m i : ℝ)) +
          (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (m i : ℂ) * z i) := by
  let e : (ι → ℤ) → (ι → ℚ) := fun m i => (m i : ℚ)
  have he : Function.Injective e := by
    intro a b h
    ext i
    have hi : (a i : ℚ) = (b i : ℚ) := congrFun h i
    exact_mod_cast hi
  have hs : Function.support (thetaTerm (finiteResidueTest w) Z z) ⊆ Set.range e := by
    intro x hx
    have hxw : (finiteResidueTest w).val (finiteDiagonal x) ≠ 0 := by
      intro h
      exact hx (by simp [thetaTerm, h])
    obtain ⟨m, hm⟩ := finiteResidueTest_rational_support w x hxw
    exact ⟨m, funext hm⟩
  rw [theta, ← he.tsum_eq hs]
  apply tsum_congr
  intro m
  have heq : finiteDiagonal (e m) = integerFinite m := by
    ext i
    simp [finiteDiagonal, integerFinite, e]
  simp only [thetaTerm, heq, finiteResidueTest_integer]
  simp [e]

/-- A residue class as its canonical element of `Fin N`. -/
def residueFin {N : ℕ} [NeZero N] (a : ZMod N) : Fin N :=
  ⟨a.val, ZMod.val_lt a⟩

theorem residueFin_intCast {N : ℕ} [NeZero N] (a : ℤ) :
    residueFin (a : ZMod N) = (Int.divModEquiv N a).2 := by
  apply Fin.ext
  have h : (a : ZMod N).val = (a % N).toNat := by
    simpa only [Int.toNat_natCast] using congrArg Int.toNat (ZMod.val_intCast (n := N) a)
  change (a : ZMod N).val = (Fin.ofNat N (a.natMod N)).val
  rw [Fin.val_ofNat]
  change (a : ZMod N).val = (a % N).toNat % N
  rw [← h, Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- The actual two-coordinate periodic weight in the finite test model. -/
def eisensteinFiniteWeight {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (r : Fin 2 → ZMod N) : ℂ :=
  w (residueFin (r 0), residueFin (r 1))

theorem eisensteinFiniteWeight_integer {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) :
    eisensteinFiniteWeight w (fun i => ((![(n.1), n.2] : Fin 2 → ℤ) i : ZMod N)) =
      HeckeTheta.periodicCoeff w n := by
  simp only [eisensteinFiniteWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, residueFin_intCast]
  rfl

/-- The compact, locally constant finite test attached to a periodic Eisenstein weight. -/
def eisensteinFiniteTest {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    finiteSchwartz (Fin 2) := finiteResidueTest (eisensteinFiniteWeight w)

/-- The finite-adelic sum agrees term for term with the weighted Eisenstein lattice sum. -/
theorem theta_eisensteinFiniteTest {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (τ : ℍ) :
    theta (eisensteinFiniteTest w) (eisensteinSiegel τ) 0 =
      ∑' n : ℤ × ℤ, HeckeTheta.periodicCoeff w n *
        eisensteinComplexGaussian (eisensteinGaussianParameter τ) n := by
  rw [eisensteinFiniteTest, theta_finiteResidueTest_eq_integer]
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq _]
  apply tsum_congr
  intro n
  have hen : (finTwoArrowEquiv ℤ).symm n = ![n.1, n.2] := rfl
  rw [hen]
  change eisensteinFiniteWeight w (fun i => ((![(n.1), n.2] : Fin 2 → ℤ) i : ZMod N)) * _ = _
  rw [eisensteinFiniteWeight_integer, eisensteinSiegel_form]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 1
  unfold eisensteinComplexGaussian eisensteinGaussianParameter
  congr 1
  push_cast
  ring

/-- No theta-series identification is assumed: the actual ideal theta is one sixth
of the constructed finite-adelic theta at its positive Eisenstein Siegel point. -/
theorem theta_eisensteinFiniteTest_eq_six_heckeTheta
    (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) (τ : ℍ) :
    theta (eisensteinFiniteTest (HeckeFamily.coefficients χ)) (eisensteinSiegel τ) 0 =
      6 * heckeTheta χ τ := by
  rw [theta_eisensteinFiniteTest, periodicGaussian_eq_six_heckeTheta χ hχ]

end ArtinMatthews
