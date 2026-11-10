module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! # Planar Quadratic Phase -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase.Construction

noncomputable section

/-! The planar quadratic phase satisfies a radial Laplacian identity. -/

def planarQuadraticPhase (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp ((b : ℂ) * Complex.I * ((z.1 : ℂ) ^ 2 - (z.2 : ℂ) ^ 2))

def planarQuadraticPhaseX (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (2 * b * Complex.I * z.1 : ℂ) * planarQuadraticPhase b z

def planarQuadraticPhaseY (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (-2 * b * Complex.I * z.2 : ℂ) * planarQuadraticPhase b z

def planarQuadraticPhaseXX (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((2 * b * Complex.I : ℂ) + (2 * b * Complex.I * z.1 : ℂ) ^ 2) * planarQuadraticPhase b z

def planarQuadraticPhaseYY (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((-2 * b * Complex.I : ℂ) + (-2 * b * Complex.I * z.2 : ℂ) ^ 2) * planarQuadraticPhase b z

theorem planarQuadraticPhase_norm (b : ℝ) (z : ℝ × ℝ) : ‖planarQuadraticPhase b z‖ = 1 := by
  simp [planarQuadraticPhase, Complex.norm_exp, pow_two]

theorem planarQuadraticPhase_continuous (b : ℝ) : Continuous (planarQuadraticPhase b) := by
  unfold planarQuadraticPhase
  fun_prop

theorem planarQuadraticPhase_hasDerivAt_x (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhase b (t, y)) (planarQuadraticPhaseX b (x, y)) x := by
  have hd := (((((hasDerivAt_id x).ofReal_comp).pow 2).sub_const ((y : ℂ) ^ 2)).const_mul
    ((b : ℂ) * Complex.I)).cexp
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseX planarQuadraticPhase
  norm_num
  ring

theorem planarQuadraticPhase_hasDerivAt_y (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhase b (x, t)) (planarQuadraticPhaseY b (x, y)) y := by
  have hd := (((((hasDerivAt_id y).ofReal_comp).pow 2).const_sub ((x : ℂ) ^ 2)).const_mul
    ((b : ℂ) * Complex.I)).cexp
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseY planarQuadraticPhase
  norm_num
  ring

theorem planarQuadraticPhaseX_hasDerivAt_x (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhaseX b (t, y)) (planarQuadraticPhaseXX b (x, y)) x := by
  have hd := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * b * Complex.I : ℂ)).mul
    (planarQuadraticPhase_hasDerivAt_x b x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseXX planarQuadraticPhaseX
  norm_num
  ring

theorem planarQuadraticPhaseY_hasDerivAt_y (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhaseY b (x, t)) (planarQuadraticPhaseYY b (x, y)) y := by
  have hd := (((hasDerivAt_id y).ofReal_comp).const_mul (-2 * b * Complex.I : ℂ)).mul
    (planarQuadraticPhase_hasDerivAt_y b x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseYY planarQuadraticPhaseY
  norm_num
  ring

theorem planarQuadraticPhase_laplacian (b : ℝ) (z : ℝ × ℝ) :
    planarQuadraticPhaseXX b z + planarQuadraticPhaseYY b z =
      (-4 * b ^ 2 * (z.1 ^ 2 + z.2 ^ 2) : ℝ) * planarQuadraticPhase b z := by
  unfold planarQuadraticPhaseXX planarQuadraticPhaseYY
  rw [← add_mul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem planarQuadraticPhase_standard (z : ℂ) :
    planarQuadraticPhase Real.pi (z.re, z.im) = ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) := by
  change Complex.exp _ = Gaussian.Construction.realCharacter 1 ((z ^ 2 / 2).re)
  rw [Gaussian.Construction.realCharacter_apply]
  congr 1
  simp only [Complex.div_ofNat_re, pow_two, Complex.mul_re]
  push_cast
  ring

end

end OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase.Construction
