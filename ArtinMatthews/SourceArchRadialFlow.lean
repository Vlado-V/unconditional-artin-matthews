module

public import ArtinMatthews.SourceArchDiagonalLog
public import ArtinMatthews.SourceArchGramCoordinates
public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKPAdelicArchHeightPaths
public import ArtinMatthews.SourceKubotaBottomRows
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

/-! Uniform vertical motion as an actual scalar-equivariant matrix flow. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchBottomNorm_left_borel (b g : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchBottomNorm (b*g) = sourceArchBottomNorm g := by
  simp only [sourceArchBottomNorm, sourceGL2_bottom_left_mul,
    sourceGL2_bottom_right_mul, hb.1, hb.2, zero_mul, one_mul, zero_add]

theorem sourceArchGramShift_left_borel (b g : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchGramShift (b*g) = b 0 0 * sourceArchGramShift g + b 0 1 := by
  have hrow : g 1 0 * star (g 1 0) + g 1 1 * star (g 1 1) =
      (sourceArchBottomNorm g : ℂ) := by
    simp only [Complex.star_def, Complex.mul_conj', sourceArchBottomNorm,
      Complex.ofReal_add, Complex.ofReal_pow]
  have h00 : (b*g) 0 0 = b 0 0 * g 0 0 + b 0 1 * g 1 0 := by
    change ((b : Matrix (Fin 2) (Fin 2) ℂ) * g) 0 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (b*g) 0 1 = b 0 0 * g 0 1 + b 0 1 * g 1 1 := by
    change ((b : Matrix (Fin 2) (Fin 2) ℂ) * g) 0 1 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (b*g) 1 0 = g 1 0 := by
    rw [sourceGL2_bottom_left_mul, hb.1, hb.2, zero_mul, one_mul, zero_add]
  have h11 : (b*g) 1 1 = g 1 1 := by
    rw [sourceGL2_bottom_right_mul, hb.1, hb.2, zero_mul, one_mul, zero_add]
  unfold sourceArchGramShift
  rw [sourceArchBottomNorm_left_borel b g hb, h00, h01, h10, h11]
  calc
    _ = (b 0 0 * (g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)) +
        b 0 1 * (g 1 0 * star (g 1 0) + g 1 1 * star (g 1 1))) /
          (sourceArchBottomNorm g : ℂ) := by ring
    _ = _ := by
      rw [hrow]
      field_simp [Complex.ofReal_ne_zero.mpr (sourceArchBottomNorm_pos g).ne']

def sourceArchRadialPoint (t : ℝ) (p : SourceArchUpperHalfSpace) : SourceArchUpperHalfSpace :=
  (p.1, ⟨Real.exp t * p.2.val, mul_pos (Real.exp_pos t) p.2.property⟩)

def sourceArchRadialBorel (t : ℝ) (z : ℂ) : GL (Fin 2) ℂ :=
  sourceKPUpperMatrix ℂ ((1 - (Real.exp t : ℂ)) * z) * sourceArchPositiveDiagonal t

theorem sourceArchRadialBorel_entry (t : ℝ) (z : ℂ) (i j : Fin 2) :
    sourceArchRadialBorel t z i j = !![(Real.exp t : ℂ), (1-(Real.exp t : ℂ))*z; 0, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchRadialBorel, sourceKPUpperMatrix, sourceArchPositiveDiagonal,
      sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceArchRadialBorel_mem (t : ℝ) (z : ℂ) :
    sourceArchRadialBorel t z ∈ sourceGL2NormalizedBorel ℂ := by
  constructor <;> simp [sourceArchRadialBorel_entry]

theorem sourceArchRadialBorel_det_norm (t : ℝ) (z : ℂ) :
    ‖(GeneralLinearGroup.det (sourceArchRadialBorel t z) : ℂ)‖ = Real.exp t := by
  rw [sourceGL2_det_val]
  simp [sourceArchRadialBorel_entry]

def sourceArchRadialFlow (t : ℝ) (g : GL (Fin 2) ℂ) : GL (Fin 2) ℂ :=
  sourceArchRadialBorel t (sourceArchGramShift g) * g

theorem sourceArchRadialFlow_shift (t : ℝ) (g : GL (Fin 2) ℂ) :
    sourceArchGramShift (sourceArchRadialFlow t g) = sourceArchGramShift g := by
  rw [sourceArchRadialFlow, sourceArchGramShift_left_borel _ _ (sourceArchRadialBorel_mem t _)]
  simp [sourceArchRadialBorel_entry]
  ring

theorem sourceArchRadialFlow_height (t : ℝ) (g : GL (Fin 2) ℂ) :
    sourceArchHeight (sourceArchRadialFlow t g) = Real.exp t * sourceArchHeight g := by
  rw [sourceArchRadialFlow, sourceArchHeight_borel _ _ (sourceArchRadialBorel_mem t _),
    sourceArchRadialBorel_det_norm]

theorem sourceArchRadialFlow_coordinates (t : ℝ) (g : GL (Fin 2) ℂ) :
    sourceArchGramCoordinates (sourceArchRadialFlow t g) =
      sourceArchRadialPoint t (sourceArchGramCoordinates g) := by
  apply Prod.ext
  · exact sourceArchRadialFlow_shift t g
  · exact Subtype.ext (sourceArchRadialFlow_height t g)

theorem sourceArchRadialBorel_zero (z : ℂ) : sourceArchRadialBorel 0 z = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sourceArchRadialBorel_entry]

theorem sourceArchRadialBorel_add (s t : ℝ) (z : ℂ) :
    sourceArchRadialBorel s z * sourceArchRadialBorel t z = sourceArchRadialBorel (s+t) z := by
  apply GeneralLinearGroup.ext
  intro i j
  change ((sourceArchRadialBorel s z : Matrix (Fin 2) (Fin 2) ℂ) *
    sourceArchRadialBorel t z) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp [sourceArchRadialBorel_entry, Real.exp_add, Complex.ofReal_mul]
  · simp [sourceArchRadialBorel_entry, Real.exp_add, Complex.ofReal_mul]
    ring
  · simp [sourceArchRadialBorel_entry]
  · simp [sourceArchRadialBorel_entry]

theorem sourceArchRadialFlow_zero (g : GL (Fin 2) ℂ) : sourceArchRadialFlow 0 g = g := by
  rw [sourceArchRadialFlow, sourceArchRadialBorel_zero, one_mul]

theorem sourceArchRadialFlow_add (s t : ℝ) (g : GL (Fin 2) ℂ) :
    sourceArchRadialFlow s (sourceArchRadialFlow t g) = sourceArchRadialFlow (s+t) g := by
  rw [sourceArchRadialFlow, sourceArchRadialFlow_shift, sourceArchRadialFlow,
    ← mul_assoc, sourceArchRadialBorel_add]
  rfl

theorem sourceArchRadialBorel_natural (t : ℝ) (z : ℂ) (b : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchRadialBorel t (b 0 0*z+b 0 1) * b = b * sourceArchRadialBorel t z := by
  apply GeneralLinearGroup.ext
  intro i j
  change ((sourceArchRadialBorel t (b 0 0*z+b 0 1) : Matrix (Fin 2) (Fin 2) ℂ) * b) i j =
    ((b : Matrix (Fin 2) (Fin 2) ℂ) * sourceArchRadialBorel t z) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchRadialBorel_entry, hb.1, hb.2] <;> ring

theorem sourceArchRadialFlow_borel (t : ℝ) (b g : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchRadialFlow t (b*g) = b*sourceArchRadialFlow t g := by
  rw [sourceArchRadialFlow, sourceArchGramShift_left_borel b g hb,
    ← mul_assoc, sourceArchRadialBorel_natural t _ b hb, mul_assoc]
  rfl

theorem sourceArchRadialFlow_scalar (t : ℝ) (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchRadialFlow t (g*GeneralLinearGroup.scalar (Fin 2) u) =
      sourceArchRadialFlow t g * GeneralLinearGroup.scalar (Fin 2) u := by
  simp only [sourceArchRadialFlow, sourceArchGramShift_scalar, mul_assoc]

theorem sourceArchRadialFlow_unitary (t : ℝ) (g : GL (Fin 2) ℂ)
    (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchRadialFlow t (g*sourceArchUnitaryGL k) =
      sourceArchRadialFlow t g * sourceArchUnitaryGL k := by
  simp only [sourceArchRadialFlow, sourceArchGramShift_unitary, mul_assoc]

theorem sourceArchRadialBorel_continuous :
    Continuous (fun p : ℝ × ℂ => sourceArchRadialBorel p.1 p.2) := by
  exact ((sourceKPCutoffUpperMatrix_continuous.comp
    ((continuous_const.sub (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_fst))).mul
      continuous_snd)).mul (sourceKPCutoffPositiveDiagonal_continuous.comp continuous_fst))

theorem sourceArchRadialFlow_continuous :
    Continuous (fun p : ℝ × GL (Fin 2) ℂ => sourceArchRadialFlow p.1 p.2) :=
  (sourceArchRadialBorel_continuous.comp
    (continuous_fst.prodMk (sourceArchGramShift_continuous.comp continuous_snd))).mul continuous_snd

end
end ArtinMatthews.SourceArchJacquet
