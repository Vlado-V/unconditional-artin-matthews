module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Unitary Inner -/

namespace OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction

noncomputable section

section

/-! The concrete LocalWeil test space embeds in L² with its specified energy. -/

open _root_.MeasureTheory
open scoped ENNReal

variable (F : Type) [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

abbrev referencePositionMeasure (d : ℕ) : Measure (FunctionsMetaplectic.Construction.Position F d) :=
  Measure.pi (fun _ : Fin d => (Measure.addHaar : Measure F))

theorem test_memLp_two (d : ℕ) (f : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    MemLp f.val 2 (referencePositionMeasure F d) :=
  FunctionsMetaplectic.Construction.schwartzBruhat_memLp _ 2 f.property

def testToL2 (d : ℕ) : FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ]
    Lp ℂ 2 (referencePositionMeasure F d) where
  toFun f := (test_memLp_two F d f).toLp f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem testToL2_injective (d : ℕ) : Function.Injective (testToL2 F d) := by
  intro f g h
  apply Subtype.ext
  have hae : f.val =ᵐ[referencePositionMeasure F d] g.val :=
    (MemLp.toLp_eq_toLp_iff (test_memLp_two F d f) (test_memLp_two F d g)).mp h
  exact MeasureTheory.Measure.eq_of_ae_eq hae
    (FunctionsMetaplectic.Construction.schwartzBruhat_continuous f.property) (FunctionsMetaplectic.Construction.schwartzBruhat_continuous g.property)

theorem testToL2_norm (d : ℕ) (f : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ‖testToL2 F d f‖ = Real.sqrt (FunctionsMetaplectic.Construction.l2Energy F d f) := by
  change ‖(test_memLp_two F d f).toLp f.val‖ = _
  rw [Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (test_memLp_two F d f)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div (2 : ℝ), ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rfl

end

/-! Energy-preserving operators preserve the genuine L² inner product. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem inner_eq_of_linear_norm_eq
    {S V : Type} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (L M : S →ₗ[ℂ] V) (h : ∀ f, ‖L f‖ = ‖M f‖) (f g : S) :
    ⟪L f, L g⟫_ℂ = ⟪M f, M g⟫_ℂ := by
  simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, h]

variable (F : Type) [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable (d : ℕ)

theorem testToL2_inner (f g : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪testToL2 F d f, testToL2 F d g⟫_ℂ =
      ∫ x, g.val x * conj (f.val x) ∂ referencePositionMeasure F d := by
  change (∫ x, ⟪(testToL2 F d f) x, (testToL2 F d g) x⟫_ℂ
    ∂ referencePositionMeasure F d) = _
  apply integral_congr_ae
  filter_upwards [(test_memLp_two F d f).coeFn_toLp,
    (test_memLp_two F d g).coeFn_toLp] with x hf hg
  change (testToL2 F d f) x = f.val x at hf
  change (testToL2 F d g) x = g.val x at hg
  rw [hf, hg]
  simp only [RCLike.inner_apply]

theorem energy_preserving_inner
    (A : FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, FunctionsMetaplectic.Construction.l2Energy F d (A f) = FunctionsMetaplectic.Construction.l2Energy F d f)
    (f g : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪testToL2 F d (A f), testToL2 F d (A g)⟫_ℂ =
      ⟪testToL2 F d f, testToL2 F d g⟫_ℂ := by
  apply inner_eq_of_linear_norm_eq ((testToL2 F d).comp A) (testToL2 F d)
  intro h
  change ‖testToL2 F d (A h)‖ = ‖testToL2 F d h‖
  rw [testToL2_norm, testToL2_norm, hA]

end

end OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction
