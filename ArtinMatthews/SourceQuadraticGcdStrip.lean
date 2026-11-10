module

public import ArtinMatthews.SourceQuadraticShortColumns
public import ArtinMatthews.SourceQuadraticCommonIdeal
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Exact removal of the shared divisor inside a B3 block. Its
shared-prime zero mask remains on the row, and the residual columns
are constrained by actual disjoint prime supports. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadratic_inf_eq_iff_quotient_disjoint (a b g : E) :
    a ⊓ b = g ↔ g ≤ a ∧ g ≤ b ∧ Disjoint (a - g).support (b - g).support := by
  constructor
  · rintro rfl
    exact ⟨inf_le_left, inf_le_right, sourceQuadraticExteriorInf_sub_disjoint F S₀ a b⟩
  · rintro ⟨hga, hgb, hdis⟩
    ext P
    have hzero : (a - g) P = 0 ∨ (b - g) P = 0 := by
      by_contra! hn
      exact Finset.disjoint_left.mp hdis (Finsupp.mem_support_iff.mpr hn.1)
        (Finsupp.mem_support_iff.mpr hn.2)
    simp only [Finsupp.tsub_apply] at hzero
    change min (a P) (b P) = g P
    have ha := hga P
    have hb := hgb P
    omega

theorem sourceQuadratic_common_pairs_eq_divisible (cols : Finset E) (g : E) :
    (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g) =
      (sourceQuadraticDivisibleColumns F S₀ cols g ×ˢ
        sourceQuadraticDivisibleColumns F S₀ cols g).filter
        (fun p : E × E => Disjoint (p.1 - g).support (p.2 - g).support) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, sourceQuadratic_mem_divisibleColumns,
    sourceQuadratic_inf_eq_iff_quotient_disjoint]
  tauto

private theorem sourceQuadraticSymbol_factor (d b g : E) (hg : g ≤ b) :
    χ d b = χ d g * χ d (b - g) := by
  rw [← sourceQuadraticSymbol_add_right, add_tsub_cancel_of_le hg]

theorem sourceQuadraticB3Block_eq_coprime_gram (rows cols : Finset E) (w : E → ℝ)
    (hw : ∀ d ∈ rows, 0 ≤ w d) (a : E → ℂ) (g : E) :
    sourceQuadraticB3Block F S₀ hζ rows cols w a g =
      let D := sourceQuadraticDivisibleColumns F S₀ cols g
      let A := sourceQuadraticShortMatrix F S₀ hζ rows cols w g
      ∑ d : rows, ((‖χ d.val g‖ ^ 2 : ℝ) : ℂ) *
        ∑ b : D, ∑ c : D, if Disjoint (b.val - g).support (c.val - g).support then
          star (A d b * a b.val) * (A d c * a c.val) else 0 := by
  let D := sourceQuadraticDivisibleColumns F S₀ cols g
  let A := sourceQuadraticShortMatrix F S₀ hζ rows cols w g
  let Z (d b c : E) : ℂ := if Disjoint (b - g).support (c - g).support then
    sourceQuadraticPairValue F S₀ hζ a d (b, c) else 0
  have hsum (d : E) :
      (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
        sourceQuadraticPairValue F S₀ hζ a d p) =
      ∑ b : D, ∑ c : D, Z d b.val c.val := by
    rw [sourceQuadratic_common_pairs_eq_divisible, Finset.sum_filter, Finset.sum_product]
    change (∑ b ∈ D, ∑ c ∈ D, Z d b c) = ∑ b : D, ∑ c : D, Z d b.val c.val
    rw [← Finset.sum_coe_sort D (fun b => ∑ c ∈ D, Z d b c)]
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.sum_coe_sort D (fun c => Z d b.val c)).symm
  unfold sourceQuadraticB3Block
  simp_rw [hsum]
  rw [← Finset.sum_coe_sort rows (fun d => (w d : ℂ) * ∑ b : D, ∑ c : D, Z d b.val c.val)]
  change _ = ∑ d : rows, ((‖χ d.val g‖ ^ 2 : ℝ) : ℂ) *
      ∑ b : D, ∑ c : D, if Disjoint (b.val - g).support (c.val - g).support then
        star (A d b * a b.val) * (A d c * a c.val) else 0
  apply Finset.sum_congr rfl
  intro d _
  have hχ : ((‖χ d.val g‖ ^ 2 : ℝ) : ℂ) = star (χ d.val g) * χ d.val g := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  have hs : star (Real.sqrt (w d.val) : ℂ) = (Real.sqrt (w d.val) : ℂ) := by
    change (starRingEnd ℂ) (Real.sqrt (w d.val) : ℂ) = _
    exact Complex.conj_ofReal _
  have hscaled (b c : D) :
      star (A d b * a b.val) * (A d c * a c.val) =
        (w d.val : ℂ) *
          (star (χ d.val (b.val - g) * a b.val) * (χ d.val (c.val - g) * a c.val)) := by
    dsimp only [A, sourceQuadraticShortMatrix]
    simp only [star_mul, hs]
    calc
      _ = (Real.sqrt (w d.val) : ℂ) ^ 2 *
          (star (a b.val) * star (χ d.val (b.val - g)) * (χ d.val (c.val - g) * a c.val)) := by ring
      _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (hw d.val d.property)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hdis : Disjoint (b.val - g).support (c.val - g).support
  · have hb := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b.val).mp b.property).2
    have hc := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g c.val).mp c.property).2
    simp only [Z, ite_eq_left hdis]
    rw [hscaled b c, hχ]
    simp only [sourceQuadraticPairValue,
      sourceQuadraticSymbol_factor F S₀ hζ d.val b.val g hb,
      sourceQuadraticSymbol_factor F S₀ hζ d.val c.val g hc, star_mul]
    ring
  · simp only [Z, ite_eq_right hdis, mul_zero]

end
end ArtinMatthews.SourceEulerAssembly
