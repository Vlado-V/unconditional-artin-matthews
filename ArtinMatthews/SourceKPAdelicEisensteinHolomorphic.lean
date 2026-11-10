module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicTranslatedHeight
public import ArtinMatthews.SourceKPAdelicEisensteinConvergence
public import ArtinMatthews.SourceKPRationalHeightComplex
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

/-! Normal convergence and holomorphy of the actual Eisenstein family
in its initial right half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCompactEisenstein (s : ℂ) (q : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicEisensteinSum K hζ s (sourceKPAdelicCompactSection K hζ s) q

theorem sourceKPAdelicCompact_openCell_strip_bound (a b : ℝ)
    (ha : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*a+1)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (x : K) (s : ℂ) (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveWeyl K hζ *
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)‖ ≤
        (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) *
          Height.mulHeight₁ x ^ (-(2*a+1)) := by
  have hsr : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 := by linarith [hs.1]
  have hr : 0 ≤ s.re+1/2 := by
    have hn : 0 ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hc : (sourceKPAdelicHeightConstant K hζ g) ^ (s.re+1/2) ≤
      (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) := by
    calc
      _ ≤ (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (s.re+1/2) :=
        Real.rpow_le_rpow (sourceKPAdelicHeightConstant_pos K hζ g).le (le_max_right _ _) hr
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith [hs.2])
  have hx : Height.mulHeight₁ x ^ (-(2*s.re+1)) ≤ Height.mulHeight₁ x ^ (-(2*a+1)) :=
    Real.rpow_le_rpow_of_exponent_le (Height.one_le_mulHeight₁ x) (by linarith [hs.1])
  exact (sourceKPAdelicCompact_openCell_bound K hζ hsr q g hp x).trans
    (mul_le_mul hc hx (Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))

theorem sourceKPAdelicCompactEisenstein_holomorphic_strip (a b : ℝ)
    (ha : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*a+1)
    (q : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicCompactEisenstein K hζ s q)
      {s : ℂ | a < s.re ∧ s.re < b} := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  let U : Set ℂ := {s | a < s.re ∧ s.re < b}
  let F : K → ℂ → ℂ := fun x s => sourceKPAdelicCompactScalar K hζ s
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)
  let M : K → ℝ := fun x =>
    (max 1 (sourceKPAdelicHeightConstant K hζ g)) ^ (b+1/2) * Height.mulHeight₁ x ^ (-(2*a+1))
  have hM : Summable M := (sourceKPRationalHeight_rpow_summable K ha).mul_left _
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hF : ∀ x, DifferentiableOn ℂ (F x) U := fun x =>
    (sourceKPAdelicCompactScalar_entire K hζ _).differentiableOn
  have hbound : ∀ x s, s ∈ U → ‖F x s‖ ≤ M x := by
    intro x s hs
    exact sourceKPAdelicCompact_openCell_strip_bound K hζ a b ha q g hg.symm x s ⟨hs.1.le,hs.2.le⟩
  have hsum : DifferentiableOn ℂ (fun s => ∑' x : K, F x s) U :=
    Complex.differentiableOn_tsum_of_summable_norm hM hF hU hbound
  have htotal := (sourceKPAdelicCompactScalar_entire K hζ q).differentiableOn.add hsum
  apply htotal.congr
  intro s hs
  have hsr : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 := by linarith [hs.1]
  exact sourceKPAdelicEisensteinSum_bruhat K hζ s (sourceKPAdelicCompactSection K hζ s) q
    (sourceKPAdelicCompactEisenstein_converges K hζ hsr q)

theorem sourceKPAdelicCompactEisenstein_holomorphic
    (q : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicCompactEisenstein K hζ s q)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  intro s hs
  let B : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  let a : ℝ := (s.re+(B-1)/2)/2
  let b : ℝ := s.re+1
  have ha : B ≤ 2*a+1 := by dsimp only [a]; change B < 2*s.re+1 at hs; linarith
  have has : a < s.re := by dsimp only [a]; change B < 2*s.re+1 at hs; linarith
  have hsb : s.re < b := by dsimp only [b]; linarith
  have hU : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  exact ((sourceKPAdelicCompactEisenstein_holomorphic_strip K hζ a b ha q).differentiableAt
    (hU.mem_nhds ⟨has,hsb⟩)).differentiableWithinAt

end
end ArtinMatthews
