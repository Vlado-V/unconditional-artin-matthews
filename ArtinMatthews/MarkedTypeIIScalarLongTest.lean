module

public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.MarkedPhysicalScalarCofactor
public import ArtinMatthews.MarkedMajorScalarActual
public import ArtinMatthews.MarkedTypeIIScalarBilinearComparison
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

/-! The source coefficient criterion for the original marked Type II
rectangle. The only cancellation input is the normalized Dirichlet test
of the actual left coefficient on the retained frequency interval. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem markedTypeII_scalar_rectangle_of_long_test
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (δ Kbox Cα Cβ G : ℝ)
    (hδ : 0 < δ) (hKbox : 0 < Kbox) (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hG : 0 ≤ G)
    (hdepth : 100*(5*(2*G+2*(Cα+Cβ)+16)+36)<(Fintype.card J:ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (H U : ℝ), x^δ ≤ H → x^δ ≤ U → H*U ≤ Kbox*x →
      ∀ (S : Finset ℕ) (l r : ℕ) (α β F : ℕ → ℂ),
        (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        (∀ m ∈ S,‖α m‖ ≤ (Real.log x)^Cα) →
        (∀ n ∈ Icc l r,‖β n‖ ≤ (Real.log x)^Cβ) →
        let L := Real.log x
        let a := 2*G+2*(Cα+Cβ)+25
        let W := Real.exp (L^(6/25:ℝ))
        (∀ m ∈ S,α m ≠ 0 → MarkedPhysicalRoughAt W m) →
        (∀ n ∈ Icc l r,β n ≠ 0 → MarkedPhysicalRoughAt W n) →
        (∀ h,‖F h‖ ≤ 1) →
        (∀ j p,p ∈ markedLogPowerBand (e j) x → ∀ h,F (p*h) = F h) →
        (∀ (k : ℕ) [NeZero k],(k:ℝ) ≤ L^a → ∀ χ : DirichletCharacter ℂ k,∀ t : ℝ,
          |t| ≤ 2*(H*U)*L^(a+2) → ‖markedTwistedSum S α χ t‖/H ≤ L^(-R)) →
        ‖∑ m ∈ S,∑ n ∈ Icc l r, α m*β n*F (m*n-1)*
          (literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤ H*U*L^(-G) := by
  have hcard : 0 < (Fintype.card J:ℝ) := lt_trans (by positivity) hdepth
  let : Nonempty J := Fintype.card_pos_iff.mp (by exact_mod_cast hcard)
  let j₀ : J := Classical.choice inferInstance
  let a := 2*G+2*(Cα+Cβ)+25
  let D := 2*G+8
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨R,hR,hmajor⟩ := markedMajorScalar_actual_log_saving j₀ e hinj he δ Kbox a Cα Cβ D
    hδ ha hCα hCβ hD
  refine ⟨R,hR,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hmajor,
    markedTypeII_scalar_rectangle_of_major e hinj he δ Kbox Cα Cβ G hδ hKbox hCα hCβ hG hdepth,
    eventually_gt_atTop (0:ℝ)] with x hm hr hx
  intro H U hH hU hX S l r α β F hS hl hr' hα hβ
  dsimp only
  intro hrα hrβ hF hinv hlong
  have hT (n : ℕ) (hn : n∈Icc l r) : U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U :=
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hr'⟩
  apply hr H U hH hU hX S (Icc l r) α β F hS hT hα hβ hrα hrβ hF hinv
  intro j _
  dsimp only
  have hscale : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hx,mul_comm]
  have hy : 0 < (2:ℝ)^j := pow_pos (by norm_num) _
  have hh := hm ((2:ℝ)^j) H U S l r α β hy (hscale.trans_le hH) (hscale.trans_le hU)
    (by simpa only [Real.exp_log hx] using hX) hS hl hr' hα hβ hrα hrβ hlong
  simpa only [Real.exp_log hx,a,D] using hh

end
end ArtinMatthews
