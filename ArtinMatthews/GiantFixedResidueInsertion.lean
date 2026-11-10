module

public import ArtinMatthews.GiantMarkedResidual
public import ArtinMatthews.GiantFixedResiduePolynomial
public import ArtinMatthews.GiantFixedResidueResidualBounds
public import ArtinMatthews.GiantMarkedInsertion
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-residue model with a true giant prime inserted. The factor
one is allowed for the ordinary first moment, with its exact reciprocal. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem giantFixedResidue_single_residual (M a : ℕ) (hM : 0<M) (ha : a.Coprime M)
    (P S : Finset ℕ) (hcop : ∀ p∈P,p.Coprime M)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {ell : ℕ} (hell : ell=1 ∨ ell.Prime) (hellP : ell ∉ P)
    (hellM : ell.Coprime M) (hθell : 0 ≤ θ ell ∧ θ ell ≤ 1)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hellmin : ell=1 ∨ y ≤ ell) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r (T*x),
        Φ ((u : ℝ) / x) * ((if ell ∣ u then (1 : ℝ) else 0) *
          markedWeightedResidual P S θ u)) -
        giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t) *
          ((1 / (ell : ℝ)) * markedWeightedModel P S θ)|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / ((ell : ℝ) * (∏ p ∈ S, p : ℕ))) *
        ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  classical
  rcases hell with rfl | hell
  · have hg := giantFixedResidue_weighted_residual_rescaled_quantitative M a hM ha P S hcop hP hS θ hθ
      m R hy hmin hV hmass Φ hx hT hΦ hderiv hΦT hΦ0
    simp only [one_dvd,ite_true,one_mul,Nat.cast_one,div_one]
    apply hg.trans
    have hHar : 0≤(harmonic R:ℝ) := by
      rw [← reciprocal_Icc_eq_harmonic]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    have hI : 0≤∫ t in Set.Ioc 0 T, Φ t := integral_nonneg hΦ0
    gcongr
    exact Nat.le_succ _
  · have hS' : ell ∉ S := fun hs => hellP (hS hs)
    have hyell : y≤(ell:ℝ) := hellmin.resolve_left hell.ne_one
    have hg := giantFixedResidue_weighted_residual_rescaled_quantitative M a hM ha
      (insert ell P) (insert ell S)
      (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hellM) (hcop p))
      (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hell) (hP p))
      (Finset.insert_subset_insert ell hS) θ
      (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hθell) (hθ p)) m R
      hy (fun p hp => (Finset.mem_insert.mp hp).elim (fun h => h ▸ hyell) (hmin p)) hV
      (by simpa only [marked_insert_selected_sdiff P S hellP] using hmass)
      Φ hx hT hΦ hderiv hΦT hΦ0
    simpa only [markedWeightedResidual_insert_selected P S hS θ hellP,
      markedWeightedModel_insert_selected P S hS θ hellP,
      marked_insert_selected_sdiff P S hellP, Finset.card_insert_of_notMem hS',
      Finset.prod_insert hS', Nat.cast_mul] using hg

/-- A genuine finite arithmetic estimate; no distribution error is assumed. -/
theorem giantFixedResidue_window_residual (M a : ℕ) (hM : 0<M) (ha : a.Coprime M)
    (G P S : Finset ℕ) (hcop : ∀ p∈P,p.Coprime M)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    (hG : ∀ ell ∈ G, ell=1 ∨ ell.Prime) (hdis : Disjoint G P)
    (hGM : ∀ ell∈G,ell.Coprime M)
    (hθG : ∀ ell ∈ G, 0 ≤ θ ell ∧ θ ell ≤ 1)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hGmin : ∀ ell ∈ G, ell=1 ∨ y ≤ (ell : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r (T*x),
        Φ ((u : ℝ) / x) * (giantWindowDivisorCount G u * markedWeightedResidual P S θ u)) -
        giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t) *
          ((∑ ell ∈ G, 1 / (ell : ℝ)) * markedWeightedModel P S θ)|) ≤
      ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1))) * G.card +
      (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ ell ∈ G, 1 / (ell : ℝ)) := by
  classical
  have hterm (ell : ℕ) (hell : ell ∈ G) := giantFixedResidue_single_residual M a hM ha
    P S hcop hP hS θ hθ m R (hG ell hell)
    (fun hp => Finset.disjoint_left.mp hdis hell hp) (hGM ell hell) (hθG ell hell)
    hy hmin (hGmin ell hell) hV hmass Φ hx hT hΦ hderiv hΦT hΦ0
  have hfam := marked_family_summed_error_of_bounds (Finset.Icc 1 R)
    (fun r => giantFixedResidueSet M a r (T*x)) G
    (fun u => Φ ((u : ℝ) / x)) (fun _ => (1 : ℝ))
    (fun ell => (1 / (ell : ℝ)) * markedWeightedModel P S θ)
    (fun ell u => (if ell ∣ u then (1 : ℝ) else 0) * markedWeightedResidual P S θ u)
    (fun r => giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t)) (fun ell => (ell : ℝ))
    ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
      (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
        (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)))
    (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
      (1 / (∏ p ∈ S, p : ℕ)) *
      ((((S.card + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
        2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)))
    (by intro ell hell; convert hterm ell hell using 1; ring)
  simpa only [one_mul, abs_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_mul, giantWindowDivisorCount] using hfam

end
end ArtinMatthews
