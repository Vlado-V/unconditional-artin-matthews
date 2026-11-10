module

public import ArtinMatthews.GiantComparisonStripKernel
public import ArtinMatthews.GiantComparisonEndpointMarkMoment
public import ArtinMatthews.GiantComparisonCutoffRows
public import ArtinMatthews.GiantComparisonPositionGeometry
public import ArtinMatthews.GiantComparisonSelectedMarkTest
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

/-! The physical smooth cutoff on one pair of product cells is the
literal additive shift sum with its normalized two endpoint tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {k ell M : ℕ} {P : J → Finset ℕ} {C : J → Finset (Fin k)}

private theorem comparison_shift_sum_single
    (R : Finset ℕ) (w d : ℕ) (u v : ℕ → ℂ) (a : ℂ) :
    (∑ z ∈ R, if z = w+d then conj (u w)*v z*a else 0) =
      if w+d ∈ R then conj (u w)*v (w+d)*a else 0 := by
  classical
  rw [Finset.sum_ite_eq']

theorem giantComparisonPositionKernel_cell_eq
    (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ) (hF : ∀ n, conj (F n) = F n)
    (Ψ ψL ψR : ℝ → ℂ) {a b x W : ℝ} (ha : 0 < a)
    (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hψL : ∀ t, conj (ψL t) = ψL t)
    (hψ : ∀ t ∈ Set.Icc a (25*(b+1)), ψL t = (t:ℂ)⁻¹ ∧ ψR t = 1)
    (hx : 1 ≤ x) (hW : 0 < W) {d N : ℕ} (hd : W ≤ (d:ℝ)) (hd' : (d:ℝ) ≤ 25*W)
    (hN : (25*(b+1)+a/2)*(x*W) ≤ (N:ℝ)) (q : ℝ)
    (s t : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ) :
    let Y := x*W
    let R := giantComparisonCutoffRows Y (a/2) (25*(b+1)+a/2)
    let t_g (j : J) := ell+(C j).card
    let U := giantComparisonWeightedEndpoint P t_g (fun _ => q) (fun l => conj (s l)) ψL F Y
    let V := giantComparisonWeightedEndpoint P t_g (fun _ => q) t ψR (fun n => χ n*G n) Y
    (∑ w ∈ Ioc 0 N, giantComparisonPositionKernel x Ψ χ F G d w *
      sourceComparisonMarkWeight P t_g (fun _ => q) s w *
      sourceComparisonMarkWeight P t_g (fun _ => q) t (w+d)) =
      (Y:ℂ)⁻¹*conj (χ d)*
        ∑ w ∈ R, ∑ z ∈ R, if z = w+d then
          conj (U w)*V z*Ψ ((w:ℝ)/(x*(d:ℝ))) else 0 := by
  intro Y R t_g U V
  have hY : 0 < Y := mul_pos (zero_lt_one.trans_le hx) hW
  have hYc : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hgeom {w : ℕ} (hw : Ψ ((w:ℝ)/(x*(d:ℝ))) ≠ 0) :=
    giantComparisonPositionCell_geometry ha hx hW hd hd' (hsupp hw)
  have hrow {w : ℕ} (hw : 0 < w) (hw' : (w:ℝ)/Y ∈ Set.Icc a (25*(b+1))) : w ∈ R :=
    (mem_giantComparisonCutoffRows hY).mpr
      ⟨hw, (by linarith [hw'.1]), (by linarith [hw'.2])⟩
  have hsub : R ⊆ Ioc 0 N := by
    intro w hw
    obtain ⟨hw₀, hw₁⟩ := (mem_giantComparisonCutoffRows hY).mp hw
    exact mem_Ioc.mpr ⟨hw₀, Nat.cast_le.mp (((div_le_iff₀ hY).mp hw₁.2).trans hN)⟩
  have hsum :
      (∑ w ∈ R, giantComparisonPositionKernel x Ψ χ F G d w *
        sourceComparisonMarkWeight P t_g (fun _ => q) s w *
        sourceComparisonMarkWeight P t_g (fun _ => q) t (w+d)) =
      (∑ w ∈ Ioc 0 N, giantComparisonPositionKernel x Ψ χ F G d w *
        sourceComparisonMarkWeight P t_g (fun _ => q) s w *
        sourceComparisonMarkWeight P t_g (fun _ => q) t (w+d)) := by
    apply sum_subset hsub
    intro w _ hw
    have hzero : Ψ ((w:ℝ)/(x*(d:ℝ))) = 0 := by
      by_contra hn
      exact hw (hrow (hgeom hn).1 (hgeom hn).2.1)
    simp [giantComparisonPositionKernel, hzero]
  rw [← hsum, mul_sum]
  apply sum_congr rfl
  intro w hw
  rw [comparison_shift_sum_single]
  by_cases hcut : Ψ ((w:ℝ)/(x*(d:ℝ))) = 0
  · by_cases ht : w+d ∈ R <;> simp [giantComparisonPositionKernel,hcut,ht]
  have ⟨hw₀, hwl, hwr⟩ := hgeom hcut
  have ht : w+d ∈ R := hrow (Nat.add_pos_left hw₀ d) hwr
  rw [if_pos ht]
  have hstar : (fun l => conj (conj (s l))) = s := by
    funext l
    exact star_star _
  dsimp only [U, V]
  simp only [giantComparisonPositionKernel, giantComparisonWeightedEndpoint, map_mul,
    hψL, hF, sourceComparisonMarkWeight_conj]
  rw [hstar, (hψ _ hwl).1, (hψ _ hwr).2]
  have hinv : (((w:ℝ)/(x*W):ℝ):ℂ)⁻¹ = (Y:ℂ)/(w:ℂ) := by
    change (((w:ℝ)/Y:ℝ):ℂ)⁻¹ = _
    rw [Complex.ofReal_div, Complex.ofReal_natCast, inv_div]
  rw [hinv]
  have hwc : (w:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hw₀.ne'
  field_simp [hYc, hwc]

end
end ArtinMatthews
