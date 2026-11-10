module

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import OAI.RepresentationTheory.Weil.Local.Gaussian
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Haar integration through a finite quotient.  The finite reduction
map is required to be a surjective additive homomorphism; its fiber weights
are derived by Haar translation, not supplied as a counting premise. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory
open OAI.RepresentationTheory.Weil.Local
open scoped Classical BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {A : Type*} [AddCommGroup A] [Fintype A]

theorem compact_finite_average (μ : Measure E) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup E) (hU : IsCompact (U : Set E))
    (r : U →+ A) (hr : Function.Surjective r) (g : A → ℂ)
    (f : E → ℂ) (hf : Continuous f) (hfactor : ∀ x : U, f x = g (r x)) :
    (Fintype.card A : ℂ) * (∫ x in (U : Set E), f x ∂μ) =
      (μ.real (U : Set E) : ℂ) * ∑ z : A, g z := by
  let representative (z : A) : U := Classical.choose (hr z)
  have hrepresentative (z : A) : r (representative z) = z := Classical.choose_spec (hr z)
  let G := ∫ x in (U : Set E), f x ∂μ
  have htranslate (t : U) : (∫ x in (U : Set E), f (x + t.val) ∂μ) = G := by
    let F := (U : Set E).indicator f
    have heq : (U : Set E).indicator (fun x => f (x + t.val)) = fun x => F (x + t.val) := by
      funext x
      have hm : x + t.val ∈ U ↔ x ∈ U := U.add_mem_cancel_right t.property
      by_cases hx : x ∈ U
      · simp [F, hx, hm.mpr hx]
      · have hxt : x + t.val ∉ U := fun h => hx (hm.mp h)
        simp [F, hx, hxt]
    rw [← integral_indicator U.isOpen.measurableSet, heq, integral_add_right_eq_self]
    exact integral_indicator U.isOpen.measurableSet
  have hsum (x : U) : (∑ z : A, f (x.val + (representative z).val)) = ∑ z : A, g z := by
    calc
      _ = ∑ z : A, g (r x + z) := by
        apply Finset.sum_congr rfl
        intro z _
        change f ((x + representative z : U) : E) = _
        rw [hfactor, map_add, hrepresentative]
      _ = _ := Equiv.sum_comp (Equiv.addLeft (r x)) g
  calc
    _ = ∑ z : A, ∫ x in (U : Set E), f (x + (representative z).val) ∂μ := by
      simp only [htranslate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, G]
    _ = ∫ x in (U : Set E), ∑ z : A, f (x + (representative z).val) ∂μ := by
      rw [integral_finsetSum]
      intro z _
      exact (hf.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hU
    _ = ∫ _ in (U : Set E), ∑ z : A, g z ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
      exact hsum ⟨x, hx⟩
    _ = _ := by
      simp only [integral_const, Complex.real_smul, Measure.real, Measure.restrict_apply_univ]

theorem compact_finite_integral (μ : Measure E) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup E) (hU : IsCompact (U : Set E))
    (r : U →+ A) (hr : Function.Surjective r) (g : A → ℂ)
    (f : E → ℂ) (hf : Continuous f) (hfactor : ∀ x : U, f x = g (r x)) :
    (∫ x in (U : Set E), f x ∂μ) =
      ((μ.real (U : Set E) : ℂ) * ∑ z : A, g z) / Fintype.card A := by
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card A : ℂ) ≠ 0)).mpr
  simpa only [mul_comm] using compact_finite_average μ U hU r hr g f hf hfactor

theorem compact_finite_integral_phase (μ : Measure E) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup E) (hU : IsCompact (U : Set E))
    (r : U →+ A) (hr : Function.Surjective r) (g : A → ℂ)
    (f : E → ℂ) (hf : Continuous f) (hfactor : ∀ x : U, f x = g (r x)) :
    FunctionsMetaplectic.Construction.phase (∫ x in (U : Set E), f x ∂μ) =
      FunctionsMetaplectic.Construction.phase (∑ z : A, g z) := by
  have h := congrArg FunctionsMetaplectic.Construction.phase
    (compact_finite_average μ U hU r hr g f hf hfactor)
  rw [← Complex.ofReal_natCast] at h
  rw [Gaussian.Construction.phase_positive_mul (Fintype.card A : ℝ)
    (Nat.cast_pos.mpr Fintype.card_pos),
    Gaussian.Construction.phase_positive_mul (μ.real (U : Set E))
      (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ U hU)] at h
  exact h

end

end ArtinMatthews.QuadraticWeil
