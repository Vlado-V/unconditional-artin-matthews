module

public import ArtinMatthews.FixedURootMixedWeights
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
public import Mathlib.Order.CompletePartialOrder
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

/-! A single C² hypothesis supplies the mixed regularity used by the
actual root-weight theorem. The derivative bounds are still explicit. -/

noncomputable section
namespace ArtinMatthews

theorem root_contDiff_partial_second (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (p.1,s)) p.2) := by
  have heq (p : ℝ × ℝ) : deriv (fun s : ℝ => F (p.1,s)) p.2 =
      (fderiv ℝ F p) (0,1) := by
    have h := ((hF.differentiable (by norm_num)) p).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    exact h.deriv
  simp_rw [heq]
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem fixedURootC2_regularities (F : ℝ → ℝ → ℂ) (hF : ContDiff ℝ 2 F.uncurry) :
    Continuous F.uncurry ∧
    (∀ s, Differentiable ℝ (fun t => F t s)) ∧
    (∀ s, Continuous (deriv (fun t => F t s))) ∧
    (∀ t, Differentiable ℝ (F t)) ∧
    Continuous (fun p : ℝ × ℝ => deriv (F p.1) p.2) ∧
    (∀ s, Differentiable ℝ (fun t => deriv (F t) s)) ∧
    (∀ s, Continuous (deriv (fun t => deriv (F t) s))) := by
  have hx (s : ℝ) : ContDiff ℝ 2 (fun t => F t s) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hy (t : ℝ) : ContDiff ℝ 2 (F t) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hd : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (F p.1) p.2) :=
    root_contDiff_partial_second F.uncurry hF
  have hxy (s : ℝ) : ContDiff ℝ 1 (fun t => deriv (F t) s) :=
    hd.comp (contDiff_id.prodMk contDiff_const)
  exact ⟨hF.continuous, fun s => (hx s).differentiable (by norm_num),
    fun s => (hx s).continuous_deriv (by norm_num),
    fun t => (hy t).differentiable (by norm_num), hd.continuous,
    fun s => (hxy s).differentiable (by norm_num),
    fun s => (hxy s).continuous_deriv (by norm_num)⟩

open Filter

/-- Actual normalized root replacement for an arbitrary global C² weight.
In particular it applies to compactly supported C² weights. No separability
or weighted root-distribution assumption remains. -/
theorem fixedURootC2Sum_normalized_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D Cx Cy Cxy : ℝ) (lcR rcR : Bool) (F : ℝ → ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        ContDiff ℝ 2 F.uncurry →
        (∀ t ∈ Set.Icc A B, ‖deriv (fun z => F z C) t‖ ≤ Cx) →
        (∀ s ∈ Set.Icc C D, ‖deriv (F A) s‖ ≤ Cy) →
        (∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
          ‖deriv (fun z => deriv (F z) s) t‖ ≤ Cxy) →
        ‖fixedURootMixedSum g₀ A B α β C D lcR rcR F -
          fixedURootMixedMain S A B α β C D F‖ / (U*V) ≤
          E*x^(-δ/1000)*rootMixedWeightNorm F A B C D Cx Cy Cxy := by
  obtain ⟨E,hE,hroot⟩ := fixedURootMixedSum_normalized_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hroot] with x hx
  intro S g₀ U V A B α β C D Cx Cy Cxy lcR rcR F hU hV hS hSr hUA hAB hB
    hα hαβ hβ hVC hCD hD hF hCx hCy hCxy
  obtain ⟨hc,hFx,hDx,hFy,hDy,hFxy,hDxy⟩ := fixedURootC2_regularities F hF
  exact hx S g₀ U V A B α β C D Cx Cy Cxy lcR rcR F hU hV hS hSr hUA hAB hB
    hα hαβ hβ hVC hCD hD hc hFx hDx hFy hDy hFxy hDxy hCx hCy hCxy

/-- Finite interval masks and finite sums of arbitrary C² weights retain
the actual root count and pay their explicit coefficient/derivative mass. -/
theorem fixedURootC2IntervalSum_normalized_power_saving {δ : ℝ}
    (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β Cx Cy Cxy : ι → ℝ) (lcR rcR : ι → Bool)
        (c : ι → ℂ) (F : ι → ℝ → ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ α i ≤ β i ∧ β i ≤ 1) →
        (∀ i ∈ I, ContDiff ℝ 2 (F i).uncurry) →
        (∀ i ∈ I, ∀ t ∈ Set.Icc A B, ‖deriv (fun z => F i z C) t‖ ≤ Cx i) →
        (∀ i ∈ I, ∀ s ∈ Set.Icc C D, ‖deriv (F i A) s‖ ≤ Cy i) →
        (∀ i ∈ I, ∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
          ‖deriv (fun z => deriv (F i z) s) t‖ ≤ Cxy i) →
        ‖(∑ i ∈ I, c i*fixedURootMixedSum g₀ A B (α i) (β i) C D (lcR i) (rcR i) (F i)) -
          ∑ i ∈ I, c i*fixedURootMixedMain S A B (α i) (β i) C D (F i)‖ / (U*V) ≤
          E*x^(-δ/1000) *
            ∑ i ∈ I, ‖c i‖*rootMixedWeightNorm (F i) A B C D (Cx i) (Cy i) (Cxy i) := by
  obtain ⟨E,hE,hroot⟩ := fixedURootC2Sum_normalized_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hroot, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β Cx Cy Cxy lcR rcR c F hU hV hS hSr hUA hAB hB
    hVC hCD hD hα hF hCx hCy hCxy
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hterm (i : ι) (hi : i ∈ I) := (div_le_iff₀ (mul_pos hUp hVp)).mp
    (hx S g₀ U V A B (α i) (β i) C D (Cx i) (Cy i) (Cxy i) (lcR i) (rcR i) (F i)
      hU hV hS hSr hUA hAB hB (hα i hi).1 (hα i hi).2.1 (hα i hi).2.2
      hVC hCD hD (hF i hi) (hCx i hi) (hCy i hi) (hCxy i hi))
  apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ I, ‖c i*(fixedURootMixedSum g₀ A B (α i) (β i) C D (lcR i) (rcR i) (F i) -
        fixedURootMixedMain S A B (α i) (β i) C D (F i))‖ := by
      simp_rw [← mul_sub]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ I, ‖c i‖*((E*x^(-δ/1000)*
        rootMixedWeightNorm (F i) A B C D (Cx i) (Cy i) (Cxy i))*(U*V)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hterm i hi) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ArtinMatthews
