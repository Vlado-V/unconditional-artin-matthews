module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceFiber
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeCoefficient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The full signed minor kernel on actual fixed-label edge fibers. The
integer target count is inherited from the proved determinant fibers. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawEdgeCrude_fiber_last_eq {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (I : Finset J) (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1))
    (c d : MarkedDirtyFixedEdgeChoice hZ s I)
    (hc : c ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh)
    (hd : d ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh) :
    markedRawEdgeTargetLast s.2.2 c.1.promotions c.1.fresh=
      markedRawEdgeTargetLast s.2.2 d.1.promotions d.1.fresh := by
  classical
  funext j
  by_cases hj : j ∈ I
  · rw [markedRawEdgeTargetLast_promoted _ _ _ _ _
      (markedDirtyMajorChoiceFiber_promoted hZ s I store indices fresh c hc ⟨j,hj⟩),
      markedRawEdgeTargetLast_promoted _ _ _ _ _
      (markedDirtyMajorChoiceFiber_promoted hZ s I store indices fresh d hd ⟨j,hj⟩)]
  · have hjc : j ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩
    have hcf := congrArg (fun labels => labels.2.2) (Finset.mem_filter.mp hc).2
    have hdf := congrArg (fun labels => labels.2.2) (Finset.mem_filter.mp hd).2
    exact (congrFun hcf ⟨j,hjc⟩).trans (congrFun hdf ⟨j,hjc⟩).symm

theorem markedRawEdgeCrude_fiber_sum_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (r d₀ Y Q ρ H W A : ℝ) (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (hsupp : ∀ t, ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ)
    (hw : markedMinorIntegerDet s.1.1 w=1) (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z, |markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16)
    (I : Finset J) (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1)) :
    (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
      ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖) ≤
      H^2*(33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  classical
  let coeff (c : MarkedDirtyFixedEdgeChoice hZ s I) :=
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1
  let F := markedDirtyMajorChoiceFiber hZ s I store indices fresh
  let S := F.filter (fun c => coeff c ≠ 0)
  have hSF : S ⊆ F := Finset.filter_subset _ _
  have hzero : (∑ c ∈ F, ‖coeff c‖)=∑ c ∈ S, ‖coeff c‖ := by
    symm
    apply Finset.sum_subset hSF
    intro c hc hn
    have hh : coeff c=0 := by
      by_contra hne
      exact hn (Finset.mem_filter.mpr ⟨hc,hne⟩)
    rw [hh,norm_zero]
  change (∑ c ∈ F, ‖coeff c‖) ≤ _
  rw [hzero]
  by_cases hS : S.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hS
    let D : ℤ := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
    let b : ℤ := markedRawLastProduct ((markedRawActiveSplit pads) s.2.1).2
    let a : ℤ := markedRawLastProduct (markedRawEdgeTargetLast s.2.2 c₀.1.promotions c₀.1.fresh)
    let kernel (v : ℤ × ℤ) := markedBanEdgeKernel ψ Q Y b a (markedBanNormalizedDet s.1.1 D v)
    let T := S.image (fun c => c.1.target.1)
    have hlegal : ∀ v ∈ T, D ∣ markedMinorIntegerDet s.1.1 v ∧
        |markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16 := by
      intro v hv
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨markedRawEdgeCrude_coefficient_divides hZ ψ η d₀ Y Q ρ χ s c.1
        (Finset.mem_filter.mp hc).2,hbox _ c.1.target.2⟩
    have hbound (c) (hc : c ∈ S) : ‖coeff c‖ ≤ H^2*‖kernel c.1.target.1‖ := by
      have hh := markedRawEdgeCrude_coefficient_norm_le hZ ψ η d₀ Y Q hρ₀ hρ₁ hH hη χ hχ s c.1
      have he := congrArg markedRawLastProduct
        (markedRawEdgeCrude_fiber_last_eq hZ s I store indices fresh c c₀ (hSF hc) (hSF hc₀))
      rw [he] at hh
      exact hh
    have hinj : Set.InjOn (fun c : MarkedDirtyFixedEdgeChoice hZ s I => c.1.target.1) ↑S :=
      (markedDirtyMajorChoiceFiber_target_injective hZ s I store indices fresh).mono hSF
    have hsum : (∑ c ∈ S, ‖kernel c.1.target.1‖)=∑ v ∈ T, ‖kernel v‖ := by
      symm
      exact Finset.sum_image (fun _ ha _ hb hab => hinj ha hb hab)
    have hk := markedBan_kernel_row_bound r s.1.1 w D b a hw hτ T hlegal ψ hQ hY hA hW hψ hsupp
      (fun _ => 1) (by intros; simp)
    simp only [one_mul] at hk
    calc
      _ ≤ ∑ c ∈ S,H^2*‖kernel c.1.target.1‖ := Finset.sum_le_sum hbound
      _ = H^2*(∑ v ∈ T,‖kernel v‖) := by rw [← Finset.mul_sum,hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

end ArtinMatthews
