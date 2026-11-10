module

public import ArtinMatthews.SourceHyperbolicH1Tests
public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceHyperbolicC1Green
public import ArtinMatthews.SourceKPCompactTruncatedLocalEquation
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! A compact native test can be split into finitely many genuine smooth
bumps, so a weak equation checked on each support neighborhood gives the
same equation for the original test. -/
namespace ArtinMatthews
open NumberField Filter MeasureTheory Set Topology SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "T" => h1Tests (InfinitePlace K) 2
local notation "μ" => productVolume (InfinitePlace K)

theorem sourceProductGradientPair_test_congr {v w : P → ℂ} (ψ : T)
    {O : Set P} (hO : IsOpen O) (hψ : tsupport ψ.val ⊆ O) (he : Set.EqOn v w O) :
    productGradientPair ψ.val v = productGradientPair ψ.val w := by
  funext p
  by_cases hp : p ∈ tsupport ψ.val
  · have hE : v =ᶠ[𝓝 p] w := by
      filter_upwards [hO.mem_nhds (hψ hp)] with x hx
      exact he hx
    simp only [productGradientPair,productPartial,hE.fderiv_eq (𝕜 := ℝ)]
  · have hz (i : InfinitePlace K) (j : Fin 3) : productPartial ψ.val i j p = 0 := by
      rw [productPartial,fderiv_of_notMem_tsupport ℝ hp]
      rfl
    simp only [productGradientPair,hz,star_zero,zero_mul,Finset.sum_const_zero,mul_zero]

private theorem sourceProductGradientPair_add_test (φ ψ : T) (u : P → ℂ) (p : P) :
    productGradientPair (φ.val+ψ.val) u p =
      productGradientPair φ.val u p+productGradientPair ψ.val u p := by
  have hf := φ.prop.1.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0) p
  have hg := ψ.prop.1.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0) p
  simp only [productGradientPair,productPartial,fderiv_add hf hg,ContinuousLinearMap.add_apply,
    star_add,add_mul,Finset.sum_add_distrib,mul_add]

theorem sourceProductWeakEigen_of_support_neighborhoods (u : P → ℂ) (eigenvalue : ℂ)
    (hu : ∀ p ∈ U, ContDiffAt ℝ 1 u p) (φ : T)
    (hlocal : ∀ p ∈ tsupport φ.val, ∃ O : Set P, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∀ ψ : T, tsupport ψ.val ⊆ O →
        (∫ x, productGradientPair ψ.val u x ∂μ) = eigenvalue*(∫ x, star (ψ.val x)*u x ∂μ)) :
    (∫ x, productGradientPair φ.val u x ∂μ) = eigenvalue*(∫ x, star (φ.val x)*u x ∂μ) := by
  let I := tsupport φ.val
  have hcover (i : I) : ∃ O : Set P, IsOpen O ∧ i.val ∈ O ∧ O ⊆ U ∧
      ∀ ψ : T, tsupport ψ.val ⊆ O →
        (∫ x, productGradientPair ψ.val u x ∂μ) = eigenvalue*(∫ x, star (ψ.val x)*u x ∂μ) :=
    hlocal i.val i.property
  choose O hopen hpoint hupper htest using hcover
  have hr (i : I) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall i.val r ⊆ O i :=
    Metric.nhds_basis_closedBall.mem_iff.mp ((hopen i).mem_nhds (hpoint i))
  choose r hr₀ hsub using hr
  let V (i : I) := Metric.ball i.val (r i/2)
  let β (i : I) : ContDiffBump i.val := ⟨r i/2,r i,div_pos (hr₀ i) (by norm_num),by linarith [hr₀ i]⟩
  have hβ (i : I) (x : P) (hx : x ∈ V i) : β i x = 1 :=
    (β i).one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hβsupport (i : I) : tsupport (β i : P → ℝ) ⊆ O i := by
    rw [(β i).tsupport_eq]
    exact hsub i
  obtain ⟨J,hJ⟩ := φ.prop.2.1.elim_finite_subcover V (fun _ => Metric.isOpen_ball)
    (fun p hp => Set.mem_iUnion.mpr ⟨⟨p,hp⟩,Metric.mem_ball_self (div_pos (hr₀ ⟨p,hp⟩) (by norm_num))⟩)
  have hG (ψ : T) : Integrable (productGradientPair ψ.val u) μ :=
    productGradientPair_integrable_C1 hu ψ.prop.1 ψ.prop.2.1 ψ.prop.2.2
  have hM (ψ : T) : Integrable (fun p => star (ψ.val p)*u p) μ :=
    sourceKPProductTestPair_integrable K ψ (fun p hp => (hu p hp).continuousAt.continuousWithinAt)
  have hglue (F : Finset I) : ∀ ψ : T, tsupport ψ.val ⊆ ⋃ i ∈ F, V i →
      (∫ x, productGradientPair ψ.val u x ∂μ) = eigenvalue*(∫ x, star (ψ.val x)*u x ∂μ) := by
    induction F using Finset.induction_on with
    | empty =>
      intro ψ hψ
      have hz : ψ.val = 0 := by
        funext p
        exact image_eq_zero_of_notMem_tsupport (fun hp => by simpa using hψ hp)
      simp only [hz,Pi.zero_apply,productGradientPair,productPartial,fderiv_zero,
        ContinuousLinearMap.zero_apply,star_zero,zero_mul,Finset.sum_const_zero,mul_zero,integral_zero]
    | @insert i F hi ih =>
      intro ψ hψ
      let B : P → ℂ := fun x => (β i x : ℂ)
      have hB : ContDiff ℝ 2 B := Complex.ofRealCLM.contDiff.comp (β i).contDiff
      have hb : tsupport B ⊆ O i :=
        (tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero (β i : P → ℝ)).trans (hβsupport i)
      let ψ₁ : T := ⟨B*ψ.val,hB.mul ψ.prop.1,ψ.prop.2.1.mul_left,
        (tsupport_mul_subset_left.trans hb).trans (hupper i)⟩
      let ψ₂ : T := ⟨(1-B)*ψ.val,(contDiff_const.sub hB).mul ψ.prop.1,ψ.prop.2.1.mul_left,
        tsupport_mul_subset_right.trans ψ.prop.2.2⟩
      have hψ₂ : tsupport ψ₂.val ⊆ ⋃ j ∈ F, V j := by
        intro x hx
        have hxo : x ∈ tsupport ψ.val := tsupport_mul_subset_right hx
        obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp (hψ hxo)
        rcases Finset.mem_insert.mp hj with hji | hj
        · have hxi : x ∈ V i := by simpa only [hji] using hxj
          exfalso
          apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
          filter_upwards [Metric.isOpen_ball.mem_nhds hxi] with y hy
          change ((1 : ℂ)-((β i y : ℝ) : ℂ))*ψ.val y = 0
          rw [hβ i y hy,Complex.ofReal_one,sub_self,zero_mul]
        · exact Set.mem_iUnion₂.mpr ⟨j,hj,hxj⟩
      have h₁ := htest i ψ₁ (tsupport_mul_subset_left.trans hb)
      have h₂ := ih ψ₂ hψ₂
      have hsum : ψ.val = ψ₁.val+ψ₂.val := by
        funext x
        change ψ.val x = B x*ψ.val x+(1-B x)*ψ.val x
        ring
      have hleft : (∫ x, productGradientPair ψ.val u x ∂μ) =
          (∫ x, productGradientPair ψ₁.val u x ∂μ)+(∫ x, productGradientPair ψ₂.val u x ∂μ) := by
        rw [← integral_add (hG ψ₁) (hG ψ₂)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          conv_lhs => rw [hsum]
          exact sourceProductGradientPair_add_test K ψ₁ ψ₂ u x
      have hright : (∫ x, star (ψ.val x)*u x ∂μ) =
          (∫ x, star (ψ₁.val x)*u x ∂μ)+(∫ x, star (ψ₂.val x)*u x ∂μ) := by
        rw [← integral_add (hM ψ₁) (hM ψ₂)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          conv_lhs => rw [hsum]
          simp only [Pi.add_apply,star_add,add_mul]
      rw [hleft,hright,h₁,h₂,mul_add]
  exact hglue J φ hJ

end
end ArtinMatthews
