module

public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceHyperbolicProductMeasure
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import ArtinMatthews.SourceKPAdelicEisensteinConvergence
public import ArtinMatthews.SourceKPAdelicProductCompactBound
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

/-! Compact tests commute with the actual rational Eisenstein sum in
the full product of hyperbolic coordinates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory Filter OAI.CubicEisenstein
open SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicProductChart_test_integral_tsum {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ)
    {ψ : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ productUpper (InfinitePlace K)) :
    (∫ p, ψ p*sourceKPAdelicEisensteinProductChart K hζ s q p
      ∂productVolume (InfinitePlace K)) =
      ∑' c : SourceKPRationalBorelCoset K,
        ∫ p, ψ p*sourceKPAdelicRationalProductChart K hζ s q c p
          ∂productVolume (InfinitePlace K) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  let : Countable (SourceKPRationalBorelCoset K) :=
    (sourceKPRationalBorelCosetEquiv K).symm.injective.countable
  let C : Set (InfinitePlace K → EuclideanSpatial) := tsupport ψ
  let F := sourceKPAdelicRationalProductChart K hζ s q
  obtain ⟨M,hM,hbound⟩ := sourceKPAdelicRationalProductChart_compact_bound K hζ hs q C hc
    (fun p hp v => productUpper_pos (hsupp hp) v)
  have hFbound (c : SourceKPRationalBorelCoset K) (p : InfinitePlace K → EuclideanSpatial)
      (hp : p ∈ C) : ‖F c p‖ ≤ M c := hbound c p hp
  have hden (p : InfinitePlace K → EuclideanSpatial) (hp : p ∈ C) :
      ContinuousAt (productComplexDensity (ι := InfinitePlace K)) p := by
    change Tendsto (fun x : InfinitePlace K → EuclideanSpatial =>
      ∏ v, ((x v 2 : ℂ)^3)⁻¹) (𝓝 p) (𝓝 (∏ v, ((p v 2 : ℂ)^3)⁻¹))
    apply tendsto_finsetProd
    intro v _
    have hv : Continuous (fun x : InfinitePlace K → EuclideanSpatial => x v 2) :=
      (EuclideanSpace.proj 2).continuous.comp (continuous_apply v)
    exact ((Complex.continuous_ofReal.comp hv).pow 3).continuousAt.inv₀
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (productUpper_pos (hsupp hp) v).ne'))
  let W : (InfinitePlace K → EuclideanSpatial) → ℂ := fun p => ψ p*productComplexDensity p
  let G : SourceKPRationalBorelCoset K → (InfinitePlace K → EuclideanSpatial) → ℂ :=
    fun c p => W p*F c p
  have hW : Integrable W volume := product_compact_mul_integrable hψ hc hden
  have hG (c : SourceKPRationalBorelCoset K) : Integrable (G c) volume := by
    have hi := product_compact_mul_integrable hψ hc
      (F := fun p => productComplexDensity p*F c p) (fun p hp =>
        (hden p hp).mul
          (sourceKPAdelicRationalProductChart_contDiffAt K hζ s q c p
            (fun v => productUpper_pos (hsupp hp) v)).continuousAt)
    convert hi using 1
    funext p
    dsimp only [G,W]
    ring
  have hGbound (c : SourceKPRationalBorelCoset K) (p : InfinitePlace K → EuclideanSpatial) :
      ‖G c p‖ ≤ ‖M c‖*‖W p‖ := by
    by_cases hp : p ∈ C
    · rw [show G c p = W p*F c p from rfl,norm_mul]
      calc
        ‖W p‖*‖F c p‖ ≤ ‖W p‖*M c :=
          mul_le_mul_of_nonneg_left (hFbound c p hp) (norm_nonneg _)
        _ ≤ ‖W p‖*‖M c‖ :=
          mul_le_mul_of_nonneg_left (le_abs_self (M c)) (norm_nonneg _)
        _ = _ := mul_comm _ _
    · have hz : ψ p=0 := image_eq_zero_of_notMem_tsupport hp
      simpa only [G,W,hz,zero_mul,norm_zero,mul_zero] using (le_refl (0 : ℝ))
  have hsumF (p : InfinitePlace K → EuclideanSpatial) : Summable (fun c => F c p) := by
    by_cases hp : ∀ v, 0 < p v 2
    · have h := sourceKPAdelicCompactEisenstein_converges K hζ hs
        (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1))
      change Summable (fun c : SourceKPRationalBorelCoset K =>
        sourceKPAdelicRationalSummand K hζ
          (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
          (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) c) at h
      simpa only [F,sourceKPAdelicRationalProductChart,dite_eq_left hp] using h
    · simp only [F,sourceKPAdelicRationalProductChart,dite_eq_right hp]
      exact summable_zero
  have hlimit (p : InfinitePlace K → EuclideanSpatial) :
      HasSum (fun c => G c p) (W p*sourceKPAdelicEisensteinProductChart K hζ s q p) := by
    have hh := (hsumF p).hasSum.mul_left (W p)
    rw [← sourceKPAdelicEisensteinProductChart_tsum K hζ s q p] at hh
    exact hh
  have hboundInt : Integrable (fun p => ∑' c, ‖M c‖*‖W p‖) volume := by
    have he : (fun p => ∑' c, ‖M c‖*‖W p‖) = fun p => (∑' c, ‖M c‖)*‖W p‖ := by
      funext p
      exact tsum_mul_right
    rw [he]
    exact hW.norm.const_mul _
  have hh := hasSum_integral_of_dominated_convergence (fun c p => ‖M c‖*‖W p‖)
    (fun c => (hG c).aestronglyMeasurable)
    (fun c => Eventually.of_forall (hGbound c))
    (Eventually.of_forall (fun p => hM.norm.mul_right (‖W p‖))) hboundInt
    (Eventually.of_forall hlimit)
  have hdensity (f : (InfinitePlace K → EuclideanSpatial) → ℂ) :
      (∫ p, ψ p*f p ∂productVolume (InfinitePlace K)) = ∫ p, W p*f p := by
    rw [product_density_integral _ (fun p hp => by
      have hz : ψ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
      rw [hz,zero_mul])]
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp only [W]
    ring
  rw [hdensity]
  calc
    _ = ∑' c, ∫ p, G c p := hh.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro c
      exact (hdensity (F c)).symm

end
end ArtinMatthews
