module

public import ArtinMatthews.SourceHyperbolicH1Gradient
public import ArtinMatthews.L2FiniteChartCompactness
public import ArtinMatthews.SourceHyperbolicRellichEuclideanBounds
public import ArtinMatthews.SourceHyperbolicRellichWeights
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
public import OAI.MathematicalPhysics.BFSS.RellichCompactness


set_option backward.privateInPublic true
@[expose] public section

/-! Local compactness in the native weighted hyperbolic mass space. -/
namespace ArtinMatthews
open MeasureTheory Set Filter SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators ENNReal NNReal Classical
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Nonempty ι]

theorem sourceHyperbolicLocalRellich (f : κ → h1Tests ι 2) (S : Set (ProductSpace ι))
    (hS : IsCompact S) (hSu : S ⊆ productUpper ι)
    (hsupp : ∀ k, tsupport (f k).val ⊆ S) (A B : ℝ)
    (hA : ∀ k, ‖h1TestMass (f k)‖^2 ≤ A) (hB : ∀ k, ‖h1TestGradient (f k)‖^2 ≤ B) :
    IsCompact (closure (range (fun k => h1TestMass (f k)))) := by
  obtain ⟨a,ha,hheight⟩ := sourceHyperbolicRellich_height_lower hS hSu
  obtain ⟨d,C,hd,hC,hlo,hhi⟩ := sourceHyperbolicRellich_density_bounds hS hSu
  let e := sourceHyperbolicFlatten ι
  let S' : Set (HyperbolicFlatSpace ι) := e '' S
  have hS' : IsCompact S' := hS.image e.continuous
  let : CompactSpace S' := isCompact_iff_compactSpace.mp hS'
  let F : κ → HyperbolicFlatSpace ι → ℂ := fun k => sourceHyperbolicFlatTest (f k)
  have hF (k : κ) : ContDiff ℝ 1 (F k) := sourceHyperbolicFlatTest_contDiff (f k)
  have hFs (k : κ) : tsupport (F k) ⊆ S' := sourceHyperbolicFlatTest_support (f k) hS (hsupp k)
  have hFc (k : κ) : HasCompactSupport (F k) :=
    sourceHyperbolicFlatTest_hasCompactSupport (f k) hS (hsupp k)
  let A₀ : ℝ := max A 0 / d
  let B₀ : ℝ := (Fintype.card (ι × Fin 3) : ℝ) * (max B 0 / (a^2*d))
  have hA₀ : 0 ≤ A₀ := div_nonneg (le_max_right _ _) hd.le
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  let R : ℝ≥0 := ⟨Real.sqrt B₀, Real.sqrt_nonneg _⟩
  let L : ℝ≥0 := ⟨volume.real S' + A₀, by positivity⟩
  have hGrad (k : κ) : (∫ x, ‖fderiv ℝ (F k) x‖^2) ≤ (R : ℝ)^2 := by
    change _ ≤ (Real.sqrt B₀)^2
    rw [Real.sq_sqrt hB₀]
    exact (sourceHyperbolicFlatTest_fderiv_le (f k) hS (hsupp k) ha hd hheight hlo).trans
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right ((hB k).trans (le_max_left _ _))
          (mul_nonneg (sq_nonneg a) hd.le)) (Nat.cast_nonneg _))
  have hL1 (k : κ) : (∫ x, ‖F k x‖) ≤ (L : ℝ) := by
    have hm : (∫ x, ‖F k x‖^2) ≤ A₀ :=
      (sourceHyperbolicFlatTest_mass_le (f k) hS (hsupp k) hd hlo).trans
        (div_le_div_of_nonneg_right ((hA k).trans (le_max_left _ _)) hd.le)
    exact (OAI.BFSSRellich.integral_norm_le_volume_add_square (hF k).continuous
      (hFc k) hS' ((subset_tsupport _).trans (hFs k))).trans (add_le_add le_rfl hm)
  let G := fun k => OAI.BFSSRellich.localLp (K := S') (F k) (hF k).continuous
  have hG : TotallyBounded (range G) := OAI.BFSSRellich.localRellich (K := S') F hF hFc R L hGrad hL1
  have hdist (k l : κ) : dist (h1TestMass (f k)) (h1TestMass (f l)) ≤
      Real.sqrt C * dist (G k) (G l) := by
    have hSub : tsupport (f k-f l).val ⊆ S :=
      (tsupport_sub (f k).val (f l).val).trans (union_subset (hsupp k) (hsupp l))
    have hW : dist (h1TestMass (f k)) (h1TestMass (f l))^2 ≤
        C * ∫ p in S, ‖(f k).val p-(f l).val p‖^2 := by
      have he := (h1TestMassLinear ι 2).map_sub (f k) (f l)
      change h1TestMass (f k-f l) = h1TestMass (f k)-h1TestMass (f l) at he
      rw [dist_eq_norm, ← he]
      exact sourceHyperbolicRellich_weighted_mass_bound (f k-f l) hS hSub hC hhi
    have hD : dist (G k) (G l)^2 = ∫ p in S, ‖(f k).val p-(f l).val p‖^2 := by
      change dist (OAI.BFSSRellich.localLp (K := S') (F k) (hF k).continuous)
        (OAI.BFSSRellich.localLp (K := S') (F l) (hF l).continuous)^2 = _
      rw [OAI.BFSSRellich.localLp_dist_square]
      have h := (sourceHyperbolicFlatten_measurePreserving (ι := ι)).setIntegral_image_emb
        e.toHomeomorph.measurableEmbedding (fun x => ‖F k x-F l x‖^2) S
      simpa only [S',F,sourceHyperbolicFlatTest,Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply] using h
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp
    rw [mul_pow,Real.sq_sqrt hC,hD]
    exact hW
  have ht := totallyBounded_range_of_dist_le G (fun k => h1TestMass (f k))
    (Real.sqrt C) (Real.sqrt_nonneg C) hG hdist
  exact ht.closure.isCompact_of_isClosed isClosed_closure

end
end ArtinMatthews
