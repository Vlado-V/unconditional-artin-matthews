module

public import ArtinMatthews.SourceKPArchTranslatedProduct
public import ArtinMatthews.SourceArchNormalizedRow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! Compactness of unit bottom rows gives a common spatial second derivative
bound for the full translated archimedean product. -/

namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein Filter
open scoped MatrixGroups BigOperators ContDiff Topology
noncomputable section

private theorem norm_iteratedFDeriv_two_rightSlice_le
    {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : R × P → ℂ} {u : R} {p : P}
    (hf : ContDiffAt ℝ 2 f (u, p)) :
    ‖iteratedFDeriv ℝ 2 (fun q => f (u, q)) p‖ ≤ ‖iteratedFDeriv ℝ 2 f (u, p)‖ := by
  let L := LinearIsometry.inr ℝ R P
  let g := fun z : R × P => f ((u, 0) + z)
  have hshift : ContDiffAt ℝ 2 g (L p) := by
    have ht : ContDiffAt ℝ 2 (fun z : R × P => (u, 0) + z) (L p) := by fun_prop
    have hpoint : (u, 0) + L p = (u, p) := by simp [L, LinearIsometry.inr_apply]
    have hft : ContDiffAt ℝ 2 f ((u, 0) + L p) := by simpa only [hpoint] using hf
    exact hft.comp (L p) ht
  obtain ⟨V, hV, hgV⟩ := hshift.contDiffOn le_rfl (by norm_num)
  obtain ⟨U, hUV, hoU, hpU⟩ := mem_nhds_iff.mp hV
  have hoPre : IsOpen (L.toContinuousLinearMap ⁻¹' U) :=
    hoU.preimage L.continuous
  have h := L.toContinuousLinearMap.iteratedFDerivWithin_comp_right (hgV.mono hUV)
    hoU.uniqueDiffOn hoPre.uniqueDiffOn (x := p) hpU (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 2 hoPre (show p ∈ L.toContinuousLinearMap ⁻¹' U from hpU),
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) 2 hoU
      (show L.toContinuousLinearMap p ∈ U from hpU)] at h
  have hg : g ∘ L.toContinuousLinearMap = fun q => f (u, q) := by
    funext q
    simp [g, L, LinearIsometry.inr_apply]
  have htrans : iteratedFDeriv ℝ 2 g (L.toContinuousLinearMap p) =
      iteratedFDeriv ℝ 2 f (u, p) := by
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_left]
    simp [L, LinearIsometry.inr_apply]
  rw [hg, htrans] at h
  rw [h]
  exact (iteratedFDeriv ℝ 2 f (u, p)).norm_compContinuous_linearIsometry_le (fun _ => L)

variable {ι : Type*} [Fintype ι]

private def rowCoordinateProduct (s : ℂ)
    (up : (ι → Fin 2 → ℂ) × (ι → EuclideanSpatial)) : ℂ :=
  ∏ v, sourceArchRowCoordinateProfile s (up.1 v, up.2 v)

private theorem rowCoordinateProduct_ne_zero (s : ℂ)
    (up : (ι → Fin 2 → ℂ) × (ι → EuclideanSpatial)) :
    rowCoordinateProduct s up ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => sourceArchRowCoordinateProfile_ne_zero s _

private theorem rowCoordinateProduct_contDiffAt (s : ℂ)
    (up : (ι → Fin 2 → ℂ) × (ι → EuclideanSpatial))
    (hu : ∀ v, up.1 v ≠ 0) (hp : ∀ v, 0 < up.2 v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (rowCoordinateProduct s) up := by
  unfold rowCoordinateProduct
  apply contDiffAt_prod
  intro v _
  let e := fun z : (ι → Fin 2 → ℂ) × (ι → EuclideanSpatial) => (z.1 v, z.2 v)
  have hev : ContDiffAt ℝ (∞ : ℕ∞ω) e up := by unfold e; fun_prop
  have hlocal : ContDiffAt ℝ (∞ : ℕ∞ω) (sourceArchRowCoordinateProfile s) (e up) :=
    sourceArchRowCoordinateProfile_contDiffAt s _ _ (hu v) (hp v)
  have hcomp : ContDiffAt ℝ (∞ : ℕ∞ω) (sourceArchRowCoordinateProfile s ∘ e) up :=
    hlocal.comp up hev
  exact hcomp

/-- The second spatial derivative is bounded by the absolute value of the
actual translated archimedean product, uniformly over its complex matrices on
each compact set of positive coordinates. -/
theorem sourceArchTranslatedCoordinateProduct_iteratedFDeriv_two_le_of_isCompact
    (s : ℂ) (S : Set (ι → EuclideanSpatial)) (hS : IsCompact S)
    (hpos : ∀ p ∈ S, ∀ v, 0 < p v 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ι → GL (Fin 2) ℂ), ∀ p ∈ S,
      ‖iteratedFDeriv ℝ 2 (sourceArchTranslatedCoordinateProduct s g) p‖ ≤
        C * ‖sourceArchTranslatedCoordinateProduct s g p‖ := by
  let U : Set (ι → Fin 2 → ℂ) := Set.pi Set.univ (fun _ => Metric.sphere 0 1)
  let K := U ×ˢ S
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_sphere _ _).prod hS
  let F := rowCoordinateProduct (ι := ι) s
  have hF (up) (hup : up ∈ K) : ContDiffAt ℝ (∞ : ℕ∞ω) F up := by
    refine rowCoordinateProduct_contDiffAt s up (fun v => ?_) (hpos up.2 hup.2)
    have hv := hup.1 v (Set.mem_univ v)
    rw [Metric.mem_sphere, dist_zero_right] at hv
    intro he
    rw [he, norm_zero] at hv
    exact zero_ne_one hv
  let D := fun up => ‖iteratedFDeriv ℝ 2 F up‖ / ‖F up‖
  have hD : ContinuousOn D K := by
    intro up hup
    exact (((hF up hup).continuousAt_iteratedFDeriv (k := 2) (by simp)).norm.div
      (hF up hup).continuousAt.norm
      (norm_ne_zero_iff.mpr (rowCoordinateProduct_ne_zero s up))).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hD
  let C := max B 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro g p hp
  let u := fun v => sourceArchNormalizedRow (sourceArchTranslatedRow (g v))
  have hu : u ∈ U := by
    intro v _
    rw [Metric.mem_sphere, dist_zero_right]
    exact sourceArchNormalizedRow_norm _ (sourceArchTranslatedRow_ne_zero (g v))
  have hup : (u, p) ∈ K := ⟨hu, hp⟩
  have hDle : D (u, p) ≤ C := (hB ⟨(u, p), hup, rfl⟩).trans (le_max_left _ _)
  have hbound : ‖iteratedFDeriv ℝ 2 F (u, p)‖ ≤ C * ‖F (u, p)‖ :=
    (div_le_iff₀ (norm_pos_iff.mpr (rowCoordinateProduct_ne_zero s (u, p)))).mp hDle
  have hf2 : ContDiffAt ℝ 2 F (u, p) := (hF (u, p) hup).of_le (by simp)
  have hslice : ContDiffAt ℝ 2 (fun q => F (u, q)) p := by
    have hev : ContDiffAt ℝ 2 (fun q : ι → EuclideanSpatial => (u, q)) p := by fun_prop
    exact hf2.comp p hev
  let c := ∏ v, sourceArchTranslatedRowScale s (g v)
  have hnear : ∀ᶠ q : ι → EuclideanSpatial in 𝓝 p, ∀ v, 0 < q v 2 := by
    rw [Filter.eventually_all]
    intro v
    have hy : Continuous (fun q : EuclideanSpatial => q 2) := (EuclideanSpace.proj 2).continuous
    exact (hy.comp (_root_.continuous_apply v)).continuousAt.eventually_const_lt (hpos p hp v)
  have hfactor : sourceArchTranslatedCoordinateProduct s g =ᶠ[𝓝 p]
      fun q => c • F (u, q) := by
    filter_upwards [hnear] with q hq
    change (∏ v, sourceArchTranslatedProfile s (g v) (q v)) =
      (∏ v, sourceArchTranslatedRowScale s (g v)) *
        (∏ v, sourceArchRowCoordinateProfile s (u v, q v))
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => sourceArchTranslatedProfile_eq_normalizedRow s _ _ (hq v)
  rw [(hfactor.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_const_smul_apply' hslice,
    hfactor.eq_of_nhds]
  calc
    _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ 2 (fun q => F (u, q)) p‖ := norm_smul_le _ _
    _ ≤ ‖c‖ * (C * ‖F (u, p)‖) := mul_le_mul_of_nonneg_left
      ((norm_iteratedFDeriv_two_rightSlice_le hf2).trans hbound) (norm_nonneg _)
    _ = C * ‖c • F (u, p)‖ := by rw [smul_eq_mul, norm_mul]; ring

end
end ArtinMatthews.SourceArchJacquet
