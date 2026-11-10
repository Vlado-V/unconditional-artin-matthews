module

public import ArtinMatthews.SourceKPAdelicHeightProductChart
public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicProductSection
public import ArtinMatthews.SourceKPAdelicCutoffLocalFinite
public import ArtinMatthews.SourceKPAdelicProductChartTopology
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

/-! Smoothness of the literal cutoff series in the full product upper
chart follows from its actual locally finite rational support. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein Filter SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators ContDiff Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCutoffSummandProductChart (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (p : InfinitePlace K → EuclideanSpatial) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicRationalSummand K hζ
    (sourceKPAdelicCutoffSeed K hζ T s)
    (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) c else 0

def sourceKPAdelicCutoffEisensteinProductChart (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicCutoffEisenstein K hζ T s
    (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) else 0

theorem sourceKPAdelicCutoffEisensteinProductChart_apply (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p =
      sourceKPAdelicCutoffEisenstein K hζ T s
        (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) := by
  rw [sourceKPAdelicCutoffEisensteinProductChart,dite_eq_left hp]

theorem sourceKPAdelicCutoffSummandProductChart_mk (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (γ : PGL(2,K)) :
    sourceKPAdelicCutoffSummandProductChart K hζ T s q (sourceKPRationalBorelCosetMk K γ) =
      fun p => (sourceKPAdelicHeightCutoff T
        (sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p):ℂ)*
          sourceKPAdelicProductSection K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p := by
  funext p
  by_cases hp : ∀ v, 0 < p v 2
  · simp only [sourceKPAdelicCutoffSummandProductChart,sourceKPAdelicProductHeight,
      sourceKPAdelicProductSection,dite_eq_left hp]
    let a : SourceKPAdelicProjective K hζ :=
      (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)
    let r := sourceKPAdelicProjectiveRationalLift K hζ γ
    change (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ (r*(q*a))):ℂ)*
      sourceKPAdelicCompactScalar K hζ s (r*(q*a)) =
        (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ ((r*q)*a)):ℂ)*
          sourceKPAdelicCompactScalar K hζ s ((r*q)*a)
    rw [mul_assoc r q a]
  · simp only [sourceKPAdelicCutoffSummandProductChart,sourceKPAdelicProductSection,
      dite_eq_right hp,mul_zero]

theorem sourceKPAdelicCutoffSummandProductChart_contDiffAt (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicCutoffSummandProductChart K hζ T s q c) p := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change ContDiffAt ℝ (∞ : ℕ∞ω)
      (sourceKPAdelicCutoffSummandProductChart K hζ T s q (sourceKPRationalBorelCosetMk K γ)) p
    rw [sourceKPAdelicCutoffSummandProductChart_mk]
    let r := sourceKPAdelicProjectiveRationalLift K hζ γ*q
    have hcut : ContDiffAt ℝ (∞ : ℕ∞ω) (fun x =>
        (sourceKPAdelicHeightCutoff T (sourceKPAdelicProductHeight K hζ r x):ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((sourceKPAdelicHeightCutoff_contDiff T).contDiffAt.comp p
          (sourceKPAdelicProductHeight_contDiffAt K hζ r p hp))
    exact hcut.mul (sourceKPAdelicProductSection_contDiffAt K hζ s r p hp)

theorem sourceKPAdelicCutoffEisensteinProductChart_tsum (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial) :
    sourceKPAdelicCutoffEisensteinProductChart K hζ T s q p =
      ∑' c : SourceKPRationalBorelCoset K, sourceKPAdelicCutoffSummandProductChart K hζ T s q c p := by
  by_cases hp : ∀ v, 0 < p v 2
  · simp only [sourceKPAdelicCutoffEisensteinProductChart,sourceKPAdelicCutoffSummandProductChart,
      dite_eq_left hp]
    rfl
  · simp only [sourceKPAdelicCutoffEisensteinProductChart,sourceKPAdelicCutoffSummandProductChart,
      dite_eq_right hp,tsum_zero]

theorem sourceKPAdelicCutoffSummandProductChart_locally_finite {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ᶠ x : InfinitePlace K → EuclideanSpatial in 𝓝 p, ∀ s c, c ∉ I →
        sourceKPAdelicCutoffSummandProductChart K hζ T s q c x = 0 := by
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  let p₀ : SourceKPProductUpper K := ⟨p,hp⟩
  let G : SourceKPProductUpper K → GL (Fin 2) (InfiniteAdeleRing K) :=
    fun x => g*sourceKPProductUpperSection K hζ x
  have hG : Continuous G := continuous_const.mul (sourceKPProductUpperSection_continuous K hζ)
  obtain ⟨I,hI,hsupp⟩ := sourceKPAdelicCutoffSummand_locally_finite K hζ hT qf (G p₀)
  have hsub : ∀ᶠ x : SourceKPProductUpper K in 𝓝 p₀, ∀ s c, c ∉ I →
      sourceKPAdelicCutoffSummandProductChart K hζ T s (ProjGenLinGroup.mk g,qf) c x.val = 0 := by
    filter_upwards [hG.continuousAt.eventually hsupp] with x hx
    intro s c hc
    rw [sourceKPAdelicCutoffSummandProductChart,dite_eq_left x.property]
    change sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s)
      (ProjGenLinGroup.mk g*ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ x.val x.property),qf*1) c = 0
    rw [mul_one,← map_mul,← sourceKPProductUpperSection_eq K hζ x]
    exact hx s c hc
  let U : Set (InfinitePlace K → EuclideanSpatial) := {x | ∀ v, 0 < x v 2}
  have hu : U ∈ 𝓝 p := sourceKPProductUpper_eventually K p hp
  have hwithin := (eventually_nhds_subtype_iff U p₀ (fun x => ∀ s c, c ∉ I →
    sourceKPAdelicCutoffSummandProductChart K hζ T s (ProjGenLinGroup.mk g,qf) c x = 0)).mp hsub
  change (∀ᶠ x in 𝓝[U] p, ∀ s c, c ∉ I →
    sourceKPAdelicCutoffSummandProductChart K hζ T s (ProjGenLinGroup.mk g,qf) c x = 0) at hwithin
  rw [nhdsWithin_eq_nhds.mpr hu] at hwithin
  exact ⟨I,hI,hwithin⟩

theorem sourceKPAdelicCutoffEisensteinProductChart_contDiffAt {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicCutoffEisensteinProductChart K hζ T s q) p := by
  classical
  obtain ⟨I,hI,hnear⟩ := sourceKPAdelicCutoffSummandProductChart_locally_finite K hζ hT q p hp
  let J := hI.toFinset
  have hsum : ContDiffAt ℝ (∞ : ℕ∞ω) (fun x =>
      ∑ c ∈ J, sourceKPAdelicCutoffSummandProductChart K hζ T s q c x) p :=
    ContDiffAt.sum (fun c _ => sourceKPAdelicCutoffSummandProductChart_contDiffAt K hζ T s q c p hp)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  rw [sourceKPAdelicCutoffEisensteinProductChart_tsum]
  apply tsum_eq_sum
  intro c hc
  exact hx s c (by simpa only [J,Set.Finite.mem_toFinset] using hc)

end
end ArtinMatthews
