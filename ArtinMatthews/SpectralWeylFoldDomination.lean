module

public import ArtinMatthews.SpectralWeylFoldSubstitution
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Local uniform domination of the actual folded compact orbital tests.
The positive lower height supports control the entire remaining endpoint. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralWeylFoldMeasure : Measure (ℝ × ℝ) :=
  spectralKLPhysicalMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))

theorem spectralWeylFoldDensity_joint_measurable (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => spectralWeylFoldDensity s t f g p.1 p.2) := by
  let z : ℝ × (ℝ × ℝ) → ℝ := fun p => spectralWeylFoldHeight (p.1^2/(4*p.2.1)) p.2.2
  have hz : Measurable z := by dsimp [z,spectralWeylFoldHeight]; fun_prop
  have hA : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ((4/(p.1*(1-p.2.2^2))*Real.cos ((s*p.2.1+t*z p)*p.2.2/Real.sqrt (1-p.2.2^2)) : ℝ) : ℂ)) := by
    fun_prop
  exact (hA.mul (hf.comp hz)).mul ((continuous_star.measurable.comp hg).comp (measurable_fst.comp measurable_snd))

theorem spectralWeylFoldDensity_measurable (s t X : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (spectralWeylFoldDensity s t f g X) := by
  have hmap : Measurable (fun q : ℝ × ℝ => (X,q)) := measurable_const.prodMk measurable_id
  have hm := (spectralWeylFoldDensity_joint_measurable s t f g hf hg).comp hmap
  change Measurable (spectralWeylFoldDensity s t f g X) at hm
  exact hm

theorem spectralWeylFoldDensity_compact_bound {a b c d M X x u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hXlo : c ≤ X) (hXhi : X ≤ d)
    (hu : u ∈ Ioo (0 : ℝ) 1) (s t : ℝ) (f g : ℝ → ℂ)
    (hflo : ∀ z ∈ tsupport f, a ≤ z) (hglo : ∀ z ∈ tsupport g, b ≤ z)
    (hM : ∀ z : ℝ, ‖f z‖ ≤ M) :
    ‖spectralWeylFoldDensity s t f g X (x,u)‖ ≤ (d^2/(c*a*b))*M*‖g x‖ := by
  let w : ℝ := 1-u^2
  let z : ℝ := spectralWeylFoldHeight (X^2/(4*x)) u
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  by_cases hg0 : g x = 0
  · simp only [spectralWeylFoldDensity,hg0,star_zero,mul_zero,norm_zero,le_refl]
  by_cases hf0 : f z = 0
  · have he : spectralWeylFoldDensity s t f g X (x,u) = 0 := by
      change ((4/(X*w)*Real.cos ((s*x+t*z)*u/Real.sqrt w) : ℝ) : ℂ)*f z*star (g x) = 0
      rw [hf0,mul_zero,zero_mul]
    rw [he,norm_zero]
    positivity
  have hxlo := hglo x (subset_tsupport g hg0)
  have hx : 0 < x := hb.trans_le hxlo
  have hzlo := hflo z (subset_tsupport f hf0)
  have hX : 0 < X := hc.trans_le hXlo
  have hw : 0 < w := by
    dsimp [w]
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hz : z = X^2*w/(4*x) := by
    dsimp [z,w,spectralWeylFoldHeight]
    ring_nf
  have hAz : a*(4*x) ≤ X^2*w := (le_div_iff₀ (by positivity : 0 < 4*x)).mp (hz ▸ hzlo)
  have hd2 : X^2 ≤ d^2 := (sq_le_sq₀ hX.le (hX.trans_le hXhi).le).mpr hXhi
  have hab : 4*a*b ≤ d^2*w := by
    calc
      _ ≤ a*(4*x) := by nlinarith [mul_le_mul_of_nonneg_left hxlo ha.le]
      _ ≤ X^2*w := hAz
      _ ≤ _ := mul_le_mul_of_nonneg_right hd2 hw.le
  have hcoef : 4/(X*w) ≤ d^2/(c*a*b) := by
    apply (div_le_div_iff₀ (mul_pos hX hw) (by positivity : 0 < c*a*b)).mpr
    calc
      _ = c*(4*a*b) := by ring_nf
      _ ≤ c*(d^2*w) := mul_le_mul_of_nonneg_left hab hc.le
      _ ≤ X*(d^2*w) := mul_le_mul_of_nonneg_right hXlo (by positivity)
      _ = _ := by ring_nf
  let k := Real.cos ((s*x+t*z)*u/Real.sqrt w)
  have hk : ‖((4/(X*w)*k : ℝ) : ℂ)‖ ≤ d^2/(c*a*b) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < 4/(X*w))]
    exact (mul_le_of_le_one_right (by positivity : 0 ≤ 4/(X*w)) (Real.abs_cos_le_one _)).trans hcoef
  change ‖((4/(X*w)*k : ℝ) : ℂ)*f z*star (g x)‖ ≤ _
  rw [norm_mul,norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hk (hM z) (norm_nonneg _) (by positivity)) (norm_nonneg _)

theorem spectralWeylFoldDensity_compact_domination {c d : ℝ} (hc : 0 < c)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ D : ℝ × ℝ → ℝ, Integrable D spectralWeylFoldMeasure ∧ ∀ X ∈ Icc c d,
      ∀ᵐ q ∂spectralWeylFoldMeasure, ‖spectralWeylFoldDensity s t f g X q‖ ≤ D q := by
  obtain ⟨a,ha,hfA⟩ := spectral_compact_positive_lower_bound f hfc hfp
  obtain ⟨b,hb,hgB⟩ := spectral_compact_positive_lower_bound g hgc hgp
  obtain ⟨M,hM⟩ := hfc.exists_bound_of_continuous hf
  let C : ℝ := (d^2/(c*a*b))*M
  have huI : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hD : Integrable (fun q : ℝ × ℝ => C*‖g q.1‖) spectralWeylFoldMeasure := by
    simpa only [spectralWeylFoldMeasure,mul_one] using (((spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul C).mul_prod huI)
  refine ⟨fun q => C*‖g q.1‖,hD,?_⟩
  intro X hX
  have hU : ∀ᵐ q ∂spectralWeylFoldMeasure, q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hU] with q hq
  exact spectralWeylFoldDensity_compact_bound ha hb hc hX.1 hX.2 hq s t f g hfA hgB hM

theorem spectralWeylFoldDensity_compact_integrable {X : ℝ} (hX : 0 < X)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure := by
  obtain ⟨D,hD,hb⟩ := spectralWeylFoldDensity_compact_domination (c := X) (d := X) hX s t f g hf hfc hfp hg hgc hgp
  have hm := spectralWeylFoldDensity_measurable s t X f g hf.measurable hg.measurable
  have hXX : X ∈ Icc X X := ⟨le_rfl,le_rfl⟩
  exact Integrable.mono' (f := spectralWeylFoldDensity s t f g X) (g := D)
    (μ := spectralWeylFoldMeasure) hD hm.aestronglyMeasurable (hb X hXX)

end ArtinMatthews
