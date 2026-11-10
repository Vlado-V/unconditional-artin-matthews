module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.Analysis.PDE.Dirichlet.Boundary.Gradient


set_option backward.privateInPublic true
@[expose] public section

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate the two defining-function barriers in an inward direction. -/
theorem inward_barrier_derivatives {u r : E → ℝ} {x v : E} {b B : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → B * r y ≤ u y ∧ u y ≤ b * r y)
    (hinward : fderiv ℝ r x v < 0) :
    B * fderiv ℝ r x v ≤ fderiv ℝ u x v ∧
      fderiv ℝ u x v ≤ b * fderiv ℝ r x v := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hu' : DifferentiableAt ℝ u (x + (0 : ℝ) • v) := by simpa using hu
  have hr' : DifferentiableAt ℝ r (x + (0 : ℝ) • v) := by simpa using hr
  have hDu := hu'.hasFDerivAt.comp_hasDerivAt 0 hline
  have hDr := hr'.hasFDerivAt.comp_hasDerivAt 0 hline
  have htu : Tendsto (fun t : ℝ ↦ u (x + t • v) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ u x v)) := by
    simpa [hux, div_eq_inv_mul] using hDu.tendsto_slope_zero_right
  have htr : Tendsto (fun t : ℝ ↦ r (x + t • v) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ r x v)) := by
    simpa [hrx, div_eq_inv_mul] using hDr.tendsto_slope_zero_right
  have hpoint : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, r (x + t • v) / t < 0 :=
    htr.eventually (eventually_lt_nhds hinward)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      B * (r (x + t • v) / t) ≤ u (x + t • v) / t ∧
      u (x + t • v) / t ≤ b * (r (x + t • v) / t) := by
    filter_upwards [hpoint.eventually hcontrol, hneg, self_mem_nhdsWithin] with t hc hn ht
    have htpos : 0 < t := ht
    have hrneg : r (x + t • v) < 0 := by
      simpa using (div_lt_iff₀ htpos).mp hn
    constructor
    · simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hc hrneg).1 htpos.le
    · simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hc hrneg).2 htpos.le
  exact ⟨le_of_tendsto_of_tendsto (tendsto_const_nhds.mul htr) htu (hle.mono fun _ h ↦ h.1),
    le_of_tendsto_of_tendsto htu (tendsto_const_nhds.mul htr) (hle.mono fun _ h ↦ h.2)⟩

theorem linear_form_factor_of_kernel (f g : E →L[ℝ] ℝ) (hg : g ≠ 0)
    (hker : ∀ v, g v = 0 → f v = 0) : ∃ a : ℝ, f = a • g := by
  have he : ∃ w, g w ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext w
    exact h w
  obtain ⟨w, hw⟩ := he
  refine ⟨f w / g w, ?_⟩
  ext v
  have hz : g (v - (g v / g w) • w) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hw, sub_self]
  have hfz := hker _ hz
  simp only [map_sub, map_smul, smul_eq_mul] at hfz
  change f v = (f w / g w) * g v
  calc
    f v = (g v / g w) * f w := sub_eq_zero.mp hfz
    _ = _ := by ring

theorem linear_form_exists_negative (g : E →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ w, g w < 0 := by
  have he : ∃ w, g w ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext w
    exact h w
  obtain ⟨w, hw⟩ := he
  by_cases hn : g w < 0
  · exact ⟨w, hn⟩
  · refine ⟨-w, ?_⟩
    simp only [map_neg]
    exact neg_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hw))

/-- At a noncharacteristic boundary point the solution gradient is a positive,
data-bounded multiple of the defining-function gradient. -/
theorem boundary_gradient_factor_of_barriers {u r : E → ℝ} {K : Set E}
    {x : E} {b B : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (_ : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K) :
    ∃ a : ℝ, b ≤ a ∧ a ≤ B ∧ fderiv ℝ u x = a • fderiv ℝ r x := by
  have hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → B * r y ≤ u y ∧ u y ≤ b * r y := by
    filter_upwards [hnear] with y hy
    exact fun h ↦ hbarriers y (hy h)
  have habs : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ B * |r y| := by
    filter_upwards [hcontrol] with y hy
    intro hry
    obtain ⟨hl, hu⟩ := hy hry
    have hnonpos : u y ≤ 0 := hu.trans (mul_nonpos_of_nonneg_of_nonpos hb hry.le)
    rw [abs_of_nonpos hnonpos, abs_of_neg hry]
    nlinarith
  have hbound := boundary_derivative_bound hu hr hux hrx hrne habs
  obtain ⟨a, ha⟩ := linear_form_factor_of_kernel (fderiv ℝ u x) (fderiv ℝ r x) hrne
    (fun v hv ↦ by simpa only [hv, abs_zero, mul_zero, abs_nonpos_iff] using hbound v)
  obtain ⟨w, hw⟩ := linear_form_exists_negative (fderiv ℝ r x) hrne
  have hineq := inward_barrier_derivatives hu hr hux hrx hcontrol hw
  simp only [ha, smul_apply, smul_eq_mul] at hineq
  exact ⟨a, (mul_le_mul_right_of_neg hw).mp hineq.2,
    (mul_le_mul_right_of_neg hw).mp hineq.1, ha⟩

end OAI.Analysis.PDE.Dirichlet
