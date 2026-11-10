module

public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.SpectralCompactLaplace
public import ArtinMatthews.SpectralABLOppositeLaplace
public import ArtinMatthews.SpectralCompactLaplaceCoshShift
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter MeasureTheory Complex
open scoped ContDiff Topology
noncomputable section

theorem spectralKLPhysicalCompactDiv_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (spectralKLPhysicalCompactDiv f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hi : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ)⁻¹) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx.ne')
    simpa only [spectralKLPhysicalCompactDiv,div_eq_mul_inv] using! hf.contDiffAt.mul hi
  · have hfx : x ∉ tsupport f := fun hx' => hx (hp hx')
    have he : spectralKLPhysicalCompactDiv f =ᶠ[𝓝 x] (0 : ℝ → ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hfx] with y hy
      simp [spectralKLPhysicalCompactDiv,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem spectralKLPhysicalCompactDiv_tsupport (f : ℝ → ℂ) :
    tsupport (spectralKLPhysicalCompactDiv f) ⊆ tsupport f := by
  simpa only [spectralKLPhysicalCompactDiv,div_eq_mul_inv] using!
    (tsupport_mul_subset_left : tsupport (fun x : ℝ => f x*((x : ℂ)⁻¹)) ⊆ tsupport f)

def spectralABLOppositeCosineProfile (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.cos ((x : ℂ)*(Real.sinh u : ℂ))*spectralKLPhysicalCompactDiv f x

theorem spectralCompactLaplace_sinh_pair (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (u : ℝ) :
    spectralCompactLaplace g ((Real.sinh u : ℂ)*I)+
      spectralCompactLaplace g (-((Real.sinh u : ℂ)*I)) =
        2*(∫ x : ℝ, Complex.cos ((x : ℂ)*(Real.sinh u : ℂ))*g x) := by
  unfold spectralCompactLaplace
  rw [← integral_add (spectralCompactLaplace_integrable g hg hc _)
    (spectralCompactLaplace_integrable g hg hc _),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← add_mul,← mul_assoc (2 : ℂ) (Complex.cos ((x : ℂ)*(Real.sinh u : ℂ))) (g x)]
  congr 1
  rw [show -(x : ℂ)*((Real.sinh u : ℂ)*I) = -(((x : ℂ)*(Real.sinh u : ℂ))*I) by ring,
    show -(x : ℂ)*(-((Real.sinh u : ℂ)*I)) = ((x : ℂ)*(Real.sinh u : ℂ))*I by ring,
    Complex.two_cos]
  ring

/-- The literal opposite-sign forward test after the two Schläfli
contour shifts. The compact spatial integral remains inside. -/
theorem spectralABLOppositeTransform_cosine (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (z : ℂ) (hz : |z.im| ≤ 1/2) :
    Integrable (fun u : ℝ => Complex.exp (2*I*z*(u : ℂ))*spectralABLOppositeCosineProfile f u) ∧
    spectralABLOppositeTransform f z = (1/(Real.pi : ℂ))*
      (∫ u : ℝ, Complex.exp (2*I*z*(u : ℂ))*spectralABLOppositeCosineProfile f u) := by
  let g := spectralKLPhysicalCompactDiv f
  let ν := 2*I*z
  let L := ∫ u : ℝ, Complex.exp (ν*(u : ℂ))*spectralCompactLaplace g (Real.cosh u : ℂ)
  let P : ℝ → ℂ := fun u => Complex.exp (ν*(u : ℂ))*spectralCompactLaplace g ((Real.sinh u : ℂ)*I)
  let M : ℝ → ℂ := fun u => Complex.exp (ν*(u : ℂ))*spectralCompactLaplace g (-((Real.sinh u : ℂ)*I))
  let Q : ℝ → ℂ := fun u => Complex.exp (ν*(u : ℂ))*spectralABLOppositeCosineProfile f u
  have hg := spectralKLPhysicalCompactDiv_smooth f hf hp
  have hgc := spectralKLPhysicalCompactDiv_hasCompactSupport f hc
  have hgp : tsupport g ⊆ Ici (0 : ℝ) := (spectralKLPhysicalCompactDiv_tsupport f).trans
    (hp.trans Ioi_subset_Ici_self)
  have hν : |ν.re| ≤ 1 := by
    dsimp [ν]
    norm_num [Complex.mul_re,Complex.mul_im,abs_mul,abs_neg]
    linarith
  have hphase : ν*((Real.pi/2 : ℝ) : ℂ)*I = -((Real.pi : ℂ)*z) := by
    dsimp [ν]
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  have hphase' : (-ν)*((Real.pi/2 : ℝ) : ℂ)*I = (Real.pi : ℂ)*z := by
    rw [neg_mul,neg_mul,hphase,neg_neg]
  obtain ⟨hP,hpos⟩ := spectralCompactLaplace_cosh_shift g hg hgc hgp ν hν
  obtain ⟨hM',hneg⟩ := spectralCompactLaplace_cosh_shift g hg hgc hgp (-ν) (by simpa only [Complex.neg_re,abs_neg])
  have hF : spectralKLCompactOrderTransform f ν = (1/2 : ℂ)*L :=
    (spectralKLCompactOrderTransform_laplace f hf.continuous hc hp ν).2
  have hFneg := (spectralKLCompactOrderTransform_laplace f hf.continuous hc hp (-ν)).2
  rw [spectralKLCompactOrderTransform_even f hp] at hFneg
  have heven : (∫ u : ℝ, Complex.exp ((-ν)*(u : ℂ))*spectralCompactLaplace g (Real.cosh u : ℂ)) = L := by
    apply mul_left_cancel₀ (show (1/2 : ℂ) ≠ 0 by norm_num)
    exact hFneg.symm.trans hF
  have hreflect (u : ℝ) : Complex.exp ((-ν)*(u : ℂ))*spectralCompactLaplace g ((Real.sinh u : ℂ)*I) =
      M (-u) := by
    simp only [M,Complex.ofReal_neg,Real.sinh_neg,neg_mul,mul_neg,neg_neg]
  have hM : Integrable M := by
    exact hM'.comp_neg.congr (ae_of_all _ fun u => by simpa only [neg_neg] using hreflect (-u))
  have hMInt : (∫ u : ℝ, Complex.exp ((-ν)*(u : ℂ))*spectralCompactLaplace g ((Real.sinh u : ℂ)*I)) =
      ∫ u : ℝ, M u := by
    calc
      _ = ∫ u : ℝ, M (-u) := integral_congr_ae (ae_of_all _ hreflect)
      _ = _ := integral_neg_eq_self M volume
  have hLpos : L = Complex.exp (-((Real.pi : ℂ)*z))*(∫ u : ℝ, P u) := by
    simpa only [L,P,hphase] using hpos
  have hLneg : L = Complex.exp ((Real.pi : ℂ)*z)*(∫ u : ℝ, M u) := by
    rw [heven,hphase',hMInt] at hneg
    exact hneg
  have hPInt : (∫ u : ℝ, P u) = Complex.exp ((Real.pi : ℂ)*z)*L := by
    rw [hLpos,← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
  have hMInt' : (∫ u : ℝ, M u) = Complex.exp (-((Real.pi : ℂ)*z))*L := by
    rw [hLneg,← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  have hsum (u : ℝ) : P u+M u = 2*Q u := by
    dsimp only [P,M,Q,spectralABLOppositeCosineProfile]
    rw [← mul_add,spectralCompactLaplace_sinh_pair g hg.continuous hgc]
    dsimp only [g]
    ring
  have hQ : Integrable Q := by
    apply ((hP.add hM).const_mul (1/2 : ℂ)).congr
    filter_upwards with u
    change (1/2 : ℂ)*(P u+M u) = Q u
    rw [hsum]
    ring
  have hQInt : (∫ u : ℝ, Q u) = Complex.cosh ((Real.pi : ℂ)*z)*L := by
    apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
    calc
      _ = (∫ u : ℝ, P u)+(∫ u : ℝ, M u) := by
        rw [← integral_const_mul,← integral_add hP hM]
        exact integral_congr_ae (ae_of_all _ fun u => (hsum u).symm)
      _ = _ := by rw [hPInt,hMInt',Complex.cosh]; ring
  refine ⟨hQ,?_⟩
  change Complex.cosh ((Real.pi : ℂ)*z)*((2/(Real.pi : ℂ))*spectralKLCompactOrderTransform f ν) =
    (1/(Real.pi : ℂ))*(∫ u : ℝ, Q u)
  rw [hF,hQInt]
  ring

end
end ArtinMatthews
