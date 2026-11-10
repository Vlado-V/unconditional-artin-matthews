module

public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralInfinityPoincareOrbitBound
public import ArtinMatthews.SpectralPoincareUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
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

/-! The actual completed infinity seed norm is bounded by the orbit
overlap times the invariant seed mass, with the exact unfolding factor. -/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped MatrixGroups CompactlySupported BigOperators

namespace ArtinMatthews

theorem gamma0Infinity_compact_seed_orbit_mass_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) {A : ℝ} (hA : 0 < A)
    (hSupp : ∀ z : UpperHalfPlane, ψ.val z ≠ 0 → z.re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ z.im) :
    ‖gamma0SmoothSeedMass N ψ‖^2 ≤
      2*((2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A))))*
        (∫ z : UpperHalfPlane, ‖ψ.val z‖^2) := by
  let C := (2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A)))
  let φ := spectralCompactSeedNormSq ψ.val
  let Q := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let H (f : C_c(UpperHalfPlane, ℂ)) (q : Q) (z : UpperHalfPlane) :=
    gamma0PoincareSeed N f (q.out⁻¹ • z)
  have hLp (f : C_c(UpperHalfPlane, ℂ)) (q : Q) :
      MemLp (H f q) 2 (volume.restrict ModularGroup.fd) :=
    arithmeticPoincareSeed_memLp_modularRegion
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) f
      (SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  have hI (q : Q) : IntegrableOn (H φ q) ModularGroup.fd :=
    memLp_one_iff_integrable.mp ((hLp φ q).mono_exponent (by norm_num))
  have hI₁ (q : Q) : IntegrableOn (fun z => ‖H ψ.val q z‖^2) ModularGroup.fd :=
    (memLp_two_iff_integrable_sq_norm (hLp ψ.val q).aestronglyMeasurable).mp (hLp ψ.val q)
  have hbound (q : Q) :
      (∫ z in ModularGroup.fd, ‖H ψ.val q z‖^2) ≤
        C*(∫ z in ModularGroup.fd, (H φ q z).re) := by
    rw [← integral_const_mul]
    exact integral_mono (hI₁ q) ((hI q).re.const_mul C)
      (fun z => gamma0Infinity_poincare_orbit_normsq_le N ψ.val hA hSupp (q.out⁻¹ • z))
  have hU :
      (∑ q : Q, ∫ z in ModularGroup.fd, H φ q z) =
        2*∫ z : UpperHalfPlane, φ z := by
    have h := gamma0_periodization_unfold_integral N (fun _ => (1 : ℂ))
      continuous_const (fun _ _ => rfl) φ
    simpa only [one_mul] using h
  have hUre :
      (∑ q : Q, ∫ z in ModularGroup.fd, (H φ q z).re) =
        2*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2) := by
    calc
      _ = (∑ q : Q, ∫ z in ModularGroup.fd, H φ q z).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro q _
        exact integral_re (hI q)
      _ = _ := by
        rw [hU]
        simp only [φ,spectralCompactSeedNormSq_apply,integral_complex_ofReal,
          Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,Complex.ofReal_re,zero_mul,sub_zero]
  rw [gamma0SmoothSeedMass_norm_sq]
  change (∑ q : Q, ∫ z in ModularGroup.fd, ‖H ψ.val q z‖^2) ≤
    2*C*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2)
  calc
    _ ≤ ∑ q : Q, C*(∫ z in ModularGroup.fd, (H φ q z).re) :=
      Finset.sum_le_sum (fun q _ => hbound q)
    _ = _ := by rw [← Finset.mul_sum,hUre]; ring

end ArtinMatthews
