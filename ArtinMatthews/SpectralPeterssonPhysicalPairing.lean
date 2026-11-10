module

public import ArtinMatthews.SpectralPeterssonHilbert
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Absolute integrability and finite linearity of the original
Petersson pairing follow from the actual physical L2 profiles. -/
noncomputable section
open MeasureTheory UpperHalfPlane
open scoped InnerProductSpace ComplexConjugate BigOperators

namespace ArtinMatthews

theorem spectralPeterssonHilbertProfile_inner (k : ℕ) (F G : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    ⟪spectralPeterssonHilbertProfile k F z, spectralPeterssonHilbertProfile k G z⟫_ℂ =
      UpperHalfPlane.petersson (k : ℤ) F G z := by
  let p := z.im^((k : ℝ)/2)
  have hp : p*p = z.im^k := by
    dsimp only [p]
    rw [← Real.rpow_add z.im_pos,show (k : ℝ)/2+(k : ℝ)/2=k by ring,Real.rpow_natCast]
  rw [RCLike.inner_apply]
  unfold spectralPeterssonHilbertProfile UpperHalfPlane.petersson
  simp only [map_mul,Complex.conj_ofReal,zpow_natCast]
  calc
    _ = conj (F z)*G z*((p : ℂ)*(p : ℂ)) := by dsimp only [p]; ring
    _ = _ := by rw [← Complex.ofReal_mul,hp,Complex.ofReal_pow]

theorem gamma0PeterssonPhysical_pair_integrable (N k : ℕ) (F G : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hG : MemLp (spectralPeterssonHilbertProfile k G) 2 (volume.restrict (gamma0InteriorRegion N))) :
    IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ) F G z) (gamma0InteriorRegion N) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (hF.toLp (spectralPeterssonHilbertProfile k F)) (hG.toLp (spectralPeterssonHilbertProfile k G))
  apply h.congr
  filter_upwards [hF.coeFn_toLp,hG.coeFn_toLp] with z hf hg
  rw [hf,hg,spectralPeterssonHilbertProfile_inner]

theorem gamma0PeterssonInner_finset_left {ι : Type*} (N k : ℕ) (t : Finset ι)
    (α : ι → ℂ) (F : ι → UpperHalfPlane → ℂ) (G : UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ t, IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ) (F i) G z)
      (gamma0InteriorRegion N)) :
    gamma0PeterssonInner N k (fun z => ∑ i ∈ t, α i*F i z) G =
      ∑ i ∈ t, conj (α i)*gamma0PeterssonInner N k (F i) G := by
  classical
  have he (z : UpperHalfPlane) :
      UpperHalfPlane.petersson (k : ℤ) (fun z => ∑ i ∈ t, α i*F i z) G z =
        ∑ i ∈ t, conj (α i)*UpperHalfPlane.petersson (k : ℤ) (F i) G z := by
    simp only [UpperHalfPlane.petersson,map_sum,map_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold gamma0PeterssonInner
  simp_rw [he]
  rw [integral_finsetSum t (fun i hi => (hF i hi).const_mul _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

end ArtinMatthews
