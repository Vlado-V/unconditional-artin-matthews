module

public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinTruncatedPairFlux
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual two upper forcings in each cusp are one compact profile.
The profile is supported in the genuine upper band. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem eisensteinCriticalUpperErrorPair_zero (s : ℂ) {A t : ℝ} (a b : ℂ)
    (ht : A*t<1 ∨ 2<A*t) :
    eisensteinCriticalUpperErrorPair s A a b t=0 := by
  simp only [eisensteinCriticalUpperErrorPair,eisensteinUpperCutoffError_zero s ht,
    eisensteinUpperCutoffError_zero (1-s) ht,mul_zero,add_zero]

theorem eisensteinCriticalUpperErrorPair_support (s : ℂ) {A : ℝ} (hA : 0<A) (a b : ℂ) :
    tsupport (eisensteinCriticalUpperErrorPair s A a b)⊆Icc (1/A) (2/A) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have ho : t<1/A ∨ 2/A<t := by simpa only [mem_Icc,not_and_or,not_le] using hn
  apply ht
  apply eisensteinCriticalUpperErrorPair_zero s a b
  simpa only [mul_comm A t] using ho.imp (lt_div_iff₀ hA).mp (div_lt_iff₀ hA).mp

theorem eisensteinCriticalUpperErrorPair_compact (s : ℂ) {A : ℝ} (hA : 0<A) (a b : ℂ) :
    HasCompactSupport (eisensteinCriticalUpperErrorPair s A a b) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinCriticalUpperErrorPair_support s hA a b)

theorem eisensteinCriticalUpperErrorPair_positive (s : ℂ) {A : ℝ} (hA : 0<A) (a b : ℂ) :
    tsupport (eisensteinCriticalUpperErrorPair s A a b)⊆Ioi (0:ℝ) :=
  fun _ ht => (one_div_pos.mpr hA).trans_le (eisensteinCriticalUpperErrorPair_support s hA a b ht).1

theorem gamma0CuspHeightProfileMass_linearCombination (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f⊆Ioi (0:ℝ)) (hgp : tsupport g⊆Ioi (0:ℝ))
    (a b : ℂ) (hfg : ContDiff ℝ ∞ (fun t => a*f t+b*g t))
    (hfgc : HasCompactSupport (fun t => a*f t+b*g t))
    (hfgp : tsupport (fun t => a*f t+b*g t)⊆Ioi (0:ℝ)) :
    gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r (fun t => a*f t+b*g t) hfg hfgc hfgp)=
      a • gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r f hf hfc hfp)+
      b • gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r g hg hgc hgp) := by
  let ψ := cuspHeightProfileSeed N r (fun t => a*f t+b*g t) hfg hfgc hfgp
  let φ := cuspHeightProfileSeed N r f hf hfc hfp
  let ξ := cuspHeightProfileSeed N r g hg hgc hgp
  have he : ψ=a • φ+b • ξ := by
    apply Subtype.ext
    ext z
    change ψ.val z=a*φ.val z+b*ξ.val z
    simp only [ψ,φ,ξ,cuspHeightProfileSeed_apply]
    ring
  simp only [gamma0CuspHeightProfileEnergy,gamma0EnergyInclusion_test]
  change gamma0SmoothSeedMass N ((1/2:ℂ) • ψ)=a • gamma0SmoothSeedMass N ((1/2:ℂ) • φ)+
    b • gamma0SmoothSeedMass N ((1/2:ℂ) • ξ)
  rw [he,smul_add,smul_comm (1/2:ℂ) a,smul_comm (1/2:ℂ) b,map_add]
  simp only [map_smul]

def gamma0EisensteinCriticalTopPairMass (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (s : ℂ) (a b : ℂ) : Gamma0RegionL2 N :=
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N r (eisensteinCriticalUpperErrorPair s A a b)
    (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
    (eisensteinCriticalUpperErrorPair_positive s hA a b))

theorem gamma0EisensteinCriticalTopPairMass_eq (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (s : ℂ) (a b : ℂ) :
    let A := gamma0EisensteinFluxScale N
    let hA := gamma0EisensteinFluxScale_pos N
    gamma0EisensteinCriticalTopPairMass N r s a b=
      a • gamma0CuspUpperCutoffForcingMass N r s A hA+b • gamma0CuspUpperCutoffForcingMass N r (1-s) A hA := by
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  exact gamma0CuspHeightProfileMass_linearCombination N r _ _
    (eisensteinUpperCutoffError_smooth s A) (eisensteinUpperCutoffError_smooth (1-s) A)
    (eisensteinUpperCutoffError_compact s hA) (eisensteinUpperCutoffError_compact (1-s) hA)
    (eisensteinUpperCutoffError_positive_support s hA) (eisensteinUpperCutoffError_positive_support (1-s) hA) a b
    (eisensteinCriticalUpperErrorPair_smooth s A a b) (eisensteinCriticalUpperErrorPair_compact s hA a b)
    (eisensteinCriticalUpperErrorPair_positive s hA a b)

theorem gamma0EisensteinCriticalTopForcing_sum_pair (N : ℕ) [NeZero N]
    (s : ℂ) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EisensteinCriticalTopForcing N s c=
      ∑ i,gamma0EisensteinCriticalTopPairMass N (gamma0EisensteinCuspClassRepresentative N i) s (c i)
        ((gamma0CuspScatteringMatrix N s).mulVec c i) := by
  simp only [gamma0EisensteinCriticalTopPairMass_eq,gamma0EisensteinCriticalTopForcing,Finset.sum_add_distrib]

end ArtinMatthews
