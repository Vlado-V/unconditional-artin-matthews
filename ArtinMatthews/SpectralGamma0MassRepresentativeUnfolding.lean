module

public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
public import ArtinMatthews.SpectralGamma0GlobalPairing
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

/-! Actual full ambient mass pairings unfold against a continuous invariant
representative, with the genuine central multiplicity two. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0Mass_inner_unfold_representative (N : ℕ) [NeZero N]
    (M : Gamma0RegionL2 N) (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hFinv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (g.val • z)=F z)
    (hM : ∀ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      (M q : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd] (fun z => F (q.out⁻¹ • z)))
    (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) M=2*∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (F z) := by
  rw [PiLp.inner_apply]
  calc
    _=∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∫ z in ModularGroup.fd, inner ℂ (gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)) (F (q.out⁻¹ • z)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [gamma0SeedMass_coeFn N ψ.val q,hM q] with z hψ hMz
      change inner ℂ ((gamma0SeedMass N ψ.val q) z) (M q z)=_
      rw [hψ,hMz]
    _=_ := gamma0_periodization_unfold_inner N F hF hFinv ψ.val

end ArtinMatthews
