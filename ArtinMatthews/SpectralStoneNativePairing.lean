module

public import ArtinMatthews.SpectralStoneEisensteinSesquilinear
public import ArtinMatthews.SpectralStoneResidualPair
public import ArtinMatthews.SpectralStoneCuspidalAtoms
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! The full compact spectral pairing in the original native mass space.
The cusp basis, positive-frequency Eisenstein integral and actual residual
eigenspace projections carry their exact normalizations. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem spectralHermitianPair_eq_of_diagonal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B D : V → V → ℂ)
    (hBa : ∀ x y z,B x (y+z)=B x y+B x z) (hDa : ∀ x y z,D x (y+z)=D x y+D x z)
    (hBs : ∀ c x y,B x (c • y)=c*B x y) (hDs : ∀ c x y,D x (c • y)=c*D x y)
    (hBc : ∀ x y,(starRingEnd ℂ) (B x y)=B y x) (hDc : ∀ x y,(starRingEnd ℂ) (D x y)=D y x)
    (hd : ∀ x,B x x=D x x) : ∀ x y,B x y=D x y := by
  let F (x y : V) := B x y-D x y
  have ha (x y z : V) : F x (y+z)=F x y+F x z := by
    simp only [F,hBa,hDa]
    ring
  have hs (c : ℂ) (x y : V) : F x (c • y)=c*F x y := by simp only [F,hBs,hDs,mul_sub]
  have hconj (x y : V) : (starRingEnd ℂ) (F x y)=F y x := by simp only [F,map_sub,hBc,hDc]
  have hla (x y z : V) : F (x+y) z=F x z+F y z := by
    rw [← hconj z (x+y),ha,map_add,hconj,hconj]
  have hls (c : ℂ) (x y : V) : F (c • x) y=(starRingEnd ℂ) c*F x y := by
    rw [← hconj y (c • x),hs,map_mul,hconj]
  have hdiag (x : V) : F x x=0 := sub_eq_zero.mpr (hd x)
  intro x y
  have h1 := hdiag (x+y)
  rw [ha,hla,hla,hdiag,hdiag,zero_add,add_zero] at h1
  have h2 := hdiag (x+Complex.I • y)
  rw [ha,hla x (Complex.I • y) x,hla x (Complex.I • y) (Complex.I • y),
    hls Complex.I y x,hs Complex.I x y,hs Complex.I (Complex.I • y) y,
    hls Complex.I y y,hdiag x,hdiag y] at h2
  simp only [mul_zero,zero_add,add_zero,Complex.conj_I] at h2
  have he : (2*Complex.I)*F x y=0 := by linear_combination h2+Complex.I*h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero))

theorem gamma0CompactStoneNoncuspidalPairing (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0NoncuspidalRemainder N (gamma0SmoothSeedMass N ψ))
      (gamma0NoncuspidalRemainder N (gamma0SmoothSeedMass N ξ))=
      gamma0StoneEisensteinPair N ψ ξ+
        gamma0StoneResidualPair N (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N ξ) := by
  let J := gamma0SmoothSeedMass N
  let R := gamma0NoncuspidalRemainder N
  let B (ψ ξ : h2SmoothCompactSeeds) := inner ℂ (R (J ψ)) (R (J ξ))
  let D (ψ ξ : h2SmoothCompactSeeds) := gamma0StoneEisensteinPair N ψ ξ+gamma0StoneResidualPair N (J ψ) (J ξ)
  change B ψ ξ=D ψ ξ
  apply spectralHermitianPair_eq_of_diagonal B D _ _ _ _ _ _ _ ψ ξ
  · intro x y z
    simp only [B,map_add,inner_add_right]
  · intro x y z
    simp only [D,map_add,gamma0StoneEisensteinPair_add_right,gamma0StoneResidualPair_add_right]
    ring
  · intro c x y
    simp only [B,map_smul,inner_smul_right]
  · intro c x y
    simp only [D,map_smul,gamma0StoneEisensteinPair_smul_right,gamma0StoneResidualPair_smul_right,mul_add]
  · intro x y
    exact inner_conj_symm (𝕜:=ℂ) (R (J y)) (R (J x))
  · intro x y
    simp only [D,map_add,gamma0StoneEisensteinPair_conj,gamma0StoneResidualPair_conj]
  · intro x
    let C := ∫ t in Ioi 0,gamma0StoneFrequencyDensity N x t
    let A := ∑' l : Ici (0:ℝ),‖R (gamma0AmbientSpectralAtomVector N (J x) (l:ℝ))‖^2
    have h : ‖R (J x)‖^2=C+A := gamma0CompactStoneNoncuspidalPlancherel N x
    calc
      B x x = ((‖R (J x)‖^2:ℝ):ℂ) := by
        rw [Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (R (J x))
      _ = ((C+A:ℝ):ℂ) := congrArg Complex.ofReal h
      _ = D x x := by
        change ((C+A:ℝ):ℂ)=gamma0StoneEisensteinPair N x x+gamma0StoneResidualPair N (J x) (J x)
        rw [gamma0StoneEisensteinPair_diagonal,gamma0StoneResidualPair_diagonal,Complex.ofReal_add]

theorem gamma0CompactStoneNativePairing (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N ξ)=
      (∑' i : Gamma0AllHeightSpectralIndex N,
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0SmoothSeedMass N ξ))+
      (gamma0StoneEisensteinPair N ψ ξ+
        gamma0StoneResidualPair N (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N ξ)) := by
  rw [gamma0_mass_spectral_split N,gamma0CompactStoneNoncuspidalPairing N ψ ξ]

end ArtinMatthews
