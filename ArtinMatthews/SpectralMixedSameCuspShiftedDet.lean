module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthDoubleCosets
public import ArtinMatthews.SpectralCuspRowDeterminants
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At the exact-divisor cusp 1/s, both diagonal residues have an
opposite integer shift before passing to the ordinary modulus rs*c. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem gamma0MixedSameCusp_correspondence_iff (r s c : ℕ) [NeZero s]
    (M : SL(2, ℤ)) (hM : M 1 0 = ((s*c : ℕ) : ℤ)) :
    M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) ↔
      (r : ℤ) ∣ (c : ℤ)+M 0 0-M 1 1-(s : ℤ)*M 0 1 := by
  let a := gamma0CuspOneOver s
  have he : (a⁻¹*M*a : SL(2,ℤ)) 1 0 =
      (s : ℤ)*((c : ℤ)+M 0 0-M 1 1-(s : ℤ)*M 0 1) := by
    change (Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) ℤ) *
      (M : Matrix (Fin 2) (Fin 2) ℤ) * (a : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
    rw [Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    simp [a,gamma0CuspOneOver,hM]
    ring
  change a⁻¹*M*a ∈ CongruenceSubgroup.Gamma0 (r*s) ↔ _
  rw [CongruenceSubgroup.Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd,
    he,Nat.cast_mul,mul_comm (r : ℤ) (s : ℤ)]
  exact mul_dvd_mul_iff_left (by exact_mod_cast NeZero.ne s : (s : ℤ) ≠ 0)

theorem gamma0MixedSameCusp_correspondence_shifted_det (r s c : ℕ) [NeZero s] [NeZero c]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (M : SL(2, ℤ)) (hM : M 1 0 = ((s*c : ℕ) : ℤ)) :
    M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) ↔
      ((r*(s*c) : ℕ) : ℤ) ∣
        (M 0 0-b*((s*c : ℕ) : ℤ))*(M 1 1+b*((s*c : ℕ) : ℤ))-1 := by
  let A := M 0 0
  let B := M 0 1
  let D := M 1 1
  let q : ℤ := ((s*c : ℕ) : ℤ)
  let k := (c : ℤ)+A-D-(s : ℤ)*B
  let t := B+b*(A-D)-b^2*q
  have hq : q ≠ 0 := by
    change (((s*c : ℕ) : ℤ) ≠ 0)
    exact_mod_cast NeZero.ne (s*c)
  have hq' : q = (s : ℤ)*(c : ℤ) := Nat.cast_mul s c
  have hk : (s : ℤ)*t+k = (r : ℤ)*(a*(A-D+(c : ℤ)*(1-(s : ℤ)*b))) := by
    dsimp only [t,k]
    rw [hq']
    linear_combination -(A-D+(c : ℤ)*(1-(s : ℤ)*b))*hab
  have hkt : (r : ℤ) ∣ k ↔ (r : ℤ) ∣ t := by
    constructor
    · rintro ⟨l,hl⟩
      have hst : (s : ℤ)*t = (r : ℤ)*(a*(A-D+(c : ℤ)*(1-(s : ℤ)*b))-l) := by
        linear_combination hk-hl
      refine ⟨a*t-b*(a*(A-D+(c : ℤ)*(1-(s : ℤ)*b))-l),?_⟩
      linear_combination -t*hab-b*hst
    · rintro ⟨l,hl⟩
      refine ⟨a*(A-D+(c : ℤ)*(1-(s : ℤ)*b))-(s : ℤ)*l,?_⟩
      linear_combination hk-(s : ℤ)*hl
  have hdet : A*D-B*q = 1 := by
    have h := M.prop
    rwa [Matrix.det_fin_two,hM] at h
  have hprod : (A-b*q)*(D+b*q)-1 = q*t := by
    dsimp only [t]
    linear_combination hdet
  rw [gamma0MixedSameCusp_correspondence_iff r s c M hM]
  change (r : ℤ) ∣ k ↔ ((r*(s*c) : ℕ) : ℤ) ∣ (A-b*q)*(D+b*q)-1
  rw [hkt,hprod,Nat.cast_mul,mul_comm (r : ℤ)]
  exact (mul_dvd_mul_iff_left hq).symm

theorem gamma0MixedSameCuspReduced_lower_dvd (r s q : ℕ) [NeZero r] [NeZero s]
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) q) :
    s ∣ q := by
  have h := gamma0MixedCusp_sameCusp_lower_dvd r s R.val R.property.1
  rw [R.property.2.1] at h
  exact_mod_cast h

end ArtinMatthews
