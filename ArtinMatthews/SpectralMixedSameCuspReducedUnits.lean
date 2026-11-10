module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthDoubleCosets
public import ArtinMatthews.SpectralInfinityReducedUnits
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedSameCuspShiftedDet
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Reduced same-cusp matrices at 1/s are exactly the ordinary units
at the normalized modulus. The two integer residue shifts are kept. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedSameCuspReduced_bounds (r s c : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c)) :
    (0 ≤ R.val 0 0 ∧ R.val 0 0 < ((r*(s*c) : ℕ) : ℤ)) ∧
      (0 ≤ R.val 1 1 ∧ R.val 1 1 < ((r*(s*c) : ℕ) : ℤ)) := by
  obtain ⟨_,_,hA₀,hA,hD₀,hD⟩ := R.property
  have hw : (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℤ)*((s*c : ℕ) : ℤ) =
      ((r*(s*c) : ℕ) : ℤ) := by
    rw [gamma0MixedCusp_trueWidth r s hcop]
    exact (Nat.cast_mul r (s*c)).symm
  exact ⟨⟨hA₀,hA.trans_eq hw⟩,⟨hD₀,hD.trans_eq hw⟩⟩

def gamma0MixedSameCuspReducedUnit (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c)) :
    (ZMod (r*(s*c)))ˣ := by
  let C := r*(s*c)
  let q : ℤ := ((s*c : ℕ) : ℤ)
  let u : ZMod C := ((R.val 1 1+b*q : ℤ) : ZMod C)
  let v : ZMod C := ((R.val 0 0-b*q : ℤ) : ZMod C)
  have h := (gamma0MixedSameCusp_correspondence_shifted_det r s c hab R.val R.property.2.1).mp R.property.1
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ C).mpr h
  have huv : v*u = 1 := by
    apply sub_eq_zero.mp
    dsimp only [v,u]
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_one] using hz
  exact ⟨u,v,by simpa only [mul_comm] using huv,huv⟩

theorem gamma0MixedSameCuspReducedUnit_val (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c)) :
    (gamma0MixedSameCuspReducedUnit r s c hab R : ZMod (r*(s*c))) =
      ((R.val 1 1+b*((s*c : ℕ) : ℤ) : ℤ) : ZMod (r*(s*c))) := rfl

theorem gamma0MixedSameCuspReducedUnit_inv_val (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c)) :
    (((gamma0MixedSameCuspReducedUnit r s c hab R)⁻¹ : (ZMod (r*(s*c)))ˣ) : ZMod (r*(s*c))) =
      ((R.val 0 0-b*((s*c : ℕ) : ℤ) : ℤ) : ZMod (r*(s*c))) := rfl

theorem gamma0MixedSameCuspReducedUnit_bijective (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Function.Bijective (gamma0MixedSameCuspReducedUnit r s c hab) := by
  let C := r*(s*c)
  let q : ℤ := ((s*c : ℕ) : ℤ)
  constructor
  · intro R S h
    have hr := gamma0MixedSameCuspReduced_bounds r s c hcop R
    have hs := gamma0MixedSameCuspReduced_bounds r s c hcop S
    have ha := congrArg (fun u : (ZMod C)ˣ => ((u⁻¹ : (ZMod C)ˣ) : ZMod C)) h
    have hd := congrArg (fun u : (ZMod C)ˣ => (u : ZMod C)) h
    change ((R.val 0 0-b*q : ℤ) : ZMod C) = ((S.val 0 0-b*q : ℤ) : ZMod C) at ha
    change ((R.val 1 1+b*q : ℤ) : ZMod C) = ((S.val 1 1+b*q : ℤ) : ZMod C) at hd
    simp only [Int.cast_sub] at ha
    simp only [Int.cast_add] at hd
    have ha' : (R.val 0 0 : ZMod C) = (S.val 0 0 : ZMod C) := by
      simpa only [sub_add_cancel] using congrArg (fun x : ZMod C => x+(b*q : ℤ)) ha
    apply Subtype.ext
    exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne (s*c)) R.val S.val
      R.property.2.1 S.property.2.1 (spectral_intCast_injective_on_residues hr.1 hs.1 ha')
      (spectral_intCast_injective_on_residues hr.2 hs.2 (add_right_cancel hd))
  · intro u
    let p : ZMod C := ((u⁻¹ : (ZMod C)ˣ) : ZMod C)+(b*q : ℤ)
    let d : ZMod C := (u : ZMod C)-(b*q : ℤ)
    let A : ℤ := p.val
    let D : ℤ := d.val
    have hA : (A : ZMod C) = p := by simp only [A,Int.cast_natCast,ZMod.natCast_zmod_val]
    have hD : (D : ZMod C) = d := by simp only [D,Int.cast_natCast,ZMod.natCast_zmod_val]
    have ha : ((A-b*q : ℤ) : ZMod C) = ((u⁻¹ : (ZMod C)ˣ) : ZMod C) := by
      rw [Int.cast_sub,hA]
      exact add_sub_cancel_right _ _
    have hd : ((D+b*q : ℤ) : ZMod C) = (u : ZMod C) := by
      rw [Int.cast_add,hD]
      exact sub_add_cancel _ _
    have hC : (C : ℤ) ∣ (A-b*q)*(D+b*q)-1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ C).mp
      rw [Int.cast_sub,Int.cast_mul,ha,hd,Units.inv_mul,Int.cast_one,sub_self]
    have hq : q ∣ (C : ℤ) := by
      change ((s*c : ℕ) : ℤ) ∣ ((r*(s*c) : ℕ) : ℤ)
      exact_mod_cast (dvd_mul_left (s*c) r)
    have hdiff : q ∣ (A-b*q)*(D+b*q)-1-(A*D-1) :=
      ⟨b*(A-D)-b^2*q,by ring⟩
    have hprod : q ∣ A*D-1 := by
      have he := dvd_sub (hq.trans hC) hdiff
      rwa [sub_sub_cancel] at he
    obtain ⟨B,hB⟩ := hprod
    let M : SL(2, ℤ) := ⟨!![A,B;q,D],by
      rw [Matrix.det_fin_two]
      change A*D-B*q = 1
      linear_combination hB⟩
    have hM : M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) :=
      (gamma0MixedSameCusp_correspondence_shifted_det r s c hab M rfl).mpr hC
    have hAb : A < (C : ℤ) := by dsimp only [A]; exact_mod_cast ZMod.val_lt p
    have hDb : D < (C : ℤ) := by dsimp only [D]; exact_mod_cast ZMod.val_lt d
    have hRw : (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℤ)*q = (C : ℤ) := by
      rw [gamma0MixedCusp_trueWidth r s hcop]
      exact (Nat.cast_mul r (s*c)).symm
    let R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) :=
      ⟨M,hM,rfl,Int.natCast_nonneg _,by change A < _; rwa [hRw],
        Int.natCast_nonneg _,by change D < _; rwa [hRw]⟩
    refine ⟨R,?_⟩
    apply Units.ext
    exact hd

def gamma0MixedSameCuspReducedUnitEquiv (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) ≃
      (ZMod (r*(s*c)))ˣ :=
  Equiv.ofBijective (gamma0MixedSameCuspReducedUnit r s c hab)
    (gamma0MixedSameCuspReducedUnit_bijective r s c hcop hab)

end ArtinMatthews
