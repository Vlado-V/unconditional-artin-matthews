module

public import ArtinMatthews.SpectralPeterssonPoincare
public import ArtinMatthews.SpectralPeterssonLowerRows
public import ArtinMatthews.SpectralCuspEisensteinZeroRows
public import ArtinMatthews.SpectralInequivalentCuspZero
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! The actual projective parabolic rows split into the zero sector
and the positive true-width reduced double cosets. -/

noncomputable section
open Set Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def Gamma0PeterssonZeroRow (N : ℕ) (b a : SL(2, ℤ)) :=
  {p : Gamma0PeterssonPositiveRow N b a // p.val.val 0 = 0}

def Gamma0PeterssonNonzeroRow (N : ℕ) (b a : SL(2, ℤ)) :=
  {p : Gamma0PeterssonPositiveRow N b a // p.val.val 0 ≠ 0}

theorem gamma0PeterssonZeroRow_bottom_right (N : ℕ) (b a : SL(2, ℤ))
    (p : Gamma0PeterssonZeroRow N b a) :
    p.val.val.val 1 = 1 := by
  let M := (gamma0PeterssonRowMatrix N b a p.val.val).val
  have hrow := gamma0PeterssonRowMatrix_row N b a p.val.val
  have hc : M 1 0 = 0 := (congrFun hrow 0).trans p.property
  have hd : 0 < M 1 1 := by
    rw [show M 1 1 = p.val.val.val 1 from congrFun hrow 1]
    rcases p.val.property with h | h
    · exact False.elim (h.ne' p.property)
    · exact h.2
  have hprod : M 0 0*M 1 1 = 1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using M.det_coe
  have hA : 0 < M 0 0 := by
    by_contra! h
    have hbad := mul_nonpos_of_nonpos_of_nonneg h hd.le
    rw [hprod] at hbad
    omega
  have hA1 : 1 ≤ M 0 0 := by omega
  have hd1 : M 1 1 ≤ 1 := by
    simpa only [one_mul,hprod] using mul_le_mul_of_nonneg_right hA1 hd.le
  have hh : M 1 1 = 1 := by omega
  exact (congrFun hrow 1).symm.trans hh

instance gamma0PeterssonZeroRow_subsingleton (N : ℕ) (b a : SL(2, ℤ)) :
    Subsingleton (Gamma0PeterssonZeroRow N b a) where
  allEq p q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact p.property.trans q.property.symm
    · exact (gamma0PeterssonZeroRow_bottom_right N b a p).trans
        (gamma0PeterssonZeroRow_bottom_right N b a q).symm

theorem gamma0PeterssonZeroRow_isEmpty_of_inequivalent (N : ℕ) (b a : SL(2, ℤ))
    (h : ¬ gamma0EisensteinCuspsEquivalent N b a) :
    IsEmpty (Gamma0PeterssonZeroRow N b a) :=
  ⟨fun p => gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N b a h
    (gamma0PeterssonRowMatrix N b a p.val.val)
    ((congrFun (gamma0PeterssonRowMatrix_row N b a p.val.val) 0).trans p.property)⟩

def gamma0PeterssonZeroRow_identity (N : ℕ) (a : SL(2, ℤ)) : Gamma0PeterssonZeroRow N a a :=
  let M : gamma0CuspCorrespondence N a a := ⟨1,by
    change a⁻¹*1*a ∈ CongruenceSubgroup.Gamma0 N
    simp⟩
  ⟨⟨gamma0PeterssonRowOfMatrix N a a M,Or.inr ⟨by simp [gamma0PeterssonRowOfMatrix,M],
    by simp [gamma0PeterssonRowOfMatrix,M]⟩⟩,by simp [gamma0PeterssonRowOfMatrix,M]⟩

def gamma0PeterssonNonzeroRowExpand (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (p : Σ c : Ioi (0 : ℕ), gamma0TrueWidthReducedMatrix N b a c.val × ℤ) :
    Gamma0PeterssonNonzeroRow N b a :=
  let R := gamma0PeterssonLowerRowExpand N b a p.1.val p.2
  have h : 0 < R.val.val 0 := by rw [R.property]; exact_mod_cast p.1.property
  ⟨⟨R.val,Or.inl h⟩,h.ne'⟩

theorem gamma0PeterssonNonzeroRowExpand_bijective (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) :
    Function.Bijective (gamma0PeterssonNonzeroRowExpand N b a) := by
  constructor
  · rintro ⟨c,p⟩ ⟨d,q⟩ he
    have hrow := congrArg (fun r : Gamma0PeterssonNonzeroRow N b a => r.val.val) he
    have hC := congrArg (fun r : Gamma0PeterssonSignedRow N b a => r.val 0) hrow
    change (gamma0PeterssonLowerRowExpand N b a c.val p).val.val 0 =
      (gamma0PeterssonLowerRowExpand N b a d.val q).val.val 0 at hC
    rw [(gamma0PeterssonLowerRowExpand N b a c.val p).property,
      (gamma0PeterssonLowerRowExpand N b a d.val q).property] at hC
    have hc : c = d := Subtype.ext (Int.natCast_inj.mp hC)
    subst d
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    have hh : gamma0PeterssonLowerRowExpand N b a c.val p =
        gamma0PeterssonLowerRowExpand N b a c.val q := Subtype.ext hrow
    exact congrArg (Sigma.mk c) ((gamma0PeterssonLowerRowExpand_bijective N b a c.val).1 hh)
  · intro p
    have hp : 0 < p.val.val.val 0 := by
      rcases p.val.property with hp | hp
      · exact hp
      · exact False.elim (p.property hp.1)
    let c := (p.val.val.val 0).toNat
    have hc : (c : ℤ) = p.val.val.val 0 := Int.toNat_of_nonneg hp.le
    have hcpos : 0 < c := Nat.cast_pos.mp (hc ▸ hp)
    let _ : NeZero c := ⟨hcpos.ne'⟩
    let v : Gamma0PeterssonLowerRow N b a c := ⟨p.val.val,hc.symm⟩
    obtain ⟨R,hR⟩ := (gamma0PeterssonLowerRowExpand_bijective N b a c).2 v
    refine ⟨⟨⟨c,hcpos⟩,R⟩,Subtype.ext (Subtype.ext ?_)⟩
    change (gamma0PeterssonLowerRowExpand N b a c R).val = p.val.val
    exact congrArg (fun q : Gamma0PeterssonLowerRow N b a c => q.val) hR

def gamma0PeterssonNonzeroRowEquiv (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) :
    (Σ c : Ioi (0 : ℕ), gamma0TrueWidthReducedMatrix N b a c.val × ℤ) ≃
      Gamma0PeterssonNonzeroRow N b a :=
  Equiv.ofBijective _ (gamma0PeterssonNonzeroRowExpand_bijective N b a)

end ArtinMatthews
