module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicGram.PeriodicPoisson
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import OAI.NumberTheory.CubicGram.Reciprocity
public import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Exact separation of a nonzero Eisenstein integer into a global unit,
a ramified-prime power, and a primary factor. -/
noncomputable section
namespace CubicFirstMoment

lemma unit_ramified_primary_decomposition {v : Eisenstein} (hv : v ≠ 0) :
    ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
      v=(u:Eisenstein)*lambdaE^k*a := by
  have H : ∀ v : Eisenstein, v ≠ 0 →
      ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
        v=(u:Eisenstein)*lambdaE^k*a := by
    intro v
    induction v using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit b hb =>
      intro _
      obtain ⟨u,rfl⟩ := hb
      exact ⟨u,0,1,primary_one,by simp⟩
    | mul b p hb hp ih =>
      intro _
      obtain ⟨u,k,a,ha,he⟩ := ih hb
      by_cases hp3 : IsCoprime p 3
      · obtain ⟨w,hw,hpw⟩ := unit_lift_mod_three (residue_isUnit_of_isCoprime hp3.symm)
        obtain ⟨w,rfl⟩ := hw
        refine ⟨u*w⁻¹,k,(p*(w:Eisenstein))*a,primary_mul hpw ha,?_⟩
        rw [he,Units.val_mul]
        linear_combination -(p*(u:Eisenstein)*lambdaE^k*a)*w.mul_inv
      · have hpd : p ∣ (3:Eisenstein) := by
          by_contra h
          exact hp3 (isRelPrime_iff_isCoprime.mp (hp.isRelPrime_iff_not_dvd.mpr h))
        have hpl : p ∣ lambdaE := hp.prime.dvd_of_dvd_pow
          (by rw [lambdaE_sq]; exact dvd_neg.mpr hpd)
        obtain ⟨w,hw⟩ := hp.associated_of_dvd lambdaE_prime.irreducible hpl
        refine ⟨u*w⁻¹,k+1,a,ha,?_⟩
        rw [he,Units.val_mul,pow_succ,←hw]
        linear_combination -(p*(u:Eisenstein)*(p*(w:Eisenstein))^k*a)*w.mul_inv
  exact H v hv

end CubicFirstMoment

end

end OAI
