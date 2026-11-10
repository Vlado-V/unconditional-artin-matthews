module

public import ArtinMatthews.KloostermanFourthMoment
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.AtkinLehnerModuli
public import ArtinMatthews.KloostermanAllModulusWeil
public import ArtinMatthews.KloostermanWeakBound
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedSameCuspReducedUnits
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

/-! The actual same-cusp Kloosterman sum at 1/s is an ordinary sum at
the normalized modulus with the literal phase of the two residue shifts. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem gamma0MixedSameCusp_trueModulus (r s c : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) :
    gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c : ℕ) =
      (r*(s*c) : ℕ) := by
  rw [gamma0TrueWidthModulus,gamma0MixedCusp_trueWidth r s hcop,mul_assoc,← sq,
    Real.sq_sqrt (show 0 ≤ (r : ℝ) by positivity)]
  push_cast
  ring

theorem gamma0MixedSameCuspKloosterman_eq_unit (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) m n =
      atkinPhase (((n : ℝ)-(m : ℝ))*(b : ℝ)/(r : ℝ))*
        unitKloostermanSum (r*(s*c)) (m : ZMod (r*(s*c))) (n : ZMod (r*(s*c))) := by
  classical
  let q := s*c
  let C := r*q
  unfold gamma0TrueWidthKloostermanSum unitKloostermanSum doubleCharacterSum
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (gamma0MixedSameCuspReducedUnitEquiv r s c hcop hab)
  intro R
  rw [zmodAddEquiv_apply_eq_stdAddChar,zmodAddEquiv_apply_eq_stdAddChar,← AddChar.map_add_eq_mul]
  change cuspTrueWidthGeometricPhase (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
      m n q R.val = _*ZMod.stdAddChar
      ((m : ZMod C)*((R.val 1 1+b*(q : ℤ) : ℤ) : ZMod C)+
        (n : ZMod C)*((R.val 0 0-b*(q : ℤ) : ℤ) : ZMod C))
  have hcast :
      (m : ZMod C)*((R.val 1 1+b*(q : ℤ) : ℤ) : ZMod C)+
        (n : ZMod C)*((R.val 0 0-b*(q : ℤ) : ℤ) : ZMod C) =
        ((m*(R.val 1 1+b*(q : ℤ))+n*(R.val 0 0-b*(q : ℤ)) : ℤ) : ZMod C) := by
    push_cast
    rfl
  rw [hcast,stdAddChar_eq_atkinPhase,← atkinPhase_add]
  have hwidth : (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)*(q : ℝ) =
      (r : ℝ)*(q : ℝ) := by rw [gamma0MixedCusp_trueWidth r s hcop]
  unfold cuspTrueWidthGeometricPhase
  simp only [Int.cast_natCast]
  rw [hwidth]
  congr 1
  simp only [C,Nat.cast_mul,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast]
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hq : (q : ℝ) ≠ 0 := by
    change (((s*c : ℕ) : ℝ) ≠ 0)
    exact_mod_cast NeZero.ne (s*c)
  field_simp [hr,hq]
  ring

theorem gamma0MixedSameCuspKloosterman_eq_standard (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) m n =
      atkinPhase (((n : ℝ)-(m : ℝ))*(b : ℝ)/(r : ℝ))*standardSum (r*(s*c)) m n := by
  rw [gamma0MixedSameCuspKloosterman_eq_unit r s c hcop hab,unitKloostermanSum_eq_standardSum]
  unfold standardSum
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem gamma0MixedSameCuspKloosterman_diag_eq_standard (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) (n : ℤ) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) n n =
      standardSum (r*(s*c)) n n := by
  obtain ⟨a,b,hab⟩ := exists_atkin_bezout hcop
  rw [gamma0MixedSameCuspKloosterman_eq_standard r s c hcop hab,sub_self,zero_mul,zero_div,
    atkinPhase_zero,one_mul]

theorem gamma0MixedSameCuspKloosterman_zero_of_not_dvd (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q]
    (h : ¬ s ∣ q) (m n : ℤ) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) q m n = 0 := by
  let _ : IsEmpty (gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) q) :=
    ⟨fun R => h (gamma0MixedSameCuspReduced_lower_dvd r s q R)⟩
  simp only [gamma0TrueWidthKloostermanSum,Finset.univ_eq_empty,Finset.sum_empty]

theorem gamma0MixedSameCuspKloosterman_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c],
      r.Coprime s → ∀ m n : ℤ,
        ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*c) m n‖ ≤
          D*(r*(s*c) : ℕ)^((1/2 : ℝ)+ε)*
            ((Nat.gcd (r*(s*c)) (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨D,hD,hW⟩ := standardKloosterman_weil_bound hε
  refine ⟨D,hD,?_⟩
  intro r s c _ _ _ hcop m n
  obtain ⟨a,b,hab⟩ := exists_atkin_bezout hcop
  rw [gamma0MixedSameCuspKloosterman_eq_standard r s c hcop hab,norm_mul,atkinPhase_norm,one_mul]
  exact hW _ m n

end ArtinMatthews
