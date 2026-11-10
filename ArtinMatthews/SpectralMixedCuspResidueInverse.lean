module

public import ArtinMatthews.SpectralMixedCuspReducedResidues
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import Mathlib.Tactic.ReduceModChar
public import ArtinMatthews.SpectralMixedCuspNormalization
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual inverse residue construction for the ABL mixed cusp.
The shifted right entry is reduced modulo the literal `r*s*c`, while the
Atkin-Lehner residue pair has modulus `s*c`. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0MixedRightRepresentative (r q : ℕ) (b d : ℤ) : ℤ :=
  ((r : ℤ)*d-(q : ℤ)*b) % ((r : ℤ)*(q : ℤ))

theorem gamma0MixedRightRepresentative_shifted (r q : ℕ) (b d : ℤ) :
    gamma0MixedRightRepresentative r q b d+(q : ℤ)*b =
      (r : ℤ)*(d-(q : ℤ)*(((r : ℤ)*d-(q : ℤ)*b)/((r : ℤ)*(q : ℤ)))) := by
  unfold gamma0MixedRightRepresentative
  have h := Int.emod_add_mul_ediv ((r : ℤ)*d-(q : ℤ)*b) ((r : ℤ)*(q : ℤ))
  linear_combination h

theorem gamma0MixedRightRepresentative_bounds (r q : ℕ) [NeZero r] [NeZero q] (b d : ℤ) :
    0 ≤ gamma0MixedRightRepresentative r q b d ∧ gamma0MixedRightRepresentative r q b d < (r : ℤ)*(q : ℤ) := by
  have hr : 0 < (r : ℤ) := by exact_mod_cast NeZero.pos r
  have hq : 0 < (q : ℤ) := by exact_mod_cast NeZero.pos q
  exact ⟨Int.emod_nonneg _ (mul_pos hr hq).ne',Int.emod_lt_of_pos _ (mul_pos hr hq)⟩

theorem gamma0MixedRightRepresentative_cast (r q : ℕ) (b d : ℤ) :
    (gamma0MixedRightRepresentative r q b d : ZMod q) = (r : ZMod q)*(d : ZMod q) := by
  have h := congrArg (fun x : ℤ => (x : ZMod q)) (gamma0MixedRightRepresentative_shifted r q b d)
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,ZMod.natCast_self,zero_mul,add_zero,sub_zero] using h

theorem gamma0MixedRightRepresentative_quotient_cast (r q : ℕ) [NeZero r] (b d : ℤ) :
    (((gamma0MixedRightRepresentative r q b d+(q : ℤ)*b)/(r : ℤ) : ℤ) : ZMod q) = (d : ZMod q) := by
  rw [gamma0MixedRightRepresentative_shifted,Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne r)]
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,sub_zero]

theorem gamma0MixedRightRepresentative_source_congruence (r s c : ℕ)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (d : ℤ) :
    (r : ℤ) ∣ (c : ℤ)-gamma0MixedRightRepresentative r (s*c) b d := by
  let q : ℤ := (s*c : ℕ)
  let k := ((r : ℤ)*d-q*b)/((r : ℤ)*q)
  have h : gamma0MixedRightRepresentative r (s*c) b d+q*b = (r : ℤ)*(d-q*k) :=
    gamma0MixedRightRepresentative_shifted r (s*c) b d
  refine ⟨(c : ℤ)*a-d+q*k,?_⟩
  have hq : q = (s : ℤ)*(c : ℤ) := Nat.cast_mul s c
  linear_combination -h-(c : ℤ)*hab+b*hq

def gamma0MixedResidueReducedMatrix (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (ad : ↥(atkinMixedResiduePairs (NeZero.pos r) hab c)) :
    gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c) := by
  let A : ℤ := ad.val.1.val
  let d : ℤ := ad.val.2.val
  let D := gamma0MixedRightRepresentative r (s*c) b d
  have hA : (A : ZMod (s*c)) = ad.val.1 := by simp [A]
  have hd : (d : ZMod (s*c)) = ad.val.2 := by simp [d]
  have hD : (D : ZMod (s*c)) = (r : ZMod (s*c))*ad.val.2 := by
    dsimp only [D]
    rw [gamma0MixedRightRepresentative_cast,hd]
  have had := (mem_atkinMixedResiduePairs_iff (NeZero.pos r) hab c ad.val).mp ad.property
  have hdet : ((A*D-1 : ℤ) : ZMod (s*c)) = 0 := by
    rw [Int.cast_sub,Int.cast_mul,Int.cast_one,hA,hD,← mul_assoc,mul_comm ad.val.1 (r : ZMod (s*c)),had,sub_self]
  have hbex : ((s*c : ℕ) : ℤ) ∣ A*D-1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdet
  let B := Classical.choose hbex
  have hB : A*D-1 = ((s*c : ℕ) : ℤ)*B := Classical.choose_spec hbex
  let M : SL(2, ℤ) := ⟨!![A,B;((s*c : ℕ) : ℤ),D],by
    rw [Matrix.det_fin_two]
    change A*D-B*((s*c : ℕ) : ℤ) = 1
    linear_combination hB⟩
  have hM : M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) 1 := by
    obtain ⟨k,hk⟩ := gamma0MixedRightRepresentative_source_congruence r s c hab d
    have hk' : (c : ℤ)-D = (r : ℤ)*k := hk
    apply (gamma0MixedCuspCorrespondence_iff r s M).mpr
    refine ⟨k,?_⟩
    change ((s*c : ℕ) : ℤ)-(s : ℤ)*D = (r : ℤ)*(s : ℤ)*k
    simp only [Nat.cast_mul]
    linear_combination (s : ℤ)*hk'
  have hDrange := gamma0MixedRightRepresentative_bounds r (s*c) b d
  refine ⟨M,hM,rfl,?_,?_,hDrange.1,?_⟩
  · change 0 ≤ A
    exact Int.natCast_nonneg _
  · simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul]
    change A < ((s*c : ℕ) : ℤ)
    dsimp only [A]
    exact_mod_cast ZMod.val_lt ad.val.1
  · rw [gamma0MixedCusp_trueWidth r s hcop]
    change D < (r : ℤ)*((s*c : ℕ) : ℤ)
    exact hDrange.2

theorem gamma0MixedReducedResiduePair_surjective (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Function.Surjective (gamma0MixedReducedResiduePair r s c hab) := by
  intro ad
  refine ⟨gamma0MixedResidueReducedMatrix r s c hcop hab ad,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (((ad.val.1.val : ℤ) : ZMod (s*c))) = ad.val.1
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  · change (((gamma0MixedRightRepresentative r (s*c) b (ad.val.2.val : ℤ)+((s*c : ℕ) : ℤ)*b)/
        (r : ℤ) : ℤ) : ZMod (s*c)) = ad.val.2
    rw [gamma0MixedRightRepresentative_quotient_cast,Int.cast_natCast,ZMod.natCast_zmod_val]

theorem gamma0MixedReduced_nonempty_iff (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Nonempty (gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 q) ↔
      ∃ c : ℕ, 0 < c ∧ q = s*c ∧ r.Coprime c := by
  constructor
  · rintro ⟨R⟩
    exact gamma0MixedReduced_modulus_shape r s q hab R
  · rintro ⟨c,hc,rfl,hrc⟩
    let _ : NeZero c := ⟨hc.ne'⟩
    have hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    let u := ZMod.unitOfCoprime r hrq
    have hu : (r : ZMod (s*c))*((u⁻¹ : (ZMod (s*c))ˣ) : ZMod (s*c)) = 1 := by
      rw [← ZMod.coe_unitOfCoprime r hrq]
      exact u.val_inv
    let ad : ↥(atkinMixedResiduePairs (NeZero.pos r) hab c) :=
      ⟨(((u⁻¹ : (ZMod (s*c))ˣ) : ZMod (s*c)),1),
        (mem_atkinMixedResiduePairs_iff (NeZero.pos r) hab c _).mpr (by simpa only [mul_one] using hu)⟩
    exact ⟨gamma0MixedResidueReducedMatrix r s c hcop hab ad⟩

end ArtinMatthews
