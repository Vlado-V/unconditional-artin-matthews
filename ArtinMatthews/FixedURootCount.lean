module

public import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-!
# Fixed first-coordinate root rectangles

The finite set below is precisely the three integer congruences in (det:fixed-u-congruences).
The CRT reduction keeps arbitrary residues modulo the part of `S` coprime to `u`.
Its estimate uses the proved incomplete-hyperbola count, with no unit assumption on
these arbitrary residues. All interval endpoints may be open or closed.
-/

namespace ArtinMatthews

open OAI.Erdos970
open ErdosHyperbolaError ErdosHyperbolaIdentities

/-- Integer pairs satisfying the fixed-`u` determinant and matrix residue conditions. -/
noncomputable def fixedURootPairs (u S : ℕ) (c₀ v₀ d₀ : ℤ)
    (x₀ x₁ y₀ y₁ : ℝ) (lcI rcI lcJ rcJ : Bool) : Finset (ℤ × ℤ) :=
  ((realIntervalIntegers x₀ x₁ lcI rcI).product
    (realIntervalIntegers y₀ y₁ lcJ rcJ)).filter fun cv =>
      Int.ModEq (S : ℤ) cv.1 c₀ ∧ Int.ModEq (S : ℤ) cv.2 v₀ ∧
      Int.ModEq ((u * S : ℕ) : ℤ) (cv.1 * cv.2) ((u : ℤ) * d₀ - 1)

/-- The modular product condition is exactly the existence of an integral
completion with the prescribed lower-right residue. -/
theorem fixedURoot_completion_iff (u S : ℕ) (c v d₀ : ℤ) :
    Int.ModEq ((u*S : ℕ) : ℤ) (c*v) ((u : ℤ)*d₀-1) ↔
      ∃ d : ℤ, (u : ℤ)*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨d₀-(S : ℤ)*k,?_,?_⟩
    · push_cast at hk
      linear_combination hk
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨k,by ring⟩
  · rintro ⟨d,hd,hm⟩
    obtain ⟨k,hk⟩ := hm.dvd
    refine ⟨k,?_⟩
    push_cast
    linear_combination (u : ℤ)*hk + hd

/-- The first residue is automatically invertible at every prime common to `S` and `u`. -/
def fixedUFirstUnit (u S₁ : ℕ) (c₀ v₀ d₀ : ℤ) (hS₁ : S₁ ∣ u)
    (hdet : (u : ZMod S₁) * d₀ - c₀ * v₀ = 1) : (ZMod S₁)ˣ where
  val := c₀
  inv := -v₀
  val_inv := by
    have hu : (u : ZMod S₁) = 0 := (ZMod.natCast_eq_zero_iff u S₁).mpr hS₁
    rw [hu, zero_mul, zero_sub] at hdet
    simpa only [mul_neg] using hdet
  inv_val := by
    have hu : (u : ZMod S₁) = 0 := (ZMod.natCast_eq_zero_iff u S₁).mpr hS₁
    rw [hu, zero_mul, zero_sub] at hdet
    simpa only [neg_mul, mul_neg, mul_comm] using hdet

/-- The determinant right-hand side is a unit modulo `u*S₁`. -/
noncomputable def fixedUProductUnit (u S₁ : ℕ) (d₀ : ℤ) (hS₁ : S₁ ∣ u) :
    (ZMod (u * S₁))ˣ :=
  ZMod.unitOfIsCoprime (-1 + (u : ℤ) * d₀)
    (source_product_coprime u S₁ hS₁ (-1) d₀ (by simp))

private theorem int_modEq_mul_iff {m n : ℕ} (hcop : m.Coprime n) (a b : ℤ) :
    Int.ModEq ((m * n : ℕ) : ℤ) a b ↔
      Int.ModEq (m : ℤ) a b ∧ Int.ModEq (n : ℤ) a b := by
  simpa only [Int.natAbs_natCast, Nat.cast_mul] using
    (Int.modEq_and_modEq_iff_modEq_mul (a := a) (b := b)
      (m := (m : ℤ)) (n := (n : ℤ)) hcop).symm

/-- CRT removes the redundant second residue modulo `S₁`, using determinant one. -/
theorem fixedURootPairs_eq_sourcePairs (u S₁ S₂ : ℕ) (c₀ v₀ d₀ : ℤ)
    (hS₁ : S₁ ∣ u) (hcop : S₂.Coprime (u * S₁))
    (hdet : Int.ModEq ((S₁ * S₂ : ℕ) : ℤ) ((u : ℤ) * d₀ - c₀ * v₀) 1)
    (x₀ x₁ y₀ y₁ : ℝ) (lcI rcI lcJ rcJ : Bool) :
    fixedURootPairs u (S₁ * S₂) c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ =
      sourcePairs u S₁ S₂ (-1) d₀ c₀ c₀ v₀ 1 x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ := by
  have hcop₁ : S₁.Coprime S₂ := (hcop.of_dvd_right (dvd_mul_left S₁ u)).symm
  have hdet₁ : (u : ZMod S₁) * d₀ - c₀ * v₀ = 1 := by
    have hh := hdet.of_dvd (show (S₁ : ℤ) ∣ ((S₁ * S₂ : ℕ) : ℤ) by
      exact_mod_cast (dvd_mul_right S₁ S₂))
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hh
  let a := fixedUFirstUnit u S₁ c₀ v₀ d₀ hS₁ hdet₁
  have hvc (c v : ℤ) (hc : Int.ModEq (S₁ : ℤ) c c₀)
      (hp : Int.ModEq ((u * S₁ : ℕ) : ℤ) (c*v) ((u : ℤ)*d₀-1)) :
      Int.ModEq (S₁ : ℤ) v v₀ := by
    have he := hp.of_dvd (show (S₁ : ℤ) ∣ ((u * S₁ : ℕ) : ℤ) by
      exact_mod_cast (dvd_mul_left S₁ u))
    have hc' : (c : ZMod S₁) = (c₀ : ZMod S₁) := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hc
    have he' : (c₀ : ZMod S₁) * v = (c₀ : ZMod S₁) * v₀ := by
      have he'' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr he
      push_cast at he''
      rw [hc'] at he''
      linear_combination he'' + hdet₁
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    exact a.isUnit.mul_left_cancel he'
  have hpS₂ (c v : ℤ) (hc : Int.ModEq (S₂ : ℤ) c c₀)
      (hv : Int.ModEq (S₂ : ℤ) v v₀) :
      Int.ModEq (S₂ : ℤ) (c*v) ((u : ℤ)*d₀-1) := by
    have hd := hdet.of_dvd (show (S₂ : ℤ) ∣ ((S₁ * S₂ : ℕ) : ℤ) by
      exact_mod_cast (dvd_mul_left S₂ S₁))
    have hr : Int.ModEq (S₂ : ℤ) (c₀*v₀) ((u : ℤ)*d₀-1) := by
      apply Int.modEq_iff_dvd.mpr
      convert hd.symm.dvd using 1; ring
    exact (hc.mul hv).trans hr
  ext ⟨c,v⟩
  simp only [fixedURootPairs, sourcePairs, Finset.mem_filter, Nat.cast_one, one_dvd, true_and]
  constructor
  · rintro ⟨hmem,hc,hv,hp⟩
    obtain ⟨hc₁,hc₂⟩ := (int_modEq_mul_iff hcop₁ c c₀).mp hc
    obtain ⟨_,hv₂⟩ := (int_modEq_mul_iff hcop₁ v v₀).mp hv
    refine ⟨hmem,hc₁,hc₂,hv₂,?_⟩
    have hh := hp.of_dvd (show ((u*S₁ : ℕ) : ℤ) ∣ ((u*(S₁*S₂) : ℕ) : ℤ) by
      exact_mod_cast (show u*S₁ ∣ u*(S₁*S₂) by use S₂; ring))
    convert hh using 1; ring
  · rintro ⟨hmem,hc₁,hc₂,hv₂,hp⟩
    have hp' : Int.ModEq ((u*S₁ : ℕ) : ℤ) (c*v) ((u : ℤ)*d₀-1) := by
      convert hp using 1; ring
    refine ⟨hmem,(int_modEq_mul_iff hcop₁ c c₀).mpr ⟨hc₁,hc₂⟩,
      (int_modEq_mul_iff hcop₁ v v₀).mpr ⟨hvc c v hc₁ hp',hv₂⟩,?_⟩
    have hh := (int_modEq_mul_iff hcop.symm (c*v) ((u : ℤ)*d₀-1)).mpr
      ⟨hp',hpS₂ c v hc₂ hv₂⟩
    simpa only [Nat.mul_assoc] using hh


/-- The genuine incomplete-hyperbola estimate for the original fixed-`u` congruences. -/
theorem fixedURootPairs_count_error (u S₁ S₂ : ℕ) (hu : 0 < u)
    (h₁ : 0 < S₁) (h₂ : 0 < S₂) (hS₁ : S₁ ∣ u)
    (hcop : S₂.Coprime (u * S₁)) (c₀ v₀ d₀ : ℤ)
    (hdet : Int.ModEq ((S₁ * S₂ : ℕ) : ℤ) ((u : ℤ) * d₀ - c₀ * v₀) 1)
    (x₀ x₁ y₀ y₁ : ℝ) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (lcI rcI lcJ rcJ : Bool) :
    |((fixedURootPairs u (S₁ * S₂) c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ).card : ℝ) -
      (x₁-x₀)*(y₁-y₀)/((u : ℝ)*((S₁*S₂ : ℕ) : ℝ)^2) *
        ((u.totient : ℝ)/(u : ℝ)*((S₁ : ℝ)/(S₁.totient : ℝ)))| ≤
      completionConstant*((u*S₁).divisors.card : ℝ)^3 *
        (Real.log (2*((u*S₁ : ℕ) : ℝ)))^2 *
        (((u*S₁ : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt S₁ *
          (1+(x₁-x₀)/((u*S₁ : ℕ) : ℝ)+(y₁-y₀)/((u*S₁ : ℕ) : ℝ)) := by
  let : NeZero u := ⟨hu.ne'⟩
  let : NeZero S₁ := ⟨h₁.ne'⟩
  have hdet₁ : (u : ZMod S₁) * d₀ - c₀ * v₀ = 1 := by
    have hh := hdet.of_dvd (show (S₁ : ℤ) ∣ ((S₁ * S₂ : ℕ) : ℤ) by
      exact_mod_cast (dvd_mul_right S₁ S₂))
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hh
  let a := fixedUFirstUnit u S₁ c₀ v₀ d₀ hS₁ hdet₁
  let c := fixedUProductUnit u S₁ d₀ hS₁
  let P := sourceInterval x₀ x₁ lcI rcI S₂ c₀ h₂
  let Q := sourceInterval y₀ y₁ lcJ rcJ S₂ v₀ h₂
  have he := sourcePairs_eq_dilated u S₁ S₂ (-1) d₀ c₀ c₀ v₀ 1
    x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ h₂ a c rfl rfl
  have hone : dilatedPairs (u*S₁) S₁ a c P Q 1 =
      hyperbolaPairs (u*S₁) S₁ a c P.points Q.points := by
    ext z
    simp only [dilatedPairs, Finset.mem_filter, Nat.cast_one, one_dvd, and_true]
  have hcount := hyperbola_count_error u S₁ a c P Q hx hy hcop hcop
  rw [fixedURootPairs_eq_sourcePairs u S₁ S₂ c₀ v₀ d₀ hS₁ hcop hdet,
    he, hone]
  have hphi := source_totient_product u S₁ hS₁ h₁
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have h₁R : (S₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have h₂R : (S₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hpR : (S₁.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr h₁).ne'
  convert hcount using 1 <;> dsimp [P,Q,sourceInterval,intervalLength]
  rw [hphi]
  push_cast
  field_simp


/-- The squarefree modulus supplies exactly the coprime split used above. -/
theorem fixedURoot_squarefree_split (u S : ℕ) (hu : 0 < u) (hS : Squarefree S) :
    0 < Nat.gcd S u ∧ 0 < S / Nat.gcd S u ∧
      Nat.gcd S u ∣ u ∧
      (S / Nat.gcd S u).Coprime (u * Nat.gcd S u) ∧
      Nat.gcd S u * (S / Nat.gcd S u) = S := by
  have hg : 0 < Nat.gcd S u := Nat.gcd_pos_of_pos_right S hu
  have hq : 0 < S / Nat.gcd S u :=
    Nat.div_pos (Nat.gcd_le_left u (Nat.pos_of_ne_zero hS.ne_zero)) hg
  have hc : (S / Nat.gcd S u).Coprime u := Nat.coprime_div_gcd_of_squarefree hS hu.ne'
  exact ⟨hg,hq,Nat.gcd_dvd_right S u,
    hc.mul_right (hc.of_dvd_right (Nat.gcd_dvd_right S u)),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left S u)⟩

end ArtinMatthews
