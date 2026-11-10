module

public import ArtinMatthews.FixedURootCount
public import ArtinMatthews.FixedURootDensity
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import ArtinMatthews.FixedURootAverageMain
public import ArtinMatthews.FixedURootMobius
public import ArtinMatthews.FixedURootResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual rectangular root counts assembled from the fixed-u estimate. -/
namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError
open scoped BigOperators

/-- The actual first-coordinate indices in the prescribed residue class. -/
noncomputable def fixedURootBoxIndices (S : ℕ) (u₀ : ℤ) (A B : ℝ) (lc rc : Bool) : Finset ℤ :=
  (realIntervalIntegers A B lc rc).filter fun u => Int.ModEq (S : ℤ) u u₀

/-- The rectangular count, with the canonical-completion coordinate scaled by `u`. -/
noncomputable def fixedURootBoxCount (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ)
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) : ℝ :=
  ∑ u ∈ fixedURootBoxIndices S u₀ A B lcU rcU,
    ((fixedURootPairs u.natAbs S c₀ v₀ d₀
      ((u.natAbs : ℝ)*α) ((u.natAbs : ℝ)*β) C D lcC rcC lcV rcV).card : ℝ)

/-- The actual finite set of triples `(u,(c,v))` in the rectangular root box. -/
noncomputable def fixedURootBoxPoints (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ)
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) :
    Finset (Σ _u : ℤ, ℤ × ℤ) :=
  (fixedURootBoxIndices S u₀ A B lcU rcU).sigma fun u =>
    fixedURootPairs u.natAbs S c₀ v₀ d₀
      ((u.natAbs : ℝ)*α) ((u.natAbs : ℝ)*β) C D lcC rcC lcV rcV

/-- The assembled count is the cardinality of its actual finite root-box set. -/
theorem fixedURootBoxCount_eq_card (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ)
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) :
    fixedURootBoxCount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV =
      ((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card : ℝ) := by
  rw [fixedURootBoxPoints,Finset.card_sigma,Nat.cast_sum]
  rfl

/-- The fixed-u count in the exact scaled coordinate `r=c/u`. -/
theorem fixedURootPairs_scaled_error : ∃ K : ℝ, 0 < K ∧
    ∀ (u S : ℕ) (c₀ v₀ d₀ : ℤ) (α β C D : ℝ) (lcC rcC lcV rcV : Bool),
      0 < u → Squarefree S →
      Int.ModEq (S : ℤ) ((u : ℤ)*d₀-c₀*v₀) 1 →
      0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      |((fixedURootPairs u S c₀ v₀ d₀ ((u : ℝ)*α) ((u : ℝ)*β)
          C D lcC rcC lcV rcV).card : ℝ) -
        ((β-α)*(D-C)/(S : ℝ)^2) * fixedURootDensity u (Nat.gcd S u)| ≤
        K*(u : ℝ)^(99/100 : ℝ)*(S : ℝ)^2*(2+(D-C)/u) := by
  obtain ⟨K,hK,hcount⟩ := fixedURootResidue_count
  refine ⟨K,hK,?_⟩
  intro u S c₀ v₀ d₀ α β C D lcC rcC lcV rcV hu hS hdet hα hαβ hβ hCD
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hdensity := fixedURootDensity_eq_product hu (Nat.gcd_pos_of_pos_right S hu)
    (Nat.gcd_dvd_right S u)
  rw [fixedU_primeFactors_filter_gcd] at hdensity
  have hh := hcount u S c₀ v₀ d₀ ((u : ℝ)*α) ((u : ℝ)*β) C D
    lcC rcC lcV rcV hu hS hdet (by nlinarith) (by nlinarith) hCD
  rw [← hdensity] at hh
  convert hh using 1
  congr 2
  field_simp

private theorem fixedURoot_interval_bounds {A B : ℝ} {lc rc : Bool} {u : ℤ}
    (hu : u ∈ realIntervalIntegers A B lc rc) : A ≤ (u : ℝ) ∧ (u : ℝ) ≤ B := by
  obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hu
  constructor
  · cases lc
    · exact le_of_lt hl
    · exact hl
  · cases rc
    · exact le_of_lt hr
    · exact hr

/-- Every actual root-box index is positive and has its natural absolute
value in the same real interval. -/
theorem fixedURootBoxIndex_bounds {S : ℕ} {u₀ : ℤ} {A B : ℝ} {lc rc : Bool}
    (hA : 1 ≤ A) {u : ℤ} (hu : u ∈ fixedURootBoxIndices S u₀ A B lc rc) :
    0 < u.natAbs ∧ (u.natAbs : ℤ) = u ∧
      A ≤ (u.natAbs : ℝ) ∧ (u.natAbs : ℝ) ≤ B := by
  obtain ⟨hl,hr⟩ := fixedURoot_interval_bounds (Finset.mem_filter.mp hu).1
  have hup : 0 < u := by exact_mod_cast (lt_of_lt_of_le (by linarith : (0:ℝ)<A) hl)
  have he : (u.natAbs : ℤ) = u := by rw [Int.natCast_natAbs,abs_of_nonneg hup.le]
  have heR : (u.natAbs : ℝ) = (u : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he
  exact ⟨Int.natAbs_pos.mpr (ne_of_gt hup),he,heR ▸ hl,heR ▸ hr⟩

/-- At most interval length divided by modulus, plus one, actual indices occur. -/
theorem fixedURootBoxIndices_card_le (S : ℕ) (hS : 0 < S) (u₀ : ℤ)
    (A B : ℝ) (hAB : A ≤ B) (lc rc : Bool) :
    ((fixedURootBoxIndices S u₀ A B lc rc).card : ℝ) ≤ (B-A)/(S : ℝ)+1 := by
  have he := sourceInterval_points A B lc rc S u₀ hS
  have hh := ErdosHyperbolaFourier.progressionPoints_count_error A B hAB lc rc S u₀ hS
  change |((sourceInterval A B lc rc S u₀ hS).points.card : ℝ) - (B-A)/(S : ℝ)| ≤ 1 at hh
  rw [he] at hh
  have hupper := (abs_le.mp hh).2
  change (((realIntervalIntegers A B lc rc).filter
    (fun n => Int.ModEq (S : ℤ) n u₀)).card : ℝ) ≤ _
  linarith


/-- Sum the genuine fixed-u errors over all actual first-coordinate indices.
This explicit uniform error is the rectangular root-residue discrepancy before
normalizing its main term by the order of the special linear group. -/
theorem fixedURootBoxCount_density_error : ∃ K : ℝ, 0 < K ∧
    ∀ (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (A B α β C D : ℝ)
      (lcU rcU lcC rcC lcV rcV : Bool),
      Squarefree S → Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
      1 ≤ A → A ≤ B → 0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      |fixedURootBoxCount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV -
        ((β-α)*(D-C)/(S : ℝ)^2) *
          (∑ u ∈ fixedURootBoxIndices S u₀ A B lcU rcU,
            fixedURootDensity u.natAbs (Nat.gcd S u.natAbs))| ≤
        K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+(D-C)/A) *
          ((B-A)/(S : ℝ)+1) := by
  obtain ⟨K,hK,hcount⟩ := fixedURootPairs_scaled_error
  refine ⟨K,hK,?_⟩
  intro S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hS hdet hA hAB hα hαβ hβ hCD
  have hSpos : 0 < S := Nat.pos_of_ne_zero hS.ne_zero
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := hApos.trans_le hAB
  have hY : 0 ≤ D-C := sub_nonneg.mpr hCD
  let U := fixedURootBoxIndices S u₀ A B lcU rcU
  let T := (β-α)*(D-C)/(S : ℝ)^2
  let E := K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+(D-C)/A)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint : ∀ u ∈ U,
      |((fixedURootPairs u.natAbs S c₀ v₀ d₀ ((u.natAbs : ℝ)*α)
        ((u.natAbs : ℝ)*β) C D lcC rcC lcV rcV).card : ℝ) -
        T * fixedURootDensity u.natAbs (Nat.gcd S u.natAbs)| ≤ E := by
    intro u hu
    obtain ⟨hup,he,hl,hr⟩ := fixedURootBoxIndex_bounds hA hu
    have hmod := (Finset.mem_filter.mp hu).2
    have hdu : Int.ModEq (S : ℤ) ((u.natAbs : ℤ)*d₀-c₀*v₀) 1 := by
      rw [he]
      exact ((hmod.mul_right d₀).sub (Int.ModEq.refl _)).trans hdet
    have hh := hcount u.natAbs S c₀ v₀ d₀ α β C D lcC rcC lcV rcV
      hup hS hdu hα hαβ hβ hCD
    have hpow : (u.natAbs : ℝ)^(99/100 : ℝ) ≤ B^(99/100 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hr (by norm_num)
    have hfrac : (D-C)/(u.natAbs : ℝ) ≤ (D-C)/A :=
      div_le_div_of_nonneg_left hY hApos hl
    refine hh.trans ?_
    dsimp [E]
    gcongr
  have hsum : |fixedURootBoxCount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV -
      T * ∑ u ∈ U, fixedURootDensity u.natAbs (Nat.gcd S u.natAbs)| ≤ (U.card : ℝ)*E := by
    unfold fixedURootBoxCount
    change |(∑ u ∈ U, _) - _| ≤ _
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _u ∈ U, E := Finset.sum_le_sum hpoint
      _ = _ := by simp
  have hcard := fixedURootBoxIndices_card_le S hSpos u₀ A B hAB lcU rcU
  exact hsum.trans (by
    change (U.card : ℝ)*E ≤ E*((B-A)/(S : ℝ)+1)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard hE)


/-- The genuine rectangular root count with its full Euler main term and
explicit errors, uniformly in the squarefree modulus and the matrix residue. -/
theorem fixedURootBoxCount_zeta_error : ∃ K : ℝ, 0 < K ∧
    ∀ (N S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (A B α β C D : ℝ)
      (lcU rcU lcC rcC lcV rcV : Bool),
      0 < N → Squarefree S → Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
      1 ≤ A → A ≤ B → B ≤ N → 0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      |fixedURootBoxCount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV -
        ((β-α)*(D-C)/(S : ℝ)^2) *
          ((B-A)/(S : ℝ) * ((riemannZeta 2).re)⁻¹ *
            (∏ p ∈ S.primeFactors, (1-1/(p : ℝ)^2)⁻¹))| ≤
        K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+(D-C)/A) *
          ((B-A)/(S : ℝ)+1) + ((β-α)*(D-C)/(S : ℝ)^2)*(2+Real.log N) := by
  obtain ⟨K,hK,hcount⟩ := fixedURootBoxCount_density_error
  refine ⟨K,hK,?_⟩
  intro N S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hN hS hdet hA hAB hBN hα hαβ hβ hCD
  have hSpos : 0 < S := Nat.pos_of_ne_zero hS.ne_zero
  have hT : 0 ≤ (β-α)*(D-C)/(S : ℝ)^2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hαβ) (sub_nonneg.mpr hCD)) (sq_nonneg _)
  have hc := hcount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hS hdet hA hAB hα hαβ hβ hCD
  have ha := fixedURootDensity_progression_average_zeta N S hN hSpos u₀
    A B hA hAB hBN lcU rcU
  change |(∑ u ∈ fixedURootBoxIndices S u₀ A B lcU rcU,
    fixedURootDensity u.natAbs (Nat.gcd S u.natAbs)) - _| ≤ _ at ha
  calc
    _ = |(fixedURootBoxCount S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV -
        ((β-α)*(D-C)/(S : ℝ)^2) *
          (∑ u ∈ fixedURootBoxIndices S u₀ A B lcU rcU,
            fixedURootDensity u.natAbs (Nat.gcd S u.natAbs))) +
        ((β-α)*(D-C)/(S : ℝ)^2) *
          ((∑ u ∈ fixedURootBoxIndices S u₀ A B lcU rcU,
            fixedURootDensity u.natAbs (Nat.gcd S u.natAbs)) -
            ((B-A)/(S : ℝ) * ((riemannZeta 2).re)⁻¹ *
              (∏ p ∈ S.primeFactors, (1-1/(p : ℝ)^2)⁻¹)))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hc (by
      rw [abs_mul,abs_of_nonneg hT]
      exact mul_le_mul_of_nonneg_left ha hT))

end ArtinMatthews
