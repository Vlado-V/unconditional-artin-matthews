module

public import ArtinMatthews.MarkedSieveMertens
public import ArtinMatthews.RoughBonferroniDivisors
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.MarkedMajorArcDivisorNormalized
public import ArtinMatthews.MarkedMajorArcDivisorReindex
public import ArtinMatthews.MarkedMajorArcRoughMertens
public import ArtinMatthews.RoughBonferroniInterval
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Actual rough-indicator character sums, including the complex truncation
remainder and both density and length normalizations. -/
namespace ArtinMatthews
open Finset

noncomputable def markedRoughCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y t H u v : ℝ) : ℂ := by
  classical
  exact ((H*markedSieveEulerProduct y:ℝ):ℂ)⁻¹ *
    ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
      (if ∀ p ∈ Nat.primesLE ⌊y⌋₊, ¬p ∣ n then (1:ℂ) else 0) *
        (((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))

noncomputable def markedRoughTruncationError (y : ℝ) (r M N : ℕ) : ℝ :=
    ((N-M:ℕ):ℝ)*
      (∑ S ∈ (Nat.primesLE ⌊y⌋₊).powersetCard (r+1), 1/(roughSubsetDivisor S:ℝ))+
      (((Nat.primesLE ⌊y⌋₊).powersetCard (r+1)).card:ℝ)

 theorem marked_log_character_weight_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t u : ℝ) (hu : 0 < u)
    (hlog : 1 ≤ Real.log u) (n : ℕ) (hn : ⌊u⌋₊ < n) :
    ‖((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))‖ ≤ 1 := by
  have hun : u < n := (Nat.floor_lt hu.le).1 hn
  have hnp : 0 < n := by exact_mod_cast (hu.trans hun)
  have hln : 1 ≤ Real.log n := hlog.trans (Real.log_le_log hu hun.le)
  have hlnp : 0 < Real.log n := by linarith
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlnp)]
  exact (mul_le_mul (inv_le_one_of_one_le₀ hln)
    (marked_character_imaginary_power_norm_le q χ t hnp) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)

 theorem marked_rough_character_explicit_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (y t H S u v : ℝ) (r : ℕ),
        0 < H → U₀ ≤ S →
        (∀ D ∈ roughTruncationSubsets (Nat.primesLE ⌊y⌋₊) r,
          S ≤ H/(roughSubsetDivisor D:ℝ) ∧
          |t/(2*Real.pi)| ≤ (H/(roughSubsetDivisor D:ℝ))^B) →
        1 ≤ |t/(2*Real.pi)| → H ≤ u → u ≤ v → v ≤ 2*H → 1 ≤ Real.log u →
        ‖markedRoughCharacterSum χ y t H u v‖ ≤
          3*(q:ℝ)*A/(markedSieveEulerProduct y)^2 *
            (1/Real.sqrt |t/(2*Real.pi)|+S^(-δ))+
          markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊/(H*markedSieveEulerProduct y) := by
  classical
  obtain ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,hbound⟩ := marked_divisor_log_normalized_uniform B hB
  refine ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,?_⟩
  intro q _ χ y t H S u v r hH hUS hi ht hHu huv hvH hlog
  let P := Nat.primesLE ⌊y⌋₊
  let V := markedSieveEulerProduct y
  let e := 1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)
  let a : ℕ → ℂ := fun n => ((Real.log n)⁻¹:ℝ)*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))
  let T : ℂ := ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, roughDivisorPolynomial P r n*a n
  let R : ℂ := ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, (if ∀ p ∈ P, ¬p∣n then (1:ℂ) else 0)*a n
  have hV : 0 < V := markedSieveEulerProduct_pos y
  have hS : 0 < S := hU₀.trans_le hUS
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hu : 0 < u := hH.trans_le hHu
  have herr : ‖R-T‖ ≤ markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊ :=
    roughDivisorPolynomial_weighted_Ioc_error_le P r ⌊u⌋₊ ⌊v⌋₊
      (fun _ hp => Nat.prime_of_mem_primesLE hp) a
      (fun n hn => marked_log_character_weight_norm_le χ t u hu hlog n (mem_Ioc.mp hn).1)
  have htrunc := hbound (roughTruncationSubsets P r) roughSubsetDivisor
    (fun D => (-1:ℂ)^D.card) q χ t H S u v hH hUS (by
      intro D hD
      refine ⟨roughSubsetDivisor_pos D ?_, (hi D hD).1, (hi D hD).2⟩
      intro p hp
      exact Nat.prime_of_mem_primesLE ((mem_powerset.mp (mem_filter.mp hD).1) hp))
    ht hHu huv hvH hlog
  have hpoly : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
      ((Real.log n)⁻¹:ℝ)*(markedMajorDivisorPolynomial (roughTruncationSubsets P r)
        roughSubsetDivisor (fun D => (-1:ℂ)^D.card) n *
        (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))) = T := by
    apply sum_congr rfl
    intro n _
    simp only [markedMajorDivisorPolynomial, roughDivisorPolynomial, a]
    ring
  rw [hpoly] at htrunc
  have htrunc' : ‖(H:ℂ)⁻¹*T‖ ≤ 3*(q:ℝ)*A*V⁻¹*e := by
    apply htrunc.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (marked_rough_reciprocal_mass_le_inverse y r) (by positivity)) he
  have hn : markedRoughCharacterSum χ y t H u v = (V:ℂ)⁻¹*((H:ℂ)⁻¹*R) := by
    simp only [markedRoughCharacterSum, Complex.ofReal_mul, mul_inv_rev, mul_assoc, V, R, P, a]
  have hdiff : ‖(H:ℂ)⁻¹*(R-T)‖ ≤
      markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊/H := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hH.le)
  rw [hn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV]
  calc
    _ ≤ V⁻¹*(‖(H:ℂ)⁻¹*T‖+‖(H:ℂ)⁻¹*(R-T)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hV.le)
      have hid : (H:ℂ)⁻¹*R = (H:ℂ)⁻¹*T+(H:ℂ)⁻¹*(R-T) := by ring
      rw [hid]
      exact norm_add_le _ _
    _ ≤ V⁻¹*(3*(q:ℝ)*A*V⁻¹*e+markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊/H) :=
      mul_le_mul_of_nonneg_left (add_le_add htrunc' hdiff) (inv_nonneg.mpr hV.le)
    _ = _ := by
      change V⁻¹*(3*(q:ℝ)*A*V⁻¹*e+markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊/H) =
        3*(q:ℝ)*A/V^2*e+markedRoughTruncationError y r ⌊u⌋₊ ⌊v⌋₊/(H*V)
      field_simp [hV.ne',hH.ne']

end ArtinMatthews
