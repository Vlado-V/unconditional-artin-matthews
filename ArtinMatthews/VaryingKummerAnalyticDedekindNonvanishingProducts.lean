module

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd


set_option backward.privateInPublic true
@[expose] public section

/-! General finite geometric-product and multiplicative Euler nonvanishing
lemmas extracted from OpenAI PrimePackets/PrimeFactors and RootOverlaps. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open scoped Classical BigOperators ENNReal
universe u v

lemma ennreal_tsum_fintype_prod {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞),
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f
    simp
  · intro α _ ih κ f
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

 


lemma complex_summable_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    Summable (fun k : ∀ i, κ i => ‖∏ i, f i (k i)‖) := by
  classical
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
  rw [ennreal_tsum_fintype_prod κ (fun i a => (‖f i a‖₊ : ℝ≥0∞))]
  exact ENNReal.prod_ne_top (fun i _ => tsum_enorm_ne_top_iff_summable_norm.mpr (hf i))

lemma complex_tsum_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℂ),
      (∀ i, Summable (fun a => ‖f i a‖)) →
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f hf
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i)) (fun i => hf (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f _
    simp
  · intro α _ ih κ f hf
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [←tsum_mul_tsum_of_summable_norm (hf none)
      (complex_summable_fintype_prod _ _ (fun i => hf (some i))), ih _ _ (fun i => hf (some i))]

lemma complex_tsum_multiset_prod {α : Type*} [Fintype α]
    (f : α → ℂ) (hf : ∀ a, ‖f a‖ < 1) :
    Summable (fun m : Multiset α => ‖(m.map f).prod‖) ∧
    (∑' m : Multiset α, (m.map f).prod) = ∏ a, (1-f a)⁻¹ := by
  classical
  let e : (α → ℕ) ≃ Multiset α :=
    Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.symm.toEquiv
  have hm (m : Multiset α) : (m.map f).prod = ∏ a, f a ^ m.count a := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    rw [Multiset.count_eq_zero.mpr (by simpa using ha),pow_zero]
  have he (k : α → ℕ) (a : α) : (e k).count a = k a := by simp [e]
  have hfS (a : α) : Summable (fun k : ℕ => ‖f a ^ k‖) := by
    simpa only [norm_pow] using summable_geometric_of_norm_lt_one
      (show ‖‖f a‖‖ < 1 by simpa using hf a)
  have hS := complex_summable_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  have hT := complex_tsum_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  constructor
  · rw [←e.summable_iff]
    simpa only [Function.comp_def,hm,he] using hS
  · rw [←e.tsum_eq]
    simp only [hm,he]
    rw [hT]
    apply Finset.prod_congr rfl
    intro a _
    exact tsum_geometric_of_norm_lt_one (hf a)

lemma primePower_succ_injective : Function.Injective
    (fun a : Nat.Primes × ℕ => (a.1 : ℕ) ^ (a.2+1)) := by
  rintro ⟨p,k⟩ ⟨q,l⟩ h
  obtain ⟨hp,hk⟩ := p.property.pow_inj q.property h
  exact Prod.ext (Subtype.ext hp) hk

 

theorem complex_multiplicative_tsum_ne_zero
    (f : ℕ → ℂ) (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hs : Summable (fun m => ‖f m‖))
    (hlocal : ∀ p : Nat.Primes, (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0) :
    (∑' m : ℕ, f m) ≠ 0 := by
  let E (p : Nat.Primes) : ℂ := ∑' k : ℕ, f ((p:ℕ)^k)
  have hpS (p : Nat.Primes) : Summable (fun k : ℕ => f ((p:ℕ)^k)) :=
    hs.of_norm.comp_injective (Nat.pow_right_injective p.property.two_le)
  have hspp : Summable (fun a : Nat.Primes × ℕ => f ((a.1:ℕ)^(a.2+1))) :=
    hs.of_norm.comp_injective primePower_succ_injective
  have he (p : Nat.Primes) : E p = 1 + ∑' k : ℕ, f ((p:ℕ)^(k+1)) := by
    change (∑' k : ℕ, f ((p:ℕ)^k)) = _
    rw [(hpS p).tsum_eq_zero_add]
    simp only [pow_zero,hone]
  have hdev : Summable (fun p : Nat.Primes => 1-E p) := by
    have H := hspp.prod.neg
    exact H.congr (fun p => by dsimp; rw [he]; ring)
  have hl : Summable (fun p : Nat.Primes => Complex.log (E p)) := by
    simpa only [sub_sub_cancel] using hdev.clog_one_sub
  have hP := hl.hasSum.cexp
  have hexp (p : Nat.Primes) : Complex.exp (Complex.log (E p)) = E p :=
    Complex.exp_log (hlocal p)
  simp only [Function.comp_def,hexp] at hP
  have hE : HasProd E (∑' m : ℕ, f m) :=
    EulerProduct.eulerProduct_hasProd hone hmul hs hzero
  rw [hE.unique hP]
  exact Complex.exp_ne_zero _

end
end ArtinMatthews.VaryingKummerAnalytic
