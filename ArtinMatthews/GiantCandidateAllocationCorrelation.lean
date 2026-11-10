module

public import ArtinMatthews.GiantCandidateAllocationTuple
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantCharacterGraph
public import ArtinMatthews.GiantExtractionCutoff
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual allocated term in predecessor coordinates, with the
paper's test t Φ(t) divided by the predecessor. The character is
evaluated at w+1, outside the active-part invariant core. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

def giantCandidateActualShiftedCorrelation {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ u ∈ (Ioc 0 ⌊T*x⌋₊).filter (fun u => ∀ p ∈ C, ¬ p ^ 2 ∣ u+1),
    (((u:ℝ)/x*Φ ((u:ℝ)/x):ℝ):ℂ)/(u:ℂ) *
      giantCandidateFirstEndpoint e ε x u *
      (giantCandidateActiveOneMark P q u : ℂ) * χ (u+1:ℕ) *
      (giantCandidateActiveOneMark P q (u+1) : ℂ) *
      giantCandidateAllocationCore C (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j (u+1)

theorem giantCandidateActualMarkedProxyTerm_eq_shifted_correlation {J ι : Type*}
    [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (hPC : univ.biUnion P ⊆ C)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (hj : 0 < j) (x : ℝ)
    (hPW : ∀ p ∈ univ.biUnion P, Real.exp ((Real.log x)^(6/25:ℝ)) < (p : ℝ))
    (hT : 0 ≤ T) (hx : 1 ≤ x) (hΦzero : Φ 0 = 0) (hhigh : ∀ t,T<t → Φ t=0) :
    giantCandidateActualMarkedProxyTerm C P e χ ε Φ (T+1) γ q j x =
      ((j : ℂ) ^ Fintype.card ι / j.factorial) *
        ((x:ℂ) * giantCandidateActualShiftedCorrelation C P e χ ε Φ T γ q j x) := by
  classical
  rw [giantCandidateActualMarkedProxyTerm_eq_allocated C P hPC hP hdis e χ ε Φ (T+1) γ q j hj x hPW]
  apply congrArg (fun s : ℂ => ((j:ℂ)^Fintype.card ι/j.factorial)*s)
  let Q (n : ℕ) : Prop := ∀ p ∈ C, ¬ p ^ 2 ∣ n
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let f (n : ℕ) : ℂ :=
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (giantCandidateActiveOneMark P q (n-1):ℂ) * χ n *
      (giantCandidateActiveOneMark P q n:ℂ) *
      giantCandidateAllocationCore C (univ.biUnion P) W (x^γ) j n
  let S := (Icc 0 ⌊T*x⌋₊).filter (fun u => Q (u+1))
  let S₀ := (Ioc 0 ⌊T*x⌋₊).filter (fun u => Q (u+1))
  change (∑ n∈(Ioc 0 ⌊(T+1)*x⌋₊).filter Q,f n) = _
  rw [giantExtraction_predecessor_reindex T x hT hx Q f (fun n hn => by
    unfold f
    rw [markedExtractionWeight_eq_zero_of_past e (giantMarkedCenteredCore ε) Φ
      (zero_lt_one.trans_le hx) hhigh hn]
    simp only [zero_mul])]
  have hsub : S₀ ⊆ S := by
    intro u hu
    obtain ⟨hu,hq⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,(mem_Ioc.mp hu).2⟩,hq⟩
  have hcut : (∑ u ∈ S₀, f (u+1)) = ∑ u ∈ S, f (u+1) := by
    apply sum_subset hsub
    intro u hu hu₀
    have he : u = 0 := by
      by_contra h
      obtain ⟨hu,hq⟩ := mem_filter.mp hu
      exact hu₀ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h,(mem_Icc.mp hu).2⟩,hq⟩)
    subst u
    simp only [f, markedExtractionWeight, Nat.zero_add, Nat.sub_self, Nat.cast_zero,
      zero_div, hΦzero, Complex.ofReal_zero, zero_mul]
  change (∑ u ∈ S, f (u+1)) = _
  rw [← hcut, giantCandidateActualShiftedCorrelation, Finset.mul_sum]
  apply sum_congr rfl
  intro u hu
  have huC : (u:ℂ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hu).1).1.ne'
  have hxR : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hscale : (x:ℂ)*((((u:ℝ)/x*Φ ((u:ℝ)/x):ℝ):ℂ)/(u:ℂ)) = (Φ ((u:ℝ)/x):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hxR, huC]
  simp only [f, W, giantCandidateFirstEndpoint, markedExtractionWeight, Nat.add_sub_cancel]
  rw [← hscale]
  ring

/-- After removing the common labels, the conjugate character of the
edge difference separates over the two free lists, including nonunits. -/
theorem giantCandidate_character_comparison_separated {M : ℕ}
    (χ : DirichletCharacter ℂ M) (R A B u : ℕ) (hR : R.Coprime M) :
    conj (χ (R*(A*B):ℕ)) * χ (R*(u+A*B):ℕ) =
      conj (χ A) * conj (χ B) * χ (u+A*B:ℕ) := by
  simpa only [Nat.cast_mul, map_mul] using giant_character_shared_factor χ R (A*B) (u+A*B) hR

theorem giantCandidate_character_free_list_norm_le {M : ℕ}
    (χ : DirichletCharacter ℂ M) (D : ℕ) (b : ℂ) :
    ‖b * conj (χ D)‖ ≤ ‖b‖ := by
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

end
end ArtinMatthews
