module

public import ArtinMatthews.MarkedMajorArcPaperSource


set_option backward.privateInPublic true
@[expose] public section

/-! Exact treatment of an arbitrary closed natural coefficient interval.
The lower endpoint is retained as a genuine singleton dyadic block. -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section

 def markedMajorIntervalPairSum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass bands:ℂ)^2*
    ∑ b ∈ markedMajorLabelSet bands,∑ m ∈ S,∑ n ∈ Icc l r,
    ∑ a ∈ markedMajorLabelSet bands,∑ r' ∈ T,∑ s ∈ Icc l r,
      cutoff ((b:ℝ)/Y)*cutoff ((a:ℝ)/Y)*
      markedMajorCenteredCoefficient W modulation m*conj (markedMajorCenteredCoefficient W modulation r')*
      β n*conj (β s)*ψ ((markedMajorIntegerDeterminant (b,m,n) (a,r',s):ℝ)/Y)*
      markedBanMajorKernel Q Y (markedMajorIntegerDeterminant (b,m,n) (a,r',s)-(b:ℤ)+(a:ℤ))

 theorem markedMajorIntervalPairSum_Ioc {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation
      (Ioc ⌊u⌋₊ ⌊v⌋₊) (Ioc ⌊u⌋₊ ⌊v⌋₊) l r β =
      markedMajorDeterminantPaperSum bands cutoff ψ Q Y W modulation u v l r β := rfl

 theorem markedMajorIntervalPairSum_closed_split {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (M N : ℕ) (hMN : M ≤ N) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation (Icc M N) (Icc M N) l r β =
      markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation (Ioc M N) (Ioc M N) l r β +
      markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation {M} (Ioc M N) l r β +
      markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation (Ioc M N) {M} l r β +
      markedMajorIntervalPairSum bands cutoff ψ Q Y W modulation {M} {M} l r β := by
  simp only [markedMajorIntervalPairSum,Icc_eq_cons_Ioc hMN,sum_cons,sum_singleton,
    sum_add_distrib,mul_add]
  ring

 theorem markedMajor_singleton_interval {M : ℕ} (hM : 1 ≤ M) :
    ({M}:Finset ℕ)=Ioc ⌊(M:ℝ)-1⌋₊ ⌊(M:ℝ)⌋₊ := by
  have hf : ⌊(M:ℝ)-1⌋₊=M-1 := by
    rw [← Nat.cast_one,← Nat.cast_sub hM,Nat.floor_natCast]
  ext n
  simp only [mem_singleton,mem_Ioc,hf,Nat.floor_natCast]
  omega

 theorem markedMajor_singleton_scale {H : ℝ} {M : ℕ}
    (hH : 2 ≤ H) (hHM : H ≤ (M:ℝ)) (hMH : (M:ℝ) ≤ 2*H) :
    H/2 ≤ (M:ℝ)/2 ∧ (M:ℝ)/2 ≤ H ∧
    (M:ℝ)/2 ≤ (M:ℝ)-1 ∧ (M:ℝ)-1 ≤ M ∧ (M:ℝ) ≤ 2*((M:ℝ)/2) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end ArtinMatthews
